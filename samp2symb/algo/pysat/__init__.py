#!/usr/bin/env python3

import sys, os, io, re
import itertools, functools, operator
from typing import *

import pysat, pysat.formula, pysat.solvers

from samp2symb.base.trace import AlphaTrace
from ...base.dfa import DFA
from ...utils import timeout_generator

Var = NewType('Var', int)

class DFASolver():
    def __init__(self, N, alphabet):
        """Create a SAT problem for inferring a DFA.
            If a weight is not set, it is considered to be hard.

            :param N: number of nodes of the final automaton.
            :type N: int

            :param alphabet: isn't it that obvious?
            :type alphabet: list(<Letter>)
        """
        self.restart(N, alphabet)

        # for trace in positive_sample:
        #     self._generate_clauses_trace(trace, True, weight=weight_sample)
        # for trace in negative_sample:
        #     self._generate_clauses_trace(trace, False, weight=weight_sample)
        # for hint in sub_hints:
        #     self._generate_clauses_incl_dfa(hint, True, weight=weight_hint)
        # for hint in sup_hints:
        #     self._generate_clauses_incl_dfa(hint, False, weight=weight_hint)


    def restart(self, N=None, alphabet=None):
        if N is not None: self.N = int(N)
        if alphabet is not None: self.alphabet = alphabet

        self.vpool = pysat.formula.IDPool()
        self.all_clauses = []

        self.trans_ids = self._new_vars(self.N * len(self.alphabet) * self.N)
        self.trans_id = lambda p, a, q: self.trans_ids[((a) * self.N + p) * self.N + q]
        self.term_ids = self._new_vars(self.N)
        self.term_id = lambda q: self.term_ids[q]

        self._generate_clauses_automaton()
        self.classification = Classification(
            label = self._generate_clauses_word_init(),
        )

        self.wcnf = None




    def _new_var(self) -> Var:
        """Create a fresh variable."""
        return self.vpool._next()

    def _new_vars(self, count) -> Sequence[Var]:
        """Create `count` fresh variables."""
        if not count: return ()
        start = self.vpool._next()
        stop = start + count - 1
        self.vpool.top = stop
        return range(start, stop+1)

    def _add_clauses(self, *clauses):
        self.all_clauses.extend(clauses)
        # self.all_clauses.append(itertools.chain.from_iterable(clauses))

    def _generate_clauses_automaton(self):
        """
        """

        # AUTOMATON DETERMINISM

        exist_transition = (
            ([
                +self.trans_id(p, a, q)
                for q in range(self.N)
            ], None)
            for p in range(self.N)
            for a,letter in enumerate(self.alphabet)
        )

        unique_transition = (
            ([
                -self.trans_id(p, a, q1),
                -self.trans_id(p, a, q2),
            ], None)
            for p in range(self.N)
            for a,letter in enumerate(self.alphabet)
            for q1 in range(self.N)
            for q2 in range(self.N)
            if q1 != q2
        )

        self._add_clauses(
            exist_transition,
            unique_transition,
        )

    def _generate_clauses_word_new(self) -> Callable[[int],Var]:
        """
            Generate clauses for a new word.

            :return: word reach state ids
            :rtype: function(q:int):int
        """
        u_reach_ids = self._new_vars(self.N)
        u_reach_id  = lambda q: u_reach_ids[q]

        exist_state = (
            ([
                +u_reach_id(q)
                for q in range(self.N)
            ], None),
        )

        unique_state = (
            ([
                -u_reach_id(q1),
                -u_reach_id(q2),
            ], None)
            for q1 in range(self.N)
            for q2 in range(self.N)
            if q1 != q2
        )

        self._add_clauses(
            exist_state,
            unique_state,
        )

        return u_reach_id

    def _generate_clauses_word_init(self) -> Callable[[int],Var]:
        """
            :return: empty word reach state ids
            :rtype: function(q:int):int
        """
        e_reach_id = self._generate_clauses_word_new()

        initial_state_clauses = (
            ([
                +e_reach_id(0),
            ], None),
        )

        self._add_clauses(
            initial_state_clauses,
        )

        return e_reach_id

    def _generate_clauses_word_trans(self, u_reach_id:Callable[[int],Var], letter) -> Callable[[int],Var]:
        """
            :param u_reach_id: prefix reach state ids
            :type: function(q:int):int

            :return: word reach state ids
            :rtype: function(q:int):int
        """
        a = self.alphabet.index(letter)
        ua_reach_id = self._generate_clauses_word_new()

        transition_state_clauses = (
            ([
                -u_reach_id(p),
                -self.trans_id(p, a, q),
                +ua_reach_id(q),
            ], None)
            for p in range(self.N)
            for q in range(self.N)
        )

        self._add_clauses(
            transition_state_clauses,
        )

        return ua_reach_id

    def _generate_clauses_word(self, word, *, break_symmetry:bool=True) -> Callable[[int],Var]:
        """
            Generate missing prefixes clauses.

            :return: word reach state ids
            :rtype: function(q:int):int
        """
        node = self.classification
        for letter in word:
            if letter not in node.keys():
                ua_reach_id = self._generate_clauses_word_trans(node.label, letter)
                if break_symmetry:
                    # total ordering of prefixes based on the order of registering to the prefix tree
                    u_reach_ids = []
                    self.classification.map_reduce(map = lambda label: u_reach_ids.append(label))
                    break_symmetry_clauses = (
                        ([
                            +u_reach_id(p)
                            for u_reach_id in u_reach_ids
                        ]+[
                            -ua_reach_id(p+1),
                        ], None)
                        for p in range(self.N-1)
                    )
                    self._add_clauses(
                        break_symmetry_clauses,
                    )
                node[letter] = Classification(label=ua_reach_id)
            node = node[letter]
        return node.label

    def _generate_clauses_trace(self, word, label:bool=True) -> Var:
        """
            :return: handle variable for this constraint
            :rtype: int
        """
        label = bool(label)
        if isinstance(word, AlphaTrace):
            assert word.finite, "finite word expected"
            word = word.vector

        word_reach_id = self._generate_clauses_word(word)
        handle_id = self._new_var()

        consistency_clauses = (
            ([
                -handle_id,
                -word_reach_id(q),
                (+1 if label else -1) * self.term_id(q),
            ], None)
            for q in range(self.N)
        )

        self._add_clauses(
            consistency_clauses,
        )

        return handle_id

    def _generate_clauses_reached_costates(self, dfa:DFA, coreach_id:Callable[[int,int],int]=None) -> Callable[[int,int],Var]:
        """
            coreach_id(q,q2) will be True if ever reached.
            Creates N * len(dfa.states) new vars.

            :return: reach costate ids
            :rtype: function(int, int)
        """
        if coreach_id is None:
            coreach_ids = self._new_vars(self.N * len(dfa.states))
            coreach_id = lambda q, q2: coreach_ids[(q2) * self.N + q]

        initial_costate_clauses = (
            ([
                +coreach_id(0, dfa.states.index(init2)),
            ], None)
            for init2 in dfa._initial_states() # should be only one
        )

        transition_costate_clauses = (
            ([
                -coreach_id(p, p2),
                -self.trans_id(p, a, q),
                +coreach_id(q, dfa.states.index(next_state2)),
            ], None)
            for p in range(self.N)
            for p2,state2 in enumerate(dfa.states)
            for a,letter in enumerate(self.alphabet)
            for q in range(self.N)
            for next_state2 in dfa._next_states([state2], letter)
        )

        self._add_clauses(
            initial_costate_clauses,
            transition_costate_clauses,
        )

        return coreach_id

    def _generate_clauses_unreached_costates(self, dfa:DFA, coreach_id:Callable[[int,int],int]=None) -> Callable[[int,int],Var]:
        """
            coreach_id(q,q2) will be False if never reached.
            Creates N^2 * len(dfa.states)^2 * (1+len(alphabet)*N) new vars (thats a lot).

            :return: reach costate ids
            :rtype: function(int, int)
        """
        if coreach_id is None:
            coreach_ids = self._new_vars(self.N * len(dfa.states))
            coreach_id = lambda q, q2: coreach_ids[(q2) * self.N + q]

        co_N = self.N * len(dfa.states) # max word length to check
        partial_coreach_ids = self._new_vars(co_N * self.N * len(dfa.states))
        def partial_coreach_id(i, q, q2):
            if i<co_N: return partial_coreach_ids[((i) * self.N + q) * len(dfa.states) + q2]
            else:      return coreach_id(q, q2) # i==co_N
        partial_coreach_by_trans_ids = self._new_vars(co_N * self.N * len(dfa.states) * len(self.alphabet) * self.N)
        def partial_coreach_by_trans_id(i, p, p2, a, q):
            return partial_coreach_by_trans_ids[((((i) * self.N + p) * len(dfa.states) + p2) * len(self.alphabet) + a) * self.N + q]

        initial_costate_clauses = (
            ([
                -partial_coreach_id(0, q, q2),
            ], None)
            for q in range(self.N)
            for q2,state2 in enumerate(dfa.states)
            if q != 0 or state2 not in dfa._initial_states()
        )

        transition_clauses = (
            ([
                -cause,
                -partial_coreach_by_trans_id(i, p, p2, a, q),
            ], None)
            for i in range(co_N)
            for p in range(self.N)
            for p2,state2 in enumerate(dfa.states)
            for a,letter in enumerate(self.alphabet)
            for q in range(self.N)
            for cause in (
                -partial_coreach_id(i, p, p2),
                -self.trans_id(p, a, q),
            )
        )

        transition_costate_clauses = (
            ([
                +partial_coreach_by_trans_id(i, p, p2, a, q)
                for a,letter in enumerate(self.alphabet)
                for p in range(self.N)
                for p2,state2 in enumerate(dfa.states)
                if next_state2 in dfa._next_states([state2], letter)
             ]+[
                +partial_coreach_id(i, q, q2),
                -partial_coreach_id(i+1, q, q2),
            ], None)
            for i in range(co_N)
            for q in range(self.N)
            for q2,next_state2 in enumerate(dfa.states)
        )

        self._add_clauses(
            initial_costate_clauses,
            transition_clauses,
            transition_costate_clauses,
        )

        return coreach_id

    def _generate_clauses_incl_dfa(self, dfa:DFA, sub=True):
        """Indicates that the given DFA is a sub/sup language wrt the inferred DFA.
            :return: handle variable for this constraint
            :rtype: int
        """
        sub = bool(sub)

        coreach_id = self._generate_clauses_reached_costates(dfa)
        handle_id = self._new_var()

        if sub: states_of_interest = dfa._terminal_states()
        else:        states_of_interest = dfa._states() - dfa._terminal_states()

        consistency_clauses = (
            ([
                -handle_id,
                -coreach_id(q, q2),
                (+1 if sub else -1) * self.term_id(q)
            ], None)
            for q in range(self.N)
            for q2,state2 in enumerate(dfa.states)
            if state2 in states_of_interest
        )

        self._add_clauses(
            consistency_clauses,
        )

        return handle_id

    def _generate_clauses_nincl_dfa(self, dfa, sub=True):
        """Indicates that the given DFA is not a sub/sup language wrt the inferred DFA.
            :return: handle variable for this constraint
            :rtype: int
        """
        sub = bool(sub)

        coreach_id = self._generate_clauses_unreached_costates(dfa)
        handle_id = self._new_var()

        if sub: states_of_interest = dfa._terminal_states()
        else:        states_of_interest = dfa._states() - dfa._terminal_states()
        states_of_interest = list(states_of_interest)
        tmp_ids = self._new_vars(self.N * len(states_of_interest))
        tmp_id = lambda q, qi2: tmp_ids[(qi2) * self.N + q]

        consistency_clauses = (
            ([
                -tmp_id(q, qi2),
                +prop,
            ], None)
            for q in range(self.N)
            for qi2,state2 in enumerate(states_of_interest)
            for prop in (
                +coreach_id(q, dfa.states.index(state2)),
                -(+1 if sub else -1) * self.term_id(q)
            )
        )

        existence_clauses = (
            ([
                -handle_id,
             ]+[
                tmp_id(q, qi2)
                for q in range(self.N)
                for qi2,state2 in enumerate(states_of_interest)
            ], None),
        )

        self._add_clauses(
            consistency_clauses,
            existence_clauses,
        )

        return handle_id

    def _generate_clauses_neq_dfa(self, dfa):
        """if 
        note: dfa should be similar (same size, same alphabet)
        :return: handle variable for this constraint
        :rtype: int
        """

        handle_id = self._new_var()

        clauses = (
            ([
                -handle_id,
            # ]+[  # We assume the unique initial state is always 0
            #     -(+1 if state in dfa._initial_states() else -1) * self.XXX_id(p)
            #     for p,state in enumerate(dfa.states)
            ]+[
                -(+1 if state in dfa._terminal_states() else -1) * self.term_id(p)
                for p,state in enumerate(dfa.states)
            ]+[
                -(+1 if state2 in dfa._next_states([state], letter) else -1) * self.trans_id(p,a,q)
                for p,state in enumerate(dfa.states)
                for a,letter in enumerate(dfa.alphabet)
                for q,state2 in enumerate(dfa.states)
            ], None),
        )

        self._add_clauses(
            clauses,
        )

        return handle_id


    def add_sample(self, sample, soft=False):
        """Makes the inferred DFA consistent with the given sample."""
        weight = True if soft else None
        for trace in sample.acceptedTraces: self.add_trace(trace, True,  weight=weight)
        for trace in sample.rejectedTraces: self.add_trace(trace, False, weight=weight)
        return self
    
    def add_trace(self, trace, label:bool=None, weight=None):
        """Makes the inferred automata ($A$) consistent with the given trace ($u$).

        Args:
            trace (AlphaTrace|Sequence[letters]): Given trace $u$.
            label (bool, optional): Enforce $(u \in A) = label$.
            weight (int, optional): Soft constraint with this weight; if `True`, the trace weight is used instead.

        Returns:
            DFASolver: self
        """
        if isinstance(trace, AlphaTrace):
            assert trace.finite, "finite word expected"
            if weight is True: weight = trace.weight
            if label is None: label = trace.intendedEvaluation
            trace = trace.vector
        handle_id = self._generate_clauses_trace(trace, label=label)
        handle_clauses = (
            ([
                +handle_id,
            ], weight),
        )
        self._add_clauses(handle_clauses)
        return self
    
    def add_dfa(self, dfa, *,
        sub:bool=None, sup:bool=None,
        weight=None,
    ):
        """Makes the inferred dfa ($A$) consistent with the given dfa ($B$).
        This method wont be effective unless you specify `sup` or `sub`.

        Args:
            dfa (Formula): The given DFA ($B$).
            sub (bool, optional): Enforce $L(B) \subseteq L(A)$ if `True`, or $L(B) \nsubseteq L(A)$ if `False`.
            sup (bool, optional): Enforce $L(B) \supseteq L(A)$ if `True`, or $L(B) \nsupseteq L(A)$ if `False`.
            weight (int, optional): Soft constraint with this weight (default: hard constraind).

        Returns:
            DFASolver: self
        """
        if sub is None: pass
        elif sub: 
            handle_id = self._generate_clauses_incl_dfa(dfa, sub=True)
            self._add_clauses((([+handle_id], weight),))
        else:
            handle_id = self._generate_clauses_nincl_dfa(dfa, sub=True)
            self._add_clauses((([+handle_id], weight),))

        if sup is None: pass
        elif sup: 
            handle_id = self._generate_clauses_incl_dfa(dfa, sub=False)
            self._add_clauses((([+handle_id], weight),))
        else:
            handle_id = self._generate_clauses_nincl_dfa(dfa, sub=False)
            self._add_clauses((([+handle_id], weight),))
        return self

    def add_neq_dfa(self, dfa, weight=None):
        """Used to specify unwanted models."""
        handle_id = self._generate_clauses_neq_dfa(dfa)
        self._add_clauses((([+handle_id], weight),))
        return self


    def build_cnf(self):
        """
            Generate all previously added constraints.
            This method is called automatically by ``solve()`` but can still
            be called by the user (e.g. to time the constraints generation).
        """
        if self.wcnf is None:
            self.wcnf = pysat.formula.WCNF()
            self.wcnf.atms = [] # FIXME in the orig code

        for clauses in self.all_clauses:
            for clause, weight in clauses:
                self.wcnf.append(clause, weight=weight)
        self.all_clauses.clear()

        return self.wcnf

    # def _solve_unweighted(self, solver=pysat.solvers.Glucose3):
    #     """
    #         Basic SAT solver. No not care about hard/soft distinction.
    #         .. warning:: ``build_cnf`` should have been called before.
    #     """
    #     self.solver = solver(bootstrap_with=self.wcnf.unweighted().clauses)
    #     if not self.solver.solve(): return False
    #     self.model = self.solver.get_model()
    #     return True

    # def _solve_FM(self):
    #     """
    #         MAXSAT solver: https://pysathq.github.io/docs/pysat.pdf#subsection.1.2.1
    #         .. warning:: ``build_cnf`` should have been called before.
    #     """
    #     from pysat.examples.fm import FM
    #     self.solver = FM(self.wcnf, verbose=0)
    #     if not self.solver.compute(): return False
    #     # print(self.solver.cost)
    #     self.model = list(self.solver.model)
    #     return True

    # def solve(self, solver=pysat.solvers.Glucose3): # NOT WORKING
    #     # https://pysathq.github.io/docs/pysat.pdf#subsection.1.2.4
    #     from pysat.examples.lbx importLBX
    #     lbx = LBX(wcnf, use_cld=True, solver_name='g3')
    #     for mcs in lbx.enumerate():
    #         lbx.block(mcs)
    #         print(mcs)

    # def _solve_RC2(self):
    #     """
    #         MAXSAT solver: https://pysathq.github.io/docs/pysat.pdf#subsection.1.2.9
    #         .. warning:: ``build_cnf`` should have been called before.
    #     """
    #     from pysat.examples.rc2 import RC2
    #     with RC2(self.wcnf) as rc2:
    #         for m in rc2.enumerate():
    #             # print('model{0}has cost{1}'.format(m, rc2.cost))
    #             self.model = m
    #             return True
    #     return False

    # def solve(self, method="rc2"):
    #     """
    #         Solve the SAT problem.

    #         :param method: "rc2"|"fm"|"gc3"
    #     """
    #     self.build_cnf()
    #     return {
    #         "gc3": functools.partial(self._solve_unweighted, solver=pysat.solvers.Glucose3),
    #         "fm":  self._solve_FM,
    #         "rc2": self._solve_RC2,
    #     }[method]()

    def _get_automaton(self, model):
        """
            Extract results as a DFA.
            .. warning:: ``solve`` should have been called successfully before.
        """
        transitions = {}
        accepting_states = []
        for p in range(self.N):
            for a,letter in enumerate(self.alphabet):
                for q in range(self.N):
                    if self.trans_id(p,a,q) in model:
                        if (p,letter) in transitions.keys():
                            print("WARNING: automaton not deterministic (too many transitions)", file=sys.stderr)
                        transitions[(p,letter)] = q
                    # elif -self.trans_id(p,a,q) not in model:
                    #     print("WARNING: transition undetermined", file=sys.stderr)
                if (p,letter) not in transitions.keys():
                    print("WARNING: automaton not deterministic (missing transition)", file=sys.stderr)
            # transitions.append(trans)
            if self.term_id(p) in model:
                accepting_states.append(p)
        transitions2 = dict()
        for (p,letter),q in transitions.items():
            transitions2.setdefault(p,dict())[letter] = q
        return DFA(
            # alphabet = self.alphabet,
            # states = list(range(self.N)),
            # transitions = transitions,
            # init_states = [0], accepting_states = accepting_states,
            transitions = transitions2,
            init_state = 0, final_states=accepting_states,
        )
    
    def solve_rc2(self, *args, **kwargs) -> DFA:
        try: return next(self.iter_solve_rc2(*args, **kwargs))
        except StopIteration: return None
    @timeout_generator
    def iter_solve_rc2(self) -> Iterable[DFA]:
        self.build_cnf()
        from pysat.examples.rc2 import RC2
        with RC2(self.wcnf) as rc2:
            for model in rc2.enumerate():
                dfa = self._get_automaton(model)
                yield dfa


    # def get_unclassified_samples(self):
    #     """
    #         return to lists of words: negative an positive.
    #         .. warning:: ``solve`` should have been called successfully before.
    #     """
    #     unclassified_positive_sample = []
    #     unclassified_negative_sample = []
    #     for i,word in enumerate(self.positive_sample):
    #         posid = +(1+i)
    #         if -self.POSIT_VARID(posid) in self.model:
    #             unclassified_positive_sample.append(word)
    #     clauses = self.wcnf.unweighted().clauses
    #     for i,word in enumerate(self.negative_sample):
    #         negid = -(1+i)
    #         if +self.NEGAT_VARID(negid) in self.model:
    #             unclassified_negative_sample.append(word)
    #     return (unclassified_positive_sample, unclassified_negative_sample)


class Classification(dict):
    """
        Tree structure allowing to classify words with labels (``None`` by default).
    """


    def __init__(self, label=None, *arg, **kwd):
        super(Classification, self).__init__(*arg, **kwd)
        self.label = label


    # def append(self, word,
    #     label = None,
    #     on_create = (lambda node, letter: None),
    # ):
    #     """
    #         :type word:  sequence(<Letter>)
    #         :type label: <Label>
    #         :rtype:      <Label>
    #     """
    #     w = iter(word)
    #     try:
    #         letter = next(w)
    #         if letter not in self.keys():
    #             self[letter] = self.__class__()
    #             on_create(self, letter)
    #         return self[letter].append(w, label)
    #     except StopIteration: # end of recursion
    #         old_label, self.label = self.label, label
    #         return old_label
    #
    # def append2(self, word,
    #     label = None,
    #     on_create = (lambda node, letter: None),
    # ):
    #     node = self
    #     for letter in word:
    #         if letter not in node.keys():
    #             node[letter] = self.__class__()
    #             on_create(node, letter)
    #         node = node[letter]
    #     old_label, node.label = node.label, label
    #     return old_label

    def get(self, word):
        """
            Get a word's label. Return ``None`` if the word is not classified.
            :type word: sequence(<Letter>)
            :rtype:     <Label>
        """
        w = iter(word)
        try:
            letter = next(w)
            if not letter in self.keys(): return None
            return self[letter].get(w)
        except StopIteration: # end of recursion
            return self.label


    def map_reduce(self, *args,
                   map        = (lambda label, *args: None),
                   reduce     = (lambda value, suffix_reduced: None),
                   args_rec   = (lambda letter, *args: args),
    ):
        """
            Iter over the tree structure.

            :param map:      function used on each node of the tree.
            :param reduce:   function used to merge the result of ``map`` and of each suffixes.
            :param args_rec: function used to change the arguments when going through branches.
            :return:         the result of the map-reduce operation.

            :type map:      function(<Label>, *list(<Args>)): <Value>
            :type reduce:   function(<Value>, <Value>): <Value>
            :type args_rec: function(<Letter>, *list(<Args>)): list(<Args>)
            :rtype:         <Value>
        """
        return functools.reduce(
            reduce,
            (
                suffix.map_reduce(
                    *args_rec(letter, *args),
                    args_rec=args_rec,
                    map=map,
                    reduce=reduce,
                )
                for letter, suffix in self.items()
            ),
            map(self.label, *args),
        )

    # without recursion (TODO)
    def map_reduce2(self, *args,
                   map        = (lambda label, *args: None),
                   reduce     = (lambda value, suffix_reduced: None),
                   args_rec   = (lambda letter, *args: args),
    ):
        """
            Iter over the tree structure.

            :param map:      function used on each node of the tree.
            :param reduce:   function used to merge the result of ``map`` and of each suffixes.
            :param args_rec: function used to change the arguments when going through branches.
            :return:         the result of the map-reduce operation.

            :type map:      function(<Label>, *list(<Args>)): <Value>
            :type reduce:   function(<Value>, <Value>): <Value>
            :type args_rec: function(<Letter>, *list(<Args>)): list(<Args>)
            :rtype:         <Value>
        """
        return functools.reduce(
            reduce,
            (
                suffix.map_reduce(
                    *args_rec(letter, *args),
                    args_rec=args_rec,
                    map=map,
                    reduce=reduce,
                )
                for letter, suffix in self.items()
            ),
            map(self.label, *args),
        )

    def print_tree(self, file=sys.stdout, print_unclassified=False):
        self.map_reduce("",
            map = (lambda label, prefix:
                file.write("{}: {}\n".format(prefix, label))
                if (print_unclassified or label is not None) else None
            ),
            args_rec = (lambda letter, prefix:
                ["{}{}".format(prefix, letter)]
            ),
        )


    def count_words(self, count_unclassified=False, *, filter=None, label=None):
        if filter is None: filter = lambda l: True
        if label is not None: filter = lambda l: l==label
        return self.map_reduce(
            map = (lambda l: bool((l is not None or count_unclassified) and filter(l))),
            reduce = operator.add,
        )


    def max_len(self):
        return self.map_reduce(
            map = (lambda label: 0),
            reduce = (lambda v,s: max(v,s+1)),
        )


    def to_simple_dict(self):
        def reduce(tree, branch):
            tree[1][branch[0]] = branch[1]
            return tree
        return self.map_reduce(None,
            map = (lambda label, l: (l,{})),
            reduce = reduce,
            args_rec = (lambda letter, l: [letter]),
        )[1]
