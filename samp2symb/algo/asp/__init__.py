#!/usr/bin/env python3

import sys, os, io, re
from typing import *
from ...base.ltl import Formula

class LTLSolver():
    op_table = {
        '&':    "land",
        '|':    "lor",
        '!':    "lnot",
        '->':   "limplies",
        '<->':  "lequiv",
        'F':    "finally",
        'G':    "globally",
        'U':    "until",
        'X':    "next",
    }
    op_rev_table = {o:l for l,o in op_table.items()}
    ENCODING_FILE = os.path.join(os.path.dirname(__file__), "ltl_encoding.lp")

    def __init__(self, size:int, use_constants:bool=True, atoms=[]):
        r"""Create an ASP problem for inferring an LTL formula $\phi$,
        that can be solved using ASP or QBF.

        Args:
            size (int): size of the inferred formula $|\phi|$.
            use_constants (bool, optional): Allows the use of constants ("true", "false") in $\phi$. Defaults to `True`.
            atoms (list, optional): list of literals that should appear. Usefull if no other literals are introduced with `add_trace()` or `add_formula()`.
        """
        
        self.program = io.StringIO()
        self.requires_QASP = False

        assert size >= 1, "invalid formula size"
        self.size = size
        self.atoms = set(atoms)
        self.used_names = dict()
        phi = "phi"

        print(f"""%% define unknown formula {phi}\n""", file=self.program)
        print(f"""#const n = {size}.""",                                                                                               file=self.program)
        print(f"""node({phi}(0..(n-1))).""",                                                                                            file=self.program)
        print(f"""_exists(3,node({phi}(P))) :- node({phi}(P)).""",                                                                      file=self.program)
        print(f""":- child({phi}(P),N0), #false: node({phi}(P0)), {phi}(P0)=N0.     % {phi}(P) can only have {phi}(P0) as childs""",    file=self.program)
        print(f""":- child({phi}(P),{phi}(P0)), not P<P0.                           % formula is acyclic, head is {phi}(0)""",          file=self.program)
        print(f"""{{child({phi}(P),{phi}(P0)) : node({phi}(P))}}>0 :- node({phi}(P0)), P0>0.  % no node is an orphan""",                     file=self.program)
        print(f"""node({phi}(P),trace(bool)) :- node({phi}(P)).                     % define typing of {phi}(P)""",                     file=self.program)
        if not use_constants:
            print(f""":- node({phi}(_),operator(const(_),_,_),_).  % do not use constants""", file=self.program)
        if atoms:
            print(f"""atom({ ';'.join(atoms)} ).""", file=self.program)
        
        print(f""":- node({phi}(_),operator(lequiv,_,_),_).""", file=self.program) # not handled yet in python
        
        # """TMP (remove me)"""
        # print(f""":- node({phi}(_),operator(const(_),_,_),_).""", file=self.program)
        # print(f""":- node({phi}(_),operator(land,_,_),_).""", file=self.program)
        # print(f""":- node({phi}(_),operator(lor,_,_),_).""", file=self.program)
        # print(f""":- node({phi}(_),operator(limplies,_,_),_).""", file=self.program)
        # print(f""":- node({phi}(_),operator(lequiv,_,_),_).""", file=self.program)
        # print(f""":- node({phi}(_),operator(until,_,_),_).""", file=self.program)
        # print(f""":- node({phi}(_),operator(next,_,_),_).""", file=self.program)
        # print(f""":- node({phi}(_),operator(finally,_,_),_).""", file=self.program)
        
        print(file=self.program)
    
    def _fresh_name(self, prefix) -> str:
        self.used_names.setdefault(prefix,-1)
        self.used_names[prefix] += 1
        return f"{prefix}{self.used_names[prefix]}"
    
    @staticmethod
    def _2const(val) -> str:
        if val in ["false", "False"]: val = False
        return "true" if val else "false"


    def add_sample(self, sample):
        """Makes the inferred formula ($\phi$) consistent with the given sample."""
        print(f"""%% define known sample...\n""", file=self.program)
        for trace in sample.acceptedTraces: self.add_trace(trace, True)
        for trace in sample.rejectedTraces: self.add_trace(trace, False)
        return self
    
    def add_trace(self, trace, label:bool=None):
        """Makes the inferred formula ($\phi$) consistent with the given trace ($u$).
        This method wont be effective unless you specify `label`.

        Args:
            trace (PropTrace): The given trace ($u$).
            label (bool, optional): Enforce $\phi(u)=label$.

        Returns:
            LTLSolver: self
        """        
        u = self._fresh_name("u")
        print(f"""%% define known {'positive' if label else 'negative'} trace\n""", file=self.program)
        len_prefix = trace.lassoStart if trace.lassoStart is not None else trace.lengthOfTrace
        len_cycle = trace.lengthOfTrace - len_prefix  # 0 if finite
        # assert len_cycle > 0, "infinite trace expected"
        print(f"""trace({u},{len_prefix},{len_cycle}).""", file=self.program)
        for t, values in enumerate(trace.vector):
            for x, v in zip(trace.literals, values):
                if v is None: continue
                self.atoms.add(x)
                print(f"""val_trace({x},{self._2const(v)}, {u},{t}).""", file=self.program)
        print(f"""_exists(3, val_trace(X,V, {u},T)) :- val_trace(X,V, {u},T).""", file=self.program)
        if label is not None:
            print(f"""val_node(phi(0),{self._2const(label)}, {u},0).""", file=self.program)
        print(file=self.program)
        return self

    @classmethod
    def _formula2nodes(cls, formula, nodes=None) -> Dict[str,Tuple[int,Formula]]:
        "return all the distinct nodes of a given formula, in the form {text: (id, formula)}."
        if nodes is None: nodes=dict()
        if formula is None: return nodes
        if formula in nodes.keys(): return nodes
        nodes[str(formula)] = (len(nodes), formula)
        cls._formula2nodes(formula.left, nodes)
        cls._formula2nodes(formula.right, nodes)
        return nodes
    
    def add_formula(self, formula, *,
        sub:bool=None, sup:bool=None,
        check_horizon:int=float('inf'), check_finite=False,
    ):
        r"""Makes the inferred formula ($\phi$) consistent with the given formula ($\psi$).
        This method wont be effective unless you specify `sup` or `sub`.

        Args:
            formula (Formula): The given formula ($\psi$).
            sub (bool, optional): Enforce $L(\psi) \subseteq L(\phi)$ if `True`, or $L(\psi) \nsubseteq L(\phi)$ if `False`.
            sup (bool, optional): Enforce $L(\psi) \supseteq L(\phi)$ if `True`, or $L(\psi) \nsupseteq L(\phi)$ if `False`.
            check_horizon (int, optional): Checks for traces up to this length.
            check_finite (bool|None, optional): Checks for finite traces (`True`), infinite traces (`False`) or both (`None`).

        Returns:
            LTLSolver: self
        """    
        phi, psi = "phi", self._fresh_name("psi")
        nodes = self._formula2nodes(formula)
        print(f"""%% define known formula {psi}\n""", file=self.program)
        for p,node in nodes.values():
            if node.label in self.op_table.keys(): op = f"{self.op_table[node.label]}"
            elif node.label in ['true', 'false']: op = f"const({node.label})"
            elif node.label[0] == 'x': op = f"atom({node.label})"; self.atoms.add(node.label)
            else: raise TypeError(node.label)
            childs = [child for child in [node.left, node.right] if child is not None]
            typ = "trace(bool)"
            print(
                "node("
                    f"""{psi}({p}),"""
                    f"""operator({op},({ ''.join(f"{typ}," for child in childs) }),{typ}),"""
                    f"""({ ''.join(f"{psi}({nodes[str(child)][0]})," for child in childs) })"""
                ").",
                file=self.program,
            )
        print(f"""_exists(3,node({psi}(P))) :- node({psi}(P)).""", file=self.program)
        print(file=self.program)

        check_horizon = min(check_horizon, 2**(self.size+formula.size))
        if check_finite is None: # check both finite and infinite traces
            LEN_HORIZON = f"""LEN_P=(0..{check_horizon}), LEN_C=(0..{check_horizon}), LEN_P+LEN_C<={check_horizon}, LEN_P+LEN_C>=1"""
        elif check_finite: # check only finite traces
            LEN_HORIZON = f"""LEN_P=(1..{check_horizon}), LEN_C=0"""
        else: # check only infinite traces
            LEN_HORIZON = f"""LEN_P=(0..{check_horizon}), LEN_C=(1..{check_horizon}), LEN_P+LEN_C<={check_horizon}"""
        # note that we excluded the empty word

        if sup is None: pass
        elif sup:
            self.requires_QASP = True
            print(f"""%% enforce {psi} \\supseteq {phi}\n""", file=self.program)
            print(f"""node({phi}_limplies_{psi}).""", file=self.program)
            print(f"""_exists(LEVEL,node({phi}_limplies_{psi})) :- _exists(LEVEL,node({phi}(0))).""", file=self.program)
            print(f"""node({phi}_limplies_{psi},operator(limplies,(bool,bool),bool),({phi}(0),{psi}(0))).""", file=self.program)
            print(file=self.program)
            # print(f"""#const t_all = {check_horizon}.""", file=self.program)
            print(f"""trace_forall(all_u(LEN_P,LEN_C)) :- {LEN_HORIZON}.""", file=self.program)
            print(f"""trace(all_u(LEN_P,LEN_C),LEN_P,LEN_C) :- trace_forall(all_u(LEN_P,LEN_C)).""", file=self.program)
            print(f"""_exists(9,trace_forall(U)) :- trace_forall(U).""", file=self.program)
            print(f"""{{val(X,T)}} :- atom(X), trace_forall(U), trace_T(U,T).""", file=self.program)
            print(f""":- not val_trace(X,true,  U,T), trace_forall(U), trace_T(U,T), atom(X),     val(X,T).""", file=self.program)
            print(f""":- not val_trace(X,false, U,T), trace_forall(U), trace_T(U,T), atom(X), not val(X,T).""", file=self.program)
            print(f"""_forall(2, val(X,T)) :- val(X,T).""", file=self.program)
            print(f"""_exists(3, val_trace(X,V, U,T)) :- val_trace(X,V, U,T), trace_forall(U).""", file=self.program)
            print(f"""val_node({phi}_limplies_{psi},true, U,0) :- trace_forall(U).""", file=self.program)
            print(file=self.program)
        elif not sup:
            print(f"""%% enforce {psi} \\nsupseteq {phi}\n""", file=self.program)
            print(f"""node({phi}_limplies_{psi}).""", file=self.program)
            print(f"""_exists(LEVEL,node({phi}_limplies_{psi})) :- _exists(LEVEL,node({phi}(0))).""", file=self.program)
            print(f"""node({phi}_limplies_{psi},operator(limplies,(bool,bool),bool),({phi}(0),{psi}(0))).""", file=self.program)
            print(file=self.program)
            # print(f"""#const t_any = {check_horizon}.""", file=self.program)
            print(f"""{{trace({any_u},LEN_P,LEN_C) : {LEN_HORIZON}}}=1.""", file=self.program)
            print(f"""_exists(3, val_trace(X,V, U,T)) :- val_trace(X,V, U,T), U={any_u}.""", file=self.program)
            print(f"""val_node({phi}_limplies_{psi},false, U,0) :- U={any_u}.""", file=self.program)
            print(file=self.program)
        
        if sub is None: pass
        elif sub:
            self.requires_QASP = True
            print(f"""%% enforce {psi} \\subseteq {phi}\n""", file=self.program)
            print(f"""node({psi}_limplies_{phi}).""", file=self.program)
            print(f"""_exists(LEVEL,node({psi}_limplies_{phi})) :- _exists(LEVEL,node({phi}(0))).""", file=self.program)
            print(f"""node({psi}_limplies_{phi},operator(limplies,(bool,bool),bool),({psi}(0),{phi}(0))).""", file=self.program)
            print(file=self.program)
            # print(f"""#const t_all = {check_horizon}.""", file=self.program)
            print(f"""trace_forall(all_u(LEN_P,LEN_C)) :- {LEN_HORIZON}.""", file=self.program)
            print(f"""trace(all_u(LEN_P,LEN_C),LEN_P,LEN_C) :- trace_forall(all_u(LEN_P,LEN_C)).""", file=self.program)
            print(f"""_exists(9,trace_forall(U)) :- trace_forall(U).""", file=self.program)
            print(f"""{{val(X,T)}} :- atom(X), trace_forall(U), trace_T(U,T).""", file=self.program)
            print(f""":- not val_trace(X,true,  U,T), trace_forall(U), trace_T(U,T), atom(X),     val(X,T).""", file=self.program)
            print(f""":- not val_trace(X,false, U,T), trace_forall(U), trace_T(U,T), atom(X), not val(X,T).""", file=self.program)
            print(f"""_forall(2, val(X,T)) :- val(X,T).""", file=self.program)
            print(f"""_exists(3, val_trace(X,V, U,T)) :- val_trace(X,V, U,T), trace_forall(U).""", file=self.program)
            print(f"""val_node({psi}_limplies_{phi},true, U,0) :- trace_forall(U).""", file=self.program)
            print(file=self.program)
        elif not sub:
            any_u = self._fresh_name("any_u")
            print(f"""%% enforce {psi} \\nsubseteq {phi}\n""", file=self.program)
            print(f"""node({psi}_limplies_{phi}).""", file=self.program)
            print(f"""_exists(LEVEL,node({psi}_limplies_{phi})) :- _exists(LEVEL,node({phi}(0))).""", file=self.program)
            print(f"""node({psi}_limplies_{phi},operator(limplies,(bool,bool),bool),({psi}(0),{phi}(0))).""", file=self.program)
            print(file=self.program)
            # print(f"""#const t_any = {check_horizon}.""", file=self.program)
            print(f"""{{trace({any_u},LEN_P,LEN_C) : {LEN_HORIZON}}}=1.""", file=self.program)
            print(f"""_exists(3, val_trace(X,V, U,T)) :- val_trace(X,V, U,T), U={any_u}.""", file=self.program)
            print(f"""val_node({psi}_limplies_{phi},false, U,0) :- U={any_u}.""", file=self.program)
            print(file=self.program)
        
        return self

    @classmethod
    def _symbols2formula(cls, symbols:Iterable[str]) -> Formula:
        """reconstruct a formula from asp atoms."""
        nodes = dict()
        for op_desc in symbols:
            op_desc = str(op_desc)
            match = re.match(r"op\((?P<parent>phi\(\d+\)),(?P<op>.+),\((?P<childs>(?:phi\(\d+\),)*(?:phi\(\d+\))?)\)\)", op_desc)
            if not match: continue  # or error?
            op = match.group('op')
            parent = match.group('parent')
            childs = [node for node in match.group('childs').split(',') if node]
            if op in cls.op_rev_table.keys():
                nodes[parent] = Formula([cls.op_rev_table[op], *childs])
                continue
            match = re.match(r"(?P<op>\w+)\((?P<arg>.+)\)", op)
            if match:
                assert not childs
                nodes[parent] = Formula(match.group('arg'))
        for node in nodes.values():
            if node.left is not None: node.left = nodes[node.left]
            if node.right is not None: node.right = nodes[node.right]
        # print(">>> symbols = ",symbols)
        # print(">>> nodes = ",nodes)
        formula = nodes['phi(0)']
        return formula

    def solve_qbf(self, *, timeout=float("inf")):
        """Solves a QASP problem with a QBF solver."""
        if not self.requires_QASP: print("WARNING: using QBF is overkill, ASP will probably compute faster.", file=sys.stderr)
        if timeout<=0: raise TimeoutError()
        phi = "phi"
        program = io.StringIO(); program.write(self.program.getvalue())
        print(f"""%% show operators of {phi}\n""", file=program)
        print(f"""op({phi}(P),OP,NODES) :- node({phi}(P),operator(OP,_,_),NODES).""",   file=program)
        print(f"""_exists(1,op({phi}(P),OP,NODES)) :- op({phi}(P),OP,NODES).""",        file=program)
        print(file=program)

        import subprocess, threading
        from subprocess import PIPE
        p1 = subprocess.Popen(["clingo", "--output=smodels", self.ENCODING_FILE, "-"], stdin=subprocess.PIPE, stdout=subprocess.PIPE, encoding='utf-8')
        p2 = subprocess.Popen(["qasp2qbf.py"],                  stdin=p1.stdout, stdout=subprocess.PIPE)
        p3 = subprocess.Popen(["lp2normal2"],                   stdin=p2.stdout, stdout=subprocess.PIPE)
        p4 = subprocess.Popen(["lp2acyc"],                      stdin=p3.stdout, stdout=subprocess.PIPE)
        p5 = subprocess.Popen(["lp2sat"],                       stdin=p4.stdout, stdout=subprocess.PIPE)
        p6 = subprocess.Popen(["qasp2qbf.py", "--cnf2qdimacs"], stdin=p5.stdout, stdout=subprocess.PIPE)
        p7 = subprocess.Popen(["caqe", "--qdo"],                stdin=p6.stdout, stdout=subprocess.PIPE)  # this is the call to the solver
        p8 = subprocess.Popen(["qasp2qbf.py", "--interpret"],   stdin=p7.stdout, stdout=subprocess.PIPE, encoding='utf-8')
        p1.stdin.write(program.getvalue())
        p1.stdin.close()
        result = []
        thread = threading.Thread(target=lambda: result.extend(p8.communicate()[0].splitlines()))
        thread.start()

        thread.join(timeout if timeout<float("inf") else None)
        if thread.is_alive():
            for p in [p1,p2,p3,p4,p5,p6,p7,p8]: p.terminate()
            thread.join()
            raise TimeoutError(f"{timeout} second passed and the solver did not resumed.")
        if p8.returncode != 0: return None  # unsat

        formula = self._symbols2formula(result)
        return formula
    
    def solve_asp(self, *args, **kwargs) -> Formula:
        """Returns the first solution of `iter_solve_asp()`."""
        return next(self.iter_solve_asp(*args, models=1, **kwargs))
    def iter_solve_asp(self, *, models:int=None, timeout=float("inf")) -> Iterable[Formula]:
        if models is None: models = "0"
        assert not self.requires_QASP, "a QASP solver is required to solve this problem."
        if timeout<=0: raise TimeoutError()
        phi = "phi"
        program = io.StringIO(); program.write(self.program.getvalue())
        print(f"""%% show operators of {phi}\n""", file=program)
        print(f"""#show.""", file=program)
        print(f"""#show op({phi}(P),OP,NODES) : node({phi}(P),operator(OP,_,_),NODES).""", file=program)
        print(file=program)

        import clingo
        from pytictoc import TicToc
        tictoc_total = TicToc()
        tictoc_total.tic()
        ctl = clingo.Control(str(models))
        ctl.load(self.ENCODING_FILE)
        ctl.add("base", [], program.getvalue())
        ctl.ground([("base", [])])
        with ctl.solve(yield_=True, async_=True) as handle:
            models = iter(handle)
            while True:
                # if not handle.wait(): break
                # print(handle.wait(0))
                while not handle.wait(0):
                    if tictoc_total.tocvalue() > timeout:
                        raise TimeoutError()
                try: model = next(models)
                except StopIteration: break
                symbols = model.symbols(shown=True)
                formula = self._symbols2formula(symbols)
                yield formula
        # with ctl.solve(yield_=True) as handle:
        #     for model in handle:
        #         symbols = model.symbols(shown=True)
        #         formula = self._symbols2formula(symbols)
        #         yield formula
    
    def __str__(self) -> str:
        """Return the ASP program."""
        return self.program.getvalue()