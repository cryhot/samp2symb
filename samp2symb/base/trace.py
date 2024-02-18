#!/usr/bin/env python3
import sys
import pdb
import io
import re
import itertools
import contextlib
from timeit import repeat
from typing import *

class Trace:
    def __init__(self, vector, lassoStart=None, *, intendedEvaluation=None, weight=1):

        self.lengthOfTrace = len(vector)
        self.intendedEvaluation = intendedEvaluation
        if lassoStart is not None:
            self.lassoStart = int(lassoStart)
            if self.lassoStart < 0: self.lassoStart += self.lengthOfTrace
            if self.lassoStart >= self.lengthOfTrace:
                # pdb.set_trace()
                raise Exception(
                    "lasso start = %s is greater than any value in trace (trace length = %s) -- must be smaller" % (
                    self.lassoStart, self.lengthOfTrace))
        else:
            self.lassoStart = None
        assert self.lassoStart is None or self.lengthOfTrace > 0 and self.lassoStart <= self.lengthOfTrace
        self.vector = vector
        self.weight = weight
    
    def __eq__(self, other) -> bool:
        if not isinstance(other, Trace): return NotImplemented
        if self.lassoStart != other.lassoStart: return False
        if self.lengthOfTrace != other.lengthOfTrace: return False
        if any(s!=o for s,o in zip(self.vector, other.vector)): return False
        return True
    
    @property
    def finite(self) -> bool:
        return self.lassoStart is None
    @property
    def infinite(self) -> bool:
        return self.lassoStart is not None
    

    @staticmethod
    def _seq2str(vector:List[Any]) -> str:
        """Return a string representation of the vector."""
        sequence = ';'.join(','.join(f'{int(k)}' for k in t) for t in vector)
        return sequence
    
    @staticmethod
    def _str2seq(sequence:str) -> List[Any]:
        """Parse a string representation of the vector."""
        sequence = sequence.rstrip(';')
        vector = [
            [bool(int(varValue)) for varValue in varsInTimestep.split(',')]
            for varsInTimestep in sequence.split(';')
        ]
        return vector

    def __repr__(self) -> str:
        return repr(self.vector) + "\n" + repr(self.lassoStart) + "\n\n"

    def __str__(self) -> str:
        return self.dumps()
    
    def __iter__(self):
        return itertools.chain(
            self.vector,
            itertools.repeat(self.vector[self.lassoStart:]) if self.infinite else (),
        )

    def dumps(self) -> str:
        string = self._seq2str(self.vector)
        suffix = ''
        if self.infinite: suffix = f'{suffix}{self.lassoStart}'
        if self.weight is not None and self.weight != 1: suffix = f'{suffix}[{self.weight}]'
        if suffix: string = f"{string}::{suffix}"
        return string
    
    @classmethod
    def loads(cls, string:str, **kwargs) -> "Trace":
        """Opposite of `str(trace)`."""
        string = string.strip()
        suffix = ''
        try:
            traceData, suffix = string.split('::')
        except ValueError:
            traceData = string
        match = re.fullmatch(r'(?P<lassoStart>-?\d+)?(?:\[(?P<weight>\d+)])?', suffix)
        if match.group('lassoStart') is not None: kwargs['lassoStart'] = int(match.group('lassoStart'))
        if match.group('weight') is not None: kwargs['weight'] = int(match.group('weight'))
        vector = cls._str2seq(traceData)
        trace = cls(vector, **kwargs)
        return trace


    def nextPos(self, currentPos):
        if currentPos is None:
            return None
        if currentPos == self.lengthOfTrace - 1:
            return self.lassoStart
        else:
            return currentPos + 1

    def futurePos(self, currentPos):
        futurePositions = []
        alreadyGathered = set()
        while currentPos not in alreadyGathered:
            if currentPos is None: break
            futurePositions.append(currentPos)
            alreadyGathered.add(currentPos)
            currentPos = self.nextPos(currentPos)
        # else:
        #     # always add a new one so that all the next-relations are captured
        #     futurePositions.append(currentPos)
        return futurePositions


class PropTrace(Trace):
    """Sequence of subsets of propositions. Appropriate for LTL formulas."""

    def __init__(self, *args, literals=None, **kwargs):
        super().__init__(*args, **kwargs)
        self.numVariables = len(self.vector[0]) if self.vector else None
        if literals == None:
            # pdb.set_trace()
            self.literals = ["x" + str(i) for i in range(self.numVariables)]
        else:
            self.literals = literals


    def evaluate(self, formula):
        """Evaluate a formula on this trace."""
        from .ltl import Formula, DecisionTreeFormula

        if isinstance(formula, Formula):

            nodes = list(set(formula.getAllNodes()))
            self.truthAssignmentTable = {node: [None for _ in range(self.lengthOfTrace)] for node in nodes}

            for i in range(self.numVariables):
                literalFormula = Formula(self.literals[i])

                self.truthAssignmentTable[literalFormula] = [bool(measurement[i]) for measurement in self.vector]

            return self.__truthValue(formula, 0)

        elif isinstance(formula, DecisionTreeFormula):
            truthValue = None
            tree = formula
            while tree is not None:
                truthValue = self.evaluate(tree.label)
                tree = tree.left if truthValue else tree.right
            return truthValue

        else:
            raise NotImplementedError(f"evaluating {type(formula)}")

    def __truthValue(self, formula, timestep):
        if timestep is None:
            return False
        futureTracePositions = self.futurePos(timestep)
        tableValue = self.truthAssignmentTable[formula][timestep]
        if tableValue != None:
            return tableValue
        else:
            label = formula.label
            if label == '&':
                return self.__truthValue(formula.left, timestep) and self.__truthValue(formula.right, timestep)
            elif label == '|':
                return self.__truthValue(formula.left, timestep) or self.__truthValue(formula.right, timestep)
            elif label == '!':
                return not self.__truthValue(formula.left, timestep)
            elif label == '->':
                return not self.__truthValue(formula.left, timestep) or self.__truthValue(formula.right, timestep)
            elif label == '<->':
                return self.__truthValue(formula.left, timestep) == self.__truthValue(formula.right, timestep)
            elif label == 'F':
                return max([self.__truthValue(formula.left, futureTimestep) for futureTimestep in futureTracePositions])
                # return self.__truthValue(formula.left, timestep) or self.__truthValue(formula, self.nextPos(timestep))
            elif label == 'G':
                return min([self.__truthValue(formula.left, futureTimestep) for futureTimestep in futureTracePositions])
                # return self.__truthValue(formula.left, timestep) and not self.__truthValue(formula, self.nextPos(timestep))
            elif label == 'U':
                return max(
                    [self.__truthValue(formula.right, futureTimestep) for futureTimestep in futureTracePositions]) == True \
                       and ( \
                                   self.__truthValue(formula.right, timestep) \
                                   or \
                                   (self.__truthValue(formula.left, timestep) and self.__truthValue(formula,
                                                                                                self.nextPos(timestep))) \
                           )
            elif label == 'X':
                return self.__truthValue(formula.left, self.nextPos(timestep))
            elif label == 'true':
                return True
            elif label == 'false':
                return False
            else:
                raise NotImplementedError(f"evaluation of operator {label!r}")
    
    def to_spot(self) -> "spot.twa":
        """generate an infinite word acceptor."""
        import spot
        miniterms = [
            "&".join(
                ("" if k else "!") + l
                for l,k in zip(self.literals,t)
            )
            for t in self.vector
        ]
        word = ';'.join(itertools.chain(
            miniterms[:self.lassoStart],
            ("cycle{%s}" % ';'.join(miniterms[self.lassoStart:]),),
        ))
        word = spot.parse_word(word)
        return word

    @classmethod
    def from_spot(cls, twa_word:"spot.twa", literals:List[str], *,
        default=False, # used when no explicit value is assigned to a litteral
        **kwargs,
    ) -> "Trace":
        import spot
        if literals is None: raise NotImplementedError()
        vector = []
        for t in itertools.chain(twa_word.prefix, twa_word.cycle):
            t = spot.bdd_format_formula(twa_word.get_dict(), t)
            t = cls._miniterm2props(t, literals, default=default)
            vector.append(t)
        trace = cls(vector,
            lassoStart=len(twa_word.prefix),
            literals=literals,
            **kwargs,
        )
        return trace
    @staticmethod
    def _miniterm2props(miniterm:str, literals:List[str], default=None) -> "List[bool]":
        """Transforms spot minitems in values of propositions."""
        ans = [default for l in literals]
        for t in miniterm.split('&'):
            try:
                if re.match(r'\s*(0|1)\s*', t): continue
                v,l = re.match(r'\s*(!?)\s*(\w+)\s*', t).groups()
            except Exception as e:
                raise RuntimeError(f"{miniterm!r}") from e
            ans[literals.index(l)] = (v!='!')
        return ans

defaultOperators = ['G', 'F', '!', 'U', '&', '|', '->', 'X']



class AlphaTrace(Trace):
    """Sequence of letters from an alphabet."""

    def __init__(self, *args, **kwargs):
        super().__init__(*args, **kwargs)
    
    @staticmethod
    def _seq2str(vector:List[Any]) -> str:
        """Return a string representation of the vector."""
        sequence = ''.join(f'{t}' for t in vector)
        return sequence
    
    @staticmethod
    def _str2seq(sequence:str) -> List[Any]:
        """Parse a string representation of the vector."""
        # sequence = sequence.rstrip()
        # vector = list(sequence.split()[0])
        vector = [
            letter
            for letter in sequence
        ]
        return vector
    

    def evaluate(self, dfa):
        """Evaluate a dfa on this trace."""
        from .dfa import DFA

        if isinstance(dfa, DFA):
            return self in dfa

        else:
            raise NotImplementedError(f"evaluating {type(formula)}")



class Sample():
    "Set of labeled traces."
    # TODO: accept any labels (not just True and False)

    def __init__(self,
        tracesToAccept=None,
        tracesToReject=None,
        *,
        operators=['G', 'F', '!', 'U', '&', '|', '->', 'X'],
        depth=None,
        possibleSolution=None,
        # numVariables=None,
    ):
        self.acceptedTraces = tracesToAccept if tracesToAccept is not None else []
        self.rejectedTraces = tracesToReject if tracesToReject is not None else []
        # self.numVariables = numVariables

        self.operators = operators
        self.depthOfSolution = depth
        self.possibleSolution = possibleSolution
    
    def copy(self):
        return __class__(
            # numVariables=self.numVariables,
            tracesToAccept=self.acceptedTraces[:],
            tracesToReject=self.rejectedTraces[:],
            operators=self.operators,
            depth=self.depthOfSolution,
            possibleSolution=self.possibleSolution,
        )
    
    def extend(self, *other):
        """merge other samples into this one"""
        for o in other:
            assert o.numVariables == self.numVariables
            self.acceptedTraces.extend(o.acceptedTraces)
            self.rejectedTraces.extend(o.rejectedTraces)
    
    def negate(self):
        """Switches pos and neg trajectories"""
        self.acceptedTraces, self.rejectedTraces = self.rejectedTraces, self.acceptedTraces
    
    def __neg__(self): ans = self.copy(); ans.negate(); return ans
    def __iadd__(self, other): self.extend(other); return self
    def __add__(self, other): ans = self.copy(); ans += other; return ans
    def __isub__(self, other): self += (-other); return self
    def __sub__(self, other): return self + (-other)


    def __len__(self):
        return len(self.acceptedTraces) + len(self.rejectedTraces)
    def __bool__(self):
        return len(self) > 0

    def __iter__(self):
        return itertools.chain(self.acceptedTraces, self.rejectedTraces)
    
    def items(self):
        """Iter through pairs of (trace, label)."""
        return itertools.chain(
            zip(self.acceptedTraces, itertools.repeat(True)),
            zip(self.rejectedTraces, itertools.repeat(False)),
        )
    
    def append(self, trace, *, label):
        if label: self.acceptedTraces.append(trace)
        else:     self.rejectedTraces.append(trace)
    
    def clear(self):
        """remove all traces."""
        self.acceptedTraces.clear()
        self.rejectedTraces.clear()

    @property
    def maxLengthOfTraces(self):
        return max((trace.lengthOfTrace for trace in self), default=0)
    
    @property
    def numVariables(self):
        try:
            return next(iter(self)).numVariables
        except StopIteration:
            return None
    
    @property
    def alphabet(self):
        """extracts alphabet from the words/traces provided in the data"""
        alphabet = set()
        for trace in self:
            if isinstance(trace, PropTrace):
                # return trace.literals
                return list(itertools.product((0,1), repeat=trace.numVariables))
            elif isinstance(trace, AlphaTrace):
                alphabet.update(trace.vector)
        return list(alphabet)
    
    @property
    def literals(self):
        for trace in self:
            if isinstance(trace, PropTrace):
                return trace.literals
        return None

    def isFormulaConsistent(self, f):

        # not checking consistency in the case that traces are contradictory
        if f == None:
            return True
        for accTrace in self.acceptedTraces:
            if not accTrace.evaluate(f):
                return False
        for rejTrace in self.rejectedTraces:
            if rejTrace.evaluate(f):
                return False
        return True

    def split(self, filter):
        """ Split the traces in two.
            :param filter: function(trace:Trace, label:bool)->bool
            :return: (filtered_true, filtered_false)
            :rtype: (ExperimentTraces, ExperimentTraces)
        """
        split = dict()
        for label, traces in [
            (True,  self.acceptedTraces),
            (False, self.rejectedTraces),
        ]:
            split[label] = {True: [], False: [],}
            for trace in traces:
                split[label][bool(filter(trace, label))].append(trace)
        ans = []
        for value in (True, False):
            traces = __class__(
                # numVariables=self.numVariables,
                tracesToAccept=split[True][value],
                tracesToReject=split[False][value],
                operators=self.operators,
                depth=self.depthOfSolution,
                possibleSolution=self.possibleSolution,
            )
            ans.append(traces)
        return tuple(ans)


    def splitEval(self, f):
        """ Split the traces accordingly to evaluation.
            :return: (accepted_traces, rejected_traces)
            :rtype: (ExperimentTraces, ExperimentTraces)
        """
        return self.split(lambda t,l: t.evaluate(f))
    def splitCorrect(self, f):
        """ Split the traces accordingly to correctness.
            :return: (classified_traces, misclassified_traces)
            :rtype: (ExperimentTraces, ExperimentTraces)
        """
        return self.split(lambda t,l: t.evaluate(f)==l)

    @property
    def positive(self):
        return __class__(
            # numVariables=self.numVariables,
            tracesToAccept=self.acceptedTraces,
            operators=self.operators,
            depth=self.depthOfSolution,
            possibleSolution=self.possibleSolution,
        )
    @property
    def negative(self):
        return __class__(
            # numVariables=self.numVariables,
            tracesToReject=self.rejectedTraces,
            operators=self.operators,
            depth=self.depthOfSolution,
            possibleSolution=self.possibleSolution,
        )
    @property
    def weight(self):
        return sum(trace.weight for trace in self)

    def get_score(self, f, score='count'):
        good, bad = self.splitCorrect(f)
        if score == 'count':
            return  good.weight / self.weight
        elif score == 'ratio':
            return 0.5 * good.positive.weight / self.positive.weight + 0.5 * good.negative.weight / self.negative.weight
        else:
            msg = f'score={score!r}'
            raise NotImplementedError(msg)

    def get_misclassification(self, f):
        return 1-self.get_score(f, score='count')


    def __repr__(self):
        returnString = ""
        returnString += "accepted traces:\n"
        for trace in self.acceptedTraces:
            returnString += repr(trace)
        returnString += "\nrejected traces:\n"

        for trace in self.rejectedTraces:
            returnString += repr(trace)
        returnString += "depth of solution: " + repr(self.depthOfSolution) + "\n"
        return returnString

    def __str__(self):
        return self.dumps()
    
    def summary(self, *, separator=", ") -> str:
        """return a (one line) summary of this sample."""
        quals = []
        if len(self)==0: pass
        elif all(trace.finite for trace in self): quals.append("finite")
        elif all(trace.infinite for trace in self): quals.append("infinite")
        quals = "".join(qual+" " for qual in quals)
        infos = [
            f"{len(self.positive)}+{len(self.negative)}={len(self)} (pos+neg) {quals}traces",
            
        ]
        if len(self)>0:
            trace1 = next(iter(self))
            if isinstance(trace1, PropTrace):
                infos.extend([
                    f"{len(trace1.literals)} features",
                ])
            infos.extend([
                f"{sum(trace.lengthOfTrace for trace in self)/len(self):.3} timesteps (avg)",
            ])
        if self.possibleSolution is not None:
            if self.depthOfSolution is None:
                infos.append(f"possible solution: {self.possibleSolution}")
            else:
                infos.append(f"possible solution: {self.possibleSolution} (depth={self.depthOfSolution})")
        elif self.depthOfSolution is not None:
            infos.append(f"possible solution: ? (depth={self.depthOfSolution})")
        return separator.join(infos)
    
    def json_summary(self, json_stats=None) -> dict:
        if json_stats is None: json_stats = dict()
        json_stats.update(
            traces = len(self),
            pos_traces = len(self.positive),
            neg_traces = len(self.negative),
        )
        if len(self)==0: pass
        elif all(trace.finite for trace in self): json_stats.update(finite_traces=True)
        elif all(trace.infinite for trace in self): json_stats.update(finite_traces=False)
        if len(self)>0:
            trace1 = next(iter(self))
            if isinstance(trace1, PropTrace):
                json_stats.update(features=len(trace1.literals))
            json_stats.update(avg_timesteps=sum(trace.lengthOfTrace for trace in self)/len(self))
        if self.possibleSolution is not None:
            json_stats.update(possible_solution=str(self.possibleSolution))
        if self.depthOfSolution is not None:
            json_stats.update(possible_solution=self.depthOfSolution)
        return json_stats

    
    def dumps(self) -> str:
        with io.StringIO() as stream:
            self.dump(stream)
            return stream.getvalue()

    def dump(self, dest=sys.stdout, only_traces=False):
        """Write sample to a file or a stream."""
        if isinstance(dest, str): cm = open(dest, "w")
        # else: cm = contextlib.nullcontext(dest)
        else: cm = contextlib.contextmanager(lambda: (yield dest))()
        with cm as tracesFile:
            for accTrace in self.acceptedTraces:
                line = str(accTrace) + "\n"
                tracesFile.write(line)
            tracesFile.write("---\n")
            for rejTrace in self.rejectedTraces:
                line = str(rejTrace) + "\n"
                tracesFile.write(line)
            if only_traces: return
            tracesFile.write("---\n")
            tracesFile.write(','.join(self.operators) + '\n')
            tracesFile.write("---\n")
            # tracesFile.write(str(self.depthOfSolution) + '\n')
            if self.literals is not None:
                tracesFile.write(','.join(str(l) for l in self.literals) + '\n')
            else:
                tracesFile.write(','.join(str(l) for l in self.alphabet) + '\n')
            tracesFile.write("---\n")
            tracesFile.write(str(self.possibleSolution))

    @staticmethod
    def _flieLiteralsStringToVector(v, literals):
        vec = []
        for l in literals:
            if l in v:
                vec.append(1)
            else:
                vec.append(0)
        return vec

    def _flieTraceToTrace(self, tracesString):
        try:
            (initPart, lasso) = tracesString.split("|")
        except ValueError:
            raise Exception("every trace has to have initial part and a lasso part")
        initPart = initPart.split(";")
        lasso = lasso.split(";")
        lassStart = len(initPart)
        traceVector = [self._flieLiteralsStringToVector(v, self.literals) for v in initPart + lasso]
        return Trace(traceVector, lassStart, literals=self.literals)

    def _getLiteralsFromData(self, data):

        for tr in data:
            try:
                (initPart, lasso) = tr.split("|")
            except ValueError:
                raise Exception("every trace has to have initial part and a lasso part")
            initPart = initPart.split(";")
            lasso = lasso.split(";")
            for tmstp in initPart + lasso:
                lits = tmstp.split(",")
                for lit in lits:
                    lit = lit.strip()
                    if not lit == "null" and not lit in self.literals:
                        self.literals.append(lit)

    def readTracesFromFlieJson(self, data):

        positive = data["positive"]
        negative = data["negative"]
        self.literals = []
        try:
            self.literals = data["literals"]
        except KeyError:
            self._getLiteralsFromData(positive)
            self._getLiteralsFromData(negative)

        self.numVariables = len(self.literals)
        try:
            self.operators = data["operators"]
        except KeyError:
            self.operators = defaultOperators

        for tr in positive:
            trace = self._flieTraceToTrace(tr)
            self.acceptedTraces.append(trace)
        for tr in negative:
            trace = self._flieTraceToTrace(tr)
            self.rejectedTraces.append(trace)

    @classmethod
    def loads(cls, string:str, *args, **kwargs):
        """Read sample from a string."""
        with io.StringIO(string) as stream:
            return cls.load(stream, *args, **kwargs)
    
    @classmethod
    def load(cls, source, type=PropTrace):
        """Read sample from a file or a stream."""
        if isinstance(source, str): cm = open(source, "r")
        # else: cm = contextlib.nullcontext(source)
        else: cm = contextlib.contextmanager(lambda: (yield source))()
        with cm as stream:
            accepted_traces, rejected_traces = [], []
            kwargs = dict()
            readingMode = 0

            if issubclass(type, PropTrace):
                kwargs.setdefault('operators', defaultOperators)
            if issubclass(type, AlphaTrace):
                pass

            operators = None
            for line in stream:
                lassoStart = None
                if '---' in line:
                    readingMode += 1
                else:
                    if readingMode == 0:
                        trace = type.loads(line)
                        trace.intendedEvaluation = True
                        accepted_traces.append(trace)

                    elif readingMode == 1:
                        trace = type.loads(line)
                        trace.intendedEvaluation = False
                        rejected_traces.append(trace)

                    elif readingMode == 2:
                        kwargs['operators'] = [s.strip() for s in line.split(',')]

                    elif readingMode == 3:
                        pass
                        # self.depthOfSolution = int(line)
                    elif readingMode == 4:
                        possibleSolution = line.strip()
                        if possibleSolution.lower() == "none":
                            kwargs['possibleSolution'] = None
                        elif issubclass(type, PropTrace):
                            from .ltl import Formula
                            kwargs['possibleSolution'] = Formula.loads(possibleSolution)
                        elif issubclass(type, AlphaTrace):
                            kwargs['possibleSolution'] = None
                            # TODO: read automata

                    else:
                        break

            sample = cls(accepted_traces, rejected_traces, **kwargs)

            for trace in sample:
                if issubclass(type, PropTrace) and trace.numVariables != sample.numVariables:
                    raise Exception("number of variables not consistent")

            return sample


    def generator_dfa_in_batch_advanced(self, 
        formula=None,
        filename='generated.words', 
        num_traces=(5,5),
        length_traces=None, 
        alphabet = ['p','q','r'], 
        length_range=(5,15),
        is_words=True,
        operators=['G', 'F', '!', 'U', '&','|', 'X']
    ):
        """fills """
        from .ltl import Formula
        from .dfa import DFA

        if is_words:
            word2trace = lambda word, alphabet: AlphaTrace([letter for letter in word])
        else:
            word2trace = lambda word, alphabet: PropTrace([list(letter) for letter in word], literals=alphabet)

        total_num_positives = num_traces[0]
        total_num_negatives = num_traces[1]
        print(num_traces)
        ver = True

        # Generating positive words
        print("Generating positive words")
        if isinstance(formula, Formula): ltldfa = formula.to_dfa(literals=alphabet)
        elif isinstance(formula, DFA): ltldfa = formula
        else: raise TypeError("formula")
        ltldfa_list = []

        ### Some super optimization
        
        final_states = ltldfa.final_states
        for state in ltldfa.final_states:
            new_dfa = DFA(ltldfa.init_state, [state], ltldfa.transitions)
            new_dfa.generate_num_accepting_words(length_range[1])
            ltldfa_list.append(new_dfa)

        num_accepted_words_length = {}
        num_words_per_length = {}
        for i in range(length_range[0], length_range[1]+1):
            num_accepted_words_length[i] = sum([dfa.number_of_words[(dfa.init_state,i)] for dfa in ltldfa_list])
        
        total_accepted_words = sum(num_accepted_words_length.values())
        for i in range(length_range[0], length_range[1]):
            num_words_per_length[i] = int((num_accepted_words_length[i]/total_accepted_words)*total_num_positives)

        num_words_per_length[length_range[1]] = total_num_positives - sum(num_words_per_length.values())

        for i in range(length_range[0], length_range[1]+1):
            num_words_per_dfa = {}
            non_empty_dfas = []
            for dfa in ltldfa_list:
                if dfa.number_of_words[(dfa.init_state, i)] != 0:
                    non_empty_dfas.append(dfa)

            num_remaining_words = num_words_per_length[i] - len(non_empty_dfas)
            for dfa in non_empty_dfas[:-1]:
                num_words_per_dfa[dfa] = 1 + int((dfa.number_of_words[(dfa.init_state,i)]/num_accepted_words_length[i])*num_remaining_words)
                try:
                    new_words = dfa.generate_random_words_in_batch((i,i), num_words_per_dfa[dfa])
                    for word in new_words:
                        trace = word2trace(word, alphabet)
                        self.append(trace, label=True)
                        assert(ltldfa.is_word_in(word)==True)
                except Exception: pass
            
            dfa = ltldfa_list[-1]
            num_words_per_dfa[dfa] = num_words_per_length[i] - sum(num_words_per_dfa.values())
            try:
                new_words = dfa.generate_random_words_in_batch((i,i), num_words_per_dfa[dfa])
                for word in new_words:
                    trace = word2trace(word, alphabet)
                    self.append(trace, label=True)
                    assert(ltldfa.is_word_in(word)==True)
            except Exception: pass

        # Generating negative words
        print("Generating negative words")
        ltldfa_c = ltldfa.complement()
        ltldfa_list = []

        ### Some super optimization
        
        for state in ltldfa_c.final_states:
            new_dfa = DFA(ltldfa_c.init_state, [state], ltldfa_c.transitions)
            new_dfa.generate_num_accepting_words(length_range[1])
            ltldfa_list.append(new_dfa)

        num_accepted_words_length = {}
        num_words_per_length = {}
        for i in range(length_range[0], length_range[1]+1):
            num_accepted_words_length[i] = sum([dfa.number_of_words[(dfa.init_state,i)] for dfa in ltldfa_list])
        
        total_accepted_words = sum(num_accepted_words_length.values())
        for i in range(length_range[0], length_range[1]):
            num_words_per_length[i] = int((num_accepted_words_length[i]/total_accepted_words)*total_num_positives)

        num_words_per_length[length_range[1]] = total_num_negatives - sum(num_words_per_length.values())
        print(num_words_per_length.values())


        for i in range(length_range[0], length_range[1]+1):
            num_words_per_dfa = {}
            non_empty_dfas = []
            for dfa in ltldfa_list:
                if dfa.number_of_words[(dfa.init_state, i)] != 0:
                    non_empty_dfas.append(dfa)

            num_remaining_words = num_words_per_length[i] - len(non_empty_dfas)
            for dfa in non_empty_dfas[:-1]:
                num_words_per_dfa[dfa] = 1 + int((dfa.number_of_words[(dfa.init_state,i)]/num_accepted_words_length[i])*num_remaining_words)
                try:
                    new_words = dfa.generate_random_words_in_batch((i,i), num_words_per_dfa[dfa])
                    for word in new_words:
                        trace = word2trace(word, alphabet)
                        self.append(trace, label=False)
                        assert(ltldfa.is_word_in(word)==False)
                except Exception: pass
            
            dfa = ltldfa_list[-1]
            num_words_per_dfa[dfa] = num_words_per_length[i] - sum(num_words_per_dfa.values())
            try:
                new_words = dfa.generate_random_words_in_batch((i,i), num_words_per_dfa[dfa])
                for word in new_words:
                    trace = word2trace(word, alphabet)
                    self.append(trace, label=False)
                    assert(ltldfa.is_word_in(word)==False)
            except Exception: pass
            

        # self.alphabet = alphabet
        # self.letter2pos = {alphabet[i]:i for i in range(len(alphabet))}
        self.operators = operators
        self.possibleSolution = formula
        self.dump(filename)
