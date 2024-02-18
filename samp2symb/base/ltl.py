#!/usr/bin/env python3
import pdb
import re
import contextlib
from collections import deque
import lark

import typing
from typing import *
if False: # for type checking
    import spot

symmetric_operators = ['&', '|', '<->']
binary_operators = ['&', '|', 'U', '->', '<->']
unary_operators = ['X', 'F', 'G', '!']
constants = ['true', 'false']
class SimpleTree:
    def __init__(self, label = "dummy"):
        self.left = None
        self.right = None
        self.label = label
        self.lb = None
        self.ub = None

    def __hash__(self):
        return hash((self.label, self.left, self.right))

    def __eq__(self, other):
        if not isinstance(other, __class__):
            return False
        else:
            return self.label == other.label and self.left == other.left and self.right == other.right

    def __ne__(self, other):
        return not self == other

    def _isLeaf(self):
        return self.right == None and self.left == None

    def _addLeftChild(self, child):
        if child == None:
            return
        if type(child) is str:
            child = SimpleTree(child)
        self.left = child

    def _addRightChild(self, child):
        if type(child) is str:
            child = SimpleTree(child)
        self.right = child

    def addChildren(self, leftChild = None, rightChild = None):
        self._addLeftChild(leftChild)
        self._addRightChild(rightChild)


    def addChild(self, child):
        self._addLeftChild(child)

    def getAllNodes(self):
        leftNodes = []
        rightNodes = []

        if self.left != None:
            leftNodes = self.left.getAllNodes()
        if self.right != None:
            rightNodes = self.right.getAllNodes()
        return [self] + leftNodes + rightNodes

    def getAllLabels(self):
        if self.left != None:
            leftLabels = self.left.getAllLabels()
        else:
            leftLabels = []

        if self.right != None:
            rightLabels = self.right.getAllLabels()
        else:
            rightLabels = []
        return [self.label] + leftLabels + rightLabels

    def getSize(self):
        "Get the size of the formula tree (not the formula DAG)."
        size = 1
        if self.left != None:
            size += self.left.getSize()
        if self.right != None:
            size += self.right.getSize()
        return size
    
    @property
    def size(self):
        """Size of the formula tree (not the formula DAG).
        To get the size of the DAG, use len(set(formula.getAllNodes())).
        """
        return self.getSize()

    def getDepth(self):
        "Get the depth of the formula tree."
        depth = 0
        if self.left != None:
            depth = max(depth, 1 + self.left.getDepth())
        if self.right != None:
            depth = max(depth, 1 + self.right.getDepth())
        return depth
    
    @property
    def depth(self):
        "Depth of the formula tree."
        return self.getDepth()


    def __repr__(self):
        if self.left == None and self.right == None:
            return self.label

        # the (not enforced assumption) is that if a node has only one child, that is the left one
        elif self.left != None and self.right == None:
            return self.label + '(' + self.left.__repr__() + ')'

        elif self.left != None and self.right != None:
            return self.label + '(' + self.left.__repr__() + ',' + self.right.__repr__() + ')'


class Formula(SimpleTree):

    def __init__(self, formulaArg = "dummyF"):

        if not isinstance(formulaArg, str):
            self.label = formulaArg[0]
            self.left = formulaArg[1]
            try:
                self.right = formulaArg[2]
            except IndexError:
                self.right = None
        else:
            super().__init__(formulaArg)

    def __lt__(self, other):

        if self.getDepth() < other.getDepth():
            return True
        elif self.getDepth() > other.getDepth():
            return False
        else:
            if self._isLeaf() and other._isLeaf():
                return self.label < other.label

            if self.left != other.left:
                return self.left < other.left

            if self.right is None:
                return False
            if other.right is None:
                return True
            if self.right != other.right:
                return self.right < other.right

            else:
                return self.label < other.label


    def __invert__(self): return Formula(['!', self])
    def __and__(self, other): return Formula(['&', self, other])
    def __or__(self, other): return Formula(['|', self, other])
    def __rshift__(self, other): return Formula(['->', self, other])
    def __lshift__(self, other): return Formula(['->', other, self])

    @classmethod
    def normalize(cls, f):
        """normalization in an incomplete method to eliminate equivalent formulas"""

        if f is None:
            return None
        if f._isLeaf():
            return Formula([f.label, f.left, f.right])
        fLeft = Formula.normalize(f.left)
        fRight = Formula.normalize(f.right)

        if fLeft.label == 'true':
            if f.label in ['|', 'F', 'G', 'X']:
                return Formula('true')
            if f.label in ['&', '->', '<->']:
                return Formula.normalize(fRight)
            if f.label == '!':
                return Formula('false')
            if f.label == 'U':
                return Formula.normalize(Formula(['F', fRight, None]))

        if fLeft.label == 'false':
            if f.label in ['->', '!']:
                return Formula['true']
            if f.label in ['&', 'F', 'G', 'X']:
                return Formula['false']
            if f.label in ['|', 'U']:
                return Formula.normalize(fRight)
            if f.label in ['<->']:
                return Formula.normalize(Formula(['!', fRight, None]))

        if not fRight is None:
            if fRight.label == 'true':
                if f.label in ['|', '->', 'U']:
                    return Formula('true')
                if f.label in ['&', '<->']:
                    return Formula.normalize(fLeft)

            if fRight.label == 'false':
                if f.label in []:
                    return Formula['true']
                if f.label in ['&', 'U']:
                    return Formula['false']
                if f.label in ['|']:
                    return Formula.normalize(fLeft)
                if f.label in ['->', '<->']:
                    return Formula.normalize(Formula(['!', fLeft, None]))

        # elimiting p&p and similar
        if fLeft == fRight:
            if f.label in ['&', 'U', '|']:
                return Formula.normalize(fLeft)
            if f.label in ['->', '<->']:
                return Formula('true')

        # eliminating Fp U p and !p U p
        if f.label == 'U':
            if fLeft.label == 'F' or fLeft.label == '!':
                fLeftLeft = Formula.normalize(fLeft.left)
                if fLeftLeft == fRight:
                    return Formula.normalize(Formula(['F', fLeftLeft]))
            if fRight.label == 'F':
                fRightLeft = Formula.normalize(fRight.left)
                if fRightLeft == fLeft:
                    return fRight

        if f.label == 'F' and fLeft.label == 'F':
            return fLeft

        # if there is p | q, don't add q | p
        if f.label in symmetric_operators and not fLeft < fRight:
            return Formula([f.label, fRight, fLeft])

        return Formula([f.label, fLeft, fRight])


    @classmethod
    def convertTextToFormula(cls, formulaText):
        """Opposite of __str__()"""
        f = Formula()
        try:
            formula_parser = lark.Lark(r"""
                ?formula: _binary_expression
                        | _unary_expression
                        | constant
                        | variable
                _binary_expression.9: op_binary "(" formula "," formula ")"
                _unary_expression.9: op_unary "(" formula ")"
                constant.8: op_false | op_true
                variable.1: /[a-zA-Z][a-zA-Z0-9]*/
                ?op_unary: op_not | op_eventually | op_always | op_next
                ?op_binary: op_and | op_or | op_implies | op_equiv | op_until
                op_false: "false" | "0" | "⊥"
                op_true: "true" | "1" | "⊤"
                op_not: "!" | "~" | "¬"
                op_and: "&" | "&&" | "∧"
                op_or: "|" | "||" | "∨"
                op_implies: "->" | ">" | "→"
                op_equiv: "<->" | "=" | "↔"
                op_eventually: "F" | "◊"
                op_always: "G" | "□"
                op_until: "U"
                op_next: "X" | "○"
                %import common.SIGNED_NUMBER
                %import common.WS
                %ignore WS
            """, start = 'formula')

            tree = formula_parser.parse(formulaText)
            #print(tree.pretty())

        except Exception as err:
            raise ValueError(f"can't parse formula {formulaText!r}") from err

        f = TreeToFormula().transform(tree)
        return f

    def prettyPrint(self, top=False):
        if top is True:
            lb = ""
            rb = ""
        else:
            lb = "("
            rb = ")"
        if self._isLeaf():
            return self.label
        if self.label in unary_operators:
            return lb + self.label +" "+ self.left.prettyPrint() + rb
        if self.label in binary_operators:
            return lb + self.left.prettyPrint() +" "+  self.label +" "+ self.right.prettyPrint() + rb

    @classmethod
    def convertPrettyToFormula(cls, formulaText):

        f = Formula()
        try:
            formula_parser = lark.Lark(r"""
                ?formula: _binary_expression
                        | _unary_expression
                        | constant
                        | variable
                        | "(" formula ")"
                _binary_expression.9: formula op_binary formula
                _unary_expression.9: op_unary formula
                constant.8: op_false | op_true
                variable.1: /[a-zA-Z][a-zA-Z0-9]*/
                ?op_unary: op_not | op_eventually | op_always | op_next
                ?op_binary: op_and | op_or | op_implies | op_equiv | op_until
                op_false: "false" | "0" | "⊥"
                op_true: "true" | "1" | "⊤"
                op_not: "!" | "~" | "¬"
                op_and: "&" | "&&" | "∧"
                op_or: "|" | "||" | "∨"
                op_implies: "->" | ">" | "→"
                op_equiv: "<->" | "=" | "↔"
                op_eventually: "F" | "◊"
                op_always: "G" | "□"
                op_until: "U"
                op_next: "X" | "○"
                %import common.SIGNED_NUMBER
                %import common.WS
                %ignore WS
            """, start = 'formula')

            tree = formula_parser.parse(formulaText)
            #print(tree.pretty())

        except Exception as err:
            raise ValueError(f"can't parse formula {formulaText!r}") from err

        f = TreeToFormula().transform(tree)
        return f

    @classmethod
    def loads(cls, text:str) -> "Formula":
        "Deserialize a string to a formula."
        try:
            return cls.convertTextToFormula(text)
        except ValueError as err:
            return cls.convertPrettyToFormula(text)
    
    def dumps(self) -> str:
        "Serialize a string to a formula. Uses infix notation by default."
        return self.prettyPrint()


    def getAllVariables(self):
        allNodes = list(set(self.getAllNodes()))
        return [ node for node in allNodes if node._isLeaf() == True ]

    @property
    def literals(self) -> 'List[str]':
        return sorted(
            node.label
            for node in set(self.getAllNodes())
            if node._isLeaf() == True
            if node.label not in ['true','false']
        )

    def getNumberOfSubformulas(self):
        return len(self.getSetOfSubformulas())

    def getSetOfSubformulas(self):
        if self.left == None and self.right == None:
            return [repr(self)]
        leftValue = []
        rightValue = []
        if self.left != None:
            leftValue = self.left.getSetOfSubformulas()
        if self.right != None:
            rightValue = self.right.getSetOfSubformulas()
        return list(set([repr(self)] + leftValue + rightValue))
    
    def accepting_word(self, *, finite=None, literals=None):
        """Returns a minimal trace that is accepted.
        """
        from .trace import PropTrace
        if literals is None: literals = self.literals
        if finite in [True, None]: # finite trace
            a = self.to_dfa(literals)
            trace = a.accepting_word()
            if trace is not None: return PropTrace(tuple(trace), literals=literals)
        if finite in [False, None]: # infinite trace
            a = self.to_spot().translate()
            trace = a.accepting_word()
            if trace is not None: return PropTrace.from_spot(trace, literals=literals)
        return None

    def rejecting_word(self, *, finite=None, literals=None):
        """Returns a minimal trace that is rejected.
        """
        return (~self).accepting_word(finite=finite, literals=literals)
    
    def intersecting_word(self, other, *, finite=None, literals=None):
        """Returns a minimal trace that is accepted by both formulas.
        """
        from .trace import PropTrace
        if literals is None: literals = self.literals
        if finite in [True, None]: # finite trace
            a1 = self.to_dfa(literals)
            a2 = other.to_dfa(literals)
            trace = a1.intersecting_word(a2)
            if trace is not None: return PropTrace(tuple(trace), literals=literals)
        if finite in [False, None]: # infinite trace
            a1 = self.to_spot().translate()
            a2 = other.to_spot().translate()
            trace = a1.intersecting_word(a2)
            if trace is not None: return PropTrace.from_spot(trace, literals=literals)
        return None
    
    @classmethod
    def from_spot(cls, formula:"spot.formula") -> "Formula":
        """Convert this spot LTL formula into a samb2symb LTL formula.
        Assumes that it is an LTL formula (over infinite traces).
        """
        import spot
        formula = f"{formula:p}"
        if formula == "0": formula = "false"
        if formula == "1": formula = "true"
        formula = cls.convertPrettyToFormula(formula)
        return formula
    
    def to_spot(self) -> "spot.formula":
        """Convert this LTL formula into it's spot counterpart.
        Assumes that it is an LTL formula (over infinite traces).
        To get Büchi automaton, use for example:
        >>> f.to_spot().translate('Buchi','Deterministic','Complete','StateBasedAcceptance')
        """
        import spot
        formula = spot.formula(self.prettyPrint())
        return formula
    
    def to_dfa(self, literals=None) -> "samp2symb.base.dfa.DFA":
        """Translate this LTLf formula to a DFA.
        Assumes that it is an LTLf formula (over finite traces).
        """
        from .dfa import DFA, ltl2dfa
        if literals is None: literals = self.literals
        letter2pos = {x:i for i,x in enumerate(literals)}
        dfa = ltl2dfa(self, letter2pos, is_word=False)
        return dfa



@lark.v_args(inline=True)
class TreeToFormula(lark.Transformer):
    @lark.v_args(inline=False)
    def formula(self, formulaArgs):
        if not isinstance(formulaArgs[0], str): formulaArgs.insert(0, formulaArgs.pop(1))
        return Formula(formulaArgs)
    def variable(self, varName):
        return Formula([str(varName), None, None])
    def constant(self, arg):
        return Formula(str(arg))
        # if str(arg) == "true":
        #     connector = "|"
        # elif str(arg) == "false":
        #     connector = "&"
        # return Formula([connector, Formula(["x0", None, None]), Formula(["!", Formula(["x0", None, None] ), None])])

    def op_false(self): return 'false'
    def op_true(self): return 'true'
    def op_not(self): return '!'
    def op_and(self): return '&'
    def op_or(self): return '|'
    def op_implies(self): return '->'
    def op_equiv(self): return '<->'
    def op_eventually(self): return 'F'
    def op_always(self): return 'G'
    def op_until(self): return 'U'
    def op_next(self): return 'X'



class DecisionTreeFormula(SimpleTree):

    def is_terminal(self):
        return self in {DT_LEAF_TRUE,DT_LEAF_FALSE}

    def getSize(self):
        if self.is_terminal():
            return 0
        if self.label == "...":
            return float("inf")
        return super().getSize()

    def getDepth(self):
        if self.is_terminal():
            return 0
        if self.label == "...":
            return float("inf")
        return super().getDepth()

    def __repr__(self):
        left_repr = f"{self.left!r}" if self.left!=None else ""
        right_repr = f"{self.right!r}" if self.right!=None else ""
        return f"{self.label};{left_repr};{right_repr}"

    @classmethod
    def convertTextToFormula(cls, formulaTreeText):
        """Opposite of prettyPrint"""
        formulaTextQueue = deque()
        for formulaText in formulaTreeText.split(";"):
            if not formulaText: # leaf
                formulaTextQueue.append(None)
            else:
                try:
                    formula = Formula.convertTextToFormula(formulaText)
                except ValueError:
                    formula = formulaText
                formulaTextQueue.append(formula)
        formulaTree = cls.convertQueueToFormula(formulaTextQueue)
        assert not formulaTextQueue, "no nodes should be left over"
        return formulaTree
    @classmethod
    def convertQueueToFormula(cls, formulaTextQueue):
        """Pop subformulas from the queue to reconstruct"""
        formula = formulaTextQueue.popleft()
        if formula is None:
            return None
        node = cls(label=formula)
        node.left = cls.convertQueueToFormula(formulaTextQueue)
        node.right = cls.convertQueueToFormula(formulaTextQueue)
        return node

    def prettyPrint(self, top=False):
        """Opposite of convertTextToFormula"""
        left_repr = self.left.prettyPrint(top) if self.left!=None else ""
        right_repr = self.right.prettyPrint(top) if self.right!=None else ""
        label_repr = self.label.prettyPrint(top) if isinstance(self.label, SimpleTree) else self.label
        return f"{label_repr};{left_repr};{right_repr}"

    def flattenToFormula(self):
        Any = "*"
        left_case = Any
        if self.left in {DT_LEAF_TRUE,None}: left_case = True
        if self.left in {DT_LEAF_FALSE}: left_case = False
        right_case = Any
        if self.right in {DT_LEAF_TRUE}: right_case = True
        if self.right in {DT_LEAF_FALSE,None}: right_case = False
        case = left_case, right_case

        if case == (Any  , Any  ):
            return Formula(["|",
                Formula(["&", self.label, self.left.flattenToFormula()]),
                Formula(["&", Formula(["!", self.label]), self.right.flattenToFormula()]),
            ])
        if case == (Any  , False):
            return Formula(["&", self.label, self.left.flattenToFormula()])
        if case == (True , Any  ):
            return Formula(["|", self.label, self.right.flattenToFormula()])
        if case == (True , False):
            return self.label
        if case == (Any  , True ):
            return Formula(["|", Formula(["!", self.label]), self.left.flattenToFormula()])
        if case == (False, Any  ):
            return Formula(["&", Formula(["!", self.label]), self.right.flattenToFormula()])
        if case == (False, True ):
            return Formula(["!", self.label])
        if case == (True , True ):
            return Formula("true")
        if case == (False, False):
            return Formula("false")



    def trimPseudoNodes(self):
        """return a copy where pseudo leaves such as "..." are trimed.
        Return the tree itself if no change is made."""
        if not isinstance(self.label, Formula):
            return None
        left, right = None, None
        if self.left is not None: left = self.left.trimPseudoNodes()
        if self.right is not None: right = self.right.trimPseudoNodes()
        if left is self.left and right is self.right:
            return self
        result = self.__class__(label=self.label)
        result.left, result.right = left, right
        return result

    def writeDotFile(self, file, traces=None):
        if isinstance(file, str): cm = open(file, "w")
        # else: cm = contextlib.nullcontext(file)
        else: cm = contextlib.contextmanager(lambda: (yield file))()
        with cm as stream:
            stream.write('digraph Tree {\n')
            stream.write('\tnode [shape=box, style="filled", color="black"] ;\n')
            DecisionTreeFormula._writeDotNode(self, stream, indent='\t', traces=traces, alltraces=traces)
            stream.write('}\n')

    @staticmethod
    def _writeDotNode(node, stream, name="", indent='', traces=None, alltraces=None):
        if alltraces is None: alltraces = traces
        infos = []
        style = ["filled"]
        fillcolor = "#ffffff"
        formula = None

        if node is None:
            # if name.endswith("T"):
            #     infos.append("⊤")
            #     fillcolor = "#37a600"
            #     style.append("dashed")
            #     formula = Formula('true')
            # elif name.endswith("F"):
            #     infos.append("⊥")
            #     fillcolor = "#e6300c"
            #     style.append("dashed")
            #     formula = Formula('false')
            return
        elif not isinstance(node.label, Formula):
            infos.append(node.label)
            fillcolor = "#9940ec"
        else:
            infos.append(node.label.prettyPrint())
            formula = node.label
            if node==DT_LEAF_TRUE:
                fillcolor = "#37a600"
                style.append("dashed")
            if node==DT_LEAF_FALSE:
                fillcolor = "#e6300c"
                style.append("dashed")


        if traces is not None:
            infos.append(f"traces = {len(traces.positive)} + {len(traces.negative)} = {len(traces)}")
            traces_percentage = p = len(traces)/len(alltraces)
            if formula is not None:
                if len(traces):
                    misclassification = m = traces.get_misclassification(formula)
                    # fillcolor=f"#{int(m*255):02x}{int((1-m)*255):02x}{0:02x}"
                    fillcolor=f"#{int((p*m+1-p)*255):02x}{int((1-p*m)*255):02x}{int((1-p)*255):02x}"
                    infos.append(f"misclass = {misclassification*100:.2f}%")
                else:
                    # fillcolor=f"#{191:02x}{191:02x}{191:02x}"
                    fillcolor=f"#{255:02x}{255:02x}{255:02x}"
            else:
                fillcolor=f"#{int(255-(255-153)*p):02x}{int(255-(255-64)*p):02x}{int(255-(255-236)*p):02x}"
            #TODO: use adequate library for mixing colors

        opts = dict(
            label=r"\n".join(infos),
            style=",".join(style),
            fillcolor=fillcolor,
        )
        opts = ', '.join(f'{k}="{v}"' for k,v in opts.items())
        stream.write(f'{indent}{name or "root"} [{opts}] ;\n')
        if name.endswith("T"):
            stream.write(f'{indent}{name[:-1] or "root"} -> {name} [labeldistance=2.5, labelangle=45, headlabel="True"] ;\n')
        elif name.endswith("F"):
            stream.write(f'{indent}{name[:-1] or "root"} -> {name} [labeldistance=2.5, labelangle=-45, headlabel="False"] ;\n')

        if node is not None and formula is not None:
            accTraces, rejTraces = None, None
            if traces is not None:
                accTraces, rejTraces = traces.splitEval(formula)
            __class__._writeDotNode(node.left,  stream, name=name+"T", indent=indent+"\t", traces=accTraces, alltraces=alltraces)
            __class__._writeDotNode(node.right, stream, name=name+"F", indent=indent+"\t", traces=rejTraces, alltraces=alltraces)

DT_LEAF_TRUE = DecisionTreeFormula(Formula("true"))
DT_LEAF_FALSE = DecisionTreeFormula(Formula("false"))
