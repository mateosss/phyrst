"Main implementation of first order data structures and its operators"

from __future__ import annotations

from enum import Enum
from functools import reduce
from typing import Any, Dict, Iterable, List, Optional, TypeVar, Union, cast

# TODO: Binary relationships should be writed infix, but other functions and
# relationships should support f(t1, ..., tn) writing format
# TODO: Support functions

Element = TypeVar("Element")
Universe = Iterable[Element]
Interpretation = Dict[str, Any]
Assignment = Dict[str, Element]
ExprType = Enum(
    "ExprType", "EMPTY CONST VAR FUNC REL EQ AND OR IMPLIES IFF NOT EXISTS FORALL"
)


class Expression:
    "Represents an expression in first order logic, can be part of other expressions"
    expression: str
    exprtype: ExprType
    subexpressions: Optional[List[Expression]]
    varname: Optional[str]
    quantifier_varname: Optional[str]

    def __init__(
        self,
        expression: str,
        exprtype: ExprType,
        subexpressions: Optional[List[Expression]] = None,
        varname: Optional[str] = None,
        constname: Optional[str] = None,
        relname: Optional[str] = None,
        funcname: Optional[str] = None,
        quantifier_varname: Optional[str] = None,
    ) -> None:
        self.expression = expression
        self.exprtype = exprtype
        self.subexpressions = subexpressions
        self.varname = varname
        self.constname = constname
        self.relname = relname
        self.funcname = funcname
        self.quantifier_varname = quantifier_varname

    def __call__(
        self: Expression,
        universe: Universe,
        interpretation: Interpretation,
        assignment: Assignment,
    ) -> Union[bool, Element]:
        args = universe, interpretation, assignment
        self.varname = cast(str, self.varname)
        self.constname = cast(str, self.constname)
        self.relname = cast(str, self.relname)
        self.funcname = cast(str, self.funcname)

        subexp = left = right = Expression.empty()
        if self.subexpressions:
            self.subexpressions = cast(List[Expression], self.subexpressions)
            if len(self.subexpressions) == 2:
                left, right = self.subexpressions
            elif len(self.subexpressions) == 1:
                subexp = self.subexpressions[0]
            else:
                raise Exception("Invalid subexpressions count")

        # -> Element
        if self.exprtype is ExprType.CONST:
            return interpretation[self.constname]
        if self.exprtype is ExprType.VAR:
            return assignment[self.varname]
        if self.exprtype is ExprType.FUNC:
            # TODO: Support for n-ary functions
            return interpretation[self.funcname](left(*args), right(*args))
        # -> bool
        if self.exprtype is ExprType.EQ:
            return left(*args) == right(*args)
        if self.exprtype is ExprType.REL:
            # TODO: Support for n-ary relations
            return interpretation[self.relname](left(*args), right(*args))
        if self.exprtype is ExprType.AND:
            return left(*args) and right(*args)
        if self.exprtype is ExprType.OR:
            return left(*args) or right(*args)
        if self.exprtype is ExprType.IMPLIES:
            return not left(*args) or right(*args)
        if self.exprtype is ExprType.IFF:
            return left(*args) == right(*args)
        if self.exprtype is ExprType.NOT:
            return not subexp(*args)
        if self.exprtype is ExprType.EXISTS:

            def f(anyprevious, element):
                a = dict(**assignment)
                a[self.quantifier_varname] = element
                return anyprevious or subexp(universe, interpretation, a)

            return reduce(f, universe, False)

        if self.exprtype is ExprType.FORALL:

            def f(allprevious, element):  # type: ignore # pylint: disable=function-redefined
                a = dict(**assignment)
                a[self.quantifier_varname] = element
                return allprevious and subexp(universe, interpretation, a)

            return reduce(f, universe, True)

        if self.exprtype is ExprType.EMPTY:
            raise Exception("Trying to evaluate an empty expression")

        raise Exception("Invalid semantics reached")

    def __eq__(self, o: Expression) -> Expression:  # type: ignore
        return Expression(
            f"({self.expression} = {o.expression})", ExprType.EQ, [self, o]
        )

    def __le__(self, o: Expression) -> Expression:
        # TODO: Maybe a bit too specific for posets
        return Expression(
            f"({self.expression} <= {o.expression})",
            ExprType.REL,
            [self, o],
            relname="<=",
        )

    def __and__(self, o: Expression) -> Expression:
        return Expression(
            f"({self.expression} ∧ {o.expression})", ExprType.AND, [self, o]
        )

    def __or__(self, o: Expression) -> Expression:
        return Expression(
            f"({self.expression} ∨ {o.expression})", ExprType.OR, [self, o]
        )

    def __rshift__(self, o: Expression) -> Expression:
        return Expression(
            f"({self.expression} ⇒ {o.expression})", ExprType.IMPLIES, [self, o]
        )

    def __pow__(self, o: Expression) -> Expression:
        return Expression(
            f"({self.expression} ⇔ {o.expression})", ExprType.IFF, [self, o]
        )

    def __invert__(self):
        return Expression(f"¬{self.expression}", ExprType.NOT, [self])

    def exists(self, qvar: Expression) -> Expression:
        "Returns existencially quantified Expression which has self as subexpression"
        assert qvar.exprtype is ExprType.VAR
        return Expression(
            f"∃{qvar.varname}{self.expression}",
            ExprType.EXISTS,
            [self],
            quantifier_varname=qvar.varname,
        )

    def forall(self, qvar: Expression) -> Expression:
        "Returns universally quantified Expression which has self as subexpression"
        assert qvar.exprtype is ExprType.VAR
        return Expression(
            f"∀{qvar.varname}{self.expression}",
            ExprType.FORALL,
            [self],
            quantifier_varname=qvar.varname,
        )

    @staticmethod
    def empty() -> Expression:
        "Returns an object representing an empty expression"
        return Expression("", ExprType.EMPTY)

    def __str__(self) -> str:
        return self.expression


const = lambda constname: Expression(constname, ExprType.CONST, constname=constname)
var = lambda varname: Expression(varname, ExprType.VAR, varname=varname)
exists = lambda varname, exp: exp.exists(varname)
forall = lambda varname, exp: exp.forall(varname)
