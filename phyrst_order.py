"Main implementation of first order data structures and its operators"

from __future__ import annotations

from enum import Enum
from functools import reduce
from typing import Any, Dict, Iterable, Optional, TypeVar, Union, cast

# TODO: Binary relationships should be writed infix, but other functions and
# relationships should support f(t1, ..., tn) writing format
# TODO: Support functions

Element = TypeVar("Element")
Universe = Iterable[Element]
Interpretation = Dict[str, Any]
Assignment = Dict[str, Element]
ExprType = Enum(
    "ExprType", "CONST VAR FUNC REL EQ AND OR IMPLIES IFF NOT EXISTS FORALL"
)


class Expression:
    "Represents an expression in first order logic, can be part of other expressions"
    expression: str
    exprtype: ExprType
    left: Optional[Expression]
    right: Optional[Expression]
    subexp: Optional[Expression]
    varname: Optional[str]
    quantifier_varname: Optional[str]

    def __init__(
        self,
        expression: str,
        exprtype: ExprType,
        left: Optional[Expression] = None,
        right: Optional[Expression] = None,
        subexp: Optional[Expression] = None,
        varname: Optional[str] = None,
        constname: Optional[str] = None,
        relname: Optional[str] = None,
        quantifier_varname: Optional[str] = None,
    ) -> None:
        self.expression = expression
        self.exprtype = exprtype
        self.left = left
        self.right = right
        self.subexp = subexp
        self.varname = varname
        self.constname = constname
        self.relname = relname
        self.quantifier_varname = quantifier_varname

    def __call__(
        self: Expression,
        universe: Universe,
        interpretation: Interpretation,
        assignment: Assignment,
    ) -> Union[bool, Element]:
        args = universe, interpretation, assignment
        self.left = cast(Expression, self.left)
        self.right = cast(Expression, self.right)
        self.subexp = cast(Expression, self.subexp)
        self.varname = cast(str, self.varname)
        self.constname = cast(str, self.constname)
        self.relname = cast(str, self.relname)

        # -> Element
        if self.exprtype is ExprType.CONST:
            return interpretation[self.constname]
        if self.exprtype is ExprType.VAR:
            return assignment[self.varname]
        if self.exprtype is ExprType.FUNC:
            raise NotImplementedError
        # -> bool
        if self.exprtype is ExprType.EQ:
            return self.left(*args) == self.right(*args)
        if self.exprtype is ExprType.REL:
            return interpretation[self.relname](self.left(*args), self.right(*args))
        if self.exprtype is ExprType.AND:
            return self.left(*args) and self.right(*args)
        if self.exprtype is ExprType.OR:
            return self.left(*args) or self.right(*args)
        if self.exprtype is ExprType.IMPLIES:
            return not self.left(*args) or self.right(*args)
        if self.exprtype is ExprType.IFF:
            return self.left(*args) == self.right(*args)
        if self.exprtype is ExprType.NOT:
            return not self.subexp(*args)
        if self.exprtype is ExprType.EXISTS:

            def f(anyprevious, element):
                a = dict(**assignment)
                a[self.quantifier_varname] = element
                return anyprevious or self.subexp(universe, interpretation, a)

            return reduce(f, universe, False)

        if self.exprtype is ExprType.FORALL:

            def f(allprevious, element):  # type: ignore # pylint: disable=function-redefined
                a = dict(**assignment)
                a[self.quantifier_varname] = element
                return allprevious and self.subexp(universe, interpretation, a)

            return reduce(f, universe, True)

        raise Exception("Invalid semantics reached")

    def __eq__(self, o: Expression) -> Expression:  # type: ignore
        return Expression(f"({self.expression} = {o.expression})", ExprType.EQ, self, o)

    def __le__(self, o: Expression) -> Expression:
        # TODO: Maybe a bit too specific for posets
        return Expression(
            f"({self.expression} <= {o.expression})",
            ExprType.REL,
            self,
            o,
            relname="<=",
        )

    def __and__(self, o: Expression) -> Expression:
        return Expression(
            f"({self.expression} ∧ {o.expression})", ExprType.AND, self, o
        )

    def __or__(self, o: Expression) -> Expression:
        return Expression(f"({self.expression} ∨ {o.expression})", ExprType.OR, self, o)

    def __rshift__(self, o: Expression) -> Expression:
        return Expression(
            f"({self.expression} ⇒ {o.expression})", ExprType.IMPLIES, self, o
        )

    def __pow__(self, o: Expression) -> Expression:
        return Expression(
            f"({self.expression} ⇔ {o.expression})", ExprType.IFF, self, o
        )

    def __invert__(self):
        return Expression(f"¬{self.expression}", ExprType.NOT, subexp=self)

    def exists(self, qvar: Expression) -> Expression:
        "Returns existencially quantified Expression which has self as subexpression"
        assert qvar.exprtype is ExprType.VAR
        return Expression(
            f"∃{qvar.varname}{self.expression}",
            ExprType.EXISTS,
            subexp=self,
            quantifier_varname=qvar.varname,
        )

    def forall(self, qvar: Expression) -> Expression:
        "Returns universally quantified Expression which has self as subexpression"
        assert qvar.exprtype is ExprType.VAR
        return Expression(
            f"∀{qvar.varname}{self.expression}",
            ExprType.FORALL,
            subexp=self,
            quantifier_varname=qvar.varname,
        )

    def __str__(self) -> str:
        return self.expression


const = lambda constname: Expression(constname, ExprType.CONST, constname=constname)
var = lambda varname: Expression(varname, ExprType.VAR, varname=varname)
exists = lambda varname, exp: exp.exists(varname)
forall = lambda varname, exp: exp.forall(varname)
