"Main implementation of first order data structures and its operators"

from __future__ import annotations

from enum import Enum
from functools import reduce
from typing import (
    Any,
    Callable,
    Dict,
    Iterable,
    List,
    Optional,
    Sequence,
    Tuple,
    TypeVar,
    Union,
    cast,
)

Element = TypeVar("Element")
Universe = Iterable[Element]
Interpretation = Dict[str, Any]
Assignment = Dict[str, Element]
ExprType = Enum(
    "ExprType", "EMPTY CONST VAR FUNC REL EQ AND OR IMPLIES IFF NOT EXISTS FORALL"
)


class Type:
    "Defines the names and arities of a first order type"
    constnames: List[str]
    funcnames: List[str]
    relnames: List[str]
    arities: Dict[str, int]

    def __init__(
        self,
        constnames: List[str],
        funcnames: List[str],
        relnames: List[str],
        arities: Dict[str, int],
    ) -> None:
        self.constnames = constnames
        self.funcnames = funcnames
        self.relnames = relnames
        self.arities = arities

        # Arities is suryective over funcnames + relnames
        assert all((name in arities) for name in funcnames + relnames)
        assert all(
            name in funcnames + relnames and arity > 0
            for name, arity in arities.items()
        )

        # All different names
        names = constnames + funcnames + relnames
        assert all(
            name != oname
            for i, name in enumerate(names[:-1])
            for oname in names[i + 1 :]
        )

    @property
    def names(self) -> List[str]:
        "Returns all type names"
        return self.constnames + self.funcnames + self.relnames

    @property
    def name_types(self) -> Iterable[Tuple[str, ExprType]]:
        "Generator that for all names gives a tuple like (name, ExprType)"
        for name in self.names:
            yield (name, self.name_type(name))

    def name_type(self, name: str) -> ExprType:
        "Returns ExprType.CONST/FUNC/REL for a name"
        if name in self.constnames:
            return ExprType.CONST
        if name in self.funcnames:
            return ExprType.FUNC
        if name in self.relnames:
            return ExprType.REL
        raise Exception(f"{name=} is not a valid name for this type")


class Expression:
    "Represents an expression in first order logic, can be part of other expressions"
    expression: str
    exprtype: ExprType
    subexpressions: Sequence[Expression]  # E.g. A & B => subexpressions = [A, B]
    name: Optional[str]  # name of const / rel / func / var / quantified var

    def __init__(
        self,
        expression: str,
        exprtype: ExprType,
        subexpressions: Sequence[Expression] = (),
        name: Optional[str] = None,
    ) -> None:
        self.expression = expression
        self.exprtype = exprtype
        self.subexpressions = subexpressions
        self.name = name

    def __call__(
        self: Expression,
        universe: Universe,
        interpretation: Interpretation,
        assignment: Assignment,
    ) -> Union[bool, Element]:
        args = universe, interpretation, assignment
        self.name = cast(str, self.name)

        subexp = left = right = Expression.empty()
        if len(self.subexpressions) == 2:
            left, right = self.subexpressions
        elif len(self.subexpressions) == 1:
            subexp = self.subexpressions[0]

        # -> Element
        if self.exprtype is ExprType.CONST:
            return interpretation[self.name]
        if self.exprtype is ExprType.VAR:
            return assignment[self.name]
        if self.exprtype is ExprType.FUNC:
            return interpretation[self.name](*[t(*args) for t in self.subexpressions])
        # -> bool
        if self.exprtype is ExprType.EQ:
            return left(*args) == right(*args)
        if self.exprtype is ExprType.REL:
            return interpretation[self.name](*[t(*args) for t in self.subexpressions])
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
                a[self.name] = element
                return anyprevious or subexp(universe, interpretation, a)

            return reduce(f, universe, False)

        if self.exprtype is ExprType.FORALL:

            def f(allprevious, element):  # type: ignore # pylint: disable=function-redefined
                a = dict(**assignment)
                a[self.name] = element
                return allprevious and subexp(universe, interpretation, a)

            return reduce(f, universe, True)

        if self.exprtype is ExprType.EMPTY:
            raise Exception("Trying to evaluate an empty expression")

        raise Exception("Invalid semantics reached")

    def __eq__(self, o: Expression) -> Expression:  # type: ignore
        return Expression(f"({self} = {o})", ExprType.EQ, [self, o])

    def __le__(self, o: Expression) -> Expression:
        # TODO: Maybe a bit too specific for posets
        return Expression(f"({self} ≤ {o})", ExprType.REL, [self, o], "<=")

    def __and__(self, o: Expression) -> Expression:
        return Expression(f"({self} ∧ {o})", ExprType.AND, [self, o])

    def __or__(self, o: Expression) -> Expression:
        return Expression(f"({self} ∨ {o})", ExprType.OR, [self, o])

    def __rshift__(self, o: Expression) -> Expression:
        return Expression(f"({self} ⇒ {o})", ExprType.IMPLIES, [self, o])

    def __pow__(self, o: Expression) -> Expression:
        return Expression(f"({self} ⇔ {o})", ExprType.IFF, [self, o])

    def __invert__(self):
        return Expression(f"¬{self}", ExprType.NOT, [self])

    def exists(self, qvar: Expression) -> Expression:
        "Returns existencially quantified Expression which has self as subexpression"
        assert qvar.exprtype is ExprType.VAR
        return Expression(f"∃{qvar.name}{self}", ExprType.EXISTS, [self], qvar.name)

    def forall(self, qvar: Expression) -> Expression:
        "Returns universally quantified Expression which has self as subexpression"
        assert qvar.exprtype is ExprType.VAR
        return Expression(f"∀{qvar.name}{self}", ExprType.FORALL, [self], qvar.name)

    @staticmethod
    def empty() -> Expression:
        "Returns an object representing an empty expression"
        return Expression("", ExprType.EMPTY)

    # # def __call__(self, *args: Expression) -> Expression:
    # #         assert self.exprtype in [ExprType.FUNC, ExprType.REL]
    # #         assert cantidad de args coincide con nombre de mi func

    @staticmethod
    def expr_mappings(ttype: Type) -> List[Callable]:
        """Returns for each name in the type an object that is a syntax sugar
        for writing first order expressions in python. For FUNCs and RELs
        a function that when evaluated fun(t1, ..., tn) builds the
        appropiate expression. For CONSTs a const expression."""

        mappings: List[Callable] = []
        for name, ntype in ttype.name_types:
            if ntype is ExprType.CONST:
                nconst = Expression(name, ExprType.CONST, name=name)
                mappings.append(nconst)
            elif ntype in [ExprType.FUNC, ExprType.REL]:
                nrelfunc = lambda *subexprs, name=name, ntype=ntype: Expression(
                    f"{name}({', '.join(str(t) for t in subexprs)})",
                    ntype,
                    subexprs,
                    name,
                )
                mappings.append(nrelfunc)
            else:
                raise Exception(f"Invalid {ntype=}")

        return mappings

    def __str__(self) -> str:
        return self.expression


const = lambda constname: Expression(constname, ExprType.CONST, name=constname)
var = lambda varname: Expression(varname, ExprType.VAR, name=varname)
exists = lambda varname, exp: exp.exists(varname)
forall = lambda varname, exp: exp.forall(varname)
