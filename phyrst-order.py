from __future__ import annotations

from enum import Enum
from functools import reduce
from typing import Any, Dict, List, Optional, Union, cast

Element = int
Universe = List[Element]
Interpretation = Dict[str, Any]
Assignment = Dict[str, Element]
ExprType = Enum(
    "ExprType", "ZEROCONST VAR LEQREL EQ AND OR IMPLIES IFF NOT EXISTS FORALL"
)


class Expression:
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
        quantifier_varname: Optional[str] = None,
    ) -> None:
        self.expression = expression
        self.exprtype = exprtype
        self.left = left
        self.right = right
        self.subexp = subexp
        self.varname = varname
        self.quantifier_varname = quantifier_varname

    def __call__(
        self: Expression,
        universe: List[Element],
        interpretation: Dict[str, Any],
        assignment: Dict[str, Element],
    ) -> Union[bool, Element]:
        args = universe, interpretation, assignment
        self.left = cast(Expression, self.left)
        self.right = cast(Expression, self.right)
        self.subexp = cast(Expression, self.subexp)
        self.varname = cast(str, self.varname)

        # -> Element
        if self.exprtype is ExprType.ZEROCONST:
            return interpretation["0"]
        if self.exprtype is ExprType.VAR:
            return assignment[self.varname]
        # -> bool
        if self.exprtype is ExprType.EQ:
            return self.left(*args) == self.right(*args)
        if self.exprtype is ExprType.LEQREL:
            return interpretation["<="](self.left(*args), self.right(*args))
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

            def f(exists, element):
                a = dict(**assignment)
                a[self.quantifier_varname] = element
                return exists or self.subexp(universe, interpretation, a)

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
        return Expression(
            f"({self.expression} <= {o.expression})", ExprType.LEQREL, self, o
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
        assert qvar.exprtype is ExprType.VAR
        return Expression(
            f"∃{qvar.varname}{self.expression}",
            ExprType.EXISTS,
            subexp=self,
            quantifier_varname=qvar.varname,
        )

    def forall(self, qvar: Expression) -> Expression:
        assert qvar.exprtype is ExprType.VAR
        return Expression(
            f"∀{qvar.varname}{self.expression}",
            ExprType.FORALL,
            subexp=self,
            quantifier_varname=qvar.varname,
        )

    def __str__(self) -> str:
        return self.expression


zeroconst = lambda: Expression("0", ExprType.ZEROCONST)
var = lambda varname: Expression(varname, ExprType.VAR, varname=varname)
exists = lambda varname, exp: exp.exists(varname)
forall = lambda varname, exp: exp.forall(varname)


def test_raw_expressions(
    universe: Universe, interpretation: Interpretation, assignment: Assignment
) -> bool:
    sems = universe, interpretation, assignment
    e_z = Expression("0", ExprType.ZEROCONST)
    e_x0 = Expression("x0", ExprType.VAR, varname="x0")
    e_x1 = Expression("x1", ExprType.VAR, varname="x1")
    e_x2 = Expression("x2", ExprType.VAR, varname="x2")
    e_zeqz = Expression("0 = 0", ExprType.EQ, e_z, e_z)
    e_x1eqz = Expression("x1 = 0", ExprType.EQ, e_x1, e_z)
    e_x1eqx2 = Expression("x1 = x2", ExprType.EQ, e_x1, e_x2)
    e_x1leqx2 = Expression("x1 <= x2", ExprType.LEQREL, e_x1, e_x2)
    e_complex = Expression("x1 = 0 or x1 <= x2", ExprType.OR, e_x1eqz, e_x1leqx2)

    x0: int = assignment["x0"]
    x1: int = assignment["x1"]
    x2: int = assignment["x2"]
    assert e_z(*sems) == 0
    assert e_x0(*sems) == x0
    assert e_x1(*sems) == x1
    assert e_x2(*sems) == x2
    assert e_zeqz(*sems) == (0 == 0)
    assert e_x1eqz(*sems) == (x1 == 0)
    assert e_x1eqx2(*sems) == (x1 == x2)
    assert e_x1leqx2(*sems) == interpretation["<="](x1, x2)
    assert e_complex(*sems) == (x1 == 0 or interpretation["<="](x1, x2))

    return True


def test_operator_expressions(
    universe: Universe, interpretation: Interpretation, assignment: Assignment
) -> bool:
    sems = universe, interpretation, assignment
    leq = interpretation["<="]
    e_z = Expression("0", ExprType.ZEROCONST)
    e_x0 = Expression("x0", ExprType.VAR, varname="x0")
    e_x1 = Expression("x1", ExprType.VAR, varname="x1")
    e_x2 = Expression("x2", ExprType.VAR, varname="x2")

    e_zeqz = e_z == e_z
    e_x1eqz = e_x1 == e_z
    e_x1eqx2 = e_x1 == e_x2
    e_x1leqx2 = e_x1 <= e_x2
    e_complex1 = (e_x1 == e_z) | (e_x1 <= e_x2)
    e_complex2 = ~(e_x1 == e_z) & (e_z <= e_x2)
    e_complex3 = ((e_x0 <= e_x1) & (e_x1 <= e_x2)) >> (e_x0 <= e_x2)
    e_complex4 = (e_x1 == e_x2) ** (e_x2 == e_x1)
    e_complex5 = ~(~(e_x1 == e_x2) >> ((e_x1 <= e_x2) | (e_x2 <= e_x1)))

    x0: int = assignment["x0"]
    x1: int = assignment["x1"]
    x2: int = assignment["x2"]
    assert e_z(*sems) == 0
    assert e_x0(*sems) == x0
    assert e_x1(*sems) == x1
    assert e_x2(*sems) == x2
    assert e_zeqz(*sems) == (0 == 0)
    assert e_x1eqz(*sems) == (x1 == 0)
    assert e_x1eqx2(*sems) == (x1 == x2)
    assert e_x1leqx2(*sems) == leq(x1, x2)
    assert e_complex1(*sems) == (x1 == 0 or leq(x1, x2))
    assert e_complex2(*sems) == ((not (x1 == 0)) and leq(0, x2))
    assert e_complex3(*sems) == ((not (leq(x0, x1) and leq(x1, x2))) or leq(x0, x2))
    assert e_complex4(*sems) == ((x1 == x2) == (x2 == x1))
    assert e_complex5(*sems) == (not ((not (x1 != x2)) or (leq(x1, x2) or leq(x2, x1))))
    return True


def test_quantification(
    universe: Universe, interpretation: Interpretation, assignment: Assignment
) -> bool:
    sems = universe, interpretation, assignment
    x = var("x")
    y = var("y")
    z = var("z")
    w = var("w")
    zero = zeroconst()
    reflexiveness = forall(x, x <= x)
    transitivity = forall(
        x,
        forall(
            y,
            forall(z, (((x <= y) & (y <= z)) >> (x <= z))),
        ),
    )
    antisimetry = forall(x, forall(y, (((x <= y) & (y <= x)) >> (x == y))))
    zeromin = forall(x, zero <= x)
    onlythree = exists(
        x,
        exists(
            y,
            exists(
                z,
                (
                    (~(x == y) & ~(x == z) & ~(y == z))
                    & forall(w, (w == x) | (w == y) | (w == z))
                ),
            ),
        ),
    )
    assert reflexiveness(*sems)
    assert transitivity(*sems)
    assert antisimetry(*sems)
    assert zeromin(*sems)
    assert onlythree(*sems)


def main() -> None:
    def leqchain(rhs: Element, lfs: Element) -> bool:  # Order for chain poset
        reflexiveness = [(elem, elem) for elem in universe]
        return (rhs, lfs) in reflexiveness + [(0, 1), (1, 2), (0, 2)]

    def leqv(rhs: Element, lfs: Element) -> bool:  # Order for V poset
        reflexiveness = [(elem, elem) for elem in universe]
        return (rhs, lfs) in reflexiveness + [(0, 1), (0, 2)]

    universe: List[Element] = [0, 1, 2]
    interpretation_v = {"<=": leqv, "0": 0}
    interpretation_chain = {"<=": leqchain, "0": 0}
    assignment: Dict[str, Element] = {"x1": 1, "x0": 0, "x2": 2}
    chain_sems = universe, interpretation_chain, assignment
    v_sems = universe, interpretation_v, assignment

    test_raw_expressions(*v_sems)
    test_raw_expressions(*chain_sems)

    test_operator_expressions(*v_sems)
    test_operator_expressions(*chain_sems)

    test_quantification(*v_sems)
    test_quantification(*chain_sems)

    x, y, z = var("x"), var("y"), var("z")
    custom_expression = forall(x, forall(y, (x <= y) | (y <= x)))
    print(f"[V]\t𝔸⊨{custom_expression.expression}[𝑎⃗] ≡ {custom_expression(*v_sems)}")
    print(
        f"[Chain]\t𝔹⊨{custom_expression.expression}[𝑎⃗] ≡ {custom_expression(*chain_sems)}"
    )


if __name__ == "__main__":
    main()
