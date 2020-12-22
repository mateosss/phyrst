"Varied tests for the phyrst_order functionality"

# TODO: These tests may be too specific for posets as they use the <= operator

from phyrst_order import (
    Assignment,
    Expression,
    ExprType,
    Interpretation,
    Universe,
    const,
    exists,
    forall,
    var,
)


def test_raw_expressions(
    universe: Universe, interpretation: Interpretation, assignment: Assignment
) -> bool:
    "Tests expressions constructed from the ground up as regular classes"
    sems = universe, interpretation, assignment
    e_z = Expression("0", ExprType.CONST, constname="0")
    e_x0 = Expression("x0", ExprType.VAR, varname="x0")
    e_x1 = Expression("x1", ExprType.VAR, varname="x1")
    e_x2 = Expression("x2", ExprType.VAR, varname="x2")
    e_zeqz = Expression("0 = 0", ExprType.EQ, e_z, e_z)
    e_x1eqz = Expression("x1 = 0", ExprType.EQ, e_x1, e_z)
    e_x1eqx2 = Expression("x1 = x2", ExprType.EQ, e_x1, e_x2)
    e_x1leqx2 = Expression("x1 <= x2", ExprType.REL, e_x1, e_x2, relname="<=")
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
    "Tests expressions generated through operator chaining"
    sems = universe, interpretation, assignment
    leq = interpretation["<="]
    e_z = Expression("0", ExprType.CONST, constname="0")
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
    assert e_complex2(*sems) == (not (x1 == 0) and leq(0, x2))
    assert e_complex3(*sems) == (not (leq(x0, x1) and leq(x1, x2)) or leq(x0, x2))
    assert e_complex4(*sems) == ((x1 == x2) == (x2 == x1))
    assert e_complex5(*sems) == (not (not (x1 != x2) or (leq(x1, x2) or leq(x2, x1))))
    return True


def test_quantification(
    universe: Universe, interpretation: Interpretation, assignment: Assignment
) -> bool:
    "Tests quantified expressions for a poset, in particular posets and related properties"
    sems = universe, interpretation, assignment
    x = var("x")
    y = var("y")
    z = var("z")
    w = var("w")
    zero = const("0")
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
    return True
