"Varied tests for the phyrst_order functionality"

# TODO: These tests may be too specific for posets as they use the <= operator

from typing import cast

from phyrst_order import (
    Assignment,
    Expression,
    ExprType,
    Interpretation,
    Model,
    Theory,
    Type,
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
    e_z = Expression("0", ExprType.CONST, name="0")
    e_x0 = Expression("x0", ExprType.VAR, name="x0")
    e_x1 = Expression("x1", ExprType.VAR, name="x1")
    e_x2 = Expression("x2", ExprType.VAR, name="x2")
    e_zeqz = Expression("0 = 0", ExprType.EQ, [e_z, e_z])
    e_x1eqz = Expression("x1 = 0", ExprType.EQ, [e_x1, e_z])
    e_x1eqx2 = Expression("x1 = x2", ExprType.EQ, [e_x1, e_x2])
    e_x1leqx2 = Expression("x1 <= x2", ExprType.REL, [e_x1, e_x2], "<=")
    e_complex = Expression("x1 = 0 or x1 <= x2", ExprType.OR, [e_x1eqz, e_x1leqx2])

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
    e_z = Expression("0", ExprType.CONST, name="0")
    e_x0 = Expression("x0", ExprType.VAR, name="x0")
    e_x1 = Expression("x1", ExprType.VAR, name="x1")
    e_x2 = Expression("x2", ExprType.VAR, name="x2")

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


def test_nary_names() -> bool:
    "Tests expressions with n-ary functions"
    universe: Universe = range(42, 53)
    assignment: Assignment = {}
    interpretation: Interpretation = {
        "0": min(universe),
        "clamp": lambda x, a, b: max(a, min(x, b)),
        "max": max,
        "min": min,
        "<=": lambda x, y: x <= y,
    }
    arities = {"clamp": 3, "max": 2, "min": 2, "<=": 2}
    sems = universe, interpretation, assignment

    ttype = Type(["0"], ["clamp", "max", "min"], ["<="], arities)
    o, clamp, maxx, minn, leq = Expression.expr_mappings(ttype)
    zero: Expression = cast(Expression, o)

    x, y, z = var("x"), var("y"), var("z")
    minworks = forall(x, forall(y, (minn(x, y) <= x) & (minn(x, y) <= y)))
    maxworks = forall(x, forall(y, (x <= maxx(x, y)) & leq(y, maxx(x, y))))
    clampworks = forall(x, forall(y, forall(z, clamp(x, y, z) == maxx(y, minn(x, z)))))
    clampbounds = forall(
        x,
        forall(
            y, forall(z, (y <= z) >> ((clamp(x, y, z) <= z) & (y <= clamp(x, y, z))))
        ),
    )
    zmin = forall(x, zero <= x)
    assert minworks(*sems)
    assert maxworks(*sems)
    assert clampworks(*sems)
    assert clampbounds(*sems)
    assert zmin(*sems)

    return True


def test_boole_algebra_model() -> bool:
    "This test builds a boolean algebra model from the ground up and checks some of its properties"

    # Type definition
    constnames = ["0", "1"]
    funcnames = ["s", "i", "c"]
    relnames = ["<="]
    arities = {"s": 2, "i": 2, "c": 1, "<=": 2}
    ttype = Type(constnames, funcnames, relnames, arities)
    zero, one, s, i, c, leq = Expression.expr_mappings(ttype)

    # Theory definition
    x, y, z = var("x"), var("y"), var("z")
    reflexivity = forall(x, x <= x)
    transitivity = forall(x, forall(y, forall(z, ((x <= z) & (z <= y)) >> (x <= y))))
    antisimetry = forall(x, forall(y, ((x <= y) & (y <= x)) >> (x == y)))
    poset_axioms = [reflexivity, transitivity, antisimetry]
    sisbound = forall(x, forall(y, (x <= s(x, y)) & (y <= s(x, y))))
    slowbnd = forall(x, forall(y, forall(z, ((x <= z) & (y <= z)) >> (s(x, y) <= z))))
    iisbound = forall(x, forall(y, (i(x, y) <= x) & (i(x, y) <= y)))
    iuppbnd = forall(x, forall(y, forall(z, ((z <= x) & (z <= y)) >> (z <= i(x, y)))))
    ret_axioms = [sisbound, slowbnd, iisbound, iuppbnd]
    min0 = forall(x, s(zero, x) == x)
    max1 = forall(x, s(one, x) == one)
    scomplement = forall(x, s(x, c(x)) == one)
    icomplement = forall(x, i(x, c(x)) == zero)
    dist1 = forall(x, forall(y, forall(z, i(x, s(y, z)) == s(i(x, y), i(x, z)))))
    boole_axioms = [min0, max1, scomplement, icomplement, dist1]
    axioms = poset_axioms + ret_axioms + boole_axioms
    theory = Theory(axioms, ttype)

    # Model definition
    universe: Universe = [set(), {1}, {2}, {3}, {1, 2}, {1, 3}, {2, 3}, {1, 2, 3}]
    interpretation: Interpretation = {
        "0": set(),
        "1": {1, 2, 3},
        "s": lambda x, y: x | y,
        "i": lambda x, y: x & y,
        "c": lambda x: x ^ {1, 2, 3},
        "<=": lambda x, y: x.issubset(y),
    }
    model = Model(theory, universe, interpretation)

    # Check valid sentences
    dist2 = forall(x, forall(y, forall(z, s(x, i(y, z)) == i(s(x, y), s(x, z)))))
    assert model.eval(dist2)

    # Define an assignment and its variables
    assignment: Assignment = {"x1": {1}, "x2": {2}, "x12": {1, 2}}
    x1, x2, x12 = var("x1"), var("x2"), var("x12")

    # Check valid formulas given an assignment
    phi = s(x1, x2) == x12
    psi = leq(x1, x12)
    assert model.eval(phi, assignment)
    assert model.eval(psi, assignment)

    # Check the value of a term given an assignment
    t = i(x1, s(x1, x2))
    assert model.eval(t, assignment) == {1}

    return True
