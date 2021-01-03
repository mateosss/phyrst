"Various tests for the phyrst module functionality"

import itertools as it
from typing import Tuple, cast

from phyrst import (
    Assignment,
    Element,
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

Semantics = Tuple[Universe, Interpretation, Assignment]


def vchain_posets_semantics_example() -> Tuple[Semantics, Semantics]:
    "Returns the semantics of a V shaped poset and a chain poset both with three elements"

    def leqchain(rhs: Element, lfs: Element) -> bool:  # Order for chain poset
        reflexiveness = [(elem, elem) for elem in universe]
        return (rhs, lfs) in reflexiveness + [(0, 1), (1, 2), (0, 2)]

    def leqv(rhs: Element, lfs: Element) -> bool:  # Order for V poset
        reflexiveness = [(elem, elem) for elem in universe]
        return (rhs, lfs) in reflexiveness + [(0, 1), (0, 2)]

    universe: Universe = [0, 1, 2]
    interpretation_v: Interpretation = {"<=": leqv, "0": 0}
    interpretation_chain: Interpretation = {"<=": leqchain, "0": 0}
    assignment: Assignment = {"x1": 1, "x0": 0, "x2": 2}

    chain_sems = universe, interpretation_chain, assignment
    v_sems = universe, interpretation_v, assignment

    return v_sems, chain_sems


def _test_raw_expressions(
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


def _test_operator_expressions(
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


def _test_quantification(
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


def test_raw_expressions():
    "Perform some raw expressions tests on particular posets"
    v_sems, chain_sems = vchain_posets_semantics_example()
    _test_raw_expressions(*v_sems)
    _test_raw_expressions(*chain_sems)


def test_operator_expressions():
    "Perform some operator expressions tests on particular posets"
    v_sems, chain_sems = vchain_posets_semantics_example()
    _test_operator_expressions(*v_sems)
    _test_operator_expressions(*chain_sems)


def test_quantification():
    "Perform some quantification tests on particular posets"
    v_sems, chain_sems = vchain_posets_semantics_example()
    _test_quantification(*v_sems)
    _test_quantification(*chain_sems)


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
    lattice_axioms = [sisbound, slowbnd, iisbound, iuppbnd]

    min0 = forall(x, s(zero, x) == x)
    max1 = forall(x, s(one, x) == one)
    scomplement = forall(x, s(x, c(x)) == one)
    icomplement = forall(x, i(x, c(x)) == zero)
    dist1 = forall(x, forall(y, forall(z, i(x, s(y, z)) == s(i(x, y), i(x, z)))))
    boole_axioms = [min0, max1, scomplement, icomplement, dist1]

    axioms = poset_axioms + lattice_axioms + boole_axioms
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


def test_model_exploration():
    "Looks for examples of certain models of up to three elements in a given theory"
    ttype = Type([], [], ["r"], {"r": 2})
    theory = Theory([], ttype)
    r = Expression.expr_mappings(ttype)[0]
    x, y = var("x"), var("y")
    phi = exists(x, forall(y, r(x, y)))
    psi = forall(y, exists(x, r(x, y)))

    for l in [1, 2, 3]:  # universe sizes
        relpairs = tuple(it.product(range(l), range(l)))  # possible 2-element relations
        for k in range(len(relpairs) + 1):  # k: amount of pairs in the relationship
            rels = it.combinations(relpairs, k)  # relationships with k pairs
            for rel in rels:
                interpretation = {"r": lambda x, y, rel=rel: (x, y) in rel}
                model = Model(theory, range(l), interpretation)
                satisfies_phi = model.eval(phi)
                satisfies_psi = model.eval(psi)
                if satisfies_psi and not satisfies_phi:
                    pass  # Example found. Do something like print its r relationship
                assert not satisfies_phi or satisfies_psi  # phi => psi
    return True
