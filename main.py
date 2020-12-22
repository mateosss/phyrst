"This is a runnable usage of phyrst_order data types"

from phyrst_order import Assignment, Element, Interpretation, Universe, forall, var
from tests import (
    test_nary_names,
    test_operator_expressions,
    test_quantification,
    test_raw_expressions,
)


def main() -> None:
    "Runs tests through two three-element posets. A V-like poset and a chain poset"

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

    test_raw_expressions(*v_sems)
    test_raw_expressions(*chain_sems)

    test_operator_expressions(*v_sems)
    test_operator_expressions(*chain_sems)

    test_quantification(*v_sems)
    test_quantification(*chain_sems)

    x, y = var("x"), var("y")
    custom_expression = forall(x, forall(y, (x <= y) | (y <= x)))
    print(f"[V]\t𝔸⊨{custom_expression.expression}[𝑎⃗] ≡ {custom_expression(*v_sems)}")
    print(
        f"[Chain]\t𝔹⊨{custom_expression.expression}[𝑎⃗] ≡ {custom_expression(*chain_sems)}"
    )

    test_nary_names()


if __name__ == "__main__":
    main()
