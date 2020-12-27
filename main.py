"The only file intended to run. If you don't get an error it means all tests have passed"

from phyrst import forall, var
from phyrst_test import (
    test_boole_algebra_model,
    test_model_exploration,
    test_nary_names,
    test_operator_expressions,
    test_quantification,
    test_raw_expressions,
    vchain_posets_semantics_example,
)


def main() -> None:
    "Runs all tests and some more."

    test_raw_expressions()
    test_operator_expressions()
    test_quantification()
    test_nary_names()
    test_boole_algebra_model()
    test_model_exploration()

    # A quick check on total order without defining a type nor theory nor model
    v_sems, chain_sems = vchain_posets_semantics_example()
    x, y = var("x"), var("y")
    totally_ordered = forall(x, forall(y, (x <= y) | (y <= x)))
    assert totally_ordered(*chain_sems) and not totally_ordered(*v_sems)
    print(f"[V]\t𝔸⊨{totally_ordered}[𝑎⃗] ≡ {totally_ordered(*v_sems)}")
    print(f"[Chain]\t𝔹⊨{totally_ordered}[𝑎⃗] ≡ {totally_ordered(*chain_sems)}")


if __name__ == "__main__":
    main()
