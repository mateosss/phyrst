# Phyrst

A first order syntax evaluator without dependencies using and abusing of
python's operator overloading.

Each of the following operators is overloaded so as to compose a new
`Expression` from other subexpressions.

- `==`: Equality
- `&`: Conjunction
- `|`: Disjunction
- `>>`: Implication
- `**`: Equivalence (*iff*)
- `~`: Negation
- `forall`: Universal quantification
- `exists`: Existential quantification
- `!=`, `<=`, `<`, `>=`, `>`: Other non essential useful relationships.

For expressing the sentence `∀𝑥 ∀𝑦 𝑥 ≤ 𝑦 ∨ 𝑦 ≤ 𝑥` you would write:

```py
x, y = var("x"), var("y")
sentence = forall(x, forall(y, (x <= y) | (y <= x)))
```

And you can evaluate its truth value in a given model with:

```py
# Example model of a chain poset with three elements and a minimum

ttype = Type(
  constnames=["0"], funcnames=[],
  relnames=["<="], arities={"<=": 2}
)
theory = Theory(axioms=poset_axioms, ttype)
model = Model(
  theory, universe=[0, 1, 2],
  interpretation={"0": 0, "<=": lambda x, y: x <= y}
)
assert model.eval(sentence, assignment={"x1": 1})
```

Another more thorough and interesting example of defining and evaluating
expressions over a boolean algebra can be found on the
[`test_boole_algebra()`](https://github.com/mateosss/phyrst/blob/d057a99cad8dd3be015874629cc8dd9cbc222bee/tests.py#L173)
test.

*The name `phyrst` comes from **first** order, the greek letter φ
(**phi**) usually used for representing first order formulas and the **py**
prefix for python.*
