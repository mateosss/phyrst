# Phyrst Order

A quick and dirty first order syntax evaluator using and abusing of python's
operator overloading. Made for fun, may be a bit rough on the edges.

- `==`: Equality
- `&`: Conjunction
- `|`: Disjunction
- `>>`: Implication
- `**`: Equivalence (*iff*)
- `~`: Negation
- `forall`: Universal quantification
- `exists`: Existential quantification
- `<=`: Partial order. It should be generalized outside of the Expression class

For expressing the sentence `∀𝑥 ∀𝑦 𝑥 ≤ 𝑦 ∨ 𝑦 ≤ 𝑥` you would write:
```py
x, y = var("x"), var("y")
sentence = forall(x, forall(y, (x <= y) | (y <= x)))
```

And you can evaluate its truth value in a given model with:
```py
# Example model of a chain poset with three elements and a minimum
universe = [0, 1, 2]
interpretation = {"<=": lambda x, y: x <= y, "0": 0}
assignment = {"x0": 0, "x1": 1, "x2": 2}
truth: bool = sentence(universe, interpretation, assignment)
```
