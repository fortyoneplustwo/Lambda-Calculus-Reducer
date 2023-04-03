# Description
A lambda calculus reducer in GNU Smalltalk.

# Features
* **de Bruijn notation**\
The `toDeBruijn` method converts a non-de-Bruijn-indexed expression to a de-Bruijn-indexed one, and both
returns the de-Bruijn-indexed expression and sets the internal expression to it.
* **Applicative Order Evaluation**\
The `aoe` method performs a single reduction step using applicative order evaluation on the expression, and
returns the reduced version. It should also update the internal expression, so that if `aoe` is called repeatedly,
multiple steps of reduction are taken.
* **Normal Order Reduction**\
The `nor` and `nor:` methods behave like `aoe` and `aoe:`, but using normal order reduction instead of applicative
order evaluation. Like `aoe` and `aoe:`, they may mutate the expression, or create a new one.
* **η-reduction**\
The `eta` and `eta:` methods behave like `aoe` and `aoe:` or `nor` and `nor:`, but using η-reduction instead of β-reduction.
Reduce the leftmost, innermost η-reducible expression.

# Motivation
To really understand how Lambda Calculus works, why not implement it using a purely object-oriented language?\

# Demonstration
```
st> | x s l |
st> x := LambdaParser parse: '(\mul.\two.mul two two) (\m.\n.\f.m(n f)) (\f.\x.f (f x))'.
(((\mul.(\two.((mul two) two))) (\m.(\n.(\f.(m (n f)))))) (\f.(\x.(f (f x)))))
st> l := Lambda new: x.
a Lambda
st> l aoe.
((\two.(((\m.(\n.(\f.(m (n f))))) two) two)) (\f.(\x.(f (f x)))))
st> l aoe.
(((\m.(\n.(\f.(m (n f))))) (\f.(\x.(f (f x))))) (\f.(\x.(f (f x)))))
st> l aoe.
((\n.(\f.((\f.(\x.(f (f x)))) (n f)))) (\f.(\x.(f (f x)))))
st> x := l aoe.
(\f.((\f.(\x.(f (f x)))) ((\f.(\x.(f (f x)))) f)))
st> x toDeBruijn.
(\.((\.(\.(2 (2 1)))) ((\.(\.(2 (2 1)))) 1)))
st> l aoe.
nil
st> x := LambdaParser parse: '(\mul.\two.mul two two) (\m.\n.\f.m(n f)) (\f.\x.f (f x))'.
(((\mul.(\two.((mul two) two))) (\m.(\n.(\f.(m (n f)))))) (\f.(\x.(f (f x)))))
st> l := Lambda new: x.
a Lambda
st> x := l aoe: 1000.
(\f.((\f.(\x.(f (f x)))) ((\f.(\x.(f (f x)))) f)))
st> s := x displayString.
'(\f.((\f.(\x.(f (f x)))) ((\f.(\x.(f (f x)))) f)))'
st> x toDeBruijn.
(\.((\.(\.(2 (2 1)))) ((\.(\.(2 (2 1)))) 1)))
```
# Credits
Documentation (features and demonstration above) and lambda.st written by Prof. Gregor Richards for CS442.
