Bounded Relative Finder 
=====

This package provides an algorithm for quickly finding something like "nearest
neighbors" according to a particular distance function.

It is a simplified but slightly more abstract version of the SymSpell
spell-check algorithm, for similar distance functions.

This article describes SymSpell: [1000x Faster Spelling Correction algorithm
(2012)](https://wolfgarbe.medium.com/1000x-faster-spelling-correction-algorithm-2012-8701fcd87a5f).

The Distance Function
-----

The SymSpell spell-check algorithm, in its core, is an algorithm taking a term
and a dictionary of words and returning the set of words in the dictionary that
are within a particular distance of the input term, according to some distance
function.  The algorithm purports to filter according to the unweighted
[Levenshtein](https://en.wikipedia.org/wiki/Levenshtein_distance) and (optimal
string alignment variation of the)
[Levenshtein-Damerau](https://en.wikipedia.org/wiki/Damerau%E2%80%93Levenshtein_distance)
edit distances when configured. The distance function which the core of the
SymSpell spell-check algorithm considers is different, sometimes called the
unrestricted Levenshtein-Damerau distance.  A definition of it follows:

We define the covering relation `<|`: `x <| y` only holds iff `y` can be
obtained from `x` by a single-character insertion.

We define the partial order `<=`: `<=` is the transitive-reflexive closure of
the covering relation `<|`.

We define the distance function `d(x, y)`: `x` and `y` have at least one
greatest lower bound `a` according to `<=`; this is any string from which one
can obtain `x` and `y` by inserting zero or more characters and which has the
greatest possible length. 

`d(x, y)` is, equivalently:

1. The maximum of `length(x) - length(a)` and `length(y) - length(a)`.  This is
equivalent to the edit distance between `x` and `y` with the allowed edits
being deletions, insertions, replacements, and *arbitrary transpositions* of
characters, sometimes called the unrestricted Levenshtein-Damerau distance.

2. Let `Card(e, f)` be the cardinality, or number of elements, in each chain
from `e` to `f`.  `d(x, y)` is the maximum of `Card(a, x) - 1` and `Card(a, y -
1)`. 

The generalized algorithm essentially arises from the knowledge that this
algorithm and distance function are useful for other similarly-defined partial
orders.

Generalization
-----

A poset is *lower semimodular* iff whenever `w` covers `x` and `y`, there
exists `z` such that `x` and `y` both cover `z`. This is true of the above
poset; if `w` covers `x` and `y`, it can be obtained from both `x` and `y` by a
single-character insertion. This implies that `x` and `y` are each themselves
the result of a single-character insertion into a common ancestor `z`.

Any lower semimodular poset satisfies the *Jordan-Dedekind chain condition*,
that for any interval `I` in the poset, all maximal chains in `I` have the same
cardinality. This justifies us above in the second definition of the distance
function when we pretend that `a` is a single element, because we only use the
length of the chain to `a` and none of its other properties.

By [Proposition 6](https://arxiv.org/pdf/1307.0244.pdf), the distance function
`d` defined as above on any lower semimodular poset satisfies the triangle
inequality, making it a metric, and making bounded relative finder a bounded
near-neighbor search algorithm with respect to this metric.

In addition, under this condition, a similar distance function which results
from adding the lengths of the two chains rather than taking the maximum, also
satisfies the triangle equality by [Proposition
5](https://arxiv.org/pdf/1307.0244.pdf).  In the case of the previously-defined
partial order on strings, this latter distance function is the Levenshtein edit
distance. The former distance function is the edit distance when inserts,
deletes, replacements and arbitrary transpositions are the allowed edits, sometimes
called the unrestricted Levenshtein-Damerau distance.

The generalization made by bounded relative finder is to any "delete" operator
(which we call a shrink operator) `shrink :: a -> [a]`. Usually, for this
generalization to be well-behaved, `x <| y = elem x (shrink y)` is the covering
relation of a lower semimodular poset. Stating this a slightly different way,
the condition is that 

```
elem x (shrink z) && elem y (shrink z) && y /= z
``` 

implies

```
not (null (intersect (shrink x) (shrink y))
```

Any such shrink operator we call a "triangular" shrink operator.

Algorithm
-----

Bounded relative finder proceeds much the same way as the
SymSpell algorithm with the exception that "deletes" are abstracted over.

There are two steps: the first is to build what is in SymSpell a "delete
dictionary", here called the "shrink dictionary", and the second is to query
it. The shrink dictionary can be reused for multiple queries over the same
dictionary.

Building the shrink dictionary proceeds exactly the same as in SymSpell; each
value in the original dictionary is shrunk as far as the user desires, and each
such shrunken value's hash is added to the shrink dictionary, with a list of
pointers to the original values.

Similarly, to query the dictionary, the user provides the shrink operator,
the search term, and the allowed number of shrinks from the search term.

Shrink Operators
-----

The deletion operator which returns one string for each position in the input
string, each with the character at that position deleted, is one example of a
shrink operator. There are others, too. The most straightforward generalization
of that operator is one which works on any lists instead of strings, otherwise
doing the same thing. This is a triangular shrink operator as well.

There is also an empty shrink operator which returns no results; this generates
the trivial ordering, which is lower-semimodular.

The shrink operator on lists can be further generalized. Intuitively, given one
shrink operator operating on the type `a`, we can make another shrink operator
operating on the type `[a]` which shrinks each element of the input until
nothing is left. This is currently called `shrinkListEverywhere`.
`shrinkListEverywhere empty` recovers the previous shrink operator on lists.
If the input shrink operator is triangular, so is the resulting one.

There is an analogous shrink operator transformer which works on trees. A
crucial observation here is that if one is shrinking a tree (or for that matter
a list), deleting a node which could be further shrunk by the input shrink
operator is disallowed, otherwise the resulting poset will not be lower
semimodular.

The name "shrink operator" is suggestive; there is existing work done in the
area of test data generation regarding "shrinking" test data to make test
failures easier to understand by way of a minimal example. Some of the
shrinking functions for that purpose are triangular; often however they
sacrifice it in the name of faster convergence to a minimal example. For
example, repeatedly halving an integer, eagerly trying the smallest possible
data before anything else, or progressing via binary search toward some
particular value.

The dual of a shrink operator is a grow operator `grow :: a -> [a]`. A `grow`
operator generates a covering relation and poset in a similar way to `shrink`,
backwards: `x <| y == elem y (grow x)`. A grow operator and shrink operator are
*compatible* if they generate the same poset. Proving a grow operator generates
a lower semimodular poset and is compatible with a shrink operator is a
potentially simpler approach to ensuring a shrink operator is triangular.
`grow` operations are not provided by the accompanying library.

