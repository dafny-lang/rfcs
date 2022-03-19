- Feature Name: for_each_loops
- Start Date: 2022-02-22 (twosday!)
- RFC PR: [dafny-lang/rfcs#0000](https://github.com/dafny-lang/rfcs/pull/0000)
- Dafny Issue: [dafny-lang/dafny#1753](https://github.com/dafny-lang/dafny/issues/1753)

# Summary
[summary]: #summary

This RFC proposes adding two closely-related new features to Dafny for working with collections :

1. `foreach` loops, initially only supporting the builtin collection types but leaving the door open for user-defined collections.
2. Generalized sequence comprehension expressions, similar to the existing `set` and `map` comprehension expressions and more flexible than the current `seq(5, i => i*i)` form.

# Motivation
[motivation]: #motivation

Loops are notoriously difficult for Dafny users to verify. *** TODO ***

Perhaps the most serious shortcoming is that there is currently no efficient way to iterate over the elements of a `set`.
The best alternative is to use the assign-such-that operator and set subtraction, illustrated in the reference manual as follows ([sec 10.5.2](https://dafny-lang.github.io/dafny/DafnyRef/DafnyRef#1052-sets)):

```dafny
// s is a set<int>
var ss := s;
while ss != {}
  decreases |ss|
{
  var i: int :| i in ss;
  ss := ss - {i};
  print i, "\n";
}
```

This is functionally correct, but because set subtraction requires creating a fresh copy,
the compiled loop requires quadratic time and memory (or at least garbage-collection work) in the size of the set. 
The equivalent loop using `foreach` is:

```dafny
foreach i | i in s {
  print i, "\n";
}
```

The runtime implementation of this loop can use the native iteration features of the target language.
Just producing a sequence of the values in the set is even simpler, using a sequence comprehension expression: `seq i | i in s`.

# Guide-level explanation
[guide-level-explanation]: #guide-level-explanation

## foreach Loops

Here is very simple example of a `foreach` loop:

```dafny
foreach x | x in [1, 2, 3, 4, 5] {
  print x, "\n";
}
```

The feature supports much more sophisticated uses as well, however,
including binding multiple variables at once and filtering:

```dafny
var myDoubleDeckerSeq: seq<seq<int>> := ...;
foreach x, y | x in myDoubleDeckerSeq && y in x && y != 0 {
  Process(y);
}
```

The high-level syntax for a `foreach` loop reuses several existing concepts:

```
ForeachLoop ::=
  "foreach"
  QuantifierDomain
  LoopSpec
  Body
```

More specifically, this expands to:

```
ForeachLoop ::=
  "foreach" 
  Ident [":" Type] { "," Ident [":" Type] } [ "|" Expression ]
  { InvariantDecl | ModifiesDecl | DecreasesDecl }
  Body
```

A `foreach` loop closely resembles a `forall` statement, the key difference being that a `forall`
loop executes its body once for every tuple of quantified values simultaneously, whereas a `foreach` loop
executes its body once for each tuple of quantified values in sequence, one at a time.

Similarly to set comprehensions or assign-such-that statements, the domain of a `foreach` loop
must be enumerable. The following loop would produce the error `"the domain of a foreach loop must be enumerable,
but Dafny's heuristics can't figure out how to produce an enumeration for 'x'"`.

```dafny
foreach x: real | 0.0 <= x < 1.0 {
  ...
}
```

The domain is allowed to be infinite, however, if the loop is used in a compiled context and an explicit `decreases` clause is provided.
`decreases *` is permitted, in which the `foreach` loop may never terminate. Any other `decreases` clause can be provided
to ensure the loop terminates even if the domain is potentially infinite. The following (slightly bizarre) example is legal:

```dafny
foreach x: nat 
  decreases 10 - x
{
  print x, "\n";
  if x == 10 { break; }
}
```

Most `foreach` loops will take the form `foreach x | x in c { ... }`, where `c` is a `seq`, `set` or `multiset`.
This includes expressions like `m.Keys`, `m.Values` and `m.Elements` when `m` is a `map`.
Looping over the keys and values of a map is particularly readable and aesthetically pleasing with this syntax,
which also makes it easier for the compiled program to avoid unnecessary intermediate tuple values:

```dafny
foreach k, v | m[k] == v {
  print "m[", k, "] == ", v;
}
```

There is no builtin support for automatically tracking the enumerated values so far, as there is for
`iterator` values (see https://dafny-lang.github.io/dafny/DafnyRef/DafnyRef#sec-iterator-types). 
It is straightforward to track these values manually, however:

```dafny
ghost var xs := [];
foreach x | x in s {
  ...
  xs := xs + [x];
}
```

It is even possible to attach this ghost state directly to the sequence with a helper function:

```dafny
foreach x, xs | (x, xs) in WithPrefixes(c) {
  ...
}
```

Where the signature of `WithPrefixes` is something like:

```dafny
function method WithPrefixes<T>(s: seq<T>): seq<(T, ghost seq<T>)> {
  ...
}
```

Similarly, a helper function can be provided to maintain a running index of the enumerated values:

```dafny
foreach x, i | (x, i) in WithIndexes(s) {
  ...
}

// Alternatively, if s is a sequence:
foreach x, i | 0 <= i < |s| && s[i] == x {
  ...
}
```

## Sequence comprehensions

A sequence comprehension has identical syntax to a set comprehension, except that it begins with
`seq` rather than `set`. Therefore its syntax is:

```
SeqComprehension ::=
  "seq" 
  Ident [":" Type] { "," Ident [":" Type] } 
  "|" Expression
  [ :: Expression ]
```

Sequence comprehensions are the expression analogues of `foreach` loops, just as
`forall` expressions are the analogues of `forall` statements. The value of any given
`seq <BoundVariables> | <Range> :: <Term>` expression is calculated by the following `foreach` loop:

```dafny
var result := [];
foreach <BoundVariables> | <Range> {
  result := result + [<Term>];
}
```

Sequence comprehensions are likely to be easier to work with than `foreach` loops, and Dafny users should be
encouraged to use them instead where possible. Many high-order operations on sequences can be expressed directly
using sequence comprehensions:

```dafny
// Filtering to optional values
var s: seq<Option<T>> := ...;
var filtered: seq<T> := seq x | x in s && x.Some? :: x.value;

// Zipping two lists together
var a: seq<T> := ...;
var b: seq<T> := ...;
assert |a| == |b|;
var zipped := seq i | 0 <= i < |a| :: (a[i], b[i])

// Map and then flatten (a.k.a. "FlatMap")
var f: T -> seq<T> := ...;
var c: seq<T> := ...;
var flatMapped: seq<T> := seq x, y | x in c && y in f(x) :: y;
```

Note that the existing `seq(k, n => n + 1)` syntax is inconsistently-named in the Dafny reference manual, 
but we refer to it here as a "sequence construction" expression, to disambiguate it from the proposed sequence comprehension feature.
Sequence comprehensions are strictly more expressive, as any construction `seq(size, f)` can be rewritten as 
`seq i | 0 <= i < size :: f(i)`.

## Ordered enumeration of quantifier domains

The semantics of both of these features depend on defining an enumeration order for any enumerable
quantifier domain. The logic for enumerating the values of variables bound by quantification at runtime
already exists, to support compiling features such as assign-such-that statements and set comprehensions,
but the semantics of these existing features do not depend on this ordering.

By far the most common domain for either feature will be `x in c && P(x)`, where `c` is a builtin collection
type that determines the order, and `P(x)` will only filter the enumeration and not affect the ordering.
If `c` is a sequence, it contributes the obvious ordering. If `c` is a set or multiset, however, the ordering is
deterministic but under-specified. That is, it will be the same for each enumeration of the same value
within the same execution of the same program, but the verifier will have no information about this ordering,
only that all values are eventually produced exactly once. We expect a common pattern will be to create a sequence
holding the elements of a set and then sort this sequence, at which point this result WILL be fully deterministic.

The general rules for ordering are syntax-driven, recursively defined for any boolean expression. A sketch of
these rules is provided in the following section, but should not be relevant for Dafny users except for unusual cases.
Fortunately, if a user misunderstands these rules and attempts to assert a property that does not actually hold,
the verifier will at least flag this explicitly. Ideally, Dafny IDE would provide hover text with information about
how a particular domain is ordered when relevant, just as *** TODO ***

# Reference-level explanation
[reference-level-explanation]: #reference-level-explanation

TODO:

  * Verification encoding
    * foreach loops mostly desugared into ???
    * sequence comprehensions mapped to Seq.Build calls, but may need more axioms
  * At least a sketch of domain enumeration ordering
    * Define rules like associativity that determines ordering. Mostly left overrides right.
    * `x in A && P(x)` -> `A.Enumerator().Filter(P)`
      * Sort-of consistent with multiset "*" intersection but not quite
    * `x in A || x in B` -> `A.Enumerator().Concat(B.Enumerator())`
      * Consistent with multiset "+" union
    * `x !in A` -> `(seq x: T).Enumerator().Filter(x => x !in A)`
    * `x in A && y in B` -> `A.Enumerator().CrossProduct(B.Enumerator())` (or nested loop depending on context)
    * Simplest if every subexpression must be enumerable, even if there are cases where that's not necessary
  * SeqComprehension can borrow a lot from the common ComprehensionExpr supertype

# Drawbacks
[drawbacks]: #drawbacks

* New concept of enumeration ordering, extra implementation effort for new builtin collection types
* Potential confusion over enumeration ordering rules
* 

# Rationale and alternatives
[rationale-and-alternatives]: #rationale-and-alternatives

I propose that leveraging the existing mathematical concepts and syntax is very "Dafny like".

* Matching `forall` statement advantages:
  * If someone starts with a forall and then hits the limitation, can easily switch to `foreach`
  * Natural parallel programming paradigm in the future (if `forall` is made more powerful): `foreach` for sequential, `forall` for parallel


* Could overload `for LHS in RHS` so we didn't need another keyword
  * Doesn't read quite as well since the RHS won't name individual values like `0 to 10` does
* Could extend `forall` statements to support compilation as well
  * Probably only support specific syntax
  * Semantics don't match - `forall` has simultaneous semantics, allowing things like swaps (?), but we need sequential execution
  * But parallel evaluation of `forall`s could be really nice in the future! Prove disjointness and therefore safety.



# Prior art
[prior-art]: #prior-art

These features are largely and obviously inspired by the existing features in Dafny for quantification of one or more variables.

Sequence comprehensions bear a strong resemblance to list comprehensions in Python. 

# Unresolved questions
[unresolved-questions]: #unresolved-questions

- What parts of the design do you expect to resolve through the RFC process before this gets merged?
- What parts of the design do you expect to resolve through the implementation of this feature before stabilization?
- What related issues do you consider out of scope for this RFC that could be addressed in the future independently of the solution that comes out of this RFC?

# Future possibilities
[future-possibilities]: #future-possibilities

## Collections

  * Already a concept in Dafny, but now possible to have user-implemented collections
    * `Contains(t)`, which is used for `x in c` expressions
      * Implies `T(0)`
      * Default is `exists x | x in c :: x == t`

## Enumerable and IEnumerable

  * Must define `Enumerator() returns Enumerator<T>`
  * May define `Size()` to support `|c|`?
    * Default is `|seq x in c|`
  * All finite enumerables are collections, and all finite collections are enumerable, but some infinite collections are not (only defining `in`)

## Enumerator and IEnumerator

  * Must define `Next()`
  * For `Enumerator`
    * `T` must be failure-compatible
    * Must define `Decreases()`

* Adding chaining methods to Enumerator/Enumerable
* Batch optimization of the above
  * Requires allowing subclasses to override default implementations

## Short-form quantifier domains

  * `x in c` ==> `x | x in c`
  * `(x, y) in myMap.Items` ==> `x, y | (x, y) in myMap.Items`
  * In general: `<Expr>` ==> `<bound vars in Expr> | <Expr>`
  * Can also allow omitting the range expression: `x: T` ==> `x: T | true`
    * Useful for subset types: define something like `type Index = x: int | 0 <= index < 10`, and then do `foreach i: Index { ... }`
  * Applies to comprehensions (seq, set, map) and quantifier expressions (forall, exists)

## Array comprehensions

* Avoids requiring the element type is auto-initializable

`var a := new int[] i :: i * i;`
`var a := new int[|s|] i :: s[i]`
`var a := new int[10, 10] i, j :: i * j`

## Multiset comprehensions

* Similar semantics as sequence comprehensions: counts the number of times a result is enumerated, but does not maintain ordering.

## Ranges as first-class values

* Allows `seq i | i in 0..10 :: f(i)`