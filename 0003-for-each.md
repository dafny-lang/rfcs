- Feature Name: for_each_loops
- Start Date: 2022-02-22 (twosday!)
- RFC PR: [dafny-lang/rfcs#0000](https://github.com/dafny-lang/rfcs/pull/0000)
- Dafny Issue: [dafny-lang/dafny#1753](https://github.com/dafny-lang/dafny/issues/1753)

# Summary
[summary]: #summary

This RFC proposes adding two closely-related new features to Dafny for working with collections :

1. `foreach` loops over any enumerable domain, initially only supporting the builtin collection types but leaving the door open for user-defined collections.
2. Generalized sequence comprehension expressions, similar to the existing `set` and `map` comprehension expressions and more flexible than the current `seq(5, i => i*i)` form.

# Motivation
[motivation]: #motivation

Loops are notoriously difficult for Dafny users to verify, and coming up with the correct loop invariants to prove a loop correct 
is particularly challenging. The recent addition of `for` loops was a good step to abstract away from raw `while` loops,
but only supports consecutive integer indices. They still fall short of the expressiveness and economy of `for` or `foreach` loops in
many mainstream programming languages. which generally iterate through the contents of a collection of some kind.
It is a well-established best practice to avoid manual loop indexes wherever possible, as they force the assumption that datatypes
support efficient random access, and are more likely to be used incorrectly by accident:

```dafny
// Before:
method AllPairs(s: seq<nat>) returns (result: seq<(nat, nat)>) {
  for i := 0 to |s| {
    for j := 0 to |s| {
      result := result + (s[i], s[i]);  // Whoops!
    }
  }
}

// After:
method AllPairs(s: seq<nat>) returns (result: seq<(nat, nat)>) {
  foreach left | left in s {
    foreach right | right in s {
      result := result + (left, right);
    }
  }
}

// Or even better, as an expression:
function AllPairs(s: seq<nat>): seq<(nat, nat)> {
  seq left, right | left in s && right in s
}
```

Perhaps the most serious shortcoming is that there is currently no efficient way to iterate over the elements of a `set` at all.
The best alternative is to use the assign-such-that operator and set subtraction, illustrated in the reference manual as follows
([sec 10.5.2](https://dafny-lang.github.io/dafny/DafnyRef/DafnyRef#1052-sets)):

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
when compiled this loop requires quadratic time and memory (or at least garbage-collection work) in the size of the set.
The only way to avoid this cost is to write additional external code in the target language to interface directly with the
internal runtime implementation of `set` values.

By comparison, the equivalent `foreach` loop is:

```dafny
foreach i | i in s {
  print i, "\n";
}
```

The runtime implementation of this loop can use the native iteration features of the target language.

Going further, it is better to avoid writing any imperative loop at all where possible. Sticking to immutable data and
expressions rather than statements allows logic to be used in specifications as well as implementation,
and reduces the burden on the Dafny verifier. The proposed sequence comprehension expression allows more
logic that ultimately produces a sequence of values to be expressed as a value rather than a statement.
Just producing a sequence of the values in a set is simple using a sequence comprehension expression: `seq i | i in s`.

# Guide-level explanation
[guide-level-explanation]: #guide-level-explanation

## foreach Loops

A `foreach` loop in Dafny resembles `for` or `foreach` loops in many other mainstream languages,
but is substantially more general and expressive. A very simple example only looks slightly different than expected:

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

The domain is allowed to infinite if the loop is used in a compiled context and an explicit `decreases` clause is provided.
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
foreach k, v | k in m.Keys && m[k] == v {
  print "m[", k, "] == ", v;
}
```

Note that the range expression is optional, and if omitted the loop will iterate over all
possible values of the types of the bound variables. This is only permitted if all such types
are enumerable, which is not true of the `real` type, for example. This supports an elegant
pattern for iterating over simple datatypes and other types with few values, including subset types.

```
datatype Suit = Clubs | Diamonds | Hearts | Spades

foreach s: Suit {
  ...
}

foreach b1: bool, b2: bool {
  expect TestMyFunctionWithOptions(b1, b2) == true;
}

type SmallIndex = x: nat | 0 <= x < 8

foreach i: SmallIndex {
  ...
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
`seq <BoundVariables> | <Range> :: <Term>` expression is specified by the following `foreach` loop:

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
already exists, to support compiling features such as assign-such-that statements (i.e. using `:|`) and set comprehensions,
but the semantics of these existing features do not depend on this ordering.

By far the most common domain for either feature will be `x in c && P(x)`, where `c` is a builtin collection
type that determines the order, and `P(x)` will only filter the enumeration and not affect the ordering (and will
most often be omitted entirely).
If `c` is a sequence, it contributes the obvious ordering. If `c` is a set or multiset, however, the ordering is
deterministic but under-specified. That is, it will be the same for each enumeration of the same value
within the same execution of the same program, but the verifier will have no information about this ordering,
only that all values are eventually produced exactly once. We expect a common pattern will be to create a sequence
holding the elements of a set and then sort this sequence, at which point this result WILL be fully deterministic
and understood by the verifier.

The general rules for ordering are syntax-driven, recursively defined for any boolean expression. A sketch of
these rules is provided in the following section, but should not be relevant for Dafny users except for unusual cases.
Fortunately, if a user misunderstands these rules and attempts to assert a property that does not actually hold,
the verifier will at least flag this explicitly. Ideally, Dafny IDEs would provide hover text with information about
how a particular domain is ordered when relevant, just as the current language server highlights selected triggers
for a quantification. 

# Reference-level explanation
[reference-level-explanation]: #reference-level-explanation

As mentioned in the guide-level explanation, `foreach` loops and sequence comprehensions are both able to
borrow concepts and implementation substantially from other features. Parsing, resolving, verifying, and compiling
quantifier domains is already a mature aspect of the Dafny implementation. The most significant implementation burden
is ensuring that enumeration ordering is deterministic. The existing compilation logic for enumerating a domain
treats this ordering as pure implementation detail, and applies heuristic optimizations to try to make the search as short
as possible. Ensuring consistent ordering is an additional constraint on this logic, applied only when the surrounding context
is a sequence comprehension or `foreach` loop.

Here is a sketch of the rules that define the enumeration ordering of a quantifier domain.
These rules are chosen as generalizations of the existing semantics for set comprehensions,
such that building a set from all elements in the ordered enumeration results in the same value.

  * Every boolean expression defines an ordered enumeration of free variable bindings that satisfy it. This enumeration may include duplicate bindings, and the ordering is significant.
  * The most common base case is an expression of the form `x in C`, where `C` is an expression with a sequence, multiset, or (i)set type. These expressions produce enumerations that bind only `x` to each value in the collection.
    * For sequences, the ordering is the obvious ordering of values in the sequence.
    * For multisets or (i)sets, the exact ordering is deterministic but unspecified.
    * Potentially-infinite sets are only allowed if they are enumerable.
    * If `x` is not a variable, then the enumeration produces an empty set of bindings once for each time the LHS appears in the RHS collection.
  * For an expression of the form `A && B`, the enumeration includes all bindings that satisfy both `A` and `B`. The enumeration ordering is defined by ordering first by `A`'s ordering and then by `B`'s. See below for the pseudocode that calculates this enumeration.
    * This means that the `&&` operation is not fully symmetrical, but this is already true as verification considers it to be "short-circuiting": 
      `b != 0 && a/b > 1` is valid but `a/b > 1 && b != 0` is not.
    * This definition is chosen such that the multiplicities of results from `A && B` is the same as `B && A`, even if the ordering is not the same. 
  * For an expression of the form `A || B`, the enumeration will simply produce the values enumerated by `A` followed by those enumerated by `B`.
  * If the context of an expression binds a variable that is not used in the expression, such as `seq x: bool | true`, 
    then the default ordering for the type of the variable is used (i.e. `[false, true]` in this case). 
    If this type is not enumerable, then the expression is not allowed.
  * For an expression of the form `!A`, the enumeration will produce all values of the types of the bound variables that do not satisfy `A`. 
    As above, if any of these types are not enumerable the expression is not allowed.

Here is the pseudocode for the semantics of the ordered enumeration of bindings for `A && B`:

```
IEnumerable<ActualBindings> EnumerateConjunction(Expr A, Expr B) {
  foreach (ActualBindings a in A) {
    Expr B' := B[a];  // Substitute the given bindings into the expression B
    foreach (ActualBindings b' in B') {
      yield return b';
    }
  }
}
```

And some illustrative examples using sequence comprehensions:

```dafny
// Special cases for one variable:
seq x: T | A && B == seq x | A * seq x | B  // Not an actual built-in operation, but a generalization of set intersection.
seq x: T | A || B == seq x | A + seq x | B
seq x: T | !A == seq x: T - seq x | A       // Not an actual built-in operation, but a generalization of set subtraction.
                                            // Only well-formed if T itself is enumerable.

seq x | x in [1, 2, 2] && x in [2, 2, 1] == [1, 2, 2, 2, 2]
seq x | x in [1, 2, 2] && x in {2, 1} == [1, 2, 2]
seq x | x in [1, 2, 2] || x in {2, 1} == [1, 2, 2, 1, 2] // Ordering of last two not specified
seq x, y | y in [[1, 2], [3, 4]] && x in y :: x == [1, 2, 3, 4]
seq x, y | y in [[1, 1], [1, 1]] && x in y :: x == [1, 1, 1, 1]

seq x, y | y == {1, 2, 3} && x in y == [2, 3, 1] // Ordering not specified
seq x, y | x in y && y == {1, 2, 3} // ==> "Error: can't calculate ordered enumeration"

// Edge case with no bound variables (not literally supported in Dafny source, but a base case for the general algorithm)
seq | 2 in [2, 2] :: 42 == [42, 42]
seq | 1 in [2, 2] :: 42 == []
```

## Verification

TODO:

  * Verification encoding
    * foreach loops most likely just desugared into existing loop translation
    * sequence comprehensions mapped to Seq.Build calls, but may need more axioms
## Compilation

TODO:

# Drawbacks
[drawbacks]: #drawbacks

The primary drawback to this proposal is the burden of adding the new concept of enumeration ordering. 
This means extra cognitive load for Dafny users, extra implementation effort for any new builtin collection types, 
and additional testing to ensure that all supported quantification domains are deterministically enumerable.

It can be argued that if any compiled Dafny program uses existing features that depend on domain enumeration,
such as `exists` expressions or `:|` statements, its runtime behavior already depends heavily on how this domain
searching is implemented. The compiler only enforces that such domains are finite and enumerable, but an inefficient
choice can lead to the search for a matching value taking orders of magnitude more time than expected.
Therefore we should already be documenting this aspect of Dafny semantics and implementation better anyway.

# Rationale and alternatives
[rationale-and-alternatives]: #rationale-and-alternatives

*** TODO *** 

I propose that leveraging the existing mathematical concepts and syntax is very "Dafny like".

* Matching `forall` statement syntax/semantics (partially) advantages:
  * If someone starts with a forall and then hits the limitation, can easily switch to `foreach`
  * Natural parallel programming paradigm in the future (if `forall` is made more powerful): `foreach` for sequential, `forall` for parallel

Alternatives:

* Could only support `foreach x in c`: only direct collections, one bound value (even if we allow destructuring as in `foreach (k, v) in myMap`)
* Could overload `for LHS in RHS` so we didn't need another keyword
  * Doesn't read quite as well since the RHS won't name individual values like `0 to 10` does
* Could extend `forall` statements to support compilation as well
  * Probably only support specific syntax
  * Semantics don't match - `forall` has simultaneous semantics, allowing things like swaps (?), but we need sequential execution

# Prior art
[prior-art]: #prior-art

*** TODO ***

These features are largely and obviously inspired by the existing features in Dafny for quantification of one or more variables.

Sequence comprehensions bear a strong resemblance to list comprehensions in Python. 

* Standard library functionality in (for e.g.) Java and Rust

JMatch! https://www.cs.cornell.edu/andru/papers/padl03.pdf

# Unresolved questions
[unresolved-questions]: #unresolved-questions

One large open question is how difficult it will be to convince the verifier the following method is correct:

```dafny
function method SortedElements(s: set<int>): seq<int> 
  ensures multiset(SortedElements(s)) == multiset(s)
  ensures Seq.IsSorted(SortedElements(s), (a, b) => a < b)
{
  // Assume Seq.Sorted and Seq.IsSorted are part of the standard library
  Seq.Sorted(seq x | x in s, (a, b) => a < b)
}

method Foo() {
  var smallSet := {1, 2};
  var smallSortedSeq := SortedElements(smallSet);
  // smallSortedSeq is fully specified, but can the verifier figure that out?
  assert smallSortedSeq == [1, 2];
}
```

One of the first milestones when implementing this RFC will be to prototype just enough verification
plumbing to evaluate how difficult proving such properties will be, and how many additional axioms
may need to be added to the Dafny prelude.

# Future possibilities
[future-possibilities]: #future-possibilities

Adding these building blocks to the Dafny language opens up a wide array of tempting new features.

## User-defined Collections

  * Already a concept in Dafny, but now possible to have user-implemented collections
    * `Contains(t)`, which is used for `x in c` expressions
      * Implies `T(0)`
      * Default is `exists x | x in c :: x == t`

## User-defined Enumerable and IEnumerable values

  * Must define `Enumerator() returns Enumerator<T>`
  * May define `Size()` to support `|c|`?
    * Default is `|multiset x in c|`
  * All finite enumerables are collections, and all finite collections are enumerable, but some infinite collections are not (only defining `in`)

## User-defined Enumerator and IEnumerator implementations

  * Must define `Next()`
  * For `Enumerator`
    * `T` must be failure-compatible
    * Must define `Decreases()`

* Adding chaining methods to Enumerator/Enumerable
* Batch optimization of the above
  * Requires allowing subclasses to override default implementations

## Short-form quantifier domains

  * `x in c` ==> `x | x in c`
  * `(k, v) in myMap.Items` ==> `k, v | (k, v) in myMap.Items`
    * `k, v | m[k] == v` ==> `m[k] == v`
  * In general: `<Expr>` ==> `<bound vars in Expr> | <Expr>`
  * Can also allow omitting the range expression: `x: T` ==> `x: T | true`
    * Useful for subset types: define something like `type Index = x: int | 0 <= index < 10`, and then do `foreach i: Index { ... }`
  * Applies to comprehensions (seq, set, map) and quantifier expressions (forall, exists)

## Unicode strings

  * Both features provide an efficient way to iterate over values in an ordered collection that isn't efficiently random access

## More flexible && enumeration

  * could generalize to say that domains have an ordering even if they are not enumerable, allow RHS to enumerate and then sort by LHS
## Array comprehensions

* Avoids requiring the element type is auto-initializable

`var a := new int[10] i :: i * i;`
`var a := new int[|s|] i :: s[i]`
`var a := new int[] i | i in 0..10`
  * SeqToArray helper method?
  * Good way to dump a set into an array so you can sort it
`var a := new int[10, 10] i, j :: i * j`

## Multiset comprehensions

* Similar semantics as sequence comprehensions: counts the number of times a result is enumerated, but does not maintain ordering.

## Ranges as first-class values

* Another kind of builtin collection
* Allows `seq i | i in 0..10 :: f(i)`

## collect expressions?

* Comprehensions can express a lot, but not combining values
* `exists x: T | P(x)` == `collect x: T :: P(x) to ||. false`
* `forall x: T | P(x)` == `collect x: T :: P(x) to &&, true`
* Might realistically depend on "operations" as first-class values somehow
  * type class?
  * Dual of enumerator, "aggregator"? "collector"?
    * More like the dual of a collection
  * Could just parameterize just by the intermediate type:
    * `collect<Averager>`
* `exists x: T | P(x) == collect(||) x: T :: P(x)`
* `forall x: T | P(x) == collect(&&) x: T :: P(x)`
* `var sum := collect(+) x: T :: P(x)`
* `var avg := collect(Average) x: T :: P(x)`


## iterator types as collections