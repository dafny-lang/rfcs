- Feature Name: ordered_quantification
- Start Date: 2022-02-22 (twosday!)
- RFC PR: [dafny-lang/rfcs#9](https://github.com/dafny-lang/rfcs/pull/9)
- Dafny Issue: [dafny-lang/dafny#1753](https://github.com/dafny-lang/dafny/issues/1753)

# Summary
[summary]: #summary

This RFC proposes adding two closely-related new features to Dafny for working with collections and iteration:

1. `foreach` loops over any enumerable domain, initially only supporting the builtin collection types but leaving the door open for user-defined collections.
2. Generalized sequence comprehension expressions, similar to the existing `set` and `map` comprehension expressions and more flexible than the current `seq(5, i => i*i)` form.

These features both build on the fundamental new concept of *ordered quantification*, and their syntax and semantics overlap substantially.

# Motivation
[motivation]: #motivation

Loops are notoriously difficult for Dafny users to verify, and coming up with the correct loop invariants to prove a loop correct 
is particularly challenging. The recent addition of `for` loops was a good step to abstract away from raw `while` loops,
but only supports consecutive integer indices. They still fall short of the expressiveness and economy of `for` or `foreach` loops in
many mainstream programming languages, which generally iterate through the contents of a collection of some kind.
It is a well-established best practice to avoid manual loop indexes wherever possible, as they force the assumption that datatypes
support efficient random access, and are more likely to be used incorrectly by accident:

```dafny
// Before:
method AllPairs(s: seq<nat>) returns (result: seq<(nat, nat)>) {
  for i := 0 to |s| {
    var left := s[i];
    for j := 0 to |s| {
      var right := s[i]; // Whoops!
      result := result + (left, right);  
    }
  }
}

// After:
method AllPairs(s: seq<nat>) returns (result: seq<(nat, nat)>) {
  foreach left <- s, right <- s {
    result := result + (left, right);
  }
}

// Or even better, as an expression:
function method AllPairs(s: seq<nat>): seq<(nat, nat)> {
  seq left <- s, right <- s :: (left, right)
}
```

A more serious shortcoming is that there is currently no efficient way to iterate over the elements of a `set` at all.
The best alternative is to use the assign-such-that operator and set subtraction, illustrated in the reference manual as follows
([sec 10.5.2](https://dafny-lang.github.io/dafny/DafnyRef/DafnyRef#1052-sets)):

```dafny
// s is a set<int>
var ss := s;
while ss != {}
{
  var i: int :| i in ss;
  ss := ss - {i};
  print i, "\n";
}
```

This is functionally correct, but in the current compiler and runtimes takes quadratic time.
https://github.com/dafny-lang/dafny/issues/2062 contains a more in-depth exploration of this issue;
the overall conclusion is that improving the situation through optimization is risky and expensive.

By comparison, the equivalent `foreach` loop is:

```dafny
foreach i <- s {
  print i, "\n";
}
```

The runtime implementation of this loop can use the native iteration features of the target language.

Going further, it is better to avoid writing any imperative loop at all where possible. Sticking to immutable data and
expressions rather than statements allows logic to be used in specifications as well as implementation,
and reduces the effort Dafny users have to spend on proving their code correct. The proposed sequence comprehension expression allows more
logic that ultimately produces a sequence of values to be expressed as a value rather than a statement.
Just producing a sequence of the values in the set above, sorted by the natural ordering of `int` values,
is simple using a sequence comprehension expression: `seq i: int | i in s`.

# Guide-level explanation
[guide-level-explanation]: #guide-level-explanation

Both of the proposed new features depend on another new and more fundamental concept: quantification ordering. 
Therefore, allow me to outline this concept first before then describing `foreach` loops and sequence comprehensions.

## Quantification ordering

This concept augments the existing common syntax for quantifier domains with a notion of ordering, and allows quantified variables to
bind to duplicate values. The key points are:

* Any quantifier domain defines a potentially infinite, partially-ordered set of *quantifier bindings*.
* The quantified variable declarations define the values each binding maps to each variable, AND how these bindings are ordered.
* The range expression after the `|` restricts the quantification to a subset of these bindings, but does not influence their ordering.
* A quantifier domain only guarantees an ordering of bindings, but is NOT prescriptive on how to enumerate this domain at runtime, if it is compiled!
  This is consistent with existing expressions such as `set x: real | x in mySet && P(x)`: although the unfiltered domain of `real` values is not
  enumerable, the bound `x in mySet` is, and at runtime this set is calculated by enumerating the contents of `mySet` and filtering out values
  that do not satisfy `P(x)`. The new features that are affected by quantification ordering will behave similarly: `seq x: real | x in mySet && P(x)`

There will be three supported *quantifier variable declaration* cases for determining this ordering, and others could potentially be added in the future:

1. `x [: T]`

    In the existing syntax for quantified variables (where the type `T` may be explicitly provided or omitted and inferred),
    the quantification bindings will be ordered according to the *natural ordering* of the type `T`. Not all Dafny types will
    have such a natural ordering defined, but at a minimum `int` and `real`, and any subset type or newtype based on them,
    will use the natural mathematical ordering. `x: int | x in {2, 5, 3}`, for example, would bind x to `2`, `3`, and `5` in that order.

2. `x [: T] <- C` 

    In this new syntax, the quantification bindings will be defined and ordered according to the expression `C`, which must be a collection. Initially only the builtin collection types (`set`, `multiset`, `map` and `seq`) will be supported, but support for user-defined collection types will be possible in the future. If `C` is a `map`, the bound values will be the keys of the `map`, in order to be consistent with the meaning of `x in C`; `map.Items` should be used instead to bind key-value pairs. 
    Unlike the first case, this syntax may produce duplicate bindings. The ordering of bindings is non-deterministic unless `C` is a sequence.
    If `C` is a `multiset`, multiple bindings with the same value of `x` will be created, but their ordering is still non-deterministic.

    The `<-` symbol would be read as "from", so a statement like `foreach x <- C { ... }` would be read as "for each x from C ...". Note that `<-` is not an independent operator and is intentionally distinct from the `in` boolean operator.

    The expression `C` is allowed to depend on quantifier variables declared in earlier clauses, such as `x <- C, y <- x`.

3. `<CasePatternLocal> <- C`

    This is a generalization of the previous case that supports pattern matching, as in variable declaration and match statements.
    It allows destructuring datatypes and tuples, as in `(k, v) <- myMap.Items`, and filtering, as in `Some(x) <- mySetOfOptionals`.

A single quantifier domain may include multiple such clauses separated by commas, in which case the orderings described for each clause take
lexicographic precedence. The domain `x <- [1, 2], y <- [3, 4]` will therefore specify the following bindings in that order:

1.  `x == 1, y == 3`
1.  `x == 1, y == 4`
1.  `x == 2, y == 3`
1.  `x == 2, y == 4`

The syntax for quantifier domains will therefore become:

QuantifierVarDecl ::=
  Ident [":" Type]
  | Ident [":" Type] "<-" Expression
  | CasePatternLocal "<-" Expression

QuantifierDomain ::=
  QuantifierVarDecl 
  { "," QuantifierVarDecl }
  [ "|" Expression ]

Note that this concept and the new `<-` syntax applies to any use of quantifier domains, even though ordering and multiplicity
is irrelevant for all current uses: the semantics of `[i]set` and `map` comprehensions, `forall` and `exists` expressions, 
and `forall` statements all do not depend on the order of quantification and semantically ignore duplicates. 
This syntax does offer a more efficient expression of common uses of these features, however: `set Some(x) <- s` is equivalent to
`set x | x in s && x.Some? :: x.value`, for example.

## foreach Loops

A `foreach` loop in Dafny resembles `for` or `foreach` loops in many other mainstream languages,
but is substantially more general and expressive. A very simple example only looks slightly different than expected:

```dafny
foreach x <- [1, 2, 3, 4, 5] {
  print x, "\n";
}
```

The feature supports much more sophisticated uses as well, however,
including binding multiple variables at once and filtering:

```dafny
var myDoubleDeckerSeq: seq<seq<int>> := ...;
foreach x <- myDoubleDeckerSeq, y <- x | y != 0 {
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
  [ Body ]
```

A `foreach` loop closely resembles a `forall` statement, the key difference being that a `forall`
loop executes its body once for every tuple of quantified values simultaneously, whereas a `foreach` loop
executes its body once for each tuple of quantified values in sequence, one at a time.

Similarly to set comprehensions or assign-such-that statements, the domain of a `foreach` loop
must be enumerable. The following loop would produce the error `"the domain of a foreach loop must be enumerable,
but Dafny's heuristics can't figure out how to produce an enumeration for 'x'"`.

```dafny
foreach x: real | 0.0 <= x < 1.0 {  // Error: ...
  ...
}
```

The domain is allowed to be potentially infinite if the loop is used in a compiled context and an explicit `decreases` clause is provided.
`decreases *` is permitted, in which the `foreach` loop may never terminate. Any other `decreases` clause can be provided
to ensure the loop terminates even if the domain is potentially infinite. The following (slightly bizarre) example is legal:

```dafny
foreach x: nat 
  invariant x <= 10
  decreases 10 - x
{
  print x, "\n";
  if x == 10 { break; }
}
```

Most `foreach` loops will take the form `foreach x <- C { ... }`, where `C` is a `seq`, `set` or `multiset`.
This includes expressions like `m.Keys`, `m.Values` and `m.Items` when `m` is a `map`.
Looping over the keys and values of a map is particularly clean with this syntax:

```dafny
foreach (k, v) <- m.Items {
  print "m[", k, "] == ", v;
}
```

Note that the range expression is optional, and if omitted the loop will iterate over all
possible values of the types of the bound variables. This is only permitted if all such types
are enumerable, which is not true of the `real` type, for example. This supports an elegant
pattern for mapping over simple datatypes and other types with few values, including subset types.

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

Similarly, a helper function can be provided to maintain a running index of the enumerated values:

```dafny
foreach (x, i) in WithIndexes(s) {
  ...
}

// Alternatively, if s is a sequence:
foreach i, x | 0 <= i < |s| && s[i] == x {
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

Sequence comprehensions are likely to be easier to work with than `foreach` loops, and Dafny users should be
encouraged to use them instead where possible. Many high-order operations on sequences can be expressed directly
using sequence comprehensions:

```dafny
// Filtering to optional values
var s: seq<Option<T>> := ...;
var filtered: seq<T> := seq Some(x) <- s;

// Zipping two lists together
var a: seq<T> := ...;
var b: seq<T> := ...;
assert |a| == |b|;
var zipped := seq i | 0 <= i < |a| :: (a[i], b[i])

// Map and then flatten (a.k.a. "FlatMap")
var c: seq<S> := ...;
var f: S -> seq<T> := ...;
var flatMapped: seq<T> := seq x <- c, y <- f(x) :: y;

// Sorted sequence from a set
var setOfReals := {3.141, 2.718, 1.618};
var sortedList := seq x | x in setOfReals;
assert sortedList == {1.618, 2.718, 3.141};
```

Note that the existing `seq(size, i => i + 1)` syntax is inconsistently-named in the Dafny reference manual, 
but we refer to it here as a "sequence construction" expression, to disambiguate it from the proposed sequence comprehension feature.
Sequence comprehensions are strictly more expressive, as any construction `seq(size, f)` can be rewritten as 
`seq i | 0 <= i < size :: f(i)`. They also avoid the common trap of forgetting to explicitly attach the `requires 0 <= i < size`
pre-condition to a lambda expression, as this issue highlights: https://github.com/dafny-lang/dafny/issues/1332

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
    * For (i)sets or multisets, the exact ordering is deterministic but unspecified.
    * Potentially-infinite sets are only allowed if they are enumerable.
    * If `x` is not a variable, then the enumeration produces an empty set of bindings once for each time the LHS appears in the RHS collection.
  * For an expression of the form `A && B`, the enumeration includes all bindings that satisfy both `A` and `B`. The enumeration ordering is defined by ordering first by `A`'s ordering and then by `B`'s, and the multiplicities of bindings is multiplied. See below for the pseudocode that calculates this enumeration.
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
(seq x: T | A && B) == (seq x | A) * (seq x | B)  // Not an actual built-in operation, but a generalization of set intersection.
(seq x: T | A || B) == (seq x | A) + (seq x | B)
(seq x: T | !A) == (seq x: T) - (seq x | A)       // Not an actual built-in operation, but a generalization of set subtraction.
                                                  // Only well-formed if T itself is enumerable.

(seq x | x in [1, 2, 2] && x in [2, 2, 1]) == [1, 2, 2, 2, 2]
(seq x | x in [1, 2, 2] && x in {2, 1}) == [1, 2, 2]
(seq x | x in [1, 2, 2] || x in {2, 1}) == [1, 2, 2, 1, 2] // Ordering of last two not specified
(seq x, y | y in [[1, 2], [3, 4]] && x in y :: x) == [1, 2, 3, 4]
(seq x, y | y in [[1, 1], [1, 1]] && x in y :: x) == [1, 1, 1, 1]

(seq x, y | y == {1, 2, 3} && x in y) == [2, 3, 1] // Ordering not specified
(seq x, y | x in y && y == {1, 2, 3}) // ==> "Error: can't calculate ordered enumeration"

// Edge case with no bound variables (not literally supported in Dafny source, but a base case for the general algorithm)
(seq | 2 in [2, 2] :: 42) == [42, 42]
(seq | 1 in [2, 2] :: 42) == []
```

## Verification

The optimal encoding of sequence comprehensions to Boogie is something of an open question:
set comprehensions are encoded as their indicator predicates, but there is no such direct representation
for sequence comprehensions as defined here. The initial encoding will likely be with a function,
similar to the `Seq#Create` function used for set constructions, that accepts an indicator predicate.
Axioms will be included to at least state that values are elements of a sequence comprehension iff
they satisfy this predicate. This property is likely the most important to infer automatically,
although it says nothing about the ordering or multiplicity of these values.

Since `x | x in C && P(x)` where `C` is a sequence will be a very common pattern, it will likely be worthwhile
to also include axioms for this pattern to encode the fact that elements in the result
maintain their ordering from `C`, and that the length of the result and the multiplicities of values
are all bounded from above by their analogues from `C`.

The translation of `foreach` loops should be reducible to sequence comprehensions
and other existing features for loops in general,
as the semantics of such loops can usually be expressed as follows:

```dafny
// A loop of this form:
foreach x1, x2, ..., xN | <Range> {
  <Body>
}

// Is semantically equivalent to:
var __s := seq x1, x2, ..., xN | <Range> :: (x1, x2, ..., xN);
for __i := 0 to |__s| {
  var (x1, x2, ..., xN) := __s[__i];
  <Body>
}
```

This is not a complete equivalency as the domain of `foreach` loop with explicit `decreaes` clauses
are allowed to be infinite. It may make sense to support encoding potentially infinite sequences in the Boogie prelude
even if they are not (yet) supported in Dafny, to close this gap.

## Compilation

The most challenging part of compiling these new features is ensuring the enumeration
ordering of unordered collection types such as sets and multisets is deterministic when used in a sequence comprehension.
This is closely related to compiling let-such-that expressions (`var x :| ...; ...`), as such expressions
are implemented by enumerating through the parameters of a domain to search for a match,
and hence are influenced by this ordering. The current solution is to require any such expressions
have only one solution, which is not an option here.
As illustrated in [this paper](https://easychair.org/publications/paper/dM), the challenge is
that although the runtime values of `{1, 2}` and `{2, 1}` will compare equal to each other,
their internal representation may differ and hence their enumeration ordering may as well.

Most if not all current Dafny compilers implement a Dafny `set<T>` with some variation on a hash set,
which is generally a good default choice since this datatype offers constant-time access on average.
Although different copies of the same set must place each value into the same hashing bucket, multiple
values may be assigned to the same bucket, so it is necessary to use a secondary data structure of some kind for each bucket.
A common simple approach is to use a linked list,
in which case a single bucket will store elements in the order they were added and hence not meet the requirement
of a deterministic ordering based only on the set of contained elements.

One solution is to use a binary search tree as this secondary data structure instead, assuming that a total ordering of
the elements of the type `T` is available. Some hash set implementations, such as recent versions of the Java `HashSet<T>` type,
use a similar approach as an internal optimization when many hashing collisions occur, 
so that the worst case runtime of lookups is O(log N) rather than O(N).
The included Dafny runtimes can provide an implementation of Dafny sets and multisets that use this approach consistently,
and hence provide the efficient average-case access of a hash set but still provide a deterministic enumeration order.

The good news is that individual compilers are free to decide they do not support sequence comprehensions
whose ordering depends on any such collections. Dafny code that will be compiled using such compilers can 
fall back to using a `foreach` loop to iterate over sets instead, as statements are permitted to
observe non-determinism. This means a particular compiler can still map a Dafny `set<T>` value 
directly to a native implementation of sets, such as a Java `Set<T>`, even though these implementations will
enumerate their contents with non-deterministic ordering.

# Drawbacks
[drawbacks]: #drawbacks

The primary drawback to this proposal is the burden of adding the new concept of quantification ordering. 
This means extra cognitive load for Dafny users, extra implementation effort for any new builtin collection types, 
and additional testing to ensure that all supported quantification domains are deterministically enumerable.

It can be argued that if any compiled Dafny program uses existing features that depend on domain enumeration,
such as `exists` expressions or `:|` statements, its runtime behavior already depends heavily on how this domain
searching is implemented. The compiler only enforces that such domains are finite and enumerable, but an inefficient
choice can lead to the search for a matching value taking orders of magnitude more time than expected.
Therefore we should already be documenting this aspect of Dafny semantics and implementation better anyway.

# Rationale and alternatives
[rationale-and-alternatives]: #rationale-and-alternatives



# Prior art
[prior-art]: #prior-art

Sequence comprehensions bear a strong resemblance to list comprehensions in Python, which also include similar abilities to 
bind multiple variables and filter the enumerated values: `[(x, y) for x in [1,2,3] for y in [3,1,4] if x != y]`

Most mainstream programming languages include rich libraries for working with collections and iterators,
and define much the same operations such as "filter" and "flatMap".
The proposed Dafny features provide similar functionality at a higher level
of abstraction more amenable to verification: quantification expressions are used to succinctly declare the behavior of
an operation that in spirit applies several such operations. See the "Future Possibilities" section for ideas for
pushing this philosophy even further.

# Unresolved questions
[unresolved-questions]: #unresolved-questions

* Is inconsistency between quantification ordering and `<` an issue? (e.g. `<` on datatypes means "rank comparison"
and can't be compiled, string prefix rather than lexicographic ordering, etc)

```dafny
function QuickSort(s: seq<int>): seq<int> {
  // Oops, this discards multiplicity
  seq x | x in s
} by method {
  // ...
}
```

# Future possibilities
[future-possibilities]: #future-possibilities

Adding this building block to the Dafny language opens up a wide array of tempting new features!

## User-defined collections

As discussed in the earlier [`for` loops RFC](https://github.com/dafny-lang/rfcs/pull/4), the semantics of
`for` or `foreach` loops in many programming languages are defined in terms of "iterator" or "enumerator" objects. 
The features proposed here only support builtin collections, but could easily be extended to support
arbitrary Dafny types that provide a way to obtain an enumerator for their contents.
[This PR](https://github.com/dafny-lang/libraries/pull/37) should be a good start towards designing
the necessary interface. This is also likely the best way to provide a better user experience
for looping or quantifying over the values produced by an `iterator` type.

## Unicode strings

As I have previously ranted about in https://github.com/dafny-lang/dafny/issues/413, the Dafny `string` type is currently an alias
for `seq<char>`, where `char` is defined as a UTF-16 code units, and hence allows invalid sequences according to the semantics of
Unicode. Modelling unicode correctly will involve specifying that the semantic contents of a UTF-8 string, for example, is
a sequence of Unicode code points that is not efficiently accessed with indices. The features proposed here provide ways to work with
such datatypes efficiently at runtime.

## Array comprehensions

The same syntax for sequence comprehensions could also be used for flexible array initialization,
since this is another case where the user has to declare an ordered source of values:

```
var a := new int[10] i :: i * i;
var a := new int[|s|] i :: s[i];     // Where s is a seq<int>
var a := new int[] i | 10 <= i < 20;
```

It would likely be prudent to limit these cases to those where the size of the domain
is easy to infer statically, so that the size of the array to allocate is known before
enumerating the values.

## Multiset comprehensions

There would have similar semantics to sequence comprehensions, 
where the multiplicity of results is significant but not the ordering.
This feature would be very cheap to implement once sequence comprehensions are implemented.

## Generalized comprehensions

As shown above, sequence comprehensions are a powerfully expressive feature,
but they can only express enumerating multiple values from a small number of source expressions, 
and not the opposite direction of aggregating multiple values into one.
The existing quantifier and comprehension expressions can be viewed as specific
cases of aggregating multiple values into a single result value.
An equally powerful feature would be to generalize this pattern and define
a parameterized collection expression to aggregate a quantifier domain into
a single value:

```dafny
collect(&&) x: T | P(x) :: Q(x)         == forall x: T | P(x) :: Q(x)
collect(||) x: T | P(x) :: Q(x)         == exists x: T | P(x) :: Q(x)
collect(SeqBuilder) x: T | P(x) :: Q(x) == seq x: T | P(x) :: Q(x)
collect(SetBuilder) x: T | P(x) :: Q(x) == set x: T | P(x) :: Q(x)
collect(+) x: T | P(x) :: Q(x)          == (summation)
collect(*) x: T | P(x) :: Q(x)          == (product)
collect(<) x: T | P(x) :: Q(x)          == (minimum)
collect(Averager) x: T | P(x) :: Q(x)   == (average)
collect(First(n)) x: T | P(x) :: Q(x)   == Take(seq x: T | P(x) :: Q(x), n)
...
```

This mirrors the `Collector` concept from the Java streaming APIs, and ideally the shape of the
parameter to `collect` expressions would define similar operations for merging intermediate results
to leave the door open for parallel or even distributed computation.

## Notes

New version:

"Quantifier domain" exists as a parsing concept, now define it more explicitly: a totally ordered set of bindings. Bindings have their own identity for the sake of the ordering definition, so 
`x <- [1, 1, 1, 1, 1]` contains 5 distinct bindings, although each binds `x` to `1`.
Not necessarily enumerable or finite. Doesn't even need to be when compiled, because
quantifier ranges can restrict to a domain that is, e.g. `set x: real | x in setOfReals`.

```dafny
seq x <- xs, y <- ys :: (x, y)
seq k <- m.Keys, v == m[k] :: (k, v)
multiset (k, v) <- m.Items :: v
seq Some(v) <- optionals :: v
seq x <- doubleDeckerSeq, y <- x :: y
seq x | 0 <= x < 10
foreach x <- c { ... }
```

How to get the domain of a multiset? `x <- ms` is fine as long as the ordering
doesn't have to be deterministic.

Binding patterns:
* x (: T) - natural order of T, may need heuristics to determine finiteness
* x <- C - order of C, may contain duplicates
* x by myLessThen (future) - user-provided ordering

Provide a way to specify the ordering when you don't have a collection?
* x: int will be a wibble wobble order, but x: nat will be sequential
  * Technially that's a wibble wobble order restricted to nat values!

"Exists uniquely" quantifier?
