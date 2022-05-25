- Feature Name: ordered_quantification
- Start Date: 2022-02-22 (twosday!)
- RFC PR: [dafny-lang/rfcs#10](https://github.com/dafny-lang/rfcs/pull/10)
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
  result := [];
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
and reduces the effort Dafny users have to spend on proving their code correct.
The proposed sequence comprehension expression allows more logic 
that ultimately produces a sequence of values to be expressed as a value rather than a statement.
Just producing a sequence of the values in the set above, in a non-deterministic order,
is simple using a sequence comprehension expression: `seq i <- s`.

These higher-level features also provide a simpler Dafny idiom for compilers to recognize
and translate to idiomatic code in a target language, which is an important requirement for some Dafny users.
A sequence comprehension like `seq e: Entry <- myList | e.active :: e.id` could be translated to a loop like the following in Java:

```java
List<ID> result = new ArrayList<>(myList.size());
for (Entry e : myList) {
  if (e.isActive()) {
    result.add(e.getID());
  }
}
```

Or this, which is arguably more idiomatic for most Java logic that works with collections:

```java
List<ID> result = myList.stream().filter(Entry::isActive).map(Entry::getID).collect(Collectors.toList());
```

# Guide-level explanation
[guide-level-explanation]: #guide-level-explanation

Both of the proposed new features depend on another new and more fundamental concept: quantification ordering. 
Therefore, allow me to outline this concept first before then describing `foreach` loops and sequence comprehensions.

## Quantification ordering

Several existing Dafny features support a common syntax for quantifying over one or more variables, internally referred to
as a *quantifier domain*. For example, consider this universal quantifier:

```dafny
forall x: nat, y: nat | 0 < x && 0 < y :: x % gcd(x, y) == 0 && y % gcd(x, y) == 0
```

The quantifier domain is this case is the `x: nat, y: nat | 0 < x && 0 < y` portion.
The boolean expression after the `|` is referred to as the *range*,
and I will label the `x: nat` and `y: nat` sections as *quantifier variable declarations*
(or alternatively, *quantified variable declarations*).

We can extend the syntax and semantics of this concept in natural,
backwards-compatible ways to allow a well-defined notion of ordering over some quantification domains,
which will be the foundation of both `foreach` loops and sequence comprehensions and potentially other future language features.

### Quantified variable domains

By default, any quantified variable ranges over all values of its type, and is only further constrained by the range expression.
The first extension is to allow an optional *quantifier variable domain*, declared with the syntax `x <- C` where `C` is a collection. 
Initially only the builtin collection types (`[i]set`, `multiset`, `[i]map`, and `seq`) will be allowed, 
but support for user-defined collection types will be possible in the future. 
If `C` is a `map`, the bound values will be the keys of the `map`, in order to be consistent with the meaning of `x in C`;
`map.Items` can be used instead to bind key-value pairs.

Assuming that we have `posNat == iset n: nat | 0 <= n`, the set comprehension above could also then be expressed as:

```dafny
forall x <- posNat, y <- posNat :: x % gcd(x, y) == 0 && y % gcd(x, y) == 0
```

This aligns nicely with the variation of guarded quantifier notation in mathematics that explicitly attaches domains to variables: 
$\forall x \in \mathbb{N}^+, y \in \mathbb{N}^+ \bullet x | gcd(x, y) \land y | gcd(x, y)$. 

Besides offering a slightly more succinct expression of existing quantification domains,
quantified variable domains also specify the ordering of quantification bindings, and allow variables to be bound to duplicate values.
This ordering of bindings is non-deterministic unless `C` is a sequence.
If `C` is a `multiset`, multiple bindings with the same value of `x` will be created, but their ordering is still non-deterministic.
Note that ordering and multiplicity is irrelevant for all current uses:
the semantics of `[i]set` and `[i]map` comprehensions, `forall` and `exists` expressions, 
and `forall` statements all do not depend on the order of quantification and semantically ignore duplicates.

The `<-` symbol would be read as "from", so a statement like `foreach x <- C { ... }` would be read as "for each x from C, ...". 
`<-` is not an independent operator and is intentionally distinct from the `in` boolean operator.
This should help clarify that while any `x` value bound from `x <- C` also satisfies `x in C`,
they are different concepts and the former carries more information than the latter.

Quantified variable domains will be optional in all existing features that use them,
but required on variables quantified by a `foreach` loop or sequence comprehension.
This is to avoid having to define the ordering of an expression like `seq x: int`:
should this have a non-deterministic ordering, or should it be ordered
according to the natural mathematical ordering on integers?
This restriction could be lifted in the future if the answer becomes clearer
(and see also Future Possibilities).

When a single quantifier domain includes multiple declarations separated by commas, 
the the orderings take precedence from left to right. 
The domain `x <- [1, 2], y <- [3, 4]` will therefore specify the following bindings in this order:

1.  `x == 1, y == 3`
1.  `x == 1, y == 4`
1.  `x == 2, y == 3`
1.  `x == 2, y == 4`

The domain expression of one quantified variable is allowed to reference other variables
declared earlier in the quantifier domain.
The domain `x <- [[1, 2], [3, 4]], y <- x` therefore produces these bindings:

1.  `x == [1, 2], y == 1`
1.  `x == [1, 2], y == 2`
1.  `x == [3, 4], y == 3`
1.  `x == [3, 4], y == 4`

### Quantified variable ranges

Since quantifier variable domains are values themselves, they carry well-formedness requirements with them as well.
To make quantifier domains with multiple quantified variables easier to express,
range expressions will be supported after each variable declaration, instead of as a separate component of quantifier domains.
Assuming that `seqOfInts` is of type `seq<int>` and the function `natsFromZeroTo` accepts a `nat` rather than an `int`,
the quantifier domain `x <- seqOfInts | 0 <= x, y <- natsFromZeroTo(x)` is then well-formed.

The overall syntax for quantifier domains will therefore become:

```
QuantifierVarDecl ::=
  Ident [":" Type] [ "<-" Expression ] { Attribute } [ "|" Expression ]

QuantifierDomain ::=
  QuantifierVarDecl { "," QuantifierVarDecl }
```

It is perhaps a bit surprising that this change does not break existing quantification domains,
but it only means existing range expressions will be re-interpreted as binding to the last quantifier variable,
where it can still reference all quantified variables and has the same filtering semantics.
The only wrinkle is attributes like `{:heapQuantifier}` that are currently only allowed in-between
the quantified variable declarations and the single range. To maintain backwards compatibility,
`QuantifierVarDecl` accepts attributes just before the optional range expression.
This means that the parser will accept attributes in-between variables, 
but these can be easily rejected by the resolver instead.

Note that in quantification contexts not sensitive to ordering or multiplicity,
quantified variable domains and ranges can both be rewritten back into a single range without changing semantics.
For example, note that the RHS of the following identity is equally well-formed
because `&&` is short-circuiting in Dafny:

```dafny
(forall x <- C | P1(x), y <- f(x) | P2(x, y) :: Q(x, y)) == 
(forall x, y | x in C && P1(x) && y in f(x) && P2(x, y) :: Q(x, y))
```

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
var mySeq: seq<int> := ...;
function method getSomeValues(x: nat): seq<int> 
{
  ...
}
foreach x <- mySeq | 0 <= x,
        y <- getSomeValues(x) | y != 0 
{
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
  Ident [":" Type] [ "<-" Expression ] [ "|" Expression ] 
  { "," Ident [":" Type] [ "<-" Expression ] [ "|" Expression ] } 
  { InvariantDecl | ModifiesDecl | DecreasesDecl }
  [ BlockStmt ]
```

A `foreach` loop closely resembles a `forall` statement, the key difference being that a `forall`
statement executes its body once for every binding of quantified values simultaneously, whereas a `foreach` loop
executes its body once for each binding of quantified values in sequence, one at a time.

Similarly to compiled set comprehensions or assign-such-that statements, the domain of a `foreach` loop
must be enumerable, even in ghost contexts. The following loop would produce the error `"the domain of a foreach loop must be enumerable,
but Dafny's heuristics can't figure out how to produce an enumeration for 'x'"`.

```dafny
var someReals := iset n | 0.0 <= x < 1.0;
foreach x <- someReals {  // Error: ...
  ...
}
```

The quantifier domain is allowed to be potentially infinite if an explicit `decreases` clause is provided.
`decreases *` is permitted in compiled contexts, in which the `foreach` loop may never terminate.
Any other `decreases` clause can be provided
to ensure the loop terminates even if the domain is potentially infinite. For example, the following example collects
at most five arbitrary primes (assuming that Dafny can figure out how to enumerate the `allPrimes` infinite set):

```dafny
var allPrimes := iset n | !exists i, j | 1 < i <= j < n :: i * j == n;
var fivePrimes := {};
foreach p <- allPrimes
  invariant |fivePrimes| <= 5
  decreases 5 - |fivePrimes|
{
  if |fivePrimes| == 5 { break; }
  fivePrimes := fivePrimes + [x];
}
// We can't assert |fivePrimes| == 5 here, since
// we haven't proven that the loop couldn't have terminated
// earlier by running out of primes.
// The decreases metric proves that the loop will terminate,
// but is only an upper bound on the number of iterations.
assert |fivePrimes| <= 5;
```

There will not initially (see Open Questions) be any builtin support for automatically tracking the enumerated values so far, 
as there is for `iterator` values (see https://dafny-lang.github.io/dafny/DafnyRef/DafnyRef#sec-iterator-types). 
It is straightforward to track these values manually, however:

```dafny
ghost var xs := [];
foreach x <- s {
  ...
  xs := xs + [x];
}
```

It is even possible to attach this ghost state directly to sequences with a helper function:

```dafny
foreach xAndXs <- WithPrefixes(c) {
  var (x, xs) := xAndXs;
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
foreach xAndI <- WithIndexes(s) {
  var (x, i) := xAndI;
  ...
}
```

## Sequence comprehensions

A sequence comprehension has identical syntax to a set comprehension, except that it begins with
`seq` rather than `set`. Therefore its syntax is:

```
SeqComprehension ::=
  "seq" 
  QuantifierDomain
  [ :: Expression ]
```

Sequence comprehensions are likely to be easier to work with than `foreach` loops, and Dafny users should be
encouraged to use them instead where possible. Many high-order operations on sequences can be expressed directly
using sequence comprehensions:

```dafny
// Filtering to optional values
var s: seq<Option<T>> := ...;
var filtered: seq<T> := seq o <- s | o.Some? :: o.value;

// Map and then flatten (a.k.a. "FlatMap")
var c: seq<S> := ...;
var f: S -> seq<T> := ...;
var flatMapped: seq<T> := seq x <- c, y <- f(x) :: y;

// Intersection of sequences
var a := [4, 1, 3, 5];
var b := [3, 1, 7];
assert (seq x <- a | x in b) == [1, 3];
assert (seq x <- b | x in a) == [3, 1];
```

Since sequence comprehensions are expressions rather than statements, they carry an additional restriction
when compiled: their ordering must be fully deterministic. If `s` is a `set<int>`, for example,
`seq x <- s` would be rejected in compiled code.
This is very similar to the restriction on `:|` let-such-that expressions, which is not relevant for equivalent
`:|` assign-such-that statements.

# Reference-level explanation
[reference-level-explanation]: #reference-level-explanation

As mentioned in the guide-level explanation, `foreach` loops and sequence comprehensions are both able to
borrow concepts and implementation substantially from other features. Parsing, resolving, verifying, and compiling
quantifier domains is already a mature aspect of the Dafny implementation. The most significant implementation burden
is ensuring that the required quantification ordering is threaded through the stack, 
and checked to be deterministic when used in compiled sequence comprehensions. 

## Verification

The optimal encoding of sequence comprehensions to Boogie is something of an open question:
set comprehensions are encoded as their indicator predicates, but there is no such direct representation
for sequence comprehensions as defined here. The initial encoding will likely be with a function,
similar to the `Seq#Create` function used for seq constructions, that accepts a source sequence and indicator predicate.
The useful axioms about these values will fall into three categories, sketched below for the simple
case of comprehensions with a single variable bound from a sequence:

`var S := seq x <- C | P(x) :: Q(x);`

1. Membership: `forall x :: x in C && P(x) ==> Q(x) in S`
2. Cardinality: `|S| <= |C|`
3. Ordering: `forall i, j | 0 <= i < j < |S| :: 
      exists i', j' | 0 <= i' < j' < |C| :: 
        Q(C[i']) == S[i] && Q(C[j']) == S[j]`

The translation of `foreach` loops should be reducible to sequence comprehensions
and other existing features for loops in general,
as the semantics of such loops can usually be expressed as follows:

```dafny
// A loop of this form:
foreach x1, x2, ..., xN {
  <Body>
}

// Is semantically equivalent to:
var __s := seq x1, x2, ..., xN :: (x1, x2, ..., xN);
for __i := 0 to |__s| {
  var (x1, x2, ..., xN) := __s[__i];
  <Body>
}
```

This is not a complete equivalency as the domain of `foreach` loop with explicit `decreaes` clauses
are allowed to be infinite. It may make sense to support encoding potentially infinite sequences in the Boogie prelude
even if they are not (yet) supported in Dafny, to close this gap.

## Compilation

The existing resolution logic for quantified domains in Dafny applies heuristics to identify
conjuncts in the range expression that define a bounded, potentially-enumerable set of values. The 
[`BoundedPool`](https://github.com/dafny-lang/dafny/blob/master/Source/Dafny/AST/DafnyAst.cs#L11487) type is used
to represent these cases, and models common patterns such as `0 <= i < n` (`IntBoundedPool`),
`x in s` (`CollectionBoundedPool`), enum-like datatypes with no parameterized constructors (`DatatypeBoundedPool`),
and `x == C` (`ExactBoundedPool`).
Different bounded pool types have different "virtues", including whether or not they are finite or enumerable.
In compiled contexts, Dafny will produce an error if it cannot identify at least one enumerable bound.

To support ordered quantification, this mechanism will be extended to include tracking the ordering these pools 
will enumerate values with. The `x <- C` syntax will be another potential `CollectionBoundedPool` source, and often one that encodes
an explicit enumeration order. The existing compilation logic treats ordering as pure implementation detail, 
and applies optimizations to try to make the search as short as possible. Ensuring consistent ordering is an additional 
constraint on this logic, applied only when the surrounding context is a sequence comprehension or `foreach` loop.

Each target language compiler already implements methods such as `CreateForEachLoop` to emit the implementation of
iterating over a particular `BoundedPool`.
One benefit to adding `foreach` loops to Dafny is that this logic can be refactored as a pure lowering translation
phase, rewriting quantification of many kinds to explicit `foreach` loop AST nodes, which can then be translated to
target languages constructs in later phases.

Note that quantifier variable domain collections do not necessarily have to be materialized as values!
In the expression `seq pair <- myMap.Items :: pair.1`, for example, a separate set value holding the contents of
`myMap.Items` does not have to be built at runtime. Only an enumerator or target-language loop of some kind
to enumerate over these values is necessary.

# Implementation plan

This RFC proposes a lot of functionality, which can be delivered in multiple smaller phases:

1. Quantifier variable domains and ranges.
   1. Adds the new syntax but rewrites it immediately after parsing.
2. Sequence comprehensions for a single quantified variable with a sequence source, only usable in ghost code.
   1. Depends on at least minimal support for ordered quantification.
   2. Ensures verification is effective before moving on to other derived features.
3. Compiling sequence comprehensions.
4. Other source collection types (`set`, `multiset`, etc.)
5. Multiple quantifier variables.
6. `foreach` loops.
7. etc.

It may even be possible to implement multiple extensions in parallel.

# Drawbacks
[drawbacks]: #drawbacks

The primary drawback to this proposal is the burden of adding the new concept of quantification ordering. 
This means extra cognitive load for Dafny users, extra implementation effort for any new builtin collection types, 
and additional testing to ensure that quantification domains are deterministically ordered when required.

The bounded pool heuristics described above are necessary in order to support compiling expressions such as set
comprehensions that are not computable in general. They come with the downside that it is less obvious to Dafny
programmers how their code will behave at runtime, and hence these new features come with
the same downside. Dafny is free to implement an expression like `seq x <- a | x in b` by either enumerating the values
of `a` and skipping those not in `b`, or by sorting the elements of `b` according to the ordering in `a`. This flexibility
is excellent for future optimizations, but makes it harder to reason about runtime performance.

It can be argued that if any compiled Dafny program uses existing features that depend on domain enumeration,
such as `exists` expressions or `:|` statements, its runtime behavior already depends heavily on how this domain
searching is implemented. The compiler only enforces that such domains are finite and enumerable, but an inefficient
choice can lead to the search for a matching value taking orders of magnitude more time than expected.
Therefore we should already be documenting this aspect of Dafny semantics and implementation better anyway, potentially
including communicating this through the IDE.

# Rationale and alternatives
[rationale-and-alternatives]: #rationale-and-alternatives

The primary rationale for this design is to leverage the fact that Dafny already heavily relies on expressing
quantification directly in the language, to the point that it already has a similar `forall` statement
expressed using the same quantification syntax. Allowing quantification to also
declare sequential bindings provides a lot of expressive power for a small language change,
and is just as composable with existing language features.

The most obvious alternative is to only provide the simpler `foreach x <- C` syntax, with only a single bound variable,
no additional filtering, and with `C` directly providing the enumeration and not just the ordering of values.
This is certainly a well-formed and sound construct, but far less powerful than the proposed version, especially
when sequence comprehensions are excluded. Offering `foreach` loops along with sequence comprehensions means we can 
recommend the latter where possible, with the former as a fallback that is inevitably more complicated to verify.

An earlier version of this proposal (https://github.com/dafny-lang/rfcs/pull/9) described an alternative
where the ordering and multiplicity of bindings was specified by clauses such as `x in C`
in a quantifier domain's range expression. 
This had the advantage of not requiring any new syntax, 
but also broke expectations of referential transparency of boolean expressions in these ordered contexts.

# Prior art
[prior-art]: #prior-art

Sequence comprehensions bear a strong resemblance to list comprehensions in Python, which also include similar abilities to 
bind multiple variables and filter the enumerated values: `[(x, y) for x in [1,2,3] for y in [3,1,4] if x != y]`.
Haskell and Cryptol also feature similar constructs.

Although the syntax `for[each] x in c` is more common, there is precedent for using the symbol `<-` instead in other languages,
including Scala, Cryptol, and Haskell. Using something other than `in` is recommended to avoid confusion with the `in` boolean operator,
but I don't have a strong opinion about which symbol or keyword we use.

Most mainstream programming languages include rich libraries for working with collections and iterators,
and define much the same operations such as "filter" and "flatMap".
The proposed Dafny features provide similar functionality at a higher level
of abstraction that will require less effort from Dafny programmers to successfully verify: 
quantification expressions are used to succinctly declare the behavior of
an operation that in spirit applies several such operations. See the "Future Possibilities" section for ideas for
pushing this philosophy even further.

The [JMatch language](https://www.cs.cornell.edu/andru/papers/padl03.pdf), an extension of Java to support
pattern matching, includes a `foreach` loop remarkably similar to the proposal here: it is parameterized by
a boolean expression and iterates through all matching bindings. For example, the statement `foreach(a[int i] != 0) n += i;`
sums the indices of all non-zero elements of the array `a`.

# Unresolved questions
[unresolved-questions]: #unresolved-questions

Tracking the values enumerated so far and/or the number of iterations in a `foreach` loop
is possible with manual helper functions as illustrated above, but only when the source collection is a sequence.
It may be a good idea in the next iteration of the feature to have convenient mechanisms for this,
if they are frequently requested. They may be best addressed when adding support for 
user-defined collection types and enumerators instead. Another possibility is supporting
parallel orderings as in Cryptol or Haskell, such that indexing an arbitrary collections could be expressed as
`seq x <- s (some symbol) i <- (0 to *) :: (s, i)`, but I don't see an obvious choice of syntax.

# Future possibilities
[future-possibilities]: #future-possibilities

Adding this building block to the Dafny language opens up a wide array of tempting new features!

## Pattern matching on quantifier variables

The LHS of `<-` declarations could be extended to allow case patterns, just as variable declaration statements do.
This would allow destructuring datatypes and tuples, as in `(k, v) <- myMap.Items`.
It could also support filtering, as in `Some(x) <- mySetOfOptionals`.
This would be consistent with how case patterns are used in match statements; these two loops would be equivalent, for example:

```dafny
foreach Some(x) <- [None, Some(42), None] {
  print x;
}

foreach o <- [None, Some(42), None] {
  match o {
    case Some(x) => print x;
  }
}
```

## User-defined collections

As discussed in the earlier [`for` loops RFC](https://github.com/dafny-lang/rfcs/pull/4), the semantics of
`for` or `foreach` loops in many programming languages are defined in terms of "iterator" or "enumerator" objects. 
The features proposed here only support builtin collections, but could easily be extended to support
arbitrary Dafny types that provide a way to obtain an enumerator for their contents.
[This PR](https://github.com/dafny-lang/libraries/pull/37) should be a good start towards designing
the necessary interface. This is also likely the best way to provide a better user experience
for looping or quantifying over the values produced by an `iterator` type.

## Range expressions

This would interpret the existing `i..j` syntax, 
currently only usable in sequence or array indexing expressions such as `s[i..j]`,
as an alternate option for expressing the sequence value `[i, i + 1, ..., j - 1]`.
To avoid actually materializing these values, range expressions would be implemented in the runtimes as a special case
`RangeSequence` type, similar to the existing lazily-evaluated `ConcatSequence` datatype in the C# and Java runtimes.
This would allow us to deprecate sequence constructions in favour of sequence comprehensions,
as any construction `seq(size, f)` could be rewritten as `seq i <- 0..size :: f(i)`.

## Ordered infinite collections

A quantifier variable domain only specifies the ordering of bindings and not necessarily how they are enumerated.
Just as a set comprehension like `set x: object | x in S1 && P(x)` 
may be enumerable even though the set of allocated objects are not,
we could introduce a variation of `iset` to represent partially-ordered sets,
so that `seq x <- objectsOrderedByFoo | x in S1 && P(x)` could provide a deterministically-ordered equivalent.

## Unicode strings

As I have previously ranted about in https://github.com/dafny-lang/dafny/issues/413, the Dafny `string` type is currently an alias
for `seq<char>`, where `char` is defined as a UTF-16 code units, and hence allows invalid sequences according to the semantics of
Unicode. Modelling unicode correctly will involve specifying that the semantic contents of a UTF-8 string, for example, is
a sequence of Unicode code points that is not efficiently accessed with indices. The features proposed here provide ways to work with
such datatypes efficiently at runtime.

## Compiled let-such-that expressions without uniqueness proofs

An expression `var x :| P(x); ...` is currently only allowed in compiled contexts
if Dafny can prove that there is exactly one such `x` that satisfies `P(x)`.
With ordered quantification in our toolbox, we could lift this requirement when
the quantification is ordered, and ensure that the first such `x` according to that
order is picked. This would probably necessitate allowing such statements to specify
variable domains as well, i.e. `var x <- C :| P(x); ...`.

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
collect(&&) x <- C | P(x) :: Q(x)         == forall x <- C | P(x) :: Q(x)
collect(||) x <- C | P(x) :: Q(x)         == exists x <- C | P(x) :: Q(x)
collect(SeqBuilder) x <- C | P(x) :: Q(x) == seq x <- C | P(x) :: Q(x)
collect(SetBuilder) x <- C | P(x) :: Q(x) == set x <- C | P(x) :: Q(x)
collect(+) x <- C | P(x) :: Q(x)          == (summation)
collect(*) x <- C | P(x) :: Q(x)          == (product)
collect(<) x <- C | P(x) :: Q(x)          == (minimum)
collect(Averager) x <- C | P(x) :: Q(x)   == (average)
collect(First(n)) x <- C | P(x) :: Q(x)   == Take(seq x <- C | P(x) :: Q(x), n)
...
```

This mirrors the `Collector` concept from the Java streaming APIs, and ideally the shape of the
parameter to `collect` expressions would define similar operations for merging intermediate results
to leave the door open for parallel or even distributed computation.
