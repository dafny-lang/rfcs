- Feature Name: for_each_loops
- Start Date: 2022-02-22 (twosday!)
- RFC PR: [dafny-lang/rfcs#9](https://github.com/dafny-lang/rfcs/pull/9)
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

A more serious shortcoming is that there is currently no efficient way to iterate over the elements of a `set` at all.
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

The domain is allowed to be potentially infinite if the loop is used in a compiled context and an explicit `decreases` clause is provided.
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
This includes expressions like `m.Keys`, `m.Values` and `m.Items` when `m` is a `map`.
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

Note that the existing `seq(size, i => i + 1)` syntax is inconsistently-named in the Dafny reference manual, 
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

The general rules for ordering are syntax-driven and recursively-defined for any boolean expression. A sketch of
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
so that the worst case runtime of lookups is O(N log N) rather than O(N).
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

The most obvious alternative is to only provide the simpler `foreach x in C` syntax, where `C` is any collection value.
This is certainly a well-formed and sound construct, but far less powerful than the proposed version, especially
when sequence comprehensions are excluded. It also still runs into some of the same semantic challenges around
ordering if `C` is allowed to be a set or multiset anyway, since verification of such a loop still needs to be aware of
this ordering. Offering `foreach` loops along with sequence comprehensions means we can recommend the latter where possible,
with the former as a fallback that is inevitably more complicated to verify.

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

The [JMatch language](https://www.cs.cornell.edu/andru/papers/padl03.pdf), an extension of Java to support
pattern matching, includes a `foreach` loop remarkably similar to the proposal here: it is parameterized by
a boolean expression and iterates through all matching bindings. For example, the statement `foreach(a[int i] != 0) n += i;`
sums the indices of all non-zero elements of the array `a`. The JMatch version declares the bound variables inline in
the boolean expression, which is also proposed here as a future possibility below.

# Unresolved questions
[unresolved-questions]: #unresolved-questions

One large open question is how difficult it will be to convince the verifier the following is correct,
since it will be a common idiom for depending on the unpredictable enumeration ordering of a set:

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

Adding these building blocks to the Dafny language opens up a wide array of tempting new features!

## User-defined collections

As discussed in the earlier [`for` loops RFC](https://github.com/dafny-lang/rfcs/pull/4), the semantics of
`for` or `foreach` loops in many programming languages are defined in terms of "iterator" or "enumerator" objects. 
The features proposed here only support builtin collections, but could easily be extended to support
arbitrary Dafny types that provide a way to obtain an enumerator for their contents.
[This PR](https://github.com/dafny-lang/libraries/pull/37) should be a good start towards designing
the necessary interface. This is also likely the best way to provide a better user experience
for looping or quantifying over the values produced by an `iterator` type.

## Short-form quantifier domains

This would be independent syntactic sugar to avoid the repetition of bound variables in quantifier
expressions and comprehensions. It would allow a loop such as:

```dafny
foreach x | x in mySeq {
  ...
}` 
```

to be shortened to:

```dafny
foreach x in mySeq
```

Or:

```dafny
foreach k, v | (k, v) in myMap.Items {
  ...
}
```

to:

```dafny
foreach (k, v) in myMap.Items {
  ...
}
```

In general, it would allow omitting the list of bound variables in a quantifier domain expression and instead automatically
infer them from the list of free variables in the range expression.

## Unicode strings

As I have previously ranted about in https://github.com/dafny-lang/dafny/issues/413, the Dafny `string` type is currently an alias
for `seq<char>`, where `char` is defined as a UTF-16 code units, and hence allows invalid sequences according to the semantics of
Unicode. Modelling unicode correctly will involve specifying that the semantic contents of a UTF-8 string, for example, is
a sequence of Unicode code points that is not efficiently accessed with indices. The features proposed here provide ways to work with
such datatypes efficiently at runtime.

## More flexible conjunction enumerations

The proposed definition of domain ordering only allows the LHS of a conjunction to drive the primary enumeration,
but this could be loosened to support enumerating via the RHS and only ordering according to the LHS.
This would provide a succinct way to extract the values from a set in a fully predictable ordering, for example:

```dafny
var setOfReals := {3.141, 2.718, 1.618};
var sortedList := seq x | x is real && x in setOfReals;
assert sortedList == {1.618, 2.718, 3.141};
```

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
