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

*** TODO ***

Perhaps the most serious shortcoming is that there is currently no efficient way to iterate over the elements of a `set`.
The best alternative is to use the assign-such-that operator and set subtraction, illustrated in the reference manual as follows (sec 19.6):

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
including binding multiple variables at once, and filtering:

```dafny
var myDoubleDeckerSeq: seq<seq<int>> := ...;
foreach x, y | x in myDoubleDeckerSeq && y in x && y != 0 {
  Process(x);
}
```

The high-level syntax for a `foreach` loop reuses several existing concepts:

```
ForeachLoop ::=
  "foreach" QuantifierDomain LoopSpec Body
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

TODO:

  * Any quantifier domain implicitly defines a collection of bound variable values that satisfy it
    * Error if the domain is not enumerable
    * Error if the domain is not finite and `decreases *` is not specified
  * Ordering determined by domain:
    * By far the most common will be `x in c`, and usually `c` will be a `seq`
    * Define rules like associativity that determines ordering. Mostly left overrides right.
      * `x in A && x in B` -> `A.Enumerator().Filter(B.Contains)`
      * `x in A || x in B` -> `A.Enumerator().Concat(B.Enumerator())`
      * `x !in A` -> `(seq x: T).Enumerator().Filter(x => x !in A)`
      * `x in A && y in B` -> `A.Enumerator().CrossProduct(B.Enumerator())` (or nested loop depending on context)
      * Simplest if every subexpression must be enumerable, even if there are cases where that's not necessary
    * The good news is if you care about the ordering and try to prove something based on an incorrect understanding of the
      enumeration order, verification will fail.

There is no builtin support for automatically tracking the enumerated values so far, as there is for
`iterator` values (see https://dafny-lang.github.io/dafny/DafnyRef/DafnyRef#sec-iterator-types). 
It is straightforward to track these values manually, however:

```dafny
ghost var xs := [];
foreach x | x in s {
  ...

  xs := xs + [x];
}

It is even possible to attach this ghost state directly to the sequence with a helper function:

```dafny
foreach x, xs | (x, xs) in WithPrefixes(s) {
  ...
}

Where the signature of `WithPrefixes` is something like:

```dafny
function method WithPrefixes<T>(s: seq<T>): seq<(T, ghost seq<T>)> {
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
`forall` expressions are the analogues of `forall` statements.

The existing `seq(k, n => n + 1)` syntax is inconsistently-named in the Dafny reference manual, but we refer to it here as
a "sequence construction" expression, to disambiguate it from the proposed sequence comprehension feature.
Sequence comprehensions are strictly more expressive, as any construction `seq(size, f)` can be rewritten as 
`seq i | 0 <= i < size :: f(i)`.

TODO:

  * Probably more useful than `foreach` loops and should be encouraged where possible.
  * Examples:
    * Flatmap: `seq x, y | x in c && y in f(x) :: y`
    * Collapsing options: `seq x | x in c && x.Some? :: x.value`
    * Zipping: `seq 0 <= i < |s| :: (s[i], t[t])`




## Notes

* [I]Collection type characteristic
  * "Enumerator() where the single return value is an [I]Enumerator"
    * Baked-in for built-in collection types
  * Having this separate from Enumerator especially effective for Dafny, because
    higher-order operations on collections can be functions, unlike enumerators
  * Even `Option<T>` can be a collection!
    * `match o case Some(v) => { print v; }` => `foreach v in o { print v }`
    * Other Wrappers could be too, but more questionable
* [I]Enumerator type characteristic
  * "Next() with a single return value"
  * (Enumerator only) "Decreases() where the return values are usable in decreases clauses"
* Built-in Collection implementations, with Enumerators baked into runtime code
  * set<T> extends Collection<T>
    * DON'T want to customize by ordering, better to have users collect into an array and sort explicitly
  * multiset<T> extends Collection<T>
    * Also convertor to `map<T, nat>`, so you can enumerate multiplicity pairs instead: Just `map(myMultiset)` is unambiguous.
  * seq<T> extends Collection<T>
    * Only case where ordering is guaranteed
  * map<K, V>.Items/Keys/Values enumerable through the above
  * (future) string extends Collection<char>
  * `iset` and `imap` should work as ICollections too - type characteristics seem to line up with mathematical definition
  * enumerator for all values of a given type?? Can you always say `iset x: T | true`?
* Add ranges as collections as well?
  * `foreach x in lo..hi { ... }` equivalent to `for x := lo to hi { ... }`
  * Nice for sequence comprehensions as well: `seq i in 0..|s| :: s[i] + 1`
* Built-in expression for collecting to a sequence? Potentially much easier to implement internally
  * See alternate `seq` comprehension syntax below
* Built-in expression for casting an `iterator` to an enumerable/enumerator?
  * Could have all existing iterators now have a `Next()` method as well.
  * Can't infer `Decreases()` though :(
    * Might be possible to attach `Decreases` extrinsically though!
  * Might work better to cast an iterator value as an enumerator of itself:
    * `foreach i in seq(MyIterator) { print i.key, i.value; }`
  * Might be just too much of a stretch, iterators need specific specs to work as enumerators, just make users do it themselves
* Standard library implementations and combinators
  * Will likely assume tighter definitions of type characteristics that fit into traits
  * Trait limitations may improve over time!
* For each with index:
  * `foreach (x, index) in WithIndex(e) { ... }`
  * Don't see the need for baking this into the feature
  * OR: `foreach x, index | 0 <= index < |e| && x == e[index]`
* `foreach` loop:
  * almost like a compiled `forall`
    * Key difference is executing the body once for each value in sequence, instead of all simultaenously
    * By default needs to be finite, whereas only the parallel-assignment kind of forall statement needs to be
  * Three options for termination:
    * No `decreases` ==> default to `decreases iter.Decreases()`
    * `decreases *` ==> supports `IEnumerable<T>`
    * other `decreases` ==> not touched
    * No way to explicitly reference `iter` in a manual `decreases` clause, but if you want that write your own `[I]Enumerable<T>` wrapper.
  * How to refer to values already enumerated?
    * We don't like the `elements` trick `iterators` pull (but this would be consistent)
    * Syntax to bind values enumerated so far? No precedent for this in other languages AFAICT
    * Almost want additional specification clauses, similar to `yield ensures`, possibly leveraging `old`?
    * Instead: `foreach (x, xs) in WithEnumerated(c)`
      * This will be very common since you can't prove semantics (as opposed to just safety) without it
      * Making it not strictly necessary helps new users get started, as long as we document the pattern above well
      * TODO: need to try an actual proof with this
  * Alternate sequence comprehension
    * `seq x | x in c && x % 2 == 0 :: Cell(x)` - filter_map!
      * Getting to be like Python!
      * Common: `seq x in c | x.Some? :: x.value` - otherwise have to do `Seq.Map(x requires x.Some? => x.value, Seq.Filter(x => x.Some?, c))`
      * `c` must be a "sized" enumerable (?) - probably means defining `.Size()` or something
        * Really only as an optimization
    * Array comprehension? `new int[] from c`
      * Only way I can think of to avoid needing `T(0)`
      * Doesn't generalize to multi-dimensional arrays though
    * Need a `function-by-method` kind of verification that it's legal to have an expression like this implemented with objects and temporary state
      * Should be valid as long as semantics are tied to effects on `e.enumerated`
    * Allows easy conversion of set to sequence: `seq x | x in mySet`
    * Could replace existing index-based comprehension too:
      * `seq i in Range(0, 10) :: f(i)` or even `seq i in 0..10 :: f(i)`
    * Semantic equivalence:
      * `seq x: T | x in c && P(x) :: Q(x)` == `Collections.Map(x => Q(x), Collections.Filter(x => P(x), c))`
        * if the domain expression does not include a `x in c`, then `c` defaults to `set x: T | true`, and may fail if `T` is not finite
      * Need to generalize this to multiple bound variables
* Should there also be a `foreach` expression?
  * That's more or less what the alternate seq comprehension is
  * Should it be `for x in c ...` instead?
    * Probably not, more consistent with other comprehensions to start with the type kind keyword
  * Handling `in` in general should allow `forall` expressions to do what we'd want
* `LHS in RHS` becomes another standard piece of syntax similar to QuantifierDomain, in both `foreach` and `seq` comprehensions
  * Better to use a different keyword to indicate ordering?
    * Ordering already indirectly observable at runtime, since you can compile `:|` and observe how long it takes to find a solution :)
  * Support `x in c` expression for ANY finite collection c? Always computable, but usually not efficient unless specialized!
    * Already true for sequences, so already something to be cautious of
  * `if x :| x in c { ... }`?
  * Technically can support: `foreach b: bool { print b; }`
  * Technically can support: `foreach x: T | P(x) { print b; }`
    * Describing the ordering just gets interesting :)
    * What is the ordering here? `foreach x | x in C1 && x in C2 { print x; }`
      * The good news is you can try to prove whatever you think it is and find out :)



  
```dafny
foreach s in ["Sally", "Mike", "John"] {
  print "Hello ", s, "!\n";
}

foreach s: nat
  decreases *
{
  print "Hello ", s, "!\n";
}

(short form for)

foreach s in iset x: nat | true 
  decreases *
{
  print "Hello ", s, "!\n";
}

method ToArray<T(0)>(e: SizedEnumerable<T>) returns (result: array<T>)
  ...
{
  new T[e.count];
  foreach (element, index, elements) in WithIndexAndEnumerated(e)
    invariant result[0..index] == elements
  {
    result[index] := element.value;
  }
```

* `foreach <LHS> in <E> { ... }` is just a short-form for `foreach <vars bound in LHS> | <LHS> in <E> { ... }`

```dafny
  foreach LHS in <E> 
    invariant <I>
    modifies <M>
    decreases <D>
  {
    <fBody>
  }

  ==>

  var __e := <E>.Enumerator();
  while __e.HasNext() 
    invariant __e.Valid() && fresh(__e.Repr)
    decreases __e.Decreases() // If no explicit decreases

    invariant <I>
    modifies <M>
    decreases <D>
  {
    var __next := __e.Next();  // Method call
    if __next.IsFailure() {
      break;
    }
    var LHS := __next.Extract(); // Allows destructuring. 
                                 // Assumes Extract is a function, can we lock that down? Do we have to?

    <fBody>
  }

  // Implicit trait probably not actually in stdlib.
  trait Enumerable<T> {

    // TODO: Don't want to flat-out require "contents: seq<T>"
    // because we want to allow it to be expensive or complicated
    // to calculate or track in ghost state, or even non-deterministic.
    // But we do want to assert the connection between the contents
    // of this value and what will be enumerated by the enumerator somehow.
    // Could make it a function instead, but still doesn't avoid having
    // to define a body if you're compiling your Dafny code.
    // In a way the Enumerator method spec IS the spec of your contents.
    // We might need an additional predicate of some kind.

    // Can attach properties of what is to be enumerated
    // with specializations of the trait.
    method Enumerator() returns (e: Enumerator<T>)
      ensures e.Valid()
      ensures fresh(e.Repr)

    // Default, O(n) implementation
    // TODO: Orthogonal feature of default implementations.
    // In this case the spec can be used as the default implementation!
    function method Contains(t: T) {
      exists x in this :: x != t
    }
  }
```

Explain the proposal as if it was already included in the language and you were teaching it to another Dafny programmer. That generally means:

- Introducing new named concepts.
- Explaining the feature largely in terms of examples.
- Explaining how dafny programmers should *think* about the feature, and how it should impact the way they use Dafny. It should explain the impact as concretely as possible.
- If applicable, provide sample error messages, deprecation warnings, or migration guidance.
- If applicable, describe the differences between teaching this to existing Dafny programmers and new Dafny programmers.

For implementation-oriented RFCs (e.g. for compiler internals), this section should focus on how compiler contributors should think about the change, and give examples of its concrete impact.

# Reference-level explanation
[reference-level-explanation]: #reference-level-explanation

* Mostly implemented through desugaring
  * Just need to translate resolution and verification errors back well
* Can compilers/runtimes leverage the logic for comprehensions that already have to iterate over all possible values?

This is the technical portion of the RFC. Explain the design in sufficient detail that:

- Its interaction with other features is clear.
- It is reasonably clear how the feature would be implemented.
- Corner cases are dissected by example.

The section should return to the examples given in the previous section, and explain more fully how the detailed proposal makes those examples work.

# Drawbacks
[drawbacks]: #drawbacks

Why should we *not* do this?

# Rationale and alternatives
[rationale-and-alternatives]: #rationale-and-alternatives

* Could overload `for LHS in RHS` so we didn't need another keyword
  * Doesn't read quite as well since the RHS won't name individual values like `0 to 10` does
* Could just define `foreach` for built-in collection types
* Could extend `forall` statements to support compilation as well
  * Probably only support specific syntax
  * Semantics don't match - `forall` has simultaneous semantics, allowing things like swaps (?), but we need sequential execution
  * But parallel evaluation of `forall`s could be really nice in the future! Prove disjointness and therefore safety.
* Could avoid assuming that Enumerators modify the heap
  * Alternative of `Next(): (t, e')`, where `e' == e` can often work if it's an object
  * Doesn't seem worth it - a single object allocation for a tree of datatypes is cheap
* Could use an alternative API for Enumerator
  * (multiple options to cover)
  * Wacky option:
```
  while x :- e.Next() 
    decreases e.Decreases()
  {

  }
```

- Why is this design the best in the space of possible designs?
- What other designs have been considered and what is the rationale for not choosing them?
- What is the impact of not doing this?

# Prior art
[prior-art]: #prior-art

Discuss prior art, both the good and the bad, in relation to this proposal.
A few examples of what this can include are:

- For language, library, tools, and compiler proposals: Does this feature exist in other programming languages and what experience have their community had?
- For community proposals: Is this done by some other community and what were their experiences with it?
- For other teams: What lessons can we learn from what other communities have done here?
- Papers: Are there any published papers or great posts that discuss this? If you have some relevant papers to refer to, this can serve as a more detailed theoretical background.

This section is intended to encourage you as an author to think about the lessons from other languages, provide readers of your RFC with a fuller picture.
If there is no prior art, that is fine - your ideas are interesting to us whether they are brand new or if it is an adaptation from other languages.

Note that while precedent set by other languages is some motivation, it does not on its own motivate an RFC.

# Unresolved questions
[unresolved-questions]: #unresolved-questions

* How valuable is it to support multiple enumerated values, as opposed to assuming tuple results instead?
* How to support concurrency in the future? Anything cheap we can do to be more forward-compatible?
* `Repr` hasn't actually been added to the stdlib yet, and iterators define `_reads`, `_modifies`, etc.
  instead. What do for enumera[ble|tor]s?

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