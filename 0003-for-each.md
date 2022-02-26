- Feature Name: for_each_loops
- Start Date: 2022-02-22 (twosday!)
- RFC PR: [dafny-lang/rfcs#0000](https://github.com/dafny-lang/rfcs/pull/0000)
- Dafny Issue: [dafny-lang/dafny#1753](https://github.com/dafny-lang/dafny/issues/1753)

# Summary
[summary]: #summary

One paragraph explanation of the feature.

# Motivation
[motivation]: #motivation

* Why does Dafny need enumerators at all? Can't seq<T> do everything?
  * External code, especially I/O
  * Data structures that are not efficiently random access, strings
  * Accessibility for engineers less accustomed to functional programming. Dafny intentionally supports imperative programming
  * Easier verification of loops in general

Why are we doing this? What use cases does it support? What is the expected outcome?

# Guide-level explanation
[guide-level-explanation]: #guide-level-explanation

* [I]Enumerable type characteristic
  * "Enumerator() where the single return value is an [I]Enumerator"
    * May be baked-in for things like collections
  * Having this separate from Enumerator especially effective for Dafny, because
    higher-order operations on enumerables can be functions, unlike enumerators
* [I]Enumerator type characteristic
  * "Next() where the first return value is failure-compatible"
  * (Enumerator only) "Decreases() where the return values are usable in decreases clauses"
* Built-in Enumerable implementations, with Enumerators baked into runtime code
  * set<T> extends Enumerable<T>
    * DON'T want to customize by ordering, better to have users collect into an array and sort explicitly
  * multiset<T> extends Enumerable<T> (or Enumerable2<T, nat>?)
    * Perhaps offer both, or a convertor to `map<T, nat>`? Just `map(myMultiset)` is unambiguous.
  * seq<T> extends Enumerable<T>
    * Only case where ordering is guaranteed
  * map<K, V> extends Enumerable<(K, V)> (or Enumerable2<K, V>?)
  * (future) string extends Enumerable<char>
  * `iset` and `imap` should work too - type characteristics seem to line up with mathematical definition
  * enumerator for all values of a given type?? Can you always say `iset x: T | true`?
* Built-in expression for collecting to a sequence? Potentially much easier to implement internally
* Built-in expression for casting an `iterator` to an enumerable/enumerator?
  * Could have all existing iterators now have a `Next()` method as well.
  * Can't infer `Decreases()` though :(
* Standard library implementations and combinators
  * Will likely assume tighter definitions of type characteristics that fit into traits
  * Trait limitations may improve over time!
* TODO: How to provide "with index" as nicely as possible?
  * Two decent options, `foreach` allows either:
    * `foreach (x, index) in WithIndex(e) { ... }` (`Enumerable<(T, nat)>`)
    * `foreach x, index in WithIndex(e) { ... }` (`Enumerable2<T, nat>`)
  * Don't see the need for backing this into the feature
* `foreach` loop:
  * almost like a compiled `forall`
  * Three options for termination:
    * No `decreases` ==> default to `decreases iter.Decreases()`
    * `decreases *` ==> supports `IEnumerable<T>`
    * other `decreases` ==> not touched
  * No way to explicitly reference `iter` in a manual `decreases` clause, but if you want that write your own `[I]Enumerable<T>` wrapper.

  
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

Issue: there's no implication of predictible ordering! There's the "below" ordering
but that doesn't necessarily enduce an enumeration.

method ToArray<T(0)>(e: SizedEnumerable<T>) returns (result: array<T>)
  ...
{
  new T[e.count];
  foreach element, index in WithIndex(e)
    invariant result[0..index] == elements // Best way to refer to values looped over so far?
  {
    result[index] := element.value;
  }
```

```dafny
  for <LHS> in <E> 
    invariant <I>
    modifies <M>
  {
    <fBody>
  }

  ==>

  var __e := <E>.Enumerator();
  while __e.HasNext() 
    invariant __e.Valid() && fresh(e.Repr)
    decreases __e.Decreases()

    invariant <I>
    modifies <M>
  {
    var __element := __e.Next();  // Method call
    // Allow case pattern destructuring 
    var <LHS> := __element;       // Variable declaration

    <fBody>
  }

  trait Enumerable<T> {
    // TODO: How to attach extra invariants?
    // I don't think we want to attach a ghost var
    // here of the elements that will be enumerated,
    // but some use cases will definitely want that.
    method Enumerator returns (e: Enumerator<T>)
      ensures e.Valid()
      ensures fresh(e.Repr)
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
* Could just define `foreach` for built-in collection types
* Could avoid assuming that Enumerators modify the heap
  * Alternative of `Next(): (t, e')`, where `e' == e` can often work if it's an object
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

* How to support concurrency in the future? Anything cheap we can do to be more forward-compatible?

- What parts of the design do you expect to resolve through the RFC process before this gets merged?
- What parts of the design do you expect to resolve through the implementation of this feature before stabilization?
- What related issues do you consider out of scope for this RFC that could be addressed in the future independently of the solution that comes out of this RFC?

# Future possibilities
[future-possibilities]: #future-possibilities

* Adding chaining methods to Enumerator/Enumerable
* Batch optimization of the above
  * Requires allowing subclasses to override default implementations