- Feature Name: reads_clauses_on_methods
- Start Date: 2021-09-17
- RFC PR: [dafny-lang/rfcs#0000](https://github.com/dafny-lang/rfcs/pull/0000)
- Dafny Issue: [dafny-lang/dafny#0000](https://github.com/dafny-lang/dafny/issues/0000)

# Summary
[summary]: #summary

This proposal simply adds support for optional `reads` clauses on methods, just as they are already supported on functions. While the default for functions is disallowing all reads (i.e. `reads {}`) the default for methods would be allowing all reads (i.e. `reads *`), allowing full backwards-compatibility.

# Motivation
[motivation]: #motivation

Dafny currently has no direct support for concurrency. The soundness of method verification depends on the assumption that no modification to mutable state occurs other than what is present in the method body. Consider this example of a Dafny class with internal state:

```dafny
class Counter {
  var x: int
  constructor() {
    x := 0;
  }
  function method Get() 
    reads this
    ensures Get() == x
  {
    x
  }
  method Increment() 
    modifies this
    ensures x == old(x) + 1
  {
    x := x + 1;
  }
}
```

If this class is compiled to C#, for example, and its instances are shared between multiple threads, its verified properties are no longer true. If two threads both invoke `Increment` on a single counter, the effect could easily be to only increment `x` once, since reading and writing `x` does not occur atomically. Even the post-condition on `Get` is no longer valid, because the value of `x` could change in-between reading its value and returning from the compiled body.

This proposal does not aim to add concurrency primitives to Dafny, or even propose any particular choice of paradigm for asynchronous or concurrent execution. Instead it supports verifying that a particular method is safe to use in a concurrent environment, by verifying that it does not operate on any mutable state unsafely.

# Guide-level explanation
[guide-level-explanation]: #guide-level-explanation

In most Dafny code, you will not have to specify a reads clause on any methods, as they are permitted to read any mutable state by default. In some cases the specification for a method needs to be more precise. In particular, invoking a compiled method from external, native code in a concurrent environment is much more likely to be safe if the method does not read or write any shared mutable state. It is now possible to specify this requirement by using `reads` clauses on methods as well as functions. For example:

```dafny
method {:extern} Fibonacci(n: nat) returns (r: nat)
  reads {}
{
  var x, y := 0, 1;
  for i := 0 to n {
    x, y := y, x + y;
  }
  return x;
}

// Attempting to memoize the fibonacci function with a shared cache.

class Box<T> {
  var value: T
  constructor(value: T) {
    this.value := value;
  }
}

method {:extern} UnsafeMemoizedFibonacci(n: int, cacheBox: Box<map<nat, nat>>) returns (r: nat)
  reads {}
{
  var cache := cacheBox.value; // Error: insufficient reads clause to read field
  if n in cache.Keys { 
    r := cache[n];
  } else {
    r := Fibonacci(n);
    cacheBox.value := cache[n := r];
  }
}

```


This is most effective when the person providing the specification is different from the person implementing it. It ensures that the implementation cannot interact with shared state by accident, especially deep within shared libraries that are perfectly safe to use in a single-threaded context.

When shared state is neccessary 

Explain the proposal as if it was already included in the language and you were teaching it to another Dafny programmer. That generally means:


- Explaining the feature largely in terms of examples.
- Explaining how dafny programmers should *think* about the feature, and how it should impact the way they use Dafny. It should explain the impact as concretely as possible.
- If applicable, provide sample error messages, deprecation warnings, or migration guidance.
- If applicable, describe the differences between teaching this to existing Dafny programmers and new Dafny programmers.


# Reference-level explanation
[reference-level-explanation]: #reference-level-explanation

This is the technical portion of the RFC. Explain the design in sufficient detail that:

- Its interaction with other features is clear.
- It is reasonably clear how the feature would be implemented.
- Corner cases are dissected by example.

The section should return to the examples given in the previous section, and explain more fully how the detailed proposal makes those examples work.

# Drawbacks
[drawbacks]: #drawbacks

The biggest potential drawback is that inexperienced Dafny programmers might have the incorrect impression that defining a tight `reads` clause for methods is necessary, and hence expend unnecessary effort for no benefit. ***

Why should we *not* do this?

# Rationale and alternatives
[rationale-and-alternatives]: #rationale-and-alternatives

- Why is this design the best in the space of possible designs?
- What other designs have been considered and what is the rationale for not choosing them?
- What is the impact of not doing this?

# Prior art
[prior-art]: #prior-art

The most obvious prior art for this is the existing support for `reads` on function definitions.

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

- What parts of the design do you expect to resolve through the RFC process before this gets merged?
- What parts of the design do you expect to resolve through the implementation of this feature before stabilization?
- What related issues do you consider out of scope for this RFC that could be addressed in the future independently of the solution that comes out of this RFC?

# Future possibilities
[future-possibilities]: #future-possibilities

Think about what the natural extension and evolution of your proposal would
be and how it would affect the language and project as a whole in a holistic
way. Try to use this section as a tool to more fully consider all possible
interactions with the project and language in your proposal.
Also consider how the this all fits into the roadmap for the project
and of the relevant sub-team.

This is also a good place to "dump ideas", if they are out of scope for the
RFC you are writing but otherwise related.

If you have tried and cannot think of any future possibilities,
you may simply state that you cannot think of anything.

Note that having something written down in the future-possibilities section
is not a reason to accept the current or a future RFC; such notes should be
in the section on motivation or rationale in this or subsequent RFCs.
The section merely provides additional information.