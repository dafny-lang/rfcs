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

This proposal does not aim to add concurrency primitives to Dafny, or even propose any particular choice of paradigm for asynchronous or concurrent execution. Instead, it supports verifying that a particular method is safe to use in a concurrent environment, by verifying that it does not operate on any mutable state unsafely.

# Guide-level explanation
[guide-level-explanation]: #guide-level-explanation

In most Dafny code, you will not have to specify a reads clause on any methods, as they are permitted to read any mutable state by default. In some cases the specification for a method needs to be more precise, however. In particular, invoking a compiled method from external, native code in a concurrent environment is much more likely to be safe if the method does not read or write any shared mutable state. It is now possible to specify this requirement by using `reads` clauses on methods as well as functions. For example:

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

// TODO: example of permitted thread-local mutable state. Perhaps change to a polynomial datatype
// which would like to use a stateful Fold-er type thingy over a sequence?

```

This is most effective when the person providing the specification is different from the person implementing it. It ensures that the implementation cannot interact with shared state by accident, especially deep within shared libraries that are perfectly safe to use in a single-threaded context.

When shared state is necessary, it must be implemented externally in native code, which case native facilities for synchronizing access mutable state.

```dafny
TODO
```

The wiki page on [Modelling External State Correctly](https://github.com/dafny-lang/dafny/wiki/Modeling-External-State-Correctly) would be updated to recommend that methods exposed to concurrent native code should include `reads {}` and omit any `modifies` clauses.

# Reference-level explanation
[reference-level-explanation]: #reference-level-explanation

This is the technical portion of the RFC. Explain the design in sufficient detail that:

- Its interaction with other features is clear.
- It is reasonably clear how the feature would be implemented.
- Corner cases are dissected by example.

The section should return to the examples given in the previous section, and explain more fully how the detailed proposal makes those examples work.

# Drawbacks
[drawbacks]: #drawbacks

The biggest potential drawback is that inexperienced Dafny programmers might have the incorrect impression that defining a tight `reads` clause for methods is necessary, and hence expend unnecessary effort for no benefit. The verifier would never prompt users to add `reads` clauses unless they already appear elsewhere in a codebase, so the issue is more that they could see them used in documentation or examples and not realize they are largely optional.

Reusable Dafny code such as the modules in https://github.com/dafny-lang/libraries will need to specify `reads` clauses in order to support consumers that need to specify them. This does not appear to be a significant burden: at the time of writing this the `libraries` repo only contained one `method`. All other uses of the `method` keyword were in defining `function method`s instead, which already default to `reads {}` and hence can be used as is in the control flow of methods with `reads` clauses. Again, the issue is more that readers could imitate standard library `method` definitions and include superfluous `reads` clauses. The answer is likely to document explicitly why the standard library uses this feature and to emphasize that it should not be copied blindly. There is already a similar issue with the standard library's use of `{:trigger}` attributes, which are not encouraged in most Dafny codebases.

There is a chance that if and when explicit concurrency support is added to Dafny, the much more limited solution of verifying a method body `reads` and `modifies` nothing may become unused. This would make supporting `reads` clauses on methods harmless but also a maintenance burden. On the other hand, the feature is a generic and independent concept with relatively low implementation complexity, and the extra information provided by `reads` clauses is potentially useful for verifier and compiler optimizations in the future. There is a reasonable chance that `reads` clauses will be part of the future solution for concurrency anyway.

# Rationale and alternatives
[rationale-and-alternatives]: #rationale-and-alternatives

- 

- Expect Dafny users to synchronize

- Add direct support for concurrency to Dafny.


- Why is this design the best in the space of possible designs?
- What other designs have been considered and what is the rationale for not choosing them?
- What is the impact of not doing this?

# Prior art
[prior-art]: #prior-art

The most obvious prior art for this is the existing support in Dafny itself for `reads` on function definitions and `modifies` on methods. The implementation overlaps substantially with both, and mainly consists of allowing both kinds of frames to be defined and verified at once for method bodies.

# Unresolved questions
[unresolved-questions]: #unresolved-questions

- Are there other use cases for this feature worth mentioning, aside from external thread-safety?

- Ideas for how Dafny should tackle asynchronous or concurrent execution in general are out of scope for this particular RFC, but still worth discussing in case they influence any immediate decisions in the name of forwards-compatibility.

# Future possibilities
[future-possibilities]: #future-possibilities

*** Point to adding concurrency support to Dafny itself, so it's not necessary
to have shared mutable state in native code. ***

TODO:

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