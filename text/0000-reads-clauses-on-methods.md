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

In most Dafny code, you will not have to specify a reads clause on any methods, as they are permitted to read any mutable state by default. In some cases the specification for a method needs to be more precise, however. In particular, invoking a compiled method from external, native code in a concurrent environment is much more likely to be safe if the method does not read or write any shared mutable state. It will now be possible to specify this requirement by using `reads` clauses on methods as well as functions.

Let's consider a case where we want to provide some Dafny-implemented functionality to external code. Let's use our favorite example, the Fibonacci sequence. Assume that this needs to work in at least one language with threads and shared memory, such as C# or Java. Knowing that is a requirement, one way to meet it is to ensure that the Dafny code does not read or write any shared mutable state:

```dafny
// Here {:extern} is used to allow external code to invoke this method,
// rather than indicate it will be externally implemented.
method {:extern} Fibonacci(n: nat) returns (r: nat)
  reads {}
  // modifies {} is the default so it can be omitted 
{
  ...
}
```

Suppose you want to add some caching as we implement this, since the results of one call can be reused by others. We need to have clients pass in the cache since Dafny offers no way to store it as global state (which is frankly a good thing). Our first attempt leads to a verification error, however, which saves us from accidentally introducing a race condition!

```dafny

class FibonacciMemoizer {
  var cache: map<nat, nat>
  constructor() reads {} {
    cache := map[];
  }
  method Get(n: nat) returns (r: nat) 
    modifies this
  {
    if n <= 2 {
      return 1;
    }
    if n in cache {
      r := cache[n];
    } else {
      var oneBefore := Get(n - 1);
      var twoBefore := Get(n - 2);
      r := oneBefore + twoBefore;
      // This line introduces a race condition in multi-threaded target languages.
      // Updating two different entries concurrently can lead to one of them being dropped!
      cache := cache[n := r];
    }
  }
}

method {:extern} Fibonacci(n: nat, memoizer: FibonacciMemoizer) returns (r: nat)
  reads {}
{
  r := memoizer.Get(n);   // Error: insufficient reads clause to invoke method
                          // Error: call may violate context's modifies clause
}
```

Note that this technique is most effective when the person providing the specification is different from the person implementing it. It ensures that the implementation cannot interact with shared state by accident, especially deep within shared libraries that are perfectly safe to use in a single-threaded context. The wiki page on [Modelling External State Correctly](https://github.com/dafny-lang/dafny/wiki/Modeling-External-State-Correctly) would be updated to recommend that methods exposed to concurrent native code should include `reads {}` and omit any `modifies` clauses.

The nature of frame specifications in Dafny makes `reads {}` less restrictive than it might appear. First of all, it only specifies that a method reads no *mutable* fields. `const` declarations on classes are still fair game. It also only forbids reading *existing* mutable state. It is legal to allocate new mutable objects and modify their fields, either inline or by calling other methods. This means that creating and sharing a cache between multiple calculations within a single externally-exposed method is permitted:

```dafny
method {:extern} FirstNFibonaccis(n: nat) returns (rs: seq<nat>)
  reads {}
{
  var memoizer := new FibonacciMemoizer();
  rs := [];
  for i := 1 to n + 1 {
    var r := memoizer.Get(i);
    rs := rs + [r];
  }
}
```

When sharing state externally really is necessary, it must be implemented externally in native code, where native facilities for synchronizing access to mutable state can be used. Therefore the solution is to push the caching logic into the target language instead:

```dafny
datatype Option<T> = Some(value: T) | None

//
// Wrapper around a concurrent data structure, such as
// ConcurrentHashMap<K, V> in Java.
//
// Note the lack of a ghost variable to track the state of the map,
// which intentionally puts the mutable state outside of the Dafny-verified model.
// These methods instead appear to have non-deterministic behavior to Dafny, which accurately
// represents the fact that it cannot assume anything about state that might be changed by
// other threads.
//
class {:extern} ExternalMutableMap<K, V> {
  constructor {:extern} () reads {}
  method {:extern} Put(k: K, v: V) reads {}
  method {:extern} Get(k: V) returns (v: Option<V>) reads {}
}

class FibonacciMemoizer {
  const cache: ExternalMutableMap<nat, nat>
  constructor() reads {} {
    cache := new ExternalMutableMap();
  }
  method Get(n: nat) returns (r: nat)
    reads {}
  {
    if n <= 2 {
      return 1;
    }
    var cached := cache.Get(n);
    if cached.Some? {
      r := cached.value;
    } else {
      var oneBefore := Get(n - 1);
      var twoBefore := Get(n - 2);
      r := oneBefore + twoBefore;
      cache.Put(n, r);
    }
  }
}

method {:extern} Fibonacci(n: nat, memoizer: FibonacciMemoizer) returns (r: nat)
  reads {}
{
  r := memoizer.Get(n);  // This version verifies
}
```

# Reference-level explanation
[reference-level-explanation]: #reference-level-explanation

Implementing the translation of `reads` clauses on methods to Boogie should be relatively straightforward, and reuse most of the translation of `reads` on functions and `modifies` on methods. The main change will be to split the `$_Frame` Boogie variable used by the `ExpressionTranslator` into two different variables named `$_ReadsFrame` and `$_ModifiesFrame`, so that they can both be defined and referenced for a single method body at the same time. This will have the side-effect of slightly increasing the readability of the translation of frame verification.

We also need to ensure that each Dafny compiler produces "thread-safe" code when given code that is verified to not depend on shared mutable state, whenever that is a meaningful requirement for the target language. This is technically independent from the feature proposed here, but is necessary for users to infer that it can be used into order to produce thread-safe code, and is not an explicitly documented property of the compilers and runtimes nor are there any mechanisms in the regression test suite to ensure it. The main likely source of race conditions is in optimizations of data types in the runtimes that are semantically immutable but contain mutable internal state, such as the lazy concatenated sequence resolution in the [C#](https://github.com/dafny-lang/dafny/blob/90eb1084d9862384accd03fb5a1c8af500212a05/Source/DafnyRuntime/DafnyRuntime.cs#L1111-L1120) and [Java](https://github.com/dafny-lang/dafny/blob/90eb1084d9862384accd03fb5a1c8af500212a05/Source/DafnyRuntime/DafnyRuntimeJava/src/main/java/dafny/DafnySequence.java#L756-L761) runtimes. Avoiding such bugs will involve applying industry-standard tooling for analyzing and testing for race conditions, such as [Coyote](https://microsoft.github.io/coyote/) for C# code.

# Drawbacks
[drawbacks]: #drawbacks

The biggest potential drawback is that inexperienced Dafny programmers might have the incorrect impression that defining a tight `reads` clause for methods is necessary, and hence expend unnecessary effort for no benefit. The verifier would never prompt users to add `reads` clauses unless they already appear elsewhere in a codebase, so the issue is more that they could see them used in documentation or examples and not realize they are largely optional.

Reusable Dafny code such as the modules in https://github.com/dafny-lang/libraries will need to specify `reads` clauses in order to support consumers that need to specify them. This does not appear to be a significant burden: at the time of writing this the `libraries` repo only contained one `method`. All other uses of the `method` keyword were in defining `function method`s instead, which already default to `reads {}` and hence can be used as is in the control flow of methods with `reads` clauses. Also note that adding a `reads` clause to a method that does not already have one will never break existing callers of that method. Again, the issue is more that users could imitate standard library `method` definitions and include superfluous `reads` clauses. The answer is likely to document explicitly why the standard library uses this feature and to emphasize that it should not be copied blindly. There is already a similar issue with the standard library's use of `{:trigger}` attributes, which are not encouraged in most Dafny codebases.

There is a chance that if and when explicit concurrency support is added to Dafny, the much more limited solution of verifying a method body `reads` and `modifies` nothing may become unused. This would make supporting `reads` clauses on methods harmless but also a maintenance burden. On the other hand, the feature is a generic and independent concept with relatively low implementation complexity, and the extra information provided by `reads` clauses is potentially useful for verifier and compiler optimizations in the future. There is a reasonable chance that `reads` clauses will be part of the future solution for concurrency anyway.

# Rationale and alternatives
[rationale-and-alternatives]: #rationale-and-alternatives

This proposal is intended to be a low-cost solution to thread-safety for Dafny. The main alternatives are as follows.

## Accept and document that compiled Dafny is not thread-safe

We could make the intentional decision that Dafny currently does not support this use case. This would mean users that wish to use Dafny in possibly-concurrent environments have three options:

1. Document that their own cross-compiled Dafny code is not thread-safe, and rely on downstream clients to avoid sharing objects.
2. Wrap all invocations of compiled Dafny code with a common lock, in the style of a Global Interpreter Lock. This would be safer, but would also penalize single-threaded use cases with an unnecessary synchronization overhead.
3. Ensure their compiled code is thread-safe by manual review and testing. This would be error-prone and especially unsatisfying given the static guarantees Dafny otherwise provides. It would also force end users to validate that the Dafny runtime implementations are thread-safe, which is not currently guaranteed, and even if currently true could regress in future versions of Dafny.

## Add direct support for concurrency to Dafny

If there is intentional use of shared mutable state in Dafny code that needs to be externally thread-safe, currently the only solution is to move this logic into external code and make use of synchronization features in the target language(s). This is unfortunate when a single `synchronized` block would hypothetically address a tiny race condition.

Besides the fact that adding full concurrent support to Dafny will be a large and expensive undertaking, we need to be very careful about what paradigm we choose. Implementing `synchronized` blocks would imply that Dafny uses a shared memory model, but it's very possible something like message passing would make specifications easier to write and less costly to verify. Selecting or designing a paradigm for Dafny is particularly challenging given it has to be compilable to multiple target languages: a shared memory model compiles naturally to C# or Java, but much less so to Go. 

# Prior art
[prior-art]: #prior-art

The most obvious prior art for this is the existing support in Dafny itself for `reads` on function definitions and `modifies` on methods.

# Unresolved questions
[unresolved-questions]: #unresolved-questions

- Parsing is simplest if `reads` clauses are allowed on all `method`-like definitions, including the various flavours of lemmas. Allowing `reads` clauses on lemmas seems harmless, but are there downsides?
- Are there other potential use cases for this feature worth mentioning, aside from external thread-safety?
- Is there a good term for a `method` that does not read or modify any shared state? "Pure" is not a good choice in this context, since it usually implies a procedure that always produces the same value when run on the same input (i.e. a `function` in Dafny) and that has no side effects (which a `method` could still have through calls to external code).

# Future possibilities
[future-possibilities]: #future-possibilities

It could be useful to have a utility to infer and add `reads` clauses to all the methods declared in a Dafny codebase, to reduce the burden of ensuring existing code is externally thread-safe.

Ideas for how Dafny should tackle asynchronous or concurrent execution in general are out of scope for this particular RFC, but still worth discussing in case they influence any immediate decisions in the name of forwards-compatibility.
