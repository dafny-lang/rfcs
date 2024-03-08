- Feature Name: Abstract reference type by class
- Start Date: 2024-08-03
- RFC PR: [dafny-lang/rfcs#14](https://github.com/dafny-lang/rfcs/pull/14)
- Dafny Issue: [dafny-lang/dafny#5169](https://github.com/dafny-lang/dafny/issues/5169)

# Summary
[summary]: #summary

This RFC makes it possible to declare reference types with a different implementation than their interface. It makes it possible to have an “internal” heap region consisting of all mutable fields not declared in a public interface. It makes it possible to generalize function by methods with persistent caches from one function call to the next, and to define `AtomicBox` in the language itself.
Language feature summary and requirements:

* We define `type X { public body } by class { private body }` which defines X as a reference type and Dafny performs all necessary checks so that X really behaves as if it was a stand-alone declaration.

# Motivation
[motivation]: #motivation


Functions by methods is one of the great features of Dafny because they allow
to create efficient implementations of functionswhile being able to reason about their functionality.
The by-method part can allocate state like arrays, which makes it possible to perform computations
more efficiently. Besides print effects, this allocation is the only side effect functions can have,
and none of both are observable at the call site.
However, by-method parts cannot write to a private cache, which many times would be useful.

The notion of private memory does not exist yet in Dafny. Several attempts have been made,
but there were always apparently soundness issues with them. They always involved the following example:
If we could hide that we modified some memory locations, then from within the place where private memory is accessible
we could call external functions or methods that would call back into the original one and modify private memory locations unknowingly.
Or, if an object was supposedly private to an instance, and this object was an ordinary object,
it would almost always be possible to leak this object and that would cause tons of problems.
I even investigated reachability as a generalization of the `allocated()` axiom, but it looks like nothing like that would be backward compatible.

Having private memory would make reasoning even more modular.
For example, we could omit modifies clauses that are not relevant for the caller, such as `modifies this.Repr`.
It would make it one step closer to proper abstraction, where we can manipulate objects without having direct access to their inner objects.
It would make it possible to have private caches for implementations and even for functions themselves.

For now, private memory is often achieved through the use of `{:extern}` so that it’s possible to hide fields,
and implementing functions via methods that modify existing state.
That’s the only way to do caching for functions, even if the extern code was in Dafny itself.
But this way is never proved and obviously prone to making mistakes.
It would be so much better if we could avoid this altogether and define everything in Dafny.

In this RFC, I will not discuss heap-reading invariants although they can definitely be useful for more advanced versions of private memory.
I’ll only focus on the idea of having private memory.

To see how private memory could be useful, let’s investigate a toy motivational example:
A function computing Fibonacci with a cache.

### 2.1. Motivation: Fibonacci cache

Let’s say we want to implement a Fibonacci *function* whose results are *cached* in memory.
But at the same time, we don’t want users to know about the cache, which could be a map from
integers to integers. Not having to deal with the cache is the desire we identified earlier:
To hide the set of modified objects..

Ideally, we would love to declare this type as an abstract type with the following signature
that does not expose any modifies clause, so that another object accessible in the same method
is untouched.

```
type FibCache {
  function getCached(n: nat): nat {
    if n <= 1 then n else get(n-1) + get(n-2)
  }
  
  method numOfCachedEntries() returns (n: nat)
}

method {:test} TestFibCache() {
{  
  var fib := new FibCache();
  // Proved as usual
  assert fib.get(50) + fib.get(51) == fib.get(52);

  // None of these statements have side effects!
  var fib50 := fib.getCached(50);
  var fib51 := fib.getCached(51);// But this one computes extremely fast
  var fib52 := fib.getCached(52);// And this one too
  
  // Proved and true as usual
  assert fib50 + fib51 == fib52;
  
  // We can access meta information about the cache
  // N reads clause!
  var entries = fib.numOfCachedEntries();
  expect entries == 50;
}
```

The only way to implement such a cache is to declare the class `{:extern} {:compile false}`
nd implement it with external code, but as you can guess, no verification will be made.

```
class {:compile false} {:extern} FibCache { ... }

// Hack more than anything.
class {:extern "FibCache"} FibCacheImplementation {
  var cache: map<nat, nat>
  method getCached(n: nat) returns (r: nat) modifies this`cache { ... }
}
```

### 2.2. Background summary

Our users prefer the sound approach but have the wish for getting rid of modifies clauses,
one for concurrency reasons, and the other for simplicity.
The Dafny project is using the unsound approach (carefully reviewed!) in our DafnyRuntime
(implementation of seq and AtomicBox).

Overall, we want to have both:

* We want any new approach to be sound.
* We want to be able to handle references with methods and functions while
  *omitting modifies clauses* that are not relevant

Optionally, I think we want also to be able to have an equivalent of private state
(I implement it in this proposal)

# Guide-level explanation
[guide-level-explanation]: #guide-level-explanation

With the new feature of abstract references by class, Dafny makes it possible to define a
new abstract reference type, like `FibCache` above, implemented using a private class implementation.
It’s like a trait, except that it can declare a constructor, and its functions and methods 
can be defined in a unique class adjacent to it. The “type” part is named **the interface**
and is public, whereas the “by class” part is called **the implementation** and is private.

Notably:

* The implementation can access all that the interface declares, plus its own functions, methods and fields.
* Functions can be implemented by methods

Let’s revisit our Fibonacci example with this new feature.

### Implement a `modifies`-free `FibCache`

To implement `FibCache`, one would write the following.
I’ll detail after this example everything that you ought to realize, meanwhile, I mark the points of interest with `// !`.

```
// The function we want to have a cache for
ghost function FibGet(n: nat): nat {
  if n <= 1 then n else FibGet(n-1) + FibGet(n-2)
}

type FibMap = m: map<nat, nat> |
  0 in m && 1 in m &&
  forall k <- m :: m[k] == FibGet(m) witness map[]

type FibCache {
  function get(n: nat): nat { // ! Not a ghost function!
    FibGet(n)                 // ! Ghost but that's just the spec of get
  }
  
  constructor()               // ! Declared
  
  method cachedEntries() returns (n: nat)

} by class {                  // ! New syntax
  
  var cache: FibMap           // ! "Private" heap region

  constructor() {             // !
    cache := map[0 := 0, 1 := 1];
  }
  
  // Let's implement our get function!
  method get(n: nat) returns (r: nat)
    modifies this`cache       // ! this`cache is not in interface so it is ok
    ensures r == FibGet(n)    // ! Would have been added by Dafny anyway
    ensures n in cache        // ! Not visible from the outside
  {
    if n in cache {
      return cache[n];
    }
    assert n > 2; // true because 0 and 1 are in cache.
    // We could do a while loop if we did not want to consume O(n) stack
    var f1 := get(n-1);
    var f2 := get(n-2);
    // The last two are method calls so they have to be in separate lines
    // Private methods cannot call functions that are not private
    r := f1 + f2;
    cache := cache[n := r];
  }
  method cachedEntries() returns (n: nat) reads this {
    n := |cache|;
  }
}

method {:test} TestFibCache() {
{  
  var fib := new FibCache(); // As before
  // ...
}
```

The important points about the example above are that:

* The **interface** part (inside `type {...}`) declares functions and methods that are consistent, similarly to an export set.
    * It has a non-ghost `function get()` whose body is ghost, but that’s fine because it’s going to have an implementation.
    * It declares a constructor, so it can be built like a class. The constructor has to be defined in the implementation.
    * It declares a method that does not say anything about how it’s going to return the cache size.
* The **implementation** part (inside `by class {....}`) declares a kind of private field `cache`, that is assigned
  in the `constructor` and read in the method `cachedEntries` implementation.
  But more interestingly, it is read and modified in the `get` method that is implementing the function.

This approach fulfills our wishes:

* This approach is sound because checks are comprehensive (proved in appendix)
* We can omit elements from the modifies clauses in the public interface

Let’s visit the new proposed syntax in more details.

# Reference-level explanation
[reference-level-explanation]: #reference-level-explanation

An abstract reference type by class consists of a reference type declaration followed by a nameless class declaration.
An abstract reference type by class can declare everything that a class would declare. Its syntax is:

```
type MyClass<TypeParameters...> {
  const Field1: Type // Can be ghost
  
  var field2: Type // Can be ghost
  
  function GetThat(arguments...): Type // Can be ghost
    requires R
    reads    A
  { ... } // Interface functions need to be defined
  
  method PutThat(arguments...) returns (r: Type) // Can be ghost
    requires R
    reads    A
    modifies M
    ensures  E
  // Methods can be defined here or in the implementation
  
 // constructors are like methods
} by class {
  var hiddenConstant: Type

  var hiddenField: Type // Can only be read by methods or functions in implementation
  
  function PrivateFunction(arg: Type): Type
    reads this
  { ... } // This function is private and can read private fields
  
  method GetThat(arguments...) returns (r: Type) // Same signature, can be a method
    requires R
    modifies this`hiddenField //`
  { ... }
  
  method PutThat(arguments...) returns (returnValue: Type)
    modifies M, modifies this`hiddenField //`
    ensures  E
    ensures E' // Anything that depends on private fields can be ensured
  { ... }
}
```

### How are type by class sound?

To make this approach sound, the following conditions are sufficient:


* Private fields (fields only in the implementation) should not be readable or modifiable except in the implementation part.
* Inside the interface
    * Functions must have a body. Otherwise, their implementation’s value might depend on something not in their reads clause like private mutable fields, and that would be unsound. This is not like a function declaration in a trait. *There might be a way to declare functions without body, implemented by functions that read the private state, and prove that every method does not change their value, but I haven’t found a sound way to do so and haven’t found examples where it would be useful.*
    * Methods may or may not have a body.
* Inside the implementation
    * Function or methods should have a requires clause that is weaker than the precondition in the respective declaration in the interface
    * Functions or methods should have an ensures clause that is stronger than the postcondition in the respective declaration in the interface
    * Functions can also declare that they read private fields not present in the interface
    * Methods can also declare that they modify private fields not present in the interface
    * Having access to private fields, functions should not be able to call into functions that might modify the private state indirectly. Otherwise, the value of private fields could change from one read to the other.
    * In practice, as a first approximation, **functions or methods in the implementation cannot call functions that are not part of the implementation**, period. For me this is a reasonable restriction, as I expect anyway implementations to be quite low-level anyway, and we can always use library methods for specifications without restriction.
        * Later, if the need arise, we could still detect if the function being called could possibly call into functions that modify the instance’s private state, and if that is not possible, then it’s fine. But that seems like a heuristic that might not be worth it.
    * Calls to methods outside of the implementation are possible but always assume that all the private fields are part of the external modifies clause. This also apply to calls to methods that are *declared and implemented in the interface.* I don’t expect that it will be very common to call methods outside of the implementation, so we might as well decide that calls to methods outside of the implementation are forbidden altogether.
        This means that, to any method call
        `O.methodCall(arguments)`
        we add the following modifies clause, for every private field:
        `(if O == this then {} else {this})`privateField`
    * It is possible to define regular function by methods, but both the function and the by-method are not visible from the interface.

These rules are backward-compatible, meaning any method outside of the implementation would not need to care about these observations.

# Drawbacks
[drawbacks]: #drawbacks


* There is no backtracking after introducing such a feature, it has to be maintained.

# Rationale and alternatives
[rationale-and-alternatives]: #rationale-and-alternatives

So far so good. But is it the only possible approach to hide memory and modifies clauses? And even using a similar approach, is it the best design we want for our users?

Let’s think about one of the restrictions of this proposal: In the implementation, we can’t call external functions.
If we want to be able to always reason sequentially, the only way to accept that private state might change when in the implementation is via method calls. In the implementation, function calls should not be able to modify private state. But we have absolutely no control over what external function calls might do if we call them. Dynamic dispatch would prevent us in general from inspecting functions. Therefore, if we accept the idea that functions might be implemented by methods that modify the private state, it would be unsound in general if any implementation function could call another external function.

The notion of private state requires that we accept that by-method can modify the internal state. If you are not convinced, we could perform this modification anyway indirectly, by placing a call to an external method that is unaware of private state, and that external method call could circle back to a method that modifies the private state.

For external *method* calls in the implementation, we have a bit more control, since such calls can have a modifies clause. Therefore, we could simply assume that these calls could circle back to another implementation method and modify the private state, so that we can take into account how private state could be modified.

With these remarks it seems that, with the given assumptions that we don’t have invariants or any kind of other memory, the only way to have private fields is by respecting the rules set up by this proposal. And these rules are sound.

# Prior art
[prior-art]: #prior-art

- `Private[this]` in Scala allows to modify only the fields of "this".
- Splitting the interface from the implementation is a common practice in OOO. Interface, trait, mixins...
- functions by methods in Dafny itself.

Other comparison points are welcome!

# Unresolved questions
[unresolved-questions]: #unresolved-questions

Here are few design considerations to discuss

#### Type by class vs. “private” keyword.

We could have just one class, and mark fields, methods, functions, ensures clauses and modifies clauses as public/private.
See how it would compare

Current proposal:

```
type A {
  const a: int
  var b: int
  function f(): ... reads R { ... } // Implemented publicly
  function g(): ... reads P {...}   // Implemented privately using a method
  method m(args) modifies X { ... } // Implemented publicly
  method n(args) modifies Y         // Implemented privately
  constructor()                     // Always implemented privately
} by class {
  const c: int
  var d: int
  method g(): ... modifies`d { ... } //`
  function h(): ... // Private function
  method n(args) modifies Y modifies this`d { ... } //`
  method nn(args) // private method
  constructor() ensures d == Z
}
```

Private keyword proposal


```
class A {
  const a: int
  var b: int
  private const c: int
  private var d: int
  function f(): ... reads R { ... }
  function g(): ... reads P {...} by method
    private modifies`d //`
  {
    ...
  }
  private function h(): ... { ... }
  method m(args) modifies X { ... }
  method n(args) modifies Y private modifies this`d { ... } //`
  private method nn(args) ... 
  constructor()
    private ensures d == Z
  { ... }
}
```

Here is a rough comparison between the two, and why I prefer the first syntax over the second one:

|Comparison point	|`type ... by class ...`	|`private `keyword	|
|---	|---	|---	|
|In harmony with function by method	|Yes	|No	|
|In harmony with assert ... by	|Yes	|No	|
|Similar to trait implementation	|Yes	|No	|
|The public API is viewable by itself	|Yes	|No	|
|Can be transposed to abstract module refinement of reference type	|Yes	|No	|
|Only one declaration	|Yes (even if separated by a keyword)	|Yes	|
|Similar to existing object-oriented features	|No	|yes, `private[this]` in Scala	|
|No need to prove the override of ensures clauses, requires clauses and modifies clauses	|No	|Yes	|
|In harmony with export sets	|No	|No	|

Which one is your favorite and why? Mine is type by class, because it resembles more the philosophy of Dafny, which did not have the private keyword until now: the private modifier in usual OOO sense can leak information. Moreover mixing the interface from the implementation is not a good design practice, although we could think of having to repeat public fields

#### Keyword choice for the first declaration.

1. `type` (already exist and would be an extension of the existing syntax)
2. `newtype` (we are hiding the implementation and could let the compiler choose what implementation to take)
3. `abstract type`
4. `abstract class` (might conflict with existing class)

Which one is your favorite and why? Mine is #1 but I like #2 as well.

#### Keyword choice for the second declaration

1. `by class`
2. `by` (like `assert ... by`)
3. `by implementation`
4. `by object`
5. `implemented by`
6. `with`
7. `with implementation`

Which one is your favorite and why? Mine is #1 because we still use the “class”. however, since this is not a regular class, I’d also like just #2

#### Implementation choice

We could also declare the type in an abstract module and implement it as a class in a refined module, or in a replaceable/replaces pair

```
abstract module X {
  type Y {
    ... interface
  }
}
module XP refines X {
  type Y = class {
    ... implementation
  }
}

replaceable module R {
  type Y {
    ... interface
  }
}
module RP replaces R {
  type Y = class {
    ... implementation
  }
}
```

We could actually do both. The stand-alone syntax without module refinement would mean less intrication with modules, so I think we should implement it first
What do you think? Please choose

1. We should only implement the standalone type by class
2. We should only implement the type by class by module refinement
3. We should implement the standalone type by class, and then later we could implement it for module refinement if needed
4. We should implement the type by class module refinement and then later we could implement the standalone version if needed
5. We should implement and ship both at the same time

Which one do you prefer and why? I prefer 3, standalone type by class for now, and later implement it for module refinement / replacement

# Future possibilities
[future-possibilities]: #future-possibilities

- Private objects?
  - Linear types to have more objects as part of the private memory area?
  - Reachability analysis to have more objects as part of the private memory area?
  - Import modules inside the by class so that all their allocated types become private and can't escape?
- datatypes by class? Need to implement equality and hash, and also custom resource clearing code if applicable.
- Custom big integer representation by class?
- Custom theories by class?

## Appendix A

### A.1. Atomic box with invariant

This is the same atomic box described in the DafnyRuntimeDafny, only this time it can be implemented in Dafny itself.

```
abstract module AtomicBox {
  type T // Can be a subset type
  
  type AtomicBox<T> {
    constructor(init: T)

    // A non-deterministic method to obtain the current value
    method Get() returns (t: T)

    // A method to store a new value
    // We cannot ensure that Get() will return it though
    method Put(t: T)
  } by class {
  
    // The field that stores the value. Not visible externally
    var value: T
  
  
    // The constructor
    constructor(value: T)
      ensures this.value == value
    {
      this.value := value;
    }
  
    // Get cannot be implemented as a function
    // as one cannot not prove its value did not change
    // before/after the method Put(). This is sound.
    method Get() returns (t: T)
    {
      t := value;
    }

    // Put stores t in the value but since it's an immutable type,  
    // it's not possible from the outside to know that value
    method Put(t: T)
      modifies this`value //`
      ensures this.value == t
    {
      value := t
    }
  }
}

module Even refines AtomicBox {
  type T = x: int | x % 2 == 0
}
method Test() {
  var x := new Even.AtomicBox(0);
  //x.Put(3); // Would statically fails
  x.Put(2);
  var j := x.Get();
  // assert j == 2; // Fails as we don't have information
  assert j % 2 == 0; // OK
  expect 2 ==j;      // No run-time exception
}
```

