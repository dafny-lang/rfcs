# Exceptions

## Preliminaries

The examples in this document depend on the following small "library":

```
function method Unreachable<R>(): R
    requires false 
{
    var o: Option<R> := None;
    assert o.Some?;
    o.get
}

datatype Option<T> = None | Some(get: T)
```

By `Result<T>`, we mean the following datatype:

```
datatype Result<T> =
| Success(value: T)
| Failure(error: string)
{
    predicate method IsFailure() { 
        this.Failure?
    }
	function method PropagateFailure<U>(): Result<U> requires IsFailure() {
        Failure<U>(this.error)
    }
	function method Extract(): T requires !IsFailure() { 
        this.value
    }
}
```

Note that this is a datatype with instance methods, a feature which is not yet in Dafny at the moment, but will soon be added.

Moreover, we will also use a type `NatOutcome`, which is a bit like `Result`, but uses traits and classes instead of a dataype, and hardcodes the type `T` to be `nat`:

```
trait NatOutcome {
    predicate method IsFailure()
	function method PropagateFailure(): NatOutcome requires IsFailure()
	function method Extract(): nat requires !IsFailure()
}

class NatSuccess extends NatOutcome {
    const value: nat
    constructor(value: nat) {
        this.value := value;
    }
    predicate method IsFailure() { 
        false 
    }
	function method PropagateFailure(): NatOutcome requires IsFailure() {
        Unreachable<NatOutcome>() 
    }
	function method Extract(): nat requires !IsFailure() { 
        value
    }
}

class NatFailure extends NatOutcome {
    predicate method IsFailure() { 
        true
    }
	function method PropagateFailure(): NatOutcome requires IsFailure() {
        this
    }
	function method Extract(): nat requires !IsFailure() { 
        Unreachable<nat>()
    }
}
```

And finally, the example will also use a generic `Outcome<T>` type, which is not supported by Dafny at the moment, because traits can't have type parameters, but we want to keep this example in mind in the design because type parameters might be added to traits at some point.

```
trait Outcome<T> {
    predicate method IsFailure()
	function method PropagateFailure<U>(): Outcome<U> requires IsFailure()
	function method Extract(): T requires !IsFailure()
}

class Success<T> extends Outcome<T> {
    const value: T
    constructor(value: T) {
        this.value := value;
    }
    predicate method IsFailure() { 
        false 
    }
	method PropagateFailure<U>() returns (o: Outcome<U>) requires IsFailure() {
        o := Unreachable<Outcome<U>>();
    }
	method Extract() returns (t: T) requires !IsFailure() { 
        t := value;
    }
}

class Failure<T> extends Outcome<T> {
    const error: string
    predicate method IsFailure() { 
        true
    }
	method PropagateFailure<U>() returns (o: Outcome<U>) requires IsFailure() {
        o := Failure<U>(this.error);
    }
	method Extract() returns (t: T) requires !IsFailure() { 
        t := Unreachable<T>();
    }
}
```

For simplicity, we use "C#" to refer to any target language into which Dafny compiles.


## Motivations

### More readable Dafny code

At the moment, we're writing a lot of code of the following form:

```
var res1: Result<T1> := operation1(args1);
if res1.Failure? {
    return Failure(res1.error);
}
var value1: T1 := res1.value;

var res2: Result<T2> := operation2(args2);
if res2.Failure? {
    return Failure(res2.error);
}
var value2: T2 := res2.value;

...
```

It would be nicer to have more concise code, which could look like this:
```
var value1: T1 :- operation1(args1);
var value2: T2 :- operation2(args2);
...
```

### Less glue code to interoperate with other languages

Many Dafny libraries will live in a "sandwich" between two layers of C# code (or any other language Dafny compiles to):
* Code written in C# by clients who find it cool to use verified software, but don't want to write Dafny themselves
* Code written in Dafny, compiled to C#
* Primitives written in C# which cannot be written in Dafny (eg networking, file system access, etc)

Both the layer above and the layer below the Dafny layer use exceptions, and at the moment, we have to wrap the primitives to turn exceptions into something Dafny understands, and then wrap the Dafny-generated C# code into exception-producing code, because clients don't want to deal with types such as `Result` or `Option`, they want exceptions.
It would be good to get rid of these two extra layers of wrappers.

### Don't swallow exceptions if you can't handle them

If an exception is thrown in the primitives layer, it should be possible to let it bubble up through the layers all the way up to the client code, because in many situations, only the client code knows how to deal with the exception appropriately.
For instance, if the exception is a network failure, and we're in an application which has an offline mode, we don't want the lower layers to swallow the exception and return some dummy value, or terminate the program, but the exception should be passed on to the client app, which could just say, "ok so let's switch to offline mode".

### Printing stack traces

While a client is debugging their app, it would be useful for them to get a stack trace in case of unhandled exceptions which goes all the way through the stack, and is not interrupted by the Dafny layer.


## Language-level changes

The grammar of expressions is augmented with the following two forms:

```
var x :- E; F
:- E; F
```

where `E` and `F` are expressions, and `x` is a variable name or a pattern.

The grammar of statements is augmented with the following six forms:

```
var x :- M(...);
y :- M(...);
:- M(...);
var x :- E;
y :- E;
:- E;
```

where `M` is a method name, `E` is an expression, `x` is a variable name or a pattern, and `y` is a (previously declared) variable.

We say that a type `A` `SupportsNonVoidErrorHandling` if all of these are true:
* it has a member called `IsFailure`
* it has a member called `PropagateFailure`
* it has a member called `Extract`

We say that a type `A` `SupportsVoidErrorHandling` if it has the following members:
* it has a member called `IsFailure`
* it has a member called `PropagateFailure`
* it has no member called `Extract`

Note that we do not make any requirements on how many arguments and how many type parameters the above members have, nor on their return types, nor on whether they are functions, function methods, methods, or ghost methdos; as long as the code produced (as described below) makes type parameter inference and typechecking work, it's fine.

In the following, we will define how each of the above new grammar forms is desugared.
Let `EorM` be an expression or method call, let `TM` be its type, let `E` be an expression, let `TE` be the type of `E` and let `temp` denote a fresh variable name.

* Expression `var x :- E; F`: If `TE` `SupportsNonVoidErrorHandling` then desugar into `var temp := E; if temp.IsFailure() then temp.PropagateFailure() else var x := temp.Extract(); F` else emit error "`TE` does not support non-void error handling"
* Expression `:- E; F`: If `TE` `SupportsVoidErrorHandling` then desugar into `var temp := E; if temp.IsFailure() then temp.PropagateFailure() else F` else emit error "`TE` does not support void error handling"
* Statement `var x :- EorM;`: If `TM` `SupportsNonVoidErrorHandling` then desugar into `var temp := EorM; if temp.IsFailure() { return temp.PropagateFailure(); } var x := temp.Extract();` else emit error "`TM` does not support non-void error handling"
* Statement `y :- EorM;`: If `TM` `SupportsNonVoidErrorHandling` then desugar into `var temp := EorM; if temp.IsFailure() { return temp.PropagateFailure(); } y := temp.Extract();` else emit error "`TM` does not support non-void error handling"
* Statement `:- EorM;`: If `TM` `SupportsVoidErrorHandling` then desugar into `var temp := EorM; if temp.IsFailure() { return temp.PropagateFailure(); }` else emit error "`TM` does not support void error handling"

Note that there are cases where the desugaring succeeds, yet the typechecker will fail on the produced desugared expression, and this is intended.


## Dafny-to-C# compiler changes

The compiler will compile all methods which return a type which `SupportsErrorHandling` into C# methods with signatures of the form

```
public T MethodCall(A1 a1, A2 a2, ...) throws Exception
```

(Note that C# method signatures do not have `throws` clauses, but we just add them here for clarity, even though that's not valid C# code).

In particular, the same signature translation also applies for methods annotated with `{:extern}`, so for instance, given the C# method `System.IO.Stream.Read` with signature 

```
public int Read (byte[] buffer, int offset, int count)
```

one could write a Dafny stub for it as

```
method {:extern} Read(buffer: array<byte>, offset: int32, count: int32) returns (nRead: Result<int32>)
```

which would enable us to call exception-throwing C# methods from Dafny without an extra unverified layer turning exceptions into `Result<int32>`.

In the same way, methods implemented in Dafny which return `Result<T>` would be compiled to exception-throwing methods and thus be directly usable by C# client programs.

Moreover,

```
return Failure(someErrorMsg);
```

is compiled into a `throw` statement:

```
throw new Exception(dafnyStringToNativeString(someErrorMsg));
```

Compilation of

```
return Success(someValue);
```

simply drops the wrapping:

```
return someValue;
```

And the new Dafny construct

```
var value1: T1 :- operation1(args1);
```

is simply compiled into

```
var value1 = operation1(args1);
```

and the handling of the failure case is done by C#'s exception mechanism.


## FAQ

**Q:** What about target languages which do not have exceptions, such as Go?

**A:** Go uses a pattern of returning an additional return value to report success/failure, and the Dafny-to-Go compiler would use this pattern too. In general, the idea is to compile `Result<T>` to the idiomatic way of dealing with failure in the target language, be it exceptions, extra return values, `Option`, `Maybe`, ...

**Q:** Can this work for methods which have multiple return values?

**A:** Not really, but one can always just return a tuple.

**Q:** Should `IsFailure`, `PropagateFailure`, `Extract` be functions or methods?

**A:** `IsFailure` has to be a function, because it appears in the preconditions of the other two. We allow the user to choose whether `PropagateFailure` and `Extract` are functions, function methods, methods or ghost methods, but depending on what the user chooses, this exception handling feature might not be available in expressions or in statements. Note that requiring them to be function methods would prevent `PropagateFailure` from allocating a new object.


## Discussion points, open questions

### Should  `Result<T>` be first-class?

Should it be possible to pass around values of type `Result<T>`? That is, should it be allowed to assign a `Result<T>` to a variable, or to pass a `Result<T>` to a method? Say the user writes
```
var res1: Result<T1> := operation1(args1);
anotherMethodCall(res1);
```
If this happens, and the compiler compiled `operation1` into a `public T1 operation1(args) throws Exception`, then the code generated for the above snippet would have to catch the exception and materialize it into a `Result<T1>`.
In most cases, this is probably not the code which the user meant to write, so the questions are: Should this still be supported? Should it emit a warning? Should it emit an error?


### How to support returning through assignement instead of `return`?

Should the following be supported?

```
method Test() returns (res: Result<int32>) {
    res := someMethodCall();
    if changedMyMind() {
        res := someOtherMethodCall();
    }
}
```

The most straightforward way of supporting this would be to surround `someMethodCall` and `someOtherMethodCall` with a `try/catch` block, materialize their result into a `Result<int32>`, and at the end of the method body, to return `res.value` or throw `res.error`.
This seems inefficient, can we do better?
Should it be supported at all, or would we only allow `return` in methods returning `Result`, but no assignment to the result variable?


### What's the name for this?

Googling `:-` will be very hard, so to make this new syntax less confusing, it would be good to agree on one canonical name for this feature, and use that same name everywhere (Dafny source code, documentation, blog posts, etc).


## Status

This has not been implemented yet, and not been fully thought trough yet, so it could be that we oversaw problems which would make this impossible.

