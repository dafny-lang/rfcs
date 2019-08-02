# Exceptions

## Preliminaries

By `Result<T>`, we mean the following datatype:

```
datatype Result<T> =
| Success(value: T)
| Failure(error: string)
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
var value1: T1 := res1.get;

var res2: Result<T2> := operation2(args2);
if res2.Failure? {
    return Failure(res2.error);
}
var value2: T2 := res2.get;

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


## Implementation

The type `Result<T>` is hardcoded into Dafny, the same way as `seq`, `map`, `int`, etc.

Given a `MethodCall(args)` which returns `Result<T>`, let's define

```
var v :- MethodCall(args);
... rest of the code using v as if it had type T ...
```

to be syntactic sugar for

```
var res_v: Result<T> := MethodCall(args);
if res_v.Failure? {
    return Failure(res_v.error);
}
var v := res_v.value;
... rest of the code using v as if it had type T ...
```

as far as verification and Boogie are concerned.

We will not really implement it as syntactic sugar, though, because we want a separate AST node for this so that the compiler can recognize it easily.

The compiler will then compile all methods which return `Result<T>` into C# methods with signatures of the form

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

**Q:** Are we also adding special syntax/support for this inside expressions?

**A:** Not at the moment

**Q:** What about target languages which do not have exceptions, such as Go?

**A:** Go uses a pattern of returning an additional return value to report success/failure, and the Dafny-to-Go compiler would use this pattern too. In general, the idea is to compile `Result<T>` to the idiomatic way of dealing with failure in the target language, be it exceptions, extra return values, `Option`, `Maybe`, ...

**Q:** Can this work for methods which have multiple return values?

**A:** It seems so.


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

The most straightforward way of supporting this would be to surround `someMethodCall` and `someOtherMethodCall` with a `try/catch` block, materialize their result into a `Result<int32>`, and at the end of the method body, to return `res.get` or throw `res.error`.
This seems inefficient, can we do better?
Should it be supported at all, or would we only allow `return` in methods returning `Result`, but no assignment to the result variable?


### What's the name for this?

Googling `:-` will be very hard, so to make this new syntax less confusing, it would be good to agree on one canonical name for this feature, and use that same name everywhere (Dafny source code, documentation, blog posts, etc).


## Status

This has not been implemented yet, and not been fully thought trough yet, so it could be that we oversaw problems which would make this impossible.

