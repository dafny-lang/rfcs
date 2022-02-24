- Feature Name: predicate_types
- Start Date: 2022-02-24
- RFC PR: [dafny-lang/rfcs#0008](https://github.com/dafny-lang/rfcs/pull/0008)
- Dafny Issue: [dafny-lang/dafny#1680](https://github.com/dafny-lang/dafny/issues/1680)

# Summary
[summary]: #summary

We introduce the new construct `predicate type`, which acts both like a subset type and a predicate
```dafny
predicate type Even(x: int) {
  x % 2 == 0
}
```

which would desugar into:
```dafny
predicate Even(x: int) {
  x % 2 == 0
}

type Even = x: int | Even(x)
```

# Motivation
[motivation]: #motivation

The last snippet above is very common: We define a predicate, and use that predicate to define a subset type.
However, for maintenance, nothing prevents anyone to add `&& OtherFun(x)` next to `Even(x)`, which would break the meaning associated with this subset type.

Merging the subset type and the type in one single `predicate type` would make it possible to use the name both as a type, and as a predicate, thus removing any maintenance problem.

# Guide-level explanation
[guide-level-explanation]: #guide-level-explanation

You can migrate to **predicate types** from two either *subset types*, or from *predicates*.
In the near future, you could even have an IDE wizard helping you do either migrations.

## Migrating from subset types
Let's say you have a **subset type** that you are using somewhere:
```dafny
type Odd = x: int | x % 2 == 1 witness 1

method Main() {
  var i:int := f();
  var j: Odd := if i % 2 == 1 then i else 1;
}
```
If you would like to access the subset constraint `x % 2 == 1` so that you do not repeat it in `Main()`,
instead of refactoring this constraint into a new method manually, you can rewrite your code like this:
```dafny
predicate type Odd(x: int) {
  x % 2 == 1
} witness 1

method Main() {
  var i:int := f();
  var j: Odd := if Odd(i) then i else 1;
}
```
The **witness** to the end of the predicate is like a lemma whose body is `assert MyType(1);


## Migrating from predicates
Let's say you have a **predicate** that you are using somewhere:
```dafny
predicate Odd(x: int) {
  x % 2 == 1
}

method Main() {
  var i:int := f();
  var j: int := if Odd(i) then i else 1;
  j := j + 1;
  assert Odd(j); // You'd get an error here.
  j := j + 2;
}
```
You might want to specify the *type* of `j` to ensure it always passes the `odd` predicate, so that any further assignments to `j` keep this odd-ness.
All you have to do is change `predicate` into `predicate type`, and to help Dafny figure out that the newly defined type is not empty, add `witness 1`.
Now you can get rid of the assertions, because it's going to be checked on the assignment to j:
```dafny
predicate type Odd(x: int) {
  x % 2 == 1
} witness 1

method Main() {
  var i:int := f();
  var j: Odd := if Odd(i) then i else 1;
  j := j + 1; // '+' highlighted, value does not satisfy the subset constraints of 'Odd'
  j := j + 2; // Here you get no error, assuming j is odd.
}
```

# Reference-level explanation
[reference-level-explanation]: #reference-level-explanation

Ideally, we would wait for `predicate` to be compilable by default, so that the keyword `type` is unambiguously added afterwards: `ghost predicate type` or `predicate type`
(contrary to `predicate type` and `predicate method type` that would be weird today)

We would have to change:
* **Dafny AST:** Add fields `isType` and `witness` to `Predicate`.
* **Parser:** support the new syntax with the optional fields above, namely an optional "type" after `predicate` and an optional `witness ...` like subset types after the definition of the predicate.
  We should reject `predicate type`s with more than one argument (for now), with `requires` or `reads`, but we can keep `ensures`
* **Resolver:** Add an internal rewriter before resolution that converts a `predicate type` into both a `predicate`,
  and a subset type of the same name with a call to the predicate for constraint, with the witness provided.
  We also need a predicate to be able to have the same name as a type, for example by internally prefixing types with "t_"

There is nothing more to implement for the verifier and compiler, since this is desugarding.
The last example above would be rewritten:

```dafny
predicate Odd(x: int) {
  x % 2 == 1
}
type Odd = x: int | Odd(x) witness 1

method Main() {
  var i:int := f();
  var j: Odd := if Odd(i) then i else 1;
  j := j + 1; // You'd get an error here, cannot assign something not Odd to something that is Odd
  j := j + 2; // Here you get no error, assuming j is odd.
}
```

which would automatically satisfy all 

## Further notes

* We would still be able to use `{:opaque}` and use `reveal` because that annotation can be directly added after `predicate`.
* It would be possible to define `predicate newtype` the same way, and it would have the same advantages.
* In a second milestone, we could define another kind of `predicate type` inside a class or a datatype,
  where the type is statically accessible, but predicate is not and has no argument. For example:
  ```dafny
  datatype Boxed = BoxedNumber(n: int) {
    predicate type Odd() {
      this.n % 2 == 1
    }
  }
  ... var j: Boxed.Odd = BoxedNumber(1) ...
  ```
  would become
  ```dafny
  datatype Boxed = BoxedNumber(n: int) {
    predicate Odd() {
      this.n % 2 == 1
    }
    type Odd = s: Boxed | s.Odd()
  }
  ... var j: Boxed.Odd = BoxedNumber(1) ...
  ```
  Dafny does not support nested types (which would automatically be static) so that would be a huge refactoring.

# Drawbacks
[drawbacks]: #drawbacks

* It feels odd to have restrictions on a predicate so that it becomes a type.
* It might be even more confusing for newcomers.
* It feels weird that the type is statically accessible in a class but there is no "static" keyword in front of `predicate type`.

# Rationale and alternatives
[rationale-and-alternatives]: #rationale-and-alternatives

- For every subset type `MyType`, we could also generate by default a predicate with the name `MyType?` that has the same constraint.
  That might actually be even simpler, but then there would be no control over the predicate like `{:opaque}` and `reveal`.
- `type predicate` instead of `predicate type`? What should be the focus? I think the second one is more English.
- Should the name of the predicate and the type be the same? We could also enfore the name of the predicate to end with `?`,
  so that the type doesn't have the `?`. For example, `predicate type Even?` that becomes `predicate Even?` and `type Even`.

# Prior art
[prior-art]: #prior-art

This feature to combine both the predicate and a subset type in a single construct does not exist in other programming languages, as far as I know.
However, there is at least another instance  where a type is the same as a value, so one does not need to bother:
- TypeScript's `"value"` is both a value and a string of the same type (not a subset type)

Also, it becomes common to realize that types share the same world as functions, they can have lambdas, match statements
(for example, https://dotty.epfl.ch/docs/reference/new-types/match-types.html).
Hence, similarly to Dafny enabling to define a `function method` that is both specification and implementation,
we could make it easy to define something that is both a `predicate` and a `subset type`

# Unresolved questions
[unresolved-questions]: #unresolved-questions

- What are other problems that this RFC would introduce? What is the simplest way to implement the benefit of this feature?

# Future possibilities
[future-possibilities]: #future-possibilities

A natural evolution of this proposal would be to accept multiple arguments to `predicate type`,
which would enable dependent types like in the following discussion:
https://github.com/dafny-lang/dafny/discussions/1557#discussioncomment-1926952
