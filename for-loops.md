- Feature Name: for-loops
- Start Date: 2021-01-20

# Summary
[summary]: #summary

This RFC gives a concrete proposal for adding `for` loops to Dafny.

# Motivation
[motivation]: #motivation

Dafny has only one kind of loop, `while` loops (with either one guard or with a set of guards). Some tasks
where other languages require a loop can be done in Dafny with the aggregate `forall` statement, avoiding
iteration altogether. Still, some situations call for a loop with a loop index and iteration pattern just
like what a typical `for` loop provides. This RFC
gives a concrete proposal, so that design aspects of `for` loops in the context of Dafny can be discussed.

Two central design points are:     
- the half-open interval of values for which the loop body is performed (e.g., `0 <= i < a.Length`) and
  the closed interval that appears in the loop invariant (e.g., `0 <= i <= a.Length`)
- what should be the possible increments of the loop index (e.g., `+1`, `-1`, `+2`)

Requests for `for` loops in Dafny come up from time to time. Here is a record of
[one such request](https://github.com/dafny-lang/dafny/issues/7).

# Guide-level explanation
[guide-level-explanation]: #guide-level-explanation

The `for` loop has the following syntax:

```
ForLoop ::=
  "for" Ident [":" Type] ":=" Expression ("to" | "downto") Expression
  { InvariantDecl | ModifiesDecl }
  [ Body ]
```

The scope of the loop-index variable introduced by `Ident` is the `for` loop itself. Its name must not be
the same as any local variable introduced in the same block scope as the `for` loop itself.
The loop index is immutable in the `Body`.

The type of loop index is `Type`, if present; otherwise, it is inferred from the types of the
two expressions, which must be assignable to the loop index. In either case, the type must be an
integer-based type (`int`, some subset type based on an integer-based type, or a `newtype` based
on an integer-based type; note that bitvector types, `ORDINAL`, and `real`-based types are not
allowed).

The loop index is automatically updated by the `for` loop. This guarantees that the loop will always
terminate. Therefore, the `for` loop does not allow user-specified `decreases` clauses.

The meaning of the loop is defined in terms of existing language features. Ignoring the scope of the
loop index (which was explained above), the "up" loop

```
for i: I := lo to hi
  invariant J
  modifies W
{
  Body
}
```

has the meaning

``` dafny
var _lo := lo;
var _hi := hi;
assert _lo <= _hi;  // this is Dafny-like
assert forall _i :: _lo <= _i <= _hi ==> /* _i is a value of the type of I */;
var i := _lo;
while i < _hi
  invariant _lo <= i <= _hi  // automatically generated
  invariant J
  modifies W
{
  Body
  i := i + 1;
}
```

The "down" loop

```
for i: I := hi downto lo
  invariant J
  modifies W
{
  Body
}
```

has the meaning

``` dafny
var _lo := lo;
var _hi := hi;
assert _lo <= _hi;
assert forall _i :: _lo <= _i <= _hi ==> /* _i is a value of the type of I */;
var i := _hi;  // this is different from the "up" loop
while _lo < i  // this is different from the "up" loop
  invariant _lo <= i <= _hi
  invariant J
  modifies W
{
  i := i - 1;  // this is different from the "up" loop
  Body
}
```

Note that the "up" loop performs a post-increment of `i`, whereas the "down" loop
performs a pre-decrement of `i`. This is common in computer science.

Note that in both cases, `Body` is never executed with `i` having the value `hi`.
This is likely to lead to confusion for users who are used to adding those
ugly `- 1`'s. Programs in the proposed design will look prettier, and also offer
a more direct translation to pretty intervals in invariants.

# Rationale and alternatives
[rationale-and-alternatives]: #rationale-and-alternatives

The proposal introduces 3 new keywords: `for`, `to`, `downto`. Alternatives are:

- Make `to` and `downto` context-sensitive keywords. That is, reserve them only in
  `for` loops as shown by the grammar above.

- Don't support "down" loops. This would mean `downto` does not need to be reserved.

- Use `..` instead of `to` for "up" loops. Without the invention of new syntax
  for intervals written in the "opposite order", this excludes "down" loops.
  If `..` is used in the syntax, then it would also seem natural to write `in`
  instead of `:=`, like this:

  ```
  for i in lo .. hi
  ```

# Prior art
[prior-art]: #prior-art

Most popular languages have some form of `for` loop. In C-like languages, the first
line of the proposed `for` loops would look like:

``` C
for (int i = lo; i < hi; i++)
```

ignoring issues of types, issues of scopes, the issue of re-evaluating `hi`, and
the issue of prohibiting other updates of `i`.

"Down" loops written in C look like:

``` C
for (int i = hi; lo <= --i; )
```

The Eiffel programming language supports loop invariants. It has an `until`
condition, which says when to terminate, rather than the negated termination
condition of standard `while` loops and C's `for` loop. The update of the
loop index is provided in the program text, as in C and as for common `while` loops.

Why3 supports the OCaml-like `for` loop

```
for i = lo to hi do invariant { J } Body done
```

It also has a `downto` variant. In this form, the upper bound `hi` is still
inclusive; that is, the automatically generated loop invariant is

```
lo <= i <= hi + 1
```

Another unique and verification-friendly feature of Why3's `for` loops
is that if the values of `lo` and `hi` are such that the loop body will not
iterate at all, then the entire loop is skipped, including the checking of
the invariant on entry to the loop.

# Unresolved questions
[unresolved-questions]: #unresolved-questions

- Are "down" loops important to include in the language?
- Is it okay to exclude loops there the loop index changes by something other than `+1` or `-1`?
- Is the `..` token to be preferred over the `to` keyword?
- If `..` is used and "down" loops are important, should there be an additional keyword like `reverse`
  added to the syntax somewhere?
- `while` loops are nice in teaching. They make it clear where the loop index is declared and what
  values it may have. You can also see the update of the loop index, which is useful if you want
  to use weakest preconditions to compute the needed values of variables near the end of the loop
  body. Would the availability of `for` loops lead teachers and students astray by luring them
  into using `for` loops before loop invariants are clearly understood?

# Future possibilities
[future-possibilities]: #future-possibilities

Another kind of loop that is missing from Dafny are `foreach` loops, which loop over all
values of some collection or `iterator`. If such were ever introduced, a syntax like

```
foreach x in S
  invariant J
{
  Body
}
```

is still available.
