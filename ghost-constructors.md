Ghost datatype constructors
===========================

This RFC proposes that each constructor of a datatype can be declared
to be `ghost`. The proposal also applies to codatatypes, but, for
brevity, the RFC will continue to say just "datatype". Declaring a
constructor to be `ghost` limits usage of that constructor to ghost
contexts and auto-initialization.  It also restricts discriminators
and destructors in compiled contexts, so that it is never necessary at
run time to check if a value is of a ghost variant.

Simple Example
--------------

A simple application of ghost constructors is a program that defines

``` dafny
datatype Color = Red | Green | Yellow | Blue
```

and models some program behavior that's described in terms of these 4
colors.  Although all the colors play a role in the specification, the
program only needs `Green` and `Blue` at run time. With ghost
constructors, the program can then change the definition of `Color` to

``` dafny
datatype Color = ghost Red | Green | ghost Yellow | Blue
```

This is in the style of using ghosts today. For example, today, a
program may include parameters and functions that are used only in
specifications, and these can then be marked as ghost.

Motivating Example
------------------

The main motivating example for ghost constructors is uninitialized
storage. In general, not initializing storage is a bad idea, since
accidental use of the uninitialized storage may lead to unintended
behavior at run time. However, one can make some programs more
efficient if large quantities of storage are initialized lazily.  To
verify that lazily initialized storage is used properly, a language
needs some mechanism by which a verifier understands that certain
values are not to be used. One can imagine that a program has some
"ghost values"---values that may be present at run time, but are never
used for anything important at run time. Ghost constructors is a
simple and natural way to extend Dafny so that one can reason about
such "ghost values".

To show this more concretely, consider a class that implements an
extensible vector of elements. The element type is given as a type
parameter, about which nothing is known. The class uses a fixed-lenght
array to hold the elements of the vector. To reduce copying, the class
allocates the array to be "oversized", to give room for future
extensions of the vector. The class only uses a prefix of the array's
elements, so the values of the remaining array elements are
immaterial. It would therefore be nice not to have to initialize those
elements until the vector needs them.

Here is a module that implements such a class. Note how the
`InitSingleton` constructor and the `Extend` method allocate oversized
arrays, whereas the `InitEmpty` constructor allocates a precisely
sized array. (The example uses the Dafny 4 syntax for functions and
predicates.)

``` dafny
module VectorModule {
  export
    reveals Vector
    provides Vector.Elements, Vector.Repr, Vector.Valid
    provides Vector.InitEmpty, Vector.InitSingleton
    provides Vector.Get, Vector.Put, Vector.Extend

  class Vector<X> {
    ghost var Elements: seq<X>
    ghost var Repr: set<object>

    var arr: array<X>
    var n: nat // the number of elements of "arr" that are in use

    ghost predicate Valid()
      reads this, Repr
      ensures Valid() ==> this in Repr
    {
      && this in Repr
      && arr in Repr
      && n <= arr.Length
      && Elements == arr[..n]
    }

    constructor InitEmpty()
      ensures Valid() && fresh(Repr)
      ensures Elements == []
    {
      arr := new X[0];
      n := 0;
      Elements := [];
      Repr := {this, arr};
    }

    constructor InitSingleton(x: X)
      ensures Valid() && fresh(Repr)
      ensures Elements == [x]
    {
      arr := new X[1000](_ => x);
      n := 1;
      Elements := [x];
      Repr := {this, arr};
    }

    function Get(i: nat): X
      requires Valid() && i < |Elements|
      reads Repr
      ensures Get(i) == Elements[i]
    {
      arr[i]
    }

    method Put(i: nat, x: X)
      requires Valid() && i < |Elements|
      modifies Repr
      ensures Valid() && fresh(Repr - old(Repr))
      ensures Elements == old(Elements)[i := x]
    {
      arr[i] := x;
      Elements := Elements[i := x];
    }

    method Extend(x: X)
      requires Valid()
      modifies Repr
      ensures Valid() && fresh(Repr - old(Repr))
      ensures Elements == old(Elements) + [x]
    {
      if n == arr.Length {
        arr := new X[n + 3000](i requires Valid() reads this, Repr => if 0 <= i < n then arr[i] else x);
        Repr := Repr + {arr};
      } else {
        arr[n] := x;
      }
      n := n + 1;
      Elements := Elements + [x];
    }
  }
}
```

The unused portion of the two oversized arrays (in `InitSingleton` and
`Extend`) are initialized with a value of type `X` that these routines
happen to have around. In contrast, `InitEmpty` does not know what an
`X` element looks like (or if one even exists), so it has no choice
but to allocate an empty array.

We can change the class to use an `Option` type to indicate which
elements are in use:

``` dafny
module VectorModule {
  export
    reveals Vector
    provides Vector.Elements, Vector.Repr, Vector.Valid
    provides Vector.InitEmpty, Vector.InitSingleton
    provides Vector.Get, Vector.Put, Vector.Extend

  datatype Option<X> = None | Some(value: X)

  class Vector<X> {
    ghost var Elements: seq<X>
    ghost var Repr: set<object>

    var arr: array<Option<X>>
    var n: nat // the number of elements of "arr" that are in use

    ghost predicate Valid()
      reads this, Repr
      ensures Valid() ==> this in Repr
    {
      && this in Repr
      && arr in Repr
      && |Elements| == n <= arr.Length
      && forall i :: 0 <= i < n ==> arr[i].Some? && Elements[i] == arr[i].value
    }

    constructor InitEmpty()
      ensures Valid() && fresh(Repr)
      ensures Elements == []
    {
      arr := new Option<X>[1000];
      n := 0;
      Elements := [];
      Repr := {this, arr};
    }

    constructor InitSingleton(x: X)
      ensures Valid() && fresh(Repr)
      ensures Elements == [x]
    {
      arr := new Option<X>[1000];
      n := 1;
      Elements := [x];
      Repr := {this, arr};
      new;
      arr[0] := Some(x);
    }

    function Get(i: nat): X
      requires Valid() && i < |Elements|
      reads Repr
      ensures Get(i) == Elements[i]
    {
      arr[i].value
    }

    method Put(i: nat, x: X)
      requires Valid() && i < |Elements|
      modifies Repr
      ensures Valid() && fresh(Repr - old(Repr))
      ensures Elements == old(Elements)[i := x]
    {
      arr[i] := Some(x);
      Elements := Elements[i := x];
    }

    method Extend(x: X)
      requires Valid()
      modifies Repr
      ensures Valid() && fresh(Repr - old(Repr))
      ensures Elements == old(Elements) + [x]
    {
      if n == arr.Length {
        var b := new Option<X>[n + 3000];
        forall i | 0 <= i < n {
          b[i] := arr[i];
        }
        arr := b;
        Repr := Repr + {arr};
      }
      arr[n] := Some(x);
      n := n + 1;
      Elements := Elements + [x];
    }
  }
}
```

In this new program, nothing is said about the unused parts of the
arrays. Dafny is okay with this, because `Option<X>`, unlike `X`, is
known to be an auto-init type. Note that the `InitEmpty` is now able
to allocate an oversized array, too. The `Option` datatype is also
nice, because it gives a well understood way to describe when an array
element has a value of importance.

However, the program has some drawbacks. One is that it has a
"wrapper" (`Some`) around each element. This wrapper has some run-time
overhead. Another drawback is that the run-time system still has to
initialize the elements of the oversized arrays, namely to the value
`None`. Still, every elements that's ever used in the array is of the
`Some` variant.

By changing the `None` constructor to be ghost, we remove these drawbacks.

``` dafny
datatype Option<X> = ghost None | Some(value: X)
```

This is the only change necessary---the rest of the program and
specifications stay the same.

The rules of ghost constructors (see below) ensure that the program
never needs to distinquish `None` and `Some` values. Because of the
restrictions around ghost constructors, a compiler now has the freedom
to omit an initialization when such an initialization would have used
the value `None` anyway. Furthermore, the compiler can also do the
optimization of removing the wrapper. That is, the type
`array<Option<X>>` can be compiled just like `array<X>`, and the
destructor `.value` is then just the identity function.

Syntax
------

The name of a constructor in a datatype declaration can be preceded
with the keyword `ghost`.  This makes the constructor a ghost
constructor. A value created by a ghost constructor is called a ghost
variant, and a datatype that has one or more ghost constructors is
called a ghost-variant datatype.

Resolution
----------

For a ghost constructor `ghost G(...)`, the automatically
generated discriminator `G?` is also ghost.  Discriminators for
non-ghost constructors can be used in compiled contexts; however, use
of these discriminators has a precondition that is checked by the
verifier (explained below).

In a `match` construct, a `case` pattern can be a variable that will
bind to a particular part of the source expression. (If the name of
this variable is irrelevant, the language allows it to be given as
`_`.) In a compiled context, the type of such a variable is not
allowed to be a ghost-variant datatype.

A ghost-variant datatype is considered _not_ an equality-supporting
type. That is, the type does not obtain the type characteristic
`(==)`, and thus values of the type can be compared for equality only
in ghost contexts.

The way that a datatype is considered to be an auto-init type or
nonempty empty is not affected by the presence of ghost constructors.
Internally, the resolver picks out a "default constructor" for every
auto-init type; the constructor thus picked may be a ghost
constructor.

How `(!new)` is used and inferred is not affected by ghost
constructors.

Verification
------------

For a ghost-variant datatype, the use of a non-ghost discriminator in
a compiled context is allowed only if it is known that the value is
not of any of the ghost variants. As a concrete example, consider the
following declaration:

``` dafny
datatype D = ghost G(x: int) | D0(y: int) | D1(z: int)
```

In a compiled context, the expression `d.D0?` has the precondition
`!d.G?`.

Similarly, a destructor `x` usually has as its precondition (for both
reading and updating) that the receiver is of a variant that supports
the destructor. In compiled contexts, this precondition is now
strengthened with the condition that the receiver is not of a ghost
variant. As a concrete example, consider the declaration

``` dafny
datatype D = ghost G(x: int, y: int) | D0(x: int) | D1(z: int)
```

In a compiled context, the expression `d.x` has the precondition
`x.D0?`, and the expression `d.y` has the precondition `false`.

Compilation
-----------

In a simple compilation strategy, the only differences brought about
by ghost constructors are:

* If a ghost constructor is picked as the default constructor, then
  the compiler uses an arbitrary bit pattern (possibly, but not
  limited to, the all-zero bit pattern) for initialization.

* For a destructor that appears in both a ghost constructor and a
  non-ghost constructor, any need to consult a ghost discriminator at
  run time is replaced by `false` and optimized.  For example, if
  constructors `G0` and `G1` are ghost, constructors `D0` and `D1` are
  non-ghost, and these four constructors define a destructor `x`, then
  the expression `d.x` is compiled along the lines of

      if d.D0? then ((D0)d).x
      else ((D1)d).x

  instead of

      if d.G0? then ((G0)d.x)
      else if d.G1? then ((G1)d.x)
      else if d.D0? then ((D0)d).x
      else ((D1)d).x

  and similarly for the expression `d.(x := E)`.

A more elaborate compilation strategy can attempt to eliminate the
constructor wrappers altogether. This is best explained by example.
The most compelling use case for this is an "optionally initialized"
type:

``` dafny
datatype Unknown<T> = ghost Absent | Present(value: T)
```

Consider a variable `u` of type `Unknown<T>` for some `T`. Type
`Unknown<T>` is an auto-init type, so the language says `u` has some
initial value. As far as the program can tell, this initial value may
be `Absent`. There is no way in compiled code to test if the value is
`Absent`, so the only way to make sure the `u`'s value is not `Absent`
is to initialize `u` with a `Present` value. Also, the only way to use
`u` is to prove that its value is present. Therefore, the more
elaborate compiler strategy can choose to compile an `Unknown<T>` in
the same way that it compiles `T`. More precisely, the target variable
`u` would have type `T` and there's no reason to give `u` any
particular initial value since it won't ever be used (unless the
target language of the compilation has stricter rules). A use of the
discriminator `u.Present?` is compiled as `true` (because, remember,
this discriminator can only be used if the condition `!u.Absent?` has
been verified), and a use of the destructor `u.value` is compiled as
just `u`.

This lets a program allocate an array with element type `Unknown<T>`
without specifying any particular initial value for the elements, even
if `T` is not an auto-init type. The program then needs to keep track
of which elements of the array it has initialized. When an initialized
element is used, it is at run time accessed directly in the target
array, which has type `array<T>`. What is described here can, for
example, be used to naturally implement a variable-size vector of
elements using a fixed-size array, where the invariant is that the
first `n` elements are present (where `n` is the current length of the
vector).
