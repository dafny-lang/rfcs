Ghost datatype constructors
===========================

This RFC proposes that each constructor of a datatype can be declared
to be `ghost`. The proposal also applies to codatatypes, but, for
brevity, the RFC will continue to say just "datatype". Declaring a
constructor to be `ghost` limits usage of that constructor to ghost
contexts and auto-initialization.  It also restricts discriminators
and destructors in compiled contexts, so that it is never necessary at
run time to check if a value is of a ghost variant.

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

```
datatype D = ghost G(x: int) | D0(y: int) | D1(z: int)
```

In a compiled context, the expression `d.D0?` has the precondition
`!d.G?`.

Similarly, a destructor `x` usually has as its precondition (for both
reading and updating) that the receiver is of a variant that supports
the destructor. In compiled contexts, this precondition is now
strengthened with the condition that the receiver is not of a ghost
variant. As a concrete example, consider the declaration

```
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

```
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
