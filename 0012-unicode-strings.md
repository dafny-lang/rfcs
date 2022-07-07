- Feature Name: unicode_strings
- Start Date: 2022-07-06
- RFC PR: [dafny-lang/rfcs#13](https://github.com/dafny-lang/rfcs/pull/13)
- Dafny Issue: [dafny-lang/dafny#413](https://github.com/dafny-lang/dafny/issues/413)

# Summary
[summary]: #summary

The Dafny `string` type is an alias for the type `seq<char>`, and the `char` type is an opaque built-in type
representing individual characters. `char` values can be converted to and from `int` values (using `as char` and `as int` expressions),
and an `int` value corresponding to a `char` value is currently required to be a valid UTF-16 code point, i.e. in the range
`[0, 65536)`. This range includes the so-called "surrogate" characters, i.e. code points in the range `[0xD800, 0xDFFF)`, which must be used in pairs in order to encode some characters in UTF-16, and are not assignable Unicode code points themselves.

I propose a breaking change in Dafny 4.0 to make `char` instead represent any Unicode character.
*** TODO ***: You don't mean any currently assigned character, otherwise you break as new characters are added.
This means that the corresponding `int` value for a `char` must always be a [Unicode scalar value](https://www.unicode.org/versions/Unicode14.0.0/ch03.pdf#G7404), meaning any value in the range `[0, 0x10FFFF]` excluding the surrogate characters from `[0xD800, 0xDFFF)`.

# Motivation
[motivation]: #motivation

The two primary motivations behind this change are correctness and compatibility.

## Correctness

The current definition of these types means that the Dafny `string` type allows data that is not a valid Unicode string.
The value `[0xD800 as char]`, for example, does not represent any character and has no valid encoding in UTF-8.
This means that any logic to process strings must manually specify pre-conditions to exclude invalid values, or
be less precise with its specification. For example, a naive implementation of UTF-8 encoding would have to reject
invalid inputs in a pre-condition, dynamically fail if given invalid strings, or implement a lossy encoding by
discarding or replacing invalid characters.

## Compatibility

The current definitions of `string` and `char` are biased towards using a UTF-16 encoding at runtime.
This aligns well with some compilation target languages which also use UTF-16, such as Java and C#, 
but less well with those that use the more popular UTF-8 encoding, such as Go or Rust.
Any Dafny code that interfaces with external code will often have to convert between `string` values and
native representations of strings, and baking in the assumption of UTF-16 imposes a complexity and performance
penalty for multiple target environments.

# Guide-level explanation
[guide-level-explanation]: #guide-level-explanation

As of Dafny 4.0, the `char` type ...

TODO: change \uXXXX to allow up to six digits, reject surrogates? Could allow surrogates and have the compiler enforce pairs

The exact representation of strings at runtime, including the particular encoding,
is an implementation detail of a particular backend, and will often be optimized for the idioms and support
of the target environment.

## Migration

Requirements:

* Can we ensure there is always a compile-time error?

# Reference-level explanation
[reference-level-explanation]: #reference-level-explanation

(runtime representation compatibility, usually considered advanced use)

 In general, each runtime should make it possible to wrap an idiomatic representation of a Unicode string
 as the runtime representation of `seq<char>`. As of the date of writing this, the Java runtime enables this through
 a `StringDafnySequence` class that wraps a `java.lang.String` value.

# Drawbacks
[drawbacks]: #drawbacks

Why should we *not* do this?

# Rationale and alternatives
[rationale-and-alternatives]: #rationale-and-alternatives

## Enforce valid UTF-16 strings in the verifier

## Encode valid UTF-16 strings as a library predicates

## Distinct string type

## Distinct "rune" type

## Disallow compiling s[i] 

# Prior art
[prior-art]: #prior-art



# Unresolved questions
[unresolved-questions]: #unresolved-questions


# Future possibilities
[future-possibilities]: #future-possibilities

