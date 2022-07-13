- Feature Name: unicode_strings
- Start Date: 2022-07-06
- RFC PR: [dafny-lang/rfcs#13](https://github.com/dafny-lang/rfcs/pull/13)
- Dafny Issue: [dafny-lang/dafny#413](https://github.com/dafny-lang/dafny/issues/413)

# Summary
[summary]: #summary

The Dafny `string` type is an alias for the type `seq<char>`, and the `char` type is an opaque built-in type
representing individual characters. `char` values can be converted to and from `int` values (using `as char` and `as int` expressions),
and an `int` value corresponding to a `char` value is currently required to be a valid UTF-16 code point, i.e. in the range
`[0, 65536)`. This range includes the so-called "surrogate" characters, i.e. code points in the range `[0xD800, 0xDFFF]`, which must be used in pairs in order to encode some characters in UTF-16, and are not assignable Unicode code points themselves.

I propose a breaking change in Dafny 4.0, to make `char` represent any Unicode character, independent of the encoding used.
This means that the corresponding `int` value for a `char` must always be a [Unicode scalar value](https://www.unicode.org/versions/Unicode14.0.0/ch03.pdf#G7404), meaning any value in the range `[0, 0x10FFFF]` but excluding the surrogate characters from `[0xD800, 0xDFFF]`.

# Motivation
[motivation]: #motivation

The two primary motivations behind this change are correctness and compatibility.

## Correctness

The current definition of these types means that the Dafny `string` type allows data that is not a valid Unicode string.
The value `[0xD800 as char]`, for example, is not a valid Unicode string and has no valid encoding in UTF-8, UTF-16,
or any other encoding.
This means that any logic to process strings must manually specify pre-conditions to exclude invalid values, or
be less precise with its specification. For example, an implementation of UTF-8 encoding would have to reject
invalid inputs in a pre-condition, dynamically fail if given invalid strings, or implement a lossy encoding by
discarding or replacing invalid characters.

## Compatibility

The current definitions of `string` and `char` are biased towards using a UTF-16 encoding at runtime.
This aligns well with some compilation target languages which also use UTF-16, such as Java, C#, and JavaScript, 
but less well with those that use the more popular UTF-8 encoding, such as Go or Rust.
Any Dafny code that interfaces with external code will often have to convert between `string` values and
native representations of strings, and baking in the assumption of UTF-16 imposes a complexity and performance
penalty for multiple target environments.

# Guide-level explanation
[guide-level-explanation]: #guide-level-explanation

As of Dafny 4.0, the default semantics of the `char` type have been changed to represent Unicode scalar values instead of UTF-16 code points.
This means that surrogate code points, meaning those in the range `[0xD800, 0xDFFF]`, are no longer allowed. This also means
code points that require more than 16 bits, meaning those in the range `[0x10000, 0x1FFFF]`, are now directly representable
as `char` values.

The definition of the `char` type is controlled by a command-line switch called `/unicodeChar`, where `/unicodeChar:0`
enables the previous semantics and `/unicodeChar:1` enables the new semantics described above.
The default prior to Dafny 4.0 is `/unicodeChar:0`, but the default as of Dafny 4.0 is `/unicodeChar:1`.
This change in definition can cause previously verified code to no longer verify,
since expressions such as `someIntValue as char` or `someCharValue + 'a'` are no longer allowed to result in
surrogate code points.

A related but largely orthogonal issue has also been addressed.
Dafny source code files must be encoded in UTF-8,
but in previous versions of Dafny string literals could only contain printable and white-space ASCII characters,
due to a limitation of the parser generator the toolchain uses.
This has been fixed, and both standard form and verbatim form string literals now allow any Unicode characters.
A second form of escape sequence, `\UXXXXXXXX`, is now provided to support characters outside of the Basic Multilingual Plane
using their direct Unicode code points instead of using surrogates.
This change is fully backwards-compatible and not controlled by the `unicodeChar` flag.

The exact representation of strings at runtime, including the particular encoding,
is an implementation detail of a particular backend, and will often be optimized for the idioms and support
of the target environment. Enabling Unicode characters will change the target language types used to
represent characters and strings, and hence may cause compilation errors when using additional external
target language code.

Note also that although the Unicode scalar value concept is more general than UTF-16 code units,
it still does not always correspond to what humans will perceive as a single atomic characters when rendered;
see the concept of grapheme clusters [here](https://unicode.org/reports/tr29/) for more information.
The proposed change to the `char` type is only intended to allow the Dafny language to safely abstract
away from encodings, especially to support verifiably-correct code that must compile to multiple target languages.
Providing more of the concepts defined by the Unicode standard is left out of scope for this proposal,
under the assumption that it will enable such implementations via Dafny source code in sharable libraries instead.

# Reference-level explanation
[reference-level-explanation]: #reference-level-explanation

## Verification

The change to the definition of `char` in the `DafnyPrelude.bpl` file is very minimal.
The only change is to replace expressions such as `0 <= n && n < 65536` with a separate predicate defined as follows:

```boogie
function char#IsUnicodeScalarValue(n: int): bool {
  (0                  <= n && n <= 55295   /* 0xD7FF */) || 
  (57344 /* 0xE000 */ <= n && n <= 1114111 /* 0x10FFFF */ )
}
```

As described above in the user-facing description of this feature, this will cause verification failures by design.
Unlike many other programming languages that have had to add Unicode support over a major version bump,
Dafny is unusually well-positioned to catch most regressions statically.
Given this, it is not worth the effort to build any additional migration features to help customers adopt this change.

## Compilation/Runtime

This change also has a reasonably small effect on the runtime behavior of any self-contained Dafny program,
meaning a program that does not pass data over an interface with external code.
The only difference is that the `char` type will need to be compiled to a native datatype
that supports 32 bits of data (or technically 21 according to the actual Unicode scalar value range)
rather than 16 bits as previous versions did.
Many target languages will have dedicated types designed to hold any Unicode scalar value,
such as the `char` primitive type in Rust or the `rune` alias for `int32` in Go.

The main complexity in implementing this change is minimizing the migration pain for
code bases that use `{:extern}` definitions to pass string values in and out of the Dafny runtime.
This generally requires converting between the internal representation of Dafny strings
and the native implementation in the target language,
e.g. between `Dafny.ISequence<char>` and `System.String` in C#.
Even there, the various Dafny runtime libraries provide helper methods that can be adjusted 
to work with the new semantics of Unicode characters.
In the C# runtime, for example, the `Sequence.FromString(string)` method converts a native string
to a equivalent `Dafny.ISequence<char>` copy.
A parallel method named something similar to `Sequence.UnicodeFromString(string)` could be added
that would return a `Dafny.ISequence<uint32>` copy instead.
Migrating an existing codebase should reduce to a simple find-and-replace operation.

Each runtime should also make it possible to wrap an idiomatic representation of a Unicode string
as the runtime representation of the Dafny `seq<char>` type, without having to make an additional copy. 
At the time of writing this, only the Java runtime supports this feature,
via a `StringDafnySequence` class that wraps a `java.lang.String` value and implements the `ISequence<Character>` interface.
Another similar parallel `UnicodeStringDafnySequence` adaptor can be provided that implements `ISequence<Integer>` instead.

The one wrinkle with this feature is that methods such as `select(i)`, which implement Dafny expressions such as `s[i]`,
currently take constant time on an `StringDafnySequence`, since a `java.lang.String` also stores its contents as UTF-16
code units. However, if `UnicodeStringDafnySequence.select(i)` will need to produce the i'th Unicode scalar value instead,
this will require decoding all characters up to that index, which will take linear time in general instead.
The solution will be to lazily decode strings into their UTF-32 encoded equivalent (i.e. sequence of scalar values)
on the first operation that requires it. This mirrors the optimization of evaluating concatenation of sequences
lazily in the current C# and Java runtimes, and means that in most code that manipulates individual characters,
the amortized runtime of indexing operations will still be constant.

Note that this optimization will also help offset the fact that materializing and manipulating individual `char` values
will in general require twice as much memory after this change.
The compiler can leverage this support to initially store string literal values as UTF-8 bytes,
and operations such as concatenation or equality comparisons can be implemented
without having to decode these bytes into character values.

# Drawbacks
[drawbacks]: #drawbacks

Changing the behavior of an existing concept in a backwards-incompatible way always carries a high cost,
and I do not propose it lightly. It optimizes for a better new Dafny user experience,
where simple code that works with strings will be more correct by default,
at the expense of existing users potentially needing to change their code when upgrading,
or adding the `/unicodeChar:0` option to their build process.
It is likely that the `/unicodeChar:0` option will need to be supported for a long time,
to support users unable or unwilling to do this work,
although the burden of maintaining this option should not be high.

I propose this approach since Dafny is still relatively young as a programming language,
and hence the impact of the breaking change is still relatively small.
If anything, the longer we wait to correct this issue,
the more Dafny code will continue to be written with subtle bugs that verification does not detect,
or even new compilation targets that introduce them when compiling.

# Rationale and alternatives
[rationale-and-alternatives]: #rationale-and-alternatives

There are many ways to tackle this problem, many of them inspired in part by how other programming languages
have tackled them in the past (see also [Prior Art](#prior-art)).

## Enforce valid UTF-16 strings in the verifier

The cheapest solution to implement would likely be to add a new requirement in the verifier
that surrogate `char` values are only used in pairs as intended.
This would likely require more user effort to migrate their code, however,
as every operation on strings would now have to prove that a surrogate pair
is not being split up.
It also does not reduce the complexity of compiling
strings to various target languages that do not necessarily use UTF-16.

## Define "valid UTF-16 strings" as a predicate in a shared library

The next cheapest solution would be to define a subset type of `string` that enforces
correct usage of surrogate characters.
Similar such definitions already exist for valid [UTF-8](https://github.com/aws/aws-encryption-sdk-dafny/blob/mainline/src/Util/UTF8.dfy#L21).
and [UTF-16](https://github.com/dafny-lang/libraries/blob/master/src/Unicode/Utf16EncodingForm.dfy) code unit sequences
in some Dafny codebases.
This also introduces the same proof obligations as the previous solution,
although here they could be proved by numerous helper methods that operate on the subset type
in the same shared library.

***TODO***

## Change the definition of the string type

The current definition of `string` as an alias for `seq<char>` is problematic because surrogate code points
are not truly independent values in the sequence.
It is actually quite unusual for a general-purpose language to treat strings as only a special case of
generic datatypes for arbitrary sequences of values.
Dafny could instead make `string` an alias for a different type, whether built-in or defined in Dafny source in the runtime or a standard library,
that treats strings as a more specialized datatype. It could then be more prescriptive about picking a definitive encoding to
support directly (most likely UTF-8).

This would certainly require more effort for existing code to migrate to.
It is also a much more expensive solution to implement, since it requires creating an API for strings
that is at least adequate to replace all existing usage of sequence operations.
These interfaces often become very large to support all common string operations efficiently,
and would need very careful thought.
Although unusual, representing strings directly as sequences of abstract characters
works very well for a verification-focussed language like Dafny,
since sequences are already a deep built-in concept in the language semantics.

This new type could alternatively be introduced with a different name, while keeping the alias of `string` for `seq<char>`.
This would only increase the confusion and cognitive burden for Dafny users in the future, though.
It may be a good idea, however, for a shared Dafny source library to define a `EncodedString` wrapper
around encoded bytes that includes a ghost `string` value defining the actual abstract string encoded.
This could make the [existing implementations of UTF-8 and UTF-16 encodings](https://github.com/dafny-lang/libraries/tree/master/src/Unicode)
more efficient and pleasant to use.

## Add a new, distinct "rune" type

We could maintain the current definition of the `char` type, and introduce a new `rune` type to represent Unicode scalar values
instead ("rune" being the term both Go and C# use for this).
This would make it more obvious when reading Dafny source code in isolation whether it was using the new definitions of strings.
There are often few explicit references to individual character values in code that references string values, however,
and even when the `char` type is used it can often be only implicitly referenced because of type inference.
This alternative does not seem to be worth the implementation cost or additional cognitive load on users,
especially since it is hard to imagine any codebase needing to use both `char` and `rune` together.

## Disallow compiling s[i] 

Given popular Unicode encodings such as UTF-8 and UTF-16 do not support random access of characters,
we could decide to forbid random access of string elements (i.e. `s[i]`) in compiled code,
instead directing users to fallback to external code for efficient access,
or to sequential access via the new [ordered quantification features](https://github.com/dafny-lang/rfcs/pull/10) (once they are implemented).
This would be a much more disruptive breaking change for existing code, however.
String indexing would not be the first instance in Dafny of a simple, mathematical expression
that supports verification easily but is inefficient at runtime.
The proposed lazy decoding approach should provide a good balance between the clean expression of concepts
and efficient, unsurprising runtime behavior.

# Prior art
[prior-art]: #prior-art

Unicode has a long and messy history, and the approach to supporting Unicode varies dramatically across different programming languages.
Here is the current state of several popular programming languages, especially those that Dafny currently or will likely
soon support compiling to:

***TODO***

* C#:
* Java:
* Go:
* JavaScript:
* C/C++:
* Python:
* Ruby:
* Rust:
* Swift:

# Unresolved questions
[unresolved-questions]: #unresolved-questions

***TODO***

# Future possibilities
[future-possibilities]: #future-possibilities

***TODO***