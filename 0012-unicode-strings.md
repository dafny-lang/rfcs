- Feature Name: unicode_strings
- Start Date: 2022-07-06
- RFC PR: [dafny-lang/rfcs#13](https://github.com/dafny-lang/rfcs/pull/13)
- Dafny Issue: [dafny-lang/dafny#413](https://github.com/dafny-lang/dafny/issues/413)

# Summary
[summary]: #summary

The Dafny `string` type is an alias for the type `seq<char>`, and the `char` type is an opaque built-in type
representing individual characters. `char` values can be converted to and from `int` values (using `as char` and `as int` expressions),
and an `int` value corresponding to a `char` value is currently required to be a valid UTF-16 code unit, i.e. in the range
`[0, 65536)`. This range includes the so-called ["surrogate" code points](https://unicode.org/faq/utf_bom.html#utf16-2),
i.e. values in the range `[0xD800, 0xE000)`,
which must be used in pairs in order to encode some characters in UTF-16,
and are not assignable Unicode code points themselves.

I propose a breaking change in Dafny 4.0, to make `char` represent any Unicode code point, independent of the encoding used.
This means that the corresponding `int` value for a `char` must always be a [Unicode scalar value](https://www.unicode.org/versions/Unicode14.0.0/ch03.pdf#G7404), meaning any value in the range `[0, 0x11_0000)` but excluding the surrogate code points from `[0xD800, 0xE000)`.

# Motivation
[motivation]: #motivation

The two primary motivations behind this change are correctness and compatibility.

## Correctness

The current definition of these types means that the Dafny `string` type allows data that is not a valid Unicode string.
The value `"\uD800"`, for example, is not a valid Unicode string and has no valid encoding in UTF-8, UTF-16,
or any other encoding.
This means that any logic to process strings must manually specify pre-conditions to exclude invalid values, or
be less precise with its specification. For example, an implementation of UTF-8 encoding would have to reject
invalid inputs in a pre-condition, dynamically fail if given invalid strings, or implement a lossy encoding by
discarding or replacing invalid characters.

## Compatibility

The current definitions of `string` and `char` are biased towards using a UTF-16 encoding at runtime.
This aligns well with some compilation target languages which also use UTF-16, such as Java, C#, and JavaScript, 
but less well with those that use the recently more popular UTF-8 encoding, such as Go or Rust.
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

This change can also result in behavioral changes that may not be caught by verification,
as they may not intersect with any explicit specifications.
Here is an example of a program that will behave differently depending on the value of `/unicodeChar`,
and hence differently on Dafny 4.0 compared to earlier versions:

```dafny
method Main() {
  var s := "Unicode is just so \ud83d\ude0e";
  print s, "\n"     // "Unicode is just so 😎" (not affected by /unicodeChar)
  print |s|, "\n"   // /unicodeChar:0 => "21"
                    // /unicodeChar:1 => "20"
  print s[19], "\n" // /unicodeChar:0 => "�"
                    // /unicodeChar:1 => "😎"
}
```

A related but largely orthogonal issue has also been addressed.
Dafny source code files must be encoded in UTF-8,
but in previous versions of Dafny,
string and character literals could only contain printable and white-space ASCII characters,
due to a limitation of the Coco/R parser generator the toolchain uses.
This has been fixed, and both standard form and verbatim form string literals now allow any Unicode characters.
A second form of escape sequence accepting a hexadecimal number with up to six digits, `\u{XXXXXX}`, 
is now provided to support characters outside of the Basic Multilingual Plane
using their direct Unicode code points instead of using surrogates.
These changes are fully backwards-compatible and not controlled by the `unicodeChar` flag.

```dafny
// Several different ways to express the same string literal
var s1 := "Unicode is just so \ud83d\ude0e";
var s2 := "Unicode is just so \u{1F60E}";
var s3 := "Unicode is just so 😎";
var s4 := @"Unicode is just so 😎";  // Escape sequences are not supported in verbatim strings
```

The exact representation of strings at runtime, including the particular encoding,
is an implementation detail of a particular backend, and will often be optimized for the idioms and support
of the target environment. Enabling Unicode characters will change the target language types used to
represent characters and strings, and hence may be a breaking change when using additional external
target language code.

Note also that although the Unicode scalar value concept is more general than UTF-16 code units,
it still does not always correspond to what humans will perceive as single atomic characters when rendered.
For example, the string `"e\u0301"` contains two Unicode scalar values, but renders as the single character `é`.
See the concept of grapheme clusters [here](https://unicode.org/reports/tr29/) for more details.
The proposed change to the `char` type is only intended to allow the Dafny language to safely abstract
away from encodings, especially to support correct code that must compile to multiple target languages.
Providing more of the concepts defined by the Unicode standard is left out of scope for this proposal,
under the assumption that it will enable such implementations via Dafny source code in sharable libraries instead.

# Reference-level explanation
[reference-level-explanation]: #reference-level-explanation

## Verification

The change to the definition of `char` in the `DafnyPrelude.bpl` file is minimal.
The only change is to replace expressions such as `0 <= n && n < 65536` with a separate predicate defined as follows:

```boogie
function char#IsUnicodeScalarValue(n: int): bool {
  (0                  <= n && n < 55296   /* 0xD800 */) || 
  (57344 /* 0xE000 */ <= n && n < 1114112 /* 0x11_0000 */)
}
```

As described above in the user-facing description of this feature, this will cause verification failures by design.
Unlike many other programming languages that have added Unicode support over a major version bump,
Dafny is unusually well-positioned to catch most regressions statically.
Given this, it does not seem worth the effort to build any additional migration features to help customers adopt this change.

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
to an equivalent `Dafny.ISequence<char>` copy.
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

## Define "valid UTF-16 strings" as a subset type in a shared library

The next cheapest solution would be to define a subset type of `string` that enforces
correct usage of surrogate characters.
Similar such definitions already exist for valid [UTF-8](https://github.com/aws/aws-encryption-sdk-dafny/blob/mainline/src/Util/UTF8.dfy#L21)
and [UTF-16](https://github.com/dafny-lang/libraries/blob/master/src/Unicode/Utf16EncodingForm.dfy) code unit sequences
in some Dafny codebases.
This also introduces the same proof obligations as the previous solution,
although here they could be proved by numerous helper methods that operate on the subset type
in the same shared library.

This would likely be the best solution if changing the Dafny language itself was not an option.
The major downside is that built-in sequence operations such as `s[i]` and `s + s'` would still require additional
effort to achieve verification, or would have to be abandoned entirely in favour of the helper methods
provided by the shared library.

## Change the definition of the `string` type

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
works very well for a verification-focused language like Dafny,
since sequences are already a deep built-in concept in the language semantics.

This new type could alternatively be introduced with a different name, such as `unicode` as in Python 2,
while keeping the alias of `string` for `seq<char>`.
This would only increase the confusion and cognitive burden for Dafny users in the future, though.

## Add a new, distinct `rune` type

We could maintain the current definition of the `char` type, and introduce a new `rune` type to represent Unicode scalar values
instead ("rune" being the term both Go and C# use for this).
This would make it more obvious when reading Dafny source code in isolation whether it was using the new definitions of strings.
There are often few explicit references to individual character values in code that references string values, however,
and even when the `char` type is used it is often only implicitly referenced because of type inference.
This alternative does not seem to be worth the implementation cost or additional cognitive load on users,
especially since it is hard to imagine any codebase needing to use both `char` and `rune` together.

## Disallow compilation of string indexing

Given popular Unicode encodings such as UTF-8 and UTF-16 do not support random access of characters,
we could decide to forbid random access of string elements (e.g. `s[i]`) in compiled code,
instead directing users to fallback to external code for efficient access,
or to sequential access via the new [ordered quantification features](https://github.com/dafny-lang/rfcs/pull/10) (once they are implemented).
This would be a much more disruptive breaking change for existing code, however.
String indexing would not be the first instance in Dafny of a simple, mathematical expression
that supports verification easily but is inefficient at runtime.
The proposed lazy decoding approach should provide a good balance between the clean expression of concepts
and efficient, unsurprising runtime behavior.

## Change `char` to mean an extended grapheme cluster

Rather than just augmenting `char` to represent the more abstract Unicode scalar value concept,
we could push further and define it to mean an [*extended grapheme cluster*](https://unicode.org/reports/tr29/#Grapheme_Cluster_Boundaries),
which is the Unicode concept closest to what humans perceive visually as a distinct, atomic "character".
This would make operations on strings as sequences of values correspond more closely to meaningful concepts on text,
such as `|s|` actually providing a "character count" that aligns with expectations in a word processor.

Although there are definite benefits to this approach for logic that heavily processes text
(and is the approach that the [Swift](#swift) language takes, for example),
the definition of how scalar values are grouped into grapheme clusters
is much more complicated and locale-specific than the simple mathematical rules of common encodings
like UTF-8 and UTF-16. This means a higher cost and risk of bugs in adding these concepts
to the core definition of Dafny, and a much higher likelihood of having to change
the language definition or implementation to support future versions of Unicode.
It would also mean `char` can no longer be represented as a single integer value,
instead needing multiple scalar values in some cases,
which would be a large a deep change to the encoding of `char` in the Boogie prelude and translator.

# Prior art
[prior-art]: #prior-art

Unicode has a long and messy history, and the approach to supporting Unicode varies dramatically across different programming languages.
Here is the current state of several popular programming languages, especially those that Dafny currently supports compiling to,
or could in the future:

## C#:

`char` is an alias for the `System.Char` value type, which represents a single character as a UTF-16 code unit. 
`string` is an alias for the `System.String` class, which represents an immutable sequence of `char` values.
The `System.Text.Rune` struct is provided to represent any Unicode scalar value,
and its API guarantees that invalid values (e.g. surrogates) will be rejected on construction.
The method `String.EnumerateRunes()` produces the sequence of runes in a string via an `IEnumerator<Rune>`.

## Java:

`char` is one of the eight primitive types in Java, and also represents a UTF-16 code unit.
In recent versions of the Java Runtime Environment, the `java.lang.String` class supports
encoding its data either in UTF-16 or in Latin-1, where the latter is an optimization for space
when all characters in the string are supported by this encoding. 

Java does not included a dedicated type for Unicode scalar values
and instead uses the 32-bit wide `int` primitive type.

## Go:

In Go a string is a read-only slice of bytes, which generally contains UTF-8 encoded bytes
but may contain arbitrary bytes. The `rune` type is an alias for `int32`.

## JavaScript:

The JavaScript `String` type represents an immutable sequence of UTF-16 code units as integer values.
There is no distinct type for representing individual characters.

## C++:

The `char` type represents bytes, and the `std::string` class from the standard library
operates on bytes as character, and generally does not produce correct results if used
together with any encoding other than single-byte encodings such as ASCII.
C++11 added two new character types, `char16_t` and `char32_t`, 
and two new corresponding `std::u16string` and `std::u32string` collection classes.
It also provides three new kinds of string literals,
`u8"..."`, `u"..."`, and `U"..."`,
which produce binary values encoded with UTF-8, UTF-16, and UTF-32 respectively.

## Python:

In Python 2, the `str` type was used for both binary and text data.
A separate `unicode` type was introduced to store textual data,
and a separate mode for unicode string literals (`u"..."`).
Python 3 changed `str` to be this `unicode` datatype instead.
Like JavaScript, Python has no dedicated character type,
and just uses the unbounded `int` type for Unicode scalar values.

## Rust:

The `char` type directly represents any Unicode scalar value, and rejects out-of-range values.
The "string slice" type `str` is the most primitive string type,
which is guaranteed to refers to valid UTF-8 data.
It primarily acts as a sequence of bytes, but directly provides many methods that work with `char` values:
`chars()` provides an iterator of `char` values,
`get(<slice>)` returns a subslice but produces `None` if the bounds do not align with UTF-8 sequence boundaries,
etc.

## Swift:

Swift defines `String` as a collection of characters,
and unusually defines `Character` as an [*extended grapheme cluster*](https://unicode.org/reports/tr29/#Grapheme_Cluster_Boundaries),
which is the closest concept to an atomic characeter as perceived visually by users.
Unicode scalar values are represented with a distinct `Unicode.Scalar` structure instead.
`String` provides `utf8`, `utf16`, and `unicodeScalars` views
that present the contents as sequences of UTF-8, UTF-16, and UTF-32 code units respectively.

# Unresolved questions
[unresolved-questions]: #unresolved-questions

Is there anything more we can do to make migration easier and safer for users?
Chance are very good that all Dafny code in existence to date either will not change behavior
across this change, or will slightly improve because of the improved handling of surrogate code points.
I have been unable to think of anything that would provide more value than the verifier will already provide,
but I am open to suggestion as always!

# Future possibilities

## `EncodedString` type

It may be a good idea for a shared Dafny source library to define a `EncodedString` wrapper
around encoded bytes that includes a ghost `string` value defining the actual abstract string encoded.
This could make the [existing implementations of UTF-8 and UTF-16 encodings](https://github.com/dafny-lang/libraries/tree/master/src/Unicode)
more efficient and pleasant to use.