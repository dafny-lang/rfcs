- Feature Name: Library support
- Start Date: 2021-08-05
<!-- - RFC PR: [dafny-lang/rfcs#0000](https://github.com/dafny-lang/rfcs/pull/0000) -->
<!-- - Dafny Issue: [dafny-lang/dafny#0000](https://github.com/dafny-lang/dafny/issues/0000) -->

# Summary
[summary]: #summary

Compiled programming languages typically allow programs to reference and use code that is already compiled. The benefit of this is that it makes the compilation process faster: referenced compilation artefacts don’t need to be recompiled from source. Enabling programs to grow the amount of source code they depend on, without increasing their build time, is required to let programs scale to large sizes.

With Dafny, it’s currently already possible to grow the code base of a program without significantly increasing its build time, but there are several problems with how this works. In this RFC, we identify those problems and suggest a solution.

# Motivation
[motivation]: #motivation

The goal of this RFC is to allow Dafny programs to reference already built Dafny code without increasing their build time, and without requiring any work from the programmer such as adding include directives to the source code.

We define a Dafny *build* as invoking dafny to transform Dafny source files into source code in a target language, while ensuring that all Dafny source files have at some point been verified. Since verification can be slow, allowing Dafny programs to reference other Dafny sources and build without verifying those is important. 

Currently, it’s already possible to build a Dafny program but only verify part of that program. Dafny only verifies files that are directly passed to the CLI. Files that are only included by other files are not verified. Since most of the build time comes from verification, customers can use include directives to reference Dafny code without increasing the build time by much. Most if not all Dafny customers use this technique.

However, this method is not ideal because:

* Using include directives requires the programmer to do more work, particularly if lots of source files and source files in very different locations are involved. A contributor from CMU comments that they “want to do better than lots of include "../../../dafny-stdlib/stuff" ([ref](https://github.com/dafny-lang/dafny/issues/1236#issuecomment-883603131)).
* This method only skips the verification of the referenced code, while still requiring the other build steps such as parsing, resolution and compilation to a target language to be performed.

# Proposal
[guide-level-explanation]: #guide-level-explanation

To enable building large Dafny applications quickly, we add the `library` command line option to the Dafny CLI. This option takes a Dafny source file as an argument. An example call would be 
`dafny consumer.dfy /library:library.dfy`

The emitted compilation artefacts files of this call have the same semantics as when we would have called 
`dafny consumer.dfy library.dfy`, which would consider both `consumer.dfy` and `library.dfy` as regular Dafny source files.

However, the call that uses the `/library` option builds faster because:

* None of the proofs in `library.dfy` are verified
* Separate compilation artefacts are emitted for `library.dfy` and `consumer.dfy`, and when calling `dafny` again, those of `library.dfy` are not re-emitted unless `library.dfy` has changed, which saves the compiler work. This re-use of previous compilation artefacts can occur again in downstream compilation tasks.

Example:
```dafny
// Producer.dfy
module Export {
  const A := 1
}

// Consumer.dfy
module Foo {
  import Export
  const myA := Export.A
}

// Consumer2.dfy
module Bar {
  import Export
  const myA := Export.A + 1
}

// Files produced by running 
// dafny Consumer.dfy Consumer2.dfy /library:Producer.dfy \
//   /compileTarget:cs /out:output/cs
output/cs/Consumer.cs
output/cs/Consumer.csproj
 ^ references ./Producer.csproj
output/cs/Producer.cs
output/cs/Producer.csproj

// Files produced by running
// dotnet build output/cs/Consumer.csproj
output/cs/bin/Release/net5.0/Consumer.dll
output/cs/bin/Release/net5.0/Producer.dll
```

### Dafny compilation artefact caching
Running dafny will not emit build artefacts that already exist and are up-to-date. In the above example, if the file `Consumer.dfy` is changed and the command `dafny Consumer.dfy /artifact:Producer.lib.dfy compileTarget:cs /out:output/cs` is run again, then `Producer.cs` and `Producer.csproj` are not emitted since they already exist. 

### Downstream compilation artefact caching
`dafny` produces source files in a target language, that in the case of a compiled target language such as C#, still need to be compiled further before they can be executed. By not recreating target language source files, Dafny improves the chance that target language build tools, `dotnet` in the above example, will skip rebuilding those files, since those tools may depend on file modification timestamps. 
<!-- Check whether this is the case for dotnet -->

In the above example, modifying the file `Consumer.dfy` and then running both dafny and dotnet, will not recreate the file `Producer.dll`.

## Producing a library

Suppose you have a Dafny project that consists of multiple .dfy files, and you want to vend this project as a library for other Dafny projects to consume, then what is the best way to do this?

To prevent the library author from having to think about this too much, we introduce a new compileTarget for dafny called `library`. Using this option will emit a single file to the output directory with a `.lib.dfy` extension, that is ready to be consumed by other Dafny projects by using the `/library` option. 

The .lib.dfy file may simply be a concatenation of all input source files, but it may also perform some source-to-source translation such as syntax desugaring and type inference. The .lib in the extension has no impact on dafny, but helps the programmer know where the file originated from and why it might not look like idiomatic Dafny.

A `.lib.dfy` file produced by `dafny /compileTarget:library` is still a valid .dfy file, and it can be used by future versions of dafny as long as those versions did not introduce backwards incompatible changes to the language.

Example:

```dafny
// Producer.dfy
module Export {
  const A := 1
}

// Producer2.dfy
module AnotherExport {
  const A := 1
}

// Files produced by running 
// dafny Producer.dfy Producer2.dfy /compileTarget:library /out:output/lib
output/lib/Producer.lib.dfy
```

## Libraries using libraries

When Dafny projects that are used as libraries, are also consuming other libraries, they specify both a `/library` and a `/compileTarget:library` option, in which case Dafny will copy any input libraries to the output directory.

Example:
```dafny
// Files produced by running
// dafny src/source.dfy /library:libs/math.lib.dfy /compileTarget:library /out:output/lib
output/lib/source.lib.dfy
output/lib/math.lib.dfy
 ^ copied from libs/math.lib.dfy

To distribute the src/source.dfy library to other projects, all files in the output/lib folder must be shared. To make it easier to consume the multiple libraries files, the `/library` option can also take a directory as an argument, in which case it will look for all .lib.dfy files directly in this directory and consume them as if they were passed as separate /library options.
```

# Implementation
[reference-level-explanation]: #reference-level-explanation

To let Dafny determine which files need to be re-emitting, it can either compare the timestamps of previously emitted files with the timestamps of input files, or it can store a unique hash of the used input files in the emitted file, and read that on a next run to determine whether the file is outdated or not.

<!-- This is the technical portion of the RFC. Explain the design in sufficient detail that:

- Its interaction with other features is clear.
- It is reasonably clear how the feature would be implemented.
- Corner cases are dissected by example.

The section should return to the examples given in the previous section, and explain more fully how the detailed proposal makes those examples work. -->

<!-- # Drawbacks
[drawbacks]: #drawbacks

Why should we *not* do this? -->

# Rationale and alternatives
[rationale-and-alternatives]: #rationale-and-alternatives

Alternatives would be:
- Instead of introducing a new command line option, let the Dafny CLI use the extension of a file to determine whether to treat it as a library or a source file.
- Use a different name for the `/library` option and `/compileTarget:library`, such as `dependency` or `package`.
- Let `dafny` reject any files passed to `/library` that do not end in a `.lib.dfy` extension, to make it less likely that unverified files are accidentally passed as a library.
  
<!-- - Why is this design the best in the space of possible designs?
- What other designs have been considered and what is the rationale for not choosing them?
- What is the impact of not doing this? -->

# Prior art
[prior-art]: #prior-art

The Java compiler `javac` has a classpath option that enables passing `.jar` files which contain compiled Java code.

The .NET build tool `dotnet`, which can consume `.csproj` files to build C# projects, allows referencing a compiled C# program, a `.dll` file, with the following syntax:

```
<ItemGroup>
  <Reference Include="MyAssembly">
    <HintPath>path\to\MyAssembly.dll</HintPath>
  </Reference>
</ItemGroup>
```

`GCC` uses the extension of input files to determine what operations need to be performed ([link](https://gcc.gnu.org/onlinedocs/gcc/Overall-Options.html#Overall-Options)).

<!-- Discuss prior art, both the good and the bad, in relation to this proposal.
A few examples of what this can include are:

- For language, library, tools, and compiler proposals: Does this feature exist in other programming languages and what experience have their community had?
- For community proposals: Is this done by some other community and what were their experiences with it?
- For other teams: What lessons can we learn from what other communities have done here?
- Papers: Are there any published papers or great posts that discuss this? If you have some relevant papers to refer to, this can serve as a more detailed theoretical background.

This section is intended to encourage you as an author to think about the lessons from other languages, provide readers of your RFC with a fuller picture.
If there is no prior art, that is fine - your ideas are interesting to us whether they are brand new or if it is an adaptation from other languages.

Note that while precedent set by other languages is some motivation, it does not on its own motivate an RFC. -->

# Unresolved questions
[unresolved-questions]: #unresolved-questions

Out of scope for this RFC are:
- Support distributing Dafny libraries
- Enable verifying large Dafny program with optimal concurrency, without requiring make files or include directives.

<!-- What parts of the design do you expect to resolve through the RFC process before this gets merged?
- What parts of the design do you expect to resolve through the implementation of this feature before stabilization?
- What related issues do you consider out of scope for this RFC that could be addressed in the future independently of the solution that comes out of this RFC? -->

# Future possibilities
[future-possibilities]: #future-possibilities

## Library distribution
Dafny will enable publishing and fetching libraries to and from a Dafny library registry.

## Smarter handling of downstream compilation artefacts
Dafny will have some understanding of downstream compilation artefacts such as .NET’s .dll files. We’ll update the `/library` option so that downstream compilation artefacts can be passed in, in addition to the Dafny library file. This allows Dafny to skip producing target language source files for the library and instead reference the library’s downstream compilation artefacts directly. 

Example:
```
// Files produced by running 
// dafny Consumer.dfy Consumer2.dfy /library:Producer.dfy:Producer.dll \
//   /compileTarget:cs /out:output/cs
output/cs/Consumer.cs
output/cs/Consumer.csproj
 ^ references Producer.dll as a dependency
```

## Secure & fast library usage through solver proofs
Some customers may want to guarantee that a library they’re using was verified at some point, but still prefer not to verify this library themselves. We may we able to let the Dafny solver back-end, given a verification condition, emit a proof that can be used to quickly verify the verification condition again. The proof can be distributed together with the library to allow customer to quickly verify the library.

## Dafny library format
In the future we could consider changing the format of Dafny library files that are emitted by `/compileTarget:library` and consumed by `/library:<file>`, to be something other than a single large Dafny file. An option would be to have two files:

* An intermediate language in the verification pipeline of Dafny, possibly still valid Dafny but with only ghost code and only the ghost code that can be imported. This file would be used in the resolution and verification steps of the consuming library.
* An intermediate language in the compilation pipeline of Dafny where there no longer is any ghost code. This file would be used to compile the library to new target languages.


