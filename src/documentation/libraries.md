---
title: Libraries
toc: false
---

A set of Arend source files .ard and/or binary files .arc (compiled .ard files) can be arranged into an _Arend library_.
A library can be created by creating its header file named arend.yaml in the root directory of the library. The name of 
a library is simply the name of the library's root directory, that is the parent directory of its header file. All other
information about a library is contained inside the header file and may include or not the following:

* Language version can be specified by writing `langVersion: VERSION`, where `VERSION` is either a specific version of the language or a range,
which is written as either `>= VERSION`, `<= VERSION`, or `>= VERSION_1, <= VERSION_2`.

* Directories with library's source and binary files. It can be specified by writing `sourcesDir: PATH` and 
`binariesDir: PATH` for sources and binaries respectively, where `PATH` is either
a path relative to the library's root directory or an absolute path.

* The list of names of libraries this library depends on. The list of library's dependencies can be specified by writing
`dependencies: [NAME_1, ..., NAME_k]`, where `NAME_1`, ... `NAME_k` are names of the libraries. 

All libraries should be put in some specific directory.
The path to this directory can be specified either with command line option `-L` in the console application or in module settings in IntelliJ IDEA.
