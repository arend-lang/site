---
title: Arend Libraries
---
An **Arend library** is a collection of Arend files and Java code organized in a directory structure to support modular development and reuse.
Libraries are the fundamental building blocks of the Arend ecosystem, allowing developers to organize their code, manage dependencies, and distribute libraries or projects.
The Arend standard library, [**arend-lib**](/arend-lib) is the primary library of the Arend ecosystem covering constructive mathematics, homotopy type theory and computer science.

## Structure and Components
An Arend library typically consists of multiple `.ard` files (Arend source files) and optionally `.arc` files (compiled binaries produced by the Arend type checker).
These files are organized into a directory structure with the following key components:

- **Root Directory**: Contains the mandatory `arend.yaml` header file, which serves as the library's manifest and configuration file.
- **Source Directory** (`src`): Houses `.ard` files.
- **Binaries Directory** (`bin`): Houses `.arc` files.
- **Extensions Directory** (`ext`): Optionally contains auxiliary Java classes for metas. Metas are the Arend equivalent of tactics in Coq or Lean. The mechanism of language extensions allows any Arend library to define its own metas.
- **Tests Directory** (`test`): Optionally contains tests for metas introduced by the library.

## Manifest YAML file
The `arend.yaml` file provides essential information about the library:
- **Language Version**: Defined using `langVersion: VERSION`, where `VERSION` specifies a particular version or range (e.g., `>= VERSION`, `<= VERSION`, or `>= VERSION_1, <= VERSION_2`).
- **Library Version**: Defined using `version: VERSION`.
- **Content Paths**:
  - `sourcesDir: PATH` for source files.
  - `binariesDir: PATH` for binary files.
  - `extensionsDir: PATH`: for library extensions (optional).
  - `testsDir: PATH` for test files (optional).

  Paths can be relative to the root directory or absolute.
- **Extension main class** (optional): Defined using `extensionMainClass: CLASS_PATH`, where `CLASS_PATH` is a Java class path pointing to the extension's main class implementing the `org.arend.ext.ArendExtension` interface.
- **Dependencies**: Listed as `dependencies: [NAME_1, ..., NAME_k]`, where `NAME_1, ..., NAME_k` are the names of libraries that the library depends on.
Notice that while Arend files within a single Arend library can depend on each other, circular dependencies between different Arend libraries are *not* allowed.

## Intellij IDEA modules
To work with Arend in Intellij IDEA, you must open or create a project containing at least one Arend library.
The Arend plugin introduces a specialized module type which corresponds precisely to an Arend library, adding the option **Arend** into the **New Module** and **Import Module** standard dialogs of Intellij IDEA.
The plugin ensures consistency by synchronizing the contents of the `arend.yaml` file with the information stored in the IntelliJ IDEA module settings.
![Arend module settings pane](/assets/images/ArendModuleSettings.png)

## Console Application
Arend libraries can also be built and typechecked using the console version of Arend, independent of IntelliJ IDEA.
To be able to use multiple Arend libraries from the console, you must put them into a single directory.
You then need to specify this directory via: `-L` command-line option in the console Arend application.
