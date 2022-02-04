---
title: Getting Started
---

{% include jre-requirement.md %}

Arend is available either as an [IntelliJ IDEA](https://www.jetbrains.com/idea) plugin (see [IntelliJ Arend](#intellij-arend) for the installation instructions)
or as a console application (see [Console Application](#console-application) for the installation instructions).


# IntelliJ Arend

{% include intellij-arend.md %}

Let's create our first Arend project.

* Run Intellij IDEA and choose either **Create New Project** if you are on a _Welcome screen_ or **File \| New \| Project** from the main menu if a project is open.
* Choose **Arend** in the list on the left. If you want to use external libraries, for example, the standard library,
you can set up the path to a directory with these libraries in the field **Path to libraries**.
Available libraries will be displayed in the list on the right.
To add them to the project, move them to the left list.
The standard library **arend-lib** is always available; it will be downloaded if the file is missing.
* Click **Next**. In the successive step set up the name of the project and the path to it and click **Finish**.

You should get a new project which contains (among other files) a file `arend.yaml` and an empty source directory
(`src` by default).
The yaml file contains a description of the project.
You can read more about this configuration file [here](libraries).

Now, let us write some code.
Create a new file `Example.ard` in the source directory.
Add the following line to this file:

{% arend %}
\func f => 0
{% endarend %}

You should see a green gutter icon next to the declaration of `f`, which indicates that `f` was successfully typechecked.
Modify the file as follows:

{% arend %}
\func f : Nat -> Nat => 0
{% endarend %}

The gutter icon should become red.
To go to the next error, press **F2**.
You should see the following error message:

{% arend %}
Type mismatch
  Expected type: Nat -> Nat
    Actual type: Nat
{% endarend %}

You can read more about IntelliJ IDEA [here](https://www.jetbrains.com/help/idea/discover-intellij-idea.html).
To learn more about Arend, see the [language reference](language-reference).
Also, check out the tutorial on [interactive theorem proving with IntelliJ Arend](intellij-arend-tutorial).

# Console Application

{% include console-application.md %}

Let's create our first Arend project.
Create a directory for your project:

```shell
$ mkdir testProject
$ cd testProject
```

Create file `arend.yaml` inside this directory.
This file contains the description of your project.
Minimally, we just need to specify the location of source files of your project.
Add the following line to `arend.yaml`:
```yaml
sourcesDir: src
```

Create directory `src` which will contain source files for this project.
Create a file `Example.ard` inside `src` with the following content:

{% arend %}
\func f => 0
{% endarend %}

Run `java -jar $arend $myProject`, where `$arend` is the path to `arend.jar`, `$myProject` is the path to `arend.yaml` or the directory containing it,
and you can optionally pass `-L$libs` where `$libs` is the path to the directory with Arend libraries (if the project does not have dependencies, this option can be omitted).
When `$myProject` equals `.`, it can be omitted.
You should see the following output:
```
[INFO] Loading library prelude
[INFO] Loaded library prelude
[INFO] Loading library myProject
[INFO] Loaded library myProject
--- Typechecking myProject ---
[ ] Example
--- Done ---
```

This means that module `Example` was successfully typechecked.
Modify file `Example.ard` as follows:

{% arend %}
\func f : Nat -> Nat => 0
{% endarend %}

If you run `java -jar $arend $myProject` again, it should produce the following error message:

```
[INFO] Loading library prelude
[INFO] Loaded library prelude
[INFO] Loading library myProject
[INFO] Loaded library myProject
--- Typechecking myProject ---
[ERROR] Example:1:25: Type mismatch
  Expected type: Nat -> Nat
    Actual type: Nat
  In: 0
  While processing: f
[✗] Example
Number of modules with errors: 1
--- Done ---
```

To learn more about Arend, see the [language reference](language-reference).

# Standard Library

In case you would also like to use the standard library, download it as described [here](/download#standard-library) (if you are using the IntelliJ plugin, it can be downloaded from the IDE) and add the following line to `arend.yaml`:
```
dependencies: [arend-lib]
```
You can read more about this configuration file [here](libraries).
