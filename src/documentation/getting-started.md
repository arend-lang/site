---
title: Getting Started
---

You need to have [JRE 8](https://docs.oracle.com/javase/8/docs/technotes/guides/install/install_overview.html) installed on your computer to use Arend.
Arend is available either as an [IntelliJ IDEA](https://www.jetbrains.com/idea) plugin (see [IntelliJ Arend](#intellij-arend) for the installation instructions)
or as a console application (see [Console Application](#console-application) for the installation instructions).

# IntelliJ Arend

{% include intellij-arend.md %}

Let's create our first Arend project.

* Run Intellij IDEA and choose either **Create New Project** if you are on a _Welcome screen_ or **File \| New \| Project** from the main menu if a project is open.
* Choose **Arend** in the list on the left. If you want to use external libraries, for example, the standard library, 
you can set up the path to a directory with
these libraries in the panel on the right. In order to do this, click **+** button in the top left corner of the panel, select
**Arend libraries** and choose a path in the dialog.
* Click **Next**. In the successive steps set up the name of the project, directories for sources and binaries and click **Finish**. 
 
You should get a new project which contains (among other files) a file `arend.yaml` and an empty source directory 
(`src` by default).
The yaml file contains a description of the project.
You can read more about this configuration file [here](libraries).

If you want to use the standard library, you should add it to the list of dependencies in **File \| Project Structure**.
In case you did not specify the path to Arend external libraries on creation of the project, you should do it in Project SDK
section of **File \| Project Structure \| Project**.  Once this is done, click **+** button on the right of the panel
**File \| Project Structure \| Modules**, select **Library \| Arend library** and choose the libraries to be added as 
dependencies.

Create a new file `example.ard` in the source directory.
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

# Console Application

{% include console-application.md %}

Let's create our first Arend project.
Create a directory for your project:

{% arend %}
$ mkdir testProject
$ cd testProject
{% endarend %}

Create file `arend.yaml` inside this directory.
This file contains the description of your project.
Minimally, we just need to specify the location of source files of your project.
Add the following line to `arend.yaml`:
```
sourcesDir: src
```

Create directory `src` which will contain source files for this project.
Create a file `example.ard` inside `src` with the following content:

{% arend %}
\func f => 0
{% endarend %}

Run `java -jar $arend -L$libs $myProject`, where `$arend` is the path to `arend.jar`, `$myProject` is the path to `arend.yaml`,
and `$libs` is the path to the directory with Arend libraries (if the project does not have dependencies, this option can be omitted).
You should see the following output:
```
[INFO] Loading library prelude
[INFO] Loaded library prelude
[INFO] Loading library myProject
[INFO] Loaded library myProject
--- Typechecking myProject ---
[ ] example
--- Done ---
```

This means that module `example` was successfully typechecked.
Modify file `example.ard` as follows:

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
[ERROR] example:1:25: Type mismatch
  Expected type: Nat -> Nat
    Actual type: Nat
  In: 0
  While processing: f
[✗] example
Number of modules with errors: 1
--- Done ---
```

To learn more about Arend, see the [language reference](language-reference).

# Standard Library

In case you would also like to use the standard library, download it as described [here](/download#standard-library) and add the following line to `arend.yaml`:
```
dependencies: [arend-lib]
```
You can read more about this configuration file [here](libraries).
