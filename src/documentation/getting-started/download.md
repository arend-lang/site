---
layout: single
title: Downloading Arend
nav: download
toc: true
toc_label: Downloading Arend
---

You need to have [JDK] of version no less than 17 installed on your computer to use Arend.
You are free to choose any alternative JDK distributions such as the [Liberica JDK],
as long as the version fits the requirement.

 [JDK]: https://www.oracle.com/java/technologies/javase/jdk17-archive-downloads.html
 [Liberica JDK]: https://bell-sw.com/pages/downloads/#jdk-17-lts

Arend is available either as an [IntelliJ IDEA plugin](#intellij-idea-plugin) or as a [console application](#console-application).

## IntelliJ Arend

IntelliJ Arend is a plugin for IntelliJ IDEA.
To install it, follow the instructions below.

* Download (either community or ultimate version of) [IntelliJ IDEA](https://www.jetbrains.com/idea).
* Run Intellij IDEA, choose either **Configure \| Plugins** if you are on a _Welcome screen_ or **File \| Settings** from the main menu if a project is open, go to **Plugins** tab, search for _Arend_ plugin and install it, restart Intellij IDEA.
* Another way to get the latest version of the plugin is by following instructions on [GitHub](https://github.com/JetBrains/intellij-arend/blob/master/README.md).

You can read more about IntelliJ IDEA [here](https://www.jetbrains.com/help/idea/discover-intellij-idea.html).
To create an Arend project, follow instructions [here](/documentation/getting-started/started).

## Console Application

To install the console application, follow the instructions below.

* Download the Arend [jar file](https://github.com/JetBrains/Arend/releases/latest/download/Arend.jar).
  You can also get the latest version of the application by following instructions on [GitHub](https://github.com/JetBrains/Arend/blob/master/README.md).
* Run `java -jar Arend.jar` to check that everything is alright. You should see an output similar to the following:

```
$ java -jar Arend.jar
[INFO] Loading library prelude
[INFO] Loaded library prelude (233ms)
Nothing to load
```

To see command line options, run `java -jar Arend.jar --help`.

To create an Arend project, follow instructions [here](/documentation/getting-started/started).

## Standard Library

The standard library `arend-lib` contains a number of essential definitions and proofs, in particular, in constructive algebra and homotopy theory.
It can be downloaded from [GitHub](https://github.com/JetBrains/arend-lib/releases/latest/download/arend-lib.zip) 
The downloaded file should be put in the `libs` directory in which all Arend libraries are stored (by default, this is `$HOME/.arend/libs`, where `$HOME` is the home folder.

If you are using the IntelliJ plugin `arend-lib` will be downloaded automatically by the IDE once you add `arend-lib` as a dependency library in the **Module Settings** window.

The path to `libs` can be specified either with command line option `-L` in the console application or in module settings in IntelliJ IDEA.
