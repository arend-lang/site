---
layout: single
title: Download
toc: true
toc_label: Download
toc_sticky: true
---

You need to have JRE 8 installed on your computer to use Arend.
Arend is available either as an [IntelliJ IDEA plugin](#intellij-idea-plugin) or as a [console application](#console-application).

## IntelliJ IDEA Plugin

To install the IntelliJ IDEA plugin, follow the instructions below.

* Download (either community or ultimate version of) [IntelliJ IDEA](https://www.jetbrains.com/idea).
* Run Intellij IDEA, choose either **Configure \| Plugins** if you are on a _Welcome screen_ or **File \| Settings** from the main menu if a project is open, go to **Plugins** tab, search for _Arend_ plugin and install it, restart Intellij IDEA.
* Another way to get the latest version of the plugin is by following instructions on [this page](https://github.com/JetBrains/intellij-arend/blob/dev/README.md).

You can read more about IntelliJ IDEA [here](https://www.jetbrains.com/help/idea/discover-intellij-idea.html).
To create an Arend project, follow instructions [here](https://arend.readthedocs.io/en/latest/getting-started/#intellij-idea-plugin).

## Console Application

To install the console application, follow the instructions below.

* Download the arend [jar file](http://valis.github.io/arend.jar).
  You can also get the latest version of the plugin by following instructions on [this page](https://github.com/JetBrains/arend/blob/master/README.md).
* Run `java -jar arend.jar` to check that everything is alright. You should see the following output:
  <pre><code class="bash">$ java -jar arend.jar
  [INFO] Loading library prelude
  [INFO] Loaded library prelude
  Nothing to load
  </code></pre>
To see command line options, run `java -jar arend.jar --help`.

To create an Arend project, follow instructions [here](https://arend.readthedocs.io/en/latest/getting-started/#console-application).

## Standard Library

The standard library contains a number of essential definitions and proofs, in particular,
in constructive algebra and homotopy theory. It can be downloaded from [here](https://github.com/JetBrains/arend-lib).
