---
title: Features overview
---

In this section we provide an overview of key features of Arend and Arend plugin for Intellij IDEA.
We briefly discuss peculiarities of Arend scoping rules, the mechanism of dependency analysis and incremental type checking implemented in the Arend plugin.

For the overview of the features of Arend language itself the reader is referred to [here](/about/arend-features).

# Scoping
Arend files can depend on other Arend files, and Arend also allows circular dependencies within a single Arend library (aka Intellij IDEA module of type “Arend”). 
Furthermore, the scope of any Arend definition or theorem is not restricted to the text that follows it, but rather extends throughout the entire enclosing scope. 
For instance, the scope of a top-level definition spans the entire Arend file to which it belongs. This behavior is similar to the scoping mechanisms found in many general-purpose programming languages and contrasts with typical proof assistants like Coq or Mizar. 
On the positive side, this approach simplifies import management and code migration for the user. 

On the negative side, it creates a need for Arend’s type checker to track dependencies between individual definitions across different files and to handle potential circular dependencies between them, as these can result in inconsistent theory. 
In Arend, circular dependencies are only allowed between recursively defined functions, and even then, only if the termination checker can detect that parameters of recursive function calls become “smaller” from one call to another call. 
The termination checker algorithm largely follows the one outlined in A. Abel’s master’s thesis [FOETUS](https://www.cse.chalmers.se/~abela/foetus.pdf).

# Dependency analysis
The mechanism of dependency analysis in Arend ensures that type checking is performed not on a per-file basis, but for each definition individually. The outcome of type checking is displayed in the editor using IntelliJ IDEA's Gutter Icons — a set of small icons positioned on the left side of the code. When a definition or theorem is fully correct and has no unresolved goals, this fact is indicated by a green "pass" gutter icon. If a definition or theorem contains syntax or type errors, a red "error" or yellow “warning” icon appears in the gutter. The latter happens when e.g. no type-checking errors are found, but a theorem still has an unresolved goal.

# Incremental type checking
![Short video showing the operation of the background type checker](/about//intellij-features/Typechecking.gif)
The dependency analysis mechanism enables another key feature in Arend: incremental type checking. When a user modifies one or more definitions, the type checker selectively discards cached information related to those definitions, as well as any other definitions that depend on them, either directly or through a chain of dependencies. This ensures that unaffected parts of the code are not reprocessed, significantly speeding up the type-checking process and helping to conserve laptop battery life.

Under normal circumstances the Arend plugin uses the so-called "on-the-fly" (or smart) mode of type checking. In this mode, the type checker operates in a background thread, automatically reprocessing each code modification made by the user. Running the type checker in the background prevents the IDE from freezing during the process. Since the type checking can be time-consuming and may involve extensive computations, a special mechanism halts the process if it exceeds the user-defined time limit (defaulted to 5 seconds). Additionally, there is an option to disable on-the-fly inspection entirely, switching the IDE into "dumb mode." In this mode, the IDE still resolves identifiers on the fly but does not automatically perform type checking which can still be manually run via IntelliJ IDEA’s standard mechanism of run configurations.
![Arend type checking settings pane](/assets/images/ArendTypecheckingMode.png)


# Functions, lemmas and goals
Like in any proof assistant, the process of formal verification of a mathematical fact in Arend involves formulating definitions and proving theorems about them. Mathematical statements in Arend are introduced using either the `\func` or `\lemma` keyword. The `\lemma` keyword does not mean “lemma” in the usual mathematical sense but rather indicates that the value of the marked definition is irrelevant (see e.g. proof irrelevance) and can be discarded after typechecking. Of course, only functions residing in the `Prop` universe, i. e. mere proposition in the sense of HoTT, can be marked as `\lemma`'s. Otherwise, the syntax of the `\func`- and `\lemma`-statements is identical. In practice this means that in Arend mathematical lemmas, propositions, theorems and corollaries are all rendered using keywords `\lemma` or `\func`.

Like any other definition in Arend, `\lemma` or `\func` can be defined using pattern matching (with the `\elim` or `\with` keywords) or by specifying a proof term after the `=>` symbol. If a proof is incomplete or omitted, the placeholder `{?}`, commonly called an "unresolved goal", can be used to indicate this. The term "goal" refers to a part of a statement that still needs to be verified or, in terms of the Propositions-as-Types correspondence, the type of the expression that the user still needs to construct.

In Arend, proof terms do not need to be fully detailed. Users can take advantage of the "inference of implicit arguments" mechanism, which allows them to omit some arguments in expressions (more concretely, the ones that can be inferred via the “inference of implicit arguments mechanism” built into the Arend type checker). Additionally, users can employ metas such as rewrite to construct particularly complicated parts of expressions. Metas should be seen as "expression-level tactics", meaning they can be seamlessly interwoven with standard Arend term constructs. In other words, unlike Coq, Arend does not have separate “proof” and “term” levels – everything (including proofs) in Arend happens on the “term” level.

