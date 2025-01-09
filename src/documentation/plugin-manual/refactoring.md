---
title: Refactoring Arend projects
---

# Code formatting
![Short video illustrating Reformat Code feature](/about//intellij-features/CodeFormatter.gif){: style="display: block; margin: 0 auto;" }
Pressing **Ctrl+Alt+L** (or **⌘⌥L**) will format the selected Arend file (or a selected piece of code) according to Arend's text formatting conventions, just as it would for Java or Kotlin files.

# Optimize Imports
![Short video illustrating Unused Imports feature](/about/intellij-features/UnusedImports.gif){: style="display: block; margin: 0 auto;" }
Similar to other languages supported by IntelliJ IDEA, the Arend plugin provides a tool to analyze import headers in each file for potentially superfluous import directives.
 These unnecessary directives are highlighted in gray and can be removed using the corresponding intention action. To use this feature:
 - Place the caret on the highlighted (superfluous) import directive.
 - Press **Alt+Enter** (or **⌥Enter** on macOS) to trigger the action and remove it.
The tool requires the type checker to be in Smart mode to produce fully accurate results. 
This limitation exists because, in Arend, an `\import` directive might still be necessary even if there are no explicit references to the contents of the imported file. 
For example, a file may export a class instance implicitly used via the implicit-instance mechanism.
To avoid false positives, the tool will not mark `\import` directives as superfluous in **Dumb** mode if they refer to files containing `\instance` declarations.

# Rename refactoring
The Rename feature in IntelliJ IDEA allows the user to change the name of variables, classes, functions, data types, or other identifiers across the Arend project. 
This ensures consistency and prevents manual errors. The feature can be invoked using **Shift+F6** (or **⇧F6** on MacOS). 
When the user renames a symbol, IntelliJ automatically updates all references, comments, and related files.

# Change Signature refactoring
![Short video showing the operation of Change Signature feature](/about/intellij-features/ChangeSignature.gif){: style="display: block; margin: 0 auto;" }
The Arend plugin supports the Change Signature refactoring feature of IntelliJ IDEA, providing a tool for modifying function or theorem signatures while preserving the correctness of call expressions and types throughout the entire Arend codebase. 
This feature can be activated by pressing **Ctrl+F6** (or **⌘F6** on macOS) when the caret is positioned on the header of the definition whose signature is to be changed.
Parameters of the definition are displayed in a table format with three columns: **Name**, **Type**, and **Explicitness**. 

Users can add, remove, reorder, and rename parameters, as well as toggle their explicitness (i.e. switch between explicit and implicit). 
Changes to a parameter's name are automatically updated in all references to that parameter within the table.
Clicking the **Refactor** button applies these changes across the codebase, ensuring that type dependencies—such as variables referenced in the types of other parameters—are accurately adjusted. For example, renaming a parameter used in a type declaration automatically updates all type definitions that reference it.

## Current limitations
The **Change Signature** refactoring, like the **Parameter Hints** feature, aims to handle dynamically inferred implicit parameters in definitions’ signatures. 
For accurate results, it is recommended to use this refactoring only when the target definition and its surrounding definitions are fully type-checked. 
Without full type-checking, the tool may fail to correctly infer the definition's signature.

A known limitation occurs when the refactoring processes a function call that ends with an implicit tail argument. 
At the syntactic level (without type-checking), the tool cannot distinguish between the following two cases:
Passing a function `f` as an argument to another function (e.g., `g f`).
Invoking f with an implicit parameter, inferred by the type checker, then passing the result to another function (e.g., `g f`, but actually `g (f {_})`).
These two cases require different handling by the refactoring tool:
- Case 1: The refactoring should generate `g (\lam {x} => f x)`.
- Case 2: The output should be `g (f _)`.

To properly handle such an ambiguity, the tool would need to perform type-checking on every syntactically ambiguous expression with implicit tail arguments. 
However, this feature is currently not implemented due to performance limitations. 
As a result, the tool processes all tail implicit arguments as in Case 1, which may produce erroneous code requiring manual correction.


# Move Refactoring
![Short video showing the operation of Move Refactoring feature](/about//intellij-features/MoveRefactoring.gif){: style="display: block; margin: 0 auto;" }
The Arend plugin implements IntelliJ IDEA’s Move Refactoring feature, enabling the user to reorganize code by moving classes, functions, data types, or fields to a new location within the same file or to a different Arend file. 
This operation automatically updates all references and corrects file imports.
To use the feature, the user must place the cursor on the definition to be moved and press **F6** (or **⌃T**, followed by **6** on macOS). A dialog window will appear, allowing the user to specify the new destination, including the target Arend file and the fully qualified name of the target namespace. 
If the selected namespace is an Arend class, the user can choose whether to place the definition in the “static” namespace (the class’s `\where` block) or the “dynamic” namespace (the main class body where all members implicitly have a `\this` parameter).
Multiple definitions can be moved simultaneously. In this case, the dialog provides a list of definitions located within the same namespace, and the user can select items to be moved by checking their corresponding boxes.
The refactoring process ensures safety by highlighting potential name conflicts and offering suggestions to resolve them before finalizing the operation.

