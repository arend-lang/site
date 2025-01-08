---
title: Editor features of Arend plugin
---
When the user opens an Arend file located within a correctly configured Arend module the Arend type checker along with other IDE visual components become accessible. The user can run the Arend type checker, use various information assistants and helpers intended to refactor the code. The specific features provided by the Arend plugin are described in detail in the following sections.

# Code and usages highlighting
By default, the Arend IntelliJ IDEA plugin provides syntax highlighting for comments, built-in keywords, infix operators, string and number literals, as well as for the usages of metas and patterns in pattern-matching clauses. When the text cursor is placed on an identifier, all occurrences of that identifier in the current file are highlighted. If the identifier corresponds to a definition with an alias, all occurrences of the alias will also be highlighted.

# Collapsible code blocks
Arend plugin enables users to collapse and expand code blocks using gutter icons positioned next to each Arend namespace or definition. By clicking these icons or using the keyboard shortcuts **Ctrl + "+"** / **Ctrl + "-"** (or **⌘ + "+"** / **⌘ + "-"** on macOS), users can toggle the visibility of code blocks in an Arend file. These blocks correspond to the inner contents of Arend classes or the nested namespaces of definitions introduced with the `\where` keyword. Similar to the breadcrumbs bar, collapsible code blocks streamline navigation within an Arend file. Furthermore, all code blocks can be expanded or collapsed simultaneously using **Shift + Ctrl + "+"** / **Shift + Ctrl + "-"** (or **⇧⌘ + "+"** / **⇧⌘ + "-"** on macOS).

# Errors, warnings and weak warnings
To display errors in Arend files, a dedicated panel called the **Arend Messages View** is provided. This panel automatically appears after the type checker is run. 
It is divided into three sections: a list box which shows all errors found in the current file, the “Current Error” message window, and the “Latest goal” window, where the closest unresolved goal to the cursor is displayed.
In IntelliJ IDEA, there are three types of issues which are displayed in the **Arend Messages View** and simultaneously are indicated in Arend files using wavy underline highlighting beneath the affected code:
 - **Errors**. A red wavy underline indicates an error encountered during the processing of a definition. For example, syntax errors and type errors are marked with this highlighting.
 - **Warnings**. An orange wavy underline highlights a potential issue in the . For instance, unused variables or unresolved goals are marked with orange wavy lines.
 - **Weak Warnings**. An olive-colored wavy underline signifies a minor issue in the code, such as an expression unnecessarily surrounded by extra parentheses.
Hovering over the code with the wavy underline will display the error content in a pop-up panel. Placing the text cursor on a source line containing the wavy line will also display the full text of the error message in the “Current Error” section of the Arend Messages panel. Errors and warnings are also indicated by corresponding markings on the editor's scroll bar, located on the right-hand side of the file.

The total number of warnings and errors for the current file is also displayed in the top-right corner of the editor. The user can navigate between errors and warnings using keyboard shortcuts: **F2** / **Shift+F2** (or **F2** / **⇧F2** on MacOS) moves to the next (or previous) piece of code with an error or warning relative to the caret's current position.

# Unicode symbols in Arend code and the mechanism of aliases
![Short video illustrating the operation of the mechanism of aliases in Arend](/about/intellij-features/Aliases.gif){: style="display: block; margin: 0 auto;" }
To enhance code readability, Arend allows the use of Unicode characters from math operator ranges (`2200–22FF` and `2A00–2AFF`) in identifiers of global definitions, such as functions or theorems. However, there is no way to input a special symbol in IntelliJ IDEA without the help of external tools: the user must copy and paste the symbol from the OS-provided “Character Map” app or use another OS-provided mechanism of inputting Unicode characters. 

Arend plugin, however, offers a partial solution to the problem of typing special symbols through the mechanism of definition aliases. This mechanism allows the on-the-fly substitution of definition names as they are being typed in Intellij IDEA, so that the user needs to manually enter a Unicode symbol-containing name only once—when defining the alias. 

To use this mechanism for a definition called `defName`, the user needs to add `\alias` aliasName after the definition name. Consider, for example, the Arend’s analogue of exists tactics from Coq or Lean:
{% arend %}
\meta Exists \alias ∃
{% endarend %}


When the user types the prefix of definition having an alias (e.g. the prefix of the word `Exists`), the IDE will show an auto-completion menu  where the user could choose the item `defName`. If they do so or if the user presses **Ctrl+Space** (or **⌘Space** on MacOS), the IDE will automatically replace the entered prefix with `aliasName` (in this case with the symbol “∃”). 

# Quick documentation, markdown and LaTeX
![Short video illustrating the usage of Quick Documentation feature](/about//intellij-features/QuickDocumentation.gif){: style="display: block; margin: 0 auto;" }

When hovering over parts of Arend code in IntelliJ IDEA, the editor displays additional information in a popup panel. Specifically:
- Identifier Information: Hovering over an identifier triggers a quick documentation popup, showing the identifier's declared type, its documentation, and the file it was imported from. This popup can also be opened using the keyboard shortcut **Ctrl+Q** (or **F1** on MacOS) at the current caret position.
- Errors, Warnings, and Weak Warnings: Hovering over code underlined with a wavy line reveals the associated error, warning, or informational message.

Pressing **Ctrl+Q** (or **F1** on MacOS) while the quick documentation popup is open will expand it into a dockable panel in the IDE sidebar. This panel will then display the documentation for any identifier the user hovers over or places the caret on.

The documentation for a definition should be written as a line comment or a block comment directly before the definition it refers to. 
The comment should begin with a space followed by vertical bar symbol ‘|’ after the comment start, as shown in the example:

{% arend %}
-- | ``Meets x y`` is the type of elements which are meets of {x} and {y}.
\func Meets {E : Poset} (x y : E) =>
 \Sigma (j : E) (j <= x) (j <= y) (\Pi (z : E) -> z <= x -> z <= y -> z <= j)
{% endarend %}

A subset of Markdown tags is supported in documentation comments. As of version 1.10, the following tags are available:
- **Line breaks**: Inserted by ending a line with two spaces.
- **Italic and bold text**: Italics are created by surrounding text with `*`, and bold text with `**`.
- **External links**: Added using the format `[Link text]{https://link.site}`.
- **Headers**: Defined by placing multiple (at least 2) `=` or `-` symbols after the header text:
{% arend %}
Header1
==
Header2
--
{% endarend %}

- **Block quotes**: Created by adding `>` before the quoted text.
- **Multi-level** lists: Indented by two spaces for each nesting level. Each list item should start either with an item number of symbol `+` or `-`.
- **LaTeX Formulas**: The user can insert LaTeX formulas by enclosing the formula in `$...$` for inline formulas or `$$...$$` for centered, block-level formulas. 
This feature relies on the JLatexMath library (a fork of JMathTex), which supports a subset of LaTeX functionality similar to that provided by MathJax, used on sites like MathOverflow.

![Short video illustrating the usage of LaTeX in Quick Documentation](/about/intellij-features/LatexDoc.png){: style="display: block; margin: 0 auto;" }

## Current limitations

1. **Commutative Diagrams**: These are not supported at the moment.
2. **Upper Indices in Formulas**: LaTeX expressions with upper indices (e.g., `g^{-1}`) may not be processed correctly due to limitations in the Arend lexer. This issue arises because the lexer misinterprets the subexpression `{-` as the start of a block comment, since it supports nested block comments.
   * **Workaround**: Add a space after the opening brace, using `g^{ -1}` instead of `g^{-1}` to render the formula correctly.
3. **Formula Alignment in Quick Documentation**: The default Swing browser used by IntelliJ IDEA’s visual components does not support CSS formatting, which can lead to misaligned LaTeX formulas in quick documentation popups.
   * **Workaround**: To ensure correct alignment, click the "Open in the alternative browser" link in the popup. This opens the documentation in a more modern HTML browser where LaTeX formulas are displayed properly.


# Parameters Hints
![Short video illustrating the usage of Parameter Hints feature](/about//intellij-features/ParameterHints.gif){: style="display: block; margin: 0 auto;" }
Placing the cursor inside a data type or function call expression and pressing **Ctrl+P** (or **⌘P** on MacOS) activates the **Parameter Hints** feature. 
This displays a tooltip showing the function or datatype's signature, including expected parameters (both explicit and implicit) along with their types. 
The tooltip also highlights the parameter corresponding to the argument where the caret is positioned. 
Moving the caret to a different argument updates the highlighted parameter accordingly. 
When the caret is moved away from the call expression, the tooltip disappears.

The **Show Parameters** feature requires the target definition to be fully type-checked, as definitions in Arend may include dynamically inferred implicit parameters that are not explicitly listed in their signatures. 
However, a fallback mechanism is available: it tries to match the arguments of the selected expression to the parameters of the definition, even when the definition has not been type-checked 
 (e.g., when the typechecker is in **Dumb** mode). 
 In this case, the tooltip may display “???” in the positions where dynamically inferred implicit parameters might exist according to the language specification (even if no such parameters are actually present in the definition).

# Auto-completion
![Short video illustrating the operation of code completion](/about/intellij-features/CodeCompletion.gif){: style="display: block; margin: 0 auto;" }

Auto-completion is a feature that helps identify available identifiers in the current scope and to complete partially entered identifiers. 
Also, it imports definitions from scopes that have not yet been imported. 
The current scope is determined by the set of active imports, along with surrounding local and global declarations and variables. 
Auto-completion can always be triggered manually using the **Ctrl+Space** (or **⌘Space** on MacOS) keystroke.
IntelliJ IDEA will complete the selected identifier when **Enter** or **Tab** is pressed.

There are four types of auto-completion in Arend:
 - **Identifier completion**: When typing an identifier, IntelliJ IDEA displays all identifiers available in the current context that match the partially typed input. The search implemented by IntelliJ IDEA is fuzzy and supports "hump-back" matching: typing only the capital letters or key parts of a name will match the corresponding definition. For instance, typing `RC` or `id-i` will be sufficient for `RepresentationCategory` or `id-intertwining` to appear in the completion menu.
 - **Dot completion**: After typing a dot following a namespace identifier IntelliJ IDEA shows a list of identifiers and sub-namespaces within that namespace, allowing the user to insert them after the dot.
 - **Import completion**: After the `\import` keyword, triggered by **Ctrl+Space** (or **⌘Space** on MacOS) or typing the initial characters of an import statement, IntelliJ IDEA displays all Arend files whose names match the input. Selecting a file from the menu will insert its fully qualified name, separated by dots.
 - **Identifier completion for unimported definitions**: If the user enters a prefix that does not match any identifier in the current scope, the IDE will search all identifiers in the Arend libraries added to the project (except those explicitly marked with `\private` keyword, which indicates that the definition should be invisible anywhere except the current file). Selecting an item from the completion menu will turn the prefix into a valid reference, automatically adding the necessary imports.

Next to the currently selected identifier in the completion menu, IntelliJ IDEA displays the identifier's signature. Pressing **Ctrl+Q** (or **F1** on MacOS) within the open completion menu provides quick documentation for the selected identifier.


# Intention actions and quick fixes

## Replace a meta with result

## Replace an expression with weak head normal form
![Short video illustrating Arend Normalize intention action](/about//intellij-features/NormalizeExpr.gif){: style="display: block; margin: 0 auto;" }

## Extract code as a function

## Generate function from goal
![Short video illustrating Generate Function intention action](/about/intellij-features/GenerateFunction.gif){: style="display: block; margin: 0 auto;" }

## Replace with constructor

## Implement fields quick fix
![Short video illustrating Arend implement missing field quick fix](/about//intellij-features/ImplementMissingFields.gif){: style="display: block; margin: 0 auto;" }

## Implement clauses quick fix and Split pattern variable intention
![Short video illustrating Arend intention actions related with pattern matching](/about//intellij-features/PatternGenerator.gif){: style="display: block; margin: 0 auto;" }

## Auto import quick fix
![Short video illustrating the Auto Import quick fix](/about//intellij-features/AutoImport.gif){: style="display: block; margin: 0 auto;" }


