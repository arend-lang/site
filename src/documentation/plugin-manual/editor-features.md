---
title: Editor features of Arend plugin
---
When the user opens an Arend file located within a correctly configured Arend module the Arend type checker along with other IDE visual components become accessible. The user can run the Arend type checker, use various information assistants and helpers intended to refactor the code. The specific features provided by the Arend plugin are described in detail in the following sections.

# Code and usages highlighting
By default, the Arend IntelliJ IDEA plugin provides syntax highlighting for comments, built-in keywords, infix operators, string and number literals, as well as for the usages of metas and patterns in pattern-matching clauses. When the text cursor is placed on an identifier, all occurrences of that identifier in the current file are highlighted. If the identifier corresponds to a definition with an alias, all occurrences of the alias will also be highlighted.

# Incremental background type checking
![Short video showing the operation of the background type checker](/about//intellij-features/Typechecking.gif){: style="display: block; margin: 0 auto;" }

Under normal circumstances the Arend plugin uses the so-called "on-the-fly" (or smart) mode of type checking. In this mode, the type checker operates in a background thread, automatically reprocessing each code modification made by the user. Running the type checker in the background prevents the IDE from freezing during the process. Since the type checking can be time-consuming and may involve extensive computations, a special mechanism halts the process if it exceeds the user-defined time limit (defaulted to 5 seconds). Additionally, there is an option to disable on-the-fly inspection entirely, switching the IDE into "dumb mode." In this mode, the IDE still resolves identifiers on the fly but does not automatically perform type checking which can still be manually run via IntelliJ IDEA’s standard mechanism of run configurations.

![Arend type checking settings pane](/assets/images/ArendTypecheckingMode.png){: style="display: block; margin: 0 auto;" }

When a user modifies one or more definitions, the type checker selectively discards cached information related to those definitions, as well as any other definitions that depend on them, either directly or through a chain of dependencies. This ensures that unaffected parts of the code are not reprocessed, significantly speeding up the type-checking process and helping to conserve laptop battery life.


# Dependency analysis
The mechanism of dependency analysis in Arend ensures that type checking is performed not on a per-file basis, but for each definition individually. The outcome of type checking is displayed in the editor using IntelliJ IDEA's Gutter Icons — a set of small icons positioned on the left side of the code. When a definition or theorem is fully correct and has no unresolved goals, this fact is indicated by a green "pass" gutter icon. If a definition or theorem contains syntax or type errors, a red "error" or yellow “warning” icon appears in the gutter. The latter happens when e.g. no type-checking errors are found, but a theorem still has an unresolved goal.

# Errors, warnings and weak warnings
To display errors in Arend files, a dedicated panel called the [**Arend messages tool window**](#arend-messages-tool-window) is provided. This panel automatically appears after the type checker is run. 

In IntelliJ IDEA, there are three types of issues which are displayed in the [**Arend messages tool window**](#arend-messages-tool-window) and simultaneously are indicated in Arend files using wavy underline highlighting beneath the affected code:
 - **Errors**. A red wavy underline indicates an error encountered during the processing of a definition. For example, syntax errors and type errors are marked with this highlighting.
 - **Warnings**. An orange wavy underline highlights a potential issue in the . For instance, unused variables or unresolved goals are marked with orange wavy lines.
 - **Weak Warnings**. An olive-colored wavy underline signifies a minor issue in the code, such as an expression unnecessarily surrounded by extra parentheses.

Hovering over the code with the wavy underline will display the error content in a pop-up panel. Placing the text cursor on a source line containing the wavy line will also display the full text of the error message in the “Current Error” section of the Arend Messages panel. Errors and warnings are also indicated by corresponding markings on the editor's scroll bar, located on the right-hand side of the file.

The total number of warnings and errors for the current file is also displayed in the top-right corner of the editor. The user can navigate between errors and warnings using keyboard shortcuts: **F2** / **Shift+F2** (or **F2** / **⇧F2** on macOS) moves to the next (or previous) piece of code with an error or warning relative to the caret's current position.

# Arend messages tool window
The Arend Messages tool window serves as the primary interactive element in Arend, providing essential insight into proof goals, expected types, and error notifications. The user can access this tool window via the quick access button. Like other tool windows in IntelliJ IDEA, the Arend Messages window can be detached from its default position at the bottom and used as a floating toolbar, offering flexibility in how the user interacts with it. It can be repositioned anywhere within the IntelliJ IDEA interface or even disabled, depending on the user's workflow preferences.

The Arend Messages tool window is organized into three distinct sections, which we will describe in order from left to right.
 - **Messages Overview**: This section remains visible at all times and lists all messages reported by the type checker. It provides a detailed, categorized overview of errors and warnings, organized by the respective files where they occur.
 - **Latest Goal**: When the caret is placed near an open goal, this section reveals extended goal context information, including both in-scope variables and the current goal statement.
 - **Current Error**: By placing the caret near a highlighted error or selecting one from the Messages Overview, this section displays the relevant error details.

The user can customize how types are displayed in the **Goal’s Printing Options** menu for the **Latest Goal** and **Current Error** sections. For instance, they can choose to enable or disable the printing of implicit arguments in functions or constructors. Additionally, the user can switch on and off the display of class instances in class members, the printing of the full long name prefix of a definition, and also the printing of the universe levels of definitions (including both homotopical levels and the levels of polymorphic universes).
The links provided in the Latest Goal and Current Error panels are interactive, allowing the user to navigate to the original definition by pressing **Ctrl+B** / **Ctrl+Left Click** (or **⌘B** / **⌘click** on macOS). The user can also copy content from these sections.

# Collapsible code blocks
Arend plugin enables users to collapse and expand code blocks using gutter icons positioned next to each Arend namespace or definition. By clicking these icons or using the keyboard shortcuts **Ctrl + "+"** / **Ctrl + "-"** (or **⌘ + "+"** / **⌘ + "-"** on macOS), users can toggle the visibility of code blocks in an Arend file. These blocks correspond to the inner contents of Arend classes or the nested namespaces of definitions introduced with the `\where` keyword. Similar to the breadcrumbs bar, collapsible code blocks streamline navigation within an Arend file. Furthermore, all code blocks can be expanded or collapsed simultaneously using **Shift + Ctrl + "+"** / **Shift + Ctrl + "-"** (or **⇧⌘ + "+"** / **⇧⌘ + "-"** on macOS).

# Unicode symbols and aliases
![Short video illustrating the operation of the mechanism of aliases in Arend](/about/intellij-features/Aliases.gif){: style="display: block; margin: 0 auto;" }

To enhance code readability, Arend allows the use of Unicode characters from math operator ranges (`2200–22FF` and `2A00–2AFF`) in identifiers of global definitions, such as functions or theorems. However, there is no way to input a special symbol in IntelliJ IDEA without the help of external tools: the user must copy and paste the symbol from the OS-provided “Character Map” app or use another OS-provided mechanism of inputting Unicode characters. 

Arend plugin, however, offers a partial solution to the problem of typing special symbols through the mechanism of definition aliases. This mechanism allows the on-the-fly substitution of definition names as they are being typed in Intellij IDEA, so that the user needs to manually enter a Unicode symbol-containing name only once—when defining the alias. 

To use this mechanism for a definition called `defName`, the user needs to add `\alias aliasName` after the definition name. Consider, for example, the Arend’s analogue of exists tactics from Coq or Lean:
{% arend %}
\meta Exists \alias ∃
{% endarend %}


When the user types the prefix of definition having an alias (e.g. the prefix of the word `Exists`), the IDE will show an auto-completion menu  where the user could choose the item `defName`. If they do so or if the user presses **Ctrl+Space** (or **⌘Space** on macOS), the IDE will automatically replace the entered prefix with `aliasName` (in this case with the symbol “∃”). 

# Quick documentation
![Short video illustrating the usage of Quick Documentation feature](/about//intellij-features/QuickDocumentation.gif){: style="display: block; margin: 0 auto;" }

When hovering over parts of Arend code in IntelliJ IDEA, the editor displays additional information in a popup panel. Specifically:
- **Identifier Information**: Hovering over an identifier triggers a quick documentation popup, showing the identifier's declared type, its documentation, and the file it was imported from. This popup can also be opened using the keyboard shortcut **Ctrl+Q** (or **F1** on macOS) at the current caret position.
- **Errors, Warnings, and Weak Warnings**: Hovering over code underlined with a wavy line reveals the associated error, warning, or informational message.

Pressing **Ctrl+Q** (or **F1** on macOS) while the quick documentation popup is open will expand it into a dockable panel in the IDE sidebar. This panel will then display the documentation for any identifier the user hovers over or places the caret on.

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


# Parameter Hints
![Short video illustrating the usage of Parameter Hints feature](/about//intellij-features/ParameterHints.gif){: style="display: block; margin: 0 auto;" }

Placing the cursor inside a data type or function call expression and pressing **Ctrl+P** (or **⌘P** on macOS) activates the **Parameter Hints** feature. 
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
Auto-completion can always be triggered manually using the **Ctrl+Space** (or **⌘Space** on macOS) keystroke.
IntelliJ IDEA will complete the selected identifier when **Enter** or **Tab** is pressed.

There are four types of auto-completion in Arend:
 - **Identifier completion**: When typing an identifier, IntelliJ IDEA displays all identifiers available in the current context that match the partially typed input. The search implemented by IntelliJ IDEA is fuzzy and supports "hump-back" matching: typing only the capital letters or key parts of a name will match the corresponding definition. For instance, typing `RC` or `id-i` will be sufficient for `RepresentationCategory` or `id-intertwining` to appear in the completion menu.
 - **Dot completion**: After typing a dot following a namespace identifier IntelliJ IDEA shows a list of identifiers and sub-namespaces within that namespace, allowing the user to insert them after the dot.
 - **Import completion**: After the `\import` keyword, triggered by **Ctrl+Space** (or **⌘Space** on macOS) or typing the initial characters of an import statement, IntelliJ IDEA displays all Arend files whose names match the input. Selecting a file from the menu will insert its fully qualified name, separated by dots.
 - **Identifier completion for unimported definitions**: If the user enters a prefix that does not match any identifier in the current scope, the IDE will search all identifiers in the Arend libraries added to the project (except those explicitly marked with `\private` keyword, which indicates that the definition should be invisible anywhere except the current file). Selecting an item from the completion menu will turn the prefix into a valid reference, automatically adding the necessary imports.

Next to the currently selected identifier in the completion menu, IntelliJ IDEA displays the identifier's signature. Pressing **Ctrl+Q** (or **F1** on macOS) within the open completion menu provides quick documentation for the selected identifier.

# Intention actions and quick fixes
**Quick Fixes** and **Intention Actions** are standard features in IntelliJ IDEA that provide suggestions for modifying code. When a quick fix or intention action is available at the current cursor position, a light bulb icon appears. The user can click this icon or press **Alt+Enter** (or **⌥Enter** on macOS) to view a list of available actions and apply the suggested changes.
The main distinction between **Quick Fixes** and **Intention Actions** lies in their purpose. Quick Fixes are specifically aimed at resolving errors detected by the Arend type checker, while Intention Actions offer general improvements or suggestions not directly linked to specific errors. In the **Editor > Intentions** section of the IntelliJ IDEA settings, the user can configure which Arend intention actions are suggested, view examples of each action, and assign keyboard shortcuts.

## Replace a meta with result
Replaces a meta with the proof term it generates. Note that the resulting proof terms can be quite large.

## Replace an expression with weak head normal form
![Short video illustrating Arend Normalize intention action](/about//intellij-features/NormalizeExpr.gif){: style="display: block; margin: 0 auto;" }
Replaces a selected expression with its partially normalized version. Recall that an expression is said to be in WHNF if it is reduced to the point where it can’t be further simplified at the outermost level, but may still contain unevaluated or partially evaluated expressions within it. WHNF is a representation of terms used internally by the Arend type checker. It is used mainly for efficiency, as fully normalizing (reducing to a normal form) can be computationally expensive.

## Extract code as a function
Moves a selected part of an expression into a separate function within the same namespace, replacing the original part with a function call. This action also generates the necessary function arguments.

## Generate function from goal
![Short video illustrating Generate Function intention action](/about/intellij-features/GenerateFunction.gif){: style="display: block; margin: 0 auto;" }

This action can be invoked on an unfilled goal, replacing it with a call to an auxiliary function in the namespace of the current definition or theorem. The function's type will match the goal's type, and its arguments will include the minimal subset of context variables required for the goal.

## Replace with constructor
This action fills an unfilled goal with the appropriate constructor. For example, a goal with a `\Pi` type will be filled with a lambda expression, a sigma type with a tuple, and an inductive type with one of its constructors (with a prompt if multiple constructors exist), etc.

## Implement fields quick fix
![Short video illustrating Arend implement missing field quick fix](/about//intellij-features/ImplementMissingFields.gif){: style="display: block; margin: 0 auto;" }

When applied to an empty `\instance` statement with a specified type class, this quick fix generates a skeleton for implementing the class. It lists all fields inherited from ancestor classes that are not yet implemented or lack a default implementation.

## Pattern generators
![Short video illustrating Arend intention actions related with pattern matching](/about//intellij-features/PatternGenerator.gif){: style="display: block; margin: 0 auto;" }

If an Arend definition or pattern-matching construct is missing some or all of its clauses, the type checker suggests adding them using the **Implement missing clauses** quick fix. 
This quick fix works for both `\case`-expressions and definitions given by pattern-matching through the `\elim` or `\with` keywords.

In addition, the **Split Pattern** action can be applied to pattern variables used in pattern-matching clauses. This action performs the following 3 things:
- **Type Analysis**: It determines the type of the pattern variable upon which it is invoked and identifies its associated constructors.
- **Clause Duplication**: It creates as many copies of the current pattern-matching clause as there are constructors.
- **Constructor Substitution**: It replaces every instance of the original pattern variable with a call to the respective constructor in each of the newly created clauses.

## Auto import quick fix
![Short video illustrating the Auto Import quick fix](/about//intellij-features/AutoImport.gif){: style="display: block; margin: 0 auto;" }

If the user click on an unresolved identifier or presses **Ctrl+Space** (or **⌘Space** on macOS), this quick fix searches for definitions with this name among the imported Arend libraries. 
If multiple matches are found, the user can choose one. 
Once selected, the quick fix updates the identifier to a valid reference and adds the necessary `\import` directives.

Additionally, several other quick fixes perform simpler tasks, such as removing unnecessary elements or making basic corrections. 
These include adding a missing argument or class instance to a function call if the type checker can infer it, or fixing import directives in case of errors in the Arend file preamble.

