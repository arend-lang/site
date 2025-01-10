---
title: Navigation
---

# Go to declaration
To jump to the location where an identifier is defined, the user can use the Declaration or Usages command by positioning the cursor on the identifier and pressing **Ctrl+B** (or **⌘B** on macOS). The user can also right-click on the identifier and select **Go to > Declaration or Usages**, or simply hold **Ctrl** and click on the identifier.

# File structure
The File Structure view, accessible via **Alt+7**, (or **⌘ 7** on macOS) provides an overview of all namespaces, sections, and declarations within an Arend file. Clicking any entry in this view navigates directly to the corresponding location in the code.

# Breadcrumbs bar
When the text cursor is placed anywhere in an Arend file, IntelliJ IDEA displays a breadcrumbs bar at the bottom of the editor. 
This bar shows the file path, namespaces, sections, and the current declaration where the cursor is located. Clicking on any item in the breadcrumbs bar reveals a list of all related elements. For example, clicking on a declaration will display all other declarations within the same namespace. Selecting an entry navigates directly to the associated code or file.

# Find usages
![Short video illustrating the usage of Find Usages feature](/about//intellij-features/FindUsages.gif){: style="display: block; margin: 0 auto;" }
The **Find Usages** command can be invoked by either right-clicking on an identifier and selecting Find Usages, or by placing the cursor on the identifier and pressing **Alt+Shift+7** (or **⌥F7** on macOS). This command locates all occurrences of the identifier within the specified scope, organizes them by the type of usage and the containing file, and also displays a brief snippet of the surrounding code.

# Project-wide text search/replacement
The **Find in Files** command **Ctrl+Shift+F** (or **⇧⌘F** on macOS) and **Replace in Files** command **Ctrl+Shift+R** (or **⇧⌘R** on macOS) provide effective tools for searching and replacing text within an Arend project. As the user types, matching entries are displayed and organized by the files in which they are found. By selecting a result, the user is directed to the corresponding location in the code. The search can be refined using various options available as icons adjacent to the search field, such as **Match Case**, **Match Whole Word**, or **Use Regex**. Additionally, file name masks can be applied to impose further conditions on file names or to restrict the search to a specific directory

# Go to Class/File/Symbol
Pressing **Ctrl+N** (or **⌘O** on macOS) (resp. **Ctrl+Alt+Shift+N** or **⌥⌘O** on macOS) opens the **Go to** window in IntelliJ IDEA, which can also be accessed via the Navigate menu. In the **Class** or **Symbol** tab, typing a name displays all matching classes or Arend definitions within the selected scope, which by default includes all Arend libraries added to the project. The Arend plugin also adds a special **Arend Files** tab to this window limiting the search to files with the `.ard` extension.

# Class Hierarchy
![Short video illustrating the usage of Class Hierarchy feature](/about//intellij-features/ClassHierarchy.gif){: style="display: block; margin: 0 auto;" }
The Arend plugin supports IntelliJ IDEA’s **Class Hierarchy** feature, enabling the user to visualize and navigate the inheritance structure of an Arend class or record, showing its parent and child classes. 
To view the hierarchy, the user needs to place the cursor on the class name and press **Ctrl+H** (or **⌘H** on macOS). 
This opens a dedicated tool window displaying the hierarchy tree. 
The user can toggle between views of superclasses and subclasses.

The hierarchy panel is interactive, allowing the user to navigate directly to any class by clicking on it. 
Clicking the **Visualize as Orthogonal Diagram** button opens a separate window with an orthogonal diagram of the class hierarchy.
Note that the contents of the diagram depend on whether the subclasses or superclasses view is active.
The user can also press **Ctrl+Alt+H** (or **⌘⌥H** on macOS) to show the **Call Hierarchy** in the same tool window.

# Proof search
![Short video illustrating the usage of Proof Search feature](/assets/images/ProofSearch.gif){: style="display: block; margin: 0 auto;" }
Nearly every proof assistant struggles with the problem of efficient location of relevant theorems or lemmas in their formal libraries. 
Consider, for instance, the problem of recalling the name of a lemma that encodes the property that addition is commutative. 
Is it labeled as `add_comm`, or `+-comm` in the library?

The Arend plugin helps address this issue by allowing the user to search for functions based on the definitions they reference. 
This functionality, called **Proof Search** is comparable to the Search vernacular command in Coq, Type-Directed Search in Idris, or Loogle in Lean.
**Proof Search** can be accessed via **Tools > Arend > Proof Search**, or by using the predefined shortcut **Ctrl+Alt+P** (or **⌥⌘P** on macOS). 

The user needs to type a query pattern in the input field. 
**Proof Search** then lists all definitions whose parameter or result types contain a subexpression matching the specified pattern.
In the simplest case this pattern consists of a single reference to an Arend definition and the **Proof Search** lists all definitions mentioning this identifier in their parameters or result type (notice that a theorem’s statement does count as a result type due to Curry--Howard correspondence).

For example, the following definitions can be found using the pattern List:

{% arend %}
\func foo : List Nat => {?}
\func bar : \Sigma (List Bool) Nat => {?}
\func baz {A : \Type} : List A => {?}
{% endarend %}

An example of a more advanced search query is a pattern resembling a partial application of a function or a type. 
Such patterns are allowed to be written in infix form.
The placeholder `_` can be used as a wildcard pattern to match any arbitrary term. 
For instance, the query `List Nat` will return only those definitions that explicitly include the subexpression `List Nat` within the types of their parameters (or within their result type). 
On the other hand, the following definitions can be found using the search pattern `_ + _ = _ + _`:

{% arend %}
\func foo (a b : Nat) : a + b = b + a
\func bar (a b : Int) : a + b = b + a
{% endarend %}

The user can navigate search results using arrow keys and perform the following actions in the **Proof Search** window:
- **View Definition**: Pressing **Enter** will display the definition of a selected result.
- **Navigate to Location**: Pressing **F4** will navigate the editor to the location of a selected definition.
- **Insert in Editor**: Pressing **Ctrl+Enter** (or **⌘Enter** on macOS) will insert the name selected definition into the editor.

## The grammar of queries
The grammar of **Proof Search** queries is defined as follows:
```
  query ::= (and_pattern '->')* and_pattern
  and_pattern ::= (app_pattern '\and')*
  app_pattern app_pattern ::= atom_pattern+
  atom_pattern ::= '_' | (IDENTIFIER '.')* IDENTIFIER | '(' app_pattern ')'
```
As is evident from the grammar, the `app_pattern` construct corresponds precisely to the "partial application" pattern mentioned above.
When a **Proof Search** query includes the symbol `->` (i. e. when there are multiple `and_pattern` entries), the query is processed as follows:
The rightmost `and_pattern` is matched against the codomain (result type) of a definition.
The preceding `and_pattern` entries (separated by `->`) are matched against the domain parameters of the definition. 
Importantly, the result of matching these and_pattern entries is insensitive to both the order of patterns and the order of parameters.
For example, the query `Foo -> Bar` will produce the following results:

{% arend %}
\func foo (f : Foo) : Bar -- matched
\func bar :    Foo -> Bar -- matched
\func baz :           Bar -- not matched
{% endarend %}

Similarly, the query Nat -> Bool -> List Nat will produce the following results:

{% arend %}
\func foo (n : Nat)  (b : Bool) : List Nat -- matched
\func bar (b : Bool) (n : Nat)  : List Nat -- matched
{% endarend %}

When an `and_pattern` includes multiple `app_patterns` separated with `\and` keyword, a parameter of a definition is matched with the pattern only if it matches all indicated `app_pattern`’s simultaneously. 
For example, the query `Nat -> Bool -> _` will return all definitions with parameters mentioning `Nat` and `Bool`, regardless of whether these mentions occur in the same or different parameters, whereas the query `Nat \and Bool -> _` will match only those definitions which contain at least one parameter whose type expression refers to both `Nat` and `Bool`. 

