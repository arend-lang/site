---
title: Interface elements added by Arend plugin
---
In this section we briefly overview the interface elements added to Intellij IDEA by the Arend plugin.

# File structure
The File Structure view, accessible via **Alt+7**, (or **⌘ 7** on MacOS) provides an overview of all namespaces, sections, and declarations within an Arend file. Clicking any entry in this view navigates directly to the corresponding location in the code.

# Breadcrumbs bar
When the text cursor is placed anywhere in an Arend file, IntelliJ IDEA displays a breadcrumbs bar at the bottom of the editor. 
This bar shows the file path, namespaces, sections, and the current declaration where the cursor is located. Clicking on any item in the breadcrumbs bar reveals a list of all related elements. For example, clicking on a declaration will display all other declarations within the same namespace. Selecting an entry navigates directly to the associated code or file.

# Arend messages tool window
The Arend Messages tool window serves as the primary interactive element in Arend, providing essential insight into proof goals, expected types, and error notifications. The user can access this tool window via the quick access button. Like other tool windows in IntelliJ IDEA, the Arend Messages window can be detached from its default position at the bottom and used as a floating toolbar, offering flexibility in how the user interacts with it. It can be repositioned anywhere within the IntelliJ IDEA interface or even disabled, depending on the user's workflow preferences.

The Arend Messages tool window is organized into three distinct sections, which we will describe in order from left to right.
 - **Messages Overview**: This section remains visible at all times and lists all messages reported by the type checker. It provides a detailed, categorized overview of errors and warnings, organized by the respective files where they occur.
 - **Latest Goal**: When the caret is placed near an open goal, this section reveals extended goal context information, including both in-scope variables and the current goal statement.
 - **Current Error**: By placing the caret near a highlighted error or selecting one from the Messages Overview, this section displays the relevant error details.

The user can customize how types are displayed in the **Goal’s Printing Options** menu for the **Latest Goal** and **Current Error** sections. For instance, they can choose to enable or disable the printing of implicit arguments in functions or constructors. Additionally, the user can switch on and off the display of class instances in class members, the printing of the full long name prefix of a definition, and also the printing of the universe levels of definitions (including both homotopical levels and the levels of polymorphic universes).
The links provided in the Latest Goal and Current Error panels are interactive, allowing the user to navigate to the original definition by pressing **Ctrl+B** / **Ctrl+Left Click** (or **⌘B** / **⌘click** on MacOS). The user can also copy content from these sections.

