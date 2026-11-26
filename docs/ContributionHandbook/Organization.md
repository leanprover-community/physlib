# Organization of the code

Within Physlib it is important that code is organized
in a way which makes the physics content and flow as
easy to read as possible.

## Contents

1. [Directory Organization](#directory-organization)
2. [Areas should be based around structures](#area-organization)
3. [Files should be organized around definitions](#file-organization)
4. [Name files after what they define](#file-name)

<a id="directory-organization"></a>

## 1. Directory Organization

Physlib is organized by its definitions. Each directory exists for one key definition, with it and its basic properties in the Basic.lean file. The other files and subdirectories are each dedicated either to a definition descended from the key definition, that is, built from it, or to a single named property of those definitions. This leads to a hierarchy of definitions, which the directories follow. A definition descended from several key definitions sits under the most downstream of them. When enough is built on a definition, its file becomes a directory. Every lemma and theorem sits under one of the definitions that its statement concerns, namely the one furthest down the hierarchy. This allows any result in Physlib to be found by asking what definitions it depends on.

This is similar to Bourbaki's organizational principle, "the concept of a hierarchy of structures, going from the simple to the complex, from the general to the particular".

<a id="area-organization"></a>

## 2. Areas should be based around structures

This means that for an area in physics it is best to define a `structure` which is the basic object of study in that area. Examples of this throughout Physlib include:
- `ElectromagneticPotential` for electromagnetism
- `FLRW` and `CosmicFluid` in cosmology
- `CanonicalEnsemble` for statistical mechanics

<a id="file-organization"></a>

## 3. Files should be organized around definitions

Files should be organized around a single definition. An example of such a definition would be an eigenvector of a Quantum Mechanical system. The key definition of that file should be placed at the start of the file. What follows should be lemmas related to that file. Two important definitions should not occupy the same file.

<a id="file-name"></a>

## 4. Name files after what they define

Since Physlib is organized by definitions, every file should be named after the key definition contained within them. Examples include `Reversible.lean` and `GibbsState.lean`. The exception is the `Basic.lean` file, which contains the basic results or key data structure for the given area corresponding to the name of the overarching directory.
