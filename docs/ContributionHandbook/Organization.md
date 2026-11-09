# Organization of the code

Within Physlib it is important that code is organized
in a way which makes the physics content and flow as
easy to read as possible.

<a id="area-organization"></a>

## 1. Areas should be based around structures

One of the best ways to organize an area in physics such as 'Lagrangian Mechanics' is to define a `structure` which is the basic object of study in that area. Examples of this throughout Physlib include:
- `ElectromagneticPotential` for electromagnetism
- `FLRW` and `CosmicFluid` in cosmology
- `CanonicalEnsemble` for statistical

## 2. Files should be organized around definitions

It is best to organize files around a single definition. An example of such a definition would be an eigenvector of a Quantum Mechanical system. The key definition of that file should be placed at the start of the file. What follows should be lemmas related to that file.
