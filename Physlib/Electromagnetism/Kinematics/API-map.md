# Electromagnetic Potential

The electromagnetic potential is the primitive kinematic object of the electromagnetism API: a
map from spacetime to contravariant Lorentz vectors, packaged as a structure so that it can
carry its own additive-group and scalar-action structure, the action of the Lorentz group, and
an API for differentiability and smoothness. It can be built from a scalar potential, from a
vector potential, or from a pair of non-relativistic potentials, and it can be recovered from
the electric and magnetic fields in the Poincaré gauge.

A distributional counterpart is a tempered distribution on spacetime valued in Lorentz vectors,
built from distributional scalar and vector potentials in the same way.

From a potential the API derives the electric field, the magnetic field — as a vector and as an
antisymmetric matrix — the field-strength term, and the electromagnetic Lagrangian, in both the
function and the distributional settings. Reading the potential as a connection on a U(1)-gauge
bundle is remarked on in the module documentation, but is not formalized.

## Built on

- SpaceTime — `Physlib/SpaceAndTime/SpaceTime`
- LorentzGroup — `Physlib/Relativity/LorentzGroup`

## Requirements

The key data structure is defined: the electromagnetic potential, a map from spacetime to
contravariant Lorentz vectors, with extensionality, a function-like coercion, and
additive-group and real-scalar-action structure. [1]

A distributional electromagnetic potential is defined, a tempered distribution on spacetime
valued in Lorentz vectors, with constructors from distributional scalar and vector
potentials. [2]

A potential can be built from a scalar potential, from a vector potential, and from a pair of
non-relativistic potentials, each with a static variant, and the combined constructor is the
sum of the other two. [3]

A potential will be constructible from a connection on a U(1)-gauge bundle. The relationship is
noted in the module documentation, but nothing is formalized. [planned]

The electric field is defined from the potential, in both the function and the distributional
settings. [4][5]

The magnetic field is defined from the potential: as a vector field in the function setting,
and as an antisymmetric matrix field in both settings. [6][7]

The field-strength term is defined from the potential, with its gradient, in both
settings. [8][9]

The Lagrangian is defined from the potential, together with the free current coupling term and
the gradients of both. [10][11]

## Further reading

- J. D. Jackson, Classical Electrodynamics, 3rd ed., Sections 6.2-6.3 (vector and scalar potentials; gauge transformations)

## Lean declarations

1. Physlib/Electromagnetism/Kinematics/EMPotential.lean — `ElectromagneticPotential`,
   `eq_of_val_eq`, `add_val`, `neg_val`, `sub_val`, `smul_val`
2. Physlib/Electromagnetism/TemperedDistributional/Basic.lean — `TempDistElectromagneticPotential`,
   `ofScalarPotential`, `ofVectorPotential`
3. Physlib/Electromagnetism/Kinematics/EMPotential.lean — `ofScalarPotential`,
   `ofVectorPotential`, `ofPotentials`, `ofStaticScalarPotential`, `ofStaticVectorPotential`,
   `ofStaticPotentials`, `ofPotentials_eq_add`
4. Physlib/Electromagnetism/Kinematics/ElectricField.lean — `electricField`
5. Physlib/Electromagnetism/TemperedDistributional/ElectricField.lean — `electricField`
6. Physlib/Electromagnetism/Kinematics/MagneticField.lean — `magneticField`,
   `magneticFieldMatrix`
7. Physlib/Electromagnetism/TemperedDistributional/MagneticField.lean — `magneticFieldMatrix`
8. Physlib/Electromagnetism/Dynamics/KineticTerm.lean — `kineticTerm`, `gradKineticTerm`
9. Physlib/Electromagnetism/TemperedDistributional/Dynamics/KineticTerm.lean — `gradKineticTerm`
10. Physlib/Electromagnetism/Dynamics/Lagrangian.lean — `lagrangian`, `freeCurrentPotential`,
   `gradLagrangian`, `gradFreeCurrentPotential`
11. Physlib/Electromagnetism/TemperedDistributional/Dynamics/Lagrangian.lean — `gradLagrangian`,
   `gradFreeCurrentPotential`
