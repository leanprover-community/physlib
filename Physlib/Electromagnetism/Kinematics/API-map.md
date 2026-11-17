# Electromagnetic Potential

## Abstract (Alpha)

The electromagnetic potential is the primitive kinematic object of electromagnetism: a map from
spacetime to contravariant Lorentz vectors, carrying its own additive-group and scalar-action
structure and the action of the Lorentz group, with a distributional counterpart given by a tempered
distribution on spacetime valued in Lorentz vectors. It can be built from a scalar potential, from a
vector potential, or from a pair of non-relativistic potentials, and recovered from the electric and
magnetic fields in the Poincaré gauge; from it come the electric field, the magnetic field, the
field-strength term and the electromagnetic Lagrangian, in both the function and the distributional
settings.

## Content (Alpha)

### The potential

An electromagnetic potential is a map from spacetime {1} to contravariant Lorentz vectors {2}; it is
determined by its values, and potentials add, negate, subtract and scale by reals pointwise. [1] A
distributional electromagnetic potential is a tempered distribution on spacetime valued in Lorentz
vectors, and it arises from distributional scalar and vector potentials. [2]

A potential arises from a scalar potential, from a vector potential, and from a pair of
non-relativistic potentials {3}, each with a static variant, and the potential of a pair is the sum
of the potentials of its two members. [3] A connection on a U(1)-gauge bundle determines a
potential. [TODO]

### Fields and Lagrangian

The electric field is determined by the potential, both for functions [4] and for
distributions. [5] The magnetic field is determined by the potential as a vector field and as an
antisymmetric matrix field for functions [6], and as an antisymmetric matrix field for
distributions. [7] The field-strength term of the Lagrangian is built from the potential, with
its gradient, for functions [8], and its gradient exists for distributions too. [9] The
electromagnetic Lagrangian is built from the potential, together with the coupling to a free
current, and both have gradients for functions [10] and for distributions. [11]

## Lean References

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

## References

1. Spacetime API map — Physlib/SpaceAndTime/SpaceTime/API-map.md
2. Lorentz group API map — Physlib/Relativity/LorentzGroup/API-map.md
3. J. D. Jackson, *Classical Electrodynamics*, 3rd ed., Sections 6.2-6.3, on vector and scalar
   potentials and gauge transformations.
