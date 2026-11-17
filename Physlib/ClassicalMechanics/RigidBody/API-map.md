# Rigid body

## Abstract (Alpha)

A rigid body in d-dimensional space is specified by its mass distribution, which is what a body
contributes to any integral over it: a linear functional on the smooth functions on space. From that
single piece of data come the total mass, the centre of mass and the inertia tensor, both about the
origin and about an arbitrary point, with the solid sphere as a worked example. A rigid body in
motion additionally carries the trajectory of its centre of mass and its orientation at each time,
from which come the velocity of the centre of mass, the angular velocity — in any dimension as a
skew-symmetric tensor, and in three dimensions as the dual vector obtained by the hat map — and the
kinetic energy, which splits into a translational part and a rotational part about the centre of
mass (the König decomposition).

## Content (Alpha)

### Mass distribution and inertia

A rigid body {1} is specified by its mass distribution, a linear functional on the smooth functions
on space {2}. [1] That functional is continuous. [TODO] The total mass of a rigid body is its
mass distribution applied to the constant function one. [2] The centre of mass is the mass-weighted
average of the coordinate functions. [3] The inertia tensor of a rigid body, I_ij = ∫ (δ_ij |x|² −
x_i x_j) dm, is built from the second moments of its mass distribution about the origin. [4] It is
symmetric. [5] The inertia tensor about an arbitrary point takes its moments about that point, and
the parallel-axis theorem expresses it as the inertia tensor about the centre of mass plus that of a
point mass at the centre of mass. [6]

The solid sphere of mass m and radius R > 0, with uniform density on the closed ball about the
origin, is a rigid body whose total mass is m and whose centre of mass is the origin. [7] In three
dimensions its inertia tensor about its centre is (2/5) m R² times the identity. [11][TODO]

### Motion

The angular velocity of a rotating rigid body is the skew-symmetric tensor Ω = Ṙ Rᵀ built from its
orientation R, and in three dimensions it is the vector dual to that tensor under the hat map. [8]
The velocity of the centre of mass is the time derivative of the centre-of-mass trajectory. [9] The
rotational kinetic energy at angular velocity ω is ½ ω · (I ω), and the total kinetic energy of a
moving body is half the mass integral of the squared speed of its points. [10] The orientation of a
rigid body is described by Euler angles. [TODO]

## Lean References

1. Physlib/ClassicalMechanics/RigidBody/Basic.lean — `RigidBody`
2. Physlib/ClassicalMechanics/RigidBody/Basic.lean — `RigidBody.mass`
3. Physlib/ClassicalMechanics/RigidBody/Basic.lean — `RigidBody.centerOfMass`
4. Physlib/ClassicalMechanics/RigidBody/Basic.lean — `RigidBody.inertiaTensor`
5. Physlib/ClassicalMechanics/RigidBody/Basic.lean — `RigidBody.inertiaTensor_symmetric`
6. Physlib/ClassicalMechanics/RigidBody/Basic.lean — `RigidBody.inertiaTensorAbout`,
   `RigidBody.inertiaTensorAbout_eq_centerOfMass_add_pointMass`
7. Physlib/ClassicalMechanics/RigidBody/SolidSphere.lean — `RigidBody.solidSphere`,
   `RigidBody.solidSphere_mass`, `RigidBody.solidSphere_centerOfMass`
8. Physlib/ClassicalMechanics/RigidBody/AngularVelocity.lean — `RigidBodyMotion.angularVelocityTensor`,
   `RigidBodyMotion.angularVelocity`
9. Physlib/ClassicalMechanics/RigidBody/Motion.lean — `RigidBodyMotion.centerOfMassVelocity`
10. Physlib/ClassicalMechanics/RigidBody/KineticEnergy.lean — `RigidBody.rotationalKineticEnergy`,
   `RigidBodyMotion.kineticEnergy`
11. Physlib/ClassicalMechanics/RigidBody/SolidSphere.lean — `solidSphere_inertiaTensor`

## References

1. Landau and Lifshitz, *Mechanics*, Section 32 (page 100).
2. Space API map — Physlib/SpaceAndTime/Space/API-map.md
