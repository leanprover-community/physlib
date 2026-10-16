# Rigid body

A rigid body in d dimensions is specified by its mass distribution, which is what a body
contributes to any integral over it: a linear functional on the smooth functions on space. From
that single piece of data the API derives the total mass, the centre of mass and the inertia
tensor, and shows the inertia tensor to be symmetric. The inertia tensor is also available
about an arbitrary point, where the parallel-axis theorem relates it to the one about the
centre of mass. The solid sphere is worked out as a concrete example.

A rigid body in motion additionally records the trajectory of its centre of mass and its
orientation at each time. From these the API builds the velocity and linear momentum of the
centre of mass, the rigid displacement and the mass distribution it carries the body to, and
the angular velocity — in any dimension as a skew-symmetric tensor, and in three dimensions as
the dual vector obtained from it by the hat map. The total kinetic energy of the motion splits
into a translational part and a rotational part about the centre of mass, which is the König
decomposition.

## Built on

- Space — `Physlib/SpaceAndTime/Space`

## Requirements

The key data structure is defined: a rigid body, specified by its mass distribution. [1]

The total mass of a rigid body can be calculated. [2]

The centre of mass of a rigid body can be calculated. [3]

The inertia tensor of a rigid body can be calculated. [4]

The inertia tensor of a rigid body is symmetric. [5]

The inertia tensor about an arbitrary point can be calculated, and the parallel-axis theorem
relates it to the inertia tensor about the centre of mass. [6]

The solid sphere is worked out as an example, with its total mass and centre of mass
computed. [7]

The inertia tensor of a solid sphere will be shown to be two fifths of its mass times the
square of its radius, times the identity. The statement stands in the source, but its proof is
still open. [11][planned]

The angular velocity of a rotating rigid body is defined. [8]

The velocity of the centre of mass of a rigid body is defined. [9]

The kinetic energy of a rigid body is defined. [10]

Euler angles will be defined for a rigid body. [planned]

The mass distribution will be recorded as a continuous linear functional on the smooth
functions, rather than a plain linear one. [planned]

## Further reading

- Landau and Lifshitz, Mechanics, Section 32 (page 100)

## Lean declarations

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
