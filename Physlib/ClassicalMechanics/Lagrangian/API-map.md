# Lagrangian mechanics

## Abstract (Alpha)

A Lagrangian system on a smooth manifold of configurations is a smooth function of time and of
the positions and velocities, that is, a function on time and the tangent bundle of the manifold.
Its motions are the critical points of the action, the integral of the Lagrangian along a curve,
under smooth variations of the curve that fix its endpoints. Around this sit the Euler–Lagrange
equations in charts, Noether's theorem with the conservation laws it gives, the conservation of
energy for autonomous systems, natural systems built from a Riemannian metric, and Lagrangians
written in generalised coordinates.

## Content (Alpha)

### Lagrangian systems and the action

A Lagrangian system on a configuration space M {1} is a smooth function L : Time × TM → ℝ of
time {2} and of the positions and velocities, depending on first derivatives only. [1] A smooth
variation of a curve γ on [t₀, t₁] is a smooth family of curves starting at γ and fixing γ(t₀)
and γ(t₁). [2] The action of γ is ∫ L(t, γ, γ̇) dt over [t₀, t₁], and γ is a critical point of
the action when it is smooth and every variation has zero first variation of the action {3}.
[3] On a normed space, the action is the integral of L(t, q, q̇) along the
coordinate curve. [4]

### Equations of motion

On a normed space, a smooth curve is a critical point of the action over a non-degenerate
interval if and only if the Euler–Lagrange equations hold. [5] A critical point of the action
satisfies the Euler–Lagrange equations in every chart containing it {4}. [7] A smooth curve
satisfying the Euler–Lagrange equations in every chart is a critical point of the action. [TODO]
Lagrangians L(q, q̇, t) written in generalised coordinates are Lagrangian systems {5}. [6]

### Symmetries and conservation laws

Noether's theorem: if an autonomous Lagrangian system admits a one-parameter group of
diffeomorphisms of M, then its Lagrange equations have a first integral {4}. [TODO] The
conservation of momentum and of angular momentum follow from Noether's theorem. [TODO] The energy
of an autonomous Lagrangian system is constant along its motions. [TODO]

### Natural systems

A natural system is one whose Lagrangian is kinetic minus potential energy, the kinetic energy
coming from a Riemannian metric on M. [TODO]

## Lean References

1. Physlib/ClassicalMechanics/Lagrangian/Basic.lean — `LagrangianSystem`
2. Physlib/ClassicalMechanics/ConfigurationSpace/Variation.lean — `Variation`
3. Physlib/ClassicalMechanics/Lagrangian/Basic.lean — `LagrangianSystem.action`,
   `LagrangianSystem.IsCriticalPoint`
4. Physlib/ClassicalMechanics/Lagrangian/NormedSpace.lean — `LagrangianSystem.action_ofNormedSpace`
5. Physlib/ClassicalMechanics/Lagrangian/EulerLagrange.lean —
   `LagrangianSystem.isCriticalPoint_ofNormedSpace_iff`
6. Physlib/ClassicalMechanics/Lagrangian/Basic.lean — `LagrangianSystem.ofNormedSpace`
7. Physlib/ClassicalMechanics/Lagrangian/EulerLagrangeChart.lean —
   `LagrangianSystem.eulerLagrange_chartLagrangian_of_isCriticalPoint`

## References

1. Configuration Space API map — Physlib/ClassicalMechanics/ConfigurationSpace/API-map.md
2. Time API map — Physlib/SpaceAndTime/Time/API-map.md
3. Ivo Terek, *Introductory Variational Calculus on Manifolds*.
4. V. I. Arnold, *Mathematical Methods of Classical Mechanics*.
5. L. D. Landau and E. M. Lifshitz, *Mechanics*.
