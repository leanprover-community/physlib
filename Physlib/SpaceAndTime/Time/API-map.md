# Time

## Abstract (Alpha)

An instant of time is modelled by a single real number, read against an arbitrary but fixed
choice of unit and orientation, so that a statement about time has to hold whichever unit and
whichever direction of time is picked. Instants form an affine space over the reals with no
distinguished present moment; choosing the implicit origin turns it into the one-dimensional real
inner-product space that non-relativistic physics usually works with, carrying the norm, the inner
product, the order and the volume measure. On top of this sit the derivative of a function of
time, for targets that are normed spaces and for targets that are manifolds, time as a bare
oriented manifold, and the choices of time unit, from seconds up to weeks.

## Content (Alpha)

### Instants and their structure

An instant of time is a single real number, for an arbitrary but fixed choice of unit and
orientation. [1] Instants form an affine space over the reals: a real number translates an
instant to another instant, and any two instants differ by a real elapsed time. [2] No instant is
canonically zero.

Given the implicit origin, the instant whose real number is zero, time is a real vector space of
dimension one. It has an orthonormal basis and continuous linear and isometric equivalences to the
reals. [3] Instants are ordered, so that one instant comes no later than another. [4] Time carries
a norm, and an inner product making it a one-dimensional real inner-product space. [5] It is a
Borel measurable space whose volume measure is the Haar measure of the basis, and the
identification with the reals preserves that measure. [6] Time carries an action of the
translation group. [TODO]

Time with no structure beyond its orientation is a manifold in its own right, with its topology,
its charted-space and manifold structures, and a diffeomorphism to the reals. [10]

### Derivatives in time

A function from time into a normed space has a time derivative. The derivative is compatible with
scalar multiplication and with quotients, kills constants, and preserves smoothness. Differentiating
a function valued in Euclidean space, or in Lorentz vectors {1}, agrees with differentiating its
components one at a time. [7] The time derivative of a product of square-matrix-valued functions
obeys the product rule, and the time derivative commutes with the transpose. [9]

A function from time into a manifold has a time derivative too, and for a target that is both a
normed space and a manifold the two derivatives agree. [8]

Distributions from time into a normed space are differentiable. [TODO] Distributions from time
into a manifold are differentiable. [TODO]

### Units of time

A choice of time unit is a positive real number. Two units have a ratio, and a unit rescales an
elapsed time. The concrete units run from seconds up to weeks, with the relations between them,
such as the number of seconds in an hour. [11]

## Lean References

1. Physlib/SpaceAndTime/Time/Basic.lean — `Time`
2. Physlib/SpaceAndTime/Time/Basic.lean — `VAdd ℝ Time`, `VSub ℝ Time`, `AddTorsor ℝ Time`,
   `vadd_val`, `vsub_eq_val`
3. Physlib/SpaceAndTime/Time/InnerProductSpace.lean — `AddCommGroup Time`, `Module ℝ Time`,
   `basis : OrthonormalBasis (Fin 1) ℝ Time`, `toRealCLM`, `toRealCLE`, `toRealLIE`
4. Physlib/SpaceAndTime/Time/InnerProductSpace.lean — `LE Time`, `PartialOrder Time`
5. Physlib/SpaceAndTime/Time/InnerProductSpace.lean — `Norm Time`, `NormedAddCommGroup Time`,
   `NormedSpace ℝ Time`, `InnerProductSpace ℝ Time`
6. Physlib/SpaceAndTime/Time/InnerProductSpace.lean — `MeasurableSpace Time`, `BorelSpace Time`,
   `volume_eq_basis_addHaar`, `val_measurePreserving`
7. Physlib/SpaceAndTime/Time/Derivatives.lean — `Time.deriv`, `notation ∂ₜ`, `deriv_smul`,
   `deriv_div`, `deriv_const`, `deriv_contDiff_of_contDiff`, `deriv_euclid`,
   `deriv_lorentzVector`
8. Physlib/SpaceAndTime/Time/Derivatives.lean — `Time.manifoldDeriv`, `deriv_eq_manifoldDeriv`
9. Physlib/SpaceAndTime/Time/MatrixDerivatives.lean — `Time.deriv_matrix_mul`,
   `Time.deriv_matrix_transpose`
10. Physlib/SpaceAndTime/Time/TimeMan.lean — `TimeMan`, `ChartedSpace ℝ TimeMan`,
   `IsManifold 𝓘(ℝ, ℝ) ω TimeMan`, `valDiffeomorphism`
11. Physlib/SpaceAndTime/Time/TimeUnit.lean — `TimeUnit`, `HDiv TimeUnit TimeUnit ℝ≥0`, `scale`,
   `seconds`, `hours_div_seconds`

## References

1. Lorentz tensors API map — Physlib/Relativity/Tensors/API-map.md
