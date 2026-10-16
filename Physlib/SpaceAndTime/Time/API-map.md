# Time

An instant of time is modelled by a single real number, read against an arbitrary but fixed
choice of unit and orientation. Nothing in the API fixes that choice, so a statement about time
has to hold whichever unit and whichever direction of time is picked.

Instants form an affine space over the reals: any two of them determine an elapsed time, and
none of them is canonically zero — there is no distinguished present moment. Choosing the
implicit origin, the instant whose real number is zero, turns that affine space into the
one-dimensional real inner-product space that non-relativistic physics usually works with, and
that is where the norm, the inner product, the order and the volume measure live.

On top of this sit the derivative of a function of time, for targets that are normed spaces and
for targets that are manifolds; time as a bare oriented manifold, carrying no further structure;
and the type of choices of time unit, from seconds up to weeks.

## Built on

- Space — `Physlib/SpaceAndTime/Space`
- Lorentz vectors — `Physlib/Relativity/Tensors/RealTensor/Vector`

## Requirements

The key data structure is defined: an instant of time, given by a single real number, for an
arbitrary but fixed choice of unit and orientation. [1]

Instants carry an affine structure over the reals: a real number translates an instant to
another instant, and any two instants differ by a real elapsed time. [2]

Given the implicit origin, time is a real vector space of dimension one, with an orthonormal
basis and continuous linear and isometric equivalences to the reals. [3]

Instants are ordered, so that one instant can be said to come no later than another. [4]

Time carries a norm, and an inner product making it a one-dimensional real inner-product
space. [5]

Time carries a measure-theoretic structure: it is a Borel measurable space whose volume measure
is the Haar measure of the basis, and the identification with the reals preserves that
measure. [6]

A function from time into a normed space can be differentiated with respect to time. The
derivative is compatible with scalar multiplication and with quotients, kills constants,
preserves smoothness, and agrees with differentiating Euclidean and Lorentz-vector components
one at a time. [7]

A function from time into a manifold can be differentiated too, and for a target that is both,
the manifold derivative agrees with the one above. [8]

The derivative of a square-matrix-valued function of time obeys the product rule and commutes
with the transpose. [9]

Time with no structure beyond its orientation is available as a manifold in its own right, with
its topology, its charted-space and manifold structures, and its diffeomorphism to the
reals. [10]

A choice of time unit is a positive real number. Two units have a ratio, a unit rescales an
elapsed time, and the concrete units from seconds up to weeks are defined together with the
relations between them. [11]

Time will carry an action of the translation group. [planned]

Distributions from time into a normed space will be differentiable. [planned]

Distributions from time into a manifold will be differentiable. [planned]

## Lean declarations

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
