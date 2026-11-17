# Space

## Abstract (Alpha)

A point of space is modelled by its d real coordinates, read against an arbitrary but fixed
choice of length unit and origin; the default dimension is three, but nothing is special to it,
and the space is flat and Euclidean throughout. Around that bare structure sit the structures
physics needs on space: a metric and a torsor over the Euclidean space of the same dimension, a
vector space once the origin is fixed, a norm and an inner product, and a smooth manifold,
together with a basis and coordinates, length units, the cross product in three dimensions, the
relation between spaces of different dimension, and the actions of translations and rotations.
Space is also the home of differentiation in a spatial direction, for functions and for
distributions, of gradient, divergence and curl, and of the distributions made from functions
that are bounded in the appropriate sense.

## Content (Alpha)

### Points of space and their structure

A point of space is given by its d real coordinates. [1] Space is a type of its own, distinct
from the Euclidean space of the same dimension although closely related to it, a choice discussed
on the Lean Zulip {1}.
Subtracting two points of space gives a vector of Euclidean space. [8] Space is a normed torsor
over Euclidean space of the same dimension. [9]

Space has a choice of origin, the zero of its vector space structure, and a standard
affine-isometry chart onto Euclidean space of the same dimension. [5] Once the origin is taken as
its zero, space is a real vector space. [2] It carries a norm, an inner product and a metric,
making it a finite-dimensional real inner-product space and a metric space. [3][4] It has basis
vectors, one for each coordinate direction, forming an orthonormal basis. [7]

Space is a smooth manifold, charted over Euclidean space of the same dimension through a
homeomorphism with it. [6]

### Dimensions, units and the cross product

Spaces of different dimensions are related: one dimension of space splits off as a real factor,
and one-dimensional space is isometrically the reals. [14][15] A choice of length unit rescales
lengths, and concrete units such as the metre are available. [16]

Three-dimensional Euclidean space carries the cross product. Taking the cross product with a fixed
vector commutes with the time derivative, and the cross product of a vector with another is
orthogonal to it. [17]

### Translations and rotations

Points of space can be translated, and so can distributions on space. [10][11] The group of
rotations acts on space, and that action agrees with multiplying coordinates by the rotation
matrix. [12][13]

### Derivatives and distributions

A function from space into a normed space can be differentiated along a coordinate
direction. [18] A function from space into a manifold is differentiable. [TODO]

A function bounded in the appropriate sense determines a distribution on space; the constant
function and the constant slice are such distributions. [19][20][21][22] A distribution on space
valued in a normed space can be differentiated, giving also its gradient, its divergence and its
curl. [23][24][25][26] A distribution from space into a manifold is differentiable. [TODO]

## Lean References

1. Physlib/SpaceAndTime/Space/Basic.lean — `Space`
2. Physlib/SpaceAndTime/Space/Module.lean — `AddCommGroup (Space d)`, `Module ℝ (Space d)`
3. Physlib/SpaceAndTime/Space/Module.lean — `Norm`, `InnerProductSpace ℝ (Space d)`
4. Physlib/SpaceAndTime/Space/Basic.lean — `Dist`, `MetricSpace`
5. Physlib/SpaceAndTime/Space/Origin.lean — `Zero (Space d)`, `chartEuclidean`
6. Physlib/SpaceAndTime/Space/Basic.lean — `homEuclideanSpaceSpace`, `ChartedSpace`,
   `IsManifold`
7. Physlib/SpaceAndTime/Space/Module.lean — `basis : OrthonormalBasis (Fin d) ℝ (Space d)`
8. Physlib/SpaceAndTime/Space/Basic.lean — `VSub (EuclideanSpace ℝ (Fin d)) (Space d)`
9. Physlib/SpaceAndTime/Space/Basic.lean — `AddTorsor and NormedAddTorsor (EuclideanSpace ℝ (Fin d)) (Space d)`
10. Physlib/SpaceAndTime/Space/Basic.lean — `AddAction (EuclideanSpace ℝ (Fin d)) (Space d)`
11. Physlib/SpaceAndTime/Space/Translations.lean — `translateSchwartz`, `distTranslate`
12. Physlib/SpaceAndTime/Space/EuclideanGroup/Basic.lean — `RotationGroup`
13. Physlib/SpaceAndTime/Space/EuclideanGroup/Action.lean — `MulAction (EuclideanGroup d) (Space d)`,
   `rotation_smul_eq`
14. Physlib/SpaceAndTime/Space/Slice.lean — `slice : Space d.succ ≃L[ℝ] ℝ × Space d`
15. Physlib/SpaceAndTime/Space/Module.lean — `oneEquiv : Space 1 ≃ₗᵢ[ℝ] ℝ`
16. Physlib/SpaceAndTime/Space/LengthUnit.lean — `LengthUnit`, `scale`, `meters`
17. Physlib/SpaceAndTime/Space/CrossProduct.lean — `⨯ₑ₃`, `time_deriv_cross_commute`,
   `inner_cross_self`
18. Physlib/SpaceAndTime/Space/Derivatives/Basic.lean — `Space.deriv`, `notation ∂[·]`
19. Physlib/SpaceAndTime/Space/IsDistBounded.lean — `IsDistBounded`
20. Physlib/SpaceAndTime/Space/DistOfFunction.lean — `distOfFunction`
21. Physlib/SpaceAndTime/Space/DistConst.lean — `distConst`
22. Physlib/SpaceAndTime/Space/ConstantSliceDist.lean — `sliceSchwartz`, `constantSliceDist`
23. Physlib/SpaceAndTime/Space/Derivatives/Basic.lean — `distDeriv`
24. Physlib/SpaceAndTime/Space/Derivatives/Grad.lean — `distGrad`
25. Physlib/SpaceAndTime/Space/Derivatives/Div.lean — `distDiv`
26. Physlib/SpaceAndTime/Space/Derivatives/Curl.lean — `distCurl`

## References

1. Lean Zulip, #PhysLean > Space vs EuclideanSpace,
   https://leanprover.zulipchat.com/#narrow/channel/479953-PhysLean/topic/Space.20vs.20EuclideanSpace/with/575938877
