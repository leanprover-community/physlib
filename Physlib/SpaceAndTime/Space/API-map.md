# Space

A point of space is modelled by its d real coordinates, read against an arbitrary but fixed
choice of length unit and origin. The default dimension is three, but nothing is special to it;
the space is flat and Euclidean throughout.

Around that bare structure the API builds the structures physics needs on space: a metric and a
torsor over the Euclidean space of the same dimension, a vector space once the origin is fixed,
a norm and an inner product, and a smooth manifold. The surrounding definitions and lemmas
cover a basis and coordinates, length units, the cross product in three dimensions, the
relation between spaces of different dimension, and the actions of translations and rotations.

Space is also where the API keeps differentiation in a spatial direction, both for functions
and for distributions, along with gradient, divergence and curl, and the means of making a
distribution out of a function that is bounded in the appropriate sense.

## Built on

- Distribution — `Physlib/Mathematics/TemperedDistribution`
- Time — `Physlib/SpaceAndTime/Time`
- Lorentz vectors — `Physlib/Relativity/Tensors/RealTensor/Vector`

## Requirements

The key data structure is defined: a point of space, given by its d real coordinates. [1]

Space is a real vector space, once the origin is taken as its zero. [2]

Space carries a norm, an inner product and a metric, making it a finite-dimensional real
inner-product space and a metric space. [3][4]

Space has a choice of origin, namely the zero of the vector space, and the standard
affine-isometry chart onto Euclidean space of the same dimension. [5]

Space is a smooth manifold: it is charted over Euclidean space of the same dimension, and
diffeomorphic to it. [6]

Space has basis vectors, one for each coordinate direction. [7]

Subtracting two points of space gives a vector of Euclidean space. [8]

Space is a normed torsor over Euclidean space of the same dimension. [9]

Points of space can be translated, and so can distributions on space. [10][11]

The group of rotations acts on space, and that action agrees with multiplying coordinates by
the rotation matrix. [12][13]

Spaces of different dimensions are related: one dimension can be split off as a real factor,
and the one-dimensional space is isometrically the reals. [14][15]

A choice of length unit is available, with rescaling and concrete units. [16]

Three-dimensional Euclidean space carries the cross product, with the properties relating it to
time derivatives and to inner products. [17]

A function from space into a normed space can be differentiated along a coordinate
direction. [18]

A function from space into a manifold will be differentiable. [planned]

A function bounded in the appropriate sense determines a distribution on space; the constant
function and the constant slice are such distributions. [19][20][21][22]

A distribution on space valued in a normed space can be differentiated, giving also its
gradient, its divergence and its curl. [23][24][25][26]

A distribution from space into a manifold will be differentiable. [planned]

## Further reading

- Lean Zulip, #Physlib > Space vs EuclideanSpace: https://leanprover.zulipchat.com/#narrow/channel/479953-PhysLean/topic/Space.20vs.20EuclideanSpace/with/575938877

## Lean declarations

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
