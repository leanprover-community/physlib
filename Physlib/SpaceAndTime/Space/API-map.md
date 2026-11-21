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
distributions, of gradient, divergence, curl and the Laplacian, and of the distributions made
from functions
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

A function from space into a normed space can be differentiated along each coordinate direction,
by taking its derivative along the corresponding basis vector. [18] The coordinate derivative
vanishes on constants, is additive and commutes with constant scalar multiples on differentiable
functions, and obeys the product rule for a scalar function times a vector-valued one at points
where both are differentiable; on a twice continuously differentiable function, two coordinate
derivatives commute. [27] At a point, the derivative of a function along any vector is the sum of
its coordinate derivatives weighted by the coordinates of that vector, and for a differentiable
function valued in Euclidean space, the derivative of a component is the component of the
derivative. [28] A function from space into a manifold is differentiable. [TODO]

Repeated coordinate derivatives are indexed by multi-indices, which record how many times each
coordinate direction is used, the total being the order of the multi-index. [29] The
multi-indices of order at most a given bound form a finite set. [30] The iterated derivative along
a multi-index applies the corresponding coordinate derivatives one after another; on smooth real
functions it is linear, keeps them smooth and commutes with a further coordinate derivative, and
on any real function it does not enlarge the closed support. [31]

The gradient of a real function on space is the vector of Euclidean space formed by its coordinate
derivatives; it is linear on differentiable functions, and, read through the basis of space, it is
the gradient defined by the inner product. [32] The divergence of a vector field, a function from
space into Euclidean space of the same dimension, is the sum of the derivatives of its components
along the matching directions, and is linear on differentiable fields. [33] In three dimensions a
vector field also has a curl, whose components contract the Levi-Civita symbol with the
derivatives of the components of the field; it too is linear on differentiable fields. [34] A
field of real d by d matrices on d-dimensional space has a divergence, taken row by row, which is
linear on differentiable fields. [35]

The Laplacian of a real function is the divergence of its gradient, that is the sum of its second
derivatives along the coordinate directions, and the Laplacian of a vector field is taken
component by component. [36]

In three dimensions, for twice continuously differentiable fields and functions, the divergence of a
curl and the curl of a gradient vanish, and the curl of a curl is the gradient of the divergence
minus the vector Laplacian. [37] Conversely, on the whole of three-dimensional space, a continuously
differentiable field with zero divergence is the curl of a differentiable field: explicitly, it is
minus the curl of the integral over t from 0 to 1 of the cross product of t x with the field at t x.
A differentiable field with zero curl is the gradient of a differentiable function, which for a
continuously differentiable field is the integral of the field along the segment from the origin.
[38] A field that also depends on time, with zero divergence at each time, is the curl of a field
depending on time that is as many times continuously differentiable, jointly in time and space, as
the original field; likewise a curl-free one is such a gradient. [TODO]

A function that is bounded in the appropriate sense, that is almost everywhere strongly measurable
and bounded by a finite sum of non-negative multiples of integer powers of the distances to some
fixed points, with exponents at least 1 - d (at least 0 when d = 0), determines a distribution on
space by integration against Schwartz functions, called below the distribution of the function.
[19][20] The constant distribution sends a Schwartz function to its integral times a fixed vector.
[21] A distribution on space of one dimension less gives a distribution on space that is constant
along a chosen direction, by first integrating Schwartz functions along that direction. [22]

A distribution on space valued in a normed space has a derivative along each coordinate direction,
and any two of these derivatives commute. [23] When a differentiable function and its derivative
along a coordinate direction are both bounded in the appropriate sense, the derivative of its
distribution along that direction is the distribution of its derivative. [39] The constant
extension of a distribution has zero derivative along the chosen direction, and along any other
direction its derivative is the constant extension of the derivative of the original
distribution. [40]

A real-valued distribution has a gradient, whose components are its coordinate derivatives. [24] A
distribution valued in Euclidean space of the same dimension has a divergence, the sum of the
derivatives of its components along the matching directions; for the distribution of a vector
field bounded in the appropriate sense, it sends a Schwartz function to minus the integral of the
inner product of the field with the gradient of that function. [25] In three dimensions a
distribution valued in Euclidean space also has a curl, and the curl of the gradient of any
real-valued distribution vanishes. [26] The Laplacian of a real-valued distribution is the
divergence of its gradient, and it vanishes on the constant distributions. [41] The coordinate
derivatives, the gradient, the divergence and the curl of a constant distribution vanish as
well. [42] A distribution from space into a manifold is differentiable. [TODO]

In positive dimension d, for an integer m with m + d > 2, the Laplacian of the distribution of
‖x‖^m is m (m + d - 2) times the distribution of ‖x‖^(m - 2). [43] In positive dimension d, the
divergence of the distribution of the radial field x / ‖x‖^d is d times the volume of the unit
ball times the Dirac delta at the origin. [44] In every dimension d, the Laplacian of the
distribution of ‖x‖^(2 - d) is (2 - d) d times the volume of the unit ball times the Dirac delta
at the origin; in dimension two, where this is the Laplacian of a constant, the Laplacian of the
distribution of the logarithm of the norm is twice the area of the unit disc times the Dirac
delta. [45] In odd dimension 2m + 1, applying the Laplacian m + 1 times to the distribution of
the norm gives a non-zero multiple of the Dirac delta at the origin. [46]

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
23. Physlib/SpaceAndTime/Space/Derivatives/Basic.lean — `distDeriv`, `notation ∂ᵈ[·]`,
   `distDeriv_commute`
24. Physlib/SpaceAndTime/Space/Derivatives/Grad.lean — `distGrad`, `notation ∇ᵈ`, `distGrad_apply`
25. Physlib/SpaceAndTime/Space/Derivatives/Div.lean — `distDiv`, `notation ∇ᵈ ⬝`,
   `distDiv_apply_eq_sum_distDeriv`, `distDiv_ofFunction`
26. Physlib/SpaceAndTime/Space/Derivatives/Curl.lean — `distCurl`, `notation ∇ᵈ ⨯`,
   `distCurl_distGrad_eq_zero`
27. Physlib/SpaceAndTime/Space/Derivatives/Basic.lean — `deriv_const`, `deriv_add`, `deriv_sub`,
   `deriv_const_smul`, `deriv_smul`, `deriv_commute`
28. Physlib/SpaceAndTime/Space/Derivatives/Basic.lean — `fderiv_eq_sum_deriv`, `deriv_euclid`
29. Physlib/SpaceAndTime/Space/Derivatives/MultiIndex.lean — `MultiIndex`, `MultiIndex.order`
30. Physlib/SpaceAndTime/Space/Derivatives/DerivativeIndex.lean — `DerivativeIndex`,
   `Fintype (DerivativeIndex d k)`
31. Physlib/SpaceAndTime/Space/Derivatives/Iterated.lean — `iteratedDeriv`, `notation ∂^[·]`,
   `iteratedDeriv_add`, `iteratedDeriv_const_smul`, `iteratedDeriv_contDiff`,
   `deriv_iteratedDeriv_commute`, `tsupport_iteratedDeriv_subset`
32. Physlib/SpaceAndTime/Space/Derivatives/Grad.lean — `grad`, `notation ∇`, `grad_apply`,
   `grad_add`, `grad_smul`, `grad_eq_gradient`
33. Physlib/SpaceAndTime/Space/Derivatives/Div.lean — `div`, `notation ∇ ⬝`, `div_add`,
   `div_smul`
34. Physlib/SpaceAndTime/Space/Derivatives/Curl.lean — `curl`, `notation ∇ ⨯`,
   `curl_eq_sum_leviCivitaSymbol`, `curl_add`, `curl_smul`
35. Physlib/SpaceAndTime/Space/Derivatives/MatrixDiv.lean — `matrixDiv`, `matrixDiv_apply`,
   `matrixDiv_add`, `matrixDiv_smul`
36. Physlib/SpaceAndTime/Space/Derivatives/Laplacian.lean — `laplacian`, `notation Δ`,
   `laplacian_eq_sum_snd_deriv`, `laplacianVec`, `notation Δᵥ`
37. Physlib/SpaceAndTime/Space/Derivatives/Curl.lean — `div_of_curl_eq_zero`,
   `curl_of_grad_eq_zero`, `curl_of_curl`
38. Physlib/SpaceAndTime/Space/Derivatives/Curl.lean — `exists_curl_of_div_zero`,
   `eq_neg_curl_of_div_zero`, `exists_grad_of_curl_zero`, `eq_grad_integral_of_curl_zero`
39. Physlib/SpaceAndTime/Space/DistOfFunction.lean — `distDeriv_distOfFunction`
40. Physlib/SpaceAndTime/Space/ConstantSliceDist.lean — `distDeriv_constantSliceDist_same`,
   `distDeriv_constantSliceDist_succAbove`
41. Physlib/SpaceAndTime/Space/Derivatives/Laplacian.lean — `distLaplacian`, `notation Δᵈ`,
   `distLaplacian_const`
42. Physlib/SpaceAndTime/Space/DistConst.lean — `distDeriv_distConst`, `distGrad_distConst`,
   `distDiv_distConst`, `distCurl_distConst`
43. Physlib/SpaceAndTime/Space/Norm/Basic.lean — `distLaplacian_distOfFunction_norm_zpow`
44. Physlib/SpaceAndTime/Space/Norm/Basic.lean — `distDiv_inv_pow_eq_dim`
45. Physlib/SpaceAndTime/Space/Norm/Basic.lean — `distLaplacian_fundamentalSolution_norm_zpow`,
   `distLaplacian_fundamentalSolution_log_norm`
46. Physlib/SpaceAndTime/Space/Norm/IteratedLaplacian.lean —
   `iterated_distLaplacian_norm_zpow_odd_eq_smul_diracDelta`,
   `oddNormIteratedLaplacianCoeff_ne_zero`

## References

1. Lean Zulip, #PhysLean > Space vs EuclideanSpace,
   https://leanprover.zulipchat.com/#narrow/channel/479953-PhysLean/topic/Space.20vs.20EuclideanSpace/with/575938877
