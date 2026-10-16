# SpaceTime

Minkowski space-time, for an arbitrary but fixed choice of units and origin and an arbitrary
spatial dimension, is a Lorentz vector: a point is its time and space coordinates taken
together, and the Lorentz group acts on it.

The API gives the coordinate maps, the projections onto space and onto time and the equivalence
with their product, and the measure-space structure that integration over space-time needs —
including the splitting of such an integral into an integral over time of an integral over
space. Differentiation along a coordinate is here too, for functions and for distributions, as
is the slicing of either at a fixed instant.

## Built on

- Lorentz vectors — `Physlib/Relativity/Tensors/RealTensor/Vector`
- Space — `Physlib/SpaceAndTime/Space`
- Time — `Physlib/SpaceAndTime/Time`
- Lorentz group — `Physlib/Relativity/LorentzGroup`

## Requirements

The key data structure is defined: Minkowski space-time, with an arbitrary but fixed choice of
units and origin. [1]

Space-time maps onto space and onto time. [2]

The spatial projection intertwines the Lorentz and Euclidean actions of one and the same
special orthogonal rotation about the coordinate origin. [3]

A function from space-time into a normed space can be differentiated along a coordinate. [4]

A function from space-time into a manifold can be differentiated too. [5]

A distribution on space-time valued in a normed space can be differentiated. [6]

A distribution from space-time into a manifold will be differentiable. [planned]

An integral over space-time splits into an integral over space and an integral over time. [7]

The Lorentz group acts on space-time. [8]

Space-time carries the measure-space structure that integration over it uses. [9]

A function or a distribution on space-time can be sliced at a fixed instant. [10]

## Lean declarations

1. Physlib/SpaceAndTime/SpaceTime/Basic.lean — `SpaceTime (d : ℕ := 3)`, `coord`, `coordCLM`
2. Physlib/SpaceAndTime/SpaceTime/Basic.lean — `space`, `time`, `toTimeAndSpace`
3. Physlib/SpaceAndTime/SpaceTime/Basic.lean — `space_equivariant`
4. Physlib/SpaceAndTime/SpaceTime/Derivatives.lean — `deriv`, `tensorDeriv`
5. Physlib/SpaceAndTime/SpaceTime/Derivatives.lean — `manifoldDeriv`, `manifoldDeriv_eq`
6. Physlib/SpaceAndTime/SpaceTime/Derivatives.lean — `distDeriv`, `distTensorDeriv`
7. Physlib/SpaceAndTime/SpaceTime/Basic.lean — `spaceTime_integral_eq_time_space_integral`,
   `spaceTime_integral_eq_time_integral_space_integral`,
   `spaceTime_integral_eq_space_integral_time_integral`
8. Physlib/SpaceAndTime/SpaceTime/LorentzAction.lean — `schwartzAction`,
   `SMul (LorentzGroup d)`, `DistribMulAction (LorentzGroup d)`, `SMulCommClass`,
   `distActionLinearMap`
9. Physlib/SpaceAndTime/SpaceTime/Basic.lean — `MeasurableSpace`, `BorelSpace`, `MeasureSpace`,
   `IsOpenPosMeasure`, `IsFiniteMeasureOnCompacts`, `Measure.IsAddHaarMeasure`
10. Physlib/SpaceAndTime/SpaceTime/TimeSlice.lean — `timeSlice`, `timeSliceLinearEquiv`,
   `distTimeSlice`
