# SpaceTime

## Abstract (Alpha)

Minkowski space-time, for an arbitrary but fixed choice of units and origin and an arbitrary
spatial dimension, is a Lorentz vector: a point is its time and space coordinates taken together,
and the Lorentz group acts on it. Around it sit the coordinate maps, the projections onto space
and onto time and the equivalence with their product, the measure-space structure that
integration over space-time needs, including the splitting of such an integral into an integral
over time of an integral over space, differentiation along a coordinate for functions and for
distributions, and the slicing of either at a fixed instant.

## Content (Alpha)

### Points of space-time

A point of Minkowski space-time is a Lorentz vector {1} of coordinates, for an arbitrary but
fixed choice of units and origin. [1] Space-time maps onto space {2} and onto time {3}, and is
equivalent to their product. [2]

The Lorentz group {4} acts on space-time, and through it
on Schwartz maps and distributions on space-time. [8] A rotation about the coordinate origin acts
on space-time through the Lorentz group and on space through the Euclidean group, and the
spatial projection intertwines these two actions of one and the same special orthogonal
rotation. [3]

### Integration and slicing

Space-time carries the measure-space structure that integration over it uses: a Borel
measurable space with an additive Haar volume measure. [9] An integral over space-time splits
into an integral over space and an integral over time, in either order. [7] A function or a
distribution on space-time can be sliced at a fixed instant. [10]

### Derivatives

A function from space-time into a normed space can be differentiated along a coordinate, and its
derivatives assemble into a tensor. [4] A function from space-time into a manifold can be
differentiated along a coordinate too, giving a tangent vector at its value. [5] A distribution
on space-time valued in a normed space can be differentiated. [6] A distribution from space-time
into a manifold is differentiable. [TODO]

## Lean References

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

## References

1. Lorentz tensors API map — Physlib/Relativity/Tensors/API-map.md
2. Space API map — Physlib/SpaceAndTime/Space/API-map.md
3. Time API map — Physlib/SpaceAndTime/Time/API-map.md
4. Lorentz group API map — Physlib/Relativity/LorentzGroup/API-map.md
