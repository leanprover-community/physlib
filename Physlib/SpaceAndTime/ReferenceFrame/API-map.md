# Reference frame

## Abstract (Alpha)

An observer describing motion needs a coordinate grid, and the grid is a choice rather than a
feature of space: two points of space determine a displacement, but a
displacement acquires numerical components only once axes have been picked, the observer need not
use the zero point space carries, and no instant of time is canonically zero.
A reference frame is that collection of choices, a time origin together with an origin and a set
of axes carried along through time. An inertial frame is one whose grid is not being pushed
around, the setting in which the familiar Newtonian statements about free motion hold, and a
vector quantity measured by an observer is a list of components read off that observer's axes,
whose lengths and angles are nevertheless taken from the underlying space.

## Content (Alpha)

### Frames

A reference frame records a time origin, together with an affine origin and a basis of displacements
of space {1} at each time. [1] Its time origin converts a real time coordinate into an instant of
time {2}. [14] The spatial origin and each basis vector are smooth in time. [2]

The pairwise inner products of the basis vectors are constant in time: the axes may rotate,
but their lengths and the angles between them stay fixed. [3] A frame may also have orthonormal
axes at every time. [4]

### Inertial frames

A frame is inertial when its origin moves with constant velocity and its axes are the same at
every time, both measured against the affine structure that space itself supplies. [5] This is a
restriction on the observer rather than on whatever is being observed. An inertial frame's origin
has a definite constant velocity. [6] Over any elapsed time the origin is displaced by that
elapsed time multiplied by this velocity. [7]

The relative motion of two inertial frames is the boost, rotation and translation carrying one to
the other, and it induces a transformation law on measured components. [TODO] A frame whose
axes are constant and whose origin moves with constant velocity relative to an inertial frame is
itself inertial. Its velocity is the sum of the original frame velocity and the relative velocity,
both expressed in ambient space. [15]

### Measured vector quantities

A vector quantity measured by an observer, a relative position, a velocity, an acceleration, a
force, a momentum, is a list of components read off that observer's axes. These components have
a carrier of their own, equivalent to the tuples of coordinates. [8] They add and scale
componentwise, inheriting the additive and scalar structure of their entries, regardless of which
quantity they stand for; the physical dimension, units and transformation law belong to whatever
supplies the quantity. [9] The frame vectors form a finite-dimensional real vector space. [11]

Through the frame's basis at a given time, such components name a geometric displacement in
space by a linear isometry. [10] Lengths and angles are geometric facts
about that displacement rather than about the numbers. In every frame, the components carry
a norm and an inner product pulled back through the frame basis from
displacement space, so that a displacement keeps its length and its angles even when the axes are
skew or unequally scaled. [12] In an orthonormal frame these reduce to the familiar Euclidean
formulas: the sum of the squared components gives the squared length, and the sum of the
componentwise products gives the inner product. [13]

The derivative of a trajectory expressed in a frame gives the velocity and acceleration that frame
measures, as the time derivative of the coordinate components. [TODO]

## Lean References

1. Physlib/SpaceAndTime/ReferenceFrame.lean — `ReferenceFrame`, `ReferenceFrame.timeOrigin`,
   `ReferenceFrame.origin`, `ReferenceFrame.basis`
2. Physlib/SpaceAndTime/ReferenceFrame.lean — `ReferenceFrame.origin_smooth`,
   `ReferenceFrame.basis_smooth`
3. Physlib/SpaceAndTime/ReferenceFrame.lean — `ReferenceFrame.gram_matrix_constant`
4. Physlib/SpaceAndTime/ReferenceFrame.lean — `ReferenceFrame.Orthonormal`
5. Physlib/SpaceAndTime/ReferenceFrame.lean — `ReferenceFrame.IsInertial`,
   `IsInertial.velocity_constant`, `IsInertial.basis_constant`
6. Physlib/SpaceAndTime/ReferenceFrame.lean — `IsInertial.velocity`
7. Physlib/SpaceAndTime/ReferenceFrame.lean — `IsInertial.origin_vsub_eq`
8. Physlib/SpaceAndTime/ReferenceFrame.lean — `ReferenceFrame.Vector`, `components`,
   `componentEquiv`, `componentLinearEquiv`
9. Physlib/SpaceAndTime/ReferenceFrame.lean — `AddCommGroup frame.Vector`,
   `Module ℝ frame.Vector`
10. Physlib/SpaceAndTime/ReferenceFrame.lean — `Vector.dispEquiv`, `Vector.dispIsometry`
11. Physlib/SpaceAndTime/ReferenceFrame.lean — `FiniteDimensional ℝ frame.Vector`
12. Physlib/SpaceAndTime/ReferenceFrame.lean — `NormedAddCommGroup frame.Vector`,
   `InnerProductSpace ℝ frame.Vector`
13. Physlib/SpaceAndTime/ReferenceFrame.lean — `norm_euclidean_if_orthonormal`,
   `inner_euclidean_if_orthonormal`
14. Physlib/SpaceAndTime/ReferenceFrame.lean — `ReferenceFrame.timeOrigin`,
   `ReferenceFrame.timeEquiv`
15. Physlib/SpaceAndTime/ReferenceFrame.lean — `IsInertial.of_relative_motion`

## References

1. Space API map — Physlib/SpaceAndTime/Space/API-map.md
2. Time API map — Physlib/SpaceAndTime/Time/API-map.md
