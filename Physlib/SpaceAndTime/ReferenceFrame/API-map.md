# Reference frame

An observer describing motion needs a coordinate grid, and the grid is a choice rather than a
feature of space. Two points of space determine a displacement, and a displacement acquires
numerical components only once axes have been picked. Space carries a zero point of its own, but
an observer is under no obligation to use it: which point the coordinates call zero is part of
the observer's choice. Likewise, no instant of time is canonically zero. A reference frame is
that collection of choices: a time origin, and an origin and a set of axes carried along through
time.

An inertial frame is one whose grid is not being pushed around. Its axes are the same at every
time, and its origin drifts in a straight line at constant speed, both measured against the
affine structure that space itself supplies. This is a restriction on the observer rather than
on whatever is being observed, and it is the setting in which the familiar Newtonian statements
about free motion hold.

A vector quantity measured by an observer, a relative position, a velocity, an acceleration, a
force, a momentum, is a list of components read off that observer's axes. Such lists add and
scale componentwise regardless of which quantity they stand for, so they share one carrier here;
the physical dimension, units and transformation law belong to whatever definition supplies the
quantity. Lengths and angles are the exception, since they are geometric facts about the
displacement rather than about the numbers: they are taken from the underlying space through the
frame's axes, so that a grid with skew or unequal axes cannot make the same physical
displacement appear to change length. When the axes are orthonormal this reduces to the familiar
Euclidean formulas, the sum of the squared components giving the squared length and the sum of
the componentwise products giving the inner product.

## Built on

- Space — `Physlib/SpaceAndTime/Space`
- Time — `Physlib/SpaceAndTime/Time`

## Requirements

The key data structure is defined: a reference frame, recording a time origin together with an
affine origin and a displacement basis at each time. [1]

A frame can be built from the trajectories of a collection of reference points, provided those
points form an affine basis at every time. [2]

A frame may induce the same inner product on coordinates at every time; that condition is
stated. [3]

A frame may have orthonormal axes at every time. Such a frame conserves its coordinate metric,
and an instance makes that fact available to typeclass inference. [4]

A frame is inertial when its origin moves with constant velocity and its axes are the same at
every time. [5]

An inertial frame's origin has a constant velocity, which the API names. [6]

An inertial frame conserves its coordinate metric, and an instance makes that fact available to
typeclass inference. [7]

The components of a vector quantity measured relative to a frame have a carrier of their own,
equivalent to the tuples of coordinates. [8]

Those components add and scale componentwise, inheriting the additive and scalar structure of
their entries. [9]

Through the frame's basis, such components name a geometric displacement in space at a given
time; the identification is available both as a linear and as a continuous linear map. [10]

The components carry a topology, a continuous linear equivalence with coordinate tuples, and
finite dimensionality. [11]

For a frame that conserves its coordinate metric, the components carry a norm and an inner
product, pulled back through the frame basis from geometric displacement space, so that a
displacement keeps its length and its angles even when the axes are skew or unequally
scaled. [12]

In an orthonormal frame, that norm and inner product reduce to the familiar Euclidean formulas
in the components. [13]

A frame carries a choice of time origin, so that time translations can act on frames. [14]

The defining property of an inertial frame's origin velocity, and the origin and basis of a
frame built from reference points, will be recorded. [planned]

The relative motion of two inertial frames will be expressed as the boost, rotation and
translation carrying one to the other, together with the transformation law this induces on
measured components. [planned]

The derivative of a trajectory expressed in a frame will give the velocity and acceleration
that frame measures, as the time derivative of the coordinate components. [planned]

A frame whose axes are constant and whose origin moves with constant velocity relative to an
inertial frame will be shown to be inertial itself. [planned]

## Lean declarations

1. Physlib/SpaceAndTime/ReferenceFrame.lean — `ReferenceFrame`, `ReferenceFrame.timeOrigin`,
   `ReferenceFrame.origin`, `ReferenceFrame.basis`
2. Physlib/SpaceAndTime/ReferenceFrame.lean — `ReferenceFrame.fromReferencePoints`
3. Physlib/SpaceAndTime/ReferenceFrame.lean — `ReferenceFrame.IsMetricConserved`
4. Physlib/SpaceAndTime/ReferenceFrame.lean — `ReferenceFrame.Orthonormal`,
   `Orthonormal.isMetricConserved`, `Fact frame.IsMetricConserved`
5. Physlib/SpaceAndTime/ReferenceFrame.lean — `ReferenceFrame.IsInertial`,
   `origin_moves_uniformly`, `basis_conserved`
6. Physlib/SpaceAndTime/ReferenceFrame.lean — `IsInertial.velocity`
7. Physlib/SpaceAndTime/ReferenceFrame.lean — `IsInertial.isMetricConserved`,
   `Fact frame.IsMetricConserved`
8. Physlib/SpaceAndTime/ReferenceFrame.lean — `ReferenceFrame.Vector`, `components`,
   `componentEquiv`, `componentLinearEquiv`
9. Physlib/SpaceAndTime/ReferenceFrame.lean — `AddCommGroup frame.Vector`,
   `Module ℝ frame.Vector`
10. Physlib/SpaceAndTime/ReferenceFrame.lean — `dispEquiv`, `contDispEquiv`
11. Physlib/SpaceAndTime/ReferenceFrame.lean — `componentContLinearEquiv`,
   `TopologicalSpace frame.Vector`, `FiniteDimensional ℝ frame.Vector`
12. Physlib/SpaceAndTime/ReferenceFrame.lean — `NormedAddCommGroup frame.Vector`,
   `InnerProductSpace ℝ frame.Vector`
13. Physlib/SpaceAndTime/ReferenceFrame.lean — `norm_euclidean_if_orthonormal`,
   `inner_euclidean_if_orthonormal`
14. Physlib/SpaceAndTime/ReferenceFrame.lean — `ReferenceFrame.timeOrigin`,
   `ReferenceFrame.timeEquiv`
