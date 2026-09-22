/-
Copyright (c) 2026 Raunak Chhatwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raunak Chhatwal
-/
module

public import Mathlib.LinearAlgebra.AffineSpace.Basis
public import Mathlib.Topology.Algebra.Module.TransferInstance
public import Physlib.SpaceAndTime.Space.Basic
public import Physlib.SpaceAndTime.Time.Basic
/-!
# Reference frames

A point in space and a list of coordinates are different kinds of data. Assigning coordinates to a
point requires an origin and a basis for measuring displacements from that origin. A
`ReferenceFrame` records those choices at every time.

This distinction is built into `Space d`, which is an affine space. Two points determine a
displacement, but no point is automatically the zero point. The chosen origin therefore belongs to
the frame, not to space itself. Similarly, a displacement has coordinate components only after a
basis has been chosen. Real-valued coordinates in all frames use the same implicit units of space
and time. Different frames represent different coordinate grids, not different units.

Most applications should use frames that are both inertial and orthonormal. In orthonormal frames,
the norm and inner product of coordinate vectors are given by the familiar Euclidean formulas. The
extra generality here also permits nonorthonormal coordinate grids. Giving every coordinate tuple
the standard Euclidean norm and dot product, independently of its basis, would make coordinate
transformations involving such a grid non-isometric: the same geometric displacement could acquire
different lengths, or a pair of displacements a different angle, merely by changing frames. Instead,
the metric on frame vectors is pulled back from geometric displacement space through the frame
basis. The usual component formulas are recovered for orthonormal frames.
-/

@[expose] public noncomputable section

namespace ClassicalMechanics

variable {d : ℕ}

/-!
## A. Reference frames

A reference frame can be pictured as a coordinate grid carried through time. It is part of how
motion is described, not an additional physical object moving with the particles.
-/

/-- A time origin and a time-indexed spatial origin and basis in `d`-dimensional space. -/
structure ReferenceFrame (d : ℕ) where
  /-- The instant assigned time coordinate zero. -/
  timeOrigin : Time
  /-- The point assigned coordinate zero at each time. -/
  origin : Time → Space d
  /-- The basis used to turn displacement vectors into coordinate components at each time. -/
  basis : Time → Module.Basis (Fin d) ℝ (EuclideanSpace ℝ (Fin d))

/-- Build a reference frame from the trajectories of a collection of reference points.

At each time, the reference points must form an affine basis: none is redundant, and together they
span the whole space. One reference point is chosen as the origin, and the displacements from it to
the remaining points form the coordinate basis. The resulting frame need not be inertial or
orthonormal. -/
def ReferenceFrame.fromReferencePoints
    (timeOrigin : Time)
    (referencePoints : Finset (Time → Space d))
    (independence : ∀ t, AffineIndependent ℝ fun point : referencePoints => point.val t)
    (spans_space : ∀ t, affineSpan ℝ {point.val t | point : referencePoints} = ⊤) :
    ReferenceFrame d :=
  let affineBasis (t : Time) : AffineBasis referencePoints ℝ (Space d) :=
    ⟨fun point => point.val t, independence t, spans_space t⟩
  let reference_points_not_empty := (affineBasis timeOrigin).nonempty
  let origin := Classical.choice reference_points_not_empty
  letI := Fintype.ofFinite {point : referencePoints // point ≠ origin}
  let basis t := (affineBasis t).basisOf origin
  let other_reference_points_size_eq_dim :
      Fintype.card {point : referencePoints // point ≠ origin} = d :=
    by simpa using (Module.finrank_eq_card_basis <| basis timeOrigin).symm
  let basisReindexed t :=
    (basis t).reindex (Fintype.equivFinOfCardEq other_reference_points_size_eq_dim)
  { timeOrigin := timeOrigin, origin := origin, basis := basisReindexed }

namespace ReferenceFrame

variable {frame : ReferenceFrame d}

/-- Convert a frame's real-valued time coordinate into an instant in affine time. -/
def timeEquiv (frame : ReferenceFrame d) : ℝ ≃ᵃ[ℝ] Time :=
  AffineEquiv.vaddConst ℝ frame.timeOrigin

/-!
## B. Inertial reference frames

In Newtonian mechanics, an inertial coordinate grid does not rotate or change scale, and its origin
moves in a straight line at constant velocity. These conditions restrict the frame, not the
particles described in that frame.
-/

/-- Whether the frame basis induces the same inner product on coordinates at every time. -/
def IsMetricConserved (frame : ReferenceFrame d) : Prop :=
  ∀ t₁ t₂ i j,
    inner ℝ (frame.basis t₁ i) (frame.basis t₁ j) = inner ℝ (frame.basis t₂ i) (frame.basis t₂ j)

/-- Whether the frame's coordinate basis is orthonormal at every time. -/
def Orthonormal (frame : ReferenceFrame d) : Prop :=
  ∀ t, _root_.Orthonormal ℝ (frame.basis t)

/-- An orthonormal frame conserves its coordinate metric. -/
lemma Orthonormal.isMetricConserved (h : frame.Orthonormal) : frame.IsMetricConserved := by
  intro t₁ t₂ i j
  rw [orthonormal_iff_ite.mp (h t₁) i j, orthonormal_iff_ite.mp (h t₂) i j]

instance [h : Fact frame.Orthonormal] : Fact frame.IsMetricConserved := ⟨h.out.isMetricConserved⟩

/-- Whether a reference frame is related to its initial grid by uniform translation alone. -/
structure IsInertial (frame : ReferenceFrame d) : Prop where
  /-- Elapsed time times `velocity` is exactly the origin's displacement. -/
  origin_moves_uniformly :
    ∃ velocity, ∀ t₁ t₂, frame.origin t₂ -ᵥ frame.origin t₁ = (t₂ -ᵥ t₁) • velocity
  /-- The coordinate axes neither rotate nor change scale with time. -/
  basis_conserved : ∀ t₁ t₂, frame.basis t₁ = frame.basis t₂

/-- The time-independent velocity of an inertial frame's coordinate origin. -/
def IsInertial.velocity (h : frame.IsInertial) : EuclideanSpace ℝ (Fin d) :=
  Classical.choose h.origin_moves_uniformly

/-- An inertial frame conserves its coordinate metric. -/
lemma IsInertial.isMetricConserved (h : frame.IsInertial) : frame.IsMetricConserved := by
  intro t₁ t₂ i j
  rw [h.basis_conserved t₁ t₂]

/-- Inertiality provides the conserved metric needed for metric operations on frame vectors. -/
instance [h : Fact frame.IsInertial] : Fact frame.IsMetricConserved := ⟨h.out.isMetricConserved⟩

/-!
## C. Vectors in a reference frame

`frame.Vector` is the common coordinate carrier for vector quantities expressed relative to
`frame`. It intentionally records the coordinate frame but not the physical dimension, so relative
position, velocity, acceleration, force, momentum, and similar quantities can use the same
componentwise calculations. Their different physical roles, units, and transformation laws must be
supplied by the surrounding definitions. When a vector represents a displacement, `dispEquiv`
converts its coordinates into the corresponding geometric displacement at a given time.
-/

/-- The `d` real components used to express a vector quantity relative to `frame`. -/
structure Vector (frame : ReferenceFrame d) where
  /-- One scalar coefficient for each axis of the frame. -/
  components : Fin d → ℝ

namespace Vector

/-- Equivalence between frame vectors and coordinate components -/
def componentEquiv : frame.Vector ≃ (Fin d → ℝ) :=
  Equiv.mk components mk Eq.refl Eq.refl

instance : AddCommGroup frame.Vector := componentEquiv.addCommGroup

instance : Module ℝ frame.Vector :=
  AddEquiv.module ℝ { componentEquiv with map_add' _ _ := rfl }

/-- Scalar multiplication by a positive real. -/
instance : SMul {x : ℝ // 0 < x} frame.Vector where
  smul c x := c.val • x

/-- Linear equivalence between frame vectors and coordinate components. -/
def componentLinearEquiv : frame.Vector ≃ₗ[ℝ] (Fin d → ℝ) :=
  {componentEquiv with map_add' _ _ := rfl, map_smul' _ _ := rfl}

/-- Equivalence between frame vectors and geometric displacements in space,
defined by the frame's basis at time coordinate `t`. -/
def dispEquiv (t : ℝ) : frame.Vector ≃ₗ[ℝ] EuclideanSpace ℝ (Fin d) :=
  componentLinearEquiv.trans (frame.basis (frame.timeEquiv t)).equivFun.symm

/-- Use the same topology for frame vectors as components' product topology. -/
instance : TopologicalSpace frame.Vector := componentEquiv.topologicalSpace

/-- Continuous linear equivalence between frame vectors and coordinate components. -/
def componentContLinearEquiv (frame : ReferenceFrame d) : frame.Vector ≃L[ℝ] (Fin d → ℝ) :=
  { componentLinearEquiv with
    continuous_toFun := continuous_induced_dom
    continuous_invFun := componentEquiv.homeomorph.continuous_invFun }

instance : FiniteDimensional ℝ frame.Vector :=
  FiniteDimensional.of_injective componentLinearEquiv.toLinearMap componentEquiv.injective

/-- Continuous equivalence between frame vectors and geometric displacements in space,
defined by the frame's basis at time coordinate `t`. -/
def contDispEquiv (t : ℝ) : frame.Vector ≃L[ℝ] EuclideanSpace ℝ (Fin d) :=
  (componentContLinearEquiv frame).trans
    (frame.basis (frame.timeEquiv t)).equivFun.toContinuousLinearEquiv.symm

/-- The physical norm on frame vectors, pulled back from geometric displacement space. -/
instance [_h : Fact frame.IsMetricConserved] : NormedAddCommGroup frame.Vector :=
  let normedSpace :=
    NormedAddCommGroup.induced _ _ (dispEquiv 0).toLinearMap (dispEquiv 0).injective
  let metricSpace :=
    normedSpace.replaceTopology <| (contDispEquiv 0).toHomeomorph.isInducing.eq_induced
  { metricSpace with norm := normedSpace.norm, dist_eq := normedSpace.dist_eq }

/-- The physical inner product on frame vectors, pulled back from geometric displacement space. -/
instance [Fact frame.IsMetricConserved] : InnerProductSpace ℝ frame.Vector where
  inner x y := inner ℝ (dispEquiv 0 x) (dispEquiv 0 y)
  norm_smul_le c x := show ‖dispEquiv 0 (c • x)‖ ≤ _ * ‖dispEquiv 0 x‖ by rw [map_smul, norm_smul]
  norm_sq_eq_re_inner x := norm_sq_eq_re_inner (dispEquiv 0 x)
  conj_inner_symm x y := inner_conj_symm _ _
  add_left x y z := by rw [map_add, inner_add_left]
  smul_left x y r := by rw [map_smul, inner_smul_left]

/-- In an orthonormal frame, the norm is the square root of squared components. -/
lemma norm_euclidean_if_orthonormal [h : Fact frame.Orthonormal] :
    ∀ v : frame.Vector, ‖v‖^2 = ∑ i, (v.components i)^2 := by
  intro v
  let basis := (frame.basis (frame.timeEquiv 0)).toOrthonormalBasis (h.out _)
  calc
    _ = ‖basis.repr.symm (WithLp.toLp 2 v.components)‖ ^ 2 := by rfl
    _ = ‖WithLp.toLp 2 v.components‖ ^ 2 := by rw [basis.repr.symm.norm_map]
    _ = _ := EuclideanSpace.real_norm_sq_eq _

/-- In an orthonormal frame, the inner product is the sum of component products. -/
lemma inner_euclidean_if_orthonormal [h : Fact frame.Orthonormal] :
    ∀ v w : frame.Vector, inner ℝ v w = ∑ i, v.components i * w.components i := by
  intro v w
  let basis := (frame.basis (frame.timeEquiv 0)).toOrthonormalBasis (h.out _)
  calc
    _ = inner ℝ (basis.repr.symm <| WithLp.toLp 2 v.components)
        (basis.repr.symm <| WithLp.toLp 2 w.components) := by rfl
    _ = inner ℝ (WithLp.toLp 2 v.components) _ := by rw [basis.repr.symm.inner_map_map]
    _ = _ := by rw [PiLp.inner_apply]; simp_rw [Real.inner_apply]

end ClassicalMechanics.ReferenceFrame.Vector

end
