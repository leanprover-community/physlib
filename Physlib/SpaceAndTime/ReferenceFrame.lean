/-
Copyright (c) 2026 Raunak Chhatwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raunak Chhatwal
-/
module

public import Mathlib.Analysis.InnerProductSpace.GramMatrix
public import Physlib.Mathematics.ForMathlib.IsConst
public import Physlib.SpaceAndTime.Space.Basic
public import Physlib.SpaceAndTime.Time.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
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

open scoped ContDiff Manifold RealInnerProductSpace

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
  /-- The spatial origin is smooth. -/
  origin_smooth : ContMDiff 𝓘(ℝ) (𝓡 d) ∞ origin
  /-- The basis used to turn displacement vectors into coordinate components at each time. -/
  basis : Time → Module.Basis (Fin d) ℝ (EuclideanSpace ℝ (Fin d))
  /-- Each basis vector is smooth. -/
  basis_smooth : ∀ i, ContMDiff 𝓘(ℝ) (𝓡 d) ∞ (basis · i)
  /-- The pairwise inner products of the basis vectors are constant in time. -/
  gram_matrix_constant : (Matrix.gram ℝ <| basis ·).IsConst

namespace ReferenceFrame

variable (frame : ReferenceFrame d)

/-- Convert a frame's real-valued time coordinate into an instant in affine time. -/
def timeEquiv : ℝ ≃ᵃ[ℝ] Time :=
  AffineEquiv.vaddConst ℝ frame.timeOrigin

/-- Whether the frame's coordinate basis is orthonormal at every time. -/
def Orthonormal : Prop :=
  ∀ t, _root_.Orthonormal ℝ (frame.basis t)

/-- The geometric velocity of the frame's origin at time coordinate `t`. -/
def velocity (t : ℝ) : EuclideanSpace ℝ (Fin d) :=
  mfderiv 𝓘(ℝ) (𝓡 d) frame.origin (frame.timeEquiv t) (1 : ℝ)

/-!
## B. Inertial reference frames

In Newtonian mechanics, an inertial coordinate grid does not rotate or change scale, and its origin
moves in a straight line at constant velocity. These conditions restrict the frame, not the
particles described in that frame.
-/

/-- Whether a reference frame is related to its initial grid by uniform translation alone. -/
structure IsInertial (frame : ReferenceFrame d) : Prop where
  /-- The spatial origin has constant velocity. -/
  velocity_constant : frame.velocity.IsConst
  /-- The coordinate axes neither rotate nor change scale with time. -/
  basis_constant : frame.basis.IsConst

namespace IsInertial

variable {frame} (h : frame.IsInertial)

/-- The time-independent velocity of an inertial frame's coordinate origin. -/
def velocity : EuclideanSpace ℝ (Fin d) :=
  h.velocity_constant.value

/-- The origin of an inertial frame moves by elapsed time times its constant velocity. -/
lemma origin_vsub_eq (t₁ t₂ : Time) :
    frame.origin t₂ -ᵥ frame.origin t₁ = (t₂ -ᵥ t₁) • h.velocity := by
  let p (s : ℝ) := (Space.homEuclideanSpaceSpace d).symm (frame.origin ⟨s⟩)
  refine (intervalIntegral.integral_eq_sub_of_hasDerivAt (f := p) (fun x _ ↦ ?_)
    intervalIntegrable_const).symm.trans (intervalIntegral.integral_const h.velocity)
  have hx := (frame.origin_smooth.mdifferentiable (by decide) ⟨x⟩).hasMFDerivAt.2
  rw [velocity, ← h.velocity_constant.apply_eq_value (frame.timeEquiv.symm ⟨x⟩),
    ReferenceFrame.velocity, AffineEquiv.apply_symm_apply]
  simpa using! ((hasFDerivAt_comp_add_right (f := p) x).mp (hx.hasFDerivAt (by simp))).hasDerivAt

/-- A frame with fixed axes moving uniformly relative to an inertial frame is inertial,
with velocity given by addition of the ambient velocities. -/
lemma of_relative_motion {other : ReferenceFrame d} {u : EuclideanSpace ℝ (Fin d)}
    (hrel : ∀ t₁ t₂, (other.origin t₂ -ᵥ frame.origin t₂) -
      (other.origin t₁ -ᵥ frame.origin t₁) = (t₂ -ᵥ t₁) • u)
    (hbasis : ∀ t₁ t₂, other.basis t₁ = other.basis t₂) :
    ∃ h' : other.IsInertial, h'.velocity = h.velocity + u := by
  simp_rw [vsub_sub_vsub_comm (other.origin _) (frame.origin _), h.origin_vsub_eq,
    sub_eq_iff_eq_add', ← smul_add] at hrel
  have hv (x : ℝ) : other.velocity x = h.velocity + u := by
    let t := other.timeEquiv x
    have hd := (other.origin_smooth.mdifferentiable (by decide) t).hasMFDerivAt.2
    refine HasDerivAt.unique (f := fun s : ℝ ↦ other.origin (s +ᵥ t) -ᵥ other.origin t)
      ((hd.hasFDerivAt (by simp)).sub_const (WithLp.toLp 2 (other.origin t).val)).hasDerivAt ?_
    simpa only [hrel, vadd_vsub] using! (ContinuousLinearMap.toSpanSingleton ℝ _).hasFDerivAt
  let hc := Function.IsConst.of_forall_eq _ hv
  exact ⟨⟨hc, hbasis⟩, (hc.apply_eq_value 0).symm.trans (hv 0)⟩

end IsInertial

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

variable {frame}

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

instance : FiniteDimensional ℝ frame.Vector :=
  FiniteDimensional.of_injective componentLinearEquiv.toLinearMap componentEquiv.injective

/-- Equivalence between frame vectors and geometric displacements in space,
defined by the frame's basis at time coordinate `t`. -/
def dispEquiv (t : ℝ) : frame.Vector ≃ₗ[ℝ] EuclideanSpace ℝ (Fin d) :=
  componentLinearEquiv.trans (frame.basis (frame.timeEquiv t)).equivFun.symm

/-- The geometric inner product pulled back to frame vectors at time coordinate `t`. -/
@[instance_reducible] def inducedInnerProduct (t : ℝ) : InnerProductSpace.Core ℝ frame.Vector where
  inner v w  := ⟪dispEquiv t v, dispEquiv t w⟫
  conj_inner_symm _ _ := inner_conj_symm _ _
  re_inner_nonneg _ := inner_self_nonneg
  add_left _ _ _ := by rw [map_add, inner_add_left]
  smul_left _ _ _ := by rw [map_smul, inner_smul_left]
  definite _ inner_zero := (dispEquiv t).map_eq_zero_iff.mp (inner_self_eq_zero.mp inner_zero)

/-- The frame's constant Gram matrix makes the induced inner product independent of time. -/
lemma inner_product_conserved : inducedInnerProduct (frame := frame) |>.IsConst := by
  intro t₁ t₂
  simp only [inducedInnerProduct, dispEquiv, LinearEquiv.trans_apply,
    Module.Basis.equivFun_symm_apply, ← Matrix.star_dotProduct_gram_mulVec,
    frame.gram_matrix_constant (frame.timeEquiv t₁) (frame.timeEquiv t₂)]

instance : NormedAddCommGroup frame.Vector :=
  inner_product_conserved.value.toNormedAddCommGroup

instance : InnerProductSpace ℝ frame.Vector :=
  .ofCore inner_product_conserved.value.toCore

/-- The linear isometry from frame vectors to geometric displacements at time `t`. -/
def dispIsometry (t : ℝ) : frame.Vector ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d) :=
  (dispEquiv t).isometryOfInner (congr($(inner_product_conserved.apply_eq_value t).inner · ·))

/-- In an orthonormal frame, the inner product is the sum of component products. -/
lemma inner_euclidean_if_orthonormal : frame.Orthonormal →
    ∀ v w : frame.Vector, ⟪v, w⟫ = ∑ i, v.components i * w.components i := by
  intro h v w
  change inner_product_conserved.value.inner v w = _
  rw [← inner_product_conserved.apply_eq_value 0]
  change ⟪dispEquiv 0 v, dispEquiv 0 w⟫ = _
  simp [dispEquiv, Module.Basis.equivFun_symm_apply, (h _).inner_sum, componentLinearEquiv,
    componentEquiv]

/-- In an orthonormal frame, the squared norm is the sum of squared components. -/
lemma norm_euclidean_if_orthonormal : frame.Orthonormal →
    ∀ v : frame.Vector, ‖v‖^2 = ∑ i, (v.components i)^2 := by
  intro h v
  simpa only [real_inner_self_eq_norm_sq, pow_two] using inner_euclidean_if_orthonormal h v v

end ClassicalMechanics.ReferenceFrame.Vector
