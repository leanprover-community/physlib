/-
Copyright (c) 2026 Philippe Kevorkian. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Philippe Kevorkian
-/
module

public import PhyslibAlpha.ClassicalMechanics.MomentMap.GalileanMass
public import Physlib.SpaceAndTime.GalileanGroup.Basic
public import Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree
public import Mathlib.Algebra.Group.TransferInstance
public import Mathlib.Algebra.Module.TransferInstance
public import Mathlib.LinearAlgebra.Matrix.Adjugate
public import Mathlib.Analysis.Calculus.Deriv.Prod
/-!

# The mass cocycle of the Galilean group (Souriau)

## i. Overview

This file is the group level of `PhyslibAlpha.ClassicalMechanics.MomentMap.GalileanMass`, which
treats chapter 12 of Souriau's Structure des systèmes dynamiques (Dunod 1970) at the level of the
Lie algebra. The group is Physlib's `GalileanGroup 3` (`Physlib.SpaceAndTime.GalileanGroup.Basic`),
`a = (R, b, c, e)` (rotation, velocity, space translation, time translation), whose action
`(t, x) ↦ (t + e, R x + b t + c)` is Souriau's (12.76); `EvolutionSpace.smul_time_position` shows
that the action on the evolution space below is that action on each material point.

For `N` free material points, the file defines the action of the group on the evolution space
(12.76), the adjoint action on the Lie algebra (6.24) in components, and the coadjoint action on
the torsors (11.15). It proves that the group preserves the Lagrange form (12.76), that the
adjoint action satisfies (6.25), and that the moment of the free points is equivariant up to the
total mass times Souriau's cocycle `θ₀(a) = {c × b, c - b e, b, ½ ‖b‖²}` (12.126)-(12.127).
`θ₀` is a 1-cocycle (12.128) and is not a coboundary, on Souriau's group (`det R = 1`) as on the
whole group (p. 151), so the class of the system is not zero for a non-zero total mass (12.136);
its derivative at the identity is the 2-cocycle `f₀` of `GalileanMass` (12.130).

The rotation part of `GalileanGroup` ranges over `O(3)`, whereas Souriau's (12.73) takes it in
`SO(3)`. The rotation vector `ω`, an axial vector, is then transformed with the factor `det R`
(`orthogonal_mulVec_cross`). The identities proved for all `a` ((12.76), (12.77), (6.25), (11.15),
(12.126)-(12.128)) restrict to Souriau's group `properGalileanGroup`, where `det R = 1` and the
factor disappears. A negative statement does not restrict: a cocycle that is not a coboundary of
the larger group could be one of the smaller, so the statements of p. 151 and (12.136) are also
proved on `properGalileanGroup`. The adjoint and coadjoint actions in components are not printed
in chapter 12; they are computed here from (6.24), (6.28) and (11.15).

The cohomology vocabulary is Mathlib's: `θ₀` is a `groupCohomology.IsCocycle₁` for the coadjoint
action, which is (11.19 ♡), and "the class is not zero" is `¬ groupCohomology.IsCoboundary₁`,
which is (11.19 ◇). As in `PhyslibAlpha.ClassicalMechanics.MomentMap.Cohomology`, Souriau's
requirement that a cocycle be differentiable is not part of these definitions. This does not
weaken the non-coboundary statements: a coboundary `a ↦ a • μ₀ - μ₀` of (11.19 ◇) is polynomial in
the entries of `a`, hence differentiable.

What is not formalised here:
- the identification of the law of `GalileanGroup` with the product of the matrices (12.73) (it
  was checked numerically outside Lean);
- the identification of the adjoint action in components with the conjugation `a Z a⁻¹` (6.28) of
  the matrices (12.73), (12.74); it is characterised instead by (6.25), `vectorField_smul`,
  together with the injectivity of `Z ↦ Z_V` for `N ≥ 1`, `vectorField_injective`;
- that the vector field `Z_V` (12.119), taken as printed in `GalileanMass`, is the derivative at
  the identity of the action in the direction `Z` (6.11); the characterisation of the adjoint
  action by (6.25) rests on this printed formula;
- the Lie group structure (12.75) and any manifold: the derivative (12.130) is taken along curves;
- that `θ₀` is a symplectic cocycle (11.30), the dimension `1` of (12.131), forces, and the second
  half of (12.136) (Hamilton's Lagrangian is not invariant);
- (12.126) is printed for one point of unit mass; here it is proved for `N` points and the moment
  of `GalileanMass`, whose additive constant is zero.

## ii. Key results

- `EvolutionSpace.lagrangeForm_smul`: (12.76), the group preserves the Lagrange form.
- `EvolutionSpace.vectorField_smul`: (6.25), `(a • Z)_V(a • y) = D(a_V)(y)(Z_V(y))`.
- `GalileanTorsor.coadjoint_pair`: (11.15), `(a • μ)(Z) = μ(a⁻¹ • Z)`.
- `EvolutionSpace.moment_smul_sub`: (12.126)-(12.127), `μ(a • y) - a • μ(y) = m θ₀(a)`.
- `isCocycle₁_massCocycle`: (12.128); `isCocycle₁_massCocycle_proper` on Souriau's group.
- `isCoboundary₁_smul_massCocycle_proper_iff`, `not_isCoboundary₁_massCocycle_proper`: p. 151 on
  Souriau's group `properGalileanGroup`, `M θ₀` is a coboundary if and only if `M = 0`;
  `isCoboundary₁_smul_massCocycle_iff`, `not_isCoboundary₁_massCocycle`: the same on the whole
  group.
- `EvolutionSpace.not_isCoboundary₁_moment_smul_sub_proper`: (12.136) at the level of Souriau's
  group; `EvolutionSpace.not_isCoboundary₁_moment_smul_sub` on the whole group.
- `hasDerivAt_massCocycle`: (12.130), `f₀ = D(θ₀)(e)`.

## iii. Table of contents

- A. Orthogonal matrices and the cross product
- B. The action on the evolution space
- C. The adjoint action
- D. Torsors and the coadjoint action
- E. The cocycle `θ₀` and the mass
- F. The derivative of `θ₀` at the identity

## iv. References

- J.-M. Souriau, Structure des systèmes dynamiques, Dunod, Paris, 1970: pp. 139-140
  (12.73)-(12.77), p. 151 (12.126)-(12.130), pp. 152-153 (12.132)-(12.136); pp. 52-53 (6.24),
  (6.25), (6.28); p. 108 (11.15), p. 109 (11.17), p. 111 (the order of the arguments of the
  derivative of a cocycle), p. 112 (11.19), p. 113 (11.22 b).

## References

* J.-M. Souriau, *Structure des systèmes dynamiques*, Maîtrises de mathématiques, Dunod,
  Paris, 1970, chapters 6, 11 and 12. The equation numbers refer to this edition.
  [ref: Souriau1970]

-/

@[expose] public section

noncomputable section

namespace ClassicalMechanics

open Matrix

local notation "ℝ³" => Fin 3 → ℝ

/-!

## A. Orthogonal matrices and the cross product

-/

section Orthogonal

variable (R : Matrix.orthogonalGroup (Fin 3) ℝ)

/-- On coordinates, the action of `O(3)` on `EuclideanSpace ℝ (Fin 3)` is the matrix product. -/
lemma ofLp_orthogonal_smul (v : EuclideanSpace ℝ (Fin 3)) :
    WithLp.ofLp (R • v) = R.1 *ᵥ WithLp.ofLp v := rfl

/-- On coordinates, the real scalar multiplication of `EuclideanSpace ℝ (Fin 3)`. Stated apart
from `WithLp.ofLp_smul`, which would also rewrite the action of `O(3)`. -/
lemma ofLp_real_smul (k : ℝ) (v : EuclideanSpace ℝ (Fin 3)) :
    WithLp.ofLp (k • v) = k • WithLp.ofLp v := rfl

/-- An orthogonal matrix satisfies `Rᵀ R = 1`. -/
lemma orthogonal_transpose_mul_self : R.1ᵀ * R.1 = 1 := by
  have h := R.2
  rw [Matrix.mem_orthogonalGroup_iff'] at h
  simpa [Matrix.star_eq_conjTranspose] using h

/-- An orthogonal matrix satisfies `R Rᵀ = 1`. -/
lemma orthogonal_mul_transpose_self : R.1 * R.1ᵀ = 1 := by
  have h := R.2
  rw [Matrix.mem_orthogonalGroup_iff] at h
  simpa [Matrix.star_eq_conjTranspose] using h

/-- The inverse of an orthogonal matrix is its transpose. -/
lemma orthogonal_inv_val : (R⁻¹).1 = R.1ᵀ := by
  have h : (R⁻¹).1 * R.1 = 1 := by
    rw [← Submonoid.coe_mul, inv_mul_cancel, OneMemClass.coe_one]
  calc (R⁻¹).1 = (R⁻¹).1 * (R.1 * R.1ᵀ) := by rw [orthogonal_mul_transpose_self, Matrix.mul_one]
    _ = R.1ᵀ := by rw [← Matrix.mul_assoc, h, Matrix.one_mul]

/-- The determinant of an orthogonal matrix is `1` or `-1`: its square is `1`. -/
lemma orthogonal_det_mul_self : R.1.det * R.1.det = 1 := by
  calc R.1.det * R.1.det = R.1ᵀ.det * R.1.det := by rw [Matrix.det_transpose]
    _ = 1 := by rw [← Matrix.det_mul, orthogonal_transpose_mul_self, Matrix.det_one]

/-- The inverse of an orthogonal matrix has the same determinant. -/
lemma orthogonal_det_inv : (R⁻¹).1.det = R.1.det := by
  rw [orthogonal_inv_val, Matrix.det_transpose]

/-- An orthogonal matrix preserves the dot product. -/
lemma orthogonal_mulVec_dotProduct (u v : ℝ³) : (R.1 *ᵥ u) ⬝ᵥ (R.1 *ᵥ v) = u ⬝ᵥ v := by
  rw [Matrix.dotProduct_mulVec, ← Matrix.vecMul_transpose, Matrix.vecMul_vecMul,
    orthogonal_transpose_mul_self, Matrix.vecMul_one]

/-- Moving an orthogonal matrix to the other side of a dot product: `⟨x, Rᵀ y⟩ = ⟨R x, y⟩`. -/
lemma dotProduct_transpose_mulVec (x y : ℝ³) : x ⬝ᵥ (R.1ᵀ *ᵥ y) = (R.1 *ᵥ x) ⬝ᵥ y := by
  rw [Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]

/-- For any `3 × 3` matrix, `(M u) × (M v) = (adj M)ᵀ (u × v)`. -/
private lemma mulVec_cross_mulVec (M : Matrix (Fin 3) (Fin 3) ℝ) (u v : ℝ³) :
    (M *ᵥ u) ⨯₃ (M *ᵥ v) = (adjugate M)ᵀ *ᵥ (u ⨯₃ v) := by
  funext i
  fin_cases i <;>
    simp [cross_apply, adjugate_fin_three, mulVec, dotProduct, Fin.sum_univ_three,
      transpose_apply] <;>
    ring

/-- The adjugate of an orthogonal matrix is `det R • Rᵀ`. -/
lemma orthogonal_adjugate : adjugate R.1 = R.1.det • R.1ᵀ := by
  calc adjugate R.1 = (R.1ᵀ * R.1) * adjugate R.1 := by
        rw [orthogonal_transpose_mul_self, Matrix.one_mul]
    _ = R.1ᵀ * (R.1 * adjugate R.1) := by rw [Matrix.mul_assoc]
    _ = R.1.det • R.1ᵀ := by rw [Matrix.mul_adjugate, Matrix.mul_smul, Matrix.mul_one]

/-- An orthogonal matrix maps the cross product to `det R` times the cross product of the images:
`R (u × v) = det R • (R u × R v)`. A rotation (`det R = 1`) preserves the cross product. -/
lemma orthogonal_mulVec_cross (u v : ℝ³) :
    R.1 *ᵥ (u ⨯₃ v) = R.1.det • ((R.1 *ᵥ u) ⨯₃ (R.1 *ᵥ v)) := by
  rw [mulVec_cross_mulVec, orthogonal_adjugate, transpose_smul, transpose_transpose,
    Matrix.smul_mulVec, smul_smul, orthogonal_det_mul_self, one_smul]

/-- The same for the transpose: `Rᵀ (u × v) = det R • (Rᵀ u × Rᵀ v)`. -/
lemma orthogonal_transpose_mulVec_cross (u v : ℝ³) :
    R.1ᵀ *ᵥ (u ⨯₃ v) = R.1.det • ((R.1ᵀ *ᵥ u) ⨯₃ (R.1ᵀ *ᵥ v)) := by
  have h := orthogonal_mulVec_cross R⁻¹ u v
  rwa [orthogonal_inv_val, Matrix.det_transpose] at h

/-- `⟨u × v, det R • Rᵀ w⟩ = ⟨R u × R v, w⟩`: the angular momentum paired with an axial vector. -/
lemma cross_dotProduct_det_smul_transpose_mulVec (u v w : ℝ³) :
    (u ⨯₃ v) ⬝ᵥ (R.1.det • (R.1ᵀ *ᵥ w)) = ((R.1 *ᵥ u) ⨯₃ (R.1 *ᵥ v)) ⬝ᵥ w := by
  rw [dotProduct_smul, dotProduct_transpose_mulVec, orthogonal_mulVec_cross, smul_dotProduct,
    smul_smul, orthogonal_det_mul_self, one_smul]

end Orthogonal

/-!

## B. The action on the evolution space

-/

namespace EvolutionSpace

variable {N : ℕ}

/-- The action (12.76) of the Galilean group on the evolution space of `N` material points,
`t* = t + e`, `r_j* = R r_j + b t + c`, `v_j* = R v_j + b`, for
`a = (R, b, c, e)` (rotation, velocity, space translation, time translation). -/
instance : SMul (GalileanGroup 3) (EvolutionSpace N) :=
  ⟨fun a y => ⟨y.t + a.timeTranslation.val,
    fun j => a.rotation.1 *ᵥ y.r j + y.t • WithLp.ofLp a.velocity
      + WithLp.ofLp a.spaceTranslation,
    fun j => a.rotation.1 *ᵥ y.v j + WithLp.ofLp a.velocity⟩⟩

@[simp]
lemma smul_t (a : GalileanGroup 3) (y : EvolutionSpace N) :
    (a • y).t = y.t + a.timeTranslation.val := rfl

@[simp]
lemma smul_r (a : GalileanGroup 3) (y : EvolutionSpace N) (j : Fin N) :
    (a • y).r j = a.rotation.1 *ᵥ y.r j + y.t • WithLp.ofLp a.velocity
      + WithLp.ofLp a.spaceTranslation := rfl

@[simp]
lemma smul_v (a : GalileanGroup 3) (y : EvolutionSpace N) (j : Fin N) :
    (a • y).v j = a.rotation.1 *ᵥ y.v j + WithLp.ofLp a.velocity := rfl

/-- The Galilean group acts on the evolution space (12.77). -/
instance : MulAction (GalileanGroup 3) (EvolutionSpace N) where
  one_smul y := by
    apply EvolutionSpace.ext
    · simp
    · funext j
      simp
    · funext j
      simp
  mul_smul a a' y := by
    apply EvolutionSpace.ext
    · simp only [smul_t, GalileanGroup.mul_timeTranslation, Time.add_val]
      ring
    · funext j
      simp only [smul_r, smul_t, GalileanGroup.mul_rotation, GalileanGroup.mul_velocity,
        GalileanGroup.mul_spaceTranslation, Submonoid.coe_mul, WithLp.ofLp_add,
        ofLp_orthogonal_smul, ofLp_real_smul, ← Matrix.mulVec_mulVec, Matrix.mulVec_add,
        Matrix.mulVec_smul, add_smul, smul_add]
      module
    · funext j
      simp only [smul_v, GalileanGroup.mul_rotation, GalileanGroup.mul_velocity, Submonoid.coe_mul,
        WithLp.ofLp_add, ofLp_orthogonal_smul, ← Matrix.mulVec_mulVec, Matrix.mulVec_add]
      abel

/-- The differential of the affine map `y ↦ a • y`, applied to a tangent vector `dy`:
`(dt, R dr_j + b dt, R dv_j)`. -/
def tangentSMul (a : GalileanGroup 3) (dy : EvolutionSpace N) : EvolutionSpace N :=
  ⟨dy.t, fun j => a.rotation.1 *ᵥ dy.r j + dy.t • WithLp.ofLp a.velocity,
    fun j => a.rotation.1 *ᵥ dy.v j⟩

/-- The action is affine with linear part `tangentSMul a`: it maps the line `s ↦ y + s dy` to the
line `s ↦ a • y + s (tangentSMul a dy)`. -/
lemma smul_line (a : GalileanGroup 3) (y dy : EvolutionSpace N) (s : ℝ) :
    a • line y dy s = line (a • y) (tangentSMul a dy) s := by
  apply EvolutionSpace.ext
  · simp only [smul_t, line, tangentSMul]
    ring
  · funext j
    simp only [smul_r, line, tangentSMul, Matrix.mulVec_add, Matrix.mulVec_smul]
    module
  · funext j
    simp only [smul_v, line, tangentSMul, Matrix.mulVec_add, Matrix.mulVec_smul]
    abel

/-- On each material point, the action is Physlib's action of the Galilean group on
`Time × Space 3`: the time and the position of the `j`th point of `a • y` are the images of those
of `y`. -/
lemma smul_time_position (a : GalileanGroup 3) (y : EvolutionSpace N) (j : Fin N) :
    a • ((⟨y.t⟩ : Time), Space.vectorToSpace (WithLp.toLp 2 (y.r j)))
      = ((⟨(a • y).t⟩ : Time), Space.vectorToSpace (WithLp.toLp 2 ((a • y).r j))) := by
  refine Prod.ext (Time.ext ?_) (Space.eq_of_apply fun i => ?_)
  · simp [Time.add_val]
  · simp only [GalileanGroup.smul_snd, GalileanGroup.actSpace_apply, Space.vectorToSpace_vsub_zero,
      Space.vectorToSpace_apply, smul_r]
    rfl

/-- (12.76 ♣): the Galilean group preserves the Lagrange form of free material points,
`σ(a • y)(a dy)(a δy) = σ(y)(dy)(δy)`. -/
lemma lagrangeForm_smul (m : Fin N → ℝ) (a : GalileanGroup 3) (y dy δy : EvolutionSpace N) :
    lagrangeForm m (a • y) (tangentSMul a dy) (tangentSMul a δy) = lagrangeForm m y dy δy := by
  simp only [lagrangeForm, tangentSMul, smul_v]
  refine Finset.sum_congr rfl fun j _ => ?_
  have h (s : ℝ) (r : ℝ³) : a.rotation.1 *ᵥ r + s • WithLp.ofLp a.velocity
      - s • (a.rotation.1 *ᵥ y.v j + WithLp.ofLp a.velocity)
      = a.rotation.1 *ᵥ (r - s • y.v j) := by
    rw [Matrix.mulVec_sub, Matrix.mulVec_smul]
    module
  rw [h, h, orthogonal_mulVec_dotProduct, orthogonal_mulVec_dotProduct]

/-!

## C. The adjoint action

-/

end EvolutionSpace

namespace GalileanAlgebra

/-- The adjoint action (6.24) of the Galilean group on its Lie algebra, in components: with
`ω* = det R • R ω`, `a • (ω, β, γ, ε) = (ω*, R β - ω* × b, R γ + ε b - e R β - ω* × (c - e b), ε)`.
It is the conjugation `Z ↦ a Z a⁻¹` (6.28) of the matrices (12.73), (12.74) with `R` taken in
`O(3)`; this identification is not proved here, the action is characterised by (6.25)
(`EvolutionSpace.vectorField_smul`). The factor `det R` is `1` for a rotation; it makes `ω` an
axial vector under reflections. -/
instance : SMul (GalileanGroup 3) GalileanAlgebra :=
  ⟨fun a Z => ⟨a.rotation.1.det • (a.rotation.1 *ᵥ Z.ω),
    a.rotation.1 *ᵥ Z.β - (a.rotation.1.det • (a.rotation.1 *ᵥ Z.ω)) ⨯₃ WithLp.ofLp a.velocity,
    a.rotation.1 *ᵥ Z.γ + Z.ε • WithLp.ofLp a.velocity
      - a.timeTranslation.val • (a.rotation.1 *ᵥ Z.β)
      - (a.rotation.1.det • (a.rotation.1 *ᵥ Z.ω)) ⨯₃
        (WithLp.ofLp a.spaceTranslation - a.timeTranslation.val • WithLp.ofLp a.velocity),
    Z.ε⟩⟩

@[simp]
lemma smul_ω (a : GalileanGroup 3) (Z : GalileanAlgebra) :
    (a • Z).ω = a.rotation.1.det • (a.rotation.1 *ᵥ Z.ω) := rfl

@[simp]
lemma smul_β (a : GalileanGroup 3) (Z : GalileanAlgebra) :
    (a • Z).β = a.rotation.1 *ᵥ Z.β
      - (a.rotation.1.det • (a.rotation.1 *ᵥ Z.ω)) ⨯₃ WithLp.ofLp a.velocity := rfl

@[simp]
lemma smul_γ (a : GalileanGroup 3) (Z : GalileanAlgebra) :
    (a • Z).γ = a.rotation.1 *ᵥ Z.γ + Z.ε • WithLp.ofLp a.velocity
      - a.timeTranslation.val • (a.rotation.1 *ᵥ Z.β)
      - (a.rotation.1.det • (a.rotation.1 *ᵥ Z.ω)) ⨯₃
        (WithLp.ofLp a.spaceTranslation - a.timeTranslation.val • WithLp.ofLp a.velocity) := rfl

@[simp]
lemma smul_ε (a : GalileanGroup 3) (Z : GalileanAlgebra) : (a • Z).ε = Z.ε := rfl

/-- The adjoint action is an action of the Galilean group on its Lie algebra. -/
instance : MulAction (GalileanGroup 3) GalileanAlgebra where
  one_smul Z := by
    apply GalileanAlgebra.ext <;> simp
  mul_smul a a' Z := by
    apply GalileanAlgebra.ext
    · simp only [smul_ω, GalileanGroup.mul_rotation, Submonoid.coe_mul, Matrix.det_mul,
        ← Matrix.mulVec_mulVec, Matrix.mulVec_smul, smul_smul]
    · simp only [smul_ω, smul_β, GalileanGroup.mul_rotation, GalileanGroup.mul_velocity,
        Submonoid.coe_mul, Matrix.det_mul, WithLp.ofLp_add, ofLp_orthogonal_smul,
        ← Matrix.mulVec_mulVec, Matrix.mulVec_sub, Matrix.mulVec_smul, orthogonal_mulVec_cross,
        smul_smul, map_add, map_smul, LinearMap.smul_apply]
      module
    · simp only [smul_ω, smul_β, smul_γ, smul_ε, GalileanGroup.mul_rotation,
        GalileanGroup.mul_velocity, GalileanGroup.mul_spaceTranslation,
        GalileanGroup.mul_timeTranslation, Time.add_val, Submonoid.coe_mul, Matrix.det_mul,
        WithLp.ofLp_add, ofLp_orthogonal_smul, ofLp_real_smul, ← Matrix.mulVec_mulVec,
        Matrix.mulVec_add, Matrix.mulVec_sub, Matrix.mulVec_smul, orthogonal_mulVec_cross,
        smul_smul, map_add, map_sub, map_smul, LinearMap.smul_apply, add_smul, smul_add, smul_sub]
      module
    · rfl

/-- The adjoint action of `a⁻¹` in closed form:
`a⁻¹ • Z = (det R • Rᵀ ω, Rᵀ (β + ω × b), Rᵀ (γ - ε b + e β + ω × c), ε)`. -/
lemma inv_smul_eq (a : GalileanGroup 3) (Z : GalileanAlgebra) :
    a⁻¹ • Z = ⟨a.rotation.1.det • (a.rotation.1ᵀ *ᵥ Z.ω),
      a.rotation.1ᵀ *ᵥ (Z.β + Z.ω ⨯₃ WithLp.ofLp a.velocity),
      a.rotation.1ᵀ *ᵥ (Z.γ - Z.ε • WithLp.ofLp a.velocity + a.timeTranslation.val • Z.β
        + Z.ω ⨯₃ WithLp.ofLp a.spaceTranslation), Z.ε⟩ := by
  apply GalileanAlgebra.ext
  · simp only [smul_ω, GalileanGroup.inv_rotation, orthogonal_inv_val, Matrix.det_transpose]
  · simp only [smul_β, GalileanGroup.inv_rotation, GalileanGroup.inv_velocity,
      orthogonal_inv_val, Matrix.det_transpose, WithLp.ofLp_neg, ofLp_orthogonal_smul,
      Matrix.mulVec_add, orthogonal_transpose_mulVec_cross, map_neg, map_smul,
      LinearMap.smul_apply]
    module
  · simp only [smul_γ, GalileanGroup.inv_rotation, GalileanGroup.inv_velocity,
      GalileanGroup.inv_spaceTranslation, GalileanGroup.inv_timeTranslation, Time.neg_val,
      WithLp.ofLp_neg, WithLp.ofLp_add, ofLp_orthogonal_smul, ofLp_real_smul, orthogonal_inv_val,
      Matrix.det_transpose, Matrix.mulVec_add, Matrix.mulVec_sub, Matrix.mulVec_smul,
      orthogonal_transpose_mulVec_cross, map_add, map_sub, map_neg, map_smul,
      LinearMap.smul_apply, smul_neg, neg_smul]
    module
  · rfl

end GalileanAlgebra

namespace EvolutionSpace

variable {N : ℕ}

/-- (6.25): the vector field of `a • Z` at `a • y` is the image of the vector field of `Z` at `y`,
`(a • Z)_V(a • y) = D(a_V)(y)(Z_V(y))`. -/
lemma vectorField_smul (a : GalileanGroup 3) (Z : GalileanAlgebra) (y : EvolutionSpace N) :
    vectorField (a • Z) (a • y) = tangentSMul a (vectorField Z y) := by
  apply EvolutionSpace.ext
  · rfl
  · funext j
    simp only [vectorField, tangentSMul, GalileanAlgebra.smul_ω, GalileanAlgebra.smul_β,
      GalileanAlgebra.smul_γ, GalileanAlgebra.smul_ε, smul_r, smul_t, Matrix.mulVec_add,
      Matrix.mulVec_smul, orthogonal_mulVec_cross, map_add, map_sub, map_smul,
      LinearMap.smul_apply, add_smul, smul_sub]
    module
  · funext j
    simp only [vectorField, tangentSMul, GalileanAlgebra.smul_ω, GalileanAlgebra.smul_β, smul_v,
      Matrix.mulVec_add, orthogonal_mulVec_cross, map_add, map_smul, LinearMap.smul_apply]
    abel

/-- For `N ≥ 1` the map `Z ↦ Z_V` is injective, so (6.25) characterises the adjoint action. -/
lemma vectorField_injective [NeZero N] {Z Z' : GalileanAlgebra}
    (h : ∀ y : EvolutionSpace N, vectorField Z y = vectorField Z' y) : Z = Z' := by
  have h0 := h ⟨0, 0, 0⟩
  have hβ : Z.β = Z'.β := by
    simpa [vectorField] using congrFun (congrArg EvolutionSpace.v h0) 0
  have hω (u : ℝ³) : Z.ω ⨯₃ u = Z'.ω ⨯₃ u := by
    have := congrFun (congrArg EvolutionSpace.v (h ⟨0, 0, fun _ => u⟩)) 0
    simp only [vectorField, hβ] at this
    exact add_right_cancel this
  have h1 := hω ![1, 0, 0]
  have h2 := hω ![0, 1, 0]
  apply GalileanAlgebra.ext
  · have a1 := congrFun h1 1
    have a2 := congrFun h1 2
    have b2 := congrFun h2 2
    simp [cross_apply] at a1 a2 b2
    funext i
    fin_cases i
    · exact b2
    · exact a2
    · exact a1
  · exact hβ
  · simpa [vectorField] using congrFun (congrArg EvolutionSpace.r h0) 0
  · exact congrArg EvolutionSpace.t h0

end EvolutionSpace

/-!

## D. Torsors and the coadjoint action

-/

namespace GalileanTorsor

/-- The torsors as `ℝ³ × ℝ³ × ℝ³ × ℝ`, to transfer the vector space structure. -/
def equivProd : GalileanTorsor ≃ ℝ³ × ℝ³ × ℝ³ × ℝ where
  toFun μ := (μ.l, μ.g, μ.p, μ.E)
  invFun x := ⟨x.1, x.2.1, x.2.2.1, x.2.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The torsors form an additive group, component by component. -/
instance : AddCommGroup GalileanTorsor := equivProd.addCommGroup

/-- The torsors form a real vector space, component by component. -/
instance : Module ℝ GalileanTorsor := AddEquiv.module ℝ equivProd.addEquiv

/-- The pairing is additive in the torsor. -/
lemma pair_add (μ ν : GalileanTorsor) (Z : GalileanAlgebra) :
    (μ + ν).pair Z = μ.pair Z + ν.pair Z := by
  change (μ.l + ν.l) ⬝ᵥ Z.ω - (μ.g + ν.g) ⬝ᵥ Z.β + (μ.p + ν.p) ⬝ᵥ Z.γ - (μ.E + ν.E) * Z.ε = _
  simp only [pair, add_dotProduct]
  ring

/-- The pairing is additive in the torsor: subtraction. -/
lemma pair_sub (μ ν : GalileanTorsor) (Z : GalileanAlgebra) :
    (μ - ν).pair Z = μ.pair Z - ν.pair Z := by
  change (μ.l - ν.l) ⬝ᵥ Z.ω - (μ.g - ν.g) ⬝ᵥ Z.β + (μ.p - ν.p) ⬝ᵥ Z.γ - (μ.E - ν.E) * Z.ε = _
  simp only [pair, sub_dotProduct]
  ring

/-- The zero torsor pairs to zero. -/
lemma pair_zero (Z : GalileanAlgebra) : (0 : GalileanTorsor).pair Z = 0 := by
  change (0 : ℝ³) ⬝ᵥ Z.ω - (0 : ℝ³) ⬝ᵥ Z.β + (0 : ℝ³) ⬝ᵥ Z.γ - (0 : ℝ) * Z.ε = 0
  simp

/-- The pairing is linear in the torsor. -/
lemma pair_smul (k : ℝ) (μ : GalileanTorsor) (Z : GalileanAlgebra) :
    (k • μ).pair Z = k * μ.pair Z := by
  change (k • μ.l) ⬝ᵥ Z.ω - (k • μ.g) ⬝ᵥ Z.β + (k • μ.p) ⬝ᵥ Z.γ - (k • μ.E) * Z.ε = _
  simp only [pair, smul_dotProduct, smul_eq_mul]
  ring

/-- A torsor is determined by its values on the Lie algebra. -/
lemma ext_pair {μ ν : GalileanTorsor} (h : ∀ Z, μ.pair Z = ν.pair Z) : μ = ν := by
  apply GalileanTorsor.ext
  · funext i
    simpa [pair] using h ⟨Pi.single i 1, 0, 0, 0⟩
  · funext i
    simpa [pair] using h ⟨0, Pi.single i 1, 0, 0⟩
  · funext i
    simpa [pair] using h ⟨0, 0, Pi.single i 1, 0⟩
  · simpa [pair] using h ⟨0, 0, 0, 1⟩

/-- The coadjoint action (11.15) of the Galilean group on the torsors, in closed form:
`a • {l, g, p, E} = {det R • R l - b × R g + c × R p, R g - e R p, R p, E + ⟨R p, b⟩}`.
It is characterised by `(a • μ)(Z) = μ(a⁻¹ • Z)` (`coadjoint_pair`). -/
instance : SMul (GalileanGroup 3) GalileanTorsor :=
  ⟨fun a μ => ⟨a.rotation.1.det • (a.rotation.1 *ᵥ μ.l)
      - WithLp.ofLp a.velocity ⨯₃ (a.rotation.1 *ᵥ μ.g)
      + WithLp.ofLp a.spaceTranslation ⨯₃ (a.rotation.1 *ᵥ μ.p),
    a.rotation.1 *ᵥ μ.g - a.timeTranslation.val • (a.rotation.1 *ᵥ μ.p),
    a.rotation.1 *ᵥ μ.p, μ.E + (a.rotation.1 *ᵥ μ.p) ⬝ᵥ WithLp.ofLp a.velocity⟩⟩

/-- (11.15): `(a • μ)(Z) = μ(a⁻¹ • Z)`. -/
lemma coadjoint_pair (a : GalileanGroup 3) (μ : GalileanTorsor) (Z : GalileanAlgebra) :
    (a • μ).pair Z = μ.pair (a⁻¹ • Z) := by
  rw [GalileanAlgebra.inv_smul_eq]
  change (a.rotation.1.det • (a.rotation.1 *ᵥ μ.l) - WithLp.ofLp a.velocity ⨯₃ (a.rotation.1 *ᵥ μ.g)
      + WithLp.ofLp a.spaceTranslation ⨯₃ (a.rotation.1 *ᵥ μ.p)) ⬝ᵥ Z.ω
    - (a.rotation.1 *ᵥ μ.g - a.timeTranslation.val • (a.rotation.1 *ᵥ μ.p)) ⬝ᵥ Z.β
    + (a.rotation.1 *ᵥ μ.p) ⬝ᵥ Z.γ
    - (μ.E + (a.rotation.1 *ᵥ μ.p) ⬝ᵥ WithLp.ofLp a.velocity) * Z.ε
    = μ.l ⬝ᵥ (a.rotation.1.det • (a.rotation.1ᵀ *ᵥ Z.ω))
    - μ.g ⬝ᵥ (a.rotation.1ᵀ *ᵥ (Z.β + Z.ω ⨯₃ WithLp.ofLp a.velocity))
    + μ.p ⬝ᵥ (a.rotation.1ᵀ *ᵥ (Z.γ - Z.ε • WithLp.ofLp a.velocity + a.timeTranslation.val • Z.β
        + Z.ω ⨯₃ WithLp.ofLp a.spaceTranslation))
    - μ.E * Z.ε
  rw [dotProduct_smul, dotProduct_transpose_mulVec, dotProduct_transpose_mulVec,
    dotProduct_transpose_mulVec]
  generalize a.rotation.1 *ᵥ μ.l = L
  generalize a.rotation.1 *ᵥ μ.g = G
  generalize a.rotation.1 *ᵥ μ.p = P
  generalize a.rotation.1.det = d
  simp only [dotProduct, Fin.sum_univ_three, cross_apply, Pi.add_apply, Pi.sub_apply,
    Pi.smul_apply, smul_eq_mul, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  ring

/-- The coadjoint action is an action of the Galilean group on the torsors. -/
instance : MulAction (GalileanGroup 3) GalileanTorsor where
  one_smul μ := ext_pair fun Z => by rw [coadjoint_pair, inv_one, one_smul]
  mul_smul a a' μ := ext_pair fun Z => by
    rw [coadjoint_pair, coadjoint_pair, coadjoint_pair, _root_.mul_inv_rev, mul_smul]

/-- The coadjoint action is additive; it is linear by `coadjoint_smul_real`. -/
instance : DistribMulAction (GalileanGroup 3) GalileanTorsor where
  smul_zero a := ext_pair fun Z => by rw [coadjoint_pair, pair_zero, pair_zero]
  smul_add a μ ν := ext_pair fun Z => by
    rw [coadjoint_pair, pair_add, pair_add, coadjoint_pair, coadjoint_pair]

/-- The coadjoint action commutes with the real scalar multiplication: it is a linear
representation, as in (11.14)-(11.15). -/
lemma coadjoint_smul_real (a : GalileanGroup 3) (k : ℝ) (μ : GalileanTorsor) :
    a • (k • μ) = k • (a • μ) :=
  ext_pair fun Z => by rw [coadjoint_pair, pair_smul, pair_smul, coadjoint_pair]

end GalileanTorsor

/-!

## E. The cocycle `θ₀` and the mass

-/

/-- Souriau's cocycle `θ₀(a) = {c × b, c - b e, b, ½ ‖b‖²}` of the Galilean group (12.127), for
`a = (R, b, c, e)`. -/
def massCocycle (a : GalileanGroup 3) : GalileanTorsor :=
  ⟨WithLp.ofLp a.spaceTranslation ⨯₃ WithLp.ofLp a.velocity,
    WithLp.ofLp a.spaceTranslation - a.timeTranslation.val • WithLp.ofLp a.velocity,
    WithLp.ofLp a.velocity, (1 / 2 : ℝ) * (WithLp.ofLp a.velocity ⬝ᵥ WithLp.ofLp a.velocity)⟩

/-- `θ₀(1) = 0`. -/
lemma massCocycle_one : massCocycle 1 = 0 := by
  apply GalileanTorsor.ext_pair
  intro Z
  rw [GalileanTorsor.pair_zero]
  simp [massCocycle, GalileanTorsor.pair]

/-- (12.128): `θ₀` satisfies the cocycle identity (11.19 ♡) for the coadjoint action,
`θ₀(a a') = a • θ₀(a') + θ₀(a)` (`groupCohomology.IsCocycle₁`). The differentiability also
required by (11.19) is not part of this statement. -/
lemma isCocycle₁_massCocycle : groupCohomology.IsCocycle₁ massCocycle := by
  intro a a'
  refine GalileanTorsor.ext_pair fun Z => ?_
  rw [GalileanTorsor.pair_add, GalileanTorsor.coadjoint_pair, GalileanAlgebra.inv_smul_eq]
  have hE : WithLp.ofLp a'.velocity ⬝ᵥ WithLp.ofLp a'.velocity
      = (a.rotation.1 *ᵥ WithLp.ofLp a'.velocity) ⬝ᵥ (a.rotation.1 *ᵥ WithLp.ofLp a'.velocity) :=
    (orthogonal_mulVec_dotProduct _ _ _).symm
  change (WithLp.ofLp (a * a').spaceTranslation ⨯₃ WithLp.ofLp (a * a').velocity) ⬝ᵥ Z.ω
      - (WithLp.ofLp (a * a').spaceTranslation
        - (a * a').timeTranslation.val • WithLp.ofLp (a * a').velocity) ⬝ᵥ Z.β
      + WithLp.ofLp (a * a').velocity ⬝ᵥ Z.γ
      - (1 / 2 : ℝ) * (WithLp.ofLp (a * a').velocity ⬝ᵥ WithLp.ofLp (a * a').velocity) * Z.ε
    = ((WithLp.ofLp a'.spaceTranslation ⨯₃ WithLp.ofLp a'.velocity)
        ⬝ᵥ (a.rotation.1.det • (a.rotation.1ᵀ *ᵥ Z.ω))
      - (WithLp.ofLp a'.spaceTranslation - a'.timeTranslation.val • WithLp.ofLp a'.velocity)
        ⬝ᵥ (a.rotation.1ᵀ *ᵥ (Z.β + Z.ω ⨯₃ WithLp.ofLp a.velocity))
      + WithLp.ofLp a'.velocity ⬝ᵥ (a.rotation.1ᵀ *ᵥ (Z.γ - Z.ε • WithLp.ofLp a.velocity
        + a.timeTranslation.val • Z.β + Z.ω ⨯₃ WithLp.ofLp a.spaceTranslation))
      - (1 / 2 : ℝ) * (WithLp.ofLp a'.velocity ⬝ᵥ WithLp.ofLp a'.velocity) * Z.ε)
      + ((WithLp.ofLp a.spaceTranslation ⨯₃ WithLp.ofLp a.velocity) ⬝ᵥ Z.ω
      - (WithLp.ofLp a.spaceTranslation - a.timeTranslation.val • WithLp.ofLp a.velocity) ⬝ᵥ Z.β
      + WithLp.ofLp a.velocity ⬝ᵥ Z.γ
      - (1 / 2 : ℝ) * (WithLp.ofLp a.velocity ⬝ᵥ WithLp.ofLp a.velocity) * Z.ε)
  rw [cross_dotProduct_det_smul_transpose_mulVec, dotProduct_transpose_mulVec,
    dotProduct_transpose_mulVec, hE, Matrix.mulVec_sub, Matrix.mulVec_smul]
  simp only [GalileanGroup.mul_velocity, GalileanGroup.mul_spaceTranslation,
    GalileanGroup.mul_timeTranslation, Time.add_val, WithLp.ofLp_add, ofLp_orthogonal_smul,
    ofLp_real_smul]
  generalize a.rotation.1 *ᵥ WithLp.ofLp a'.velocity = B'
  generalize a.rotation.1 *ᵥ WithLp.ofLp a'.spaceTranslation = C'
  generalize WithLp.ofLp a.velocity = b
  generalize WithLp.ofLp a.spaceTranslation = c
  simp only [dotProduct, Fin.sum_univ_three, cross_apply, Pi.add_apply, Pi.sub_apply,
    Pi.smul_apply, smul_eq_mul, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  ring

/-- The witness of p. 151: if `a • μ₀ - μ₀ = M θ₀(a)` for the pure boost `a = (1, e₁, 0, 0)`,
then `M = 0`. This boost has `R = 1`, so it lies in Souriau's group `properGalileanGroup`. -/
lemma eq_zero_of_smul_massCocycle_boost (M : ℝ) (μ₀ : GalileanTorsor)
    (h : (⟨1, WithLp.toLp 2 ![1, 0, 0], 0, 0⟩ : GalileanGroup 3) • μ₀ - μ₀
      = M • massCocycle ⟨1, WithLp.toLp 2 ![1, 0, 0], 0, 0⟩) : M = 0 := by
  have hZ : (⟨1, WithLp.toLp 2 ![1, 0, 0], 0, 0⟩ : GalileanGroup 3)⁻¹ •
      (⟨0, 0, ![1, 0, 0], 0⟩ : GalileanAlgebra) = ⟨0, 0, ![1, 0, 0], 0⟩ := by
    rw [GalileanAlgebra.inv_smul_eq]
    apply GalileanAlgebra.ext <;> simp [Time.zero_val]
  have hθ : (massCocycle ⟨1, WithLp.toLp 2 ![1, 0, 0], 0, 0⟩).pair ⟨0, 0, ![1, 0, 0], 0⟩ = 1 := by
    simp [massCocycle, GalileanTorsor.pair, Time.zero_val]
  have h1 := congrArg (fun μ => μ.pair ⟨0, 0, ![1, 0, 0], 0⟩) h
  simp only [GalileanTorsor.pair_sub, GalileanTorsor.coadjoint_pair, hZ, sub_self,
    GalileanTorsor.pair_smul, hθ, mul_one] at h1
  exact h1.symm

/-- `M θ₀` is a coboundary of Physlib's Galilean group (rotations in `O(3)`),
`M θ₀(a) = a • μ₀ - μ₀` for some torsor `μ₀` (11.19 ◇), if and only if `M = 0`. For Souriau's
group (12.73) see `isCoboundary₁_smul_massCocycle_proper_iff`, which this lemma does not
imply. -/
lemma isCoboundary₁_smul_massCocycle_iff (M : ℝ) :
    groupCohomology.IsCoboundary₁ (fun a : GalileanGroup 3 => M • massCocycle a) ↔ M = 0 := by
  constructor
  · rintro ⟨μ₀, h⟩
    exact eq_zero_of_smul_massCocycle_boost M μ₀ (h _)
  · rintro rfl
    exact ⟨0, fun a => by simp⟩

/-- `θ₀` is not a coboundary of Physlib's Galilean group (rotations in `O(3)`). Souriau's
statement (p. 151) is on his group (12.73) and is `not_isCoboundary₁_massCocycle_proper`; it is
not implied by this one. -/
lemma not_isCoboundary₁_massCocycle : ¬ groupCohomology.IsCoboundary₁ massCocycle := by
  intro h
  refine one_ne_zero ((isCoboundary₁_smul_massCocycle_iff 1).mp ?_)
  simpa using h

/-- Souriau's Galilean group (12.73): the elements of `GalileanGroup 3` whose rotation part has
determinant `1`, that is `R ∈ SO(3)`. -/
def properGalileanGroup : Subgroup (GalileanGroup 3) where
  carrier := {a | a.rotation.1.det = 1}
  mul_mem' {a b} ha hb := by
    change a.rotation.1.det = 1 at ha
    change b.rotation.1.det = 1 at hb
    change (a.rotation.1 * b.rotation.1).det = 1
    rw [Matrix.det_mul, ha, hb, mul_one]
  one_mem' := by
    change (1 : GalileanGroup 3).rotation.1.det = 1
    simp
  inv_mem' {a} ha := by
    change a.rotation.1.det = 1 at ha
    change (a.rotation⁻¹).1.det = 1
    rw [orthogonal_det_inv, ha]

/-- (12.128) on Souriau's group (12.73): the restriction of `θ₀` to `properGalileanGroup` satisfies
the cocycle identity (11.19 ♡). -/
lemma isCocycle₁_massCocycle_proper :
    groupCohomology.IsCocycle₁ (fun a : properGalileanGroup => massCocycle a) :=
  fun a a' => isCocycle₁_massCocycle a a'

/-- p. 151 on Souriau's group (12.73): `M θ₀` is a coboundary of `properGalileanGroup`,
`M θ₀(a) = a • μ₀ - μ₀` for some torsor `μ₀` (11.19 ◇), if and only if `M = 0`. -/
lemma isCoboundary₁_smul_massCocycle_proper_iff (M : ℝ) :
    groupCohomology.IsCoboundary₁ (fun a : properGalileanGroup => M • massCocycle a) ↔
      M = 0 := by
  constructor
  · rintro ⟨μ₀, h⟩
    refine eq_zero_of_smul_massCocycle_boost M μ₀
      (h ⟨⟨1, WithLp.toLp 2 ![1, 0, 0], 0, 0⟩, ?_⟩)
    change (1 : GalileanGroup 3).rotation.1.det = 1
    simp
  · rintro rfl
    exact ⟨0, fun a => by simp⟩

/-- p. 151 on Souriau's group (12.73): `θ₀` is not a coboundary of `properGalileanGroup`, so it
defines a non-zero cohomology class of Souriau's Galilean group. -/
lemma not_isCoboundary₁_massCocycle_proper :
    ¬ groupCohomology.IsCoboundary₁ (fun a : properGalileanGroup => massCocycle a) := by
  intro h
  refine one_ne_zero ((isCoboundary₁_smul_massCocycle_proper_iff 1).mp ?_)
  simpa using h

namespace EvolutionSpace

variable {N : ℕ}

/-- (12.126)-(12.127) for `N` points: with the moment of `GalileanMass` (additive constant zero)
and `m = Σ_j m_j` (12.135), `μ(a • y) - a • μ(y) = m θ₀(a)`, independently of `y`. Souriau
prints (12.126) for one point of unit mass; for `N` points this is (12.132) with `μ₀ = 0`. -/
lemma moment_smul_sub (m : Fin N → ℝ) (a : GalileanGroup 3) (y : EvolutionSpace N) :
    moment m (a • y) - a • moment m y = totalMass m • massCocycle a := by
  refine GalileanTorsor.ext_pair fun Z => ?_
  rw [GalileanTorsor.pair_sub, GalileanTorsor.coadjoint_pair, GalileanTorsor.pair_smul,
    GalileanAlgebra.inv_smul_eq, pair_moment, pair_moment, totalMass, Finset.sum_mul,
    ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← mul_sub]
  congr 1
  have hE : y.v j ⬝ᵥ y.v j = (a.rotation.1 *ᵥ y.v j) ⬝ᵥ (a.rotation.1 *ᵥ y.v j) :=
    (orthogonal_mulVec_dotProduct _ _ _).symm
  simp only [smul_r, smul_v, smul_t, massCocycle, GalileanTorsor.pair]
  rw [cross_dotProduct_det_smul_transpose_mulVec, dotProduct_transpose_mulVec,
    dotProduct_transpose_mulVec, hE, Matrix.mulVec_sub, Matrix.mulVec_smul]
  generalize a.rotation.1 *ᵥ y.r j = X
  generalize a.rotation.1 *ᵥ y.v j = Y
  generalize WithLp.ofLp a.velocity = b
  generalize WithLp.ofLp a.spaceTranslation = c
  simp only [dotProduct, Fin.sum_univ_three, cross_apply, Pi.add_apply, Pi.sub_apply,
    Pi.smul_apply, smul_eq_mul, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  ring

/-- (12.132) and (12.136) at the level of the group, on Physlib's Galilean group (rotations in
`O(3)`): for a non-zero total mass, the cocycle `a ↦ μ(a • y) - a • μ(y)` of the system is not a
coboundary. For Souriau's group (12.73) see `not_isCoboundary₁_moment_smul_sub_proper`, which this
lemma does not imply. -/
lemma not_isCoboundary₁_moment_smul_sub (m : Fin N → ℝ) (hM : totalMass m ≠ 0)
    (y : EvolutionSpace N) :
    ¬ groupCohomology.IsCoboundary₁
      (fun a : GalileanGroup 3 => moment m (a • y) - a • moment m y) := by
  simp_rw [moment_smul_sub]
  rw [isCoboundary₁_smul_massCocycle_iff]
  exact hM

/-- (12.132) and (12.136) at the level of the group, on Souriau's group (12.73): for a non-zero
total mass, the cocycle `a ↦ μ(a • y) - a • μ(y)` of the system, restricted to
`properGalileanGroup`, is not a coboundary. -/
lemma not_isCoboundary₁_moment_smul_sub_proper (m : Fin N → ℝ) (hM : totalMass m ≠ 0)
    (y : EvolutionSpace N) :
    ¬ groupCohomology.IsCoboundary₁
      (fun a : properGalileanGroup => moment m (a • y) - a • moment m y) := by
  simp_rw [Subgroup.smul_def, moment_smul_sub]
  rw [isCoboundary₁_smul_massCocycle_proper_iff]
  exact hM

end EvolutionSpace

/-!

## F. The derivative of `θ₀` at the identity

-/

/-- Product rule for the dot product of two curves in `ℝ³`. -/
private lemma hasDerivAt_dotProduct {u v : ℝ → ℝ³} {u' v' : ℝ³} {x : ℝ} (hu : HasDerivAt u u' x)
    (hv : HasDerivAt v v' x) : HasDerivAt (fun s => u s ⬝ᵥ v s) (u' ⬝ᵥ v x + u x ⬝ᵥ v') x := by
  have h := HasDerivAt.fun_sum (u := Finset.univ)
    (fun i _ => ((hasDerivAt_pi.1 hu) i).fun_mul ((hasDerivAt_pi.1 hv) i))
  refine h.congr_deriv ?_
  simp only [dotProduct, Finset.sum_add_distrib]

/-- Product rule for the cross product of two curves in `ℝ³`. -/
private lemma hasDerivAt_cross {u v : ℝ → ℝ³} {u' v' : ℝ³} {x : ℝ} (hu : HasDerivAt u u' x)
    (hv : HasDerivAt v v' x) : HasDerivAt (fun s => u s ⨯₃ v s) (u' ⨯₃ v x + u x ⨯₃ v') x := by
  have hu' := hasDerivAt_pi.1 hu
  have hv' := hasDerivAt_pi.1 hv
  refine hasDerivAt_pi.2 fun i => ?_
  fin_cases i
  · convert ((hu' 1).fun_mul (hv' 2)).fun_sub ((hu' 2).fun_mul (hv' 1)) using 1
    · funext t
      simp [cross_apply]
    · simp [cross_apply]
      ring
  · convert ((hu' 2).fun_mul (hv' 0)).fun_sub ((hu' 0).fun_mul (hv' 2)) using 1
    · funext t
      simp [cross_apply]
    · simp [cross_apply]
      ring
  · convert ((hu' 0).fun_mul (hv' 1)).fun_sub ((hu' 1).fun_mul (hv' 0)) using 1
    · funext t
      simp [cross_apply]
    · simp [cross_apply]
      ring

/-- (12.130), `f₀ = D(θ₀)(e)`: along a curve `s ↦ γ s` of the Galilean group through the identity
whose velocity, space translation and time translation are differentiable at `0`, with derivatives
`b'`, `c'` and `e'`, the derivative at `0` of `s ↦ θ₀(γ s)(Z)` is `f₀(Z')(Z)` with
`Z' = (0, b', c', 0)`. It depends neither on the rotation part of the curve nor on `e'`. -/
lemma hasDerivAt_massCocycle (γ : ℝ → GalileanGroup 3) (hγ : γ 0 = 1)
    {b' c' : EuclideanSpace ℝ (Fin 3)} {e' : ℝ} (hb : HasDerivAt (fun s => (γ s).velocity) b' 0)
    (hc : HasDerivAt (fun s => (γ s).spaceTranslation) c' 0)
    (he : HasDerivAt (fun s => (γ s).timeTranslation.val) e' 0) (Z : GalileanAlgebra) :
    HasDerivAt (fun s => (massCocycle (γ s)).pair Z)
      (GalileanAlgebra.cocycle ⟨0, WithLp.ofLp b', WithLp.ofLp c', 0⟩ Z) 0 := by
  have hb' : HasDerivAt (fun s => WithLp.ofLp (γ s).velocity) (WithLp.ofLp b') 0 :=
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).hasFDerivAt.comp_hasDerivAt 0 hb
  have hc' : HasDerivAt (fun s => WithLp.ofLp (γ s).spaceTranslation) (WithLp.ofLp c') 0 :=
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).hasFDerivAt.comp_hasDerivAt 0 hc
  have h0b : WithLp.ofLp (γ 0).velocity = 0 := by rw [hγ]; rfl
  have h0c : WithLp.ofLp (γ 0).spaceTranslation = 0 := by rw [hγ]; rfl
  have h0e : (γ 0).timeTranslation.val = 0 := by rw [hγ]; exact Time.zero_val
  have h1 := hasDerivAt_dotProduct (hasDerivAt_cross hc' hb') (hasDerivAt_const (0 : ℝ) Z.ω)
  have h2 := hasDerivAt_dotProduct (hc'.fun_sub (he.fun_smul hb')) (hasDerivAt_const (0 : ℝ) Z.β)
  have h3 := hasDerivAt_dotProduct hb' (hasDerivAt_const (0 : ℝ) Z.γ)
  have h4 := ((hasDerivAt_dotProduct hb' hb').const_mul (1 / 2 : ℝ)).mul_const Z.ε
  refine (((h1.fun_sub h2).fun_add h3).fun_sub h4).congr_deriv ?_
  simp only [GalileanAlgebra.cocycle, h0b, h0c, h0e, map_zero, LinearMap.zero_apply, add_zero,
    zero_smul, smul_zero, sub_zero, dotProduct_zero, zero_dotProduct, mul_zero, zero_mul]
  rw [dotProduct_comm Z.β]
  ring

/-- (12.130) along the curve `s ↦ (1, s b', s c', s e')`, which satisfies the hypotheses of
`hasDerivAt_massCocycle`. -/
lemma hasDerivAt_massCocycle_line (b' c' : EuclideanSpace ℝ (Fin 3)) (e' : ℝ)
    (Z : GalileanAlgebra) :
    HasDerivAt (fun s : ℝ => (massCocycle ⟨1, s • b', s • c', ⟨s * e'⟩⟩).pair Z)
      (GalileanAlgebra.cocycle ⟨0, WithLp.ofLp b', WithLp.ofLp c', 0⟩ Z) 0 := by
  refine hasDerivAt_massCocycle (fun s => ⟨1, s • b', s • c', ⟨s * e'⟩⟩) ?_ (b' := b') (c' := c')
    (e' := e') ?_ ?_ ?_ Z
  · refine GalileanGroup.ext rfl (zero_smul ℝ b') (zero_smul ℝ c') ?_
    exact Time.ext (by simp [Time.zero_val])
  · simpa using (hasDerivAt_id (0 : ℝ)).smul_const b'
  · simpa using (hasDerivAt_id (0 : ℝ)).smul_const c'
  · simpa using (hasDerivAt_id (0 : ℝ)).mul_const e'

end ClassicalMechanics
