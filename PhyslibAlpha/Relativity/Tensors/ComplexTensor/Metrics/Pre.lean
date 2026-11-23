/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Relativity.LorentzGroup.Boosts.Axis
public import Physlib.Relativity.Tensors.ComplexTensor.Metrics.Pre
public import PhyslibAlpha.Mathematics.RepresentationTheory.Invariants
public import PhyslibAlpha.Relativity.SL2C.AxisRotations
/-!
# The metrics are the unique invariants

Up to scale, the Minkowski metric is the only invariant of two complex Lorentz vector indices.

## i. Overview

On `ComplexVector ⊗ ComplexVector` the group `SL(2, ℂ)` acts on the matrix of components by
`Y ↦ Λ Y Λᵀ`, with `Λ` the complexified Lorentz matrix. The complexified Minkowski matrix `η`
squares to the identity and gives `Λ⁻¹ = η Λᵀ η` (A), so the other orderings of upper and lower
indices reduce to this action after multiplying by `η`.

Let `F` be a linear map out of the matrices which intertwines `Y ↦ Λ Y Λᵀ` with an action on `B`,
and let `F X` be invariant (B). The three half turns act by diagonal sign matrices, and averaging
over them keeps only the diagonal, so `F X` is the image of the diagonal of `X` (B.1). For a
diagonal `D` the boost along the axis `i` changes only the time and `i` entries of the diagonal,
by a multiple of `d_t + d_i`, so `(d_t + d_i) • F P_i = 0`, where `P_i` projects onto the plane
of time and the axis `i` (B.2). The cyclic rotation of the axes carries `P_i` to `P_{i+1}`, so
the three `F P_i` vanish together (B.3). If they vanish, `F D` and `F η` are both multiples of
the image of the time projection, and otherwise `D` is a multiple of `η`. Either way `F X` is a
multiple of `F η` (B.4).

The result follows for any tensor product whose matrix of components carries this action (C).
On two contravariant indices the invariants of the tensor product are the line through the metric
(D). The same holds for two covariant indices, through the matrix of components conjugated by `η`
(E).

## ii. Key results

- `Lorentz.map_eq_smul_map_minkowskiMatrix_of_invariant` : on matrices with the action
  `Y ↦ Λ Y Λᵀ`, an invariant in the image of an equivariant map is a multiple of the image of `η`.
- `Lorentz.ComplexVector.invariants_tprod_eq_span_metricVal` : the invariants of
  `ComplexVector ⊗ ComplexVector` are the line through the metric.
- `Lorentz.ComplexCoVector.invariants_tprod_eq_span_metricVal` : the same for
  `ComplexCoVector ⊗ ComplexCoVector`.

## iii. Table of contents

- A. The complexified Minkowski matrix
- B. Invariants in the image of an equivariant map on matrices
  - B.1. The diagonal part
  - B.2. Boosts
  - B.3. Cycling the axes
  - B.4. Invariants are multiples of the image of the metric
- C. Tensor products with a matrix of components
- D. Two contravariant indices
- E. Two covariant indices

## iv. References

The metrics are in `Physlib.Relativity.Tensors.ComplexTensor.Metrics.Pre`, where these results are
written to move, and sections D and E settle the `TODO` in that file on the uniqueness of the
metrics. The matrices of components are in `Physlib.Relativity.Tensors.ComplexTensor.Matrix.Pre`,
the half turns and the cyclic rotation in `PhyslibAlpha.Relativity.SL2C.AxisRotations`, and the
axis boosts in `Physlib.Relativity.LorentzGroup.Boosts.Axis`. The analogous results for two Weyl
indices are in `PhyslibAlpha.Relativity.Fermions.Weyl.Metric`.

-/

@[expose] public section

noncomputable section

open Module Matrix MatrixGroups Complex TensorProduct

/-!

## A. The complexified Minkowski matrix

-/

namespace LorentzGroup

variable {d : ℕ}

/-- The complexified Minkowski matrix squares to the identity. -/
lemma minkowskiMatrix_map_mul_self :
    (@minkowskiMatrix d).map ofRealHom * (@minkowskiMatrix d).map ofRealHom = 1 := by
  rw [← Matrix.map_mul, minkowskiMatrix.sq, Matrix.map_one _ (map_zero _) (map_one _)]

/-- Multiplying twice by the complexified Minkowski matrix is the identity. -/
lemma minkowskiMatrix_map_mul_minkowskiMatrix_map_mul
    (X : Matrix (Fin 1 ⊕ Fin d) (Fin 1 ⊕ Fin d) ℂ) :
    (@minkowskiMatrix d).map ofRealHom * ((@minkowskiMatrix d).map ofRealHom * X) = X := by
  rw [← Matrix.mul_assoc, minkowskiMatrix_map_mul_self, Matrix.one_mul]

/-- The complexified Minkowski matrix is symmetric. -/
lemma transpose_minkowskiMatrix_map :
    ((@minkowskiMatrix d).map ofRealHom)ᵀ = (@minkowskiMatrix d).map ofRealHom := by
  rw [← Matrix.transpose_map, minkowskiMatrix.eq_transpose]

/-- The inverse of a complexified Lorentz matrix is `η Λᵀ η`. -/
lemma inv_toComplex (Λ : LorentzGroup d) : (toComplex Λ)⁻¹ =
    minkowskiMatrix.map ofRealHom * (toComplex Λ)ᵀ * minkowskiMatrix.map ofRealHom := by
  refine Matrix.inv_eq_left_inv ?_
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (toComplex Λ)ᵀ, toComplex_transpose_mul_minkowskiMatrix_mul_self,
    minkowskiMatrix_map_mul_self]

/-- Moving `Λ⁻¹` across `η` turns it into `Λᵀ`. -/
lemma minkowskiMatrix_map_mul_inv_toComplex (Λ : LorentzGroup d) :
    minkowskiMatrix.map ofRealHom * (toComplex Λ)⁻¹ =
      (toComplex Λ)ᵀ * minkowskiMatrix.map ofRealHom := by
  rw [inv_toComplex]
  simp only [← Matrix.mul_assoc, minkowskiMatrix_map_mul_self, Matrix.one_mul]

/-- Moving `Λ⁻¹ᵀ` across `η` turns it into `Λ`. -/
lemma inv_toComplex_transpose_mul_minkowskiMatrix_map (Λ : LorentzGroup d) :
    (toComplex Λ)⁻¹ᵀ * minkowskiMatrix.map ofRealHom =
      minkowskiMatrix.map ofRealHom * toComplex Λ := by
  rw [inv_toComplex]
  simp only [Matrix.transpose_mul, transpose_minkowskiMatrix_map, Matrix.transpose_transpose,
    Matrix.mul_assoc, minkowskiMatrix_map_mul_self, Matrix.mul_one]

/-- Conjugating by `η` turns the action `X ↦ Λ⁻¹ᵀ X Λ⁻¹` on two covariant indices into the
  action `Y ↦ Λ Y Λᵀ` on two contravariant indices. -/
lemma inv_toComplex_transpose_mul_conj_minkowskiMatrix_map (Λ : LorentzGroup d)
    (Y : Matrix (Fin 1 ⊕ Fin d) (Fin 1 ⊕ Fin d) ℂ) :
    (toComplex Λ)⁻¹ᵀ * (minkowskiMatrix.map ofRealHom * Y * minkowskiMatrix.map ofRealHom) *
      (toComplex Λ)⁻¹ = minkowskiMatrix.map ofRealHom * (toComplex Λ * Y * (toComplex Λ)ᵀ) *
      minkowskiMatrix.map ofRealHom := by
  calc _ = ((toComplex Λ)⁻¹ᵀ * minkowskiMatrix.map ofRealHom) * Y *
        (minkowskiMatrix.map ofRealHom * (toComplex Λ)⁻¹) := by simp only [Matrix.mul_assoc]
    _ = _ := by
      rw [inv_toComplex_transpose_mul_minkowskiMatrix_map, minkowskiMatrix_map_mul_inv_toComplex]
      simp only [Matrix.mul_assoc]

end LorentzGroup

namespace Lorentz

/-!

## B. Invariants in the image of an equivariant map on matrices

Throughout, `F` is a linear map out of the `4 × 4` complex matrices with
`F (Λ Y Λᵀ) = ρ g (F Y)`, where `Λ` is the complexified Lorentz matrix of `g`.

-/

section MatrixInvariants

variable {B : Type*} [AddCommGroup B] [Module ℂ B] {ρ : Representation ℂ SL(2,ℂ) B}
  {F : Matrix (Fin 1 ⊕ Fin 3) (Fin 1 ⊕ Fin 3) ℂ →ₗ[ℂ] B}

/-!

### B.1. The diagonal part

-/

/-- The complexified Lorentz matrix of the half turn about the axis `k` is the diagonal matrix of
  the signs `halfTurnSign k`. -/
lemma toComplex_toLorentzGroup_halfTurn (k : Fin 3) :
    LorentzGroup.toComplex (SL2C.toLorentzGroup (SL2C.halfTurn k)) =
      diagonal fun μ => (halfTurnSign k μ : ℂ) := by
  ext a b
  simp only [LorentzGroup.toComplex, MonoidHom.coe_mk, OneHom.coe_mk, map_apply,
    SL2C.toLorentzGroup_halfTurn_apply, diagonal_apply]
  split_ifs <;> simp

/-- Adding a matrix to its conjugates by the three half turns keeps four times its diagonal. -/
lemma add_sum_halfTurnSign_conj (Y : Matrix (Fin 1 ⊕ Fin 3) (Fin 1 ⊕ Fin 3) ℂ) :
    Y + ∑ k, diagonal (fun μ => (halfTurnSign k μ : ℂ)) * Y *
      (diagonal fun μ => (halfTurnSign k μ : ℂ))ᵀ = (4 : ℂ) • diagonal fun μ => Y μ μ := by
  ext a b
  simp only [Matrix.add_apply, Matrix.sum_apply, diagonal_transpose, mul_diagonal, diagonal_mul,
    Matrix.smul_apply, diagonal_apply]
  rcases a with a | a <;> rcases b with b | b <;> fin_cases a <;> fin_cases b <;>
    simp [Fin.sum_univ_three, halfTurnSign] <;> ring

/-- When `F Y` is invariant, it is the image of the diagonal of `Y`. -/
lemma map_eq_map_diagonal_of_invariant
    (hF : ∀ g Y, F (LorentzGroup.toComplex (SL2C.toLorentzGroup g) * Y *
      (LorentzGroup.toComplex (SL2C.toLorentzGroup g))ᵀ) = ρ g (F Y))
    {Y : Matrix (Fin 1 ⊕ Fin 3) (Fin 1 ⊕ Fin 3) ℂ} (hY : ∀ g, ρ g (F Y) = F Y) :
    F Y = F (diagonal fun μ => Y μ μ) := by
  have h (k : Fin 3) : F (diagonal (fun μ => (halfTurnSign k μ : ℂ)) * Y *
      (diagonal fun μ => (halfTurnSign k μ : ℂ))ᵀ) = F Y := by
    rw [← toComplex_toLorentzGroup_halfTurn, hF, hY]
  have h4 := congrArg F (add_sum_halfTurnSign_conj Y)
  simp only [map_add, map_sum, map_smul, h, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin] at h4
  refine smul_right_injective B (by norm_num : (4 : ℂ) ≠ 0) ?_
  simp only [← h4]
  module

/-!

### B.2. Boosts

-/

/-- The projection onto the plane of time and the axis `i`, the diagonal matrix with `1` in the
  time and `i` slots and `0` in the other two. -/
def timeAxisProj (i : Fin 3) : Matrix (Fin 1 ⊕ Fin 3) (Fin 1 ⊕ Fin 3) ℂ :=
  diagonal fun μ => if μ = Sum.inl 0 ∨ μ = Sum.inr i then 1 else 0

/-- The boost along the axis `i` with parameter `2` changes the diagonal of a diagonal matrix
  `diagonal d` only in the time and `i` slots, by `(225 / 64) (d_t + d_i)`. -/
lemma diagonal_boost_conj_sub (i : Fin 3) (d : Fin 1 ⊕ Fin 3 → ℂ) :
    (diagonal fun μ => (LorentzGroup.toComplex (SL2C.toLorentzGroup
      (SL2C.boostAxis i 2 two_ne_zero)) * diagonal d * (LorentzGroup.toComplex
      (SL2C.toLorentzGroup (SL2C.boostAxis i 2 two_ne_zero)))ᵀ) μ μ) - diagonal d =
      ((225 / 64 : ℂ) * (d (Sum.inl 0) + d (Sum.inr i))) • timeAxisProj i := by
  have h (a b) : (SL2C.toLorentzGroup (SL2C.boostAxis i 2 two_ne_zero)).1 a b =
      (LorentzGroup.boostAxis i 2 two_ne_zero).1 a b := rfl
  ext a b
  by_cases hab : a = b
  · subst hab
    simp only [Matrix.sub_apply, Matrix.smul_apply, diagonal_apply_eq, timeAxisProj,
      Matrix.mul_apply, transpose_apply, LorentzGroup.toComplex, MonoidHom.coe_mk, OneHom.coe_mk,
      map_apply, h, LorentzGroup.boostAxis_apply]
    fin_cases i <;> rcases a with a | a <;> fin_cases a <;>
      simp [Fintype.sum_sum_type, Fin.sum_univ_three] <;> ring
  · simp [timeAxisProj, diagonal_apply_ne _ hab]

/-- When `F (diagonal d)` is invariant, `d_t + d_i` kills the image of the projection onto the
  plane of time and the axis `i`. -/
lemma add_smul_map_timeAxisProj_eq_zero
    (hF : ∀ g Y, F (LorentzGroup.toComplex (SL2C.toLorentzGroup g) * Y *
      (LorentzGroup.toComplex (SL2C.toLorentzGroup g))ᵀ) = ρ g (F Y))
    {d : Fin 1 ⊕ Fin 3 → ℂ} (hd : ∀ g, ρ g (F (diagonal d)) = F (diagonal d)) (i : Fin 3) :
    (d (Sum.inl 0) + d (Sum.inr i)) • F (timeAxisProj i) = 0 := by
  have h1 := (hF (SL2C.boostAxis i 2 two_ne_zero) (diagonal d)).trans (hd _)
  have h2 := map_eq_map_diagonal_of_invariant hF (fun g => by rw [h1]; exact hd g)
  have h3 := congrArg F (diagonal_boost_conj_sub i d)
  rw [map_sub, ← h2, h1, sub_self, map_smul, ← smul_smul] at h3
  exact (smul_eq_zero.1 h3.symm).resolve_left (by norm_num)

/-!

### B.3. Cycling the axes

-/

/-- The cyclic rotation of the axes carries the projection onto the plane of time and the axis
  `i` to that of the axis `i + 1`. -/
lemma rotationCycle_conj_timeAxisProj (i : Fin 3) :
    LorentzGroup.toComplex (SL2C.toLorentzGroup SL2C.rotationCycle) * timeAxisProj i *
      (LorentzGroup.toComplex (SL2C.toLorentzGroup SL2C.rotationCycle))ᵀ =
      timeAxisProj (i + 1) := by
  ext a b
  simp only [timeAxisProj, Matrix.mul_apply, transpose_apply, LorentzGroup.toComplex,
    MonoidHom.coe_mk, OneHom.coe_mk, map_apply, SL2C.toLorentzGroup_rotationCycle_apply,
    diagonal_apply]
  fin_cases i <;> rcases a with a | a <;> rcases b with b | b <;> fin_cases a <;> fin_cases b <;>
    simp [Fintype.sum_sum_type, cycDir]

/-- The images of the projections onto the three planes of time and an axis vanish together. -/
lemma map_timeAxisProj_eq_zero_of_eq_zero
    (hF : ∀ g Y, F (LorentzGroup.toComplex (SL2C.toLorentzGroup g) * Y *
      (LorentzGroup.toComplex (SL2C.toLorentzGroup g))ᵀ) = ρ g (F Y))
    {i : Fin 3} (h : F (timeAxisProj i) = 0) (j : Fin 3) : F (timeAxisProj j) = 0 := by
  have hstep (i : Fin 3) (h : F (timeAxisProj i) = 0) : F (timeAxisProj (i + 1)) = 0 := by
    rw [← rotationCycle_conj_timeAxisProj, hF, h, map_zero]
  have h1 := hstep _ h
  have h2 := hstep _ h1
  fin_cases i <;> fin_cases j <;> first | exact h | exact h1 | exact h2

/-!

### B.4. Invariants are multiples of the image of the metric

-/

/-- A diagonal matrix in terms of the time projection and the projections onto the planes of
  time and an axis. -/
lemma diagonal_eq_sum_timeAxisProj (d : Fin 1 ⊕ Fin 3 → ℂ) :
    diagonal d = (d (Sum.inl 0) - ∑ i, d (Sum.inr i)) • diagonal (Pi.single (Sum.inl 0) 1) +
      ∑ i, d (Sum.inr i) • timeAxisProj i := by
  ext a b
  rcases a with a | a <;> rcases b with b | b <;> fin_cases a <;> fin_cases b <;>
    simp [timeAxisProj, Fin.sum_univ_three]

/-- The complexified Minkowski matrix in terms of the time projection and the projections onto
  the planes of time and an axis. -/
lemma minkowskiMatrix_map_eq_sum_timeAxisProj :
    minkowskiMatrix.map ofRealHom =
      (4 : ℂ) • diagonal (Pi.single (Sum.inl 0) 1) - ∑ i, timeAxisProj i := by
  ext a b
  rcases a with a | a <;> rcases b with b | b <;> fin_cases a <;> fin_cases b <;>
    norm_num [timeAxisProj, Fin.sum_univ_three, minkowskiMatrix.as_diagonal]

/-- A diagonal matrix with `d_t + d_i = 0` for each axis `i` is `d_t η`. -/
lemma diagonal_eq_smul_minkowskiMatrix_map {d : Fin 1 ⊕ Fin 3 → ℂ}
    (hd : ∀ i, d (Sum.inl 0) + d (Sum.inr i) = 0) :
    diagonal d = d (Sum.inl 0) • minkowskiMatrix.map ofRealHom := by
  ext a b
  rcases a with a | a <;> rcases b with b | b <;> fin_cases a <;> fin_cases b <;>
    simp [minkowskiMatrix.as_diagonal] <;> linear_combination hd _

/-- When `F (diagonal d)` is invariant, it is a multiple of `F η`. If the images of the
  projections onto the planes of time and an axis vanish, both are multiples of the image of the
  time projection, and otherwise `diagonal d` is a multiple of `η`. -/
lemma map_diagonal_eq_smul_of_invariant
    (hF : ∀ g Y, F (LorentzGroup.toComplex (SL2C.toLorentzGroup g) * Y *
      (LorentzGroup.toComplex (SL2C.toLorentzGroup g))ᵀ) = ρ g (F Y))
    {d : Fin 1 ⊕ Fin 3 → ℂ} (hd : ∀ g, ρ g (F (diagonal d)) = F (diagonal d)) :
    ∃ c : ℂ, F (diagonal d) = c • F (minkowskiMatrix.map ofRealHom) := by
  by_cases h0 : F (timeAxisProj 0) = 0
  · have hz := map_timeAxisProj_eq_zero_of_eq_zero hF h0
    refine ⟨(d (Sum.inl 0) - ∑ i, d (Sum.inr i)) / 4, ?_⟩
    rw [diagonal_eq_sum_timeAxisProj, minkowskiMatrix_map_eq_sum_timeAxisProj]
    simp only [map_add, map_sub, map_sum, map_smul, hz, smul_zero, Finset.sum_const_zero,
      add_zero, sub_zero, smul_smul]
    congr 1
    ring
  · have hs (i : Fin 3) : d (Sum.inl 0) + d (Sum.inr i) = 0 :=
      (smul_eq_zero.1 (add_smul_map_timeAxisProj_eq_zero hF hd i)).resolve_right
        fun h => h0 (map_timeAxisProj_eq_zero_of_eq_zero hF h 0)
    exact ⟨d (Sum.inl 0), by rw [diagonal_eq_smul_minkowskiMatrix_map hs, map_smul]⟩

/-- When `F X` is invariant, it is a multiple of the image `F η` of the complexified Minkowski
  matrix. -/
lemma map_eq_smul_map_minkowskiMatrix_of_invariant
    (hF : ∀ g Y, F (LorentzGroup.toComplex (SL2C.toLorentzGroup g) * Y *
      (LorentzGroup.toComplex (SL2C.toLorentzGroup g))ᵀ) = ρ g (F Y))
    {X : Matrix (Fin 1 ⊕ Fin 3) (Fin 1 ⊕ Fin 3) ℂ} (hX : ∀ g, ρ g (F X) = F X) :
    ∃ c : ℂ, F X = c • F (minkowskiMatrix.map ofRealHom) := by
  rw [map_eq_map_diagonal_of_invariant hF hX]
  exact map_diagonal_eq_smul_of_invariant hF fun g => by
    rw [← map_eq_map_diagonal_of_invariant hF hX, hX]

end MatrixInvariants

/-!

## C. Tensor products with a matrix of components

-/

section TensorInvariants

/-- Let `T` be a linear map from the matrices onto `V` which intertwines `Y ↦ Λ Y Λᵀ` with the
  action on `V`. The invariants of `V` are the line through `T η`. -/
lemma invariants_eq_span_map_minkowskiMatrix {V : Type*} [AddCommGroup V]
    [Module ℂ V] {σ : Representation ℂ SL(2,ℂ) V}
    (T : Matrix (Fin 1 ⊕ Fin 3) (Fin 1 ⊕ Fin 3) ℂ →ₗ[ℂ] V) (hT : Function.Surjective T)
    (hσ : ∀ g Y, T (LorentzGroup.toComplex (SL2C.toLorentzGroup g) * Y *
      (LorentzGroup.toComplex (SL2C.toLorentzGroup g))ᵀ) = σ g (T Y)) :
    σ.invariants = ℂ ∙ T (minkowskiMatrix.map ofRealHom) := by
  refine Representation.invariants_eq_span_singleton (fun g => ?_) fun v hv => ?_
  · rw [← hσ, LorentzGroup.toComplex_mul_minkowskiMatrix_mul_transpose]
  · obtain ⟨Y, rfl⟩ := hT v
    exact map_eq_smul_map_minkowskiMatrix_of_invariant (F := T) hσ (X := Y) hv

/-!

## D. Two contravariant indices

-/

/-- Up to scale, the metric `ηᵃᵃ` is the unique invariant of `ComplexVector ⊗ ComplexVector`. -/
lemma ComplexVector.invariants_tprod_eq_span_metricVal :
    (ComplexVector.SL2CRep.tprod ComplexVector.SL2CRep).invariants =
      ℂ ∙ ComplexVector.metricVal :=
  invariants_eq_span_map_minkowskiMatrix contrContrToMatrix.symm.toLinearMap
    contrContrToMatrix.symm.surjective fun g Y => by
      simp only [LinearEquiv.coe_coe, Representation.tprod_apply, contrContrToMatrix_ρ_symm]

/-!

## E. Two covariant indices

-/

/-- Up to scale, the metric `ηᵢᵢ` is the unique invariant of `ComplexCoVector ⊗ ComplexCoVector`. -/
lemma ComplexCoVector.invariants_tprod_eq_span_metricVal :
    (ComplexCoVector.SL2CRep.tprod ComplexCoVector.SL2CRep).invariants =
      ℂ ∙ ComplexCoVector.metricVal := by
  have h := invariants_eq_span_map_minkowskiMatrix
    (σ := ComplexCoVector.SL2CRep.tprod ComplexCoVector.SL2CRep)
    (coCoToMatrix.symm.toLinearMap ∘ₗ LinearMap.mulLeftRight ℂ
      (minkowskiMatrix.map ofRealHom, minkowskiMatrix.map ofRealHom))
    (fun v => ⟨minkowskiMatrix.map ofRealHom * coCoToMatrix v * minkowskiMatrix.map ofRealHom,
      by simp [Matrix.mul_assoc, LorentzGroup.minkowskiMatrix_map_mul_self,
        LorentzGroup.minkowskiMatrix_map_mul_minkowskiMatrix_map_mul]⟩)
    fun g Y => by
      simp only [LinearMap.comp_apply, LinearMap.mulLeftRight_apply, LinearEquiv.coe_coe,
        Representation.tprod_apply, coCoToMatrix_ρ_symm,
        LorentzGroup.inv_toComplex_transpose_mul_conj_minkowskiMatrix_map]
  simpa [LorentzGroup.minkowskiMatrix_map_mul_self, ComplexCoVector.metricVal] using h

end TensorInvariants

end Lorentz
