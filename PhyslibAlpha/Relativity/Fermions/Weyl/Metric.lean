/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jinzheng Li, Nathaneal Sajan, Joseph Tooby-Smith
-/
module

public import Physlib.Relativity.Fermions.Weyl.Metric
public import PhyslibAlpha.Mathematics.RepresentationTheory.Invariants
public import PhyslibAlpha.Relativity.LorentzGroup.Invariants.Reynolds
/-!
# Invariants of two Weyl indices

The invariants of two Weyl indices are the metric `ε` or zero, and `ε` lies in `SL(2, ℂ)`.

## i. Overview

The Weyl metric `Fermion.metricRaw = !![0, 1; -1, 0]` has determinant one, so it is itself an
element of `SL(2, ℂ)`, written `Lorentz.SL2C.epsilon`. In that form it is the invariant symplectic
form, `gᵀ ε g = ε`. Contracting spinor indices needs the single-index version of that invariance. A
factor of `(g⁻¹)ᵀ`, or of `(g⁻¹)ᴴ`, moved across `ε` becomes a factor of `g`, or of its entrywise
conjugate, on the other slot. Those are `metricRaw_comm` and `metricRaw_comm_star` at `g⁻¹`, read
entrywise. Alongside this, `LeftHandedWeyl.metricVal_rep` states the invariance of `εᵃᵃ` as the
plain equation on the tensor product, rather than through the intertwining property of
`LeftHandedWeyl.metric`.

Conversely, `ε` is the only invariant: the invariants of the tensor square of a Weyl
representation are the line through `ε`.

On the matrix of components `SL(2, ℂ)` acts by `X ↦ M X Mᵀ`, up to reparametrising the group (C).
The argument runs on matrices, for a linear map `F` with `F (M Y Mᵀ) = ρ M (F Y)` and `F X`
invariant, and shows that `F X` is a multiple of `F ε` (D). Each of the four tensor squares
reduces to it, with `F` the inverse of the matrix of components (E).

The other tensor products of two Weyl representations are handled through a uniform matrix of
components (F). The four `V ⊗ V*` have the unit `δ` as their only invariant, and are in
`PhyslibAlpha.Relativity.Fermions.Weyl.Unit`. A left-handed and a right-handed index have no
invariants at all, which is `complexLorentzTensor.invariants_upL_upR_eq_bot` in
`PhyslibAlpha.Relativity.Bispinors.ComplexifiedAction`. A product of an undotted and a dotted
one-index Weyl family is an equivariant map out of the tensors with a dual left- and a dual
right-handed index (G). The tensor-level form of the uniqueness of the metric is with the metric
tensors, in `PhyslibAlpha.Relativity.Tensors.ComplexTensor.Metrics.Basic`.

The results are named after the statement. On a tensor square `X ⊗ X` it is
`X.invariants_tprod_eq_span_metricVal`. The other forms of these
statements, for invariant elements, for the invariants in the range of an intertwining map and for
intertwining maps out of the trivial representation, follow from them by the lemmas of
`PhyslibAlpha.Mathematics.RepresentationTheory.Invariants`.

## ii. Key results

- `Fermion.LeftHandedWeyl.metricVal_rep` : `εᵃᵃ` is invariant under `SL(2, ℂ)`.
- `Lorentz.SL2C.epsilon` : the Weyl metric as an element of `SL(2, ℂ)`.
- `Lorentz.SL2C.transpose_mul_epsilon_mul` : `ε` is the invariant symplectic form.
- `Lorentz.SL2C.sum_epsilon_mul_inv_transpose`,
  `Lorentz.SL2C.sum_epsilon_mul_inv_conjTranspose` : the single-index forms.
- `Fermion.map_eq_smul_map_metricRaw_of_invariant` : on matrices, an invariant image of `X` is a
  multiple of the image of `ε`.
- `Fermion.LeftHandedWeyl.invariants_tprod_eq_span_metricVal` and its three siblings : the
  invariants of the tensor square are the line through the metric.
- `Fermion.tensorToMatrix_map` : on the matrix of components of `V ⊗ W` a pair of linear maps acts
  by `X ↦ A X Bᵀ`.
- `Lorentz.isEquivariant_downLDownR_mul` : an undotted family times a dotted one is an
  equivariant map out of `ℂT[.downL, .downR]`.

## iii. Table of contents

- A. Invariance of the left metric
- B. The symplectic form as an element of `SL(2, ℂ)`
- C. Reparametrising the group
- D. Matrices with an invariant image
  - D.1. The diagonal part
  - D.2. The symmetric off-diagonal part
  - D.3. The antisymmetric part
- E. The metrics are the unique invariants
- F. Components of a tensor product of two Weyl representations
  - F.1. The matrix of components
  - F.2. Three elements of `SL(2, ℂ)`
- G. One-index Weyl families and their products

## iv. References

The Weyl metrics and `Fermion.metricRaw` are in `Physlib.Relativity.Fermions.Weyl.Metric`, and
sections C to F are written to move there, with `tensorToMatrix` beside the matrix equivalences
of `Physlib.Relativity.Fermions.Weyl.Two` and the elements of F.2 in `Physlib.Relativity.SL2C`.
Section E settles the `TODO` in that file on the uniqueness of the metrics. Section G uses the
equivariant maps of `PhyslibAlpha.Relativity.Tensors.Equivariant` and stays here.
Compare `SULieAlgebra.intertwiningMap_eq_smul_adjointℂContr`.

-/

@[expose] public section

namespace Fermion

noncomputable section

open Module Matrix
open MatrixGroups
open Complex
open TensorProduct

/-!

## A. Invariance of the left metric

-/

/-- The metric `εᵃᵃ` is invariant under the action of `SL(2,ℂ)`. -/
lemma LeftHandedWeyl.metricVal_rep (M : SL(2,ℂ)) :
    TensorProduct.map (LeftHandedWeyl.rep M) (LeftHandedWeyl.rep M) LeftHandedWeyl.metricVal =
      LeftHandedWeyl.metricVal := by
  have h := LinearMap.congr_fun (LeftHandedWeyl.metric.isIntertwining' M) (1 : ℂ)
  simpa [LeftHandedWeyl.metric_apply_one, Representation.tprod_apply] using h.symm

end

end Fermion

/-!

## B. The symplectic form as an element of `SL(2, ℂ)`

`ε = metricRaw` has determinant one, so it lies in `SL(2,ℂ)`, and `gᵀ ε g = ε` for every `g`
there. The single-index identities move a factor of `(g⁻¹)ᵀ` or `(g⁻¹)ᴴ` across `ε`, where it
becomes a factor of `g` or of its conjugate on the other slot: they are `metricRaw_comm` and
`metricRaw_comm_star` at `g⁻¹`, read entrywise.

-/

namespace Lorentz.SL2C

open Matrix MatrixGroups

/-- The antisymmetric symplectic form `ε = !![0, 1; -1, 0]`, the Weyl metric
  `Fermion.metricRaw`, as an element of `SL(2,ℂ)`. -/
def epsilon : SL(2,ℂ) :=
  ⟨Fermion.metricRaw, by simp [Fermion.metricRaw, Matrix.det_fin_two_of]⟩

/-- The matrix underlying `epsilon`. -/
lemma epsilon_coe : (epsilon : Matrix (Fin 2) (Fin 2) ℂ) = !![0, 1; -1, 0] := rfl

/-- The matrix underlying `epsilon` is the Weyl metric `Fermion.metricRaw`. -/
lemma epsilon_coe_metricRaw : (epsilon : Matrix (Fin 2) (Fin 2) ℂ) = Fermion.metricRaw := rfl

/-- `ε g⁻¹ = gᵀ ε`, `Fermion.metricRaw_comm` at `g⁻¹`. -/
lemma epsilon_mul_inv (g : SL(2,ℂ)) : epsilon.1 * g.1⁻¹ = g.1ᵀ * epsilon.1 := by
  have h := Fermion.metricRaw_comm g⁻¹
  rw [inverse_coe g⁻¹, inv_inv, ← inverse_coe g] at h
  exact h

/-- `ε` is the invariant symplectic form of `SL(2,ℂ)`, `gᵀ ε g = ε`. -/
lemma transpose_mul_epsilon_mul (g : SL(2,ℂ)) : g.1ᵀ * epsilon.1 * g.1 = epsilon.1 := by
  rw [← epsilon_mul_inv, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ (by simp), Matrix.mul_one]

/-- Single-index form. A factor of `(g⁻¹)ᵀ` moved across `ε` becomes a factor of `g` on the
  other slot. -/
lemma sum_epsilon_mul_inv_transpose (g : SL(2,ℂ)) (l a : Fin 2) :
    ∑ k : Fin 2, epsilon.1 l k * (g.1⁻¹)ᵀ a k = ∑ b : Fin 2, g.1 b l * epsilon.1 b a := by
  have h : (epsilon.1 * g.1⁻¹) l a = (g.1ᵀ * epsilon.1) l a := by rw [epsilon_mul_inv]
  simpa [Matrix.mul_apply, Matrix.transpose_apply] using h

/-- The conjugate single-index form. A factor of `(g⁻¹)ᴴ` moved across `ε` becomes a factor of
  the conjugate of `g` on the other slot. -/
lemma sum_epsilon_mul_inv_conjTranspose (g : SL(2,ℂ)) (l a : Fin 2) :
    ∑ k : Fin 2, epsilon.1 l k * (g.1⁻¹)ᴴ a k
      = ∑ b : Fin 2, star (g.1 b l) * epsilon.1 b a := by
  have h0 := Fermion.metricRaw_comm_star g⁻¹
  rw [inverse_coe g⁻¹, inv_inv, ← inverse_coe g] at h0
  have h : (epsilon.1 * (g.1⁻¹).map star) l a = (g.1ᴴ * epsilon.1) l a := by
    rw [epsilon_coe_metricRaw, h0]
  simpa [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.map_apply] using h

end Lorentz.SL2C

/-!

## C. Reparametrising the group

On two undotted indices `SL(2,ℂ)` acts on the matrix of components by `X ↦ M X Mᵀ`, and `ε` is
fixed by it. On the other three Weyl representations the group acts through `(M⁻¹)ᵀ`, the
conjugate of `M`, or `(M⁻¹)ᴴ`, and each of these runs over all of `SL(2,ℂ)` as `M` does.

-/

namespace Fermion

noncomputable section

open Matrix MatrixGroups TensorProduct

/-- The element of `SL(2,ℂ)` whose matrix `(M⁻¹)ᵀ` is the given `N`. -/
lemma inv_coe_transpose_inv (N : SL(2,ℂ)) : (N.transpose⁻¹ : SL(2,ℂ)).1⁻¹ = N.1ᵀ := by
  rw [Lorentz.SL2C.inverse_coe, inv_inv, SpecialLinearGroup.coe_transpose]

/-- The element of `SL(2,ℂ)` whose conjugate matrix is the given `N`. -/
lemma map_star_coe_map_starRingEnd (N : SL(2,ℂ)) :
    (SpecialLinearGroup.map (starRingEnd ℂ) N).1.map star = N.1 := by
  ext i j
  simp

/-- The element of `SL(2,ℂ)` whose matrix `(M⁻¹)ᴴ` is the given `N`. -/
lemma conjTranspose_inv_coe_transpose_inv_map (N : SL(2,ℂ)) :
    ((SpecialLinearGroup.map (starRingEnd ℂ) N).transpose⁻¹ : SL(2,ℂ)).1⁻¹ᴴ = N.1 := by
  rw [inv_coe_transpose_inv]
  ext i j
  simp

/-- The Weyl metric is fixed by the action `X ↦ M X Mᵀ` of `SL(2,ℂ)` on two undotted indices. -/
lemma mul_metricRaw_mul_transpose (M : SL(2,ℂ)) : M.1 * metricRaw * M.1ᵀ = metricRaw := by
  rw [comm_metricRaw, Matrix.mul_assoc, ← Matrix.transpose_mul]
  simp

/-!

## D. Matrices with an invariant image

The argument runs on the matrix of components, through a linear map `F` with
`F (M Y Mᵀ) = ρ M (F Y)`, and with `F Y` invariant. Here `ρ` is any family of linear maps, so
that it can be a representation composed with one of the reparametrisations of C. The boosts
`diag (2, 2⁻¹)` and `diag (2⁻¹, 2)` combine to give the diagonal part of `Y`, so `F` kills it
(D.1). The element `!![1, -1; 1, 0]` sends the symmetric off-diagonal matrix `O` to minus itself
plus a diagonal matrix, so `F O` is its own negative and vanishes (D.2). What is left of `Y` is
its antisymmetric part, a multiple of `ε` (D.3).

-/

/-!

### D.1. The diagonal part

-/

section ImageInvariants

variable {B : Type*} [AddCommGroup B] [Module ℂ B] {ρ : SL(2,ℂ) → Module.End ℂ B}
  {F : Matrix (Fin 2) (Fin 2) ℂ →ₗ[ℂ] B}

/-- The diagonal part of a `2 × 2` matrix as a combination of its images under the boosts
  `diag (2, 2⁻¹)` and `diag (2⁻¹, 2)`, with coefficients summing to zero. -/
lemma diagonal_eq_smul_boost_sub (Y : Matrix (Fin 2) (Fin 2) ℂ) :
    !![Y 0 0, 0; 0, Y 1 1] = (4 / 9 : ℂ) • (!![2, 0; 0, 2⁻¹] * Y * !![2, 0; 0, 2⁻¹]ᵀ +
      !![2⁻¹, 0; 0, 2] * Y * !![2⁻¹, 0; 0, 2]ᵀ - (2 : ℂ) • Y) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct] <;> ring

/-- An equivariant map with `F Y` invariant vanishes on the diagonal part of `Y`. -/
lemma map_diagonal_eq_zero_of_invariant (hF : ∀ (M : SL(2,ℂ)) Y, F (M.1 * Y * M.1ᵀ) = ρ M (F Y))
    {Y : Matrix (Fin 2) (Fin 2) ℂ} (hY : ∀ g, ρ g (F Y) = F Y) :
    F !![Y 0 0, 0; 0, Y 1 1] = 0 := by
  have h1 : F (!![2, 0; 0, 2⁻¹] * Y * !![2, 0; 0, 2⁻¹]ᵀ) = F Y :=
    (hF ⟨!![2, 0; 0, 2⁻¹], by simp [det_fin_two_of]⟩ Y).trans (hY _)
  have h2 : F (!![2⁻¹, 0; 0, 2] * Y * !![2⁻¹, 0; 0, 2]ᵀ) = F Y :=
    (hF ⟨!![2⁻¹, 0; 0, 2], by simp [det_fin_two_of]⟩ Y).trans (hY _)
  rw [diagonal_eq_smul_boost_sub, map_smul, map_sub, map_add, map_smul, h1, h2]
  module

/-!

### D.2. The symmetric off-diagonal part

-/

/-- An equivariant map with `F !![0, c; c, 0]` invariant vanishes on `!![0, c; c, 0]`. -/
lemma map_offDiagonal_eq_zero_of_invariant
    (hF : ∀ (M : SL(2,ℂ)) Y, F (M.1 * Y * M.1ᵀ) = ρ M (F Y)) {c : ℂ}
    (hc : ∀ g, ρ g (F !![0, c; c, 0]) = F !![0, c; c, 0]) : F !![0, c; c, 0] = 0 := by
  set Y := !![1, -1; 1, 0] * !![0, c; c, 0] * !![1, -1; 1, 0]ᵀ
  have hY : F Y = F !![0, c; c, 0] :=
    (hF ⟨!![1, -1; 1, 0], by simp [det_fin_two_of]⟩ _).trans (hc _)
  have hsplit : Y = !![Y 0 0, 0; 0, Y 1 1] - !![0, c; c, 0] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Y, Matrix.vecHead, Matrix.vecTail]
  have hdiag := map_diagonal_eq_zero_of_invariant hF (Y := Y) (by simpa [hY] using hc)
  have h := congrArg F hsplit
  rw [map_sub, hdiag, zero_sub, hY] at h
  have h2 : (2 : ℂ) • F !![0, c; c, 0] = 0 := by
    rw [two_smul]
    nth_rewrite 2 [h]
    exact add_neg_cancel _
  exact (smul_eq_zero.mp h2).resolve_left two_ne_zero

/-!

### D.3. The antisymmetric part

-/

/-- An equivariant map with `F X` invariant sends `X` to a multiple of the image of the Weyl
  metric. -/
lemma map_eq_smul_map_metricRaw_of_invariant
    (hF : ∀ (M : SL(2,ℂ)) Y, F (M.1 * Y * M.1ᵀ) = ρ M (F Y)) {X : Matrix (Fin 2) (Fin 2) ℂ}
    (hX : ∀ g, ρ g (F X) = F X) : F X = ((X 0 1 - X 1 0) / 2) • F metricRaw := by
  set s := (X 0 1 + X 1 0) / 2
  have hdec : X = !![X 0 0, 0; 0, X 1 1] + !![0, s; s, 0] + ((X 0 1 - X 1 0) / 2) • metricRaw := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [s, metricRaw] <;> ring
  have hO : F !![0, s; s, 0] = F X - ((X 0 1 - X 1 0) / 2) • F metricRaw := by
    have h := congrArg F hdec
    rw [map_add, map_add, map_smul, map_diagonal_eq_zero_of_invariant hF hX, zero_add] at h
    rw [h, add_sub_cancel_right]
  have hε (g : SL(2,ℂ)) : ρ g (F metricRaw) = F metricRaw := by
    rw [← hF, mul_metricRaw_mul_transpose]
  have h0 := map_offDiagonal_eq_zero_of_invariant hF (c := s) fun g => by
    rw [hO, map_sub, map_smul, hX, hε]
  rwa [h0, eq_comm, sub_eq_zero] at hO

end ImageInvariants

/-!

## E. The metrics are the unique invariants

On the matrix of components `SL(2,ℂ)` acts by `X ↦ N X Nᵀ`, where `N` is `M`, `(M⁻¹)ᵀ`, the
conjugate of `M`, or `(M⁻¹)ᴴ`, and by section C section D applies to each, with `F` the inverse of
the matrix of components. So the invariants of each tensor square are the line through its
metric.

-/

/-- The `SL(2,ℂ)`-invariants of `LeftHandedWeyl ⊗ LeftHandedWeyl` are the line through the
  metric `εᵃᵃ`. -/
lemma LeftHandedWeyl.invariants_tprod_eq_span_metricVal :
    (rep.tprod rep).invariants = ℂ ∙ metricVal := by
  refine Representation.invariants_eq_span_singleton
    (by simpa [metric_apply_one] using metric.apply_one_mem_invariants) fun v hinv => ?_
  have hinv : ∀ g, (rep.tprod rep) g v = v := hinv
  set F := leftLeftToMatrix.symm.toLinearMap
  have hF (M : SL(2,ℂ)) (Y : Matrix (Fin 2) (Fin 2) ℂ) :
      F (M.1 * Y * M.1ᵀ) = (rep.tprod rep) M (F Y) := by
    simp [F, ← leftLeftToMatrix_ρ_symm, Representation.tprod_apply]
  have h := map_eq_smul_map_metricRaw_of_invariant hF (X := leftLeftToMatrix v)
    (by simpa [F] using hinv)
  refine ⟨-((leftLeftToMatrix v 0 1 - leftLeftToMatrix v 1 0) / 2), ?_⟩
  simpa [F, metricVal] using h

/-- The `SL(2,ℂ)`-invariants of `DualLeftHandedWeyl ⊗ DualLeftHandedWeyl` are the line through
  the metric `εₐₐ`. -/
lemma DualLeftHandedWeyl.invariants_tprod_eq_span_metricVal :
    (rep.tprod rep).invariants = ℂ ∙ metricVal := by
  refine Representation.invariants_eq_span_singleton
    (by simpa [metric_apply_one] using metric.apply_one_mem_invariants) fun v hinv => ?_
  have hinv : ∀ g, (rep.tprod rep) g v = v := hinv
  set F := dualLeftdualLeftToMatrix.symm.toLinearMap
  have hF (N : SL(2,ℂ)) (Y : Matrix (Fin 2) (Fin 2) ℂ) :
      F (N.1 * Y * N.1ᵀ) = (rep.tprod rep) N.transpose⁻¹ (F Y) := by
    have h := dualLeftdualLeftToMatrix_ρ_symm Y N.transpose⁻¹
    rw [inv_coe_transpose_inv, transpose_transpose] at h
    simp [F, ← h, Representation.tprod_apply]
  have h := map_eq_smul_map_metricRaw_of_invariant hF (X := dualLeftdualLeftToMatrix v)
    (by simpa [F] using fun g => hinv _)
  refine ⟨(dualLeftdualLeftToMatrix v 0 1 - dualLeftdualLeftToMatrix v 1 0) / 2, ?_⟩
  simpa [F, metricVal] using h

/-- The `SL(2,ℂ)`-invariants of `RightHandedWeyl ⊗ RightHandedWeyl` are the line through the
  metric `ε^{ȧȧ}`. -/
lemma RightHandedWeyl.invariants_tprod_eq_span_metricVal :
    (rep.tprod rep).invariants = ℂ ∙ metricVal := by
  refine Representation.invariants_eq_span_singleton
    (by simpa [metric_apply_one] using metric.apply_one_mem_invariants) fun v hinv => ?_
  have hinv : ∀ g, (rep.tprod rep) g v = v := hinv
  set F := rightRightToMatrix.symm.toLinearMap
  have hF (N : SL(2,ℂ)) (Y : Matrix (Fin 2) (Fin 2) ℂ) :
      F (N.1 * Y * N.1ᵀ) = (rep.tprod rep) (SpecialLinearGroup.map (starRingEnd ℂ) N) (F Y) := by
    have h := rightRightToMatrix_ρ_symm Y (SpecialLinearGroup.map (starRingEnd ℂ) N)
    rw [map_star_coe_map_starRingEnd] at h
    simp [F, ← h, Representation.tprod_apply]
  have h := map_eq_smul_map_metricRaw_of_invariant hF (X := rightRightToMatrix v)
    (by simpa [F] using fun g => hinv _)
  refine ⟨-((rightRightToMatrix v 0 1 - rightRightToMatrix v 1 0) / 2), ?_⟩
  simpa [F, metricVal] using h

/-- The `SL(2,ℂ)`-invariants of `DualRightHandedWeyl ⊗ DualRightHandedWeyl` are the line through
  the metric `ε_{ȧȧ}`. -/
lemma DualRightHandedWeyl.invariants_tprod_eq_span_metricVal :
    (rep.tprod rep).invariants = ℂ ∙ metricVal := by
  refine Representation.invariants_eq_span_singleton
    (by simpa [metric_apply_one] using metric.apply_one_mem_invariants) fun v hinv => ?_
  have hinv : ∀ g, (rep.tprod rep) g v = v := hinv
  set F := dualRightDualRightToMatrix.symm.toLinearMap
  have hF (N : SL(2,ℂ)) (Y : Matrix (Fin 2) (Fin 2) ℂ) : F (N.1 * Y * N.1ᵀ) =
      (rep.tprod rep) (SpecialLinearGroup.map (starRingEnd ℂ) N).transpose⁻¹ (F Y) := by
    have h := dualRightDualRightToMatrix_ρ_symm Y
      (SpecialLinearGroup.map (starRingEnd ℂ) N).transpose⁻¹
    rw [conjTranspose_inv_coe_transpose_inv_map] at h
    simp [F, ← h, Representation.tprod_apply]
  have h := map_eq_smul_map_metricRaw_of_invariant hF (X := dualRightDualRightToMatrix v)
    (by simpa [F] using fun g => hinv _)
  refine ⟨(dualRightDualRightToMatrix v 0 1 - dualRightDualRightToMatrix v 1 0) / 2, ?_⟩
  simpa [F, metricVal] using h

/-!

## F. Components of a tensor product of two Weyl representations

The other twelve tensor products of two Weyl representations are handled uniformly through
their matrix of components, `tensorToMatrix`, on which `SL(2,ℂ)` acts by `X ↦ K₁ X K₂ᵀ` with
`Kᵢ` the matrices of the two factors (F.1). The arguments of
`PhyslibAlpha.Relativity.Fermions.Weyl.Unit` only test this action against three elements of
`SL(2,ℂ)`, the boosts `boostTwo` and `boostHalf` along `z`, and `epsilon` (F.2).

-/

/-!

### F.1. The matrix of components

-/

section Components

variable {V W : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  (b : Module.Basis (Fin 2) ℂ V) (c : Module.Basis (Fin 2) ℂ W)

/-- The matrix of components of an element of `V ⊗ W`, in a basis of `V` and a basis of `W`. -/
def tensorToMatrix : V ⊗[ℂ] W ≃ₗ[ℂ] Matrix (Fin 2) (Fin 2) ℂ :=
  (b.tensorProduct c).repr ≪≫ₗ Finsupp.linearEquivFunOnFinite ℂ ℂ (Fin 2 × Fin 2) ≪≫ₗ
    LinearEquiv.curry ℂ ℂ (Fin 2) (Fin 2)

/-- The components of a pure tensor are the products of the components of its factors. -/
lemma tensorToMatrix_tmul (x : V) (y : W) (i j : Fin 2) :
    tensorToMatrix b c (x ⊗ₜ y) i j = b.repr x i * c.repr y j := by
  change (b.tensorProduct c).repr (x ⊗ₜ y) (i, j) = _
  rw [Module.Basis.tensorProduct_repr_tmul_apply, smul_eq_mul, mul_comm]

/-- A pair of linear maps acts on the matrix of components by `X ↦ A X Bᵀ`. -/
lemma tensorToMatrix_map (f : V →ₗ[ℂ] V) (g : W →ₗ[ℂ] W) (v : V ⊗[ℂ] W) :
    tensorToMatrix b c (TensorProduct.map f g v) =
      LinearMap.toMatrix b b f * tensorToMatrix b c v * (LinearMap.toMatrix c c g)ᵀ := by
  induction v using TensorProduct.inductionOn with
  | tmul x y =>
    ext i j
    rw [TensorProduct.map_tmul, tensorToMatrix_tmul, ← LinearMap.toMatrix_mulVec_repr b b f x,
      ← LinearMap.toMatrix_mulVec_repr c c g y]
    simp [tensorToMatrix_tmul, Matrix.mul_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    ring
  | add v w hv hw => simp [hv, hw, Matrix.mul_add, Matrix.add_mul]

/-- An element of `V ⊗ W` with invariant components `Y` is unchanged by an element of
  `SL(2,ℂ)` acting on the components. -/
lemma symm_act_eq {ρV : Representation ℂ SL(2,ℂ) V} {ρW : Representation ℂ SL(2,ℂ) W}
    {Y : Matrix (Fin 2) (Fin 2) ℂ} (hY : (tensorToMatrix b c).symm Y ∈ (ρV.tprod ρW).invariants)
    {Φ : Matrix (Fin 2) (Fin 2) ℂ → Matrix (Fin 2) (Fin 2) ℂ}
    (h : ∃ g, ∀ X, LinearMap.toMatrix b b (ρV g) * X * (LinearMap.toMatrix c c (ρW g))ᵀ = Φ X) :
    (tensorToMatrix b c).symm (Φ Y) = (tensorToMatrix b c).symm Y := by
  obtain ⟨g, hg⟩ := h
  have hmap := tensorToMatrix_map b c (ρV g) (ρW g) ((tensorToMatrix b c).symm Y)
  rw [LinearEquiv.apply_symm_apply] at hmap
  rw [← hg, ← hmap, LinearEquiv.symm_apply_apply]
  exact hY g

end Components

/-!

### F.2. Three elements of `SL(2, ℂ)`

-/

/-- The boost along `z` with matrix `diag (2, 2⁻¹)`. -/
def _root_.Lorentz.SL2C.boostTwo : SL(2,ℂ) := ⟨!![2, 0; 0, 2⁻¹], by simp [det_fin_two_of]⟩

/-- The boost along `z` with matrix `diag (2⁻¹, 2)`, the inverse of `boostTwo`. -/
def _root_.Lorentz.SL2C.boostHalf : SL(2,ℂ) := ⟨!![2⁻¹, 0; 0, 2], by simp [det_fin_two_of]⟩

/-- Computes `K₁ X K₂ᵀ` entrywise, for `Kᵢ` the matrix of a Weyl representation at one of
  `boostTwo`, `boostHalf` or `epsilon`. -/
scoped macro "weyl_act" : tactic => `(tactic| (
  intro X
  simp only [LeftHandedWeyl.rep_toMatrix, DualLeftHandedWeyl.rep_toMatrix,
    RightHandedWeyl.rep_toMatrix, DualRightHandedWeyl.rep_toMatrix, Lorentz.SL2C.inverse_coe,
    SpecialLinearGroup.coe_inv]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [adjugate_fin_two, Lorentz.SL2C.boostTwo, Lorentz.SL2C.boostHalf,
      Lorentz.SL2C.epsilon_coe, Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct,
      map_ofNat] <;> (try ring_nf) <;> (try simp) <;> (try ring_nf)))

end

end Fermion

/-!

## G. One-index Weyl families and their products

A two-element family of elements of an algebra `B` can carry one dual Weyl index, undotted or
dotted. Both laws are contragredient, and the dotted law carries the extra complex conjugation. A
fermion field of the Standard Model with every index but its spinor index frozen is such a family.
When the Lorentz action is multiplicative, an undotted family times a dotted one is an equivariant
map out of `ℂT[.downL, .downR]`, in either order, the shape of a Dirac mass term `ψ̄ ψ`. That such
a map carries no invariant is `Lorentz.reducesInvariantsTo_bot_leftRight`, in
`PhyslibAlpha.Relativity.Bispinors.ComplexifiedAction`.

-/

namespace Lorentz

open Matrix MatrixGroups SL2C TensorSpecies complexLorentzTensor
open TensorSpecies.Tensor


section ChiralFamilies

variable {B : Type} [Ring B] [Algebra ℂ B] {repLorentz : Representation ℂ SL(2,ℂ) B}
  (hrepLorentz_mul : ∀ (Λ : SL(2,ℂ)) (b₁ b₂ : B),
    repLorentz Λ (b₁ * b₂) = repLorentz Λ b₁ * repLorentz Λ b₂)

include hrepLorentz_mul

/-- A family `X` with a dual undotted spinor index, moved by the contragredient of the
  left-handed Weyl representation, times a family `Y` with a dual dotted spinor index, moved by
  its conjugate, is an equivariant map out of `ℂT[.downL, .downR]`. -/
lemma isEquivariant_downLDownR_mul {X Y : Fin 2 → B}
    (hX : ∀ (Λ : SL(2,ℂ)) (a : Fin 2), repLorentz Λ (X a) = ∑ β, (Λ⁻¹).1 a β • X β)
    (hY : ∀ (Λ : SL(2,ℂ)) (a : Fin 2), repLorentz Λ (Y a) = ∑ β, star ((Λ⁻¹).1 a β) • Y β) :
    complexLorentzTensor.IsEquivariant ![.downL, .downR] repLorentz
      (liftComponents ((fun p => X p.1 * Y p.2) ∘ pairIdx)) :=
  isEquivariant_liftComponents_pair (S := complexLorentzTensor) (c1 := .downL) (c2 := .downR)
    (fun a b => X a * Y b) fun g a b => by
    rw [toMatrix_rep_downL, toMatrix_rep_downR, hrepLorentz_mul, hX g a, hY g b,
      Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
    rw [smul_mul_smul_comm]
    congr 1
    rw [Matrix.transpose_apply, Matrix.conjTranspose_apply, ← SL2C.inverse_coe]

/-- A dotted family times an undotted one is an equivariant map out of `ℂT[.downL, .downR]`, the
  two spinor slots exchanged. -/
lemma isEquivariant_downLDownR_mul_swap {X Y : Fin 2 → B}
    (hX : ∀ (Λ : SL(2,ℂ)) (a : Fin 2), repLorentz Λ (X a) = ∑ β, star ((Λ⁻¹).1 a β) • X β)
    (hY : ∀ (Λ : SL(2,ℂ)) (a : Fin 2), repLorentz Λ (Y a) = ∑ β, (Λ⁻¹).1 a β • Y β) :
    complexLorentzTensor.IsEquivariant ![.downL, .downR] repLorentz
      (liftComponents ((fun p => X p.2 * Y p.1) ∘ pairIdx)) :=
  isEquivariant_liftComponents_pair (S := complexLorentzTensor) (c1 := .downL) (c2 := .downR)
    (fun a b => X b * Y a) fun g a b => by
    rw [toMatrix_rep_downL, toMatrix_rep_downR, hrepLorentz_mul, hX g b, hY g a,
      Finset.sum_mul_sum, Finset.sum_comm]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
    rw [smul_mul_smul_comm]
    congr 1
    rw [Matrix.transpose_apply, Matrix.conjTranspose_apply, ← SL2C.inverse_coe]
    ring

end ChiralFamilies

end Lorentz
