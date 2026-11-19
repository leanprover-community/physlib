/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jinzheng Li, Nathaneal Sajan, Joseph Tooby-Smith
-/
module

public import Physlib.Relativity.Fermions.Weyl.Metric
public import PhyslibAlpha.Mathematics.RepresentationTheory.Invariants
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

Conversely, `ε` is the only invariant, and this survives any equivariant map. Let `f` be an
equivariant map out of the tensor square of a Weyl representation into `B`, with `B` carrying any
action of `SL(2, ℂ)`. The invariants in the image of `f`, `ρ.invariants ⊓ f.range`, are the line
through `f ε`. The preimage of such an invariant need not itself be invariant, so this is
stronger than the statement about invariant elements, which is the case `f = id`: the invariants
of the tensor square are the line through `ε`. In turn every intertwining map out of the trivial
representation into the tensor square is a multiple of the metric.

On the matrix of components `SL(2, ℂ)` acts by `X ↦ M X Mᵀ`, up to reparametrising the group (C).
The argument runs on matrices, for a linear map `F` with `F (M Y Mᵀ) = ρ M (F Y)` and `F X`
invariant, and shows that `F X` is a multiple of `F ε` (D). Each of the four tensor squares
reduces to it (E).

The other twelve tensor products of two Weyl representations go the same way, through a uniform
matrix of components (F), which `PhyslibAlpha.Relativity.Fermions.Weyl.Unit` also uses. A
left-handed and a right-handed index, in either order and either dual, have no invariants at all,
also after an equivariant map (G). The remaining four, `V ⊗ V*`, have the unit `δ` as their only
invariant, and are in `PhyslibAlpha.Relativity.Fermions.Weyl.Unit`.

The results are named after the statement. On a tensor square `X ⊗ X` they are
`X.invariants_inf_range_eq_span_map_metricVal`, `X.invariants_tprod_eq_span_metricVal` and
`X.intertwiningMap_eq_smul_metric`. On a pair `X ⊗ Y` of opposite chirality the second factor
is named, as in `LeftHandedWeyl.invariants_tprod_rightHandedWeyl_eq_bot`.

## ii. Key results

- `Fermion.LeftHandedWeyl.metricVal_rep` : `εᵃᵃ` is invariant under `SL(2, ℂ)`.
- `Lorentz.SL2C.epsilon` : the Weyl metric as an element of `SL(2, ℂ)`.
- `Lorentz.SL2C.transpose_mul_epsilon_mul` : `ε` is the invariant symplectic form.
- `Lorentz.SL2C.sum_epsilon_mul_inv_transpose`,
  `Lorentz.SL2C.sum_epsilon_mul_inv_conjTranspose` : the single-index forms.
- `Fermion.map_eq_smul_map_metricRaw_of_invariant` : on matrices, an invariant image of `X` is a
  multiple of the image of `ε`.
- `Fermion.LeftHandedWeyl.invariants_inf_range_eq_span_map_metricVal` and its three siblings :
  the invariants in the image of an equivariant map out of the tensor square are the line through
  the image of the metric.
- `Fermion.LeftHandedWeyl.invariants_tprod_eq_span_metricVal` and its three siblings : the
  invariants of the tensor square are the line through the metric.
- `Fermion.LeftHandedWeyl.intertwiningMap_eq_smul_metric` and its three siblings : every
  intertwining map from the trivial representation into the tensor square is a multiple of the
  metric.
- `Fermion.tensorToMatrix_map` : on the matrix of components of `V ⊗ W` a pair of linear maps acts
  by `X ↦ A X Bᵀ`.
- `Fermion.LeftHandedWeyl.invariants_tprod_rightHandedWeyl_eq_bot` and its seven siblings : two
  indices of opposite chirality have no invariants, with the corresponding
  `invariants_inf_range_tprod_…_eq_bot` and `intertwiningMap_tprod_…_eq_zero`.

## iii. Table of contents

- A. Invariance of the left metric
- B. The symplectic form as an element of `SL(2, ℂ)`
- C. Reparametrising the group
- D. Matrices with an invariant image
  - D.1. The diagonal part
  - D.2. The symmetric off-diagonal part
  - D.3. The antisymmetric part
- E. The metrics are the unique invariants
  - E.1. Invariants in the image of an equivariant map
  - E.2. Invariant elements
  - E.3. Intertwining maps out of the trivial representation
- F. Components of a tensor product of two Weyl representations
  - F.1. The matrix of components
  - F.2. Four elements of `SL(2, ℂ)`
- G. Two indices of opposite chirality
  - G.1. Matrices
  - G.2. Tensor products
  - G.3. The eight pairs

## iv. References

The Weyl metrics and `Fermion.metricRaw` are in `Physlib.Relativity.Fermions.Weyl.Metric`, and
sections C to G are written to move there, with `tensorToMatrix` beside the matrix equivalences
of `Physlib.Relativity.Fermions.Weyl.Two` and the elements of F.2 in `Physlib.Relativity.SL2C`.
Section E settles the `TODO` in that file on the uniqueness of the metrics. Compare
`SULieAlgebra.intertwiningMap_eq_smul_adjointℂContr`.

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
      simp [Y, Fin.sum_univ_two, Matrix.vecMul, dotProduct]
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

Let `f` be an equivariant map out of the tensor square of a Weyl representation into `B`, for `B`
carrying any action of `SL(2,ℂ)`. The invariants in the image of `f` are the line through `f ε`
(E.1). On the matrix of components `SL(2,ℂ)` acts by `X ↦ N X Nᵀ`, where `N` is `M`, `(M⁻¹)ᵀ`,
the conjugate of `M`, or `(M⁻¹)ᴴ`, and by section C section D applies to each. For `f` the
identity this says that the invariants of the tensor square are the line through `ε` (E.2), and
so every intertwining map out of the trivial representation is a multiple of the metric (E.3).

-/

/-!

### E.1. Invariants in the image of an equivariant map

-/

section TensorSquares

variable {B : Type*} [AddCommGroup B] [Module ℂ B] {ρ : Representation ℂ SL(2,ℂ) B}

/-- For an equivariant map `f` out of `LeftHandedWeyl ⊗ LeftHandedWeyl`, the
  `SL(2,ℂ)`-invariants in the image of `f` are the line through the image `f εᵃᵃ` of the
  metric. -/
lemma LeftHandedWeyl.invariants_inf_range_eq_span_map_metricVal
    (f : (rep.tprod rep).IntertwiningMap ρ) :
    ρ.invariants ⊓ f.range.toSubmodule = ℂ ∙ f metricVal := by
  refine Representation.invariants_inf_range_eq_span
    (by simpa [metric_apply_one] using metric.apply_one_mem_invariants) fun _ hinv hb => ?_
  obtain ⟨v, rfl⟩ := hb
  have hinv : ∀ g, ρ g (f v) = f v := hinv
  set F := f.toLinearMap ∘ₗ leftLeftToMatrix.symm.toLinearMap
  have hF (M : SL(2,ℂ)) (Y : Matrix (Fin 2) (Fin 2) ℂ) : F (M.1 * Y * M.1ᵀ) = ρ M (F Y) := by
    simp [F, ← leftLeftToMatrix_ρ_symm, ← f.isIntertwining, Representation.tprod_apply]
  have h := map_eq_smul_map_metricRaw_of_invariant hF (X := leftLeftToMatrix v)
    (by simpa [F] using hinv)
  refine ⟨-((leftLeftToMatrix v 0 1 - leftLeftToMatrix v 1 0) / 2), ?_⟩
  simpa [F, metricVal] using h

/-- For an equivariant map `f` out of `DualLeftHandedWeyl ⊗ DualLeftHandedWeyl`, the
  `SL(2,ℂ)`-invariants in the image of `f` are the line through the image `f εₐₐ` of the
  metric. -/
lemma DualLeftHandedWeyl.invariants_inf_range_eq_span_map_metricVal
    (f : (rep.tprod rep).IntertwiningMap ρ) :
    ρ.invariants ⊓ f.range.toSubmodule = ℂ ∙ f metricVal := by
  refine Representation.invariants_inf_range_eq_span
    (by simpa [metric_apply_one] using metric.apply_one_mem_invariants) fun _ hinv hb => ?_
  obtain ⟨v, rfl⟩ := hb
  have hinv : ∀ g, ρ g (f v) = f v := hinv
  set F := f.toLinearMap ∘ₗ dualLeftdualLeftToMatrix.symm.toLinearMap
  have hF (N : SL(2,ℂ)) (Y : Matrix (Fin 2) (Fin 2) ℂ) :
      F (N.1 * Y * N.1ᵀ) = ρ N.transpose⁻¹ (F Y) := by
    have h := dualLeftdualLeftToMatrix_ρ_symm Y N.transpose⁻¹
    rw [inv_coe_transpose_inv, transpose_transpose] at h
    simp [F, ← h, ← f.isIntertwining, Representation.tprod_apply]
  have h := map_eq_smul_map_metricRaw_of_invariant hF (X := dualLeftdualLeftToMatrix v)
    (by simpa [F] using fun g => hinv _)
  refine ⟨(dualLeftdualLeftToMatrix v 0 1 - dualLeftdualLeftToMatrix v 1 0) / 2, ?_⟩
  simpa [F, metricVal] using h

/-- For an equivariant map `f` out of `RightHandedWeyl ⊗ RightHandedWeyl`, the
  `SL(2,ℂ)`-invariants in the image of `f` are the line through the image `f ε^{ȧȧ}` of the
  metric. -/
lemma RightHandedWeyl.invariants_inf_range_eq_span_map_metricVal
    (f : (rep.tprod rep).IntertwiningMap ρ) :
    ρ.invariants ⊓ f.range.toSubmodule = ℂ ∙ f metricVal := by
  refine Representation.invariants_inf_range_eq_span
    (by simpa [metric_apply_one] using metric.apply_one_mem_invariants) fun _ hinv hb => ?_
  obtain ⟨v, rfl⟩ := hb
  have hinv : ∀ g, ρ g (f v) = f v := hinv
  set F := f.toLinearMap ∘ₗ rightRightToMatrix.symm.toLinearMap
  have hF (N : SL(2,ℂ)) (Y : Matrix (Fin 2) (Fin 2) ℂ) :
      F (N.1 * Y * N.1ᵀ) = ρ (SpecialLinearGroup.map (starRingEnd ℂ) N) (F Y) := by
    have h := rightRightToMatrix_ρ_symm Y (SpecialLinearGroup.map (starRingEnd ℂ) N)
    rw [map_star_coe_map_starRingEnd] at h
    simp [F, ← h, ← f.isIntertwining, Representation.tprod_apply]
  have h := map_eq_smul_map_metricRaw_of_invariant hF (X := rightRightToMatrix v)
    (by simpa [F] using fun g => hinv _)
  refine ⟨-((rightRightToMatrix v 0 1 - rightRightToMatrix v 1 0) / 2), ?_⟩
  simpa [F, metricVal] using h

/-- For an equivariant map `f` out of `DualRightHandedWeyl ⊗ DualRightHandedWeyl`, the
  `SL(2,ℂ)`-invariants in the image of `f` are the line through the image `f ε_{ȧȧ}` of the
  metric. -/
lemma DualRightHandedWeyl.invariants_inf_range_eq_span_map_metricVal
    (f : (rep.tprod rep).IntertwiningMap ρ) :
    ρ.invariants ⊓ f.range.toSubmodule = ℂ ∙ f metricVal := by
  refine Representation.invariants_inf_range_eq_span
    (by simpa [metric_apply_one] using metric.apply_one_mem_invariants) fun _ hinv hb => ?_
  obtain ⟨v, rfl⟩ := hb
  have hinv : ∀ g, ρ g (f v) = f v := hinv
  set F := f.toLinearMap ∘ₗ dualRightDualRightToMatrix.symm.toLinearMap
  have hF (N : SL(2,ℂ)) (Y : Matrix (Fin 2) (Fin 2) ℂ) :
      F (N.1 * Y * N.1ᵀ) = ρ (SpecialLinearGroup.map (starRingEnd ℂ) N).transpose⁻¹ (F Y) := by
    have h := dualRightDualRightToMatrix_ρ_symm Y
      (SpecialLinearGroup.map (starRingEnd ℂ) N).transpose⁻¹
    rw [conjTranspose_inv_coe_transpose_inv_map] at h
    simp [F, ← h, ← f.isIntertwining, Representation.tprod_apply]
  have h := map_eq_smul_map_metricRaw_of_invariant hF (X := dualRightDualRightToMatrix v)
    (by simpa [F] using fun g => hinv _)
  refine ⟨(dualRightDualRightToMatrix v 0 1 - dualRightDualRightToMatrix v 1 0) / 2, ?_⟩
  simpa [F, metricVal] using h

end TensorSquares

/-!

### E.2. Invariant elements

-/

/-- The `SL(2,ℂ)`-invariants of `LeftHandedWeyl ⊗ LeftHandedWeyl` are the line through the
  metric `εᵃᵃ`. -/
lemma LeftHandedWeyl.invariants_tprod_eq_span_metricVal :
    (rep.tprod rep).invariants = ℂ ∙ metricVal := by
  simpa using invariants_inf_range_eq_span_map_metricVal (Representation.IntertwiningMap.id _)

/-- The `SL(2,ℂ)`-invariants of `DualLeftHandedWeyl ⊗ DualLeftHandedWeyl` are the line through
  the metric `εₐₐ`. -/
lemma DualLeftHandedWeyl.invariants_tprod_eq_span_metricVal :
    (rep.tprod rep).invariants = ℂ ∙ metricVal := by
  simpa using invariants_inf_range_eq_span_map_metricVal (Representation.IntertwiningMap.id _)

/-- The `SL(2,ℂ)`-invariants of `RightHandedWeyl ⊗ RightHandedWeyl` are the line through the
  metric `ε^{ȧȧ}`. -/
lemma RightHandedWeyl.invariants_tprod_eq_span_metricVal :
    (rep.tprod rep).invariants = ℂ ∙ metricVal := by
  simpa using invariants_inf_range_eq_span_map_metricVal (Representation.IntertwiningMap.id _)

/-- The `SL(2,ℂ)`-invariants of `DualRightHandedWeyl ⊗ DualRightHandedWeyl` are the line through
  the metric `ε_{ȧȧ}`. -/
lemma DualRightHandedWeyl.invariants_tprod_eq_span_metricVal :
    (rep.tprod rep).invariants = ℂ ∙ metricVal := by
  simpa using invariants_inf_range_eq_span_map_metricVal (Representation.IntertwiningMap.id _)

/-!

### E.3. Intertwining maps out of the trivial representation

-/

/-- Every intertwining map from the trivial representation into
  `LeftHandedWeyl ⊗ LeftHandedWeyl` is a multiple of the metric `εᵃᵃ`. -/
lemma LeftHandedWeyl.intertwiningMap_eq_smul_metric
    (φ : (Representation.trivial ℂ SL(2,ℂ) ℂ).IntertwiningMap (rep.tprod rep)) :
    ∃ z : ℂ, φ = z • metric :=
  Representation.IntertwiningMap.exists_eq_smul_of_invariants_eq_span
    (by rw [metric_apply_one]; exact invariants_tprod_eq_span_metricVal) φ

/-- Every intertwining map from the trivial representation into
  `DualLeftHandedWeyl ⊗ DualLeftHandedWeyl` is a multiple of the metric `εₐₐ`. -/
lemma DualLeftHandedWeyl.intertwiningMap_eq_smul_metric
    (φ : (Representation.trivial ℂ SL(2,ℂ) ℂ).IntertwiningMap (rep.tprod rep)) :
    ∃ z : ℂ, φ = z • metric :=
  Representation.IntertwiningMap.exists_eq_smul_of_invariants_eq_span
    (by rw [metric_apply_one]; exact invariants_tprod_eq_span_metricVal) φ

/-- Every intertwining map from the trivial representation into
  `RightHandedWeyl ⊗ RightHandedWeyl` is a multiple of the metric `ε^{ȧȧ}`. -/
lemma RightHandedWeyl.intertwiningMap_eq_smul_metric
    (φ : (Representation.trivial ℂ SL(2,ℂ) ℂ).IntertwiningMap (rep.tprod rep)) :
    ∃ z : ℂ, φ = z • metric :=
  Representation.IntertwiningMap.exists_eq_smul_of_invariants_eq_span
    (by rw [metric_apply_one]; exact invariants_tprod_eq_span_metricVal) φ

/-- Every intertwining map from the trivial representation into
  `DualRightHandedWeyl ⊗ DualRightHandedWeyl` is a multiple of the metric `ε_{ȧȧ}`. -/
lemma DualRightHandedWeyl.intertwiningMap_eq_smul_metric
    (φ : (Representation.trivial ℂ SL(2,ℂ) ℂ).IntertwiningMap (rep.tprod rep)) :
    ∃ z : ℂ, φ = z • metric :=
  Representation.IntertwiningMap.exists_eq_smul_of_invariants_eq_span
    (by rw [metric_apply_one]; exact invariants_tprod_eq_span_metricVal) φ

/-!

## F. Components of a tensor product of two Weyl representations

The other twelve tensor products of two Weyl representations are handled uniformly through
their matrix of components, `tensorToMatrix`, on which `SL(2,ℂ)` acts by `X ↦ K₁ X K₂ᵀ` with
`Kᵢ` the matrices of the two factors (F.1). Every argument below only tests this action against
four elements of `SL(2,ℂ)`, the boosts `boostTwo` and `boostHalf` along `z`, the half turn `phase`
about `z`, and `epsilon` (F.2).

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

/-- An equivariant map out of `V ⊗ W` is unchanged by an element of `SL(2,ℂ)` acting on the
  components `Y`, when the image of `Y` is invariant. -/
lemma map_symm_act_eq {ρV : Representation ℂ SL(2,ℂ) V} {ρW : Representation ℂ SL(2,ℂ) W}
    {B : Type*} [AddCommGroup B] [Module ℂ B] {ρ : Representation ℂ SL(2,ℂ) B}
    (f : (ρV.tprod ρW).IntertwiningMap ρ) {Y : Matrix (Fin 2) (Fin 2) ℂ}
    (hY : ∀ g, ρ g (f ((tensorToMatrix b c).symm Y)) = f ((tensorToMatrix b c).symm Y))
    {Φ : Matrix (Fin 2) (Fin 2) ℂ → Matrix (Fin 2) (Fin 2) ℂ}
    (h : ∃ g, ∀ X, LinearMap.toMatrix b b (ρV g) * X * (LinearMap.toMatrix c c (ρW g))ᵀ = Φ X) :
    f ((tensorToMatrix b c).symm (Φ Y)) = f ((tensorToMatrix b c).symm Y) := by
  obtain ⟨g, hg⟩ := h
  have hmap := tensorToMatrix_map b c (ρV g) (ρW g) ((tensorToMatrix b c).symm Y)
  rw [LinearEquiv.apply_symm_apply] at hmap
  rw [← hg, ← hmap, LinearEquiv.symm_apply_apply]
  exact (f.isIntertwining _ _ g _).trans (hY g)

end Components

/-!

### F.2. Four elements of `SL(2, ℂ)`

-/

/-- The boost along `z` with matrix `diag (2, 2⁻¹)`. -/
def _root_.Lorentz.SL2C.boostTwo : SL(2,ℂ) := ⟨!![2, 0; 0, 2⁻¹], by simp [det_fin_two_of]⟩

/-- The boost along `z` with matrix `diag (2⁻¹, 2)`, the inverse of `boostTwo`. -/
def _root_.Lorentz.SL2C.boostHalf : SL(2,ℂ) := ⟨!![2⁻¹, 0; 0, 2], by simp [det_fin_two_of]⟩

/-- The rotation by `π` about `z`, with matrix `diag (i, -i)`. -/
def _root_.Lorentz.SL2C.phase : SL(2,ℂ) :=
  ⟨!![Complex.I, 0; 0, -Complex.I], by simp [det_fin_two_of]⟩

/-- Computes `K₁ X K₂ᵀ` entrywise, for `Kᵢ` the matrix of a Weyl representation at one of
  `boostTwo`, `boostHalf`, `phase` or `epsilon`. -/
scoped macro "weyl_act" : tactic => `(tactic| (
  intro X
  simp only [LeftHandedWeyl.rep_toMatrix, DualLeftHandedWeyl.rep_toMatrix,
    RightHandedWeyl.rep_toMatrix, DualRightHandedWeyl.rep_toMatrix, Lorentz.SL2C.inverse_coe,
    SpecialLinearGroup.coe_inv]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [adjugate_fin_two, Lorentz.SL2C.boostTwo, Lorentz.SL2C.boostHalf, Lorentz.SL2C.phase,
      Lorentz.SL2C.epsilon_coe, Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct,
      map_ofNat] <;> (try ring_nf) <;> (try simp) <;> (try ring_nf)))

/-!

## G. Two indices of opposite chirality

A left-handed and a right-handed index carry the vector representation, which has no invariants.
On components the boosts scale either the diagonal or the off-diagonal entries, depending on
whether exactly one of the two factors is dual, and the half turn `phase` negates the other half.
The boosts kill the scaled half and the half turn shows that the rest is its own negative, so
every invariant in the image of an equivariant map vanishes.

-/

/-!

### G.1. Matrices

-/

section OppositeChirality

variable {B : Type*} [AddCommGroup B] [Module ℂ B]

/-- A linear map on matrices unchanged at `X` by the boosts scaling the diagonal entries of `X`
  by `4` and `4⁻¹`, and by negating the off-diagonal entries of `X`, vanishes at `X`. -/
lemma map_eq_zero_of_diagonal_scale (F : Matrix (Fin 2) (Fin 2) ℂ →ₗ[ℂ] B)
    {X : Matrix (Fin 2) (Fin 2) ℂ} (h1 : F !![4 * X 0 0, X 0 1; X 1 0, X 1 1 / 4] = F X)
    (h2 : F !![X 0 0 / 4, X 0 1; X 1 0, 4 * X 1 1] = F X)
    (h3 : F !![X 0 0, -X 0 1; -X 1 0, X 1 1] = F X) : F X = 0 := by
  have hdiag : F !![X 0 0, 0; 0, X 1 1] = 0 := by
    have hsplit : !![X 0 0, 0; 0, X 1 1] = (4 / 9 : ℂ) • (!![4 * X 0 0, X 0 1; X 1 0, X 1 1 / 4]
        + !![X 0 0 / 4, X 0 1; X 1 0, 4 * X 1 1] - (2 : ℂ) • X) := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp <;> ring
    rw [hsplit, map_smul, map_sub, map_add, map_smul, h1, h2]
    module
  have hneg : !![X 0 0, -X 0 1; -X 1 0, X 1 1] = (2 : ℂ) • !![X 0 0, 0; 0, X 1 1] - X := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp <;> ring
  rw [hneg, map_sub, map_smul, hdiag, smul_zero, zero_sub] at h3
  have h : (2 : ℂ) • F X = 0 := by
    rw [two_smul]
    nth_rewrite 1 [← h3]
    exact neg_add_cancel _
  exact (smul_eq_zero.mp h).resolve_left two_ne_zero

/-- A linear map on matrices unchanged at `X` by the boosts scaling the off-diagonal entries of
  `X` by `4` and `4⁻¹`, and by negating the diagonal entries of `X`, vanishes at `X`. -/
lemma map_eq_zero_of_offDiagonal_scale (F : Matrix (Fin 2) (Fin 2) ℂ →ₗ[ℂ] B)
    {X : Matrix (Fin 2) (Fin 2) ℂ} (h1 : F !![X 0 0, 4 * X 0 1; X 1 0 / 4, X 1 1] = F X)
    (h2 : F !![X 0 0, X 0 1 / 4; 4 * X 1 0, X 1 1] = F X)
    (h3 : F !![-X 0 0, X 0 1; X 1 0, -X 1 1] = F X) : F X = 0 := by
  have hoff : F !![0, X 0 1; X 1 0, 0] = 0 := by
    have hsplit : !![0, X 0 1; X 1 0, 0] = (4 / 9 : ℂ) • (!![X 0 0, 4 * X 0 1; X 1 0 / 4, X 1 1]
        + !![X 0 0, X 0 1 / 4; 4 * X 1 0, X 1 1] - (2 : ℂ) • X) := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp <;> ring
    rw [hsplit, map_smul, map_sub, map_add, map_smul, h1, h2]
    module
  have hneg : !![-X 0 0, X 0 1; X 1 0, -X 1 1] = (2 : ℂ) • !![0, X 0 1; X 1 0, 0] - X := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp <;> ring
  rw [hneg, map_sub, map_smul, hoff, smul_zero, zero_sub] at h3
  have h : (2 : ℂ) • F X = 0 := by
    rw [two_smul]
    nth_rewrite 1 [← h3]
    exact neg_add_cancel _
  exact (smul_eq_zero.mp h).resolve_left two_ne_zero

/-!

### G.2. Tensor products

-/

/-- For an equivariant map `f` out of `V ⊗ W`, on which three elements of `SL(2,ℂ)` act on
  components by scaling the diagonal entries and by negating the off-diagonal entries, the only
  invariant in the image of `f` is zero. -/
lemma invariants_inf_range_eq_bot_of_diagonal_scale {V W : Type*} [AddCommGroup V]
    [Module ℂ V] [AddCommGroup W] [Module ℂ W] (b : Module.Basis (Fin 2) ℂ V)
    (c : Module.Basis (Fin 2) ℂ W) {ρV : Representation ℂ SL(2,ℂ) V}
    {ρW : Representation ℂ SL(2,ℂ) W} {ρ : Representation ℂ SL(2,ℂ) B}
    (f : (ρV.tprod ρW).IntertwiningMap ρ)
    (h1 : ∃ g, ∀ X, LinearMap.toMatrix b b (ρV g) * X * (LinearMap.toMatrix c c (ρW g))ᵀ =
      !![4 * X 0 0, X 0 1; X 1 0, X 1 1 / 4])
    (h2 : ∃ g, ∀ X, LinearMap.toMatrix b b (ρV g) * X * (LinearMap.toMatrix c c (ρW g))ᵀ =
      !![X 0 0 / 4, X 0 1; X 1 0, 4 * X 1 1])
    (h3 : ∃ g, ∀ X, LinearMap.toMatrix b b (ρV g) * X * (LinearMap.toMatrix c c (ρW g))ᵀ =
      !![X 0 0, -X 0 1; -X 1 0, X 1 1]) :
    ρ.invariants ⊓ f.range.toSubmodule = ⊥ := by
  refine Representation.invariants_inf_range_eq_bot fun _ hinv hx => ?_
  obtain ⟨v, rfl⟩ := hx
  have hinv' (g : SL(2,ℂ)) : ρ g (f ((tensorToMatrix b c).symm (tensorToMatrix b c v))) =
      f ((tensorToMatrix b c).symm (tensorToMatrix b c v)) := by
    rw [LinearEquiv.symm_apply_apply]
    exact hinv g
  set F := f.toLinearMap ∘ₗ (tensorToMatrix b c).symm.toLinearMap with hF
  have hFa (Z : Matrix (Fin 2) (Fin 2) ℂ) : F Z = f ((tensorToMatrix b c).symm Z) := by
    rw [hF, LinearMap.comp_apply, LinearEquiv.coe_coe,
      Representation.IntertwiningMap.toLinearMap_apply]
  have h := map_eq_zero_of_diagonal_scale F (X := tensorToMatrix b c v)
    (by rw [hFa, hFa]; exact (map_symm_act_eq b c f hinv' (h := h1) :))
    (by rw [hFa, hFa]; exact (map_symm_act_eq b c f hinv' (h := h2) :))
    (by rw [hFa, hFa]; exact (map_symm_act_eq b c f hinv' (h := h3) :))
  rwa [hFa, LinearEquiv.symm_apply_apply] at h

/-- For an equivariant map `f` out of `V ⊗ W`, on which three elements of `SL(2,ℂ)` act on
  components by scaling the off-diagonal entries and by negating the diagonal entries, the only
  invariant in the image of `f` is zero. -/
lemma invariants_inf_range_eq_bot_of_offDiagonal_scale {V W : Type*} [AddCommGroup V]
    [Module ℂ V] [AddCommGroup W] [Module ℂ W] (b : Module.Basis (Fin 2) ℂ V)
    (c : Module.Basis (Fin 2) ℂ W) {ρV : Representation ℂ SL(2,ℂ) V}
    {ρW : Representation ℂ SL(2,ℂ) W} {ρ : Representation ℂ SL(2,ℂ) B}
    (f : (ρV.tprod ρW).IntertwiningMap ρ)
    (h1 : ∃ g, ∀ X, LinearMap.toMatrix b b (ρV g) * X * (LinearMap.toMatrix c c (ρW g))ᵀ =
      !![X 0 0, 4 * X 0 1; X 1 0 / 4, X 1 1])
    (h2 : ∃ g, ∀ X, LinearMap.toMatrix b b (ρV g) * X * (LinearMap.toMatrix c c (ρW g))ᵀ =
      !![X 0 0, X 0 1 / 4; 4 * X 1 0, X 1 1])
    (h3 : ∃ g, ∀ X, LinearMap.toMatrix b b (ρV g) * X * (LinearMap.toMatrix c c (ρW g))ᵀ =
      !![-X 0 0, X 0 1; X 1 0, -X 1 1]) :
    ρ.invariants ⊓ f.range.toSubmodule = ⊥ := by
  refine Representation.invariants_inf_range_eq_bot fun _ hinv hx => ?_
  obtain ⟨v, rfl⟩ := hx
  have hinv' (g : SL(2,ℂ)) : ρ g (f ((tensorToMatrix b c).symm (tensorToMatrix b c v))) =
      f ((tensorToMatrix b c).symm (tensorToMatrix b c v)) := by
    rw [LinearEquiv.symm_apply_apply]
    exact hinv g
  set F := f.toLinearMap ∘ₗ (tensorToMatrix b c).symm.toLinearMap with hF
  have hFa (Z : Matrix (Fin 2) (Fin 2) ℂ) : F Z = f ((tensorToMatrix b c).symm Z) := by
    rw [hF, LinearMap.comp_apply, LinearEquiv.coe_coe,
      Representation.IntertwiningMap.toLinearMap_apply]
  have h := map_eq_zero_of_offDiagonal_scale F (X := tensorToMatrix b c v)
    (by rw [hFa, hFa]; exact (map_symm_act_eq b c f hinv' (h := h1) :))
    (by rw [hFa, hFa]; exact (map_symm_act_eq b c f hinv' (h := h2) :))
    (by rw [hFa, hFa]; exact (map_symm_act_eq b c f hinv' (h := h3) :))
  rwa [hFa, LinearEquiv.symm_apply_apply] at h

/-!

### G.3. The eight pairs

For each pair `X ⊗ Y` of opposite chirality there are three statements, named after the second
factor `Y` in the namespace of the first factor `X`. The invariants in the image of an equivariant
map vanish, `X.invariants_inf_range_tprod_Y_eq_bot`; so do the invariants themselves,
`X.invariants_tprod_Y_eq_bot`; and so does every intertwining map out of the trivial
representation, `X.intertwiningMap_tprod_Y_eq_zero`.

-/

variable {ρ : Representation ℂ SL(2,ℂ) B}

/-- For an equivariant map `f` out of `LeftHandedWeyl ⊗ RightHandedWeyl`, the only
  `SL(2,ℂ)`-invariant in the image of `f` is zero. -/
lemma LeftHandedWeyl.invariants_inf_range_tprod_rightHandedWeyl_eq_bot
    (f : (LeftHandedWeyl.rep.tprod RightHandedWeyl.rep).IntertwiningMap ρ) :
    ρ.invariants ⊓ f.range.toSubmodule = ⊥ :=
  invariants_inf_range_eq_bot_of_diagonal_scale LeftHandedWeyl.basis RightHandedWeyl.basis f
    ⟨Lorentz.SL2C.boostTwo, by weyl_act⟩ ⟨Lorentz.SL2C.boostHalf, by weyl_act⟩
    ⟨Lorentz.SL2C.phase, by weyl_act⟩

/-- The only `SL(2,ℂ)`-invariant element of `LeftHandedWeyl ⊗ RightHandedWeyl` is zero. -/
lemma LeftHandedWeyl.invariants_tprod_rightHandedWeyl_eq_bot :
    (LeftHandedWeyl.rep.tprod RightHandedWeyl.rep).invariants = ⊥ := by
  simpa using
    invariants_inf_range_tprod_rightHandedWeyl_eq_bot (Representation.IntertwiningMap.id _)

/-- Every intertwining map from the trivial representation into `LeftHandedWeyl ⊗ RightHandedWeyl`
  is zero. -/
lemma LeftHandedWeyl.intertwiningMap_tprod_rightHandedWeyl_eq_zero
    (φ : (Representation.trivial ℂ SL(2,ℂ) ℂ).IntertwiningMap
      (LeftHandedWeyl.rep.tprod RightHandedWeyl.rep)) :
    φ = 0 :=
  Representation.IntertwiningMap.eq_zero_of_invariants_eq_bot
    invariants_tprod_rightHandedWeyl_eq_bot φ

/-- For an equivariant map `f` out of `DualLeftHandedWeyl ⊗ DualRightHandedWeyl`, the only
  `SL(2,ℂ)`-invariant in the image of `f` is zero. -/
lemma DualLeftHandedWeyl.invariants_inf_range_tprod_dualRightHandedWeyl_eq_bot
    (f : (DualLeftHandedWeyl.rep.tprod DualRightHandedWeyl.rep).IntertwiningMap ρ) :
    ρ.invariants ⊓ f.range.toSubmodule = ⊥ :=
  invariants_inf_range_eq_bot_of_diagonal_scale DualLeftHandedWeyl.basis DualRightHandedWeyl.basis f
    ⟨Lorentz.SL2C.boostHalf, by weyl_act⟩ ⟨Lorentz.SL2C.boostTwo, by weyl_act⟩
    ⟨Lorentz.SL2C.phase, by weyl_act⟩

/-- The only `SL(2,ℂ)`-invariant element of `DualLeftHandedWeyl ⊗ DualRightHandedWeyl` is zero. -/
lemma DualLeftHandedWeyl.invariants_tprod_dualRightHandedWeyl_eq_bot :
    (DualLeftHandedWeyl.rep.tprod DualRightHandedWeyl.rep).invariants = ⊥ := by
  simpa using
    invariants_inf_range_tprod_dualRightHandedWeyl_eq_bot (Representation.IntertwiningMap.id _)

/-- Every intertwining map from the trivial representation into `DualLeftHandedWeyl ⊗
  DualRightHandedWeyl` is zero. -/
lemma DualLeftHandedWeyl.intertwiningMap_tprod_dualRightHandedWeyl_eq_zero
    (φ : (Representation.trivial ℂ SL(2,ℂ) ℂ).IntertwiningMap
      (DualLeftHandedWeyl.rep.tprod DualRightHandedWeyl.rep)) :
    φ = 0 :=
  Representation.IntertwiningMap.eq_zero_of_invariants_eq_bot
    invariants_tprod_dualRightHandedWeyl_eq_bot φ

/-- For an equivariant map `f` out of `RightHandedWeyl ⊗ LeftHandedWeyl`, the only
  `SL(2,ℂ)`-invariant in the image of `f` is zero. -/
lemma RightHandedWeyl.invariants_inf_range_tprod_leftHandedWeyl_eq_bot
    (f : (RightHandedWeyl.rep.tprod LeftHandedWeyl.rep).IntertwiningMap ρ) :
    ρ.invariants ⊓ f.range.toSubmodule = ⊥ :=
  invariants_inf_range_eq_bot_of_diagonal_scale RightHandedWeyl.basis LeftHandedWeyl.basis f
    ⟨Lorentz.SL2C.boostTwo, by weyl_act⟩ ⟨Lorentz.SL2C.boostHalf, by weyl_act⟩
    ⟨Lorentz.SL2C.phase, by weyl_act⟩

/-- The only `SL(2,ℂ)`-invariant element of `RightHandedWeyl ⊗ LeftHandedWeyl` is zero. -/
lemma RightHandedWeyl.invariants_tprod_leftHandedWeyl_eq_bot :
    (RightHandedWeyl.rep.tprod LeftHandedWeyl.rep).invariants = ⊥ := by
  simpa using invariants_inf_range_tprod_leftHandedWeyl_eq_bot (Representation.IntertwiningMap.id _)

/-- Every intertwining map from the trivial representation into `RightHandedWeyl ⊗ LeftHandedWeyl`
  is zero. -/
lemma RightHandedWeyl.intertwiningMap_tprod_leftHandedWeyl_eq_zero
    (φ : (Representation.trivial ℂ SL(2,ℂ) ℂ).IntertwiningMap
      (RightHandedWeyl.rep.tprod LeftHandedWeyl.rep)) :
    φ = 0 :=
  Representation.IntertwiningMap.eq_zero_of_invariants_eq_bot
    invariants_tprod_leftHandedWeyl_eq_bot φ

/-- For an equivariant map `f` out of `DualRightHandedWeyl ⊗ DualLeftHandedWeyl`, the only
  `SL(2,ℂ)`-invariant in the image of `f` is zero. -/
lemma DualRightHandedWeyl.invariants_inf_range_tprod_dualLeftHandedWeyl_eq_bot
    (f : (DualRightHandedWeyl.rep.tprod DualLeftHandedWeyl.rep).IntertwiningMap ρ) :
    ρ.invariants ⊓ f.range.toSubmodule = ⊥ :=
  invariants_inf_range_eq_bot_of_diagonal_scale DualRightHandedWeyl.basis DualLeftHandedWeyl.basis f
    ⟨Lorentz.SL2C.boostHalf, by weyl_act⟩ ⟨Lorentz.SL2C.boostTwo, by weyl_act⟩
    ⟨Lorentz.SL2C.phase, by weyl_act⟩

/-- The only `SL(2,ℂ)`-invariant element of `DualRightHandedWeyl ⊗ DualLeftHandedWeyl` is zero. -/
lemma DualRightHandedWeyl.invariants_tprod_dualLeftHandedWeyl_eq_bot :
    (DualRightHandedWeyl.rep.tprod DualLeftHandedWeyl.rep).invariants = ⊥ := by
  simpa using
    invariants_inf_range_tprod_dualLeftHandedWeyl_eq_bot (Representation.IntertwiningMap.id _)

/-- Every intertwining map from the trivial representation into `DualRightHandedWeyl ⊗
  DualLeftHandedWeyl` is zero. -/
lemma DualRightHandedWeyl.intertwiningMap_tprod_dualLeftHandedWeyl_eq_zero
    (φ : (Representation.trivial ℂ SL(2,ℂ) ℂ).IntertwiningMap
      (DualRightHandedWeyl.rep.tprod DualLeftHandedWeyl.rep)) :
    φ = 0 :=
  Representation.IntertwiningMap.eq_zero_of_invariants_eq_bot
    invariants_tprod_dualLeftHandedWeyl_eq_bot φ

/-- For an equivariant map `f` out of `LeftHandedWeyl ⊗ DualRightHandedWeyl`, the only
  `SL(2,ℂ)`-invariant in the image of `f` is zero. -/
lemma LeftHandedWeyl.invariants_inf_range_tprod_dualRightHandedWeyl_eq_bot
    (f : (LeftHandedWeyl.rep.tprod DualRightHandedWeyl.rep).IntertwiningMap ρ) :
    ρ.invariants ⊓ f.range.toSubmodule = ⊥ :=
  invariants_inf_range_eq_bot_of_offDiagonal_scale LeftHandedWeyl.basis DualRightHandedWeyl.basis f
    ⟨Lorentz.SL2C.boostTwo, by weyl_act⟩ ⟨Lorentz.SL2C.boostHalf, by weyl_act⟩
    ⟨Lorentz.SL2C.phase, by weyl_act⟩

/-- The only `SL(2,ℂ)`-invariant element of `LeftHandedWeyl ⊗ DualRightHandedWeyl` is zero. -/
lemma LeftHandedWeyl.invariants_tprod_dualRightHandedWeyl_eq_bot :
    (LeftHandedWeyl.rep.tprod DualRightHandedWeyl.rep).invariants = ⊥ := by
  simpa using
    invariants_inf_range_tprod_dualRightHandedWeyl_eq_bot (Representation.IntertwiningMap.id _)

/-- Every intertwining map from the trivial representation into `LeftHandedWeyl ⊗
  DualRightHandedWeyl` is zero. -/
lemma LeftHandedWeyl.intertwiningMap_tprod_dualRightHandedWeyl_eq_zero
    (φ : (Representation.trivial ℂ SL(2,ℂ) ℂ).IntertwiningMap
      (LeftHandedWeyl.rep.tprod DualRightHandedWeyl.rep)) :
    φ = 0 :=
  Representation.IntertwiningMap.eq_zero_of_invariants_eq_bot
    invariants_tprod_dualRightHandedWeyl_eq_bot φ

/-- For an equivariant map `f` out of `DualLeftHandedWeyl ⊗ RightHandedWeyl`, the only
  `SL(2,ℂ)`-invariant in the image of `f` is zero. -/
lemma DualLeftHandedWeyl.invariants_inf_range_tprod_rightHandedWeyl_eq_bot
    (f : (DualLeftHandedWeyl.rep.tprod RightHandedWeyl.rep).IntertwiningMap ρ) :
    ρ.invariants ⊓ f.range.toSubmodule = ⊥ :=
  invariants_inf_range_eq_bot_of_offDiagonal_scale DualLeftHandedWeyl.basis RightHandedWeyl.basis f
    ⟨Lorentz.SL2C.boostHalf, by weyl_act⟩ ⟨Lorentz.SL2C.boostTwo, by weyl_act⟩
    ⟨Lorentz.SL2C.phase, by weyl_act⟩

/-- The only `SL(2,ℂ)`-invariant element of `DualLeftHandedWeyl ⊗ RightHandedWeyl` is zero. -/
lemma DualLeftHandedWeyl.invariants_tprod_rightHandedWeyl_eq_bot :
    (DualLeftHandedWeyl.rep.tprod RightHandedWeyl.rep).invariants = ⊥ := by
  simpa using
    invariants_inf_range_tprod_rightHandedWeyl_eq_bot (Representation.IntertwiningMap.id _)

/-- Every intertwining map from the trivial representation into `DualLeftHandedWeyl ⊗
  RightHandedWeyl` is zero. -/
lemma DualLeftHandedWeyl.intertwiningMap_tprod_rightHandedWeyl_eq_zero
    (φ : (Representation.trivial ℂ SL(2,ℂ) ℂ).IntertwiningMap
      (DualLeftHandedWeyl.rep.tprod RightHandedWeyl.rep)) :
    φ = 0 :=
  Representation.IntertwiningMap.eq_zero_of_invariants_eq_bot
    invariants_tprod_rightHandedWeyl_eq_bot φ

/-- For an equivariant map `f` out of `RightHandedWeyl ⊗ DualLeftHandedWeyl`, the only
  `SL(2,ℂ)`-invariant in the image of `f` is zero. -/
lemma RightHandedWeyl.invariants_inf_range_tprod_dualLeftHandedWeyl_eq_bot
    (f : (RightHandedWeyl.rep.tprod DualLeftHandedWeyl.rep).IntertwiningMap ρ) :
    ρ.invariants ⊓ f.range.toSubmodule = ⊥ :=
  invariants_inf_range_eq_bot_of_offDiagonal_scale RightHandedWeyl.basis DualLeftHandedWeyl.basis f
    ⟨Lorentz.SL2C.boostTwo, by weyl_act⟩ ⟨Lorentz.SL2C.boostHalf, by weyl_act⟩
    ⟨Lorentz.SL2C.phase, by weyl_act⟩

/-- The only `SL(2,ℂ)`-invariant element of `RightHandedWeyl ⊗ DualLeftHandedWeyl` is zero. -/
lemma RightHandedWeyl.invariants_tprod_dualLeftHandedWeyl_eq_bot :
    (RightHandedWeyl.rep.tprod DualLeftHandedWeyl.rep).invariants = ⊥ := by
  simpa using
    invariants_inf_range_tprod_dualLeftHandedWeyl_eq_bot (Representation.IntertwiningMap.id _)

/-- Every intertwining map from the trivial representation into `RightHandedWeyl ⊗
  DualLeftHandedWeyl` is zero. -/
lemma RightHandedWeyl.intertwiningMap_tprod_dualLeftHandedWeyl_eq_zero
    (φ : (Representation.trivial ℂ SL(2,ℂ) ℂ).IntertwiningMap
      (RightHandedWeyl.rep.tprod DualLeftHandedWeyl.rep)) :
    φ = 0 :=
  Representation.IntertwiningMap.eq_zero_of_invariants_eq_bot
    invariants_tprod_dualLeftHandedWeyl_eq_bot φ

/-- For an equivariant map `f` out of `DualRightHandedWeyl ⊗ LeftHandedWeyl`, the only
  `SL(2,ℂ)`-invariant in the image of `f` is zero. -/
lemma DualRightHandedWeyl.invariants_inf_range_tprod_leftHandedWeyl_eq_bot
    (f : (DualRightHandedWeyl.rep.tprod LeftHandedWeyl.rep).IntertwiningMap ρ) :
    ρ.invariants ⊓ f.range.toSubmodule = ⊥ :=
  invariants_inf_range_eq_bot_of_offDiagonal_scale DualRightHandedWeyl.basis LeftHandedWeyl.basis f
    ⟨Lorentz.SL2C.boostHalf, by weyl_act⟩ ⟨Lorentz.SL2C.boostTwo, by weyl_act⟩
    ⟨Lorentz.SL2C.phase, by weyl_act⟩

/-- The only `SL(2,ℂ)`-invariant element of `DualRightHandedWeyl ⊗ LeftHandedWeyl` is zero. -/
lemma DualRightHandedWeyl.invariants_tprod_leftHandedWeyl_eq_bot :
    (DualRightHandedWeyl.rep.tprod LeftHandedWeyl.rep).invariants = ⊥ := by
  simpa using invariants_inf_range_tprod_leftHandedWeyl_eq_bot (Representation.IntertwiningMap.id _)

/-- Every intertwining map from the trivial representation into `DualRightHandedWeyl ⊗
  LeftHandedWeyl` is zero. -/
lemma DualRightHandedWeyl.intertwiningMap_tprod_leftHandedWeyl_eq_zero
    (φ : (Representation.trivial ℂ SL(2,ℂ) ℂ).IntertwiningMap
      (DualRightHandedWeyl.rep.tprod LeftHandedWeyl.rep)) :
    φ = 0 :=
  Representation.IntertwiningMap.eq_zero_of_invariants_eq_bot
    invariants_tprod_leftHandedWeyl_eq_bot φ

end OppositeChirality

end

end Fermion
