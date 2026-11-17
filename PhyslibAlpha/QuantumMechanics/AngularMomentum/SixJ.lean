/-
Copyright (c) 2026 Daniel Leonforte. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Leonforte
-/
module

public import PhyslibAlpha.QuantumMechanics.AngularMomentum.CouplingSchemes

/-!

# Recoupling coefficients and the 6j symbols

The recoupling coefficients between the two coupling schemes of `j₁ ⊗ j₂ ⊗ j₃` and the
6j symbols, with their independence of `M` and their orthogonality.

## i. Overview

The two coupling schemes `stateA` and `stateB` of `CouplingSchemes` consist of eigenvectors of
the total `J²` and `J_z`. The recoupling coefficient
`⟨(j₁ j₂) j₁₂, j₃; J M | j₁, (j₂ j₃) j₂₃; J M⟩` is the contravariant form between the two
(`recoupling`). The main results are:

- both schemes consist of eigenvectors of the total `J²` and `J_z`, so states of different `J` or
  `M` are orthogonal (`tripleForm_stateA_stateB_eq_zero`);
- the first scheme is an orthonormal basis (`eq_sum_vecA`), so the recoupling coefficients form
  an orthogonal matrix (`sum_recoupling_mul_recoupling`);
- the recoupling coefficients do not depend on `M` (`recoupling_eq_recoupling_zero`): the total
  lowering operator moves `M` in both schemes by the same factor `√((J + M)(J - M + 1))`, and it
  is adjoint to the raising operator.

The 6j symbol is defined by
`⟨(j₁ j₂) j₁₂, j₃; J | j₁, (j₂ j₃) j₂₃; J⟩ = (-1)^(j₁ + j₂ + j₃ + J) √((2j₁₂ + 1)(2j₂₃ + 1))
{j₁ j₂ j₁₂; j₃ J j₂₃}` (`sixJ`), and satisfies
`Σ_{j₁₂} (2j₁₂ + 1)(2j₂₃ + 1) {j₁ j₂ j₁₂; j₃ J j₂₃} {j₁ j₂ j₁₂; j₃ J j₂₃'} = δ_{j₂₃ j₂₃'}`
(`sum_sixJ_mul_sixJ`).

Racah's closed formula for the 6j symbols is not proved here.

## ii. Key results

- `eq_sum_vecA`: completeness of the first scheme.
- `tripleForm_stateA_stateB_eq_zero`: separation by `J` and `M`.
- `recoupling`, `recoupling_eq_recoupling_zero`, `sum_recoupling_mul_recoupling`.
- `sixJ`, `recoupling_eq_sixJ`, `sum_sixJ_mul_sixJ`.

## iii. Table of contents

- A. Eigenvalues, ladders and orthonormality of the coupled states
  - A.1. Completeness of the first coupling scheme
  - A.2. Separation by `J` and `M`
  - A.3. The recoupling coefficients
  - A.4. Orthogonality
- B. The 6j symbols

## iv. References

- G. Racah, *Theory of complex spectra. II*, Phys. Rev. 62, 438 (1942).
- A. R. Edmonds, *Angular Momentum in Quantum Mechanics*, Princeton University Press (1957),
  chapter 6.

-/

@[expose] public section

noncomputable section

namespace PhyslibAlpha.Sl2

open StandardSl2Module

open scoped TensorProduct

/-!

## A. Eigenvalues, ladders and orthonormality of the coupled states

-/

section Coupled

variable {a b c : ℕ}

section A

variable (hab : 0 < a + b) (hc : 0 < c) (k₁ : Fin (min a b + 1)) {k₂ : ℕ}
  (h₁ : k₂ ≤ a + b - 2 * (k₁ : ℕ)) (h₂ : k₂ ≤ c)

include hc h₁ h₂ in
lemma tripleH_stateA (l : ℕ) :
    tripleH a b c (stateA hab k₁ k₂ l) =
      (((a + b - 2 * (k₁ : ℕ) + c - 2 * k₂ : ℕ) : ℝ) - 2 * l) • stateA hab k₁ k₂ l := by
  rw [stateA, tripleH_rTensor_embed, tensorH_coupledVec (by omega) h₁ h₂, map_smul]

include hc h₁ h₂ in
lemma tripleCas_stateA (l : ℕ) :
    tripleCas a b c (stateA hab k₁ k₂ l) =
      (((a + b - 2 * (k₁ : ℕ) + c - 2 * k₂ : ℕ) : ℝ) *
        (((a + b - 2 * (k₁ : ℕ) + c - 2 * k₂ : ℕ) : ℝ) + 2) / 2) • stateA hab k₁ k₂ l := by
  rw [stateA, tripleCas_rTensor_embed, tensorCas_coupledVec (by omega) h₁ h₂, map_smul]

include h₁ h₂ in
lemma tripleF_stateA {l : ℕ} (hl : l < a + b - 2 * (k₁ : ℕ) + c - 2 * k₂) :
    tripleF a b c (stateA hab k₁ k₂ l) =
      Real.sqrt (((l : ℝ) + 1) * (((a + b - 2 * (k₁ : ℕ) + c - 2 * k₂ : ℕ) : ℝ) - l)) •
        stateA hab k₁ k₂ (l + 1) := by
  rw [stateA, stateA, tripleF_rTensor_embed, tensorF_coupledVec h₁ h₂ hl, map_smul]

end A

section B

variable (hbc : 0 < b + c) (ha : 0 < a) (k₃ : Fin (min b c + 1)) {k₄ : ℕ}
  (h₃ : k₄ ≤ a) (h₄ : k₄ ≤ b + c - 2 * (k₃ : ℕ))

include ha h₃ h₄ in
lemma tripleH_stateB (l : ℕ) :
    tripleH a b c (stateB hbc k₃ k₄ l) =
      (((a + (b + c - 2 * (k₃ : ℕ)) - 2 * k₄ : ℕ) : ℝ) - 2 * l) • stateB hbc k₃ k₄ l := by
  rw [stateB, tripleH_assocEmbed, tensorH_coupledVec (by omega) h₃ h₄, map_smul]

include ha h₃ h₄ in
lemma tripleCas_stateB (l : ℕ) :
    tripleCas a b c (stateB hbc k₃ k₄ l) =
      (((a + (b + c - 2 * (k₃ : ℕ)) - 2 * k₄ : ℕ) : ℝ) *
        (((a + (b + c - 2 * (k₃ : ℕ)) - 2 * k₄ : ℕ) : ℝ) + 2) / 2) • stateB hbc k₃ k₄ l := by
  rw [stateB, tripleCas_assocEmbed, tensorCas_coupledVec (by omega) h₃ h₄, map_smul]

include ha h₃ h₄ in
lemma tripleE_stateB_succ {l : ℕ} (hl : l < a + (b + c - 2 * (k₃ : ℕ)) - 2 * k₄) :
    tripleE a b c (stateB hbc k₃ k₄ (l + 1)) =
      Real.sqrt (((l : ℝ) + 1) * (((a + (b + c - 2 * (k₃ : ℕ)) - 2 * k₄ : ℕ) : ℝ) - l)) •
        stateB hbc k₃ k₄ l := by
  rw [stateB, stateB, tripleE_assocEmbed, tensorE_coupledVec_succ (by omega) h₃ h₄ hl, map_smul]

include ha h₃ h₄ in
lemma tripleForm_stateB_self {l : ℕ} (hl : l ≤ a + (b + c - 2 * (k₃ : ℕ)) - 2 * k₄) :
    tripleForm a b c (stateB hbc k₃ k₄ l) (stateB hbc k₃ k₄ l) = 1 := by
  rw [stateB, tripleForm_assocEmbed, tensorForm_coupledVec (by omega) h₃ h₄ h₃ h₄ hl,
    ite_eq_left ⟨rfl, rfl⟩]

lemma tripleForm_stateB_of_ne {k₃' : Fin (min b c + 1)} (hk : k₃ ≠ k₃') (k₄' l l' : ℕ) :
    tripleForm a b c (stateB hbc k₃ k₄ l) (stateB hbc k₃' k₄' l') = 0 := by
  rw [stateB, stateB, tripleForm_assocEmbed_of_ne hbc k₃ hk]

end B

/-!

### A.1. Completeness of the first coupling scheme

-/

/-- An orthonormal family of `finrank` many vectors expands every vector. -/
lemma eq_sum_of_orthonormal {ι M : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι] [AddCommGroup M]
    [Module ℝ M] (B : LinearMap.BilinForm ℝ M) (v : ι → M)
    (hv : ∀ i j, B (v i) (v j) = if i = j then 1 else 0)
    (hcard : Fintype.card ι = Module.finrank ℝ M) (x : M) :
    x = ∑ i, B (v i) x • v i := by
  have hli : LinearIndependent ℝ v := by
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    have h := congrArg (B (v i)) hg
    simp only [map_sum, map_smul, smul_eq_mul, hv, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq,
      Finset.mem_univ, ite_true, map_zero] at h
    exact h
  let bas := basisOfLinearIndependentOfCardEqFinrank hli hcard
  have hx := bas.sum_repr x
  have hrepr : ∀ i, bas.repr x i = B (v i) x := fun i => by
    have h := congrArg (B (v i)) hx
    simp only [map_sum, map_smul, smul_eq_mul, bas, coe_basisOfLinearIndependentOfCardEqFinrank, hv,
      mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true] at h
    exact h
  conv_lhs => rw [← hx]
  simp only [hrepr, bas, coe_basisOfLinearIndependentOfCardEqFinrank]

variable (a b c) in
/-- The index set `(k₁, k₂, l)` of the first coupling scheme. -/
abbrev IndexA : Type := Σ k₁ : Fin (min a b + 1), StringIndex (a + b - 2 * (k₁ : ℕ)) c

instance : Nonempty (IndexA a b c) := ⟨⟨0, Classical.arbitrary _⟩⟩

/-- The states of the first coupling scheme, as a family indexed by `IndexA`. -/
def vecA (hab : 0 < a + b) (i : IndexA a b c) : Triple a b c := stateA hab i.1 i.2.1 i.2.2

lemma card_indexA : Fintype.card (IndexA a b c) = Module.finrank ℝ (Triple a b c) := by
  rw [Fintype.card_sigma, Module.finrank_tensorProduct, Module.finrank_tensorProduct,
    finrank_standardSl2Module, finrank_standardSl2Module, finrank_standardSl2Module]
  simp only [card_stringIndex]
  rw [← Finset.sum_mul]
  congr 1
  rw [← card_stringIndex (m := a) (n := b), Fintype.card_sigma]
  simp only [Fintype.card_fin]

lemma tripleForm_vecA (hab : 0 < a + b) (hc : 0 < c) (i j : IndexA a b c) :
    tripleForm a b c (vecA hab i) (vecA hab j) = if i = j then 1 else 0 := by
  obtain ⟨k₁, k₂, l⟩ := i
  obtain ⟨k₁', k₂', l'⟩ := j
  simp only [vecA]
  by_cases hk : k₁ = k₁'
  · subst hk
    have h2 := k₂.isLt
    have h2' := k₂'.isLt
    have hl := l.isLt
    rw [stateA, stateA, tripleForm_rTensor_embed, tensorForm_coupledVec (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega)]
    refine if_congr ⟨fun h => ?_, fun h => ?_⟩ rfl rfl
    · obtain ⟨hk₂, hl'⟩ := h
      obtain rfl : k₂ = k₂' := Fin.ext hk₂
      obtain rfl : l = l' := Fin.ext hl'
      rfl
    · simp only [Sigma.mk.inj_iff, heq_eq_eq, true_and] at h
      obtain ⟨rfl, h'⟩ := h
      exact ⟨rfl, congrArg Fin.val (eq_of_heq h')⟩
  · rw [stateA, stateA, tripleForm_rTensor_embed_of_ne hab _ hk,
      ite_eq_right (fun h => hk (congrArg Sigma.fst h))]

/-- **Completeness.** The states `|(j₁ j₂) j₁₂, j₃; J, M⟩` form an orthonormal basis. -/
lemma eq_sum_vecA (hab : 0 < a + b) (hc : 0 < c) (x : Triple a b c) :
    x = ∑ i, tripleForm a b c (vecA hab i) x • vecA hab i :=
  eq_sum_of_orthonormal _ _ (tripleForm_vecA hab hc) card_indexA x

/-!

### A.2. Separation by `J` and `M`

-/

lemma nat_eq_of_mul_add_two_eq {p q : ℕ} (h : p * (p + 2) = q * (q + 2)) : p = q := by
  rcases lt_trichotomy p q with hpq | hpq | hpq
  · exfalso
    nlinarith
  · exact hpq
  · exfalso
    nlinarith

/-- States of different total `J` or different `M` are orthogonal. -/
lemma tripleForm_stateA_stateB_eq_zero (hab : 0 < a + b) (hbc : 0 < b + c) (ha : 0 < a)
    (hc : 0 < c) {k₁ : Fin (min a b + 1)} {k₃ : Fin (min b c + 1)} {k₂ k₄ l' l : ℕ}
    (h₁ : k₂ ≤ a + b - 2 * (k₁ : ℕ)) (h₂ : k₂ ≤ c) (h₃ : k₄ ≤ a)
    (h₄ : k₄ ≤ b + c - 2 * (k₃ : ℕ)) (h : ¬((k₁ : ℕ) + k₂ = k₃ + k₄ ∧ l' = l)) :
    tripleForm a b c (stateA hab k₁ k₂ l') (stateB hbc k₃ k₄ l) = 0 := by
  by_contra hne
  have hk₁ := k₁.isLt
  have hk₃ := k₃.isLt
  have hC := tripleForm_tripleCas (stateA hab k₁ k₂ l') (stateB hbc k₃ k₄ l)
  rw [tripleCas_stateA hab hc k₁ h₁ h₂, tripleCas_stateB hbc ha k₃ h₃ h₄, map_smul,
    LinearMap.smul_apply, map_smul, smul_eq_mul, smul_eq_mul] at hC
  have hH := tripleForm_tripleH (stateA hab k₁ k₂ l') (stateB hbc k₃ k₄ l)
  rw [tripleH_stateA hab hc k₁ h₁ h₂, tripleH_stateB hbc ha k₃ h₃ h₄, map_smul,
    LinearMap.smul_apply, map_smul, smul_eq_mul, smul_eq_mul] at hH
  have hC' := mul_right_cancel₀ hne hC
  have hH' := mul_right_cancel₀ hne hH
  have hF : a + b - 2 * (k₁ : ℕ) + c - 2 * k₂ = a + (b + c - 2 * (k₃ : ℕ)) - 2 * k₄ :=
    nat_eq_of_mul_add_two_eq (by exact_mod_cast (show
      ((a + b - 2 * (k₁ : ℕ) + c - 2 * k₂ : ℕ) : ℝ) *
        (((a + b - 2 * (k₁ : ℕ) + c - 2 * k₂ : ℕ) : ℝ) + 2) =
      ((a + (b + c - 2 * (k₃ : ℕ)) - 2 * k₄ : ℕ) : ℝ) *
        (((a + (b + c - 2 * (k₃ : ℕ)) - 2 * k₄ : ℕ) : ℝ) + 2) by linarith))
  rw [hF] at hH'
  have hl : l' = l := by exact_mod_cast (show (l' : ℝ) = l by linarith)
  exact h ⟨by omega, hl⟩

/-!

### A.3. The recoupling coefficients

-/

variable (a b c) in
/-- `k₁` gives an admissible intermediate `j₁₂` for the total `J = (a + b + c)/2 - K`. -/
abbrev ValidA (K k₁ : ℕ) : Prop := k₁ ≤ K ∧ K - k₁ ≤ a + b - 2 * k₁ ∧ K - k₁ ≤ c

variable (a b c) in
/-- `k₃` gives an admissible intermediate `j₂₃` for the total `J = (a + b + c)/2 - K`. -/
abbrev ValidB (K k₃ : ℕ) : Prop := k₃ ≤ K ∧ K - k₃ ≤ a ∧ K - k₃ ≤ b + c - 2 * k₃

/-- The recoupling coefficient `⟨(j₁ j₂) j₁₂, j₃; J M | j₁, (j₂ j₃) j₂₃; J M⟩` with
`J = (a + b + c)/2 - K`, `M = J - l`, `j₁₂ = (a + b)/2 - k₁` and `j₂₃ = (b + c)/2 - k₃`. -/
def recoupling (hab : 0 < a + b) (hbc : 0 < b + c) (K l : ℕ) (k₁ : Fin (min a b + 1))
    (k₃ : Fin (min b c + 1)) : ℝ :=
  tripleForm a b c (stateA hab k₁ (K - k₁) l) (stateB hbc k₃ (K - k₃) l)

lemma recoupling_succ (hab : 0 < a + b) (hbc : 0 < b + c) (ha : 0 < a) {K l : ℕ}
    {k₁ : Fin (min a b + 1)} {k₃ : Fin (min b c + 1)} (hA : ValidA a b c K k₁)
    (hB : ValidB a b c K k₃) (hl : l < a + b + c - 2 * K) :
    recoupling hab hbc K (l + 1) k₁ k₃ = recoupling hab hbc K l k₁ k₃ := by
  obtain ⟨hA1, hA2, hA3⟩ := hA
  obtain ⟨hB1, hB2, hB3⟩ := hB
  have hk₁ := k₁.isLt
  have hk₃ := k₃.isLt
  have hFA : a + b - 2 * (k₁ : ℕ) + c - 2 * (K - k₁) = a + b + c - 2 * K := by omega
  have hFB : a + (b + c - 2 * (k₃ : ℕ)) - 2 * (K - k₃) = a + b + c - 2 * K := by omega
  have hF := tripleF_stateA hab k₁ hA2 hA3 (l := l) (by omega)
  have hE := tripleE_stateB_succ hbc ha k₃ hB2 hB3 (l := l) (by omega)
  rw [hFA] at hF
  rw [hFB] at hE
  have hlF : (l : ℝ) < ((a + b + c - 2 * K : ℕ) : ℝ) := by exact_mod_cast hl
  have hpos : 0 < Real.sqrt (((l : ℝ) + 1) * (((a + b + c - 2 * K : ℕ) : ℝ) - l)) :=
    Real.sqrt_pos.mpr (mul_pos (by positivity) (by linarith))
  have key := tripleForm_tripleF (stateA hab k₁ (K - k₁) l) (stateB hbc k₃ (K - k₃) (l + 1))
  rw [hF, hE, map_smul, LinearMap.smul_apply, map_smul, smul_eq_mul, smul_eq_mul] at key
  exact mul_left_cancel₀ hpos.ne' key

/-- The recoupling coefficients do not depend on `M`. -/
lemma recoupling_eq_recoupling_zero (hab : 0 < a + b) (hbc : 0 < b + c) (ha : 0 < a)
    {K l : ℕ} {k₁ : Fin (min a b + 1)} {k₃ : Fin (min b c + 1)} (hA : ValidA a b c K k₁)
    (hB : ValidB a b c K k₃) (hl : l ≤ a + b + c - 2 * K) :
    recoupling hab hbc K l k₁ k₃ = recoupling hab hbc K 0 k₁ k₃ := by
  induction l with
  | zero => rfl
  | succ l ih => rw [recoupling_succ hab hbc ha hA hB (by omega), ih (by omega)]

/-!

### A.4. Orthogonality

-/

/-- **Orthogonality of the recoupling coefficients.** For fixed `J` and `M`,
`Σ_{j₁₂} ⟨(j₁ j₂) j₁₂, j₃; J M | j₁, (j₂ j₃) j₂₃; J M⟩ ⟨(j₁ j₂) j₁₂, j₃; J M |
j₁, (j₂ j₃) j₂₃'; J M⟩ = δ_{j₂₃ j₂₃'}`. -/
lemma sum_recoupling_mul_recoupling (hab : 0 < a + b) (hbc : 0 < b + c) (ha : 0 < a)
    (hc : 0 < c) {K l : ℕ} (hl : l ≤ a + b + c - 2 * K) {k₃ k₃' : Fin (min b c + 1)}
    (hB : ValidB a b c K k₃) (hB' : ValidB a b c K k₃') :
    ∑ k₁ : Fin (min a b + 1), (if ValidA a b c K k₁ then
      recoupling hab hbc K l k₁ k₃ * recoupling hab hbc K l k₁ k₃' else 0) =
        if k₃ = k₃' then 1 else 0 := by
  obtain ⟨hB1, hB2, hB3⟩ := hB
  obtain ⟨hB1', hB2', hB3'⟩ := hB'
  have hk₃ := k₃.isLt
  have hk₃' := k₃'.isLt
  have hBB : tripleForm a b c (stateB hbc k₃ (K - k₃) l) (stateB hbc k₃' (K - k₃') l) =
      if k₃ = k₃' then 1 else 0 := by
    by_cases hk : k₃ = k₃'
    · subst hk
      rw [ite_eq_left rfl, tripleForm_stateB_self hbc ha k₃ hB2 hB3 (by omega)]
    · rw [ite_eq_right hk, tripleForm_stateB_of_ne hbc k₃ hk]
  rw [← hBB]
  conv_rhs => rw [eq_sum_vecA hab hc (stateB hbc k₃' (K - k₃') l)]
  rw [map_sum, Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun k₁ _ => ?_
  have hk₁ := k₁.isLt
  rw [Fintype.sum_sigma]
  by_cases hv : ValidA a b c K k₁
  · obtain ⟨hA1, hA2, hA3⟩ := hv
    rw [ite_eq_left ⟨hA1, hA2, hA3⟩]
    have hk₂ : K - (k₁ : ℕ) < min (a + b - 2 * (k₁ : ℕ)) c + 1 := by omega
    rw [Fintype.sum_eq_single ⟨K - k₁, hk₂⟩]
    · have hl' : l < a + b - 2 * (k₁ : ℕ) + c - 2 * (K - k₁) + 1 := by omega
      rw [Fintype.sum_eq_single ⟨l, hl'⟩]
      · simp only [vecA, map_smul, smul_eq_mul, recoupling]
        rw [tripleForm_comm (stateB hbc k₃ (K - k₃) l)]
        ring
      · intro l' hl''
        simp only [vecA, map_smul, smul_eq_mul]
        rw [tripleForm_stateA_stateB_eq_zero hab hbc ha hc hA2 hA3 hB2' hB3'
          (fun h => hl'' (Fin.ext h.2)), zero_mul]
    · intro k₂ hk₂'
      have := k₂.isLt
      refine Finset.sum_eq_zero fun l' _ => ?_
      simp only [vecA, map_smul, smul_eq_mul]
      rw [tripleForm_stateA_stateB_eq_zero hab hbc ha hc (by omega) (by omega) hB2' hB3'
        (fun h => hk₂' (Fin.ext (show (k₂ : ℕ) = K - (k₁ : ℕ) by have := h.1; omega))),
        zero_mul]
  · rw [ite_eq_right hv]
    refine (Finset.sum_eq_zero fun k₂ _ => ?_).symm
    refine Finset.sum_eq_zero fun l' _ => ?_
    have := k₂.isLt
    simp only [vecA, map_smul, smul_eq_mul]
    rw [tripleForm_stateA_stateB_eq_zero hab hbc ha hc (by omega) (by omega) hB2' hB3'
      (fun h => hv (by obtain ⟨h1, _⟩ := h; exact ⟨by omega, by omega, by omega⟩)), zero_mul]

/-!

## B. The 6j symbols

-/

/-- The **6j symbol** `{j₁ j₂ j₁₂; j₃ J j₂₃}`, with `j₁ = a/2`, `j₂ = b/2`, `j₃ = c/2`,
`j₁₂ = (a + b)/2 - k₁`, `j₂₃ = (b + c)/2 - k₃` and `J = (a + b + c)/2 - K`, defined through
`⟨(j₁ j₂) j₁₂, j₃; J | j₁, (j₂ j₃) j₂₃; J⟩ = (-1)^(j₁ + j₂ + j₃ + J) √((2j₁₂ + 1)(2j₂₃ + 1)) {6j}`
(`j₁ + j₂ + j₃ + J = a + b + c - K`), and zero for inadmissible arguments. -/
def sixJ (hab : 0 < a + b) (hbc : 0 < b + c) (K : ℕ) (k₁ : Fin (min a b + 1))
    (k₃ : Fin (min b c + 1)) : ℝ :=
  if ValidA a b c K k₁ ∧ ValidB a b c K k₃ then
    (-1) ^ (a + b + c - K) * recoupling hab hbc K 0 k₁ k₃ /
      Real.sqrt (((a + b - 2 * (k₁ : ℕ) + 1 : ℕ) : ℝ) * ((b + c - 2 * (k₃ : ℕ) + 1 : ℕ) : ℝ))
  else 0

/-- The recoupling coefficients in terms of the 6j symbols, for every `M`. -/
lemma recoupling_eq_sixJ (hab : 0 < a + b) (hbc : 0 < b + c) (ha : 0 < a) {K l : ℕ}
    {k₁ : Fin (min a b + 1)} {k₃ : Fin (min b c + 1)} (hA : ValidA a b c K k₁)
    (hB : ValidB a b c K k₃) (hl : l ≤ a + b + c - 2 * K) :
    recoupling hab hbc K l k₁ k₃ = (-1) ^ (a + b + c - K) *
      Real.sqrt (((a + b - 2 * (k₁ : ℕ) + 1 : ℕ) : ℝ) * ((b + c - 2 * (k₃ : ℕ) + 1 : ℕ) : ℝ)) *
        sixJ hab hbc K k₁ k₃ := by
  have hpos : 0 < Real.sqrt (((a + b - 2 * (k₁ : ℕ) + 1 : ℕ) : ℝ) *
      ((b + c - 2 * (k₃ : ℕ) + 1 : ℕ) : ℝ)) := Real.sqrt_pos.mpr (by positivity)
  have hs : ((-1 : ℝ) ^ (a + b + c - K)) * (-1) ^ (a + b + c - K) = 1 := by
    rw [← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow]
  rw [sixJ, ite_eq_left ⟨hA, hB⟩, recoupling_eq_recoupling_zero hab hbc ha hA hB hl]
  field_simp
  linear_combination (-(recoupling hab hbc K 0 k₁ k₃)) * hs

lemma mul_mul_div_mul_div_sqrt {s U U' p₁ p₃ p₃' : ℝ} (hs : s * s = 1) (h₁ : 0 < p₁) :
    p₁ * p₃ * (s * U / Real.sqrt (p₁ * p₃)) * (s * U' / Real.sqrt (p₁ * p₃')) =
      Real.sqrt p₃ / Real.sqrt p₃' * (U * U') := by
  rw [Real.sqrt_mul h₁.le, Real.sqrt_mul h₁.le]
  have e₁ := Real.mul_self_sqrt h₁.le
  calc _ = (s * s) * (p₁ / (Real.sqrt p₁ * Real.sqrt p₁)) * (p₃ / Real.sqrt p₃) *
        (U * U' / Real.sqrt p₃') := by ring
    _ = _ := by rw [hs, e₁, div_self h₁.ne', Real.div_sqrt]; ring

/-- **Orthogonality of the 6j symbols.**
`Σ_{j₁₂} (2j₁₂ + 1)(2j₂₃ + 1) {j₁ j₂ j₁₂; j₃ J j₂₃} {j₁ j₂ j₁₂; j₃ J j₂₃'} = δ_{j₂₃ j₂₃'}`. -/
lemma sum_sixJ_mul_sixJ (hab : 0 < a + b) (hbc : 0 < b + c) (ha : 0 < a) (hc : 0 < c)
    {K : ℕ} {k₃ k₃' : Fin (min b c + 1)} (hB : ValidB a b c K k₃)
    (hB' : ValidB a b c K k₃') :
    ∑ k₁ : Fin (min a b + 1), ((a + b - 2 * (k₁ : ℕ) + 1 : ℕ) : ℝ) *
      ((b + c - 2 * (k₃ : ℕ) + 1 : ℕ) : ℝ) * sixJ hab hbc K k₁ k₃ * sixJ hab hbc K k₁ k₃' =
        if k₃ = k₃' then 1 else 0 := by
  have hs : ((-1 : ℝ) ^ (a + b + c - K)) * (-1) ^ (a + b + c - K) = 1 := by
    rw [← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow]
  have key : ∀ k₁ : Fin (min a b + 1), ((a + b - 2 * (k₁ : ℕ) + 1 : ℕ) : ℝ) *
      ((b + c - 2 * (k₃ : ℕ) + 1 : ℕ) : ℝ) * sixJ hab hbc K k₁ k₃ * sixJ hab hbc K k₁ k₃' =
      Real.sqrt ((b + c - 2 * (k₃ : ℕ) + 1 : ℕ) : ℝ) /
        Real.sqrt ((b + c - 2 * (k₃' : ℕ) + 1 : ℕ) : ℝ) *
        (if ValidA a b c K k₁ then
          recoupling hab hbc K 0 k₁ k₃ * recoupling hab hbc K 0 k₁ k₃' else 0) := fun k₁ => by
    by_cases hv : ValidA a b c K k₁
    · rw [sixJ, sixJ, ite_eq_left ⟨hv, hB⟩, ite_eq_left ⟨hv, hB'⟩, ite_eq_left hv]
      exact mul_mul_div_mul_div_sqrt hs (by positivity)
    · rw [sixJ, ite_eq_right (fun h => hv h.1), ite_eq_right hv]
      ring
  rw [Finset.sum_congr rfl fun k₁ _ => key k₁, ← Finset.mul_sum,
    sum_recoupling_mul_recoupling hab hbc ha hc (Nat.zero_le _) hB hB']
  by_cases hk : k₃ = k₃'
  · subst hk
    have hpos : 0 < Real.sqrt ((b + c - 2 * (k₃ : ℕ) + 1 : ℕ) : ℝ) :=
      Real.sqrt_pos.mpr (by positivity)
    rw [ite_eq_left rfl, div_self hpos.ne', one_mul]
  · rw [ite_eq_right hk, mul_zero]

end Coupled

end PhyslibAlpha.Sl2
