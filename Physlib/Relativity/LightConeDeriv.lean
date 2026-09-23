/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Relativity.LorentzGroup.Boosts.Axis
/-!
# The light-cone basis of an axis

A tuple of spacetime directions can be re-read in the light-cone basis along a boost axis:
`lightConeCoeff` gives the four light-cone directions `D₀ - Dᵢ`, `D₀ + Dᵢ` and the two
transverse ones, and `lightConeCoeffInv` the inverse change of basis.  The point of the
change of basis is `sum_boostAxis_lightConeCoeff`: the four directions are eigenvectors of
the boost along the axis, of weight `lightConeWeight` — `+2` for `D₀ - Dᵢ`, `-2` for
`D₀ + Dᵢ`, and `0` for the transverse directions.

On a tuple of slots the two coefficient matrices are still inverse to one another
(`sum_prod_lightConeCoeff`, `sum_prod_lightConeCoeffInv`) and the weights add
(`sum_prod_lightConeCoeff`).  That is what the classification of the Lorentz invariants in
`LorentzGroup/Invariants` runs on: it writes a coefficient tensor in this basis and keeps
only the piece of total weight zero.

-/

@[expose] public section

namespace Lorentz

open Matrix MatrixGroups

/-- The four light-cone directions along the `i`-th axis, written as coefficient vectors on
  the coordinate directions: `D₀ - Dᵢ`, `D₀ + Dᵢ`, and the two transverse directions. -/
def lightConeCoeff (i : Fin 3) (κ : Fin 4) (μ : Fin 1 ⊕ Fin 3) : ℂ :=
  if κ = 0 then (if μ = Sum.inl 0 then 1 else if μ = Sum.inr i then -1 else 0)
  else if κ = 1 then (if μ = Sum.inl 0 then 1 else if μ = Sum.inr i then 1 else 0)
  else if κ = 2 then (if μ = Sum.inr (i + 1) then 1 else 0)
  else (if μ = Sum.inr (i + 2) then 1 else 0)

/-- The boost weight carried by each light-cone direction: `+2` for `D₀ - Dᵢ`, `-2` for
  `D₀ + Dᵢ`, and `0` for the two transverse directions. -/
def lightConeWeight (κ : Fin 4) : ℤ := if κ = 0 then 2 else if κ = 1 then -2 else 0

/-- **The light-cone directions are eigenvectors of the boost.** Along the `i`-th axis
  `D₀ - Dᵢ` is scaled by `t²`, `D₀ + Dᵢ` by `t⁻²`, and the two transverse directions are
  fixed. -/
lemma sum_boostAxis_lightConeCoeff (i : Fin 3) (κ : Fin 4) (ν : Fin 1 ⊕ Fin 3)
    {t : ℝ} (ht : t ≠ 0) :
    ∑ μ : Fin 1 ⊕ Fin 3,
        (((SL2C.toLorentzGroup (SL2C.boostAxis i t ht)).1 ν μ : ℝ) : ℂ) * lightConeCoeff i κ μ
      = ((t : ℝ) : ℂ) ^ (lightConeWeight κ) * lightConeCoeff i κ ν := by
  have htc : ((t : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [show SL2C.toLorentzGroup (SL2C.boostAxis i t ht) = LorentzGroup.boostAxis i t ht from rfl]
  rcases ν with a | j
  · rw [Subsingleton.elim a 0]
    fin_cases i <;> fin_cases κ
    all_goals
      simp [lightConeCoeff, lightConeWeight, Fintype.sum_sum_type,
        LorentzGroup.boostAxis_apply]
    all_goals try field_simp
    all_goals try ring
  · fin_cases i <;> fin_cases j <;> fin_cases κ
    all_goals
      simp [lightConeCoeff, lightConeWeight, Fintype.sum_sum_type,
        LorentzGroup.boostAxis_apply]
    all_goals try field_simp
    all_goals try ring

/-- The coordinate directions written back in the light-cone basis: `D₀` and `Dᵢ` are the
  half-sum and half-difference of `D₀ ∓ Dᵢ`, and the transverse directions are themselves. -/
noncomputable def lightConeCoeffInv (i : Fin 3) (μ : Fin 1 ⊕ Fin 3) (κ : Fin 4) : ℂ :=
  if μ = Sum.inl 0 then (if κ = 0 then 2⁻¹ else if κ = 1 then 2⁻¹ else 0)
  else if μ = Sum.inr i then (if κ = 0 then -2⁻¹ else if κ = 1 then 2⁻¹ else 0)
  else if μ = Sum.inr (i + 1) then (if κ = 2 then 1 else 0)
  else (if κ = 3 then 1 else 0)

/-- The inverse coefficient toward the first transverse direction vanishes off it. -/
lemma lightConeCoeffInv_two_eq_zero (i : Fin 3) {μ : Fin 1 ⊕ Fin 3}
    (hμ : μ ≠ Sum.inr (i + 1)) : lightConeCoeffInv i μ 2 = 0 := by
  simp [lightConeCoeffInv, hμ]

/-- The inverse coefficient toward the second transverse direction vanishes off it. -/
lemma lightConeCoeffInv_three_eq_zero (i : Fin 3) {μ : Fin 1 ⊕ Fin 3}
    (hμ : μ ≠ Sum.inr (i + 2)) : lightConeCoeffInv i μ 3 = 0 := by
  rcases μ with a | m
  · rw [Subsingleton.elim a 0]
    simp [lightConeCoeffInv]
  · fin_cases i <;> fin_cases m <;> simp_all [lightConeCoeffInv]

/-- The light-cone basis is a basis: the two coefficient matrices are inverse. -/
lemma sum_lightConeCoeffInv_mul (i : Fin 3) (μ ν : Fin 1 ⊕ Fin 3) :
    ∑ κ : Fin 4, lightConeCoeffInv i μ κ * lightConeCoeff i κ ν = if μ = ν then 1 else 0 := by
  rcases μ with a | j
  · rw [Subsingleton.elim a 0]
    rcases ν with a' | j'
    · rw [Subsingleton.elim a' 0]
      fin_cases i <;>
        simp [lightConeCoeff, lightConeCoeffInv, Fin.sum_univ_four] <;> norm_num
    · fin_cases i <;> fin_cases j' <;>
        simp [lightConeCoeff, lightConeCoeffInv, Fin.sum_univ_four]
  · rcases ν with a' | j'
    · rw [Subsingleton.elim a' 0]
      fin_cases i <;> fin_cases j <;>
        simp [lightConeCoeff, lightConeCoeffInv, Fin.sum_univ_four]
    · fin_cases i <;> fin_cases j <;> fin_cases j' <;>
        simp [lightConeCoeff, lightConeCoeffInv, Fin.sum_univ_four] <;> norm_num

/-- The scalar behind `lightConeDeriv_mem`: the boost acts on a light-cone multi-index
  slot by slot, so the product of the per-slot eigenvalues factors out. -/
lemma sum_prod_lightConeCoeff (i : Fin 3) {n : ℕ} (c : Fin n → Fin 4)
    (a : Fin n → Fin 1 ⊕ Fin 3) {t : ℝ} (ht : t ≠ 0) :
    ∑ d : Fin n → Fin 1 ⊕ Fin 3, (∏ j, lightConeCoeff i (c j) (d j)) *
        (∏ j, (((SL2C.toLorentzGroup (SL2C.boostAxis i t ht)).1 (a j) (d j) : ℝ) : ℂ))
      = ((t : ℝ) : ℂ) ^ (∑ j, lightConeWeight (c j)) * ∏ j, lightConeCoeff i (c j) (a j) := by
  have htc : ((t : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  have hzpow : ∀ (s : Finset (Fin n)) (g : Fin n → ℤ),
      ∏ j ∈ s, ((t : ℝ) : ℂ) ^ (g j) = ((t : ℝ) : ℂ) ^ (∑ j ∈ s, g j) := by
    intro s g
    induction s using Finset.induction with
    | empty => simp
    | insert a s ha ih => rw [Finset.prod_insert ha, Finset.sum_insert ha, ih, zpow_add₀ htc]
  calc ∑ d : Fin n → Fin 1 ⊕ Fin 3, (∏ j, lightConeCoeff i (c j) (d j)) *
        (∏ j, (((SL2C.toLorentzGroup (SL2C.boostAxis i t ht)).1 (a j) (d j) : ℝ) : ℂ))
      = ∑ d : Fin n → Fin 1 ⊕ Fin 3, ∏ j, (lightConeCoeff i (c j) (d j) *
          (((SL2C.toLorentzGroup (SL2C.boostAxis i t ht)).1 (a j) (d j) : ℝ) : ℂ)) :=
        Finset.sum_congr rfl fun d _ => (Finset.prod_mul_distrib).symm
    _ = ∏ j, ∑ μ : Fin 1 ⊕ Fin 3, (lightConeCoeff i (c j) μ *
          (((SL2C.toLorentzGroup (SL2C.boostAxis i t ht)).1 (a j) μ : ℝ) : ℂ)) := by
        rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
    _ = ∏ j, (((t : ℝ) : ℂ) ^ (lightConeWeight (c j)) * lightConeCoeff i (c j) (a j)) := by
        refine Finset.prod_congr rfl fun j _ => ?_
        simp_rw [mul_comm (lightConeCoeff i (c j) _)]
        exact sum_boostAxis_lightConeCoeff i (c j) (a j) ht
    _ = (∏ j, ((t : ℝ) : ℂ) ^ (lightConeWeight (c j))) * ∏ j, lightConeCoeff i (c j) (a j) :=
        Finset.prod_mul_distrib
    _ = ((t : ℝ) : ℂ) ^ (∑ j, lightConeWeight (c j)) * ∏ j, lightConeCoeff i (c j) (a j) := by
        rw [hzpow]

/-- The two coefficient matrices are inverse slot by slot, hence inverse on multi-indices;
  this is `sum_prod_lightConeCoeff` with the two factors the other way round. -/
lemma sum_prod_lightConeCoeffInv (i : Fin 3) {n : ℕ} (d e : Fin n → Fin 1 ⊕ Fin 3) :
    ∑ c : Fin n → Fin 4, (∏ j, lightConeCoeffInv i (d j) (c j)) *
        (∏ j, lightConeCoeff i (c j) (e j)) = if d = e then 1 else 0 := by
  calc ∑ c : Fin n → Fin 4, (∏ j, lightConeCoeffInv i (d j) (c j)) *
        (∏ j, lightConeCoeff i (c j) (e j))
      = ∑ c : Fin n → Fin 4,
          ∏ j, (lightConeCoeffInv i (d j) (c j) * lightConeCoeff i (c j) (e j)) :=
        Finset.sum_congr rfl fun c _ => (Finset.prod_mul_distrib).symm
    _ = ∏ j, ∑ κ : Fin 4, (lightConeCoeffInv i (d j) κ * lightConeCoeff i κ (e j)) := by
        rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
    _ = ∏ j, (if d j = e j then (1 : ℂ) else 0) :=
        Finset.prod_congr rfl fun j _ => sum_lightConeCoeffInv_mul i (d j) (e j)
    _ = if d = e then 1 else 0 := by
        by_cases hde : d = e
        · subst hde
          simp
        · rw [ite_eq_right hde]
          obtain ⟨j, hj⟩ := Function.ne_iff.1 hde
          exact Finset.prod_eq_zero (Finset.mem_univ j) (ite_eq_right hj)

end Lorentz
