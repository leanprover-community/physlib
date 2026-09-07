/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Relativity.LorentzGroup.Boosts.WeightGrading
/-!
# Light-cone derivative symbols

A family of symbols indexed by tuples of spacetime directions can be re-read in the
light-cone basis along a boost axis: `lightConeCoeff` gives the four light-cone
directions `D₀ - Dᵢ`, `D₀ + Dᵢ` and the two transverse ones, `lightConeCoeffInv` the
inverse change of basis, and `lightConeDeriv` the symbol read in that basis.  The point
of the change of basis is `lightConeDeriv_mem`: a light-cone symbol is a boost
eigenvector, of weight `∑ j, lightConeWeight (c j)` — `+2` for `D₀ - Dᵢ`, `-2` for
`D₀ + Dᵢ`, and `0` for the transverse directions — on top of whatever weight its
argument already carries.

The hypothesis the development runs on is `RotatesIndices`: every index of the symbol
map is a Lorentz vector index.

-/

@[expose] public section

namespace Lorentz

open Matrix MatrixGroups Lorentz.BoostWeight

variable {B : Type} [Ring B] [Algebra ℂ B] {repLorentz : Representation ℂ SL(2,ℂ) B}
  {W : Type} [AddCommGroup W] [Module ℂ W] {repW : Representation ℂ SL(2,ℂ) W}

/-- **One shape's worth of the rotation law**: every derivative index of `F` is a Lorentz
  vector index. This is all the boost-weight development below uses, so it is taken as a
  hypothesis; `IsDerivativeCollection.rotatesIndices` supplies it for each partition. -/
abbrev RotatesIndices (repW : Representation ℂ SL(2,ℂ) W)
    (repLorentz : Representation ℂ SL(2,ℂ) B) {n : ℕ}
    (F : (Fin n → Fin 1 ⊕ Fin 3) → W →ₗ[ℂ] B) : Prop :=
  ∀ (g : SL(2,ℂ)) (d : Fin n → Fin 1 ⊕ Fin 3) (w : W),
    repLorentz g (F d w) = ∑ (a : Fin n → Fin 1 ⊕ Fin 3),
      (∏ (j : Fin n), (((SL2C.toLorentzGroup g).1 (a j) (d j) : ℝ) : ℂ)) • F a (repW g w)

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

/-- The inverse coefficient of the first transverse direction is supported on its own
  light-cone index. -/
lemma lightConeCoeffInv_transverse_one_eq_zero (i : Fin 3) {μ : Fin 1 ⊕ Fin 3} {κ : Fin 4}
    (hμ : μ = Sum.inr (i + 1)) (hκ : κ ≠ 2) : lightConeCoeffInv i μ κ = 0 := by
  subst hμ
  fin_cases i <;> fin_cases κ <;> simp_all [lightConeCoeffInv]

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

/-- **The symbol with its derivative indices in the light-cone basis.** Each slot `j` of the
  multi-index carries a light-cone direction `c j` instead of a coordinate direction, so the
  symbol is an eigenvector of the boost along the `i`-th axis, of weight
  `∑ j, lightConeWeight (c j)`. -/
noncomputable def lightConeDeriv {n : ℕ} (F : (Fin n → Fin 1 ⊕ Fin 3) → W →ₗ[ℂ] B)
    (i : Fin 3) (c : Fin n → Fin 4) : W →ₗ[ℂ] B :=
  ∑ d : Fin n → Fin 1 ⊕ Fin 3, (∏ j, lightConeCoeff i (c j) (d j)) • F d

/-- **A one-slot light-cone symbol**, written out as a combination of coordinate symbols. -/
lemma lightConeDeriv_single (F : (Fin 1 → Fin 1 ⊕ Fin 3) → W →ₗ[ℂ] B) (i : Fin 3) (κ : Fin 4) :
    lightConeDeriv F i ![κ] = ∑ μ : Fin 1 ⊕ Fin 3, lightConeCoeff i κ μ • F ![μ] := by
  rw [lightConeDeriv]
  refine Fintype.sum_equiv (Equiv.funUnique (Fin 1) (Fin 1 ⊕ Fin 3)) _ _ fun d => ?_
  have hd : d = ![d 0] := by
    funext j
    fin_cases j
    rfl
  simp only [Fin.prod_univ_one, Matrix.cons_val_zero, Equiv.funUnique_apply,
    Fin.default_eq_zero]
  rw [← hd]

/-- The light-cone combination `D₀ - Dᵢ` on one slot. -/
lemma lightConeDeriv_zero (F : (Fin 1 → Fin 1 ⊕ Fin 3) → W →ₗ[ℂ] B) (i : Fin 3) :
    lightConeDeriv F i ![0] = F ![Sum.inl 0] - F ![Sum.inr i] := by
  rw [lightConeDeriv_single]
  fin_cases i <;>
    simp [lightConeCoeff, Fintype.sum_sum_type] <;> module

/-- The light-cone combination `D₀ + Dᵢ` on one slot. -/
lemma lightConeDeriv_one (F : (Fin 1 → Fin 1 ⊕ Fin 3) → W →ₗ[ℂ] B) (i : Fin 3) :
    lightConeDeriv F i ![1] = F ![Sum.inl 0] + F ![Sum.inr i] := by
  rw [lightConeDeriv_single]
  fin_cases i <;>
    simp [lightConeCoeff, Fintype.sum_sum_type]

/-- The first transverse direction on one slot. -/
lemma lightConeDeriv_two (F : (Fin 1 → Fin 1 ⊕ Fin 3) → W →ₗ[ℂ] B) (i : Fin 3) :
    lightConeDeriv F i ![2] = F ![Sum.inr (i + 1)] := by
  rw [lightConeDeriv_single]
  fin_cases i <;>
    simp [lightConeCoeff]

/-- The second transverse direction on one slot. -/
lemma lightConeDeriv_three (F : (Fin 1 → Fin 1 ⊕ Fin 3) → W →ₗ[ℂ] B) (i : Fin 3) :
    lightConeDeriv F i ![3] = F ![Sum.inr (i + 2)] := by
  rw [lightConeDeriv_single]
  fin_cases i <;>
    simp [lightConeCoeff]

/-- **A two-slot light-cone symbol**, written out as a double sum over coordinate
  symbols. -/
lemma lightConeDeriv_pair (F : (Fin 2 → Fin 1 ⊕ Fin 3) → W →ₗ[ℂ] B) (i : Fin 3)
    (κ₀ κ₁ : Fin 4) :
    lightConeDeriv F i ![κ₀, κ₁] = ∑ μ : Fin 1 ⊕ Fin 3, ∑ ν : Fin 1 ⊕ Fin 3,
      (lightConeCoeff i κ₀ μ * lightConeCoeff i κ₁ ν) • F ![μ, ν] :=
  calc lightConeDeriv F i ![κ₀, κ₁]
      = ∑ p : (Fin 1 ⊕ Fin 3) × (Fin 1 ⊕ Fin 3),
          (lightConeCoeff i κ₀ p.1 * lightConeCoeff i κ₁ p.2) • F ![p.1, p.2] := by
        rw [lightConeDeriv]
        refine Fintype.sum_equiv (piFinTwoEquiv fun _ => Fin 1 ⊕ Fin 3) _ _ fun d => ?_
        have hd : ![d 0, d 1] = d := by
          funext j
          fin_cases j <;> rfl
        rw [Fin.prod_univ_two]
        simp only [piFinTwoEquiv_apply, Matrix.cons_val_zero, Matrix.cons_val_one, hd]
    _ = _ := Fintype.sum_prod_type _

/-- The `(D₀ - Dᵢ)(D₀ + Dᵢ)` slot pair. -/
lemma lightConeDeriv_pair_zero_one (F : (Fin 2 → Fin 1 ⊕ Fin 3) → W →ₗ[ℂ] B) (i : Fin 3) :
    lightConeDeriv F i ![0, 1] = F ![Sum.inl 0, Sum.inl 0] + F ![Sum.inl 0, Sum.inr i]
      - F ![Sum.inr i, Sum.inl 0] - F ![Sum.inr i, Sum.inr i] := by
  rw [lightConeDeriv_pair]
  simp [lightConeCoeff, Fintype.sum_sum_type, Finset.sum_add_distrib, Finset.sum_ite_eq',
    ite_smul]
  module

/-- The `(D₀ + Dᵢ)(D₀ - Dᵢ)` slot pair. -/
lemma lightConeDeriv_pair_one_zero (F : (Fin 2 → Fin 1 ⊕ Fin 3) → W →ₗ[ℂ] B) (i : Fin 3) :
    lightConeDeriv F i ![1, 0] = F ![Sum.inl 0, Sum.inl 0] - F ![Sum.inl 0, Sum.inr i]
      + F ![Sum.inr i, Sum.inl 0] - F ![Sum.inr i, Sum.inr i] := by
  rw [lightConeDeriv_pair]
  simp [lightConeCoeff, Fintype.sum_sum_type, Finset.sum_add_distrib, Finset.sum_ite_eq',
    ite_smul, neg_ite]
  module

/-- Both slots on the first transverse direction. -/
lemma lightConeDeriv_pair_two_two (F : (Fin 2 → Fin 1 ⊕ Fin 3) → W →ₗ[ℂ] B) (i : Fin 3) :
    lightConeDeriv F i ![2, 2] = F ![Sum.inr (i + 1), Sum.inr (i + 1)] := by
  rw [lightConeDeriv_pair]
  simp [lightConeCoeff]

/-- The first then second transverse directions. -/
lemma lightConeDeriv_pair_two_three (F : (Fin 2 → Fin 1 ⊕ Fin 3) → W →ₗ[ℂ] B) (i : Fin 3) :
    lightConeDeriv F i ![2, 3] = F ![Sum.inr (i + 1), Sum.inr (i + 2)] := by
  rw [lightConeDeriv_pair]
  simp [lightConeCoeff]

/-- The second then first transverse directions. -/
lemma lightConeDeriv_pair_three_two (F : (Fin 2 → Fin 1 ⊕ Fin 3) → W →ₗ[ℂ] B) (i : Fin 3) :
    lightConeDeriv F i ![3, 2] = F ![Sum.inr (i + 2), Sum.inr (i + 1)] := by
  rw [lightConeDeriv_pair]
  simp [lightConeCoeff]

/-- Both slots on the second transverse direction. -/
lemma lightConeDeriv_pair_three_three (F : (Fin 2 → Fin 1 ⊕ Fin 3) → W →ₗ[ℂ] B) (i : Fin 3) :
    lightConeDeriv F i ![3, 3] = F ![Sum.inr (i + 2), Sum.inr (i + 2)] := by
  rw [lightConeDeriv_pair]
  simp [lightConeCoeff]

/-- The `(D₀ - Dᵢ)(D₀ - Dᵢ)` slot pair. -/
lemma lightConeDeriv_pair_zero_zero (F : (Fin 2 → Fin 1 ⊕ Fin 3) → W →ₗ[ℂ] B) (i : Fin 3) :
    lightConeDeriv F i ![0, 0] = F ![Sum.inl 0, Sum.inl 0] - F ![Sum.inl 0, Sum.inr i]
      - F ![Sum.inr i, Sum.inl 0] + F ![Sum.inr i, Sum.inr i] := by
  rw [lightConeDeriv_pair]
  simp [lightConeCoeff, Fintype.sum_sum_type, Finset.sum_add_distrib, Finset.sum_ite_eq',
    ite_smul, neg_ite]
  module

/-- The `(D₀ + Dᵢ)(D₀ + Dᵢ)` slot pair. -/
lemma lightConeDeriv_pair_one_one (F : (Fin 2 → Fin 1 ⊕ Fin 3) → W →ₗ[ℂ] B) (i : Fin 3) :
    lightConeDeriv F i ![1, 1] = F ![Sum.inl 0, Sum.inl 0] + F ![Sum.inl 0, Sum.inr i]
      + F ![Sum.inr i, Sum.inl 0] + F ![Sum.inr i, Sum.inr i] := by
  rw [lightConeDeriv_pair]
  simp [lightConeCoeff, Fintype.sum_sum_type, Finset.sum_add_distrib, Finset.sum_ite_eq',
    ite_smul]
  module

/-- The `(D₀ - Dᵢ)` then second transverse slot pair. -/
lemma lightConeDeriv_pair_zero_three (F : (Fin 2 → Fin 1 ⊕ Fin 3) → W →ₗ[ℂ] B) (i : Fin 3) :
    lightConeDeriv F i ![0, 3] = F ![Sum.inl 0, Sum.inr (i + 2)]
      - F ![Sum.inr i, Sum.inr (i + 2)] := by
  rw [lightConeDeriv_pair]
  simp [lightConeCoeff, Fintype.sum_sum_type, Finset.sum_ite_eq', ite_smul]
  module

/-- The second transverse then `(D₀ - Dᵢ)` slot pair. -/
lemma lightConeDeriv_pair_three_zero (F : (Fin 2 → Fin 1 ⊕ Fin 3) → W →ₗ[ℂ] B) (i : Fin 3) :
    lightConeDeriv F i ![3, 0] = F ![Sum.inr (i + 2), Sum.inl 0]
      - F ![Sum.inr (i + 2), Sum.inr i] := by
  rw [lightConeDeriv_pair]
  simp [lightConeCoeff, Fintype.sum_sum_type, Finset.sum_add_distrib, Finset.sum_ite_eq',
    ite_smul, neg_ite]
  module

/-- The `(D₀ + Dᵢ)` then second transverse slot pair. -/
lemma lightConeDeriv_pair_one_three (F : (Fin 2 → Fin 1 ⊕ Fin 3) → W →ₗ[ℂ] B) (i : Fin 3) :
    lightConeDeriv F i ![1, 3] = F ![Sum.inl 0, Sum.inr (i + 2)]
      + F ![Sum.inr i, Sum.inr (i + 2)] := by
  rw [lightConeDeriv_pair]
  simp [lightConeCoeff, Fintype.sum_sum_type, Finset.sum_ite_eq', ite_smul]

/-- The second transverse then `(D₀ + Dᵢ)` slot pair. -/
lemma lightConeDeriv_pair_three_one (F : (Fin 2 → Fin 1 ⊕ Fin 3) → W →ₗ[ℂ] B) (i : Fin 3) :
    lightConeDeriv F i ![3, 1] = F ![Sum.inr (i + 2), Sum.inl 0]
      + F ![Sum.inr (i + 2), Sum.inr i] := by
  rw [lightConeDeriv_pair]
  simp [lightConeCoeff, Fintype.sum_sum_type, Finset.sum_add_distrib, Finset.sum_ite_eq',
    ite_smul]

/-- **The two-slot light-cone indices of weight zero**: the two mixed null pairs and the
  four transverse pairs. -/
lemma iSup_range_lightConeDeriv_pair_weight_zero
    (F : (Fin 2 → Fin 1 ⊕ Fin 3) → W →ₗ[ℂ] B) (i : Fin 3) :
    (⨆ (c : Fin 2 → Fin 4) (_ : (∑ j, lightConeWeight (c j)) = (0 : ℤ)),
        LinearMap.range (lightConeDeriv F i c))
      = ((LinearMap.range (lightConeDeriv F i ![0, 1]) ⊔
            LinearMap.range (lightConeDeriv F i ![1, 0])) ⊔
          (LinearMap.range (lightConeDeriv F i ![2, 2]) ⊔
            LinearMap.range (lightConeDeriv F i ![2, 3]))) ⊔
        (LinearMap.range (lightConeDeriv F i ![3, 2]) ⊔
          LinearMap.range (lightConeDeriv F i ![3, 3])) := by
  refine le_antisymm (iSup₂_le fun c hc => ?_)
    (sup_le (sup_le (sup_le ?_ ?_) (sup_le ?_ ?_)) (sup_le ?_ ?_))
  · obtain ⟨κ₀, κ₁, rfl⟩ : ∃ κ₀ κ₁, c = ![κ₀, κ₁] :=
      ⟨c 0, c 1, funext fun j => by fin_cases j <;> rfl⟩
    rw [Fin.sum_univ_two] at hc
    fin_cases κ₀
    · fin_cases κ₁
      · exact absurd hc (by decide)
      · exact le_sup_of_le_left (le_sup_of_le_left le_sup_left)
      · exact absurd hc (by decide)
      · exact absurd hc (by decide)
    · fin_cases κ₁
      · exact le_sup_of_le_left (le_sup_of_le_left le_sup_right)
      · exact absurd hc (by decide)
      · exact absurd hc (by decide)
      · exact absurd hc (by decide)
    · fin_cases κ₁
      · exact absurd hc (by decide)
      · exact absurd hc (by decide)
      · exact le_sup_of_le_left (le_sup_of_le_right le_sup_left)
      · exact le_sup_of_le_left (le_sup_of_le_right le_sup_right)
    · fin_cases κ₁
      · exact absurd hc (by decide)
      · exact absurd hc (by decide)
      · exact le_sup_of_le_right le_sup_left
      · exact le_sup_of_le_right le_sup_right
  · exact le_iSup₂_of_le ![0, 1] (by decide) le_rfl
  · exact le_iSup₂_of_le ![1, 0] (by decide) le_rfl
  · exact le_iSup₂_of_le ![2, 2] (by decide) le_rfl
  · exact le_iSup₂_of_le ![2, 3] (by decide) le_rfl
  · exact le_iSup₂_of_le ![3, 2] (by decide) le_rfl
  · exact le_iSup₂_of_le ![3, 3] (by decide) le_rfl

/-- **The weight-zero light-cone pairs avoiding the mixed transverse indices**: the two
  null pairs and the two repeated transverse pairs. -/
lemma iSup_range_lightConeDeriv_pair_weight_zero_notMixed
    (F : (Fin 2 → Fin 1 ⊕ Fin 3) → W →ₗ[ℂ] B) (i : Fin 3) :
    (⨆ (c : Fin 2 → Fin 4) (_ : (∑ j, lightConeWeight (c j)) = (0 : ℤ) ∧
        ¬(c 0 = 2 ∧ c 1 = 3) ∧ ¬(c 0 = 3 ∧ c 1 = 2)),
      LinearMap.range (lightConeDeriv F i c))
      = ((LinearMap.range (lightConeDeriv F i ![0, 1]) ⊔
            LinearMap.range (lightConeDeriv F i ![1, 0])) ⊔
          (LinearMap.range (lightConeDeriv F i ![2, 2]) ⊔
            LinearMap.range (lightConeDeriv F i ![3, 3]))) := by
  refine le_antisymm (iSup₂_le fun c hc => ?_)
    (sup_le (sup_le ?_ ?_) (sup_le ?_ ?_))
  · obtain ⟨κ₀, κ₁, rfl⟩ : ∃ κ₀ κ₁, c = ![κ₀, κ₁] :=
      ⟨c 0, c 1, funext fun j => by fin_cases j <;> rfl⟩
    obtain ⟨hw, h23, h32⟩ := hc
    rw [Fin.sum_univ_two] at hw
    fin_cases κ₀
    · fin_cases κ₁
      · exact absurd hw (by decide)
      · exact le_sup_of_le_left le_sup_left
      · exact absurd hw (by decide)
      · exact absurd hw (by decide)
    · fin_cases κ₁
      · exact le_sup_of_le_left le_sup_right
      · exact absurd hw (by decide)
      · exact absurd hw (by decide)
      · exact absurd hw (by decide)
    · fin_cases κ₁
      · exact absurd hw (by decide)
      · exact absurd hw (by decide)
      · exact le_sup_of_le_right le_sup_left
      · exact absurd (by decide) h23
    · fin_cases κ₁
      · exact absurd hw (by decide)
      · exact absurd hw (by decide)
      · exact absurd (by decide) h32
      · exact le_sup_of_le_right le_sup_right
  · exact le_iSup₂_of_le ![0, 1] (by decide) le_rfl
  · exact le_iSup₂_of_le ![1, 0] (by decide) le_rfl
  · exact le_iSup₂_of_le ![2, 2] (by decide) le_rfl
  · exact le_iSup₂_of_le ![3, 3] (by decide) le_rfl

/-- **The weight-zero light-cone pairs whose slots hit the first transverse direction
  together or not at all**: the two null pairs and the two repeated transverse pairs. -/
lemma iSup_range_lightConeDeriv_pair_weight_zero_sync
    (F : (Fin 2 → Fin 1 ⊕ Fin 3) → W →ₗ[ℂ] B) (i : Fin 3) :
    (⨆ (c : Fin 2 → Fin 4) (_ : (∑ j, lightConeWeight (c j)) = (0 : ℤ) ∧
        ((c 0 = 2) ↔ (c 1 = 2))),
      LinearMap.range (lightConeDeriv F i c))
      = ((LinearMap.range (lightConeDeriv F i ![0, 1]) ⊔
            LinearMap.range (lightConeDeriv F i ![1, 0])) ⊔
          (LinearMap.range (lightConeDeriv F i ![2, 2]) ⊔
            LinearMap.range (lightConeDeriv F i ![3, 3]))) := by
  refine le_antisymm (iSup₂_le fun c hc => ?_)
    (sup_le (sup_le ?_ ?_) (sup_le ?_ ?_))
  · obtain ⟨κ₀, κ₁, rfl⟩ : ∃ κ₀ κ₁, c = ![κ₀, κ₁] :=
      ⟨c 0, c 1, funext fun j => by fin_cases j <;> rfl⟩
    obtain ⟨hw, hsync⟩ := hc
    rw [Fin.sum_univ_two] at hw
    fin_cases κ₀
    · fin_cases κ₁
      · exact absurd hw (by decide)
      · exact le_sup_of_le_left le_sup_left
      · exact absurd hw (by decide)
      · exact absurd hw (by decide)
    · fin_cases κ₁
      · exact le_sup_of_le_left le_sup_right
      · exact absurd hw (by decide)
      · exact absurd hw (by decide)
      · exact absurd hw (by decide)
    · fin_cases κ₁
      · exact absurd hw (by decide)
      · exact absurd hw (by decide)
      · exact le_sup_of_le_right le_sup_left
      · exact absurd hsync (by decide)
    · fin_cases κ₁
      · exact absurd hw (by decide)
      · exact absurd hw (by decide)
      · exact absurd hsync (by decide)
      · exact le_sup_of_le_right le_sup_right
  · exact le_iSup₂_of_le ![0, 1] (by decide) le_rfl
  · exact le_iSup₂_of_le ![1, 0] (by decide) le_rfl
  · exact le_iSup₂_of_le ![2, 2] (by decide) le_rfl
  · exact le_iSup₂_of_le ![3, 3] (by decide) le_rfl

/-- **The one-slot light-cone symbols of weight zero** are the two transverse directions:
  the join of the weight-zero ranges on a single slot is the join of the ranges of the two
  transverse symbols. -/
lemma iSup_range_lightConeDeriv_single_weight_zero
    (F : (Fin 1 → Fin 1 ⊕ Fin 3) → W →ₗ[ℂ] B) (i : Fin 3) :
    (⨆ (c : Fin 1 → Fin 4) (_ : (∑ j, lightConeWeight (c j)) = (0 : ℤ)),
        LinearMap.range (lightConeDeriv F i c))
      = LinearMap.range (F ![Sum.inr (i + 1)]) ⊔ LinearMap.range (F ![Sum.inr (i + 2)]) := by
  refine le_antisymm (iSup₂_le fun c hc => ?_) (sup_le ?_ ?_)
  · obtain ⟨κ, rfl⟩ : ∃ κ, c = ![κ] := ⟨c 0, funext fun j => by fin_cases j; rfl⟩
    rw [Fin.sum_univ_one] at hc
    fin_cases κ
    · simp [lightConeWeight] at hc
    · simp [lightConeWeight] at hc
    · exact le_sup_of_le_left (le_of_eq (congrArg LinearMap.range (lightConeDeriv_two F i)))
    · exact le_sup_of_le_right (le_of_eq (congrArg LinearMap.range (lightConeDeriv_three F i)))
  · exact le_iSup₂_of_le ![2] (by simp [lightConeWeight])
      (le_of_eq (by rw [lightConeDeriv_two]))
  · exact le_iSup₂_of_le ![3] (by simp [lightConeWeight])
      (le_of_eq (by rw [lightConeDeriv_three]))

/-- The scalar behind `f_eq_sum_lightConeDeriv`: the two coefficient matrices are inverse
  slot by slot, hence inverse on multi-indices. -/
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
        · rw [if_neg hde]
          obtain ⟨j, hj⟩ := Function.ne_iff.1 hde
          exact Finset.prod_eq_zero (Finset.mem_univ j) (if_neg hj)

/-- **The coordinate symbols in the light-cone basis.** The change of basis is invertible,
  so the two families span the same submodule. -/
lemma eq_sum_lightConeDeriv {n : ℕ} (F : (Fin n → Fin 1 ⊕ Fin 3) → W →ₗ[ℂ] B) (i : Fin 3)
    (d : Fin n → Fin 1 ⊕ Fin 3) :
    F d = ∑ c : Fin n → Fin 4,
      (∏ j, lightConeCoeffInv i (d j) (c j)) • lightConeDeriv F i c := by
  simp only [lightConeDeriv, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  simp only [← Finset.sum_smul, sum_prod_lightConeCoeffInv i d, ite_smul, one_smul, zero_smul,
    Finset.sum_ite_eq, Finset.mem_univ, if_true]

/-- **The light-cone symbols have definite boost weight.** Each derivative slot contributes
  the weight of its light-cone direction, on top of the weight the argument carries in
  `W`. -/
lemma lightConeDeriv_mem {n : ℕ} (F : (Fin n → Fin 1 ⊕ Fin 3) → W →ₗ[ℂ] B)
    (hF : RotatesIndices repW repLorentz F)
    (i : Fin 3) (c : Fin n → Fin 4) {b : ℤ} {w : W}
    (hwm : w ∈ boostWeightSubmodule repW i b) :
    lightConeDeriv F i c w ∈
      boostWeightSubmodule repLorentz i ((∑ j, lightConeWeight (c j)) + b) := by
  intro t ht
  have htc : ((t : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  have key : repLorentz (SL2C.boostAxis i t ht) (lightConeDeriv F i c w)
      = ((t : ℝ) : ℂ) ^ (∑ j, lightConeWeight (c j)) •
        lightConeDeriv F i c (repW (SL2C.boostAxis i t ht) w) := by
    have hstep : ∀ x : Fin n → Fin 1 ⊕ Fin 3,
        (∏ j, lightConeCoeff i (c j) (x j)) • repLorentz (SL2C.boostAxis i t ht) (F x w)
          = ∑ a : Fin n → Fin 1 ⊕ Fin 3,
            ((∏ j, lightConeCoeff i (c j) (x j)) *
              (∏ j, (((SL2C.toLorentzGroup (SL2C.boostAxis i t ht)).1 (a j) (x j) : ℝ) : ℂ))) •
              F a (repW (SL2C.boostAxis i t ht) w) := by
      intro x
      rw [hF, Finset.smul_sum]
      exact Finset.sum_congr rfl fun a _ => smul_smul _ _ _
    simp only [lightConeDeriv, LinearMap.coe_sum, Finset.sum_apply, LinearMap.smul_apply,
      map_sum, map_smul]
    rw [Finset.smul_sum]
    simp only [hstep]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← Finset.sum_smul, smul_smul]
    congr 1
    exact sum_prod_lightConeCoeff i c a ht
  rw [key, hwm t ht, map_smul, smul_smul,
    show (algebraMap ℝ ℂ) t = ((t : ℝ) : ℂ) from rfl, ← zpow_add₀ htc]

/-- The range of a light-cone symbol over a Lorentz-scalar argument lies in the
  boost-weight space of its total slot weight. -/
lemma range_lightConeDeriv_le {n : ℕ} (F : (Fin n → Fin 1 ⊕ Fin 3) → ℂ →ₗ[ℂ] B)
    (hF : RotatesIndices (1 : Representation ℂ SL(2,ℂ) ℂ) repLorentz F)
    (i : Fin 3) (c : Fin n → Fin 4) :
    LinearMap.range (lightConeDeriv F i c) ≤
      boostWeightSubmodule repLorentz i (∑ j, lightConeWeight (c j)) := by
  rintro x ⟨w, rfl⟩
  simpa using lightConeDeriv_mem F hF i c (b := 0) (w := w)
    (mem_boostWeightSubmodule.2 fun t ht => by simp)

/-- The range of a light-cone symbol lies in the join of the coordinate ranges. -/
lemma range_lightConeDeriv_le_iSup_range {n : ℕ} (F : (Fin n → Fin 1 ⊕ Fin 3) → W →ₗ[ℂ] B)
    (i : Fin 3) (c : Fin n → Fin 4) :
    LinearMap.range (lightConeDeriv F i c) ≤ ⨆ d, LinearMap.range (F d) := by
  rintro x ⟨w, rfl⟩
  rw [lightConeDeriv]
  simp only [LinearMap.coe_sum, Finset.sum_apply, LinearMap.smul_apply]
  exact sum_mem fun d _ => Submodule.smul_mem _ _
    (Submodule.mem_iSup_of_mem d (LinearMap.mem_range_self _ w))

/-- **The value of a two-slot light-cone symbol at `1`**, for a family over `ℂ`. -/
noncomputable def lightConeDot (F : (Fin 2 → Fin 1 ⊕ Fin 3) → ℂ →ₗ[ℂ] B) (i : Fin 3)
    (c : Fin 2 → Fin 4) : B :=
  lightConeDeriv F i c (1 : ℂ)

/-- A light-cone symbol value is a boost eigenvector of its total slot weight. -/
lemma lightConeDot_mem (F : (Fin 2 → Fin 1 ⊕ Fin 3) → ℂ →ₗ[ℂ] B)
    (hF : RotatesIndices (1 : Representation ℂ SL(2,ℂ) ℂ) repLorentz F) (i : Fin 3)
    (c : Fin 2 → Fin 4) {k : ℤ} (hk : (∑ j, lightConeWeight (c j)) = k) :
    lightConeDot F i c ∈ boostWeightSubmodule repLorentz i k :=
  hk ▸ range_lightConeDeriv_le (n := 2) F hF i c ⟨1, rfl⟩

end Lorentz
