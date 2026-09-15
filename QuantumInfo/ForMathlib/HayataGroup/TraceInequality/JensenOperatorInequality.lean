/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kei Tsukamoto, Kento Mori, Hayata Yamasaki
-/
module

public import QuantumInfo.ForMathlib.HayataGroup.TraceInequality.JensenOperatorInequalityIImpIV

@[expose] public section

namespace JensenOperatorInequality

universe u

open LownerHeinzTheorem

section Theorem252

variable {ℋ : Type u}
variable [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ] [CompleteSpace ℋ]

set_option synthInstance.maxHeartbeats 400000 in
-- IsStarNormal CFC is only a theorem in Mathlib; CStarAlgebra chain through WithLp is deep.
noncomputable local instance : ContinuousFunctionalCalculus ℂ (L ℋ × L ℋ) IsStarNormal :=
  IsStarNormal.instContinuousFunctionalCalculus
set_option synthInstance.maxHeartbeats 400000 in
-- IsSelfAdjoint CFC for the product type, derived from IsStarNormal above.
noncomputable local instance : ContinuousFunctionalCalculus ℝ (L ℋ × L ℋ) IsSelfAdjoint :=
  IsSelfAdjoint.instContinuousFunctionalCalculus
set_option synthInstance.maxHeartbeats 400000 in
-- CStarAlgebra → NonnegSpectrumClass chain through WithLp is too deep for default heartbeats.
noncomputable local instance : NonnegSpectrumClass ℝ (L (HSum ℋ)) := inferInstance
set_option synthInstance.maxHeartbeats 400000 in
-- Module ℝ for L (HSum ℋ) requires deep WithLp / CStarAlgebra chain.
noncomputable local instance : Module ℝ (L (HSum ℋ)) := inferInstance

omit ℋ [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ] [CompleteSpace ℋ] in
/--
Uniform version of Condition (iv), with the Hilbert space arbitrary in the same universe.
This is the theorem-level uniform counterpart to the operator-level `...All` predicates.
-/
def CondIVAll (f : ℝ → ℝ) : Prop :=
  ∀ {K : Type u}
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [Nontrivial K],
    CondIV (ℋ := K) f

omit [CompleteSpace ℋ] in
/-- `L (HSum ℋ)` is nontrivial once `L ℋ` is. -/
private theorem nontrivial_hsumL_wrap [Nontrivial ℋ] : Nontrivial (L (HSum ℋ)) := by
  have h_not_sub : ¬ Subsingleton ℋ := by
    intro hsub
    let : Subsingleton ℋ := hsub
    let : Subsingleton (L ℋ) := by infer_instance
    exact (not_nontrivial_iff_subsingleton.mpr (by infer_instance))
      (inferInstance : Nontrivial (L ℋ))
  have hH_nontriv : Nontrivial ℋ := (not_subsingleton_iff_nontrivial.mp h_not_sub)
  let : Nontrivial ℋ := hH_nontriv
  rcases exists_pair_ne ℋ with ⟨x, y, hxy⟩
  let w : ℋ := x - y
  have hw : w ≠ 0 := sub_ne_zero.mpr hxy
  have hdiag_ne_zero : (blockDiagonal (ℋ := ℋ) (1 : L ℋ) 0 : L (HSum ℋ)) ≠ 0 := by
    intro h0
    have hz :
        blockDiagonal (ℋ := ℋ) (1 : L ℋ) 0 (hsumIncl ℋ 0 w) = 0 := by
      simp [h0]
    have hw0 : w = 0 := by
      have hz0 := congrArg (fun z : HSum ℋ => hsumProj ℋ 0 z) hz
      simpa [blockDiagonal] using hz0
    exact hw hw0
  exact ⟨0, blockDiagonal (ℋ := ℋ) (1 : L ℋ) 0, hdiag_ne_zero.symm⟩

private lemma blockDiagonal_selfAdjoint_wrap {A B : L ℋ}
    (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B) :
    IsSelfAdjoint (blockDiagonal (ℋ := ℋ) A B) := by
  change star (blockDiagonal (ℋ := ℋ) A B) = blockDiagonal (ℋ := ℋ) A B
  simp [blockDiagonal_star, hA.star_eq, hB.star_eq]

omit [CompleteSpace ℋ] in
private lemma blockDiagonal_eq_blockOp_wrap (A B : L ℋ) :
    blockDiagonal (ℋ := ℋ) A B = blockOp (ℋ := ℋ) A 0 0 B := by
  ext z i
  fin_cases i <;> simp [blockDiagonal, blockOp]

-- Multiplication of generic block operators is elaboration-heavy even in the wrapper.
set_option maxHeartbeats 400000 in
-- The generic `blockOp` product expands into large block normal forms.
omit [CompleteSpace ℋ] in
private lemma blockOp_mul_wrap (A00 A01 A10 A11 B00 B01 B10 B11 : L ℋ) :
    blockOp (ℋ := ℋ) A00 A01 A10 A11 * blockOp (ℋ := ℋ) B00 B01 B10 B11 =
      blockOp (ℋ := ℋ)
        (A00 * B00 + A01 * B10)
        (A00 * B01 + A01 * B11)
        (A10 * B00 + A11 * B10)
        (A10 * B01 + A11 * B11) := by
  refine blockOp_ext (ℋ := ℋ) ?_ ?_
  · intro z
    simp [ContinuousLinearMap.mul_def, add_left_comm, add_comm]
  · intro z
    simp [ContinuousLinearMap.mul_def, add_left_comm, add_comm]

private lemma cfcR_blockDiagonal_wrap (f : ℝ → ℝ)
    (A B : L ℋ) (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B)
    (hcont : ContinuousOn f (spectrum ℝ A ∪ spectrum ℝ B)) :
    cfcR (ℋ := HSum ℋ) f (blockDiagonal (ℋ := ℋ) A B) =
      blockDiagonal (ℋ := ℋ) (cfcR (ℋ := ℋ) f A) (cfcR (ℋ := ℋ) f B) := by
  let φ : (L ℋ × L ℋ) →⋆ₐ[ℝ] L (HSum ℋ) := blockDiagonalHom (ℋ := ℋ)
  have hφ : Continuous φ := by
    change Continuous (fun p : L ℋ × L ℋ => blockDiagonal (ℋ := ℋ) p.1 p.2)
    change Continuous (fun p : L ℋ × L ℋ =>
      hsumIncl ℋ 0 ∘L p.1 ∘L hsumProj ℋ 0 + hsumIncl ℋ 1 ∘L p.2 ∘L hsumProj ℋ 1)
    fun_prop
  have hpair : IsSelfAdjoint (A, B) := by
    change star (A, B) = (A, B)
    ext <;> simp [hA.star_eq, hB.star_eq]
  have hpair' : IsSelfAdjoint (φ (A, B)) := hpair.map φ
  have hmap := StarAlgHom.map_cfc (φ := φ) (f := f) (a := (A, B))
    (hf := by simpa [Prod.spectrum_eq] using hcont)
    (hφ := hφ) (ha := hpair) (hφa := hpair')
  have hprod :
      cfc (R := ℝ) (A := L ℋ × L ℋ) (p := IsSelfAdjoint) f (A, B) =
        (cfcR (ℋ := ℋ) f A, cfcR (ℋ := ℋ) f B) := by
    simpa [cfcR] using
      (cfc_map_prod (R := ℝ) (S := ℝ)
        (A := L ℋ) (B := L ℋ)
        (pab := IsSelfAdjoint) (pa := IsSelfAdjoint) (pb := IsSelfAdjoint)
        f A B
        (hf := hcont)
        (hab := hpair) (ha := hA) (hb := hB))
  calc
    cfcR (ℋ := HSum ℋ) f (blockDiagonal (ℋ := ℋ) A B)
        = cfc (R := ℝ) (A := L (HSum ℋ)) (p := IsSelfAdjoint) f (φ (A, B)) := by
            simp [cfcR, φ]
    _ = φ (cfc (R := ℝ) (A := L ℋ × L ℋ) (p := IsSelfAdjoint) f (A, B)) := by
            simpa using hmap.symm
    _ = φ (cfcR (ℋ := ℋ) f A, cfcR (ℋ := ℋ) f B) := by
            rw [hprod]
    _ = blockDiagonal (ℋ := ℋ) (cfcR (ℋ := ℋ) f A) (cfcR (ℋ := ℋ) f B) := by
            simp [φ, blockDiagonalHom]

private lemma continuousOn_union_of_subset_Ici_wrap {f : ℝ → ℝ}
    (hcont : ContinuousOn f (Set.Ici (0 : ℝ))) {s t : Set ℝ}
    (hs : s ⊆ Set.Ici (0 : ℝ)) (ht : t ⊆ Set.Ici (0 : ℝ)) :
    ContinuousOn f (s ∪ t) := by
  refine hcont.mono ?_
  intro x hx
  rcases hx with hx | hx
  · exact hs hx
  · exact ht hx

private lemma spectrum_Ici_of_nonneg_wrap {A : L ℋ} (hA0 : (0 : L ℋ) ≤ A) :
    spectrum ℝ A ⊆ Set.Ici (0 : ℝ) := by
  exact
    (StarOrderedRing.nonneg_iff_spectrum_nonneg (R := ℝ) A
      (ha := IsSelfAdjoint.of_nonneg hA0)).1 hA0

variable [Nontrivial ℋ]

omit [CompleteSpace ℋ] in
private lemma spectrum_zero_subset_Ici_wrap :
    spectrum ℝ (0 : L ℋ) ⊆ Set.Ici (0 : ℝ) := by
  intro x hx
  have hx0 : x = 0 := by
    simpa using hx
  simp [Set.Ici, hx0]

omit [Nontrivial ℋ] in
private lemma blockDiagonal_le_left_wrap {A0 A1 B0 B1 : L ℋ}
    (h : blockDiagonal (ℋ := ℋ) A0 A1 ≤ blockDiagonal (ℋ := ℋ) B0 B1) :
    A0 ≤ B0 := by
  have hnonneg : 0 ≤ blockDiagonal (ℋ := ℋ) (B0 - A0) (B1 - A1) := by
    have hsub :
        blockDiagonal (ℋ := ℋ) B0 B1 - blockDiagonal (ℋ := ℋ) A0 A1 =
          blockDiagonal (ℋ := ℋ) (B0 - A0) (B1 - A1) := by
      refine blockOp_ext (ℋ := ℋ) ?_ ?_
      · intro z
        simp [sub_eq_add_neg]
      · intro z
        simp [sub_eq_add_neg]
    exact hsub ▸ sub_nonneg.mpr h
  have hpos :
      (blockDiagonal (ℋ := ℋ) (B0 - A0) (B1 - A1)).IsPositive :=
    (ContinuousLinearMap.nonneg_iff_isPositive _).1 hnonneg
  have hleftPos : (B0 - A0).IsPositive := by
    rw [ContinuousLinearMap.isPositive_iff_complex]
    intro x
    have hx :=
      (ContinuousLinearMap.isPositive_iff_complex
        (blockDiagonal (ℋ := ℋ) (B0 - A0) (B1 - A1))).1 hpos (hsumIncl ℋ 0 x)
    simpa [blockDiagonal, hsumProj, hsumIncl, hsumEquiv, PiLp.inner_apply] using hx
  exact sub_nonneg.mp ((ContinuousLinearMap.nonneg_iff_isPositive _).2 hleftPos)

-- Theorem 2.5.2 `(iv) → (v)`.
-- Block-matrix normalization in this wrapper needs a larger local heartbeat budget.
theorem theorem_2_5_2_iv_imp_v {f : ℝ → ℝ} (hiv : CondIVAll.{u} f)
    (hcont : ContinuousOn f Set.univ) :
    CondV (ℋ := ℋ) f := by
  intro A B X Y hA hB hAs hBs hXY
  have hA0 : (0 : L ℋ) ≤ A := by
    refine (StarOrderedRing.nonneg_iff_spectrum_nonneg (R := ℝ) A (ha := hA)).2 ?_
    intro x hx
    simpa [Set.Ici] using hAs hx
  have hB0 : (0 : L ℋ) ≤ B := by
    refine (StarOrderedRing.nonneg_iff_spectrum_nonneg (R := ℝ) B (ha := hB)).2 ?_
    intro x hx
    simpa [Set.Ici] using hBs hx
  let Atilde : L (HSum ℋ) := blockDiagonal (ℋ := ℋ) A B
  let Xtilde : L (HSum ℋ) := blockOp (ℋ := ℋ) X 0 Y 0
  let : Nontrivial (L (HSum ℋ)) := nontrivial_hsumL_wrap (ℋ := ℋ)
  have hAtilde_sa : IsSelfAdjoint Atilde := by
    simpa [Atilde] using blockDiagonal_selfAdjoint_wrap (ℋ := ℋ) hA hB
  have hAtilde0 : (0 : L (HSum ℋ)) ≤ Atilde := by
    simpa [Atilde] using blockDiagonal_nonneg (ℋ := ℋ) hA0 hB0
  have hAtilde_spec : spectrum ℝ Atilde ⊆ Set.Ici (0 : ℝ) := by
    exact (StarOrderedRing.nonneg_iff_spectrum_nonneg (R := ℝ) Atilde (ha := hAtilde_sa)).1 hAtilde0
  have hXtilde_star_mul :
      star Xtilde * Xtilde =
        blockDiagonal (ℋ := ℋ) (star X * X + star Y * Y) 0 := by
    rw [show star Xtilde = blockOp (ℋ := ℋ) (star X) (star Y) 0 0 by
      simp [Xtilde]]
    rw [show Xtilde = blockOp (ℋ := ℋ) X 0 Y 0 by rfl]
    rw [blockOp_mul_wrap, blockDiagonal_eq_blockOp_wrap]
    simp
  have hXtilde_star_mul_le : star Xtilde * Xtilde ≤ (1 : L (HSum ℋ)) := by
    have hblock_nonneg :
        (0 : L (HSum ℋ)) ≤
          blockDiagonal (ℋ := ℋ) (1 - (star X * X + star Y * Y)) (1 : L ℋ) := by
      refine blockDiagonal_nonneg (ℋ := ℋ) ?_ ?_
      · exact sub_nonneg.mpr hXY
      · simp
    have hsub :
        (1 : L (HSum ℋ)) - blockDiagonal (ℋ := ℋ) (star X * X + star Y * Y) 0 =
          blockDiagonal (ℋ := ℋ) (1 - (star X * X + star Y * Y)) (1 : L ℋ) := by
      refine blockOp_ext (ℋ := ℋ) ?_ ?_
      · intro z
        simp [sub_eq_add_neg]
      · intro z
        simp [sub_eq_add_neg]
    have hblock :
        blockDiagonal (ℋ := ℋ) (star X * X + star Y * Y) 0 ≤ (1 : L (HSum ℋ)) := by
      exact sub_nonneg.mp (by simpa [hsub] using hblock_nonneg)
    simpa [hXtilde_star_mul] using hblock
  have hXtilde_star_mul_nonneg : (0 : L (HSum ℋ)) ≤ star Xtilde * Xtilde := by
    simp
  have hXtilde_norm : ‖Xtilde‖ ≤ 1 := by
    have hnormSq : ‖star Xtilde * Xtilde‖ ≤ 1 :=
      (CStarAlgebra.norm_le_one_iff_of_nonneg _ hXtilde_star_mul_nonneg).2 hXtilde_star_mul_le
    have hnormSq' : ‖Xtilde‖ * ‖Xtilde‖ ≤ 1 := by
      simpa [CStarRing.norm_star_mul_self] using hnormSq
    have hsq : ‖Xtilde‖ ^ 2 ≤ 1 := by
      simpa [pow_two] using hnormSq'
    nlinarith [norm_nonneg Xtilde]
  have hiv_hsum : CondIV (ℋ := HSum ℋ) f := @hiv (HSum ℋ) _ _ _ _
  have hcore := hiv_hsum (A := Atilde) (X := Xtilde) hAtilde_sa hAtilde_spec hXtilde_norm
  have hsum_sa : IsSelfAdjoint (star X * A * X + star Y * B * Y) := by
    change star (star X * A * X + star Y * B * Y) = star X * A * X + star Y * B * Y
    simp [hA.star_eq, hB.star_eq, mul_assoc]
  have hmul_block :
      star Xtilde * Atilde * Xtilde =
        blockDiagonal (ℋ := ℋ) (star X * A * X + star Y * B * Y) 0 := by
    rw [show star Xtilde = blockOp (ℋ := ℋ) (star X) (star Y) 0 0 by
      simp [Xtilde]]
    rw [show Atilde = blockOp (ℋ := ℋ) A 0 0 B by
      simpa [Atilde] using blockDiagonal_eq_blockOp_wrap (ℋ := ℋ) A B]
    rw [show Xtilde = blockOp (ℋ := ℋ) X 0 Y 0 by rfl]
    rw [blockOp_mul_wrap, blockOp_mul_wrap, blockDiagonal_eq_blockOp_wrap]
    congr 1 <;> simp [mul_assoc]
  have hAtilde_cfc :
      cfcR (ℋ := HSum ℋ) f Atilde =
        blockDiagonal (ℋ := ℋ) (cfcR (ℋ := ℋ) f A) (cfcR (ℋ := ℋ) f B) := by
    simpa [Atilde] using
      cfcR_blockDiagonal_wrap (ℋ := ℋ) (f := f) A B hA hB
        (hcont.mono (by intro x hx; simp))
  have hright_block :
      star Xtilde * cfcR (ℋ := HSum ℋ) f Atilde * Xtilde =
        blockDiagonal (star X * cfcR (ℋ := ℋ) f A * X + star Y * cfcR (ℋ := ℋ) f B * Y) 0 := by
    rw [hAtilde_cfc]
    rw [show star Xtilde = blockOp (ℋ := ℋ) (star X) (star Y) 0 0 by
      simp [Xtilde]]
    rw [show Xtilde = blockOp (ℋ := ℋ) X 0 Y 0 by rfl]
    rw [blockDiagonal_eq_blockOp_wrap, blockOp_mul_wrap, blockOp_mul_wrap, blockDiagonal_eq_blockOp_wrap]
    congr 1 <;> simp [mul_assoc]
  have hleft_block :
      cfcR (ℋ := HSum ℋ) f (star Xtilde * Atilde * Xtilde) =
        blockDiagonal (cfcR f (star X * A * X + star Y * B * Y)) (cfcR f 0) := by
    rw [hmul_block]
    simpa using
      cfcR_blockDiagonal_wrap f (star X * A * X + star Y * B * Y) 0 hsum_sa (by simp)
        (hcont.mono (by intro x hx; simp))
  rw [hleft_block, hright_block] at hcore
  exact blockDiagonal_le_left_wrap (ℋ := ℋ) hcore

/-- Uniform consequence of Theorem 2.5.2: `(i) → (v)` via `(iv)`. -/
theorem theorem_2_5_2_i_all_imp_v {f : ℝ → ℝ} (hf : CondIAll.{u} f) :
    CondV (ℋ := ℋ) f := by
  have hconv : OperatorConvex (ℋ := ℋ) f := by
    exact hf.1
  have hcont : ContinuousOn f Set.univ :=
    operatorConvex_continuousOn_univ (ℋ := ℋ) hconv
  refine theorem_2_5_2_iv_imp_v (ℋ := ℋ) ?_ hcont
  intro K _ _ _ _
  exact theorem_2_5_2_i_all_imp_iv (ℋ := K) (f := f) hf

-- Uniform localized consequence of Theorem 2.5.2: `(i) → (v)` on `Set.Ici 0`.
-- The localized wrapper repeats the same block-operator normalization as
-- `theorem_2_5_2_iv_imp_v`.
theorem theorem_2_5_2_i_ici_all_imp_v {f : ℝ → ℝ}
    (hf : CondIciAll.{u} f) :
    CondV (ℋ := ℋ) f := by
  have hfIci := hf
  rcases hf with ⟨_, hcontIci, _⟩
  intro A B X Y hA hB hAs hBs hXY
  have hA0 : (0 : L ℋ) ≤ A := by
    refine (StarOrderedRing.nonneg_iff_spectrum_nonneg (R := ℝ) A (ha := hA)).2 ?_
    intro x hx
    simpa [Set.Ici] using hAs hx
  have hB0 : (0 : L ℋ) ≤ B := by
    refine (StarOrderedRing.nonneg_iff_spectrum_nonneg (R := ℝ) B (ha := hB)).2 ?_
    intro x hx
    simpa [Set.Ici] using hBs hx
  let Atilde : L (HSum ℋ) := blockDiagonal (ℋ := ℋ) A B
  let Xtilde : L (HSum ℋ) := blockOp (ℋ := ℋ) X 0 Y 0
  let : Nontrivial (L (HSum ℋ)) := nontrivial_hsumL_wrap (ℋ := ℋ)
  have hAtilde_sa : IsSelfAdjoint Atilde := by
    simpa [Atilde] using blockDiagonal_selfAdjoint_wrap (ℋ := ℋ) hA hB
  have hAtilde0 : (0 : L (HSum ℋ)) ≤ Atilde := by
    simpa [Atilde] using blockDiagonal_nonneg (ℋ := ℋ) hA0 hB0
  have hAtilde_spec : spectrum ℝ Atilde ⊆ Set.Ici (0 : ℝ) :=
    spectrum_Ici_of_nonneg_wrap (ℋ := HSum ℋ) hAtilde0
  have hXtilde_star_mul :
      star Xtilde * Xtilde =
        blockDiagonal (ℋ := ℋ) (star X * X + star Y * Y) 0 := by
    rw [show star Xtilde = blockOp (ℋ := ℋ) (star X) (star Y) 0 0 by
      simp [Xtilde]]
    rw [show Xtilde = blockOp (ℋ := ℋ) X 0 Y 0 by rfl]
    rw [blockOp_mul_wrap, blockDiagonal_eq_blockOp_wrap]
    simp
  have hXtilde_star_mul_le : star Xtilde * Xtilde ≤ (1 : L (HSum ℋ)) := by
    have hblock_nonneg :
        (0 : L (HSum ℋ)) ≤
          blockDiagonal (ℋ := ℋ) (1 - (star X * X + star Y * Y)) (1 : L ℋ) := by
      refine blockDiagonal_nonneg (ℋ := ℋ) ?_ ?_
      · exact sub_nonneg.mpr hXY
      · simp
    have hsub :
        (1 : L (HSum ℋ)) - blockDiagonal (ℋ := ℋ) (star X * X + star Y * Y) 0 =
          blockDiagonal (ℋ := ℋ) (1 - (star X * X + star Y * Y)) (1 : L ℋ) := by
      refine blockOp_ext (ℋ := ℋ) ?_ ?_
      · intro z
        simp [sub_eq_add_neg]
      · intro z
        simp [sub_eq_add_neg]
    have hblock :
        blockDiagonal (ℋ := ℋ) (star X * X + star Y * Y) 0 ≤ (1 : L (HSum ℋ)) := by
      exact sub_nonneg.mp (by simpa [hsub] using hblock_nonneg)
    simpa [hXtilde_star_mul] using hblock
  have hXtilde_star_mul_nonneg : (0 : L (HSum ℋ)) ≤ star Xtilde * Xtilde := by
    simp
  have hXtilde_norm : ‖Xtilde‖ ≤ 1 := by
    have hnormSq : ‖star Xtilde * Xtilde‖ ≤ 1 :=
      (CStarAlgebra.norm_le_one_iff_of_nonneg _ hXtilde_star_mul_nonneg).2 hXtilde_star_mul_le
    have hnormSq' : ‖Xtilde‖ * ‖Xtilde‖ ≤ 1 := by
      simpa [CStarRing.norm_star_mul_self] using hnormSq
    have hsq : ‖Xtilde‖ ^ 2 ≤ 1 := by
      simpa [pow_two] using hnormSq'
    nlinarith [norm_nonneg Xtilde]
  have hiv_hsum : CondIV (ℋ := HSum ℋ) f :=
    theorem_2_5_2_i_ici_all_imp_iv (ℋ := HSum ℋ) (f := f) hfIci
  have hcore := hiv_hsum (A := Atilde) (X := Xtilde) hAtilde_sa hAtilde_spec hXtilde_norm
  have hsum_nonneg : (0 : L ℋ) ≤ star X * A * X + star Y * B * Y := by
    have hXA : (0 : L ℋ) ≤ star X * A * X := by
      simpa [mul_assoc] using star_left_conjugate_nonneg hA0 X
    have hYB : (0 : L ℋ) ≤ star Y * B * Y := by
      simpa [mul_assoc] using star_left_conjugate_nonneg hB0 Y
    exact add_nonneg hXA hYB
  have hsum_sa : IsSelfAdjoint (star X * A * X + star Y * B * Y) :=
    IsSelfAdjoint.of_nonneg hsum_nonneg
  have hmul_block :
      star Xtilde * Atilde * Xtilde =
        blockDiagonal (ℋ := ℋ) (star X * A * X + star Y * B * Y) 0 := by
    rw [show star Xtilde = blockOp (ℋ := ℋ) (star X) (star Y) 0 0 by
      simp [Xtilde]]
    rw [show Atilde = blockOp (ℋ := ℋ) A 0 0 B by
      simpa [Atilde] using blockDiagonal_eq_blockOp_wrap (ℋ := ℋ) A B]
    rw [show Xtilde = blockOp (ℋ := ℋ) X 0 Y 0 by rfl]
    rw [blockOp_mul_wrap, blockOp_mul_wrap, blockDiagonal_eq_blockOp_wrap]
    congr 1 <;> simp [mul_assoc]
  have hAtilde_cfc :
      cfcR (ℋ := HSum ℋ) f Atilde =
        blockDiagonal (ℋ := ℋ) (cfcR (ℋ := ℋ) f A) (cfcR (ℋ := ℋ) f B) := by
    simpa [Atilde] using
      cfcR_blockDiagonal_wrap (ℋ := ℋ) (f := f) A B hA hB
        (continuousOn_union_of_subset_Ici_wrap (f := f) hcontIci hAs hBs)
  have hright_block :
      star Xtilde * cfcR (ℋ := HSum ℋ) f Atilde * Xtilde =
        blockDiagonal (ℋ := ℋ)
          (star X * cfcR (ℋ := ℋ) f A * X + star Y * cfcR (ℋ := ℋ) f B * Y) 0 := by
    rw [hAtilde_cfc]
    rw [show star Xtilde = blockOp (ℋ := ℋ) (star X) (star Y) 0 0 by
      simp [Xtilde]]
    rw [show Xtilde = blockOp (ℋ := ℋ) X 0 Y 0 by rfl, blockDiagonal_eq_blockOp_wrap,
      blockOp_mul_wrap, blockOp_mul_wrap, blockDiagonal_eq_blockOp_wrap]
    congr 1 <;> simp [mul_assoc]
  have hsum_spec : spectrum ℝ (star X * A * X + star Y * B * Y) ⊆ Set.Ici (0 : ℝ) :=
    spectrum_Ici_of_nonneg_wrap (ℋ := ℋ) hsum_nonneg
  have hleft_block :
      cfcR (ℋ := HSum ℋ) f (star Xtilde * Atilde * Xtilde) =
        blockDiagonal (cfcR f (star X * A * X + star Y * B * Y)) (cfcR f 0) := by
    rw [hmul_block]
    simpa using
      cfcR_blockDiagonal_wrap f (star X * A * X + star Y * B * Y) 0 hsum_sa (by simp)
        (continuousOn_union_of_subset_Ici_wrap hcontIci hsum_spec spectrum_zero_subset_Ici_wrap)
  rw [hleft_block, hright_block] at hcore
  exact blockDiagonal_le_left_wrap (ℋ := ℋ) hcore

end Theorem252

end JensenOperatorInequality
