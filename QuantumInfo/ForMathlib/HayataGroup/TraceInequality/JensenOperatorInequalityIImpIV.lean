/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kei Tsukamoto, Kento Mori, Hayata Yamasaki
-/
module

public import QuantumInfo.ForMathlib.HayataGroup.TraceInequality.BlockDiagonal
public import QuantumInfo.ForMathlib.HayataGroup.TraceInequality.LownerHeinzTheorem
public import Mathlib.Analysis.CStarAlgebra.Unitary.Span
public import Mathlib.Algebra.Star.UnitaryStarAlgAut

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

/-- Condition (iv) in Theorem 2.5.2. -/
def CondIV (f : ℝ → ℝ) : Prop :=
  ∀ ⦃A X : L ℋ⦄, IsSelfAdjoint A → spectrum ℝ A ⊆ Set.Ici (0 : ℝ) → ‖X‖ ≤ 1 →
    cfcR (ℋ := ℋ) f (star X * A * X) ≤ star X * cfcR (ℋ := ℋ) f A * X

/-- Condition (i) in Theorem 2.5.2 on the fixed Hilbert space `ℋ`. -/
def CondI (f : ℝ → ℝ) : Prop :=
  OperatorConvex (ℋ := ℋ) f ∧ f 0 ≤ 0

omit ℋ [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ] [CompleteSpace ℋ] in
/--
Uniform version of Condition (i), packaged as `OperatorConvexAll` together with `f 0 ≤ 0`.
-/
def CondIAll (f : ℝ → ℝ) : Prop :=
  OperatorConvexAll.{u} f ∧
    f 0 ≤ 0

omit ℋ [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ] [CompleteSpace ℋ] in
/--
Uniform localized version of Condition (i), packaged as
`OperatorConvexOnAll (Set.Ici 0)` together with continuity and `f 0 ≤ 0`.
-/
def CondIciAll (f : ℝ → ℝ) : Prop :=
  OperatorConvexOnAll.{u} (Set.Ici (0 : ℝ)) f ∧
    ContinuousOn f (Set.Ici (0 : ℝ)) ∧
    f 0 ≤ 0

/-- Condition (v) in Theorem 2.5.2. -/
def CondV (f : ℝ → ℝ) : Prop :=
  ∀ ⦃A B X Y : L ℋ⦄,
    IsSelfAdjoint A → IsSelfAdjoint B →
    spectrum ℝ A ⊆ Set.Ici (0 : ℝ) → spectrum ℝ B ⊆ Set.Ici (0 : ℝ) →
    star X * X + star Y * Y ≤ (1 : L ℋ) →
    cfcR (ℋ := ℋ) f (star X * A * X + star Y * B * Y) ≤
      star X * cfcR (ℋ := ℋ) f A * X + star Y * cfcR (ℋ := ℋ) f B * Y

/-- Selfadjoint `2 × 2` block built from a contraction candidate `X`. -/
private noncomputable def blockSwap (X : L ℋ) : L (HSum ℋ) :=
  blockOp (ℋ := ℋ) 0 (star X) X 0

private lemma blockSwap_star (X : L ℋ) :
    star (blockSwap (ℋ := ℋ) X) = blockSwap (ℋ := ℋ) X := by
  simp [blockSwap, blockOp_star]

private lemma blockSwap_sq (X : L ℋ) :
    blockSwap (ℋ := ℋ) X * blockSwap (ℋ := ℋ) X =
      blockDiagonal (ℋ := ℋ) (star X * X) (X * star X) := by
  ext z i
  fin_cases i <;>
    simp [blockSwap, blockOp, blockDiagonal, ContinuousLinearMap.mul_def] <;> abel

omit [CompleteSpace ℋ] in
private lemma blockDiagonal_eq_blockOp (A B : L ℋ) :
    blockDiagonal (ℋ := ℋ) A B = blockOp (ℋ := ℋ) A 0 0 B := by
  ext z i
  fin_cases i <;> simp [blockDiagonal, blockOp]

set_option maxHeartbeats 400000 in
-- Multiplying two generic `blockOp` expressions is elaboration-heavy.
omit [CompleteSpace ℋ] in
private lemma blockOp_mul (A00 A01 A10 A11 B00 B01 B10 B11 : L ℋ) :
    blockOp (ℋ := ℋ) A00 A01 A10 A11 * blockOp (ℋ := ℋ) B00 B01 B10 B11 =
      blockOp (ℋ := ℋ)
        (A00 * B00 + A01 * B10)
        (A00 * B01 + A01 * B11)
        (A10 * B00 + A11 * B10)
        (A10 * B01 + A11 * B11) := by
  -- The extra heartbeat budget stays local to this normalization lemma.
  refine blockOp_ext (ℋ := ℋ) ?_ ?_
  · intro z
    simp [ContinuousLinearMap.mul_def, add_left_comm, add_comm]
  · intro z
    simp [ContinuousLinearMap.mul_def, add_left_comm, add_comm]

omit [CompleteSpace ℋ] in
private lemma blockOp_add
    (A00 A01 A10 A11 B00 B01 B10 B11 : L ℋ) :
    blockOp (ℋ := ℋ) A00 A01 A10 A11 + blockOp (ℋ := ℋ) B00 B01 B10 B11 =
      blockOp (ℋ := ℋ) (A00 + B00) (A01 + B01) (A10 + B10) (A11 + B11) := by
  ext z i
  fin_cases i <;> simp [blockOp] <;> abel

set_option synthInstance.maxHeartbeats 100000 in
-- Scalar action on `blockOp` triggers expensive instance search for nested operator expressions.
private lemma blockOp_smulR
    (r : ℝ) (A00 A01 A10 A11 : L ℋ) :
    r • blockOp (ℋ := ℋ) A00 A01 A10 A11 =
      blockOp (ℋ := ℋ) (r • A00) (r • A01) (r • A10) (r • A11) := by
  have coe_smul_hsum : ∀ (f : L (HSum ℋ)) (x : HSum ℋ), (r • f) x = r • (f x) := by
    intros; rfl
  have coe_smul_h : ∀ (f : L ℋ) (x : ℋ), (r • f) x = r • (f x) := by
    intros; rfl
  ext z i
  fin_cases i <;> {
    simp only [blockOp, add_apply, ContinuousLinearMap.comp_apply,
      smul_add, coe_smul_hsum, coe_smul_h]
    simp [hsumProj, hsumIncl, hsumEquiv]
  }

private lemma blockSwap_add_I_smul_blockDiagonal (X R0 R1 : L ℋ) :
    blockSwap (ℋ := ℋ) X + Complex.I • blockDiagonal (ℋ := ℋ) R0 R1 =
      blockOp (ℋ := ℋ) (Complex.I • R0) (star X) X (Complex.I • R1) := by
  rw [blockDiagonal_eq_blockOp]
  ext z i
  fin_cases i <;> simp [blockSwap, blockOp] <;> abel

omit [CompleteSpace ℋ] in
private lemma blockOp_mul_blockDiagonal_zero_right
    (P00 P01 P10 P11 A Q00 Q01 Q10 Q11 : L ℋ) :
    blockOp (ℋ := ℋ) P00 P01 P10 P11 * blockDiagonal (ℋ := ℋ) 0 A *
        blockOp (ℋ := ℋ) Q00 Q01 Q10 Q11 =
      blockOp (ℋ := ℋ)
        (P01 * A * Q10)
        (P01 * A * Q11)
        (P11 * A * Q10)
        (P11 * A * Q11) := by
  rw [blockDiagonal_eq_blockOp, blockOp_mul, blockOp_mul]
  simp [mul_assoc, add_comm]

set_option synthInstance.maxHeartbeats 400000 in
-- `StarAlgHom.map_cfc` needs `MulAction ℝ (L (HSum ℋ))`; search is deep without section CFC.
private lemma cfcR_blockDiagonal (f : ℝ → ℝ)
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

-- Converting positivity on a block-diagonal operator to each diagonal block is expensive.
private lemma blockDiagonal_le_left {A0 A1 B0 B1 : L ℋ}
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
  exact (sub_nonneg.mp ((ContinuousLinearMap.nonneg_iff_isPositive _).2 hleftPos))

private lemma blockDiagonal_selfAdjoint {A B : L ℋ}
    (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B) :
    IsSelfAdjoint (blockDiagonal (ℋ := ℋ) A B) := by
  change star (blockDiagonal (ℋ := ℋ) A B) = blockDiagonal (ℋ := ℋ) A B
  simp [blockDiagonal_star, hA.star_eq, hB.star_eq]

private lemma cfcR_zero (f : ℝ → ℝ) :
    cfcR (ℋ := ℋ) f (0 : L ℋ) = algebraMap ℝ (L ℋ) (f 0) := by
  change cfc (R := ℝ) (A := L ℋ) (p := IsSelfAdjoint) f (0 : L ℋ) =
    algebraMap ℝ (L ℋ) (f 0)
  simp

private lemma cfcR_conj_unitary (f : ℝ → ℝ) (hcont : ContinuousOn f Set.univ)
    (u : unitary (L ℋ)) (A : L ℋ) (hA : IsSelfAdjoint A) :
    cfcR (ℋ := ℋ) f (star u * A * u) = star u * cfcR (ℋ := ℋ) f A * u := by
  let φ : L ℋ →⋆ₐ[ℝ] L ℋ := Unitary.conjStarAlgAut ℝ (L ℋ) (star u)
  have hφ : Continuous φ := by
    have h1 : Continuous (fun x : L ℋ => (star u : L ℋ) * x * (u : L ℋ)) := by
      fun_prop
    have hEq : (fun x : L ℋ => φ x) = (fun x : L ℋ => (star u : L ℋ) * x * (u : L ℋ)) := by
      funext x
      simp [φ, Unitary.conjStarAlgAut_apply, mul_assoc]
    simpa [hEq] using h1
  have hφA : IsSelfAdjoint (φ A) := hA.map φ
  have hmap := StarAlgHom.map_cfc (φ := φ) (f := f) (a := A)
    (hf := hcont.mono (by intro x hx; simp))
    (hφ := hφ) (ha := hA) (hφa := hφA)
  simpa [φ, cfcR, Unitary.conjStarAlgAut_apply, mul_assoc] using hmap.symm

private lemma cfcR_conj_unitary_on (s : Set ℝ) (f : ℝ → ℝ) (hcont : ContinuousOn f s)
    {A : L ℋ} (hAs : spectrum ℝ A ⊆ s)
    (u : unitary (L ℋ)) (hA : IsSelfAdjoint A) :
    cfcR (ℋ := ℋ) f (star u * A * u) = star u * cfcR (ℋ := ℋ) f A * u := by
  let φ : L ℋ →⋆ₐ[ℝ] L ℋ := Unitary.conjStarAlgAut ℝ (L ℋ) (star u)
  have hφ : Continuous φ := by
    have h1 : Continuous (fun x : L ℋ => (star u : L ℋ) * x * (u : L ℋ)) := by
      fun_prop
    have hEq : (fun x : L ℋ => φ x) = (fun x : L ℋ => (star u : L ℋ) * x * (u : L ℋ)) := by
      funext x
      simp [φ, Unitary.conjStarAlgAut_apply, mul_assoc]
    simpa [hEq] using h1
  have hφA : IsSelfAdjoint (φ A) := hA.map φ
  have hmap := StarAlgHom.map_cfc (φ := φ) (f := f) (a := A)
    (hf := hcont.mono hAs)
    (hφ := hφ) (ha := hA) (hφa := hφA)
  simpa [φ, cfcR, Unitary.conjStarAlgAut_apply, mul_assoc] using hmap.symm

private lemma cfcR_real_sqrt_eq_sqrt {A : L ℋ} (hA : (0 : L ℋ) ≤ A) :
    cfcR (ℋ := ℋ) Real.sqrt A = CFC.sqrt A := by
  rw [CFC.sqrt_eq_real_sqrt A hA, cfcₙ_eq_cfc (f := Real.sqrt) (a := A) (hf0 := by simp), cfcR]

omit [CompleteSpace ℋ] in
private theorem nontrivial_hsumL [Nontrivial ℋ] : Nontrivial (L (HSum ℋ)) := by
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
      exact congrArg (fun T : L (HSum ℋ) => T (hsumIncl ℋ 0 w)) h0
    have hw0 : w = 0 := by
      have hz0 := congrArg (fun z : HSum ℋ => hsumProj ℋ 0 z) hz
      simpa [blockDiagonal] using hz0
    exact hw hw0
  exact ⟨0, blockDiagonal (ℋ := ℋ) (1 : L ℋ) 0, hdiag_ne_zero.symm⟩

set_option synthInstance.maxHeartbeats 100000 in
-- `CFC.sqrt` on block-diagonal operators triggers expensive instance search through the product map.
set_option linter.unusedSectionVars false in
private lemma sqrt_blockDiagonal_of_nonneg
    [Nontrivial ℋ]
    {A B : L ℋ} (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B)
    (hA_nonneg : (0 : L ℋ) ≤ A) (hB_nonneg : (0 : L ℋ) ≤ B) :
    CFC.sqrt (blockDiagonal (ℋ := ℋ) A B) =
      blockDiagonal (ℋ := ℋ) (CFC.sqrt A) (CFC.sqrt B) := by
  let : Algebra ℝ (L (HSum ℋ)) := by infer_instance
  let : Nontrivial (L (HSum ℋ)) := nontrivial_hsumL (ℋ := ℋ)
  have hdiag_nonneg : (0 : L (HSum ℋ)) ≤ blockDiagonal (ℋ := ℋ) A B :=
    blockDiagonal_nonneg (ℋ := ℋ) hA_nonneg hB_nonneg
  rw [← cfcR_real_sqrt_eq_sqrt (ℋ := HSum ℋ) hdiag_nonneg]
  rw [cfcR_blockDiagonal (ℋ := ℋ) (f := Real.sqrt) (A := A) (B := B) hA hB]
  · rw [← cfcR_real_sqrt_eq_sqrt (ℋ := ℋ) hA_nonneg, ← cfcR_real_sqrt_eq_sqrt (ℋ := ℋ) hB_nonneg]
  · simpa using
      (by cfc_cont_tac : ContinuousOn Real.sqrt (spectrum ℝ A ∪ spectrum ℝ B))

--BUG? In v4.28, this didn't require CompleteSpace ℋ. Then it did.
-- The `NormedAlgebra ℝ (L ℋ)` instances comes from a `CStarAlgebra (ℋ →L[ℂ] ℋ)`, which is
-- `instCStarAlgebraContinuousLinearMapComplexIdOfCompleteSpace`, which requires CompleteSpace ℋ.
-- In principle this isn't necessary.
omit [CompleteSpace ℋ] in
private lemma complex_I_smul_real_I_smul_invTwo (r : ℝ) (T : L ℋ) :
    Complex.I • r • Complex.I • (2⁻¹ : ℝ) • T =
      -((2⁻¹ : ℝ) * r) • T := by
  ext x
  have hcomm : r • (Complex.I • ((2⁻¹ : ℝ) • T x)) = Complex.I • (r • ((2⁻¹ : ℝ) • T x)) := by
    simpa using (smul_comm r (Complex.I : ℂ) ((2⁻¹ : ℝ) • T x))
  calc
    Complex.I • r • Complex.I • (2⁻¹ : ℝ) • T x
        = Complex.I • (r • (Complex.I • ((2⁻¹ : ℝ) • T x))) := by
            rfl
    _ = Complex.I • (Complex.I • (r • ((2⁻¹ : ℝ) • T x))) := by
            rw [hcomm]
    _ = ((Complex.I : ℂ) * Complex.I) • (r • ((2⁻¹ : ℝ) • T x)) := by
            rw [smul_smul]
    _ = (-1 : ℂ) • (r • ((2⁻¹ : ℝ) • T x)) := by
            norm_num
    _ = (-1 : ℂ) • (((r * 2⁻¹ : ℝ)) • T x) := by
            rw [smul_smul]
    _ = -((2⁻¹ : ℝ) * r) • T x := by
            simp [neg_smul, mul_comm]

omit [CompleteSpace ℋ] in
private lemma real_smul_complex_I_real_smul_complex_I_comm (s r : ℝ) (T : L ℋ) :
    (s : ℝ) • Complex.I • r • Complex.I • T =
      Complex.I • r • Complex.I • (s : ℝ) • T := by
  calc
    (s : ℝ) • Complex.I • r • Complex.I • T
        = Complex.I • ((s : ℝ) • (r • (Complex.I • T))) := by
            simpa [smul_smul] using (smul_comm (s : ℝ) (Complex.I : ℂ) (r • (Complex.I • T)))
    _ = Complex.I • (r • ((s : ℝ) • (Complex.I • T))) := by
            rw [smul_comm (s : ℝ) r (Complex.I • T)]
    _ = Complex.I • (r • (Complex.I • ((s : ℝ) • T))) := by
            rw [smul_comm (s : ℝ) (Complex.I : ℂ) T]
    _ = Complex.I • r • Complex.I • (s : ℝ) • T := by
            rfl

omit [CompleteSpace ℋ] in
private lemma half_add_half_eq (T : L ℋ) :
    (2⁻¹ : ℝ) • T + (2⁻¹ : ℝ) • T = T := by
  calc
    (2⁻¹ : ℝ) • T + (2⁻¹ : ℝ) • T = (2⁻¹ + 2⁻¹ : ℝ) • T := by
      simp [add_smul]
    _ = (1 : ℝ) • T := by norm_num
    _ = T := by simp

omit [CompleteSpace ℋ] in
private lemma half_mul_real_add_half_mul_real_eq (r : ℝ) (T : L ℋ) :
    ((2⁻¹ : ℝ) * r) • T + ((2⁻¹ : ℝ) * r) • T = r • T := by
  calc
    ((2⁻¹ : ℝ) * r) • T + ((2⁻¹ : ℝ) * r) • T =
        (((2⁻¹ : ℝ) * r) + ((2⁻¹ : ℝ) * r)) • T := by
          simp [add_smul]
    _ = r • T := by ring_nf

private lemma rightEval_topLeft_scalar
    (r : ℝ) (R0 X T : L ℋ) :
    (2⁻¹ : ℝ) • (star X * (T * X)) +
        ((2⁻¹ : ℝ) • (star X * (T * X)) +
          (-((2⁻¹ : ℝ) • Complex.I • r • Complex.I • (R0 * R0)) +
            -((2⁻¹ : ℝ) • Complex.I • r • Complex.I • (R0 * R0)))) =
      star X * (T * X) + r • (R0 * R0) := by
  have hP :
      (2⁻¹ : ℝ) • (star X * (T * X)) +
          (2⁻¹ : ℝ) • (star X * (T * X)) =
        star X * (T * X) := by
    simpa using half_add_half_eq (ℋ := ℋ) (star X * (T * X))
  have hQhalf :
      -((2⁻¹ : ℝ) • Complex.I • r • Complex.I • (R0 * R0)) +
          -((2⁻¹ : ℝ) • Complex.I • r • Complex.I • (R0 * R0)) =
        r • (R0 * R0) := by
    have hterm :
        -((2⁻¹ : ℝ) • Complex.I • r • Complex.I • (R0 * R0)) =
          ((2⁻¹ : ℝ) * r) • (R0 * R0) := by
      calc
        -((2⁻¹ : ℝ) • Complex.I • r • Complex.I • (R0 * R0))
            = -(Complex.I • r • Complex.I • (2⁻¹ : ℝ) • (R0 * R0)) := by
                rw [real_smul_complex_I_real_smul_complex_I_comm
                  (ℋ := ℋ) (s := (2⁻¹ : ℝ)) (r := r) (T := R0 * R0)]
        _ = ((2⁻¹ : ℝ) * r) • (R0 * R0) := by
            rw [complex_I_smul_real_I_smul_invTwo (ℋ := ℋ) (r := r) (T := R0 * R0)]
            simp
    calc
      -((2⁻¹ : ℝ) • Complex.I • r • Complex.I • (R0 * R0)) +
          -((2⁻¹ : ℝ) • Complex.I • r • Complex.I • (R0 * R0)) =
        ((2⁻¹ : ℝ) * r) • (R0 * R0) + ((2⁻¹ : ℝ) * r) • (R0 * R0) := by
          simp [hterm]
      _ = r • (R0 * R0) := half_mul_real_add_half_mul_real_eq (ℋ := ℋ) r (R0 * R0)
  calc
    (2⁻¹ : ℝ) • (star X * (T * X)) +
        ((2⁻¹ : ℝ) • (star X * (T * X)) +
          (-((2⁻¹ : ℝ) • Complex.I • r • Complex.I • (R0 * R0)) +
            -((2⁻¹ : ℝ) • Complex.I • r • Complex.I • (R0 * R0))))
        =
      ((2⁻¹ : ℝ) • (star X * (T * X)) +
          (2⁻¹ : ℝ) • (star X * (T * X))) +
        (-((2⁻¹ : ℝ) • Complex.I • r • Complex.I • (R0 * R0)) +
          -((2⁻¹ : ℝ) • Complex.I • r • Complex.I • (R0 * R0))) := by
            abel
    _ = star X * (T * X) + r • (R0 * R0) := by rw [hP, hQhalf]

private lemma rightEval_bottomRight_scalar
    (r : ℝ) (R1 X T : L ℋ) :
    (2⁻¹ * r) • (X * star X) +
        ((2⁻¹ * r) • (X * star X) +
          ((2⁻¹ : ℝ) • (R1 * (T * R1)) +
            (2⁻¹ : ℝ) • (R1 * (T * R1)))) =
      (R1 * T * R1) + r • (X * star X) := by
  have hS :
      (2⁻¹ * r) • (X * star X) + (2⁻¹ * r) • (X * star X) = r • (X * star X) := by
    simpa using half_mul_real_add_half_mul_real_eq (ℋ := ℋ) r (X * star X)
  have hT :
      (2⁻¹ : ℝ) • (R1 * (T * R1)) + (2⁻¹ : ℝ) • (R1 * (T * R1)) =
        R1 * (T * R1) := by
    simpa using half_add_half_eq (ℋ := ℋ) (R1 * (T * R1))
  calc
    (2⁻¹ * r) • (X * star X) +
        ((2⁻¹ * r) • (X * star X) +
          ((2⁻¹ : ℝ) • (R1 * (T * R1)) +
            (2⁻¹ : ℝ) • (R1 * (T * R1))))
        =
      ((2⁻¹ * r) • (X * star X) + (2⁻¹ * r) • (X * star X)) +
        ((2⁻¹ : ℝ) • (R1 * (T * R1)) + (2⁻¹ : ℝ) • (R1 * (T * R1))) := by
            abel
    _ = r • (X * star X) + R1 * (T * R1) := by rw [hS, hT]
    _ = (R1 * T * R1) + r • (X * star X) := by simp [mul_assoc, add_comm]

private lemma star_mul_le_one [Nontrivial ℋ] (X : L ℋ) (hX : ‖X‖ ≤ 1) :
    (star X * X : L ℋ) ≤ 1 := by
  have h1 : star X * X ≤ algebraMap ℝ (L ℋ) (‖X‖ ^ 2) := by
    simpa [pow_two] using (CStarAlgebra.star_mul_le_algebraMap_norm_sq (a := X))
  have hsq : ‖X‖ ^ 2 ≤ 1 := by
    nlinarith [hX, norm_nonneg X]
  exact h1.trans (by simpa [Algebra.algebraMap_eq_smul_one] using hsq)

private lemma mul_star_le_one [Nontrivial ℋ] (X : L ℋ) (hX : ‖X‖ ≤ 1) :
    (X * star X : L ℋ) ≤ 1 := by
  have h1 : X * star X ≤ algebraMap ℝ (L ℋ) (‖X‖ ^ 2) := by
    simpa [pow_two] using (CStarAlgebra.star_mul_le_algebraMap_norm_sq (a := star X))
  have hsq : ‖X‖ ^ 2 ≤ 1 := by
    nlinarith [hX, norm_nonneg X]
  exact h1.trans (by simpa [Algebra.algebraMap_eq_smul_one] using hsq)

-- `simp` and normalization over block expressions are expensive here.
private lemma blockSwap_norm_le_one [Nontrivial ℋ] (X : L ℋ) (hX : ‖X‖ ≤ 1) :
    ‖blockSwap (ℋ := ℋ) X‖ ≤ 1 := by
  have hSstar : star (blockSwap (ℋ := ℋ) X) = blockSwap (ℋ := ℋ) X :=
    blockSwap_star (ℋ := ℋ) X
  have hSstarS :
      star (blockSwap (ℋ := ℋ) X) * blockSwap (ℋ := ℋ) X =
        blockDiagonal (ℋ := ℋ) (star X * X) (X * star X) := by
    simpa [hSstar] using blockSwap_sq (ℋ := ℋ) X
  have hDiagLe :
      blockDiagonal (ℋ := ℋ) (star X * X) (X * star X) ≤ (1 : L (HSum ℋ)) := by
    have hA : 0 ≤ (1 : L ℋ) - star X * X := sub_nonneg.mpr (star_mul_le_one (ℋ := ℋ) X hX)
    have hB : 0 ≤ (1 : L ℋ) - X * star X := sub_nonneg.mpr (mul_star_le_one (ℋ := ℋ) X hX)
    have hnonneg : 0 ≤ blockDiagonal (ℋ := ℋ) (1 - star X * X) (1 - X * star X) :=
      blockDiagonal_nonneg (ℋ := ℋ) hA hB
    have hle :
        blockDiagonal (ℋ := ℋ) (star X * X) (X * star X) ≤
          blockDiagonal (ℋ := ℋ) (star X * X) (X * star X) +
            blockDiagonal (ℋ := ℋ) (1 - star X * X) (1 - X * star X) :=
      le_add_of_nonneg_right hnonneg
    have hsum :
        blockDiagonal (ℋ := ℋ) (star X * X) (X * star X) +
          blockDiagonal (ℋ := ℋ) (1 - star X * X) (1 - X * star X) =
            blockDiagonal (ℋ := ℋ) (1 : L ℋ) (1 : L ℋ) := by
      refine blockOp_ext (ℋ := ℋ) ?_ ?_
      · intro z
        simp [sub_eq_add_neg, add_left_comm, add_comm]
      · intro z
        simp [sub_eq_add_neg, add_left_comm, add_comm]
    have hle' :
        blockDiagonal (ℋ := ℋ) (star X * X) (X * star X) ≤
          blockDiagonal (ℋ := ℋ) (1 : L ℋ) (1 : L ℋ) := by
      simpa [hsum] using hle
    simpa [blockDiagonal_one] using hle'
  have hSstarSle :
      star (blockSwap (ℋ := ℋ) X) * blockSwap (ℋ := ℋ) X ≤ (1 : L (HSum ℋ)) := by
    simpa [hSstarS] using hDiagLe
  have hSstarSnonneg : 0 ≤ star (blockSwap (ℋ := ℋ) X) * blockSwap (ℋ := ℋ) X := by
    exact star_mul_self_nonneg (blockSwap (ℋ := ℋ) X)
  have hnormSq : ‖star (blockSwap (ℋ := ℋ) X) * blockSwap (ℋ := ℋ) X‖ ≤ 1 :=
    (CStarAlgebra.norm_le_one_iff_of_nonneg _ hSstarSnonneg).2 hSstarSle
  have hnormSq' : ‖blockSwap (ℋ := ℋ) X‖ * ‖blockSwap (ℋ := ℋ) X‖ ≤ 1 := by
    simpa [CStarRing.norm_star_mul_self] using hnormSq
  have hsq : ‖blockSwap (ℋ := ℋ) X‖ ^ 2 ≤ 1 := by
    simpa [pow_two] using hnormSq'
  have hnonneg : 0 ≤ ‖blockSwap (ℋ := ℋ) X‖ := norm_nonneg _
  nlinarith

private lemma continuousOn_union_of_subset_Ici {f : ℝ → ℝ}
    (hcont : ContinuousOn f (Set.Ici (0 : ℝ))) {s t : Set ℝ}
    (hs : s ⊆ Set.Ici (0 : ℝ)) (ht : t ⊆ Set.Ici (0 : ℝ)) :
    ContinuousOn f (s ∪ t) := by
  refine hcont.mono ?_
  intro x hx
  rcases hx with hx | hx
  · exact hs hx
  · exact ht hx

private lemma spectrum_Ici_of_nonneg {A : L ℋ} (hA0 : (0 : L ℋ) ≤ A) :
    spectrum ℝ A ⊆ Set.Ici (0 : ℝ) := by
  exact
    (StarOrderedRing.nonneg_iff_spectrum_nonneg (R := ℝ) A
      (ha := IsSelfAdjoint.of_nonneg hA0)).1 hA0

variable [Nontrivial ℋ]

omit [CompleteSpace ℋ] in
private lemma spectrum_zero_subset_Ici :
    spectrum ℝ (0 : L ℋ) ⊆ Set.Ici (0 : ℝ) := by
  intro x hx
  have hx0 : x = 0 := by
    simpa using hx
  simp [Set.Ici, hx0]


--Theorem 2.5.2 `(i) → (iv)`.

set_option maxHeartbeats 2000000 in
-- The localized proof duplicates the block-matrix normalization from the global theorem.
theorem theorem_2_5_2_i_ici_all_imp_iv {f : ℝ → ℝ} (hf : CondIciAll.{u} f) :
    CondIV (ℋ := ℋ) f := by
  rcases hf with ⟨hconvAll, hcontIci, hf0⟩
  intro A X hA hAs hX
  have hconv : OperatorConvexOn (ℋ := ℋ) (Set.Ici (0 : ℝ)) f := hconvAll (K := ℋ)
  have hA0 : (0 : L ℋ) ≤ A := by
    refine (StarOrderedRing.nonneg_iff_spectrum_nonneg (R := ℝ) A (ha := hA)).2 ?_
    intro x hx
    simpa [Set.Ici] using hAs hx
  let S : L (HSum ℋ) := blockSwap (ℋ := ℋ) X
  have hSsa : IsSelfAdjoint S := by
    change star S = S
    simpa [S] using blockSwap_star (ℋ := ℋ) X
  have hSnorm : ‖S‖ ≤ 1 := by
    simpa [S] using blockSwap_norm_le_one (ℋ := ℋ) X hX
  let : Algebra ℝ (L (HSum ℋ)) := by
    infer_instance
  have hU_mem : S + Complex.I • CFC.sqrt (1 - S ^ 2) ∈ unitary (L (HSum ℋ)) := by
    exact IsSelfAdjoint.self_add_I_smul_cfcSqrt_sub_sq_mem_unitary S hSsa hSnorm
  let U : unitary (L (HSum ℋ)) :=
    ⟨S + Complex.I • CFC.sqrt (1 - S ^ 2), hU_mem⟩
  let V : unitary (L (HSum ℋ)) := star U
  let Atilde : L (HSum ℋ) := blockDiagonal (ℋ := ℋ) 0 A
  let : Nontrivial (L (HSum ℋ)) := nontrivial_hsumL (ℋ := ℋ)
  have hconv₂ : OperatorConvexOn (ℋ := HSum ℋ) (Set.Ici (0 : ℝ)) f :=
    hconvAll (K := HSum ℋ)
  have hR0nonneg : (0 : L ℋ) ≤ 1 - star X * X := sub_nonneg.mpr (star_mul_le_one (ℋ := ℋ) X hX)
  have hR1nonneg : (0 : L ℋ) ≤ 1 - X * star X := sub_nonneg.mpr (mul_star_le_one (ℋ := ℋ) X hX)
  let R0 : L ℋ := CFC.sqrt (1 - star X * X)
  let R1 : L ℋ := CFC.sqrt (1 - X * star X)
  have hR0sa : IsSelfAdjoint (1 - star X * X) := by
    change star (1 - star X * X) = 1 - star X * X
    simp
  have hR1sa : IsSelfAdjoint (1 - X * star X) := by
    change star (1 - X * star X) = 1 - X * star X
    simp
  have hSsq : S ^ 2 = blockDiagonal (ℋ := ℋ) (star X * X) (X * star X) := by
    simpa [pow_two, S] using blockSwap_sq (ℋ := ℋ) X
  have hOneMinusSq :
      1 - S ^ 2 = blockDiagonal (ℋ := ℋ) (1 - star X * X) (1 - X * star X) := by
    rw [hSsq]
    refine blockOp_ext (ℋ := ℋ) ?_ ?_
    · intro z
      simp [sub_eq_add_neg, add_comm]
    · intro z
      simp [sub_eq_add_neg, add_comm]
  have hOneMinusSqNonneg : (0 : L (HSum ℋ)) ≤ 1 - S ^ 2 := by
    have hdiag : (0 : L (HSum ℋ)) ≤
        blockDiagonal (ℋ := ℋ) (1 - star X * X) (1 - X * star X) :=
      blockDiagonal_nonneg (ℋ := ℋ) hR0nonneg hR1nonneg
    simpa [hOneMinusSq] using hdiag
  have hRblock : CFC.sqrt (1 - S ^ 2) = blockDiagonal (ℋ := ℋ) R0 R1 := by
    rw [hOneMinusSq]
    simp [R0, R1]
    simpa using
      (sqrt_blockDiagonal_of_nonneg (ℋ := ℋ) (A := 1 - star X * X) (B := 1 - X * star X)
        hR0sa hR1sa hR0nonneg hR1nonneg)
  have hR0self : IsSelfAdjoint R0 := by
    have h : IsSelfAdjoint (CFC.sqrt (1 - star X * X)) :=
      (CFC.sqrt_nonneg (1 - star X * X)).isSelfAdjoint
    simpa [R0] using h
  have hR1self : IsSelfAdjoint R1 := by
    have h : IsSelfAdjoint (CFC.sqrt (1 - X * star X)) :=
      (CFC.sqrt_nonneg (1 - X * star X)).isSelfAdjoint
    simpa [R1] using h
  have hU_block :
      (U : L (HSum ℋ)) = blockOp (ℋ := ℋ) (Complex.I • R0) (star X) X (Complex.I • R1) := by
    change S + Complex.I • CFC.sqrt (1 - S ^ 2) = _
    rw [hRblock]
    simpa [S] using blockSwap_add_I_smul_blockDiagonal (ℋ := ℋ) X R0 R1
  have hV_block :
      (V : L (HSum ℋ)) = blockOp (ℋ := ℋ) (-Complex.I • R0) (star X) X (-Complex.I • R1) := by
    change star (U : L (HSum ℋ)) = _
    rw [hU_block]
    ext z i
    fin_cases i <;>
      simp [blockOp_star, hR0self.star_eq, hR1self.star_eq]
  have hB1_block :
      (star U : L (HSum ℋ)) * Atilde * (U : L (HSum ℋ)) =
        blockOp (ℋ := ℋ)
          (star X * A * X)
          (star X * A * (Complex.I • R1))
          ((-Complex.I • R1) * A * X)
          ((-Complex.I • R1) * A * (Complex.I • R1)) := by
    rw [show (star U : L (HSum ℋ)) = (V : L (HSum ℋ)) by rfl, hV_block, hU_block]
    simpa [Atilde, mul_assoc] using
      (blockOp_mul_blockDiagonal_zero_right (ℋ := ℋ)
        (-Complex.I • R0) (star X) X (-Complex.I • R1) A
        (Complex.I • R0) (star X) X (Complex.I • R1))
  have hB2_block :
      (star V : L (HSum ℋ)) * Atilde * (V : L (HSum ℋ)) =
        blockOp (ℋ := ℋ)
          (star X * A * X)
          (star X * A * (-Complex.I • R1))
          ((Complex.I • R1) * A * X)
          ((Complex.I • R1) * A * (-Complex.I • R1)) := by
    rw [show (star V : L (HSum ℋ)) = (U : L (HSum ℋ)) by simp [V], hU_block, hV_block]
    simpa [Atilde, mul_assoc] using
      (blockOp_mul_blockDiagonal_zero_right (ℋ := ℋ)
        (Complex.I • R0) (star X) X (Complex.I • R1) A
        (-Complex.I • R0) (star X) X (-Complex.I • R1))
  have hmid_block :
      (1 / 2 : ℝ) • ((star U : L (HSum ℋ)) * Atilde * (U : L (HSum ℋ)) ) +
          (1 / 2 : ℝ) • ((star V : L (HSum ℋ)) * Atilde * (V : L (HSum ℋ))) =
        blockDiagonal (ℋ := ℋ) (star X * A * X) (R1 * A * R1) := by
    rw [hB1_block, hB2_block]
    rw [blockOp_smulR, blockOp_smulR, blockOp_add, blockDiagonal_eq_blockOp]
    congr 1
    · have hhalf : (2⁻¹ + 2⁻¹ : ℝ) = (1 : ℝ) := by norm_num
      calc
        (1 / 2 : ℝ) • (star X * A * X) + (1 / 2 : ℝ) • (star X * A * X)
            = (2⁻¹ + 2⁻¹ : ℝ) • (star X * (A * X)) := by
                simp [add_smul, mul_assoc]
        _ = (1 : ℝ) • (star X * (A * X)) := by rw [hhalf]
        _ = star X * (A * X) := by simp
        _ = star X * A * X := by simp [mul_assoc]
    · simp [mul_assoc]
    · simp [mul_assoc]
    · have hhalf : (2⁻¹ + 2⁻¹ : ℝ) = (1 : ℝ) := by norm_num
      calc
        (1 / 2 : ℝ) • (-Complex.I • R1 * A * (Complex.I • R1)) +
            (1 / 2 : ℝ) • (Complex.I • R1 * A * (-Complex.I • R1))
            = (2⁻¹ + 2⁻¹ : ℝ) • (R1 * (A * R1)) := by
                simp [Complex.I_mul_I, smul_smul, add_smul, mul_assoc]
        _ = (1 : ℝ) • (R1 * (A * R1)) := by rw [hhalf]
        _ = R1 * A * R1 := by simp [mul_assoc]
  have hAtilde_sa : IsSelfAdjoint Atilde := by
    simpa [Atilde] using blockDiagonal_selfAdjoint (ℋ := ℋ) (hA := by simp) hA
  have hAtilde0 : (0 : L (HSum ℋ)) ≤ Atilde := by
    simpa [Atilde] using blockDiagonal_nonneg (ℋ := ℋ) (show (0 : L ℋ) ≤ 0 by simp) hA0
  have hAtilde_spec : spectrum ℝ Atilde ⊆ Set.Ici (0 : ℝ) := spectrum_Ici_of_nonneg hAtilde0
  have hB1_nonneg : (0 : L (HSum ℋ)) ≤ (star U : L (HSum ℋ)) * Atilde * (U : L (HSum ℋ)) := by
    simpa [mul_assoc] using star_left_conjugate_nonneg hAtilde0 (U : L (HSum ℋ))
  have hB2_nonneg : (0 : L (HSum ℋ)) ≤ (star V : L (HSum ℋ)) * Atilde * (V : L (HSum ℋ)) := by
    simpa [mul_assoc] using star_left_conjugate_nonneg hAtilde0 (V : L (HSum ℋ))
  have hB1_sa : IsSelfAdjoint ((star U : L (HSum ℋ)) * Atilde * (U : L (HSum ℋ))) :=
    IsSelfAdjoint.of_nonneg hB1_nonneg
  have hB2_sa : IsSelfAdjoint ((star V : L (HSum ℋ)) * Atilde * (V : L (HSum ℋ))) :=
    IsSelfAdjoint.of_nonneg hB2_nonneg
  have hB1_spec : spectrum ℝ (star U * Atilde * (U : L (HSum ℋ))) ⊆ Set.Ici (0 : ℝ) :=
    spectrum_Ici_of_nonneg (ℋ := HSum ℋ) hB1_nonneg
  have hB2_spec : spectrum ℝ (star V * Atilde * (V : L (HSum ℋ))) ⊆ Set.Ici (0 : ℝ) :=
    spectrum_Ici_of_nonneg (ℋ := HSum ℋ) hB2_nonneg
  have hmid_conv :
      cfcR (ℋ := HSum ℋ) f
          ((1 / 2 : ℝ) • ((star U : L (HSum ℋ)) * Atilde * (U : L (HSum ℋ))) +
            (1 / 2 : ℝ) • ((star V : L (HSum ℋ)) * Atilde * (V : L (HSum ℋ)))) ≤
        ((1 / 2 : ℝ) • cfcR (ℋ := HSum ℋ) f ((star U : L (HSum ℋ)) * Atilde * (U : L (HSum ℋ))) +
          (1 / 2 : ℝ) • cfcR (ℋ := HSum ℋ) f ((star V : L (HSum ℋ)) * Atilde * (V : L (HSum ℋ)))) := by
    have hhalf : (1 - (2⁻¹ : ℝ)) = (2⁻¹ : ℝ) := by norm_num
    simpa [hhalf] using
      (hconv₂
        (A := (star U : L (HSum ℋ)) * Atilde * (U : L (HSum ℋ)))
        (B := (star V : L (HSum ℋ)) * Atilde * (V : L (HSum ℋ)))
        (t := (1 / 2 : ℝ))
        hB1_sa hB2_sa (by positivity) (by norm_num) hB1_spec hB2_spec)
  have hAtilde_cfc :
      cfcR (ℋ := HSum ℋ) f Atilde =
        blockDiagonal (ℋ := ℋ) (cfcR (ℋ := ℋ) f 0) (cfcR (ℋ := ℋ) f A) := by
    simpa [Atilde] using
      (cfcR_blockDiagonal (ℋ := ℋ) (f := f) (A := 0) (B := A) (by simp) hA
        (continuousOn_union_of_subset_Ici (f := f) hcontIci
          (s := spectrum ℝ (0 : L ℋ)) (t := spectrum ℝ A)
          spectrum_zero_subset_Ici hAs))
  have hUcfc :
      cfcR (ℋ := HSum ℋ) f ((star U : L (HSum ℋ)) * Atilde * (U : L (HSum ℋ)) ) =
        (star U : L (HSum ℋ)) * cfcR (ℋ := HSum ℋ) f Atilde * (U : L (HSum ℋ)) := by
    simpa [mul_assoc] using
      cfcR_conj_unitary_on (ℋ := HSum ℋ) (s := Set.Ici (0 : ℝ)) (f := f) hcontIci
        hAtilde_spec U hAtilde_sa
  have hVcfc :
      cfcR (ℋ := HSum ℋ) f ((star V : L (HSum ℋ)) * Atilde * (V : L (HSum ℋ)) ) =
        (star V : L (HSum ℋ)) * cfcR (ℋ := HSum ℋ) f Atilde * (V : L (HSum ℋ)) := by
    simpa [mul_assoc] using
      cfcR_conj_unitary_on (ℋ := HSum ℋ) (s := Set.Ici (0 : ℝ)) (f := f) hcontIci
        hAtilde_spec V hAtilde_sa
  have hLeftEval :
      cfcR (ℋ := HSum ℋ) f
          ((1 / 2 : ℝ) • ((star U : L (HSum ℋ)) * Atilde * (U : L (HSum ℋ))) +
            (1 / 2 : ℝ) • ((star V : L (HSum ℋ)) * Atilde * (V : L (HSum ℋ)))) =
        blockDiagonal (cfcR f (star X * A * X)) (cfcR (ℋ := ℋ) f (R1 * A * R1)) := by
    have hXAX_nonneg : (0 : L ℋ) ≤ star X * A * X := by
      simpa [mul_assoc] using star_left_conjugate_nonneg hA0 X
    have hR1AR1_nonneg : (0 : L ℋ) ≤ R1 * A * R1 := by
      simpa [hR1self.star_eq, mul_assoc] using star_right_conjugate_nonneg hA0 R1
    have hXAX_sa : IsSelfAdjoint (star X * A * X) := IsSelfAdjoint.of_nonneg hXAX_nonneg
    have hR1AR1_sa : IsSelfAdjoint (R1 * A * R1) := IsSelfAdjoint.of_nonneg hR1AR1_nonneg
    have hXAX_spec : spectrum ℝ (star X * A * X) ⊆ Set.Ici (0 : ℝ) :=
      spectrum_Ici_of_nonneg (ℋ := ℋ) hXAX_nonneg
    have hR1AR1_spec : spectrum ℝ (R1 * A * R1) ⊆ Set.Ici (0 : ℝ) :=
      spectrum_Ici_of_nonneg (ℋ := ℋ) hR1AR1_nonneg
    rw [hmid_block]
    refine cfcR_blockDiagonal (ℋ := ℋ) (f := f) (A := star X * A * X) (B := R1 * A * R1)
      hXAX_sa hR1AR1_sa ?_
    exact continuousOn_union_of_subset_Ici (f := f) hcontIci hXAX_spec hR1AR1_spec
  have hRightEval :
      ((1 / 2 : ℝ) • cfcR (ℋ := HSum ℋ) f ((star U : L (HSum ℋ)) * Atilde * (U : L (HSum ℋ))) +
        (1 / 2 : ℝ) • cfcR (ℋ := HSum ℋ) f ((star V : L (HSum ℋ)) * Atilde * (V : L (HSum ℋ)))) =
        blockDiagonal (ℋ := ℋ)
          (star X * cfcR (ℋ := ℋ) f A * X + (f 0) • (R0 * R0))
          ((R1 * cfcR (ℋ := ℋ) f A * R1) + (f 0) • (X * star X)) := by
    rw [hUcfc, hVcfc, hAtilde_cfc, cfcR_zero]
    rw [hU_block, hV_block, blockDiagonal_eq_blockOp]
    rw [blockOp_star, blockOp_star]
    simp_rw [mul_assoc]
    rw [blockOp_mul, blockOp_mul, blockOp_mul, blockOp_mul]
    rw [blockOp_smulR, blockOp_smulR, blockOp_add, blockDiagonal_eq_blockOp]
    have hTopLeft :
        (2⁻¹ : ℝ) • (star X * (cfcR (ℋ := ℋ) f A * X)) +
            ((2⁻¹ : ℝ) • (star X * (cfcR (ℋ := ℋ) f A * X)) +
              (-((2⁻¹ : ℝ) • Complex.I • f 0 • Complex.I • (R0 * R0)) +
                -((2⁻¹ : ℝ) • Complex.I • f 0 • Complex.I • (R0 * R0)))) =
          star X * (cfcR (ℋ := ℋ) f A * X) + (f 0) • (R0 * R0) := by
      simpa using
        rightEval_topLeft_scalar (ℋ := ℋ) (r := f 0) (R0 := R0) (X := X)
          (T := cfcR (ℋ := ℋ) f A)
    have hBottomRight :
        (2⁻¹ * f 0) • (X * star X) +
            ((2⁻¹ * f 0) • (X * star X) +
              ((2⁻¹ : ℝ) • (R1 * (cfcR (ℋ := ℋ) f A * R1)) +
                (2⁻¹ : ℝ) • (R1 * (cfcR (ℋ := ℋ) f A * R1)))) =
          (R1 * cfcR (ℋ := ℋ) f A * R1) + (f 0) • (X * star X) := by
      simpa [mul_assoc] using
        rightEval_bottomRight_scalar (ℋ := ℋ) (r := f 0) (R1 := R1) (X := X)
          (T := cfcR (ℋ := ℋ) f A)
    congr 1
    · simpa [hR0self.star_eq, Algebra.algebraMap_eq_smul_one, mul_assoc,
        add_assoc, add_left_comm, add_comm] using hTopLeft
    · simp [Algebra.algebraMap_eq_smul_one]
      abel
    · simp [Algebra.algebraMap_eq_smul_one]
      abel
    · simpa [hR1self.star_eq, Algebra.algebraMap_eq_smul_one, Complex.I_mul_I, smul_smul,
        mul_assoc, add_assoc, add_left_comm, add_comm] using hBottomRight
  have hcore :
      blockDiagonal (ℋ := ℋ) (cfcR (ℋ := ℋ) f (star X * A * X)) (cfcR (ℋ := ℋ) f (R1 * A * R1)) ≤
        blockDiagonal (ℋ := ℋ)
          (star X * cfcR (ℋ := ℋ) f A * X + (f 0) • (R0 * R0))
          ((R1 * cfcR (ℋ := ℋ) f A * R1) + (f 0) • (X * star X)) := by
    rw [hLeftEval, hRightEval] at hmid_conv
    exact hmid_conv
  have hterm_nonpos : (f 0) • (R0 * R0) ≤ (0 : L ℋ) := by
    have hR0sq_nonneg : (0 : L ℋ) ≤ R0 * R0 := by
      simpa [hR0self.star_eq] using star_mul_self_nonneg R0
    have hneg : (0 : L ℋ) ≤ (- (f 0)) • (R0 * R0) := by
      exact smul_nonneg (by linarith [hf0]) hR0sq_nonneg
    exact (neg_nonneg.mp (by simpa [neg_smul] using hneg))
  have htop :
      cfcR (ℋ := ℋ) f (star X * A * X) ≤ star X * cfcR (ℋ := ℋ) f A * X + (f 0) • (R0 * R0) := by
    exact blockDiagonal_le_left (ℋ := ℋ) hcore
  have hdrop :
      star X * cfcR (ℋ := ℋ) f A * X + (f 0) • (R0 * R0) ≤ star X * cfcR (ℋ := ℋ) f A * X := by
    simpa [add_comm, add_left_comm, add_assoc] using
      add_le_add_left hterm_nonpos (star X * cfcR (ℋ := ℋ) f A * X)
  exact htop.trans hdrop

set_option maxHeartbeats 2000000 in
-- The global proof repeats the same block-matrix normalization and unitary conjugation pattern.
theorem theorem_2_5_2_i_all_imp_iv {f : ℝ → ℝ} (hf : CondIAll.{u} f) :
    CondIV (ℋ := ℋ) f := by
  rcases hf with ⟨hconvAll, hf0⟩
  intro A X hA hAs hX
  have hconv : OperatorConvex (ℋ := ℋ) f := hconvAll (K := ℋ)
  let S : L (HSum ℋ) := blockSwap (ℋ := ℋ) X
  have hSsa : IsSelfAdjoint S := by
    change star S = S
    simpa [S] using blockSwap_star (ℋ := ℋ) X
  have hSnorm : ‖S‖ ≤ 1 := by
    simpa [S] using blockSwap_norm_le_one (ℋ := ℋ) X hX
  let : Algebra ℝ (L (HSum ℋ)) := by
    infer_instance
  have hU_mem : S + Complex.I • CFC.sqrt (1 - S ^ 2) ∈ unitary (L (HSum ℋ)) := by
    exact IsSelfAdjoint.self_add_I_smul_cfcSqrt_sub_sq_mem_unitary S hSsa hSnorm
  let U : unitary (L (HSum ℋ)) :=
    ⟨S + Complex.I • CFC.sqrt (1 - S ^ 2), hU_mem⟩
  let V : unitary (L (HSum ℋ)) := star U
  let Atilde : L (HSum ℋ) := blockDiagonal (ℋ := ℋ) 0 A
  let : Nontrivial (L (HSum ℋ)) := nontrivial_hsumL (ℋ := ℋ)
  have hconv₂ : OperatorConvex (ℋ := HSum ℋ) f := hconvAll (K := HSum ℋ)
  have hcont₂ : ContinuousOn f Set.univ :=
    operatorConvex_continuousOn_univ (ℋ := HSum ℋ) hconv₂
  have hR0nonneg : (0 : L ℋ) ≤ 1 - star X * X := sub_nonneg.mpr (star_mul_le_one (ℋ := ℋ) X hX)
  have hR1nonneg : (0 : L ℋ) ≤ 1 - X * star X := sub_nonneg.mpr (mul_star_le_one (ℋ := ℋ) X hX)
  let R0 : L ℋ := CFC.sqrt (1 - star X * X)
  let R1 : L ℋ := CFC.sqrt (1 - X * star X)
  have hR0sa : IsSelfAdjoint (1 - star X * X) := by
    change star (1 - star X * X) = 1 - star X * X
    simp
  have hR1sa : IsSelfAdjoint (1 - X * star X) := by
    change star (1 - X * star X) = 1 - X * star X
    simp
  have hSsq : S ^ 2 = blockDiagonal (ℋ := ℋ) (star X * X) (X * star X) := by
    simpa [pow_two, S] using blockSwap_sq (ℋ := ℋ) X
  have hOneMinusSq :
      1 - S ^ 2 = blockDiagonal (ℋ := ℋ) (1 - star X * X) (1 - X * star X) := by
    rw [hSsq]
    refine blockOp_ext (ℋ := ℋ) ?_ ?_
    · intro z
      simp [sub_eq_add_neg, add_comm]
    · intro z
      simp [sub_eq_add_neg, add_comm]
  have hOneMinusSqNonneg : (0 : L (HSum ℋ)) ≤ 1 - S ^ 2 := by
    have hdiag : (0 : L (HSum ℋ)) ≤
        blockDiagonal (ℋ := ℋ) (1 - star X * X) (1 - X * star X) :=
      blockDiagonal_nonneg (ℋ := ℋ) hR0nonneg hR1nonneg
    simpa [hOneMinusSq] using hdiag
  have hRblock : CFC.sqrt (1 - S ^ 2) = blockDiagonal (ℋ := ℋ) R0 R1 := by
    rw [hOneMinusSq]
    simp [R0, R1]
    simpa using
      (sqrt_blockDiagonal_of_nonneg (ℋ := ℋ) (A := 1 - star X * X) (B := 1 - X * star X)
        hR0sa hR1sa hR0nonneg hR1nonneg)
  have hR0self : IsSelfAdjoint R0 := by
    have h : IsSelfAdjoint (CFC.sqrt (1 - star X * X)) :=
      (CFC.sqrt_nonneg (1 - star X * X)).isSelfAdjoint
    simpa [R0] using h
  have hR1self : IsSelfAdjoint R1 := by
    have h : IsSelfAdjoint (CFC.sqrt (1 - X * star X)) :=
      (CFC.sqrt_nonneg (1 - X * star X)).isSelfAdjoint
    simpa [R1] using h
  have hU_block :
      (U : L (HSum ℋ)) = blockOp (ℋ := ℋ) (Complex.I • R0) (star X) X (Complex.I • R1) := by
    change S + Complex.I • CFC.sqrt (1 - S ^ 2) = _
    rw [hRblock]
    simpa [S] using blockSwap_add_I_smul_blockDiagonal (ℋ := ℋ) X R0 R1
  have hV_block :
      (V : L (HSum ℋ)) = blockOp (ℋ := ℋ) (-Complex.I • R0) (star X) X (-Complex.I • R1) := by
    change star (U : L (HSum ℋ)) = _
    rw [hU_block]
    ext z i
    fin_cases i <;>
      simp [blockOp_star, hR0self.star_eq, hR1self.star_eq]
  have hB1_block :
      (star U : L (HSum ℋ)) * Atilde * (U : L (HSum ℋ)) =
        blockOp (ℋ := ℋ)
          (star X * A * X)
          (star X * A * (Complex.I • R1))
          ((-Complex.I • R1) * A * X)
          ((-Complex.I • R1) * A * (Complex.I • R1)) := by
    rw [show (star U : L (HSum ℋ)) = (V : L (HSum ℋ)) by rfl, hV_block, hU_block]
    simpa [Atilde, mul_assoc] using
      (blockOp_mul_blockDiagonal_zero_right (ℋ := ℋ)
        (-Complex.I • R0) (star X) X (-Complex.I • R1) A
        (Complex.I • R0) (star X) X (Complex.I • R1))
  have hB2_block :
      (star V : L (HSum ℋ)) * Atilde * (V : L (HSum ℋ)) =
        blockOp (ℋ := ℋ)
          (star X * A * X)
          (star X * A * (-Complex.I • R1))
          ((Complex.I • R1) * A * X)
          ((Complex.I • R1) * A * (-Complex.I • R1)) := by
    rw [show (star V : L (HSum ℋ)) = (U : L (HSum ℋ)) by simp [V], hU_block, hV_block]
    simpa [Atilde, mul_assoc] using
      (blockOp_mul_blockDiagonal_zero_right (ℋ := ℋ)
        (Complex.I • R0) (star X) X (Complex.I • R1) A
        (-Complex.I • R0) (star X) X (-Complex.I • R1))
  have hmid_block :
      (1 / 2 : ℝ) • ((star U : L (HSum ℋ)) * Atilde * (U : L (HSum ℋ)) ) +
          (1 / 2 : ℝ) • ((star V : L (HSum ℋ)) * Atilde * (V : L (HSum ℋ))) =
        blockDiagonal (ℋ := ℋ) (star X * A * X) (R1 * A * R1) := by
    rw [hB1_block, hB2_block]
    rw [blockOp_smulR, blockOp_smulR, blockOp_add, blockDiagonal_eq_blockOp]
    congr 1
    · have hhalf : (2⁻¹ + 2⁻¹ : ℝ) = (1 : ℝ) := by norm_num
      calc
        (1 / 2 : ℝ) • (star X * A * X) + (1 / 2 : ℝ) • (star X * A * X)
            = (2⁻¹ + 2⁻¹ : ℝ) • (star X * (A * X)) := by
                simp [add_smul, mul_assoc]
        _ = (1 : ℝ) • (star X * (A * X)) := by rw [hhalf]
        _ = star X * (A * X) := by simp
        _ = star X * A * X := by simp [mul_assoc]
    · simp [mul_assoc]
    · simp [mul_assoc]
    · have hhalf : (2⁻¹ + 2⁻¹ : ℝ) = (1 : ℝ) := by norm_num
      calc
        (1 / 2 : ℝ) • (-Complex.I • R1 * A * (Complex.I • R1)) +
            (1 / 2 : ℝ) • (Complex.I • R1 * A * (-Complex.I • R1))
            = (2⁻¹ + 2⁻¹ : ℝ) • (R1 * (A * R1)) := by
                simp [Complex.I_mul_I, smul_smul, add_smul, mul_assoc]
        _ = (1 : ℝ) • (R1 * (A * R1)) := by rw [hhalf]
        _ = R1 * A * R1 := by simp [mul_assoc]
  have hmid_conv :
      cfcR (ℋ := HSum ℋ) f
          ((1 / 2 : ℝ) • ((star U : L (HSum ℋ)) * Atilde * (U : L (HSum ℋ))) +
            (1 / 2 : ℝ) • ((star V : L (HSum ℋ)) * Atilde * (V : L (HSum ℋ)))) ≤
        ((1 / 2 : ℝ) • cfcR f ((star U : L (HSum ℋ)) * Atilde * (U : L (HSum ℋ))) +
          (1 / 2 : ℝ) • cfcR f ((star V : L (HSum ℋ)) * Atilde * (V : L (HSum ℋ)))) := by
    have hhalf : (1 - (2⁻¹ : ℝ)) = (2⁻¹ : ℝ) := by norm_num
    simpa [hhalf] using
        (hconv₂
          (A := (star U : L (HSum ℋ)) * Atilde * (U : L (HSum ℋ)))
          (B := (star V : L (HSum ℋ)) * Atilde * (V : L (HSum ℋ)))
          (t := (1 / 2 : ℝ))
          (by positivity) (by norm_num))
  have hAtilde_sa : IsSelfAdjoint Atilde := by
    simpa [Atilde] using blockDiagonal_selfAdjoint (ℋ := ℋ) (hA := by simp) hA
  have hAtilde_cfc :
      cfcR (ℋ := HSum ℋ) f Atilde =
        blockDiagonal (ℋ := ℋ) (cfcR (ℋ := ℋ) f 0) (cfcR (ℋ := ℋ) f A) := by
    simpa [Atilde] using
      (cfcR_blockDiagonal (ℋ := ℋ) (f := f) (A := 0) (B := A) (by simp) hA
        ((operatorConvex_continuousOn_univ (ℋ := ℋ) hconv).mono (by intro x hx; simp)))
  have hUcfc :
      cfcR (ℋ := HSum ℋ) f ((star U : L (HSum ℋ)) * Atilde * (U : L (HSum ℋ)) ) =
        (star U : L (HSum ℋ)) * cfcR (ℋ := HSum ℋ) f Atilde * (U : L (HSum ℋ)) := by
    simpa [mul_assoc] using cfcR_conj_unitary (ℋ := HSum ℋ) f hcont₂ U Atilde hAtilde_sa
  have hVcfc :
      cfcR (ℋ := HSum ℋ) f ((star V : L (HSum ℋ)) * Atilde * (V : L (HSum ℋ)) ) =
        (star V : L (HSum ℋ)) * cfcR (ℋ := HSum ℋ) f Atilde * (V : L (HSum ℋ)) := by
    simpa [mul_assoc] using cfcR_conj_unitary (ℋ := HSum ℋ) f hcont₂ V Atilde hAtilde_sa
  have hLeftEval :
      cfcR (ℋ := HSum ℋ) f
          ((1 / 2 : ℝ) • ((star U : L (HSum ℋ)) * Atilde * (U : L (HSum ℋ))) +
            (1 / 2 : ℝ) • ((star V : L (HSum ℋ)) * Atilde * (V : L (HSum ℋ)))) =
        blockDiagonal (cfcR f (star X * A * X)) (cfcR f (R1 * A * R1)) := by
    have hXAX_sa : IsSelfAdjoint (star X * A * X) := by
      change star (star X * A * X) = star X * A * X
      simp [hA.star_eq, mul_assoc]
    have hR1AR1_sa : IsSelfAdjoint (R1 * A * R1) := by
      change star (R1 * A * R1) = R1 * A * R1
      simp [hR1self.star_eq, hA.star_eq, mul_assoc]
    rw [hmid_block]
    refine cfcR_blockDiagonal (f := f) (A := star X * A * X) (B := R1 * A * R1) hXAX_sa hR1AR1_sa ?_
    · exact (operatorConvex_continuousOn_univ (ℋ := ℋ) hconv).mono (by intro x hx; simp)
  have hRightEval :
      ((1 / 2 : ℝ) • cfcR (ℋ := HSum ℋ) f ((star U : L (HSum ℋ)) * Atilde * (U : L (HSum ℋ))) +
        (1 / 2 : ℝ) • cfcR (ℋ := HSum ℋ) f ((star V : L (HSum ℋ)) * Atilde * (V : L (HSum ℋ)))) =
        blockDiagonal (ℋ := ℋ)
          (star X * cfcR (ℋ := ℋ) f A * X + (f 0) • (R0 * R0))
          ((R1 * cfcR (ℋ := ℋ) f A * R1) + (f 0) • (X * star X)) := by
    rw [hUcfc, hVcfc, hAtilde_cfc, cfcR_zero]
    rw [hU_block, hV_block, blockDiagonal_eq_blockOp]
    rw [blockOp_star, blockOp_star]
    simp_rw [mul_assoc]
    rw [blockOp_mul, blockOp_mul, blockOp_mul, blockOp_mul]
    rw [blockOp_smulR, blockOp_smulR, blockOp_add, blockDiagonal_eq_blockOp]
    have hTopLeft :
        (2⁻¹ : ℝ) • (star X * (cfcR (ℋ := ℋ) f A * X)) +
            ((2⁻¹ : ℝ) • (star X * (cfcR (ℋ := ℋ) f A * X)) +
              (-((2⁻¹ : ℝ) • Complex.I • f 0 • Complex.I • (R0 * R0)) +
                -((2⁻¹ : ℝ) • Complex.I • f 0 • Complex.I • (R0 * R0)))) =
          star X * (cfcR (ℋ := ℋ) f A * X) + (f 0) • (R0 * R0) := by
      simpa using
        rightEval_topLeft_scalar (ℋ := ℋ) (r := f 0) (R0 := R0) (X := X)
          (T := cfcR (ℋ := ℋ) f A)
    have hBottomRight :
        (2⁻¹ * f 0) • (X * star X) +
            ((2⁻¹ * f 0) • (X * star X) +
              ((2⁻¹ : ℝ) • (R1 * (cfcR (ℋ := ℋ) f A * R1)) +
                (2⁻¹ : ℝ) • (R1 * (cfcR (ℋ := ℋ) f A * R1)))) =
          (R1 * cfcR (ℋ := ℋ) f A * R1) + (f 0) • (X * star X) := by
      simpa [mul_assoc] using
        rightEval_bottomRight_scalar (ℋ := ℋ) (r := f 0) (R1 := R1) (X := X)
          (T := cfcR (ℋ := ℋ) f A)
    congr 1
    · simpa [hR0self.star_eq, Algebra.algebraMap_eq_smul_one, mul_assoc,
        add_assoc, add_left_comm, add_comm] using hTopLeft
    · simp [Algebra.algebraMap_eq_smul_one]
      abel
    · simp [Algebra.algebraMap_eq_smul_one]
      abel
    · simpa [hR1self.star_eq, Algebra.algebraMap_eq_smul_one, Complex.I_mul_I, smul_smul,
        mul_assoc, add_assoc, add_left_comm, add_comm] using hBottomRight
  have hcore :
      blockDiagonal (ℋ := ℋ) (cfcR (ℋ := ℋ) f (star X * A * X)) (cfcR (ℋ := ℋ) f (R1 * A * R1)) ≤
        blockDiagonal (ℋ := ℋ)
          (star X * cfcR (ℋ := ℋ) f A * X + (f 0) • (R0 * R0))
          ((R1 * cfcR (ℋ := ℋ) f A * R1) + (f 0) • (X * star X)) := by
    rw [hLeftEval, hRightEval] at hmid_conv
    exact hmid_conv
  have hterm_nonpos : (f 0) • (R0 * R0) ≤ (0 : L ℋ) := by
    have hR0sq_nonneg : (0 : L ℋ) ≤ R0 * R0 := by
      simpa [hR0self.star_eq] using star_mul_self_nonneg R0
    have hneg : (0 : L ℋ) ≤ (- (f 0)) • (R0 * R0) := by
      exact smul_nonneg (by linarith [hf0]) hR0sq_nonneg
    exact (neg_nonneg.mp (by simpa [neg_smul] using hneg))
  have htop :
      cfcR (ℋ := ℋ) f (star X * A * X) ≤ star X * cfcR (ℋ := ℋ) f A * X + (f 0) • (R0 * R0) := by
    exact blockDiagonal_le_left (ℋ := ℋ) hcore
  have hdrop :
      star X * cfcR (ℋ := ℋ) f A * X + (f 0) • (R0 * R0) ≤ star X * cfcR (ℋ := ℋ) f A * X := by
    simpa [add_comm, add_left_comm, add_assoc] using
      add_le_add_left hterm_nonpos (star X * cfcR f A * X)
  exact htop.trans hdrop

end Theorem252

end JensenOperatorInequality
