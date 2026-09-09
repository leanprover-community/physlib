/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.AlgebraicFramework.HilbertSpace.Unbounded.BoundedSelfAdjointData
public import Mathlib.MeasureTheory.VectorMeasure.SetIntegral

/-!

# A `{0,1}`-valued, boundedly supported `WOTSpectralMeasure` is a point mass

Stage one of the missing piece flagged in `Irreducible.lean`'s `key` lemma: a boundedly σ-additive
`{0,1}`-valued Borel measure on `ℝ` is a Dirac point mass. Built by bisecting the bounded support
interval, always keeping the half with measure `1`, and taking the (real-number) limit of the
resulting nested interval endpoints.

## Main definitions

- `WOTSpectralMeasure.exists_forall_notMem_measure_eq_zero` : given a bounded support and a
  `{0,1}`-valued measure, there is a point `r` such that every measurable set avoiding `r` has
  measure `0`.

-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Topology Classical

namespace QuantumMechanics

namespace WOTSpectralMeasure

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

section Bisect

variable (μ : WOTSpectralMeasure ℝ H)

/-- One bisection step: split `[p.1, p.2]` at its midpoint, and keep whichever half has
measure `1` (both halves are measurable, disjoint, and union to the whole interval, so by
`h01` and additivity exactly one of them does). `h01` itself is not needed to *define* this
step — only `Decidable`-free classical case analysis on `μ (Icc p.1 m) = 1` — it is only used
later to *prove properties* of the resulting sequence. -/
private noncomputable def bisectStep (p : ℝ × ℝ) : ℝ × ℝ :=
  let m := (p.1 + p.2) / 2
  if μ (Icc p.1 m) = 1 then (p.1, m) else (m, p.2)

/-- The `n`-th bisection interval's endpoints, starting from `(a, b)`. -/
private noncomputable def bisect (a b : ℝ) : ℕ → ℝ × ℝ
  | 0 => (a, b)
  | n + 1 => bisectStep μ (bisect a b n)

private theorem bisectStep_fst_le_snd {p : ℝ × ℝ} (h : p.1 ≤ p.2) :
    (bisectStep μ p).1 ≤ (bisectStep μ p).2 := by
  simp only [bisectStep]
  split <;> dsimp <;> linarith

private theorem bisectStep_sub (p : ℝ × ℝ) :
    (bisectStep μ p).2 - (bisectStep μ p).1 = (p.2 - p.1) / 2 := by
  simp only [bisectStep]
  split <;> dsimp <;> ring

private theorem bisectStep_fst_le {p : ℝ × ℝ} (h : p.1 ≤ p.2) : p.1 ≤ (bisectStep μ p).1 := by
  simp only [bisectStep]; split <;> dsimp <;> linarith

private theorem bisectStep_snd_le {p : ℝ × ℝ} (h : p.1 ≤ p.2) : (bisectStep μ p).2 ≤ p.2 := by
  simp only [bisectStep]; split <;> dsimp <;> linarith

private theorem bisectStep_subset {p : ℝ × ℝ} (h : p.1 ≤ p.2) :
    Icc (bisectStep μ p).1 (bisectStep μ p).2 ⊆ Icc p.1 p.2 :=
  Icc_subset_Icc (bisectStep_fst_le μ h) (bisectStep_snd_le μ h)

private theorem bisect_fst_le_snd {a b : ℝ} (hab : a ≤ b) :
    ∀ n, (bisect μ a b n).1 ≤ (bisect μ a b n).2
  | 0 => hab
  | n + 1 => bisectStep_fst_le_snd μ (bisect_fst_le_snd hab n)

private theorem bisect_sub (a b : ℝ) :
    ∀ n, (bisect μ a b n).2 - (bisect μ a b n).1 = (b - a) / 2 ^ n
  | 0 => by simp [bisect]
  | n + 1 => by
      show (bisectStep μ (bisect μ a b n)).2 - (bisectStep μ (bisect μ a b n)).1 = _
      rw [bisectStep_sub, bisect_sub a b n]
      ring

private theorem bisect_fst_mono {a b : ℝ} (hab : a ≤ b) (n : ℕ) :
    (bisect μ a b n).1 ≤ (bisect μ a b (n + 1)).1 :=
  bisectStep_fst_le μ (bisect_fst_le_snd μ hab n)

private theorem bisect_snd_mono {a b : ℝ} (hab : a ≤ b) (n : ℕ) :
    (bisect μ a b (n + 1)).2 ≤ (bisect μ a b n).2 :=
  bisectStep_snd_le μ (bisect_fst_le_snd μ hab n)

private theorem bisect_subset {a b : ℝ} (hab : a ≤ b) (n : ℕ) :
    Icc (bisect μ a b (n + 1)).1 (bisect μ a b (n + 1)).2 ⊆
      Icc (bisect μ a b n).1 (bisect μ a b n).2 :=
  bisectStep_subset μ (bisect_fst_le_snd μ hab n)

/-- If the whole interval has measure `1`, the bisected interval does too: whichever half
`bisectStep` keeps is forced to have measure `1` by additivity across the (disjoint) split. -/
private theorem bisectStep_measure_one (h01 : ∀ E : Set ℝ, MeasurableSet E → μ E = 0 ∨ μ E = 1)
    {p : ℝ × ℝ} (h : p.1 ≤ p.2) (hμ : μ (Icc p.1 p.2) = 1) :
    μ (Icc (bisectStep μ p).1 (bisectStep μ p).2) = 1 := by
  simp only [bisectStep]
  set m := (p.1 + p.2) / 2 with hm_def
  have hm1 : p.1 ≤ m := by rw [hm_def]; linarith
  have hm2 : m ≤ p.2 := by rw [hm_def]; linarith
  by_cases hc : μ (Icc p.1 m) = 1
  · simpa [hc]
  · simp only [hc, if_false]
    have hc0 : μ (Icc p.1 m) = 0 := (h01 _ measurableSet_Icc).resolve_right hc
    have hunion : Icc p.1 m ∪ Ioc m p.2 = Icc p.1 p.2 := Icc_union_Ioc_eq_Icc hm1 hm2
    have hdisj : Disjoint (Icc p.1 m) (Ioc m p.2) := by
      rw [Set.disjoint_left]
      rintro x ⟨-, hx2⟩ ⟨hx3, -⟩
      exact absurd hx2 (not_le.mpr hx3)
    have heq : μ (Icc p.1 m) + μ (Ioc m p.2) = μ (Icc p.1 p.2) := by
      rw [← hunion]
      exact (μ.of_union hdisj measurableSet_Icc measurableSet_Ioc).symm
    rw [hc0, hμ, zero_add] at heq
    have hinter : Ioc m p.2 ∩ Icc m p.2 = Ioc m p.2 := by
      rw [Set.inter_eq_left]
      exact Ioc_subset_Icc_self
    have hmul : μ (Ioc m p.2) * μ (Icc m p.2) = μ (Ioc m p.2) := by
      rw [μ.comp_eq_of_inter measurableSet_Ioc measurableSet_Icc, hinter]
    rw [heq, one_mul] at hmul
    exact hmul

private theorem bisect_measure_one (h01 : ∀ E : Set ℝ, MeasurableSet E → μ E = 0 ∨ μ E = 1)
    {a b : ℝ} (hab : a ≤ b) (hμ : μ (Icc a b) = 1) :
    ∀ n, μ (Icc (bisect μ a b n).1 (bisect μ a b n).2) = 1
  | 0 => by simpa [bisect] using hμ
  | n + 1 =>
      bisectStep_measure_one μ h01 (bisect_fst_le_snd μ hab n) (bisect_measure_one h01 hab hμ n)

/-- The half discarded at each bisection step has measure `0`. -/
private theorem bisect_diff_measure_zero
    (h01 : ∀ E : Set ℝ, MeasurableSet E → μ E = 0 ∨ μ E = 1)
    {a b : ℝ} (hab : a ≤ b) (hμ : μ (Icc a b) = 1) (n : ℕ) :
    μ (Icc (bisect μ a b n).1 (bisect μ a b n).2 \
        Icc (bisect μ a b (n + 1)).1 (bisect μ a b (n + 1)).2) = 0 := by
  rw [μ.toVectorMeasure.of_sdiff measurableSet_Icc measurableSet_Icc (bisect_subset μ hab n),
    bisect_measure_one μ h01 hab hμ (n + 1), bisect_measure_one μ h01 hab hμ n, sub_self]

end Bisect

section Limit

variable (μ : WOTSpectralMeasure ℝ H) {a b : ℝ}

private theorem bisectFst_mono (hab : a ≤ b) : Monotone (fun n => (bisect μ a b n).1) :=
  monotone_nat_of_le_succ (fun n => bisect_fst_mono μ hab n)

private theorem bisectSnd_anti (hab : a ≤ b) : Antitone (fun n => (bisect μ a b n).2) :=
  antitone_nat_of_succ_le (fun n => bisect_snd_mono μ hab n)

private theorem bisectSnd_le_start (hab : a ≤ b) (n : ℕ) : (bisect μ a b n).2 ≤ b :=
  bisectSnd_anti μ hab (Nat.zero_le n) |>.trans_eq (by simp [bisect])

private theorem bisectFst_ge_start (hab : a ≤ b) (n : ℕ) : a ≤ (bisect μ a b n).1 :=
  (by simp [bisect] : a = (bisect μ a b 0).1) ▸ bisectFst_mono μ hab (Nat.zero_le n)

private theorem bddAbove_bisectFst (hab : a ≤ b) :
    BddAbove (Set.range (fun n => (bisect μ a b n).1)) :=
  ⟨b, by rintro _ ⟨n, rfl⟩; exact (bisect_fst_le_snd μ hab n).trans (bisectSnd_le_start μ hab n)⟩

private theorem bddBelow_bisectSnd (hab : a ≤ b) :
    BddBelow (Set.range (fun n => (bisect μ a b n).2)) :=
  ⟨a, by rintro _ ⟨n, rfl⟩; exact (bisectFst_ge_start μ hab n).trans (bisect_fst_le_snd μ hab n)⟩

/-- The bisection point: the common limit of the (monotone, bounded) left and (antitone,
bounded) right endpoints. `hab` is not needed to state the supremum, only to prove its
properties, but is kept explicit here for uniformity with the theorems about it below. -/
private noncomputable def bisectPoint (_hab : a ≤ b) : ℝ := ⨆ n, (bisect μ a b n).1

private theorem tendsto_bisectFst (hab : a ≤ b) :
    Tendsto (fun n => (bisect μ a b n).1) atTop (𝓝 (bisectPoint μ hab)) :=
  tendsto_atTop_ciSup (bisectFst_mono μ hab) (bddAbove_bisectFst μ hab)

private theorem tendsto_bisectSub (a b : ℝ) :
    Tendsto (fun n => (bisect μ a b n).2 - (bisect μ a b n).1) atTop (𝓝 0) := by
  have heq : (fun n => (bisect μ a b n).2 - (bisect μ a b n).1) =
      (fun n : ℕ => (b - a) / 2 ^ n) := funext (bisect_sub μ a b)
  rw [heq]
  simpa using tendsto_const_nhds.div_atTop
    (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2))

private theorem tendsto_bisectSnd (hab : a ≤ b) :
    Tendsto (fun n => (bisect μ a b n).2) atTop (𝓝 (bisectPoint μ hab)) := by
  have h := (tendsto_bisectSub μ a b).add (tendsto_bisectFst μ hab)
  simp only [zero_add] at h
  refine h.congr (fun n => ?_)
  ring

private theorem bisectFst_le_bisectPoint (hab : a ≤ b) (n : ℕ) :
    (bisect μ a b n).1 ≤ bisectPoint μ hab :=
  le_ciSup (bddAbove_bisectFst μ hab) n

private theorem bisectPoint_le_bisectSnd (hab : a ≤ b) (n : ℕ) :
    bisectPoint μ hab ≤ (bisect μ a b n).2 := by
  have hanti := bisectSnd_anti μ hab
  have hlim := tendsto_bisectSnd μ hab
  exact le_of_tendsto hlim (Filter.eventually_atTop.mpr ⟨n, fun m hm => hanti hm⟩)

/-- The bisection intervals shrink to exactly the bisection point. -/
private theorem iInter_bisectIcc (hab : a ≤ b) :
    ⋂ n, Icc (bisect μ a b n).1 (bisect μ a b n).2 = {bisectPoint μ hab} := by
  ext x
  simp only [Set.mem_iInter, Set.mem_Icc, Set.mem_singleton_iff]
  constructor
  · intro hx
    have h1 : bisectPoint μ hab ≤ x :=
      le_of_tendsto (tendsto_bisectFst μ hab)
        (Filter.Eventually.of_forall (fun n => (hx n).1))
    have h2 : x ≤ bisectPoint μ hab :=
      ge_of_tendsto (tendsto_bisectSnd μ hab)
        (Filter.Eventually.of_forall (fun n => (hx n).2))
    linarith
  · rintro rfl
    exact fun n => ⟨bisectFst_le_bisectPoint μ hab n, bisectPoint_le_bisectSnd μ hab n⟩

/-- **The bisection point carries the full measure.** Since every bisection interval has measure
`1` and the intervals shrink to exactly `{bisectPoint}`, continuity from above (`Mathlib`'s
`tendsto_vectorMeasure_iInter_atTop_nat`) forces `μ {bisectPoint} = 1`. -/
private theorem measure_singleton_bisectPoint
    (h01 : ∀ E : Set ℝ, MeasurableSet E → μ E = 0 ∨ μ E = 1) (hab : a ≤ b)
    (hμ : μ (Icc a b) = 1) :
    μ {bisectPoint μ hab} = 1 := by
  have hanti : Antitone (fun n => Icc (bisect μ a b n).1 (bisect μ a b n).2) :=
    antitone_nat_of_succ_le (fun n => bisect_subset μ hab n)
  have hmeas : ∀ n, MeasurableSet (Icc (bisect μ a b n).1 (bisect μ a b n).2) :=
    fun _ => measurableSet_Icc
  have htendsto := μ.toVectorMeasure.tendsto_vectorMeasure_iInter_atTop_nat hanti hmeas
  rw [iInter_bisectIcc μ hab] at htendsto
  have hconst : (fun n => μ (Icc (bisect μ a b n).1 (bisect μ a b n).2)) =
      fun _ : ℕ => (1 : H →WOT[ℂ] H) := funext (bisect_measure_one μ h01 hab hμ)
  rw [hconst] at htendsto
  exact tendsto_nhds_unique htendsto tendsto_const_nhds

/-- **The point-mass theorem.** A boundedly σ-additive `{0,1}`-valued Borel measure on `ℝ`
concentrates all of its mass at a single point: every measurable set avoiding that point has
measure `0`. -/
theorem exists_forall_notMem_measure_eq_zero
    (h01 : ∀ E : Set ℝ, MeasurableSet E → μ E = 0 ∨ μ E = 1) (hab : a ≤ b)
    (hμ : μ (Icc a b) = 1) :
    ∃ r : ℝ, μ {r} = 1 ∧ ∀ E : Set ℝ, MeasurableSet E → r ∉ E → μ E = 0 := by
  refine ⟨bisectPoint μ hab, measure_singleton_bisectPoint μ h01 hab hμ, fun E hE hrE => ?_⟩
  have hinter : E ∩ {bisectPoint μ hab} = (∅ : Set ℝ) := by
    rw [Set.inter_singleton_eq_empty]; exact hrE
  have hmul : μ E * μ {bisectPoint μ hab} = μ (∅ : Set ℝ) := by
    rw [← hinter]
    exact μ.comp_eq_of_inter hE (measurableSet_singleton (bisectPoint μ hab))
  rw [measure_singleton_bisectPoint μ h01 hab hμ, mul_one] at hmul
  rw [hmul, μ.toVectorMeasure.empty]

end Limit

end WOTSpectralMeasure

section ScalarOperator

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

open scoped InnerProductSpace

/-- **Schur's-lemma capstone.** If every Borel spectral projection of a bounded self-adjoint
operator `S` is trivial (`0` or `1`), `S` is a scalar multiple of the identity — without ever
separately identifying `spectrum ℝ S`. Combined with irreducibility forcing every spectral
projection to be `0` or `1`, this finishes Schur's lemma for a Weyl-family representation. -/
theorem eq_smul_one_of_forall_spectralMeasure_eq_zero_or_one
    (S : H →L[ℂ] H) (hSA : IsSelfAdjoint S)
    (h01 : ∀ E : Set ℝ, MeasurableSet E →
      boundedSelfAdjointSpectralMeasure S hSA E = 0 ∨
        boundedSelfAdjointSpectralMeasure S hSA E = 1) :
    ∃ c : ℂ, S = c • (1 : H →L[ℂ] H) := by
  set μ := boundedSelfAdjointSpectralMeasure S hSA with hμ_def
  obtain ⟨C, hC⟩ := exists_boundedSelfAdjointSpectralSupport S hSA
  have hCicc : μ (Icc (-C) C) = 1 := by
    have hcompl : μ (Icc (-C) C)ᶜ = 0 := hC.2 _ measurableSet_Icc.compl disjoint_compl_left
    have heq := μ.toVectorMeasure.of_compl (measurableSet_Icc (a := -C) (b := C))
    rw [hcompl, μ.univ] at heq
    exact (sub_eq_zero.mp heq.symm).symm
  obtain ⟨r, hr1, hr0⟩ := WOTSpectralMeasure.exists_forall_notMem_measure_eq_zero μ h01
    (a := -C) (b := C) (by linarith [hC.1]) hCicc
  refine ⟨(r : ℂ), ?_⟩
  have hSx : ∀ x : H, S x = (r : ℂ) • x := by
    intro x
    have hkey : ∀ y : H, ⟪y, S x⟫_ℂ = (r : ℂ) * ⟪y, x⟫_ℂ := by
      intro y
      have hrecon := boundedSelfAdjointSpectralMeasure_reconstruction S hSA x y
      rw [← hrecon]
      set ν := μ.scalarMeasure x y with hν_def
      have hν0 : ∀ E : Set ℝ, MeasurableSet E → r ∉ E → ν E = 0 := by
        intro E hE hrE
        rw [hν_def, WOTSpectralMeasure.scalarMeasure_apply, hr0 E hE hrE]
        simp
      have hνr : ν {r} = ⟪y, x⟫_ℂ := by
        rw [hν_def, WOTSpectralMeasure.scalarMeasure_apply, hr1]
        simp
      have hrestr0 : ν.restrict {r}ᶜ = 0 := by
        apply MeasureTheory.VectorMeasure.ext
        intro F hF
        rw [MeasureTheory.VectorMeasure.restrict_apply _ (measurableSet_singleton r).compl hF,
          zero_apply]
        exact hν0 _ (hF.inter (measurableSet_singleton r).compl) (fun h => h.2 rfl)
      have hvar0 : ν.variation {r}ᶜ = 0 := by
        have hveq := MeasureTheory.VectorMeasure.variation_restrict
          (μ := ν) (measurableSet_singleton r).compl
        rw [hrestr0, MeasureTheory.VectorMeasure.variation_zero] at hveq
        have h2 := congrArg (fun m : MeasureTheory.Measure ℝ => m Set.univ) hveq.symm
        simpa [MeasureTheory.Measure.restrict_apply' (measurableSet_singleton r).compl] using h2
      have hae : ({r} : Set ℝ) =ᵐ[ν.variation] (Set.univ : Set ℝ) := by
        rw [Filter.eventuallyEq_set, MeasureTheory.ae_iff]
        have hset : {z : ℝ | ¬(z ∈ ({r} : Set ℝ) ↔ z ∈ (Set.univ : Set ℝ))} = {r}ᶜ := by
          ext z; simp
        rw [hset]
        exact hvar0
      have hcongr := MeasureTheory.VectorMeasure.setIntegral_congr_set
        (B := ContinuousLinearMap.lsmul ℝ ℂ) (f := fun z : ℝ => (z : ℂ)) (μ := ν)
        (measurableSet_singleton r) MeasurableSet.univ hae
      unfold WOTSpectralMeasure.complexWeakIntegral
      rw [← MeasureTheory.VectorMeasure.setIntegral_univ, ← hcongr,
        MeasureTheory.VectorMeasure.integral_singleton]
      show (ContinuousLinearMap.lsmul ℝ ℂ) (r : ℂ) (ν {r}) = (r : ℂ) * ⟪y, x⟫_ℂ
      rw [hνr]
      rfl
    have hzero : ⟪S x - (r : ℂ) • x, S x - (r : ℂ) • x⟫_ℂ = 0 := by
      have h1 := hkey (S x - (r : ℂ) • x)
      rw [inner_sub_right, inner_smul_right, h1]
      ring
    exact sub_eq_zero.mp (inner_self_eq_zero.mp hzero)
  exact ContinuousLinearMap.ext (fun x => by simpa using hSx x)

end ScalarOperator

end QuantumMechanics
