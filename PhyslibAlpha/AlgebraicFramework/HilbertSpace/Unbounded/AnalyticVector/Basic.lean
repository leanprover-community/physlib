/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Physlib.QuantumMechanics.Operators.Unbounded
public import Physlib.QuantumMechanics.Operators.SpectralTheory.Symmetric
public import Physlib.QuantumMechanics.Operators.SpectralTheory.SelfAdjoint
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.SmoothSeries
public import Mathlib.Analysis.Complex.RealDeriv
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Order.Filter.AtTopBot.Ring

/-!
# Analytic vectors for an unbounded operator (part 1 of Nelson's analytic-vector theorem)

This covers the `IsAnalyticVector`/`IteratesSeq`
definitions and the radius-controlled vector-valued exponential series `analyticExp` (summability,
derivative, algebraic comparison lemmas), together with the norm-preservation and deficiency-space
vanishing lemmas that feed the global-orbit essential-self-adjointness criterion
(`IsSymmetric.isEssentiallySelfAdjoint_of_denseEntireVectors`) — part 1 of Nelson's analytic-vector
theorem (Reed–Simon Vol. II, Thm X.39).

## Main definitions

- `IteratesSeq`, `IsAnalyticVector`, `AnalyticVectorWitness`, `IsEntireVector` : the analytic- and
  entire-vector notions for a `LinearPMap`, and the proof-relevant witness structure.
- `analyticExp` / `analyticExpTerm` : the local vector-valued exponential series built from an
  iterate witness.

## Main results

- `analyticExp_norm_eq_norm` : the local exponential orbit of a symmetric operator's analytic
  vector preserves norm.
- `IsSymmetric.isEssentiallySelfAdjoint_of_denseEntireVectors` : a dense family of entire vectors
  is sufficient for essential self-adjointness.
-/

@[expose] public section

noncomputable section

namespace LinearPMap

open scoped InnerProductSpace Topology
open Filter

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-! ## The definition -/

/-- `v` is the iterate sequence of `x` under `T`: `v 0 = x` and `v (n+1) = T (v n)`, as elements
of `T.domain` (so this packages, in particular, the assertion that `x` lies in the domain of every
power `Tⁿ`). Since `T` is single-valued, `v` is uniquely determined by `x` whenever it exists at
all. -/
def IteratesSeq (T : H →ₗ.[ℂ] H) (x : H) (v : ℕ → T.domain) : Prop :=
  (v 0 : H) = x ∧ ∀ n, (v (n + 1) : H) = T (v n)

omit [CompleteSpace H] in
@[nolint unusedArguments]
lemma IteratesSeq.ext {T : H →ₗ.[ℂ] H} {x : H} {v w : ℕ → T.domain}
    (hv : IteratesSeq T x v) (hw : IteratesSeq T x w) :
    ∀ n, (v n : H) = (w n : H) := by
  intro n
  induction n with
  | zero => exact hv.1.trans hw.1.symm
  | succ n ih =>
    calc
      (v (n + 1) : H) = T (v n) := hv.2 n
      _ = T (w n) := by
        congr 1
        exact Subtype.ext ih
      _ = (w (n + 1) : H) := (hw.2 n).symm

/-- **Analytic vector** (Reed–Simon Vol. II, §X.6). `x` is an analytic vector for `T` if it lies
in the domain of every iterated power `Tⁿ` (witnessed by an iterate sequence `v`, so `v n`
represents `Tⁿ x`) and the exponential-type series `∑ ‖Tⁿx‖ tⁿ / n!` converges for some `t > 0`. -/
def IsAnalyticVector (T : H →ₗ.[ℂ] H) (x : H) : Prop :=
  ∃ v : ℕ → T.domain, IteratesSeq T x v ∧
    ∃ t : ℝ, 0 < t ∧ Summable (fun n => ‖(v n : H)‖ * t ^ n / n.factorial)

/-- The data hidden by `IsAnalyticVector`, retained as a structure for recursive continuation.
The proposition is ideal for stating density assumptions; this structure is the corresponding
proof-relevant package needed to name the next exponential chart. -/
structure AnalyticVectorWitness (T : H →ₗ.[ℂ] H) where
  /-- The vector the witness is analytic for. -/
  state : H
  /-- The iterate sequence witnessing `Tⁿ state`. -/
  iterates : ℕ → T.domain
  iterates_spec : IteratesSeq T state iterates
  /-- The radius at which the majorant series is known to converge. -/
  radius : ℝ
  radius_pos : 0 < radius
  summable : Summable (fun n => ‖(iterates n : H)‖ * radius ^ n / n.factorial)

omit [CompleteSpace H] in
@[nolint unusedArguments]
lemma AnalyticVectorWitness.isAnalytic {T : H →ₗ.[ℂ] H} (W : AnalyticVectorWitness T) :
    T.IsAnalyticVector W.state :=
  ⟨W.iterates, W.iterates_spec, W.radius, W.radius_pos, W.summable⟩

/-- Extracts an explicit `AnalyticVectorWitness` from a proof that `x` is an analytic vector. -/
noncomputable def AnalyticVectorWitness.ofIsAnalytic
    {T : H →ₗ.[ℂ] H} {x : H} (h : T.IsAnalyticVector x) : AnalyticVectorWitness T := by
  let v : ℕ → T.domain := Classical.choose h
  have hv : IteratesSeq T x v := (Classical.choose_spec h).1
  let t : ℝ := Classical.choose (Classical.choose_spec h).2
  have ht : 0 < t := (Classical.choose_spec (Classical.choose_spec h).2).1
  have hsum : Summable (fun n : ℕ => ‖(v n : H)‖ * t ^ n / n.factorial) :=
    (Classical.choose_spec (Classical.choose_spec h).2).2
  exact ⟨x, v, hv, t, ht, hsum⟩

/-- An entire vector has an iterate witness whose factorial majorant converges at every positive
radius.  This is stronger than `IsAnalyticVector`; it is the class on which the local exponential
series can be evaluated at arbitrary real times without the global patching argument. -/
def IsEntireVector (T : H →ₗ.[ℂ] H) (x : H) : Prop :=
  ∃ v : ℕ → T.domain, IteratesSeq T x v ∧
    ∀ t : ℝ, 0 < t → Summable (fun n => ‖(v n : H)‖ * t ^ n / n.factorial)

/-! ## The local exponential series -/

/-- The `n`th term of the formal exponential orbit of an analytic vector.  The factor is written
with the `I • T` convention used by Stone's theorem: for a real time `s` it is
`(I * s)^n / n! • T^n x`.  Keeping the iterate witness explicit is useful because a
`LinearPMap` power is only defined on a nested domain. -/
def analyticExpTerm (T : H →ₗ.[ℂ] H) (v : ℕ → T.domain) (s : ℝ) (n : ℕ) : H :=
  (((Complex.I * (s : ℂ)) ^ n) / n.factorial) • (v n : H)

/-- The formal local exponential orbit associated to an iterate witness.  It is deliberately a
`tsum`, rather than a new bundled operator: convergence is supplied by
`IsAnalyticVector.summable_analyticExpTerm` below, while later Nelson/Stone developments can add
the local semigroup laws without changing this scalar-series interface. -/
def analyticExp (T : H →ₗ.[ℂ] H) (v : ℕ → T.domain) (s : ℝ) : H :=
  ∑' n, analyticExpTerm T v s n

omit [CompleteSpace H] in
lemma analyticExp_congr_iterates {T : H →ₗ.[ℂ] H} {x : H}
    {v w : ℕ → T.domain} (hv : IteratesSeq T x v) (hw : IteratesSeq T x w) (s : ℝ) :
    analyticExp T v s = analyticExp T w s := by
  unfold analyticExp
  congr 1
  funext n
  simp only [analyticExpTerm, IteratesSeq.ext hv hw n]

omit [CompleteSpace H] in
lemma norm_analyticExpTerm (T : H →ₗ.[ℂ] H) (v : ℕ → T.domain) (s : ℝ) (n : ℕ) :
    ‖analyticExpTerm T v s n‖ = ‖(v n : H)‖ * |s| ^ n / n.factorial := by
  unfold analyticExpTerm
  rw [norm_smul, norm_div, norm_pow, norm_mul, Complex.norm_I, one_mul, Complex.norm_real,
    Real.norm_eq_abs, Complex.norm_natCast]
  ring

/-- The formal derivative of an exponential-series term with respect to its real time parameter.
The `n - 1` convention makes the definition uniform at `n = 0`, where the leading factor `n`
annihilates the term. -/
def analyticExpDerivTerm (T : H →ₗ.[ℂ] H) (v : ℕ → T.domain) (s : ℝ) (n : ℕ) : H :=
  (((n : ℂ) * Complex.I * (Complex.I * (s : ℂ)) ^ (n - 1)) / n.factorial) • (v n : H)

omit [CompleteSpace H] in
lemma analyticExpTerm_hasDerivAt (T : H →ₗ.[ℂ] H) (v : ℕ → T.domain) (s : ℝ) (n : ℕ) :
    HasDerivAt (fun r : ℝ => analyticExpTerm T v r n)
      (analyticExpDerivTerm T v s n) s := by
  have hbase : HasDerivAt (fun r : ℝ => Complex.I * (r : ℂ)) Complex.I s := by
    have hreal : HasDerivAt (fun r : ℝ => (r : ℂ)) 1 s := by
      change HasDerivAt (⇑Complex.ofRealCLM) (Complex.ofRealCLM 1) s
      exact Complex.ofRealCLM.hasDerivAt
    simpa using hreal.const_mul Complex.I
  have hpow := hbase.pow n
  have hcoeff := hpow.div_const (n.factorial : ℂ)
  have hterm := HasDerivAt.smul_const hcoeff (v n : H)
  convert hterm using 1 <;> simp only [analyticExpTerm, analyticExpDerivTerm]
  · funext r
    rfl
  · ring_nf

omit [CompleteSpace H] in
lemma norm_analyticExpDerivTerm (T : H →ₗ.[ℂ] H) (v : ℕ → T.domain) (s : ℝ) (n : ℕ) :
    ‖analyticExpDerivTerm T v s n‖ =
      ‖(v n : H)‖ * n * |s| ^ (n - 1) / n.factorial := by
  unfold analyticExpDerivTerm
  simp only [norm_smul, norm_div, norm_mul, norm_pow, Complex.norm_natCast,
    Complex.norm_I, Complex.norm_real, Real.norm_eq_abs]
  ring

lemma analyticExp_hasDerivAt_of_mem_half_radius
    {T : H →ₗ.[ℂ] H} {v : ℕ → T.domain} {t s : ℝ} (ht : 0 < t)
    (hs : s ∈ Set.Ioo (-t / 2) (t / 2))
    (hsum : Summable (fun n => ‖(v n : H)‖ * t ^ n / n.factorial)) :
    HasDerivAt (fun r : ℝ => analyticExp T v r)
      (∑' n, analyticExpDerivTerm T v s n) s := by
  have ht0 : 0 ≤ t := ht.le
  have hnat : ∀ k : ℕ, (k + 1 : ℝ) ≤ (2 : ℝ) ^ (k + 1) := by
    intro k
    induction k with
    | zero => norm_num
    | succ k ih =>
      calc
        (↑(Nat.succ k) + 1 : ℝ) = (k + 1 + 1 : ℝ) := by norm_num
        _ ≤ 2 * (k + 1 : ℝ) := by
          have hk : (0 : ℝ) ≤ k := by positivity
          linarith
        _ ≤ 2 * (2 : ℝ) ^ (k + 1) := by gcongr
        _ = (2 : ℝ) ^ (k + 2) := by ring
  have hderiv_bound : ∀ (n : ℕ) (y : ℝ), y ∈ Set.Ioo (-t / 2) (t / 2) →
      ‖analyticExpDerivTerm T v y n‖ ≤
        (2 / t) * (‖(v n : H)‖ * t ^ n / n.factorial) := by
    intro n y hy
    rw [norm_analyticExpDerivTerm]
    have hyabs : |y| ≤ t / 2 := by
      rw [abs_le]
      constructor <;> linarith [hy.1, hy.2]
    cases n with
    | zero => simp; positivity
    | succ k =>
      have hkpow : |y| ^ k ≤ (t / 2) ^ k :=
        pow_le_pow_left₀ (abs_nonneg y) hyabs k
      have hmain : (k + 1 : ℝ) * |y| ^ k ≤ 2 * t ^ k := by
        calc
          (k + 1 : ℝ) * |y| ^ k ≤ (k + 1 : ℝ) * (t / 2) ^ k := by gcongr
          _ ≤ (2 : ℝ) ^ (k + 1) * (t / 2) ^ k := by
            exact mul_le_mul_of_nonneg_right (hnat k) (by positivity)
          _ = 2 * t ^ k := by
            rw [div_pow]
            field_simp
            ring
      have hfac : 0 ≤ ‖(v (Nat.succ k) : H)‖ / (Nat.succ k).factorial := by positivity
      calc
        ‖(v (Nat.succ k) : H)‖ * ↑(Nat.succ k) * |y| ^ k / (Nat.succ k).factorial
            = (‖(v (Nat.succ k) : H)‖ / (Nat.succ k).factorial) *
                ((k + 1 : ℝ) * |y| ^ k) := by
          simp only [Nat.cast_succ]
          ring
        _ ≤ (‖(v (Nat.succ k) : H)‖ / (Nat.succ k).factorial) * (2 * t ^ k) := by
          gcongr
        _ = (2 / t) *
            (‖(v (Nat.succ k) : H)‖ * t ^ (Nat.succ k) / (Nat.succ k).factorial) := by
          field_simp
          rw [pow_succ]
          ring
  have hu : Summable (fun n => (2 / t) * (‖(v n : H)‖ * t ^ n / n.factorial)) :=
    hsum.mul_left (2 / t)
  have hzero : (0 : ℝ) ∈ Set.Ioo (-t / 2) (t / 2) := by
    constructor <;> linarith
  have hsum_zero : Summable (fun n => analyticExpTerm T v 0 n) := by
    apply Summable.of_norm_bounded hsum
    intro n
    rw [norm_analyticExpTerm]
    by_cases hn : n = 0
    · simp [hn]
    · simp [hn]
      positivity
  exact hasDerivAt_tsum_of_isPreconnected hu isOpen_Ioo isPreconnected_Ioo
    (fun n y hy => analyticExpTerm_hasDerivAt T v y n)
    (fun n y hy => hderiv_bound n y hy) hzero hsum_zero hs

set_option linter.unusedTactic false in
lemma analyticExp_hasDerivAt_zero {T : H →ₗ.[ℂ] H} {x : H} {v : ℕ → T.domain}
    (hv : IteratesSeq T x v) {t : ℝ} (ht : 0 < t)
    (hsum : Summable (fun n => ‖(v n : H)‖ * t ^ n / n.factorial)) :
    HasDerivAt (fun s : ℝ => analyticExp T v s) (Complex.I • T (v 0)) 0 := by
  have hlocal := analyticExp_hasDerivAt_of_mem_half_radius (T := T) (v := v) ht
    (by
      change (0 : ℝ) ∈ Set.Ioo (-t / 2) (t / 2)
      constructor <;> linarith [ht]) hsum
  have hsum_deriv : (∑' n, analyticExpDerivTerm T v 0 n) = Complex.I • T (v 0) := by
    rw [tsum_eq_single 1]
    · simpa [analyticExpDerivTerm] using congrArg (fun z : H => Complex.I • z) (hv.2 0)
    · intro n hn
      cases n with
      | zero => simp [analyticExpDerivTerm]
      | succ n =>
        cases n with
        | zero => exact (hn rfl).elim
        | succ n => simp [analyticExpDerivTerm]
  rw [hsum_deriv] at hlocal
  exact hlocal

lemma summable_analyticExpDerivTerm_of_mem_half_radius
    {T : H →ₗ.[ℂ] H} {v : ℕ → T.domain} {t s : ℝ} (ht : 0 < t)
    (hs : s ∈ Set.Ioo (-t / 2) (t / 2))
    (hsum : Summable (fun n => ‖(v n : H)‖ * t ^ n / n.factorial)) :
    Summable (fun n => analyticExpDerivTerm T v s n) := by
  have hnat : ∀ k : ℕ, (k + 1 : ℝ) ≤ (2 : ℝ) ^ (k + 1) := by
    intro k
    induction k with
    | zero => norm_num
    | succ k ih =>
      calc
        (↑(Nat.succ k) + 1 : ℝ) = (k + 1 + 1 : ℝ) := by norm_num
        _ ≤ 2 * (k + 1 : ℝ) := by
          have hk : (0 : ℝ) ≤ k := by positivity
          linarith
        _ ≤ 2 * (2 : ℝ) ^ (k + 1) := by gcongr
        _ = (2 : ℝ) ^ (k + 2) := by ring
  have hbound : ∀ (n : ℕ),
      ‖analyticExpDerivTerm T v s n‖ ≤
        (2 / t) * (‖(v n : H)‖ * t ^ n / n.factorial) := by
    intro n
    rw [norm_analyticExpDerivTerm]
    cases n with
    | zero => simp; positivity
    | succ k =>
      have hyabs : |s| ≤ t / 2 := by
        rw [abs_le]
        constructor <;> linarith [hs.1, hs.2]
      have hkpow : |s| ^ k ≤ (t / 2) ^ k :=
        pow_le_pow_left₀ (abs_nonneg s) hyabs k
      have hmain : (k + 1 : ℝ) * |s| ^ k ≤ 2 * t ^ k := by
        calc
          (k + 1 : ℝ) * |s| ^ k ≤ (k + 1 : ℝ) * (t / 2) ^ k := by gcongr
          _ ≤ (2 : ℝ) ^ (k + 1) * (t / 2) ^ k := by
            exact mul_le_mul_of_nonneg_right (hnat k) (by positivity)
          _ = 2 * t ^ k := by
            rw [div_pow]
            field_simp
            ring
      calc
        ‖(v (Nat.succ k) : H)‖ * ↑(Nat.succ k) * |s| ^ k /
              (Nat.succ k).factorial
            = (‖(v (Nat.succ k) : H)‖ / (Nat.succ k).factorial) *
                ((k + 1 : ℝ) * |s| ^ k) := by
          simp only [Nat.cast_succ]
          ring
        _ ≤ (‖(v (Nat.succ k) : H)‖ / (Nat.succ k).factorial) *
              (2 * t ^ k) := by gcongr
        _ = (2 / t) *
            (‖(v (Nat.succ k) : H)‖ * t ^ (Nat.succ k) /
              (Nat.succ k).factorial) := by
          field_simp
          rw [pow_succ]
          ring
  exact Summable.of_norm_bounded (hsum.mul_left (2 / t)) hbound

lemma analyticExp_mem_closure_graph
    {T : H →ₗ.[ℂ] H} {x : H} {v : ℕ → T.domain} (hv : IteratesSeq T x v)
    {t s : ℝ} (hT : T.IsClosable)
    (hs : s ∈ Set.Ioo (-t / 2) (t / 2))
    (hsum : Summable (fun n => ‖(v n : H)‖ * t ^ n / n.factorial)) :
    (analyticExp T v s, (-Complex.I) • (∑' n, analyticExpDerivTerm T v s n)) ∈
      T.closure.graph := by
  have hexp : Summable (fun n => analyticExpTerm T v s n) := by
    apply Summable.of_norm_bounded hsum
    intro n
    rw [norm_analyticExpTerm]
    have ht : 0 ≤ t := le_of_lt (by linarith [hs.2, hs.1])
    have hsabs : |s| ≤ t := by
      rw [abs_le]
      constructor <;> linarith [hs.1, hs.2]
    have hpow : |s| ^ n ≤ t ^ n := pow_le_pow_left₀ (abs_nonneg s) hsabs n
    have hnonneg : 0 ≤ ‖(v n : H)‖ / n.factorial := by positivity
    calc
      ‖(v n : H)‖ * |s| ^ n / n.factorial
          = (‖(v n : H)‖ / n.factorial) * |s| ^ n := by ring
      _ ≤ (‖(v n : H)‖ / n.factorial) * t ^ n := by gcongr
      _ = ‖(v n : H)‖ * t ^ n / n.factorial := by ring
  have hderiv := summable_analyticExpDerivTerm_of_mem_half_radius
    (T := T) (v := v) (by linarith [hs.2, hs.1]) hs hsum
  let p : ℕ → T.domain := fun N => ∑ n ∈ Finset.range N,
    (((Complex.I * (s : ℂ)) ^ n) / n.factorial) • v n
  let q : ℕ → H := fun N => T (p N)
  have hp : Filter.Tendsto (fun N => (p N : H)) Filter.atTop (𝓝 (analyticExp T v s)) := by
    simpa [p, analyticExp, analyticExpTerm] using (hexp.hasSum.tendsto_sum_nat)
  have hq_eq : ∀ N, q N = (-Complex.I) •
      (∑ n ∈ Finset.range (N + 1), analyticExpDerivTerm T v s n) := by
    intro N
    have hterm : ∀ n : ℕ,
        T ((((Complex.I * (s : ℂ)) ^ n) / n.factorial) • v n) =
          (-Complex.I) • analyticExpDerivTerm T v s (n + 1) := by
      intro n
      rw [map_smul, ← hv.2 n]
      simp [analyticExpDerivTerm, Nat.factorial_succ, smul_smul]
      field_simp
      ring_nf
      rw [Complex.I_sq]
      simp
    induction N with
    | zero => simp [q, p, analyticExpDerivTerm]
    | succ N ih =>
      change T (∑ n ∈ Finset.range (N + 1),
        (((Complex.I * (s : ℂ)) ^ n) / n.factorial) • v n) = _
      rw [Finset.sum_range_succ, map_add]
      rw [show T (∑ n ∈ Finset.range N,
          (((Complex.I * (s : ℂ)) ^ n) / n.factorial) • v n) = q N by rfl]
      rw [ih]
      rw [hterm N]
      rw [← smul_add]
      congr 1
      rw [show N + (1 + 1) = (N + 1) + 1 by omega]
      rw [Finset.sum_range_succ]
      rw [Finset.sum_range_succ]
      rw [Finset.sum_range_succ]
  have hq : Filter.Tendsto q Filter.atTop (𝓝 ((-Complex.I) • (∑' n,
      analyticExpDerivTerm T v s n))) := by
    have hd := hderiv.hasSum.tendsto_sum_nat
    have hshift := hd.comp (Filter.tendsto_add_atTop_nat 1)
    have hshift' := hshift.const_smul (-Complex.I)
    exact hshift'.congr' (Filter.Eventually.of_forall fun N => (hq_eq N).symm)
  change (analyticExp T v s, (-Complex.I) • (∑' n, analyticExpDerivTerm T v s n)) ∈
    T.closure.graph
  rw [← hT.graph_closure_eq_closure_graph]
  apply mem_closure_iff_seq_limit.mpr
  refine ⟨fun N => ((p N : H), q N), ?_, ?_⟩
  · exact fun N => T.mem_graph (p N)
  · rw [nhds_prod_eq]
    exact hp.prodMk hq

lemma analyticExp_mem_closure_domain
    {T : H →ₗ.[ℂ] H} {x : H} {v : ℕ → T.domain} (hv : IteratesSeq T x v)
    {t s : ℝ} (hT : T.IsClosable)
    (hs : s ∈ Set.Ioo (-t / 2) (t / 2))
    (hsum : Summable (fun n => ‖(v n : H)‖ * t ^ n / n.factorial)) :
    analyticExp T v s ∈ T.closure.domain :=
  mem_domain_of_mem_graph (analyticExp_mem_closure_graph hv hT hs hsum)

lemma closure_analyticExp_apply
    {T : H →ₗ.[ℂ] H} {x : H} {v : ℕ → T.domain} (hv : IteratesSeq T x v)
    {t s : ℝ} (hT : T.IsClosable)
    (hs : s ∈ Set.Ioo (-t / 2) (t / 2))
    (hsum : Summable (fun n => ‖(v n : H)‖ * t ^ n / n.factorial)) :
    T.closure ⟨analyticExp T v s, analyticExp_mem_closure_domain hv hT hs hsum⟩ =
      (-Complex.I) • (∑' n, analyticExpDerivTerm T v s n) := by
  apply T.closure.mem_graph_snd_inj'
    (T.closure.mem_graph ⟨analyticExp T v s, analyticExp_mem_closure_domain hv hT hs hsum⟩)
    (analyticExp_mem_closure_graph hv hT hs hsum)
  rfl

lemma analyticExp_hasDerivAt_eq_smul_closure
    {T : H →ₗ.[ℂ] H} {x : H} {v : ℕ → T.domain} (hv : IteratesSeq T x v)
    {t s : ℝ} (hT : T.IsClosable)
    (hs : s ∈ Set.Ioo (-t / 2) (t / 2))
    (hsum : Summable (fun n => ‖(v n : H)‖ * t ^ n / n.factorial)) :
    HasDerivAt (fun r : ℝ => analyticExp T v r)
      (Complex.I • T.closure ⟨analyticExp T v s,
        analyticExp_mem_closure_domain hv hT hs hsum⟩) s := by
  have h := analyticExp_hasDerivAt_of_mem_half_radius
    (T := T) (v := v) (by linarith [hs.2, hs.1]) hs hsum
  convert h using 1
  rw [closure_analyticExp_apply hv hT hs hsum]
  simp [smul_smul]

omit [CompleteSpace H] in
@[nolint unusedArguments]
lemma IsSymmetric.re_inner_smul_I_apply_self
    {T : H →ₗ.[ℂ] H} (hT : T.IsSymmetric) (x : T.domain) :
    (⟪(x : H), Complex.I • T x⟫_ℂ).re = 0 := by
  have hreal := (isSymmetric_iff_inner_map_self_real.mp hT x)
  have hxy : ⟪(x : H), T x⟫_ℂ = ⟪T x, (x : H)⟫_ℂ := by
    calc
      ⟪(x : H), T x⟫_ℂ = (starRingEnd ℂ) ⟪T x, (x : H)⟫_ℂ :=
        (inner_conj_symm (x : H) (T x)).symm
      _ = ⟪T x, (x : H)⟫_ℂ := hreal
  have hconj : (starRingEnd ℂ) ⟪(x : H), T x⟫_ℂ = ⟪(x : H), T x⟫_ℂ := by
    calc
      (starRingEnd ℂ) ⟪(x : H), T x⟫_ℂ =
          (starRingEnd ℂ) ⟪T x, (x : H)⟫_ℂ := congrArg (starRingEnd ℂ) hxy
      _ = ⟪T x, (x : H)⟫_ℂ := hreal
      _ = ⟪(x : H), T x⟫_ℂ := hxy.symm
  have him : (⟪(x : H), T x⟫_ℂ).im = 0 := by
    have him' := congrArg Complex.im hconj
    rw [Complex.conj_im] at him'
    linarith
  rw [inner_smul_right]
  simp [Complex.I_mul, him]

lemma analyticExp_normSq_hasDerivAt_eq_zero
    {T : H →ₗ.[ℂ] H} (hsym : T.IsSymmetric)
    (hdense : (Submodule.span ℂ {x : H | T.IsAnalyticVector x}).topologicalClosure = ⊤)
    {x : H} {v : ℕ → T.domain} (hv : IteratesSeq T x v)
    {t s : ℝ} (hs : s ∈ Set.Ioo (-t / 2) (t / 2))
    (hsum : Summable (fun n => ‖(v n : H)‖ * t ^ n / n.factorial)) :
    HasDerivAt (fun r : ℝ => ‖analyticExp T v r‖ ^ 2) 0 s := by
  have hspan : Dense (Submodule.span ℂ {x : H | T.IsAnalyticVector x} : Set H) := by
    rw [dense_iff_closure_eq]
    rw [← Submodule.topologicalClosure_coe]
    exact congrArg (fun s : Submodule ℂ H => (s : Set H)) hdense
  have hdomain : (Submodule.span ℂ {x : H | T.IsAnalyticVector x}) ≤ T.domain := by
    refine Submodule.span_le.2 (fun y hy => ?_)
    obtain ⟨w, ⟨hw0, -⟩, -⟩ := hy
    exact hw0 ▸ (w 0).2
  have hTdense : T.HasDenseDomain := hspan.mono hdomain
  have hclosure_symm : T.closure.IsSymmetric := hsym.closure hTdense
  let _ : InnerProductSpace ℝ H := InnerProductSpace.rclikeToReal ℂ H
  have hlocal := analyticExp_hasDerivAt_eq_smul_closure hv
    (hsym.isClosable hTdense) hs hsum
  have hnorm : HasDerivAt (fun r : ℝ => ‖analyticExp T v r‖ ^ 2)
      (2 * ⟪analyticExp T v s,
        Complex.I • T.closure ⟨analyticExp T v s,
          analyticExp_mem_closure_domain hv (hsym.isClosable hTdense) hs hsum⟩⟫_ℝ) s := by
      simpa [ContinuousLinearMap.toSpanSingleton_apply] using
        hlocal.hasFDerivAt.norm_sq.hasDerivAt
  have hzero :
      (2 : ℝ) * (⟪analyticExp T v s,
        Complex.I • T.closure ⟨analyticExp T v s,
          analyticExp_mem_closure_domain hv (hsym.isClosable hTdense) hs hsum⟩⟫_ℂ).re = 0 := by
    have hinner := hclosure_symm.re_inner_smul_I_apply_self
      ⟨analyticExp T v s,
        analyticExp_mem_closure_domain hv (hsym.isClosable hTdense) hs hsum⟩
    simp [hinner]
  convert hnorm using 1
  simpa [real_inner_eq_re_inner] using hzero.symm

lemma analyticExp_normSq_eq_normSq_zero
    {T : H →ₗ.[ℂ] H} (hsym : T.IsSymmetric)
    (hdense : (Submodule.span ℂ {x : H | T.IsAnalyticVector x}).topologicalClosure = ⊤)
    {x : H} {v : ℕ → T.domain} (hv : IteratesSeq T x v)
    {t s : ℝ} (hs : s ∈ Set.Ioo (-t / 2) (t / 2))
    (hsum : Summable (fun n => ‖(v n : H)‖ * t ^ n / n.factorial)) :
    ‖analyticExp T v s‖ ^ 2 = ‖x‖ ^ 2 := by
  have ht : 0 < t := by linarith [hs.2, hs.1]
  have hconst : ∀ {r u : ℝ}, r ∈ Set.Ioo (-t / 2) (t / 2) →
      u ∈ Set.Ioo (-t / 2) (t / 2) →
      ‖analyticExp T v r‖ ^ 2 = ‖analyticExp T v u‖ ^ 2 := by
    intro r u hr hu
    refine isOpen_Ioo.is_const_of_deriv_eq_zero
      (s := Set.Ioo (-t / 2) (t / 2)) (f := fun y : ℝ => ‖analyticExp T v y‖ ^ 2)
      (isPreconnected_Ioo (a := -t / 2) (b := t / 2)) ?_ ?_ hr hu
    · intro y hy
      exact (analyticExp_normSq_hasDerivAt_eq_zero hsym hdense hv hy
          hsum).differentiableAt.differentiableWithinAt
    · intro y hy
      exact (analyticExp_normSq_hasDerivAt_eq_zero hsym hdense hv hy hsum).deriv
  have hzero : (0 : ℝ) ∈ Set.Ioo (-t / 2) (t / 2) := by
    constructor <;> linarith
  rw [hconst hs hzero]
  rw [analyticExp, tsum_eq_single 0]
  · simp [analyticExpTerm, hv.1]
  · intro n hn
    simp [analyticExpTerm, hn]

lemma analyticExp_norm_eq_norm
    {T : H →ₗ.[ℂ] H} (hsym : T.IsSymmetric)
    (hdense : (Submodule.span ℂ {x : H | T.IsAnalyticVector x}).topologicalClosure = ⊤)
    {x : H} {v : ℕ → T.domain} (hv : IteratesSeq T x v)
    {t s : ℝ} (hs : s ∈ Set.Ioo (-t / 2) (t / 2))
    (hsum : Summable (fun n => ‖(v n : H)‖ * t ^ n / n.factorial)) :
    ‖analyticExp T v s‖ = ‖x‖ := by
  have hsq := analyticExp_normSq_eq_normSq_zero hsym hdense hv hs hsum
  nlinarith [norm_nonneg (analyticExp T v s), norm_nonneg x]

lemma analyticExp_eq_zero_iff
    {T : H →ₗ.[ℂ] H} (hsym : T.IsSymmetric)
    (hdense : (Submodule.span ℂ {x : H | T.IsAnalyticVector x}).topologicalClosure = ⊤)
    {x : H} {v : ℕ → T.domain} (hv : IteratesSeq T x v)
    {t s : ℝ} (hs : s ∈ Set.Ioo (-t / 2) (t / 2))
    (hsum : Summable (fun n => ‖(v n : H)‖ * t ^ n / n.factorial)) :
    analyticExp T v s = 0 ↔ x = 0 := by
  rw [← norm_eq_zero]
  rw [analyticExp_norm_eq_norm hsym hdense hv hs hsum]
  exact norm_eq_zero

omit [CompleteSpace H] in
@[nolint unusedArguments]
lemma IsEntireVector.isAnalyticVector
    {T : H →ₗ.[ℂ] H} {x : H} (h : T.IsEntireVector x) : T.IsAnalyticVector x := by
  obtain ⟨v, hv, hall⟩ := h
  exact ⟨v, hv, 1, one_pos, hall 1 one_pos⟩

lemma analyticExp_mem_closure_domain_of_entire
    {T : H →ₗ.[ℂ] H} {x : H} {v : ℕ → T.domain} (hv : IteratesSeq T x v)
    (hall : ∀ t : ℝ, 0 < t → Summable (fun n => ‖(v n : H)‖ * t ^ n / n.factorial))
    (hT : T.IsClosable) (s : ℝ) :
    analyticExp T v s ∈ T.closure.domain := by
  let t : ℝ := 2 * |s| + 1
  have ht : 0 < t := by
    dsimp [t]
    positivity
  have hs : s ∈ Set.Ioo (-t / 2) (t / 2) := by
    dsimp [t]
    constructor <;> linarith [neg_le_abs s, le_abs_self s]
  exact analyticExp_mem_closure_domain hv hT hs (hall t ht)

lemma IsEntireVector.analyticExp_mem_closure_domain
    {T : H →ₗ.[ℂ] H} {x : H} (h : T.IsEntireVector x)
    (hT : T.IsClosable) (s : ℝ) :
    ∃ v : ℕ → T.domain, IteratesSeq T x v ∧
      analyticExp T v s ∈ T.closure.domain := by
  obtain ⟨v, hv, hall⟩ := h
  let t : ℝ := 2 * |s| + 1
  have ht : 0 < t := by
    dsimp [t]
    positivity
  have hs : s ∈ Set.Ioo (-t / 2) (t / 2) := by
    dsimp [t]
    constructor <;> linarith [neg_le_abs s, le_abs_self s]
  exact ⟨v, hv, analyticExp_mem_closure_domain_of_entire hv hall hT s⟩

lemma IsEntireVector.analyticExp_norm_eq_norm
    {T : H →ₗ.[ℂ] H} {x : H} (h : T.IsEntireVector x)
    (hsym : T.IsSymmetric)
    (hdense : (Submodule.span ℂ {x : H | T.IsAnalyticVector x}).topologicalClosure = ⊤)
    (s : ℝ) :
    ∃ v : ℕ → T.domain, IteratesSeq T x v ∧ ‖analyticExp T v s‖ = ‖x‖ := by
  obtain ⟨v, hv, hall⟩ := h
  let t : ℝ := 2 * |s| + 1
  have ht : 0 < t := by
    dsimp [t]
    positivity
  have hs : s ∈ Set.Ioo (-t / 2) (t / 2) := by
    dsimp [t]
    constructor <;> linarith [neg_le_abs s, le_abs_self s]
  exact ⟨v, hv, LinearPMap.analyticExp_norm_eq_norm hsym hdense hv hs (hall t ht)⟩

lemma analyticExp_hasDerivAt_of_entire
    {T : H →ₗ.[ℂ] H} {x : H} {v : ℕ → T.domain} (hv : IteratesSeq T x v)
    (hall : ∀ t : ℝ, 0 < t → Summable (fun n => ‖(v n : H)‖ * t ^ n / n.factorial))
    (hT : T.IsClosable) (s : ℝ) :
    HasDerivAt (fun r : ℝ => analyticExp T v r)
      (Complex.I • T.closure ⟨analyticExp T v s,
        analyticExp_mem_closure_domain_of_entire hv hall hT s⟩) s := by
  let t : ℝ := 2 * |s| + 1
  have ht : 0 < t := by
    dsimp [t]
    positivity
  have hs : s ∈ Set.Ioo (-t / 2) (t / 2) := by
    dsimp [t]
    constructor <;> linarith [neg_le_abs s, le_abs_self s]
  exact analyticExp_hasDerivAt_eq_smul_closure hv hT hs (hall t ht)

lemma analyticExp_inner_deficiency_hasDerivAt
    {T : H →ₗ.[ℂ] H} {x : H} {v : ℕ → T.domain} (hv : IteratesSeq T x v)
    (hall : ∀ t : ℝ, 0 < t → Summable (fun n => ‖(v n : H)‖ * t ^ n / n.factorial))
    (hT : T.IsClosable) {y : H}
    (hy : y ∈ (T.closure - Complex.I • 1).toFun.rangeᗮ) (s : ℝ) :
    HasDerivAt (fun r : ℝ => ⟪y, analyticExp T v r⟫_ℂ)
      (-⟪y, analyticExp T v s⟫_ℂ) s := by
  have hdom : analyticExp T v s ∈ T.closure.domain :=
    analyticExp_mem_closure_domain_of_entire hv hall hT s
  have hderiv := analyticExp_hasDerivAt_of_entire hv hall hT s
  let z : (T.closure - Complex.I • 1).domain :=
    ⟨analyticExp T v s, by
      rw [sub_domain]
      exact ⟨hdom, by simp⟩⟩
  have horth : ⟪y, T.closure ⟨analyticExp T v s, hdom⟩ -
      Complex.I • (analyticExp T v s)⟫_ℂ = 0 := by
    have hz := (Submodule.mem_orthogonal' _ y).mp hy ((T.closure - Complex.I • 1).toFun z)
      ⟨z, rfl⟩
    simpa [z, sub_apply] using hz
  have hrelation : ⟪y, T.closure ⟨analyticExp T v s, hdom⟩⟫_ℂ =
      Complex.I * ⟪y, analyticExp T v s⟫_ℂ := by
    rw [inner_sub_right, inner_smul_right] at horth
    exact sub_eq_zero.mp horth
  have hinner := (hasDerivAt_const (x := s) y).inner ℂ hderiv
  convert hinner using 1
  · rfl
  · simp only [inner_zero_left, inner_smul_right]
    rw [hrelation]
    ring_nf
    rw [Complex.I_sq]
    simp

lemma analyticExp_inner_deficiency_eq_zero
    {T : H →ₗ.[ℂ] H} (hsym : T.IsSymmetric)
    (hdense : (Submodule.span ℂ {x : H | T.IsAnalyticVector x}).topologicalClosure = ⊤)
    {x : H} {v : ℕ → T.domain} (hv : IteratesSeq T x v)
    (hall : ∀ t : ℝ, 0 < t → Summable (fun n => ‖(v n : H)‖ * t ^ n / n.factorial))
    (hT : T.IsClosable) {y : H}
    (hy : y ∈ (T.closure - Complex.I • 1).toFun.rangeᗮ) :
    ⟪y, x⟫_ℂ = 0 := by
  let _ : InnerProductSpace ℝ H := InnerProductSpace.rclikeToReal ℂ H
  let f : ℝ → ℂ := fun s => ⟪y, analyticExp T v s⟫_ℂ
  let g : ℝ → ℂ := fun s => (Real.exp s : ℂ) * f s
  have hg : ∀ s : ℝ, HasDerivAt g 0 s := by
    intro s
    have he : HasDerivAt (fun r : ℝ => (Real.exp r : ℂ)) (Real.exp s) s :=
      (Real.hasDerivAt_exp s).ofReal_comp
    have hf : HasDerivAt f (-f s) s := by
      simpa [f] using analyticExp_inner_deficiency_hasDerivAt hv hall hT hy s
    have hp := he.mul hf
    have hz : (Real.exp s : ℂ) * f s + (Real.exp s : ℂ) * (-f s) = 0 := by
      ring
    have hp' : HasDerivAt ((fun r : ℝ => (Real.exp r : ℂ)) * f) 0 s := by
      simpa only [hz] using hp
    change HasDerivAt (fun r : ℝ => (Real.exp r : ℂ) * f r) 0 s
    convert hp' using 1
    funext r
    rfl
  have hconst : ∀ s : ℝ, g s = g 0 := by
    intro s
    exact is_const_of_deriv_eq_zero (fun r => (hg r).differentiableAt)
      (fun r => (hg r).deriv) s 0
  have hexp : Filter.Tendsto (fun n : ℕ => Real.exp (-(n : ℝ))) atTop (𝓝 0) := by
    simpa [Function.comp_def] using
      Real.tendsto_exp_atBot.comp
        (tendsto_neg_atTop_atBot.comp (tendsto_natCast_atTop_atTop :
          Filter.Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop))
  have hupper : Filter.Tendsto
      (fun n : ℕ => Real.exp (-(n : ℝ)) * (‖y‖ * ‖x‖)) atTop (𝓝 0) := by
    simpa only [Pi.mul_apply, zero_mul] using
      hexp.mul (tendsto_const_nhds :
        Filter.Tendsto (fun _ : ℕ => ‖y‖ * ‖x‖) atTop (𝓝 (‖y‖ * ‖x‖)))
  have hnorm_lim : Filter.Tendsto (fun n : ℕ => ‖g (-(n : ℝ))‖) atTop (𝓝 0) := by
    refine squeeze_zero' (f := fun n : ℕ => ‖g (-(n : ℝ))‖)
      (g := fun n : ℕ => Real.exp (-(n : ℝ)) * (‖y‖ * ‖x‖))
      (Filter.Eventually.of_forall fun n => norm_nonneg _)
      (Filter.Eventually.of_forall (fun n => ?_)) hupper
    calc
      ‖g (-(n : ℝ))‖ = Real.exp (-(n : ℝ)) *
          ‖⟪y, analyticExp T v (-(n : ℝ))⟫_ℂ‖ := by
            dsimp [g, f]
            rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
              abs_of_pos (Real.exp_pos _)]
      _ ≤ Real.exp (-(n : ℝ)) *
          (‖y‖ * ‖analyticExp T v (-(n : ℝ))‖) := by
            gcongr
            exact norm_inner_le_norm _ _
      _ = Real.exp (-(n : ℝ)) * (‖y‖ * ‖x‖) := by
        have hnorm : ‖analyticExp T v (-(n : ℝ))‖ = ‖x‖ := by
          obtain ⟨w, hw, heq⟩ := IsEntireVector.analyticExp_norm_eq_norm
            ⟨v, hv, hall⟩ hsym hdense (-(n : ℝ))
          rw [analyticExp_congr_iterates hv hw, heq]
        rw [hnorm]
  have hlim : Filter.Tendsto (fun n : ℕ => g (-(n : ℝ))) atTop (𝓝 0) :=
    (tendsto_zero_iff_norm_tendsto_zero).2 hnorm_lim
  have hconst_zero : g 0 = 0 := by
    have hc : Tendsto (fun _ : ℕ => g 0) atTop (𝓝 0) :=
      hlim.congr' (Filter.Eventually.of_forall fun n => hconst (-(n : ℝ)))
    exact (tendsto_nhds_unique hc tendsto_const_nhds).symm
  have hexp_zero : analyticExp T v 0 = x := by
    rw [analyticExp, tsum_eq_single 0]
    · simpa [analyticExpTerm] using hv.1
    · intro n hn
      simp [analyticExpTerm, hn]
  simpa [g, f, hexp_zero] using hconst_zero

lemma analyticExp_inner_deficiency_hasDerivAt_neg
    {T : H →ₗ.[ℂ] H} {x : H} {v : ℕ → T.domain} (hv : IteratesSeq T x v)
    (hall : ∀ t : ℝ, 0 < t → Summable (fun n => ‖(v n : H)‖ * t ^ n / n.factorial))
    (hT : T.IsClosable) {y : H}
    (hy : y ∈ (T.closure - (-Complex.I) • 1).toFun.rangeᗮ) (s : ℝ) :
    HasDerivAt (fun r : ℝ => ⟪y, analyticExp T v r⟫_ℂ)
      (⟪y, analyticExp T v s⟫_ℂ) s := by
  have hdom : analyticExp T v s ∈ T.closure.domain :=
    analyticExp_mem_closure_domain_of_entire hv hall hT s
  have hderiv := analyticExp_hasDerivAt_of_entire hv hall hT s
  let z : (T.closure - (-Complex.I) • 1).domain :=
    ⟨analyticExp T v s, by
      rw [sub_domain]
      exact ⟨hdom, by simp⟩⟩
  have horth : ⟪y, T.closure ⟨analyticExp T v s, hdom⟩ -
      (-Complex.I) • (analyticExp T v s)⟫_ℂ = 0 := by
    have hz := (Submodule.mem_orthogonal' _ y).mp hy ((T.closure - (-Complex.I) • 1).toFun z)
      ⟨z, rfl⟩
    simpa [z, sub_apply] using hz
  have hrelation : ⟪y, T.closure ⟨analyticExp T v s, hdom⟩⟫_ℂ =
      (-Complex.I) * ⟪y, analyticExp T v s⟫_ℂ := by
    rw [inner_sub_right, inner_smul_right] at horth
    exact sub_eq_zero.mp horth
  let _ : InnerProductSpace ℝ H := InnerProductSpace.rclikeToReal ℂ H
  have hinner := (hasDerivAt_const (x := s) y).inner ℂ hderiv
  convert hinner using 1
  · rfl
  · simp only [inner_zero_left, inner_smul_right]
    rw [hrelation]
    ring_nf
    rw [Complex.I_sq]
    simp

lemma analyticExp_inner_deficiency_eq_zero_neg
    {T : H →ₗ.[ℂ] H} (hsym : T.IsSymmetric)
    (hdense : (Submodule.span ℂ {x : H | T.IsAnalyticVector x}).topologicalClosure = ⊤)
    {x : H} {v : ℕ → T.domain} (hv : IteratesSeq T x v)
    (hall : ∀ t : ℝ, 0 < t → Summable (fun n => ‖(v n : H)‖ * t ^ n / n.factorial))
    (hT : T.IsClosable) {y : H}
    (hy : y ∈ (T.closure - (-Complex.I) • 1).toFun.rangeᗮ) :
    ⟪y, x⟫_ℂ = 0 := by
  let f : ℝ → ℂ := fun s => ⟪y, analyticExp T v s⟫_ℂ
  let g : ℝ → ℂ := fun s => (Real.exp (-s) : ℂ) * f s
  have hg : ∀ s : ℝ, HasDerivAt g 0 s := by
    intro s
    have he : HasDerivAt (fun r : ℝ => (Real.exp (-r) : ℂ))
        (-Real.exp (-s)) s := by
      have hreal := (Real.hasDerivAt_exp (-s)).scomp s
        (hasDerivAt_id' (𝕜 := ℝ) s).neg
      convert hreal.ofReal_comp using 1
      · funext r
        rfl
      · simp
    have hf : HasDerivAt f (f s) s := by
      simpa [f] using analyticExp_inner_deficiency_hasDerivAt_neg hv hall hT hy s
    have hp := he.mul hf
    have hz : (-Real.exp (-s) : ℂ) * f s + (Real.exp (-s) : ℂ) * f s = 0 := by
      ring
    have hp' : HasDerivAt ((fun r : ℝ => (Real.exp (-r) : ℂ)) * f) 0 s := by
      simpa only [hz] using hp
    change HasDerivAt (fun r : ℝ => (Real.exp (-r) : ℂ) * f r) 0 s
    convert hp' using 1
    funext r
    rfl
  have hconst : ∀ s : ℝ, g s = g 0 := by
    intro s
    exact is_const_of_deriv_eq_zero (fun r => (hg r).differentiableAt)
      (fun r => (hg r).deriv) s 0
  have hexp : Filter.Tendsto (fun n : ℕ => Real.exp (-(n : ℝ))) atTop (𝓝 0) := by
    simpa [Function.comp_def] using
      Real.tendsto_exp_atBot.comp
        (tendsto_neg_atTop_atBot.comp (tendsto_natCast_atTop_atTop :
          Filter.Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop))
  have hupper : Filter.Tendsto
      (fun n : ℕ => Real.exp (-(n : ℝ)) * (‖y‖ * ‖x‖)) atTop (𝓝 0) := by
    simpa only [Pi.mul_apply, zero_mul] using
      hexp.mul (tendsto_const_nhds :
        Filter.Tendsto (fun _ : ℕ => ‖y‖ * ‖x‖) atTop (𝓝 (‖y‖ * ‖x‖)))
  have hnorm_lim : Filter.Tendsto (fun n : ℕ => ‖g (n : ℝ)‖) atTop (𝓝 0) := by
    refine squeeze_zero' (f := fun n : ℕ => ‖g (n : ℝ)‖)
      (g := fun n : ℕ => Real.exp (-(n : ℝ)) * (‖y‖ * ‖x‖))
      (Filter.Eventually.of_forall fun n => norm_nonneg _)
      (Filter.Eventually.of_forall (fun n => ?_)) hupper
    calc
      ‖g (n : ℝ)‖ = Real.exp (-(n : ℝ)) *
          ‖⟪y, analyticExp T v (n : ℝ)⟫_ℂ‖ := by
            dsimp [g, f]
            rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
              abs_of_pos (Real.exp_pos _)]
      _ ≤ Real.exp (-(n : ℝ)) *
          (‖y‖ * ‖analyticExp T v (n : ℝ)‖) := by
            gcongr
            exact norm_inner_le_norm _ _
      _ = Real.exp (-(n : ℝ)) * (‖y‖ * ‖x‖) := by
        have hnorm : ‖analyticExp T v (n : ℝ)‖ = ‖x‖ := by
          obtain ⟨w, hw, heq⟩ := IsEntireVector.analyticExp_norm_eq_norm
            ⟨v, hv, hall⟩ hsym hdense (n : ℝ)
          rw [analyticExp_congr_iterates hv hw, heq]
        rw [hnorm]
  have hlim : Filter.Tendsto (fun n : ℕ => g (n : ℝ)) atTop (𝓝 0) :=
    (tendsto_zero_iff_norm_tendsto_zero).2 hnorm_lim
  have hconst_zero : g 0 = 0 := by
    have hc : Tendsto (fun _ : ℕ => g 0) atTop (𝓝 0) :=
      hlim.congr' (Filter.Eventually.of_forall fun n => hconst (n : ℝ))
    exact (tendsto_nhds_unique hc tendsto_const_nhds).symm
  have hexp_zero : analyticExp T v 0 = x := by
    rw [analyticExp, tsum_eq_single 0]
    · simpa [analyticExpTerm] using hv.1
    · intro n hn
      simp [analyticExpTerm, hn]
  simpa [g, f, hexp_zero] using hconst_zero

lemma analyticExp_continuousAt_of_mem_half_radius
    {T : H →ₗ.[ℂ] H} {v : ℕ → T.domain} {t s : ℝ} (ht : 0 < t)
    (hs : s ∈ Set.Ioo (-t / 2) (t / 2))
    (hsum : Summable (fun n => ‖(v n : H)‖ * t ^ n / n.factorial)) :
    ContinuousAt (fun r : ℝ => analyticExp T v r) s :=
  (analyticExp_hasDerivAt_of_mem_half_radius ht hs hsum).continuousAt

lemma IsAnalyticVector.exists_analyticExp_summable
    {T : H →ₗ.[ℂ] H} {x : H} (h : T.IsAnalyticVector x) :
    ∃ v : ℕ → T.domain, IteratesSeq T x v ∧ ∃ t : ℝ, 0 < t ∧ ∀ s : ℝ, |s| ≤ t →
      Summable (fun n => analyticExpTerm T v s n) := by
  obtain ⟨v, hv, t, ht, hsum⟩ := h
  refine ⟨v, hv, t, ht, fun s hs ↦ ?_⟩
  apply Summable.of_norm_bounded hsum
  intro n
  rw [norm_analyticExpTerm]
  have hpow : |s| ^ n ≤ t ^ n := pow_le_pow_left₀ (abs_nonneg s) hs n
  have hnonneg : 0 ≤ ‖(v n : H)‖ / n.factorial := by positivity
  calc
    ‖(v n : H)‖ * |s| ^ n / n.factorial
        = (‖(v n : H)‖ / n.factorial) * |s| ^ n := by ring
    _ ≤ (‖(v n : H)‖ / n.factorial) * t ^ n := by gcongr
    _ = ‖(v n : H)‖ * t ^ n / n.factorial := by ring

lemma IsAnalyticVector.summable_analyticExpTerm
    {T : H →ₗ.[ℂ] H} {v : ℕ → T.domain} {s : ℝ} {t : ℝ} (hs : |s| ≤ t)
    (hsum : Summable (fun n => ‖(v n : H)‖ * t ^ n / n.factorial)) :
    Summable (fun n => analyticExpTerm T v s n) := by
  apply Summable.of_norm_bounded hsum
  intro n
  rw [norm_analyticExpTerm]
  have hpow : |s| ^ n ≤ t ^ n := pow_le_pow_left₀ (abs_nonneg s) hs n
  have hnonneg : 0 ≤ ‖(v n : H)‖ / n.factorial := by positivity
  calc
    ‖(v n : H)‖ * |s| ^ n / n.factorial
        = (‖(v n : H)‖ / n.factorial) * |s| ^ n := by ring
    _ ≤ (‖(v n : H)‖ / n.factorial) * t ^ n := by gcongr
    _ = ‖(v n : H)‖ * t ^ n / n.factorial := by ring

lemma IsAnalyticVector.hasSum_analyticExp
    {T : H →ₗ.[ℂ] H} {v : ℕ → T.domain} {s : ℝ} {t : ℝ} (hs : |s| ≤ t)
    (hsum : Summable (fun n => ‖(v n : H)‖ * t ^ n / n.factorial)) :
    HasSum (fun n => analyticExpTerm T v s n) (analyticExp T v s) := by
  simpa only [analyticExp] using
    (summable_analyticExpTerm hs hsum).hasSum

lemma analyticExp_smul_iterates
    {T : H →ₗ.[ℂ] H} {v : ℕ → T.domain} {c : ℂ} {s t : ℝ}
    (hs : |s| ≤ t)
    (hsum : Summable (fun n => ‖(v n : H)‖ * t ^ n / n.factorial)) :
    analyticExp T (fun n => c • v n) s = c • analyticExp T v s := by
  have hsum_smul : Summable (fun n => ‖((c • v n : T.domain) : H)‖ * t ^ n /
      n.factorial) := by
    have heq : (fun n => ‖((c • v n : T.domain) : H)‖ * t ^ n / n.factorial) =
        (fun n => ‖c‖ * (‖(v n : H)‖ * t ^ n / n.factorial)) := by
      funext n
      rw [SetLike.val_smul, norm_smul]
      ring
    rw [heq]
    exact hsum.mul_left _
  have hleft := (IsAnalyticVector.hasSum_analyticExp (T := T)
    (v := fun n => c • v n) hs hsum_smul)
  have hright := (IsAnalyticVector.hasSum_analyticExp (T := T) (v := v) hs hsum).const_smul c
  have hterms : (fun n => analyticExpTerm T (fun n => c • v n) s n) =
      (fun n => c • analyticExpTerm T v s n) := by
    funext n
    unfold analyticExpTerm
    rw [SetLike.val_smul, smul_smul, smul_smul]
    congr 1
    ring
  rw [hterms] at hleft
  exact hleft.unique hright

lemma analyticExp_add_iterates
    {T : H →ₗ.[ℂ] H} {v w : ℕ → T.domain} {s t : ℝ}
    (hs : |s| ≤ t)
    (hv : Summable (fun n => ‖(v n : H)‖ * t ^ n / n.factorial))
    (hw : Summable (fun n => ‖(w n : H)‖ * t ^ n / n.factorial)) :
    analyticExp T (fun n => v n + w n) s =
      analyticExp T v s + analyticExp T w s := by
  have hsum_add : Summable (fun n => ‖((v n + w n : T.domain) : H)‖ * t ^ n /
      n.factorial) := by
    have ht : 0 ≤ t := le_trans (abs_nonneg s) hs
    have hbound : ∀ n, ‖((v n + w n : T.domain) : H)‖ * t ^ n /
        n.factorial ≤ ‖(v n : H)‖ * t ^ n / n.factorial +
          ‖(w n : H)‖ * t ^ n / n.factorial := by
      intro n
      have htri : ‖((v n + w n : T.domain) : H)‖ ≤ ‖(v n : H)‖ + ‖(w n : H)‖ := by
        exact norm_add_le _ _
      calc
        ‖((v n + w n : T.domain) : H)‖ * t ^ n / n.factorial
            ≤ (‖(v n : H)‖ + ‖(w n : H)‖) * t ^ n / n.factorial := by
              gcongr
        _ = ‖(v n : H)‖ * t ^ n / n.factorial +
            ‖(w n : H)‖ * t ^ n / n.factorial := by ring
    exact Summable.of_nonneg_of_le (fun n => by positivity) hbound (hv.add hw)
  have hleft := (IsAnalyticVector.hasSum_analyticExp (T := T)
    (v := fun n => v n + w n) hs hsum_add)
  have hright := (IsAnalyticVector.hasSum_analyticExp (T := T) (v := v) hs hv).add
    (IsAnalyticVector.hasSum_analyticExp (T := T) (v := w) hs hw)
  have hterms : (fun n => analyticExpTerm T (fun n => v n + w n) s n) =
      (fun n => analyticExpTerm T v s n + analyticExpTerm T w s n) := by
    funext n
    simp [analyticExpTerm, smul_add]
  rw [hterms] at hleft
  exact hleft.unique hright

omit [CompleteSpace H] in
lemma analyticExp_zero {T : H →ₗ.[ℂ] H} {x : H} {v : ℕ → T.domain}
    (hv : IteratesSeq T x v) : analyticExp T v 0 = x := by
  rw [analyticExp, tsum_eq_single 0]
  · simpa [analyticExpTerm] using hv.1
  · intro n hn
    simp [analyticExpTerm, hn]

omit [CompleteSpace H] in
lemma analyticExpTerm_succ {T : H →ₗ.[ℂ] H} {v : ℕ → T.domain}
    (hv : IteratesSeq T x v) (s : ℝ) (n : ℕ) :
    analyticExpTerm T v s (n + 1) =
      (((Complex.I * (s : ℂ)) ^ (n + 1)) / (n + 1).factorial) • T (v n) := by
  unfold analyticExpTerm
  rw [hv.2 n]

omit [CompleteSpace H] in
lemma IsAnalyticVector.mem_domain {T : H →ₗ.[ℂ] H} {x : H} (h : T.IsAnalyticVector x) :
    x ∈ T.domain := by
  obtain ⟨v, ⟨hv0, -⟩, -⟩ := h
  exact hv0 ▸ (v 0).2

omit [CompleteSpace H] in
/-- An analytic-vector witness for a closable operator is also a witness for its closure.

The iterate sequence is transported pointwise along `T.le_closure`; the closure agrees with `T`
on the original domain, so no regularity beyond closability is needed for this transfer. -/
lemma IsAnalyticVector.for_closure {T : H →ₗ.[ℂ] H} {x : H}
    (h : T.IsAnalyticVector x) :
    T.closure.IsAnalyticVector x := by
  obtain ⟨v, hv, t, ht, hsum⟩ := h
  let w : ℕ → T.closure.domain := fun n =>
    ⟨(v n : H), T.le_closure.1 (v n).property⟩
  have hw : IteratesSeq T.closure x w := by
    refine ⟨?_, fun n => ?_⟩
    · exact hv.1
    · have hcl : T ⟨(v n : H), (v n).property⟩ =
          T.closure (w n) := by
        exact T.le_closure.2 rfl
      calc
        (w (n + 1) : H) = T (v n) := hv.2 n
        _ = T.closure (w n) := hcl
  refine ⟨w, hw, t, ht, ?_⟩
  simpa [w] using hsum

omit [CompleteSpace H] in
/-- Applying `T` to an analytic vector preserves analyticity, with a smaller radius.

The shifted iterate sequence is `n ↦ v (n+1)`.  The loss of radius absorbs the linear factor
`n+1` introduced when the factorial denominator is shifted. -/
lemma IsAnalyticVector.apply {T : H →ₗ.[ℂ] H} {x : H}
    (h : T.IsAnalyticVector x) :
    T.IsAnalyticVector (T ⟨x, IsAnalyticVector.mem_domain h⟩) := by
  have hx : x ∈ T.domain := IsAnalyticVector.mem_domain h
  obtain ⟨v, hv, t, ht, hsum⟩ := h
  let w : ℕ → T.domain := fun n => v (n + 1)
  have hw : IteratesSeq T (T ⟨x, hx⟩) w := by
    refine ⟨?_, fun n => ?_⟩
    · change (v (0 + 1) : H) = T ⟨x, hx⟩
      rw [show (0 + 1 : ℕ) = 1 by rfl, hv.2 0]
      congr 1
      exact Subtype.ext hv.1
    · change (v ((n + 1) + 1) : H) = T (v (n + 1))
      exact hv.2 (n + 1)
  have htail : Summable (fun n : ℕ =>
      ‖(v (n + 1) : H)‖ * t ^ (n + 1) / (n + 1).factorial) := by
    simpa only [Nat.add_assoc] using
      ((summable_nat_add_iff
        (f := fun n : ℕ => ‖(v n : H)‖ * t ^ n / n.factorial) 1).2 hsum)
  have hfactor : ∀ n : ℕ, (n + 1 : ℝ) * ((1 : ℝ) / 2) ^ n ≤ 2 := by
    intro n
    induction n with
    | zero => norm_num
    | succ n ih =>
        calc
          (n.succ + 1 : ℝ) * ((1 : ℝ) / 2) ^ n.succ =
              ((n + 2 : ℝ) / 2) * ((1 : ℝ) / 2) ^ n := by
                rw [pow_succ]
                rw [Nat.cast_succ]
                ring
          _ ≤ (n + 1 : ℝ) * ((1 : ℝ) / 2) ^ n := by
            gcongr
            nlinarith
          _ ≤ 2 := ih
  have hbound : ∀ n : ℕ,
      ‖(w n : H)‖ * (t / 2) ^ n / n.factorial ≤
        (2 / t) * (‖(v (n + 1) : H)‖ * t ^ (n + 1) / (n + 1).factorial) := by
    intro n
    have htn : t ≠ 0 := ne_of_gt ht
    have hfactor' : (n + 1 : ℝ) * ((1 : ℝ) / 2) ^ n / t ≤ 2 / t :=
      div_le_div_of_nonneg_right (hfactor n) ht.le
    calc
      ‖(w n : H)‖ * (t / 2) ^ n / n.factorial =
          ((n + 1 : ℝ) * ((1 : ℝ) / 2) ^ n / t) *
            (‖(v (n + 1) : H)‖ * t ^ (n + 1) / (n + 1).factorial) := by
              dsimp [w]
              rw [Nat.factorial_succ]
              field_simp [htn]
              push_cast
              ring
      _ ≤ (2 / t) * (‖(v (n + 1) : H)‖ * t ^ (n + 1) / (n + 1).factorial) := by
        gcongr
  have ht2 : 0 < t / 2 := by linarith
  refine ⟨w, hw, t / 2, ht2, ?_⟩
  apply Summable.of_nonneg_of_le (fun n => by positivity) hbound
  exact htail.mul_left (2 / t)

omit [CompleteSpace H] in
/-- Applying the closed operator to a transported analytic vector preserves analyticity.

This is the form used by continuation arguments: after transporting an analytic witness from
`T` to `T.closure`, the smaller-radius invariance lemma can be iterated without leaving the closed
operator's domain. -/
lemma IsAnalyticVector.closure_apply {T : H →ₗ.[ℂ] H} {x : H}
    (h : T.IsAnalyticVector x) :
    T.closure.IsAnalyticVector
      (T.closure ⟨x, IsAnalyticVector.mem_domain (IsAnalyticVector.for_closure h)⟩) := by
  exact IsAnalyticVector.apply (IsAnalyticVector.for_closure h)

/-! ## Structural closure properties -/

omit [CompleteSpace H] in
lemma isAnalyticVector_zero (T : H →ₗ.[ℂ] H) : T.IsAnalyticVector 0 := by
  let v : ℕ → T.domain := fun _ => ⟨0, T.domain.zero_mem⟩
  refine ⟨v, ⟨by simp [v], fun n => ?_⟩, 1, one_pos, ?_⟩
  · change (0 : H) = T (v n)
    change (0 : H) = T (0 : T.domain)
    exact (map_zero T).symm
  · simp [v]

omit [CompleteSpace H] in
/-- Analytic vectors are closed under scalar multiplication, with the same radius. -/
lemma IsAnalyticVector.smul {T : H →ₗ.[ℂ] H} {x : H} (h : T.IsAnalyticVector x) (c : ℂ) :
    T.IsAnalyticVector (c • x) := by
  obtain ⟨v, ⟨hv0, hvS⟩, t, ht, hsum⟩ := h
  refine ⟨fun n => c • v n, ⟨by simp [hv0], fun n => ?_⟩, t, ht, ?_⟩
  · show (c • v (n + 1) : H) = T (c • v n)
    rw [hvS n, ← LinearPMap.map_smul]
  · have heq : (fun n => ‖(c • v n : T.domain).1‖ * t ^ n / n.factorial)
        = fun n => ‖c‖ * (‖(v n : H)‖ * t ^ n / n.factorial) := by
      funext n
      rw [SetLike.val_smul, norm_smul]
      ring
    rw [heq]
    exact hsum.mul_left _

omit [CompleteSpace H] in
/-- Analytic vectors form an additive submodule: if `x` is analytic with radius `t₁` and `y` with
radius `t₂`, then `x + y` is analytic with radius `min t₁ t₂` — the standard argument, since
`T.domain` is a submodule (so `x + y` and every iterate stay in the domain, with `T` additive
there) and the two majorizing power series compare termwise once the smaller radius is used for
both. -/
lemma IsAnalyticVector.add {T : H →ₗ.[ℂ] H} {x y : H}
    (hx : T.IsAnalyticVector x) (hy : T.IsAnalyticVector y) :
    T.IsAnalyticVector (x + y) := by
  obtain ⟨v, ⟨hv0, hvS⟩, t1, ht1, hsum1⟩ := hx
  obtain ⟨w, ⟨hw0, hwS⟩, t2, ht2, hsum2⟩ := hy
  have ht : (0:ℝ) < min t1 t2 := lt_min ht1 ht2
  refine ⟨fun n => v n + w n, ⟨by simp [hv0, hw0], fun n => ?_⟩, min t1 t2, ht, ?_⟩
  · show ((v (n + 1) + w (n + 1) : T.domain) : H) = T (v n + w n)
    show ((v (n+1) : H) + (w (n+1) : H)) = T (v n + w n)
    rw [hvS n, hwS n, LinearPMap.map_add]
  · have hbound : ∀ n, ‖((v n + w n : T.domain) : H)‖ * (min t1 t2) ^ n / n.factorial
        ≤ ‖(v n : H)‖ * t1 ^ n / n.factorial + ‖(w n : H)‖ * t2 ^ n / n.factorial := by
      intro n
      have htri : ‖((v n + w n : T.domain) : H)‖ ≤ ‖(v n : H)‖ + ‖(w n : H)‖ := by
        show ‖((v n : H) + (w n : H))‖ ≤ _
        exact norm_add_le _ _
      have h1 : (min t1 t2) ^ n ≤ t1 ^ n := pow_le_pow_left₀ ht.le (min_le_left t1 t2) n
      have h2 : (min t1 t2) ^ n ≤ t2 ^ n := pow_le_pow_left₀ ht.le (min_le_right t1 t2) n
      have hv1 : (0:ℝ) ≤ ‖(v n : H)‖ := norm_nonneg _
      have hw1 : (0:ℝ) ≤ ‖(w n : H)‖ := norm_nonneg _
      calc ‖((v n + w n : T.domain) : H)‖ * (min t1 t2) ^ n / n.factorial
          ≤ (‖(v n : H)‖ + ‖(w n : H)‖) * (min t1 t2) ^ n / n.factorial := by
            gcongr
        _ = ‖(v n : H)‖ * (min t1 t2) ^ n / n.factorial
              + ‖(w n : H)‖ * (min t1 t2) ^ n / n.factorial := by ring
        _ ≤ ‖(v n : H)‖ * t1 ^ n / n.factorial + ‖(w n : H)‖ * t2 ^ n / n.factorial := by
            gcongr
    exact Summable.of_nonneg_of_le (fun n => by positivity) hbound (hsum1.add hsum2)

/-- The analytic vectors form a genuine complex submodule.  This packages the set used in the
density hypothesis of Nelson's theorem and is also the natural candidate for the common analytic
core in the joint-commutation theorem. -/
def analyticVectors (T : H →ₗ.[ℂ] H) : Submodule ℂ H where
  carrier := {x | T.IsAnalyticVector x}
  zero_mem' := isAnalyticVector_zero T
  add_mem' := IsAnalyticVector.add
  smul_mem' := fun c _ hx => hx.smul c

omit [CompleteSpace H] in
@[simp]
lemma mem_analyticVectors {T : H →ₗ.[ℂ] H} {x : H} :
    x ∈ T.analyticVectors ↔ T.IsAnalyticVector x := Iff.rfl

omit [CompleteSpace H] in
lemma analyticVectors_le_domain {T : H →ₗ.[ℂ] H} :
    T.analyticVectors ≤ T.domain := by
  intro x hx
  exact IsAnalyticVector.mem_domain hx

omit [CompleteSpace H] in
lemma dense_analyticVectors_iff {T : H →ₗ.[ℂ] H} :
    (T.analyticVectors : Submodule ℂ H).topologicalClosure = ⊤ ↔
      (Submodule.span ℂ {x : H | T.IsAnalyticVector x}).topologicalClosure = ⊤ := by
  change T.analyticVectors.topologicalClosure = ⊤ ↔
    (Submodule.span ℂ (T.analyticVectors : Set H)).topologicalClosure = ⊤
  rw [Submodule.span_eq]

/-! ## Eigenvectors are analytic -/

omit [CompleteSpace H] in
/-- Every eigenvector is analytic for `T`, with *every* radius `t > 0`: its iterate sequence has
exactly geometric norm `‖x‖ * |μ|ⁿ`, so the series is dominated by a genuine exponential series,
convergent by `Real.summable_pow_div_factorial`. In particular every vector in a dense eigenbasis
(as in `RealAnalytic.lean`'s `isEssentiallySelfAdjoint_of_hilbertBasis_eigenvectors`) is
already an analytic vector: that theorem is the special case of Nelson's theorem where the dense
set of analytic vectors is exhibited concretely as an eigenbasis, rather than only assumed to
exist abstractly. -/
lemma isAnalyticVector_of_eigenvector {T : H →ₗ.[ℂ] H} {x : H} (hx : x ∈ T.domain) (μ : ℂ)
    (heig : T ⟨x, hx⟩ = μ • x) (t : ℝ) (ht : 0 < t) : T.IsAnalyticVector x := by
  have hmem : ∀ n : ℕ, μ ^ n • x ∈ T.domain := fun n => T.domain.smul_mem _ hx
  refine ⟨fun n => ⟨μ ^ n • x, hmem n⟩, ⟨by simp, fun n => ?_⟩, t, ht, ?_⟩
  · show μ ^ (n + 1) • x = T ⟨μ ^ n • x, hmem n⟩
    have hcast : (⟨μ ^ n • x, hmem n⟩ : T.domain) = μ ^ n • (⟨x, hx⟩ : T.domain) := by
      ext; simp
    rw [hcast, LinearPMap.map_smul, heig, smul_smul, pow_succ]
  · have heq : (fun n => ‖(⟨μ ^ n • x, hmem n⟩ : T.domain).1‖ * t ^ n / n.factorial)
        = fun n => ‖x‖ * ((‖μ‖ * t) ^ n / n.factorial) := by
      funext n
      simp only [norm_smul, norm_pow, mul_pow]
      ring
    rw [heq]
    exact (Real.summable_pow_div_factorial (‖μ‖ * t)).mul_left _

omit [CompleteSpace H] in
@[nolint unusedArguments]
lemma isEntireVector_of_eigenvector {T : H →ₗ.[ℂ] H} {x : H} (hx : x ∈ T.domain) (μ : ℂ)
    (heig : T ⟨x, hx⟩ = μ • x) : T.IsEntireVector x := by
  have hmem : ∀ n : ℕ, μ ^ n • x ∈ T.domain := fun n => T.domain.smul_mem _ hx
  refine ⟨fun n => ⟨μ ^ n • x, hmem n⟩, ⟨by simp, fun n => ?_⟩, fun t ht => ?_⟩
  · show μ ^ (n + 1) • x = T ⟨μ ^ n • x, hmem n⟩
    have hcast : (⟨μ ^ n • x, hmem n⟩ : T.domain) = μ ^ n • (⟨x, hx⟩ : T.domain) := by
      ext
      simp
    rw [hcast, LinearPMap.map_smul, heig, smul_smul, pow_succ]
  · have heq : (fun n => ‖(⟨μ ^ n • x, hmem n⟩ : T.domain).1‖ * t ^ n / n.factorial)
        = fun n => ‖x‖ * ((‖μ‖ * t) ^ n / n.factorial) := by
      funext n
      simp only [norm_smul, norm_pow, mul_pow]
      ring
    rw [heq]
    exact (Real.summable_pow_div_factorial (‖μ‖ * t)).mul_left _

omit [CompleteSpace H] in
lemma isEntireVector_zero (T : H →ₗ.[ℂ] H) : T.IsEntireVector 0 := by
  let v : ℕ → T.domain := fun _ => ⟨0, T.domain.zero_mem⟩
  refine ⟨v, ⟨by simp [v], fun n => ?_⟩, fun t ht => ?_⟩
  · change (0 : H) = T (v n)
    change (0 : H) = T (0 : T.domain)
    exact (map_zero T).symm
  · simp [v]

omit [CompleteSpace H] in
lemma IsEntireVector.smul {T : H →ₗ.[ℂ] H} {x : H} (h : T.IsEntireVector x) (c : ℂ) :
    T.IsEntireVector (c • x) := by
  obtain ⟨v, ⟨hv0, hvS⟩, hall⟩ := h
  refine ⟨fun n => c • v n, ⟨by simp [hv0], fun n => ?_⟩, fun t ht => ?_⟩
  · show (c • v (n + 1) : H) = T (c • v n)
    rw [hvS n, ← LinearPMap.map_smul]
  · have heq : (fun n => ‖(c • v n : T.domain).1‖ * t ^ n / n.factorial)
        = fun n => ‖c‖ * (‖(v n : H)‖ * t ^ n / n.factorial) := by
      funext n
      rw [SetLike.val_smul, norm_smul]
      ring
    rw [heq]
    exact (hall t ht).mul_left _

omit [CompleteSpace H] in
lemma IsEntireVector.add {T : H →ₗ.[ℂ] H} {x y : H}
    (hx : T.IsEntireVector x) (hy : T.IsEntireVector y) :
    T.IsEntireVector (x + y) := by
  obtain ⟨v, ⟨hv0, hvS⟩, hallv⟩ := hx
  obtain ⟨w, ⟨hw0, hwS⟩, hallw⟩ := hy
  refine ⟨fun n => v n + w n, ⟨by simp [hv0, hw0], fun n => ?_⟩, fun t ht => ?_⟩
  · show ((v (n + 1) + w (n + 1) : T.domain) : H) = T (v n + w n)
    show ((v (n + 1) : H) + (w (n + 1) : H)) = T (v n + w n)
    rw [hvS n, hwS n, LinearPMap.map_add]
  · have hbound : ∀ n, ‖((v n + w n : T.domain) : H)‖ * t ^ n /
        n.factorial ≤ ‖(v n : H)‖ * t ^ n / n.factorial +
          ‖(w n : H)‖ * t ^ n / n.factorial := by
      intro n
      have htri : ‖((v n + w n : T.domain) : H)‖ ≤ ‖(v n : H)‖ + ‖(w n : H)‖ := by
        exact norm_add_le _ _
      calc
        ‖((v n + w n : T.domain) : H)‖ * t ^ n / n.factorial
            ≤ (‖(v n : H)‖ + ‖(w n : H)‖) * t ^ n / n.factorial := by
              gcongr
        _ = ‖(v n : H)‖ * t ^ n / n.factorial +
            ‖(w n : H)‖ * t ^ n / n.factorial := by ring
    exact Summable.of_nonneg_of_le (fun n => by positivity) hbound
      ((hallv t ht).add (hallw t ht))

omit [CompleteSpace H] in
/-- The submodule of entire vectors for `T`. -/
def entireVectors (T : H →ₗ.[ℂ] H) : Submodule ℂ H where
  carrier := {x | T.IsEntireVector x}
  zero_mem' := isEntireVector_zero T
  add_mem' := IsEntireVector.add
  smul_mem' := fun c _ hx => hx.smul c

omit [CompleteSpace H] in
@[simp]
lemma mem_entireVectors {T : H →ₗ.[ℂ] H} {x : H} :
    x ∈ T.entireVectors ↔ T.IsEntireVector x := Iff.rfl

/-! ## The global-orbit essential-self-adjointness criterion -/

/-- A dense family of entire vectors is sufficient for essential self-adjointness.

This is the part of Nelson's argument for which the global exponential orbit is available without
any continuation argument.  The two deficiency spaces are killed directly: pair the global orbit
with a deficiency vector, solve the resulting scalar ODE, and send the real time to the end at
which the compensating exponential tends to zero.  The original finite-radius Nelson theorem
below is stronger; it still requires the local-semigroup continuation step. -/
theorem IsSymmetric.isEssentiallySelfAdjoint_of_denseEntireVectors
    {T : H →ₗ.[ℂ] H} (hsym : T.IsSymmetric)
    (hdense : T.entireVectors.topologicalClosure = ⊤) :
    T.IsEssentiallySelfAdjoint := by
  have hleAnalytic : T.entireVectors ≤ T.analyticVectors := by
    intro x hx
    exact IsEntireVector.isAnalyticVector hx
  have hdenseAnalyticSubmodule : T.analyticVectors.topologicalClosure = ⊤ := by
    apply top_unique
    rw [← hdense]
    exact Submodule.topologicalClosure_mono hleAnalytic
  have hdenseAnalytic :
      (Submodule.span ℂ {x : H | T.IsAnalyticVector x}).topologicalClosure = ⊤ :=
    (dense_analyticVectors_iff (T := T)).mp hdenseAnalyticSubmodule
  have hleDomain : T.entireVectors ≤ T.domain := by
    intro x hx
    exact analyticVectors_le_domain (IsEntireVector.isAnalyticVector hx)
  have hdenseDomain : T.HasDenseDomain := by
    have hdomainClosure : T.domain.topologicalClosure = ⊤ := by
      apply top_unique
      rw [← hdense]
      exact Submodule.topologicalClosure_mono hleDomain
    rw [LinearPMap.hasDenseDomain_def, dense_iff_closure_eq]
    rw [← Submodule.topologicalClosure_coe, hdomainClosure]
    rfl
  have hT : T.IsClosable := hsym.isClosable hdenseDomain
  have hspanEntire :
      (Submodule.span ℂ (T.entireVectors : Set H)).topologicalClosure = ⊤ := by
    rw [Submodule.span_eq]
    exact hdense
  have hdefect_plus : T.defectNumber Complex.I = 0 := by
    rw [← defectNumber_closure (T := T) (z := Complex.I)
      (hsym.mem_regularityDomain_of_im_ne_zero (by simp))]
    show Module.rank ℂ ↥((T.closure - Complex.I • 1).toFun.rangeᗮ) = 0
    apply Submodule.rank_eq_zero.mpr
    apply (Submodule.eq_bot_iff _).mpr
    intro y hy
    have hyspan : y ∈ (Submodule.span ℂ (T.entireVectors : Set H))ᗮ := by
      rw [Submodule.mem_orthogonal']
      intro u hu
      refine Submodule.span_induction (p := fun z _ ↦ ⟪y, z⟫_ℂ = 0) ?_ ?_ ?_ ?_ hu
      · rintro z hz
        obtain ⟨w, hw, hallw⟩ := mem_entireVectors.mp hz
        exact analyticExp_inner_deficiency_eq_zero hsym hdenseAnalytic hw hallw hT hy
      · simp
      · intro z₁ z₂ _ _ hz₁ hz₂
        simp [inner_add_right, hz₁, hz₂]
      · intro c z _ hz
        simp [inner_smul_right, hz]
    have hspanBot :
        (Submodule.span ℂ (T.entireVectors : Set H))ᗮ = (⊥ : Submodule ℂ H) :=
      Submodule.topologicalClosure_eq_top_iff.mp hspanEntire
    exact (Submodule.mem_bot ℂ).mp (hspanBot ▸ hyspan)
  have hdefect_minus : T.defectNumber (-Complex.I) = 0 := by
    rw [← defectNumber_closure (T := T) (z := -Complex.I)
      (hsym.mem_regularityDomain_of_im_ne_zero (by simp))]
    show Module.rank ℂ ↥((T.closure - (-Complex.I) • 1).toFun.rangeᗮ) = 0
    apply Submodule.rank_eq_zero.mpr
    apply (Submodule.eq_bot_iff _).mpr
    intro y hy
    have hyspan : y ∈ (Submodule.span ℂ (T.entireVectors : Set H))ᗮ := by
      rw [Submodule.mem_orthogonal']
      intro u hu
      refine Submodule.span_induction (p := fun z _ ↦ ⟪y, z⟫_ℂ = 0) ?_ ?_ ?_ ?_ hu
      · rintro z hz
        obtain ⟨w, hw, hallw⟩ := mem_entireVectors.mp hz
        exact analyticExp_inner_deficiency_eq_zero_neg hsym hdenseAnalytic hw hallw hT hy
      · simp
      · intro z₁ z₂ _ _ hz₁ hz₂
        simp [inner_add_right, hz₁, hz₂]
      · intro c z _ hz
        simp [inner_smul_right, hz]
    have hspanBot :
        (Submodule.span ℂ (T.entireVectors : Set H))ᗮ = (⊥ : Submodule ℂ H) :=
      Submodule.topologicalClosure_eq_top_iff.mp hspanEntire
    exact (Submodule.mem_bot ℂ).mp (hspanBot ▸ hyspan)
  exact hsym.isEssentiallySelfAdjoint_of_defectNumber_eq_zero
    hdenseDomain hdefect_plus hdefect_minus

/-! ## Common domain infrastructure for the finite-radius argument -/

omit [CompleteSpace H] in
@[nolint unusedArguments]
lemma hasDenseDomain_of_denseAnalyticVectors
    {T : H →ₗ.[ℂ] H}
    (hdense : (Submodule.span ℂ {x : H | T.IsAnalyticVector x}).topologicalClosure = ⊤) :
    T.HasDenseDomain := by
  have hspan : Dense (Submodule.span ℂ {x : H | T.IsAnalyticVector x} : Set H) := by
    rw [dense_iff_closure_eq]
    rw [← Submodule.topologicalClosure_coe]
    exact congrArg (fun s : Submodule ℂ H => (s : Set H)) hdense
  have hdomain : (Submodule.span ℂ {x : H | T.IsAnalyticVector x}) ≤ T.domain := by
    refine Submodule.span_le.2 (fun x hx => ?_)
    exact IsAnalyticVector.mem_domain (by simpa using hx)
  exact hspan.mono hdomain

lemma IsSymmetric.closure_of_denseAnalyticVectors
    {T : H →ₗ.[ℂ] H} (hsym : T.IsSymmetric)
    (hdense : (Submodule.span ℂ {x : H | T.IsAnalyticVector x}).topologicalClosure = ⊤) :
    T.closure.IsSymmetric :=
  hsym.closure (hasDenseDomain_of_denseAnalyticVectors hdense)

/-! ## The global-orbit certificate targeted by Nelson continuation -/

/-- A local norm-preserving orbit on a symmetric operator's analytic radius.  The finite-radius
Nelson construction starts with this object and must extend it by overlapping local pieces. -/
structure LocalAnalyticOrbit (T : H →ₗ.[ℂ] H) (x : H) where
  /-- The radius on which the orbit is defined. -/
  radius : ℝ
  radius_pos : 0 < radius
  /-- The orbit itself, as a function of real time. -/
  toFun : ℝ → H
  initial : toFun 0 = x
  mem_domain : ∀ s, |s| < radius → toFun s ∈ T.closure.domain
  hasDerivAt : ∀ (s : ℝ) (hs : |s| < radius),
    HasDerivAt toFun
      (Complex.I • T.closure ⟨toFun s, mem_domain s hs⟩) s
  norm_eq : ∀ (s : ℝ) (_hs : |s| < radius), ‖toFun s‖ = ‖x‖


end LinearPMap
