/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.AlgebraicFramework.HilbertSpace.Unbounded.AnalyticVector.Basic

/-!
# Analytic vectors for an unbounded operator (part 2 of 3: local and global orbits)

Continuation of `AnalyticVector/Basic.lean`; this part covers `LocalAnalyticOrbit` and
`GlobalAnalyticOrbit`, the certificate objects the finite-radius
Nelson construction extends by overlapping local pieces (Reed–Simon Vol. II, Thm X.39).

## Main definitions

- `GlobalAnalyticOrbit` : a global norm-preserving orbit for a vector, with the differential
  equation interpreted in the closed operator; the exact analytic certificate needed by the
  deficiency argument.
- `LocalOrbitCover` / `LocalOrbitCoreCover` : a countable cover of `ℝ` by local analytic orbits,
  agreeing pairwise on their overlaps, used to glue local charts into a global orbit.

## Main results

- `LocalAnalyticOrbit.eq_of_same_initial` : two local orbits based at the same state agree on the
  intersection of their domains.
- `LocalOrbitCover.toGlobal` / `LocalOrbitCoreCover.toGlobal` : glue a cover into a single global
  analytic orbit.
- `GlobalAnalyticOrbit.inner_deficiency_eq_zero` / `inner_deficiency_eq_zero_neg` : a global orbit
  kills both deficiency spaces.
-/

@[expose] public section

noncomputable section

namespace LinearPMap

open scoped InnerProductSpace Topology
open Filter

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace LocalAnalyticOrbit

instance {T : H →ₗ.[ℂ] H} {x : H} : CoeFun (LocalAnalyticOrbit T x)
    (fun _ => ℝ → H) := ⟨LocalAnalyticOrbit.toFun⟩

/-- Recentring is the basic overlap operation in the finite-radius continuation argument. -/
def translateTo {T : H →ₗ.[ℂ] H} {x : H} (U : LocalAnalyticOrbit T x) (a : ℝ)
    (ha : |a| < U.radius) : LocalAnalyticOrbit T (U a) :=
  let r : ℝ := U.radius - |a|
  { radius := r
    radius_pos := sub_pos.mpr ha
    toFun := fun s => U (a + s)
    initial := by simp
    mem_domain := fun s hs => by
      have hsum : |a + s| ≤ |a| + |s| := abs_add_le _ _
      have hlt : |a| + |s| < U.radius := by
        dsimp [r] at hs
        linarith
      exact U.mem_domain (a + s) (lt_of_le_of_lt hsum hlt)
    hasDerivAt := fun s hs => by
      have hsum : |a + s| ≤ |a| + |s| := abs_add_le _ _
      have hlt : |a| + |s| < U.radius := by
        dsimp [r] at hs
        linarith
      have hcomp := U.hasDerivAt (a + s) (lt_of_le_of_lt hsum hlt)
      have hcomp' := hcomp.comp_const_add a s
      simpa only [Function.comp_def] using hcomp'
    norm_eq := fun s hs => by
      have hsum : |a + s| ≤ |a| + |s| := abs_add_le _ _
      have hlt : |a| + |s| < U.radius := by
        dsimp [r] at hs
        linarith
      calc
        ‖U (a + s)‖ = ‖x‖ := U.norm_eq (a + s) (lt_of_le_of_lt hsum hlt)
        _ = ‖U a‖ := (U.norm_eq a ha).symm }

omit [CompleteSpace H] in
@[nolint unusedArguments]
lemma translate {T : H →ₗ.[ℂ] H} {x : H} (U : LocalAnalyticOrbit T x) (a : ℝ)
    (ha : |a| < U.radius) : Nonempty (LocalAnalyticOrbit T (U a)) :=
  ⟨U.translateTo a ha⟩

/-- The direct (non-`Nonempty`) form of chart restriction. -/
def restrictTo {T : H →ₗ.[ℂ] H} {x : H} (U : LocalAnalyticOrbit T x)
    {r : ℝ} (hr : 0 < r) (hrU : r ≤ U.radius) : LocalAnalyticOrbit T x :=
  { radius := r
    radius_pos := hr
    toFun := U
    initial := U.initial
    mem_domain := fun s hs => U.mem_domain s (lt_of_lt_of_le hs hrU)
    hasDerivAt := fun s hs => U.hasDerivAt s (lt_of_lt_of_le hs hrU)
    norm_eq := fun s hs => U.norm_eq s (lt_of_lt_of_le hs hrU) }

omit [CompleteSpace H] in
/-- Restrict a local orbit to a smaller symmetric radius.  Keeping this operation explicit is
useful for gluing: adjacent recentered charts need only agree on a deliberately chosen core of
their domains, while the original charts may have larger asymmetric overlaps. -/
@[nolint unusedArguments]
lemma restrict {T : H →ₗ.[ℂ] H} {x : H} (U : LocalAnalyticOrbit T x)
    {r : ℝ} (hr : 0 < r) (hrU : r ≤ U.radius) :
    Nonempty (LocalAnalyticOrbit T x) := by
  exact ⟨U.restrictTo hr hrU⟩

omit [CompleteSpace H] in
lemma eq_of_same_initial
    {T : H →ₗ.[ℂ] H} {x : H} (U V : LocalAnalyticOrbit T x)
    (hclosure_symm : T.closure.IsSymmetric) {s : ℝ}
    (hs : |s| < min U.radius V.radius) : U s = V s := by
  let r : ℝ := min U.radius V.radius
  have hr : 0 < r := lt_min U.radius_pos V.radius_pos
  have hinterval : ∀ y : ℝ, y ∈ Set.Ioo (-r) r →
      HasDerivAt (fun q : ℝ => ‖U q - V q‖ ^ 2) 0 y := by
    intro y hy
    have hyabs : |y| < r := by
      rw [abs_lt]
      exact ⟨hy.1, hy.2⟩
    have hyU : |y| < U.radius := lt_of_lt_of_le hyabs (min_le_left _ _)
    have hyV : |y| < V.radius := lt_of_lt_of_le hyabs (min_le_right _ _)
    have hdom : U y - V y ∈ T.closure.domain :=
      T.closure.domain.sub_mem (U.mem_domain y hyU) (V.mem_domain y hyV)
    let z : T.closure.domain := ⟨U y - V y, hdom⟩
    let u : T.closure.domain := ⟨U y, U.mem_domain y hyU⟩
    let v : T.closure.domain := ⟨V y, V.mem_domain y hyV⟩
    have hderivU := U.hasDerivAt y hyU
    have hderivV := V.hasDerivAt y hyV
    have hderiv : HasDerivAt (fun q : ℝ => U q - V q)
        (Complex.I • T.closure z) y := by
      have hsub := hderivU.sub hderivV
      have hz : z = u - v := by
        apply Subtype.ext
        rfl
      rw [hz, map_sub]
      have hfun : (U.toFun - V.toFun) = (fun q : ℝ => U q - V q) := by
        funext q
        rfl
      rw [hfun] at hsub
      simpa [u, v, smul_sub] using hsub
    let _ : InnerProductSpace ℝ H := InnerProductSpace.rclikeToReal ℂ H
    have hnorm : HasDerivAt (fun q : ℝ => ‖U q - V q‖ ^ 2)
        (2 * ⟪U y - V y, Complex.I • T.closure z⟫_ℝ) y := by
      simpa [ContinuousLinearMap.toSpanSingleton_apply, inner_sub_left] using
        hderiv.hasFDerivAt.norm_sq.hasDerivAt
    have hinner := hclosure_symm.re_inner_smul_I_apply_self z
    have hinner' : ⟪U y - V y, Complex.I • T.closure z⟫_ℝ = 0 := by
      simpa [z, real_inner_eq_re_inner] using hinner
    simpa [hinner'] using hnorm
  have hconst : ∀ {a b : ℝ}, a ∈ Set.Ioo (-r) r → b ∈ Set.Ioo (-r) r →
      ‖U a - V a‖ ^ 2 = ‖U b - V b‖ ^ 2 := by
    intro a b ha hb
    exact isOpen_Ioo.is_const_of_deriv_eq_zero
      (s := Set.Ioo (-r) r) (f := fun q : ℝ => ‖U q - V q‖ ^ 2)
      (isPreconnected_Ioo (a := -r) (b := r))
      (fun q hq => (hinterval q hq).differentiableAt.differentiableWithinAt)
      (fun q hq => (hinterval q hq).deriv) ha hb
  have hzero_mem : (0 : ℝ) ∈ Set.Ioo (-r) r := by
    constructor <;> linarith
  have hs_mem : s ∈ Set.Ioo (-r) r := by
    change -r < s ∧ s < r
    exact abs_lt.mp hs
  have hnormsq : ‖U s - V s‖ ^ 2 = 0 := by
    rw [hconst hs_mem hzero_mem]
    simp [U.initial, V.initial]
  apply sub_eq_zero.mp
  apply norm_eq_zero.mp
  nlinarith [sq_nonneg ‖U s - V s‖]

/-! A translated chart and a chart independently based at the translated state agree on every
smaller symmetric core.  This is the elementary overlap statement used by the integer-chart
continuation below; the explicit radius inequalities keep the asymmetric translated radius out of
the later gluing proof. -/
omit [CompleteSpace H] in
lemma translate_eq_of_same_initial_on_core
    {T : H →ₗ.[ℂ] H} {x : H} (U : LocalAnalyticOrbit T x)
    (hclosure_symm : T.closure.IsSymmetric) {δ R : ℝ}
    (hδ : 0 < δ) (hR : 0 < R) (hδU : δ + R ≤ U.radius)
    (V : LocalAnalyticOrbit T (U δ)) (hVR : R ≤ V.radius) {s : ℝ}
    (hs : |s| < R) : U (δ + s) = V s := by
  have hδU' : |δ| < U.radius := by
    rw [abs_of_pos hδ]
    linarith
  let W : LocalAnalyticOrbit T (U δ) := U.translateTo δ hδU'
  have hWR : R ≤ W.radius := by
    dsimp [W, translateTo]
    rw [abs_of_pos hδ]
    linarith
  have hsW : |s| < W.radius := lt_of_lt_of_le hs hWR
  have hsV : |s| < V.radius := lt_of_lt_of_le hs hVR
  have heq := LocalAnalyticOrbit.eq_of_same_initial W V hclosure_symm
    (lt_min hsW hsV)
  change U (δ + s) = V s at heq
  exact heq

omit [CompleteSpace H] in
lemma translate_eq_of_same_initial_on_core'
    {T : H →ₗ.[ℂ] H} {x : H} (U : LocalAnalyticOrbit T x)
    (hclosure_symm : T.closure.IsSymmetric) {a R : ℝ}
    (hR : 0 < R) (haU : |a| + R ≤ U.radius)
    (V : LocalAnalyticOrbit T (U a)) (hVR : R ≤ V.radius) {s : ℝ}
    (hs : |s| < R) : U (a + s) = V s := by
  have haU' : |a| < U.radius := by linarith
  let W : LocalAnalyticOrbit T (U a) := U.translateTo a haU'
  have hWR : R ≤ W.radius := by
    dsimp [W, translateTo]
    linarith
  have heq := LocalAnalyticOrbit.eq_of_same_initial W V hclosure_symm
    (lt_min (lt_of_lt_of_le hs hWR) (lt_of_lt_of_le hs hVR))
  change U (a + s) = V s at heq
  exact heq

omit [CompleteSpace H] in
/-- Transport a local orbit certificate for the closure back to a closable operator.  This is the
local counterpart of `GlobalAnalyticOrbit.of_closure`; it is needed when a fresh chart is produced
recursively for the closed operator but the public continuation interface is phrased for `T`. -/
@[nolint unusedArguments]
lemma of_closure {T : H →ₗ.[ℂ] H} {x : H} (hT : T.IsClosable)
    (U : LocalAnalyticOrbit T.closure x) : Nonempty (LocalAnalyticOrbit T x) := by
  have hclosed : T.closure.closure = T.closure := hT.closure_isClosed.closure_eq
  have happly : ∀ (z : H) (hz : z ∈ T.closure.domain)
      (hz' : z ∈ T.closure.closure.domain),
      T.closure.closure ⟨z, hz'⟩ = T.closure ⟨z, hz⟩ := by
    intro z hz hz'
    have hgraph : (z, T.closure.closure ⟨z, hz'⟩) ∈ T.closure.graph := by
      have hgraph_eq : T.closure.closure.graph = T.closure.graph :=
        congrArg (fun R : H →ₗ.[ℂ] H => R.graph) hclosed
      exact hgraph_eq ▸ T.closure.closure.mem_graph ⟨z, hz'⟩
    exact T.closure.mem_graph_snd_inj' hgraph
      (T.closure.mem_graph ⟨z, hz⟩) rfl
  refine ⟨
    { radius := U.radius
      radius_pos := U.radius_pos
      toFun := U
      initial := U.initial
      mem_domain := fun s hs => by
        simpa only [hclosed] using U.mem_domain s hs
      hasDerivAt := fun s hs => by
        have hz' : U s ∈ T.closure.closure.domain := U.mem_domain s hs
        have hz : U s ∈ T.closure.domain := by
          simpa only [hclosed] using hz'
        have hd := U.hasDerivAt s hs
        convert hd using 1
        congr 1
        exact (happly _ hz hz').symm
      norm_eq := U.norm_eq }⟩

end LocalAnalyticOrbit

/-- A global norm-preserving orbit for a vector, with the differential equation interpreted in the
closed operator.  This is the exact analytic certificate needed by the deficiency argument; the
finite-radius Nelson proof constructs it by patching the local exponential series. -/
structure GlobalAnalyticOrbit (T : H →ₗ.[ℂ] H) (x : H) where
  /-- The orbit itself, as a function of real time. -/
  toFun : ℝ → H
  initial : toFun 0 = x
  mem_domain : ∀ s, toFun s ∈ T.closure.domain
  hasDerivAt : ∀ s, HasDerivAt toFun
    (Complex.I • T.closure ⟨toFun s, mem_domain s⟩) s
  norm_eq : ∀ s, ‖toFun s‖ = ‖x‖

namespace GlobalAnalyticOrbit

instance {T : H →ₗ.[ℂ] H} {x : H} : CoeFun (GlobalAnalyticOrbit T x)
    (fun _ => ℝ → H) := ⟨GlobalAnalyticOrbit.toFun⟩

lemma exists_bound_choose_mul_geometric {r : ℝ} (hr : 0 ≤ r) (hr' : r < 1) (k : ℕ) :
    ∃ C : ℝ, ∀ n : ℕ, (n + k).choose k * r ^ n ≤ C := by
  have hnorm : ‖r‖ < 1 := by
    simpa [Real.norm_eq_abs, abs_of_nonneg hr] using hr'
  have hsum : Summable (fun n : ℕ => (n + k).choose k * r ^ n) :=
    summable_choose_mul_geometric_of_norm_lt_one k hnorm
  refine ⟨∑' n : ℕ, (n + k).choose k * r ^ n, fun n => ?_⟩
  exact hsum.le_tsum n (fun j _ => by positivity)

lemma summable_shifted_factorial_majorant {a : ℕ → ℝ} {t q : ℝ}
    (ha : ∀ n, 0 ≤ a n) (ht : 0 < t) (hq : 0 ≤ q) (hqt : q < t) (k : ℕ)
    (hsum : Summable (fun n : ℕ => a n * t ^ n / n.factorial)) :
    Summable (fun n : ℕ => a (n + k) * q ^ n / n.factorial) := by
  let r : ℝ := q / t
  have hr : 0 ≤ r := div_nonneg hq ht.le
  have hr' : r < 1 := by
    dsimp [r]
    exact (div_lt_one ht).2 hqt
  obtain ⟨C, hC⟩ := exists_bound_choose_mul_geometric hr hr' k
  have hC0 : 0 ≤ C := by
    have h := hC 0
    norm_num at h
    linarith
  let b : ℕ → ℝ := fun n => a (n + k) * t ^ (n + k) / (n + k).factorial
  have hb : Summable b := by
    dsimp [b]
    exact (summable_nat_add_iff
      (f := fun n : ℕ => a n * t ^ n / n.factorial) k).2 hsum
  let K : ℝ := C * (k.factorial : ℝ) / t ^ k
  have hK : 0 ≤ K := by
    positivity
  refine Summable.of_nonneg_of_le
    (fun n => div_nonneg (mul_nonneg (ha (n + k)) (pow_nonneg hq _)) (by positivity)) ?_
    (hb.mul_left K)
  intro n
  have hchoose : (n + k).choose k * r ^ n ≤ C := hC n
  have hbase : 0 ≤ b n := by
    dsimp [b]
    exact div_nonneg (mul_nonneg (ha (n + k)) (pow_nonneg ht.le _)) (by positivity)
  have hcoef : (k.factorial : ℝ) * (n + k).choose k * r ^ n / t ^ k ≤
      C * (k.factorial : ℝ) / t ^ k := by
    have hfac : 0 ≤ (k.factorial : ℝ) / t ^ k := by positivity
    calc
      (k.factorial : ℝ) * (n + k).choose k * r ^ n / t ^ k =
          ((n + k).choose k * r ^ n) * ((k.factorial : ℝ) / t ^ k) := by
            ring
      _ ≤ C * ((k.factorial : ℝ) / t ^ k) :=
        mul_le_mul_of_nonneg_right hchoose hfac
      _ = C * (k.factorial : ℝ) / t ^ k := by ring
  calc
    a (n + k) * q ^ n / n.factorial =
        b n * ((k.factorial : ℝ) * (n + k).choose k * r ^ n / t ^ k) := by
      dsimp [b, r]
      have hfact : (n.factorial : ℝ) * (k.factorial : ℝ) *
          (n + k).choose k = (n + k).factorial := by
        have h := Nat.factorial_mul_descFactorial
          (n := n + k) (k := k) (Nat.le_add_left k n)
        rw [Nat.descFactorial_eq_factorial_mul_choose] at h
        have hnk : n + k - k = n := by omega
        rw [hnk] at h
        norm_cast
        simpa [mul_assoc] using h
      have hfact' : (n + k).factorial =
          (n.factorial : ℝ) * ((k.factorial : ℝ) * (n + k).choose k) := by
        rw [← hfact]
        ring
      rw [div_pow]
      field_simp [ne_of_gt ht]
      rw [hfact']
      ring
    _ ≤ b n * K := mul_le_mul_of_nonneg_left hcoef hbase
    _ = K * b n := by rw [mul_comm]

/-- The iterate sequence `v` shifted by `k` steps, `n ↦ v (n + k)`. -/
def shiftedIterates {T : H →ₗ.[ℂ] H} (v : ℕ → T.domain) (k : ℕ) : ℕ → T.domain :=
  fun n => v (n + k)

omit [CompleteSpace H] in
@[nolint unusedArguments]
lemma IteratesSeq.shift {T : H →ₗ.[ℂ] H} {x : H} {v : ℕ → T.domain}
    (hv : IteratesSeq T x v) (k : ℕ) :
    IteratesSeq T (v k) (shiftedIterates v k) := by
  refine ⟨?_, fun n => ?_⟩
  · simp [shiftedIterates]
  · change (v (n + 1 + k) : H) = T (v (n + k))
    rw [show n + 1 + k = (n + k) + 1 by omega, hv.2]

omit [CompleteSpace H] in
@[nolint unusedArguments]
lemma summable_shifted_iterates {T : H →ₗ.[ℂ] H} {v : ℕ → T.domain}
    {t q : ℝ} (ht : 0 < t) (hq : 0 ≤ q) (hqt : q < t) (k : ℕ)
    (hsum : Summable (fun n : ℕ => ‖(v n : H)‖ * t ^ n / n.factorial)) :
    Summable (fun n : ℕ => ‖(shiftedIterates v k n : H)‖ * q ^ n / n.factorial) := by
  exact summable_shifted_factorial_majorant
    (a := fun n : ℕ => ‖(v n : H)‖) (t := t) (q := q)
    (fun n => norm_nonneg _) ht hq hqt k (by simpa using hsum)

@[nolint unusedArguments]
lemma neg_I_smul_tsum_analyticExpDerivTerm_shift_eq
    {T : H →ₗ.[ℂ] H} {x : H} {v : ℕ → T.domain} (_hv : IteratesSeq T x v)
    {t s : ℝ} (ht : 0 < t) (hs : s ∈ Set.Ioo (-t / 2) (t / 2))
    (hsum : Summable (fun n : ℕ => ‖(v n : H)‖ * t ^ n / n.factorial)) (k : ℕ) :
    (-Complex.I) • (∑' n, analyticExpDerivTerm T (shiftedIterates v k) s n) =
      analyticExp T (shiftedIterates v (k + 1)) s := by
  have hsabs : |s| < t / 2 := by
    rw [abs_lt]
    exact ⟨by linarith [hs.1], by linarith [hs.2]⟩
  let t' : ℝ := (t + 2 * |s|) / 2
  have ht' : 0 < t' := by
    dsimp [t']
    linarith [ht, abs_nonneg s]
  have h2s : 2 * |s| < t' := by
    dsimp [t']
    linarith [hsabs]
  have ht't : t' < t := by
    dsimp [t']
    linarith [hsabs]
  have hsum_k : Summable (fun n : ℕ =>
      ‖(shiftedIterates v k n : H)‖ * t' ^ n / n.factorial) :=
    summable_shifted_iterates (v := v) ht ht'.le ht't k hsum
  have hsum_k1 : Summable (fun n : ℕ =>
      ‖(shiftedIterates v (k + 1) n : H)‖ * t' ^ n / n.factorial) :=
    summable_shifted_iterates (v := v) ht ht'.le ht't (k + 1) hsum
  have hs' : s ∈ Set.Ioo (-t' / 2) (t' / 2) := by
    change -t' / 2 < s ∧ s < t' / 2
    constructor <;> linarith [neg_le_abs s, le_abs_self s, h2s]
  have hderiv := summable_analyticExpDerivTerm_of_mem_half_radius
    (T := T) (v := shiftedIterates v k) ht' hs' hsum_k
  have hsum_next : Summable (fun n : ℕ => analyticExpTerm T
      (shiftedIterates v (k + 1)) s n) := by
    exact IsAnalyticVector.summable_analyticExpTerm
      (t := t') (le_of_lt (by linarith [h2s])) hsum_k1
  let d : ℕ → H := fun n => (-Complex.I) •
    analyticExpDerivTerm T (shiftedIterates v k) s n
  have htail : HasSum (fun n => d (n + 1))
      (analyticExp T (shiftedIterates v (k + 1)) s - d 0) := by
    convert hsum_next.hasSum using 1
    · funext n
      dsimp [d, analyticExpDerivTerm, analyticExpTerm, shiftedIterates]
      rw [show n + 1 + k = n + (k + 1) by omega]
      simp only [smul_smul]
      congr 1
      rw [Nat.factorial_succ]
      field_simp [Nat.factorial_ne_zero]
      push_cast
      ring_nf
      simp [Complex.I_sq]
    · simp [analyticExp, d, analyticExpDerivTerm]
  have hd : HasSum d ((-Complex.I) •
      (∑' n, analyticExpDerivTerm T (shiftedIterates v k) s n)) := by
    simpa [d] using hderiv.hasSum.const_smul (-Complex.I)
  have hd' : HasSum d (analyticExp T (shiftedIterates v (k + 1)) s) := by
    have htail0 : HasSum (fun n => d (n + 1))
        (analyticExp T (shiftedIterates v (k + 1)) s -
          ∑ i ∈ Finset.range 1, d i) := by
      simpa [d, analyticExpDerivTerm] using htail
    have htail' := (hasSum_nat_add_iff' (G := H) (f := d)
      (g := analyticExp T (shiftedIterates v (k + 1)) s) 1).mp htail0
    simpa [d, analyticExpDerivTerm, analyticExp] using htail'
  exact hd.unique hd'

lemma IsAnalyticVector.localAnalyticOrbit_at_exp
    {T : H →ₗ.[ℂ] H} {x : H} {v : ℕ → T.domain} (hv : IteratesSeq T x v)
    {t a : ℝ} (ht : 0 < t) (ha : |a| < t / 2)
    (hsum : Summable (fun n : ℕ => ‖(v n : H)‖ * t ^ n / n.factorial))
    (hsym : T.IsSymmetric)
    (hdense : (Submodule.span ℂ {x : H | T.IsAnalyticVector x}).topologicalClosure = ⊤) :
    Nonempty (LocalAnalyticOrbit T (analyticExp T v a)) := by
  have hdenseDomain : T.HasDenseDomain := hasDenseDomain_of_denseAnalyticVectors hdense
  have hT : T.IsClosable := hsym.isClosable hdenseDomain
  have hTcloseSym : T.closure.IsSymmetric := hsym.closure hdenseDomain
  have hTcloseDense : T.closure.HasDenseDomain := hdenseDomain.closure
  have hspan_le : Submodule.span ℂ {x : H | T.IsAnalyticVector x} ≤
      Submodule.span ℂ {x : H | T.closure.IsAnalyticVector x} := by
    apply Submodule.span_mono
    intro z hz
    exact IsAnalyticVector.for_closure hz
  have hclosedense :
      (Submodule.span ℂ {x : H | T.closure.IsAnalyticVector x}).topologicalClosure = ⊤ := by
    apply le_antisymm le_top
    exact hdense ▸ Submodule.topologicalClosure_mono hspan_le
  have hsabs : |a| < t / 2 := ha
  let t' : ℝ := (t + 2 * |a|) / 2
  have ht' : 0 < t' := by
    dsimp [t']
    linarith [ht, abs_nonneg a]
  have h2a : 2 * |a| < t' := by
    dsimp [t']
    linarith [hsabs]
  have ht't : t' < t := by
    dsimp [t']
    linarith [hsabs]
  have hs' : a ∈ Set.Ioo (-t' / 2) (t' / 2) := by
    change -t' / 2 < a ∧ a < t' / 2
    constructor <;> linarith [neg_le_abs a, le_abs_self a, h2a]
  have hsum_shift : ∀ k : ℕ, Summable (fun n : ℕ =>
      ‖(shiftedIterates v k n : H)‖ * t' ^ n / n.factorial) := by
    intro k
    exact summable_shifted_iterates (v := v) ht ht'.le ht't k hsum
  let w : ℕ → T.closure.domain := fun k =>
    ⟨analyticExp T (shiftedIterates v k) a,
      analyticExp_mem_closure_domain (IteratesSeq.shift hv k) hT hs' (hsum_shift k)⟩
  have hw : IteratesSeq T.closure (analyticExp T v a) w := by
    refine ⟨?_, fun k => ?_⟩
    · change analyticExp T (shiftedIterates v 0) a = analyticExp T v a
      congr 2
    · have happly := closure_analyticExp_apply (IteratesSeq.shift hv k) hT hs' (hsum_shift k)
      have ha_mem : a ∈ Set.Ioo (-t / 2) (t / 2) := by
        change -t / 2 < a ∧ a < t / 2
        exact ⟨by linarith [neg_le_abs a, ha], by linarith [le_abs_self a, ha]⟩
      have hshift := neg_I_smul_tsum_analyticExpDerivTerm_shift_eq hv ht ha_mem hsum k
      change analyticExp T (shiftedIterates v (k + 1)) a =
        T.closure ⟨analyticExp T (shiftedIterates v k) a, _⟩
      rw [happly, hshift]
  have hsum_half : Summable (fun k : ℕ =>
      ‖(shiftedIterates v 0 k : H)‖ * (t / 2) ^ k / k.factorial) := by
    exact summable_shifted_iterates (v := v) ht (by positivity) (by linarith) 0 hsum
  have hsum_w : Summable (fun k : ℕ => ‖(w k : H)‖ * (t / 2) ^ k / k.factorial) := by
    refine hsum_half.congr (fun k => ?_)
    have hnorm := analyticExp_norm_eq_norm hsym hdense (IteratesSeq.shift hv k) hs' (hsum_shift k)
    change ‖(shiftedIterates v 0 k : H)‖ * (t / 2) ^ k / k.factorial =
      ‖analyticExp T (shiftedIterates v k) a‖ * (t / 2) ^ k / k.factorial
    rw [hnorm]
    simp [shiftedIterates]
  have hTclose : T.closure.closure = T.closure := hT.closure_isClosed.closure_eq
  have hSclosable : T.closure.IsClosable := hT.closure_isClosed.isClosable
  have hr : 0 < (t / 2) / 2 := by linarith
  have happly_closure : ∀ (z : H) (hz : z ∈ T.closure.domain)
      (hz' : z ∈ T.closure.closure.domain),
      T.closure.closure ⟨z, hz'⟩ = T.closure ⟨z, hz⟩ := by
    intro z hz hz'
    have hgraph : (z, T.closure.closure ⟨z, hz'⟩) ∈ T.closure.graph := by
      have hgraph_eq : T.closure.closure.graph = T.closure.graph :=
        congrArg (fun R : H →ₗ.[ℂ] H => R.graph) hTclose
      exact hgraph_eq ▸ T.closure.closure.mem_graph ⟨z, hz'⟩
    exact T.closure.mem_graph_snd_inj' hgraph
      (T.closure.mem_graph ⟨z, hz⟩) rfl
  refine ⟨
    { radius := (t / 2) / 2
      radius_pos := hr
      toFun := fun s => analyticExp T.closure w s
      initial := analyticExp_zero hw
      mem_domain := fun s hs => by
        rw [abs_lt] at hs
        have hs' : s ∈ Set.Ioo (-(t / 2) / 2) ((t / 2) / 2) := by
          change -(t / 2) / 2 < s ∧ s < (t / 2) / 2
          exact ⟨by linarith [hs.1], by linarith [hs.2]⟩
        have hd := analyticExp_mem_closure_domain hw hSclosable hs' hsum_w
        simpa only [hTclose] using hd
      hasDerivAt := fun s hs => by
        rw [abs_lt] at hs
        have hs' : s ∈ Set.Ioo (-(t / 2) / 2) ((t / 2) / 2) := by
          change -(t / 2) / 2 < s ∧ s < (t / 2) / 2
          exact ⟨by linarith [hs.1], by linarith [hs.2]⟩
        have hd := analyticExp_hasDerivAt_eq_smul_closure hw hSclosable hs' hsum_w
        have hz : analyticExp T.closure w s ∈ T.closure.domain := by
          simpa only [hTclose] using analyticExp_mem_closure_domain hw hSclosable hs' hsum_w
        convert hd using 1
        congr 1
        exact (happly_closure _ hz
          (analyticExp_mem_closure_domain hw hSclosable hs' hsum_w)).symm
      , norm_eq := fun s hs => by
        rw [abs_lt] at hs
        have hs' : s ∈ Set.Ioo (-(t / 2) / 2) ((t / 2) / 2) := by
          change -(t / 2) / 2 < s ∧ s < (t / 2) / 2
          exact ⟨by linarith [hs.1], by linarith [hs.2]⟩
        exact analyticExp_norm_eq_norm hTcloseSym hclosedense hw hs' hsum_w }⟩

/-- The change-of-origin construction exposes the actual analytic-vector witness of the reached
state.  This is the recursive part of the finite-radius continuation argument: a local chart alone
does not provide enough data to apply the same construction again, whereas this theorem supplies
the shifted iterates and their smaller-radius factorial majorant for the closed operator. -/
lemma IsAnalyticVector.analyticExp_at_isAnalyticVector
    {T : H →ₗ.[ℂ] H} {x : H} {v : ℕ → T.domain} (hv : IteratesSeq T x v)
    {t a : ℝ} (ht : 0 < t) (ha : |a| < t / 2)
    (hsum : Summable (fun n : ℕ => ‖(v n : H)‖ * t ^ n / n.factorial))
    (hsym : T.IsSymmetric)
    (hdense : (Submodule.span ℂ {x : H | T.IsAnalyticVector x}).topologicalClosure = ⊤) :
    T.closure.IsAnalyticVector (analyticExp T v a) := by
  have hdenseDomain : T.HasDenseDomain := hasDenseDomain_of_denseAnalyticVectors hdense
  have hT : T.IsClosable := hsym.isClosable hdenseDomain
  have hspan_le : Submodule.span ℂ {x : H | T.IsAnalyticVector x} ≤
      Submodule.span ℂ {x : H | T.closure.IsAnalyticVector x} := by
    apply Submodule.span_mono
    intro z hz
    exact IsAnalyticVector.for_closure hz
  have hclosedense :
      (Submodule.span ℂ {x : H | T.closure.IsAnalyticVector x}).topologicalClosure = ⊤ := by
    apply le_antisymm le_top
    exact hdense ▸ Submodule.topologicalClosure_mono hspan_le
  let t' : ℝ := (t + 2 * |a|) / 2
  have ht' : 0 < t' := by
    dsimp [t']
    linarith [ht, abs_nonneg a]
  have ht't : t' < t := by
    dsimp [t']
    linarith [ha]
  have hsum_shift : ∀ k : ℕ, Summable (fun n : ℕ =>
      ‖(shiftedIterates v k n : H)‖ * t' ^ n / n.factorial) := by
    intro k
    exact summable_shifted_iterates (v := v) ht ht'.le ht't k hsum
  have hs' : a ∈ Set.Ioo (-t' / 2) (t' / 2) := by
    change -t' / 2 < a ∧ a < t' / 2
    have h2a : 2 * |a| < t' := by
      dsimp [t']
      linarith [ha]
    constructor <;> linarith [neg_le_abs a, le_abs_self a, h2a]
  let w : ℕ → T.closure.domain := fun k =>
    ⟨analyticExp T (shiftedIterates v k) a,
      analyticExp_mem_closure_domain (IteratesSeq.shift hv k) hT hs'
        (hsum_shift k)⟩
  have hw : IteratesSeq T.closure (analyticExp T v a) w := by
    refine ⟨?_, fun k => ?_⟩
    · change analyticExp T (shiftedIterates v 0) a = analyticExp T v a
      congr 2
    · have happly := closure_analyticExp_apply (IteratesSeq.shift hv k) hT hs'
        (hsum_shift k)
      have ha_mem : a ∈ Set.Ioo (-t / 2) (t / 2) := by
        change -t / 2 < a ∧ a < t / 2
        exact ⟨by linarith [neg_le_abs a, ha], by linarith [le_abs_self a, ha]⟩
      have hshift := neg_I_smul_tsum_analyticExpDerivTerm_shift_eq hv ht ha_mem hsum k
      change analyticExp T (shiftedIterates v (k + 1)) a =
        T.closure ⟨analyticExp T (shiftedIterates v k) a, _⟩
      rw [happly, hshift]
  have hsum_half : Summable (fun k : ℕ =>
      ‖(shiftedIterates v 0 k : H)‖ * (t / 2) ^ k / k.factorial) := by
    exact summable_shifted_iterates (v := v) ht (by positivity) (by linarith) 0 hsum
  have hsum_w : Summable (fun k : ℕ =>
      ‖(w k : H)‖ * (t / 2) ^ k / k.factorial) := by
    refine hsum_half.congr (fun k => ?_)
    have hnorm := analyticExp_norm_eq_norm hsym hdense (IteratesSeq.shift hv k) hs'
      (hsum_shift k)
    change ‖(shiftedIterates v 0 k : H)‖ * (t / 2) ^ k / k.factorial =
      ‖analyticExp T (shiftedIterates v k) a‖ * (t / 2) ^ k / k.factorial
    rw [hnorm]
    simp [shiftedIterates]
  exact ⟨w, hw, t / 2, by linarith, hsum_w⟩

/-- Sharp-radius form of `analyticExp_at_isAnalyticVector`: changing origin inside the
half-radius does not consume the analytic radius.  Every strictly smaller radius than the
original one remains available at the reached state.  This is the uniform-radius estimate used
to iterate local charts indefinitely. -/
lemma IsAnalyticVector.analyticExp_at_isAnalyticVector_witness_of_radius
    {T : H →ₗ.[ℂ] H} {x : H} {v : ℕ → T.domain} (hv : IteratesSeq T x v)
    {t a q : ℝ} (ht : 0 < t) (ha : |a| < t / 2) (hq : 0 < q) (hqt : q < t)
    (hsum : Summable (fun n : ℕ => ‖(v n : H)‖ * t ^ n / n.factorial))
    (hsym : T.IsSymmetric)
    (hdense : (Submodule.span ℂ {x : H | T.IsAnalyticVector x}).topologicalClosure = ⊤) :
    ∃ w : ℕ → T.closure.domain, IteratesSeq T.closure (analyticExp T v a) w ∧
      0 < q ∧ Summable (fun n : ℕ => ‖(w n : H)‖ * q ^ n / n.factorial) := by
  have hdenseDomain : T.HasDenseDomain := hasDenseDomain_of_denseAnalyticVectors hdense
  have hT : T.IsClosable := hsym.isClosable hdenseDomain
  have hspan_le : Submodule.span ℂ {x : H | T.IsAnalyticVector x} ≤
      Submodule.span ℂ {x : H | T.closure.IsAnalyticVector x} := by
    apply Submodule.span_mono
    intro z hz
    exact IsAnalyticVector.for_closure hz
  have hclosedense :
      (Submodule.span ℂ {x : H | T.closure.IsAnalyticVector x}).topologicalClosure = ⊤ := by
    apply le_antisymm le_top
    exact hdense ▸ Submodule.topologicalClosure_mono hspan_le
  let u : ℝ := (max (2 * |a|) q + t) / 2
  have h2a : 2 * |a| < t := by linarith [ha]
  have hmax : max (2 * |a|) q < t := (max_lt_iff).2 ⟨h2a, hqt⟩
  have hmax_nonneg : 0 ≤ max (2 * |a|) q :=
    le_trans (by positivity) (le_max_left _ _)
  have hqmax : q ≤ max (2 * |a|) q := le_max_right _ _
  have h2amax : 2 * |a| ≤ max (2 * |a|) q := le_max_left _ _
  have hu : 0 < u := by
    dsimp [u]
    linarith [ht, hmax_nonneg]
  have hqu : q < u := by
    dsimp [u]
    linarith [hmax, hqmax]
  have h2au : 2 * |a| < u := by
    dsimp [u]
    linarith [hmax, h2amax]
  have hut : u < t := by
    dsimp [u]
    linarith [hmax]
  have hs' : a ∈ Set.Ioo (-u / 2) (u / 2) := by
    change -u / 2 < a ∧ a < u / 2
    constructor <;> linarith [neg_le_abs a, le_abs_self a, h2au]
  have hsum_u : ∀ k : ℕ, Summable (fun n : ℕ =>
      ‖(shiftedIterates v k n : H)‖ * u ^ n / n.factorial) := by
    intro k
    exact summable_shifted_iterates (v := v) ht hu.le hut k hsum
  have hsum_q : ∀ k : ℕ, Summable (fun n : ℕ =>
      ‖(shiftedIterates v k n : H)‖ * q ^ n / n.factorial) := by
    intro k
    exact summable_shifted_iterates (v := v) ht (le_of_lt hq) hqt k hsum
  let w : ℕ → T.closure.domain := fun k =>
    ⟨analyticExp T (shiftedIterates v k) a,
      analyticExp_mem_closure_domain (IteratesSeq.shift hv k) hT hs'
        (hsum_u k)⟩
  have hw : IteratesSeq T.closure (analyticExp T v a) w := by
    refine ⟨?_, fun k => ?_⟩
    · change analyticExp T (shiftedIterates v 0) a = analyticExp T v a
      congr 2
    · have happly := closure_analyticExp_apply (IteratesSeq.shift hv k) hT hs'
        (hsum_u k)
      have ha_mem : a ∈ Set.Ioo (-t / 2) (t / 2) := by
        change -t / 2 < a ∧ a < t / 2
        exact ⟨by linarith [neg_le_abs a, ha], by linarith [le_abs_self a, ha]⟩
      have hshift := neg_I_smul_tsum_analyticExpDerivTerm_shift_eq hv ht ha_mem hsum k
      change analyticExp T (shiftedIterates v (k + 1)) a =
        T.closure ⟨analyticExp T (shiftedIterates v k) a, _⟩
      rw [happly, hshift]
  have hsum_w : Summable (fun k : ℕ =>
      ‖(w k : H)‖ * q ^ k / k.factorial) := by
    have hsum_shift_q := hsum_q
    refine (hsum_shift_q 0).congr (fun k => ?_)
    have hnorm := analyticExp_norm_eq_norm hsym hdense (IteratesSeq.shift hv k) hs'
      (hsum_u k)
    change ‖(shiftedIterates v 0 k : H)‖ * q ^ k / k.factorial =
      ‖analyticExp T (shiftedIterates v k) a‖ * q ^ k / k.factorial
    rw [hnorm]
    simp [shiftedIterates]
  exact ⟨w, hw, hq, hsum_w⟩

lemma IsAnalyticVector.analyticExp_at_isAnalyticVector_of_radius
    {T : H →ₗ.[ℂ] H} {x : H} {v : ℕ → T.domain} (hv : IteratesSeq T x v)
    {t a q : ℝ} (ht : 0 < t) (ha : |a| < t / 2) (hq : 0 < q) (hqt : q < t)
    (hsum : Summable (fun n : ℕ => ‖(v n : H)‖ * t ^ n / n.factorial))
    (hsym : T.IsSymmetric)
    (hdense : (Submodule.span ℂ {x : H | T.IsAnalyticVector x}).topologicalClosure = ⊤) :
    T.closure.IsAnalyticVector (analyticExp T v a) := by
  obtain ⟨w, hw, hq', hsum_w⟩ :=
    IsAnalyticVector.analyticExp_at_isAnalyticVector_witness_of_radius
      hv ht ha hq hqt hsum hsym hdense
  exact ⟨w, hw, q, hq', hsum_w⟩

/-! ### Gluing local charts

The following cover is deliberately an interface: the analytic change-of-origin estimate belongs
to the finite-radius part of Nelson's theorem, while the topological gluing is independent of it. -/

/-- A countable cover of `ℝ` by local analytic orbits, all based at states of the same norm as
`x`, agreeing pairwise on their overlaps. -/
structure LocalOrbitCover (T : H →ₗ.[ℂ] H) (x : H) where
  /-- The state each local chart is based at. -/
  state : ℕ → H
  /-- The real-time center of each local chart. -/
  center : ℕ → ℝ
  /-- The local analytic orbit chart based at `state n`. -/
  chart : ∀ n, LocalAnalyticOrbit T (state n)
  center_zero : center 0 = 0
  state_zero : state 0 = x
  state_norm : ∀ n, ‖state n‖ = ‖x‖
  cover : ∀ s : ℝ, ∃ n : ℕ, |s - center n| < (chart n).radius
  compatible : ∀ (m n : ℕ) (s : ℝ),
    |s - center m| < (chart m).radius → |s - center n| < (chart n).radius →
      chart m (s - center m) = chart n (s - center n)

/-! A cover may use smaller symmetric cores of its charts.  This avoids requiring compatibility on
the full overlap of two symmetric charts, which need not be contained in a recentered symmetric
domain. -/

/-- A `LocalOrbitCover` where compatibility is only required on a (possibly smaller) symmetric
core of each chart's radius. -/
structure LocalOrbitCoreCover (T : H →ₗ.[ℂ] H) (x : H) where
  /-- The state each local chart is based at. -/
  state : ℕ → H
  /-- The real-time center of each local chart. -/
  center : ℕ → ℝ
  /-- The local analytic orbit chart based at `state n`. -/
  chart : ∀ n, LocalAnalyticOrbit T (state n)
  /-- The radius of the (possibly smaller) core used for compatibility. -/
  coreRadius : ℕ → ℝ
  core_pos : ∀ n, 0 < coreRadius n
  core_le : ∀ n, coreRadius n ≤ (chart n).radius
  center_zero : center 0 = 0
  state_zero : state 0 = x
  state_norm : ∀ n, ‖state n‖ = ‖x‖
  cover : ∀ s : ℝ, ∃ n : ℕ, |s - center n| < coreRadius n
  compatible : ∀ (m n : ℕ) (s : ℝ),
    |s - center m| < coreRadius m → |s - center n| < coreRadius n →
      chart m (s - center m) = chart n (s - center n)

lemma exists_int_center_of_pos_step {δ R s : ℝ} (hδ : 0 < δ) (hδR : δ < R) :
    ∃ n : ℤ, |s - (n : ℝ) * δ| < R := by
  let n : ℤ := ⌊s / δ⌋
  have hfloor : (n : ℝ) ≤ s / δ := by
    dsimp [n]
    exact Int.floor_le _
  have hnext : s / δ < (n : ℝ) + 1 := by
    dsimp [n]
    exact Int.lt_floor_add_one _
  have hlow : (n : ℝ) * δ ≤ s := by
    have := (le_div_iff₀ hδ).mp hfloor
    simpa [mul_comm] using this
  have hupp : s < (n : ℝ) * δ + δ := by
    have := (div_lt_iff₀ hδ).mp hnext
    simpa [add_mul] using this
  refine ⟨n, ?_⟩
  have hnonneg : 0 ≤ s - (n : ℝ) * δ := sub_nonneg.mpr hlow
  rw [abs_of_nonneg hnonneg]
  linarith

/-! The purely one-dimensional part of integer-chart gluing.  If consecutive charts agree after
translation by `δ`, agreement propagates along the whole integer chain.  The endpoint hypotheses
are enough: the distance to the affine integer grid is convex, so every intermediate coordinate
remains in the same core. -/
omit [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] in
@[nolint unusedArguments]
lemma eq_of_adjacent_of_le
    {F : ℤ → ℝ → H} {δ R s : ℝ} (hδ : 0 < δ) (hR : 0 < R)
    (hadj : ∀ k : ℤ, ∀ z : ℝ, |z| < R →
      F k (δ + z) = F (k + 1) z)
    {m n : ℤ} (hmn : m ≤ n)
    (hm : |s - (m : ℝ) * δ| < R) (hn : |s - (n : ℝ) * δ| < R) :
    F m (s - (m : ℝ) * δ) = F n (s - (n : ℝ) * δ) := by
  have hinter : ∀ {k : ℤ}, m ≤ k → k ≤ n →
      |s - (k : ℝ) * δ| < R := by
    intro k hmk hkn
    have hmk' : (m : ℝ) ≤ (k : ℝ) := by exact_mod_cast hmk
    have hkn' : (k : ℝ) ≤ (n : ℝ) := by exact_mod_cast hkn
    have hmkδ : (m : ℝ) * δ ≤ (k : ℝ) * δ :=
      mul_le_mul_of_nonneg_right hmk' hδ.le
    have hknδ : (k : ℝ) * δ ≤ (n : ℝ) * δ :=
      mul_le_mul_of_nonneg_right hkn' hδ.le
    rw [abs_lt] at hm hn ⊢
    by_cases hsk : s < (k : ℝ) * δ
    · constructor
      · linarith [hn.1]
      · linarith
    · have hks : (k : ℝ) * δ ≤ s := le_of_not_gt hsk
      constructor
      · linarith
      · linarith [hm.2]
  have hchain : ∀ (k : ℤ), m ≤ k → k ≤ n → |s - (k : ℝ) * δ| < R →
      F m (s - (m : ℝ) * δ) = F k (s - (k : ℝ) * δ) := by
    intro k hmk
    refine Int.leInduction (motive := fun j _ =>
      j ≤ n → |s - (j : ℝ) * δ| < R →
        F m (s - (m : ℝ) * δ) = F j (s - (j : ℝ) * δ)) ?_ ?_ k hmk
    · intro _ _
      rfl
    · intro j hj ih hj1n hj1
      have hjn : j ≤ n := by omega
      have hj0 : |s - (j : ℝ) * δ| < R := hinter hj hjn
      have hprev := ih hjn hj0
      have hstep := hadj j (s - ((j + 1 : ℤ) : ℝ) * δ) hj1
      have hstep' : F j (s - (j : ℝ) * δ) =
          F (j + 1) (s - ((j + 1 : ℤ) : ℝ) * δ) := by
        convert hstep using 1
        push_cast
        ring
      exact hprev.trans hstep'
  exact hchain n hmn le_rfl hn

omit [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] in
lemma eq_of_adjacent
    {F : ℤ → ℝ → H} {δ R s : ℝ} (hδ : 0 < δ) (hR : 0 < R)
    (hadj : ∀ k : ℤ, ∀ z : ℝ, |z| < R →
      F k (δ + z) = F (k + 1) z)
    {m n : ℤ}
    (hm : |s - (m : ℝ) * δ| < R) (hn : |s - (n : ℝ) * δ| < R) :
    F m (s - (m : ℝ) * δ) = F n (s - (n : ℝ) * δ) := by
  rcases le_total m n with hmn | hnm
  · exact eq_of_adjacent_of_le hδ hR hadj hmn hm hn
  · exact (eq_of_adjacent_of_le hδ hR hadj hnm hn hm).symm

/-- Reindex a bi-infinite integer-indexed core cover by `ℕ`.  The reindexing is purely set-theoretic
and uses `Equiv.intEquivNat`; it lets the existing choice-based gluing implementation remain
backwards-compatible while continuation is naturally developed on integer time centers. -/
noncomputable def LocalOrbitCoreCover.ofIntIndex
    {T : H →ₗ.[ℂ] H} {x : H}
    (state : ℤ → H) (center coreRadius : ℤ → ℝ)
    (chart : ∀ n : ℤ, LocalAnalyticOrbit T (state n))
    (core_pos : ∀ n, 0 < coreRadius n)
    (core_le : ∀ n, coreRadius n ≤ (chart n).radius)
    (center_zero : center 0 = 0) (state_zero : state 0 = x)
    (state_norm : ∀ n, ‖state n‖ = ‖x‖)
    (cover : ∀ s : ℝ, ∃ n : ℤ, |s - center n| < coreRadius n)
    (compatible : ∀ (m n : ℤ) (s : ℝ),
      |s - center m| < coreRadius m → |s - center n| < coreRadius n →
      chart m (s - center m) = chart n (s - center n)) :
    LocalOrbitCoreCover T x where
  state := fun n => state (Equiv.intEquivNat.symm n)
  center := fun n => center (Equiv.intEquivNat.symm n)
  chart := fun n => chart (Equiv.intEquivNat.symm n)
  coreRadius := fun n => coreRadius (Equiv.intEquivNat.symm n)
  core_pos := fun n => core_pos _
  core_le := fun n => core_le _
  center_zero := by
    have hzero : Equiv.intEquivNat.symm 0 = (0 : ℤ) := by rfl
    simpa [hzero] using center_zero
  state_zero := by
    have hzero : Equiv.intEquivNat.symm 0 = (0 : ℤ) := by rfl
    simpa [hzero] using state_zero
  state_norm := fun n => state_norm _
  cover := by
    intro s
    obtain ⟨n, hn⟩ := cover s
    exact ⟨Equiv.intEquivNat n, by simpa only [Equiv.symm_apply_apply] using hn⟩
  compatible := by
    intro m n s hm hn
    exact compatible _ _ s hm hn

/-- Package the grid argument with the abstract core-cover certificate.  The analytic work needed
to construct the charts is intentionally not hidden here: callers only have to provide the local
adjacent equality, while this lemma supplies coverage and all non-adjacent compatibility. -/
noncomputable def LocalOrbitCoreCover.ofAdjacentIntIndex
    {T : H →ₗ.[ℂ] H} {x : H} {δ R : ℝ}
    (hδ : 0 < δ) (hδR : δ < R)
    (state : ℤ → H) (chart : ∀ n : ℤ, LocalAnalyticOrbit T (state n))
    (core_pos : 0 < R) (core_le : ∀ n : ℤ, R ≤ (chart n).radius)
    (state_zero : state 0 = x)
    (state_norm : ∀ n : ℤ, ‖state n‖ = ‖x‖)
    (hadj : ∀ n : ℤ, ∀ z : ℝ, |z| < R →
      chart n (δ + z) = chart (n + 1) z) :
    LocalOrbitCoreCover T x := by
  let center : ℤ → ℝ := fun n => (n : ℝ) * δ
  have hcenter_zero : center 0 = 0 := by
    dsimp [center]
    norm_num
  have hcover : ∀ s : ℝ, ∃ n : ℤ, |s - center n| < R := by
    intro s
    obtain ⟨n, hn⟩ := exists_int_center_of_pos_step hδ hδR
    exact ⟨n, by simpa [center] using hn⟩
  exact LocalOrbitCoreCover.ofIntIndex state center (fun _ => R) chart
    (fun _ => core_pos) core_le hcenter_zero state_zero state_norm hcover
    (fun m n s hm hn => eq_of_adjacent hδ core_pos hadj (by simpa [center] using hm)
      (by simpa [center] using hn))

/-- Restricts every chart of a core cover down to its core radius, forgetting the extra room
outside it. -/
noncomputable def LocalOrbitCoreCover.toLocalOrbitCover
    {T : H →ₗ.[ℂ] H} {x : H} (C : LocalOrbitCoreCover T x) : LocalOrbitCover T x where
  state := C.state
  center := C.center
  chart := fun n => (C.chart n).restrictTo (C.core_pos n) (C.core_le n)
  center_zero := C.center_zero
  state_zero := C.state_zero
  state_norm := C.state_norm
  cover := by
    intro s
    obtain ⟨n, hn⟩ := C.cover s
    exact ⟨n, hn⟩
  compatible := by
    intro m n s hm hn
    exact C.compatible m n s hm hn

/-- Glues a local orbit cover into a single global analytic orbit, choosing at each time the
chart that covers it. -/
noncomputable def LocalOrbitCover.toGlobal {T : H →ₗ.[ℂ] H} {x : H}
    (C : LocalOrbitCover T x) : GlobalAnalyticOrbit T x where
  toFun := fun s => C.chart (Classical.choose (C.cover s))
      (s - C.center (Classical.choose (C.cover s)))
  initial := by
    let n : ℕ := Classical.choose (C.cover 0)
    have hn : |0 - C.center n| < (C.chart n).radius := Classical.choose_spec (C.cover 0)
    have h0 : |0 - C.center 0| < (C.chart 0).radius := by
      simpa [C.center_zero] using (C.chart 0).radius_pos
    have hcompat := C.compatible 0 n 0 h0 hn
    calc
      C.chart (Classical.choose (C.cover 0))
          (0 - C.center (Classical.choose (C.cover 0))) = C.chart 0 (0 - C.center 0) := by
            simpa [n] using hcompat.symm
      _ = C.state 0 := by simpa [C.center_zero] using (C.chart 0).initial
      _ = x := C.state_zero
  mem_domain := by
    intro s
    let n : ℕ := Classical.choose (C.cover s)
    have hn : |s - C.center n| < (C.chart n).radius := Classical.choose_spec (C.cover s)
    exact (C.chart n).mem_domain (s - C.center n) hn
  hasDerivAt := by
    intro s
    let n : ℕ := Classical.choose (C.cover s)
    have hn : |s - C.center n| < (C.chart n).radius := Classical.choose_spec (C.cover s)
    have hsI : s ∈ Set.Ioo (C.center n - (C.chart n).radius)
        (C.center n + (C.chart n).radius) := by
      change C.center n - (C.chart n).radius < s ∧
        s < C.center n + (C.chart n).radius
      rw [abs_lt] at hn
      constructor <;> linarith
    have hlocal := (C.chart n).hasDerivAt (s - C.center n) hn
    have hcomp := hlocal.comp_add_const s (-C.center n)
    have hevent : ∀ᶠ q : ℝ in 𝓝 s,
        (fun r : ℝ => C.chart (Classical.choose (C.cover r))
            (r - C.center (Classical.choose (C.cover r)))) q =
          (fun r : ℝ => C.chart n (r + -C.center n)) q := by
      filter_upwards [isOpen_Ioo.mem_nhds hsI] with q hq
      have hq' : |q - C.center n| < (C.chart n).radius := by
        rw [abs_lt]
        change C.center n - (C.chart n).radius < q ∧
          q < C.center n + (C.chart n).radius at hq
        constructor <;> linarith
      have hchosen := Classical.choose_spec (C.cover q)
      simpa [sub_eq_add_neg] using
        (C.compatible n (Classical.choose (C.cover q)) q hq' hchosen).symm
    have hderiv := hcomp.congr_of_eventuallyEq hevent
    convert hderiv using 1
  norm_eq := by
    intro s
    let n : ℕ := Classical.choose (C.cover s)
    have hn : |s - C.center n| < (C.chart n).radius := Classical.choose_spec (C.cover s)
    calc
      ‖C.chart (Classical.choose (C.cover s))
          (s - C.center (Classical.choose (C.cover s)))‖ = ‖C.state n‖ :=
            (C.chart n).norm_eq (s - C.center n) hn
      _ = ‖x‖ := C.state_norm n

/-- Glues a core cover into a single global analytic orbit, via its underlying `LocalOrbitCover`. -/
noncomputable def LocalOrbitCoreCover.toGlobal {T : H →ₗ.[ℂ] H} {x : H}
    (C : LocalOrbitCoreCover T x) : GlobalAnalyticOrbit T x :=
  C.toLocalOrbitCover.toGlobal

omit [CompleteSpace H] in
@[nolint unusedArguments]
lemma LocalOrbitCoreCover.toGlobal_nonempty {T : H →ₗ.[ℂ] H} {x : H}
    (C : LocalOrbitCoreCover T x) : Nonempty (GlobalAnalyticOrbit T x) :=
  ⟨C.toGlobal⟩

omit [CompleteSpace H] in
@[nolint unusedArguments]
lemma LocalOrbitCover.toGlobal_nonempty {T : H →ₗ.[ℂ] H} {x : H}
    (C : LocalOrbitCover T x) : Nonempty (GlobalAnalyticOrbit T x) :=
  ⟨C.toGlobal⟩

omit [CompleteSpace H] in
/-- A global orbit for the closure of a closable operator is also a global orbit for the original
operator.  The only issue is the dependent domain proof in the differential equation; the closed
graph identity `T.closure.closure = T.closure` resolves it explicitly. -/
@[nolint unusedArguments]
lemma of_closure {T : H →ₗ.[ℂ] H} {x : H} (hT : T.IsClosable)
    (U : GlobalAnalyticOrbit T.closure x) : Nonempty (GlobalAnalyticOrbit T x) := by
  have hclosed : T.closure.closure = T.closure := hT.closure_isClosed.closure_eq
  have happly : ∀ (z : H) (hz : z ∈ T.closure.domain)
      (hz' : z ∈ T.closure.closure.domain),
      T.closure.closure ⟨z, hz'⟩ = T.closure ⟨z, hz⟩ := by
    intro z hz hz'
    have hgraph : (z, T.closure.closure ⟨z, hz'⟩) ∈ T.closure.graph := by
      have hgraph_eq : T.closure.closure.graph = T.closure.graph :=
        congrArg (fun R : H →ₗ.[ℂ] H => R.graph) hclosed
      exact hgraph_eq ▸ T.closure.closure.mem_graph ⟨z, hz'⟩
    exact T.closure.mem_graph_snd_inj' hgraph
      (T.closure.mem_graph ⟨z, hz⟩) rfl
  refine ⟨
    { toFun := U
      initial := U.initial
      mem_domain := fun s => by
        simpa only [hclosed] using U.mem_domain s
      hasDerivAt := fun s => by
        have hz' : U s ∈ T.closure.closure.domain := U.mem_domain s
        have hz : U s ∈ T.closure.domain := by
          simpa only [hclosed] using hz'
        have hd := U.hasDerivAt s
        convert hd using 1
        congr 1
        exact (happly _ hz hz').symm
      norm_eq := U.norm_eq }⟩

omit [CompleteSpace H] in
@[nolint unusedArguments]
lemma inner_deficiency_eq_zero
    {T : H →ₗ.[ℂ] H} {x : H} (U : GlobalAnalyticOrbit T x) {y : H}
    (hy : y ∈ (T.closure - Complex.I • 1).toFun.rangeᗮ) :
    ⟪y, x⟫_ℂ = 0 := by
  let f : ℝ → ℂ := fun s => ⟪y, U s⟫_ℂ
  let g : ℝ → ℂ := fun s => (Real.exp s : ℂ) * f s
  have hg : ∀ s : ℝ, HasDerivAt g 0 s := by
    intro s
    have hdom : U s ∈ T.closure.domain := U.mem_domain s
    let z : (T.closure - Complex.I • 1).domain :=
      ⟨U s, by
        rw [sub_domain]
        exact ⟨hdom, by simp⟩⟩
    have horth : ⟪y, T.closure ⟨U s, hdom⟩ -
        Complex.I • U s⟫_ℂ = 0 := by
      have hz := (Submodule.mem_orthogonal' _ y).mp hy
        ((T.closure - Complex.I • 1).toFun z) ⟨z, rfl⟩
      simpa [z, sub_apply] using hz
    have hrelation : ⟪y, T.closure ⟨U s, hdom⟩⟫_ℂ =
        Complex.I * ⟪y, U s⟫_ℂ := by
      rw [inner_sub_right, inner_smul_right] at horth
      exact sub_eq_zero.mp horth
    have hf0 : HasDerivAt (fun r : ℝ => ⟪y, U r⟫_ℂ)
        (-⟪y, U s⟫_ℂ) s := by
      have hinner := (hasDerivAt_const (x := s) y).inner ℂ (U.hasDerivAt s)
      convert hinner using 1
      · rfl
      · simp only [inner_zero_left, inner_smul_right]
        rw [hrelation]
        ring_nf
        rw [Complex.I_sq]
        simp
    have hf : HasDerivAt f (-f s) s := by
      simpa [f] using hf0
    have he : HasDerivAt (fun r : ℝ => (Real.exp r : ℂ)) (Real.exp s) s :=
      (Real.hasDerivAt_exp s).ofReal_comp
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
      ‖g (-(n : ℝ))‖ = Real.exp (-(n : ℝ)) * ‖⟪y, U (-(n : ℝ))⟫_ℂ‖ := by
        dsimp [g, f]
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos (Real.exp_pos _)]
      _ ≤ Real.exp (-(n : ℝ)) * (‖y‖ * ‖U (-(n : ℝ))‖) := by
        gcongr
        exact norm_inner_le_norm _ _
      _ = Real.exp (-(n : ℝ)) * (‖y‖ * ‖x‖) := by
        rw [U.norm_eq]
  have hlim : Filter.Tendsto (fun n : ℕ => g (-(n : ℝ))) atTop (𝓝 0) :=
    (tendsto_zero_iff_norm_tendsto_zero).2 hnorm_lim
  have hconst_zero : g 0 = 0 := by
    have hc : Tendsto (fun _ : ℕ => g 0) atTop (𝓝 0) :=
      hlim.congr' (Filter.Eventually.of_forall fun n => hconst (-(n : ℝ)))
    exact (tendsto_nhds_unique hc tendsto_const_nhds).symm
  simpa [g, f, U.initial] using hconst_zero

omit [CompleteSpace H] in
@[nolint unusedArguments]
lemma inner_deficiency_eq_zero_neg
    {T : H →ₗ.[ℂ] H} {x : H} (U : GlobalAnalyticOrbit T x) {y : H}
    (hy : y ∈ (T.closure - (-Complex.I) • 1).toFun.rangeᗮ) :
    ⟪y, x⟫_ℂ = 0 := by
  let f : ℝ → ℂ := fun s => ⟪y, U s⟫_ℂ
  let g : ℝ → ℂ := fun s => (Real.exp (-s) : ℂ) * f s
  have hg : ∀ s : ℝ, HasDerivAt g 0 s := by
    intro s
    have hdom : U s ∈ T.closure.domain := U.mem_domain s
    let z : (T.closure - (-Complex.I) • 1).domain :=
      ⟨U s, by
        rw [sub_domain]
        exact ⟨hdom, by simp⟩⟩
    have horth : ⟪y, T.closure ⟨U s, hdom⟩ -
        (-Complex.I) • U s⟫_ℂ = 0 := by
      have hz := (Submodule.mem_orthogonal' _ y).mp hy
        ((T.closure - (-Complex.I) • 1).toFun z) ⟨z, rfl⟩
      simpa [z, sub_apply] using hz
    have hrelation : ⟪y, T.closure ⟨U s, hdom⟩⟫_ℂ =
        (-Complex.I) * ⟪y, U s⟫_ℂ := by
      rw [inner_sub_right, inner_smul_right] at horth
      exact sub_eq_zero.mp horth
    have hf0 : HasDerivAt (fun r : ℝ => ⟪y, U r⟫_ℂ)
        (⟪y, U s⟫_ℂ) s := by
      have hinner := (hasDerivAt_const (x := s) y).inner ℂ (U.hasDerivAt s)
      convert hinner using 1
      · rfl
      · simp only [inner_zero_left, inner_smul_right]
        rw [hrelation]
        ring_nf
        rw [Complex.I_sq]
        simp
    have hf : HasDerivAt f (f s) s := by
      simpa [f] using hf0
    have he : HasDerivAt (fun r : ℝ => (Real.exp (-r) : ℂ))
        (-Real.exp (-s)) s := by
      have hreal := (Real.hasDerivAt_exp (-s)).scomp s
        (hasDerivAt_id' (𝕜 := ℝ) s).neg
      convert hreal.ofReal_comp using 1
      · funext r
        rfl
      · simp
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
      ‖g (n : ℝ)‖ = Real.exp (-(n : ℝ)) * ‖⟪y, U (n : ℝ)⟫_ℂ‖ := by
        dsimp [g, f]
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos (Real.exp_pos _)]
      _ ≤ Real.exp (-(n : ℝ)) * (‖y‖ * ‖U (n : ℝ)‖) := by
        gcongr
        exact norm_inner_le_norm _ _
      _ = Real.exp (-(n : ℝ)) * (‖y‖ * ‖x‖) := by
        rw [U.norm_eq]
  have hlim : Filter.Tendsto (fun n : ℕ => g (n : ℝ)) atTop (𝓝 0) :=
    (tendsto_zero_iff_norm_tendsto_zero).2 hnorm_lim
  have hconst_zero : g 0 = 0 := by
    have hc : Tendsto (fun _ : ℕ => g 0) atTop (𝓝 0) :=
      hlim.congr' (Filter.Eventually.of_forall fun n => hconst (n : ℝ))
    exact (tendsto_nhds_unique hc tendsto_const_nhds).symm
  simpa [g, f, U.initial] using hconst_zero

end GlobalAnalyticOrbit

end LinearPMap
