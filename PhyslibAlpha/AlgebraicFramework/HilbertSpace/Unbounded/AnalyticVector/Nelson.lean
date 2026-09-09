/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.AlgebraicFramework.HilbertSpace.Unbounded.AnalyticVector.Local

/-!
# Analytic vectors for an unbounded operator (part 3 of 3: gluing and Nelson's criterion)

Continuation of `AnalyticVector/Local.lean`; this part glues local charts into a global orbit and
concludes Nelson's single-operator analytic-vector essential-self-adjointness criterion.

## Main results

- `IsSymmetric.isEssentiallySelfAdjoint_of_denseAnalyticVectors_of_globalOrbit` : a dense family
  of analytic vectors proves essential self-adjointness once its local exponential orbits have
  been patched to global norm-preserving orbits.
- `IsSymmetric.isEssentiallySelfAdjoint_of_denseAnalyticVectors` : **Nelson's analytic-vector
  theorem, single-operator case** (Reed–Simon Vol. II, Theorem X.39, first half). A symmetric
  operator with a dense set of analytic vectors is essentially self-adjoint.
-/

@[expose] public section

noncomputable section

namespace LinearPMap

open scoped InnerProductSpace Topology
open Filter

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]


/-- Every entire vector supplies a `GlobalAnalyticOrbit` once the operator is known to be
symmetric on a dense domain.  This packages the global case through the same certificate used by
the finite-radius Nelson argument. -/
lemma IsEntireVector.globalAnalyticOrbit
    {T : H →ₗ.[ℂ] H} {x : H} (h : T.IsEntireVector x)
    (hsym : T.IsSymmetric)
    (hdense : (Submodule.span ℂ {x : H | T.IsAnalyticVector x}).topologicalClosure = ⊤) :
    Nonempty (GlobalAnalyticOrbit T x) := by
  obtain ⟨v, hv, hall⟩ := h
  have hdenseDomain : T.HasDenseDomain := hasDenseDomain_of_denseAnalyticVectors hdense
  have hT : T.IsClosable := hsym.isClosable hdenseDomain
  refine ⟨
    { toFun := fun s => analyticExp T v s
      initial := analyticExp_zero hv
      mem_domain := fun s => analyticExp_mem_closure_domain_of_entire hv hall hT s
      hasDerivAt := fun s => analyticExp_hasDerivAt_of_entire hv hall hT s
      norm_eq := ?_ }⟩
  intro s
  let t : ℝ := 2 * |s| + 1
  have ht : 0 < t := by
    dsimp [t]
    positivity
  have hs : s ∈ Set.Ioo (-t / 2) (t / 2) := by
    dsimp [t]
    constructor <;> linarith [neg_le_abs s, le_abs_self s]
  exact LinearPMap.analyticExp_norm_eq_norm hsym hdense hv hs (hall t ht)

/-- The local exponential series attached to an explicit analytic witness is a local orbit
certificate.  Keeping the witness in the constructor is important for continuation: the next
state is the value of this very series, rather than an unspecified member of a `Nonempty` proof. -/
noncomputable def IsAnalyticVector.localAnalyticOrbitOfWitness
    {T : H →ₗ.[ℂ] H} {x : H} (v : ℕ → T.domain) (hv : IteratesSeq T x v)
    {t : ℝ} (ht : 0 < t)
    (hsum : Summable (fun n : ℕ => ‖(v n : H)‖ * t ^ n / n.factorial))
    (hsym : T.IsSymmetric)
    (hdense : (Submodule.span ℂ {x : H | T.IsAnalyticVector x}).topologicalClosure = ⊤) :
    LocalAnalyticOrbit T x := by
  have hdenseDomain : T.HasDenseDomain := hasDenseDomain_of_denseAnalyticVectors hdense
  have hT : T.IsClosable := hsym.isClosable hdenseDomain
  refine
    { radius := t / 2
      radius_pos := by linarith
      toFun := fun s => analyticExp T v s
      initial := analyticExp_zero hv
      mem_domain := ?_
      hasDerivAt := ?_
      norm_eq := ?_ }
  · intro s hs
    have hs' : s ∈ Set.Ioo (-t / 2) (t / 2) := by
      rw [abs_lt] at hs
      exact ⟨by simpa only [neg_div] using hs.1, hs.2⟩
    exact analyticExp_mem_closure_domain hv hT hs' hsum
  · intro s hs
    have hs' : s ∈ Set.Ioo (-t / 2) (t / 2) := by
      rw [abs_lt] at hs
      exact ⟨by simpa only [neg_div] using hs.1, hs.2⟩
    exact analyticExp_hasDerivAt_eq_smul_closure hv hT hs' hsum
  · intro s hs
    have hs' : s ∈ Set.Ioo (-t / 2) (t / 2) := by
      rw [abs_lt] at hs
      exact ⟨by simpa only [neg_div] using hs.1, hs.2⟩
    exact LinearPMap.analyticExp_norm_eq_norm hsym hdense hv hs' hsum

/- The local exponential series attached to an analytic vector is a local orbit certificate.
The radius is halved to leave room for termwise differentiation and passage to the closed graph. -/
lemma IsAnalyticVector.localAnalyticOrbit
    {T : H →ₗ.[ℂ] H} {x : H} (h : T.IsAnalyticVector x)
    (hsym : T.IsSymmetric)
    (hdense : (Submodule.span ℂ {x : H | T.IsAnalyticVector x}).topologicalClosure = ⊤) :
    Nonempty (LocalAnalyticOrbit T x) := by
  obtain ⟨v, hv, t, ht, hsum⟩ := h
  exact ⟨IsAnalyticVector.localAnalyticOrbitOfWitness v hv ht hsum hsym hdense⟩

/-- A fresh local chart at a reached state can be chosen with any radius strictly below the
original analytic radius (up to the usual local half-radius).  The sharp-radius witness is first
constructed for the closed operator, then its local certificate is transported back to `T`. -/
lemma IsAnalyticVector.localAnalyticOrbit_at_exp_of_radius
    {T : H →ₗ.[ℂ] H} {x : H} {v : ℕ → T.domain} (hv : IteratesSeq T x v)
    {t a q : ℝ} (ht : 0 < t) (ha : |a| < t / 2) (hq : 0 < q) (hqt : q < t)
    (hsum : Summable (fun n : ℕ => ‖(v n : H)‖ * t ^ n / n.factorial))
    (hsym : T.IsSymmetric)
    (hdense : (Submodule.span ℂ {x : H | T.IsAnalyticVector x}).topologicalClosure = ⊤) :
    Nonempty (LocalAnalyticOrbit T (analyticExp T v a)) := by
  have hdenseDomain : T.HasDenseDomain := hasDenseDomain_of_denseAnalyticVectors hdense
  have hT : T.IsClosable := hsym.isClosable hdenseDomain
  have hclosedSym : T.closure.IsSymmetric := hsym.closure hdenseDomain
  have hspan_le : Submodule.span ℂ {x : H | T.IsAnalyticVector x} ≤
      Submodule.span ℂ {x : H | T.closure.IsAnalyticVector x} := by
    apply Submodule.span_mono
    intro z hz
    exact IsAnalyticVector.for_closure hz
  have hclosedense :
      (Submodule.span ℂ {x : H | T.closure.IsAnalyticVector x}).topologicalClosure = ⊤ := by
    apply le_antisymm le_top
    exact hdense ▸ Submodule.topologicalClosure_mono hspan_le
  have hy : T.closure.IsAnalyticVector (analyticExp T v a) :=
    GlobalAnalyticOrbit.IsAnalyticVector.analyticExp_at_isAnalyticVector_of_radius
      hv ht ha hq hqt hsum hsym hdense
  obtain ⟨U⟩ := IsAnalyticVector.localAnalyticOrbit hy hclosedSym hclosedense
  exact LocalAnalyticOrbit.of_closure hT U

/-- Advance a proof-relevant analytic witness by a prescribed real step.  The new radius is chosen
as the midpoint of a fixed lower bound and the old radius; consequently repeated advancement
preserves a uniform positive lower bound instead of consuming the radius geometrically. -/
noncomputable def AnalyticVectorWitness.advance
    {T : H →ₗ.[ℂ] H} (hclosed : T.closure = T)
    (hsym : T.IsSymmetric)
    (hdense : (Submodule.span ℂ {x : H | T.IsAnalyticVector x}).topologicalClosure = ⊤)
    (W : AnalyticVectorWitness T) {r a : ℝ}
    (hr : 0 < r) (hrW : r < W.radius) (ha : |a| < W.radius / 2) :
    AnalyticVectorWitness T := by
  let q : ℝ := (r + W.radius) / 2
  have hq : 0 < q := by
    dsimp [q]
    linarith [hr, W.radius_pos]
  have hqr : r < q := by
    dsimp [q]
    linarith
  have hqW : q < W.radius := by
    dsimp [q]
    linarith
  have hex : ∃ w : ℕ → T.domain,
      IteratesSeq T (analyticExp T W.iterates a) w ∧
        Summable (fun n : ℕ => ‖(w n : H)‖ * q ^ n / n.factorial) := by
    obtain ⟨w, hw, hq', hsum_w⟩ :=
      GlobalAnalyticOrbit.IsAnalyticVector.analyticExp_at_isAnalyticVector_witness_of_radius
        W.iterates_spec W.radius_pos ha hq hqW W.summable hsym hdense
    have hdom : T.closure.domain = T.domain := congrArg LinearPMap.domain hclosed
    let wT : ℕ → T.domain := fun n =>
      ⟨(w n : H), hdom ▸ (w n).property⟩
    have happly : ∀ (z : H) (hz : z ∈ T.domain) (hz' : z ∈ T.closure.domain),
        T.closure ⟨z, hz'⟩ = T ⟨z, hz⟩ := by
      intro z hz hz'
      have hgraph : (z, T.closure ⟨z, hz'⟩) ∈ T.graph := by
        have hgraph_eq : T.closure.graph = T.graph :=
          congrArg (fun R : H →ₗ.[ℂ] H => R.graph) hclosed
        exact hgraph_eq ▸ T.closure.mem_graph ⟨z, hz'⟩
      exact T.mem_graph_snd_inj' hgraph (T.mem_graph ⟨z, hz⟩) rfl
    have hwT : IteratesSeq T (analyticExp T W.iterates a) wT := by
      refine ⟨?_, fun n => ?_⟩
      · change (w 0 : H) = analyticExp T W.iterates a
        exact hw.1
      · change (w (n + 1) : H) = T (wT n)
        calc
          (w (n + 1) : H) = T.closure (w n) := hw.2 n
          _ = T (wT n) := happly (w n : H) (wT n).property (w n).property
    have hsum_wT : Summable
        (fun n : ℕ => ‖(wT n : H)‖ * q ^ n / n.factorial) := by
      change Summable (fun n : ℕ => ‖(w n : H)‖ * q ^ n / n.factorial)
      exact hsum_w
    exact ⟨wT, hwT, hsum_wT⟩
  let wT : ℕ → T.domain := Classical.choose hex
  have hwT : IteratesSeq T (analyticExp T W.iterates a) wT :=
    (Classical.choose_spec hex).1
  have hsum_wT : Summable (fun n : ℕ => ‖(wT n : H)‖ * q ^ n / n.factorial) :=
    (Classical.choose_spec hex).2
  exact ⟨analyticExp T W.iterates a, wT, hwT, q, hq, hsum_wT⟩

lemma AnalyticVectorWitness.advance_radius
    {T : H →ₗ.[ℂ] H} (hclosed : T.closure = T)
    (hsym : T.IsSymmetric)
    (hdense : (Submodule.span ℂ {x : H | T.IsAnalyticVector x}).topologicalClosure = ⊤)
    (W : AnalyticVectorWitness T) {r a : ℝ}
    (hr : 0 < r) (hrW : r < W.radius) (ha : |a| < W.radius / 2) :
    (W.advance hclosed hsym hdense hr hrW ha).radius = (r + W.radius) / 2 := by
  rfl

lemma AnalyticVectorWitness.advance_norm
    {T : H →ₗ.[ℂ] H} (hclosed : T.closure = T)
    (hsym : T.IsSymmetric)
    (hdense : (Submodule.span ℂ {x : H | T.IsAnalyticVector x}).topologicalClosure = ⊤)
    (W : AnalyticVectorWitness T) {r a : ℝ}
    (hr : 0 < r) (hrW : r < W.radius) (ha : |a| < W.radius / 2) :
    ‖(W.advance hclosed hsym hdense hr hrW ha).state‖ = ‖W.state‖ := by
  have ha' : a ∈ Set.Ioo (-W.radius / 2) (W.radius / 2) := by
    change -W.radius / 2 < a ∧ a < W.radius / 2
    rcases (abs_lt.mp ha) with ⟨ha₁, ha₂⟩
    exact ⟨by linarith [ha₁], by linarith [ha₂]⟩
  have hnorm := analyticExp_norm_eq_norm hsym hdense W.iterates_spec ha' W.summable
  simpa [AnalyticVectorWitness.advance] using hnorm

/-- A two-sided line of witnesses with a fixed lower-radius invariant.  Positive indices advance
by `δ`, negative indices by `-δ`; the midpoint choice in `advance` makes the invariant stable in
both directions. -/
noncomputable def AnalyticVectorWitness.uniformIntegerLineData
    {T : H →ₗ.[ℂ] H} (hclosed : T.closure = T)
    (hsym : T.IsSymmetric)
    (hdense : (Submodule.span ℂ {x : H | T.IsAnalyticVector x}).topologicalClosure = ⊤)
    (W0 : AnalyticVectorWitness T) {r δ : ℝ}
    (hr : 0 < r) (hrW0 : r < W0.radius)
    (hδ : 0 < δ) (h2δ : 2 * δ < r) :
    ℤ → {W : AnalyticVectorWitness T // r < W.radius ∧ ‖W.state‖ = ‖W0.state‖} := by
  let motive : ℤ → Type _ := fun _ =>
    {W : AnalyticVectorWitness T // r < W.radius ∧ ‖W.state‖ = ‖W0.state‖}
  let base : motive 0 := ⟨W0, hrW0, rfl⟩
  let succ : ∀ k : ℤ, 0 ≤ k → motive k → motive (k + 1) := fun _ _ ih => by
    have ha : |δ| < ih.1.radius / 2 := by
      rw [abs_of_pos hδ]
      linarith [ih.2.1]
    let W := AnalyticVectorWitness.advance hclosed hsym hdense ih.1 hr ih.2.1 ha
    refine ⟨W, ?_, ?_⟩
    rw [AnalyticVectorWitness.advance_radius hclosed hsym hdense ih.1 hr ih.2.1 ha]
    · linarith [ih.2.1]
    · exact (AnalyticVectorWitness.advance_norm hclosed hsym hdense ih.1 hr ih.2.1 ha).trans ih.2.2
  let pred : ∀ k : ℤ, k ≤ 0 → motive k → motive (k - 1) := fun _ _ ih => by
    have ha : |-δ| < ih.1.radius / 2 := by
      rw [abs_neg, abs_of_pos hδ]
      linarith [ih.2.1]
    let W := AnalyticVectorWitness.advance hclosed hsym hdense ih.1 hr ih.2.1 ha
    refine ⟨W, ?_, ?_⟩
    rw [AnalyticVectorWitness.advance_radius hclosed hsym hdense ih.1 hr ih.2.1 ha]
    · linarith [ih.2.1]
    · exact (AnalyticVectorWitness.advance_norm hclosed hsym hdense ih.1 hr ih.2.1 ha).trans ih.2.2
  exact fun n => Int.inductionOn' (motive := motive) n 0 base succ pred

/-- The two-sided line of witnesses underlying `uniformIntegerLineData`. -/
noncomputable def AnalyticVectorWitness.uniformIntegerLine
    {T : H →ₗ.[ℂ] H} (hclosed : T.closure = T)
    (hsym : T.IsSymmetric)
    (hdense : (Submodule.span ℂ {x : H | T.IsAnalyticVector x}).topologicalClosure = ⊤)
    (W0 : AnalyticVectorWitness T) {r δ : ℝ}
    (hr : 0 < r) (hrW0 : r < W0.radius)
    (hδ : 0 < δ) (h2δ : 2 * δ < r) :
    ℤ → AnalyticVectorWitness T :=
  fun n => (AnalyticVectorWitness.uniformIntegerLineData hclosed hsym hdense W0
    hr hrW0 hδ h2δ n).1

lemma AnalyticVectorWitness.uniformIntegerLine_succ_of_nonneg
    {T : H →ₗ.[ℂ] H} (hclosed : T.closure = T)
    (hsym : T.IsSymmetric)
    (hdense : (Submodule.span ℂ {x : H | T.IsAnalyticVector x}).topologicalClosure = ⊤)
    (W0 : AnalyticVectorWitness T) {r δ : ℝ}
    (hr : 0 < r) (hrW0 : r < W0.radius)
    (hδ : 0 < δ) (h2δ : 2 * δ < r) {n : ℤ} (hn : 0 ≤ n) :
    (AnalyticVectorWitness.uniformIntegerLine hclosed hsym hdense W0
      hr hrW0 hδ h2δ (n + 1)).state =
      analyticExp T (AnalyticVectorWitness.uniformIntegerLine hclosed hsym hdense W0
      hr hrW0 hδ h2δ n).iterates δ := by
  simp [AnalyticVectorWitness.uniformIntegerLine,
    AnalyticVectorWitness.uniformIntegerLineData,
    Int.inductionOn'_add_one, hn]
  rfl

lemma AnalyticVectorWitness.uniformIntegerLine_pred_of_nonpos
    {T : H →ₗ.[ℂ] H} (hclosed : T.closure = T)
    (hsym : T.IsSymmetric)
    (hdense : (Submodule.span ℂ {x : H | T.IsAnalyticVector x}).topologicalClosure = ⊤)
    (W0 : AnalyticVectorWitness T) {r δ : ℝ}
    (hr : 0 < r) (hrW0 : r < W0.radius)
    (hδ : 0 < δ) (h2δ : 2 * δ < r) {n : ℤ} (hn : n ≤ 0) :
    (AnalyticVectorWitness.uniformIntegerLine hclosed hsym hdense W0
      hr hrW0 hδ h2δ (n - 1)).state =
      analyticExp T (AnalyticVectorWitness.uniformIntegerLine hclosed hsym hdense W0
        hr hrW0 hδ h2δ n).iterates (-δ) := by
  simp [AnalyticVectorWitness.uniformIntegerLine,
    AnalyticVectorWitness.uniformIntegerLineData,
    Int.inductionOn'_sub_one, hn]
  rfl

lemma AnalyticVectorWitness.uniformIntegerLine_step
    {T : H →ₗ.[ℂ] H} (hclosed : T.closure = T)
    (hsym : T.IsSymmetric)
    (hdense : (Submodule.span ℂ {x : H | T.IsAnalyticVector x}).topologicalClosure = ⊤)
    (W0 : AnalyticVectorWitness T) {r δ : ℝ}
    (hr : 0 < r) (hrW0 : r < W0.radius)
    (hδ : 0 < δ) (h4δ : 4 * δ < r) {n : ℤ} :
    (AnalyticVectorWitness.uniformIntegerLine hclosed hsym hdense W0
      hr hrW0 hδ (by linarith) (n + 1)).state =
      analyticExp T (AnalyticVectorWitness.uniformIntegerLine hclosed hsym hdense W0
        hr hrW0 hδ (by linarith) n).iterates δ := by
  let W : ℤ → AnalyticVectorWitness T :=
    AnalyticVectorWitness.uniformIntegerLine hclosed hsym hdense W0
      hr hrW0 hδ (by linarith)
  have hbelow : ∀ k : ℤ, r < (W k).radius := by
    intro k
    exact (AnalyticVectorWitness.uniformIntegerLineData hclosed hsym hdense W0
      hr hrW0 hδ (by linarith) k).2.1
  have hδR : δ < r / 4 := by linarith
  have hclosedSym : T.closure.IsSymmetric := by simpa only [hclosed] using hsym
  rcases le_total 0 n with hn | hn
  · exact AnalyticVectorWitness.uniformIntegerLine_succ_of_nonneg
      hclosed hsym hdense W0 hr hrW0 hδ (by linarith) hn
  · by_cases hn0 : 0 ≤ n
    · exact AnalyticVectorWitness.uniformIntegerLine_succ_of_nonneg
        hclosed hsym hdense W0 hr hrW0 hδ (by linarith) hn0
    have hnneg : n + 1 ≤ 0 := by omega
    have hpred := AnalyticVectorWitness.uniformIntegerLine_pred_of_nonpos
      hclosed hsym hdense W0 hr hrW0 hδ (by linarith) hnneg
    let U : LocalAnalyticOrbit T ((W (n + 1)).state) :=
      IsAnalyticVector.localAnalyticOrbitOfWitness (W (n + 1)).iterates
        (W (n + 1)).iterates_spec (W (n + 1)).radius_pos (W (n + 1)).summable
        hsym hdense
    let V : LocalAnalyticOrbit T (W n).state :=
      IsAnalyticVector.localAnalyticOrbitOfWitness (W n).iterates
        (W n).iterates_spec (W n).radius_pos (W n).summable hsym hdense
    have hpred' : (W n).state = analyticExp T (W (n + 1)).iterates (-δ) := by
      simpa [W, show n + 1 - 1 = n by omega] using hpred
    have hbase : (W n).state = U (-δ) := by
      simpa [U, IsAnalyticVector.localAnalyticOrbitOfWitness] using hpred'
    let V' : LocalAnalyticOrbit T (U (-δ)) :=
      { radius := V.radius
        radius_pos := V.radius_pos
        toFun := V
        initial := by
          calc
            V 0 = (W n).state := V.initial
            _ = U (-δ) := hbase
        mem_domain := V.mem_domain
        hasDerivAt := V.hasDerivAt
        norm_eq := by
          intro s hs
          calc
            ‖V s‖ = ‖(W n).state‖ := V.norm_eq s hs
            _ = ‖U (-δ)‖ := by rw [hbase] }
    have hmarginU : |(-δ)| + r / 4 ≤ U.radius := by
      dsimp [U, IsAnalyticVector.localAnalyticOrbitOfWitness]
      rw [abs_neg, abs_of_pos hδ]
      linarith [hbelow (n + 1)]
    have hVcore : r / 4 ≤ V'.radius := by
      dsimp [V, V', IsAnalyticVector.localAnalyticOrbitOfWitness]
      linarith [hbelow n]
    have heq := LocalAnalyticOrbit.translate_eq_of_same_initial_on_core'
      U hclosedSym (a := -δ) (R := r / 4) (by positivity) hmarginU V'
      hVcore (by rw [abs_of_pos hδ]; exact hδR)
    have hzero : analyticExp T (W (n + 1)).iterates 0 = (W (n + 1)).state :=
      analyticExp_zero (W (n + 1)).iterates_spec
    have heq' : analyticExp T (W (n + 1)).iterates 0 =
        analyticExp T (W n).iterates δ := by
      simpa [U, V', V, IsAnalyticVector.localAnalyticOrbitOfWitness] using heq
    rw [hzero] at heq'
    simpa [W] using heq'

/-! Once the analytic continuation has supplied a uniformly thick integer line of witnesses, this
lemma performs the genuinely topological part of Nelson's construction.  It is kept separate from
the choice of the line so that the same gluing theorem can be reused by other continuation
arguments. -/
lemma GlobalAnalyticOrbit.of_uniform_witness_line
    {T : H →ₗ.[ℂ] H} {x : H} (hclosed : T.closure = T)
    (hsym : T.IsSymmetric)
    (hdense : (Submodule.span ℂ {x : H | T.IsAnalyticVector x}).topologicalClosure = ⊤)
    (W : ℤ → AnalyticVectorWitness T) {r δ : ℝ}
    (hr : 0 < r) (hδ : 0 < δ) (h4δ : 4 * δ < r)
    (hbelow : ∀ n : ℤ, r < (W n).radius)
    (hstate_zero : (W 0).state = x)
    (hstate_norm : ∀ n : ℤ, ‖(W n).state‖ = ‖x‖)
    (hstep : ∀ n : ℤ,
      (W (n + 1)).state = analyticExp T (W n).iterates δ) :
    Nonempty (GlobalAnalyticOrbit T x) := by
  have hδR : δ < r / 4 := by linarith
  have hclosedSym : T.closure.IsSymmetric := by
    simpa only [hclosed] using hsym
  let chart : ∀ n : ℤ, LocalAnalyticOrbit T ((W n).state) := fun n =>
    IsAnalyticVector.localAnalyticOrbitOfWitness (W n).iterates
      (W n).iterates_spec (W n).radius_pos (W n).summable hsym hdense
  have hcore : ∀ n : ℤ, r / 4 ≤ (chart n).radius := by
    intro n
    dsimp [chart, IsAnalyticVector.localAnalyticOrbitOfWitness]
    linarith [hbelow n]
  have hmargin : ∀ n : ℤ, r / 4 + δ ≤ (chart n).radius := by
    intro n
    dsimp [chart, IsAnalyticVector.localAnalyticOrbitOfWitness]
    linarith [hbelow n]
  have hadj : ∀ n : ℤ, ∀ z : ℝ, |z| < r / 4 →
      chart n (δ + z) = chart (n + 1) z := by
    intro n z hz
    let U := chart n
    have hbase : (W (n + 1)).state = U δ := by
      dsimp [U, chart, IsAnalyticVector.localAnalyticOrbitOfWitness]
      simp only [hstep n]
    let V : LocalAnalyticOrbit T (U δ) :=
      { radius := (chart (n + 1)).radius
        radius_pos := (chart (n + 1)).radius_pos
        toFun := chart (n + 1)
        initial := by
          calc
            chart (n + 1) 0 = (W (n + 1)).state := (chart (n + 1)).initial
            _ = U δ := hbase
        mem_domain := (chart (n + 1)).mem_domain
        hasDerivAt := (chart (n + 1)).hasDerivAt
        norm_eq := by
          intro s hs
          calc
            ‖chart (n + 1) s‖ = ‖(W (n + 1)).state‖ :=
              (chart (n + 1)).norm_eq s hs
            _ = ‖U δ‖ := by rw [hbase] }
    have hmarginU : |δ| + r / 4 ≤ U.radius := by
      rw [abs_of_pos hδ]
      dsimp [U]
      linarith [hmargin n]
    have heq := LocalAnalyticOrbit.translate_eq_of_same_initial_on_core'
      U hclosedSym (a := δ) (R := r / 4) (by positivity)
      hmarginU V
      (by dsimp [V]; exact hcore (n + 1)) hz
    exact heq
  let C := LocalOrbitCoreCover.ofAdjacentIntIndex hδ hδR
    (fun n => (W n).state) chart (by positivity)
    (fun n => hcore n) hstate_zero hstate_norm hadj
  exact ⟨C.toGlobal⟩

/-- A dense family of analytic vectors proves essential self-adjointness once its local exponential
orbits have been patched to global norm-preserving orbits.  The theorem is deliberately separated
from the construction of those orbits: it is the reusable deficiency-space end of Nelson's proof. -/
theorem IsSymmetric.isEssentiallySelfAdjoint_of_denseAnalyticVectors_of_globalOrbit
    {T : H →ₗ.[ℂ] H} (hsym : T.IsSymmetric)
    (hdense : (Submodule.span ℂ {x : H | T.IsAnalyticVector x}).topologicalClosure = ⊤)
    (hOrbit : ∀ x : H, T.IsAnalyticVector x → Nonempty (GlobalAnalyticOrbit T x)) :
    T.IsEssentiallySelfAdjoint := by
  have hdenseDomain : T.HasDenseDomain := hasDenseDomain_of_denseAnalyticVectors hdense
  have hdefect_plus : T.defectNumber Complex.I = 0 := by
    rw [← defectNumber_closure (T := T) (z := Complex.I)
      (hsym.mem_regularityDomain_of_im_ne_zero (by simp))]
    show Module.rank ℂ ↥((T.closure - Complex.I • 1).toFun.rangeᗮ) = 0
    apply Submodule.rank_eq_zero.mpr
    apply (Submodule.eq_bot_iff _).mpr
    intro y hy
    have hyspan : y ∈ (Submodule.span ℂ {x : H | T.IsAnalyticVector x})ᗮ := by
      rw [Submodule.mem_orthogonal']
      intro u hu
      refine Submodule.span_induction (p := fun z _ ↦ ⟪y, z⟫_ℂ = 0) ?_ ?_ ?_ ?_ hu
      · intro z hz
        obtain ⟨U⟩ := hOrbit z hz
        exact U.inner_deficiency_eq_zero hy
      · simp
      · intro z₁ z₂ _ _ hz₁ hz₂
        simp [inner_add_right, hz₁, hz₂]
      · intro c z _ hz
        simp [inner_smul_right, hz]
    have hspanBot :
        (Submodule.span ℂ {x : H | T.IsAnalyticVector x})ᗮ = (⊥ : Submodule ℂ H) :=
      Submodule.topologicalClosure_eq_top_iff.mp hdense
    exact (Submodule.mem_bot ℂ).mp (hspanBot ▸ hyspan)
  have hdefect_minus : T.defectNumber (-Complex.I) = 0 := by
    rw [← defectNumber_closure (T := T) (z := -Complex.I)
      (hsym.mem_regularityDomain_of_im_ne_zero (by simp))]
    show Module.rank ℂ ↥((T.closure - (-Complex.I) • 1).toFun.rangeᗮ) = 0
    apply Submodule.rank_eq_zero.mpr
    apply (Submodule.eq_bot_iff _).mpr
    intro y hy
    have hyspan : y ∈ (Submodule.span ℂ {x : H | T.IsAnalyticVector x})ᗮ := by
      rw [Submodule.mem_orthogonal']
      intro u hu
      refine Submodule.span_induction (p := fun z _ ↦ ⟪y, z⟫_ℂ = 0) ?_ ?_ ?_ ?_ hu
      · intro z hz
        obtain ⟨U⟩ := hOrbit z hz
        exact U.inner_deficiency_eq_zero_neg hy
      · simp
      · intro z₁ z₂ _ _ hz₁ hz₂
        simp [inner_add_right, hz₁, hz₂]
      · intro c z _ hz
        simp [inner_smul_right, hz]
    have hspanBot :
        (Submodule.span ℂ {x : H | T.IsAnalyticVector x})ᗮ = (⊥ : Submodule ℂ H) :=
      Submodule.topologicalClosure_eq_top_iff.mp hdense
    exact (Submodule.mem_bot ℂ).mp (hspanBot ▸ hyspan)
  exact hsym.isEssentiallySelfAdjoint_of_defectNumber_eq_zero
    hdenseDomain hdefect_plus hdefect_minus

/-! ## Nelson's single-operator criterion -/

/-- **Nelson's analytic-vector theorem, single-operator case** (Reed–Simon Vol. II, Theorem
X.39, first half). A symmetric operator with a dense set of analytic vectors is essentially
self-adjoint.  The proof constructs a uniform-radius two-sided integer line of local exponential
charts, proves adjacent-chart agreement by the symmetric-ODE uniqueness lemma, glues the line into
a global norm-preserving orbit, and applies the deficiency-index criterion. -/
theorem IsSymmetric.isEssentiallySelfAdjoint_of_denseAnalyticVectors
    {T : H →ₗ.[ℂ] H} (hsym : T.IsSymmetric)
    (hdense : (Submodule.span ℂ {x : H | T.IsAnalyticVector x}).topologicalClosure = ⊤) :
    T.IsEssentiallySelfAdjoint := by
  have hdenseDomain : T.HasDenseDomain := hasDenseDomain_of_denseAnalyticVectors hdense
  have hT : T.IsClosable := hsym.isClosable hdenseDomain
  have hclosed : T.closure.closure = T.closure := hT.closure_isClosed.closure_eq
  have hclosedSym : T.closure.IsSymmetric := hsym.closure hdenseDomain
  have hspan_le : Submodule.span ℂ {x : H | T.IsAnalyticVector x} ≤
      Submodule.span ℂ {x : H | T.closure.IsAnalyticVector x} := by
    apply Submodule.span_mono
    intro z hz
    exact IsAnalyticVector.for_closure hz
  have hclosedense :
      (Submodule.span ℂ {x : H | T.closure.IsAnalyticVector x}).topologicalClosure = ⊤ := by
    apply le_antisymm le_top
    exact hdense ▸ Submodule.topologicalClosure_mono hspan_le
  have hOrbit : ∀ z : H, T.IsAnalyticVector z →
      Nonempty (GlobalAnalyticOrbit T z) := by
    intro z hz
    let W0 : AnalyticVectorWitness T.closure :=
      AnalyticVectorWitness.ofIsAnalytic (IsAnalyticVector.for_closure hz)
    let r : ℝ := W0.radius / 2
    let δ : ℝ := r / 8
    have hr : 0 < r := by
      dsimp [r]
      linarith [W0.radius_pos]
    have hrW0 : r < W0.radius := by
      dsimp [r]
      linarith [W0.radius_pos]
    have hδ : 0 < δ := by
      dsimp [δ]
      positivity
    have h4δ : 4 * δ < r := by
      dsimp [δ]
      linarith
    let W : ℤ → AnalyticVectorWitness T.closure :=
      AnalyticVectorWitness.uniformIntegerLine hclosed hclosedSym hclosedense W0
        hr hrW0 hδ (by linarith)
    have hbelow : ∀ n : ℤ, r < (W n).radius := by
      intro n
      exact (AnalyticVectorWitness.uniformIntegerLineData hclosed hclosedSym hclosedense W0
        hr hrW0 hδ (by linarith) n).2.1
    have hstate_zero : (W 0).state = z := by
      have hdata0 :
          AnalyticVectorWitness.uniformIntegerLineData hclosed hclosedSym hclosedense W0
              hr hrW0 hδ (by linarith) 0 =
            (⟨W0, hrW0, rfl⟩ :
              {W : AnalyticVectorWitness T.closure //
                r < W.radius ∧ ‖W.state‖ = ‖W0.state‖}) := by
        simp [AnalyticVectorWitness.uniformIntegerLineData, Int.inductionOn'_self]
      change (AnalyticVectorWitness.uniformIntegerLineData hclosed hclosedSym hclosedense W0
        hr hrW0 hδ (by linarith) 0).1.state = z
      rw [hdata0]
      rfl
    have hstate_norm : ∀ n : ℤ, ‖(W n).state‖ = ‖z‖ := by
      intro n
      have hn := (AnalyticVectorWitness.uniformIntegerLineData hclosed hclosedSym
        hclosedense W0 hr hrW0 hδ (by linarith) n).2.2
      change ‖(AnalyticVectorWitness.uniformIntegerLineData hclosed hclosedSym hclosedense W0
        hr hrW0 hδ (by linarith) n).1.state‖ = ‖z‖
      rw [hn]
      rfl
    have hstep : ∀ n : ℤ, (W (n + 1)).state =
        analyticExp T.closure (W n).iterates δ := by
      intro n
      exact AnalyticVectorWitness.uniformIntegerLine_step
        hclosed hclosedSym hclosedense W0 hr hrW0 hδ h4δ (n := n)
    obtain ⟨U⟩ := GlobalAnalyticOrbit.of_uniform_witness_line
      (T := T.closure) (x := z) hclosed hclosedSym hclosedense W
      hr hδ h4δ hbelow hstate_zero hstate_norm (by simpa [W] using hstep)
    exact GlobalAnalyticOrbit.of_closure hT U
  exact hsym.isEssentiallySelfAdjoint_of_denseAnalyticVectors_of_globalOrbit
    hdense hOrbit


end LinearPMap
