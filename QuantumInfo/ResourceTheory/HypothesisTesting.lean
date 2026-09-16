/-
Copyright (c) 2025 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg, Leonardo A. Lessa, Rodolfo R. Soldati
-/
module

public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.Analysis.Subadditive
public import Mathlib.CategoryTheory.Functor.FullyFaithful
public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import Mathlib.Data.EReal.Basic
public import QuantumInfo.Entropy.VonNeumann
public import QuantumInfo.Entropy.SSA
public import QuantumInfo.Entropy.Relative
public import QuantumInfo.Entropy.DPI
public import QuantumInfo.Channels.Bundled
public import QuantumInfo.Channels.CPTP
public import QuantumInfo.Channels.Dual
public import QuantumInfo.Channels.MatrixMap
public import QuantumInfo.Channels.Unbundled
public import QuantumInfo.Measurements.POVM

/-!
Defines `OptimalHypothesisRate`, the optimal rate of distinguishing an `MState` ρ from a set of other
mixed states `S`, with at most Type I error ε.

That is to say: take a projective measurement (a `POVM`) with elements `{T, 1-T}`, where measuring `T`
will mean we conclude our unknown state was ρ, and measuring `1-T` will mean we think the state was
something in `S`. We only accept T's such that `Tr[(1-T)ρ] ≤ ε`, that is, we have at most an ε
probability of incorrectly concluding it was ρ. The Type II error associated to this T is then
`max_{σ ∈ S} Tr[T σ]`, that is, the (worst possible, over possible states) chance of incorrectly
concluding our state was in `S`. Optimize over `T` to get the lowest possible Type II error rate,
and the resulting error rate is `OptimalHypothesisRate ρ ε S`.

We make this accessible through the notation `β_ ε(ρ‖S)`.

See [The tangled state of quantum hypothesis testing](https://doi.org/10.1038/s41567-023-02289-9) by
Mario Berta et al. for a broader overview.
-/

@[expose] public section

open NNReal
open ComplexOrder
open Topology
open Prob
open scoped RealInnerProductSpace InnerProductSpace

variable {d : Type*} [Fintype d] [DecidableEq d]

/-- The optimal hypothesis testing rate, for a tolerance ε: given a state ρ and a set of states S,
the optimum distinguishing rate that allows a probability ε of errors. -/
noncomputable def OptimalHypothesisRate (ρ : MState d) (ε : Prob) (S : Set (MState d)) : Prob :=
  ⨅ T : { m : HermitianMat d ℂ // ρ.exp_val (1 - m) ≤ ε ∧ 0 ≤ m ∧ m ≤ 1},
    ⨆ σ ∈ S, ⟨_, σ.exp_val_prob T.prop.right⟩

scoped[OptimalHypothesisRate] notation "β_" ε " (" ρ "‖" S ")" =>  OptimalHypothesisRate ρ ε S

namespace OptimalHypothesisRate

/-- The space of strategies `T` in `OptimalHypothesisRate` is inhabited, we always have some valid strategy. -/
instance iInf_Inhabited (ρ : MState d) (ε : Prob) :
    Inhabited { m // ρ.exp_val (1 - m) ≤ ε ∧ 0 ≤ m ∧ m ≤ 1 } :=
  ⟨1, by simp⟩

instance (ρ : MState d) (ε : Prob) : Inhabited {m | ρ.exp_val (1 - m) ≤ ε ∧ 0 ≤ m ∧ m ≤ 1} :=
  iInf_Inhabited ρ ε

/-- The space of strategies `T` in `OptimalHypothesisRate` is compact. -/
theorem iInf_IsCompact (ρ : MState d) (ε : Prob) : IsCompact { m | ρ.exp_val (1 - m) ≤ ε ∧ 0 ≤ m ∧ m ≤ 1 } := by
  have hC₁ : IsCompact {m : HermitianMat d ℂ | 0 ≤ m ∧ m ≤ 1} :=
    HermitianMat.unitInterval_IsCompact
  have hC₂ : IsClosed {m | ρ.exp_val (1 - m) ≤ ε} := by
    --This is a linear constraint and so has a closed image
    change IsClosed ((fun m ↦ ρ.M.innerₗ (1 - m)) ⁻¹' (Set.Iic ε))
    refine IsClosed.preimage ?_ isClosed_Iic
    fun_prop
  exact hC₁.inter_left hC₂

/-- The space of strategies `T` in `OptimalHypothesisRate` is convex. -/
theorem iInf_IsConvex (ρ : MState d) (ε : Prob) : Convex ℝ { m | ρ.exp_val (1 - m) ≤ ε ∧ 0 ≤ m ∧ m ≤ 1 } := by
  --We *could* get this from a more general fact that any linear subspace is convex,
  --and the intersection of convex spaces is convex, and this is an intersection of
  --three convex spaces. That would be more broken-down and lemmaified.
  rintro x ⟨hx₁, hx₂, hx₃⟩ y ⟨hy₁, hy₂, hy₃⟩ a b ha hb hab
  rw [← eq_sub_iff_add_eq'] at hab
  subst b
  refine And.intro ?_ (And.intro ?_ ?_)
  · simp only [MState.exp_val, inner_sub_right, HermitianMat.inner_one, DensityOp.tr,
      tsub_le_iff_right, inner_add_right, inner_smul_right] at hx₁ hy₁ ⊢
    linear_combination a * hx₁ + (1 - a) * hy₁
  · apply HermitianMat.convex_cone <;> assumption
  · rw [← sub_nonneg] at hx₃ hy₃ ⊢
    convert HermitianMat.convex_cone hx₃ hy₃ ha hb using 1
    simp only [sub_smul, one_smul, smul_sub]
    abel

/-- When `S` is empty, the optimal hypothesis testing rate is zero. -/
@[simp]
theorem of_empty {ρ : MState d} (ε : Prob) : β_ ε(ρ‖∅) = 0 := by
  simp [OptimalHypothesisRate]
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem le_sup_exp_val {ρ : MState d} (ε : Prob) {S : Set (MState d)}
    (m : HermitianMat d ℂ) (hExp : ρ.exp_val (1 - m) ≤ ε) (hm : 0 ≤ m ∧ m ≤ 1) :
    β_ ε(ρ‖S) ≤ ⨆ σ ∈ S, ⟨_, σ.exp_val_prob hm⟩ := by
  unfold OptimalHypothesisRate
  apply iInf_le_of_le ⟨m, ⟨hExp, hm⟩⟩ _
  simp only [le_refl]

theorem le_of_subset (ρ : MState d) (ε : Prob) {S1 S2 : Set (MState d)} (h : S1 ⊆ S2) :
    β_ ε(ρ‖S1) ≤ β_ ε(ρ‖S2) :=
  iInf_mono (fun _ ↦ iSup_le_iSup_of_subset h)

theorem of_singleton {ρ σ : MState d} {ε : Prob} :
    β_ ε(ρ‖{σ}) =
      ⨅ T : { m : HermitianMat d ℂ // ρ.exp_val (1 - m) ≤ ε ∧ 0 ≤ m ∧ m ≤ 1},
        ⟨_, σ.exp_val_prob T.2.right⟩ := by
  simp only [OptimalHypothesisRate, iSup_singleton]

open scoped Prob in
theorem negLog_le_singleton (ρ : MState d) (ε : Prob) (S : Set (MState d))
    (σ : MState d) (h : σ ∈ S) : —log β_ ε(ρ‖S) ≤ —log β_ ε(ρ‖{σ}) := by
  apply Prob.negLog_Antitone
  apply le_of_subset
  exact Set.singleton_subset_iff.mpr h

set_option backward.isDefEq.respectTransparency false in
theorem singleton_le_exp_val {ρ σ : MState d} {ε : Prob} (m : HermitianMat d ℂ)
    (hExp : ρ.exp_val (1 - m) ≤ ε) (hm : 0 ≤ m ∧ m ≤ 1) :
  β_ ε(ρ‖{σ}) ≤ ⟨_, σ.exp_val_prob hm⟩ := by
  rw [of_singleton]
  apply iInf_le_of_le ⟨m, ⟨hExp, hm⟩⟩ _
  simp only [le_refl]

set_option backward.isDefEq.respectTransparency false in
/-- There exists an optimal T for the hypothesis testing, that is, it's a minimum
and not just an infimum. This states we have `1 - ε ≤ ρ.exp_val T`, but we can always
"worsen" T to make that bound tight, which is `exists_min`. -/
theorem exists_min' (ρ : MState d) (ε : Prob) (S : Set (MState d)):
    ∃ (T : { m : HermitianMat d ℂ // ρ.exp_val (1 - m) ≤ ε ∧ 0 ≤ m ∧ m ≤ 1}),
      (⨆ σ ∈ S, ⟨_, σ.exp_val_prob T.prop.right⟩ = β_ ε(ρ‖S))
      ∧ 1 - ε ≤ ρ.exp_val T := by
  have _ : Nonempty d := ρ.nonempty
  rcases S.eq_empty_or_nonempty with rfl | hS
  · simpa [-Subtype.exists] using ⟨rfl, ⟨1, by simp⟩, by simp⟩
  rw [← Set.nonempty_coe_sort] at hS
  obtain ⟨T, hT₁, hT₂⟩ := IsCompact.exists_isMinOn (α := Prob)
    (isCompact_iff_isCompact_univ.mp (iInf_IsCompact ρ ε)) Set.univ_nonempty
    (f := fun T ↦ ⨆ σ ∈ S, ⟨_, σ.exp_val_prob T.prop.right⟩)
    (by
      have h := HermitianMat.innerₗ.continuous_iSup_fst
        (Bornology.isBounded_induced.mp (Bornology.IsBounded.all S))
      apply Continuous.continuousOn
      simp_rw [← iSup_subtype'', subtype_val_iSup' (ι := S)]
      refine Continuous.subtype_mk ?_ _
      refine Continuous.comp (g := fun T ↦ ⨆ (i : S), i.val.exp_val T) ?_ continuous_subtype_val
      convert! h with T
      rw [← sSup_image' (s := S) (f := fun i ↦ i.exp_val T)]
      rw [← sSup_image' (s := (DensityOp.M '' S)) (f := fun i ↦ i.innerₗ T)]
      simp [Set.image, MState.exp_val, HermitianMat.innerₗ]
    )
  clear hT₁

  use T
  constructor
  · simp only [isMinOn_univ_iff] at hT₂
    rw [OptimalHypothesisRate]
    --Why is the following three bundled together not a theorem? Is it, and I can't find it? TODO
    apply le_antisymm
    · exact le_iInf hT₂
    · exact iInf_le_iff.mpr fun _ a ↦ a T
  · simpa [MState.exp_val_sub, add_comm (ε : ℝ) _] using T.2.1

--TODO: Maybe we should define these two instances.
-- Then we can get rid of `Prob.sub_zero` and use the generic `tsub_zero`.
-- #synth AddCommMonoid Prob
-- #synth OrderedSub Prob

set_option backward.isDefEq.respectTransparency false in
/-- There exists an optimal T for the hypothesis testing, that is, it's a minimum and
not just an infimum. This tightens the `T` from `exists_min'` to a `⟪ρ,T⟫ = 1 - ε` bound. -/
theorem exists_min (ρ : MState d) (ε : Prob) (S : Set (MState d)):
    ∃ (T : { m : HermitianMat d ℂ // ρ.exp_val (1 - m) ≤ ε ∧ 0 ≤ m ∧ m ≤ 1}),
      (⨆ σ ∈ S, ⟨_, σ.exp_val_prob T.prop.right⟩ = β_ ε(ρ‖S))
      ∧ ρ.exp_val T = 1 - ε := by
  obtain ⟨T, hT₁, hT₂⟩ := exists_min' ρ ε S

  --Instead of just `use T`, we (may) have to reduce it so that it saturates the ⟪ρ,T⟫ = 1 - ε bound.
  --We do this by multiplying it by a scalar less than 1 to get a `T'`. Since this operator is less
  --than T, it's still optimal in terms of achieving `β_ ε(ρ‖S)`, but it can get the `1 - ε` bound instead.
  set δ := ρ.exp_val ↑T - (1 - ε)-- with δ_def
  by_cases hδ : δ = 0
  · use T, hT₁
    linarith
  replace hδ : 0 < δ := by linarith +splitNe
  have hδ_le : δ ≤ 1 := by
    linarith [ρ.exp_val_le_one T.2.2.2, ε.2]

  have hTr : 0 < ρ.exp_val T := by
    linarith [ε.coe_le_one]

  set T' : HermitianMat d ℂ :=
    (1 - δ / ρ.exp_val T) • T with hT'_def
  have hT'_le : T' ≤ T := by
    rw [← one_smul ℝ T.val, hT'_def]
    gcongr
    · exact T.2.2.1
    · simp; positivity
  have hρT' : ρ.exp_val (1 - T') = ε := by
    simp [T', MState.exp_val_sub, δ, field]

  have hT' : ρ.exp_val (1 - T') ≤ ε ∧ 0 ≤ T' ∧ T' ≤ 1 := by
    use hρT'.le
    constructor
    · simp [T']
      refine smul_nonneg ?_ T.2.2.1
      bound
    · exact hT'_le.trans T.2.2.2
  use ⟨T', hT'⟩

  constructor
  · rw [OptimalHypothesisRate] at hT₁ ⊢
    apply le_antisymm
    · apply le_iInf
      intro i
      refine le_trans ?_ (le_of_eq_of_le hT₁ ?_)
      · gcongr
      · exact iInf_le_iff.mpr fun _ a ↦ a i
    · exact iInf_le_iff.mpr fun _ a ↦ a ⟨T', hT'⟩
  · simp [MState.exp_val_sub, ← hρT']

set_option backward.isDefEq.respectTransparency false in
/-- When the allowed Type I error `ε` is less than 1 (so, we have some limit on our errors),
and the kernel of the state `ρ` contains the kernel of some element in `S`, then the optimal
hypothesis rate is positive - there is some lower bound on the type II errors we'll see. In
other words, under these conditions, we cannot completely avoid type II errors. -/
theorem pos_of_lt_one {ρ : MState d} (S : Set (MState d))
  (hρ : ∃ σ ∈ S, σ.M.ker ≤ ρ.M.ker)
  {ε : Prob} (hε : ε < 1) : 0 < β_ ε(ρ‖S) := by
  obtain ⟨σ, hσ₁, hσ₂⟩ := hρ
  --Assume the converse: that the infimum is zero. The set of such T's is inhabited
  --and closed, so there is some T that attains the value zero. This T has zero
  --inner product with σ (`σ.exp_val T = 0`), and yet (by definition of T's type) we
  --also have that `ρ.exp_val (1 - T) ≤ ε < 1`. So `T` lives entirely in σ's kernel,
  --which (by `h_supp`) is contained in ρ's kernel. So
  --`ρ.exp_val (1 - T) = ρ.exp_val 1 - ρ.exp_val T = ρ.trace - 0 = 1`, a contradiction.
  by_contra h
  obtain ⟨⟨T, hT₁, hT₂, hT₃⟩, hT₄, hT₅⟩ := exists_min ρ ε S
  push Not at h
  simp at h
  rw [h] at hT₄
  have h_sup_zero := hT₄ ▸ le_iSup₂ σ hσ₁
  have h_eq := le_antisymm h_sup_zero (by simp)
  rw [Subtype.ext_iff, Set.Icc.coe_zero] at h_eq
  simp only [MState.exp_val] at h_eq
  rw [HermitianMat.inner_zero_iff σ.nonneg hT₂] at h_eq
  replace hT₁ : ρ.exp_val (1 - T) ≠ 1 := (lt_of_le_of_lt hT₁ hε).ne
  absurd hT₁
  rw [ρ.exp_val_eq_one_iff ?_, sub_sub_cancel]
  · grw [← h_eq]
    rwa [HermitianMat.ker, HermitianMat.ker,
      ContinuousLinearMap.ker_le_ker_iff_range_le_range] at hσ₂ <;> simp
  · exact sub_le_self 1 hT₂

set_option backward.isDefEq.respectTransparency false in
--Lemma 3 from Hayashi
theorem Lemma3 {ρ : MState d} (ε : Prob) {S : Set (MState d)} (hS₁ : IsCompact S)
    (hS₂ : Convex ℝ (DensityOp.M '' S)) : ⨆ σ ∈ S, β_ ε(ρ‖{σ}) = β_ ε(ρ‖S) := by
  --Work out the case where S is empty, so we can now assume it's nonempty
  rcases S.eq_empty_or_nonempty with rfl|hnS
  · simpa using _root_.bot_eq_zero
  --Upgrade this fact to an instance
  have _ : Nonempty S := hnS.to_subtype

  simp only [OptimalHypothesisRate, Set.mem_singleton_iff, iSup_iSup_eq_left]

  --This parts needs the minimax theorem. Set up the relevant sets and hypotheses.
  --The function `f` will be the `MState.exp_val` function, but bundled as a bilinear form.
  let f : LinearMap.BilinForm ℝ (HermitianMat d ℂ) := HermitianMat.innerₗ
  let S' : Set (HermitianMat d ℂ) := DensityOp.M '' S
  let T' : Set (HermitianMat d ℂ) := { m | ρ.exp_val (1 - m) ≤ ε ∧ 0 ≤ m ∧ m ≤ 1 }

  have hS'₁ : IsCompact S' := hS₁.image MState.Continuous_HermitianMat

  have hT'₁ : IsCompact T' := iInf_IsCompact ρ ε

  have hT'₂ : Convex ℝ T' := iInf_IsConvex ρ ε

  have hS'₃ : S'.Nonempty := by simpa only [Set.image_nonempty, S']

  have hT'₃ : T'.Nonempty := Set.Nonempty.of_subtype

  ext1 --turn it from Prob equality into ℝ equality
  convert LinearMap.BilinForm.minimax' (M := HermitianMat d ℂ) f S' T' hS'₁ hT'₁ hS₂ hT'₂ hS'₃ hT'₃
  --The remaining twiddling is about moving the casts inside the iInf's and iSup's.
  --In a better world, this would be mostly handled by some clever simps or push_cast's.
  · have hi := iSup_range' (ι := S) (fun x ↦ ⨅ (y : T'), (f x) ↑y) (·)
    rw [← Set.image_eq_range] at hi
    rw [← iSup_subtype'', Set.Icc.coe_iSup (zero_le_one), hi]
    congr!
    exact Set.Icc.coe_iInf zero_le_one
  · rw [Set.Icc.coe_iInf (ι := T') zero_le_one]
    congr! 2 with y
    have hi := iSup_range' (ι := S) (fun x ↦ (f x) ↑y) (·)
    rw [← Set.image_eq_range] at hi
    rw [← iSup_subtype'', Set.Icc.coe_iSup zero_le_one, hi]
    rfl

--Maybe should be phrased in terms of `0 < ...` instead? Maybe belongs in another file? It's kiinnnd of specialized..
theorem ker_diagonal_prob_eq_bot {q : Prob} (hq₁ : 0 < q) (hq₂ : q < 1) :
    HermitianMat.ker (.diagonal ℂ (ProbDistribution.coin q ·)) = ⊥ := by
  have hA : (Matrix.toLin' (HermitianMat.diagonal ℂ (ProbDistribution.coin q ·)).mat).ker = ⊥ := by
    apply Matrix.PosDef.toLin_ker_eq_bot
    apply Matrix.PosDef.diagonal
    intro i; fin_cases i
    · simpa
    · simpa [← Complex.ofReal_one, Complex.real_lt_real]
  simp [LinearMap.ker_eq_bot', HermitianMat.ker] at hA ⊢
  intro m hm
  have h := hA m
  simp at h
  apply h
  · have := congrArg (·.ofLp 0) hm
    simp [ProbDistribution.coin, HermitianMat.diagonal, HermitianMat.lin] at this
    exact this
  · have := congrArg (·.ofLp 1) hm
    simp [ProbDistribution.coin, HermitianMat.diagonal, HermitianMat.lin] at this
    exact this

variable {d₂ : Type*} [Fintype d₂] [DecidableEq d₂] in
/-- Lemma S1 -/
theorem optimalHypothesisRate_antitone (ρ σ : MState d) (ℰ : CPTPMap d d₂) (ε : Prob) :
    β_ ε(ρ‖{σ}) ≤ β_ ε(ℰ ρ‖{ℰ σ}) := by
  simp only [of_singleton]
  obtain ⟨ℰdualSubtype, h⟩ :
      ∃ e : ({ m : HermitianMat d₂ ℂ // MState.exp_val (ℰ ρ) (1 - m) ≤ ε ∧ 0 ≤ m ∧ m ≤ 1} →
      { m : HermitianMat d ℂ // ρ.exp_val (1 - m) ≤ ε ∧ 0 ≤ m ∧ m ≤ 1}),
      ∀ x, e x = ℰ.hermDual x
       := by
    constructor; swap
    · rintro ⟨m, hm₁, hm₂⟩
      refine ⟨ℰ.toPTPOp.hermDual m, ?_, PTPOp.hermDual.PTP_POVM ℰ.toPTPOp hm₂⟩
      have hℰd : MState.exp_val (ℰ ρ) (1 - m) = ρ.exp_val (ℰ.hermDual (1 - m)) :=
        ℰ.exp_val_hermDual ρ (1 - m)
      simpa [hℰd] using hm₁
    · rintro ⟨m, hm₁, hm₂⟩
      rfl
  convert! le_iInf_comp _ ℰdualSubtype
  rename_i T'
  specialize h T'
  rw [h]
  exact ℰ.exp_val_hermDual σ T'

open scoped HermitianMat in
open scoped Prob in
set_option backward.isDefEq.respectTransparency false in
/-- This is from [Strong converse exponents for a quantum channel discrimination problem
and quantum-feedback-assisted communication](https://doi.org/10.1007/s00220-016-2645-4), Lemma 5.

It seems like this is actually true for all 0 < α (with appropriate modifications at α = 1), but we only need
it for the case of 1 < α.
-/
theorem Ref81Lem5 (ρ σ : MState d) (ε : Prob) (hε : ε < 1) (α : ℝ) (hα : 1 < α) :
    —log β_ ε(ρ‖{σ}) ≤ D̃_ α(ρ‖σ) + —log (1 - ε) *
      (.ofNNReal ⟨α, zero_le_one.trans hα.le⟩) / (.ofNNReal ⟨α - 1, sub_nonneg_of_le hα.le⟩)
    := by
  generalize_proofs pfF pf1 pf2
  --If ρ isn't in the support of σ, the right hand side is just ⊤. (The left hand side is not, necessarily!)
  by_cases h_supp : σ.M.ker ≤ ρ.M.ker
  swap
  · rw [sandwichedRelRentropy_eq_top (zero_lt_one.trans hα) h_supp, top_add]
    exact le_top

  --Now we know that ρ.support ≤ σ.support. This is the main case we actually care about.
  --Proof from https://link.springer.com/article/10.1007/s00220-016-2645-4 reproduced below.
  /-
  Lemma 5. Let ρ, σ ∈ S (H) be such that supp ρ ⊆ supp σ . For any Q ∈ B(H) such
    that 0 ≤ Q ≤ I , and any α > 1,
    − log Tr[Qσ] ≤ D˜α (ρ‖σ) − α / (α−1) * log Tr[Qρ]. (3.7)
    In particular, for any α > 1 and any ε ∈ (0, 1),
    D^ε_H (ρ‖σ) ≤ D˜α (ρ‖σ) + α / (α−1) * log(1 / (1−ε)). (3.8)
    Proof. Let p ≡ Tr {Qρ} and q ≡ Tr {Qσ}. By the monotonicity of the sandwiched
    Rényi relative entropy for α > 1, we find that
    D˜α (ρ‖σ) ≥ D˜α ((p, 1 − p) ‖ (q, 1 − q)) (3.9)
      = 1 / (α−1) * log[p^α * q^(1−α) + (1−p)^α * (1−q)^(1−α) ] (3.10)
      ≥ 1 / (α−1) * log[p^α * q^(1−α) ] (3.11)
      = α / (α−1) * log p − log q, (3.12)
    from which (3.7) follows. The statement in (3.8) follows by optimizing over all Q such
    that Tr {Qρ} ≥ 1 − ε.
  -/
  -- The "monotonicity of the ..." part here refers to the data processing inequality, and
  -- the (p, 1-p) and (q,1-q) refer to states which are qubits ("coins") of probability p and
  -- q, respectively. The states ρ and σ can be "processed" into these coins by measuring the optimal T.

  have h₂ : 0 < 1 - ε.val := by
    change ε.val < 1 at hε
    linarith

  let p : Prob := 1 - ε
  set q : Prob := β_ ε(ρ‖{σ})
  let p2 : MState (Fin 2) := .ofClassical <| .coin p
  let q2 : MState (Fin 2) := .ofClassical <| .coin q

  --Show there's a lower bound on β_ε, that you can't do perfect discrimination
  --It's possible that we actually don't want this here, that it should "follow"
  --from the main proof.
  have hq : 0 < q := pos_of_lt_one {σ} ⟨σ, rfl, h_supp⟩ hε

  suffices —log q ≤ D̃_ α(p2‖q2) + —log (1 - ε) * (.ofNNReal ⟨α, pf1⟩) / (.ofNNReal ⟨α - 1, pf2⟩) by
    refine this.trans (add_le_add_left ?_ _)
    --Show that this is an instance of the Data Processing Inequality
    obtain ⟨Φ, hΦ₁, hΦ₂⟩ : ∃ (Φ : CPTPMap d (Fin 2)), p2 = Φ ρ ∧ q2 = Φ σ := by
      --The relevant map here is to take the T that optimizes inside β_ ε (ρ‖{σ}),
      --and use the projective measurement onto {T, 1 - T}. This achieves the optimum
      --discrimination rate on σ, and so gives the outcome distribution q2. And it
      --is tight on the bound that Tr[ρ T] = ε.

      --Get the measurement operator T.
      obtain ⟨T, hT₁, hT₂⟩ := exists_min ρ ε {σ}
      simp only [Set.mem_singleton_iff, iSup_iSup_eq_left] at hT₁
      --Turn it into a POVM (probably want to have lemmas around this ideally)
      let Λ : POVM (Fin 2) d := {
        mats i := if i = 0 then T else 1 - T
        nonneg i := by
          split
          · exact T.prop.2.1
          · exact HermitianMat.zero_le_iff.mpr T.prop.2.2
        normalized := by simp
      }
      use Λ.measureDiscard
      simp only [POVM.measureDiscard_apply, p2, q2]
      constructor
      · congr
        rw [ProbDistribution.coin_eq_iff]
        ext
        dsimp [MState.exp_val] at hT₂
        simp [POVM.measure, Λ, p, ProbDistribution.mk', coe_one_minus, ← hT₂, HermitianMat.inner_comm]
      · congr
        rw [ProbDistribution.coin_eq_iff]
        ext
        dsimp [POVM.measure, Λ, q]
        rw [← hT₁]
        exact HermitianMat.inner_comm _ _
    rw [hΦ₁, hΦ₂]
    exact sandwichedRenyiEntropy_DPI hα.le ρ σ Φ

  --If q = 1, this inequality is trivial
  by_cases hq₂ : q = 1
  · rw [hq₂]
    simp

  replace hq₂ : q < 1 := show q.val < 1 by
    linarith +splitNe [q.coe_le_one, unitInterval.coe_ne_one.mpr hq₂]


  --The Renyi entropy is finite
  rw [MState.sandwichedRelRentropy_eq_matrix, dif_pos (zero_lt_one.trans hα), dif_pos ?_]; swap
  · suffices q2.M.ker = ⊥ by
      simp only [this, bot_le]
    --q2 has eigenvalues β_ ε(ρ‖{σ}) and 1-β_ ε(ρ‖{σ}), so as long as β_ ε(ρ‖{σ}) isn't 0 or 1,
    --this is true.
    rw [show q2.M = HermitianMat.diagonal ℂ (ProbDistribution.coin q ·) from
      MState.coe_ofClassical _]
    exact ker_diagonal_prob_eq_bot hq hq₂

  conv => enter [2, 1, 1, 1]; rw [if_neg hα.ne']

  --The logs are finite
  rw [Prob.negLog, Prob.negLog, if_neg hq.ne']
  rw [if_neg (show 1 - ε ≠ 0 by simpa [Subtype.ext_iff, Prob.coe_sub] using h₂.ne')]

  --Turn the ENNReal problem into a Real problem
  have hα₂ : Subtype.mk _ pf2 ≠ 0 := by
    change ¬(_ = Subtype.mk 0 _)
    simp
    linarith
  rw [← ENNReal.coe_mul, ← ENNReal.coe_div hα₂, ← ENNReal.coe_add, ENNReal.coe_le_coe]
  clear hα₂
  simp only [← coe_le_coe, NNReal.coe_add, NNReal.coe_div, NNReal.coe_mul]
  simp [toReal]
  clear pf1 pf2
  rw [← add_div, ← sub_eq_add_neg]
  conv =>
    enter [2,1,1,1]
    equals (p^α * q^(1-α) + (1-p)^α * (1-q)^(1-α) : ℝ) =>
      unfold q2
      rw [MState.ofClassical_pow]
      unfold p2
      rw [MState.coe_ofClassical]
      rw [HermitianMat.diagonal_conj_diagonal, HermitianMat.diagonal_pow]
      rw [HermitianMat.trace_diagonal]
      simp only [Fin.sum_univ_two, Fin.isValue, ProbDistribution.coin_val_zero,
        ProbDistribution.coin_val_one, Prob.coe_one_minus]
      rw [Real.mul_rpow p.zero_le (by positivity)]
      rw [← Real.rpow_natCast_mul (by bound)]
      rw [← Real.rpow_mul q.zero_le]
      rw [Real.mul_rpow (by bound) (by positivity)]
      rw [← Real.rpow_natCast_mul (by bound)]
      rw [← Real.rpow_mul (by bound)]
      congr <;> simp [field]

  by_cases h : ε = 0
  · simp [h, p, @Real.zero_rpow α (by positivity)]
    apply Eq.le
    rw [Real.log_rpow hq]
    have : α - 1 ≠ 0 := by linarith
    field_simp
    ring_nf

  have hp : 0 < p := show (0 : ℝ) < p by simp [p, hε]

  replace h : 0 < ε := zero_lt_iff.mpr h
  trans (Real.log (p ^ α * q ^ (1 - α)) - Real.log (1 - ε.val) * α) / (α - 1)
  · rw [Real.log_mul]
    rotate_left
    · exact (Real.rpow_pos_of_pos hp _).ne'
    · exact (Real.rpow_pos_of_pos hq _).ne'
    simp only [p, Prob.coe_one_minus]
    rw [Real.log_rpow (by linarith), mul_comm α, add_sub_cancel_left]
    rw [Real.log_rpow (x := q.val) hq]
    rw [mul_comm, ← mul_div, mul_comm, show (1 - α) = -(α - 1) by abel]
    simp [-neg_sub, neg_div, div_self (a := α - 1) (by linarith)]
  · rw [div_le_div_iff_of_pos_right (by linarith), tsub_le_iff_right]
    simp only [sub_add_cancel]
    apply Real.log_le_log
    · refine mul_pos (Real.rpow_pos_of_pos hp _) (Real.rpow_pos_of_pos hq _)
    rw [le_add_iff_nonneg_right]
    refine mul_nonneg (Real.rpow_nonneg ?_ _) (Real.rpow_nonneg ?_ _)
    · exact sub_nonneg_of_le p.2.2
    · exact sub_nonneg_of_le q.2.2

set_option backward.isDefEq.respectTransparency false in
theorem rate_pos_of_smul_pos {ε : Prob} {d : Type*} [Fintype d] [DecidableEq d] {ρ σ₁ σ₂ : MState d}
    (hσ₂ : 0 < β_ ε(ρ‖{σ₂})) {c : ℝ} (hc : 0 < c) (hσ : c • σ₂ ≤ σ₁.M) : 0 < β_ ε(ρ‖{σ₁}) := by
  simp only [of_singleton, lt_iInf_iff] at hσ₂ ⊢
  rcases hσ₂ with ⟨⟨b, _, hb_le⟩, hb_pos, hb⟩
  simp only [← Subtype.coe_lt_coe, Prob.coe_zero] at hb_pos
  use ⟨(min c 1) * b, by positivity, by bound⟩
  constructor
  · simp only [← Subtype.coe_lt_coe, Prob.coe_zero]; positivity
  intro i
  specialize hb i
  rw [Subtype.mk_le_mk, MState.exp_val] at hb ⊢
  replace hb : c * b ≤ ⟪c • σ₂.M, i⟫ := by
    rwa [← mul_le_mul_iff_of_pos_left hc, ← HermitianMat.inner_smul_left] at hb
  grw [min_le_left]
  refine hb.trans (HermitianMat.inner_mono' i.2.2.1 hσ)

set_option backward.isDefEq.respectTransparency false in
@[fun_prop]
theorem rate_Continuous_singleton {ε : Prob} {d : Type*} [Fintype d] [DecidableEq d] (ρ : MState d) :
    Continuous fun σ ↦ β_ ε(ρ‖{σ}) := by
  have h := HermitianMat.innerₗ.flip.continuous_iInf_fst
    (S := { m | ρ.exp_val (1 - m) ≤ ↑ε ∧ 0 ≤ m ∧ m ≤ 1 })
    ((Metric.isBounded_Icc 0 1).subset (Set.ofPred_subset_ofPred_of_imp fun _ ↦ And.right))
  simp only [of_singleton]
  conv => enter [1, σ]; rw [subtype_val_iInf']
  exact Continuous.subtype_mk (h.comp MState.Continuous_HermitianMat) _

set_option backward.isDefEq.respectTransparency false in
/-- On the 1D Hilbert space, the optimal hypothesis testing rate is simply 1 - ε,
since there's nothing to learn. (More generally this would hold whenever ρ=σ.) --/
theorem optimalHypothesisRate_unique {d : Type*} [Fintype d] [DecidableEq d]
    (ε : Prob) (ρ σ : MState d) [Unique d] : β_ ε(ρ‖{σ}) = 1 - ε := by
  obtain rfl := Unique.eq_default ρ
  obtain rfl := Unique.eq_default σ
  rw [OptimalHypothesisRate.of_singleton]
  apply le_antisymm
  · refine iInf_le_of_le ⟨((1 - ε : Prob) : ℝ) • 1, ⟨?_, ?_, ?_⟩⟩ ?_
    · simp [MState.exp_val_sub]
    · apply smul_nonneg ?_ zero_le_one
      simp
    · apply smul_le_of_le_one_left zero_le_one
      simp
    · simp [-Prob.coe_one_minus]
  · simp
    intro a he1 ha0 ha1
    rw [MState.exp_val_sub, MState.exp_val_one, tsub_le_iff_right] at he1
    rw [← tsub_le_iff_left, ← Prob.coe_one_minus] at he1
    exact he1
