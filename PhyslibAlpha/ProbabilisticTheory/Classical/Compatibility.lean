/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.ProbabilisticTheory.Classical.Basic
public import PhyslibAlpha.ProbabilisticTheory.Measurement.Compatibility
public import PhyslibAlpha.ProbabilisticTheory.OrderUnit.Bidual
public import PhyslibAlpha.Mathematics.Order.PositiveDual.Majorant
public import PhyslibAlpha.ProbabilisticTheory.OrderUnit.Interpolation
public import Mathlib.Analysis.LocallyConvex.Separation
public import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Classical theories are those without incompatibility

Kuramochi's theorem: a system is classical exactly when all yes/no measurements are compatible.

## i. Overview

In classical probability every two yes/no questions can be asked at once. In quantum theory they
cannot: spin along `x` and spin along `z` have no joint measurement. Compatibility of all pairs of
yes/no measurements characterizes classical theories: it holds exactly when the positive
functionals form a lattice, that is, when the state space is a Choquet simplex.

When observables have the Riesz decomposition, every two yes/no measurements have a joint
measurement. Conversely, compatibility in `E` passes to the bidual of `E`, where increasing families
have suprema. There, a maximal decomposition turns compatibility into Riesz decomposition, and the
least upper bound of two positive functionals on the bidual restricts to one on `E`. For the other
direction, a lattice of positive functionals yields interpolants between observables; when the
observables are complete, these give joint effects exactly.

## ii. Key results

- `HasRieszDecomposition.exists_isBinaryJointEffect` : Riesz decomposition makes every two yes/no
  measurements compatible.
- `Bidual.exists_effect_near` : effects of `E` approximate effects of the bidual on finitely many
  positive functionals.
- `Bidual.exists_isBinaryJointEffect` : compatibility passes from `E` to its bidual.
- `Bidual.hasRieszDecomposition` : compatibility in the bidual gives Riesz decomposition there.
- `isClassical_of_jointlyMeasurable` : if every two yes/no measurements are compatible, the
  positive functionals form a lattice.
- `isClassical_iff_jointlyMeasurable` : **Kuramochi's theorem**: on a complete Archimedean
  order-unit space, the positive functionals form a lattice exactly when every two yes/no
  measurements are compatible.

## iii. Table of contents

- A. Riesz decomposition gives compatibility
- B. Approximating effects of the bidual
- C. Compatibility in the bidual
- D. Riesz decomposition in the bidual
- E. Compatibility makes the dual cone a lattice
- F. The characterization

## iv. References

- Y. Kuramochi, *Compatibility of any pair of 2-outcome measurements characterizes the Choquet
  simplex*, Positivity 24 (2020), 1479–1486. <https://arxiv.org/abs/1912.00563>
- M. Plávala, *All measurements in a probabilistic theory are compatible if and only if the state
  space is a simplex*, Phys. Rev. A 94 (2016), 042108.

-/

@[expose] public section

namespace ProbabilisticTheory

open scoped NNReal

variable {E : Type*} [OrderUnitSpace E]

/-! ## A. Riesz decomposition gives compatibility -/

/-- With Riesz decomposition, every two effects have a joint effect: split `e ≤ f + (1 - f)`. -/
lemma _root_.HasRieszDecomposition.exists_isBinaryJointEffect (hE : HasRieszDecomposition E)
    (e f : Effect E) : ∃ g : E, Effect.IsBinaryJointEffect e f g := by
  obtain ⟨g, ⟨hg0, hgf⟩, hrest⟩ := hE f.2.1 (sub_nonneg.2 f.2.2) ⟨e.2.1, by simpa using e.2.2⟩
  refine ⟨g, hg0, sub_nonneg.1 hrest.1, hgf, ?_⟩
  calc (e : E) + f - 1 = (e - g) + (f - 1 + g) := by abel
    _ ≤ (1 - f) + (f - 1 + g) := add_le_add_left hrest.2 _
    _ = g := by abel

section Archimedean

variable {F : Type*} [ArchimedeanOrderUnitSpace F]

/-- With Riesz decomposition, every two yes/no measurements are jointly measurable. -/
lemma _root_.HasRieszDecomposition.jointlyMeasurable
    (hF : HasRieszDecomposition F) (e f : Effect F) :
    Measurement.JointlyMeasurable (Effect.binaryMeasurement e)
      (Effect.binaryMeasurement f) :=
  (Effect.jointlyMeasurable_binaryMeasurement_iff e f).2 (hF.exists_isBinaryJointEffect e f)

end Archimedean

end ProbabilisticTheory

namespace Bidual
open ProbabilisticTheory
open scoped NNReal
variable {E : Type*} [OrderUnitSpace E]

/-! ## B. Approximating effects of the bidual -/

/-- An element of the bidual that is nonnegative is monotone in the positive functional. -/
lemma apply_mono {x : Bidual E} (hx : 0 ≤ x) {φ ψ : E →ₚ[ℝ] ℝ} (h : φ ≤ ψ) : x φ ≤ x ψ :=
  eval_mono h x hx

/-- If `P - N` is at most `m` on the effects of `E`, it is at most `m` on every effect of the
bidual. -/
lemma sub_le_of_forall_effect {x : Bidual E} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (P N : E →ₚ[ℝ] ℝ) {m : ℝ}
    (hm : ∀ a : E, 0 ≤ a → a ≤ 1 → P a - N a ≤ m) : x P - x N ≤ m := by
  obtain ⟨π, hπ, hπ1⟩ :=
    PositiveLinearMap.exists_le_add_of_forall_le P N OrderUnitSpace.isOrderUnit_one hm
  have := (apply_mono hx0 (show P ≤ π + N from hπ)).trans_eq (x.map_add π N)
  linarith [(hx1 π).trans hπ1]

/-- A real combination of positive functionals is a difference `P - N` of positive functionals, also
in its values on the bidual. -/
lemma exists_sub_eq_sum {ι : Type*} [Fintype ι] (φ : ι → E →ₚ[ℝ] ℝ) (w : ι → ℝ) :
    ∃ P N : E →ₚ[ℝ] ℝ, (∀ a, P a - N a = ∑ i, w i * φ i a) ∧
      ∀ x : Bidual E, x P - x N = ∑ i, w i * x (φ i) := by
  refine ⟨∑ i, (w i).toNNReal • φ i, ∑ i, (-w i).toNNReal • φ i, fun a => ?_, fun x => ?_⟩
  · simp only [sum_apply, PositiveLinearMap.nnsmul_apply, ← Finset.sum_sub_distrib, ← sub_mul,
      Real.coe_toNNReal', max_zero_sub_max_neg_zero_eq_self]
  · simp only [map_sum, map_nnsmul, ← Finset.sum_sub_distrib, ← sub_mul, Real.coe_toNNReal',
      max_zero_sub_max_neg_zero_eq_self]

/-- The values of the effects of `E` on the positive functionals in `S`. -/
def effectValues (S : Finset (E →ₚ[ℝ] ℝ)) : Set (S → ℝ) :=
  {v | ∃ a : E, 0 ≤ a ∧ a ≤ 1 ∧ v = fun φ => φ.1 a}

lemma convex_effectValues (S : Finset (E →ₚ[ℝ] ℝ)) : Convex ℝ (effectValues S) := by
  rintro _ ⟨a, ha0, ha1, rfl⟩ _ ⟨b, hb0, hb1, rfl⟩ s t hs ht hst
  refine ⟨s • a + t • b, by positivity, ?_, by ext; simp⟩
  calc s • a + t • b ≤ s • (1 : E) + t • (1 : E) := by gcongr
    _ = 1 := by rw [← add_smul, hst, one_smul]

/-- The values of an effect of the bidual lie in the closure of the values of effects of `E`. -/
lemma mem_closure_effectValues {x : Bidual E} (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (S : Finset (E →ₚ[ℝ] ℝ)) : (fun φ : S => x φ.1) ∈ closure (effectValues S) := by
  classical
  by_contra hnot
  obtain ⟨L, u, hLu, hut⟩ := geometric_hahn_banach_closed_point (convex_effectValues S).closure
    isClosed_closure hnot
  have hL (v : S → ℝ) : L v = ∑ i, (L fun j => if i = j then 1 else 0) * v i := by
    simpa [smul_eq_mul, mul_comm] using LinearMap.pi_apply_eq_sum_univ L.toLinearMap v
  obtain ⟨P, N, hPN, hxPN⟩ := exists_sub_eq_sum (fun i : S => i.1) fun i => L fun j =>
    if i = j then 1 else 0
  have := sub_le_of_forall_effect hx0 hx1 P N (m := u) fun a ha0 ha1 => by
    rw [hPN, ← hL]
    exact (hLu _ (subset_closure ⟨a, ha0, ha1, rfl⟩)).le
  rw [hxPN, ← hL] at this
  linarith

/-- Effects of `E` approximate an effect of the bidual on finitely many positive functionals. -/
lemma exists_effect_near {x : Bidual E} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (S : Finset (E →ₚ[ℝ] ℝ))
    {ε : ℝ} (hε : 0 < ε) : ∃ a : E, 0 ≤ a ∧ a ≤ 1 ∧ ∀ φ ∈ S, |φ a - x φ| < ε := by
  obtain ⟨v, ⟨a, ha0, ha1, rfl⟩, hv⟩ :=
    Metric.mem_closure_iff.1 (mem_closure_effectValues hx0 hx1 S) ε hε
  refine ⟨a, ha0, ha1, fun φ hφ => ?_⟩
  have := (dist_le_pi_dist (fun φ : S => x φ.1) (fun φ : S => φ.1 a) ⟨φ, hφ⟩).trans_lt hv
  rwa [Real.dist_eq, abs_sub_comm] at this

/-! ## C. Compatibility in the bidual -/

/-- The functions on positive functionals that are additive, positively homogeneous, lie between
`-φ 1` and `2 • φ 1`, and satisfy the joint-effect conditions for `x` and `y` up to `1 / (n + 1)` on
the finite set `S`. -/
def jointCandidates (x y : Bidual E) (i : Finset (E →ₚ[ℝ] ℝ) × ℕ) :
    Set ((E →ₚ[ℝ] ℝ) → ℝ) :=
  Set.pi Set.univ (fun φ => Set.Icc (-φ 1) (2 * φ 1)) ∩
    ({z | ∀ φ ψ, z (φ + ψ) = z φ + z ψ} ∩ {z | ∀ (c : ℝ≥0) φ, z (c • φ) = c * z φ}) ∩
    {z | ∀ φ ∈ i.1, -(1 / (i.2 + 1)) ≤ z φ ∧ z φ ≤ x φ + 1 / (i.2 + 1) ∧
      z φ ≤ y φ + 1 / (i.2 + 1) ∧ x φ + y φ - φ 1 ≤ z φ + 1 / (i.2 + 1)}

lemma isClosed_jointCandidates (x y : Bidual E) (i : Finset (E →ₚ[ℝ] ℝ) × ℕ) :
    IsClosed (jointCandidates x y i) := by
  refine ((isClosed_set_pi fun φ _ => isClosed_Icc).inter (IsClosed.inter ?_ ?_)).inter ?_
  · simp only [Set.ofPred_forall]
    exact isClosed_iInter fun φ => isClosed_iInter fun ψ => isClosed_eq (by fun_prop) (by fun_prop)
  · simp only [Set.ofPred_forall]
    exact isClosed_iInter fun c => isClosed_iInter fun φ => isClosed_eq (by fun_prop) (by fun_prop)
  · simp only [Set.ofPred_forall, Set.ofPred_and]
    exact isClosed_iInter fun φ => isClosed_iInter fun _ =>
      (isClosed_le (by fun_prop) (by fun_prop)).inter
        ((isClosed_le (by fun_prop) (by fun_prop)).inter
          ((isClosed_le (by fun_prop) (by fun_prop)).inter
            (isClosed_le (by fun_prop) (by fun_prop))))

/-- The values of an approximate joint effect of approximations of `x` and `y`: a candidate. -/
lemma mem_jointCandidates_of_near {x y : Bidual E} {i : Finset (E →ₚ[ℝ] ℝ) × ℕ} {a b c : E}
    {δ : ℝ} (hδ : δ • (∑ φ ∈ i.1, φ 1) ≤ 1 / (i.2 + 1) / 4) (hδ1 : δ ≤ 1)
    (ha : ∀ φ ∈ i.1, |φ a - x φ| < 1 / (i.2 + 1) / 4)
    (hb : ∀ φ ∈ i.1, |φ b - y φ| < 1 / (i.2 + 1) / 4) (ha1 : a ≤ 1)
    (hc : -(δ • (1 : E)) ≤ c ∧ c ≤ a + δ • 1 ∧ c ≤ b + δ • 1 ∧ a + b - 1 ≤ c + δ • 1) :
    (fun φ => φ c) ∈ jointCandidates x y i := by
  obtain ⟨h₀, h₁, h₂, h₃⟩ := hc
  have hv (φ : E →ₚ[ℝ] ℝ) : -(δ * φ 1) ≤ φ c ∧ φ c ≤ φ a + δ * φ 1 ∧ φ c ≤ φ b + δ * φ 1 ∧
      φ a + φ b - φ 1 ≤ φ c + δ * φ 1 := by
    have e₀ : φ (-(δ • 1)) ≤ φ c := φ.monotone' h₀
    have e₁ : φ c ≤ φ (a + δ • 1) := φ.monotone' h₁
    have e₂ : φ c ≤ φ (b + δ • 1) := φ.monotone' h₂
    have e₃ : φ (a + b - 1) ≤ φ (c + δ • 1) := φ.monotone' h₃
    simp only [map_neg, _root_.map_add, map_sub, map_smul, smul_eq_mul] at e₀ e₁ e₂ e₃
    exact ⟨e₀, e₁, e₂, e₃⟩
  refine ⟨⟨fun φ _ => ⟨?_, ?_⟩, fun _ _ => rfl, fun _ _ => rfl⟩, fun φ hφ => ?_⟩ <;> beta_reduce
  · nlinarith [(hv φ).1, map_nonneg φ OrderUnitSpace.one_nonneg]
  · have : φ a ≤ φ 1 := φ.monotone' ha1
    nlinarith [(hv φ).2.1, map_nonneg φ OrderUnitSpace.one_nonneg]
  · have hφ1 : δ * φ 1 ≤ 1 / (i.2 + 1) / 4 := by
      rcases le_total 0 δ with hδ0 | hδ0
      · exact (mul_le_mul_of_nonneg_left (Finset.single_le_sum (fun ψ _ =>
          map_nonneg ψ OrderUnitSpace.one_nonneg) hφ) hδ0).trans (by simpa using hδ)
      · nlinarith [map_nonneg φ OrderUnitSpace.one_nonneg, show (0 : ℝ) ≤ 1 / (i.2 + 1) / 4 by
          positivity]
    obtain ⟨e₀, e₁, e₂, e₃⟩ := hv φ
    have := abs_lt.1 (ha φ hφ)
    have := abs_lt.1 (hb φ hφ)
    refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith

/-- Approximate compatibility of the observables provides candidates for a joint effect in the
bidual. -/
lemma jointCandidates_nonempty
    (hE : ∀ (e f : Effect E) (δ : ℝ), 0 < δ → ∃ g : E, Effect.IsApproxBinaryJointEffect e f δ g)
    (x y : Effect (Bidual E)) (i : Finset (E →ₚ[ℝ] ℝ) × ℕ) :
    (jointCandidates (x : Bidual E) y i).Nonempty := by
  have hε : (0 : ℝ) < 1 / (i.2 + 1) / 4 := by positivity
  have hS : 0 ≤ ∑ φ ∈ i.1, φ 1 :=
    Finset.sum_nonneg fun φ _ => map_nonneg φ OrderUnitSpace.one_nonneg
  set δ : ℝ := 1 / (i.2 + 1) / 4 / (1 + ∑ φ ∈ i.1, φ 1)
  have hδ : 0 < δ := by positivity
  obtain ⟨a, ha0, ha1, ha⟩ := exists_effect_near (x := (x : Bidual E)) x.2.1 x.2.2 i.1 hε
  obtain ⟨b, hb0, hb1, hb⟩ := exists_effect_near (x := (y : Bidual E)) y.2.1 y.2.2 i.1 hε
  obtain ⟨c, hc⟩ := hE ⟨a, ha0, ha1⟩ ⟨b, hb0, hb1⟩ δ hδ
  refine ⟨_, mem_jointCandidates_of_near (δ := δ) ?_ ?_ ha hb ha1 hc⟩
  · rw [smul_eq_mul, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith
  · rw [div_le_one (by positivity)]
    have : (1 : ℝ) / (i.2 + 1) ≤ 1 := by rw [div_le_one (by positivity)]; simp
    linarith

lemma jointCandidates_antitone (x y : Bidual E) {i j : Finset (E →ₚ[ℝ] ℝ) × ℕ} (h : i ≤ j) :
    jointCandidates x y j ⊆ jointCandidates x y i := by
  rintro z ⟨hz, hz'⟩
  refine ⟨hz, fun φ hφ => ?_⟩
  have hn : 1 / ((j.2 : ℝ) + 1) ≤ 1 / (i.2 + 1) :=
    one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right h.2 1)
  obtain ⟨h₀, h₁, h₂, h₃⟩ := hz' φ (h.1 hφ)
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩

/-- Compatibility of the observables makes all candidate sets meet. -/
lemma nonempty_iInter_jointCandidates
    (hE : ∀ (e f : Effect E) (δ : ℝ), 0 < δ → ∃ g : E, Effect.IsApproxBinaryJointEffect e f δ g)
    (x y : Effect (Bidual E)) : (⋂ i, jointCandidates (x : Bidual E) y i).Nonempty := by
  classical
  have hT : IsCompact (Set.pi Set.univ fun φ : E →ₚ[ℝ] ℝ => Set.Icc (-φ 1) (2 * φ 1)) :=
    isCompact_univ_pi fun _ => isCompact_Icc
  exact IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed _
    (fun i j => ⟨i ⊔ j, jointCandidates_antitone _ _ le_sup_left,
      jointCandidates_antitone _ _ le_sup_right⟩)
    (jointCandidates_nonempty hE x y)
    (fun i => hT.of_isClosed_subset (isClosed_jointCandidates _ _ i)
      (Set.inter_subset_left.trans Set.inter_subset_left))
    (isClosed_jointCandidates _ _)

/-- A function in all candidate sets is a joint effect in the bidual. -/
lemma exists_isBinaryJointEffect_of_mem {x y : Effect (Bidual E)} {z : (E →ₚ[ℝ] ℝ) → ℝ}
    (hz : z ∈ ⋂ i, jointCandidates (x : Bidual E) y i) :
    ∃ z' : Bidual E, Effect.IsBinaryJointEffect x y z' := by
  simp only [Set.mem_iInter] at hz
  obtain ⟨⟨hT, hadd, hsmul⟩, -⟩ := hz (∅, 0)
  have hbound (φ : E →ₚ[ℝ] ℝ) : |z φ| ≤ 2 * φ 1 := by
    obtain ⟨h₁, h₂⟩ := hT φ trivial
    exact abs_le.2 ⟨by linarith [map_nonneg φ OrderUnitSpace.one_nonneg], h₂⟩
  have hineq (φ : E →ₚ[ℝ] ℝ) (n : ℕ) := (hz ({φ}, n)).2 φ (Finset.mem_singleton_self φ)
  refine ⟨mk z hadd hsmul
      ⟨(2 : ℝ) • (1 : E), fun φ => by rw [map_smul, smul_eq_mul]; exact hbound φ⟩,
    fun φ => Real.le_of_forall_nat_le_add fun n => by
      have := (hineq φ n).1; show (0 : ℝ) ≤ z φ + 1 / (n + 1); linarith,
    fun φ => Real.le_of_forall_nat_le_add fun n => (hineq φ n).2.1,
    fun φ => Real.le_of_forall_nat_le_add fun n => (hineq φ n).2.2.1,
    fun φ => Real.le_of_forall_nat_le_add fun n => ?_⟩
  simpa using (hineq φ n).2.2.2

/-- **Compatibility passes to the bidual.** If every two effects of `E` have joint effects up to any
error, every two effects of the bidual have a joint effect. -/
lemma exists_isBinaryJointEffect
    (hE : ∀ (e f : Effect E) (δ : ℝ), 0 < δ → ∃ g : E, Effect.IsApproxBinaryJointEffect e f δ g)
    (x y : Effect (Bidual E)) : ∃ z : Bidual E, Effect.IsBinaryJointEffect x y z :=
  exists_isBinaryJointEffect_of_mem (nonempty_iInter_jointCandidates hE x y).choose_spec

/-! ## D. Riesz decomposition in the bidual -/

/-- The least `t ≥ 0` with `x ≤ t • 1`. -/
noncomputable def gauge (x : Bidual E) : ℝ := sInf {t : ℝ | 0 ≤ t ∧ x ≤ t • 1}

lemma gauge_set_nonempty (x : Bidual E) : {t : ℝ | 0 ≤ t ∧ x ≤ t • 1}.Nonempty := by
  obtain ⟨n, hn⟩ := OrderUnitSpace.exists_nsmul_one_le x
  exact ⟨n, n.cast_nonneg, by rwa [Nat.cast_smul_eq_nsmul]⟩

lemma gauge_nonneg (x : Bidual E) : 0 ≤ gauge x :=
  le_csInf (gauge_set_nonempty x) fun _ ht => ht.1

lemma gauge_le {x : Bidual E} {t : ℝ} (ht : 0 ≤ t) (h : x ≤ t • 1) : gauge x ≤ t :=
  csInf_le ⟨0, fun _ h => h.1⟩ ⟨ht, h⟩

lemma le_gauge_smul (x : Bidual E) : x ≤ gauge x • 1 := fun φ => by
  have hall : ∀ t ∈ {t : ℝ | 0 ≤ t ∧ x ≤ t • 1}, x φ ≤ t * φ 1 := fun t ht => ht.2 φ
  change x φ ≤ gauge x * φ 1
  rcases (map_nonneg φ OrderUnitSpace.one_nonneg).eq_or_lt with h0 | hpos
  · obtain ⟨t, ht⟩ := gauge_set_nonempty x
    simpa [← h0] using hall t ht
  · exact (div_le_iff₀ hpos).1 <| le_csInf (gauge_set_nonempty x) fun t ht =>
      (div_le_iff₀ hpos).2 (hall t ht)

@[simp]
lemma gauge_zero : gauge (0 : Bidual E) = 0 :=
  le_antisymm (gauge_le le_rfl (by simp)) (gauge_nonneg _)

lemma eq_zero_of_gauge_eq_zero {x : Bidual E} (hx : 0 ≤ x) (h : gauge x = 0) : x = 0 :=
  le_antisymm (by simpa [h] using le_gauge_smul x) hx

lemma inv_gauge_smul_mem {x : Bidual E} (hx : 0 ≤ x) (h : 0 < gauge x) :
    (gauge x)⁻¹ • x ∈ (Effect (Bidual E) : Set (Bidual E)) :=
  ⟨smul_nonneg (inv_nonneg.2 h.le) hx, by
    rw [inv_smul_le_iff_of_pos h]; exact le_gauge_smul x⟩

/-- A nonnegative element below `c⁻¹ • r` and `d⁻¹ • w` vanishes when `r` and `w` have no nonzero
common lower bound. -/
lemma eq_zero_of_le_inv_smul {r w z : Bidual E} {c d : ℝ} (hc : 0 < c) (hd : 0 < d) (hz0 : 0 ≤ z)
    (hzr : z ≤ c⁻¹ • r) (hzw : z ≤ d⁻¹ • w) (horth : ∀ y, 0 ≤ y → y ≤ r → y ≤ w → y = 0) :
    z = 0 := by
  have hm : 0 < min c d := lt_min hc hd
  refine (smul_eq_zero.1 (horth (min c d • z) (smul_nonneg hm.le hz0) ?_ ?_)).resolve_left hm.ne'
  · calc min c d • z ≤ c • z := smul_le_smul_of_nonneg_right (min_le_left _ _) hz0
      _ ≤ c • (c⁻¹ • r) := smul_le_smul_of_nonneg_left hzr hc.le
      _ = r := smul_inv_smul₀ hc.ne' r
  · calc min c d • z ≤ d • z := smul_le_smul_of_nonneg_right (min_le_right _ _) hz0
      _ ≤ d • (d⁻¹ • w) := smul_le_smul_of_nonneg_left hzw hd.le
      _ = w := smul_inv_smul₀ hd.ne' w

variable (hc : ∀ x y : Effect (Bidual E), ∃ z : Bidual E, Effect.IsBinaryJointEffect x y z)
include hc

/-- Compatible nonnegative elements `r` and `w` with no nonzero common lower bound are spread
apart: `r / gauge r + w / gauge w ≤ 1`. -/
lemma gauge_mul_le_of_orthogonal {r w : Bidual E} (hr : 0 ≤ r) (hw : 0 ≤ w)
    (horth : ∀ c, 0 ≤ c → c ≤ r → c ≤ w → c = 0) (φ : E →ₚ[ℝ] ℝ) :
    gauge r * w φ ≤ gauge w * (gauge r * φ 1 - r φ) := by
  rcases (gauge_nonneg r).eq_or_lt with hT | hT
  · simp [eq_zero_of_gauge_eq_zero hr hT.symm]
  rcases (gauge_nonneg w).eq_or_lt with hs | hs
  · simp [eq_zero_of_gauge_eq_zero hw hs.symm]
  obtain ⟨z, hz0, hza, hzb, habz⟩ :=
    hc ⟨_, inv_gauge_smul_mem hr hT⟩ ⟨_, inv_gauge_smul_mem hw hs⟩
  obtain rfl := eq_zero_of_le_inv_smul hT hs hz0 hza hzb horth
  have key := habz φ
  simp only [coe_sub, coe_add, coe_smul, coe_one, coe_zero] at key
  have := mul_le_mul_of_nonneg_left (by linarith : (gauge r)⁻¹ * r φ + (gauge w)⁻¹ * w φ ≤ φ 1)
    (mul_pos hT hs).le
  rw [mul_add, show gauge r * gauge w * ((gauge r)⁻¹ * r φ) = gauge w * r φ by field_simp,
    show gauge r * gauge w * ((gauge w)⁻¹ * w φ) = gauge r * w φ by field_simp] at this
  nlinarith

/-- A nonnegative element below `w₁ + w₂` that has no nonzero common lower bound with `w₁` nor with
`w₂` vanishes. -/
lemma eq_zero_of_orthogonal {r w₁ w₂ : Bidual E} (hr : 0 ≤ r) (hw₁ : 0 ≤ w₁) (hw₂ : 0 ≤ w₂)
    (hle : r ≤ w₁ + w₂) (o₁ : ∀ c, 0 ≤ c → c ≤ r → c ≤ w₁ → c = 0)
    (o₂ : ∀ c, 0 ≤ c → c ≤ r → c ≤ w₂ → c = 0) : r = 0 := by
  by_contra hne
  have hT : 0 < gauge r :=
    (gauge_nonneg _).lt_of_ne fun h => hne (eq_zero_of_gauge_eq_zero hr h.symm)
  have hs₁ := gauge_nonneg w₁
  have hs₂ := gauge_nonneg w₂
  have hbound : r ≤ ((gauge w₁ + gauge w₂) * gauge r / (gauge r + gauge w₁ + gauge w₂)) • 1 :=
    fun φ => by
      have k₁ := gauge_mul_le_of_orthogonal hc hr hw₁ o₁ φ
      have k₂ := gauge_mul_le_of_orthogonal hc hr hw₂ o₂ φ
      have hsum := hle φ
      simp only [coe_add, coe_smul, coe_one] at hsum ⊢
      rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
      nlinarith
  have hlt : (gauge w₁ + gauge w₂) * gauge r / (gauge r + gauge w₁ + gauge w₂) < gauge r := by
    rw [div_lt_iff₀ (by positivity)]; nlinarith
  linarith [gauge_le (by positivity) hbound]

omit hc in
/-- Pairs of pieces of `u` below `v₁` and `v₂`. -/
def decompositions (v₁ v₂ u : Bidual E) : Set (Bidual E × Bidual E) :=
  {p | p.1 ∈ Set.Icc 0 v₁ ∧ p.2 ∈ Set.Icc 0 v₂ ∧ p.1 + p.2 ≤ u}

omit hc in
/-- A chain of decompositions has an upper bound among the decompositions: its supremum. -/
lemma exists_upperBound_of_isChain {v₁ v₂ u : Bidual E} {C : Set (Bidual E × Bidual E)}
    (hCA : C ⊆ decompositions v₁ v₂ u) (hC : IsChain (· ≤ ·) C) {y : Bidual E × Bidual E}
    (hy : y ∈ C) : ∃ ub ∈ decompositions v₁ v₂ u, ∀ z ∈ C, z ≤ ub := by
  have : Nonempty C := ⟨⟨y, hy⟩⟩
  have hdir : Directed (· ≤ ·) (fun i : C => (i : Bidual E × Bidual E)) := hC.directed
  have hdir₁ := Directed.mono_comp (g := Prod.fst) (· ≤ ·)
    (fun (a b : Bidual E × Bidual E) (h : a ≤ b) => h.1) hdir
  have hdir₂ := Directed.mono_comp (g := Prod.snd) (· ≤ ·)
    (fun (a b : Bidual E × Bidual E) (h : a ≤ b) => h.2) hdir
  have hb₁ (i : C) : (i : Bidual E × Bidual E).1 ≤ v₁ := (hCA i.2).1.2
  have hb₂ (i : C) : (i : Bidual E × Bidual E).2 ≤ v₂ := (hCA i.2).2.1.2
  have hl₁ := isLUB_ciSup hdir₁ hb₁
  have hl₂ := isLUB_ciSup hdir₂ hb₂
  refine ⟨(ciSup hdir₁ hb₁, ciSup hdir₂ hb₂), ⟨⟨(hCA hy).1.1.trans (hl₁.1 ⟨⟨y, hy⟩, rfl⟩),
    hl₁.2 (Set.forall_mem_range.2 hb₁)⟩, ⟨(hCA hy).2.1.1.trans (hl₂.1 ⟨⟨y, hy⟩, rfl⟩),
    hl₂.2 (Set.forall_mem_range.2 hb₂)⟩, fun φ => ?_⟩,
    fun z hz => ⟨hl₁.1 ⟨⟨z, hz⟩, rfl⟩, hl₂.1 ⟨⟨z, hz⟩, rfl⟩⟩⟩
  simp only [coe_add, ciSup_apply, Function.comp_apply]
  rw [← Real.ciSup_add (bddAbove_apply hb₁ φ) (bddAbove_apply hb₂ φ) fun i j =>
    (hdir i j).imp fun _ h => ⟨h.1.1 φ, h.2.2 φ⟩]
  exact ciSup_le fun i => (hCA i.2).2.2 φ

omit hc in
/-- The remainder of a maximal decomposition has no nonzero common lower bound with the room left
below `v₁`. -/
lemma orthogonal_fst_of_maximal {v₁ v₂ u : Bidual E} {p : Bidual E × Bidual E}
    (hp : Maximal (· ∈ decompositions v₁ v₂ u) p) :
    ∀ c, 0 ≤ c → c ≤ u - p.1 - p.2 → c ≤ v₁ - p.1 → c = 0 := fun c hc0 hcr hcw => by
  have hmem : (p.1 + c, p.2) ∈ decompositions v₁ v₂ u :=
    ⟨⟨add_nonneg hp.1.1.1 hc0, calc p.1 + c ≤ p.1 + (v₁ - p.1) := by gcongr
        _ = v₁ := by abel⟩, hp.1.2.1, calc p.1 + c + p.2 ≤ p.1 + (u - p.1 - p.2) + p.2 := by gcongr
        _ = u := by abel⟩
  have := (hp.2 hmem (Prod.mk_le_mk.2 ⟨le_add_of_nonneg_right hc0, le_rfl⟩)).1
  exact le_antisymm (by simpa using this) hc0

omit hc in
/-- The remainder of a maximal decomposition has no nonzero common lower bound with the room left
below `v₂`. -/
lemma orthogonal_snd_of_maximal {v₁ v₂ u : Bidual E} {p : Bidual E × Bidual E}
    (hp : Maximal (· ∈ decompositions v₁ v₂ u) p) :
    ∀ c, 0 ≤ c → c ≤ u - p.1 - p.2 → c ≤ v₂ - p.2 → c = 0 := fun c hc0 hcr hcw => by
  have hmem : (p.1, p.2 + c) ∈ decompositions v₁ v₂ u :=
    ⟨hp.1.1, ⟨add_nonneg hp.1.2.1.1 hc0, calc p.2 + c ≤ p.2 + (v₂ - p.2) := by gcongr
        _ = v₂ := by abel⟩, calc p.1 + (p.2 + c) ≤ p.1 + (p.2 + (u - p.1 - p.2)) := by gcongr
        _ = u := by abel⟩
  have := (hp.2 hmem (Prod.mk_le_mk.2 ⟨le_rfl, le_add_of_nonneg_right hc0⟩)).2
  exact le_antisymm (by simpa using this) hc0

/-- **Riesz decomposition in the bidual.** When every two effects of the bidual are compatible,
a maximal decomposition of `u` below `v₁ + v₂` leaves no remainder. -/
lemma hasRieszDecomposition : HasRieszDecomposition (Bidual E) := by
  intro v₁ v₂ u hv₁ hv₂ hu
  obtain ⟨p, -, hp⟩ := zorn_le_nonempty₀ (decompositions v₁ v₂ u)
    (fun _ hCA hC _ hy => exists_upperBound_of_isChain hCA hC hy) 0
    ⟨⟨le_rfl, hv₁⟩, ⟨le_rfl, hv₂⟩, by simpa using hu.1⟩
  have hr0 : u - p.1 - p.2 = 0 := eq_zero_of_orthogonal hc
    (by rw [sub_sub, sub_nonneg]; exact hp.1.2.2) (sub_nonneg.2 hp.1.1.2) (sub_nonneg.2 hp.1.2.1.2)
    (by calc u - p.1 - p.2 ≤ v₁ + v₂ - p.1 - p.2 := by gcongr; exact hu.2
          _ = v₁ - p.1 + (v₂ - p.2) := by abel)
    (orthogonal_fst_of_maximal hp) (orthogonal_snd_of_maximal hp)
  refine ⟨p.1, hp.1.1, ?_⟩
  rw [sub_sub, sub_eq_zero] at hr0
  rw [hr0, add_sub_cancel_left]
  exact hp.1.2.1

end Bidual

namespace ProbabilisticTheory

open scoped NNReal
variable {E : Type*} [OrderUnitSpace E]

/-! ## E. Compatibility makes the dual cone a lattice -/

/-- An observable as a positive map into the bidual. -/
def _root_.Bidual.ofEPos : E →ₚ[ℝ] Bidual E :=
  .mk₀ Bidual.ofE fun _ hA φ => map_nonneg φ hA

/-- If the bidual has Riesz decomposition, the positive functionals on `E` form a lattice: the least
upper bound in the bidual, restricted to `E`, is the least upper bound. -/
lemma isClassical_of_bidual (hF : HasRieszDecomposition (Bidual E)) :
    IsClassical E := by
  intro φ ψ
  obtain ⟨χ, hχ⟩ := hF.hasLatticeDualCone (Bidual.eval φ) (Bidual.eval ψ)
  refine ⟨χ.comp Bidual.ofEPos, fun θ hθ f hf => ?_, fun θ hθ f hf => ?_⟩
  · have hθ' : Bidual.eval θ ∈ ({Bidual.eval φ, Bidual.eval ψ} : Set _) := by
      rcases hθ with rfl | rfl
      exacts [Set.mem_insert _ _, Set.mem_insert_of_mem _ rfl]
    exact hχ.1 hθ' (Bidual.ofE f) fun φ => map_nonneg φ hf
  · have hub : Bidual.eval θ ∈ upperBounds ({Bidual.eval φ, Bidual.eval ψ} : Set _) := by
      rintro _ (rfl | rfl)
      exacts [Bidual.eval_mono (hθ (Set.mem_insert _ _)),
        Bidual.eval_mono (hθ (Set.mem_insert_of_mem _ rfl))]
    exact hχ.2 hub (Bidual.ofE f) fun φ => map_nonneg φ hf

/-- If every two effects have joint effects up to any error, the positive functionals form a
lattice. -/
lemma isClassical_of_approxJoint
    (h : ∀ (e f : Effect E) (δ : ℝ), 0 < δ → ∃ g : E, Effect.IsApproxBinaryJointEffect e f δ g) :
    IsClassical E :=
  isClassical_of_bidual <| Bidual.hasRieszDecomposition <|
    Bidual.exists_isBinaryJointEffect h

/-- **Compatibility characterizes classicality (Kuramochi).** If every two yes/no measurements are
jointly measurable, the positive functionals form a lattice: the state space is a Choquet
simplex. -/
lemma isClassical_of_jointlyMeasurable {F : Type*} [ArchimedeanOrderUnitSpace F]
    (h : ∀ e f : Effect F, Measurement.JointlyMeasurable (Effect.binaryMeasurement e)
      (Effect.binaryMeasurement f)) : IsClassical F :=
  isClassical_of_approxJoint fun e f _ hδ =>
    ((Effect.jointlyMeasurable_binaryMeasurement_iff e f).1 (h e f)).imp fun _ hg =>
      hg.isApprox hδ.le

/-! ## F. The characterization -/

section Complete

open scoped ArchimedeanOrderUnitSpace

variable {F : Type*} [ArchimedeanOrderUnitSpace F] [CompleteSpace F]

/-- On a complete Archimedean order-unit space whose positive functionals form a lattice, every two
effects have a joint effect. -/
lemma IsClassical.exists_isBinaryJointEffect (hF : IsClassical F) (e f : Effect F) :
    ∃ g : F, Effect.IsBinaryJointEffect e f g := by
  obtain ⟨g, hlo, hhi⟩ := hF.exists_interpolant (a := ![0, (e : F) + f - 1]) (b := ![e, f]) <| by
    simp only [Fin.forall_fin_two, Matrix.cons_val_zero, Matrix.cons_val_one]
    refine ⟨⟨e.2.1, f.2.1⟩, ?_, ?_⟩
    · rw [add_sub_assoc]; exact add_le_of_nonpos_right (sub_nonpos.2 f.2.2)
    · rw [add_comm, add_sub_assoc]; exact add_le_of_nonpos_right (sub_nonpos.2 e.2.2)
  exact ⟨g, hlo 0, hhi 0, hhi 1, hlo 1⟩

/-- **Kuramochi's theorem.** On a complete Archimedean order-unit space, the positive functionals
form a lattice — the state space is a Choquet simplex — exactly when every two yes/no measurements
are jointly measurable. -/
lemma isClassical_iff_jointlyMeasurable :
    IsClassical F ↔ ∀ e f : Effect F,
      Measurement.JointlyMeasurable (Effect.binaryMeasurement e)
        (Effect.binaryMeasurement f) :=
  ⟨fun h e f => (Effect.jointlyMeasurable_binaryMeasurement_iff e f).2
    (h.exists_isBinaryJointEffect e f), isClassical_of_jointlyMeasurable⟩

end Complete

end ProbabilisticTheory
