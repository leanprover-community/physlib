/-
Copyright (c) 2025 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Order.CompletePartialOrder

@[expose] public section

--Can this be rewritten more generally? For `finiteness` to work, I don't know how.
--PR'ed in #33105
@[aesop (rule_sets := [finiteness]) unsafe apply]
lemma ite_eq_top {α : Type*} [Top α] (h : Prop) [Decidable h] {x y : α} (hx : x ≠ ⊤) (hy : y ≠ ⊤) :
    (if h then x else y) ≠ ⊤ := by
  split <;> assumption

section subtype_val_iSup

/-
When
https://leanprover.zulipchat.com/#narrow/channel/287929-mathlib4/topic/diamond.20in.20ConditionallyCompleteLattice/near/538053239
is fixed, the declarations below should be changed to
```
theorem subtype_val_iSup {ι α : Type*} [ConditionallyCompleteLattice α] {s : Set α} {f : ι → α}
    [Inhabited ↑s] [s.OrdConnected] (h : ∀ i, f i ∈ s) :
    (⨆ i, (⟨f i, h i⟩ : ↑s)).val = ⨆ i, f i := by
  sorry

theorem subtype_val_iSup' {ι α : Type*} [ConditionallyCompleteLattice α] {s : Set α} {f : ι → α}
    [Inhabited ↑s] [s.OrdConnected] (h : ∀ i, f i ∈ s) :
    ⨆ i, (⟨f i, h i⟩ : ↑s) = ⟨⨆ i, f i, by sorry⟩ := by
  rw [Subtype.eq_iff, subtype_val_iSup]
```
Sadly, though, there's a "diamond" and we need it with the other data (the one we specify more narrowly
below).
-/
variable {ι α : Type*} [i : Nonempty ι] [ConditionallyCompleteLattice α]
  {f : ι → α} {a b : α} [Fact (a ≤ b)]

/- This isn't marked as `simp` because rewriting from a sup over a `CompleteLattice` into a
`ConditionallyCompleteLattice` would, pretty often, be undesirable. -/
lemma subtype_val_iSup (h : ∀ i, f i ∈ Set.Icc a b) :
    (⨆ i, (⟨f i, h i⟩ : ↑(Set.Icc a b))).val = ⨆ i, f i := by
  simp only [iSup, sSup, Set.range_eq_empty_iff, not_isEmpty_of_nonempty, reduceDIte]
  congr 1; ext1
  simp

lemma subtype_val_iSup' (h : ∀ i, f i ∈ Set.Icc a b) :
    ⨆ i, (⟨f i, h i⟩ : ↑(Set.Icc a b)) =
      ⟨⨆ i, f i, ⟨(h i.some).1.trans (le_ciSup ⟨b, by intro; grind⟩ _), ciSup_le (h ·|>.2)⟩⟩ := by
  rw [Subtype.ext_iff, subtype_val_iSup]

/- This isn't marked as `simp` because rewriting from a sup over a `CompleteLattice` into a
`ConditionallyCompleteLattice` would, pretty often, be undesirable. -/
lemma subtype_val_iInf (h : ∀ i, f i ∈ Set.Icc a b) :
    (⨅ i, (⟨f i, h i⟩ : ↑(Set.Icc a b))).val = ⨅ i, f i := by
  simp only [iInf, sInf, Set.range_eq_empty_iff, not_isEmpty_of_nonempty, reduceDIte]
  congr 1; ext1
  simp

lemma subtype_val_iInf' (h : ∀ i, f i ∈ Set.Icc a b) :
    ⨅ i, (⟨f i, h i⟩ : ↑(Set.Icc a b)) =
      ⟨⨅ i, f i, ⟨le_ciInf (h ·|>.1), (ciInf_le ⟨a, by intro; grind⟩ _).trans (h i.some).2⟩⟩ := by
  rw [Subtype.ext_iff, subtype_val_iInf]

end subtype_val_iSup

open scoped ENNReal Topology in
/-- Analogous to `bdd_le_mul_tendsto_zero`, for `ENNReal` (which otherwise lacks a continuous
multiplication function). The product of a sequence that tends to zero with any bounded sequence
also tends to zero. -/
protected lemma ENNReal.bdd_le_mul_tendsto_zero
  {α : Type*} {l : Filter α} {f g : α → ℝ≥0∞} {b : ℝ≥0∞} (hb : b ≠ ⊤)
  (hf : l.Tendsto f (𝓝 0)) (hg : ∀ᶠ (x : α) in l, g x ≤ b) :
    l.Tendsto (fun x ↦ f x * g x) (𝓝 0) := by
  rw [ENNReal.tendsto_nhds_zero] at hf ⊢
  intro ε hεpos
  by_cases hb_pos : 0 < b
  · filter_upwards [hf (ε / b) (by simp [hb, hεpos.ne']), hg] with x hx₁ hx₂
    grw [hx₁, hx₂, ENNReal.div_mul_cancel hb_pos.ne' hb]
  · filter_upwards [hg] with x hx
    grind [not_lt, nonpos_iff_eq_zero, mul_zero, zero_le]

--PULLOUT: Belongs in Mathlib/Algebra/Order/Group/Pointwise/CompleteLattice.lean
-- (after appropriately generalizing to MulPosMono)
open scoped Pointwise in
lemma csInf_mul_nonneg {s t : Set ℝ}
  (hs₀ : s.Nonempty) (hs₁ : ∀ x ∈ s, 0 ≤ x) (ht₀ : t.Nonempty) (ht₁ : ∀ x ∈ t, 0 ≤ x) :
    sInf (s * t) = sInf s * sInf t := by
  apply le_antisymm
  · set a := sInf s
    set b := sInf t
    have h_eps : ∀ ε > 0, ∃ x ∈ s, x < a + ε ∧ ∃ y ∈ t, y < b + ε := by
      intro ε ε_pos
      obtain ⟨x, hx₁, hx₂⟩ := exists_lt_of_csInf_lt hs₀ (lt_add_of_pos_right a ε_pos)
      obtain ⟨y, hy₁, hy₂⟩ := exists_lt_of_csInf_lt ht₀ (lt_add_of_pos_right b ε_pos)
      exact ⟨x, hx₁, hx₂, y, hy₁, hy₂⟩
    have h_prod_eps : ∀ ε > 0, ∃ x ∈ s, ∃ y ∈ t, x * y < (a + ε) * (b + ε) := by
      intro ε hε
      obtain ⟨x, hx₁, hx₂, y, hy₁, hy₂⟩ := h_eps ε hε
      exact ⟨x, hx₁, y, hy₁, by nlinarith [hs₁ x hx₁, ht₁ y hy₁]⟩
    have h_lim : Filter.Tendsto (fun ε => (a + ε) * (b + ε)) (nhdsWithin 0 (Set.Ioi 0)) (nhds (a * b)) := by
      exact tendsto_nhdsWithin_of_tendsto_nhds (Continuous.tendsto' (by continuity) _ _ (by norm_num))
    apply le_of_tendsto_of_tendsto tendsto_const_nhds h_lim
    filter_upwards [self_mem_nhdsWithin] with ε hε
    specialize h_prod_eps ε hε
    choose x hx y hy using h_prod_eps
    refine le_trans ?_ hy.right.le
    refine csInf_le ⟨0, ?_⟩ ?_
    · rintro x ⟨u, hu, v, hv, rfl⟩
      exact mul_nonneg (hs₁ u hu) (ht₁ v hv)
    · exact ⟨_, hx, _, hy.left, rfl⟩
  · apply le_csInf (hs₀.mul ht₀)
    rintro _ ⟨x, hx, y, hy, rfl⟩
    apply mul_le_mul
    · exact csInf_le ⟨0, hs₁⟩ hx
    · exact csInf_le ⟨0, ht₁⟩ hy
    · exact Real.sInf_nonneg ht₁
    · exact hs₁ x hx

/--
If two functions from finite types have the same multiset of values, there exists a bijection between the domains that commutes with the functions.
-/
lemma Multiset.map_univ_eq_iff {α β : Type*} [Fintype α] (f g : α → β) :
    Multiset.map f Finset.univ.val = Multiset.map g Finset.univ.val ↔ ∃ (e : α ≃ α), f = g ∘ e := by
  apply Iff.intro
  · intro a
    classical
    -- Since these two multisets are equal, their elements must be equal up to permutation.
    have h_perm : ∃ e : α ≃ α, ∀ x, f x = g (e x) := by
      have h_count_eq : ∀ y : β, Finset.card (Finset.filter (fun x => f x = y) Finset.univ) = Finset.card (Finset.filter (fun x => g x = y) Finset.univ) := by
        intro y;
        replace a := congr_arg ( fun m => m.count y ) a;
        simp_all ( config := { decide := Bool.true } ) [ Multiset.count_map ];
        simp_all [ eq_comm ]
        exact a
      have h_perm : ∀ y : β, ∃ e : { x : α // f x = y } ≃ { x : α // g x = y }, True := by
        intro y
        simp_all only [exists_const_iff, and_true]
        exact ⟨ Fintype.equivOfCardEq <| by simpa [ Fintype.card_subtype ] using h_count_eq y ⟩;
      choose e he using h_perm;
      refine' ⟨ _, _ ⟩;
      exact ( Equiv.sigmaFiberEquiv f ).symm.trans ( Equiv.sigmaCongrRight e ) |> Equiv.trans <| Equiv.sigmaFiberEquiv g;
      intro x
      specialize e ( f x )
      rename_i e_1
      simp_all only [implies_true, Equiv.trans_apply, Equiv.sigmaCongrRight_apply,
        Equiv.sigmaFiberEquiv_apply]
      exact Eq.symm ( e_1 ( f x ) ⟨ x, rfl ⟩ |>.2 );
    exact ⟨ h_perm.choose, funext h_perm.choose_spec ⟩;
  · intro a
    obtain ⟨w, h⟩ := a
    subst h
    simp_all only [Function.comp_apply, Finset.univ]
    -- Since $w$ is a bijection, the multiset of $w(x)$ for $x$ in the original multiset is just a permutation of the original multiset.
    have h_perm : Multiset.map (fun x => w x) (Finset.val Fintype.elems) = Finset.val Fintype.elems := by
      exact Multiset.map_univ_val_equiv w;
    conv_rhs => rw [ ← h_perm ];
    simp +zetaDelta at *

/--
If two functions from finite types have the same multiset of values, there exists a bijection between the domains that commutes with the functions.
-/
lemma exists_equiv_of_multiset_map_eq {α β γ : Type*} [Fintype α] [Fintype β] [DecidableEq γ]
    (f : α → γ) (g : β → γ) (h : Multiset.map f Finset.univ.val = Multiset.map g Finset.univ.val) :
    ∃ e : α ≃ β, f = g ∘ e := by
  -- Since the multisets of values are equal, the cardinalities of the domains must be equal (as the multiset size is the cardinality of the domain). Thus there exists a bijection `σ : α ≃ β`.
  obtain ⟨σ, hσ⟩ : ∃ σ : α ≃ β, Multiset.map f Finset.univ.val = Multiset.map (g ∘ σ) Finset.univ.val := by
    have h_card : Fintype.card α = Fintype.card β := by
      simpa using congr_arg Multiset.card h;
    obtain σ := Fintype.equivOfCardEq h_card
    use σ
    have h_multiset_eq : Multiset.map g Finset.univ.val = Multiset.map (g ∘ σ) Finset.univ.val := by
      rw [ ← Multiset.map_univ_val_equiv σ ] ;
      rw [ Multiset.map_map ]
    exact h.trans h_multiset_eq;
  -- By `Multiset.map_univ_eq_iff`, there exists `e' : α ≃ α` such that `f = (g ∘ σ) ∘ e'`.
  obtain ⟨e', he'⟩ : ∃ e' : α ≃ α, f = (g ∘ σ) ∘ e' := by
    exact (Multiset.map_univ_eq_iff f (g ∘ ⇑σ)).mp hσ;
  exact ⟨ e'.trans σ, by simp_all [ Function.comp ]; grind⟩
