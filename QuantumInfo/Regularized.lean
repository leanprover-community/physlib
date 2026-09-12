/-
Copyright (c) 2025 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
-/
module

public import QuantumInfo.ForMathlib.Superadditive
public import Mathlib.Order.LiminfLimsup
public import Mathlib.Topology.Order.LiminfLimsup
public import Mathlib.Topology.Order.MonotoneConvergence

/-! Definition of "Regularized quantities" as are common in information theory,
from one-shot versions, and good properties coming from Fekete's lemma.
-/

@[expose] public section

variable {T : Type*} [ConditionallyCompleteLattice T]

/-- An `InfRegularized` value is the lim sup of value at each natural number, but requires
 a proof of lower- and upper-bounds to be defined. -/
noncomputable def InfRegularized (fn : ℕ → T) {lb ub : T}
    (_ : ∀ n, lb ≤ fn n) (_ : ∀ n, fn n ≤ ub) : T :=
  Filter.atTop.liminf fn

/-- A `SupRegularized` value is the lim sup of value at each natural number, but requires
 a proof of lower- and upper-bounds to be defined. -/
noncomputable def SupRegularized (fn : ℕ → T) {lb ub : T}
    (_ : ∀ n, lb ≤ fn n) (_ : ∀ n, fn n ≤ ub) : T :=
  Filter.atTop.limsup fn

namespace InfRegularized

variable {fn : ℕ → T} {_lb _ub : T} {hl : ∀ n, _lb ≤ fn n} {hu : ∀ n, fn n ≤ _ub}

/-- The `InfRegularized` value is also lower bounded. -/
theorem lb : _lb ≤ InfRegularized fn hl hu := by
  rw [InfRegularized, Filter.liminf_eq]
  refine le_csSup ⟨_ub, fun a ha => ?_⟩ (Filter.Eventually.of_forall hl)
  obtain ⟨n, hn⟩ := Filter.eventually_atTop.mp ha
  exact (hn n le_rfl).trans (hu n)

/-- The `InfRegularized` value is also upper bounded. -/
theorem ub : InfRegularized fn hl hu ≤ _ub := by
  unfold InfRegularized;
  simp +decide [Filter.liminf_eq];
  refine' csSup_le _ _;
  · exact ⟨ _, ⟨ 0, fun n _ => hl n ⟩ ⟩;
  · exact fun b hb => by rcases hb with ⟨ n, hn ⟩ ; exact le_trans ( hn n le_rfl ) ( hu n ) ;

/-- For `Antitone` functions, the `InfRegularized` is the supremum of values. -/
theorem anti_inf (h : Antitone fn) :
    InfRegularized fn hl hu = sInf (Set.range fn) := by
  unfold InfRegularized; simp +decide [ Filter.liminf_eq ] ;
  rw [ @csSup_eq_of_forall_le_of_forall_lt_exists_gt ];
  · exact ⟨ _, ⟨ 0, fun n _ => hl n ⟩ ⟩;
  · rintro a ⟨ n, hn ⟩;
    exact le_csInf ⟨ _, Set.mem_range_self n ⟩ fun x hx => by rcases hx with ⟨ m, rfl ⟩ ; exact hn _ ( le_max_left _ _ ) |> le_trans <| h <| le_max_right _ _;
  · exact fun w hw => ⟨ _, ⟨ 0, fun n _ => csInf_le ⟨ _lb, Set.forall_mem_range.2 hl ⟩ ⟨ n, rfl ⟩ ⟩, hw ⟩

/-- For `Antitone` functions, the `InfRegularized` is lower bounded by
  any particular value. -/
theorem anti_ub (h : Antitone fn) : ∀ n, InfRegularized fn hl hu ≤ fn n := by
  intro n
  rw [InfRegularized, Filter.liminf_eq]
  refine csSup_le ⟨_lb, Filter.Eventually.of_forall hl⟩ fun b hb => ?_
  obtain ⟨m, hm⟩ := Filter.eventually_atTop.mp hb
  exact (hm (max m n) (le_max_left _ _)).trans (h (le_max_right _ _))

end InfRegularized

namespace SupRegularized

variable {fn : ℕ → T} {_lb _ub : T} {hl : ∀ n, _lb ≤ fn n} {hu : ∀ n, fn n ≤ _ub}

/-- The `SupRegularized` value is also lower bounded. -/
theorem lb : _lb ≤ SupRegularized fn hl hu := by
  -- Suppose, for contradiction, that $\mathrm{InfRegularized} \; fn < \mathrm{SupRegularized} \; fn$.
  by_contra h_contra;
  -- By definition of `SupRegularized`, we have that $\mathrm{SupRegularized} \; fn \geq \mathrm{InfRegularized} \; fn$.
  have h_sup_ge_inf : SupRegularized fn hl hu ≥ InfRegularized fn hl hu := by
    apply_rules [ Filter.liminf_le_limsup ];
    · exact ⟨ _ub, Filter.eventually_atTop.2 ⟨ 0, fun n hn => hu n ⟩ ⟩;
    · exact ⟨ _, Filter.eventually_atTop.2 ⟨ 0, fun n hn => hl n ⟩ ⟩;
  exact h_contra ( le_trans ( by exact InfRegularized.lb ) h_sup_ge_inf )

/-- The `SupRegularized` value is also upper bounded. -/
theorem ub : SupRegularized fn hl hu ≤ _ub := by
  -- By definition of `limsup`, we know that for any `ε > 0`, there exists an `N` such that for all `n ≥ N`, `fn n ≤ _ub + ε`.
  apply csInf_le;
  · exact ⟨ _, fun x hx => hx.exists.choose_spec.trans' ( hl _ ) ⟩;
  · aesop

/-- For `Monotone` functions, the `SupRegularized` is the supremum of values. -/
theorem mono_sup (h : Monotone fn) :
    SupRegularized fn hl hu = sSup { fn n | n : ℕ} := by
  unfold SupRegularized;
  simp +decide [ Filter.limsup_eq, Filter.eventually_atTop ];
  refine' le_antisymm _ _;
  · refine' csInf_le _ _;
    · exact ⟨ _lb, by rintro x ⟨ n, hn ⟩ ; exact le_trans ( hl n ) ( hn n le_rfl ) ⟩;
    · exact ⟨ 0, fun n _ => le_csSup ⟨ _ub, by rintro x ⟨ m, rfl ⟩ ; exact hu m ⟩ ⟨ n, rfl ⟩ ⟩;
  · refine' csSup_le _ _;
    · exact ⟨ _, ⟨ 0, rfl ⟩ ⟩;
    · norm_num +zetaDelta at *;
      exact fun n => le_csInf ⟨ _ub, ⟨ n, fun m hm => hu m ⟩ ⟩ fun x hx => by rcases hx with ⟨ m, hm ⟩ ; exact hm _ ( le_max_left _ _ ) |> le_trans ( h ( le_max_right _ _ ) ) ;

/-- For `Monotone` functions, the `SupRegularized` is lower bounded by
  any particular value. -/
theorem mono_lb (h : Monotone fn) : ∀ n, fn n ≤ SupRegularized fn hl hu := by
  intro n
  unfold SupRegularized;
  refine' le_csInf _ _;
  · exact ⟨ _ub, Filter.eventually_atTop.2 ⟨ 0, fun n hn => hu n ⟩ ⟩;
  · simp +zetaDelta at *;
    exact fun b m hm => le_trans ( h ( Nat.le_max_left _ _ ) ) ( hm _ ( Nat.le_max_right _ _ ) )

end SupRegularized

section real

variable {fn : ℕ → ℝ} {_lb _ub : ℝ} {hl : ∀ n, _lb ≤ fn n} {hu : ∀ n, fn n ≤ _ub}

/-- Negating a real sequence swaps `liminf` and `limsup`. -/
private theorem liminf_neg (s : ℕ → ℝ) :
    Filter.liminf (fun n ↦ -s n) Filter.atTop = -Filter.limsup s Filter.atTop := by
  rw [Filter.liminf_eq, Filter.limsup_eq, Real.sInf_def, neg_neg]
  congr 1
  ext a
  simp [le_neg]

theorem InfRegularized.to_SupRegularized : InfRegularized fn hl hu = -SupRegularized (-fn ·)
    (lb := -_ub) (ub := -_lb) (neg_le_neg_iff.mpr <| hu ·) (neg_le_neg_iff.mpr <| hl ·) := by
  rw [InfRegularized, SupRegularized, ← liminf_neg]
  simp

theorem SupRegularized.to_InfRegularized : SupRegularized fn hl hu = -InfRegularized (-fn ·)
    (lb := -_ub) (ub := -_lb) (neg_le_neg_iff.mpr <| hu ·) (neg_le_neg_iff.mpr <| hl ·) := by
  rw [InfRegularized, SupRegularized, liminf_neg, neg_neg]

/-- For `Antitone` functions, the value `Filter.Tendsto` the `InfRegularized` value. -/
theorem InfRegularized.anti_tendsto (h : Antitone fn) :
    Filter.Tendsto fn .atTop (nhds (InfRegularized fn hl hu)) := by
  convert tendsto_atTop_ciInf h ⟨_lb, fun _ ⟨a,b⟩ ↦ b ▸ hl a⟩
  rw [InfRegularized.anti_inf h, iInf.eq_1]

variable {f₁ : ℕ → ℝ} {_lb _ub : ℝ} {hl : ∀ n, _lb ≤ fn n} {hu : ∀ n, fn n ≤ _ub}

theorem InfRegularized.of_Subadditive (hf : Subadditive (fun n ↦ fn n * n))
    :
    hf.lim = InfRegularized fn hl hu := by
  have h₁ := hf.tendsto_lim (by
    use min 0 _lb
    rw [mem_lowerBounds]
    rintro x ⟨y,(rfl : _ / _ = _)⟩
    rcases y with (_|n)
    · simp
    · refine inf_le_right.trans ?_
      rw [mul_div_assoc, div_self (by positivity), mul_one]
      exact hl (n + 1)
  )
  have h₂ : Filter.Tendsto fn .atTop (nhds hf.lim) := by
    refine h₁.congr' ?_
    filter_upwards [Filter.eventually_ne_atTop 0] with n hn
    have : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
    field_simp
  exact h₂.liminf_eq.symm
