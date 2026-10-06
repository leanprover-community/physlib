/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.Mathematics.Order.PositiveDual.RieszKantorovich
public import PhyslibAlpha.Mathematics.Sublinear
public import Mathlib.Basic.Real.Pointwise

/-!
# Approximate interpolation

Approximate interpolation between finite families when the positive functionals form a lattice.

## i. Overview

Given finitely many lower elements `a i` below finitely many upper elements `b j` of an ordered
real vector space with an order unit `u`, an interpolant is an element `g` with `a i ≤ g ≤ b j` for
all `i` and `j`. When the positive functionals form a lattice, interpolants exist up to any error:
for every `ε > 0` some `g` has `a i ≤ g + ε • u` and `g ≤ b j + ε • u`. The proof measures the
failure to interpolate by a sublinear gauge; Hahn–Banach turns a linear functional below it into
positive functionals, and refining these in the lattice of positive functionals shows the gauge is
not positive.

## ii. Key results

- `HasLatticeDualCone.exists_table` : two finite families of positive functionals with the same sum
  have a common refinement.
- `Interpolation.gauge` : the interpolation gauge.
- `Interpolation.exists_linear_le_gauge` : a linear functional below the interpolation gauge.
- `HasLatticeDualCone.exists_approx_interpolant` : approximate interpolants exist.

## iii. Table of contents

- A. Refinement tables
- B. The interpolation gauge
- C. Approximate interpolants

## iv. References

* None.

-/

@[expose] public section

open PositiveLinearMap
open scoped Pointwise

variable {E : Type*} [AddCommGroup E] [PartialOrder E] [IsOrderedAddMonoid E] [Module ℝ E]
  [PosSMulMono ℝ E] [IsDirectedOrder E] {u : E} (hu : IsOrderUnit u)

/-! ## A. Refinement tables -/

namespace HasLatticeDualCone

variable (hE : HasLatticeDualCone E)
include hE

omit [PosSMulMono ℝ E] in
/-- Two finite families of positive functionals with the same sum have a common refinement: a table
whose rows add up to the first family and whose columns add up to the second. -/
lemma exists_table {n : ℕ} (θ : Fin n → E →ₚ[ℝ] ℝ) : ∀ {m : ℕ} (θ' : Fin m → E →ₚ[ℝ] ℝ),
    ∑ i, θ i = ∑ j, θ' j → ∃ τ : Fin n → Fin m → E →ₚ[ℝ] ℝ,
      (∀ i, ∑ j, τ i j = θ i) ∧ ∀ j, ∑ i, τ i j = θ' j
  | 0, θ', h => ⟨fun _ j => j.elim0, fun i => by
      simp only [Finset.univ_eq_empty, Finset.sum_empty] at h ⊢
      exact (le_antisymm (h ▸ le_sum θ (Finset.mem_univ i)) (zero_le _)).symm,
      fun j => j.elim0⟩
  | m + 1, θ', h => by
    rw [Fin.sum_univ_succ] at h
    obtain ⟨ψ₁, ψ₂, hψ, s₁, s₂⟩ := hE.exists_refinement θ h
    obtain ⟨τ, hτ₁, hτ₂⟩ := exists_table ψ₂ (fun j => θ' j.succ) s₂
    refine ⟨fun i => Fin.cons (ψ₁ i) (τ i), fun i => ?_, fun j => ?_⟩
    · simp only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, hτ₁, hψ]
    · refine Fin.cases ?_ (fun j => ?_) j
      · simpa only [Fin.cons_zero] using s₁
      · simpa only [Fin.cons_succ] using hτ₂ j

end HasLatticeDualCone

/-! ## B. The interpolation gauge -/


namespace Interpolation

include hu

variable {n m : ℕ}

variable (u) in
/-- The slacks `μ` for which some `g` satisfies `v.1 i - g ≤ μ • u` and `g + v.2 j ≤ μ • u`. -/
def slacks (v : (Fin n → E) × (Fin m → E)) : Set ℝ :=
  {μ | ∃ g : E, (∀ i, v.1 i - g ≤ μ • u) ∧ ∀ j, g + v.2 j ≤ μ • u}

variable (u) in
/-- The interpolation gauge: the least slack. -/
noncomputable def gauge (v : (Fin n → E) × (Fin m → E)) : ℝ := sInf (slacks u v)

omit [IsDirectedOrder E] in
lemma slacks_nonempty (v : (Fin n → E) × (Fin m → E)) : (slacks u v).Nonempty := by
  obtain ⟨μ, -, hμ⟩ := hu.exists_forall_le_smul (Sum.elim v.1 v.2)
  exact ⟨μ, 0, fun i => by simpa using hμ (.inl i), fun j => by simpa using hμ (.inr j)⟩

variable [Nontrivial E] [NeZero n] [NeZero m]

omit [IsDirectedOrder E] in
lemma slacks_bddBelow (v : (Fin n → E) × (Fin m → E)) : BddBelow (slacks u v) := by
  obtain ⟨k, hk, -⟩ := hu.exists_two_sided (v.1 0 + v.2 0)
  refine ⟨-(k / 2), fun μ ⟨g, h₁, h₂⟩ => ?_⟩
  have : -((k : ℝ) • u) ≤ (2 * μ) • u := by
    rw [Nat.cast_smul_eq_nsmul]
    calc -(k • u) ≤ v.1 0 + v.2 0 := hk
      _ = (v.1 0 - g) + (g + v.2 0) := by abel
      _ ≤ μ • u + μ • u := add_le_add (h₁ 0) (h₂ 0)
      _ = (2 * μ) • u := by rw [two_mul, add_smul]
  have h2 : (0 : E) ≤ (2 * μ + k) • u := by
    rw [add_smul]; simpa [add_comm] using neg_le_iff_add_nonneg.1 this
  have := hu.nonneg_of_smul_nonneg h2
  linarith

omit [IsDirectedOrder E] in
lemma gauge_le {v : (Fin n → E) × (Fin m → E)} {μ : ℝ} (hμ : μ ∈ slacks u v) : gauge u v ≤ μ :=
  csInf_le (slacks_bddBelow hu v) hμ

omit hu [Nontrivial E] [NeZero n] [NeZero m] [PosSMulMono ℝ E] [IsDirectedOrder E] in
lemma add_mem_slacks {v w : (Fin n → E) × (Fin m → E)} {μ ν : ℝ} (hμ : μ ∈ slacks u v)
    (hν : ν ∈ slacks u w) : μ + ν ∈ slacks u (v + w) := by
  obtain ⟨g, hg₁, hg₂⟩ := hμ
  obtain ⟨h, hh₁, hh₂⟩ := hν
  refine ⟨g + h, fun i => ?_, fun j => ?_⟩
  · calc (v + w).1 i - (g + h) = (v.1 i - g) + (w.1 i - h) := by simp; abel
      _ ≤ μ • u + ν • u := add_le_add (hg₁ i) (hh₁ i)
      _ = (μ + ν) • u := (add_smul _ _ _).symm
  · calc g + h + (v + w).2 j = (g + v.2 j) + (h + w.2 j) := by simp; abel
      _ ≤ μ • u + ν • u := add_le_add (hg₂ j) (hh₂ j)
      _ = (μ + ν) • u := (add_smul _ _ _).symm

omit [IsDirectedOrder E] in
lemma gauge_add_le (v w : (Fin n → E) × (Fin m → E)) : gauge u (v + w) ≤ gauge u v + gauge u w := by
  have h₁ : ∀ ν ∈ slacks u w, gauge u (v + w) - ν ≤ gauge u v := fun ν hν =>
    le_csInf (slacks_nonempty hu v) fun μ hμ => by linarith [gauge_le hu (add_mem_slacks hμ hν)]
  have h₂ : gauge u (v + w) - gauge u v ≤ gauge u w :=
    le_csInf (slacks_nonempty hu w) fun ν hν => by linarith [h₁ ν hν]
  linarith

omit hu [Nontrivial E] [NeZero n] [NeZero m] [IsDirectedOrder E] in
lemma slacks_smul {c : ℝ} (hc : 0 < c) (v : (Fin n → E) × (Fin m → E)) :
    slacks u (c • v) = c • slacks u v := by
  ext μ
  constructor
  · rintro ⟨g, h₁, h₂⟩
    refine ⟨c⁻¹ * μ, ⟨c⁻¹ • g, fun i => ?_, fun j => ?_⟩, by simp [hc.ne']⟩
    · have := smul_le_smul_of_nonneg_left (h₁ i) (inv_nonneg.2 hc.le)
      simpa [smul_sub, smul_smul, hc.ne'] using this
    · have := smul_le_smul_of_nonneg_left (h₂ j) (inv_nonneg.2 hc.le)
      simpa [smul_add, smul_smul, hc.ne'] using this
  · rintro ⟨μ, ⟨g, h₁, h₂⟩, rfl⟩
    refine ⟨c • g, fun i => ?_, fun j => ?_⟩
    · have := smul_le_smul_of_nonneg_left (h₁ i) hc.le
      simpa [smul_sub, smul_smul] using this
    · have := smul_le_smul_of_nonneg_left (h₂ j) hc.le
      simpa [smul_add, smul_smul] using this

omit hu [Nontrivial E] [NeZero n] [NeZero m] [IsDirectedOrder E] in
lemma gauge_smul {c : ℝ} (hc : 0 < c) (v : (Fin n → E) × (Fin m → E)) :
    gauge u (c • v) = c * gauge u v := by
  rw [gauge, slacks_smul hc, Real.sInf_smul_of_nonneg hc.le, smul_eq_mul]
  rfl

omit [IsDirectedOrder E] in
lemma gauge_zero : gauge u (0 : (Fin n → E) × (Fin m → E)) = 0 := by
  refine le_antisymm (gauge_le hu ⟨0, fun i => by simp, fun j => by simp⟩)
    (le_csInf (slacks_nonempty hu 0) fun μ ⟨g, h₁, h₂⟩ => ?_)
  have : (0 : E) ≤ (2 * μ) • u := by
    calc (0 : E) = (0 - g) + (g + 0) := by abel
      _ ≤ μ • u + μ • u := add_le_add (h₁ 0) (h₂ 0)
      _ = (2 * μ) • u := by rw [two_mul, add_smul]
  linarith [hu.nonneg_of_smul_nonneg this]

omit [IsDirectedOrder E] in
lemma gauge_nonpos {v : (Fin n → E) × (Fin m → E)} (hv₁ : ∀ i, v.1 i ≤ 0) (hv₂ : ∀ j, v.2 j ≤ 0) :
    gauge u v ≤ 0 :=
  gauge_le hu ⟨0, fun i => by simpa using hv₁ i, fun j => by simpa using hv₂ j⟩

omit [IsDirectedOrder E] in
/-- The gauge scales at least linearly, also by negative factors. -/
lemma mul_gauge_le (t : (Fin n → E) × (Fin m → E)) (c : ℝ) : c * gauge u t ≤ gauge u (c • t) := by
  rcases lt_trichotomy c 0 with hc | rfl | hc
  · have := gauge_add_le hu t (-t)
    rw [add_neg_cancel, gauge_zero hu] at this
    rw [show c • t = (-c) • (-t) by simp, gauge_smul (neg_pos.2 hc)]
    nlinarith
  · simp [gauge_zero hu]
  · rw [gauge_smul hc]

omit [IsDirectedOrder E] in
/-- A linear functional below the interpolation gauge that attains it at `t`. -/
lemma exists_linear_le_gauge (t : (Fin n → E) × (Fin m → E)) :
    ∃ Λ : (Fin n → E) × (Fin m → E) →ₗ[ℝ] ℝ, (∀ v, Λ v ≤ gauge u v) ∧ Λ t = gauge u t :=
  exists_linearMap_le_eq_of_sublinear (N := gauge u) (fun _ hc v => gauge_smul hc v)
    (gauge_add_le hu) t

end Interpolation

/-! ## C. Approximate interpolants -/

namespace Interpolation

variable [Nontrivial E] {n m : ℕ} [NeZero n] [NeZero m]
  {Λ : (Fin n → E) × (Fin m → E) →ₗ[ℝ] ℝ} (hΛ : ∀ v, Λ v ≤ gauge u v)


omit hu [Nontrivial E] [NeZero n] [NeZero m] in
/-- The part of a linear functional acting on the `i`-th lower observable. -/
def lowerPart (Λ : (Fin n → E) × (Fin m → E) →ₗ[ℝ] ℝ) (i : Fin n) : E →ₗ[ℝ] ℝ :=
  Λ.comp ((LinearMap.inl ℝ _ _).comp (LinearMap.single ℝ (fun _ => E) i))

omit hu [Nontrivial E] [NeZero n] [NeZero m] in
/-- The part of a linear functional acting on the `j`-th upper observable. -/
def upperPart (Λ : (Fin n → E) × (Fin m → E) →ₗ[ℝ] ℝ) (j : Fin m) : E →ₗ[ℝ] ℝ :=
  Λ.comp ((LinearMap.inr ℝ _ _).comp (LinearMap.single ℝ (fun _ => E) j))

omit hu [Nontrivial E] [NeZero n] [NeZero m] [PartialOrder E] [IsOrderedAddMonoid E]
  [PosSMulMono ℝ E] [IsDirectedOrder E] in
lemma apply_eq_sum (v : (Fin n → E) × (Fin m → E)) :
    Λ v = ∑ i, lowerPart Λ i (v.1 i) + ∑ j, upperPart Λ j (v.2 j) := by
  classical
  have hv : v = ∑ i, (Pi.single i (v.1 i), (0 : Fin m → E)) +
      ∑ j, ((0 : Fin n → E), Pi.single j (v.2 j)) := by
    ext <;> simp [Prod.fst_sum, Prod.snd_sum, Finset.univ_sum_single]
  conv_lhs => rw [hv]
  simp only [map_add, map_sum]
  rfl

include hu hΛ

omit [IsDirectedOrder E] in
lemma lowerPart_nonneg (i : Fin n) {x : E} (hx : 0 ≤ x) : 0 ≤ lowerPart Λ i x := by
  classical
  have := (hΛ (-(Pi.single i x, 0))).trans (gauge_nonpos hu (fun k => by
    rcases eq_or_ne k i with rfl | hk <;> simp [*]) (fun _ => by simp))
  rw [map_neg] at this
  change 0 ≤ Λ (Pi.single i x, 0)
  linarith

omit [IsDirectedOrder E] in
lemma upperPart_nonneg (j : Fin m) {x : E} (hx : 0 ≤ x) : 0 ≤ upperPart Λ j x := by
  classical
  have := (hΛ (-(0, Pi.single j x))).trans (gauge_nonpos hu (fun _ => by simp) (fun k => by
    rcases eq_or_ne k j with rfl | hk <;> simp [*]))
  rw [map_neg] at this
  change 0 ≤ Λ (0, Pi.single j x)
  linarith

omit [IsDirectedOrder E] in
/-- The lower and the upper parts of a functional below the gauge have the same total. -/
lemma sum_lowerPart (h : E) : ∑ i, lowerPart Λ i h = ∑ j, upperPart Λ j h := by
  have hb (s : ℝ) : Λ (fun _ => s • h, fun _ => -(s • h)) ≤ 0 :=
    (hΛ _).trans (gauge_le hu ⟨s • h, fun i => by simp, fun j => by simp⟩)
  have h₁ := hb 1
  have h₂ := hb (-1)
  rw [apply_eq_sum] at h₁ h₂
  simp only [one_smul, neg_one_smul, neg_neg, map_neg, Finset.sum_neg_distrib] at h₁ h₂
  linarith

end Interpolation

namespace HasLatticeDualCone

open Interpolation

variable (hE : HasLatticeDualCone E) [Nontrivial E] {n m : ℕ} [NeZero n] [NeZero m]
  {a : Fin n → E} {b : Fin m → E} (hab : ∀ i j, a i ≤ b j)
include hu hE hab

/-- When the positive functionals form a lattice, lower observables below upper observables leave
no positive interpolation slack. -/
lemma gauge_nonpos : gauge u (a, -b) ≤ 0 := by
  obtain ⟨Λ, hΛ, hΛt⟩ := exists_linear_le_gauge hu (a, -b)
  let θ (i : Fin n) : E →ₚ[ℝ] ℝ := .mk₀ (lowerPart Λ i) fun _ => lowerPart_nonneg hu hΛ i
  let θ' (j : Fin m) : E →ₚ[ℝ] ℝ := .mk₀ (upperPart Λ j) fun _ => upperPart_nonneg hu hΛ j
  obtain ⟨τ, hτ₁, hτ₂⟩ := hE.exists_table θ θ' (PositiveLinearMap.ext fun h => by
    simp only [sum_apply]; exact sum_lowerPart hu hΛ h)
  have hθ (i) (x : E) : lowerPart Λ i x = ∑ j, τ i j x := by rw [← sum_apply, hτ₁]; rfl
  have hθ' (j) (x : E) : upperPart Λ j x = ∑ i, τ i j x := by rw [← sum_apply, hτ₂]; rfl
  rw [← hΛt, apply_eq_sum]
  simp only [hθ, hθ', Pi.neg_apply, map_neg, Finset.sum_neg_distrib]
  rw [Finset.sum_comm (γ := Fin m), ← sub_eq_add_neg, ← Finset.sum_sub_distrib]
  refine Finset.sum_nonpos fun i _ => ?_
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_nonpos fun j _ => sub_nonpos.2 ((τ i j).monotone' (hab i j))

/-- **Approximate interpolation.** When the positive functionals form a lattice, lower observables
below upper observables admit an interpolant up to any error. -/
lemma exists_approx_interpolant {ε : ℝ} (hε : 0 < ε) :
    ∃ g : E, (∀ i, a i ≤ g + ε • u) ∧ ∀ j, g ≤ b j + ε • u := by
  obtain ⟨μ, ⟨g, h₁, h₂⟩, hμ⟩ :=
    exists_lt_of_csInf_lt (slacks_nonempty hu _) ((hE.gauge_nonpos hu hab).trans_lt hε)
  have hμε : μ • u ≤ ε • u := smul_le_smul_of_nonneg_right hμ.le hu.nonneg
  refine ⟨g, fun i => ?_, fun j => ?_⟩
  · exact sub_le_iff_le_add'.1 ((h₁ i).trans hμε)
  · have := (h₂ j).trans hμε
    change g + -b j ≤ _ at this
    rwa [← sub_eq_add_neg, sub_le_iff_le_add'] at this

end HasLatticeDualCone
