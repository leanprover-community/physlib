/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.ProbabilisticTheory.Classical.Basic
public import PhyslibAlpha.ProbabilisticTheory.Classical.BauerSimplex
public import PhyslibAlpha.ProbabilisticTheory.Classical.BoundedMeasurable
public import PhyslibAlpha.ProbabilisticTheory.Classical.FiniteSystem

/-!
# Lattice-ordered observables

## i. Overview

When observables form a lattice, a state is pure exactly when it gives the minimum
of two observables the smaller of their expectation values, `ω (f ⊓ g) = min (ω f) (ω g)`. This
condition is closed, so the pure states form a compact space, and every observable becomes a
continuous function on it. The positive functionals form a lattice as well, so ensembles refine.
Hence the state space is a Bauer simplex and every state is a mixture of pure states in exactly one
way.

## ii. Key results

- `UnitalPositiveLinearMap.isPure_iff_map_inf` proves that a state is pure exactly when it preserves
  minima.
- `OrderUnitLattice.isClosed_setOf_isPure` proves that the pure states form a closed set.
- `OrderUnitLattice.isBauerSimplexStateSpace` proves that the state space is a Bauer simplex.
- `OrderUnitLattice.hasUniquePureDecomposition` proves that every state is a mixture of pure states
  in exactly one way.

## iii. Table of contents

- A. The band component
- B. Pure states preserve infima
- C. States preserving infima are pure
- D. Pure states of order-unit lattices
- E. Observables as continuous functions
- F. Unique decomposition
- G. Classical systems are Bauer simplices
- H. Finite classical systems are Bauer simplices

## iv. References

- E. M. Alfsen, *Compact Convex Sets and Boundary Integrals*, Springer, 1971, ch. II.

-/

@[expose] public section

namespace ProbabilisticTheory

open StateSpace

open scoped NNReal
open ArchimedeanOrderUnitSpace MeasureTheory Set

namespace UnitalPositiveLinearMap

/-!

## A. The band component

-/

section Lattice

variable {E : Type*} [OrderUnitLattice E] (ω : E →ₚ[ℝ] ℝ) (u : E)

open OrderUnitLattice VectorLattice

/-- The part of `ω` carried by `u`: `h ↦ sup {ω (h ⊓ a • u) | a ≥ 0}`. -/
noncomputable def band (h : E) : ℝ := ⨆ a : ℝ≥0, ω (h ⊓ (a : ℝ) • u)

variable {ω u}

lemma bddAbove_band (h : E) : BddAbove (range fun a : ℝ≥0 => ω (h ⊓ (a : ℝ) • u)) :=
  ⟨ω h, forall_mem_range.2 fun _ => OrderHomClass.mono ω inf_le_left⟩

lemma le_band (h : E) (a : ℝ≥0) : ω (h ⊓ (a : ℝ) • u) ≤ band ω u h :=
  le_ciSup (bddAbove_band h) a

lemma band_le {h : E} {r : ℝ} (hr : ∀ a : ℝ≥0, ω (h ⊓ (a : ℝ) • u) ≤ r) : band ω u h ≤ r :=
  ciSup_le hr

lemma band_nonneg {h : E} (hh : 0 ≤ h) : 0 ≤ band ω u h :=
  (le_band h 0).trans' (by simp [inf_eq_right.2 hh])

lemma band_add (hu : 0 ≤ u) {h₁ h₂ : E} (h₁0 : 0 ≤ h₁) (h₂0 : 0 ≤ h₂) :
    band ω u (h₁ + h₂) = band ω u h₁ + band ω u h₂ := by
  refine le_antisymm (band_le fun a => ?_) ?_
  · refine (OrderHomClass.mono ω (add_inf_le h₁0 h₂0 (smul_nonneg a.coe_nonneg hu))).trans ?_
    rw [map_add]
    exact add_le_add (le_band h₁ a) (le_band h₂ a)
  · have key (a b : ℝ≥0) : ω (h₁ ⊓ (a : ℝ) • u) + ω (h₂ ⊓ (b : ℝ) • u) ≤ band ω u (h₁ + h₂) := by
      refine (le_band (h₁ + h₂) (a + b)).trans' ?_
      rw [← map_add]
      refine OrderHomClass.mono ω (le_inf (add_le_add inf_le_left inf_le_left) ?_)
      rw [NNReal.coe_add, add_smul]
      exact add_le_add inf_le_right inf_le_right
    exact ciSup_add_ciSup_le key

lemma apply_smul_inf_smul {c : ℝ} (hc : 0 ≤ c) (h : E) (a : ℝ) :
    ω (c • h ⊓ (c * a) • u) = c * ω (h ⊓ a • u) := by
  rw [mul_smul, ← smul_inf hc, map_smul, smul_eq_mul]

lemma band_smul {c : ℝ} (hc : 0 < c) {h : E} :
    band ω u (c • h) = c * band ω u h := by
  refine le_antisymm (band_le fun a => ?_) ?_
  · have := apply_smul_inf_smul (ω := ω) (u := u) hc.le h (c⁻¹ * a)
    rw [← mul_assoc, mul_inv_cancel₀ hc.ne', one_mul] at this
    rw [this]
    exact mul_le_mul_of_nonneg_left (le_band h ⟨c⁻¹ * a, by positivity⟩) hc.le
  · rw [← le_inv_mul_iff₀ hc]
    refine band_le fun a => (le_inv_mul_iff₀ hc).2 ?_
    rw [← apply_smul_inf_smul hc.le]
    exact le_band (c • h) ⟨c * a, by positivity⟩

variable (ω) in
/-- The part of `ω` carried by a positive element `u`, as a positive functional. -/
noncomputable def bandMap (hu : 0 ≤ u) : E →ₚ[ℝ] ℝ :=
  PositiveLinearMap.ofCone (band ω u) (fun _ hh => band_nonneg hh)
    (fun _ _ h₁ h₂ => band_add hu h₁ h₂) (fun _ _ hc _ => band_smul hc)

lemma bandMap_apply (hu : 0 ≤ u) {h : E} (hh : 0 ≤ h) : bandMap ω hu h = band ω u h :=
  PositiveLinearMap.ofCone_apply _ _ _ _ hh

lemma bandMap_le (hu : 0 ≤ u) : bandMap ω hu ≤ ω := fun h hh => by
  rw [bandMap_apply hu hh]
  exact band_le fun _ => OrderHomClass.mono ω inf_le_left

lemma bandMap_self (hu : 0 ≤ u) : bandMap ω hu u = ω u := by
  refine le_antisymm (bandMap_le hu u hu) ?_
  rw [bandMap_apply hu hu]
  simpa using le_band (ω := ω) (u := u) u 1

lemma bandMap_eq_zero (hu : 0 ≤ u) {g : E} (hg : 0 ≤ g) (h : g ⊓ u = 0) : bandMap ω hu g = 0 := by
  rw [bandMap_apply hu hg]
  exact le_antisymm (band_le fun a => by rw [inf_smul_eq_zero hg hu h a.coe_nonneg, map_zero])
    (band_nonneg hg)

/-!

## B. Pure states preserve infima

-/

/-- A pure state vanishes on one of any two disjoint positive elements. -/
lemma IsPure.apply_eq_zero_of_inf_eq_zero {ω : 𝓢[ℝ, E]} (hω : ω.IsPure) {g u : E} (hg : 0 ≤ g)
    (hu : 0 ≤ u) (h : g ⊓ u = 0) : ω g = 0 ∨ ω u = 0 := by
  rcases (map_nonneg ω hu).eq_or_lt with hu0 | hu0
  · exact .inr hu0.symm
  have hle := bandMap_le (ω := ω.toPositiveLinearMap) hu
  have h1 := hω.apply_eq_of_le hle u
  rw [bandMap_self hu] at h1
  have ht : bandMap ω.toPositiveLinearMap hu 1 = 1 := by
    have := mul_right_cancel₀ hu0.ne' (h1.symm.trans (one_mul _).symm)
    exact this
  have h2 := hω.apply_eq_of_le hle g
  rw [bandMap_eq_zero hu hg h, ht, one_mul] at h2
  exact .inl h2.symm

/-- Pure states preserve infima. -/
lemma IsPure.map_inf {ω : 𝓢[ℝ, E]} (hω : ω.IsPure) (f g : E) :
    ω (f ⊓ g) = min (ω f) (ω g) := by
  have h := hω.apply_eq_zero_of_inf_eq_zero (sub_nonneg.2 (inf_le_left : f ⊓ g ≤ f))
    (sub_nonneg.2 (inf_le_right : f ⊓ g ≤ g)) (by rw [← inf_sub, sub_self])
  refine le_antisymm
    (le_min (OrderHomClass.mono ω inf_le_left) (OrderHomClass.mono ω inf_le_right)) ?_
  rcases h with h | h <;> rw [map_sub, sub_eq_zero] at h
  · exact (min_le_left _ _).trans h.le
  · exact (min_le_right _ _).trans h.le

/-!

## C. States preserving infima are pure

-/

/-- An infimum-preserving state does not see the deviation of an observable from its value. -/
lemma map_abs_sub_eq_zero_of_map_inf {ω : 𝓢[ℝ, E]} (h : ∀ f g, ω (f ⊓ g) = min (ω f) (ω g))
    (f : E) : ω |f - ω f • (1 : E)| = 0 := by
  have hk : ω (f - ω f • (1 : E)) = 0 := by simp [map_sub, map_smul]
  have := map_sup_of_map_inf (ω := ω.toPositiveLinearMap) h (f - ω f • 1) (-(f - ω f • 1))
  change ω (_ ⊔ _) = max (ω _) (ω _) at this
  change ω (_ ⊔ _) = 0
  rw [this, map_neg, hk, neg_zero, max_self]

/-- A state dominated by a multiple of an infimum-preserving state is that state. -/
lemma eq_of_le_smul_of_map_inf {ω φ : 𝓢[ℝ, E]} (h : ∀ f g, ω (f ⊓ g) = min (ω f) (ω g))
    {c : ℝ} (hφ : ∀ f, 0 ≤ f → φ f ≤ c * ω f) : φ = ω := by
  refine ext fun f => ?_
  have habs := map_abs_sub_eq_zero_of_map_inf h f
  set k := f - ω f • (1 : E)
  have hφk : φ |k| = 0 := le_antisymm (by simpa [habs] using hφ _ (abs_nonneg k))
    (map_nonneg φ (abs_nonneg k))
  have h₁ := OrderHomClass.mono φ (le_abs_self k)
  have h₂ := OrderHomClass.mono φ (neg_le_abs k)
  rw [hφk] at h₁ h₂
  rw [map_neg] at h₂
  have : φ k = φ f - ω f := by simp [k, map_sub, map_smul]
  linarith

/-- States preserving infima are pure. -/
lemma isPure_of_map_inf {ω : 𝓢[ℝ, E]} (h : ∀ f g, ω (f ⊓ g) = min (ω f) (ω g)) : ω.IsPure := by
  refine isPure_iff_forall_mix_eq.2 fun φ ψ t ht0 ht1 hmix => ?_
  have ht : (0 : ℝ) < t := unitInterval.pos_iff_ne_zero.2 ht0
  have ht' : (0 : ℝ) < 1 - t := sub_pos.2 (unitInterval.lt_one_iff_ne_one.2 ht1)
  have hω f : ω f = t * φ f + (1 - t) * ψ f := by rw [← hmix, mix_apply]
  refine ⟨eq_of_le_smul_of_map_inf h (c := (t : ℝ)⁻¹) fun f hf => ?_,
    eq_of_le_smul_of_map_inf h (c := (1 - t)⁻¹) fun f hf => ?_⟩
  · rw [hω, le_inv_mul_iff₀ ht]
    nlinarith [map_nonneg ψ hf]
  · rw [hω, le_inv_mul_iff₀ ht']
    nlinarith [map_nonneg φ hf]

/-- The pure states of an order-unit lattice are the states preserving infima. -/
lemma isPure_iff_map_inf {ω : 𝓢[ℝ, E]} : ω.IsPure ↔ ∀ f g, ω (f ⊓ g) = min (ω f) (ω g) :=
  ⟨IsPure.map_inf, isPure_of_map_inf⟩

end Lattice

end UnitalPositiveLinearMap

/-!

## D. Pure states of order-unit lattices

-/

namespace OrderUnitLattice

variable (E : Type*) [OrderUnitLattice E]

/-- The pure states of an order-unit lattice form a weak-star closed set. -/
lemma isClosed_setOf_isPure : IsClosed {ω : stateSpace E | (toState ω).IsPure} := by
  have h : {ω : stateSpace E | (toState ω).IsPure} = ⋂ f : E, ⋂ g : E,
      {ω : stateSpace E | toState ω (f ⊓ g) = min (toState ω f) (toState ω g)} := by
    ext ω
    simp [UnitalPositiveLinearMap.isPure_iff_map_inf]
  rw [h]
  exact isClosed_iInter fun f => isClosed_iInter fun g => isClosed_eq
    (StateSpace.continuous_apply _)
    ((StateSpace.continuous_apply f).min (StateSpace.continuous_apply g))

end OrderUnitLattice

namespace OrderUnitLattice

open PureState

variable {E : Type*} [OrderUnitLattice E]

instance : CompactSpace (PureState E) :=
  isCompact_iff_compactSpace.1 (isClosed_setOf_isPure E).isCompact

/-!

## E. Observables as continuous functions

-/

lemma evalPure_inf (f g : E) : evalPure (f ⊓ g) = evalPure f ⊓ evalPure g := by
  ext ω
  simpa using UnitalPositiveLinearMap.isPure_iff_map_inf.1 ω.2 f g

lemma evalPure_sup (f g : E) : evalPure (f ⊔ g) = evalPure f ⊔ evalPure g := by
  ext ω
  exact map_sup_of_map_inf (ω := (toState ω.1).toPositiveLinearMap)
    (UnitalPositiveLinearMap.isPure_iff_map_inf.1 ω.2) f g

lemma separatesPointsStrongly : (range (evalPure (E := E))).SeparatesPointsStrongly :=
  fun v x y => by
    obtain ⟨a, hx, hy⟩ := StateSpace.exists_apply_eq_apply (x := x.1) (y := y.1) (v x) (v y)
      fun h => congrArg v (Subtype.ext h)
    exact ⟨_, ⟨a, rfl⟩, hx, hy⟩

/-- **Stone–Weierstrass**: observables are dense among continuous functions on the pure
states. -/
lemma denseRange_evalPure : DenseRange (evalPure (E := E)) :=
  dense_iff_closure_eq.2 <| ContinuousMap.sublattice_closure_eq_top _ ⟨_, 0, rfl⟩
    (by rintro _ ⟨f, rfl⟩ _ ⟨g, rfl⟩; exact ⟨f ⊓ g, evalPure_inf f g⟩)
    (by rintro _ ⟨f, rfl⟩ _ ⟨g, rfl⟩; exact ⟨f ⊔ g, evalPure_sup f g⟩) separatesPointsStrongly

/-!

## F. Unique decomposition

-/

variable (E) in
/-- **Classicality of lattice-ordered observables**: the state space of an order-unit lattice is a
Bauer simplex. -/
lemma isBauerSimplexStateSpace : IsBauerSimplexStateSpace E :=
  isBauerSimplexStateSpace_iff.2
    ⟨(OrderUnitLattice.isClassical E).ensemblesRefine, isClosed_setOf_isPure E⟩

/-- **Unique decomposition into pure states**: every state of an order-unit lattice is a mixture
of pure states in exactly one way. -/
lemma hasUniquePureDecomposition (φ : 𝓢[ℝ, E]) : φ.HasUniquePureDecomposition :=
  (isBauerSimplexStateSpace E).1 φ

end OrderUnitLattice

/-!

## G. Classical systems are Bauer simplices

-/

end ProbabilisticTheory

namespace BoundedMeasurable
open ProbabilisticTheory
open StateSpace
open scoped NNReal
open ArchimedeanOrderUnitSpace MeasureTheory Set

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **The state space of a classical system is a Bauer simplex.** -/
lemma isBauerSimplexStateSpace : IsBauerSimplexStateSpace (BoundedMeasurable Ω) :=
  OrderUnitLattice.isBauerSimplexStateSpace _

/-- **Classicality**: every state of a classical system decomposes uniquely into pure states. -/
lemma hasUniquePureDecomposition
    (φ : 𝓢[ℝ, BoundedMeasurable Ω]) : φ.HasUniquePureDecomposition :=
  OrderUnitLattice.hasUniquePureDecomposition φ

end BoundedMeasurable

namespace ProbabilisticTheory

open StateSpace
open scoped NNReal
open ArchimedeanOrderUnitSpace MeasureTheory Set

/-!

## H. Finite classical systems are Bauer simplices

-/

namespace FiniteClassicalSystem

variable {ι : Type*} [Fintype ι]

instance : OrderUnitLattice (FiniteClassicalSystem ι) :=
  { (inferInstance : ArchimedeanOrderUnitSpace (FiniteClassicalSystem ι)),
    (inferInstance : Lattice (ι → ℝ)) with }

/-- The state space of a finite classical system is a Bauer simplex. -/
lemma isBauerSimplexStateSpace : IsBauerSimplexStateSpace (FiniteClassicalSystem ι) :=
  OrderUnitLattice.isBauerSimplexStateSpace _

end FiniteClassicalSystem

end ProbabilisticTheory
