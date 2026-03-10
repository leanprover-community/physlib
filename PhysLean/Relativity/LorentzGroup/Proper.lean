/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import PhysLean.Relativity.LorentzGroup.Basic
public import Mathlib.Topology.Connected.PathConnected
public import Mathlib.Tactic.Cases
/-!
# The Proper Lorentz Group

The proper Lorentz group is the subgroup of the Lorentz group with determinant `1`.

We define the give a series of lemmas related to the determinant of the Lorentz group.

-/

@[expose] public section

noncomputable section

open Matrix
open Complex
open ComplexConjugate

namespace LorentzGroup

open minkowskiMatrix

variable {d : ℕ}

/-- The determinant of a member of the Lorentz group is `1` or `-1`. -/
lemma det_eq_one_or_neg_one (Λ : 𝓛 d) : Λ.1.det = 1 ∨ Λ.1.det = -1 := by
  refine mul_self_eq_one_iff.mp ?_
  simpa only [det_mul, det_dual, det_one] using congrArg det ((mem_iff_self_mul_dual).mp Λ.2)

/-- The group `ℤ₂`. -/
local notation "ℤ₂" => Multiplicative (ZMod 2)

/-- The instance of a topological space on `ℤ₂` corresponding to the discrete topology. -/
instance : TopologicalSpace ℤ₂ := instTopologicalSpaceFin

/-- The topological space defined by `ℤ₂` is discrete. -/
instance : DiscreteTopology ℤ₂ := by
  exact discreteTopology_iff_forall_isOpen.mpr fun _ => trivial

/-- The instance of a topological group on `ℤ₂` defined via the discrete topology. -/
instance : IsTopologicalGroup ℤ₂ := IsTopologicalGroup.mk

/-- A continuous function from `({-1, 1} : Set ℝ)` to `ℤ₂`. -/
@[simps!]
def coeForℤ₂ : C(({-1, 1} : Set ℝ), ℤ₂) where
  toFun x := if x = ⟨1, Set.mem_insert_of_mem (-1) rfl⟩
    then Additive.toMul 0 else Additive.toMul (1 : ZMod 2)
  continuous_toFun := continuous_of_discreteTopology

/-- The continuous map taking a Lorentz matrix to its determinant. -/
def detContinuous : C(𝓛 d, ℤ₂) :=
  ContinuousMap.comp coeForℤ₂ {
    toFun := fun Λ => ⟨Λ.1.det, Or.symm (LorentzGroup.det_eq_one_or_neg_one _)⟩,
    continuous_toFun := by
      refine Continuous.subtype_mk ?_ _
      exact Continuous.matrix_det $
        Continuous.comp' (continuous_iff_le_induced.mpr fun U a => a) continuous_id'
      }

lemma detContinuous_eq_one (Λ : LorentzGroup d) :
    detContinuous Λ = Additive.toMul 0 ↔ Λ.1.det = 1 := by
  simp only [detContinuous, ContinuousMap.comp_apply, ContinuousMap.coe_mk, coeForℤ₂_apply,
    Subtype.mk.injEq]
  simp only [toMul_zero, ite_eq_left_iff, toMul_eq_one]
  refine Iff.intro (fun h => ?_) (fun h => ?_)
  · by_contra hn
    have h' := h hn
    change (1 : Fin 2) = (0 : Fin 2) at h'
    simp only [Fin.isValue, one_ne_zero] at h'
  · intro h'
    exact False.elim (h' h)

lemma detContinuous_eq_zero (Λ : LorentzGroup d) :
    detContinuous Λ = Additive.toMul (1 : ZMod 2) ↔ Λ.1.det = - 1 := by
  simp only [detContinuous, ContinuousMap.comp_apply, ContinuousMap.coe_mk, coeForℤ₂_apply,
    Subtype.mk.injEq, Nat.reduceAdd]
  refine Iff.intro (fun h => ?_) (fun h => ?_)
  · by_contra hn
    rw [if_pos] at h
    · change (0 : Fin 2) = (1 : Fin 2) at h
      simp only [Fin.isValue, zero_ne_one] at h
    · cases' det_eq_one_or_neg_one Λ with h2 h2
      · simp_all only [ite_true]
      · simp_all only [not_true_eq_false]
  · rw [if_neg]
    · rfl
    · cases' det_eq_one_or_neg_one Λ with h2 h2
      · rw [h]
        linarith
      · linarith

lemma detContinuous_eq_iff_det_eq (Λ Λ' : LorentzGroup d) :
    detContinuous Λ = detContinuous Λ' ↔ Λ.1.det = Λ'.1.det := by
  match det_eq_one_or_neg_one Λ, det_eq_one_or_neg_one Λ' with
  | .inl h1, .inl h2 =>
    rw [h1, h2, (detContinuous_eq_one Λ).mpr h1, (detContinuous_eq_one Λ').mpr h2]
    simp only [toMul_zero]
  | .inr h1, .inr h2 =>
    rw [h1, h2, (detContinuous_eq_zero Λ).mpr h1, (detContinuous_eq_zero Λ').mpr h2]
    simp only [Nat.reduceAdd]
  | .inl h1, .inr h2 =>
    rw [h1, h2, (detContinuous_eq_one Λ).mpr h1, (detContinuous_eq_zero Λ').mpr h2]
    change (0 : Fin 2) = (1 : Fin 2) ↔ _
    simp only [zero_ne_one, false_iff]
    linarith
  | .inr h1, .inl h2 =>
    rw [h1, h2, (detContinuous_eq_zero Λ).mpr h1, (detContinuous_eq_one Λ').mpr h2]
    change (1 : Fin 2) = (0 : Fin 2) ↔ _
    simp only [one_ne_zero, false_iff]
    linarith

/-- The representation taking a Lorentz matrix to its determinant. -/
@[simps!]
def detRep : 𝓛 d →* ℤ₂ where
  toFun Λ := detContinuous Λ
  map_one' := by
    simp only [detContinuous, ContinuousMap.comp_apply, ContinuousMap.coe_mk,
      lorentzGroupIsGroup_one_coe, det_one, coeForℤ₂_apply, ↓reduceIte]
  map_mul' Λ1 Λ2 := by
    cases' det_eq_one_or_neg_one Λ1 with h1 h1
    · rw [(detContinuous_eq_one Λ1).mpr h1]
      cases' det_eq_one_or_neg_one Λ2 with h2 h2
      · rw [(detContinuous_eq_one Λ2).mpr h2]
        apply (detContinuous_eq_one _).mpr
        simp only [lorentzGroupIsGroup_mul_coe, det_mul, h1, h2, mul_one]
      · rw [(detContinuous_eq_zero Λ2).mpr h2]
        apply (detContinuous_eq_zero _).mpr
        simp only [lorentzGroupIsGroup_mul_coe, det_mul, h1, h2, mul_neg, mul_one]
    · rw [(detContinuous_eq_zero Λ1).mpr h1]
      cases' det_eq_one_or_neg_one Λ2 with h2 h2
      · rw [(detContinuous_eq_one Λ2).mpr h2]
        apply (detContinuous_eq_zero _).mpr
        simp only [lorentzGroupIsGroup_mul_coe, det_mul, h1, h2, mul_one]
      · rw [(detContinuous_eq_zero Λ2).mpr h2]
        apply (detContinuous_eq_one _).mpr
        simp only [lorentzGroupIsGroup_mul_coe, det_mul, h1, h2, mul_neg, mul_one, neg_neg]

/-- The representation of the Lorentz group defined by taking the determinant `detRep` is
  continuous. -/
lemma detRep_continuous : Continuous (@detRep d) := detContinuous.2

/-- Two Lorentz transformations which are in the same connected component have the same
  determinant. -/
lemma det_on_connected_component {Λ Λ' : LorentzGroup d} (h : Λ' ∈ connectedComponent Λ) :
    Λ.1.det = Λ'.1.det := by
  obtain ⟨s, hs, hΛ'⟩ := h
  let f : ContinuousMap s ℤ₂ := ContinuousMap.restrict s detContinuous
  haveI : PreconnectedSpace s := isPreconnected_iff_preconnectedSpace.mp hs.1
  simpa [f, detContinuous_eq_iff_det_eq] using
    (@IsPreconnected.subsingleton ℤ₂ _ _ _ (isPreconnected_range f.2))
    (Set.mem_range_self ⟨Λ, hs.2⟩) (Set.mem_range_self ⟨Λ', hΛ'⟩)

/-- Two Lorentz transformations which are in the same connected component have the same
  image under `detRep`, the determinant representation. -/
lemma detRep_on_connected_component {Λ Λ' : LorentzGroup d} (h : Λ' ∈ connectedComponent Λ) :
    detRep Λ = detRep Λ' := by
  simp only [detRep_apply, detContinuous, ContinuousMap.comp_apply, ContinuousMap.coe_mk,
    coeForℤ₂_apply, Subtype.mk.injEq]
  rw [det_on_connected_component h]

/-- Two Lorentz transformations which are joined by a path have the same determinant. -/
lemma det_of_joined {Λ Λ' : LorentzGroup d} (h : Joined Λ Λ') : Λ.1.det = Λ'.1.det :=
  det_on_connected_component $ pathComponent_subset_component _ h

/-- A Lorentz Matrix is proper if its determinant is 1. -/
@[simp]
def IsProper (Λ : LorentzGroup d) : Prop := Λ.1.det = 1

/-- The predicate `IsProper` is decidable. -/
instance : DecidablePred (@IsProper d) := by
  intro Λ
  apply Real.decidableEq

/-- The product of two proper Lorentz transformations is proper. -/
lemma isProper_mul {Λ Λ' : LorentzGroup d}
    (h : IsProper Λ) (h' : IsProper Λ') : IsProper (Λ * Λ') := by
  rw [IsProper, lorentzGroupIsGroup_mul_coe, det_mul, h, h', mul_one]

/-- A Lorentz transformation is proper if its image under the det-representation
  `detRep` is `1`. -/
lemma isProper_iff (Λ : LorentzGroup d) : IsProper Λ ↔ detRep Λ = 1 := by
  rw [show 1 = detRep 1 from Eq.symm (MonoidHom.map_one detRep), detRep_apply, detRep_apply,
    detContinuous_eq_iff_det_eq]
  simp only [IsProper, lorentzGroupIsGroup_one_coe, det_one]

/-- The identity Lorentz transformation is proper. -/
lemma isProper_id : @IsProper d 1 := by
  simp [IsProper]

/-- If two Lorentz transformations are in the same connected component, and one is proper then
  the other is also proper. -/
lemma isProper_on_connected_component {Λ Λ' : LorentzGroup d} (h : Λ' ∈ connectedComponent Λ) :
    IsProper Λ ↔ IsProper Λ' := by
  simp only [IsProper]
  rw [det_on_connected_component h]

end LorentzGroup

end
