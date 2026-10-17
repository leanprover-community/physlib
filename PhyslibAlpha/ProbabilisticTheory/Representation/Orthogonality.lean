/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.ProbabilisticTheory.Representation.VectorMeasure
public import Mathlib.Algebra.Module.CharacterModule
public import Mathlib.MeasureTheory.Measure.Haar.Basic
public import Mathlib.MeasureTheory.Group.Integral
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-!

# Orthogonality of characters

Characters separate the points of a discrete abelian group, and the normalized Haar measure of the
dual group makes the characters orthogonal.

## i. Overview

For a discrete abelian group `G` and `g ≠ 0` there is a unitary character `χ` of `G` with
`χ(g) ≠ 1`. This comes from the injectivity of the circle: a character into `ℚ/ℤ` separating `g`
from `0`, composed with the injection `ℚ/ℤ → S¹`, `q ↦ e^{2πi q}`. The Pontryagin dual `Ĝ` is a
compact abelian group, so it carries a Haar probability measure `μ`. The evaluation `χ ↦ χ(g)` is a
nontrivial character of `Ĝ` for `g ≠ 0`, so by translation invariance
`∫ χ(g) dμ(χ) = 0`, and `= 1` for `g = 0`: the characters are orthonormal.

## ii. Key results

- `exists_character_apply_ne_one` : characters separate points.
- `dualHaar` : the Haar probability measure of the dual group.
- `integral_character_dualHaar` : `∫ χ(g) dμ(χ) = 1` for `g = 0` and `0` otherwise.

## iii. Table of contents

- A. Characters separate points
- B. The Haar measure of the dual group

## iv. References

* None.

-/

@[expose] public section

noncomputable section

namespace ProbabilisticTheory

open MeasureTheory Set Topology

namespace QuantumMechanics

/-! ## A. Characters separate points -/

/-- The injection of `ℚ/ℤ` into the circle, `q ↦ e^{2πi q}`. -/
def rationalCircle : AddCircle (1 : ℚ) →+ Additive Circle :=
  QuotientAddGroup.lift (AddSubgroup.zmultiples (1 : ℚ))
    (Circle.expHom.comp ((AddMonoidHom.mulLeft (2 * Real.pi)).comp
      (Rat.castHom ℝ).toAddMonoidHom))
    (by
      intro q hq
      obtain ⟨n, rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp hq
      simp only [AddMonoidHom.mem_ker, AddMonoidHom.coe_comp, Function.comp_apply]
      have : Circle.exp (2 * Real.pi * ((n • (1 : ℚ) : ℚ) : ℝ)) = 1 := by
        rw [Circle.exp_eq_one]
        exact ⟨n, by simp; ring⟩
      exact this)

lemma rationalCircle_eq_zero {x : AddCircle (1 : ℚ)} (h : rationalCircle x = 0) : x = 0 := by
  induction x using QuotientAddGroup.induction_on with
  | H q =>
    have h' : Circle.exp (2 * Real.pi * (q : ℝ)) = 1 := h
    rw [Circle.exp_eq_one] at h'
    obtain ⟨n, hn⟩ := h'
    have hq : q = (n : ℚ) := by
      have : (q : ℝ) = n := by
        have hpi : (2 * Real.pi) ≠ 0 := by positivity
        field_simp at hn
        linarith
      exact_mod_cast this
    rw [AddCircle.coe_eq_zero_iff]
    exact ⟨n, by simp [hq]⟩

variable {G : Type*} [AddCommGroup G]

/-- **Characters separate the points of a discrete abelian group.** -/
lemma exists_character_apply_ne_one [TopologicalSpace G] [DiscreteTopology G] {g : G}
    (hg : g ≠ 0) : ∃ χ : PontryaginDual (Multiplicative G), χ (Multiplicative.ofAdd g) ≠ 1 := by
  obtain ⟨c, hc⟩ := CharacterModule.exists_character_apply_ne_zero_of_ne_zero hg
  refine ⟨⟨⟨⟨fun a => Additive.toMul (rationalCircle (c (Multiplicative.toAdd a))), ?_⟩, ?_⟩,
    continuous_of_discreteTopology⟩, ?_⟩
  · simp
  · intro a b
    simp [map_add]
  · intro h
    apply hc
    apply rationalCircle_eq_zero
    exact h

/-! ## B. The Haar measure of the dual group -/

section Haar

variable [TopologicalSpace G] [DiscreteTopology G]
variable [MeasurableSpace (PontryaginDual (Multiplicative G))]
  [BorelSpace (PontryaginDual (Multiplicative G))]

/-- The normalized Haar measure of the compact dual group. -/
def dualHaar : Measure (PontryaginDual (Multiplicative G)) :=
  Measure.haarMeasure ⊤

instance : (dualHaar (G := G)).IsHaarMeasure := by
  unfold dualHaar; infer_instance

instance : IsProbabilityMeasure (dualHaar (G := G)) :=
  ⟨by
    have h : dualHaar (G := G) ((⊤ : TopologicalSpace.PositiveCompacts
        (PontryaginDual (Multiplicative G))) : Set _) = 1 := Measure.haarMeasure_self
    simpa using h⟩

open scoped Classical in
/-- **Orthogonality of characters**: the evaluation characters are orthonormal for the Haar
probability measure of the dual group. -/
lemma integral_character_dualHaar (g : G) :
    ∫ χ, ((χ (Multiplicative.ofAdd g) : Circle) : ℂ) ∂(dualHaar (G := G)) =
      if g = 0 then 1 else 0 := by
  by_cases hg : g = 0
  · subst hg
    simp
  · rw [ite_eq_right hg]
    obtain ⟨χ₀, hχ₀⟩ := exists_character_apply_ne_one (G := G) hg
    have h := integral_mul_left_eq_self
      (fun χ : PontryaginDual (Multiplicative G) => ((χ (Multiplicative.ofAdd g) : Circle) : ℂ))
      χ₀ (μ := dualHaar (G := G))
    have hmul : ∀ χ : PontryaginDual (Multiplicative G),
        (((χ₀ * χ) (Multiplicative.ofAdd g) : Circle) : ℂ) =
          ((χ₀ (Multiplicative.ofAdd g) : Circle) : ℂ) *
            ((χ (Multiplicative.ofAdd g) : Circle) : ℂ) := fun χ => rfl
    simp only [hmul, integral_const_mul] at h
    have hne : ((χ₀ (Multiplicative.ofAdd g) : Circle) : ℂ) ≠ 1 := fun h1 =>
      hχ₀ (Circle.ext h1)
    by_contra hI
    apply hne
    have := mul_right_cancel₀ hI (h.trans (one_mul _).symm)
    exact this

end Haar

end QuantumMechanics

end ProbabilisticTheory

end
