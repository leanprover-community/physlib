/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import PhyslibAlpha.Mathematics.TauCeti.RepresentationTheory.Continuous.Pontryagin.Basic

/-!
# Continuity of the integrated-character parameter

Let `π` be a strongly continuous unitary representation of an abelian topological group equipped
with a regular invariant measure, and let `A` be a complete star subalgebra containing all
integrated operators.

## i. Overview

Let `π` be a strongly continuous unitary representation of an abelian topological group equipped
with a regular invariant measure, and let `A` be a complete star subalgebra containing all
integrated operators.
A character of `A` that is nonzero on some integrated operator determines a continuous group
character by `ContRepresentation.existsUnique_pontryaginDual_of_integratedOperatorL1`.

This file packages the characters on which that construction is defined and proves that the
resulting map to the Pontryagin dual is continuous.  Near a character `ω`, choose an integrated
operator `π(f)` on which `ω` is nonzero.  The detected group character then has the local formula

`χ(g) = ω(π(g)π(f)) / ω(π(f))`.

The numerator is jointly continuous in `ω` and `g`: norm continuity of translated integrated
operators combines with weak-* continuity of evaluation and the uniform norm bound on characters
of a Banach algebra.  The denominator remains nonzero in a neighbourhood of `ω`, so the displayed
quotient proves the required local continuity.  This continuity is the input needed to push a
character-space spectral measure to the Pontryagin dual.

## ii. Key results

* `ContRepresentation.integratedCharacterSet`: algebra characters that do not annihilate every
  integrated operator.
* `ContRepresentation.integratedCharacterToPontryaginDual`: the group character detected by an
  integrated-algebra character.
* `ContRepresentation.continuous_integratedCharacterToPontryaginDual`: continuity of this
  assignment.

## iii. Table of contents

- A. Development

## iv. References

* G. B. Folland, *A Course in Abstract Harmonic Analysis*, second edition, §§3.2 and 4.4.
* The local-quotient continuity proof generalizes Tau Ceti's earlier formalization in
  `TauCeti.StronglyContinuousSpectral.continuousOn_dual`
  (`TauCeti.Analysis.Fourier.Pontryagin.StronglyContinuous`), which was stated for the
  integrated algebra of a unitary representation with respect to a Haar measure.
-/

public section

/-! ## A. Development -/

noncomputable section

open Filter MeasureTheory WeakDual
open scoped Topology

variable {G H : Type*} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
  [MeasurableSpace G] [BorelSpace G]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {μ : Measure G} [μ.IsAddLeftInvariant] [μ.InnerRegularCompactLTTop]
  [IsLocallyFiniteMeasure μ]

namespace ContRepresentation

variable (π : ContRepresentation ℂ (Multiplicative G) H)
  (hcont : ∀ v, Continuous fun g : G => π (.ofAdd g) v)
  (hbdd : ∃ C, ∀ g, ‖π g‖ ≤ C)
  (A : StarSubalgebra ℂ (H →L[ℂ] H)) [CompleteSpace A]
  (hA : ∀ f : G →₁[μ] ℂ, π.integratedOperatorL1 hcont hbdd μ f ∈ A)

/-- The characters of an algebra containing the integrated form which do not annihilate every
integrated operator.  When `π` is unitary, these are exactly the algebra characters from which
the representation detects a point of the Pontryagin dual. -/
def integratedCharacterSet : Set (characterSpace ℂ A) :=
  {ω | ∃ f : G →₁[μ] ℂ, ω ⟨π.integratedOperatorL1 hcont hbdd μ f, hA f⟩ ≠ 0}

omit [μ.IsAddLeftInvariant] [IsLocallyFiniteMeasure μ] [CompleteSpace A] in
/-- Membership in the integrated-character set means nonvanishing on some integrated operator. -/
@[simp]
lemma mem_integratedCharacterSet_iff (ω : characterSpace ℂ A) :
    ω ∈ π.integratedCharacterSet hcont hbdd A hA ↔
      ∃ f : G →₁[μ] ℂ, ω ⟨π.integratedOperatorL1 hcont hbdd μ f, hA f⟩ ≠ 0 :=
  Iff.rfl

omit [μ.IsAddLeftInvariant] [IsLocallyFiniteMeasure μ] [CompleteSpace A] in
/-- The integrated-character set is open in the character space. -/
lemma isOpen_integratedCharacterSet :
    IsOpen (π.integratedCharacterSet hcont hbdd A hA) := by
  rw [isOpen_iff_mem_nhds]
  intro ω hω
  obtain ⟨f, hf⟩ := (π.mem_integratedCharacterSet_iff hcont hbdd A hA ω).mp hω
  apply mem_of_superset ((isOpen_ne_fun ((eval_continuous _).comp continuous_subtype_val)
    continuous_const).mem_nhds hf)
  intro ψ hψ
  exact (π.mem_integratedCharacterSet_iff hcont hbdd A hA ψ).mpr ⟨f, hψ⟩

variable (hπ : ContRepresentation.IsUnitary π)

/-- The continuous group character detected by an algebra character that does not annihilate the
integrated form. -/
noncomputable def integratedCharacterToPontryaginDual
    (ω : π.integratedCharacterSet hcont hbdd A hA) : PontryaginDual (Multiplicative G) :=
  Classical.choose
    (π.existsUnique_pontryaginDual_of_integratedOperatorL1 hbdd hπ A hA ω.1
      ((π.mem_integratedCharacterSet_iff hcont hbdd A hA ω).mp ω.2))

/-- The defining multiplier identity for the group character detected by an integrated
character. -/
lemma integratedCharacterToPontryaginDual_spec
    (ω : π.integratedCharacterSet hcont hbdd A hA) (g : G) (f : G →₁[μ] ℂ) :
    ω.1
        ⟨π.integratedOperatorL1 hcont hbdd μ
          (Lp.compMeasurePreserving (fun t => -g + t)
            (measurePreserving_add_left μ (-g)) f), hA _⟩ =
      (π.integratedCharacterToPontryaginDual hcont hbdd A hA hπ ω (.ofAdd g) : ℂ) *
        ω.1 ⟨π.integratedOperatorL1 hcont hbdd μ f, hA f⟩ :=
  (Classical.choose_spec
    (π.existsUnique_pontryaginDual_of_integratedOperatorL1 hbdd hπ A hA ω.1
      ((π.mem_integratedCharacterSet_iff hcont hbdd A hA ω).mp ω.2))).1 g f

/-- Local quotient formula for the group character detected by an integrated character. -/
lemma coe_integratedCharacterToPontryaginDual_apply_eq_div
    (ω : π.integratedCharacterSet hcont hbdd A hA) (g : G) (f : G →₁[μ] ℂ)
    (hf : ω.1 ⟨π.integratedOperatorL1 hcont hbdd μ f, hA f⟩ ≠ 0) :
    (π.integratedCharacterToPontryaginDual hcont hbdd A hA hπ ω (.ofAdd g) : ℂ) =
      ω.1 ⟨π.integratedOperatorL1 hcont hbdd μ
        (Lp.compMeasurePreserving (fun t => -g + t)
          (measurePreserving_add_left μ (-g)) f), hA _⟩ /
        ω.1 ⟨π.integratedOperatorL1 hcont hbdd μ f, hA f⟩ :=
  (eq_div_iff hf).2
    (π.integratedCharacterToPontryaginDual_spec hcont hbdd A hA hπ ω g f).symm

/-- The group character detected by a nonvanishing integrated character depends continuously on
the algebra character. -/
lemma continuous_integratedCharacterToPontryaginDual :
    Continuous (π.integratedCharacterToPontryaginDual hcont hbdd A hA hπ) := by
  let D := π.integratedCharacterSet hcont hbdd A hA
  let θ : D → PontryaginDual (Multiplicative G) :=
    π.integratedCharacterToPontryaginDual hcont hbdd A hA hπ
  apply ContinuousMonoidHom.continuous_of_continuous_uncurry
  apply continuous_induced_rng.mpr
  rw [continuous_iff_continuousAt]
  rintro ⟨ω, g⟩
  obtain ⟨f, hf⟩ := (π.mem_integratedCharacterSet_iff hcont hbdd A hA ω).mp ω.2
  let a : A := ⟨π.integratedOperatorL1 hcont hbdd μ f, hA f⟩
  let v : Multiplicative G → A := fun g =>
    ⟨π.integratedOperatorL1 hcont hbdd μ
      (Lp.compMeasurePreserving (fun t => -g.toAdd + t)
        (measurePreserving_add_left μ (-g.toAdd)) f), hA _⟩
  have hv : Continuous v := by
    apply continuous_induced_rng.mpr
    refine ((π.continuous_comp_integratedOperatorL1 (hcont := hcont) (hbdd := hbdd) f).comp
      continuous_toAdd).congr fun g => ?_
    exact π.comp_integratedOperatorL1 (hcont := hcont) (hbdd := hbdd) g.toAdd f
  have heval (b : A) : Continuous fun p : D × Multiplicative G => (p.1.1 b : ℂ) :=
    (eval_continuous b).comp (continuous_subtype_val.comp (continuous_subtype_val.comp
      continuous_fst))
  -- Characters are uniformly bounded, so `ω(v g') - ω(v g)` is small uniformly in `ω`.
  have hnum : ContinuousAt (fun p : D × Multiplicative G => (p.1.1 (v p.2) : ℂ)) (ω, g) := by
    have hsmall : Tendsto (fun p : D × Multiplicative G => p.1.1 (v p.2 - v g)) (𝓝 (ω, g))
        (𝓝 0) := by
      refine squeeze_zero_norm (fun p => AlgHom.norm_apply_le_self_mul_norm_one p.1.1 _) ?_
      simpa using ((hv.comp continuous_snd).sub (continuous_const (y := v g))).norm.mul_const
        ‖(1 : A)‖ |>.tendsto (ω, g)
    have h : Tendsto (fun p : D × Multiplicative G => (p.1.1 (v p.2) : ℂ)) (𝓝 (ω, g))
        (𝓝 (ω.1 (v g) + 0)) :=
      ((heval (v g)).continuousAt.tendsto.add hsmall).congr fun p => by simp
    rwa [add_zero] at h
  have hden : Continuous fun p : D × Multiplicative G => (p.1.1 a : ℂ) := heval a
  have hquot : ContinuousAt (fun p : D × Multiplicative G =>
      p.1.1 (v p.2) / p.1.1 a) (ω, g) :=
    hnum.div hden.continuousAt (by simpa only [a] using hf)
  have hden_ne : ∀ᶠ p in 𝓝 (ω, g), p.1.1 a ≠ 0 :=
    hden.continuousAt.eventually_ne (by simpa only [a] using hf)
  -- `Circle` is a non-reducible type synonym for the unit-sphere subtype of `ℂ`, so
  -- `continuous_induced_rng` leaves the goal in terms of `Subtype.val`, which `simp` cannot
  -- match against the `Circle` coercion used by the quotient formula; restate it by unfolding.
  change ContinuousAt (fun p : D × Multiplicative G => (θ p.1 p.2 : ℂ)) (ω, g)
  apply hquot.congr_of_eventuallyEq
  filter_upwards [hden_ne] with p hp
  simpa only [θ, v, a, ofAdd_toAdd] using π.coe_integratedCharacterToPontryaginDual_apply_eq_div
    hcont hbdd A hA hπ p.1 p.2.toAdd f hp

end ContRepresentation
