/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.AlgebraicFramework.HilbertSpace.Unbounded.WeakIntegral
public import PhyslibAlpha.AlgebraicFramework.HilbertSpace.Unbounded.Cayley.Basic

/-!

# Transporting a spectral measure through the Cayley transform

`Cayley/Basic.lean` gives the scalar Cayley transform `cayley : ℝ → ℂ` and its (one-sided)
inverse `cayleyInverse`. This file pushes a `WOTSpectralMeasure` forward and backward along those
maps (`cayleyMap`, `cayleyInverseMap`), proves the round trip on the real side is exact
(`cayleyInverseMap_cayleyMap`, hence `cayleyMap_injective`), and identifies exactly which complex
measures are genuine Cayley images: those supported on the unit circle away from `1`
(`CayleySupported`), giving an equivalence `cayleyMeasureEquiv` between real spectral measures and
Cayley-supported complex ones. This is the reusable measure-level core of the self-adjoint/unitary
correspondence; no unbounded operator is mentioned in this file at all.

- `cayleyMap`, `cayleyInverseMap` : pushing a `WOTSpectralMeasure` forward/backward along the
  Cayley transform.
- `cayleyInverseMap_cayleyMap`, `cayleyMap_injective` : the round trip on the real side, and the
  resulting injectivity of `cayleyMap`.
- `cayleyMeasureEquiv` : the equivalence between real spectral measures and complex spectral
  measures supported on the unit circle away from `1`.

-/

@[expose] public section

noncomputable section

open Function MeasureTheory Set
open scoped ComplexOrder InnerProductSpace

namespace QuantumMechanics
namespace WOTSpectralMeasure

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-! ## A. Pushforward and pullback along the Cayley transform -/

/-- The bounded spectral measure obtained from a real spectral measure by the Cayley map. -/
def cayleyMap (μS : WOTSpectralMeasure ℝ H) : WOTSpectralMeasure ℂ H :=
  μS.map cayley measurable_cayley

/-- Pull a complex spectral measure back to a real variable using the inverse Cayley coordinate. -/
def cayleyInverseMap (ν : WOTSpectralMeasure ℂ H) : WOTSpectralMeasure ℝ H :=
  ν.map cayleyInverse measurable_cayleyInverse

lemma cayleyInverseMap_cayleyMap (μS : WOTSpectralMeasure ℝ H) :
    cayleyInverseMap (cayleyMap μS) = μS := by
  cases μS with
  | mk vm hp hu =>
    have hvm : ((vm.map cayley).map cayleyInverse) = vm := by
      apply MeasureTheory.VectorMeasure.ext
      intro S hS
      rw [MeasureTheory.VectorMeasure.map_apply _ measurable_cayleyInverse hS]
      rw [MeasureTheory.VectorMeasure.map_apply _ measurable_cayley
        (hS.preimage measurable_cayleyInverse)]
      congr 1
      ext x
      simp [Set.mem_preimage, cayleyInverse_cayley]
    unfold cayleyInverseMap cayleyMap
    rw [QuantumMechanics.WOTSpectralMeasure.mk.injEq]
    exact hvm

/-- The Cayley pushforward is injective on real spectral measures. Thus a real spectral measure
is completely recoverable from its bounded Cayley-side measure; this is the basic uniqueness
half of the Cayley equivalence used by the unbounded spectral theorem. -/
lemma cayleyMap_injective {μS νS : WOTSpectralMeasure ℝ H}
    (h : cayleyMap μS = cayleyMap νS) : μS = νS := by
  calc
    μS = cayleyInverseMap (cayleyMap μS) :=
      (cayleyInverseMap_cayleyMap μS).symm
    _ = cayleyInverseMap (cayleyMap νS) := congrArg cayleyInverseMap h
    _ = νS := cayleyInverseMap_cayleyMap νS

/-! ## B. The Cayley equivalence of spectral-measure data -/

/-- The support condition which makes the inverse Cayley coordinate an actual inverse rather than
an arbitrary choice at the point representing infinity. -/
def CayleySupported (ν : WOTSpectralMeasure ℂ H) : Prop :=
  ∀ S : Set ℂ, MeasurableSet S →
    ν S = ν (S ∩ {z | ‖z‖ = 1 ∧ z ≠ 1})

lemma cayleyMap_cayleyInverseMap_of_supported
    {ν : WOTSpectralMeasure ℂ H} (hν : CayleySupported ν) :
    cayleyMap (cayleyInverseMap ν) = ν := by
  rw [WOTSpectralMeasure.mk.injEq]
  apply MeasureTheory.VectorMeasure.ext
  intro S hS
  change ((ν.map cayleyInverse measurable_cayleyInverse).map cayley measurable_cayley) S = ν S
  rw [(ν.map cayleyInverse measurable_cayleyInverse).map_apply cayley measurable_cayley hS]
  rw [ν.map_apply cayleyInverse measurable_cayleyInverse
    (hS.preimage measurable_cayley)]
  have hL : MeasurableSet (cayleyInverse ⁻¹' cayley ⁻¹' S) :=
    (hS.preimage measurable_cayley).preimage measurable_cayleyInverse
  rw [hν _ hL, hν _ hS]
  congr 1
  ext z
  constructor
  · rintro ⟨hz, hunit⟩
    refine ⟨?_, hunit⟩
    simpa [Set.mem_preimage, cayley_cayleyInverse hunit.1 hunit.2] using hz
  · rintro ⟨hz, hunit⟩
    have hz' : cayley (cayleyInverse z) = z := cayley_cayleyInverse hunit.1 hunit.2
    refine ⟨?_, hunit⟩
    simpa [Set.mem_preimage, hz'] using hz

lemma cayleyMap_cayleySupported (μS : WOTSpectralMeasure ℝ H) :
    CayleySupported (cayleyMap μS) := by
  have hne : MeasurableSet {z : ℂ | z ≠ 1} := by
    rw [show {z : ℂ | z ≠ 1} = ({1} : Set ℂ)ᶜ by ext; simp]
    exact (measurableSet_singleton (1 : ℂ)).compl
  have hunit : MeasurableSet {z : ℂ | ‖z‖ = 1 ∧ z ≠ 1} := by
    exact (measurableSet_eq_fun measurable_norm measurable_const).inter
      hne
  intro S hS
  change (μS.map cayley measurable_cayley) S =
    (μS.map cayley measurable_cayley) (S ∩ {z | ‖z‖ = 1 ∧ z ≠ 1})
  rw [μS.map_apply cayley measurable_cayley hS,
    μS.map_apply cayley measurable_cayley
      (MeasurableSet.inter hS hunit)]
  congr 1
  ext x
  constructor
  · intro hx
    exact ⟨hx, cayley_norm x, cayley_ne_one x⟩
  · exact fun hx => hx.1

/-- Cayley transport is an equivalence between real WOT spectral measures and complex WOT
spectral measures supported on the unit circle away from `1`. This is the reusable measure-level
core of the self-adjoint/unitary correspondence. -/
def cayleyMeasureEquiv :
    WOTSpectralMeasure ℝ H ≃ {ν : WOTSpectralMeasure ℂ H // CayleySupported ν} where
  toFun μS := ⟨cayleyMap μS, cayleyMap_cayleySupported μS⟩
  invFun ν := cayleyInverseMap ν.1
  left_inv μS := cayleyInverseMap_cayleyMap μS
  right_inv ν := Subtype.ext (cayleyMap_cayleyInverseMap_of_supported ν.property)

lemma cayleyMap_weakIntegral {μS : WOTSpectralMeasure ℝ H}
    (g : ℂ → ℝ) (x y : H)
    (hg : AEStronglyMeasurable g ((μS.scalarMeasure x y).variation.map cayley))
    (hgi : (μS.scalarMeasure x y).Integrable (g ∘ cayley)) :
    (cayleyMap μS).weakIntegral g x y = μS.weakIntegral (g ∘ cayley) x y := by
  exact WOTSpectralMeasure.weakIntegral_map (μS := μS) cayley measurable_cayley g x y hg hgi

end WOTSpectralMeasure
end QuantumMechanics

end
