/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.ProbabilisticTheory.HilbertSpace.Unbounded.WeakIntegral
public import PhyslibAlpha.ProbabilisticTheory.HilbertSpace.Unbounded.Cayley.Basic

/-!

# Spectral measures and the Cayley transform

## i. Overview

Spectral measures on `ℝ` push forward along the Cayley transform to spectral measures on `ℂ`
supported on the unit circle away from `1`. Pulling back along the inverse Cayley transform undoes
this, which gives an equivalence between spectral measures on `ℝ` and such measures on `ℂ`.

## ii. Key results

- `cayleyMap`, `cayleyInverseMap` : pushing forward along the Cayley transform and its inverse.
- `cayleyMap_injective` : the pushforward is injective.
- `CayleySupported` : a spectral measure on `ℂ` supported on the unit circle away from `1`.
- `cayleyMeasureEquiv` : the equivalence between spectral measures on `ℝ` and Cayley-supported ones
  on `ℂ`.

## iii. Table of contents

- A. Pushforward and pullback along the Cayley transform
- B. The Cayley equivalence of spectral-measure data

-/

@[expose] public section

noncomputable section

namespace ProbabilisticTheory

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

/-- A spectral measure on `ℂ` is Cayley supported when it lives on the unit circle and gives no mass
to `1`. -/
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

/-- The Cayley transform is an equivalence between spectral measures on `ℝ` and Cayley-supported
spectral measures on `ℂ`. -/
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

end ProbabilisticTheory

end
