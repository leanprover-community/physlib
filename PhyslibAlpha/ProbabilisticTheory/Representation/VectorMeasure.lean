/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.ProbabilisticTheory.Representation.AbelianSpectral
public import PhyslibAlpha.Mathematics.TauCeti.Analysis.Fourier.Pontryagin.Uniqueness
public import PhyslibAlpha.Mathematics.TauCeti.Analysis.Fourier.Pontryagin.Measure

/-!

# The spectral measure of a vector

The distribution of a vector over the characters of the group, and its uniqueness.

## i. Overview

For a unitary representation `π` of an abelian group and a vector `ξ`, the diagonal measure
`S ↦ ‖P(S) ξ‖²` of the spectral measure is a finite measure `μ_ξ` on the Pontryagin dual with
`⟪ξ, π(g) ξ⟫ = ∫ χ(g) dμ_ξ(χ)`. It is the distribution of `ξ` over the characters of the group;
for a state it is the momentum distribution. Its total mass is `‖ξ‖²`. For a countable group, a
finite measure on the dual is determined by its Fourier–Stieltjes transform, so `μ_ξ` is the
unique measure with this property.

## ii. Key results

- `UnitaryRep.vectorMeasure` : the spectral measure `μ_ξ` of a vector.
- `UnitaryRep.inner_eq_integral_vectorMeasure` : `⟪ξ, π(g) ξ⟫ = ∫ χ(g) dμ_ξ(χ)`.
- `UnitaryRep.vectorMeasure_univ` : the total mass of `μ_ξ` is `‖ξ‖²`.
- `UnitaryRep.eq_vectorMeasure_of_transform_eq` : uniqueness of the spectral measure of a vector.

## iii. Table of contents

- A. The spectral measure of a vector
- B. Uniqueness

## iv. References

* None.

-/

@[expose] public section

noncomputable section

namespace ProbabilisticTheory

open MeasureTheory Set Topology WeakDual
open scoped ComplexOrder CStarAlgebra InnerProductSpace

namespace QuantumMechanics

namespace UnitaryRep

variable {G : Type*} [AddCommGroup G] [TopologicalSpace G] [DiscreteTopology G]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (π : Multiplicative G →* unitary (H →L[ℂ] H))
variable [MeasurableSpace (PontryaginDual (Multiplicative G))]
  [BorelSpace (PontryaginDual (Multiplicative G))]

/-! ## A. The spectral measure of a vector -/

/-- The spectral measure `S ↦ ‖P(S) ξ‖²` of a vector `ξ`, a finite measure on the Pontryagin dual:
the distribution of `ξ` over the characters of the group. -/
def vectorMeasure (ξ : H) : Measure (PontryaginDual (Multiplicative G)) :=
  (spectralMeasure π).diagonalMeasure ξ

instance (ξ : H) : IsFiniteMeasure (vectorMeasure π ξ) :=
  inferInstanceAs (IsFiniteMeasure ((spectralMeasure π).diagonalMeasure ξ))

lemma vectorMeasure_apply (ξ : H) {S : Set (PontryaginDual (Multiplicative G))}
    (hS : MeasurableSet S) :
    vectorMeasure π ξ S = ENNReal.ofReal (‖spectralMeasure π S ξ‖ ^ 2) :=
  (spectralMeasure π).diagonalMeasure_apply_eq_norm_sq ξ S hS

/-- The total mass of the spectral measure of a vector is its squared norm. -/
lemma vectorMeasure_univ (ξ : H) : vectorMeasure π ξ univ = ENNReal.ofReal (‖ξ‖ ^ 2) :=
  (spectralMeasure π).diagonalMeasure_univ ξ

/-- The vector measure is the pushforward of the Riesz measure of the vector state. -/
lemma vectorMeasure_eq_map (ξ : H) :
    vectorMeasure π ξ = Measure.map (dual π) (starHomScalarMeasure (family π).starHom ξ) := by
  rw [vectorMeasure, spectralMeasure, WOTSpectralMeasure.diagonalMeasure_map]
  congr 1
  exact starHomSpectralMeasure_diagonalMeasure (family π).starHom ξ

/-- **The spectral measure of a vector represents its matrix coefficients**:
`⟪ξ, π(g) ξ⟫ = ∫ χ(g) dμ_ξ(χ)`. -/
lemma inner_eq_integral_vectorMeasure (ξ : H) (g : Multiplicative G) :
    ⟪ξ, ((π g : unitary (H →L[ℂ] H)) : H →L[ℂ] H) ξ⟫_ℂ =
      ∫ χ, ((χ g : Circle) : ℂ) ∂vectorMeasure π ξ := by
  rw [vectorMeasure_eq_map, integral_map (continuous_dual π).aemeasurable
    (TauCeti.PontryaginDual.continuous_coe_eval_const (G := Multiplicative G) g
      ).aestronglyMeasurable]
  have := integral_starHomScalarMeasure (family π).starHom
    (gelfandStarTransform (family π).algebra (elem π g)) ξ
  rw [(family π).starHom_gelfandStarTransform] at this
  exact this.symm

/-! ## B. Uniqueness -/

section Countable

variable [Countable G]

/-- **Uniqueness of the spectral measure of a vector.** For a countable group, a finite measure on
the Pontryagin dual whose Fourier–Stieltjes transform is `g ↦ ⟪ξ, π(g) ξ⟫` is the spectral
measure of `ξ`. -/
lemma eq_vectorMeasure_of_transform_eq (ξ : H) (μ : Measure (PontryaginDual (Multiplicative G)))
    [IsFiniteMeasure μ]
    (h : ∀ g : Multiplicative G, ∫ χ, ((χ g : Circle) : ℂ) ∂μ =
      ⟪ξ, ((π g : unitary (H →L[ℂ] H)) : H →L[ℂ] H) ξ⟫_ℂ) :
    μ = vectorMeasure π ξ := by
  have : Countable (Multiplicative G) := inferInstanceAs (Countable G)
  have : SecondCountableTopology (Multiplicative G) :=
    DiscreteTopology.secondCountableTopology_of_countable
  have : PolishSpace (PontryaginDual (Multiplicative G)) := TauCeti.instPolishSpacePontryaginDual
  let Pμ : FiniteMeasure (PontryaginDual (Multiplicative G)) := ⟨μ, inferInstance⟩
  let Pv : FiniteMeasure (PontryaginDual (Multiplicative G)) := ⟨vectorMeasure π ξ, inferInstance⟩
  have key : Pμ = Pv := FiniteMeasure.ext_of_forall_pontryaginMeasureTransform_eq (fun g => by
    have e1 := FiniteMeasure.pontryaginMeasureTransform_apply Pμ g
    have e2 := FiniteMeasure.pontryaginMeasureTransform_apply Pv g
    rw [e1, e2]
    exact (h (Multiplicative.ofAdd g)).trans
      (inner_eq_integral_vectorMeasure π ξ (Multiplicative.ofAdd g)))
  exact congrArg FiniteMeasure.toMeasure key

end Countable

end UnitaryRep

end QuantumMechanics

end ProbabilisticTheory

end
