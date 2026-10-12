/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.Mathematics.TauCeti.Analysis.Bochner.DiscreteGroup
public import PhyslibAlpha.Mathematics.TauCeti.Analysis.Fourier.Pontryagin.Uniqueness
public import PhyslibAlpha.Mathematics.TauCeti.Analysis.Fourier.Pontryagin.Measure
public import PhyslibAlpha.Mathematics.TauCeti.Topology.Algebra.PontryaginDual

/-!

# The structure factor of an invariant state

The correlation function of a translation-invariant positive functional is the Fourier transform of
a positive measure on the momenta.

## i. Overview

Let `B` be a ⋆-algebra of observables on which a discrete abelian group `G` of translations acts by
⋆-automorphisms `α_g`, and let `ω` be a positive linear functional with `ω ∘ α_g = ω`. For an
observable `a` the correlation function `g ↦ ω(a⋆ α_g(a))` is positive definite on `G`: for any
finite family of translations `g_i` and scalars `c_i` it is the value of `ω` at `b⋆ b` with
`b = ∑ c_i α_{g_i}(a)`. By Bochner's theorem for discrete abelian groups it is the Fourier
transform of a unique finite positive measure `μ_a` on the Pontryagin dual of `G`, the group of
momenta. This measure is the structure factor of `a`: its total mass is `ω(a⋆ a)`, and
`∫ χ(g) dμ_a(χ) = ω(a⋆ α_g(a))`. No Hilbert space, representation of the algebra or Hamiltonian is
needed, and the algebra need not be a C⋆-algebra.

## ii. Key results

- `StructureFactor.isPositiveDefiniteSub_correlation` : the correlation function is positive
  definite.
- `StructureFactor.exists_measure` : the structure factor exists.
- `StructureFactor.measure_univ` : its total mass is `ω(a⋆ a)`.
- `StructureFactor.eq_of_transform_eq` : for a countable group it is unique.
- `StructureFactor.isPositiveDefiniteSub_iff_exists_measure` : positive semidefinite
  translation-invariant couplings are Fourier transforms of positive measures.

## iii. Table of contents

- A. Positive definiteness of the correlation function
- B. The structure factor

## iv. References

* None.

-/

@[expose] public section

noncomputable section

namespace ProbabilisticTheory

open MeasureTheory Set Topology
open scoped ComplexOrder

namespace QuantumMechanics

namespace StructureFactor

variable {G : Type*} [AddCommGroup G]
variable {B : Type*} [Ring B] [StarRing B] [Algebra ℂ B] [StarModule ℂ B]
variable (ω : B →ₗ[ℂ] ℂ) (α : Multiplicative G →* (B ≃⋆ₐ[ℂ] B))

/-- The correlation function `g ↦ ω(a⋆ α_g(a))` of an observable `a`. -/
def correlation (a : B) (g : G) : ℂ := ω (star a * α (Multiplicative.ofAdd g) a)

/-! ## A. Positive definiteness of the correlation function -/

/-- **The correlation function of an invariant positive functional is positive definite.** -/
lemma isPositiveDefiniteSub_correlation (hpos : ∀ b : B, 0 ≤ ω (star b * b))
    (hinv : ∀ g b, ω (α g b) = ω b) (a : B) :
    TauCeti.IsPositiveDefiniteSub (correlation ω α a) := by
  rw [TauCeti.isPositiveDefiniteSub_iff_forall_sum_nonneg]
  intro n c v
  set b : B := ∑ i, c i • α (Multiplicative.ofAdd (v i)) a with hb
  have key : ∀ i j, ω (star (α (Multiplicative.ofAdd (v j)) a) *
      α (Multiplicative.ofAdd (v i)) a) = correlation ω α a (v i - v j) := by
    intro i j
    have h1 : star (α (Multiplicative.ofAdd (v j)) a) * α (Multiplicative.ofAdd (v i)) a =
        α (Multiplicative.ofAdd (v j)) (star a * α (Multiplicative.ofAdd (v i - v j)) a) := by
      have hcomp : α (Multiplicative.ofAdd (v j)) (α (Multiplicative.ofAdd (v i - v j)) a) =
          α (Multiplicative.ofAdd (v i)) a := by
        have : α (Multiplicative.ofAdd (v j)) (α (Multiplicative.ofAdd (v i - v j)) a) =
            α (Multiplicative.ofAdd (v j) * Multiplicative.ofAdd (v i - v j)) a := by
          rw [map_mul]; rfl
        rw [this, ← ofAdd_add]
        congr 2
        abel_nf
      rw [map_mul, map_star, hcomp]
    rw [h1, hinv]
    rfl
  have hsum : ω (star b * b) = ∑ i, ∑ j, c i * (starRingEnd ℂ) (c j) *
      correlation ω α a (v i - v j) := by
    rw [hb, star_sum, Finset.sum_mul, map_sum, Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    rw [map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [star_smul, smul_mul_smul_comm, map_smul, key k i, smul_eq_mul]
    simp only [RCLike.star_def]
    ring
  rw [← hsum]
  exact hpos b

/-! ## B. The structure factor -/

section Bochner

variable [TopologicalSpace G] [DiscreteTopology G]
  [MeasurableSpace (PontryaginDual (Multiplicative G))]
  [BorelSpace (PontryaginDual (Multiplicative G))]

/-- **The structure factor exists.** The correlation function of an observable in an invariant
positive functional is the Fourier transform of a finite positive measure on the momenta:
`ω(a⋆ α_g(a)) = ∫ χ(g) dμ_a(χ)`. -/
lemma exists_measure (hpos : ∀ b : B, 0 ≤ ω (star b * b)) (hinv : ∀ g b, ω (α g b) = ω b)
    (a : B) :
    ∃ μ : Measure (PontryaginDual (Multiplicative G)), IsFiniteMeasure μ ∧ μ.InnerRegular ∧
      ∀ g : G, ∫ χ, ((χ (Multiplicative.ofAdd g) : Circle) : ℂ) ∂μ = correlation ω α a g := by
  obtain ⟨μ, hreg, hμ⟩ := (TauCeti.isPositiveDefiniteSub_iff_exists_pontryaginMeasureTransform_eq
    (correlation ω α a)).mp (isPositiveDefiniteSub_correlation ω α hpos hinv a)
  refine ⟨μ.toMeasure, inferInstance, hreg, fun g => ?_⟩
  rw [← hμ, FiniteMeasure.pontryaginMeasureTransform_apply]

omit [StarModule ℂ B] [DiscreteTopology G]
  [BorelSpace (PontryaginDual (Multiplicative G))] in
/-- The total mass of the structure factor is the expectation of `a⋆ a`. -/
lemma integral_one_eq {μ : Measure (PontryaginDual (Multiplicative G))}
    (a : B) (h : ∀ g : G, ∫ χ, ((χ (Multiplicative.ofAdd g) : Circle) : ℂ) ∂μ =
      correlation ω α a g) :
    (μ.real univ : ℂ) = ω (star a * a) := by
  have h0 := h 0
  simp only [ofAdd_zero, map_one, Circle.coe_one, integral_const] at h0
  simpa [correlation] using h0

section Countable

variable [Countable G]

/-- **The structure factor is unique.** For a countable group a finite measure on the momenta is
determined by its Fourier transform. -/
lemma eq_of_transform_eq {μ ν : Measure (PontryaginDual (Multiplicative G))}
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : ∀ g : G, ∫ χ, ((χ (Multiplicative.ofAdd g) : Circle) : ℂ) ∂μ =
      ∫ χ, ((χ (Multiplicative.ofAdd g) : Circle) : ℂ) ∂ν) : μ = ν := by
  have : Countable (Multiplicative G) := inferInstanceAs (Countable G)
  have : SecondCountableTopology (Multiplicative G) :=
    DiscreteTopology.secondCountableTopology_of_countable
  have : PolishSpace (PontryaginDual (Multiplicative G)) := TauCeti.instPolishSpacePontryaginDual
  let Pμ : FiniteMeasure (PontryaginDual (Multiplicative G)) := ⟨μ, inferInstance⟩
  let Pν : FiniteMeasure (PontryaginDual (Multiplicative G)) := ⟨ν, inferInstance⟩
  have key : Pμ = Pν := FiniteMeasure.ext_of_forall_pontryaginMeasureTransform_eq (fun g => by
    rw [FiniteMeasure.pontryaginMeasureTransform_apply Pμ g,
      FiniteMeasure.pontryaginMeasureTransform_apply Pν g]
    exact h g)
  exact congrArg FiniteMeasure.toMeasure key

end Countable

/-- **Positive semidefinite translation-invariant couplings are Fourier transforms of positive
measures.** A coupling `J(r)` depending only on the displacement `r` is positive semidefinite, in
the sense that every finite quadratic form `∑ c_i c̄_j J(r_i - r_j)` is nonnegative, if and only if
it is the Fourier transform of a finite positive measure on the momenta, whose density is the
dispersion of the coupling. -/
lemma isPositiveDefiniteSub_iff_exists_measure (J : G → ℂ) :
    TauCeti.IsPositiveDefiniteSub J ↔
      ∃ μ : Measure (PontryaginDual (Multiplicative G)), IsFiniteMeasure μ ∧ μ.InnerRegular ∧
        ∀ r : G, J r = ∫ χ, ((χ (Multiplicative.ofAdd r) : Circle) : ℂ) ∂μ := by
  rw [TauCeti.isPositiveDefiniteSub_iff_exists_pontryaginMeasureTransform_eq]
  constructor
  · rintro ⟨μ, hreg, hμ⟩
    exact ⟨μ.toMeasure, inferInstance, hreg, fun r => by
      rw [← hμ, FiniteMeasure.pontryaginMeasureTransform_apply]⟩
  · rintro ⟨μ, hfin, hreg, hμ⟩
    let Pμ : FiniteMeasure (PontryaginDual (Multiplicative G)) := ⟨μ, hfin⟩
    refine ⟨Pμ, hreg, funext fun r => ?_⟩
    have h := FiniteMeasure.pontryaginMeasureTransform_apply Pμ r
    exact h.trans (hμ r).symm

end Bochner

end StructureFactor

end QuantumMechanics

end ProbabilisticTheory

end
