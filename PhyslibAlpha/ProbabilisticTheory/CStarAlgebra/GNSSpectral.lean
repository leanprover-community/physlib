/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.ProbabilisticTheory.CStarAlgebra.GNSAutomorphism
public import PhyslibAlpha.ProbabilisticTheory.Representation.Commutant

/-!

# The momentum decomposition of an invariant state

The GNS space of a translation-invariant state decomposes over the momenta, and the momentum
distribution of a local excitation is its structure factor.

## i. Overview

For a state `ω` of a C⋆-algebra and an abelian group `G` of ⋆-automorphisms preserving `ω`, the
unitary representation of `G` on the GNS space is the integral of the characters of `G` against a
projection-valued measure `P` on the Pontryagin dual of `G`. The cyclic vector `Ω` is invariant, so
it has momentum zero: `P` gives it to the trivial character. The vector `π(a) Ω` created by an
observable `a` has momentum distribution `μ_a`, the finite measure with
`∫ χ(g) dμ_a(χ) = ω(a⋆ α_g(a))`, the structure factor of `a`, and total mass `ω(a⋆ a)`.

## ii. Key results

- `UnitalPositiveLinearMap.gnsStructureFactor` : the momentum distribution of `π(a) Ω`.
- `UnitalPositiveLinearMap.integral_gnsStructureFactor` : its Fourier transform is the
  correlation function of `a`.
- `UnitalPositiveLinearMap.projection_one_gnsCyclicVector` : the invariant vector has momentum
  zero.

## iii. Table of contents

- A. The momentum distribution of a local excitation
- B. The invariant vector

## iv. References

* None.

-/

@[expose] public section

noncomputable section

namespace ProbabilisticTheory

open MeasureTheory
open scoped ComplexOrder InnerProductSpace
open QuantumMechanics QuantumMechanics.UnitaryRep

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

namespace UnitalPositiveLinearMap

variable {ω : 𝓢[ℂ, A]}
variable {G : Type*} [AddCommGroup G] [TopologicalSpace G] [DiscreteTopology G]
variable {α : Multiplicative G →* (A ≃⋆ₐ[ℂ] A)} (hα : ∀ g a, ω (α g a) = ω a)
variable [MeasurableSpace (PontryaginDual (Multiplicative G))]
  [BorelSpace (PontryaginDual (Multiplicative G))]

/-! ## A. The momentum distribution of a local excitation -/

/-- The momentum distribution of the excitation `π(a) Ω` created by the observable `a` from the
invariant state: the distribution of the vector `π(a) Ω` over the characters of the symmetry
group. -/
def gnsStructureFactor (a : A) : Measure (PontryaginDual (Multiplicative G)) :=
  vectorMeasure (gnsUnitaryRep hα) (ω.gnsRep a ω.gnsCyclicVector)

instance (a : A) : IsFiniteMeasure (gnsStructureFactor hα a) :=
  inferInstanceAs (IsFiniteMeasure (vectorMeasure (gnsUnitaryRep hα) _))

/-- **The Fourier transform of the momentum distribution is the correlation function**:
`∫ χ(g) dμ_a(χ) = ω(a⋆ α_g(a))`. -/
lemma integral_gnsStructureFactor (a : A) (g : Multiplicative G) :
    ∫ χ, ((χ g : Circle) : ℂ) ∂gnsStructureFactor hα a = ω (star a * α g a) := by
  rw [gnsStructureFactor, ← inner_eq_integral_vectorMeasure]
  exact inner_gnsRep_cyclicVector_gnsUnitary hα g a

/-- The total momentum weight of the excitation `π(a) Ω` is `ω(a⋆ a)`. -/
lemma gnsStructureFactor_univ (a : A) :
    (gnsStructureFactor hα a).real Set.univ = (ω (star a * a)).re := by
  have h := integral_gnsStructureFactor hα a 1
  simp only [map_one, Circle.coe_one, integral_const] at h
  have h2 := congrArg Complex.re h
  simpa using h2

/-! ## B. The invariant vector -/

omit [DiscreteTopology G] in
omit [BorelSpace (PontryaginDual (Multiplicative G))] in
omit [MeasurableSpace (PontryaginDual (Multiplicative G))] in
/-- The cyclic vector of an invariant state has momentum zero: its spectral measure is carried
by the trivial character. -/
lemma gnsCyclicVector_mem_sector :
    ω.gnsCyclicVector ∈ ProbabilisticTheory.Representation.sector (toEnd (gnsUnitaryRep hα))
      (fun g => (((1 : PontryaginDual (Multiplicative G)) g : Circle) : ℂ)) := by
  intro g
  rw [toEnd_apply]
  show ((gnsUnitary hα g : unitary (ω.GNS →L[ℂ] ω.GNS)) : ω.GNS →L[ℂ] ω.GNS) _ = _ • _
  have h := gnsUnitary_cyclicVector hα g
  simpa using h

/-- **The vacuum has momentum zero.** For a countable symmetry group the spectral projection of
the trivial character fixes the cyclic vector. -/
lemma projection_one_gnsCyclicVector [Countable G] :
    projection (gnsUnitaryRep hα) {(1 : PontryaginDual (Multiplicative G))} ω.gnsCyclicVector =
      ω.gnsCyclicVector :=
  projection_singleton_eq_self_of_mem_sector _ 1 (gnsCyclicVector_mem_sector hα)

end UnitalPositiveLinearMap

end ProbabilisticTheory

end
