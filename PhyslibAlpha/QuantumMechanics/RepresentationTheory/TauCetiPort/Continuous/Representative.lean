/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import PhyslibAlpha.QuantumMechanics.RepresentationTheory.TauCetiPort.Continuous.Character
public import PhyslibAlpha.QuantumMechanics.RepresentationTheory.TauCetiPort.Continuous.Conjugate
public import PhyslibAlpha.QuantumMechanics.RepresentationTheory.TauCetiPort.Continuous.TensorProduct
public import PhyslibAlpha.QuantumMechanics.RepresentationTheory.TauCetiPort.Continuous.Transport

/-!
# The representative ring of a monoid with a topology

A **representative function** on a monoid `G` equipped with a topology is a matrix coefficient of a
finite-dimensional continuous representation of `G`. Their span
`TauCeti.representativeSubmodule` is the **representative ring** `𝓡(G) ⊆ C(G, 𝕜)`, and the point of
this file is that the span is far more than a subspace: it is a `*`-subalgebra,
`TauCeti.representativeStarSubalgebra`.

Three constructions supply the three closure properties, and each is a statement about
representations rather than about functions:

* the **trivial** representation on `𝕜` gives the constants
  (`TauCeti.isRepresentative_one`);
* the **tensor product** of two representations multiplies their matrix coefficients
  (`TauCeti.ContRepresentation.matrixCoeff_tprod`), giving closure under multiplication;
* the **conjugate** representation conjugates them
  (`TauCeti.ContRepresentation.star_matrixCoeff_eq_matrixCoeff_conjugate`), giving closure under the
  involution of `C(G, 𝕜)`.

Characters are sums of diagonal matrix coefficients, so they lie in `𝓡(G)` as well
(`TauCeti.ContRepresentation.character_mem_representativeSubmodule`).

## Implementation notes

The carrier of a representation cannot be quantified over all types at once, so the *definition*
of a representative function pins the standard models `EuclideanSpace 𝕜 (Fin n)`. Nothing is lost:
`TauCeti.matrixCoeff_mem_representativeSubmodule` says that a matrix coefficient of a continuous
representation on *any* finite-dimensional inner product space is a representative function, by
transporting the representation along the isometry supplied by `stdOrthonormalBasis`
(`TauCeti.ContRepresentation.congr`). That transport lemma is what makes the pinned model harmless,
and it is how the closure proofs feed the tensor product `V ⊗ W` and the conjugate back into the
definition. Requiring the carrier to be an inner product space is no restriction on the span
either: over `𝕜` every finite-dimensional space admits an inner product, and every functional on it
is `⟪·, w⟫` for some `w`, so pairing with a functional produces no function beyond these.

No unitarity is required, of `𝓡(G)` or of any lemma about it: none of the three closure properties
uses it, `π ⊗ ρ` and the conjugate of `π` being available for an arbitrary continuous `π`. The
unitary case is the one Layer 4 and Layer 5 work in, and that the three constructions preserve
unitarity is recorded with each of them
(`TauCeti.ContRepresentation.IsUnitary.tprod`, `TauCeti.ContRepresentation.IsUnitary.conjugate`,
`TauCeti.ContRepresentation.IsUnitary.congr`); on a *compact* group the distinction is empty
anyway, since Haar averaging (Layer 1) unitarizes.

Neither `TauCeti.IsRepresentative` nor `TauCeti.representativeSubmodule` exposes its
implementation. What downstream arguments need of them is supplied by
`TauCeti.isRepresentative_iff`, which produces a representation from a representative function, and
`TauCeti.representativeSubmodule_eq_span`, which is what an induction over the span runs on.

**Point separation is deliberately absent.** That `𝓡(G)` separates the points of a compact `G` is
equivalent to the Peter-Weyl theorem, so it cannot be recorded at this stage without circularity;
it is a Layer 5 corollary of the analytic density theorem, proved in
`TauCeti/RepresentationTheory/Compact/RepresentativeDensity.lean`, not an input to it.

## Main definitions

* `TauCeti.IsRepresentative`: being a matrix coefficient of a finite-dimensional continuous
  representation.
* `TauCeti.representativeSubmodule`: the span of the representative functions.
* `TauCeti.representativeStarSubalgebra`: that span, as a `*`-subalgebra of `C(G, 𝕜)`.

## Main statements

* `TauCeti.isRepresentative_iff` and `TauCeti.representativeSubmodule_eq_span`: the elimination
  principles for the two definitions.
* `TauCeti.matrixCoeff_mem_representativeSubmodule`: every matrix coefficient of a
  finite-dimensional continuous representation lies in `𝓡(G)`.
* `TauCeti.IsRepresentative.mul`, `TauCeti.IsRepresentative.star`,
  `TauCeti.isRepresentative_one`, `TauCeti.isRepresentative_zero`: the representative functions
  themselves are closed under multiplication and conjugation and contain the constants and `0`.
* `TauCeti.mul_mem_representativeSubmodule`, `TauCeti.star_mem_representativeSubmodule`: the same
  closure properties for their span.
* `TauCeti.ContRepresentation.character_mem_representativeSubmodule`: characters lie in `𝓡(G)`.

This is the representative-`*`-subalgebra item of Layer 3 of the
[compact-groups roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/CompactGroups/README.md),
the algebra whose uniform density in `C(G)` is the analytic core of Layer 5. The mathematical
development follows Daniel Bump, *Lie Groups*, second edition, Chapter 2, and
T. Bröcker, T. tom Dieck, *Representations of Compact Lie Groups*, Chapter III.
-/

public section

open scoped InnerProductSpace

namespace TauCeti

open _root_.TauCeti.ContRepresentation

section Defs

variable {𝕜 G : Type*} [RCLike 𝕜] [Monoid G] [TopologicalSpace G]

/-- **A representative function** on `G`: a matrix coefficient of a finite-dimensional continuous
representation. The carrier is pinned to a standard model `EuclideanSpace 𝕜 (Fin n)`, which by
`TauCeti.isRepresentative_matrixCoeff` is no restriction. -/
def IsRepresentative (f : C(G, 𝕜)) : Prop :=
  ∃ (n : ℕ) (π : ContRepresentation 𝕜 G (EuclideanSpace 𝕜 (Fin n))) (hπ : Continuous π)
    (v w : EuclideanSpace 𝕜 (Fin n)), f = matrixCoeff π hπ v w

/-- Being a representative function is exhibiting the function as a matrix coefficient of a
continuous representation on a standard model. -/
theorem isRepresentative_iff {f : C(G, 𝕜)} :
    IsRepresentative f ↔ ∃ (n : ℕ) (π : ContRepresentation 𝕜 G (EuclideanSpace 𝕜 (Fin n)))
      (hπ : Continuous π) (v w : EuclideanSpace 𝕜 (Fin n)), f = matrixCoeff π hπ v w :=
  (Iff.rfl)

variable (𝕜 G) in
/-- **The representative ring `𝓡(G)`**, as a submodule of `C(G, 𝕜)`: the span of the matrix
coefficients of the finite-dimensional continuous representations of `G`. -/
def representativeSubmodule : Submodule 𝕜 C(G, 𝕜) :=
  Submodule.span 𝕜 {f : C(G, 𝕜) | IsRepresentative f}

variable (𝕜 G) in
/-- The representative ring is the span of the representative functions. -/
theorem representativeSubmodule_eq_span :
    representativeSubmodule 𝕜 G = Submodule.span 𝕜 {f : C(G, 𝕜) | IsRepresentative f} :=
  (rfl)

/-- A representative function lies in the representative ring. -/
theorem mem_representativeSubmodule_of_isRepresentative {f : C(G, 𝕜)} (hf : IsRepresentative f) :
    f ∈ representativeSubmodule 𝕜 G :=
  Submodule.subset_span hf

end Defs

section Membership

variable {𝕜 G V : Type*} [RCLike 𝕜] [Monoid G] [TopologicalSpace G]
  [NormedAddCommGroup V] [InnerProductSpace 𝕜 V] [FiniteDimensional 𝕜 V]

/-- **Every matrix coefficient is representative.** A matrix coefficient of a continuous
representation on an arbitrary finite-dimensional inner product space is a representative function:
transporting the representation along `(stdOrthonormalBasis 𝕜 V).repr` puts it on a standard model
without changing its matrix coefficients. -/
theorem isRepresentative_matrixCoeff (π : ContRepresentation 𝕜 G V)
    (hπ : Continuous π) (v w : V) :
    IsRepresentative (matrixCoeff π hπ v w) :=
  ⟨Module.finrank 𝕜 V,
    ContRepresentation.congr (stdOrthonormalBasis 𝕜 V).repr.toContinuousLinearEquiv π,
    continuous_congr _ hπ, _, _,
    (matrixCoeff_congr (stdOrthonormalBasis 𝕜 V).repr hπ v w).symm⟩

/-- Every matrix coefficient of a finite-dimensional continuous representation lies in `𝓡(G)`. -/
theorem matrixCoeff_mem_representativeSubmodule (π : ContRepresentation 𝕜 G V)
    (hπ : Continuous π) (v w : V) :
    matrixCoeff π hπ v w ∈ representativeSubmodule 𝕜 G :=
  mem_representativeSubmodule_of_isRepresentative (isRepresentative_matrixCoeff π hπ v w)

end Membership

section Algebra

variable {𝕜 G : Type*} [RCLike 𝕜] [Monoid G] [TopologicalSpace G]

variable (𝕜 G) in
/-- **The constants are representative.** The constant function `1` is the matrix coefficient of the
trivial one-dimensional representation at the unit vector `1 : 𝕜`. -/
theorem isRepresentative_one : IsRepresentative (1 : C(G, 𝕜)) := by
  have h : (1 : C(G, 𝕜)) =
      matrixCoeff (ContRepresentation.trivial 𝕜 G 𝕜) continuous_const (1 : 𝕜) (1 : 𝕜) := by
    rw [matrixCoeff_trivial]
    ext g
    simp
  rw [h]
  exact isRepresentative_matrixCoeff _ _ _ _

variable (𝕜 G) in
/-- **The zero function is representative.** It is the matrix coefficient of the trivial
one-dimensional representation at the zero vector. -/
theorem isRepresentative_zero : IsRepresentative (0 : C(G, 𝕜)) := by
  simpa only [matrixCoeff_zero_left (ContRepresentation.trivial 𝕜 G 𝕜) continuous_const] using
    isRepresentative_matrixCoeff (ContRepresentation.trivial 𝕜 G 𝕜) continuous_const
      (0 : 𝕜) (0 : 𝕜)

variable (𝕜 G) in
/-- The constant function `1` lies in `𝓡(G)`. -/
theorem one_mem_representativeSubmodule : (1 : C(G, 𝕜)) ∈ representativeSubmodule 𝕜 G :=
  mem_representativeSubmodule_of_isRepresentative (isRepresentative_one 𝕜 G)

/-- **A product of representative functions is representative**: the product of a matrix coefficient
of `π` and one of `ρ` is a matrix coefficient of `π ⊗ ρ`. -/
theorem IsRepresentative.mul {a b : C(G, 𝕜)} (ha : IsRepresentative a)
    (hb : IsRepresentative b) : IsRepresentative (a * b) := by
  obtain ⟨n, π, hπ, v, w, rfl⟩ := ha
  obtain ⟨m, ρ, hρ, v', w', rfl⟩ := hb
  rw [← matrixCoeff_tprod π ρ hπ hρ v w v' w']
  exact isRepresentative_matrixCoeff _ _ _ _

/-- **The conjugate of a representative function is representative**: the conjugate of a matrix
coefficient of `π` is a matrix coefficient of the conjugate of `π`. -/
theorem IsRepresentative.star {a : C(G, 𝕜)} (ha : IsRepresentative a) :
    IsRepresentative (star a) := by
  obtain ⟨n, π, hπ, v, w, rfl⟩ := ha
  rw [star_matrixCoeff_eq_matrixCoeff_conjugate (EuclideanSpace.basisFun (Fin n) 𝕜) π hπ v w]
  exact isRepresentative_matrixCoeff _ _ _ _

/-- **`𝓡(G)` is closed under multiplication.** -/
theorem mul_mem_representativeSubmodule {a b : C(G, 𝕜)} (ha : a ∈ representativeSubmodule 𝕜 G)
    (hb : b ∈ representativeSubmodule 𝕜 G) : a * b ∈ representativeSubmodule 𝕜 G := by
  induction ha, hb using Submodule.span_induction₂ with
  | mem_mem x y hx hy => exact mem_representativeSubmodule_of_isRepresentative (hx.mul hy)
  | zero_left y _ => simp
  | zero_right x _ => simp
  | add_left x y z _ _ _ ihx ihy => rw [add_mul]; exact add_mem ihx ihy
  | add_right x y z _ _ _ ihy ihz => rw [mul_add]; exact add_mem ihy ihz
  | smul_left c x y _ _ ih => rw [smul_mul_assoc]; exact Submodule.smul_mem _ c ih
  | smul_right c x y _ _ ih => rw [mul_smul_comm]; exact Submodule.smul_mem _ c ih

/-- **`𝓡(G)` is closed under the involution of `C(G, 𝕜)`.** -/
theorem star_mem_representativeSubmodule {a : C(G, 𝕜)} (ha : a ∈ representativeSubmodule 𝕜 G) :
    star a ∈ representativeSubmodule 𝕜 G := by
  induction ha using Submodule.span_induction with
  | mem x hx => exact mem_representativeSubmodule_of_isRepresentative hx.star
  | zero => simp
  | add x y _ _ ihx ihy => rw [star_add]; exact add_mem ihx ihy
  | smul c x _ ih => rw [star_smul]; exact Submodule.smul_mem _ _ ih

variable (𝕜 G) in
/-- **The representative ring as a `*`-subalgebra of `C(G, 𝕜)`.** The span of the matrix
coefficients of the finite-dimensional continuous representations of `G` contains the constants,
and is closed under multiplication and under conjugation. -/
def representativeStarSubalgebra : StarSubalgebra 𝕜 C(G, 𝕜) where
  carrier := representativeSubmodule 𝕜 G
  mul_mem' := mul_mem_representativeSubmodule
  add_mem' := add_mem
  zero_mem' := zero_mem _
  algebraMap_mem' r := by
    rw [Algebra.algebraMap_eq_smul_one]
    exact Submodule.smul_mem _ r (one_mem_representativeSubmodule 𝕜 G)
  star_mem' := star_mem_representativeSubmodule

/-- Membership in the representative `*`-subalgebra is membership in its underlying span. -/
@[simp]
theorem mem_representativeStarSubalgebra_iff {f : C(G, 𝕜)} :
    f ∈ representativeStarSubalgebra 𝕜 G ↔ f ∈ representativeSubmodule 𝕜 G :=
  Iff.rfl

end Algebra

namespace ContRepresentation

variable {𝕜 G V : Type*} [RCLike 𝕜] [Monoid G] [TopologicalSpace G]
  [NormedAddCommGroup V] [InnerProductSpace 𝕜 V] [FiniteDimensional 𝕜 V]

/-- **The character of a finite-dimensional continuous representation lies in `𝓡(G)`.** Its
conjugate is the sum of the diagonal matrix coefficients, and `𝓡(G)` is closed under
conjugation. -/
theorem character_mem_representativeSubmodule (π : ContRepresentation 𝕜 G V) (hπ : Continuous π) :
    character π hπ ∈ representativeSubmodule 𝕜 G := by
  have h : character π hπ =
      star (∑ i, matrixCoeff π hπ (stdOrthonormalBasis 𝕜 V i) (stdOrthonormalBasis 𝕜 V i)) := by
    rw [← star_character π hπ (stdOrthonormalBasis 𝕜 V), star_star]
  rw [h]
  exact star_mem_representativeSubmodule
    (Submodule.sum_mem _ fun i _ ↦ matrixCoeff_mem_representativeSubmodule π hπ _ _)

end ContRepresentation

end TauCeti
