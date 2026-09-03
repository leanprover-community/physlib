/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import PhyslibAlpha.QuantumMechanics.RepresentationTheory.TauCetiPort.Analysis.InnerProductSpace.Conjugation
public import PhyslibAlpha.QuantumMechanics.RepresentationTheory.TauCetiPort.Continuous.MatrixCoefficient

/-!
# The conjugate of a continuous representation

Complex conjugation of the matrix entries of a representation gives another representation, the
**conjugate** (equivalently, for a unitary representation, the contragredient). It is what the span
of the matrix coefficients needs in order to be closed under the involution of `C(G, 𝕜)`:
conjugating a matrix coefficient of `π` produces a matrix coefficient of the conjugate of `π`, not
of `π` itself.

There is no canonical conjugation on an abstract inner product space, so the construction takes an
orthonormal basis `e` as data and conjugates each action operator by the coordinatewise conjugation
`TauCeti.conjugation` of that basis, using `TauCeti.conjCLM`. Different bases give conjugates that
are isomorphic representations, so the choice is immaterial for the uses downstream, which only
need one conjugate to exist.

## Main definitions

* `TauCeti.ContRepresentation.conjugate`: the conjugate representation.

## Main statements

* `TauCeti.ContRepresentation.continuous_conjugate` and
  `TauCeti.ContRepresentation.IsUnitary.conjugate`: the conjugate of a continuous representation is
  continuous, and of a unitary one is unitary.
* `TauCeti.ContRepresentation.conjugate_conjugate`: conjugating twice returns the original
  representation.
* `TauCeti.ContRepresentation.star_matrixCoeff_eq_matrixCoeff_conjugate`: the conjugate of a matrix
  coefficient of `π` is a matrix coefficient of the conjugate of `π`.

This supplies the conjugation half of the representative-ring item of Layer 3 of the
[compact-groups roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/CompactGroups/README.md),
whose statement of it is "closed under conjugation (via the contragredient)". The mathematical
development follows Daniel Bump, *Lie Groups*, second edition, Chapter 2.
-/

public section

open scoped InnerProductSpace

namespace TauCeti

namespace ContRepresentation

variable {𝕜 ι G V : Type*} [RCLike 𝕜] [Fintype ι] [Monoid G] [TopologicalSpace G]
  [NormedAddCommGroup V] [InnerProductSpace 𝕜 V] (e : OrthonormalBasis ι 𝕜 V)

/-- **The conjugate of a continuous representation** with respect to an orthonormal basis: the
action operators are conjugated entrywise in that basis. -/
noncomputable def conjugate (π : ContRepresentation 𝕜 G V) : ContRepresentation 𝕜 G V :=
  .ofMonoidHom
    { toFun g := conjCLM e (π g)
      map_one' := by simp
      map_mul' g h := by rw [map_mul, conjCLM_mul] }

variable (π : ContRepresentation 𝕜 G V)

omit [TopologicalSpace G] in
/-- The action operators of the conjugate representation. -/
@[simp]
theorem conjugate_apply (g : G) : conjugate e π g = conjCLM e (π g) :=
  (rfl)

omit [TopologicalSpace G] in
/-- **Conjugating twice returns the original representation**, because conjugation of operators is
an involution. -/
@[simp]
theorem conjugate_conjugate : conjugate e (conjugate e π) = π :=
  DFunLike.ext _ _ fun g ↦ by simp

/-- The conjugate of a continuous representation has a continuous operator-valued action. -/
theorem continuous_conjugate (hπ : Continuous π) : Continuous (conjugate e π) :=
  (lipschitzWith_one_conjCLM e).continuous.comp hπ

omit [TopologicalSpace G] in
/-- The conjugate of a unitary representation is unitary. -/
theorem IsUnitary.conjugate {π : ContRepresentation 𝕜 G V} (hπ : IsUnitary π) :
    IsUnitary (ContRepresentation.conjugate e π) :=
  (isUnitary_iff_norm_map _).mpr fun g x ↦ by simp [hπ.norm_map]

/-- **The conjugate of a matrix coefficient is a matrix coefficient of the conjugate
representation**, at the conjugated vectors. This is the identity that makes the span of all matrix
coefficients stable under the involution of `C(G, 𝕜)`. -/
theorem star_matrixCoeff_eq_matrixCoeff_conjugate (hπ : Continuous π) (v w : V) :
    star (matrixCoeff π hπ v w) =
      matrixCoeff (conjugate e π) (continuous_conjugate e π hπ)
        (conjugation e v) (conjugation e w) := by
  ext g
  simp [inner_conjugation_conjugation, RCLike.star_def]

end ContRepresentation

end TauCeti
