/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import PhyslibAlpha.QuantumMechanics.RepresentationTheory.TauCetiPort.Analysis.Normed.Module.Trace
public import PhyslibAlpha.QuantumMechanics.RepresentationTheory.TauCetiPort.Continuous.MatrixCoefficient
public import Mathlib.RepresentationTheory.Character
public import Mathlib.Analysis.InnerProductSpace.Trace

/-!
# Characters of continuous representations

The character of a finite-dimensional representation is the function `g ↦ trace (π g)`. Mathlib
builds it for a bare `Representation` and proves its algebraic identities; this file packages it
as an element of `C(G, 𝕜)` for a representation with continuous operator-valued action, and links
it to the matrix coefficients of `TauCeti/RepresentationTheory/Continuous/MatrixCoefficient.lean`.

## Main definitions

* `TauCeti.ContRepresentation.character`: the character `g ↦ trace (π g)` as an element of
  `C(G, 𝕜)`.

## Main statements

* `TauCeti.ContRepresentation.character_one`: the character at the identity is the dimension.
* `TauCeti.ContRepresentation.character_conj`: the character is a class function.
* `TauCeti.ContRepresentation.star_character`: the conjugate of the character is the sum of the
  diagonal matrix coefficients `∑ i, ⟪π g eᵢ, eᵢ⟫` in an orthonormal basis. The conjugation is not
  decoration: Mathlib's inner product is conjugate linear in its *first* argument, so the diagonal
  matrix coefficient `matrixCoeff π hπ eᵢ eᵢ` is `⟪π g eᵢ, eᵢ⟫`, whereas the diagonal entry of the
  matrix of `π g` in that basis, which the trace sums, is `⟪eᵢ, π g eᵢ⟫`.
* `TauCeti.ContRepresentation.character_apply_inv`: the character of a unitary representation at an
  inverse is the conjugate of its value.
* `TauCeti.ContRepresentation.norm_character_apply_le`: a unitary character is bounded by the
  dimension.
* `ContRepresentation.continuous_character_mul_self`: the character read along the squaring map
  `g ↦ g * g` is continuous.

## Implementation notes

The underlying function is Mathlib's `Representation.character`, so the identities that are purely
algebraic — the value at `1`, invariance under conjugation, the behaviour under a product of group
elements — are restatements of `Representation.char_one`, `Representation.char_conj` and
`Representation.char_mul_comm` rather than new proofs. What this file adds is continuity, which
`Representation.character` cannot see, and the orthonormal-basis bridge to matrix coefficients.

Continuity of the trace is not automatic from continuity of `π` alone: it is continuity of the
functional `T ↦ trace T` on `V →L[𝕜] V`, which holds because that space is finite-dimensional over
the complete field `𝕜`. That functional is `TauCeti.traceCLM` of
`TauCeti/Analysis/Normed/Module/Trace.lean`, shared with
`TauCeti/RepresentationTheory/Compact/Intertwiner/Basic.lean`, which uses it to average a trace.

Only the trace is at stake in the sections without an inner product, so they ask no more of the
scalars than that functional does: `𝕜` is a complete nontrivially normed field there, and becomes
`RCLike` only where an orthonormal basis or unitarity enters.

This is the character definition of Layer 6 of the
[compact-groups roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/CompactGroups/README.md);
the `L²` theory and the orthogonality relations are in
`TauCeti/RepresentationTheory/Compact/Character/Basic.lean`. Nothing here needs a group, a measure,
or compactness, so it is stated over a topological monoid. The mathematical development follows
Daniel Bump, *Lie Groups*, second edition, Chapter 2.
-/

public section

open scoped InnerProductSpace

namespace TauCeti

namespace ContRepresentation

section Monoid

variable {𝕜 G V : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜] [Monoid G]
  [TopologicalSpace G] [NormedAddCommGroup V] [NormedSpace 𝕜 V] [FiniteDimensional 𝕜 V]

/-- **The character** `g ↦ trace (π g)` of a finite-dimensional representation with continuous
operator-valued action, as an element of `C(G, 𝕜)`.

The underlying function is Mathlib's `Representation.character`; only the continuity is new, and it
comes from `TauCeti.traceCLM`, the trace as a continuous linear functional. -/
noncomputable def character (π : ContRepresentation 𝕜 G V) (hπ : Continuous π) : C(G, 𝕜) where
  toFun := π.toRepresentation.character
  continuous_toFun := by
    have h : π.toRepresentation.character = fun g ↦ traceCLM 𝕜 V (π g) := by
      funext g
      rw [traceCLM_apply]
      rfl
    rw [h]
    exact (traceCLM 𝕜 V).continuous.comp hπ

variable (π : ContRepresentation 𝕜 G V) (hπ : Continuous π)

/-- The character of a continuous representation is Mathlib's character of the underlying
representation; every algebraic identity about the latter therefore applies verbatim. -/
theorem coe_character : ⇑(character π hπ) = π.toRepresentation.character :=
  (rfl)

/-- Evaluation of the character. -/
@[simp]
theorem character_apply (g : G) :
    character π hπ g = LinearMap.trace 𝕜 V (π g : V →ₗ[𝕜] V) :=
  (rfl)

/-- The character at the identity is the dimension of the representation. -/
theorem character_one : character π hπ 1 = (Module.finrank 𝕜 V : 𝕜) :=
  Representation.char_one π.toRepresentation

/-- The character is unchanged by transposing a product of group elements. -/
theorem character_mul_comm (g h : G) :
    character π hπ (h * g) = character π hπ (g * h) :=
  Representation.char_mul_comm π.toRepresentation g h

/-- The character of the trivial representation is the constant function at the dimension: every
action operator is the identity, whose trace is the dimension. The trivial action is constant, so
`continuous_const` is its continuity witness. -/
@[simp]
theorem character_trivial :
    character (ContRepresentation.trivial 𝕜 G V) continuous_const =
      ContinuousMap.const G (Module.finrank 𝕜 V : 𝕜) := by
  ext g
  have hid : ((ContRepresentation.trivial 𝕜 G V g : V →L[𝕜] V) : V →ₗ[𝕜] V) = LinearMap.id :=
    LinearMap.ext fun v ↦ ContRepresentation.trivial_apply (R := 𝕜) (G := G) (V := V) g v
  -- `character_apply` gets its arguments explicitly: `continuous_const` has the required type only
  -- after unfolding `trivial`, which the matching of `rw` does not do.
  rw [character_apply (ContRepresentation.trivial 𝕜 G V) continuous_const, hid,
    LinearMap.trace_id, ContinuousMap.const_apply]

/-- Restricting a representation along a continuous homomorphism precomposes its character. -/
@[simp]
theorem character_restrict {H : Type*} [Monoid H] [TopologicalSpace H] (φ : H →* G)
    (hφ : Continuous φ) :
    character (π.restrict φ) (hπ.comp hφ) = (character π hπ).comp ⟨φ, hφ⟩ := by
  ext h
  rw [character_apply, ContinuousMap.comp_apply, character_apply, ContinuousMap.coe_mk,
    ContRepresentation.restrict_apply]

end Monoid

section MonoidInner

variable {𝕜 G V : Type*} [RCLike 𝕜] [Monoid G] [TopologicalSpace G]
  [NormedAddCommGroup V] [InnerProductSpace 𝕜 V] [FiniteDimensional 𝕜 V]
variable (π : ContRepresentation 𝕜 G V) (hπ : Continuous π)

/-- The character read off an orthonormal basis: it is the sum of the diagonal entries
`⟪eᵢ, π g eᵢ⟫` of the matrix of `π g`. -/
theorem character_apply_eq_sum_inner {ι : Type*} [Fintype ι] (e : OrthonormalBasis ι 𝕜 V) (g : G) :
    character π hπ g = ∑ i, ⟪e i, π g (e i)⟫_𝕜 :=
  LinearMap.trace_eq_sum_inner _ e

/-- **The conjugate of the character is the sum of the diagonal matrix coefficients.** With
`matrixCoeff π hπ v w g = ⟪π g v, w⟫`, conjugate linear in `v`, the diagonal matrix coefficient
`πᵢᵢ(g) = ⟪π g eᵢ, eᵢ⟫` is the *conjugate* of the diagonal entry `⟪eᵢ, π g eᵢ⟫` summed by the
trace; the conjugation on the left is what records that. This is the identity through which the
Schur orthogonality relations compute inner products of characters. -/
theorem star_character {ι : Type*} [Fintype ι] (e : OrthonormalBasis ι 𝕜 V) :
    star (character π hπ) = ∑ i, matrixCoeff π hπ (e i) (e i) := by
  ext g
  rw [ContinuousMap.star_apply, character_apply_eq_sum_inner π hπ e g]
  simp [inner_conj_symm]

/-- The character of a unitary representation is bounded by the dimension: each of the `dim V`
diagonal entries `⟪eᵢ, π g eᵢ⟫` has modulus at most `‖eᵢ‖ * ‖π g eᵢ‖ = 1`. -/
theorem norm_character_apply_le (hunitary : IsUnitary π) (g : G) :
    ‖character π hπ g‖ ≤ Module.finrank 𝕜 V := by
  classical
  set e := stdOrthonormalBasis 𝕜 V
  calc ‖character π hπ g‖
      = ‖∑ i, ⟪e i, π g (e i)⟫_𝕜‖ := by rw [character_apply_eq_sum_inner π hπ e g]
    _ ≤ ∑ i, ‖⟪e i, π g (e i)⟫_𝕜‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Fin (Module.finrank 𝕜 V), (1 : ℝ) := by
        refine Finset.sum_le_sum fun i _ ↦ ?_
        calc ‖⟪e i, π g (e i)⟫_𝕜‖ ≤ ‖e i‖ * ‖π g (e i)‖ := norm_inner_le_norm _ _
          _ = 1 := by rw [hunitary.norm_map, e.orthonormal.1 i, mul_one]
    _ = Module.finrank 𝕜 V := by simp

end MonoidInner

section Group

variable {𝕜 G V : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜] [Group G]
  [TopologicalSpace G] [NormedAddCommGroup V] [NormedSpace 𝕜 V] [FiniteDimensional 𝕜 V]
variable (π : ContRepresentation 𝕜 G V) (hπ : Continuous π)

/-- **The character is a class function.** This is `Representation.char_conj` transported to the
continuous packaging. -/
theorem character_conj (g h : G) :
    character π hπ (h * g * h⁻¹) = character π hπ g :=
  Representation.char_conj π.toRepresentation g h

end Group

section GroupInner

variable {𝕜 G V : Type*} [RCLike 𝕜] [Group G] [TopologicalSpace G]
  [NormedAddCommGroup V] [InnerProductSpace 𝕜 V] [FiniteDimensional 𝕜 V]
variable (π : ContRepresentation 𝕜 G V) (hπ : Continuous π)

/-- The character of a **unitary** representation at an inverse is the conjugate of its value: the
action of `g⁻¹` is the adjoint of the action of `g`, and taking adjoints conjugates the diagonal
entries in an orthonormal basis. -/
theorem character_apply_inv (hunitary : IsUnitary π) (g : G) :
    character π hπ g⁻¹ = (starRingEnd 𝕜) (character π hπ g) := by
  set e := stdOrthonormalBasis 𝕜 V
  rw [character_apply_eq_sum_inner π hπ e, character_apply_eq_sum_inner π hπ e, map_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [hunitary.inner_map_right g⁻¹ (e i) (e i), inv_inv, inner_conj_symm]

end GroupInner

end ContRepresentation

end TauCeti

open TauCeti.ContRepresentation

namespace ContRepresentation

/-! ### The character along the squaring map

The lemma below is declared in the **root** `ContRepresentation` namespace, unlike the rest of this
file, so that `π.continuous_character_mul_self hπ` elaborates: `ContRepresentation` is Mathlib's
type, and `scripts/lint-dot-notation.py` asks that new declarations about it not recreate its
namespace inside `TauCeti`. -/

variable {𝕜 G V : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜] [Monoid G]
  [TopologicalSpace G] [ContinuousMul G] [NormedAddCommGroup V] [NormedSpace 𝕜 V]
  [FiniteDimensional 𝕜 V]

/-- The character read along the squaring map `g ↦ g * g` is continuous. -/
theorem continuous_character_mul_self (π : ContRepresentation 𝕜 G V) (hπ : Continuous π) :
    Continuous fun g : G ↦ character π hπ (g * g) :=
  (character π hπ).continuous.comp (continuous_id.mul continuous_id)

end ContRepresentation
