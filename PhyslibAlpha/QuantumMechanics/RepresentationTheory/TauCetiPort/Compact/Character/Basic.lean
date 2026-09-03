/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import PhyslibAlpha.QuantumMechanics.RepresentationTheory.TauCetiPort.Compact.SchurOrthogonality
public import PhyslibAlpha.QuantumMechanics.RepresentationTheory.TauCetiPort.Continuous.Character
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import PhyslibAlpha.QuantumMechanics.RepresentationTheory.TauCetiPort.Irreducible

/-!
# Orthonormality of the characters of a compact group

The character of a finite-dimensional continuous representation of a compact group is a continuous
function, hence square integrable for normalized Haar measure. This file records its image in
`L²(G)` and proves the two orthogonality relations that make the irreducible unitary characters an
orthonormal system: the normalization `∫ |χ_π|² = 1` for an irreducible unitary `π`, and the
orthogonality `∫ conj χ_π · χ_ρ = 0` for a pair `π`, `ρ` admitting no nonzero continuous
intertwiner `ρ → π`. Schur's lemma is what supplies that hypothesis for a pair of inequivalent
irreducibles; deriving it is not done here.

Both statements are read off the Schur orthogonality relations of
`TauCeti/RepresentationTheory/Compact/SchurOrthogonality.lean` and
`TauCeti/RepresentationTheory/Compact/Intertwiner/Basic.lean`: a character is, up to conjugation,
the sum of the diagonal matrix coefficients in an orthonormal basis, so an inner product of
characters is a double sum of inner products of matrix coefficients. The `[Finite G]` shadow of
these two results is Mathlib's `Representation.char_orthonormal`, whose finite average is replaced
here by the Haar integral.

## Main definitions

* `TauCeti.ContRepresentation.characterLp`: the character as an element of `Lp 𝕜 2 (haarProb G)`.

## Main statements

* `TauCeti.ContRepresentation.inner_characterLp_eq_sum`: the `L²` inner product of two characters
  is the double sum of the inner products of the diagonal matrix coefficients.
* `TauCeti.ContRepresentation.character_orthonormal_self`: **first character orthogonality.** The
  character of a finite-dimensional irreducible unitary representation is a unit vector of `L²(G)`.
* `TauCeti.ContRepresentation.character_orthonormal_distinct`: **second character orthogonality.**
  The characters of two representations with no nonzero intertwiner between them are
  `L²`-orthogonal.

## Implementation notes

The diagonal matrix coefficient `matrixCoeff π hπ eᵢ eᵢ` is `g ↦ ⟪π g eᵢ, eᵢ⟫`, while the diagonal
entry of the matrix of `π g` that the trace sums is `⟪eᵢ, π g eᵢ⟫`; in Mathlib's convention, where
the inner product is conjugate linear in its first argument, these are conjugate to one another.
So a character is the conjugate, not the sum, of its diagonal matrix coefficients
(`TauCeti.ContRepresentation.star_character`), and `inner_characterLp_eq_sum` carries that
conjugation as a transposition of the two arguments of the inner product. That transposition is
also why `character_orthonormal_distinct` asks for the vanishing of the intertwiners `ρ → π` rather
than `π → ρ`, and asks unitarity of `π` rather than of `ρ`: those are exactly the hypotheses of
`TauCeti.ContRepresentation.schur_orthogonality_distinct` at the transposed pair. The reverse
orientation is the conjugate statement, since `⟪χ_π, χ_ρ⟫ = conj ⟪χ_ρ, χ_π⟫`.

Packaging the character in `L²` asks nothing of `V` beyond the finite-dimensional normed structure
that the character itself needs, so `characterLp` is stated there; `V` carries an inner product only
from `inner_characterLp_eq_sum` on, where an orthonormal basis enters. The scalars stay `RCLike`
even for that packaging: `ContinuousMap.toLp` needs `SecondCountableTopologyEither G 𝕜`, which a
general complete nontrivially normed field does not supply.

This is the first half of Layer 6 of the
[compact-groups roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/CompactGroups/README.md);
its remaining item, that the characters span the central subspace of `L²(G)`, needs the Peter-Weyl
theorem of Layer 5 and is proved in `TauCeti/RepresentationTheory/Compact/Character/Basis.lean`.
The mathematical development follows Daniel Bump, *Lie Groups*, second edition, Chapter 2.
-/

public section

open MeasureTheory
open scoped InnerProductSpace

namespace TauCeti

namespace ContRepresentation

section CharacterLp

variable {𝕜 G V : Type*} [RCLike 𝕜] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
  [NormedAddCommGroup V] [NormedSpace 𝕜 V] [FiniteDimensional 𝕜 V]

/-- The character of a finite-dimensional continuous representation as an element of `L²(G)` for
normalized Haar measure.

The character is continuous and `G` is compact, so `ContinuousMap.toLp` applies; the normalization
of Haar measure to a probability measure is what makes `‖characterLp π hπ‖ = 1` the right form of
orthonormality. -/
noncomputable def characterLp (π : ContRepresentation 𝕜 G V) (hπ : Continuous π) :
    Lp 𝕜 2 (haarProb G) :=
  ContinuousMap.toLp 2 (haarProb G) 𝕜 (character π hπ)

variable (π : ContRepresentation 𝕜 G V) (hπ : Continuous π)

theorem characterLp_def :
    characterLp π hπ = ContinuousMap.toLp 2 (haarProb G) 𝕜 (character π hπ) :=
  (rfl)

/-- A character in `L²` is represented, almost everywhere, by the trace of the action. -/
theorem coeFn_characterLp :
    characterLp π hπ =ᵐ[haarProb G] fun g ↦ LinearMap.trace 𝕜 V (π g : V →ₗ[𝕜] V) := by
  filter_upwards [ContinuousMap.coeFn_toLp (𝕜 := 𝕜) (p := 2) (haarProb G)
    (character π hπ)] with g hg
  rw [characterLp_def, hg, character_apply]

end CharacterLp

section CompactGroup

variable {𝕜 G V W : Type*} [RCLike 𝕜] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
  [NormedAddCommGroup V] [InnerProductSpace 𝕜 V] [FiniteDimensional 𝕜 V]
  [NormedAddCommGroup W] [InnerProductSpace 𝕜 W] [FiniteDimensional 𝕜 W]

variable (π : ContRepresentation 𝕜 G V) (hπ : Continuous π)

/-- Conjugating both arguments of the `L²` inner product of two continuous functions conjugates
the result: passing to `L²` is linear, and conjugation commutes with the Haar integral. -/
private theorem inner_toLp_star (F H : C(G, 𝕜)) :
    ⟪ContinuousMap.toLp 2 (haarProb G) 𝕜 (star F),
        ContinuousMap.toLp 2 (haarProb G) 𝕜 (star H)⟫_𝕜 =
      (starRingEnd 𝕜) ⟪ContinuousMap.toLp 2 (haarProb G) 𝕜 F,
        ContinuousMap.toLp 2 (haarProb G) 𝕜 H⟫_𝕜 := by
  rw [ContinuousMap.inner_toLp, ContinuousMap.inner_toLp, ← integral_conj]
  refine integral_congr_ae (Filter.Eventually.of_forall fun g ↦ ?_)
  -- `integral_congr_ae` leaves the two integrands applied but unreduced.
  beta_reduce
  simp

/-- **The `L²` inner product of two characters is a double sum of inner products of diagonal matrix
coefficients.** The two arguments are transposed on the right-hand side because a character is the
*conjugate* of the sum of its diagonal matrix coefficients
(`TauCeti.ContRepresentation.star_character`).

This is the identity through which both orthogonality relations below are read off the Schur
orthogonality relations for matrix coefficients. -/
theorem inner_characterLp_eq_sum (ρ : ContRepresentation 𝕜 G W) (hρ : Continuous ρ)
    {ι κ : Type*} [Fintype ι] [Fintype κ] (e : OrthonormalBasis ι 𝕜 V)
    (f : OrthonormalBasis κ 𝕜 W) :
    ⟪characterLp π hπ, characterLp ρ hρ⟫_𝕜 =
      ∑ i, ∑ k, ⟪matrixCoeffLp ρ hρ (f k) (f k), matrixCoeffLp π hπ (e i) (e i)⟫_𝕜 := by
  have hstar := inner_toLp_star (character π hπ) (character ρ hρ)
  rw [star_character π hπ e, star_character ρ hρ f, map_sum, map_sum] at hstar
  simp only [← matrixCoeffLp_def, ← characterLp_def, sum_inner, inner_sum] at hstar
  calc ⟪characterLp π hπ, characterLp ρ hρ⟫_𝕜
      = (starRingEnd 𝕜) ((starRingEnd 𝕜) ⟪characterLp π hπ, characterLp ρ hρ⟫_𝕜) := by
        simp
    _ = (starRingEnd 𝕜)
          (∑ k, ∑ i, ⟪matrixCoeffLp π hπ (e i) (e i), matrixCoeffLp ρ hρ (f k) (f k)⟫_𝕜) := by
        rw [hstar]
    _ = ∑ i, ∑ k, ⟪matrixCoeffLp ρ hρ (f k) (f k), matrixCoeffLp π hπ (e i) (e i)⟫_𝕜 := by
        simp only [map_sum, inner_conj_symm]
        exact Finset.sum_comm

end CompactGroup

section Orthogonality

variable {𝕜 G V W : Type*} [RCLike 𝕜] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
  [NormedAddCommGroup V] [InnerProductSpace 𝕜 V] [NormedSpace ℝ V] [SMulCommClass ℝ 𝕜 V]
  [FiniteDimensional 𝕜 V]
  [NormedAddCommGroup W] [InnerProductSpace 𝕜 W] [NormedSpace ℝ W] [SMulCommClass ℝ 𝕜 W]
  [FiniteDimensional 𝕜 W]

local instance instCompleteSpaceCharacterDomain : CompleteSpace V :=
  FiniteDimensional.complete 𝕜 V

local instance instCompleteSpaceCharacterCodomain : CompleteSpace W :=
  FiniteDimensional.complete 𝕜 W

variable (π : ContRepresentation 𝕜 G V) (hπ : Continuous π)

/-- **First character orthogonality.** The character of a finite-dimensional irreducible unitary
representation of a compact group has `L²` inner product `1` with itself.

Summing the first Schur orthogonality relation over the diagonal collapses the `d²` terms of
`inner_characterLp_eq_sum` to the `d` terms `d⁻¹`, whose sum is `1`. The `[Finite G]` shadow of this
statement is the diagonal half of Mathlib's `Representation.char_orthonormal`. -/
theorem character_orthonormal_self [IsAlgClosed 𝕜] (hunitary : IsUnitary π)
    (hirr : Representation.IsIrreducible π.toRepresentation) :
    ⟪characterLp π hπ, characterLp π hπ⟫_𝕜 = 1 := by
  classical
  let : Representation.IsIrreducible π.toRepresentation := hirr
  have hd : (Module.finrank 𝕜 V : 𝕜) ≠ 0 :=
    Representation.IsIrreducible.natCast_finrank_ne_zero hirr
  set e := stdOrthonormalBasis 𝕜 V
  -- Only the diagonal term of each inner sum survives, so each of the `d` rows contributes `d⁻¹`.
  have hrow : ∀ i, ∑ k, ⟪matrixCoeffLp π hπ (e k) (e k), matrixCoeffLp π hπ (e i) (e i)⟫_𝕜 =
      (Module.finrank 𝕜 V : 𝕜)⁻¹ := by
    intro i
    simp only [schur_orthogonality_basis π hπ hunitary hirr e]
    rw [Finset.sum_eq_single i (fun k _ hk ↦ by simp [hk]) (by simp)]
    simp
  rw [inner_characterLp_eq_sum π hπ π hπ e e, Finset.sum_congr rfl fun i _ ↦ hrow i,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_inv_cancel₀ hd]

omit [NormedSpace ℝ W] [SMulCommClass ℝ 𝕜 W] in
/-- **Second character orthogonality.** If there is no nonzero continuous intertwiner `ρ → π`, the
characters of `π` and `ρ` are orthogonal in `L²(G)`.

Schur's lemma is not invoked here; it is what supplies the hypothesis for a pair of inequivalent
irreducibles. Unitarity is asked of `π` alone, and the intertwiners are those `ρ → π`, because
`inner_characterLp_eq_sum` transposes the two arguments; see the module docstring. -/
theorem character_orthonormal_distinct (ρ : ContRepresentation 𝕜 G W) (hρ : Continuous ρ)
    (hunitary : IsUnitary π)
    (hdistinct : ∀ f : ContIntertwiningMap ρ π, f.toContinuousLinearMap = 0) :
    ⟪characterLp π hπ, characterLp ρ hρ⟫_𝕜 = 0 := by
  rw [inner_characterLp_eq_sum π hπ ρ hρ (stdOrthonormalBasis 𝕜 V) (stdOrthonormalBasis 𝕜 W)]
  simp [schur_orthogonality_distinct ρ hρ π hπ hunitary hdistinct]

/-- The character of a finite-dimensional irreducible unitary representation is a **unit vector**
of `L²(G)`. This is `character_orthonormal_self` in norm form; it is the normalization that makes
the irreducible characters an orthonormal system rather than merely an orthogonal one. -/
theorem norm_characterLp_eq_one [IsAlgClosed 𝕜] (hunitary : IsUnitary π)
    (hirr : Representation.IsIrreducible π.toRepresentation) :
    ‖characterLp π hπ‖ = 1 := by
  have h := character_orthonormal_self π hπ hunitary hirr
  rw [inner_self_eq_norm_sq_to_K] at h
  have h' : ‖characterLp π hπ‖ ^ 2 = 1 ^ 2 := by
    have h'' : ‖characterLp π hπ‖ ^ 2 = (1 : ℝ) := by exact_mod_cast h
    simpa using h''
  exact (sq_eq_sq₀ (norm_nonneg _) zero_le_one).1 h'

end Orthogonality

end ContRepresentation

end TauCeti
