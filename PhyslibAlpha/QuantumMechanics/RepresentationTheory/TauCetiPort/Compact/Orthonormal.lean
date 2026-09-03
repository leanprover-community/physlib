/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import PhyslibAlpha.QuantumMechanics.RepresentationTheory.TauCetiPort.Compact.Character.Basic

/-!
# The orthonormal systems cut out by Schur orthogonality

Fix a family `π i` of pairwise inequivalent finite-dimensional irreducible unitary representations
of a compact group `G`, one for each index `i`. This file assembles the two orthogonality relations
of `TauCeti/RepresentationTheory/Compact/SchurOrthogonality.lean` and
`TauCeti/RepresentationTheory/Compact/Character/Basic.lean` into `Orthonormal` families in `L²(G)`:

* the **normalized matrix coefficients** `√(dim V_i) • (π i)_{ab}`, indexed by
  `Σ i, Fin (dim V_i) × Fin (dim V_i)`;
* the **characters** `χ_(π i)`, indexed by `i`.

The family is arbitrary apart from being pairwise inequivalent, so the first is a subsystem of the
system that the Peter-Weyl theorem proves complete: it is the whole of it only when the family runs
over one representative of every irreducible equivalence class. The second lies in the central
subspace of `L²(G)`.

## Main statements

* `TauCeti.ContRepresentation.orthonormal_matrixCoeffLp`: the normalized matrix coefficients of a
  family of pairwise inequivalent irreducible unitary representations form an orthonormal system
  in `L²(G)`.
* `TauCeti.ContRepresentation.orthonormal_characterLp`: the characters of such a family form an
  orthonormal system in `L²(G)`.

## Implementation notes

Inequivalence is the hypothesis `Pairwise fun i j ↦ IsEmpty (ContRepresentation.Equiv (π i) (π j))`.
Nothing here selects the family: "one representative per equivalence class" is chosen data,
supplied by the caller as `π` together with the orthonormal bases `e`, exactly as the Peter-Weyl
basis of Layer 5 will need it.

Both systems live in the *same* `L²(G)`, so the index of the matrix-coefficient system is a sigma
type over the family rather than a product: different `i` contribute different numbers of
coefficients.

The normalizing scalar is `√(n i)`, where `n i` is the cardinality of the index type of the chosen
basis of `V i` and so equals `Module.finrank 𝕜 (V i)` by `Module.finrank_eq_card_basis`. Taking the
basis index as data rather than reading it off `Module.finrank` is what lets the caller keep
whatever indexing the representation came with.

This is the orthonormal-system item of Layer 4, together with the system half of the
character-orthonormality item of Layer 6, of the
[compact-groups roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/CompactGroups/README.md).
The completeness of the first system is the Layer 5 summit, proved in
`TauCeti/RepresentationTheory/Compact/PeterWeyl.lean` for a family that also exhausts the
irreducibles; the completeness of the second (class-function completeness) is proved in
`TauCeti/RepresentationTheory/Compact/Character/Basis.lean`. The mathematical development follows
Daniel Bump, *Lie Groups*, second edition, Chapter 2.
-/

public section

open MeasureTheory
open scoped InnerProductSpace

namespace TauCeti

namespace ContRepresentation

section OrthonormalSystem

variable {𝕜 G ι : Type*} {V : ι → Type*} [RCLike 𝕜] [IsAlgClosed 𝕜]
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [MeasurableSpace G] [BorelSpace G]
  [∀ i, NormedAddCommGroup (V i)] [∀ i, InnerProductSpace 𝕜 (V i)]
  [∀ i, NormedSpace ℝ (V i)] [∀ i, SMulCommClass ℝ 𝕜 (V i)]
  [∀ i, FiniteDimensional 𝕜 (V i)]

local instance instCompleteSpaceOrthonormalSystem (i : ι) : CompleteSpace (V i) :=
  FiniteDimensional.complete 𝕜 (V i)

variable (π : ∀ i, ContRepresentation 𝕜 G (V i)) (hπ : ∀ i, Continuous (π i))

/-- **The normalized matrix coefficients are orthonormal.** For a family `π` of pairwise
inequivalent finite-dimensional irreducible unitary representations of a compact group, with a
chosen orthonormal basis `e i` of each carrier, the functions
`√(dim V_i) • ⟪(π i) · (e i a), e i b⟫` form an orthonormal system in `L²(G)` indexed by
`Σ i, Fin (n i) × Fin (n i)`.

Within a single `i` this is the first Schur orthogonality relation, whose value `(n i)⁻¹` on the
diagonal is exactly what the normalization `√(n i)` cancels; across distinct `i` it is the second
relation, whose hypothesis Schur's lemma supplies from inequivalence.

The family is not asked to be exhaustive, so this is in general a subsystem of the system that the
Peter-Weyl theorem completes to a Hilbert basis of `L²(G)`; it is that whole system exactly when `π`
contains a representative of every irreducible equivalence class. -/
theorem orthonormal_matrixCoeffLp {n : ι → ℕ} (hunitary : ∀ i, IsUnitary (π i))
    (hirr : ∀ i, Representation.IsIrreducible (π i).toRepresentation)
    (hne : Pairwise fun i j ↦ IsEmpty (_root_.ContRepresentation.Equiv (π i) (π j)))
    (e : ∀ i, OrthonormalBasis (Fin (n i)) 𝕜 (V i)) :
    Orthonormal 𝕜 fun x : Σ i, Fin (n i) × Fin (n i) ↦
      (Real.sqrt (n x.1) : 𝕜) •
        matrixCoeffLp (π x.1) (hπ x.1) (e x.1 x.2.1) (e x.1 x.2.2) := by
  classical
  rw [orthonormal_iff_ite]
  rintro ⟨i, a, b⟩ ⟨j, c, d⟩
  rw [inner_smul_left, inner_smul_right, RCLike.conj_ofReal]
  rcases eq_or_ne i j with rfl | hij
  · -- `Fin (n i)` is inhabited by `a`, so the dimension is positive and the normalization is legal.
    have hn : (0 : ℝ) < n i := by
      exact_mod_cast Fin.pos a
    have hsq : (Real.sqrt (n i) : 𝕜) * (Real.sqrt (n i) : 𝕜) = (n i : 𝕜) := by
      rw [← RCLike.ofReal_mul, Real.mul_self_sqrt hn.le, RCLike.ofReal_natCast]
    rw [schur_orthogonality_basis (π i) (hπ i) (hunitary i) (hirr i) (e i) b a d c,
      ← mul_assoc, ← mul_assoc, hsq]
    have hn' : (n i : 𝕜) ≠ 0 := by
      exact_mod_cast hn.ne'
    split_ifs <;> simp_all [Sigma.ext_iff, Prod.ext_iff]
  · rw [schur_orthogonality (π i) (hπ i) (π j) (hπ j) (hunitary j) (hirr i) (hirr j) (hne hij)]
    simp [Sigma.ext_iff, hij]

/-- **The irreducible characters are orthonormal.** The characters of a family of pairwise
inequivalent finite-dimensional irreducible unitary representations of a compact group form an
orthonormal system in `L²(G)`.

This is the system form of the two character orthogonality relations: normalization is the first,
and orthogonality across the family is the second, whose intertwiner hypothesis Schur's lemma
supplies from inequivalence. For a finite group it is the statement that the irreducible characters
are an orthonormal set of class functions. -/
theorem orthonormal_characterLp (hunitary : ∀ i, IsUnitary (π i))
    (hirr : ∀ i, Representation.IsIrreducible (π i).toRepresentation)
    (hne : Pairwise fun i j ↦ IsEmpty (_root_.ContRepresentation.Equiv (π i) (π j))) :
    Orthonormal 𝕜 fun i ↦ characterLp (π i) (hπ i) := by
  classical
  rw [orthonormal_iff_ite]
  intro i j
  rcases eq_or_ne i j with rfl | hij
  · simpa using character_orthonormal_self (π i) (hπ i) (hunitary i) (hirr i)
  · -- The second character orthogonality asks for the intertwiners `π j → π i`, not `π i → π j`,
    -- so it is the pair `(j, i)` that Schur's lemma is applied to.
    rw [character_orthonormal_distinct (π i) (hπ i) (π j) (hπ j) (hunitary i)
      fun f ↦ by simp [eq_zero_of_isEmpty_equiv (hirr j) (hirr i) (hne hij.symm) f]]
    simp [hij]

end OrthonormalSystem

end ContRepresentation

end TauCeti
