/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
public import PhyslibAlpha.QuantumMechanics.RepresentationTheory.TauCetiPort.LinearAlgebra.Dimension.DirectSum
public import PhyslibAlpha.QuantumMechanics.RepresentationTheory.TauCetiPort.Continuous.InvariantComplement
public import PhyslibAlpha.QuantumMechanics.RepresentationTheory.TauCetiPort.Continuous.Transport
public import PhyslibAlpha.QuantumMechanics.RepresentationTheory.TauCetiPort.Irreducible

/-!
# The orthogonal decomposition of a unitary representation into irreducibles

A finite-dimensional unitary continuous representation of a group is an **orthogonal internal
direct sum of irreducible subrepresentations**. This is the geometric — as opposed to
lattice-theoretic — form of complete reducibility: not merely that every subrepresentation has a
complement, but that the whole space is cut into finitely many mutually orthogonal irreducible
blocks.

The proof is the classical descent. A nonzero subrepresentation of a finite-dimensional
representation contains an atom of the lattice of subrepresentations
(`TauCeti.Representation.exists_isAtom_le`), and an atom carries an irreducible representation
(`TauCeti.Representation.isIrreducible_toRepresentation_of_isAtom`). Unitarity enters exactly
once, to split off that atom orthogonally: the orthogonal complement of an invariant subspace is
again invariant (`TauCeti.ContRepresentation.IsUnitary.orthogonal_mem_invtSubmodule`), so the
remainder is a strictly smaller subrepresentation and the descent recurses on it.

No measure, no compactness, and no continuity of the representation are used: the argument runs on
a `ContRepresentation` only because that is where `TauCeti.ContRepresentation.IsUnitary` lives, and
the acting group may be arbitrary. For a compact group the unitarity hypothesis is what Weyl's
unitarian trick in `TauCeti.RepresentationTheory.Compact.Unitarizable` is there to supply. That
trick does not make `π` itself unitary — it conjugates it into a unitary representation — so the
decomposition is also recorded in the form that consumes such a conjugation, with the blocks
carried back to `π` along it.

## Main results

* `TauCeti.ContRepresentation.IsUnitary.exists_orthogonal_irreducible_decomposition`: complete
  reducibility in orthogonal internal form, with the dimension count that goes with it.
* `TauCeti.ContRepresentation.IsUnitary.exists_orthogonal_irreducible_decomposition_of_congr`: the
  same decomposition for a representation that is merely *conjugate* to a unitary one, its blocks
  carried back along the conjugating equivalence and orthogonal for the inner product that
  equivalence pulls back.

## Implementation notes

Invariant subspaces are carried as `Subrepresentation π.toRepresentation` rather than as bare
submodules with an invariance side condition: the lattice operations, the atoms, and the
`toRepresentation` needed to say "irreducible" are then all Mathlib's, and the translation to
submodules is `Subrepresentation.toSubmodule_le_toSubmodule` and its relatives.

Orthogonality of the resulting family is stated as Mathlib's `OrthogonalFamily`, which unfolds to
the pairwise vanishing of inner products between distinct blocks and is the form the orthogonal
projection API consumes; `DirectSum.IsInternal` is then read off it through
`OrthogonalFamily.isInternal_iff`.

## References

This is the target `exists_orthogonal_irreducible_decomposition` of Layer 2 of the
[compact-groups roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/CompactGroups/README.md).
The mathematical development follows Daniel Bump, *Lie Groups*, second edition, Chapter 2.
-/

public section

open scoped InnerProductSpace

namespace TauCeti

/-- Splitting the supremum of a family indexed by `Fin (n + 1)` off its first member. -/
private theorem iSup_fin_succ {α : Type*} [CompleteLattice α] {n : ℕ} (f : Fin (n + 1) → α) :
    ⨆ i, f i = f 0 ⊔ ⨆ i : Fin n, f i.succ := by
  refine le_antisymm (iSup_le fun i ↦ ?_)
    (sup_le (le_iSup f 0) (iSup_le fun j ↦ le_iSup f j.succ))
  rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨j, rfl⟩
  · exact le_sup_left
  · exact le_sup_of_le_right (le_iSup (fun j : Fin n ↦ f j.succ) j)

namespace ContRepresentation

namespace IsUnitary

section Unitary

variable {𝕜 G V : Type*} [RCLike 𝕜] [Group G] [NormedAddCommGroup V] [InnerProductSpace 𝕜 V]
  {π : ContRepresentation 𝕜 G V}

section FiniteDimensional

variable [FiniteDimensional 𝕜 V]

omit [FiniteDimensional 𝕜 V] in
/-- Inside a nonzero subrepresentation `σ` there is an atom `τ` whose orthogonal complement in
`σ` is a subrepresentation `ω` with `τ ⊔ ω = σ` and strictly smaller dimension. Only `σ` itself
need be finite-dimensional; the ambient space may not be. -/
private theorem exists_isAtom_sup_eq_and_lt (hπ : IsUnitary π)
    {σ : Subrepresentation π.toRepresentation} [FiniteDimensional 𝕜 σ.toSubmodule] (hσ : σ ≠ ⊥) :
    ∃ τ ω : Subrepresentation π.toRepresentation, IsAtom τ ∧ τ ⊔ ω = σ ∧
      ω.toSubmodule = τ.toSubmoduleᗮ ⊓ σ.toSubmodule ∧ ω.toSubmodule < σ.toSubmodule := by
  obtain ⟨τ, hτσ, hτ⟩ := Representation.exists_isAtom_le hσ
  -- The atom sits inside `σ`, so it inherits finite-dimensionality, hence a projection.
  have : FiniteDimensional 𝕜 τ.toSubmodule :=
    Submodule.finiteDimensional_of_le (Subrepresentation.toSubmodule_le_toSubmodule.mpr hτσ)
  have hτbot : τ.toSubmodule ≠ ⊥ := fun hc ↦ hτ.1 (Subrepresentation.toSubmodule_injective
    (hc.trans Subrepresentation.toSubmodule_bot.symm))
  refine ⟨τ, hπ.orthogonalSubrepresentation τ ⊓ σ, hτ,
    hπ.sup_orthogonalSubrepresentation_inf hτσ, ?_, ?_⟩
  · rw [Subrepresentation.toSubmodule_inf, toSubmodule_orthogonalSubrepresentation]
  · have hωsub : (hπ.orthogonalSubrepresentation τ ⊓ σ).toSubmodule
        = τ.toSubmoduleᗮ ⊓ σ.toSubmodule := by
      rw [Subrepresentation.toSubmodule_inf, toSubmodule_orthogonalSubrepresentation]
    refine lt_of_le_of_ne (hωsub ▸ inf_le_right) fun heq ↦ hτbot (le_bot_iff.mp ?_)
    refine Submodule.orthogonal_disjoint τ.toSubmodule le_rfl ?_
    calc τ.toSubmodule ≤ σ.toSubmodule := Subrepresentation.toSubmodule_le_toSubmodule.mpr hτσ
      _ = (hπ.orthogonalSubrepresentation τ ⊓ σ).toSubmodule := heq.symm
      _ ≤ τ.toSubmoduleᗮ := hωsub ▸ inf_le_left

omit [FiniteDimensional 𝕜 V] in
/-- An orthogonal family of atoms spanning `ω` extends by an atom `τ` orthogonal to all of it to
an orthogonal family of atoms spanning `τ ⊔ ω`. -/
private theorem exists_atom_family_of_sup_eq {τ : Subrepresentation π.toRepresentation}
    (hτ : IsAtom τ) {n : ℕ} {U : Fin n → Subrepresentation π.toRepresentation}
    (hatom : ∀ i, IsAtom (U i)) {σ ω : Subrepresentation π.toRepresentation}
    (hiSup : ⨆ i, (U i).toSubmodule = ω.toSubmodule)
    (horth : Pairwise fun i j ↦
      ∀ v ∈ (U i).toSubmodule, ∀ w ∈ (U j).toSubmodule, ⟪v, w⟫_𝕜 = 0)
    (hmix : ∀ j : Fin n, ∀ v ∈ τ.toSubmodule, ∀ w ∈ (U j).toSubmodule, ⟪v, w⟫_𝕜 = 0)
    (hsup : τ ⊔ ω = σ) :
    ∃ (n : ℕ) (U : Fin n → Subrepresentation π.toRepresentation),
      (∀ i, IsAtom (U i)) ∧ ⨆ i, (U i).toSubmodule = σ.toSubmodule ∧
        Pairwise fun i j ↦
          ∀ v ∈ (U i).toSubmodule, ∀ w ∈ (U j).toSubmodule, ⟪v, w⟫_𝕜 = 0 := by
  refine ⟨n + 1, Fin.cons τ U, ?_, ?_, ?_⟩
  · intro i
    rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨j, rfl⟩
    · simpa using hτ
    · simpa using hatom j
  · rw [iSup_fin_succ]
    simp only [Fin.cons_zero, Fin.cons_succ]
    rw [hiSup, ← Subrepresentation.toSubmodule_sup, hsup]
  · rw [pairwise_fin_succ_iff]
    refine ⟨fun i v hv w hw ↦ ?_, fun j ↦ ?_, ?_⟩
    · simp only [Fin.cons_succ, Fin.cons_zero] at hv hw
      exact inner_eq_zero_symm.mp (hmix i w hw v hv)
    · simpa using hmix j
    · simpa using horth

/-- The descent behind `exists_orthogonal_irreducible_decomposition`: every subrepresentation of a
finite-dimensional unitary representation is the supremum of a finite, pairwise orthogonal family
of atoms. The extra numeral `m` is a bound on the dimension, giving the induction something to
decrease. -/
private theorem exists_atom_family_aux (hπ : IsUnitary π) :
    ∀ (m : ℕ) (σ : Subrepresentation π.toRepresentation),
      Module.finrank 𝕜 σ.toSubmodule ≤ m →
      ∃ (n : ℕ) (U : Fin n → Subrepresentation π.toRepresentation),
        (∀ i, IsAtom (U i)) ∧ ⨆ i, (U i).toSubmodule = σ.toSubmodule ∧
          Pairwise fun i j ↦
            ∀ v ∈ (U i).toSubmodule, ∀ w ∈ (U j).toSubmodule, ⟪v, w⟫_𝕜 = 0 := by
  intro m
  induction m with
  | zero =>
    intro σ hle
    refine ⟨0, Fin.elim0, fun i ↦ i.elim0, ?_, fun i ↦ i.elim0⟩
    rw [iSup_of_empty, Submodule.finrank_eq_zero.mp (Nat.le_zero.mp hle)]
  | succ m ih =>
    intro σ hle
    rcases eq_or_ne σ ⊥ with rfl | hσ
    · exact ⟨0, Fin.elim0, fun i ↦ i.elim0, by rw [iSup_of_empty,
        Subrepresentation.toSubmodule_bot], fun i ↦ i.elim0⟩
    obtain ⟨τ, ω, hτ, hsup, hωsub, hωlt⟩ := exists_isAtom_sup_eq_and_lt hπ hσ
    have hωle : Module.finrank 𝕜 ω.toSubmodule ≤ m := by
      have := Submodule.finrank_lt_finrank_of_lt hωlt
      omega
    obtain ⟨n, U, hatom, hiSup, horth⟩ := ih ω hωle
    -- every block of the recursive decomposition lands in the orthogonal complement of the atom
    have hUorth : ∀ j : Fin n, (U j).toSubmodule ≤ τ.toSubmoduleᗮ := fun j ↦
      le_trans (hiSup ▸ le_iSup (fun i ↦ (U i).toSubmodule) j) (hωsub ▸ inf_le_left)
    exact exists_atom_family_of_sup_eq hτ hatom hiSup horth
      (fun j v hv w hw ↦ (Submodule.mem_orthogonal _ w).mp (hUorth j hw) v hv) hsup

/-- **Complete reducibility, orthogonal internal form.** A finite-dimensional unitary continuous
representation of a group decomposes as an orthogonal internal direct sum of finitely many
irreducible subrepresentations, and its dimension is the sum of theirs.

The four conclusions say, in order: each block is irreducible; distinct blocks are orthogonal;
the blocks decompose the space as an internal direct sum; and the dimensions add up. Unitarity is
essential: a general finite-dimensional representation need not decompose into irreducible
subrepresentations at all, since an invariant subspace need not have an invariant complement.
Unitarity supplies one, and supplies it orthogonally, which is what makes the descent go through
and the resulting family orthogonal. -/
theorem exists_orthogonal_irreducible_decomposition (hπ : IsUnitary π) :
    ∃ (n : ℕ) (U : Fin n → Subrepresentation π.toRepresentation),
      (∀ i, (U i).toRepresentation.IsIrreducible) ∧
      OrthogonalFamily 𝕜 (fun i ↦ (U i).toSubmodule) (fun i ↦ ((U i).toSubmodule).subtypeₗᵢ) ∧
      DirectSum.IsInternal (fun i ↦ (U i).toSubmodule) ∧
      Module.finrank 𝕜 V = ∑ i, Module.finrank 𝕜 (U i).toSubmodule := by
  classical
  obtain ⟨n, U, hatom, hiSup, horth⟩ :=
    hπ.exists_atom_family_aux (Module.finrank 𝕜 V) ⊤
      (le_of_eq (by rw [Subrepresentation.toSubmodule_top, finrank_top]))
  have hfamily :
      OrthogonalFamily 𝕜 (fun i ↦ (U i).toSubmodule) (fun i ↦ ((U i).toSubmodule).subtypeₗᵢ) :=
    fun i j hij v w ↦ horth hij v v.2 w w.2
  have htop : ⨆ i, (U i).toSubmodule = ⊤ := by
    rw [hiSup, Subrepresentation.toSubmodule_top]
  have hinternal : DirectSum.IsInternal (fun i ↦ (U i).toSubmodule) :=
    hfamily.isInternal_iff.mpr (by rw [htop, Submodule.top_orthogonal_eq_bot])
  refine ⟨n, U, fun i ↦ Representation.isIrreducible_toRepresentation_of_isAtom (hatom i),
    hfamily, hinternal, ?_⟩
  exact finrank_eq_sum_finrank_of_isInternal hinternal

end FiniteDimensional

end Unitary

section Congr

variable {𝕜 G V W : Type*} [RCLike 𝕜] [Group G]
  [NormedAddCommGroup V] [NormedSpace 𝕜 V] [FiniteDimensional 𝕜 V]
  [NormedAddCommGroup W] [InnerProductSpace 𝕜 W] {π : ContRepresentation 𝕜 G V}

/-- **Complete reducibility for a unitarizable representation, orthogonal internal form.** If a
continuous linear equivalence `e : V ≃L[𝕜] W` conjugates `π` into a *unitary* representation
`congr e π`, then `π` itself — not merely its unitary model — is an internal direct sum of finitely
many irreducible subrepresentations, of dimensions adding up to `dim V`, whose images under `e` are
pairwise orthogonal.

This is `TauCeti.ContRepresentation.IsUnitary.exists_orthogonal_irreducible_decomposition` carried
back along the equivalence of continuous representations
`ContRepresentation.congrEquiv : π.Equiv (congr e π)`: each block `U i` of the unitary model pulls
back to `(U i).toSubmodule.map e.symm`, which is `π`-invariant because `e` intertwines `π` with
`congr e π`, and irreducibility, internality and the dimension count travel along the linear
equivalence `e.symm` restricted to it.

Orthogonality is not stated inside `V`, which carries no inner product here: `e` is there
precisely because `π` need not preserve one, and the form the blocks are orthogonal for is the
invariant `⟪e ·, e ·⟫` pulled back from `W`. Only the unitary model needs an inner product, so
`V` is asked for no more than a finite-dimensional normed space, as
`TauCeti.ContRepresentation.congr` itself is. Nothing here uses finiteness or compactness of the
acting group; a construction of an `e` is what such a hypothesis is for, Weyl's unitarian trick
`TauCeti.ContRepresentation.exists_isUnitary_congr` being one. -/
theorem exists_orthogonal_irreducible_decomposition_of_congr {e : V ≃L[𝕜] W}
    (he : IsUnitary (ContRepresentation.congr e π)) :
    ∃ (n : ℕ) (U : Fin n → Subrepresentation π.toRepresentation),
      (∀ i, (U i).toRepresentation.IsIrreducible) ∧
      (Pairwise fun i j ↦ ∀ v ∈ (U i).toSubmodule, ∀ w ∈ (U j).toSubmodule, ⟪e v, e w⟫_𝕜 = 0) ∧
      DirectSum.IsInternal (fun i ↦ (U i).toSubmodule) ∧
      Module.finrank 𝕜 V = ∑ i, Module.finrank 𝕜 (U i).toSubmodule := by
  have _ : FiniteDimensional 𝕜 W := (e : V ≃ₗ[𝕜] W).finiteDimensional
  obtain ⟨n, U, hirr, horth, hinternal, hdim⟩ := he.exists_orthogonal_irreducible_decomposition
  -- `e` intertwines `π` with `congr e π`: that is the equivalence `ContRepresentation.congrEquiv`.
  have hint : ∀ (g : G) (v : V),
      (e : V ≃ₗ[𝕜] W) ((π.toRepresentation : Representation 𝕜 G V) g v) =
        ((ContRepresentation.congr e π).toRepresentation : Representation 𝕜 G W) g
          ((e : V ≃ₗ[𝕜] W) v) := fun g v ↦ by
    have h := (_root_.ContRepresentation.congrEquiv π e).toContIntertwiningMap.isIntertwining g v
    simp only [_root_.ContRepresentation.Equiv.coe_toContIntertwiningMap,
      _root_.ContRepresentation.congrEquiv_apply] at h
    exact h
  have hsymm : ∀ (g : G) (w : W),
      (e : V ≃ₗ[𝕜] W).symm
          (((ContRepresentation.congr e π).toRepresentation : Representation 𝕜 G W) g w) =
        (π.toRepresentation : Representation 𝕜 G V) g ((e : V ≃ₗ[𝕜] W).symm w) := by
    intro g w
    have h := hint g ((e : V ≃ₗ[𝕜] W).symm w)
    rw [LinearEquiv.apply_symm_apply] at h
    rw [← h, LinearEquiv.symm_apply_apply]
  have hmem : ∀ (i : Fin n) (v : V),
      v ∈ (U i).toSubmodule.map ((e : V ≃ₗ[𝕜] W).symm : W →ₗ[𝕜] V) ↔
        (e : V ≃ₗ[𝕜] W) v ∈ (U i).toSubmodule := fun i v ↦ Submodule.mem_map_equiv _
  have hinv : ∀ (i : Fin n) (g : G) ⦃v : V⦄,
      v ∈ (U i).toSubmodule.map ((e : V ≃ₗ[𝕜] W).symm : W →ₗ[𝕜] V) →
        (π.toRepresentation : Representation 𝕜 G V) g v ∈
          (U i).toSubmodule.map ((e : V ≃ₗ[𝕜] W).symm : W →ₗ[𝕜] V) := by
    intro i g v hv
    refine (hmem i _).mpr ?_
    rw [hint g v]
    exact (U i).apply_mem_toSubmodule g ((hmem i v).mp hv)
  refine ⟨n, fun i ↦ ⟨(U i).toSubmodule.map ((e : V ≃ₗ[𝕜] W).symm : W →ₗ[𝕜] V), hinv i⟩,
    fun i ↦ ?_, fun i j hij v hv w hw ↦ ?_, ?_, ?_⟩
  · refine Representation.isIrreducible_of_linearEquiv
      ((e : V ≃ₗ[𝕜] W).symm.submoduleMap (U i).toSubmodule) (fun g x ↦ Subtype.ext ?_) (hirr i)
    simp only [LinearEquiv.submoduleMap_apply, Subrepresentation.toRepresentation_apply]
    exact hsymm g x
  · exact horth hij ⟨_, (hmem i v).mp hv⟩ ⟨_, (hmem j w).mp hw⟩
  · obtain ⟨hindep, htop⟩ :=
      (DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top _).mp hinternal
    refine (DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top _).mpr
      ⟨hindep.map_orderIso (Submodule.orderIsoMapComap (e : V ≃ₗ[𝕜] W).symm), ?_⟩
    rw [← Submodule.map_iSup, htop, Submodule.map_top, LinearEquiv.range]
  · rw [(e : V ≃ₗ[𝕜] W).finrank_eq, hdim]
    exact Finset.sum_congr rfl fun i _ ↦
      ((e : V ≃ₗ[𝕜] W).symm.submoduleMap (U i).toSubmodule).finrank_eq

end Congr

end IsUnitary

end ContRepresentation

end TauCeti
