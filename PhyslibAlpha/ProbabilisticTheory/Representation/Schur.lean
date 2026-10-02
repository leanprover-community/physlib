/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.ProbabilisticTheory.Representation.Covariance.Basic
public import Mathlib.Algebra.DirectSum.Module

/-!

# Schur's lemma for covariant channels

## i. Overview

If the observables split into invariant blocks `E = ⨁ᵢ Wᵢ` on each of which every equivariant map
acts as a scalar, then every equivariant map preserving the blocks is determined by one real number
per block. For the qubit, the Hermitian `2 × 2` matrices split into the scalars and the Pauli
vectors, so a rotation-covariant channel is determined by one number.

Mathlib's Schur lemma needs an algebraically closed field, while the observables are a real space.
The Schur property of a block is therefore a hypothesis, `IsSchurBlock`.

## ii. Key results

- `IsSchurBlock` : every equivariant map preserving the block acts on it as a scalar.
- `exists_scalar_of_isSchurBlock` : an equivariant map is a scalar on each block.
- `UnitalPositiveLinearMap.IsCovariant.exists_scalar_of_isSchurBlock` : the same for covariant
  channels.

## iii. Table of contents

- A. The Schur hypothesis on a single block
- B. The multiplicity-free classification theorem
- C. Covariant channels

-/

@[expose] public section

namespace ProbabilisticTheory

/-! ## A. The Schur hypothesis on a single block -/

section IsSchurBlock

variable {G E : Type*} [AddCommGroup E] [Module ℝ E]

/-- The **Schur hypothesis** for a submodule `W`, relative to an action `smul : G → E → E`: every
linear endomorphism of `E` that is `G`-equivariant on `W` (`f (smul g x) = smul g (f x)` for
`x ∈ W`) and maps `W` into itself acts on all of `W` as a single scalar `c`. This is the abstract
shape of "every `G`-equivariant self-map of an irreducible real representation is a scalar" — taken
here as a hypothesis to be supplied per block (cited or proved separately), not derived from a
general representation-theoretic classification (see the file docstring). -/
def IsSchurBlock (smul : G → E → E) (W : Submodule ℝ E) : Prop :=
  ∀ f : E →ₗ[ℝ] E, (∀ g : G, ∀ x ∈ W, f (smul g x) = smul g (f x)) →
    (∀ x ∈ W, f x ∈ W) → ∃ c : ℝ, ∀ x ∈ W, f x = c • x

end IsSchurBlock

/-! ## B. The multiplicity-free classification theorem -/

section MultiplicityFree

variable {G E ι : Type*} [AddCommGroup E] [Module ℝ E] [DecidableEq ι] [Fintype ι]

omit [Fintype ι] in
/-- **Equivariant maps are scalars on Schur blocks.** If `E = ⨁ᵢ Wᵢ` with invariant Schur blocks
`Wᵢ`, every equivariant linear map preserving the blocks acts on each `Wᵢ` as a real scalar. -/
lemma exists_scalar_of_isSchurBlock (smul : G → E → E) (W : ι → Submodule ℝ E)
    (_hsum : DirectSum.IsInternal W) (_hW_inv : ∀ i g, ∀ x ∈ W i, smul g x ∈ W i)
    (hSchur : ∀ i, IsSchurBlock smul (W i)) (f : E →ₗ[ℝ] E)
    (hf_equiv : ∀ g x, f (smul g x) = smul g (f x)) (hf_block : ∀ i, ∀ x ∈ W i, f x ∈ W i) :
    ∃ c : ι → ℝ, ∀ i, ∀ x ∈ W i, f x = c i • x := by
  choose c hc using fun i => hSchur i f (fun g x _ => hf_equiv g x) (hf_block i)
  exact ⟨c, hc⟩

end MultiplicityFree

/-! ## C. Covariant channels

A channel intertwining a symmetry action with itself is a `G`-equivariant endomorphism. -/

section CovariantChannel

variable {G E ι : Type*} [Group G] [OrderUnitSpace E]
  [DecidableEq ι] [Fintype ι]

omit [Fintype ι] in
/-- **Schur's lemma for covariant channels.** A channel covariant for a symmetry action `ρ` acts as
a real scalar on each block of a finite decomposition of `E` into invariant Schur blocks that it
preserves. -/
lemma UnitalPositiveLinearMap.IsCovariant.exists_scalar_of_isSchurBlock
    {ρ : G →* Symmetry E} {φ : Channel E E} (hφ : φ.IsCovariant ρ ρ) (W : ι → Submodule ℝ E)
    (hsum : DirectSum.IsInternal W)
    (hW_inv : ∀ i g, ∀ x ∈ W i, (ρ g).1 x ∈ W i)
    (hSchur : ∀ i, IsSchurBlock (fun g x => (ρ g).1 x) (W i))
    (hφ_block : ∀ i, ∀ x ∈ W i, φ x ∈ W i) :
    ∃ c : ι → ℝ, ∀ i, ∀ x ∈ W i, φ x = c i • x := by
  refine ProbabilisticTheory.exists_scalar_of_isSchurBlock (fun g x => (ρ g).1 x) W hsum hW_inv
    hSchur φ.toLinearMap (fun g x => ?_) hφ_block
  have := DFunLike.congr_fun (hφ g) x
  exact this

end CovariantChannel

end ProbabilisticTheory
