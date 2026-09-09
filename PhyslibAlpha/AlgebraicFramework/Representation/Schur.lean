/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.AlgebraicFramework.Representation.Covariance.Basic
public import Mathlib.Algebra.DirectSum.Module

/-!

# Schur's lemma and multiplicity-free covariant channels

There is a recurring pattern in representation theory: once a `G`-invariant object (a
representation space, an operator space, a channel's domain) is decomposed into blocks
$E = \bigoplus_i W_i$ that are individually `G`-invariant and "Schur" (no non-scalar `G`-equivariant
self-map), *every* `G`-equivariant endomorphism of the whole space is pinned down block-by-block to
a single real scalar per block — instead of classifying arbitrary linear maps on a
high-dimensional space, one classifies a handful of numbers. For the qubit, this is exactly why
a rotationally covariant channel on the Hermitian $2\times2$ matrices reduces from "an arbitrary
linear self-map of a four-real-dimensional space" to "one real number $\lambda$": the space splits
as the scalar sector (spin $0$) plus the Pauli-vector sector (spin $1$), each Schur.

This file formalizes the reusable core of that argument, deliberately *not* mathlib's
representation-theoretic Schur's lemma (see the note below on why): a bare `Prop`-valued Schur
hypothesis on a submodule, and the classification theorem for a finite direct sum of Schur blocks.

## Why not mathlib's `Representation`/`FDRep` Schur's lemma

`Mathlib.RepresentationTheory.Irreducible` has
`Representation.IsIrreducible.algebraMap_intertwiningMap_bijective_of_isAlgClosed`, the sharpest
form of Schur's lemma mathlib has (the endomorphism ring of an irreducible representation is
exactly the base field), and `Mathlib.CategoryTheory.Preadditive.Schur` /
`Mathlib.RepresentationTheory.FDRep` have the abstract Krull–Schmidt-flavoured Hom-space version.
Both require the base field to be algebraically closed (`IsAlgClosed k`) — true for `ℂ`, false for
`ℝ`. Over `ℝ` this hypothesis genuinely fails in general (a real irreducible representation can
have endomorphism ring `ℝ`, `ℂ`, or the quaternions `ℍ`, e.g. the standard real representation of
the circle group on `ℝ²` is irreducible with endomorphism ring `ℂ`, not `ℝ` — rotation-by-90° is a
non-scalar equivariant endomorphism). The qubit's Pauli-vector sector genuinely is a "real type"
representation (endomorphism ring `ℝ`), but this is *extra* representation-theoretic input beyond
generic Schur, not something `IsAlgClosed`-Schur gives for free over `ℝ`. Moreover this codebase's
`E`/`Symmetry E` (`OrderUnit/Symmetry.lean`) is a bare order-unit module with a group of
order-automorphisms, not mathlib's `Representation k G V` structure (a genuine `k[G]`-module) —
bridging the two would cost more than it buys. So the Schur hypothesis below is taken as an
explicit, minimal `Prop` on a `Submodule`, to be discharged per-block by whatever means are
available (cited from elsewhere or proved directly), rather than derived from a general
representation-theoretic classification result.

## Main definitions

- `IsSchurBlock smul W` : the Schur hypothesis for a submodule `W`, relative to an action
  `smul : G → E → E` — every linear self-map of `E` that is equivariant on `W` and preserves `W`
  acts as a single scalar on all of `W`.

## Main results

- `exists_scalar_of_isSchurBlock` : the multiplicity-free classification theorem — given a finite
  family of Schur blocks decomposing `E` as an internal direct sum, each individually `G`-invariant,
  every `G`-equivariant linear endomorphism of `E` that preserves every block acts on each block `W
  i` as `c i • id` for some real scalar `c i`.
- `UnitalPositiveLinearMap.IsCovariant.exists_scalar_of_isSchurBlock` : the same theorem phrased for
  a covariant channel `φ : E →ₚ₁[ℝ] E` (`Measurement/Covariance.lean`), the form that plugs directly
  into this codebase's existing covariance notion.

-/

@[expose] public section

/-! ## The Schur hypothesis on a single block -/

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

/-! ## The multiplicity-free classification theorem -/

section MultiplicityFree

variable {G E ι : Type*} [AddCommGroup E] [Module ℝ E] [DecidableEq ι] [Fintype ι]

omit [Fintype ι] in
/-- **Multiplicity-free classification of covariant endomorphisms.** Suppose `E` decomposes as an
internal direct sum `E = ⨁ i, W i` (`hsum`) of finitely many submodules, each `G`-invariant
(`hW_inv`) and each satisfying the Schur hypothesis (`hSchur`). Then every `G`-equivariant linear
endomorphism `f` of `E` that preserves each block (`hf_block` — automatic when the blocks are
pairwise non-isomorphic as `G`-representations, e.g. the qubit's spin-$0$/spin-$1$ split, but not
derivable from the single-block Schur hypothesis alone, so it is taken as a hypothesis here; see the
file docstring) acts on each block `W i` as `c i • id` for some real scalar `c i` — the whole
endomorphism is pinned down by finitely many real numbers, one per block.

The direct-sum and block-invariance hypotheses (`hsum`, `hW_inv`) record the intended setting — a
genuine decomposition of `E` into `G`-subrepresentations — even though the conclusion, stated only
on each block separately, does not need to unfold them further than `hf_block` already supplies. -/
theorem exists_scalar_of_isSchurBlock (smul : G → E → E) (W : ι → Submodule ℝ E)
    (_hsum : DirectSum.IsInternal W) (_hW_inv : ∀ i g, ∀ x ∈ W i, smul g x ∈ W i)
    (hSchur : ∀ i, IsSchurBlock smul (W i)) (f : E →ₗ[ℝ] E)
    (hf_equiv : ∀ g x, f (smul g x) = smul g (f x)) (hf_block : ∀ i, ∀ x ∈ W i, f x ∈ W i) :
    ∃ c : ι → ℝ, ∀ i, ∀ x ∈ W i, f x = c i • x := by
  choose c hc using fun i => hSchur i f (fun g x _ => hf_equiv g x) (hf_block i)
  exact ⟨c, hc⟩

end MultiplicityFree

/-! ## Connecting to covariant channels

`Measurement/Covariance.lean` phrases covariance for a channel `φ : E →ₚ₁[ℝ] E` intertwining a
symmetry action `ρ : G →* Symmetry E` with itself, via `UnitalPositiveLinearMap.IsCovariant`. The
underlying linear map of such a channel is exactly a `G`-equivariant endomorphism of `E` for the
action `g • x := (ρ g).1 x`, so the classification theorem above applies directly. -/

section CovariantChannel

variable {G E ι : Type*} [Group G] [AddCommGroup E] [PartialOrder E] [Module ℝ E] [One E]
  [DecidableEq ι] [Fintype ι]

omit [Fintype ι] in
/-- The multiplicity-free classification theorem, specialized to a **covariant channel**
`φ : E →ₚ₁[ℝ] E` (`UnitalPositiveLinearMap.IsCovariant`, `Measurement/Covariance.lean`) intertwining
a symmetry action `ρ : G →* Symmetry E` with itself. Given a finite internal direct sum
decomposition of `E` into `G`-invariant Schur blocks that `φ` preserves, `φ` acts on each block
`W i` as multiplication by a single real scalar `c i`. -/
theorem UnitalPositiveLinearMap.IsCovariant.exists_scalar_of_isSchurBlock
    {ρ : G →* Symmetry E} {φ : E →ₚ₁[ℝ] E} (hφ : φ.IsCovariant ρ ρ) (W : ι → Submodule ℝ E)
    (hsum : DirectSum.IsInternal W)
    (hW_inv : ∀ i g, ∀ x ∈ W i, (ρ g).1 x ∈ W i)
    (hSchur : ∀ i, IsSchurBlock (fun g x => (ρ g).1 x) (W i))
    (hφ_block : ∀ i, ∀ x ∈ W i, φ x ∈ W i) :
    ∃ c : ι → ℝ, ∀ i, ∀ x ∈ W i, φ x = c i • x := by
  refine _root_.exists_scalar_of_isSchurBlock (fun g x => (ρ g).1 x) W hsum hW_inv hSchur
    φ.toLinearMap (fun g x => ?_) hφ_block
  have := DFunLike.congr_fun (hφ g) x
  simpa [UnitalPositiveLinearMap.comp_apply] using this

end CovariantChannel
