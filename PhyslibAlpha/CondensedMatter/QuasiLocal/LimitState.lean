/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.CondensedMatter.QuasiLocal.Instances
public import PhyslibAlpha.CondensedMatter.QuasiLocal.Interaction
public import PhyslibAlpha.ProbabilisticTheory.QuasiLocal.Limit
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.Matrix.Order
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order

/-!

# Thermodynamic limit states of an interaction

The Gibbs states of the finite boxes have limit points, which are states of the infinite system.

## i. Overview

Every local operator of a quantum lattice system is bounded, `a* a ≤ ‖a‖² · 1`, so the net of
box expectations of a fixed local observable is bounded. By compactness the canonical or grand
canonical Gibbs states of the boxes `Λ` converge, along any ultrafilter finer than the filter of
large boxes, to a state of the quasi-local algebra. This is the *thermodynamic limit state*. It is
a state of the infinite crystal, not a number attached to it.

## ii. Key results

- `matrix_exists_sumSq` : in a matrix algebra `a* a + p = c · 1` for a sum of squares `p`.
- `quantumNet_isLocallyBounded` : the net of operators is locally bounded.
- `Interaction.canonicalLimitState` : the thermodynamic limit state of the canonical ensemble.
- `Interaction.grandCanonicalLimitState` : that of the grand canonical ensemble.

## iii. Table of contents

- A. Local boundedness of the net of operators
- B. Limit states of the ensembles

## iv. References

* O. Bratteli & D. Robinson, Operator Algebras and Quantum Statistical Mechanics 2,
  Section 6.2.3.

-/

@[expose] public section

noncomputable section

namespace CondensedMatter

namespace QuasiLocal

open ProbabilisticTheory ProbabilisticTheory.QuasiLocal Filter

/-! ## A. Local boundedness of the net of operators -/

section Bounded

open scoped Matrix.Norms.L2Operator MatrixOrder

/-- In a matrix algebra every `a* a` lies below a multiple of the identity by a sum of
squares. -/
lemma matrix_exists_sumSq {n : Type*} [Fintype n] [DecidableEq n] (a : Matrix n n ℂ) :
    ∃ c : ℝ, ∃ p ∈ sumSq (Matrix n n ℂ), star a * a + p = (c : ℂ) • (1 : Matrix n n ℂ) := by
  obtain ⟨p, hp, h⟩ := (StarOrderedRing.le_iff _ _).1
    (CStarAlgebra.star_mul_le_algebraMap_norm_sq a)
  refine ⟨‖a‖ ^ 2, p, hp, ?_⟩
  rw [← h, Algebra.algebraMap_eq_smul_one, Complex.coe_smul]

end Bounded

variable {S : Type*} [DecidableEq S]
variable {Ω : S → Type*} [∀ s, Fintype (Ω s)] [∀ s, DecidableEq (Ω s)]

/-- **The net of operators is locally bounded.** -/
lemma quantumNet_isLocallyBounded : (quantumNet Ω).IsLocallyBounded :=
  fun _ a => matrix_exists_sumSq a

/-! ## B. Limit states of the ensembles -/

variable [∀ s, Nonempty (Ω s)]

/-- **The thermodynamic limit state of the canonical ensemble** along an ultrafilter of boxes:
a state of the infinite system. -/
def Interaction.canonicalLimitState (I : Interaction Ω) (β : ℝ) (𝒰 : Ultrafilter (Finset S))
    (h𝒰 : (𝒰 : Filter (Finset S)) ≤ atTop) : AlgState (quantumNet Ω).Quasilocal :=
  limitState (N := quantumNet Ω) (fun Λ => I.canonicalState β Λ) quantumNet_isLocallyBounded h𝒰

/-- **The thermodynamic limit state of the grand canonical ensemble** along an ultrafilter of
boxes. -/
def Interaction.grandCanonicalLimitState (I : Interaction Ω) (q : Charge Ω) (β μ : ℝ)
    (𝒰 : Ultrafilter (Finset S)) (h𝒰 : (𝒰 : Filter (Finset S)) ≤ atTop) :
    AlgState (quantumNet Ω).Quasilocal :=
  limitState (N := quantumNet Ω) (fun Λ => I.grandCanonicalState q β μ Λ)
    quantumNet_isLocallyBounded h𝒰

/-- The limit state of the canonical ensemble on a local observable is the limit of the box
expectations. -/
lemma Interaction.canonicalLimitState_of (I : Interaction Ω) (β : ℝ) (𝒰 : Ultrafilter (Finset S))
    (h𝒰 : (𝒰 : Filter (Finset S)) ≤ atTop) (X : Finset S) (a : Alg Ω X) :
    Tendsto (localSeq (N := quantumNet Ω) (fun Λ => I.canonicalState β Λ) X a) 𝒰
      (nhds (I.canonicalLimitState β 𝒰 h𝒰 ((quantumNet Ω).of X a))) :=
  limitState_of (N := quantumNet Ω) (fun Λ => I.canonicalState β Λ)
    quantumNet_isLocallyBounded h𝒰 X a

end QuasiLocal

end CondensedMatter

end
