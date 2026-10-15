/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.CondensedMatter.QuasiLocal.Gibbs
public import PhyslibAlpha.CondensedMatter.QuasiLocal.Local
public import Mathlib.Analysis.Matrix.Normed

/-!

# Interactions, finite-volume Hamiltonians and ensembles of a lattice system

An interaction assigns an operator to each finite region of a lattice, and the finite-volume
Hamiltonian is the sum of the lifts to a box of the terms it contains.

## i. Overview

An *interaction* `Φ` assigns to each finite region `X` of the sites a Hermitian operator `Φ X` of
the algebra of `X`. The Ising chain has `Φ {x} = h σᶻ_x` and `Φ {x, y} = - J σᶻ_x σᶻ_y` for
neighbours. The *Hamiltonian of a finite box* `Λ` is
`H_Λ = ∑_{X ⊆ Λ} (Φ X ⊗ 1)`: every term supported inside the box, lifted to the box by `M ↦ M ⊗ 1`
and summed. A *charge* is a function `q_x` on the configuration space of each site, such as the
occupation number, and the total charge `N_Λ = ∑_{x ∈ Λ} q_x` of a box is the diagonal operator
with value `∑ q_x(c_x)` on the configuration `c`.

The lifts commute with the exponential: for a unital `*`-homomorphism `φ`, `φ (e^a) = e^{φ a}`, so
the Gibbs weight of a lifted operator is the lift of its Gibbs weight. The canonical and grand
canonical states of a box are the Gibbs states of `H_Λ` and `H_Λ - μ N_Λ` at inverse temperature
`β`, as in `Gibbs`. If the interaction conserves the charge, they factorize.

## ii. Key results

- `Interaction` : a family of Hermitian operators indexed by finite regions.
- `Interaction.hamiltonian` : the Hamiltonian of a finite box.
- `inclMat_exp` : the lift of an exponential is the exponential of the lift.
- `chargeOp` : the total charge of a box.
- `Interaction.canonicalState`, `Interaction.grandCanonicalState` : the ensembles of a box.

## iii. Table of contents

- A. Interactions and the Hamiltonian of a box
- B. Lifts and the exponential
- C. Charges and the ensembles of a box

## iv. References

* O. Bratteli & D. Robinson, Operator Algebras and Quantum Statistical Mechanics 2,
  Section 6.2.

-/

@[expose] public section

noncomputable section

namespace CondensedMatter

namespace QuasiLocal

open ProbabilisticTheory
open scoped Matrix

variable {S : Type*} [DecidableEq S]
variable (Ω : S → Type*) [∀ s, Fintype (Ω s)] [∀ s, DecidableEq (Ω s)]

/-! ## A. Interactions and the Hamiltonian of a box -/

/-- **An interaction**: a Hermitian operator of each finite region. -/
structure Interaction where
  /-- The term of the interaction supported in a region. -/
  Φ : ∀ X : Finset S, Alg Ω X
  /-- Every term is Hermitian. -/
  isHermitian : ∀ X, (Φ X).IsHermitian

variable {Ω}

/-- **The Hamiltonian of a finite box**: the sum of the lifts to the box of the terms of the
interaction supported inside it. -/
def Interaction.hamiltonian (I : Interaction Ω) (Λ : Finset S) : Alg Ω Λ :=
  ∑ X : Λ.powerset, inclMat (Finset.mem_powerset.1 X.2) (I.Φ X)

omit [∀ s, Fintype (Ω s)] in
lemma Interaction.hamiltonian_isHermitian (I : Interaction Ω) (Λ : Finset S) :
    (I.hamiltonian Λ).IsHermitian := by
  rw [Matrix.IsHermitian, hamiltonian, Matrix.conjTranspose_sum]
  refine Finset.sum_congr rfl fun X _ => ?_
  rw [← inclMat_conjTranspose, (I.isHermitian X).eq]

/-! ## B. Lifts and the exponential -/

open scoped Matrix.Norms.Operator in
/-- The lift `M ↦ M ⊗ 1` commutes with the exponential. -/
lemma inclMat_exp {X Y : Finset S} (h : X ≤ Y) (a : Alg Ω X) :
    inclMat h (NormedSpace.exp a) = NormedSpace.exp (inclMat h a) :=
  NormedSpace.map_exp (inclStarAlg h)
    (LinearMap.continuous_of_finiteDimensional (inclStarAlg h).toAlgHom.toLinearMap) a

/-- **The lift of a Gibbs weight is the Gibbs weight of the lift.** -/
lemma inclMat_gibbsWeight {X Y : Finset S} (h : X ≤ Y) (a : Alg Ω X) :
    inclMat h (gibbsWeight a) = gibbsWeight (inclMat h a) := by
  rw [gibbsWeight, gibbsWeight, inclMat_exp]
  congr 1
  exact map_neg (inclStarAlg h) a

/-! ## C. Charges and the ensembles of a box -/

/-- A charge: a real number attached to each value of the configuration space of each site, such
as the occupation number of a mode. -/
abbrev Charge (Ω : S → Type*) := ∀ s, Ω s → ℝ

/-- **The total charge of a box**: the diagonal operator with the value `∑_{x ∈ Λ} q_x(c_x)` on
the configuration `c`. -/
def chargeOp (q : Charge Ω) (Λ : Finset S) : Alg Ω Λ :=
  Matrix.diagonal fun c => ((∑ x : Λ, q x.1 (c x) : ℝ) : ℂ)

omit [DecidableEq S] [∀ s, Fintype (Ω s)] in
lemma chargeOp_isHermitian (q : Charge Ω) (Λ : Finset S) : (chargeOp q Λ).IsHermitian := by
  rw [Matrix.IsHermitian, chargeOp, Matrix.diagonal_conjTranspose]
  congr 1
  funext c
  simp

variable [∀ s, Nonempty (Ω s)]

/-- **The canonical ensemble of a box** at inverse temperature `β`. -/
def Interaction.canonicalState (I : Interaction Ω) (β : ℝ) (Λ : Finset S) :
    AlgState (Alg Ω Λ) :=
  QuasiLocal.canonicalState β (I.hamiltonian Λ) (I.hamiltonian_isHermitian Λ)

/-- **The grand canonical ensemble of a box** at inverse temperature `β` and chemical potential
`μ` for the charge `q`. -/
def Interaction.grandCanonicalState (I : Interaction Ω) (q : Charge Ω) (β μ : ℝ)
    (Λ : Finset S) : AlgState (Alg Ω Λ) :=
  QuasiLocal.grandCanonicalState β μ (I.hamiltonian Λ) (chargeOp q Λ)
    (I.hamiltonian_isHermitian Λ) (chargeOp_isHermitian q Λ)

/-- The interaction conserves the charge: the Hamiltonian of every box commutes with its
total charge. -/
def Interaction.Conserves (I : Interaction Ω) (q : Charge Ω) : Prop :=
  ∀ Λ : Finset S, Commute (I.hamiltonian Λ) (chargeOp q Λ)

omit [∀ s, Nonempty (Ω s)] in
/-- **For a conserved charge the grand canonical weight of a box is its canonical weight times a
fugacity.** -/
lemma Interaction.grandCanonicalWeight_of_conserves (I : Interaction Ω) {q : Charge Ω}
    (hq : I.Conserves q) (β μ : ℝ) (Λ : Finset S) :
    gibbsWeight (grandCanonicalOp β μ (I.hamiltonian Λ) (chargeOp q Λ)) =
      gibbsWeight ((β : ℂ) • I.hamiltonian Λ) *
        NormedSpace.exp (((β * μ : ℝ) : ℂ) • chargeOp q Λ) :=
  grandCanonicalWeight_of_commute β μ (hq Λ)

end QuasiLocal

end CondensedMatter

end
