/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import PhyslibAlpha.ClassicalFieldTheory.GaugeTheory.GlobalGaugeGroup.Basic
public import Mathlib.LinearAlgebra.SymplecticGroup
/-!
# The global gauge group Sp(n)

The compact symplectic group, as a global gauge group.

## i. Overview

The compact symplectic group `Sp(n)`, also written `USp(2n)`, is the group of unitary
`2n × 2n` complex matrices `A` which preserve the standard symplectic form `J`,
`A J Aᵀ = J`. It is the compact real form of the complex symplectic group, and it appears as
a gauge group in grand unified and supersymmetric theories. Here `Sp(1)` is `SU(2)`.

Unitarity and the symplectic condition are both closed, so the compact symplectic matrices
form a closed submonoid of matrices. The conjugate transpose of a unitary matrix is its
inverse, and the inverse of a symplectic matrix is symplectic, so the submonoid is closed
under the conjugate transpose. An invertible matrix therefore lies in the global gauge
group `Sp(n)` exactly when it is unitary and symplectic.

## ii. Key results

- `GlobalGaugeGroup.compactSymplecticGroup` : the unitary symplectic matrices.
- `GlobalGaugeGroup.Sp` : the global gauge group `Sp(n)`.
- `GlobalGaugeGroup.mem_Sp_iff` : an invertible matrix lies in `Sp(n)` exactly when it is
  unitary and symplectic.

## iii. Table of contents

- A. The group Sp(n)
- B. Membership

## iv. References

* None.

-/

@[expose] public section

open Matrix

namespace GlobalGaugeGroup

/-!

## A. The group Sp(n)

-/

/-- The unitary `2n × 2n` complex matrices `A` preserving the symplectic form,
  `A J Aᵀ = J`. -/
def compactSymplecticGroup (n : ℕ) : Submonoid (Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ) :=
  unitaryGroup (Fin n ⊕ Fin n) ℂ ⊓ symplecticGroup (Fin n) ℂ

/-- The global gauge group `Sp(n)`, the unitary `2n × 2n` complex matrices preserving the
  symplectic form. Unitarity and the symplectic condition are both closed conditions. -/
def Sp (n : ℕ) : GlobalGaugeGroup (Fin n ⊕ Fin n) :=
  ofSubmonoid (compactSymplecticGroup n) (by
    rw [compactSymplecticGroup, Submonoid.coe_inf]
    exact isClosed_unitary.inter (isClosed_eq
      ((continuous_id.matrix_mul continuous_const).matrix_mul continuous_id.matrix_transpose)
      continuous_const))

/-!

## B. Membership

-/

/-- A matrix lies in the unitary symplectic matrices exactly when it is unitary and
  symplectic. -/
lemma mem_compactSymplecticGroup_iff {n : ℕ} {A : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ} :
    A ∈ compactSymplecticGroup n ↔
      A ∈ unitaryGroup (Fin n ⊕ Fin n) ℂ ∧ A ∈ symplecticGroup (Fin n) ℂ :=
  Iff.rfl

/-- The conjugate transpose of a unitary symplectic matrix is unitary symplectic, being its
  inverse. -/
lemma star_mem_compactSymplecticGroup {n : ℕ} {A : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ}
    (hA : A ∈ compactSymplecticGroup n) : star A ∈ compactSymplecticGroup n := by
  refine ⟨Unitary.star_mem hA.1, ?_⟩
  rw [← inv_eq_left_inv ((mem_unitaryGroup_iff' (α := ℂ)).1 hA.1),
    ← SymplecticGroup.coe_inv' ⟨A, hA.2⟩]
  exact SetLike.coe_mem _

/-- An invertible matrix lies in `Sp(n)` exactly when it is unitary and symplectic. -/
lemma mem_Sp_iff {n : ℕ} {g : GeneralLinearGroup (Fin n ⊕ Fin n) ℂ} :
    g ∈ (Sp n).group ↔ (g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ) ∈ compactSymplecticGroup n :=
  mem_ofSubmonoid_iff_of_star_mem inf_le_left fun _ => star_mem_compactSymplecticGroup

end GlobalGaugeGroup
