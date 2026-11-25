/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jinzheng Li, Nathaneal Sajan, Joseph Tooby-Smith
-/
module

public import PhyslibAlpha.ClassicalFieldTheory.GaugeTheory.GlobalGaugeGroup.U1
public import PhyslibAlpha.Mathematics.InvariantReduction
/-!
# The eigenspaces of the elements of `U(1)`

The subspaces on which an element of `U(1)` acts by a scalar, and the families of a given charge.

## i. Overview

The group `U(1)`, the unit complex numbers `unitary ℂ`, is abelian, so it is its own centre and
every element `z` plays the part that `-1` plays for `SL(2,ℂ)` and `ω 1` for `SU(N)`.
`centreEigenspace ρ z ε` names the subspace on which `z` acts by the scalar `ε` (A). A family of
charge `q`, moved by `u` to `u ^ q` times itself, spans a subspace of the eigenspace of `z` at
`z ^ q` (B). For a representation on an algebra by algebra maps the scalar of a product is the
product of the scalars (C), and a vector that the group fixes and that lies in an eigenspace with
`ε ≠ 1` is zero, also modulo a stable submodule `S` (D).

## ii. Key results

- `GlobalGaugeGroup.U1.centreEigenspace` : the subspace on which `z` acts by `ε`.
- `GlobalGaugeGroup.U1.span_le_centreEigenspace_of_charge` : a family of charge `q` lies in the
  eigenspace of `z` at `z ^ q`.
- `GlobalGaugeGroup.U1.eq_zero_of_invariant_of_mem_centreEigenspace` : an invariant in an
  eigenspace with `ε ≠ 1` is zero.
- `GlobalGaugeGroup.U1.mem_of_invariant_of_mem_sup_centreEigenspace` : the same modulo a stable
  submodule.

## iii. Table of contents

- A. The eigenspaces
- B. Families of a given charge
- C. Scalars multiply
- D. Invariants in an eigenspace

## iv. References

The same pattern for `SL(2,ℂ)` is
`PhyslibAlpha.Relativity.LorentzGroup.Invariants.CentreEigenspace`, and for `SU(N)`
`PhyslibAlpha.ClassicalFieldTheory.GaugeTheory.GlobalGaugeGroup.SU.CentreEigenspace`.

-/

@[expose] public section

namespace GlobalGaugeGroup.U1

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

/-!

## A. The eigenspaces

-/

/-- The subspace on which the element `z` of `U(1)` acts by the scalar `ε`. -/
def centreEigenspace (ρ : Representation ℂ (unitary ℂ) V) (z : unitary ℂ) (ε : ℂ) :
    Submodule ℂ V :=
  Module.End.eigenspace (ρ z) ε

/-- Membership of `centreEigenspace` unfolded: `z` scales the vector by `ε`. -/
lemma mem_centreEigenspace {ρ : Representation ℂ (unitary ℂ) V} {z : unitary ℂ} {ε : ℂ}
    {x : V} : x ∈ centreEigenspace ρ z ε ↔ ρ z x = ε • x := by
  simp [centreEigenspace]

/-!

## B. Families of a given charge

-/

/-- A family of charge `q`, moved by every `u` to `u ^ q` times itself, spans a subspace of the
  eigenspace of `z` at `z ^ q`. -/
lemma span_le_centreEigenspace_of_charge {ρ : Representation ℂ (unitary ℂ) V} {ι : Type*}
    {T : ι → V} {q : ℤ} (hT : ∀ (u : unitary ℂ) (l : ι), ρ u (T l) = ((u : ℂ) ^ q) • T l)
    (z : unitary ℂ) : Submodule.span ℂ (Set.range T) ≤ centreEigenspace ρ z ((z : ℂ) ^ q) :=
  Submodule.span_le.2 <| Set.range_subset_iff.2 fun l => mem_centreEigenspace.2 (hT z l)

/-!

## C. Scalars multiply

-/

/-- For a representation by multiplicative maps, the scalar of a product is the product of the
  scalars. -/
lemma mul_le_centreEigenspace {A : Type} [Ring A] [Algebra ℂ A]
    {ρ : Representation ℂ (unitary ℂ) A}
    (hmul : ∀ (g : unitary ℂ) (x y : A), ρ g (x * y) = ρ g x * ρ g y) {z : unitary ℂ}
    {W₁ W₂ : Submodule ℂ A} {ε₁ ε₂ : ℂ} (h₁ : W₁ ≤ centreEigenspace ρ z ε₁)
    (h₂ : W₂ ≤ centreEigenspace ρ z ε₂) :
    W₁ * W₂ ≤ centreEigenspace ρ z (ε₁ * ε₂) := by
  refine Submodule.mul_le.2 fun a ha b hb => ?_
  rw [mem_centreEigenspace, hmul, mem_centreEigenspace.1 (h₁ ha),
    mem_centreEigenspace.1 (h₂ hb), Algebra.smul_mul_assoc, Algebra.mul_smul_comm, smul_smul]

/-!

## D. Invariants in an eigenspace

-/

/-- A vector fixed by `U(1)` that lies in an eigenspace of `z` with `ε ≠ 1` is zero: `z` fixes it
  and scales it by `ε`. -/
lemma eq_zero_of_invariant_of_mem_centreEigenspace {ρ : Representation ℂ (unitary ℂ) V}
    {z : unitary ℂ} {ε : ℂ} (hε : ε ≠ 1) {x : V} (hx : x ∈ centreEigenspace ρ z ε)
    (hinv : ∀ u : unitary ℂ, ρ u x = x) : x = 0 := by
  have h : (ε - 1) • x = 0 := by
    rw [sub_smul, ← mem_centreEigenspace.1 hx, hinv, one_smul, sub_self]
  exact (smul_eq_zero.1 h).resolve_left (sub_ne_zero.2 hε)

/-- A subspace on which `z` acts by `ε ≠ 1` carries no invariant beyond a stable submodule `S`: an
  invariant of the join with `S` already lies in `S`. -/
lemma mem_of_invariant_of_mem_sup_centreEigenspace {ρ : Representation ℂ (unitary ℂ) V}
    {z : unitary ℂ} {ε : ℂ} (hε : ε ≠ 1) {W : Submodule ℂ V}
    (hW : W ≤ centreEigenspace ρ z ε) (S : Submodule ℂ V)
    (hS : ∀ g : unitary ℂ, ∀ y ∈ S, ρ g y ∈ S) {x : V} (hx : x ∈ W ⊔ S)
    (hinv : ∀ g : unitary ℂ, ρ g x = x) : x ∈ S := by
  simpa using reducesInvariantsTo_bot_of_apply_eq_smul (σ := fun g => ρ g) z hε
    (fun v hv => mem_centreEigenspace.1 (hW hv)) S hS x hx hinv

end GlobalGaugeGroup.U1
