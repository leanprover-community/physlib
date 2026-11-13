/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import PhyslibAlpha.ClassicalFieldTheory.GaugeTheory.GlobalGaugeGroup.Basic
public import PhyslibAlpha.SpaceAndTime.SpaceTime.SpaceTimeAlgebra.Matrix
public import PhyslibAlpha.SpaceAndTime.SpaceTime.SpaceTimeAlgebra.Taylor
/-!
# The Lie algebra jets of a global gauge group

The Taylor series at a point of the infinitesimal gauge transformations.

## i. Overview

An infinitesimal gauge transformation of a global gauge group `G` with Lie algebra `𝔤` is a
smooth map from spacetime into `𝔤`. Its jet at the base point is a matrix of formal power
series in the spacetime coordinates, all of whose base-point derivatives `∂_s A (0)` lie in
`𝔤`. These Lie algebra jets form a Lie algebra under the commutator, since by the Leibniz
rule each base-point derivative of a commutator is a sum of commutators of base-point
derivatives.

Membership is checked through `mem_jetLieAlgebra_of`: a property of matrices of jets that is
preserved by every derivative, and that places the value in `𝔤`, places every base-point
derivative in `𝔤`. This is how the gauge jets are shown to act on the Lie algebra jets in
`PhyslibAlpha.ClassicalFieldTheory.GaugeTheory.GlobalGaugeGroup.GaugeJetGroup`.

## ii. Key results

- `GlobalGaugeGroup.jetLieAlgebra` : the Lie algebra jets, as a real subspace.
- `GlobalGaugeGroup.mem_jetLieAlgebra_iff` : a matrix of jets is a Lie algebra jet exactly
  when its value lies in the Lie algebra and its derivatives are Lie algebra jets.
- `GlobalGaugeGroup.mem_jetLieAlgebra_of` : the induction principle for Lie algebra jets.
- `GlobalGaugeGroup.jetLieSubalgebra` : the Lie algebra jets, as a Lie subalgebra.

## iii. Table of contents

- A. The Lie algebra jets
- B. Closure properties

## iv. References

* None.

-/

@[expose] public section

open Matrix MvPowerSeries SpaceTimeAlgebra

attribute [local instance 100] LieRing.ofAssociativeRing

namespace GlobalGaugeGroup

variable {κ : Type} [Fintype κ] [DecidableEq κ] (G : GlobalGaugeGroup κ)

/-!

## A. The Lie algebra jets

-/

/-- The real subspace of matrices of jets all of whose base-point derivatives lie in the
  Lie algebra. -/
def jetLieAlgebra : Submodule ℝ (Matrix κ κ SpaceTimeAlgebra) where
  carrier := {A | ∀ s, derivValueMatrix s A ∈ G.lieAlgebra}
  add_mem' hA hB s := by
    rw [derivValueMatrix_add]
    exact add_mem (hA s) (hB s)
  zero_mem' s := by
    rw [derivValueMatrix_zero_right]
    exact G.lieAlgebra.zero_mem
  smul_mem' r A hA s := by
    rw [derivValueMatrix_real_smul]
    exact G.lieAlgebra.smul_mem r (hA s)

lemma mem_jetLieAlgebra {A : Matrix κ κ SpaceTimeAlgebra} :
    A ∈ G.jetLieAlgebra ↔ ∀ s, derivValueMatrix s A ∈ G.lieAlgebra := Iff.rfl

/-- A matrix of jets is a Lie algebra jet exactly when its value lies in the Lie algebra and
  its derivatives are Lie algebra jets. -/
lemma mem_jetLieAlgebra_iff {A : Matrix κ κ SpaceTimeAlgebra} :
    A ∈ G.jetLieAlgebra ↔
      (constantCoeff : SpaceTimeAlgebra →+* ℂ).mapMatrix A ∈ G.lieAlgebra ∧
        ∀ μ, A.map (pderiv μ) ∈ G.jetLieAlgebra := by
  refine ⟨fun hA => ⟨hA 0, fun μ s => derivValueMatrix_cons μ s A ▸ hA (μ ::ₘ s)⟩,
    fun ⟨h0, hd⟩ s => ?_⟩
  induction s using Multiset.induction_on with
  | empty => exact h0
  | cons μ t _ => exact (derivValueMatrix_cons μ t A).symm ▸ hd μ t

/-- An induction principle for Lie algebra jets: a property of matrices of jets that is
  preserved by every derivative, and that forces the value into the Lie algebra, forces
  every base-point derivative into the Lie algebra. -/
lemma mem_jetLieAlgebra_of {P : Matrix κ κ SpaceTimeAlgebra → Prop}
    (h0 : ∀ A, P A → (constantCoeff : SpaceTimeAlgebra →+* ℂ).mapMatrix A ∈ G.lieAlgebra)
    (hd : ∀ A, P A → ∀ μ, P (A.map (pderiv μ))) {A : Matrix κ κ SpaceTimeAlgebra}
    (hA : P A) : A ∈ G.jetLieAlgebra := by
  intro s
  induction s using Multiset.induction_on generalizing A with
  | empty => exact h0 A hA
  | cons μ t ih => exact (derivValueMatrix_cons μ t A).symm ▸ ih (hd A hA μ)

/-!

## B. Closure properties

-/

lemma map_pderiv_mem_jetLieAlgebra {A : Matrix κ κ SpaceTimeAlgebra}
    (hA : A ∈ G.jetLieAlgebra) (μ : Fin 1 ⊕ Fin 3) : A.map (pderiv μ) ∈ G.jetLieAlgebra :=
  (G.mem_jetLieAlgebra_iff.1 hA).2 μ

/-- The Lie algebra jets are closed under the commutator: by the Leibniz rule each
  base-point derivative of a commutator is a sum of commutators of base-point derivatives. -/
lemma commutator_mem_jetLieAlgebra {A B : Matrix κ κ SpaceTimeAlgebra}
    (hA : A ∈ G.jetLieAlgebra) (hB : B ∈ G.jetLieAlgebra) : A * B - B * A ∈ G.jetLieAlgebra := by
  intro s
  induction s using Multiset.induction_on generalizing A B with
  | empty =>
    rw [derivValueMatrix_zero, map_sub, map_mul, map_mul]
    exact commutator_mem_lieAlgebraOfIsClosed (hA 0) (hB 0)
  | cons μ t ih =>
    rw [derivValueMatrix_cons, map_pderiv_commutator, derivValueMatrix_add]
    exact add_mem (ih (G.map_pderiv_mem_jetLieAlgebra hA μ) hB)
      (ih hA (G.map_pderiv_mem_jetLieAlgebra hB μ))

/-- The Lie algebra jets, as a Lie subalgebra of matrices of jets under the commutator. -/
def jetLieSubalgebra : LieSubalgebra ℝ (Matrix κ κ SpaceTimeAlgebra) where
  toSubmodule := G.jetLieAlgebra
  lie_mem' hA hB := by
    rw [Ring.lie_def]
    exact G.commutator_mem_jetLieAlgebra hA hB

@[simp]
lemma mem_jetLieSubalgebra {A : Matrix κ κ SpaceTimeAlgebra} :
    A ∈ G.jetLieSubalgebra ↔ A ∈ G.jetLieAlgebra := Iff.rfl

noncomputable instance : LieRing G.jetLieSubalgebra := inferInstance

noncomputable instance : LieAlgebra ℝ G.jetLieSubalgebra := inferInstance

/-- A constant matrix in the Lie algebra is a Lie algebra jet. -/
lemma mapMatrix_C_mem_jetLieAlgebra {a : Matrix κ κ ℂ} (ha : a ∈ G.lieAlgebra) :
    (C : ℂ →+* SpaceTimeAlgebra).mapMatrix a ∈ G.jetLieAlgebra := by
  refine G.mem_jetLieAlgebra_iff.2 ⟨?_, fun μ => ?_⟩
  · convert ha
    ext i j
    simp [RingHom.mapMatrix_apply, constantCoeff_C]
  · rw [map_pderiv_mapMatrix_C]
    exact G.jetLieAlgebra.zero_mem

/-- The Lie algebra jets are closed under multiplication by a coordinate. -/
lemma X_smul_mem_jetLieAlgebra (μ : Fin 1 ⊕ Fin 3) {A : Matrix κ κ SpaceTimeAlgebra}
    (hA : A ∈ G.jetLieAlgebra) : (X μ : SpaceTimeAlgebra) • A ∈ G.jetLieAlgebra := by
  refine G.mem_jetLieAlgebra_of (P := fun D => ∃ A ∈ G.jetLieAlgebra, ∃ B ∈ G.jetLieAlgebra,
      D = (X μ : SpaceTimeAlgebra) • A + B)
    ?_ ?_ ⟨A, hA, 0, G.jetLieAlgebra.zero_mem, (add_zero _).symm⟩
  · rintro _ ⟨A, -, B, hB, rfl⟩
    have h : (constantCoeff : SpaceTimeAlgebra →+* ℂ).mapMatrix
        ((X μ : SpaceTimeAlgebra) • A) = 0 := by
      ext i j
      simp [RingHom.mapMatrix_apply, Matrix.map_apply]
    rw [map_add, h, zero_add]
    exact hB 0
  · rintro _ ⟨A, hA, B, hB, rfl⟩ ν
    refine ⟨A.map (pderiv ν), G.map_pderiv_mem_jetLieAlgebra hA ν,
      (if ν = μ then A else 0) + B.map (pderiv ν),
      add_mem (by split_ifs <;> simp [hA]) (G.map_pderiv_mem_jetLieAlgebra hB ν), ?_⟩
    ext i j
    by_cases h : ν = μ
    · subst h
      simp [Matrix.map_apply, Derivation.leibniz, pderiv_X_self]
      ring
    · simp [Matrix.map_apply, Derivation.leibniz, pderiv_X_of_ne (Ne.symm h), h]

end GlobalGaugeGroup
