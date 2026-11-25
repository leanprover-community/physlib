/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import PhyslibAlpha.Mathematics.RepresentationTheory.Sl2.Casimir
public import Physlib.Mathematics.ForMathlib.DataStructures.Matrix.LieTrace
/-!
# The standard sl₂ triple

The matrices `e`, `f`, `h` of `sl(2, ℂ)`, and the vanishing of their images on the generalized
kernel of the Casimir.

## i. Overview

Three operators `H`, `E`, `F` satisfying the `sl₂` relations `[H, E] = 2E`, `[H, F] = -2F` and
`[E, F] = H` all vanish on the generalized kernel of their Casimir `H² + 2H + 4FE` (A). This is
the operator form of `PhyslibAlpha.Mathematics.RepresentationTheory.Sl2.Casimir`.

The standard triple `sl2E`, `sl2F`, `sl2H` of `2 × 2` matrices spans the traceless matrices (B).
For a map `φ` out of the `2 × 2` matrices preserving brackets, its Casimir `sl2Casimir φ` is the
Casimir of the images of the triple, and on its generalized kernel `φ` vanishes on every
traceless matrix (C).

## ii. Key results

- `Module.End.apply_eq_zero_of_sl2_relations` : operators with the `sl₂` relations vanish on the
  generalized kernel of their Casimir.
- `Matrix.sl2E`, `Matrix.sl2F`, `Matrix.sl2H` : the standard `sl₂` triple.
- `Matrix.eq_sl2_of_trace_eq_zero` : a traceless matrix is a combination of the triple.
- `Matrix.sl2Casimir` : the Casimir of the images of the triple.
- `Matrix.apply_eq_zero_of_mem_maxGenEigenspace_sl2Casimir` : on the generalized kernel of the
  Casimir a bracket-preserving map vanishes on traceless matrices.

## iii. Table of contents

- A. Operators satisfying the sl₂ relations
- B. The standard sl₂ triple
- C. Images of the triple

## iv. References

- J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*.

-/

@[expose] public section

open Matrix Polynomial

attribute [local instance 100] LieRing.ofAssociativeRing

/-!

## A. Operators satisfying the sl₂ relations

-/

namespace Module.End

variable {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

/-- Three endomorphisms `H`, `E`, `F` satisfying the `sl₂` relations all vanish on the generalized
kernel of their Casimir `H² + 2H + 4FE`. -/
lemma apply_eq_zero_of_sl2_relations {H E F : Module.End ℂ V} (hHE : H * E - E * H = 2 • E)
    (hHF : H * F - F * H = -(2 • F)) (hEF : E * F - F * E = H) {v : V}
    (hv : v ∈ (H * H + 2 • H + 4 • (F * E)).maxGenEigenspace 0) :
    E v = 0 ∧ F v = 0 ∧ H v = 0 := by
  by_cases hH : H = 0
  · subst hH
    simp only [zero_mul, mul_zero, sub_zero, zero_eq_neg] at hHE hHF
    have hE : (2 : ℂ) • E = 0 := by rw [two_smul, ← two_nsmul, ← hHE]
    have hF : (2 : ℂ) • F = 0 := by rw [two_smul, ← two_nsmul, hHF]
    simp [(smul_eq_zero.mp hE).resolve_left two_ne_zero,
      (smul_eq_zero.mp hF).resolve_left two_ne_zero]
  · have t : IsSl2Triple H E F := ⟨hH, hEF, hHE, hHF⟩
    have hC : IsSl2Triple.casimir ℂ V H E F = H * H + 2 • H + 4 • (F * E) := by
      ext w
      simp [IsSl2Triple.casimir]
    simpa using t.lie_eq_zero_of_mem_maxGenEigenspace (M := V) (hC ▸ hv)

/-- The linear map underlying a continuous linear map on a finite-dimensional space acts as it
does. -/
lemma toContinuousLinearMap_symm_apply {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [FiniteDimensional ℂ E] (A : E →L[ℂ] E) (w : E) :
    (Module.End.toContinuousLinearMap E).symm A w = A w :=
  rfl

end Module.End

/-!

## B. The standard sl₂ triple

-/

namespace Matrix

/-- The raising element `e` of the standard `sl₂` triple of `2 × 2` matrices. -/
def sl2E : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 0, 0]

/-- The lowering element `f` of the standard `sl₂` triple of `2 × 2` matrices. -/
def sl2F : Matrix (Fin 2) (Fin 2) ℂ := !![0, 0; 1, 0]

/-- The Cartan element `h` of the standard `sl₂` triple of `2 × 2` matrices. -/
def sl2H : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, -1]

/-- The bracket `[h, e] = 2 e`. -/
lemma lie_sl2H_sl2E : ⁅sl2H, sl2E⁆ = ((2 : ℝ) : ℂ) • sl2E := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [sl2H, sl2E, Ring.lie_def]
  norm_num

/-- The bracket `[h, f] = -2 f`. -/
lemma lie_sl2H_sl2F : ⁅sl2H, sl2F⁆ = ((-2 : ℝ) : ℂ) • sl2F := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [sl2H, sl2F, Ring.lie_def]
  norm_num

/-- The bracket `[e, f] = h`. -/
lemma lie_sl2E_sl2F : ⁅sl2E, sl2F⁆ = sl2H := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [sl2H, sl2E, sl2F, Ring.lie_def]

/-- A traceless `2 × 2` matrix is a complex combination of the standard `sl₂` triple. -/
lemma eq_sl2_of_trace_eq_zero {X : Matrix (Fin 2) (Fin 2) ℂ} (htr : X.trace = 0) :
    X = X 0 1 • sl2E + X 1 0 • sl2F + X 0 0 • sl2H := by
  rw [trace_fin_two] at htr
  ext i j
  fin_cases i <;> fin_cases j <;> simp [sl2H, sl2E, sl2F]
  linear_combination htr

end Matrix

/-!

## C. Images of the triple

-/

namespace Matrix

variable {B : Type*} [Ring B] [Algebra ℂ B]

/-- The Casimir `H² + 2H + 4FE` of the images `H`, `E`, `F` of the standard `sl₂` triple under a
map `φ` into an algebra. -/
def sl2Casimir (φ : Matrix (Fin 2) (Fin 2) ℂ → B) : B :=
  φ sl2H * φ sl2H + 2 • φ sl2H + 4 • (φ sl2F * φ sl2E)

/-- The images of the standard `sl₂` triple under a map preserving brackets and real multiples
satisfy the `sl₂` relations. -/
lemma sl2_relations {φ : Matrix (Fin 2) (Fin 2) ℂ → B} (hlie : ∀ X Y, ⁅φ X, φ Y⁆ = φ ⁅X, Y⁆)
    (hsmul : ∀ (r : ℝ) X, φ ((r : ℂ) • X) = (r : ℂ) • φ X) :
    φ sl2H * φ sl2E - φ sl2E * φ sl2H = 2 • φ sl2E ∧
      φ sl2H * φ sl2F - φ sl2F * φ sl2H = -(2 • φ sl2F) ∧
      φ sl2E * φ sl2F - φ sl2F * φ sl2E = φ sl2H := by
  refine ⟨?_, ?_, ?_⟩
  · rw [← Ring.lie_def, hlie, lie_sl2H_sl2E, hsmul]
    simp [two_smul]
  · rw [← Ring.lie_def, hlie, lie_sl2H_sl2F, hsmul]
    simp [two_smul]
  · rw [← Ring.lie_def, hlie, lie_sl2E_sl2F]

/-- The Casimir of a map whose values lie in a subspace closed under multiplication lies in that
subspace. -/
lemma sl2Casimir_mem {φ : Matrix (Fin 2) (Fin 2) ℂ → B} {S : Submodule ℂ B}
    (hS : ∀ a ∈ S, ∀ b ∈ S, a * b ∈ S) (hφ : ∀ X, φ X ∈ S) : sl2Casimir φ ∈ S :=
  add_mem (add_mem (hS _ (hφ _) _ (hφ _)) (S.smul_of_tower_mem 2 (hφ _)))
    (S.smul_of_tower_mem 4 (hS _ (hφ _) _ (hφ _)))

omit [Algebra ℂ B] in
/-- The Casimirs of two maps with commuting values commute. -/
lemma commute_sl2Casimir {φ χ : Matrix (Fin 2) (Fin 2) ℂ → B}
    (h : ∀ X Y, Commute (φ X) (χ Y)) : Commute (sl2Casimir φ) (sl2Casimir χ) := by
  have hφ (Y) : Commute (sl2Casimir φ) (χ Y) :=
    (((h _ Y).mul_left (h _ Y)).add_left ((h _ Y).smul_left 2)).add_left
      (((h _ Y).mul_left (h _ Y)).smul_left 4)
  exact ((hφ _).mul_right (hφ _)).add_right ((hφ _).smul_right 2) |>.add_right
    (((hφ _).mul_right (hφ _)).smul_right 4)

/-- A map from `2 × 2` matrices, additive and scaling each matrix by some complex number, which
kills a vector on the standard `sl₂` triple, kills it on every traceless matrix. -/
lemma apply_eq_zero_of_sl2 {V : Type*} [AddCommGroup V] [Module ℂ V]
    {φ : Matrix (Fin 2) (Fin 2) ℂ → Module.End ℂ V} (hadd : ∀ X Y, φ (X + Y) = φ X + φ Y)
    (hsmul : ∀ (c : ℂ) X, ∃ c' : ℂ, φ (c • X) = c' • φ X) {v : V} (hE : φ sl2E v = 0)
    (hF : φ sl2F v = 0) (hH : φ sl2H v = 0) {X : Matrix (Fin 2) (Fin 2) ℂ} (htr : X.trace = 0) :
    φ X v = 0 := by
  obtain ⟨a, ha⟩ := hsmul (X 0 1) sl2E
  obtain ⟨b, hb⟩ := hsmul (X 1 0) sl2F
  obtain ⟨c, hc⟩ := hsmul (X 0 0) sl2H
  rw [eq_sl2_of_trace_eq_zero htr, hadd, hadd, ha, hb, hc]
  simp [hE, hF, hH]

/-- On the generalized kernel of the Casimir of a map preserving brackets and real multiples, the
images of the standard `sl₂` triple vanish. -/
lemma apply_eq_zero_of_mem_maxGenEigenspace_sl2Casimir {V : Type*} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] {φ : Matrix (Fin 2) (Fin 2) ℂ → Module.End ℂ V}
    (hlie : ∀ X Y, ⁅φ X, φ Y⁆ = φ ⁅X, Y⁆) (hsmul : ∀ (r : ℝ) X, φ ((r : ℂ) • X) = (r : ℂ) • φ X)
    {v : V} (hv : v ∈ (sl2Casimir φ).maxGenEigenspace 0) :
    φ sl2E v = 0 ∧ φ sl2F v = 0 ∧ φ sl2H v = 0 :=
  have h := sl2_relations hlie hsmul
  Module.End.apply_eq_zero_of_sl2_relations h.1 h.2.1 h.2.2 hv

end Matrix
