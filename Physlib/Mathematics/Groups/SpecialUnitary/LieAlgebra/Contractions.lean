/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jinzheng Li, Nathaneal Sajan, Joseph Tooby-Smith
-/
module

public import Mathlib.LinearAlgebra.BilinearForm.TensorProduct
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Physlib.Mathematics.Groups.SpecialUnitary.LieAlgebra.Adjoint
/-!

# The contraction of adjoint indices of `SU(n)`

The trace form on `su(n)` and on its complexification, and the invariant bilinear forms.

## i. Overview

The contraction `adjointContr` of two real adjoint indices is the trace form `x ⊗ y ↦ tr (x y)` on
`su(n)`, which is real since `x` and `y` are hermitian, and invariant under the adjoint action by
the cyclicity of the trace. It is symmetric, invariant under the bracket, and positive definite
since `tr (x x) = tr (x x†)` vanishes only for `x = 0` (A.1).

The contraction `adjointℂContr` of two complex adjoint indices is its complexification. On the
underlying matrices it is the trace form `A ⊗ B ↦ tr (A B)`, and it is again symmetric, invariant
under the bracket and nondegenerate (A.2).

Every bilinear form on the complexification is the contraction against an endomorphism, which
commutes with the adjoint action if the form is invariant. By Schur's lemma such an endomorphism is
a scalar, so every `SU(n)`-invariant bilinear form on the complexification is a multiple of the
contraction (B).

## ii. Key results

- `SULieAlgebra.adjointContr` : the contraction of two real adjoint indices.
- `SULieAlgebra.adjointℂContr` : the contraction of two complex adjoint indices.
- `SULieAlgebra.adjointContr_self_pos` : the real contraction is positive definite.
- `SULieAlgebra.adjointℂContr_nondegenerate` : the complex contraction is nondegenerate.
- `SULieAlgebra.intertwiningMap_eq_smul_adjointℂContr` : every intertwiner `adj ⊗ adj → ℂ` is a
  multiple of the complex contraction.

## iii. Table of contents

- A. The contraction of adjoint indices
  - A.1. The real case
  - A.2. The complex case
- B. Invariant bilinear forms

## iv. References

* None.

-/

@[expose] public section

open Matrix TensorProduct ComplexStarModule
open scoped ComplexOrder

namespace SULieAlgebra

/-!

## A. The contraction of adjoint indices

### A.1. The real case

-/

/-- The contraction of two real adjoint indices: the trace form `x ⊗ y ↦ tr (x y)` on `su(n)`,
  which is real since `x` and `y` are hermitian. -/
noncomputable def adjointContr {n : ℕ} : ((adjoint (n := n)).tprod adjoint).IntertwiningMap
    (Representation.trivial ℝ (specialUnitaryGroup (Fin n) ℂ) ℝ) where
  toLinearMap := TensorProduct.lift <|
    LinearMap.mk₂ ℝ (fun x y : SULieAlgebra n ℂ => (x.1 * y.1).trace.re)
      (fun x x' y => by simp [add_mul, trace_add])
      (fun r x y => by simp)
      (fun x y y' => by simp [mul_add, trace_add])
      (fun r x y => by simp)
  isIntertwining' g := TensorProduct.ext' fun x y => by
    have hg : star g.1 * g.1 = 1 := (mem_specialUnitaryGroup_iff.mp g.2).1.1
    simp only [LinearMap.comp_apply, Representation.tprod_apply, TensorProduct.map_tmul,
      Representation.trivial_apply, lift.tmul, LinearMap.mk₂_apply, adjoint_val]
    rw [show g.1 * x.1 * star g.1 * (g.1 * y.1 * star g.1) = g.1 * (x.1 * y.1) * star g.1 by
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc (star g.1), hg, Matrix.one_mul],
      Matrix.trace_mul_cycle, hg, Matrix.one_mul]

/-- The real contraction is the real part of the trace, `x ⊗ y ↦ re tr (x y)`. -/
@[simp]
lemma adjointContr_tmul {n : ℕ} (x y : SULieAlgebra n ℂ) :
    adjointContr (x ⊗ₜ y) = (x.1 * y.1).trace.re := rfl

/-- The adjoint representation preserves the real contraction, so `SU(n)` acts on `su(n)` by
  isometries. -/
lemma adjointContr_adjoint {n : ℕ} (g : specialUnitaryGroup (Fin n) ℂ) (x y : SULieAlgebra n ℂ) :
    adjointContr (adjoint g x ⊗ₜ adjoint g y) = adjointContr (x ⊗ₜ y) :=
  Representation.IntertwiningMap.isIntertwining _ _ adjointContr g (x ⊗ₜ y)

/-- The trace `tr (x y)` of two elements of `su(n)` is real, equal to their contraction. -/
lemma ofReal_adjointContr_tmul {n : ℕ} (x y : SULieAlgebra n ℂ) :
    (adjointContr (x ⊗ₜ y) : ℂ) = (x.1 * y.1).trace := by
  rw [adjointContr_tmul]
  refine Complex.conj_eq_iff_re.1 ?_
  change star (x.1 * y.1).trace = _
  rw [← trace_conjTranspose, conjTranspose_mul, ← star_eq_conjTranspose,
    ← star_eq_conjTranspose, x.star_val_eq, y.star_val_eq, trace_mul_comm]

lemma adjointContr_symm {n : ℕ} (x y : SULieAlgebra n ℂ) :
    adjointContr (x ⊗ₜ y) = adjointContr (y ⊗ₜ x) := by
  rw [adjointContr_tmul, adjointContr_tmul, trace_mul_comm]

/-- The real contraction is invariant under the bracket, `tr (⁅x, y⁆ z) = tr (x ⁅y, z⁆)`; in terms
  of generators, the structure constants `tr (T^a ⁅T^b, T^c⁆)` are totally antisymmetric. -/
lemma adjointContr_lie {n : ℕ} (x y z : SULieAlgebra n ℂ) :
    adjointContr (⁅x, y⁆ ⊗ₜ z) = adjointContr (x ⊗ₜ ⁅y, z⁆) := by
  rw [adjointContr_tmul, adjointContr_tmul, val_bracket, val_bracket, Matrix.smul_mul,
    Matrix.mul_smul, trace_smul, trace_smul, sub_mul, mul_sub, trace_sub, trace_sub,
    Matrix.mul_assoc, Matrix.mul_assoc, trace_mul_comm y.1 (x.1 * z.1), Matrix.mul_assoc]

/-- The real contraction is positive semidefinite: `tr (x x) = tr (x x†) ≥ 0`. -/
lemma adjointContr_self_nonneg {n : ℕ} (x : SULieAlgebra n ℂ) : 0 ≤ adjointContr (x ⊗ₜ x) := by
  have h := (posSemidef_self_mul_conjTranspose x.1).trace_nonneg
  rw [← star_eq_conjTranspose, x.star_val_eq, ← ofReal_adjointContr_tmul] at h
  exact Complex.zero_le_real.mp h

/-- The real contraction of `x` with itself vanishes only for `x = 0`. -/
lemma adjointContr_self_eq_zero_iff {n : ℕ} (x : SULieAlgebra n ℂ) :
    adjointContr (x ⊗ₜ x) = 0 ↔ x = 0 := by
  refine ⟨fun hx => Subtype.ext (trace_mul_conjTranspose_self_eq_zero_iff.mp ?_),
    fun hx => by rw [hx, zero_tmul, map_zero]⟩
  rw [← star_eq_conjTranspose, x.star_val_eq, ← ofReal_adjointContr_tmul, hx, Complex.ofReal_zero]

/-- The real contraction is positive definite, making it an inner product on `su(n)`. -/
lemma adjointContr_self_pos {n : ℕ} {x : SULieAlgebra n ℂ} (hx : x ≠ 0) :
    0 < adjointContr (x ⊗ₜ x) :=
  (adjointContr_self_nonneg x).lt_of_ne fun h => hx ((adjointContr_self_eq_zero_iff x).mp h.symm)

lemma adjointContr_separating_left {n : ℕ} (x : SULieAlgebra n ℂ)
    (hx : ∀ y, adjointContr (x ⊗ₜ y) = 0) : x = 0 :=
  (adjointContr_self_eq_zero_iff x).mp (hx x)

lemma adjointContr_separating_right {n : ℕ} (y : SULieAlgebra n ℂ)
    (hy : ∀ x, adjointContr (x ⊗ₜ y) = 0) : y = 0 :=
  adjointContr_separating_left y fun x => by rw [adjointContr_symm, hy]

/-- The real contraction separates `su(n)`: `y ↦ (x ↦ re tr (x y))` is injective. -/
lemma adjointContr_flip_injective {n : ℕ} :
    Function.Injective (TensorProduct.curry (adjointContr (n := n)).toLinearMap).flip := by
  intro w w' h
  refine sub_eq_zero.1 (adjointContr_separating_right _ fun x => ?_)
  have hx := LinearMap.congr_fun h x
  simp only [LinearMap.flip_apply, TensorProduct.curry_apply] at hx
  rw [tmul_sub, map_sub, sub_eq_zero]
  exact hx

/-- The real contraction, as a bilinear form, is symmetric. -/
lemma adjointContr_isSymm {n : ℕ} :
    LinearMap.BilinForm.IsSymm (TensorProduct.curry (adjointContr (n := n)).toLinearMap) :=
  ⟨fun x y => adjointContr_symm x y⟩

/-- The real contraction, as a bilinear form, is nondegenerate. -/
lemma adjointContr_nondegenerate {n : ℕ} :
    (TensorProduct.curry (adjointContr (n := n)).toLinearMap).Nondegenerate :=
  ⟨fun x hx => adjointContr_separating_left x hx, fun y hy => adjointContr_separating_right y hy⟩

/-!

### A.2. The complex case

-/

/-- The contraction of two complex adjoint indices: the complexification of the real contraction
  `adjointContr`. -/
noncomputable def adjointℂContr {n : ℕ} : ((adjointℂ (n := n)).tprod adjointℂ).IntertwiningMap
    (Representation.trivial ℂ (specialUnitaryGroup (Fin n) ℂ) ℂ) where
  toLinearMap := TensorProduct.lift <| LinearMap.BilinForm.baseChange ℂ <|
    TensorProduct.curry (adjointContr (n := n)).toLinearMap
  isIntertwining' g := TensorProduct.ext' fun A B => by
    simp only [LinearMap.comp_apply, Representation.tprod_apply, TensorProduct.map_tmul,
      Representation.trivial_apply]
    induction A using TensorProduct.inductionOn with
    | tmul z x =>
      induction B using TensorProduct.inductionOn with
      | tmul w y =>
        simp only [adjointℂ_tmul, lift.tmul, LinearMap.BilinForm.baseChange_tmul,
          TensorProduct.curry_apply, Representation.IntertwiningMap.toLinearMap_apply,
          adjointContr_adjoint]
      | add B B' hB hB' => rw [map_add, tmul_add, map_add, hB, hB', tmul_add, map_add]
    | add A A' hA hA' => rw [map_add, add_tmul, map_add, hA, hA', add_tmul, map_add]

/-- The adjoint representation preserves the complex contraction. -/
lemma adjointℂContr_adjointℂ {n : ℕ} (g : specialUnitaryGroup (Fin n) ℂ)
    (A B : Complexification n) :
    adjointℂContr (adjointℂ g A ⊗ₜ adjointℂ g B) = adjointℂContr (A ⊗ₜ B) := by
  have h := Representation.IntertwiningMap.isIntertwining _ _ (adjointℂContr (n := n)) g (A ⊗ₜ B)
  simpa only [Representation.tprod_apply, TensorProduct.map_tmul, Representation.trivial_apply]
    using h

/-- The contraction is the trace form, `A ⊗ B ↦ tr (A B)`. -/
lemma adjointℂContr_tmul (A B : Complexification n) :
    adjointℂContr (A ⊗ₜ B) = (toMatrixℂ A * toMatrixℂ B).trace := by
  induction A using TensorProduct.inductionOn with
  | tmul z x =>
    induction B using TensorProduct.inductionOn with
    | tmul w y =>
      change TensorProduct.lift _ ((z ⊗ₜ x) ⊗ₜ (w ⊗ₜ y)) = _
      rw [lift.tmul, LinearMap.BilinForm.baseChange_tmul, TensorProduct.curry_apply,
        Representation.IntertwiningMap.toLinearMap_apply, Complex.real_smul,
        ofReal_adjointContr_tmul, toMatrixℂ_tmul, toMatrixℂ_tmul, Matrix.smul_mul,
        Matrix.mul_smul, trace_smul, trace_smul, smul_eq_mul, smul_eq_mul]
      ring
    | add B B' hB hB' => rw [tmul_add, map_add, hB, hB', map_add, Matrix.mul_add, trace_add]
  | add A A' hA hA' => rw [add_tmul, map_add, hA, hA', map_add, Matrix.add_mul, trace_add]

/-- On the real elements `1 ⊗ x` of the complexification the complex contraction is the real
  contraction, so the two agree on real gauge fields. -/
lemma adjointℂContr_one_tmul {n : ℕ} (x y : SULieAlgebra n ℂ) :
    adjointℂContr ((1 ⊗ₜ x) ⊗ₜ (1 ⊗ₜ y)) = adjointContr (x ⊗ₜ y) := by
  rw [adjointℂContr_tmul, toMatrixℂ_tmul, toMatrixℂ_tmul, one_smul, one_smul,
    ofReal_adjointContr_tmul]

lemma adjointℂContr_symm {n} (A B : Complexification n) :
    adjointℂContr (A ⊗ₜ B) = adjointℂContr (B ⊗ₜ A) := by
  rw [adjointℂContr_tmul, adjointℂContr_tmul, Matrix.trace_mul_comm]

/-- The complex contraction is invariant under the bracket, `tr (⁅A, B⁆ C) = tr (A ⁅B, C⁆)`. -/
lemma adjointℂContr_lie {n} (A B C : Complexification n) :
    adjointℂContr (⁅A, B⁆ ⊗ₜ C) = adjointℂContr (A ⊗ₜ ⁅B, C⁆) := by
  rw [adjointℂContr_tmul, adjointℂContr_tmul, toMatrixℂ_lie, toMatrixℂ_lie, Matrix.smul_mul,
    Matrix.mul_smul, trace_smul, trace_smul, sub_mul, mul_sub, trace_sub, trace_sub,
    Matrix.mul_assoc, Matrix.mul_assoc, trace_mul_comm (toMatrixℂ B) (toMatrixℂ A * toMatrixℂ C),
    Matrix.mul_assoc]

lemma adjointℂContr_separating_left {n} (A : Complexification n)
    (hA : ∀ B, adjointℂContr (A ⊗ₜ B) = 0) : A = 0 := by
  have h := hA (ofTracelessℂ (toMatrixℂ A)ᴴ
    (by rw [trace_conjTranspose, trace_toMatrixℂ, star_zero]))
  rw [adjointℂContr_tmul, toMatrixℂ_ofTracelessℂ, trace_mul_conjTranspose_self_eq_zero_iff] at h
  exact toMatrixℂ_injective (h.trans (map_zero _).symm)

lemma adjointℂContr_separating_right {n} (B : Complexification n)
    (hB : ∀ A, adjointℂContr (A ⊗ₜ B) = 0) : B = 0 :=
  adjointℂContr_separating_left B fun A => by rw [adjointℂContr_symm, hB]

/-- The contraction separates the complexification: `B ↦ (A ↦ tr (A B))` is injective. -/
lemma adjointℂContr_flip_injective :
    Function.Injective (TensorProduct.curry (adjointℂContr (n := n)).toLinearMap).flip := by
  intro w w' h
  refine sub_eq_zero.1 (adjointℂContr_separating_right _ fun A => ?_)
  have hA := LinearMap.congr_fun h A
  simp only [LinearMap.flip_apply, TensorProduct.curry_apply] at hA
  rw [tmul_sub, map_sub, sub_eq_zero]
  exact hA

/-- The complex contraction, as a bilinear form, is symmetric. -/
lemma adjointℂContr_isSymm {n : ℕ} :
    LinearMap.BilinForm.IsSymm (TensorProduct.curry (adjointℂContr (n := n)).toLinearMap) :=
  ⟨fun A B => adjointℂContr_symm A B⟩

/-- The complex contraction, as a bilinear form, is nondegenerate. -/
lemma adjointℂContr_nondegenerate {n : ℕ} :
    (TensorProduct.curry (adjointℂContr (n := n)).toLinearMap).Nondegenerate :=
  ⟨fun A hA => adjointℂContr_separating_left A hA,
    fun B hB => adjointℂContr_separating_right B hB⟩

/-!

## B. Invariant bilinear forms

-/

/-- Every bilinear form on the complexification is the contraction against an endomorphism,
  the contraction being nondegenerate. -/
lemma exists_eq_adjointℂContr_tmul {n : ℕ}
    (B : Complexification n ⊗[ℂ] Complexification n →ₗ[ℂ] ℂ) :
    ∃ T : Module.End ℂ (Complexification n), ∀ A C, B (A ⊗ₜ C) = adjointℂContr (T A ⊗ₜ C) :=
  ⟨(LinearMap.BilinForm.toDual _ adjointℂContr_nondegenerate).symm.toLinearMap ∘ₗ curry B,
    fun A C => (LinearMap.BilinForm.apply_toDual_symm_apply
      (hB := adjointℂContr_nondegenerate) (curry B A) C).symm⟩

/-- The endomorphism representing an invariant bilinear form commutes with the adjoint
  action. -/
lemma adjointℂ_comp_eq_of_adjointℂContr_tmul {n : ℕ}
    (B : ((adjointℂ (n := n)).tprod adjointℂ).IntertwiningMap
      (Representation.trivial ℂ (specialUnitaryGroup (Fin n) ℂ) ℂ))
    {T : Module.End ℂ (Complexification n)} (hT : ∀ A C, B (A ⊗ₜ C) = adjointℂContr (T A ⊗ₜ C))
    (g : specialUnitaryGroup (Fin n) ℂ) :
    T ∘ₗ adjointℂ g = adjointℂ g ∘ₗ T := by
  have hB (A C : Complexification n) : B (adjointℂ g A ⊗ₜ adjointℂ g C) = B (A ⊗ₜ C) := by
    simpa only [Representation.tprod_apply, TensorProduct.map_tmul,
      Representation.trivial_apply] using Representation.IntertwiningMap.isIntertwining _ _ B g
        (A ⊗ₜ C)
  refine LinearMap.ext fun A => sub_eq_zero.1 (adjointℂContr_separating_left _ fun C => ?_)
  rw [sub_tmul, map_sub, sub_eq_zero, LinearMap.comp_apply, LinearMap.comp_apply, ← hT,
    ← Representation.self_inv_apply adjointℂ g C, hB, hT, adjointℂContr_adjointℂ]

/-- Every intertwiner `adj ⊗ adj → ℂ` is a multiple of the contraction: up to scale, the
  contraction is the unique `SU(n)`-invariant bilinear form on the complexification. -/
lemma intertwiningMap_eq_smul_adjointℂContr {n : ℕ}
    (B : ((adjointℂ (n := n)).tprod adjointℂ).IntertwiningMap
      (Representation.trivial ℂ (specialUnitaryGroup (Fin n) ℂ) ℂ)) :
    ∃ z : ℂ, B = z • adjointℂContr := by
  obtain ⟨T, hT⟩ := exists_eq_adjointℂContr_tmul B.toLinearMap
  obtain ⟨μ, hμ⟩ :=
    end_eq_smul_id_of_commute_adjointℂ (adjointℂ_comp_eq_of_adjointℂContr_tmul B hT)
  refine ⟨μ, Representation.IntertwiningMap.ext (TensorProduct.ext' fun A C => ?_)⟩
  rw [hT, hμ, LinearMap.smul_apply, LinearMap.id_apply, ← smul_tmul', map_smul]
  rfl

end SULieAlgebra
