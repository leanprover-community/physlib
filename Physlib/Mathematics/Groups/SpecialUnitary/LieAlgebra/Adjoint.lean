/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jinzheng Li, Nathaneal Sajan, Joseph Tooby-Smith
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.LinearAlgebra.BilinearForm.TensorProduct
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.RepresentationTheory.Intertwining
public import Physlib.Mathematics.Groups.SpecialUnitary.LieAlgebra.Basic
/-!

# The adjoint representation of `SU(n)`

The adjoint representation of `SU(n)` and its complexification, defined as `x ↦ g x g†`.

## i. Overview

We define the adjont representation of `SU(n)` on its Lie algebra `su(n)` and its complexification.
The adjoint is defined by conjugation, `x ↦ g x g†`. It preserves the bracket, and its kernel is
the centre of `SU(n)`, the scalar matrices (A).

The contraction `adjointContr` of two real adjoint indices is the trace form `x ⊗ y ↦ tr (x y)` on
`su(n)`, which is real since `x` and `y` are hermitian, and invariant under the adjoint action by
the cyclicity of the trace. It is symmetric, invariant under the bracket, and positive definite
since `tr (x x) = tr (x x†)` vanishes only for `x = 0` (B.1).

The contraction `adjointℂContr` of two complex adjoint indices is its complexification. On the
underlying matrices it is the trace form `A ⊗ B ↦ tr (A B)`, and it is again symmetric, invariant
under the bracket and nondegenerate (B.2).

## ii. Key results

- `SULieAlgebra.adjoint` : the adjoint representation on `su(n)`.
- `SULieAlgebra.adjointℂ` : the adjoint representation on the complexification.
- `SULieAlgebra.adjoint_eq_iff` : the adjoint representation is faithful modulo the centre.
- `SULieAlgebra.adjointContr` : the contraction of two real adjoint indices.
- `SULieAlgebra.adjointℂContr` : the contraction of two complex adjoint indices.
- `SULieAlgebra.adjointContr_self_pos` : the real contraction is positive definite.
- `SULieAlgebra.adjointℂContr_nondegenerate` : the complex contraction is nondegenerate.

## iii. Table of contents

- A. The adjoint representation
  - A.1. The real adjoint representation
  - A.2. The complex adjoint representation
- B. The contraction of adjoint indices
  - B.1. The real case
  - B.2. The complex case

## iv. References

* None.

-/

@[expose] public section

open Matrix TensorProduct ComplexStarModule
open scoped ComplexOrder

namespace SULieAlgebra

/-!

## A. The adjoint representation

-/

/-!

### A.1. The real adjoint representation

-/

/-- The adjoint representation `x ↦ g x g†` of `SU(n)` on its real Lie algebra `su(n)`. -/
noncomputable def adjoint {n : ℕ} :
    Representation ℝ (specialUnitaryGroup (Fin n) ℂ) (SULieAlgebra n ℂ) :=
  conj.comp (Submonoid.inclusion specialUnitaryGroup_le_unitaryGroup)

/-- The underlying matrix of `adjoint g x` is `g x g†`. -/
@[simp]
lemma adjoint_val {n : ℕ} (g : specialUnitaryGroup (Fin n) ℂ) (x : SULieAlgebra n ℂ) :
    (adjoint g x).1 = g.1 * x.1 * star g.1 := rfl

/-- The adjoint representation preserves the bracket, so `SU(n)` acts on `su(n)` by Lie algebra
  automorphisms. -/
lemma adjoint_lie {n : ℕ} (g : specialUnitaryGroup (Fin n) ℂ) (x y : SULieAlgebra n ℂ) :
    adjoint g ⁅x, y⁆ = ⁅adjoint g x, adjoint g y⁆ :=
  conj_lie _ x y

/-- The kernel of the adjoint representation is the centre of `SU(n)`: `g` acts trivially exactly
  when it is a scalar matrix `c 1`. -/
lemma adjoint_eq_one_iff {n : ℕ} (g : specialUnitaryGroup (Fin n) ℂ) :
    adjoint g = 1 ↔ ∃ c : ℂ, g.1 = c • 1 := by
  have hg := (mem_specialUnitaryGroup_iff.mp g.2).1
  constructor
  · intro h
    -- `g x g† = x` for all `x`, so `g` commutes with `su(n)` and hence with every matrix
    have hx (x : SULieAlgebra n ℂ) : Commute g.1 x.1 := by
      have hx := congrArg Subtype.val (LinearMap.congr_fun h x)
      rw [adjoint_val, Module.End.one_apply] at hx
      calc g.1 * x.1 = g.1 * x.1 * star g.1 * g.1 := by
            rw [Matrix.mul_assoc _ (star g.1), hg.1, Matrix.mul_one]
        _ = x.1 * g.1 := by rw [hx]
    have hcen : g.1 ∈ Set.center (Matrix (Fin n) (Fin n) ℂ) :=
      Semigroup.mem_center_iff.mpr fun N => (commute_of_forall_commute_val hx N).symm.eq
    rw [Matrix.center_eq_range] at hcen
    obtain ⟨c, hc⟩ := hcen
    exact ⟨c, by rw [← hc, Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]⟩
  · rintro ⟨c, hc⟩
    refine LinearMap.ext fun x => Subtype.ext ?_
    have hcomm : g.1 * x.1 = x.1 * g.1 := by
      rw [hc, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one]
    rw [adjoint_val, Module.End.one_apply, hcomm, Matrix.mul_assoc, hg.2, Matrix.mul_one]

/-- Two elements of `SU(n)` have the same adjoint action exactly when they differ by a scalar:
  the adjoint representation is faithful on `SU(n)` modulo its centre. -/
lemma adjoint_eq_iff {n : ℕ} (g h : specialUnitaryGroup (Fin n) ℂ) :
    adjoint g = adjoint h ↔ ∃ c : ℂ, g.1 = c • h.1 := by
  have hh := (mem_specialUnitaryGroup_iff.mp h.2).1
  have hval : (g * h⁻¹).1 = g.1 * star h.1 := rfl
  have key : adjoint g = adjoint h ↔ adjoint (g * h⁻¹) = 1 := by
    constructor
    · intro hgh
      rw [map_mul, hgh, ← map_mul, mul_inv_cancel, map_one]
    · intro h1
      rw [← one_mul (adjoint h), ← h1, ← map_mul, inv_mul_cancel_right]
  rw [key, adjoint_eq_one_iff, hval]
  refine exists_congr fun c => ⟨fun hc => ?_, fun hc => ?_⟩
  · rw [← Matrix.mul_one g.1, ← hh.1, ← Matrix.mul_assoc, hc, Matrix.smul_mul, Matrix.one_mul]
  · rw [hc, Matrix.smul_mul, hh.2]

/-!

### A.2. The complex adjoint representation

-/

/-- The adjoint representation of `SU(n)` on the complexification `ℂ ⊗[ℝ] su(n)`: the
  complexification of the adjoint representation `adjoint` on `su(n)`. -/
noncomputable def adjointℂ {n : ℕ} :
    Representation ℂ (specialUnitaryGroup (Fin n) ℂ) (Complexification n) :=
  (Module.End.baseChangeHom ℝ ℂ (SULieAlgebra n ℂ) : Module.End ℝ _ →* Module.End ℂ _).comp
    adjoint

@[simp]
lemma adjointℂ_tmul {n : ℕ} (g : specialUnitaryGroup (Fin n) ℂ) (z : ℂ) (x : SULieAlgebra n ℂ) :
    adjointℂ g (z ⊗ₜ x) = z ⊗ₜ adjoint g x := rfl

/-- The complex adjoint representation preserves the bracket of the complexification, so `SU(n)`
  acts on `ℂ ⊗[ℝ] su(n)` by Lie algebra automorphisms. -/
lemma adjointℂ_lie {n : ℕ} (g : specialUnitaryGroup (Fin n) ℂ) (A B : Complexification n) :
    adjointℂ g ⁅A, B⁆ = ⁅adjointℂ g A, adjointℂ g B⁆ := by
  induction A using TensorProduct.inductionOn with
  | tmul z x =>
    induction B using TensorProduct.inductionOn with
    | tmul w y =>
      rw [LieAlgebra.ExtendScalars.bracket_tmul, adjointℂ_tmul, adjointℂ_tmul, adjointℂ_tmul,
        LieAlgebra.ExtendScalars.bracket_tmul, adjoint_lie]
    | add B B' hB hB' =>
      rw [lie_add (L := Complexification n), map_add, hB, hB', map_add,
        lie_add (L := Complexification n)]
  | add A A' hA hA' =>
    rw [add_lie (L := Complexification n), map_add, hA, hA', map_add,
      add_lie (L := Complexification n)]

/-- The kernel of the complex adjoint representation is the centre of `SU(n)`, as for the real
  adjoint representation. -/
lemma adjointℂ_eq_one_iff {n : ℕ} (g : specialUnitaryGroup (Fin n) ℂ) :
    adjointℂ g = 1 ↔ ∃ c : ℂ, g.1 = c • 1 := by
  rw [← adjoint_eq_one_iff]
  refine ⟨fun h => LinearMap.ext fun x => Subtype.ext ?_, fun h => ?_⟩
  · have hx := congrArg toMatrixℂ (LinearMap.congr_fun h (1 ⊗ₜ x))
    rwa [adjointℂ_tmul, Module.End.one_apply, toMatrixℂ_tmul, toMatrixℂ_tmul, one_smul,
      one_smul] at hx
  · change Module.End.baseChangeHom ℝ ℂ _ (adjoint g) = 1
    rw [h, map_one]

/-- Two elements of `SU(n)` have the same complex adjoint action exactly when they differ by a
  scalar, as for the real adjoint representation. -/
lemma adjointℂ_eq_iff {n : ℕ} (g h : specialUnitaryGroup (Fin n) ℂ) :
    adjointℂ g = adjointℂ h ↔ ∃ c : ℂ, g.1 = c • h.1 := by
  rw [← adjoint_eq_iff]
  refine ⟨fun hgh => LinearMap.ext fun x => Subtype.ext ?_, fun hgh => ?_⟩
  · have hx := congrArg toMatrixℂ (LinearMap.congr_fun hgh (1 ⊗ₜ x))
    rwa [adjointℂ_tmul, adjointℂ_tmul, toMatrixℂ_tmul, toMatrixℂ_tmul, one_smul, one_smul] at hx
  · change Module.End.baseChangeHom ℝ ℂ _ (adjoint g) = Module.End.baseChangeHom ℝ ℂ _ (adjoint h)
    rw [hgh]

/-- The adjoint representation conjugates the matrix, `M ↦ g M g†`. -/
@[simp]
lemma toMatrixℂ_adjointℂ {n} (g : specialUnitaryGroup (Fin n) ℂ) (A : Complexification n) :
    toMatrixℂ (adjointℂ g A) = g.1 * toMatrixℂ A * star g.1 := by
  induction A using TensorProduct.inductionOn with
  | tmul z x =>
    rw [adjointℂ_tmul, toMatrixℂ_tmul, toMatrixℂ_tmul, adjoint_val, Matrix.mul_smul,
      Matrix.smul_mul]
  | add A B hA hB => rw [map_add, map_add, hA, hB, map_add, Matrix.mul_add, Matrix.add_mul]

/-- The adjoint action of a diagonal element of `SU(n)` scales the entry at `(x, y)` of the
  matrix by `d x * star (d y)`. -/
lemma toMatrixℂ_adjointℂ_apply_of_diagonal {n} {g : specialUnitaryGroup (Fin n) ℂ}
    {d : Fin n → ℂ} (hg : g.1 = diagonal d) (A : Complexification n) (x y : Fin n) :
    toMatrixℂ (adjointℂ g A) x y = d x * star (d y) * toMatrixℂ A x y := by
  rw [toMatrixℂ_adjointℂ, hg, star_eq_conjTranspose, diagonal_conjTranspose, mul_diagonal,
    diagonal_mul, Pi.star_apply]
  ring

lemma toMatrixℂ_adjointℂ_trace {n} (g : specialUnitaryGroup (Fin n) ℂ) (A : Complexification n) :
    (toMatrixℂ (adjointℂ g A)).trace = (toMatrixℂ A).trace := by
  rw [toMatrixℂ_adjointℂ, Matrix.trace_mul_cycle, Matrix.trace_mul_cycle, Matrix.mul_assoc,
    (mem_specialUnitaryGroup_iff.mp g.2).1.1, Matrix.mul_one]

/-!

## B. The contraction of adjoint indices

### B.1. The real case

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

### B.2. The complex case

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

end SULieAlgebra
