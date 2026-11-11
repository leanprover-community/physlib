/-
Copyright (c) 2026 Gregory J. Loges. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregory J. Loges
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Physlib.Mathematics.KroneckerDelta.Basic
/-!

# Wave Vector Space

## i. Overview

In this module we define the type `WaveVectorSpace d` corresponding to the `d`-dimensional
space of (angular) wave vectors in `Space d`.

In contrast to `Space d`, `WaveVectorSpace d` has a distinguished zero;
the purpose of this file is to define this zero, the structure of a `Module`
on `WaveVectorSpace d`, and the structure of a real `InnerProductSpace` on `WaveVectorSpace d`,
none of which requires any non-canonical choices.

`WaveVectorSpace d` is implemented as a structure with a field `val : Fin d → ℝ`
rather than as an `abbrev` of `EuclideanSpace ℝ (Fin d)` or a `def` of a type with value
`EuclideanSpace ℝ (Fin d)` for the same reasons as for `Space d`;
see `Physlib.SpaceAndTime.Space.Basic` for a discussion of the (dis)advantages of each.

## ii. Key results

- `WaveVectorSpace d` : the space of wave vectors in `Space d`
- `instModuleReal` : `WaveVectorSpace d` is a module over `ℝ`
- `instInnerProductSpaceReal` : `WaveVectorSpace d` is a real inner product space
- `equivEuclideanSpace` : the linear isometric equivalence between `WaveVectorSpace d` and `ℝᵈ`

## iii. Table of contents

- A. The `WaveVectorSpace` type
- B. Instances on `WaveVectorSpace`
  - B.1. Coercion to functions
  - B.2. Subsingleton for `d = 0`
  - B.3. Zero
  - B.4. Additive commutative group
  - B.5. Module over `ℝ`
  - B.6. Inner product space
- C. Linear isometric equivalence with `ℝᵈ`
  - C.1. Standard basis
  - C.2. Coordinate functions

## iv. References

-/

@[expose] public section

/-!
## A. The `WaveVectorSpace` type
-/

/-- The type `WaveVectorSpace d` is the real vector space which corresponds to `d`-dimensional
(angular) wave vectors in `Space d` with a given (but arbitrary) choice of inverse length unit.

The default value of `d` is `3`. Thus `WaveVectorSpace = WaveVectorSpace 3`-/
structure WaveVectorSpace (d : ℕ := 3) where
  /-- The underlying map `Fin d → ℝ` associated with a vector in `WaveVectorSpace`. -/
  val : Fin d → ℝ

namespace WaveVectorSpace

variable {d : ℕ}

lemma eq_of_val {k₁ k₂ : WaveVectorSpace d} (h : k₁.val = k₂.val) : k₁ = k₂ := by
  cases k₁
  congr

@[simp]
lemma val_eq_iff {k₁ k₂ : WaveVectorSpace d} : k₁.val = k₂.val ↔ k₁ = k₂ :=
  ⟨eq_of_val, congrArg val⟩

/-!
## B. Instances on `WaveVectorSpace`
-/

/-!
### B.1. Coercion to functions
-/

instance : CoeFun (WaveVectorSpace d) (fun _ ↦ Fin d → ℝ) where
  coe k := k.val

@[ext]
lemma eq_of_apply {k₁ k₂ : WaveVectorSpace d} (h : ∀ i, k₁ i = k₂ i) : k₁ = k₂ := by
  apply eq_of_val
  funext i
  exact h i

/-!
### B.2. Subsingleton for `d = 0`
-/

instance : Subsingleton (WaveVectorSpace 0) where
  allEq _ _ := eq_of_apply fun i ↦ Fin.elim0 i

/-!
### B.3. Zero
-/

instance : Zero (WaveVectorSpace d) where
  zero := ⟨0⟩

@[simp]
lemma zero_val : (0 : WaveVectorSpace d).val = 0 := rfl

/-!
### B.4. Additive commutative group
-/

section AddCommGroup

variable (k k₁ k₂ : WaveVectorSpace d)

instance : Add (WaveVectorSpace d) where
  add k₁ k₂ := ⟨k₁.val + k₂.val⟩

@[simp]
lemma add_val : (k₁ + k₂).val = k₁.val + k₂.val := rfl

instance : Sub (WaveVectorSpace d) where
  sub k₁ k₂ := ⟨k₁.val - k₂.val⟩

@[simp]
lemma sub_val : (k₁ - k₂).val = k₁.val - k₂.val := rfl

instance : Neg (WaveVectorSpace d) where
  neg k := ⟨-k.val⟩

@[simp]
lemma neg_val : (-k).val = -k.val := rfl

instance : AddCommGroup (WaveVectorSpace d) where
  add_assoc _ _ _ := by ext; simp [add_assoc]
  zero_add _ := by ext; simp
  add_zero _ := by ext; simp
  nsmul := nsmulRec
  zsmul := zsmulRec
  neg_add_cancel _ := by ext; simp
  add_comm _ _ := by ext; simp [add_comm]

end AddCommGroup

/-!
### B.5. Module over `ℝ`
-/

instance : SMul ℝ (WaveVectorSpace d) where
  smul c k := ⟨c • k.val⟩

@[simp]
lemma smul_val (c : ℝ) (k : WaveVectorSpace d) : (c • k).val = c • k.val := rfl

instance instModuleReal : Module ℝ (WaveVectorSpace d) where
  mul_smul _ _ _ := by ext; simp [mul_assoc]
  one_smul _ := by ext; simp
  smul_zero _ := by ext; simp
  smul_add _ _ _ := by ext; simp [mul_add]
  add_smul _ _ _ := by ext; simp [add_mul]
  zero_smul _ := by ext; simp

/-!
### B.6. Inner product space
-/

section InnerProduct

open scoped RealInnerProductSpace

instance : Inner ℝ (WaveVectorSpace d) where
  inner k₁ k₂ := ∑ i, k₁ i * k₂ i

lemma inner_apply (k₁ k₂ : WaveVectorSpace d) : ⟪k₁, k₂⟫ = ∑ i, k₁ i * k₂ i := rfl

instance : InnerProductSpace.Core ℝ (WaveVectorSpace d) where
  conj_inner_symm _ _ := by simp [inner_apply, mul_comm]
  re_inner_nonneg k := Fintype.sum_nonneg fun i ↦ mul_self_nonneg (k i)
  add_left _ _ _ := by simp [inner_apply, add_mul, Finset.sum_add_distrib]
  smul_left _ _ _ := by simp [inner_apply, mul_assoc, Finset.mul_sum]
  definite _ h := by
    apply eq_of_apply
    apply (Fintype.sum_eq_zero_iff_of_nonneg fun i ↦ by simp [mul_self_nonneg]).mp at h
    simpa using congrFun h

noncomputable instance instNormedAddCommGroup : NormedAddCommGroup (WaveVectorSpace d) :=
  instCoreReal.toNormedAddCommGroup

noncomputable instance instInnerProductSpaceReal : InnerProductSpace ℝ (WaveVectorSpace d) :=
  InnerProductSpace.ofCore instCoreReal.toCore

lemma norm_eq (k : WaveVectorSpace d) : ‖k‖ = √(∑ i, k i ^ 2) := by
  simp_rw [norm_eq_sqrt_real_inner, inner_apply, pow_two]

lemma norm_sq_eq (k : WaveVectorSpace d) : ‖k‖ ^ 2 = ∑ i, k i ^ 2 := by
  simp_rw [← real_inner_self_eq_norm_sq, inner_apply, pow_two]

end InnerProduct

/-!
## C. Linear isometric equivalence with `ℝᵈ`
-/

/-- The linear isometric equivalence between `WaveVectorSpace d` and `ℝᵈ`. -/
def equivEuclideanSpace : WaveVectorSpace d ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d) where
  toFun k := WithLp.toLp 2 k.val
  map_add' _ _ := WithLp.toLp_add 2 _ _
  map_smul' _ _ := WithLp.toLp_smul 2 _ _
  invFun v := ⟨v.ofLp⟩
  norm_map' _ := by simp [norm_eq, EuclideanSpace.norm_eq]

@[simp]
lemma equivEuclideanSpace_apply (k : WaveVectorSpace d) (i : Fin d) :
    equivEuclideanSpace k i = k i :=
  rfl

@[simp]
lemma equivEuclideanSpace_symm_apply (v : EuclideanSpace ℝ (Fin d)) (i : Fin d) :
    equivEuclideanSpace.symm v i = v i :=
  rfl

@[simp]
lemma finrank_waveVectorSpace : Module.finrank ℝ (WaveVectorSpace d) = d :=
  equivEuclideanSpace.toLinearEquiv.finrank_eq ▸ finrank_euclideanSpace_fin

/-!
### C.1. Standard basis
-/

section Basis

variable (k : WaveVectorSpace d) (v : EuclideanSpace ℝ (Fin d)) (i j : Fin d)

/-- The standard basis of `WaveVectorSpace d`. -/
def basis : OrthonormalBasis (Fin d) ℝ (WaveVectorSpace d) where
  repr := equivEuclideanSpace

@[simp]
lemma basis_repr_apply : basis.repr k i = k i := rfl

@[simp]
lemma basis_repr_symm_apply : basis.repr.symm v i = v i := rfl

@[simp]
lemma basis_apply : basis i j = δ[i,j] := by rcases eq_or_ne i j <;> simp_all [basis]

@[simp high]
lemma inner_basis : inner ℝ k (basis i) = k i := by
  simp only [inner_apply, basis_apply, mul_comm, ← nsmul_eq_mul, KroneckerDelta.sum_smul]

@[simp high]
lemma basis_inner : inner ℝ (basis i) k = k i := by
  simp only [inner_apply, basis_apply, ← nsmul_eq_mul, KroneckerDelta.sum_smul]

instance : FiniteDimensional ℝ (WaveVectorSpace d) := basis.toBasis.finiteDimensional_of_finite

end Basis

/-!
### C.2. Coordinate functions
-/

noncomputable section Coord

open scoped ContDiff

variable {n : ℕ∞ω} (i : Fin d) (k : WaveVectorSpace d)

/-- The standard coordinate functions of `WaveVectorSpace` based on `Fin d`. -/
def coord : ℝ := inner ℝ k (basis i)

lemma coord_apply : k.coord i = k i := by simp [coord]

/-- The standard coordinate functions of `WaveVectorSpace` based on `Fin d`,
as a continuous linear map. -/
def coordCLM : WaveVectorSpace d →L[ℝ] ℝ where
  toFun := coord i
  map_add' _ _ := by simp [coord_apply]
  map_smul' _ _ := by simp [coord_apply]
  cont := by
    change Continuous (fun k ↦ inner ℝ k (basis i))
    fun_prop

lemma coordCLM_apply : coordCLM i k = k.coord i := rfl

@[fun_prop]
lemma coord_contDiff : ContDiff ℝ n (coord i) := (coordCLM i).contDiff

@[fun_prop]
lemma val_contDiff : ContDiff ℝ n (val · i) := by
  convert (coordCLM i).contDiff
  simp [coordCLM_apply, coord_apply]

end Coord

end WaveVectorSpace
