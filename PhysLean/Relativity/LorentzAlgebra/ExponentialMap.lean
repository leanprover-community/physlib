/-
Copyright (c) 2025 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
import Mathlib.Analysis.Normed.Field.Instances
import PhysLean.Mathematics.DataStructures.Matrix.LieTrace
import PhysLean.Relativity.LorentzAlgebra.Basic
import PhysLean.Relativity.LorentzGroup.Restricted.Basic

/-!
# Exponential map from the Lorentz algebra to the restricted Lorentz group

In 1+3 Minkowski space with metric η, the Lie algebra `lorentzAlgebra` exponentiates
onto the proper orthochronous Lorentz group (`LorentzGroup.restricted 3`). We prove:
* exp_mem_lorentzGroup : `NormedSpace.exp ℝ A.1 ∈ LorentzGroup 3` (η-preserving).
* exp_transpose_of_mem_algebra : `exp (A.1ᵀ) = η * exp (−A.1) * η`.
* exp_isProper : `det (exp A) = 1`.
* exp_isOrthochronous : `(exp A)₀₀ ≥ 1`.
Hence `exp A ∈ LorentzGroup.restricted 3`.
-/

open Matrix
open minkowskiMatrix

attribute [local instance] Matrix.linftyOpNormedAlgebra
attribute [local instance] Matrix.linftyOpNormedRing
attribute [local instance] Matrix.instCompleteSpace

noncomputable section

namespace lorentzAlgebra

/--
A key property of a Lorentz algebra element `A` is that its transpose
is related to its conjugation by the Minkowski metric η.
-/
lemma transpose_eq_neg_eta_conj (A : lorentzAlgebra) :
    A.1ᵀ = - (η * A.1 * η) := by
  have h := lorentzAlgebra.transpose_eta A
  calc
    A.1ᵀ = A.1ᵀ * 1 := by rw [mul_one]
    _ = A.1ᵀ * (η * η) := by rw [minkowskiMatrix.sq]
    _ = (A.1ᵀ * η) * η := by rw [mul_assoc]
    _ = (-η * A.1) * η := by rw [h]
    _ = - (η * A.1 * η) := by simp_all only [neg_mul]

/--
The exponential of the transpose of a Lorentz algebra element.
This connects `exp(Aᵀ)` to a conjugation of `exp(-A)`.
-/
lemma exp_transpose_of_mem_algebra (A : lorentzAlgebra) :
    NormedSpace.exp (A.1ᵀ) = η * (NormedSpace.exp (-A.1)) * η := by
  rw [transpose_eq_neg_eta_conj A]
  let P_gl : GL (Fin 1 ⊕ Fin 3) ℝ :=
    { val := η,
      inv := η,
      val_inv := minkowskiMatrix.sq,
      inv_val := minkowskiMatrix.sq }
  rw [show -(η * A.1 * η) = η * (-A.1) * η by noncomm_ring]
  erw [NormedSpace.exp_units_conj P_gl (-A.1)]
  rfl

/--
The exponential of an element of the Lorentz algebra is a member of the Lorentz group.
-/
theorem exp_mem_lorentzGroup (A : lorentzAlgebra) : NormedSpace.exp A.1 ∈ LorentzGroup 3 := by
  rw [LorentzGroup.mem_iff_transpose_mul_minkowskiMatrix_mul_self]
  rw [← Matrix.exp_transpose]
  rw [exp_transpose_of_mem_algebra A]
  calc
    (η * NormedSpace.exp (-A.1) * η) * η * NormedSpace.exp A.1
    _ = η * NormedSpace.exp (-A.1) * (η * η) * NormedSpace.exp A.1 := by noncomm_ring
    _ = η * NormedSpace.exp (-A.1) * 1 * NormedSpace.exp A.1 := by rw [minkowskiMatrix.sq]
    _ = η * NormedSpace.exp (-A.1 + A.1) := by
                                            rw [mul_one, mul_assoc, NormedSpace.exp_add_of_commute]
                                            exact Commute.neg_left rfl
    _ = η * NormedSpace.exp 0 := by rw [neg_add_cancel]
    _ = η * 1 := by rw [NormedSpace.exp_zero]
    _ = η := by rw [mul_one]

open Matrix Complex
open minkowskiMatrix

noncomputable section

attribute [local instance] Matrix.linftyOpNormedAlgebra
instance [UniformSpace 𝕂] : UniformSpace (Matrix m n 𝕂) := by unfold Matrix; infer_instance

/-- The trace of a matrix equals the sum of its diagonal elements. -/
lemma trace_eq_sum_diagonal (A : Matrix (Fin 1 ⊕ Fin 3) (Fin 1 ⊕ Fin 3) ℝ) :
    trace A = ∑ i, A i i := rfl

/-- The trace of any element of the Lorentz algebra is zero. -/
lemma trace_of_mem_is_zero (A : lorentzAlgebra) : trace A.1 = 0 := by
  rw [trace_eq_sum_diagonal]
  have h_diag_zero : ∀ μ, A.1 μ μ = 0 := lorentzAlgebra.diag_comp A
  simp [h_diag_zero]

namespace Matrix

variable {n R ι : Type*} [Fintype n]-- [DecidableEq n]

@[simp]
lemma trace_reindex [Semiring R] [Fintype ι] (e : n ≃ ι) (A : Matrix n n R) :
    trace (A.submatrix e.symm e.symm) = trace A := by
  simp only [trace, diag_apply, submatrix_apply]
  exact e.symm.sum_comp (fun i : n => A i i)

variable {n R ι : Type*} [Fintype n] [DecidableEq n]

@[simp]
lemma exp_reindex {k : Type*}
    [RCLike k] [Fintype ι] [DecidableEq ι] (e : n ≃ ι) (A : Matrix n n k) :
    NormedSpace.exp (A.submatrix e.symm e.symm) = reindex e e (NormedSpace.exp A) := by
  let f := reindexAlgEquiv k k e
  have h_cont : Continuous f := f.toLinearEquiv.continuous_of_finiteDimensional
  exact (NormedSpace.map_exp f.toAlgHom h_cont A).symm

end Matrix

open Matrix
noncomputable section

attribute [local instance] Matrix.linftyOpNormedAlgebra

/-- The exponential of an element of the Lorentz algebra is proper (has determinant 1). -/
theorem exp_isProper (A : lorentzAlgebra) :
    LorentzGroup.IsProper ⟨NormedSpace.exp A.1, exp_mem_lorentzGroup A⟩ := by
  simp only [LorentzGroup.IsProper]
  let e : (Fin 1 ⊕ Fin 3) ≃ Fin 4 := finSumFinEquiv
  -- we reindex to Fin 4 to use the faster LinearOrder
  rw [← det_reindex_self e, ← exp_reindex e]
  convert det_exp_real (reindex e e A.1)
  erw [trace_reindex e, trace_of_mem_is_zero A, Real.exp_zero]

/-- The exponential of an element of the Lorentz algebra is orthochronous. -/
theorem exp_isOrthochronous (A : lorentzAlgebra) :
    LorentzGroup.IsOrthochronous ⟨NormedSpace.exp A.1, exp_mem_lorentzGroup A⟩ := by
  -- The Lie algebra is a vector space, so there is a path from 0 to A.
  let γ : Path (0 : lorentzAlgebra) A :=
  { toFun := fun t => t.val • A,
    continuous_toFun := by
      apply Continuous.smul
      · exact continuous_subtype_val
      · exact continuous_const,
    source' := by simp [zero_smul],
    target' := by simp [one_smul] }
  let exp_γ : Path (1 : LorentzGroup 3) ⟨NormedSpace.exp A.1, exp_mem_lorentzGroup A⟩ :=
  { toFun := fun t => ⟨NormedSpace.exp (γ t).val, exp_mem_lorentzGroup (γ t)⟩,
    continuous_toFun := by
      apply Continuous.subtype_mk
      apply Continuous.comp
      · apply NormedSpace.exp_continuous
      · exact Continuous.comp continuous_subtype_val (γ.continuous_toFun),
    source' := by
      ext i j
      simp only [γ]
      simp [NormedSpace.exp_zero],
    target' := by
      ext i j
      simp only [γ]
      simp}
  have h_joined : Joined (1 : LorentzGroup 3) ⟨NormedSpace.exp A.1, exp_mem_lorentzGroup A⟩ :=
    ⟨exp_γ⟩
  have h_connected : ⟨NormedSpace.exp A.1, exp_mem_lorentzGroup A⟩ ∈ connectedComponent
      (1 : LorentzGroup 3) :=
    pathComponent_subset_component _ h_joined
  rw [← LorentzGroup.isOrthochronous_on_connected_component h_connected]
  exact LorentzGroup.id_isOrthochronous

/-- The exponential of an element of the Lorentz algebra is a member of the
restricted Lorentz group. -/
theorem exp_mem_restricted_lorentzGroup (A : lorentzAlgebra) :
    (⟨NormedSpace.exp A.1, exp_mem_lorentzGroup A⟩ : LorentzGroup 3) ∈
    LorentzGroup.restricted 3 := by
  exact ⟨exp_isProper A, exp_isOrthochronous A⟩
