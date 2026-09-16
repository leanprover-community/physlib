/-
Copyright (c) 2025 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
-/
module

public import QuantumInfo.Channels.Bundled
public import QuantumInfo.Channels.CPTP
public import QuantumInfo.Channels.Dual
public import QuantumInfo.Channels.MatrixMap
public import QuantumInfo.Channels.Unbundled

/-! # Fidelity between quantum states

The fidelity `F(ρ,σ) = Tr[√(√ρ σ √ρ)]` of two states. The definition here is basis-free, on
`DensityOp`; `DensityOp.fidelity_eq_matrix` and `DensityOp.fidelity_eq_traceNorm` are the matrix
analogues. -/

@[expose] public section

noncomputable section

open BigOperators
open ComplexConjugate
open Kronecker
open scoped Matrix ComplexOrder

variable {d d₂ : Type*} [Fintype d] [DecidableEq d] [Fintype d₂]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]

namespace DensityOp

/-- The fidelity of two quantum states. This is the quantum version of the Bhattacharyya
coefficient.

This makes no reference to a basis; `fidelity_eq_matrix` is the matrix analogue. -/
def fidelity (ρ σ : DensityOp E) : ℝ :=
  (σ.op.conj ρ.op.sqrt.op).sqrt.trace

variable (ρ σ : DensityOp E)

/-- **Matrix analogue of `DensityOp.fidelity`.** -/
theorem fidelity_eq_matrix {ι : Type*} [Fintype ι] [DecidableEq ι] [StdBasis ℂ E ι] :
    fidelity ρ σ = ((σ.M : HermitianMat ι ℂ).conj (ρ.M : HermitianMat ι ℂ).sqrt.mat).sqrt.trace := by
  have h : StdBasis.toMat ℂ E ι ρ.op.sqrt.op = ((ρ.M : HermitianMat ι ℂ).sqrt).mat := by
    rw [← HermitianOp.toMat_mat (ι := ι), HermitianOp.toMat_sqrt]
    rfl
  rw [fidelity, ← HermitianOp.trace_toMat (ι := ι), HermitianOp.toMat_sqrt,
    HermitianOp.toMat_conj, h]
  rfl

theorem fidelity_ge_zero : 0 ≤ fidelity ρ σ :=
  HermitianOp.trace_nonneg (HermitianOp.sqrt_nonneg _)

theorem fidelity_le_one : fidelity ρ σ ≤ 1 := by
  let _ : StdBasis ℂ E (Fin (Module.finrank ℂ E)) := StdBasis.some ℂ E
  rw [fidelity_eq_matrix (ι := Fin (Module.finrank ℂ E))]
  refine (HermitianMat.trace_sqrt_conj_sqrt_le σ.nonneg ρ.nonneg).trans_eq ?_
  rw [σ.tr, ρ.tr, Real.sqrt_one, one_mul]

/-- The fidelity, as a `Prob` probability with value between 0 and 1. -/
def fidelity_prob : Prob :=
  ⟨fidelity ρ σ, ⟨fidelity_ge_zero ρ σ, fidelity_le_one ρ σ⟩⟩

/-- A state has perfect fidelity with itself. -/
theorem fidelity_self_eq_one : fidelity ρ ρ = 1 := by
  let _ : StdBasis ℂ E (Fin (Module.finrank ℂ E)) := StdBasis.some ℂ E
  rw [fidelity_eq_matrix (ι := Fin (Module.finrank ℂ E))]
  simp only [HermitianMat.sqrt_eq_cfc_rpow_half]
  conv =>
    enter [1, 1, 1, 2]
    rw [← HermitianMat.cfc_id (ρ.M : HermitianMat _ ℂ)]
  rw [HermitianMat.cfc_conj, ← HermitianMat.cfc_comp_apply]
  convert ρ.tr using 2
  convert (ρ.M : HermitianMat _ ℂ).cfc_id using 1
  apply HermitianMat.cfc_congr_of_nonneg ρ.nonneg
  intro x hx
  simp only [one_div, Pi.mul_apply, id_eq, Pi.pow_apply]
  rw [← Real.rpow_two, Real.rpow_inv_rpow hx (by norm_num), ← sq, ← Real.rpow_two]
  exact Real.rpow_rpow_inv hx (by norm_num)

/-- The fidelity is 1 if and only if the two states are the same. -/
theorem fidelity_eq_one_iff_self : fidelity ρ σ = 1 ↔ ρ = σ := by
  refine ⟨fun h ↦ ?_, fun h ↦ h ▸ fidelity_self_eq_one ρ⟩
  let _ : StdBasis ℂ E (Fin (Module.finrank ℂ E)) := StdBasis.some ℂ E
  rw [fidelity_eq_matrix (ι := Fin (Module.finrank ℂ E))] at h
  exact (DensityOp.ext (ι := Fin (Module.finrank ℂ E))
    (HermitianMat.eq_of_trace_sqrt_conj_sqrt_eq_one σ.nonneg ρ.nonneg σ.tr ρ.tr h)).symm

/-- The fidelity is a symmetric quantity. -/
theorem fidelity_symm : fidelity ρ σ = fidelity σ ρ := by
  let _ : StdBasis ℂ E (Fin (Module.finrank ℂ E)) := StdBasis.some ℂ E
  rw [fidelity_eq_matrix (ι := Fin (Module.finrank ℂ E)),
    fidelity_eq_matrix (ι := Fin (Module.finrank ℂ E))]
  exact HermitianMat.trace_sqrt_conj_sqrt_comm σ.nonneg ρ.nonneg

/-- The fidelity of a pure state with any other state is the square root of the expectation value
of the pure state's projector, `F(∣ψ⟩⟨ψ∣, σ) = √(⟨ψ∣σ∣ψ⟩)`. -/
theorem fidelity_pure (ψ : Ket d) (σ : MState d) :
    fidelity (MState.pure ψ) σ = Real.sqrt (σ.exp_val (MState.pure ψ).M) := by
  have hP : (MState.pure ψ).M.sqrt = (MState.pure ψ).M :=
    HermitianMat.sqrt_eq_self (MState.pure ψ).nonneg (by
      rw [DensityOp.mat_M, MState.pure_mul_self]
      rfl)
  rw [fidelity_eq_matrix (ι := d), hP, MState.conj_pure,
    HermitianMat.sqrt_smul (MState.pure ψ).nonneg
      (MState.exp_val_nonneg σ (MState.pure ψ).nonneg),
    HermitianMat.trace_smul, hP, (MState.pure ψ).tr, mul_one]

/-- **Matrix analogue of `DensityOp.fidelity`** as a trace norm. -/
theorem fidelity_eq_traceNorm (ρ σ : MState d) :
    fidelity ρ σ = ((σ.M : HermitianMat d ℂ).sqrt.mat
      * (ρ.M : HermitianMat d ℂ).sqrt.mat).traceNorm := by
  rw [fidelity_eq_matrix (ι := d), HermitianMat.trace_sqrt_conj_sqrt_eq_traceNorm σ.nonneg]

open scoped MatrixOrder in
omit [DecidableEq d] in
/-- The Kraus form of the Cauchy-Schwarz bound `Matrix.re_trace_conjTranspose_mul_le_traceNorm'`,
applied to the stacked matrices `(X K₁ᴴ, X K₂ᴴ, …)` and `(Y K₁ᴴ, Y K₂ᴴ, …)`. -/
private theorem re_trace_kraus_le [DecidableEq d₂] {κ : Type*} [Fintype κ] (K : κ → Matrix d₂ d ℂ)
    (hcard : Fintype.card d₂ ≤ Fintype.card (κ × d)) (X Y : Matrix d d ℂ) :
    RCLike.re (∑ i, K i * (Xᴴ * Y) * (K i)ᴴ).trace ≤
      (CFC.sqrt (∑ i, K i * (Yᴴ * Y) * (K i)ᴴ) *
        CFC.sqrt (∑ i, K i * (Xᴴ * X) * (K i)ᴴ)).traceNorm := by
  have hstack : ∀ Z Z' : Matrix d d ℂ,
      (Matrix.stack fun i ↦ Z * (K i)ᴴ)ᴴ * (Matrix.stack fun i ↦ Z' * (K i)ᴴ)
        = ∑ i, K i * (Zᴴ * Z') * (K i)ᴴ := fun Z Z' ↦ by
    rw [Matrix.conjTranspose_stack_mul_stack]
    exact Finset.sum_congr rfl fun i _ ↦ by
      simp [Matrix.conjTranspose_mul, Matrix.mul_assoc]
  have key := Matrix.re_trace_conjTranspose_mul_le_traceNorm'
    (Matrix.stack fun i ↦ X * (K i)ᴴ) (Matrix.stack fun i ↦ Y * (K i)ᴴ) hcard
  rwa [hstack, hstack, hstack] at key

/-- The fidelity cannot decrease under the application of a channel.

Writing `Λ` in Kraus form `Λ(M) = ∑ᵢ Kᵢ M Kᵢᴴ` and letting `W` be a unitary attaining
`F(ρ,σ) = Re Tr[W √σ √ρ]`, the two stacked matrices `P = (√ρ Kᵢᴴ)ᵢ` and `Q = (W √σ Kᵢᴴ)ᵢ` satisfy
`PᴴP = Λ(ρ)`, `QᴴQ = Λ(σ)` and `Re Tr[PᴴQ] = F(ρ,σ)`, so the Cauchy-Schwarz bound
`Matrix.re_trace_conjTranspose_mul_le_traceNorm'` gives `F(ρ,σ) ≤ F(Λ ρ, Λ σ)`. -/
theorem fidelity_channel_nondecreasing [DecidableEq d₂] (ρ σ : MState d) (Λ : CPTPMap d d₂) :
    fidelity (Λ ρ) (Λ σ) ≥ fidelity ρ σ := by
  obtain ⟨K, hK⟩ := Λ.map_cp.exists_kraus _
  have hmap (M : Matrix d d ℂ) : ∑ i, K i * M * (K i)ᴴ = Λ.map M := by
    rw [hK, MatrixMap.of_kraus_apply]
  obtain ⟨W, hWinv, hW⟩ :=
    Matrix.exists_unitary_re_trace_eq_traceNorm
      ((σ.M : HermitianMat d ℂ).sqrt.mat * (ρ.M : HermitianMat d ℂ).sqrt.mat)
  have hWW : Wᴴ * W = 1 := by simpa using hWinv 1
  have hd : 0 < Fintype.card d := Fintype.card_pos_iff.mpr (MState.nonempty ρ)
  have hcard : Fintype.card d₂ ≤ Fintype.card ((d₂ × d) × d) := by
    simp only [Fintype.card_prod]
    calc Fintype.card d₂ = Fintype.card d₂ * 1 * 1 := by ring
      _ ≤ Fintype.card d₂ * Fintype.card d * Fintype.card d := by gcongr <;> omega
  have key := re_trace_kraus_le K hcard (ρ.M : HermitianMat d ℂ).sqrt.mat
    (W * (σ.M : HermitianMat d ℂ).sqrt.mat)
  have hXX : ((ρ.M : HermitianMat d ℂ).sqrt.mat)ᴴ * (ρ.M : HermitianMat d ℂ).sqrt.mat = ρ.m := by
    rw [HermitianMat.conjTranspose_mat, HermitianMat.sqrt_sq ρ.nonneg, mat_M]
  have hYY : (W * (σ.M : HermitianMat d ℂ).sqrt.mat)ᴴ * (W * (σ.M : HermitianMat d ℂ).sqrt.mat)
      = σ.m := by
    rw [Matrix.conjTranspose_mul, HermitianMat.conjTranspose_mat, Matrix.mul_assoc,
      ← Matrix.mul_assoc Wᴴ, hWW, Matrix.one_mul, HermitianMat.sqrt_sq σ.nonneg, mat_M]
  have hXY : ((ρ.M : HermitianMat d ℂ).sqrt.mat)ᴴ * (W * (σ.M : HermitianMat d ℂ).sqrt.mat)
      = (ρ.M : HermitianMat d ℂ).sqrt.mat * (W * (σ.M : HermitianMat d ℂ).sqrt.mat) := by
    rw [HermitianMat.conjTranspose_mat]
  rw [hXX, hYY, hXY, hmap, hmap, hmap, ← CPTPOp.mat_coe_eq_apply_mat,
    ← CPTPOp.mat_coe_eq_apply_mat] at key
  rw [ge_iff_le, fidelity_eq_traceNorm, fidelity_eq_traceNorm]
  refine le_trans (le_of_eq ?_) (key.trans (le_of_eq ?_))
  · rw [← hW, Λ.map_TP _]
    congr 1
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc]
    exact Matrix.trace_mul_cycle _ _ _
  · rw [← mat_M, ← mat_M, ← HermitianMat.mat_sqrt (Λ σ).nonneg,
      ← HermitianMat.mat_sqrt (Λ ρ).nonneg]

--TODO: Real.arccos ∘ fidelity forms a metric (triangle inequality), the Fubini–Study metric.
--Matches with classical (squared) Bhattacharyya coefficient
--Invariance under unitaries
--Uhlmann's theorem

end DensityOp
