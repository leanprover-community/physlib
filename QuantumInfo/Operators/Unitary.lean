/-
Copyright (c) 2025 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg, Rodolfo Soldati
-/
module

public import QuantumInfo.States.Mixed.MState

/-! # Unitary evolution of quantum states

This file is about the action of a unitary on a state, by conjugation. The basis-free version
`DensityOp.uConj` takes a unitary operator; `MState.uConj`, notated `U ◃ ρ`, is the matrix
analogue, taking a unitary matrix (`Matrix.unitaryGroup`).

This is imported by `CPTPMap` to define things like unitary channels, Kraus operators, and
complementary channels, so this file itself does not discuss channels yet. -/

@[expose] public section

noncomputable section

open RealInnerProductSpace
open InnerProductSpace

namespace DensityOp

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]

/-- Conjugate a state by a unitary operator (applying the unitary as an evolution). -/
def uConj (ρ : DensityOp E) (U : unitary (E →L[ℂ] E)) : DensityOp E where
  op := ρ.op.conj U.val
  op_nonneg := HermitianOp.conj_nonneg ρ.op_nonneg U.val
  op_trace := by rw [HermitianOp.trace_conj_unitary, ρ.op_trace]

@[simp]
theorem uConj_op (ρ : DensityOp E) (U : unitary (E →L[ℂ] E)) :
    (ρ.uConj U).op = ρ.op.conj U.val :=
  rfl

/-- **Matrix analogue of `DensityOp.uConj`.** -/
@[simp]
theorem uConj_M {ι : Type*} [Fintype ι] [DecidableEq ι] [StdBasis ℂ E ι] (ρ : DensityOp E)
    (U : unitary (E →L[ℂ] E)) :
    ((ρ.uConj U).M : HermitianMat ι ℂ) = (ρ.M : HermitianMat ι ℂ).conj
      (StdBasis.toMatUnitary (ι := ι) U).val :=
  HermitianOp.toMat_conj_unitary ρ.op U

end DensityOp

namespace MState

variable {d d₁ d₂ d₃ : Type*}
variable [Fintype d] [Fintype d₁] [Fintype d₂] [Fintype d₃]
variable [DecidableEq d]
variable {ψ φ f : Ket d}

/-- Conjugate a state by a unitary matrix (applying the unitary as an evolution). -/
def uConj (ρ : MState d) (U : 𝐔[d]) : MState d :=
  DensityOp.uConj ρ (StdBasis.unitaryOfMat U)

/-- `MState.uConj`, the action of a unitary on a mixed state by conjugation.
The ◃ notation comes from the theory of racks and quandles, where this is a
conjugation-like operation. -/
scoped[MState] notation:80 U:80 " ◃ " ρ:81 => MState.uConj ρ U

@[simp]
theorem uConj_M (ρ : MState d) (U : 𝐔[d]) : (U ◃ ρ).M = ρ.M.conj U.val := by
  rw [uConj, DensityOp.uConj_M, StdBasis.toMatUnitary_unitaryOfMat]

@[simp]
theorem uConj_m (ρ : MState d) (U : 𝐔[d]) :
    (U ◃ ρ).m = U.val * ρ.m * U.val.conjTranspose := by
  rw [← DensityOp.mat_M, uConj_M, HermitianMat.conj_apply_mat, DensityOp.mat_M]

set_option backward.isDefEq.respectTransparency false in
/-- You might think this should only be true up to permutation, so that it would read like
`∃ σ : Equiv.Perm d, (ρ.uConj U).spectrum = ρ.spectrum.relabel σ`. But since eigenvalues
of a matrix are always canonically sorted, this is actually an equality.
-/
@[simp]
theorem uConj_spectrum_eq (ρ : MState d) (U : 𝐔[d]) :
    (ρ.uConj U).spectrum = ρ.spectrum := by
  simp [spectrum]

@[simp]
theorem inner_uConj (ρ σ : MState d) (U : 𝐔[d]) : ⟪U ◃ ρ, U ◃ σ⟫_Prob = ⟪ρ, σ⟫_Prob := by
  simp [inner_def]

/-- The **No-cloning theorem**, saying that if states `ψ` and `φ` can both be perfectly cloned
using a unitary `U` and a fiducial state `f`, and they aren't identical (their inner product is
less than 1), then the two states must be orthogonal to begin with. In short: only orthogonal
states can be simultaneously cloned. -/
theorem no_cloning {U : 𝐔[d × d]}
    (hψ : U ◃ pure (ψ ⊗ᵠ f) = pure (ψ ⊗ᵠ ψ))
    (hφ : U ◃ pure (φ ⊗ᵠ f) = pure (φ ⊗ᵠ φ))
    (H : ⟪pure ψ, pure φ⟫_Prob < (1 : ℝ)) :
    ⟪pure ψ, pure φ⟫_Prob = (0 : ℝ) := by
  have hff : ⟪pure f, pure f⟫_Prob = 1 := (pure_iff_purity_one _).mp ⟨f, rfl⟩
  -- Cloning turns the overlap into its own square: `x * x = x`.
  have key : ⟪pure ψ, pure φ⟫_Prob * ⟪pure ψ, pure φ⟫_Prob = ⟪pure ψ, pure φ⟫_Prob := by
    rw [← prod_inner_prod, ← pure_prod_pure, ← pure_prod_pure, ← hψ, ← hφ, inner_uConj,
      pure_prod_pure, pure_prod_pure, prod_inner_prod, hff, mul_one]
  have hx : (⟪pure ψ, pure φ⟫_Prob : ℝ) * ⟪pure ψ, pure φ⟫_Prob = ⟪pure ψ, pure φ⟫_Prob := by
    exact_mod_cast congrArg Subtype.val key
  nlinarith [hx, H, (Prob.zero_le_coe : (0:ℝ) ≤ ⟪pure ψ, pure φ⟫_Prob)]

end MState
