/-
Copyright (c) 2025 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
-/
module

public import QuantumInfo.ForMathlib.HermitianMat.Unitary

/-!

# Qubits

## i. Overview

A qubit is a two-level quantum system. In this module the computational basis of a qubit is
indexed by `Qubit`, an abbreviation for `Fin 2`, and a gate on a qubit is an element of
`𝐔[Qubit]`, the group of unitary `2 × 2` complex matrices. The standard single-qubit gates are
defined by their matrices in the computational basis, and the basic identities between them are
proved. For a unitary matrix `g` indexed by a finite type `k`, the controlled gate `C[g]` acts on
`Qubit × k`: it is the identity when the `Qubit` component, the control, is `0`, and applies `g`
when it is `1`. The CNOT gate is `C[X]`.

Most proofs use the tactic `matrix_expand`, defined at the start of the module, which reduces an
equality of small matrices to its entries and tries to close them with `simp`, `norm_num`,
`field_simp` and `ring_nf`.

## ii. Key results

- `Qubit` : the index type `Fin 2` of the computational basis of a qubit.
- `matrix_expand` : a tactic reducing an equality of small matrices to its entries and
  simplifying them.
- `Qubit.X`, `Qubit.Y`, `Qubit.Z` : the Pauli gates.
- `Qubit.H`, `Qubit.S`, `Qubit.T` : the Hadamard gate and the gates `S = diag(1, i)` and
  `T = diag(1, (1 + i) / √2)`.
- `Qubit.X_Y_anticomm`, `Qubit.Y_Z_anticomm`, `Qubit.Z_X_anticomm` : the Pauli gates
  anticommute.
- `Qubit.controllize` : the controlled gate `C[g]` of a unitary `g`.
- `Qubit.CNOT`, `Qubit.CNOT_matrix` : the CNOT gate and its `4 × 4` matrix, with `Fin 2 × Fin 2`
  reindexed by `finProdFinEquiv`.
- `Qubit.X_controllize_X` : conjugating `C[g]` by `X` on the control qubit gives
  `(1 ⊗ᵤ g) * C[g⁻¹]`.

## iii. Table of contents

- A. The qubit index type and the `matrix_expand` tactic
- B. The single-qubit gates
- C. Identities between the single-qubit gates
- D. Controlled gates

## iv. References

* M. A. Nielsen and I. L. Chuang, Quantum Computation and Quantum Information, Cambridge
  University Press (2010). [ref: nielsen_chuang_qci]

-/

@[expose] public section

/-!

## A. The qubit index type and the `matrix_expand` tactic

-/

/-- The index type of the computational basis of a qubit. -/
abbrev Qubit := Fin 2

open Lean.Parser.Tactic in
open Lean in
/--
Proves goals equating small matrices by expanding out products and simplifying standard Real
arithmetic.
-/
syntax (name := matrix_expand) "matrix_expand"
  (" [" ((simpStar <|> simpErase <|> simpLemma),*,?) "]")?
  (" with " rcasesPat+)? : tactic

macro_rules
  | `(tactic| matrix_expand $[[$rules,*]]? $[with $withArg*]?) => do
    let id1 := (withArg.getD ⟨[]⟩).getD 0 (← `(rcasesPat| _))
    let id2 := (withArg.getD ⟨[]⟩).getD 1 (← `(rcasesPat| _))
    let rules' := rules.getD ⟨#[]⟩
    `(tactic| (
      ext i j
      repeat rcases (i : Prod _ _) with ⟨i, $id1⟩
      repeat rcases (j : Prod _ _) with ⟨j, $id2⟩
      fin_cases i
      <;> fin_cases j
      <;> simp [Complex.ext_iff,
        Matrix.mul_apply, Fintype.sum_prod_type, Matrix.one_apply, field,
        $rules',* ]
      <;> norm_num
      <;> try field_simp
      <;> try ring_nf
      ))

namespace Qubit
open Real
open Complex

variable {k : Type*} [Fintype k] [DecidableEq k]

/-!

## B. The single-qubit gates

-/

/-- The Pauli Z gate on a qubit. -/
def Z : 𝐔[Qubit] :=
  ⟨!![1, 0; 0, -1], by constructor <;> matrix_expand⟩

/-- The Pauli X gate on a qubit. -/
def X : 𝐔[Qubit] :=
  ⟨!![0, 1; 1, 0], by constructor <;> matrix_expand⟩

/-- The Pauli Y gate on a qubit. -/
def Y : 𝐔[Qubit] :=
  ⟨!![0, -I; I, 0], by constructor <;> matrix_expand⟩

/-- The H gate, a Hadamard gate, on a qubit. -/
noncomputable def H : 𝐔[Qubit] :=
  ⟨√(1/2) • (!![1, 1; 1, -1]), by constructor <;> matrix_expand⟩

/-- The S gate, or Rz(π/2) rotation on a qubit. -/
def S : 𝐔[Qubit] :=
  ⟨!![1, 0; 0, I], by constructor <;> matrix_expand⟩

/-- The T gate, or Rz(π/4) rotation on a qubit. -/
noncomputable def T : 𝐔[Qubit] :=
  ⟨!![1, 0; 0, (1 + I)/√2], by constructor <;> matrix_expand⟩

/-!

## C. Identities between the single-qubit gates

-/

@[simp]
lemma Z_sq : Z * Z = 1 := by
  matrix_expand [Z]

@[simp]
lemma X_sq : X * X = 1 := by
  matrix_expand [X]

@[simp]
lemma Y_sq : Y * Y = 1 := by
  matrix_expand [Y]

@[simp]
lemma H_sq : H * H = 1 := by
  matrix_expand [H]

@[simp]
lemma S_sq : S * S = Z := by
  matrix_expand [S, Z]

@[simp]
lemma T_sq : T * T = S := by
  matrix_expand [T, S]

/-- The anticommutator `{X,Y}` is zero. Marked simp as to put Pauli products in a canonical Y-X-Z
order. -/
@[simp]
theorem X_Y_anticomm : X * Y = -Y * X := by
  matrix_expand [X, Y]

/-- The anticommutator `{Y,Z}` is zero. -/
theorem Y_Z_anticomm : Z * Y = -Y * Z := by
  matrix_expand [Z, Y]

/-- The anticommutator `{Z,X}` is zero. -/
theorem Z_X_anticomm : Z * X = -X * Z := by
  matrix_expand [Z, X]

@[simp]
lemma H_mul_X_eq_Z_mul_H : H * X = Z * H := by
  matrix_expand [H, X, Z]

@[simp]
lemma H_mul_Z_eq_X_mul_H : H * Z = X * H := by
  matrix_expand [H, X, Z]

@[simp]
lemma S_Z_comm : Z * S = S * Z := by
  simp [← S_sq, mul_assoc]

@[simp]
lemma T_Z_comm : Z * T = T * Z := by
  simp [← S_sq, ← T_sq, mul_assoc]

@[simp]
lemma S_T_comm : S * T = T * S := by
  simp [← T_sq, mul_assoc]

/-!

## D. Controlled gates

-/

/-- The controlled version `C[g]` of a unitary matrix `g` indexed by `k`, acting on `Qubit × k`:
the identity when the `Qubit` component, the control, is `0`, and `g` when it is `1`. -/
def controllize (g : 𝐔[k]) : 𝐔[Qubit × k] :=
  ⟨Matrix.of fun (q₁,t₁) (q₂,t₂) ↦
    if (q₁,q₂) = (0,0) then
      (if t₁ = t₂ then 1 else 0)
    else if (q₁,q₂) = (1,1) then
      g t₁ t₂
    else 0
    , by
      rw [Matrix.mem_unitaryGroup_iff]
      matrix_expand [-Complex.ext_iff] with ti tj;
      · congr 1
        exact propext eq_comm
      · exact congrFun₂ g.2.2 ti tj
    ⟩

/-- `C[g]` is the controlled gate `controllize g`. -/
scoped notation "C[" g "]" => controllize g

/-- Controlled-NOT gate on two qubits.
The first qubit is the control and the second qubit is the target. -/
def CNOT : 𝐔[Fin 2 × Fin 2] := C[X]

/-- The matrix representation of CNOT is the standard 4×4 permutation matrix. -/
lemma CNOT_matrix :
    Matrix.reindex finProdFinEquiv finProdFinEquiv CNOT.val =
      ![![(1:ℂ), 0, 0, 0],
        ![0, 1, 0, 0],
        ![0, 0, 0, 1],
        ![0, 0, 1, 0]] := by
        ext i j
        simp only [CNOT, Qubit.X, Matrix.reindex_apply]
        fin_cases i <;> fin_cases j <;> rfl

variable (g : 𝐔[k]) (j₁ j₂ : k)

@[simp]
lemma controllize_apply_zero_zero : C[g] (0, j₁) (0, j₂) = (1 : 𝐔[k]) j₁ j₂ := by
  rfl

@[simp]
lemma controllize_apply_zero_one : C[g] (0, j₁) (1, j₂) = 0 := by
  rfl

@[simp]
lemma controllize_apply_one_zero : C[g] (1, j₁) (0, j₂) = 0 := by
  rfl

@[simp]
lemma controllize_apply_one_one : C[g] (1, j₁) (1, j₂) = g j₁ j₂ := by
  rfl

@[simp]
lemma controllize_mul (g₁ g₂ : 𝐔[k]) : C[g₁] * C[g₂] = C[g₁ * g₂] := by
  matrix_expand

@[simp]
lemma controllize_one : C[(1 : 𝐔[k])] = 1 := by
  matrix_expand

lemma controllize_mul_inv : C[g] * C[g⁻¹] = 1 := by
  simp

open scoped Matrix in
@[simp]
lemma X_controllize_X : (X ⊗ᵤ 1) * C[g] * (X ⊗ᵤ 1) = (1 ⊗ᵤ g) * C[g⁻¹] := by
  matrix_expand [X, -Complex.ext_iff] with ki kj;
  suffices (1 : Matrix k k ℂ) ki kj = (g * g⁻¹) ki kj by
    convert! this
  simp

end Qubit
