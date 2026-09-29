/-
Copyright (c) 2025 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
-/
module

public import Physlib.Meta.TODO.Basic
public import QuantumInfo.ForMathlib.HermitianMat.Unitary

/-!
Quantum theory and operations specific to qubits.
 - Standard named (single-qubit) gates: Z, X, Y, H, S, T
 - Controlled versions of gates
 - Completeness of the PPT test: a state is separable iff it is PPT.
 - Fidelity for qubits: `F(ρ,σ) = 2√(ρ.det * σ.det)`.
 - The singlet/triplet split.
-/

@[expose] public section

TODO "Improve the module doc-string of the `Qubit` file, to explain the
  current implementation."

abbrev Qubit := Fin 2

open Lean.Parser.Tactic in
open Lean in
/--
Proves goals equating small matrices by expanding out products and simpliying standard Real arithmetic.
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

@[simp]
theorem Z_sq : Z * Z = 1 := by
  matrix_expand [Z]

@[simp]
theorem X_sq : X * X = 1 := by
  matrix_expand [X]

@[simp]
theorem Y_sq : Y * Y = 1 := by
  matrix_expand [Y]

@[simp]
theorem H_sq : H * H = 1 := by
  matrix_expand [H]

@[simp]
theorem S_sq : S * S = Z := by
  matrix_expand [S, Z]

@[simp]
theorem T_sq : T * T = S := by
  matrix_expand [T, S]

/-- The anticommutator `{X,Y}` is zero. Marked simp as to put Pauli products in a canonical Y-X-Z order. -/
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
theorem H_mul_X_eq_Z_mul_H : H * X = Z * H := by
  matrix_expand [H, X, Z]

@[simp]
theorem H_mul_Z_eq_X_mul_H : H * Z = X * H := by
  matrix_expand [H, X, Z]

@[simp]
theorem S_Z_comm : Z * S = S * Z := by
  simp [← S_sq, mul_assoc]

@[simp]
theorem T_Z_comm : Z * T = T * Z := by
  simp [← S_sq, ← T_sq, mul_assoc]

@[simp]
theorem S_T_comm : S * T = T * S := by
  simp [← T_sq, mul_assoc]

/-- Given a unitary `U` on some Hilbert space `k`, we have the controllized version that acts on `Fin 2 ⊗ k`
where `U` is conditionally applied if the first qubit is `1`. -/
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
theorem controllize_apply_zero_zero : C[g] (0, j₁) (0, j₂) = (1 : 𝐔[k]) j₁ j₂ := by
  rfl

@[simp]
theorem controllize_apply_zero_one : C[g] (0, j₁) (1, j₂) = 0 := by
  rfl

@[simp]
theorem controllize_apply_one_zero : C[g] (1, j₁) (0, j₂) = 0 := by
  rfl

@[simp]
theorem controllize_apply_one_one : C[g] (1, j₁) (1, j₂) = g j₁ j₂ := by
  rfl

@[simp]
theorem controllize_mul (g₁ g₂ : 𝐔[k]) : C[g₁] * C[g₂] = C[g₁ * g₂] := by
  matrix_expand

@[simp]
theorem controllize_one : C[(1 : 𝐔[k])] = 1 := by
  matrix_expand

@[simp]
theorem controllize_mul_inv : C[g] * C[g⁻¹] = 1 := by
  simp

open scoped Matrix in
@[simp]
theorem X_controllize_X : (X ⊗ᵤ 1) * C[g] * (X ⊗ᵤ 1) = (1 ⊗ᵤ g) * C[g⁻¹] := by
  matrix_expand [X, -Complex.ext_iff] with ki kj;
  suffices (1 : Matrix k k ℂ) ki kj = (g * g⁻¹) ki kj by
    convert! this
  simp

end Qubit
