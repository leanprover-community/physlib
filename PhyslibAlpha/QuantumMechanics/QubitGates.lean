/-
Copyright (c) 2026 Daniel Leonforte. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Leonforte
-/
module

public import QuantumInfo.States.Pure.Qubit

/-!

# Real rotations of a qubit and multiplexed gates

The rotation `Ry` of a qubit given by its cosine and sine, and gates controlled by the value of a
register.

## i. Overview

For real `c`, `s` with `c² + s² = 1` the matrix `!![c, -s; s, c]` is a unitary gate on a qubit,
`ry c s h`. With `c = cos (θ/2)` and `s = sin (θ/2)` it is the rotation by `θ` about the `y`-axis;
giving it by `c` and `s` avoids trigonometric functions when the entries are square roots.

For a family of unitary gates `g r` on `k`, indexed by the values `r` of a register `ι`, the
multiplexed gate `multiplex g` on `ι × k` applies `g r` when the register is in the state `|r⟩`:
`Σ_r |r⟩⟨r| ⊗ g r`. Up to the order of the factors it is the block-diagonal matrix
`Matrix.blockDiagonal` of the `g r`, which is unitary since each block is.

## ii. Key results

- `ry`: the rotation `!![c, -s; s, c]` as a unitary gate for `c² + s² = 1`.
- `blockDiagonal_mem_unitaryGroup`: a block-diagonal matrix of unitary blocks is unitary.
- `multiplex`, `multiplex_apply`: the gate `Σ_r |r⟩⟨r| ⊗ g r` and its entries.

## iii. Table of contents

- A. The rotation `Ry`
- B. Multiplexed gates

## iv. References

- The gates and the notation `𝐔[·]` are those of `QuantumInfo.States.Pure.Qubit`.

## A. The rotation `Ry`

-/

@[expose] public section

noncomputable section

namespace PhyslibAlpha.Qubit

open Matrix

/-- The rotation `!![c, -s; s, c]` of a qubit, for real `c`, `s` with `c² + s² = 1`. -/
def ry (c s : ℝ) (h : c ^ 2 + s ^ 2 = 1) : 𝐔[Qubit] :=
  ⟨!![(c : ℂ), -s; s, c], by
    rw [mem_unitaryGroup_iff]
    have h' : (c : ℂ) ^ 2 + (s : ℂ) ^ 2 = 1 := by exact_mod_cast h
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, ← pow_two, h'] <;>
      first | linear_combination h' | ring⟩

lemma ry_apply (c s : ℝ) (h : c ^ 2 + s ^ 2 = 1) :
    (ry c s h : Matrix Qubit Qubit ℂ) = !![(c : ℂ), -s; s, c] := rfl

/-!

## B. Multiplexed gates

-/

variable {ι k : Type*} [Fintype ι] [DecidableEq ι] [Fintype k] [DecidableEq k]

/-- A block-diagonal matrix whose blocks are unitary is unitary. -/
lemma blockDiagonal_mem_unitaryGroup (g : ι → 𝐔[k]) :
    blockDiagonal (fun r => (g r : Matrix k k ℂ)) ∈ unitaryGroup (k × ι) ℂ := by
  rw [mem_unitaryGroup_iff, star_eq_conjTranspose, blockDiagonal_conjTranspose,
    ← blockDiagonal_mul]
  rw [show (fun r => (g r : Matrix k k ℂ) * (g r : Matrix k k ℂ)ᴴ) = 1 from
    funext fun r => (g r).2.2, blockDiagonal_one]

/-- The multiplexed gate `Σ_r |r⟩⟨r| ⊗ g r` on `ι × k`: the gate `g r` on `k`, controlled by the
value `r` of the register `ι`. -/
def multiplex (g : ι → 𝐔[k]) : 𝐔[ι × k] :=
  ⟨reindex (Equiv.prodComm k ι) (Equiv.prodComm k ι) (blockDiagonal fun r => (g r : Matrix k k ℂ)),
    by
      rw [mem_unitaryGroup_iff, star_eq_conjTranspose, conjTranspose_reindex,
        ← coe_reindexAlgEquiv ℂ ℂ, ← map_mul, ← star_eq_conjTranspose,
        (blockDiagonal_mem_unitaryGroup g).2, map_one]⟩

@[simp]
lemma multiplex_apply (g : ι → 𝐔[k]) (r r' : ι) (q q' : k) :
    (multiplex g : Matrix (ι × k) (ι × k) ℂ) (r, q) (r', q') =
      if r = r' then (g r : Matrix k k ℂ) q q' else 0 := by
  simp [multiplex, blockDiagonal_apply']

end PhyslibAlpha.Qubit
