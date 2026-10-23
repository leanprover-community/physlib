/-
Copyright (c) 2026 Anand Nambakam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anand Nambakam
-/
module

public import QuantumInfo.States.Pure.Braket

/-!
# Bargmann Invariant and Geometric Phase

The Bargmann invariant for three quantum states is the cyclic product
of inner products `⟨ψ₁|ψ₂⟩ · ⟨ψ₂|ψ₃⟩ · ⟨ψ₃|ψ₁⟩`. Its argument is
the geometric (Pancharatnam-Berry) phase accumulated around the
geodesic triangle in projective Hilbert space.

## Important definitions
 * `bargmannInvariantThree`: the 3-vertex Bargmann invariant `Δ₃`
 * `bargmannPhaseThree`: the geometric phase `arg(Δ₃)`

## Important results
 * `bargmannInvariantThree_degenerate`: identical states give `Δ₃ = 1`
 * `bargmannPhaseThree_degenerate`: identical states give phase `= 0`
 * `bargmannInvariantThree_reverse`: reversing conjugates `Δ₃`
 * `bargmannPhaseThree_reverse`: reversing negates the phase (mod 2π)
 * `bargmannInvariantThree_cyclic`: cyclic permutation preserves `Δ₃`
 * `bargmannPhaseThree_cyclic`: cyclic permutation preserves the phase
 * `norm_bargmannInvariantThree_le_one`: `‖Δ₃‖ ≤ 1` (via `Braket.norm_dot_le_one`)

## References

* V. Bargmann, Note on Wigner's theorem on symmetry operations, J. Math. Phys. 5, 862–868 (1964).
  [ref: bargmann1964]
* S. Pancharatnam, Generalized theory of interference, and its applications, Proc. Indian Acad.
  Sci. A 44, 247–262 (1956). [ref: pancharatnam1956]
-/

@[expose] public section

open Braket Complex

variable {d : Type*} [Fintype d] [DecidableEq d]

noncomputable section

/-- The three-vertex Bargmann invariant: `⟨ψ₁|ψ₂⟩ · ⟨ψ₂|ψ₃⟩ · ⟨ψ₃|ψ₁⟩`.
    This is a gauge-invariant complex number whose argument is the
    geometric phase of the geodesic triangle. -/
def bargmannInvariantThree (ψ₁ ψ₂ ψ₃ : Ket d) : ℂ :=
  〈ψ₁‖ψ₂〉 * 〈ψ₂‖ψ₃〉 * 〈ψ₃‖ψ₁〉

/-- The geometric (Pancharatnam-Berry) phase of three states. -/
def bargmannPhaseThree (ψ₁ ψ₂ ψ₃ : Ket d) : ℝ :=
  Complex.arg (bargmannInvariantThree ψ₁ ψ₂ ψ₃)

/-! ## Degenerate triangles -/

omit [DecidableEq d] in
/-- The Bargmann invariant of three identical states is 1. -/
@[simp]
lemma bargmannInvariantThree_degenerate (ψ : Ket d) :
    bargmannInvariantThree ψ ψ ψ = 1 := by
  unfold bargmannInvariantThree
  simp [Braket.dot_self_eq_one]

omit [DecidableEq d] in
/-- The geometric phase of three identical states is 0. -/
lemma bargmannPhaseThree_degenerate (ψ : Ket d) :
    bargmannPhaseThree ψ ψ ψ = 0 := by
  unfold bargmannPhaseThree; simp [Complex.arg_one]

/-! ## Conjugacy -/

omit [DecidableEq d] in
/-- Reversing the cyclic order conjugates the invariant. -/
lemma bargmannInvariantThree_reverse (ψ₁ ψ₂ ψ₃ : Ket d) :
    bargmannInvariantThree ψ₃ ψ₂ ψ₁ = starRingEnd ℂ (bargmannInvariantThree ψ₁ ψ₂ ψ₃) := by
  unfold bargmannInvariantThree
  conv_lhs =>
    rw [Braket.dot_swap_conj ψ₂ ψ₃, Braket.dot_swap_conj ψ₁ ψ₂, Braket.dot_swap_conj ψ₃ ψ₁,
        ← map_mul, ← map_mul]
  congr 1; ring

omit [DecidableEq d] in
/-- Reversing the cyclic order negates the geometric phase (mod 2π). -/
lemma bargmannPhaseThree_reverse (ψ₁ ψ₂ ψ₃ : Ket d) :
    (bargmannPhaseThree ψ₃ ψ₂ ψ₁ : Real.Angle) =
    -(bargmannPhaseThree ψ₁ ψ₂ ψ₃ : Real.Angle) := by
  unfold bargmannPhaseThree; rw [bargmannInvariantThree_reverse]
  exact Complex.arg_conj_coe_angle (bargmannInvariantThree ψ₁ ψ₂ ψ₃)

/-! ## Cyclic symmetry -/

omit [DecidableEq d] in
/-- Cyclic permutation of the three states preserves the Bargmann invariant. -/
lemma bargmannInvariantThree_cyclic (ψ₁ ψ₂ ψ₃ : Ket d) :
    bargmannInvariantThree ψ₂ ψ₃ ψ₁ = bargmannInvariantThree ψ₁ ψ₂ ψ₃ := by
  unfold bargmannInvariantThree; ring

omit [DecidableEq d] in
/-- Cyclic permutation preserves the geometric phase. -/
lemma bargmannPhaseThree_cyclic (ψ₁ ψ₂ ψ₃ : Ket d) :
    bargmannPhaseThree ψ₂ ψ₃ ψ₁ = bargmannPhaseThree ψ₁ ψ₂ ψ₃ := by
  unfold bargmannPhaseThree; rw [bargmannInvariantThree_cyclic]

/-! ## Norm bounds -/

omit [DecidableEq d] in
/-- The Bargmann invariant has norm at most 1: each inner product factor
    is bounded by Cauchy-Schwarz on unit vectors. -/
lemma norm_bargmannInvariantThree_le_one (ψ₁ ψ₂ ψ₃ : Ket d) :
    ‖bargmannInvariantThree ψ₁ ψ₂ ψ₃‖ ≤ 1 := by
  unfold bargmannInvariantThree
  calc ‖〈ψ₁‖ψ₂〉 * 〈ψ₂‖ψ₃〉 * 〈ψ₃‖ψ₁〉‖
      = ‖〈ψ₁‖ψ₂〉‖ * ‖〈ψ₂‖ψ₃〉‖ * ‖〈ψ₃‖ψ₁〉‖ := by rw [norm_mul, norm_mul]
    _ ≤ 1 * 1 * 1 := by
        gcongr <;> exact Braket.norm_dot_le_one _ _
    _ = 1 := by ring

