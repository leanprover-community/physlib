/-
Copyright (c) 2026 Brent Yee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brent Yee
-/
module

public import Physlib.QuantumMechanics.HilbertSpaces.FiniteTarget.Basic
public import PhyslibAlpha.Mathematics.SpecialFunctions.Walsh

/-!
# The qubit frame of two unit vectors

An orthonormal frame of the span of two unit vectors which are not equal up to a global phase.

## i. Overview

Two pure states which are not equal up to a global phase span a two-dimensional subspace of the
Hilbert space, so for the Pusey–Barrett–Rudolph (PBR) argument a pair of states is effectively a
qubit. The qubit frame is the orthonormal basis of this subspace in which the PBR paper writes
the two states, as `|ψ₀⟩ = c|0⟩ + s|1⟩` and `|ψ₁⟩ = c|0⟩ - s|1⟩` up to phases.

Let `ψ 0` and `ψ 1` be unit vectors of `𝓗[d]` with `‖⟪ψ 0, ψ 1⟫_ℂ‖ < 1`, that is, which are
not equal up to a global phase. Write `γ = ⟪ψ 0, ψ 1⟫_ℂ`, `r = ‖γ‖ < 1` and
`ζ = exp (-i arg γ)`, so that `ζ γ = r`. The frame vectors `qubitFrameVec (ψ 0) (ψ 1) ζ` are the
vectors `ψ 0 + ζ ψ 1` and `ψ 0 - ζ ψ 1` divided by their norms. We normalize by the norm
rather than by its value `√(2 * (1 ± r))`, so that `qubitFrameVec` depends only on the vectors
and the phase.
The frame vectors are orthonormal, and with `c = √((1 + r) / 2)` and `s = √((1 - r) / 2)` one has
`⟪e j, ψ b⟫_ℂ = phase b * walshSign j b * ![c, s] j`, where `e = qubitFrameVec (ψ 0) (ψ 1) ζ`
and `phase = ![1, conj ζ]`.

## ii. Key results

- `PBR.qubitFrameVec` : the normalized vectors `ψ + ζ φ` and `ψ - ζ φ`.
- `PBR.QubitFrame` : the qubit frame of a pair of unit vectors.
- `PBR.QubitFrame.sum_norm_sq_inner_e_state` : Parseval's identity for each `ψ b` in the frame.
- `PBR.exists_qubitFrame` : two unit vectors which are not equal up to a global phase have a
  qubit frame.

## iii. Table of contents

- A. The vectors `ψ ± ζ φ`
  - A.1. Inner products and norms
  - A.2. The frame vectors
- B. The qubit frame
- C. Existence of the qubit frame
  - C.1. Construction from an aligning phase
  - C.2. The aligning phase

## iv. References

- M. F. Pusey, J. Barrett and T. Rudolph, *On the reality of the quantum state*,
  Nature Phys. 8, 475–478 (2012), arXiv:1111.3328. [ref: Pusey:2011de]

-/

@[expose] public section

noncomputable section

namespace QuantumMechanics.PBR

open InnerProductSpace

variable {d : Type*} [Fintype d] [DecidableEq d]

section Vectors

/-!
## A. The vectors `ψ ± ζ φ`

Throughout, `ψ` and `φ` are unit vectors and `ζ` is a unit complex number aligning
`⟪ψ, φ⟫_ℂ` with the real axis, so that `ζ * ⟪ψ, φ⟫_ℂ = r` for a real number `r`.

### A.1. Inner products and norms

-/

variable {ψ φ : 𝓗[d]} {ζ : ℂ} {r : ℝ}

/-- The conjugate of the alignment `ζ * ⟪ψ, φ⟫_ℂ = r`. -/
lemma conj_mul_inner_swap (hr : ζ * ⟪ψ, φ⟫_ℂ = r) : starRingEnd ℂ ζ * ⟪φ, ψ⟫_ℂ = r := by
  rw [← inner_conj_symm, ← map_mul, hr, Complex.conj_ofReal]

/-- Solving the alignment `ζ * ⟪ψ, φ⟫_ℂ = r` for the inner product, `⟪ψ, φ⟫_ℂ = conj ζ * r`. -/
lemma inner_eq_conj_mul (hζ : ‖ζ‖ = 1) (hr : ζ * ⟪ψ, φ⟫_ℂ = r) :
    ⟪ψ, φ⟫_ℂ = starRingEnd ℂ ζ * r := by
  rw [← hr, ← mul_assoc, Complex.conj_mul', hζ]
  simp

/-- `⟪ψ + ζ φ, ψ⟫_ℂ = 1 + r`. -/
lemma inner_add_smul_fst (hψ : ‖ψ‖ = 1) (hr : ζ * ⟪ψ, φ⟫_ℂ = r) :
    ⟪ψ + ζ • φ, ψ⟫_ℂ = 1 + r := by
  rw [inner_add_left, inner_smul_left, inner_self_eq_one_of_norm_eq_one hψ,
    conj_mul_inner_swap hr]

/-- `⟪ψ + ζ φ, φ⟫_ℂ = conj ζ * (1 + r)`. -/
lemma inner_add_smul_snd (hφ : ‖φ‖ = 1) (hζ : ‖ζ‖ = 1) (hr : ζ * ⟪ψ, φ⟫_ℂ = r) :
    ⟪ψ + ζ • φ, φ⟫_ℂ = starRingEnd ℂ ζ * (1 + r) := by
  rw [inner_add_left, inner_smul_left, inner_self_eq_one_of_norm_eq_one hφ,
    inner_eq_conj_mul hζ hr]
  ring

/-- `⟪ψ - ζ φ, ψ⟫_ℂ = 1 - r`. -/
lemma inner_sub_smul_fst (hψ : ‖ψ‖ = 1) (hr : ζ * ⟪ψ, φ⟫_ℂ = r) :
    ⟪ψ - ζ • φ, ψ⟫_ℂ = 1 - r := by
  rw [inner_sub_left, inner_smul_left, inner_self_eq_one_of_norm_eq_one hψ,
    conj_mul_inner_swap hr]

/-- `⟪ψ - ζ φ, φ⟫_ℂ = -(conj ζ * (1 - r))`. -/
lemma inner_sub_smul_snd (hφ : ‖φ‖ = 1) (hζ : ‖ζ‖ = 1) (hr : ζ * ⟪ψ, φ⟫_ℂ = r) :
    ⟪ψ - ζ • φ, φ⟫_ℂ = -(starRingEnd ℂ ζ * (1 - r)) := by
  rw [inner_sub_left, inner_smul_left, inner_self_eq_one_of_norm_eq_one hφ,
    inner_eq_conj_mul hζ hr]
  ring

/-- The vectors `ψ + ζ φ` and `ψ - ζ φ` are orthogonal. -/
lemma inner_add_smul_sub_smul (hψ : ‖ψ‖ = 1) (hφ : ‖φ‖ = 1) (hζ : ‖ζ‖ = 1)
    (hr : ζ * ⟪ψ, φ⟫_ℂ = r) : ⟪ψ + ζ • φ, ψ - ζ • φ⟫_ℂ = 0 := by
  have hζφ : ‖ζ • φ‖ = 1 := by rw [norm_smul, hζ, hφ, one_mul]
  rw [inner_add_left, inner_sub_right, inner_sub_right, inner_self_eq_one_of_norm_eq_one hψ,
    inner_self_eq_one_of_norm_eq_one hζφ, ← inner_conj_symm (ζ • φ) ψ, inner_smul_right, hr,
    Complex.conj_ofReal]
  ring

/-- The vectors `ψ - ζ φ` and `ψ + ζ φ` are orthogonal. -/
lemma inner_sub_smul_add_smul (hψ : ‖ψ‖ = 1) (hφ : ‖φ‖ = 1) (hζ : ‖ζ‖ = 1)
    (hr : ζ * ⟪ψ, φ⟫_ℂ = r) : ⟪ψ - ζ • φ, ψ + ζ • φ⟫_ℂ = 0 := by
  rw [← inner_conj_symm, inner_add_smul_sub_smul hψ hφ hζ hr, map_zero]

/-- The squared norm of `ψ + ζ φ` is `2 * (1 + r)`. -/
lemma norm_add_smul_sq (hψ : ‖ψ‖ = 1) (hφ : ‖φ‖ = 1) (hζ : ‖ζ‖ = 1)
    (hr : ζ * ⟪ψ, φ⟫_ℂ = r) : ‖ψ + ζ • φ‖ ^ 2 = 2 * (1 + r) := by
  rw [norm_add_sq (𝕜 := ℂ), inner_smul_right, hr, norm_smul, hψ, hφ, hζ,
    RCLike.re_to_complex, Complex.ofReal_re]
  ring

/-- The squared norm of `ψ - ζ φ` is `2 * (1 - r)`. -/
lemma norm_sub_smul_sq (hψ : ‖ψ‖ = 1) (hφ : ‖φ‖ = 1) (hζ : ‖ζ‖ = 1)
    (hr : ζ * ⟪ψ, φ⟫_ℂ = r) : ‖ψ - ζ • φ‖ ^ 2 = 2 * (1 - r) := by
  rw [norm_sub_sq (𝕜 := ℂ), inner_smul_right, hr, norm_smul, hψ, hφ, hζ,
    RCLike.re_to_complex, Complex.ofReal_re]
  ring

/-- The norm of `ψ + ζ φ` is `√(2 * (1 + r))`. -/
lemma norm_add_smul (hψ : ‖ψ‖ = 1) (hφ : ‖φ‖ = 1) (hζ : ‖ζ‖ = 1) (hr : ζ * ⟪ψ, φ⟫_ℂ = r) :
    ‖ψ + ζ • φ‖ = √(2 * (1 + r)) := by
  rw [← norm_add_smul_sq hψ hφ hζ hr, Real.sqrt_sq (norm_nonneg _)]

/-- The norm of `ψ - ζ φ` is `√(2 * (1 - r))`. -/
lemma norm_sub_smul (hψ : ‖ψ‖ = 1) (hφ : ‖φ‖ = 1) (hζ : ‖ζ‖ = 1) (hr : ζ * ⟪ψ, φ⟫_ℂ = r) :
    ‖ψ - ζ • φ‖ = √(2 * (1 - r)) := by
  rw [← norm_sub_smul_sq hψ hφ hζ hr, Real.sqrt_sq (norm_nonneg _)]

/-!
### A.2. The frame vectors

-/

/-- The frame vectors `ψ + ζ φ` and `ψ - ζ φ`, each divided by its norm. A zero vector stays
zero. -/
def qubitFrameVec (ψ φ : 𝓗[d]) (ζ : ℂ) : Fin 2 → 𝓗[d] :=
  ![(‖ψ + ζ • φ‖⁻¹ : ℂ) • (ψ + ζ • φ), (‖ψ - ζ • φ‖⁻¹ : ℂ) • (ψ - ζ • φ)]

/-- The frame vector `qubitFrameVec ψ φ ζ 0` is the normalized `ψ + ζ φ`. -/
@[simp]
lemma qubitFrameVec_zero (ψ φ : 𝓗[d]) (ζ : ℂ) :
    qubitFrameVec ψ φ ζ 0 = (‖ψ + ζ • φ‖⁻¹ : ℂ) • (ψ + ζ • φ) := rfl

/-- The frame vector `qubitFrameVec ψ φ ζ 1` is the normalized `ψ - ζ φ`. -/
@[simp]
lemma qubitFrameVec_one (ψ φ : 𝓗[d]) (ζ : ℂ) :
    qubitFrameVec ψ φ ζ 1 = (‖ψ - ζ • φ‖⁻¹ : ℂ) • (ψ - ζ • φ) := rfl

/-- For `-1 < r < 1` the frame vectors are orthonormal. -/
lemma orthonormal_qubitFrameVec (hψ : ‖ψ‖ = 1) (hφ : ‖φ‖ = 1) (hζ : ‖ζ‖ = 1)
    (hr : ζ * ⟪ψ, φ⟫_ℂ = r) (hr0 : -1 < r) (hr1 : r < 1) : Orthonormal ℂ (qubitFrameVec ψ φ ζ) := by
  have h0 : ψ + ζ • φ ≠ 0 := by
    rw [← norm_ne_zero_iff, norm_add_smul hψ hφ hζ hr, Real.sqrt_ne_zero']
    linarith
  have h1 : ψ - ζ • φ ≠ 0 := by
    rw [← norm_ne_zero_iff, norm_sub_smul hψ hφ hζ hr, Real.sqrt_ne_zero']
    linarith
  refine ⟨fun j => ?_, fun j k hjk => ?_⟩
  · fin_cases j
    · exact norm_smul_inv_norm h0
    · exact norm_smul_inv_norm h1
  · fin_cases j <;> fin_cases k <;>
      simp only [ne_eq, not_true_eq_false, Fin.zero_eta, Fin.mk_one, Fin.isValue,
        qubitFrameVec_zero, qubitFrameVec_one] at hjk ⊢ <;>
      rw [inner_smul_left, inner_smul_right]
    · rw [inner_add_smul_sub_smul hψ hφ hζ hr, mul_zero, mul_zero]
    · rw [inner_sub_smul_add_smul hψ hφ hζ hr, mul_zero, mul_zero]

/-- The components of `ψ` along the frame vectors are `√((1 + r) / 2)` and `√((1 - r) / 2)`. -/
lemma inner_qubitFrameVec_fst (hψ : ‖ψ‖ = 1) (hφ : ‖φ‖ = 1) (hζ : ‖ζ‖ = 1)
    (hr : ζ * ⟪ψ, φ⟫_ℂ = r) (j : Fin 2) :
    ⟪qubitFrameVec ψ φ ζ j, ψ⟫_ℂ = ![(√((1 + r) / 2) : ℂ), (√((1 - r) / 2) : ℂ)] j := by
  have key (a : ℝ) : (√(2 * a))⁻¹ * a = √(a / 2) := by
    rw [inv_mul_eq_div, Real.sqrt_mul zero_le_two, mul_comm, ← div_div, Real.div_sqrt,
      Real.sqrt_div' _ zero_le_two]
  fin_cases j
  · simp only [Fin.zero_eta, Fin.isValue, qubitFrameVec_zero, inner_smul_left, map_inv₀,
      Complex.conj_ofReal, inner_add_smul_fst hψ hr, norm_add_smul hψ hφ hζ hr,
      Matrix.cons_val_zero, ← key (1 + r)]
    push_cast
    ring
  · simp only [Fin.mk_one, Fin.isValue, qubitFrameVec_one, inner_smul_left, map_inv₀,
      Complex.conj_ofReal, inner_sub_smul_fst hψ hr, norm_sub_smul hψ hφ hζ hr,
      Matrix.cons_val_one, Matrix.cons_val_fin_one, ← key (1 - r)]
    push_cast
    ring

/-- The component of `φ` along a frame vector is `conj ζ` times that of `ψ`, with a sign `-1`
for the frame vector `ψ - ζ φ`. -/
lemma inner_qubitFrameVec_snd (hψ : ‖ψ‖ = 1) (hφ : ‖φ‖ = 1) (hζ : ‖ζ‖ = 1)
    (hr : ζ * ⟪ψ, φ⟫_ℂ = r) (j : Fin 2) :
    ⟪qubitFrameVec ψ φ ζ j, φ⟫_ℂ =
      starRingEnd ℂ ζ * walshSign j 1 * ⟪qubitFrameVec ψ φ ζ j, ψ⟫_ℂ := by
  fin_cases j
  · simp only [Fin.zero_eta, Fin.isValue, qubitFrameVec_zero, inner_smul_left,
      inner_add_smul_fst hψ hr, inner_add_smul_snd hφ hζ hr, walshSign_zero_left]
    ring
  · simp only [Fin.mk_one, Fin.isValue, qubitFrameVec_one, inner_smul_left,
      inner_sub_smul_fst hψ hr, inner_sub_smul_snd hφ hζ hr, walshSign_one_one]
    ring

end Vectors

/-!
## B. The qubit frame

-/

/-- A qubit frame of two unit vectors `ψ 0` and `ψ 1` consists of orthonormal vectors `e 0`,
`e 1`, reals `0 < s ≤ c` with `c ^ 2 + s ^ 2 = 1` and unit phases `phase b`, such that
`⟪e j, ψ b⟫_ℂ = phase b * walshSign j b * ![c, s] j`. -/
structure QubitFrame (ψ : Fin 2 → 𝓗[d]) where
  /-- The orthonormal frame vectors. -/
  e : Fin 2 → 𝓗[d]
  /-- The amplitude of `e 0` in the vectors. For the frame `QubitFrame.ofPhase` used by
  `exists_qubitFrame` it is `√((1 + ‖⟪ψ 0, ψ 1⟫_ℂ‖) / 2)`. -/
  c : ℝ
  /-- The amplitude of `e 1` in the vectors. For the frame `QubitFrame.ofPhase` used by
  `exists_qubitFrame` it is `√((1 - ‖⟪ψ 0, ψ 1⟫_ℂ‖) / 2)`. -/
  s : ℝ
  /-- The global phases of the two vectors in the frame. -/
  phase : Fin 2 → ℂ
  /-- The smaller amplitude is positive. -/
  s_pos : 0 < s
  /-- The amplitude `s` is at most `c`. -/
  s_le_c : s ≤ c
  /-- The amplitudes are normalized. -/
  sq_add_sq : c ^ 2 + s ^ 2 = 1
  /-- The phases have unit norm. -/
  norm_phase (b : Fin 2) : ‖phase b‖ = 1
  /-- The frame vectors are orthonormal. -/
  orthonormal_e : Orthonormal ℂ e
  /-- The components of the vectors in the frame. -/
  inner_e_state (j b : Fin 2) : ⟪e j, ψ b⟫_ℂ = phase b * walshSign j b * ![(c : ℂ), (s : ℂ)] j

namespace QubitFrame

variable {ψ : Fin 2 → 𝓗[d]}

/-- The larger amplitude is positive. -/
lemma c_pos (F : QubitFrame ψ) : 0 < F.c := F.s_pos.trans_le F.s_le_c

/-- Parseval's identity. The components of the unit vector `ψ b` in the frame have total squared
norm one, so `ψ b` lies in the span of the frame. -/
lemma sum_norm_sq_inner_e_state (F : QubitFrame ψ) (b : Fin 2) :
    ∑ j, ‖⟪F.e j, ψ b⟫_ℂ‖ ^ 2 = 1 := by
  simp only [Fin.sum_univ_two, F.inner_e_state, norm_mul, F.norm_phase, norm_walshSign, one_mul,
    Matrix.cons_val_zero, Matrix.cons_val_one, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  exact F.sq_add_sq

end QubitFrame

/-!
## C. Existence of the qubit frame

### C.1. Construction from an aligning phase

-/

/-- The qubit frame of unit vectors `ψ 0` and `ψ 1` built from a unit `ζ` with
`ζ * ⟪ψ 0, ψ 1⟫_ℂ = r < 1`. Its vectors are `qubitFrameVec (ψ 0) (ψ 1) ζ`, its amplitudes are
`c = √((1 + r) / 2)` and `s = √((1 - r) / 2)`, and its phases are `![1, conj ζ]`. -/
def QubitFrame.ofPhase (ψ : Fin 2 → 𝓗[d]) (hψ : ∀ b, ‖ψ b‖ = 1) {ζ : ℂ} {r : ℝ}
    (hζ : ‖ζ‖ = 1) (hr : ζ * ⟪ψ 0, ψ 1⟫_ℂ = r) (hr0 : 0 ≤ r) (hr1 : r < 1) :
    QubitFrame ψ where
  e := qubitFrameVec (ψ 0) (ψ 1) ζ
  c := √((1 + r) / 2)
  s := √((1 - r) / 2)
  phase := ![1, starRingEnd ℂ ζ]
  s_pos := Real.sqrt_pos.mpr (by linarith)
  s_le_c := Real.sqrt_le_sqrt (by linarith)
  sq_add_sq := by
    rw [Real.sq_sqrt (by linarith), Real.sq_sqrt (by linarith)]
    ring
  norm_phase b := by fin_cases b <;> simp [hζ]
  orthonormal_e := orthonormal_qubitFrameVec (hψ 0) (hψ 1) hζ hr (by linarith) hr1
  inner_e_state j b := by
    fin_cases b
    · simp [inner_qubitFrameVec_fst (hψ 0) (hψ 1) hζ hr]
    · simp [inner_qubitFrameVec_snd (hψ 0) (hψ 1) hζ hr,
        inner_qubitFrameVec_fst (hψ 0) (hψ 1) hζ hr]

/-!
### C.2. The aligning phase

-/

/-- Two unit vectors which are not equal up to a global phase, that is with
`‖⟪ψ 0, ψ 1⟫_ℂ‖ < 1`, have a qubit frame. The aligning phase is `exp (-i arg ⟪ψ 0, ψ 1⟫_ℂ)`. -/
lemma exists_qubitFrame (ψ : Fin 2 → 𝓗[d]) (hψ : ∀ b, ‖ψ b‖ = 1)
    (h : ‖⟪ψ 0, ψ 1⟫_ℂ‖ < 1) : Nonempty (QubitFrame ψ) := by
  have hr (γ : ℂ) : Complex.exp (↑(-γ.arg) * Complex.I) * γ = ‖γ‖ := by
    nth_rw 2 [← Complex.norm_mul_exp_arg_mul_I γ]
    rw [mul_left_comm, ← Complex.exp_add]
    simp
  exact ⟨QubitFrame.ofPhase ψ hψ (Complex.norm_exp_ofReal_mul_I _) (hr _) (norm_nonneg _) h⟩

end QuantumMechanics.PBR
