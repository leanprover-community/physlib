/-
Copyright (c) 2025 Prabhoda Chandra Sarjapur. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prabhoda Chandra Sarjapur
-/
module

public import Mathlib.LinearAlgebra.UnitaryGroup
public import Mathlib.Analysis.Complex.Trigonometric
public import Mathlib.Tactic.Polyrith
/-!

# The PMNS matrix

The definition the PMNS matrix, which describes neutrino oscillations as part of U(3).

-/

@[expose] public section
open Matrix Complex

noncomputable section

/-- diagonal phase matrix from a real-valued function on indices -/
@[simp]
def diagPhase (θ : Fin 3 → ℝ) : Matrix (Fin 3) (Fin 3) ℂ :=
  λ i j => if i = j then cexp (I * θ i) else 0

/-- lemma stating that the diagonal phase matrix with all zeros is the identity matrix -/
@[simp]
lemma diagPhase_zero:
    diagPhase (fun _ : Fin 3 => 0) = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp []

/-- lemma stating that diagPhase with θ = 0 is equal to diagPhase with all zero phases -/
@[simp]
lemma diagPhase_zero_eq : diagPhase 0 = diagPhase (fun _ : Fin 3 => 0) := by
    ext i j
    simp [diagPhase]

/-- lemma stating that the Hermitian conjugate of diagPhase diag(+iθ_i)
is just diagPhase with entries diag(-iθ_i) -/
@[simp]
lemma diagPhase_star (θ : Fin 3 → ℝ) :
    (diagPhase θ)ᴴ = diagPhase (- θ) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
    simp [diagPhase, Matrix.conjTranspose_apply, ← exp_conj]

/-- lemma stating that multiplying two phase matrices is equivalent to adding the phases -/
@[simp]
lemma diagPhase_mul (θ φ : Fin 3 → ℝ) :
    diagPhase θ * diagPhase φ = diagPhase (θ + φ) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
    simp [diagPhase, Matrix.mul_apply, ← exp_add, mul_add]

/-- diagonal phase matrix diag(iθ_i) is part of the unitary group -/
def diagPhase_unitary (θ : Fin 3 → ℝ) : unitaryGroup (Fin 3) ℂ :=
    ⟨diagPhase θ,
    by
    rw[Matrix.mem_unitaryGroup_iff]
    change _ * (diagPhase θ)ᴴ = 1
    ext i j
    fin_cases i <;> fin_cases j <;> simp [diagPhase,
    Matrix.mul_apply,
    ← exp_add]⟩

/-- The underlying matrix of the phase-shift element of the unitary group is the
  phase-shift matrix. -/
@[simp]
lemma diagPhaseShift_coe_matrix (θ : Fin 3 → ℝ) : ↑(diagPhase_unitary θ) = diagPhase θ := rfl

/-- The Lepton phase shift matrix as a `3×3` complex matrix, given three reals `a b c`.
This dictates the phase shift freedom of the charged lepton sector.
-/
def leptonPhaseShift (a b c : ℝ) : Matrix (Fin 3) (Fin 3) ℂ :=
  diagPhase (fun i => if i = 0 then a else if i = 1 then b else c)

/-- The neutrino phase shift matrix as a `3×3` complex matrix, given three reals `d e f`.
This dictates the phase shift freedom of the neutrino sector (If neutrinos are Dirac).
-/
def neutrinoPhaseShift (d e f : ℝ) : Matrix (Fin 3) (Fin 3) ℂ :=
  diagPhase (fun i => if i = 0 then d else if i = 1 then e else f)

/-- If neutrinos are Majorana particles, then the neutrino phase shift matrix is physical,
and cannot be absorbed into the definition of the neutrino fields.
-/
def majoranaPhaseMatrix (α1 α2 : ℝ) : Matrix (Fin 3) (Fin 3) ℂ :=
  diagPhase (fun i => if i = 0 then 0 else if i = 1 then α1/2 else α2/2)

/-- The Dirac PMNS matrix equivalence relations -/
def PMNS_dirac_equivalence (U V : unitaryGroup (Fin 3) ℂ) : Prop :=
  ∃ (θ φ : Fin 3 → ℝ),
  U = diagPhase θ * V * diagPhase φ

/-- The relation `PMNS_dirac_equivalence` is reflexive. -/
lemma PMNS_dirac_equivalence_refl :
    ∀ U : unitaryGroup (Fin 3) ℂ, PMNS_dirac_equivalence U U := by
    intro U
    use (fun _ : Fin 3 => 0), (fun _ : Fin 3 => 0)
    simp [diagPhase_zero]

/-- The relation `PMNS_dirac_equivalence` is symmetric. -/
lemma PMNS_dirac_equivalence_symm :
    ∀ U V : unitaryGroup (Fin 3) ℂ, PMNS_dirac_equivalence U V → PMNS_dirac_equivalence V U := by
    intros U V h
    rcases h with ⟨θ, φ, h'⟩
    use -θ, -φ
    rw [h']
    rw [← mul_assoc, mul_assoc]
    simp [diagPhase_mul]
    rw [← mul_assoc]
    simp [diagPhase_mul]

/-- The relation `PMNS_dirac_equivalence` is transitive. -/
lemma PMNS_dirac_equivalence_trans {U V W : unitaryGroup (Fin 3) ℂ} :
    PMNS_dirac_equivalence U V → PMNS_dirac_equivalence V W → PMNS_dirac_equivalence U W := by
    intros h1 h2
    rcases h1 with ⟨θ1, φ1, hUV⟩
    rcases h2 with ⟨θ2, φ2, hVW⟩
    use (θ1 + θ2), (φ1 + φ2)
    rw [hUV, hVW]
    rw [← mul_assoc, mul_assoc]
    simp [diagPhase_mul]
    rw [← mul_assoc]
    simp [diagPhase_mul]
    simp [add_comm]
