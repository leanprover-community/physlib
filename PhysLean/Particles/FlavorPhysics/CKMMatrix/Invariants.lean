/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import PhysLean.Particles.FlavorPhysics.CKMMatrix.Basic
public import Mathlib.Analysis.Complex.Basic
/-!
# Invariants of the CKM Matrix

The CKM matrix is only defined up to an equivalence.

This file defines some invariants of the CKM matrix, which are well-defined with respect to
this equivalence.

Of note, this file defines the complex jarlskog invariant.

-/

@[expose] public section
open Matrix Complex
open ComplexConjugate
open CKMMatrix

noncomputable section
namespace Invariant

/-- The complex jarlskog invariant for a CKM matrix. -/
@[simps!]
def jarlskogℂCKM (V : CKMMatrix) : ℂ :=
  [V]us * [V]cb * conj [V]ub * conj [V]cs

/-- The complex jarlskog invariant is equal for equivalent CKM matrices. -/
lemma jarlskogℂCKM_equiv (V U : CKMMatrix) (h : V ≈ U) :
    jarlskogℂCKM V = jarlskogℂCKM U := by
  obtain ⟨a, b, c, e, f, g, h⟩ := h
  change V = phaseShiftApply U a b c e f g at h
  rw [h]
  simp only [jarlskogℂCKM, Fin.isValue, phaseShiftApply.ub,
  phaseShiftApply.us, phaseShiftApply.cb, phaseShiftApply.cs]
  simp only [exp_add, Fin.isValue, _root_.map_mul, ← exp_conj, conj_ofReal, conj_I, mul_neg,
    exp_neg]
  have ha : cexp (↑a * I) ≠ 0 := exp_ne_zero _
  have hb : cexp (↑b * I) ≠ 0 := exp_ne_zero _
  have hf : cexp (↑f * I) ≠ 0 := exp_ne_zero _
  have hg : cexp (↑g * I) ≠ 0 := exp_ne_zero _
  field_simp

/-- The complex jarlskog invariant for an equivalence class of CKM matrices. -/
@[simp]
def jarlskogℂ : Quotient CKMMatrixSetoid → ℂ :=
  Quotient.lift jarlskogℂCKM jarlskogℂCKM_equiv

/-- An invariant for CKM matrices corresponding to the square of the absolute values
  of the `us`, `ub` and `cb` elements multiplied together divided by `(VudAbs V ^ 2 + VusAbs V ^2)`.
-/
def VusVubVcdSq (V : Quotient CKMMatrixSetoid) : ℝ :=
    VusAbs V ^ 2 * VubAbs V ^ 2 * VcbAbs V ^2 / (VudAbs V ^ 2 + VusAbs V ^2)

/-- An invariant for CKM matrices. The argument of this invariant is `δ₁₃` in the
standard parameterization. -/
def mulExpδ₁₃ (V : Quotient CKMMatrixSetoid) : ℂ :=
  jarlskogℂ V + VusVubVcdSq V

end Invariant
end
