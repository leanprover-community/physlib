/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import PhyslibAlpha.Particles.BeyondTheStandardModel.TwoHDM.Module
public import PhyslibAlpha.Particles.BeyondTheStandardModel.TwoHDM.GaugeTorus
public import PhyslibAlpha.Particles.BeyondTheStandardModel.TwoHDM.OrbitRepresentative
/-!
# The gauge slice and the hypercharges of the doublet components

The upper-triangular slice of 2HDM configurations and the gauge-torus phases acting on it.

## i. Overview

After using `SU(2)` to align the first doublet with the first axis, a configuration lies on the
*upper-triangular slice* `sliceHiggs z w₀ w₁ = ⟨(z, 0), (w₀, w₁)⟩`. The gauge torus acts on the
three surviving components `z = Φ1₀`, `w₀ = Φ2₀`, `w₁ = Φ2₁` by their hypercharges:

* the Cartan phase `a` multiplies the *first* components `z, w₀` (and conjugates the would-be second
  component of `Φ1`, which vanishes here), giving `(z, w₀, w₁) ↦ (a z, a w₀, ā w₁)`;
* the residual `U(1)` (`ofU1Subgroup c`) multiplies the *second* component `w₁` by `c⁶`, giving
  `(z, w₀, w₁) ↦ (z, w₀, c⁶ w₁)`.

These two phase rotations are the source of the charge balancing of the effective potential.

## ii. Key results

- `TwoHiggsDoublet.sliceHiggs` : the upper-triangular slice configuration `⟨(z, 0), (w₀, w₁)⟩`.
- `TwoHiggsDoublet.sliceR` : the slice as a real-linear map from six real field parameters.
- `TwoHiggsDoublet.gaugeCartan_smul_sliceHiggs` : the hypercharge action of the Cartan phase.
- `TwoHiggsDoublet.ofU1Subgroup_smul_sliceHiggs` : the hypercharge action of the residual `U(1)`.
- `TwoHiggsDoublet.gaugeCartan_smul_sliceR` : the Cartan phase rotates the real parameters.
- `TwoHiggsDoublet.ofU1Subgroup_smul_sliceR` : the residual `U(1)` rotates only the perpendicular
  parameter pair.

## iii. Table of contents

- A. The slice configuration
- B. Hypercharge action on the slice
- C. Gauge action on the real parameters

## iv. References

* None.

-/

@[expose] public section

noncomputable section

namespace TwoHiggsDoublet

open InnerProductSpace
open StandardModel
open ComplexConjugate

/-!

## A. The slice configuration

-/

/-- The upper-triangular slice configuration `⟨(z, 0), (w₀, w₁)⟩`. It specialises to `repHiggs`
  when the components take their real "canonical frame" values. -/
def sliceHiggs (z w0 w1 : ℂ) : TwoHiggsDoublet where
  Φ1 := !₂[z, 0]
  Φ2 := !₂[w0, w1]

@[simp] lemma sliceHiggs_Φ1 (z w0 w1 : ℂ) : (sliceHiggs z w0 w1).Φ1 = !₂[z, 0] := rfl
@[simp] lemma sliceHiggs_Φ2 (z w0 w1 : ℂ) : (sliceHiggs z w0 w1).Φ2 = !₂[w0, w1] := rfl

@[simp] lemma real_smul_fst (c : ℝ) (H : TwoHiggsDoublet) : (c • H).Φ1 = c • H.Φ1 := rfl
@[simp] lemma real_smul_snd (c : ℝ) (H : TwoHiggsDoublet) : (c • H).Φ2 = c • H.Φ2 := rfl

/-- The slice as a real-linear map from the six real field parameters
  `(Re Φ1₀, Im Φ1₀, Re Φ2₀, Im Φ2₀, Re Φ2₁, Im Φ2₁)`. -/
def sliceR : (Fin 6 → ℝ) →ₗ[ℝ] TwoHiggsDoublet where
  toFun a := sliceHiggs (↑(a 0) + Complex.I * ↑(a 1)) (↑(a 2) + Complex.I * ↑(a 3))
    (↑(a 4) + Complex.I * ↑(a 5))
  map_add' a b := by
    apply ext_of_fst_snd
    · ext i; fin_cases i <;> simp [sliceHiggs]
      ring
    · ext i; fin_cases i <;> simp [sliceHiggs] <;> ring
  map_smul' c a := by
    apply ext_of_fst_snd
    · ext i; fin_cases i <;> simp [sliceHiggs, Complex.real_smul]
      ring
    · ext i; fin_cases i <;> simp [sliceHiggs, Complex.real_smul] <;> ring

@[simp] lemma sliceR_apply (a : Fin 6 → ℝ) :
    sliceR a = sliceHiggs (↑(a 0) + Complex.I * ↑(a 1)) (↑(a 2) + Complex.I * ↑(a 3))
      (↑(a 4) + Complex.I * ↑(a 5)) := rfl

/-- The representative family is the real slice. -/
lemma repHiggs_eq_sliceHiggs (X : Fin 4 → ℝ) :
    repHiggs X = sliceHiggs (X 0) ((X 1 : ℂ) + Complex.I * (X 2 : ℂ)) (X 3) := rfl

/-!

## B. Hypercharge action on the slice

-/

/-- Hypercharge action of the Cartan phase on the slice: it multiplies the first components by `a`
  and the perpendicular second component by `ā`. -/
lemma gaugeCartan_smul_sliceHiggs (a : unitary ℂ) (z w0 w1 : ℂ) :
    GaugeGroupI.gaugeCartan a • sliceHiggs z w0 w1
      = sliceHiggs ((a : ℂ) * z) ((a : ℂ) * w0) ((star a : ℂ) * w1) := by
  apply ext_of_fst_snd
  · rw [gaugeGroupI_smul_fst, GaugeGroupI.gaugeCartan_smul_eq]
    ext i
    fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  · rw [gaugeGroupI_smul_snd, GaugeGroupI.gaugeCartan_smul_eq]
    ext i
    fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-- Hypercharge action of the residual `U(1)` on the slice: it multiplies the perpendicular second
  component by `c⁶` and leaves the first components fixed. -/
lemma ofU1Subgroup_smul_sliceHiggs (c : unitary ℂ) (z w0 w1 : ℂ) :
    GaugeGroupI.ofU1Subgroup c • sliceHiggs z w0 w1
      = sliceHiggs z w0 ((c : ℂ) ^ 6 * w1) := by
  apply ext_of_fst_snd
  · rw [gaugeGroupI_smul_fst, HiggsVec.ofU1Subgroup_repGaugeGroupI_apply]
    ext i
    fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  · rw [gaugeGroupI_smul_snd, HiggsVec.ofU1Subgroup_repGaugeGroupI_apply]
    ext i
    fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-!

## C. Gauge action on the real parameters

-/

open Complex in
/-- The Cartan hypercharge phase `u`, transported to a rotation of the six real field parameters:
  it phases the first-component pairs by `u` and the perpendicular pair by `ū`. -/
def cartanRotParam (u : unitary ℂ) (a : Fin 6 → ℝ) : Fin 6 → ℝ :=
  ![((u : ℂ) * (↑(a 0) + I * ↑(a 1))).re, ((u : ℂ) * (↑(a 0) + I * ↑(a 1))).im,
    ((u : ℂ) * (↑(a 2) + I * ↑(a 3))).re, ((u : ℂ) * (↑(a 2) + I * ↑(a 3))).im,
    ((star u : ℂ) * (↑(a 4) + I * ↑(a 5))).re, ((star u : ℂ) * (↑(a 4) + I * ↑(a 5))).im]

/-- Acting by the Cartan phase on a slice configuration is the same as rotating its parameters. -/
lemma gaugeCartan_smul_sliceR (u : unitary ℂ) (a : Fin 6 → ℝ) :
    GaugeGroupI.gaugeCartan u • sliceR a = sliceR (cartanRotParam u a) := by
  have h : ∀ z : ℂ, (↑z.re + Complex.I * ↑z.im) = z := fun z => by
    rw [mul_comm]; exact Complex.re_add_im z
  rw [sliceR_apply, gaugeCartan_smul_sliceHiggs, sliceR_apply]
  congr 1 <;> simp only [cartanRotParam, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val, Fin.isValue] <;> rw [h]

open Complex in
/-- The residual `U(1)` phase `c`, transported to a rotation of the perpendicular parameter pair. -/
def resRotParam (c : unitary ℂ) (a : Fin 6 → ℝ) : Fin 6 → ℝ :=
  ![a 0, a 1, a 2, a 3, (((c : ℂ) ^ 6) * ((a 4 : ℂ) + I * (a 5 : ℂ))).re,
    (((c : ℂ) ^ 6) * ((a 4 : ℂ) + I * (a 5 : ℂ))).im]

/-- Acting by the residual `U(1)` on a slice configuration rotates only the perpendicular pair. -/
lemma ofU1Subgroup_smul_sliceR (c : unitary ℂ) (a : Fin 6 → ℝ) :
    GaugeGroupI.ofU1Subgroup c • sliceR a = sliceR (resRotParam c a) := by
  have h : ∀ z : ℂ, (↑z.re + Complex.I * ↑z.im) = z := fun z => by
    rw [mul_comm]; exact Complex.re_add_im z
  rw [sliceR_apply, ofU1Subgroup_smul_sliceHiggs, sliceR_apply]
  congr 1
  simp only [resRotParam, Matrix.cons_val, Fin.isValue]
  first | rfl | rw [h]

end TwoHiggsDoublet
