/-
Copyright (c) 2026 Justin Findlay. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Justin Findlay
-/
module

public import Physlib.Electromagnetism.Kinematics.FieldStrength
/-!

# Gauge Transformations of the Electromagnetic Potential

## i. Overview

In this module we define gauge transformations of the electromagnetic potential
`A^μ ↦ A^μ + ∂^μ χ` where `χ : SpaceTime d → ℝ` is a smooth gauge function, and prove
that the field strength tensor is invariant under such transformations.

The raised-index gradient `∂^μ χ := η^{μν} ∂_ν χ` is necessary because the bare covariant gradient
`∂_μ χ` does not make `F^{μν}` invariant. The formal witness is
`toFieldStrength_eval_bareGradient_inl_inr` (§B.5), which computes a specific nonzero component of
the field strength of a bare-gradient potential. The invariance theorem
`toFieldStrength_gaugeTransform` doubles as a correctness test of `ofGradient`.

## ii. Key results

- `ofGradient` : The pure-gauge potential `A^μ = η^{μν} ∂_ν χ` built from a gauge function `χ`.
- `gaugeTransform` : The gauge transformation `A^μ ↦ A^μ + ∂^μ χ`.
- `toFieldStrength_ofGradient` : A pure-gauge potential has vanishing field strength.
- `toFieldStrength_gaugeTransform` : The field strength tensor is invariant under gauge
  transformations.
- `toFieldStrength_eval_gaugeTransform` : The components of the field strength tensor are
  invariant under gauge transformations.
- `gaugeTransform_gaugeTransform` : Composing two gauge shifts equals shifting by the sum;
  upgrades one-step F-invariance to invariance along any finite chain.
- `ofGradient_equivariant` : `ofGradient` intertwines the Lorentz action with function composition.
- `gaugeTransform_equivariant` : Gauge transformations commute with Lorentz transformations.
- `toFieldStrength_eval_bareGradient_inl_inr` : The `(inl 0, inr i)` field-strength component of
  the bare-gradient potential `χ(x) = x⁰·xⁱ` equals `2`; in particular the bare gradient does
  not give a gauge-invariant field strength (necessity of the metric contraction in `ofGradient`).

## iii. Table of contents

- A. The pure-gauge potential
  - A.1. Definition and basic lemmas
  - A.2. Differentiability of the pure-gauge potential
  - A.3. Vanishing field strength of the pure-gauge potential
  - A.4. Lorentz equivariance of the pure-gauge potential
- B. Gauge transformations
  - B.1. Definition and basic lemmas
  - B.2. Invariance of the field strength
  - B.3. Group structure of gauge shifts
  - B.4. Equivariance under Lorentz transformations
  - B.5. Necessity: bare gradient does not give gauge invariance

## iv. References

* https://en.wikipedia.org/wiki/Mathematical_descriptions_of_the_electromagnetic_field#Gauge_freedom.
  [ref: wiki_em_field_gauge_freedom]
-/

@[expose] public section
namespace Electromagnetism
open Module realLorentzTensor
open TensorSpecies
open Tensor

namespace ElectromagneticPotential

open TensorSpecies
open Tensor
open SpaceTime
open TensorProduct
open minkowskiMatrix Tensorial
open Lorentz

attribute [-simp] Fintype.sum_sum_type
attribute [-simp] Nat.succ_eq_add_one
/-!

## A. The pure-gauge potential

-/

/-!

### A.1. Definition and basic lemmas

-/

/-- The pure-gauge electromagnetic potential `A^μ = ∂^μ χ = η^{μν} ∂_ν χ` built from a
  gauge function `χ`. The metric-contracted form `∑ κ, η μ κ * ∂_ κ χ` is the definition;
  the diagonal form (which equals `η μ μ * ∂_ μ χ` since `η` is diagonal) is derived in
  `ofGradient_apply`. -/
noncomputable def ofGradient {d} (χ : SpaceTime d → ℝ) : ElectromagneticPotential d where
  val x μ := ∑ κ, η μ κ * ∂_ κ χ x

/-- Unfolding of the summed definition of `ofGradient`. -/
lemma ofGradient_apply_sum {d} (χ : SpaceTime d → ℝ) (x : SpaceTime d) (μ : Fin 1 ⊕ Fin d) :
    ofGradient χ x μ = ∑ κ, η μ κ * ∂_ κ χ x := rfl

/-- Evaluation of `ofGradient` in the diagonal form; the off-diagonal entries of `η` vanish so
  only the `κ = μ` term survives. -/
lemma ofGradient_apply {d} (χ : SpaceTime d → ℝ) (x : SpaceTime d) (μ : Fin 1 ⊕ Fin d) :
    ofGradient χ x μ = η μ μ * ∂_ μ χ x := by
  rw [ofGradient_apply_sum]
  rw [Finset.sum_eq_single μ]
  · intro κ _ hκ
    rw [minkowskiMatrix.off_diag_zero (Ne.symm hκ)]
    simp
  · simp

/-- The pure-gauge potential built from the zero gauge function has all components zero. -/
lemma ofGradient_zero {d} (x : SpaceTime d) (μ : Fin 1 ⊕ Fin d) :
    ofGradient (0 : SpaceTime d → ℝ) x μ = 0 := by
  rw [ofGradient_apply]
  simp [SpaceTime.deriv_eq]

/-- `ofGradient` is additive in the gauge function (when both summands are differentiable). -/
lemma ofGradient_add {d} {χ₁ χ₂ : SpaceTime d → ℝ}
    (hχ₁ : Differentiable ℝ χ₁) (hχ₂ : Differentiable ℝ χ₂) :
    ofGradient (χ₁ + χ₂) = ofGradient χ₁ + ofGradient χ₂ := by
  apply eq_of_val_eq; funext x μ
  show ofGradient (χ₁ + χ₂) x μ = ofGradient χ₁ x μ + ofGradient χ₂ x μ
  simp only [ofGradient_apply, SpaceTime.deriv_eq,
    fderiv_add hχ₁.differentiableAt hχ₂.differentiableAt, _root_.add_apply,
    mul_add]

/-!

### A.2. Differentiability of the pure-gauge potential

-/

/-- The pure-gauge potential is differentiable when `χ` is `C^2`. -/
lemma differentiable_ofGradient {d} {χ : SpaceTime d → ℝ} (hχ : ContDiff ℝ 2 χ) :
    Differentiable ℝ (ofGradient χ) := by
  show Differentiable ℝ (ofGradient χ).val
  rw [← SpaceTime.differentiable_vector]
  intro μ
  simp_rw [ofGradient_apply]
  exact (SpaceTime.differentiable_deriv μ χ hχ).const_mul _

/-- The pure-gauge potential is `C^n` when `χ` is `C^{n+1}`. -/
lemma contDiff_ofGradient {n} {d} {χ : SpaceTime d → ℝ} (hχ : ContDiff ℝ (n + 1) χ) :
    ContDiff ℝ n (ofGradient χ) := by
  show ContDiff ℝ n (ofGradient χ).val
  rw [← SpaceTime.contDiff_vector]
  intro μ
  simp_rw [ofGradient_apply]
  have h := SpaceTime.contDiff_deriv μ χ hχ
  fun_prop

/-!

### A.3. Vanishing field strength of the pure-gauge potential

-/

/-- A pure-gauge potential has vanishing field strength. -/
lemma toFieldStrength_ofGradient {d} {χ : SpaceTime d → ℝ} (hχ : ContDiff ℝ 2 χ)
    (x : SpaceTime d) : (ofGradient χ).toFieldStrength x = 0 := by
  rw [congrFun (toFieldStrength_eq_sum_basis_eval (A := ofGradient χ)) x]
  refine Finset.sum_eq_zero fun μ _ => Finset.sum_eq_zero fun ν _ => ?_
  rw [toFieldStrength_eval_apply_eq_single]
  rw [SpaceTime.deriv_apply_eq μ ν (ofGradient χ) (differentiable_ofGradient hχ),
    SpaceTime.deriv_apply_eq ν μ (ofGradient χ) (differentiable_ofGradient hχ)]
  simp only [ofGradient_apply]
  rw [fderiv_const_mul (SpaceTime.differentiable_deriv μ χ hχ).differentiableAt,
    fderiv_const_mul (SpaceTime.differentiable_deriv ν χ hχ).differentiableAt]
  simp only [FunLike.coe_smul, Pi.smul_apply, smul_eq_mul]
  -- use Clairaut: ∂_ μ (∂_ ν χ) x = ∂_ ν (∂_ μ χ) x, so the two terms cancel
  have heq : fderiv ℝ (∂_ ν χ) x (Lorentz.Vector.basis μ) =
      fderiv ℝ (∂_ μ χ) x (Lorentz.Vector.basis ν) := by
    change ∂_ μ (∂_ ν χ) x = ∂_ ν (∂_ μ χ) x
    rw [← SpaceTime.deriv_commute ν μ χ hχ]
  rw [heq, mul_left_comm, sub_self, zero_smul]

/-!

### A.4. Lorentz equivariance of the pure-gauge potential

`ofGradient` intertwines the Lorentz action on potentials with composition by Λ⁻¹ on the gauge
function: `Λ • ofGradient χ = ofGradient (χ ∘ (Λ⁻¹ • ·))`. The proof reduces to the
metric-commutativity identity `Λ * η = η * (Λ⁻¹)ᵀ`, which is the defining property of the
Lorentz group (`LorentzGroup.comm_minkowskiMatrix`).

-/

/-- `ofGradient` intertwines the Lorentz action on potentials with composition by Λ⁻¹ on the
  gauge function: `Λ • ofGradient χ = ofGradient (χ ∘ (Λ⁻¹ • ·))`. -/
lemma ofGradient_equivariant {d} (χ : SpaceTime d → ℝ) (hχ : Differentiable ℝ χ)
    (Λ : LorentzGroup d) :
    Λ • ofGradient χ = ofGradient (χ ∘ (Λ⁻¹ • ·)) := by
  -- The metric-commutativity row identity, extracted from `comm_minkowskiMatrix`:
  -- ∑ ν, Λ.1 μ ν * η ν κ = ∑ ν, η μ ν * (Λ⁻¹).1 κ ν
  have hmetric : ∀ (μ κ : Fin 1 ⊕ Fin d),
      ∑ ν, Λ.1 μ ν * η ν κ = ∑ ν, η μ ν * (Λ⁻¹).1 κ ν := by
    intro μ κ
    -- comm_minkowskiMatrix: Λ.1 * η = η * (Λ⁻¹)ᵀ, applied at (μ, κ)
    have h := congr_fun₂ (LorentzGroup.comm_minkowskiMatrix (Λ := Λ)) μ κ
    simp only [Matrix.mul_apply, LorentzGroup.transpose_val, Matrix.transpose_apply] at h
    exact h
  apply eq_of_val_eq; funext x μ
  -- Let a κ = ∂_ κ χ (Λ⁻¹ • x). Both sides equal ∑ κ, (∑ ν, Λ.1 μ ν * η ν κ) * a κ.
  set a : Fin 1 ⊕ Fin d → ℝ := fun κ => ∂_ κ χ (Λ⁻¹ • x)
  -- Expand LHS: action_val → smul_eq_sum → ofGradient_apply_sum → reassociate + factor
  have hlhs : (Λ • ofGradient χ).val x μ = ∑ κ, (∑ ν, Λ.1 μ ν * η ν κ) * a κ := by
    simp only [ElectromagneticPotential.action_val, Lorentz.Vector.smul_eq_sum, a,
      ofGradient_apply_sum, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro κ _
    simp_rw [← mul_assoc]
    rw [← Finset.sum_mul]
  -- Expand RHS: ofGradient_apply_sum → deriv_comp_lorentz_action → sum_comm + factor + hmetric
  have hrhs : (ofGradient (χ ∘ (Λ⁻¹ • ·))).val x μ = ∑ κ, (∑ ν, Λ.1 μ ν * η ν κ) * a κ := by
    simp only [ofGradient_apply_sum, a]
    conv_lhs =>
      enter [2, ν]
      rw [show ∂_ ν (χ ∘ (Λ⁻¹ • ·)) x = ∂_ ν (fun y => χ (Λ⁻¹ • y)) x from rfl,
        SpaceTime.deriv_comp_lorentz_action ν χ hχ Λ⁻¹ x]
    simp only [smul_eq_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro κ _
    simp_rw [← mul_assoc]
    rw [← Finset.sum_mul, ← hmetric]
  rw [hlhs, hrhs]

/-!

## B. Gauge transformations

-/

/-!

### B.1. Definition and basic lemmas

-/

/-- The gauge transformation `A^μ ↦ A^μ + ∂^μ χ` of an electromagnetic potential. -/
noncomputable def gaugeTransform {d} (χ : SpaceTime d → ℝ) (A : ElectromagneticPotential d) :
    ElectromagneticPotential d := A + ofGradient χ

/-- Evaluation of `gaugeTransform`. -/
lemma gaugeTransform_apply {d} (χ : SpaceTime d → ℝ) (A : ElectromagneticPotential d)
    (x : SpaceTime d) : gaugeTransform χ A x = A x + ofGradient χ x := by
  simp [gaugeTransform, add_apply]

/-!

### B.2. Invariance of the field strength

The key ingredient — that a pure-gauge potential has vanishing field strength — is proved in §A.3
(`toFieldStrength_ofGradient`).

-/

/-- The field strength tensor is invariant under gauge transformations. -/
lemma toFieldStrength_gaugeTransform {d} (A : ElectromagneticPotential d)
    (χ : SpaceTime d → ℝ) (hA : Differentiable ℝ A) (hχ : ContDiff ℝ 2 χ) (x : SpaceTime d) :
    (gaugeTransform χ A).toFieldStrength x = A.toFieldStrength x := by
  rw [gaugeTransform, toFieldStrength_add A (ofGradient χ) x hA (differentiable_ofGradient hχ),
    toFieldStrength_ofGradient hχ, add_zero]

/-- The components of the field strength tensor are invariant under gauge transformations. -/
lemma toFieldStrength_eval_gaugeTransform {d} (A : ElectromagneticPotential d)
    (χ : SpaceTime d → ℝ) (hA : Differentiable ℝ A) (hχ : ContDiff ℝ 2 χ) (x : SpaceTime d)
    (μ ν : Fin 1 ⊕ Fin d) :
    toScalar {(gaugeTransform χ A).toFieldStrength x | [μ] [ν]}ᵀ =
    toScalar {A.toFieldStrength x | [μ] [ν]}ᵀ := by
  rw [toFieldStrength_gaugeTransform A χ hA hχ]

/-!

### B.3. Group structure of gauge shifts

Composing two gauge shifts by χ₁ and χ₂ is the same as shifting by χ₁ + χ₂. Together with
`gaugeTransform_zero` this shows that the map `χ ↦ (A ↦ gaugeTransform χ A)` is a group action
of the additive group of smooth functions. (We do not build the formal `MulAction` here —
the composition lemma is the agreeable core, and the rest is straightforward from it.)

The `ofGradient` lemmas used here — `ofGradient_zero` and `ofGradient_add` — are proved in §A.1.

-/

/-- Shifting by the zero gauge function is the identity. -/
lemma gaugeTransform_zero {d} (A : ElectromagneticPotential d) :
    gaugeTransform (0 : SpaceTime d → ℝ) A = A := by
  apply eq_of_val_eq; funext x μ
  show gaugeTransform (0 : SpaceTime d → ℝ) A x μ = A x μ
  simp [gaugeTransform, add_apply, ofGradient_zero]

/-- Two successive gauge shifts compose: shifting by χ₂ then χ₁ equals shifting by χ₁ + χ₂.
  This upgrades one-step F-invariance to invariance along any finite chain of gauge shifts. -/
lemma gaugeTransform_gaugeTransform {d} (A : ElectromagneticPotential d)
    (χ₁ χ₂ : SpaceTime d → ℝ) (hχ₁ : Differentiable ℝ χ₁) (hχ₂ : Differentiable ℝ χ₂) :
    gaugeTransform χ₁ (gaugeTransform χ₂ A) = gaugeTransform (χ₁ + χ₂) A := by
  apply eq_of_val_eq; funext x μ
  simp only [gaugeTransform, add_apply]
  rw [ofGradient_add hχ₁ hχ₂]
  simp [add_apply, add_comm, add_left_comm]

/-!

### B.4. Equivariance under Lorentz transformations

The gauge-transformation map commutes with the Lorentz group action: applying Λ to a potential
and then gauge-transforming by χ is the same as gauge-transforming by `χ ∘ (Λ⁻¹ • ·)` and then
applying Λ. The proof delegates to `ofGradient_equivariant` (§A.4).

-/

/-- Gauge transformations commute with Lorentz transformations: applying Λ and then performing
  a gauge transformation by `χ` equals performing a gauge transformation by `χ ∘ (Λ⁻¹ • ·)`
  and then applying Λ. -/
lemma gaugeTransform_equivariant {d} (A : ElectromagneticPotential d)
    (χ : SpaceTime d → ℝ) (hχ : Differentiable ℝ χ) (Λ : LorentzGroup d) :
    Λ • gaugeTransform χ A = gaugeTransform (χ ∘ (Λ⁻¹ • ·)) (Λ • A) := by
  -- Unfold both sides to Λ • A + ofGradient (χ ∘ (Λ⁻¹ • ·))
  simp only [gaugeTransform]
  rw [← ofGradient_equivariant χ hχ Λ]
  -- Goal: Λ • (A + ofGradient χ) = Λ • A + Λ • ofGradient χ
  apply eq_of_val_eq; funext x μ
  simp only [ElectromagneticPotential.action_val, add_val, Pi.add_apply,
    Lorentz.Vector.smul_add]

/-!

### B.5. Necessity: bare gradient does not give gauge invariance

We exhibit a concrete gauge function `χ(x) = x⁰·xⁱ` whose **bare** covariant gradient
`B^μ := ∂_μ χ` has a nonzero field-strength component (equal to `2`), certifying that the metric
contraction in `ofGradient` is required for gauge invariance.

-/

/-- The `(inl 0, inr i)` component of the field strength tensor of the bare-gradient potential
  `B^μ := ∂_μ χ` for `χ(x) = x⁰·xⁱ` equals `2`. This witnesses that the bare covariant gradient
  does not produce a gauge-invariant field strength, so the raised-index contraction
  `η^{μν} ∂_ν χ` in `ofGradient` is necessary (see the module overview). -/
lemma toFieldStrength_eval_bareGradient_inl_inr {d : ℕ} (i : Fin d)
    (x : SpaceTime d) :
    let χ : SpaceTime d → ℝ := fun y => y (Sum.inl 0) * y (Sum.inr i)
    let B : ElectromagneticPotential d := ⟨fun y μ => ∂_ μ χ y⟩
    toScalar {B.toFieldStrength x | [Sum.inl 0] [Sum.inr i]}ᵀ = 2 := by
  intro χ B
  have hχ : ContDiff ℝ 2 χ := by
    show ContDiff ℝ 2 (fun y : SpaceTime d => y (Sum.inl 0) * y (Sum.inr i))
    fun_prop
  have hB : Differentiable ℝ B := by
    rw [← SpaceTime.differentiable_vector]; intro μ
    exact SpaceTime.differentiable_deriv μ χ hχ
  -- F^{μν} = η μ μ * ∂_ μ B x ν − η ν ν * ∂_ ν B x μ
  rw [toFieldStrength_eval_apply_eq_single]
  -- Expand ∂_ μ B x ν as ∂_ μ (fun y => ∂_ ν χ y) x = ∂_ μ (∂_ ν χ) x
  rw [SpaceTime.deriv_apply_eq (Sum.inl 0) (Sum.inr i) B hB,
      SpaceTime.deriv_apply_eq (Sum.inr i) (Sum.inl 0) B hB]
  -- Now compute the mixed partials of χ = t·xⁱ using fderiv_fun_mul + deriv_coord
  -- ∂_t χ = xⁱ, ∂_{xⁱ} χ = t; so ∂_{xⁱ}(∂_t χ) = 1 and ∂_t(∂_{xⁱ} χ) = 1
  have hfderiv : ∀ (y : SpaceTime d),
      fderiv ℝ χ y = (y (Sum.inr i)) • Lorentz.Vector.coordCLM (Sum.inl 0) +
                      (y (Sum.inl 0)) • Lorentz.Vector.coordCLM (Sum.inr i) := fun y => by
    have h : fderiv ℝ (fun z : SpaceTime d => z (Sum.inl 0) * z (Sum.inr i)) y =
        (y (Sum.inr i)) • Lorentz.Vector.coordCLM (Sum.inl 0) +
        (y (Sum.inl 0)) • Lorentz.Vector.coordCLM (Sum.inr i) := by
      have hmul := fderiv_fun_mul (𝕜 := ℝ)
        (hc := (Lorentz.Vector.coordCLM (Sum.inl 0)).differentiableAt)
        (hd := (Lorentz.Vector.coordCLM (Sum.inr i)).differentiableAt) (x := y)
      simp only [ContinuousLinearMap.fderiv, Lorentz.Vector.coordCLM_apply] at hmul
      -- hmul: fderiv ... y = y (Sum.inl 0) • coordCLM (Sum.inr i)
      --                         + y (Sum.inr i) • coordCLM (Sum.inl 0)
      -- goal: ... = y (Sum.inr i) • coordCLM (Sum.inl 0)
      --               + y (Sum.inl 0) • coordCLM (Sum.inr i)
      rw [hmul, add_comm]
    exact h
  simp only [SpaceTime.deriv_eq, B]
  simp_rw [hfderiv]
  simp only [_root_.add_apply, FunLike.coe_smul,
    Pi.smul_apply, Lorentz.Vector.coordCLM_apply, smul_eq_mul, Lorentz.Vector.basis_apply]
  simp only [mul_ite, mul_one, mul_zero, ite_add, zero_add, ite_true]
  simp only [minkowskiMatrix.inl_0_inl_0, minkowskiMatrix.inr_i_inr_i]
  simp only [reduceCtorEq, ↓reduceIte, add_zero]
  simp only [Lorentz.Vector.fderiv_coord, Lorentz.Vector.coordCLM_apply,
    Lorentz.Vector.basis_apply, ↓reduceIte]
  norm_num

/-- The field strength of the bare-gradient potential `B^μ := ∂_μ χ` for
  `χ(x) = x⁰·xⁱ` is nonzero (follows from `toFieldStrength_eval_bareGradient_inl_inr`). -/
lemma toFieldStrength_bareGradient_ne_zero {d : ℕ} (i : Fin d)
    (x : SpaceTime d) :
    let χ : SpaceTime d → ℝ := fun y => y (Sum.inl 0) * y (Sum.inr i)
    let B : ElectromagneticPotential d := ⟨fun y μ => ∂_ μ χ y⟩
    B.toFieldStrength x ≠ 0 := by
  intro χ B h
  have h2 := toFieldStrength_eval_bareGradient_inl_inr i x
  dsimp only at h2
  rw [h] at h2
  simp only [map_zero] at h2
  norm_num at h2

end ElectromagneticPotential

end Electromagnetism
