/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.ClassicalFieldTheory.GaugeTheory.Matter.MatterField
/-!
# Charged matter fields under `U(1)` jets

## i. Overview

A field valued in a complex vector space `V` with integer charge `n` transforms under a
`U(1)` gauge transformation `U = e^{iχ}` by `ψ ↦ U^n ψ`. On jets this is multiplication of the
jet-ring factor of `JetRing ⊗[ℂ] V` by the unitary power series `U^n`; the action is
manifestly fibrewise. `MatterField.charged` packages a Lorentz representation, a charge and
a mass weight into a matter field for the jet gauge group `unitary JetRing` of `U(1)`.

## ii. Key results

- `MatterField.chargeRep` : the charge-`n` action of `U(1)` jets on the jets of a field.
- `MatterField.chargeRep_smul` : the action is fibrewise.
- `MatterField.charged` : the matter field of charge `n`.

## iii. Table of contents

- A. Powers of a unitary jet
- B. The charge action on jets
- C. Charged matter fields

-/

@[expose] public section

namespace MatterField

open Matrix MatrixGroups TensorProduct

variable {V : Type} [AddCommGroup V] [Module ℂ V]

/-!

## A. Powers of a unitary jet

-/

/-- The unitary power series `U ^ n` of a `U(1)` jet, for an integer charge `n`. -/
noncomputable def chargePow (n : ℤ) (U : unitary JetRing) : JetRing :=
  ((Unitary.toUnits U ^ n : JetRingˣ) : JetRing)

lemma chargePow_one (n : ℤ) : chargePow n 1 = 1 := by
  simp [chargePow]

lemma chargePow_mul (n : ℤ) (U W : unitary JetRing) :
    chargePow n (U * W) = chargePow n U * chargePow n W := by
  simp [chargePow, mul_zpow]

/-!

## B. The charge action on jets

-/

/-- **The charge-`n` action of `U(1)` jets on the jets of a `V`-valued field**:
  multiplication of the jet-ring factor by `U ^ n`. -/
noncomputable def chargeRep (n : ℤ) (V : Type) [AddCommGroup V] [Module ℂ V] :
    Representation ℂ (unitary JetRing) (JetRing ⊗[ℂ] V) where
  toFun U := LinearMap.rTensor V (LinearMap.mulLeft ℂ (chargePow n U))
  map_one' := by
    rw [chargePow_one, LinearMap.mulLeft_one, LinearMap.rTensor_id]
    rfl
  map_mul' U W := by
    rw [chargePow_mul,
      show LinearMap.mulLeft ℂ (chargePow n U * chargePow n W)
        = (LinearMap.mulLeft ℂ (chargePow n U)) ∘ₗ (LinearMap.mulLeft ℂ (chargePow n W)) from
        LinearMap.ext fun z => mul_assoc _ _ z,
      LinearMap.rTensor_comp]
    rfl

lemma chargeRep_tmul (n : ℤ) (U : unitary JetRing) (f : JetRing) (v : V) :
    chargeRep n V U (f ⊗ₜ[ℂ] v) = (chargePow n U * f) ⊗ₜ[ℂ] v :=
  LinearMap.rTensor_tmul _ _ _ _

/-- **The charge action is fibrewise**: it commutes with multiplication by scalar jets. -/
lemma chargeRep_smul (n : ℤ) (U : unitary JetRing) (χ : JetRing) (z : JetRing ⊗[ℂ] V) :
    chargeRep n V U (χ • z) = χ • chargeRep n V U z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul f v =>
    rw [TensorProduct.smul_tmul', chargeRep_tmul, chargeRep_tmul, TensorProduct.smul_tmul',
      smul_eq_mul, smul_eq_mul, mul_left_comm]
  | add x y hx hy => rw [smul_add, map_add, map_add, hx, hy, smul_add]

/-!

## C. Charged matter fields

-/

/-- **The charged matter field**: a field with values in `V`, Lorentz representation
  `repLorentz`, electric charge `n` and mass weight `w`, as a matter field for the jets of
  `U(1)`. -/
noncomputable def charged [Module.Free ℂ V] [Module.Finite ℂ V]
    (repLorentz : Representation ℂ SL(2,ℂ) V) (n : ℤ) (w : ℕ) :
    MatterField (unitary JetRing) where
  V := V
  repLorentz := repLorentz
  repJet := chargeRep n V
  repJet_smul := chargeRep_smul n
  massWeight := w

@[simp]
lemma charged_V [Module.Free ℂ V] [Module.Finite ℂ V]
    (repLorentz : Representation ℂ SL(2,ℂ) V) (n : ℤ) (w : ℕ) :
    (charged repLorentz n w).V = V := rfl

end MatterField
