/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Particles.BeyondTheStandardModel.TwoHDM.GramMatrix
/-!
# The gauge torus acting on Higgs vectors

The SU(2) Cartan element diag(a, ā), which with ofU1Subgroup realises the gauge torus.

## i. Overview

The maximal torus of the gauge group acting on a Higgs doublet is the group of diagonal phase
rotations `diag(a, b)` of the two components. We realise it using

* the `SU(2)` Cartan element `diag(a, ā)` (constructed here as `gaugeCartan`), and
* the existing `ofU1Subgroup`, whose action is `diag(1, μ)`.

Together these realise an arbitrary diagonal phase `diag(a, b)`, which is the symmetry underlying
the charge-balancing ("Condition A") of the effective potential on the orbit representatives.

## ii. Key results

- `StandardModel.GaugeGroupI.gaugeCartan` : the Cartan `SU(2)` gauge element `diag(a, ā)`.
- `StandardModel.GaugeGroupI.gaugeCartan_smul_eq` : it acts on a Higgs vector as `diag(a, ā)`.

## iii. Table of contents

- A. The Cartan gauge element

## iv. References

* None.

-/

@[expose] public section

noncomputable section

namespace StandardModel
namespace GaugeGroupI

open Matrix Complex

/-!

## A. The Cartan gauge element

-/

/-- The Cartan `SU(2)` gauge element `diag(a, ā)`, for `a` a phase. -/
noncomputable def gaugeCartan (a : unitary ℂ) : GaugeGroupI :=
  (1,
  ⟨!![(a : ℂ), 0; 0, (star a : ℂ)], by
    have h1 : (starRingEnd ℂ) (a : ℂ) * (a : ℂ) = 1 := a.2.1
    have h2 : (a : ℂ) * (starRingEnd ℂ) (a : ℂ) = 1 := a.2.2
    simp only [SetLike.mem_coe]
    rw [mem_unitaryGroup_iff']
    funext i j
    rw [Matrix.mul_apply]
    fin_cases i <;> fin_cases j <;>
      simp [Fin.sum_univ_two, h1, h2], by
    simp only [RCLike.star_def, SetLike.mem_coe, MonoidHom.mem_mker, coe_detMonoidHom,
      det_fin_two_of, mul_zero, sub_zero]
    simpa using a.2.2⟩, 1)

@[simp]
lemma gaugeCartan_toU1 (a : unitary ℂ) : (gaugeCartan a).toU1 = 1 := rfl

@[simp]
lemma gaugeCartan_toSU2_coe (a : unitary ℂ) :
    ((gaugeCartan a).toSU2 : Matrix (Fin 2) (Fin 2) ℂ) = !![(a : ℂ), 0; 0, (star a : ℂ)] := rfl

/-- The Cartan element acts as the diagonal matrix `diag(a, ā)`. -/
lemma gaugeCartan_smul_eq (a : unitary ℂ) (φ : HiggsVec) :
    HiggsVec.repGaugeGroupI (gaugeCartan a) φ =
      WithLp.toLp 2 (!![(a : ℂ), 0; 0, (star a : ℂ)] *ᵥ φ.ofLp) := by
  rw [HiggsVec.repGaugeGroupI_apply, gaugeCartan_toU1, one_pow, one_smul, gaugeCartan_toSU2_coe]

end GaugeGroupI
end StandardModel
