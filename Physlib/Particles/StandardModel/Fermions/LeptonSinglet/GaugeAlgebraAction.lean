/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Particles.StandardModel.Fermions.LeptonSinglet.Basic
public import Physlib.Particles.StandardModel.GaugeAlgebra.InfinitesimalAction
public import Physlib.Particles.StandardModel.GaugeBosons.GaugeJetAlgebra.GaugeAction
/-!
# The gauge-algebra action on the charged-lepton singlet

## i. Overview

The charged-lepton singlet carries the `(1, 1)_{-6}` representation of the gauge group,
so the infinitesimal action of the gauge algebra is scalar: multiplication by
`i` times `-6` times the `u(1)` value of the algebra element. This file defines that
action and proves it is the infinitesimal action underlying the jet gauge action, in
the sense of `GaugeAlgebra.IsInfinitesimalActionOf`.

Because the singlet has no colour or weak index, the jet gauge action is multiplication
of the jet-ring factor by the hypercharge phase `(star u) ^ 6`, and both laws of
`IsInfinitesimalActionOf` reduce to scalar identities about the base-point Taylor
coefficients of that phase: the derivative identity `∂ ((star u) ^ 6) =
-(i (-6) ω) (star u) ^ 6` against the `u(1)` value of the Maurer–Cartan form, and the
trivial `u(1)` adjoint equivariance.

## ii. Key results

- `gaugeAlgebraAction` : the infinitesimal `(1, 1)_{-6}` action of the gauge algebra.
- `jetPhase` : the hypercharge phase `(star u) ^ 6` of the jet gauge action.
- `repCoeff_eq` : the base-point Taylor coefficients of the jet gauge action are the
  base-point Taylor coefficients of the hypercharge phase.
- `jetPhase_pderiv` : the derivative identity for the hypercharge phase.
- `isInfinitesimalActionOf` : the gauge-algebra action is the infinitesimal action
  underlying the jet gauge action.

## iii. Table of contents

- A. The infinitesimal action of the gauge algebra
- B. The hypercharge phase of the jet gauge action
- C. The Taylor coefficients of the jet gauge action
- D. The derivative identity for the hypercharge phase
- E. The infinitesimal action underlies the jet gauge action

-/

@[expose] public section

namespace StandardModel

namespace LeptonSinglet

open TensorProduct MvPowerSeries

/-!

## A. The infinitesimal action of the gauge algebra

The `(1, 1)_{-6}` representation acts through the `u(1)` factor alone, so its
derivative is scalar multiplication by `i (-6)` times the `u(1)` value.

-/

/-- **The infinitesimal action of the gauge algebra on the charged-lepton singlet**:
  the derivative of the `(1, 1)_{-6}` action of the gauge group — scalar
  multiplication by `i` times `-6` times the `u(1)` value, real-linear in the algebra
  slot and complex-linear in the value slot — the form consumed by
  `GaugeAlgebra.IsInfinitesimalActionOf`. -/
noncomputable def gaugeAlgebraAction :
    GaugeAlgebra →ₗ[ℝ] LeptonSinglet →ₗ[ℂ] LeptonSinglet where
  toFun c := (Complex.I * (-(6 : ℂ) * c.toU1Value))
    • (LinearMap.id : LeptonSinglet →ₗ[ℂ] LeptonSinglet)
  map_add' c₁ c₂ := by
    rw [GaugeAlgebra.add_toU1Value,
      show Complex.I * (-(6 : ℂ) * (c₁.toU1Value + c₂.toU1Value))
          = Complex.I * (-(6 : ℂ) * c₁.toU1Value)
            + Complex.I * (-(6 : ℂ) * c₂.toU1Value) from by ring,
      add_smul]
  map_smul' r c := by
    rw [GaugeAlgebra.smul_toU1Value, RingHom.id_apply,
      show r • c.toU1Value = algebraMap ℝ ℂ r * c.toU1Value from by
        rw [← algebraMap_smul ℂ r c.toU1Value, smul_eq_mul],
      show Complex.I * (-(6 : ℂ) * (algebraMap ℝ ℂ r * c.toU1Value))
          = algebraMap ℝ ℂ r * (Complex.I * (-(6 : ℂ) * c.toU1Value)) from by ring,
      mul_smul, algebraMap_smul]

/-- The gauge-algebra action on the charged-lepton singlet is scalar multiplication
  by `i` times `-6` times the `u(1)` value. -/
lemma gaugeAlgebraAction_apply (c : GaugeAlgebra) :
    gaugeAlgebraAction c
      = (Complex.I * (-(6 : ℂ) * c.toU1Value))
        • (LinearMap.id : LeptonSinglet →ₗ[ℂ] LeptonSinglet) := rfl

/-!

## B. The hypercharge phase of the jet gauge action

The jet gauge action multiplies the jet-ring factor by the hypercharge power series
`(star u) ^ 6`: the scalar analogue of the colour matrix of a coloured species.

-/

/-- The `JetRing`-valued hypercharge phase of the jet gauge action on the
  charged-lepton singlet: the `-6` hypercharge power series `(star u) ^ 6` of the
  gauge jet. -/
noncomputable def jetPhase (U : JetGaugeGroupI) : JetRing :=
  (star ((U.2.2 : unitary JetRing) : JetRing)) ^ 6

/-- The hypercharge phase, unfolded. -/
lemma jetPhase_eq (U : JetGaugeGroupI) :
    jetPhase U = (star ((U.2.2 : unitary JetRing) : JetRing)) ^ 6 := rfl

/-- The jet gauge action on the charged-lepton singlet is multiplication of the
  jet-ring factor by the hypercharge phase. -/
lemma repJetGaugeGroupI_eq_jetPhase (U : JetGaugeGroupI) :
    repJetGaugeGroupI U
      = LinearMap.rTensor LeptonSinglet (LinearMap.mulLeft ℂ (jetPhase U)) := rfl

/-!

## C. The Taylor coefficients of the jet gauge action

-/

/-- The iterated formal derivative is `ℂ`-homogeneous. -/
private lemma foldl_pderiv_smul (x : Multiset (Fin 1 ⊕ Fin 3)) (z : ℂ) (f : JetRing) :
    x.foldl (fun h ρ => pderiv ℂ ρ h) (z • f)
      = z • x.foldl (fun h ρ => pderiv ℂ ρ h) f := by
  induction x using Multiset.induction_on generalizing f with
  | empty => rfl
  | cons ν t ih => rw [Multiset.foldl_cons, Derivation.map_smul, ih, Multiset.foldl_cons]

/-- The iterated formal derivative of a negation. -/
private lemma foldl_pderiv_neg (x : Multiset (Fin 1 ⊕ Fin 3)) (f : JetRing) :
    x.foldl (fun h ρ => pderiv ℂ ρ h) (-f)
      = -(x.foldl (fun h ρ => pderiv ℂ ρ h) f) := by
  induction x using Multiset.induction_on generalizing f with
  | empty => rfl
  | cons ν t ih => rw [Multiset.foldl_cons, map_neg, ih, Multiset.foldl_cons]

/-- The iterated formal derivative of a jet of charged-lepton singlets acts on the
  jet-ring factor of a pure tensor. -/
private lemma jetIteratedDeriv_tmul (x : Multiset (Fin 1 ⊕ Fin 3)) (f : JetRing)
    (ψ : LeptonSinglet) :
    jetIteratedDeriv x (f ⊗ₜ[ℂ] ψ)
      = (x.foldl (fun h ρ => pderiv ℂ ρ h) f) ⊗ₜ[ℂ] ψ := by
  induction x using Multiset.induction_on generalizing f with
  | empty => rw [jetIteratedDeriv_zero]; rfl
  | cons μ t ih =>
    rw [jetIteratedDeriv_cons, LinearMap.comp_apply, ih, jetDeriv_tmul,
      Multiset.foldl_cons, JetRing.foldl_pderiv_pderiv]

/-- Scalar multiples of the identity compose through multiplication. -/
private lemma smul_id_comp (a b : ℂ) :
    (a • (LinearMap.id : LeptonSinglet →ₗ[ℂ] LeptonSinglet))
        ∘ₗ (b • (LinearMap.id : LeptonSinglet →ₗ[ℂ] LeptonSinglet))
      = (a * b) • (LinearMap.id : LeptonSinglet →ₗ[ℂ] LeptonSinglet) := by
  refine LinearMap.ext fun l => ?_
  simp [mul_smul]

/-- A multiset sum of scalar multiples of the identity is the scalar multiple by the
  sum. -/
private lemma sum_map_smul_id {α : Type*} (m : Multiset α) (z : α → ℂ) :
    (m.map fun p => z p • (LinearMap.id : LeptonSinglet →ₗ[ℂ] LeptonSinglet)).sum
      = (m.map z).sum • (LinearMap.id : LeptonSinglet →ₗ[ℂ] LeptonSinglet) := by
  induction m using Multiset.induction_on with
  | empty => simp
  | cons a t ih =>
    rw [Multiset.map_cons, Multiset.sum_cons, ih, Multiset.map_cons,
      Multiset.sum_cons, add_smul]

/-- **The base-point Taylor coefficients of the jet gauge action** on the
  charged-lepton singlet are scalar: multiplication by the base-point Taylor
  coefficients of the hypercharge phase. -/
lemma repCoeff_eq (U : JetGaugeGroupI) (x : Multiset (Fin 1 ⊕ Fin 3)) :
    IsGaugeField.repCoeff repJetGaugeGroupI U x
      = constantCoeff (x.foldl (fun h ρ => pderiv ℂ ρ h) (jetPhase U))
        • (LinearMap.id : LeptonSinglet →ₗ[ℂ] LeptonSinglet) := by
  refine LinearMap.ext fun l => ?_
  rw [show IsGaugeField.repCoeff repJetGaugeGroupI U x l
      = StandardModel.jetEval (StandardModel.jetIteratedDeriv x
          (repJetGaugeGroupI U (StandardModel.jetOfConstant l))) from rfl,
    StandardModel.jetOfConstant_apply, repJetGaugeGroupI_tmul, mul_one,
    jetIteratedDeriv_tmul, StandardModel.jetEval_tmul, jetPhase_eq,
    LinearMap.smul_apply, LinearMap.id_apply]

/-- At the base point, a gauge jet with trivial value acts trivially: the zeroth
  Taylor coefficient of the jet gauge action is the identity. -/
lemma repCoeff_zero_of_eval_eq_one {U : JetGaugeGroupI} (hU : U.eval = 1) :
    IsGaugeField.repCoeff repJetGaugeGroupI U 0 = LinearMap.id := by
  have hu : constantCoeff ((U.2.2 : unitary JetRing) : JetRing) = 1 :=
    Subtype.ext_iff.mp (congrArg (fun p : GaugeGroupI => p.2.2) hU)
  rw [repCoeff_eq, Multiset.foldl_zero, jetPhase_eq, map_pow,
    JetRing.constantCoeff_star, hu, star_one, one_pow, one_smul]


/-!

## D. The derivative identity for the hypercharge phase

-/

/-- **The derivative identity** for the hypercharge phase of the jet gauge action: the
  formal derivative of the phase is minus `i` times `-6` times the `u(1)` value of the
  Maurer–Cartan form, times the phase. -/
lemma jetPhase_pderiv (U : JetGaugeGroupI) (μ : Fin 1 ⊕ Fin 3) :
    pderiv ℂ μ (jetPhase U)
      = -(((Complex.I * (-(6 : ℂ))) • (maurerCartanForm U μ).toU1Value)
          * jetPhase U) := by
  have hleib : ∀ f g : JetRing,
      pderiv ℂ μ (f * g) = pderiv ℂ μ f * g + f * pderiv ℂ μ g := fun f g => by
    rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul, add_comm, mul_comm g]
  have huu : ((U.2.2 : unitary JetRing) : JetRing)
      * star ((U.2.2 : unitary JetRing) : JetRing) = 1 :=
    Unitary.mul_star_self_of_mem (U.2.2 : unitary JetRing).2
  have h0 : pderiv ℂ μ ((U.2.2 : unitary JetRing) : JetRing)
        * star ((U.2.2 : unitary JetRing) : JetRing)
      + ((U.2.2 : unitary JetRing) : JetRing)
        * pderiv ℂ μ (star ((U.2.2 : unitary JetRing) : JetRing)) = 0 := by
    have h := congrArg (pderiv ℂ μ) huu
    rw [hleib, Derivation.map_one_eq_zero] at h
    exact h
  have hsu : pderiv ℂ μ (star ((U.2.2 : unitary JetRing) : JetRing))
      = -(pderiv ℂ μ ((U.2.2 : unitary JetRing) : JetRing)
          * (star ((U.2.2 : unitary JetRing) : JetRing)
            * star ((U.2.2 : unitary JetRing) : JetRing))) := by
    have h1 : star ((U.2.2 : unitary JetRing) : JetRing)
        * (pderiv ℂ μ ((U.2.2 : unitary JetRing) : JetRing)
            * star ((U.2.2 : unitary JetRing) : JetRing)
          + ((U.2.2 : unitary JetRing) : JetRing)
            * pderiv ℂ μ (star ((U.2.2 : unitary JetRing) : JetRing))) = 0 := by
      rw [h0, mul_zero]
    linear_combination h1
      - pderiv ℂ μ (star ((U.2.2 : unitary JetRing) : JetRing)) * huu
  have hiC : (algebraMap ℂ JetRing) Complex.I * (algebraMap ℂ JetRing) Complex.I
      = -1 := by
    rw [← map_mul, Complex.I_mul_I, map_neg, map_one]
  rw [jetPhase_eq, maurerCartanForm_toU1Value, pderiv_pow,
    show (6 : ℕ) - 1 = 5 from rfl, Nat.cast_ofNat, hsu,
    Algebra.smul_def, Algebra.smul_def, map_mul, map_neg, map_ofNat]
  linear_combination (-(6 * pderiv ℂ μ ((U.2.2 : unitary JetRing) : JetRing)
    * (star ((U.2.2 : unitary JetRing) : JetRing)) ^ 7)) * hiC

/-!

## E. The infinitesimal action underlies the jet gauge action

Both laws of `GaugeAlgebra.IsInfinitesimalActionOf` reduce through `repCoeff_eq` to
scalar identities: the Maurer–Cartan Leibniz law is the all-orders product rule at the
base point applied to the derivative identity, and the adjoint intertwining collapses
because the adjoint action on the `u(1)` component is trivial.

-/

set_option maxHeartbeats 1000000 in
/-- **The `(1, 1)_{-6}` action of the gauge algebra is the infinitesimal action
  underlying the jet gauge action on the charged-lepton singlet**: its base-point
  Taylor coefficients obey the Maurer–Cartan Leibniz law and intertwine the action
  with the adjoint transports. -/
theorem isInfinitesimalActionOf :
    GaugeAlgebra.IsInfinitesimalActionOf gaugeAlgebraAction repJetGaugeGroupI := by
  constructor
  · intro U μ x
    have hMcons : constantCoeff ((μ ::ₘ x).foldl (fun h ρ => pderiv ℂ ρ h) (jetPhase U))
        = -((x.antidiagonal.map fun p =>
            Complex.I * (-(6 : ℂ) * (JetGaugeAlgebra.eval (JetGaugeAlgebra.iteratedDeriv
                p.1 (maurerCartanForm U μ))).toU1Value)
              * constantCoeff (p.2.foldl (fun h ρ => pderiv ℂ ρ h) (jetPhase U))).sum) := by
      rw [Multiset.foldl_cons, jetPhase_pderiv, foldl_pderiv_neg, map_neg,
        JetRing.constantCoeff_foldl_pderiv_mul]
      exact congrArg Neg.neg (congrArg Multiset.sum (Multiset.map_congr rfl
        fun p hp => by
          rw [foldl_pderiv_smul, constantCoeff_smul, smul_eq_mul,
            JetGaugeAlgebra.eval_iteratedDeriv_toU1Value]
          ring))
    rw [repCoeff_eq, hMcons, neg_smul, ← sum_map_smul_id]
    exact congrArg Neg.neg (congrArg Multiset.sum (Multiset.map_congr rfl
      fun p hp => by rw [gaugeAlgebraAction_apply, repCoeff_eq, smul_id_comp]))
  · intro U x c
    have hterm : ∀ p : Multiset (Fin 1 ⊕ Fin 3) × Multiset (Fin 1 ⊕ Fin 3),
        gaugeAlgebraAction (IsGaugeField.adjointCoeff U p.1 c)
            ∘ₗ IsGaugeField.repCoeff repJetGaugeGroupI U p.2
          = (Complex.I * (-(6 : ℂ) * constantCoeff (p.1.foldl (fun h ρ => pderiv ℂ ρ h)
                (C c.toU1Value)))
              * constantCoeff (p.2.foldl (fun h ρ => pderiv ℂ ρ h) (jetPhase U)))
            • (LinearMap.id : LeptonSinglet →ₗ[ℂ] LeptonSinglet) := fun p => by
      rw [gaugeAlgebraAction_apply, repCoeff_eq, smul_id_comp,
        IsGaugeField.adjointCoeff_toU1Value]
    have hvan : ∀ p : Multiset (Fin 1 ⊕ Fin 3) × Multiset (Fin 1 ⊕ Fin 3), p.1 ≠ 0 →
        (Complex.I * (-(6 : ℂ) * constantCoeff (p.1.foldl (fun h ρ => pderiv ℂ ρ h)
              (C c.toU1Value)))
            * constantCoeff (p.2.foldl (fun h ρ => pderiv ℂ ρ h) (jetPhase U)))
          • (LinearMap.id : LeptonSinglet →ₗ[ℂ] LeptonSinglet) = 0 := by
      intro p hp
      rw [JetRing.foldl_pderiv_C_of_ne_zero hp, map_zero, mul_zero, mul_zero,
        zero_mul, zero_smul]
    have hcollapse : (x.antidiagonal.map fun p =>
          (Complex.I * (-(6 : ℂ) * constantCoeff (p.1.foldl (fun h ρ => pderiv ℂ ρ h)
                (C c.toU1Value)))
              * constantCoeff (p.2.foldl (fun h ρ => pderiv ℂ ρ h) (jetPhase U)))
            • (LinearMap.id : LeptonSinglet →ₗ[ℂ] LeptonSinglet)).sum
        = (Complex.I * (-(6 : ℂ) * c.toU1Value)
            * constantCoeff (x.foldl (fun h ρ => pderiv ℂ ρ h) (jetPhase U)))
          • (LinearMap.id : LeptonSinglet →ₗ[ℂ] LeptonSinglet) := by
      rw [Multiset.sum_antidiagonal_eq_of_fst_ne_zero x
          (fun p => (Complex.I * (-(6 : ℂ) * constantCoeff (p.1.foldl
                (fun h ρ => pderiv ℂ ρ h) (C c.toU1Value)))
              * constantCoeff (p.2.foldl (fun h ρ => pderiv ℂ ρ h) (jetPhase U)))
            • (LinearMap.id : LeptonSinglet →ₗ[ℂ] LeptonSinglet)) hvan,
        show ((0 : Multiset (Fin 1 ⊕ Fin 3)).foldl (fun h ρ => pderiv ℂ ρ h)
            (C c.toU1Value : JetRing)) = C c.toU1Value from rfl,
        constantCoeff_C]
    rw [repCoeff_eq, gaugeAlgebraAction_apply, smul_id_comp,
      show constantCoeff (x.foldl (fun h ρ => pderiv ℂ ρ h) (jetPhase U))
          * (Complex.I * (-(6 : ℂ) * c.toU1Value))
        = Complex.I * (-(6 : ℂ) * c.toU1Value)
          * constantCoeff (x.foldl (fun h ρ => pderiv ℂ ρ h) (jetPhase U)) from
        mul_comm _ _,
      ← hcollapse]
    exact congrArg Multiset.sum (Multiset.map_congr rfl fun p hp => (hterm p).symm)

end LeptonSinglet

end StandardModel
