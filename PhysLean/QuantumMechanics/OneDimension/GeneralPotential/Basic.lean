/-
Copyright (c) 2025 Ammar Husain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ammar Husain
-/
module

public import PhysLean.QuantumMechanics.OneDimension.Operators.Momentum
public import PhysLean.QuantumMechanics.OneDimension.Operators.Position

/-!

# The 1d QM system with general potential

-/

@[expose] public section

namespace QuantumMechanics

namespace OneDimension

open PhysLean HilbertSpace Constants

private lemma fun_add {α : Type*} (f g : α → ℂ) :
  (fun x ↦ f x) + (fun x ↦ g x) = fun x ↦ f x + g x := by
  rfl

private lemma fun_smul (a1: ℂ) (f : ℝ → ℂ) : (a1 • fun x ↦ f x) = (fun x ↦ a1*(f x)) := by
    rfl

lemma momentumOperator_linear (a1 a2 : ℂ) (ψ1 ψ2 : ℝ → ℂ)
    (hψ1_x: Differentiable ℝ ψ1) (hψ2_x: Differentiable ℝ ψ2) :
    momentumOperator ((a1 • ψ1) + (a2 • ψ2)) =
    a1 • momentumOperator ψ1 + a2 • momentumOperator ψ2 := by
  unfold momentumOperator
  have h1: (a1 • fun x ↦ -Complex.I * ↑ℏ * deriv ψ1 x) =
      (fun x ↦ a1*(-Complex.I * ↑ℏ * deriv ψ1 x)) := rfl
  have h2: (a2 • fun x ↦ -Complex.I * ↑ℏ * deriv ψ2 x) =
      (fun x ↦ a2*(-Complex.I * ↑ℏ * deriv ψ2 x)) := rfl
  rw [h1, h2]
  rw [fun_add ((fun x ↦ a1 * (-Complex.I * ↑ℏ * deriv ψ1 x))) _]
  ext x
  have h : deriv ((a1 •ψ1) + (a2 •ψ2)) x = deriv (fun y ↦ ((a1 •ψ1) y) + ((a2 •ψ2) y)) x := rfl
  rw [h, deriv_fun_add]
  have ht1 : deriv (a1 •ψ1) x = deriv (fun y ↦ (a1 •ψ1 y)) x := rfl
  have ht2 : deriv (a2 •ψ2) x = deriv (fun y ↦ (a2 •ψ2 y)) x := rfl
  rw [ht1, ht2, deriv_fun_const_smul, deriv_fun_const_smul, mul_add]
  simp only [mul_comm]
  rw [← mul_assoc, ← mul_assoc, ← mul_assoc a1, ← mul_assoc a2, mul_assoc, mul_assoc]
  · rfl
  · exact hψ2_x x
  · exact hψ1_x x
  · exact (hψ1_x x).const_smul a1
  · exact (hψ2_x x).const_smul a2

lemma momentumOperator_sq_linear (a1 a2 : ℂ) (ψ1 ψ2 : ℝ → ℂ)
    (hψ1_x: Differentiable ℝ ψ1) (hψ2_x: Differentiable ℝ ψ2)
    (hψ1_xx: Differentiable ℝ (momentumOperator ψ1))
    (hψ2_xx: Differentiable ℝ (momentumOperator ψ2)) :
    momentumOperator (momentumOperator ((a1 • ψ1) + (a2 • ψ2))) =
    a1 • (momentumOperator (momentumOperator ψ1)) +
    a2 • (momentumOperator (momentumOperator ψ2)) := by
  rw [momentumOperator_linear, momentumOperator_linear] <;> assumption

/-- The potential operator is defined as the map from `ℝ → ℂ` to `ℝ → ℂ` taking
  `ψ` to `V(x) ψ`. -/
noncomputable def potentialOperator (V : ℝ → ℝ) (ψ : ℝ → ℂ) : ℝ → ℂ :=
  fun x ↦ V x * ψ x

lemma potentialOperator_linear (V: ℝ → ℝ) (a1 a2 : ℂ) (ψ1 ψ2 : ℝ → ℂ) :
    potentialOperator V ((a1 • ψ1) + (a2 • ψ2)) =
    a1 • potentialOperator V ψ1 + a2 • potentialOperator V ψ2 := by
  unfold potentialOperator
  have h1: (a1 • fun x ↦ V x * ψ1 x) = (fun x ↦ a1*(V x * ψ1 x)) := rfl
  have h2: (a2 • fun x ↦ V x * ψ2 x) = (fun x ↦ a2*(V x * ψ2 x)) := rfl
  rw [h1, h2, fun_add (fun x ↦ a1*(V x * ψ1 x)) _]
  ext x
  have h: (a1 • ψ1 + a2 • ψ2) x = a1 *ψ1 x + a2 * ψ2 x := rfl
  rw [h, mul_add]
  simp only [mul_comm]
  rw [mul_comm,mul_assoc, ← mul_assoc _ a2, mul_comm _ a2, mul_assoc a2, mul_comm (ψ2 x)]

/-- A quantum mechanical system in 1D is specified by a three
  real parameters: the mass of the particle `m`, a value of Planck's constant `ℏ`, and
  a potential function `V` -/
structure GeneralPotential where
  /-- The mass of the particle. -/
  m : ℝ
  /-- The potential. -/
  V : ℝ → ℝ
  hm : 0 < m

namespace GeneralPotential

variable (Q : GeneralPotential)

/-- For a 1D quantum mechanical system in potential `V`, the Schrodinger Operator corresponding
  to it is defined as the function from `ℝ → ℂ` to `ℝ → ℂ` taking

  `ψ ↦ - ℏ^2 / (2 * m) * ψ'' + V(x) * ψ`. -/
noncomputable def schrodingerOperator (ψ : ℝ → ℂ) : ℝ → ℂ :=
  fun x ↦ 1 / (2 * Q.m) * (momentumOperator (momentumOperator ψ) x) + (Q.V x) * ψ x

private lemma eval_add (f g : ℝ → ℂ) :
    (f + g) x = f x + g x :=
  rfl

lemma schrodingerOperator_linear (a1 a2 : ℂ) (ψ1 ψ2 : ℝ → ℂ)
    (hψ1_x: Differentiable ℝ ψ1) (hψ2_x: Differentiable ℝ ψ2)
    (hψ1_xx: Differentiable ℝ (momentumOperator ψ1))
    (hψ2_xx: Differentiable ℝ (momentumOperator ψ2)) :
    schrodingerOperator Q ((a1 • ψ1) + (a2 • ψ2)) =
    a1 • schrodingerOperator Q ψ1 + a2 • schrodingerOperator Q ψ2 := by
  unfold schrodingerOperator
  rw [momentumOperator_sq_linear]
  rw [fun_smul a1 (fun x ↦ 1 / (2 * Q.m) *
    (momentumOperator (momentumOperator ψ1) x) + (Q.V x) * ψ1 x)]
  rw [fun_smul a2 (fun x ↦ 1 / (2 * Q.m) *
    (momentumOperator (momentumOperator ψ2) x) + (Q.V x) * ψ2 x)]
  rw [fun_add (fun x ↦ a1*(1 / (2 * Q.m) *
    (momentumOperator (momentumOperator ψ1) x) + (Q.V x) * ψ1 x)) _]
  ext x
  rw [eval_add, mul_add, eval_add, mul_add, mul_add,mul_add]
  have h1: (a1 • ψ1) x = a1*ψ1 x := rfl
  have h2: (a2 • ψ2) x = a2*ψ2 x := rfl
  rw [h1, h2]
  simp only [mul_comm,mul_assoc,add_comm,add_assoc]
  rw [add_comm _ (a2 * (ψ2 x * ↑(Q.V x)))]
  rw [← add_assoc _ _ (a2 * (1 / (↑Q.m * 2) * momentumOperator (momentumOperator ψ2) x))]
  rw [← add_assoc _ (a1 * (ψ1 x * ↑(Q.V x)) + a2 * (ψ2 x * ↑(Q.V x))) _]
  rw [add_comm _ (a1 * (ψ1 x * ↑(Q.V x)) + a2 * (ψ2 x * ↑(Q.V x))), add_assoc, add_assoc]
  have ht1: 1 / (↑Q.m * 2) * (a1 • momentumOperator (momentumOperator ψ1)) x =
      a1 * ((1 / (↑Q.m * 2)) * (momentumOperator (momentumOperator ψ1)) x) := by
    have ht1_t: (a1 • momentumOperator (momentumOperator ψ1)) x =
        a1*((momentumOperator (momentumOperator ψ1)) x) := rfl
    rw [ht1_t, ← mul_assoc, mul_comm _ a1, mul_assoc]
  have ht2: 1 / (↑Q.m * 2) * (a2 • momentumOperator (momentumOperator ψ2)) x =
      a2 * ((1 / (↑Q.m * 2)) * (momentumOperator (momentumOperator ψ2)) x) := by
    have ht2_t: (a2 • momentumOperator (momentumOperator ψ2)) x =
        a2 * ((momentumOperator (momentumOperator ψ2)) x) := rfl
    rw [ht2_t, ← mul_assoc, mul_comm _ a2, mul_assoc]
  rw [ht1, ht2]
  · exact hψ1_x
  · exact hψ2_x
  · exact hψ1_xx
  · exact hψ2_xx

end GeneralPotential

end OneDimension

end QuantumMechanics
