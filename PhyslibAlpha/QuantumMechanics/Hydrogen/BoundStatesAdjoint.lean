/-
Copyright (c) 2026 Daniel Leonforte. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Leonforte
-/
module

public import PhyslibAlpha.QuantumMechanics.Hydrogen.BoundStatesL2
public import PhyslibAlpha.QuantumMechanics.Hydrogen.GreenIdentity

/-!
# Regularised hydrogen bound states

The regularised hydrogen bound states, their Laplacian and Green's identity for them.

## i. Overview

The bound states are not smooth at the nucleus, so they do not lie in the domain of
`H.hamiltonianOperator` (whose kinetic part is defined on Schwartz maps). To move the
Hamiltonian from a Schwartz map onto a bound state `ψ`, one works with the regularised bound
states `ψ_ε(y) = R(√(‖y‖² + ε²)) P(y)` of `GreenIdentity` and lets `ε → 0`.

This part collects the regularised bound states: their Laplacian away from the origin
(`laplacian_regBoundState`), the bound state as the case `ε = 0` (`boundState_eq_regG`), and
Green's identity for `ψ_ε` with `ε ≠ 0` (`integral_regBoundState_mul_sum_deriv_deriv`).

## ii. Key results

- `laplacian_regBoundState` : the Laplacian of `ψ_ε` away from the origin.
- `boundState_eq_regG` : the bound state is `ψ_0`.
- `integral_regBoundState_mul_sum_deriv_deriv` : Green's identity for `ψ_ε`, `ε ≠ 0`.

## iii. Table of contents

- A. Regularised bound states

## iv. References

- None.
-/

@[expose] public section

noncomputable section

namespace PhyslibAlpha.Hydrogen

open MeasureTheory Space
open scoped SchwartzMap LineDeriv

open QuantumMechanics

/-!

## A. Regularised bound states

-/

/-- Away from the origin, `Δψ_ε = ((4l + 2d) G_ε' + 4‖y‖² G_ε'') P` for a homogeneous harmonic `P`
of degree `l` (also for `ε = 0`, where `ψ_0` is the bound state). -/
lemma laplacian_regBoundState {d : ℕ} (κ : ℝ) (N α : ℕ) {l : ℕ}
    {P : MvPolynomial (Fin d) ℝ} (hP : P ∈ harmonicSubmodule d l) (ε : ℝ) {y : Space d}
    (hy : y ≠ 0) :
    Δ (fun y => regG (radialFactor κ N α) ε (‖y‖ ^ 2) * toFun P y) y =
      ((4 * l + 2 * d) * regG' (radialFactor' κ N α) ε (‖y‖ ^ 2) +
        4 * ‖y‖ ^ 2 * regG'' (radialFactor' κ N α) (radialFactor'' κ N α) ε (‖y‖ ^ 2)) *
          toFun P y := by
  obtain ⟨hhom, hker⟩ := Submodule.mem_inf.mp hP
  have hΔ : Δ (toFun P) y = 0 := by
    rw [laplacian_toFun, LinearMap.mem_ker.mp hker]
    simp [toFun]
  have hE := euler_toFun ((MvPolynomial.mem_homogeneousSubmodule l P).mp hhom) y
  rw [laplacian_radial_mul (G' := regG' (radialFactor' κ N α) ε)
    (G'' := regG'' (radialFactor' κ N α) (radialFactor'' κ N α) ε)
    (fun s hs => hasDerivAt_regG (fun r _ => hasDerivAt_radialFactor κ N α r)
      (add_pos_of_pos_of_nonneg hs (sq_nonneg ε)))
    (fun s hs => hasDerivAt_regG' (fun r _ => hasDerivAt_radialFactor' κ N α r)
      (add_pos_of_pos_of_nonneg hs (sq_nonneg ε)))
    (contDiff_toFun P) hy, hΔ, hE]
  ring

/-- The bound state is the regularised bound state at `ε = 0`. -/
lemma boundState_eq_regG (H : QuantumMechanics.HydrogenAtom d) (N l : ℕ)
    (P : MvPolynomial (Fin d) ℝ) :
    boundState H N l (toFun P) = fun y =>
      regG (radialFactor (boundKappa H (N + l)) N (2 * l + d - 2)) 0 (‖y‖ ^ 2) *
        toFun P y := by
  funext y
  simp [boundState, regG, Real.sqrt_sq (norm_nonneg y)]

/-- The regularised bound state `ψ_ε(y) = R(√(‖y‖² + ε²)) P(y)` is twice continuously
differentiable for `ε ≠ 0`. -/
lemma contDiff_regBoundState {d : ℕ} (κ : ℝ) (N α : ℕ) (P : MvPolynomial (Fin d) ℝ) {ε : ℝ}
    (hε : ε ≠ 0) :
    ContDiff ℝ 2 (fun y : Space d => regG (radialFactor κ N α) ε (‖y‖ ^ 2) * toFun P y) := by
  have hsq : ContDiff ℝ 2 (fun y : Space d => ‖y‖ ^ 2 + ε ^ 2) :=
    (contDiff_norm_sq ℝ).add contDiff_const
  have hsqrt : ContDiff ℝ 2 (fun y : Space d => Real.sqrt (‖y‖ ^ 2 + ε ^ 2)) :=
    hsq.sqrt fun y => by positivity
  have hRs : ContDiff ℝ 2 (radialFactor κ N α) := by
    have hL : ContDiff ℝ 2 (fun r : ℝ => (laguerreScaled κ N α).eval r) := by
      simpa using Polynomial.contDiff_aeval (𝕜 := ℝ) (laguerreScaled κ N α) 2
    exact hL.mul (Real.contDiff_exp.comp (contDiff_const.mul contDiff_id).neg)
  exact (hRs.comp hsqrt).mul (contDiff_toFun P)

/-- **Green's identity for the regularised bound state** `ψ_ε(y) = R(√(‖y‖² + ε²)) P(y)`,
`R = radialFactor κ N α` with `κ ≥ 0`. -/
lemma integral_regBoundState_mul_sum_deriv_deriv {d : ℕ} {κ : ℝ} (hκ : 0 ≤ κ) (N α : ℕ)
    (P : MvPolynomial (Fin d) ℝ) {ε : ℝ} (hε : ε ≠ 0) (f : 𝓢(Space d, ℂ)) :
    ∫ y, ((regG (radialFactor κ N α) ε (‖y‖ ^ 2) * toFun P y : ℝ) : ℂ) *
        ∑ i, ∂[i] (∂[i] ⇑f) y =
      ∫ y, ((∑ i, ∂[i] (∂[i] (fun y => regG (radialFactor κ N α) ε (‖y‖ ^ 2) * toFun P y)) y :
        ℝ) : ℂ) * f y := by
  set L := laguerreScaled κ N α
  set L₁ := Polynomial.derivative L - Polynomial.C κ * L
  set L₂ := Polynomial.derivative L₁ - Polynomial.C κ * L₁
  have hR : radialFactor κ N α = fun r => L.eval r * Real.exp (-(κ * r)) := rfl
  have hR' : radialFactor' κ N α = fun r => L₁.eval r * Real.exp (-(κ * r)) := rfl
  have hR'' : radialFactor'' κ N α = fun r => L₂.eval r * Real.exp (-(κ * r)) := rfl
  have hG : ∀ s, 0 ≤ s → HasDerivAt (regG (radialFactor κ N α) ε)
      (regG' (radialFactor' κ N α) ε s) s :=
    fun s hs => hasDerivAt_regG (fun r _ => hasDerivAt_radialFactor κ N α r)
      (by have := pow_pos (abs_pos.mpr hε) 2; rw [sq_abs] at this; linarith)
  have hG' : ∀ s, 0 ≤ s → HasDerivAt (regG' (radialFactor' κ N α) ε)
      (regG'' (radialFactor' κ N α) (radialFactor'' κ N α) ε s) s :=
    fun s hs => hasDerivAt_regG' (fun r _ => hasDerivAt_radialFactor' κ N α r)
      (by have := pow_pos (abs_pos.mpr hε) 2; rw [sq_abs] at this; linarith)
  have hQ : ContDiff ℝ 2 (toFun P) := contDiff_toFun P
  have hQd : Differentiable ℝ (toFun P) := hQ.differentiable (by norm_num)
  have hb₀ := isPolyBounded_regG (d := d) L hκ ε
  have hb₁ := isPolyBounded_regG' (d := d) L₁ hκ hε
  have hb₂ := isPolyBounded_regG'' (d := d) L₁ L₂ hκ hε
  rw [← hR] at hb₀
  rw [← hR'] at hb₁
  rw [← hR', ← hR''] at hb₂
  refine integral_ofReal_mul_sum_deriv_deriv ?_ (hb₀.mul (IsPolyBounded.toFun P)) (fun i => ?_)
    (fun i => ?_) f
  · exact contDiff_regBoundState κ N α P hε
  · rw [deriv_radial_mul hG hQd i]
    exact (hb₀.mul (by rw [deriv_toFun]; exact IsPolyBounded.toFun _)).add
      ((IsPolyBounded.toFun P).mul (hb₁.mul ((IsPolyBounded.const 2).mul (IsPolyBounded.coord i))))
  · have h2 : ∂[i] (∂[i] (fun y => regG (radialFactor κ N α) ε (‖y‖ ^ 2) * toFun P y)) =
        fun x => regG (radialFactor κ N α) ε (‖x‖ ^ 2) * ∂[i] (∂[i] (toFun P)) x +
          4 * regG' (radialFactor' κ N α) ε (‖x‖ ^ 2) * (x i * ∂[i] (toFun P) x) +
          (2 * regG' (radialFactor' κ N α) ε (‖x‖ ^ 2) +
            4 * x i ^ 2 * regG'' (radialFactor' κ N α) (radialFactor'' κ N α) ε (‖x‖ ^ 2)) *
              toFun P x :=
      funext (deriv_deriv_radial_mul hG hG' hQ i)
    rw [h2]
    simp only [deriv_toFun]
    have hc := IsPolyBounded.coord (d := d) i
    exact ((hb₀.mul (IsPolyBounded.toFun _)).add
      (((IsPolyBounded.const 4).mul hb₁).mul (hc.mul (IsPolyBounded.toFun _)))).add
      ((((IsPolyBounded.const 2).mul hb₁).add
        (((IsPolyBounded.const 4).mul (hc.pow 2)).mul hb₂)).mul (IsPolyBounded.toFun P))

end PhyslibAlpha.Hydrogen
