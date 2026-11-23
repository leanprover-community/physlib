/-
Copyright (c) 2026 Daniel Leonforte. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Leonforte
-/
module

public import PhyslibAlpha.QuantumMechanics.Hydrogen.BoundStatesL2
public import PhyslibAlpha.QuantumMechanics.Hydrogen.GreenIdentity

/-!
# Towards the weak eigenvalue equation of the hydrogen bound states

Regularised bound states, the Hamiltonian on its domain, and a uniform bound for the Laplacian.

## i. Overview

The bound states are not smooth at the nucleus, so they do not lie in the domain of
`H.hamiltonianOperator` (whose kinetic part is defined on Schwartz maps). To move the
Hamiltonian from a Schwartz map onto a bound state `ψ`, one works with the regularised bound
states `ψ_ε(y) = R(√(‖y‖² + ε²)) P(y)` of `GreenIdentity` and lets `ε → 0`.

This part collects the regularised bound states: their Laplacian away from the origin
(`laplacian_regBoundState`), the bound state as the case `ε = 0` (`boundState_eq_regG`), and
Green's identity for `ψ_ε` with `ε ≠ 0` (`integral_regBoundState_mul_sum_deriv_deriv`).

For the limit `ε → 0` two more ingredients follow: the Hamiltonian acts on its domain as
`-ℏ²/(2m) Σᵢ ∂ᵢ∂ᵢ f + V f` on a Schwartz representative `f` (`hamiltonianOperator_apply_ae`),
and `|Δψ_ε|` has an integrable bound uniform in `|ε| ≤ 1`
(`exists_abs_laplacian_regBoundState_le`).

## ii. Key results

- `laplacian_regBoundState` : the Laplacian of `ψ_ε` away from the origin.
- `boundState_eq_regG` : the bound state is `ψ_0`.
- `integral_regBoundState_mul_sum_deriv_deriv` : Green's identity for `ψ_ε`, `ε ≠ 0`.
- `kineticOperator_apply_of_eq_schwartzEquiv`, `potentialOperator_apply_ae`: the kinetic and
  potential operators on their domains.
- `hamiltonianOperator_apply_ae` : on its domain the Hamiltonian is
  `-ℏ²/(2m) Σᵢ ∂ᵢ∂ᵢ f + V f` almost everywhere, for a Schwartz representative `f`.
- `exists_abs_laplacian_regBoundState_le` : a bound on `|Δψ_ε|` uniform in `|ε| ≤ 1`.

## iii. Table of contents

- A. Regularised bound states
- B. The weak eigenvalue equation

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

/-!

## B. The weak eigenvalue equation

-/

open scoped InnerProductSpace LinearPMap SchwartzMap
open SpaceDHilbertSpace

/-- On (the class of) a Schwartz map `g`, the momentum operator acts as `𝐩ᵢ g`. -/
lemma momentumOperator_apply_schwartzEquiv {d : ℕ} (i : Fin d) (g : 𝓢(Space d, ℂ)) :
    𝓟 i (schwartzEquiv volume g) = schwartzEquiv volume (𝐩 i g) := by
  rw [momentumOperator_apply, LinearEquiv.symm_apply_apply]

/-- On (the class of) a Schwartz map `f`, the momentum squared acts as `Σᵢ 𝐩ᵢ 𝐩ᵢ f`. -/
lemma momentumSqOperator_apply_schwartzEquiv {d : ℕ} (f : 𝓢(Space d, ℂ))
    (h : ((schwartzEquiv volume f : SchwartzSubmodule d) : SpaceDHilbertSpace d) ∈
      (momentumSqOperator (d := d)).domain) :
    momentumSqOperator ⟨_, h⟩ =
      ((schwartzEquiv volume (∑ i, 𝐩 i (𝐩 i f)) : SchwartzSubmodule d) : SpaceDHilbertSpace d) := by
  change (LinearPMap.sum fun i => (𝓟 i).comp (𝓟 i) (momentumOperator_range i)) ⟨_, h⟩ = _
  rw [LinearPMap.sum_apply, map_sum, Submodule.coe_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  calc ((𝓟 i).comp (𝓟 i) (momentumOperator_range i)) ⟨_, _⟩
      = 𝓟 i (schwartzEquiv volume (𝐩 i f)) := by
        change 𝓟 i ⟨𝓟 i (schwartzEquiv volume f), _⟩ = _
        congr 1
        exact Subtype.ext (momentumOperator_apply_schwartzEquiv i f)
    _ = _ := by rw [momentumOperator_apply_schwartzEquiv]

/-- Applying the momentum operator twice in the direction `i` to a Schwartz map gives
`-ℏ² ∂ᵢ∂ᵢ f`. -/
lemma momentumCLM_momentumCLM_apply {d : ℕ} (i : Fin d) (f : 𝓢(Space d, ℂ)) (y : Space d) :
    (𝐩 i (𝐩 i f)) y = -((Constants.ℏ : ℝ) : ℂ) ^ 2 * ∂[i] (∂[i] ⇑f) y := by
  have hdiff : Differentiable ℝ (∂[i] ⇑f) := Space.deriv_differentiable (f.smooth 2) i
  have h1 : ⇑(𝐩 i f) = (-Complex.I * (Constants.ℏ : ℝ)) • ∂[i] ⇑f := by
    funext x
    simp [momentumCLM_apply]
  rw [momentumCLM_apply, h1, Space.deriv_const_smul _ hdiff]
  simp only [Pi.smul_apply, smul_eq_mul]
  ring_nf
  rw [Complex.I_sq]
  ring

/-- On (the class of) a Schwartz map `f`, the kinetic operator acts as `(2m)⁻¹ Σᵢ 𝐩ᵢ 𝐩ᵢ f`. -/
lemma kineticOperator_apply_of_eq_schwartzEquiv (H : HydrogenAtom d)
    (x : H.kineticOperator.domain) (f : 𝓢(Space d, ℂ))
    (hx : (x : SpaceDHilbertSpace d) = (schwartzEquiv volume f : SchwartzSubmodule d)) :
    H.kineticOperator x = ((2 * H.m : ℝ)⁻¹ : ℂ) •
      ((schwartzEquiv volume (∑ i, 𝐩 i (𝐩 i f)) : SchwartzSubmodule d) :
        SpaceDHilbertSpace d) := by
  have hSq : ((schwartzEquiv volume f : SchwartzSubmodule d) : SpaceDHilbertSpace d) ∈
      (momentumSqOperator (d := d)).domain := by
    rw [momentumSqOperator_domain_eq]; exact (schwartzEquiv volume f).2
  have key : ∀ (T : SpaceDHilbertSpace d →ₗ.[ℂ] SpaceDHilbertSpace d)
      (_ : T = (((2 * H.m)⁻¹ : ℝ) : ℂ) • momentumSqOperator) (z : T.domain)
      (_ : (z : SpaceDHilbertSpace d) = x), T z = ((2 * H.m : ℝ)⁻¹ : ℂ) •
        ((schwartzEquiv volume (∑ i, 𝐩 i (𝐩 i f)) : SchwartzSubmodule d) :
          SpaceDHilbertSpace d) := by
    rintro T rfl z hz
    rw [LinearPMap.smul_apply]
    congr 1
    · exact Complex.ofReal_inv _
    · rw [← momentumSqOperator_apply_schwartzEquiv f hSq]
      exact congrArg momentumSqOperator (Subtype.ext (hz.trans hx))
  exact key _ SpaceDQuantumSystem.kineticOperator_eq x rfl

/-- The potential operator of the hydrogen atom acts by multiplication with `V`, almost
everywhere. -/
lemma potentialOperator_apply_ae (H : HydrogenAtom d) (x : H.potentialOperator.domain) :
    (H.potentialOperator x : SpaceDHilbertSpace d) =ᵐ[volume]
      fun y => (H.potential y : ℂ) * (x : SpaceDHilbertSpace d) y := by
  have key : ∀ (T : SpaceDHilbertSpace d →ₗ.[ℂ] SpaceDHilbertSpace d)
      (_ : T = 𝓜 volume (Complex.ofReal ∘ H.potential)) (z : T.domain),
      (T z : SpaceDHilbertSpace d) =ᵐ[volume]
        fun y => (H.potential y : ℂ) * (z : SpaceDHilbertSpace d) y := by
    rintro T rfl z
    filter_upwards [mulOperator_apply_ae z] with y hy
    rw [hy]
    rfl
  exact key _ SpaceDQuantumSystem.potentialOperator_eq x

/-- A vector `φ` in the domain of the Hamiltonian is (the class of) a Schwartz map `f`, and
`H φ = -ℏ²/(2m) Σᵢ ∂ᵢ∂ᵢ f + V f` almost everywhere. -/
lemma hamiltonianOperator_apply_ae (H : HydrogenAtom d) (φ : H.hamiltonianOperator.domain) :
    ∃ f : 𝓢(Space d, ℂ), (φ : SpaceDHilbertSpace d) =ᵐ[volume] f ∧
      H.hamiltonianOperator φ =ᵐ[volume] fun y =>
        (-((Constants.ℏ : ℝ) : ℂ) ^ 2 / (2 * H.m)) * ∑ i, ∂[i] (∂[i] ⇑f) y +
          (H.potential y : ℂ) * f y := by
  have hkin : (φ : SpaceDHilbertSpace d) ∈ H.kineticOperator.domain :=
    (Submodule.mem_inf.mp φ.2).1
  have hpot : (φ : SpaceDHilbertSpace d) ∈ H.potentialOperator.domain :=
    (Submodule.mem_inf.mp φ.2).2
  have hS : (φ : SpaceDHilbertSpace d) ∈ SchwartzSubmodule d := by
    rw [SpaceDQuantumSystem.kineticOperator_eq, LinearPMap.smul_domain,
      momentumSqOperator_domain_eq] at hkin
    exact hkin
  set f := (schwartzEquiv (d := d) volume).symm ⟨(φ : SpaceDHilbertSpace d), hS⟩ with hf
  have hφf : (φ : SpaceDHilbertSpace d) = (schwartzEquiv volume f : _) := by
    simp [hf]
  have hφae : (φ : SpaceDHilbertSpace d) =ᵐ[volume] f := by
    rw [hφf]; exact SchwartzSubmodule.schwartzEquiv_coe_ae f
  refine ⟨f, hφae, ?_⟩
  have hH : H.hamiltonianOperator φ =
      H.kineticOperator ⟨φ, hkin⟩ + H.potentialOperator ⟨φ, hpot⟩ :=
    LinearPMap.add_apply _ _ φ
  rw [hH, kineticOperator_apply_of_eq_schwartzEquiv H ⟨φ, hkin⟩ f hφf]
  filter_upwards [Lp.coeFn_add (((2 * H.m : ℝ)⁻¹ : ℂ) • ((schwartzEquiv volume
      (∑ i, 𝐩 i (𝐩 i f)) : SchwartzSubmodule d) : SpaceDHilbertSpace d))
      (H.potentialOperator ⟨φ, hpot⟩),
    Lp.coeFn_smul (((2 * H.m : ℝ)⁻¹ : ℂ)) (((schwartzEquiv volume
      (∑ i, 𝐩 i (𝐩 i f)) : SchwartzSubmodule d) : SpaceDHilbertSpace d)),
    SchwartzSubmodule.schwartzEquiv_coe_ae (∑ i, 𝐩 i (𝐩 i f)),
    potentialOperator_apply_ae H ⟨φ, hpot⟩, hφae] with y h₁ h₂ h₃ h₄ h₅
  rw [h₁, Pi.add_apply, h₂, Pi.smul_apply, h₃, h₄, h₅, _root_.sum_apply]
  simp only [momentumCLM_momentumCLM_apply, ← Finset.mul_sum]
  push_cast
  ring

/-- An elementary bound for the coefficient of the radial Laplacian: for `0 < r ≤ ρ` and `c ≥ 0`,
`|c a₁/(2ρ) + 4r² (a₂ - a₁/ρ)/(4ρ²)| ≤ (c + 1) B₁/r + B₂` whenever `|a₁| ≤ B₁` and `|a₂| ≤ B₂`. -/
lemma abs_radialLaplacianCoeff_le {r ρ c a₁ a₂ B₁ B₂ : ℝ} (hr : 0 < r) (hrρ : r ≤ ρ)
    (hc : 0 ≤ c) (h₁ : |a₁| ≤ B₁) (h₂ : |a₂| ≤ B₂) :
    |c * (a₁ / (2 * ρ)) + 4 * r ^ 2 * ((a₂ - a₁ / ρ) / (4 * ρ ^ 2))| ≤
      (c + 1) * B₁ * r⁻¹ + B₂ := by
  have hρ : 0 < ρ := hr.trans_le hrρ
  have ha₁ : |a₁| / ρ ≤ B₁ * r⁻¹ :=
    (div_le_div_of_nonneg_left (abs_nonneg _) hr hrρ).trans (by rw [div_eq_mul_inv]; gcongr)
  have t₁ : |c * (a₁ / (2 * ρ))| ≤ c * B₁ * r⁻¹ := by
    rw [abs_mul, abs_of_nonneg hc, abs_div, abs_of_pos (by linarith : (0 : ℝ) < 2 * ρ),
      mul_assoc]
    exact mul_le_mul_of_nonneg_left ((div_le_div_of_nonneg_left (abs_nonneg a₁) hρ
      (by linarith : ρ ≤ 2 * ρ)).trans ha₁) hc
  have t₂ : |4 * r ^ 2 * ((a₂ - a₁ / ρ) / (4 * ρ ^ 2))| ≤ B₂ + B₁ * r⁻¹ := by
    have key : 4 * r ^ 2 * ((a₂ - a₁ / ρ) / (4 * ρ ^ 2)) = r ^ 2 / ρ ^ 2 * (a₂ - a₁ / ρ) := by
      field_simp
    rw [key, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ r ^ 2 / ρ ^ 2)]
    have hq : r ^ 2 / ρ ^ 2 ≤ 1 := by
      rw [div_le_one (by positivity)]; nlinarith
    have hsub : |a₂ - a₁ / ρ| ≤ |a₂| + |a₁| / ρ :=
      (abs_sub _ _).trans (le_of_eq (by rw [abs_div, abs_of_pos hρ]))
    calc r ^ 2 / ρ ^ 2 * |a₂ - a₁ / ρ| ≤ 1 * (|a₂| + |a₁| / ρ) :=
          mul_le_mul hq hsub (abs_nonneg _) zero_le_one
      _ ≤ B₂ + B₁ * r⁻¹ := by rw [one_mul]; exact add_le_add h₂ ha₁
  calc _ ≤ _ := abs_add_le _ _
    _ ≤ c * B₁ * r⁻¹ + (B₂ + B₁ * r⁻¹) := add_le_add t₁ t₂
    _ = (c + 1) * B₁ * r⁻¹ + B₂ := by ring

/-- A bound `|Δψ_ε(y)| ≤ (A (1 + ‖y‖)^k₁ ‖y‖⁻¹ + C (1 + ‖y‖)^k₂) |P(y)|` away from the origin,
uniform in `|ε| ≤ 1` (including the bound state itself at `ε = 0`). -/
lemma exists_abs_laplacian_regBoundState_le {d : ℕ} {κ : ℝ} (hκ : 0 ≤ κ) (N α : ℕ) {l : ℕ}
    {P : MvPolynomial (Fin d) ℝ} (hP : P ∈ harmonicSubmodule d l) :
    ∃ (A C : ℝ) (k₁ k₂ : ℕ), 0 ≤ A ∧ 0 ≤ C ∧ ∀ ε : ℝ, |ε| ≤ 1 → ∀ y : Space d, y ≠ 0 →
      |Δ (fun y => regG (radialFactor κ N α) ε (‖y‖ ^ 2) * toFun P y) y| ≤
        (A * (1 + ‖y‖) ^ k₁ * ‖y‖⁻¹ + C * (1 + ‖y‖) ^ k₂) * |toFun P y| := by
  set L := laguerreScaled κ N α
  set L₁ := Polynomial.derivative L - Polynomial.C κ * L
  set L₂ := Polynomial.derivative L₁ - Polynomial.C κ * L₁
  obtain ⟨C₁, k₁, hC₁, hb₁⟩ := exists_abs_poly_exp_regRadius_le (d := d) L₁ hκ
  obtain ⟨C₂, k₂, hC₂, hb₂⟩ := exists_abs_poly_exp_regRadius_le (d := d) L₂ hκ
  set A : ℝ := (4 * l + 2 * d + 1) * C₁
  refine ⟨A, C₂, k₁, k₂, by positivity, hC₂, fun ε hε y hy => ?_⟩
  have hy' : 0 < ‖y‖ := norm_pos_iff.mpr hy
  set ρ := Real.sqrt (‖y‖ ^ 2 + ε ^ 2)
  have hρy : ‖y‖ ≤ ρ := by
    rw [Real.le_sqrt (norm_nonneg y) (by positivity)]; nlinarith [sq_nonneg ε]
  have hρ : 0 < ρ := lt_of_lt_of_le hy' hρy
  have hsq : ‖y‖ ^ 2 + ε ^ 2 = ρ ^ 2 := (Real.sq_sqrt (by positivity)).symm
  have e₁ := hb₁ ε hε y
  have e₂ := hb₂ ε hε y
  set a₁ := L₁.eval ρ * Real.exp (-(κ * ρ))
  set a₂ := L₂.eval ρ * Real.exp (-(κ * ρ))
  have hΔ : Δ (fun y => regG (radialFactor κ N α) ε (‖y‖ ^ 2) * toFun P y) y =
      ((4 * l + 2 * d) * (a₁ / (2 * ρ)) +
        4 * ‖y‖ ^ 2 * ((a₂ - a₁ / ρ) / (4 * (‖y‖ ^ 2 + ε ^ 2)))) * toFun P y :=
    laplacian_regBoundState κ N α hP ε hy
  rw [hΔ, hsq, abs_mul]
  refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
  calc _ ≤ (4 * l + 2 * d + 1) * (C₁ * (1 + ‖y‖) ^ k₁) * ‖y‖⁻¹ + C₂ * (1 + ‖y‖) ^ k₂ :=
        abs_radialLaplacianCoeff_le hy' hρy (by positivity) e₁ e₂
    _ = A * (1 + ‖y‖) ^ k₁ * ‖y‖⁻¹ + C₂ * (1 + ‖y‖) ^ k₂ := by ring

end PhyslibAlpha.Hydrogen
