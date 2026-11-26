/-
Copyright (c) 2026 Daniel Leonforte. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Leonforte
-/
module

public import PhyslibAlpha.QuantumMechanics.Hydrogen.BoundStatesL2
public import PhyslibAlpha.QuantumMechanics.Hydrogen.GreenIdentity

/-!
# The weak eigenvalue equation of the hydrogen bound states

Green's identity for a hydrogen bound state and the weak eigenvalue equation.

## i. Overview

The bound states are not smooth at the nucleus, so they do not lie in the domain of
`H.hamiltonianOperator` (whose kinetic part is defined on Schwartz maps). To move the
Hamiltonian from a Schwartz map onto a bound state `ψ`, one works with the regularised bound
states `ψ_ε(y) = R(√(‖y‖² + ε²)) P(y)` of `GreenIdentity` and lets `ε → 0`.

With Green's identity for the kinetic term (`integral_boundState_mul_sum_deriv_deriv`) and the
Coulomb term, the Hamiltonian moves from a Schwartz map onto the bound state
(`integral_boundState_mul_hamiltonian`), which gives the weak eigenvalue equation
`⟪E ψ, φ⟫ = ⟪ψ, H φ⟫` for all `φ` in the domain of `H` (`inner_boundStateHS_hamiltonianOperator`).

## ii. Key results

- `laplacian_regBoundState` : the Laplacian of `ψ_ε` away from the origin.
- `boundState_eq_regG` : the bound state is `ψ_0`.
- `integral_regBoundState_mul_sum_deriv_deriv` : Green's identity for `ψ_ε`, `ε ≠ 0`.
- `kineticOperator_apply_of_eq_schwartzEquiv`, `potentialOperator_apply_ae`: the kinetic and
  potential operators on their domains.
- `hamiltonianOperator_apply_ae` : on its domain the Hamiltonian is
  `-ℏ²/(2m) Σᵢ ∂ᵢ∂ᵢ f + V f` almost everywhere, for a Schwartz representative `f`.
- `exists_abs_laplacian_regBoundState_le` : a bound on `|Δψ_ε|` uniform in `|ε| ≤ 1`.
- `integral_boundState_mul_sum_deriv_deriv` : Green's identity `∫ ψ Σᵢ ∂ᵢ∂ᵢ f = ∫ (Δψ) f` for a
  bound state `ψ`, the limit `ε → 0` by dominated convergence
  (`tendsto_integral_regBoundState_mul_sum_deriv_deriv`,
  `tendsto_integral_laplacian_regBoundState_mul`).
- `integral_boundState_mul_hamiltonian` : Green's identity `∫ ψ H f = ∫ (H ψ) f` for a bound state
  `ψ` and a Schwartz map `f`.
- `inner_boundStateHS_hamiltonianOperator` : the weak eigenvalue equation
  `⟪E ψ, φ⟫ = ⟪ψ, H φ⟫` for `φ` in the domain of the Hamiltonian.

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

/-- For `d ≥ 2`, almost every point of `Space d` is nonzero. -/
lemma ae_ne_zero_of_two_le {d : ℕ} (hd : 2 ≤ d) : ∀ᵐ y ∂(volume : Measure (Space d)), y ≠ 0 := by
  have : Nontrivial (Space d) :=
    Module.nontrivial_of_finrank_pos (by rw [Space.finrank_eq_dim]; omega)
  exact measure_eq_zero_iff_ae_notMem.mp (measure_singleton 0) |>.mono fun y hy => hy

/-- The dominating function `‖y‖⁻¹ |A (1 + ‖y‖)^k₁ P(y)| ‖f(y)‖ + |C (1 + ‖y‖)^k₂ P(y)| ‖f(y)‖` of
the Laplacians of the regularised bound states is integrable for `d ≥ 2`. -/
lemma integrable_laplacianBound_mul {d : ℕ} (hd : 2 ≤ d) (P : MvPolynomial (Fin d) ℝ)
    (A C : ℝ) (k₁ k₂ : ℕ) (f : 𝓢(Space d, ℂ)) :
    Integrable (fun y : Space d => ‖y‖⁻¹ * (|A * (1 + ‖y‖) ^ k₁ * toFun P y| * ‖f y‖) +
      |C * (1 + ‖y‖) ^ k₂ * toFun P y| * ‖f y‖) := by
  have hnorm : IsPolyBounded (fun y : Space d => 1 + ‖y‖) :=
    (IsPolyBounded.const 1).add IsPolyBounded.norm
  have hQc : Continuous (toFun P) := (contDiff_toFun_infty P).continuous
  have hu₁ : IsPolyBounded (fun y => A * (1 + ‖y‖) ^ k₁ * toFun P y) :=
    ((IsPolyBounded.const A).mul (hnorm.pow k₁)).mul (IsPolyBounded.toFun P)
  have hu₂ : IsPolyBounded (fun y => C * (1 + ‖y‖) ^ k₂ * toFun P y) :=
    ((IsPolyBounded.const C).mul (hnorm.pow k₂)).mul (IsPolyBounded.toFun P)
  have hum₁ : AEStronglyMeasurable (fun y : Space d => A * (1 + ‖y‖) ^ k₁ * toFun P y) :=
    (by fun_prop : Continuous fun y : Space d => A * (1 + ‖y‖) ^ k₁ * toFun P y)
      |>.aestronglyMeasurable
  have hum₂ : AEStronglyMeasurable (fun y : Space d => C * (1 + ‖y‖) ^ k₂ * toFun P y) :=
    (by fun_prop : Continuous fun y : Space d => C * (1 + ‖y‖) ^ k₂ * toFun P y)
      |>.aestronglyMeasurable
  exact (hu₁.integrable_inv_norm_mul hd hum₁ f).add (hu₂.integrable_abs_mul_norm_schwartz hum₂ f)

/-- A pointwise bound `|g(y)| ≤ (A (1 + ‖y‖)^k₁ ‖y‖⁻¹ + C (1 + ‖y‖)^k₂) |P(y)|` gives the bound of
`g f` by the dominating function of `integrable_laplacianBound_mul`. -/
lemma norm_mul_le_laplacianBound {d : ℕ} {g : Space d → ℝ} {A C : ℝ} {k₁ k₂ : ℕ} (hA : 0 ≤ A)
    (hC : 0 ≤ C) (P : MvPolynomial (Fin d) ℝ) (f : 𝓢(Space d, ℂ)) {y : Space d}
    (hb : |g y| ≤ (A * (1 + ‖y‖) ^ k₁ * ‖y‖⁻¹ + C * (1 + ‖y‖) ^ k₂) * |toFun P y|) :
    ‖((g y : ℝ) : ℂ) * f y‖ ≤ ‖y‖⁻¹ * (|A * (1 + ‖y‖) ^ k₁ * toFun P y| * ‖f y‖) +
      |C * (1 + ‖y‖) ^ k₂ * toFun P y| * ‖f y‖ := by
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  simp only [abs_mul, abs_of_nonneg hA, abs_of_nonneg hC,
    abs_of_nonneg (pow_nonneg (by positivity : (0 : ℝ) ≤ 1 + ‖y‖) k₁),
    abs_of_nonneg (pow_nonneg (by positivity : (0 : ℝ) ≤ 1 + ‖y‖) k₂)]
  calc |g y| * ‖f y‖
      ≤ (A * (1 + ‖y‖) ^ k₁ * ‖y‖⁻¹ + C * (1 + ‖y‖) ^ k₂) * |toFun P y| * ‖f y‖ := by gcongr
    _ = _ := by ring

/-- Along a sequence `εₙ → 0` with `|εₙ| ≤ 1`,
`∫ ψ_{εₙ} Σᵢ ∂ᵢ∂ᵢ f → ∫ ψ_0 Σᵢ ∂ᵢ∂ᵢ f`, by dominated convergence. -/
lemma tendsto_integral_regBoundState_mul_sum_deriv_deriv {d : ℕ} {κ : ℝ} (hκ : 0 ≤ κ) (N α : ℕ)
    (P : MvPolynomial (Fin d) ℝ) {εs : ℕ → ℝ} (hεs_le : ∀ n, |εs n| ≤ 1)
    (hεs : Filter.Tendsto εs Filter.atTop (nhds 0)) (f : 𝓢(Space d, ℂ)) :
    Filter.Tendsto (fun n => ∫ y, ((regG (radialFactor κ N α) (εs n) (‖y‖ ^ 2) * toFun P y : ℝ) :
        ℂ) * ∑ i, ∂[i] (∂[i] ⇑f) y) Filter.atTop
      (nhds (∫ y, ((regG (radialFactor κ N α) 0 (‖y‖ ^ 2) * toFun P y : ℝ) : ℂ) *
        ∑ i, ∂[i] (∂[i] ⇑f) y)) := by
  set ψ := fun ε : ℝ => fun y : Space d => regG (radialFactor κ N α) ε (‖y‖ ^ 2) * toFun P y
  obtain ⟨C₀, k₀, hC₀, hb₀⟩ :=
    exists_abs_poly_exp_regRadius_le (d := d) (laguerreScaled κ N α) hκ
  set S : 𝓢(Space d, ℂ) := ∑ i : Fin d, ∂_{Space.basis i} (∂_{Space.basis i} f)
  have hS : ∀ y, ∑ i, ∂[i] (∂[i] ⇑f) y = S y := fun y => by
    simp only [S, _root_.sum_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [deriv_schwartz f i, deriv_schwartz]
  have hnorm : IsPolyBounded (fun y : Space d => 1 + ‖y‖) :=
    (IsPolyBounded.const 1).add IsPolyBounded.norm
  have hu : IsPolyBounded (fun y => C₀ * (1 + ‖y‖) ^ k₀ * toFun P y) :=
    ((IsPolyBounded.const C₀).mul (hnorm.pow k₀)).mul (IsPolyBounded.toFun P)
  have hQc : Continuous (toFun P) := (contDiff_toFun_infty P).continuous
  have hψc : ∀ ε, Continuous (ψ ε) := fun ε => by
    simp only [ψ, regG, radialFactor]
    fun_prop
  have hum : AEStronglyMeasurable (fun y : Space d => C₀ * (1 + ‖y‖) ^ k₀ * toFun P y) :=
    (by fun_prop : Continuous fun y : Space d => C₀ * (1 + ‖y‖) ^ k₀ * toFun P y)
      |>.aestronglyMeasurable
  simp only [hS]
  refine tendsto_integral_of_dominated_convergence
    (fun y => |C₀ * (1 + ‖y‖) ^ k₀ * toFun P y| * ‖S y‖)
    (fun n => ((Complex.continuous_ofReal.comp (hψc _)).mul S.continuous).aestronglyMeasurable)
    (hu.integrable_abs_mul_norm_schwartz hum S)
    (fun n => Filter.Eventually.of_forall fun y => ?_) (Filter.Eventually.of_forall fun y => ?_)
  · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
    rw [abs_mul, abs_mul (C₀ * _), abs_mul C₀, abs_of_nonneg hC₀,
      abs_of_nonneg (pow_nonneg (by positivity : (0 : ℝ) ≤ 1 + ‖y‖) _)]
    exact mul_le_mul_of_nonneg_right (hb₀ (εs n) (hεs_le n) y) (abs_nonneg _)
  · have hc : Continuous fun ε : ℝ => regG (radialFactor κ N α) ε (‖y‖ ^ 2) := by
      simp only [regG, radialFactor]
      fun_prop
    exact ((Complex.continuous_ofReal.tendsto _).comp
      (((hc.tendsto 0).comp hεs).mul_const (toFun P y))).mul_const (S y)

/-- Away from the origin, `Δψ_{εₙ}(y) → Δψ_0(y)` along a sequence `εₙ → 0`. -/
lemma tendsto_laplacian_regBoundState {d : ℕ} (κ : ℝ) (N α : ℕ) {l : ℕ}
    {P : MvPolynomial (Fin d) ℝ} (hP : P ∈ harmonicSubmodule d l) {εs : ℕ → ℝ}
    (hεs : Filter.Tendsto εs Filter.atTop (nhds 0)) {y : Space d} (hy : y ≠ 0) :
    Filter.Tendsto
      (fun n => Δ (fun y => regG (radialFactor κ N α) (εs n) (‖y‖ ^ 2) * toFun P y) y)
      Filter.atTop (nhds (Δ (fun y => regG (radialFactor κ N α) 0 (‖y‖ ^ 2) * toFun P y) y)) := by
  have hy' : 0 < ‖y‖ ^ 2 := by positivity
  simp only [laplacian_regBoundState κ N α hP _ hy]
  have hc : ∀ g : ℝ → ℝ, Continuous g →
      Filter.Tendsto (fun n => g (Real.sqrt (‖y‖ ^ 2 + εs n ^ 2))) Filter.atTop
        (nhds (g (Real.sqrt (‖y‖ ^ 2 + 0 ^ 2)))) := fun g hg =>
    ((by fun_prop : Continuous fun ε : ℝ => g (Real.sqrt (‖y‖ ^ 2 + ε ^ 2))).tendsto 0).comp hεs
  have hρ0 : Real.sqrt (‖y‖ ^ 2 + 0 ^ 2) ≠ 0 := by
    rw [zero_pow two_ne_zero, add_zero]; positivity
  have hs0 : ‖y‖ ^ 2 + (0 : ℝ) ^ 2 ≠ 0 := by positivity
  have hR' : Continuous (radialFactor' κ N α) := by unfold radialFactor'; fun_prop
  have hR'' : Continuous (radialFactor'' κ N α) := by unfold radialFactor''; fun_prop
  have hG' := (hc _ hR').div ((hc _ continuous_id).const_mul 2) (mul_ne_zero two_ne_zero hρ0)
  have hG'' := ((hc _ hR'').sub ((hc _ hR').div (hc _ continuous_id) hρ0)).div
    ((((by fun_prop : Continuous fun ε : ℝ => ‖y‖ ^ 2 + ε ^ 2).tendsto 0).comp hεs).const_mul 4)
    (mul_ne_zero four_ne_zero hs0)
  exact ((hG'.const_mul (4 * (l : ℝ) + 2 * (d : ℝ))).add
    (hG''.const_mul (4 * ‖y‖ ^ 2))).mul_const (toFun P y)

/-- Along a sequence `εₙ → 0` with `|εₙ| ≤ 1`, `∫ (Δψ_{εₙ}) f → ∫ (Δψ_0) f`, by dominated
convergence with the bound `exists_abs_laplacian_regBoundState_le`. -/
lemma tendsto_integral_laplacian_regBoundState_mul {d : ℕ} (hd : 2 ≤ d) {κ : ℝ} (hκ : 0 ≤ κ)
    (N α : ℕ) {l : ℕ} {P : MvPolynomial (Fin d) ℝ} (hP : P ∈ harmonicSubmodule d l)
    {εs : ℕ → ℝ} (hεs_le : ∀ n, |εs n| ≤ 1) (hεs : Filter.Tendsto εs Filter.atTop (nhds 0))
    (f : 𝓢(Space d, ℂ)) :
    Filter.Tendsto (fun n => ∫ y, ((Δ (fun y => regG (radialFactor κ N α) (εs n) (‖y‖ ^ 2) *
        toFun P y) y : ℝ) : ℂ) * f y) Filter.atTop
      (nhds (∫ y, ((Δ (fun y => regG (radialFactor κ N α) 0 (‖y‖ ^ 2) * toFun P y) y : ℝ) :
        ℂ) * f y)) := by
  obtain ⟨A, C₂, k₁, k₂, hA, hC₂, hbound⟩ := exists_abs_laplacian_regBoundState_le hκ N α hP
  have hΔm : ∀ ε, Measurable (Δ (fun y => regG (radialFactor κ N α) ε (‖y‖ ^ 2) *
      toFun P y)) := fun ε => by
    rw [laplacian_eq_sum_snd_deriv]
    exact Finset.measurable_sum _ fun i _ => measurable_fderiv_apply_const ℝ _ _
  refine tendsto_integral_of_dominated_convergence
    (fun y => ‖y‖⁻¹ * (|A * (1 + ‖y‖) ^ k₁ * toFun P y| * ‖f y‖) +
      |C₂ * (1 + ‖y‖) ^ k₂ * toFun P y| * ‖f y‖)
    (fun n => ((Complex.continuous_ofReal.measurable.comp (hΔm _)).aestronglyMeasurable).mul
      f.continuous.aestronglyMeasurable)
    (integrable_laplacianBound_mul hd P A C₂ k₁ k₂ f) (fun n => ?_) ?_
  · filter_upwards [ae_ne_zero_of_two_le hd] with y hy
    exact norm_mul_le_laplacianBound hA hC₂ P f (hbound (εs n) (hεs_le n) y hy)
  · filter_upwards [ae_ne_zero_of_two_le hd] with y hy
    exact ((Complex.continuous_ofReal.tendsto _).comp
      (tendsto_laplacian_regBoundState κ N α hP hεs hy)).mul_const (f y)

/-- **Green's identity for the kinetic term**: `∫ ψ Σᵢ ∂ᵢ∂ᵢ f = ∫ (Δψ) f` for a bound state `ψ`,
the limit `ε → 0` of `integral_regBoundState_mul_sum_deriv_deriv`. -/
lemma integral_boundState_mul_sum_deriv_deriv (H : HydrogenAtom d) (hd : 2 ≤ d) (hk : 0 < H.k)
    (N l : ℕ) {P : MvPolynomial (Fin d) ℝ} (hP : P ∈ harmonicSubmodule d l)
    (f : 𝓢(Space d, ℂ)) :
    ∫ y, (boundState H N l (toFun P) y : ℂ) * ∑ i, ∂[i] (∂[i] ⇑f) y =
      ∫ y, ((Δ (boundState H N l (toFun P)) y : ℝ) : ℂ) * f y := by
  set κ := boundKappa H (N + l)
  have hκ : 0 ≤ κ := (boundKappa_pos H hd hk (N + l)).le
  set α := 2 * l + d - 2
  have hψ0 := boundState_eq_regG H N l P
  set εs : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hεs_ne : ∀ n, εs n ≠ 0 := fun n => by positivity
  have hεs_le : ∀ n, |εs n| ≤ 1 := fun n => by
    rw [abs_of_pos (by positivity)]
    exact div_le_one_of_le₀ (by linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]) (by positivity)
  have hεs : Filter.Tendsto εs Filter.atTop (nhds 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  -- the regularised identities, and their limits on both sides
  have hreg : ∀ n, ∫ y, ((regG (radialFactor κ N α) (εs n) (‖y‖ ^ 2) * toFun P y : ℝ) : ℂ) *
      ∑ i, ∂[i] (∂[i] ⇑f) y = ∫ y, ((Δ (fun y => regG (radialFactor κ N α) (εs n) (‖y‖ ^ 2) *
        toFun P y) y : ℝ) : ℂ) * f y := fun n => by
    rw [integral_regBoundState_mul_sum_deriv_deriv hκ N α P (hεs_ne n) f]
    simp only [laplacian_eq_sum_snd_deriv]
  rw [hψ0]
  exact tendsto_nhds_unique
    ((tendsto_integral_regBoundState_mul_sum_deriv_deriv hκ N α P hεs_le hεs f).congr hreg)
    (tendsto_integral_laplacian_regBoundState_mul hd hκ N α hP hεs_le hεs f)

/-- A hydrogen bound state is polynomially bounded. -/
lemma isPolyBounded_boundState (H : HydrogenAtom d) (hd : 2 ≤ d) (hk : 0 < H.k) (N l : ℕ)
    (P : MvPolynomial (Fin d) ℝ) : IsPolyBounded (boundState H N l (toFun P)) := by
  have hκ : 0 ≤ boundKappa H (N + l) := (boundKappa_pos H hd hk (N + l)).le
  obtain ⟨C₀, k₀, hC₀, hb₀⟩ := exists_abs_poly_exp_regRadius_le (d := d)
    (laguerreScaled (boundKappa H (N + l)) N (2 * l + d - 2)) hκ
  have hG0 : IsPolyBounded fun y : Space d =>
      regG (radialFactor (boundKappa H (N + l)) N (2 * l + d - 2)) 0 (‖y‖ ^ 2) :=
    ⟨C₀, k₀, hC₀, fun y => by
      have h := hb₀ 0 (by simp) y
      simpa [regG, radialFactor, abs_mul] using h⟩
  rw [boundState_eq_regG H N l P]
  exact hG0.mul (IsPolyBounded.toFun P)

/-- The Coulomb term `ψ V f` of a bound state `ψ` and a Schwartz map `f` is integrable. -/
lemma integrable_boundState_mul_potential_mul (H : HydrogenAtom d) (hd : 2 ≤ d) (hk : 0 < H.k)
    (N l : ℕ) (P : MvPolynomial (Fin d) ℝ) (f : 𝓢(Space d, ℂ)) :
    Integrable fun y => (boundState H N l (toFun P) y : ℂ) * ((H.potential y : ℂ) * f y) := by
  set ψ := boundState H N l (toFun P)
  have hψc : Continuous ψ := continuous_boundState H N l P
  have hV : ∀ y, H.potential y = -H.k * ‖y‖⁻¹ := fun y => by simp
  have hVm : Measurable fun y : Space d => H.potential y := by
    simp only [hV]; fun_prop
  have hkψ : IsPolyBounded fun y => H.k * ψ y :=
    (IsPolyBounded.const H.k).mul (isPolyBounded_boundState H hd hk N l P)
  have hkψm : AEStronglyMeasurable fun y => H.k * ψ y := (by fun_prop : Continuous fun y =>
    H.k * ψ y).aestronglyMeasurable
  refine (hkψ.integrable_inv_norm_mul hd hkψm f).mono'
    ((Complex.continuous_ofReal.comp hψc).aestronglyMeasurable.mul
      ((Complex.continuous_ofReal.measurable.comp hVm).aestronglyMeasurable.mul
        f.continuous.aestronglyMeasurable)) (Filter.Eventually.of_forall fun y => ?_)
  rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
    Real.norm_eq_abs, hV, abs_mul, abs_mul, abs_neg, abs_of_pos hk,
    abs_of_nonneg (inv_nonneg.mpr (norm_nonneg y))]
  exact le_of_eq (by ring)

/-- The kinetic term `(Δψ) f` of a bound state `ψ` and a Schwartz map `f` is integrable. -/
lemma integrable_laplacian_boundState_mul (H : HydrogenAtom d) (hd : 2 ≤ d) (hk : 0 < H.k)
    (N l : ℕ) {P : MvPolynomial (Fin d) ℝ} (hP : P ∈ harmonicSubmodule d l)
    (f : 𝓢(Space d, ℂ)) :
    Integrable fun y => ((Δ (boundState H N l (toFun P)) y : ℝ) : ℂ) * f y := by
  have hκ : 0 ≤ boundKappa H (N + l) := (boundKappa_pos H hd hk (N + l)).le
  obtain ⟨A, C₂, k₁, k₂, hA, hC₂, hbound⟩ := exists_abs_laplacian_regBoundState_le hκ N
    (2 * l + d - 2) hP
  have hΔm : Measurable (Δ (boundState H N l (toFun P))) := by
    rw [laplacian_eq_sum_snd_deriv]
    exact Finset.measurable_sum _ fun i _ => measurable_fderiv_apply_const ℝ _ _
  refine (integrable_laplacianBound_mul hd P A C₂ k₁ k₂ f).mono'
    ((Complex.continuous_ofReal.measurable.comp hΔm).aestronglyMeasurable.mul
      f.continuous.aestronglyMeasurable) ?_
  filter_upwards [ae_ne_zero_of_two_le hd] with y hy
  have hb := hbound 0 (by simp) y hy
  rw [← boundState_eq_regG H N l P] at hb
  exact norm_mul_le_laplacianBound hA hC₂ P f hb

/-- **Green's identity for a bound state.** Moving the Hamiltonian from a Schwartz map `f` onto
the bound state `ψ`, which is smooth away from the nucleus:
`∫ ψ (-ℏ²/(2m) Σᵢ ∂ᵢ∂ᵢ f + V f) = ∫ (-ℏ²/(2m) Δψ + V ψ) f`. -/
lemma integral_boundState_mul_hamiltonian (H : HydrogenAtom d) (hd : 2 ≤ d) (hk : 0 < H.k)
    (N l : ℕ) {P : MvPolynomial (Fin d) ℝ} (hP : P ∈ harmonicSubmodule d l)
    (f : 𝓢(Space d, ℂ)) :
    ∫ y, (boundState H N l (toFun P) y : ℂ) *
        ((-((Constants.ℏ : ℝ) : ℂ) ^ 2 / (2 * H.m)) * ∑ i, ∂[i] (∂[i] ⇑f) y +
          (H.potential y : ℂ) * f y) =
      ∫ y, ((-((Constants.ℏ : ℝ) ^ 2 / (2 * H.m)) * Δ (boundState H N l (toFun P)) y +
          H.potential y * boundState H N l (toFun P) y : ℝ) : ℂ) * f y := by
  set ψ := boundState H N l (toFun P)
  set c : ℂ := -((Constants.ℏ : ℝ) : ℂ) ^ 2 / (2 * H.m)
  have hψc : Continuous ψ := continuous_boundState H N l P
  -- the second derivatives of `f` form a Schwartz map
  set S : 𝓢(Space d, ℂ) := ∑ i : Fin d, ∂_{Space.basis i} (∂_{Space.basis i} f)
  have hS : ∀ y, ∑ i, ∂[i] (∂[i] ⇑f) y = S y := fun y => by
    simp only [S, _root_.sum_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [deriv_schwartz f i, deriv_schwartz]
  -- integrability of the three pieces
  have I₁ : Integrable fun y => (ψ y : ℂ) * (c * S y) := by
    simpa [mul_left_comm] using
      ((isPolyBounded_boundState H hd hk N l P).integrable_ofReal_mul_schwartz
        hψc.aestronglyMeasurable S).const_mul c
  have I₂ := integrable_boundState_mul_potential_mul H hd hk N l P f
  have I₃ := integrable_laplacian_boundState_mul H hd hk N l hP f
  -- assemble
  have hkin : ∫ y, (ψ y : ℂ) * S y = ∫ y, ((Δ ψ y : ℝ) : ℂ) * f y := by
    have h := integral_boundState_mul_sum_deriv_deriv H hd hk N l hP f
    simp only [hS] at h
    exact h
  simp only [hS]
  have hL : ∫ y, (ψ y : ℂ) * (c * S y + (H.potential y : ℂ) * f y) =
      c * (∫ y, (ψ y : ℂ) * S y) + ∫ y, (ψ y : ℂ) * ((H.potential y : ℂ) * f y) := by
    simp only [mul_add]
    rw [integral_add I₁ I₂]
    congr 1
    rw [← integral_const_mul]
    exact integral_congr_ae (Filter.Eventually.of_forall fun y => by ring)
  have hR : ∫ y, ((-((Constants.ℏ : ℝ) ^ 2 / (2 * H.m)) * Δ ψ y + H.potential y * ψ y : ℝ) : ℂ) *
      f y = c * (∫ y, ((Δ ψ y : ℝ) : ℂ) * f y) +
        ∫ y, (ψ y : ℂ) * ((H.potential y : ℂ) * f y) := by
    rw [show c * (∫ y, ((Δ ψ y : ℝ) : ℂ) * f y) = ∫ y, c * (((Δ ψ y : ℝ) : ℂ) * f y) from
      (integral_const_mul c _).symm, ← integral_add (I₃.const_mul c) I₂]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only [c]
    push_cast
    ring
  rw [hL, hR, hkin]

/-- The weak eigenvalue equation `⟪E ψ, φ⟫ = ⟪ψ, H φ⟫` of a bound state `ψ` of the level `N + l`,
for every `φ` in the domain of the Hamiltonian. -/
lemma inner_boundStateHS_hamiltonianOperator (H : HydrogenAtom d) (hd : 2 ≤ d) (hk : 0 < H.k)
    (N l : ℕ) {P : MvPolynomial (Fin d) ℝ} (hP : P ∈ harmonicSubmodule d l)
    (φ : H.hamiltonianOperator.domain) :
    ⟪(H.energyLevel (N + l) : ℂ) • boundStateHS H hd hk N l P, (φ : SpaceDHilbertSpace d)⟫_ℂ =
      ⟪boundStateHS H hd hk N l P, H.hamiltonianOperator φ⟫_ℂ := by
  obtain ⟨f, hφ, hHφ⟩ := hamiltonianOperator_apply_ae H φ
  set ψ := boundState H N l (toFun P)
  have hψ : (boundStateHS H hd hk N l P : SpaceDHilbertSpace d) =ᵐ[volume]
      fun y => (ψ y : ℂ) := coeFn_mk _
  rw [inner_smul_left, L2.inner_def, L2.inner_def, Complex.conj_ofReal]
  -- left side: `E ∫ ψ f`
  have hL : ∫ y, ⟪(boundStateHS H hd hk N l P : SpaceDHilbertSpace d) y,
      (φ : SpaceDHilbertSpace d) y⟫_ℂ = ∫ y, (ψ y : ℂ) * f y := by
    refine integral_congr_ae ?_
    filter_upwards [hψ, hφ] with y h₁ h₂
    rw [h₁, h₂, RCLike.inner_apply, Complex.conj_ofReal, mul_comm]
  -- right side: `∫ ψ H f`
  have hR : ∫ y, ⟪(boundStateHS H hd hk N l P : SpaceDHilbertSpace d) y,
      (H.hamiltonianOperator φ : SpaceDHilbertSpace d) y⟫_ℂ =
      ∫ y, (ψ y : ℂ) * ((-((Constants.ℏ : ℝ) : ℂ) ^ 2 / (2 * H.m)) * ∑ i, ∂[i] (∂[i] ⇑f) y +
        (H.potential y : ℂ) * f y) := by
    refine integral_congr_ae ?_
    filter_upwards [hψ, hHφ] with y h₁ h₂
    rw [h₁, h₂, RCLike.inner_apply, Complex.conj_ofReal, mul_comm]
  rw [hL, hR, integral_boundState_mul_hamiltonian H hd hk N l hP f, ← integral_const_mul]
  -- away from the nucleus the eigenvalue equation holds pointwise
  refine integral_congr_ae ?_
  filter_upwards [ae_ne_zero_of_two_le hd] with y hy
  rw [boundState_eigen_of_mem_harmonicSubmodule H hd hk N l hP hy]
  push_cast
  ring

end PhyslibAlpha.Hydrogen
