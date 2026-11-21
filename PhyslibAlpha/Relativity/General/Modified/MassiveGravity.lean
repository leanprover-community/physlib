/-
Copyright (c) 2026 Alex Vergara Gil. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Vergara Gil
-/
module

public import PhyslibAlpha.Relativity.General.Einstein
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!

# Fierz–Pauli and dRGT massive gravity

Fierz–Pauli Lorentz-invariant mass term, Boulware–Deser ghost-free tuning `α = -1`, tracelessness of
transverse massive gravitons, the van Dam–Veltman–Zakharov (vDVZ) propagator discontinuity, and
de Rham–Gabadadze–Tolley (dRGT) elementary symmetric potential polynomials.

## i. Overview

Giving the graviton a non-zero mass `m > 0` on a Minkowski reference background `η = eta4`
requires a quadratic potential built from the two Lorentz scalars `h_{ab} h^{ab}` and
`h² = (η^{ab} h_{ab})²`. Fierz and Pauli showed that only the specific combination
`h_{ab} h^{ab} - h²` (`α = -1`) eliminates the sixth (Boulware–Deser) ghost degree of freedom: for
pure longitudinal scalar fluctuations `h_{ab} = ∂_a ∂_b φ`, the kinetic-mass trace forces `h = 0`
on shell, leaving the `2 s + 1 = 5` polarizations of a massive spin-2 particle.

In the massless limit `m → 0`, the helicity-0 mode remains coupled to the trace of the matter
stress-energy tensor with strength `1/3` instead of the GR factor `1/2`, producing the van
Dam–Veltman–Zakharov (vDVZ) discontinuity: rescaling Newton's constant by `3/4` to match static
Newtonian gravity reduces light deflection around a static mass to `3/4` of the General Relativity
prediction. Non-linear completion without reviving the Boulware–Deser ghost is achieved by the dRGT
potential built from the elementary symmetric polynomials `e_k(K)` of
`K^a_b = δ^a_b - (√(g⁻¹ f))^a_b`.

## ii. Key results

- `hContractionSq`, `hTraceEta`, `fierzPauliLagrangian`, `fpMassTensor` : quadratic mass invariants
  and Fierz–Pauli mass variation tensor.
- `fpMassTensor_trace`, `fpMassTensor_trace_tuned`, `fp_traceless_of_zero_trace_source` : trace
  identity `η^{ij} M_{ij}(α) = (m² / 2) (1 + 4 α) h`, special value `-(3 / 2) m² h` at `α = -1`,
  and vanishing trace `h = 0` for `m ≠ 0`.
- `grPropagatorCoupling`, `massivePropagatorCoupling`, `vdvz_static_ratio`,
  `vdvz_light_deflection_ratio` : vDVZ `4/3` static coupling enhancement and `3/4` light-bending
  discontinuity.
- `elemSymm0`, `elemSymm1`, `elemSymm2`, `elemSymm3`, `dRGTPotential`,
  `dRGTPotential_vacuum_zero` : dRGT elementary symmetric polynomials of `K` and vanishing
  potential at the Minkowski vacuum `K = 0`.

## iii. Table of contents

- A. Fierz–Pauli mass term and ghost-free trace constraint
- B. The vDVZ propagator discontinuity
- C. dRGT elementary symmetric potential polynomials

## iv. References

* None.

-/

@[expose] public section

namespace GeneralRelativity

namespace Modified

namespace MassiveGravity

/-!

## A. Fierz–Pauli mass term and ghost-free trace constraint

-/

/-- Minkowski trace `h = η^{ab} h_{ab}` of a rank-2 perturbation `h : Tensor2 4`. -/
def hTraceEta (h : Tensor2 4) : ℝ :=
  ∑ a : Fin 4, eta4 a a * h a a

/-- Full Minkowski quadratic contraction `h_{ab} h^{ab} = ∑_{a,b} η^{aa} η^{bb} (h_{ab})²`. -/
def hContractionSq (h : Tensor2 4) : ℝ :=
  ∑ a : Fin 4, ∑ b : Fin 4, eta4 a a * eta4 b b * h a b * h a b

/-- General Lorentz-invariant quadratic graviton mass Lagrangian density
`ℒ_mass(α) = -(m² / 4) (h_{ab} h^{ab} + α h²)`. The Fierz–Pauli tuning is `α = -1`. -/
noncomputable def fierzPauliLagrangian (m α : ℝ) (h : Tensor2 4) : ℝ :=
  -(m ^ 2 / 4) * (hContractionSq h + α * hTraceEta h ^ 2)

/-- Mass-term contribution to the linearized field equations:
`M_{ij}(α) = (m² / 2) (h_{ij} + α η_{ij} h)`. -/
noncomputable def fpMassTensor (m α : ℝ) (h : Tensor2 4) : Tensor2 4 :=
  fun i j => (m ^ 2 / 2) * (h i j + α * eta4 i j * hTraceEta h)

/-- Minkowski trace of the general mass tensor:
`η^{ij} M_{ij}(α) = (m² / 2) (1 + 4 α) h`. -/
lemma fpMassTensor_trace (m α : ℝ) (h : Tensor2 4) :
    (∑ i : Fin 4, eta4 i i * fpMassTensor m α h i i) =
      (m ^ 2 / 2) * (1 + 4 * α) * hTraceEta h := by
  unfold fpMassTensor hTraceEta
  simp only [Fin.sum_univ_four, eta4]
  norm_num
  ring

/-- At the Fierz–Pauli ghost-free point `α = -1`, the trace of the mass tensor is
`-(3 / 2) m² h`. -/
lemma fpMassTensor_trace_tuned (m : ℝ) (h : Tensor2 4) :
    (∑ i : Fin 4, eta4 i i * fpMassTensor m (-1) h i i) = -(3 / 2) * m ^ 2 * hTraceEta h := by
  rw [fpMassTensor_trace]
  ring

/-- Longitudinal kinetic-mass decoupling criterion: for a 1D plane-wave longitudinal mode
`h_{00} = ϕ''`, all other components `0`, the quadratic mass combination `h_{ab} h^{ab} + α h²`
vanishes (preventing a fourth-order time-derivative Boulware–Deser ghost) if and only if
`α = -1`. -/
lemma longitudinal_time_ghost_free_iff (α ϕdd : ℝ) (hϕ : ϕdd ≠ 0) :
    hContractionSq (fun i j => if i = 0 ∧ j = 0 then ϕdd else 0)
      + α * hTraceEta (fun i j => if i = 0 ∧ j = 0 then ϕdd else 0) ^ 2 = 0 ↔ α = -1 := by
  unfold hContractionSq hTraceEta
  simp only [Fin.sum_univ_four, eta4]
  norm_num
  constructor
  · intro h
    have h2 : ϕdd ^ 2 ≠ 0 := pow_ne_zero 2 hϕ
    have hfac : (1 + α) * ϕdd ^ 2 = 0 := by linarith
    rcases mul_eq_zero.mp hfac with h1 | h2'
    · linarith
    · exact False.elim (h2 h2')
  · intro h
    subst h
    ring

/-- On shell in vacuum (where the divergence constraint forces the trace of the mass tensor to
vanish), any non-zero Fierz–Pauli mass `m ≠ 0` at `α = -1` forces the metric perturbation to be
traceless (`h = 0`). -/
lemma fp_traceless_of_zero_trace_source (m : ℝ) (hm : m ≠ 0) (h : Tensor2 4)
    (htr : (∑ i : Fin 4, eta4 i i * fpMassTensor m (-1) h i i) = 0) :
    hTraceEta h = 0 := by
  rw [fpMassTensor_trace_tuned] at htr
  have hm2 : m ^ 2 ≠ 0 := pow_ne_zero 2 hm
  have hfac : (-(3 / 2 : ℝ) * m ^ 2) * hTraceEta h = 0 := by linarith
  rcases mul_eq_zero.mp hfac with h1 | h2
  · exfalso; apply hm2; linarith
  · exact h2

/-!

## B. The vDVZ propagator discontinuity

-/

/-- Minkowski trace `T = η^{ab} T_{ab}` of a matter stress-energy tensor `T : Tensor2 4`. -/
def stressTrace (T : Tensor2 4) : ℝ :=
  ∑ a : Fin 4, eta4 a a * T a a

/-- Massless General Relativity spin-2 propagator residue contracted between two conserved
stress-energy tensors `T₁, T₂`: `T₁_{ab} T₂^{ab} - ½ T₁ T₂`. -/
noncomputable def grPropagatorCoupling (T1 T2 : Tensor2 4) : ℝ :=
  (∑ a : Fin 4, ∑ b : Fin 4, eta4 a a * eta4 b b * T1 a b * T2 a b)
    - (1 / 2) * stressTrace T1 * stressTrace T2

/-- Massive Fierz–Pauli spin-2 propagator residue in the `m → 0` limit contracted between two
conserved stress-energy tensors `T₁, T₂`: `T₁_{ab} T₂^{ab} - ⅓ T₁ T₂`. -/
noncomputable def massivePropagatorCoupling (T1 T2 : Tensor2 4) : ℝ :=
  (∑ a : Fin 4, ∑ b : Fin 4, eta4 a a * eta4 b b * T1 a b * T2 a b)
    - (1 / 3) * stressTrace T1 * stressTrace T2

/-- Stress-energy tensor of a static non-relativistic mass density `ρ`: `T_{00} = ρ`, all other
components zero. -/
def staticSource (ρ : ℝ) : Tensor2 4 :=
  fun i j => if i = 0 ∧ j = 0 then ρ else 0

/-- The vDVZ static discontinuity: for two static non-relativistic sources `ρ₁, ρ₂`, the massive
graviton exchange amplitude is `4/3` times the massless General Relativity amplitude. -/
lemma vdvz_static_ratio (ρ1 ρ2 : ℝ) :
    massivePropagatorCoupling (staticSource ρ1) (staticSource ρ2) =
      (4 / 3) * grPropagatorCoupling (staticSource ρ1) (staticSource ρ2) := by
  unfold massivePropagatorCoupling grPropagatorCoupling stressTrace staticSource
  simp only [Fin.sum_univ_four, eta4]
  norm_num
  ring

/-- The vDVZ light-deflection discontinuity: for a null electromagnetic/light probe `T_light`
(`stressTrace T_light = 0`), after calibrating the massive gravitational coupling by `3/4` to
reproduce Newton's law for static masses, the effective coupling to light is strictly `3/4` of the
General Relativity coupling. -/
lemma vdvz_light_deflection_ratio (Tmass Tlight : Tensor2 4) (hnull : stressTrace Tlight = 0) :
    (3 / 4) * massivePropagatorCoupling Tmass Tlight =
      (3 / 4) * grPropagatorCoupling Tmass Tlight := by
  unfold massivePropagatorCoupling grPropagatorCoupling
  rw [hnull]
  ring

/-!

## C. dRGT elementary symmetric potential polynomials

-/

/-- Matrix power traces `tr(K)`, `tr(K²)`, `tr(K³)` of the dRGT building-block tensor
`K^a_b = δ^a_b - (√(g⁻¹ f))^a_b`. -/
def trK1 (K : Tensor2 4) : ℝ := ∑ a : Fin 4, K a a

/-- Quadratic power trace `tr(K²) = ∑_{a,b} K^a_b K^b_a`. -/
def trK2 (K : Tensor2 4) : ℝ := ∑ a : Fin 4, ∑ b : Fin 4, K a b * K b a

/-- Cubic power trace `tr(K³) = ∑_{a,b,c} K^a_b K^b_c K^c_a`. -/
def trK3 (K : Tensor2 4) : ℝ := ∑ a : Fin 4, ∑ b : Fin 4, ∑ c : Fin 4, K a b * K b c * K c a

/-- Zeroth dRGT elementary symmetric polynomial `e₀(K) = 1`. -/
def elemSymm0 (_K : Tensor2 4) : ℝ := 1

/-- First dRGT elementary symmetric polynomial `e₁(K) = [K] = tr(K)`. -/
def elemSymm1 (K : Tensor2 4) : ℝ := trK1 K

/-- Second dRGT elementary symmetric polynomial `e₂(K) = ½ ([K]² - [K²])`. -/
noncomputable def elemSymm2 (K : Tensor2 4) : ℝ := (1 / 2) * (trK1 K ^ 2 - trK2 K)

/-- Third dRGT elementary symmetric polynomial `e₃(K) = ⅙ ([K]³ - 3 [K] [K²] + 2 [K³])`. -/
noncomputable def elemSymm3 (K : Tensor2 4) : ℝ :=
  (1 / 6) * (trK1 K ^ 3 - 3 * trK1 K * trK2 K + 2 * trK3 K)

/-- On an isotropic spatial deformation `K = diag(0, λ, λ, λ)`, the elementary symmetric
polynomials evaluate to the binomial values `e₁ = 3 λ`, `e₂ = 3 λ²`, `e₃ = λ³`. -/
lemma elemSymm_isotropic3 (lam : ℝ) :
    let K : Tensor2 4 := Matrix.diagonal ![0, lam, lam, lam]
    elemSymm1 K = 3 * lam ∧ elemSymm2 K = 3 * lam ^ 2 ∧ elemSymm3 K = lam ^ 3 := by
  intro K
  have h0 : K 0 0 = 0 := rfl
  have h1 : K 1 1 = lam := rfl
  have h2 : K 2 2 = lam := rfl
  have h3 : K 3 3 = lam := rfl
  have hoff : ∀ i j : Fin 4, i ≠ j → K i j = 0 := fun i j hij => Matrix.diagonal_apply_ne _ hij
  unfold elemSymm1 elemSymm2 elemSymm3 trK1 trK2 trK3
  simp only [Fin.sum_univ_four, h0, h1, h2, h3, hoff, ne_eq, Fin.reduceEq, not_false_eq_true]
  refine ⟨by ring, by ring, by ring⟩

/-- Cubic dRGT ghost-free potential `U(K) = e₂(K) + α₃ e₃(K)` with free parameter `α₃`
(normalized so the quadratic term reproduces the Fierz–Pauli mass term). -/
noncomputable def dRGTPotential (α3 : ℝ) (K : Tensor2 4) : ℝ :=
  elemSymm2 K + α3 * elemSymm3 K

/-- At the Minkowski vacuum `K = 0` (`g = f`), the dRGT potential vanishes identically
(zero cosmological constant / tadpole-free vacuum). -/
lemma dRGTPotential_vacuum_zero (α3 : ℝ) :
    dRGTPotential α3 0 = 0 := by
  unfold dRGTPotential elemSymm2 elemSymm3 trK1 trK2 trK3
  simp

end MassiveGravity

end Modified

end GeneralRelativity
