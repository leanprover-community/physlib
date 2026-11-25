/-
Copyright (c) 2025 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina, Joseph Tooby-Smith
-/
module

public import Physlib.StatisticalMechanics.CanonicalEnsemble.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
/-!
# Canonical Ensemble: Thermodynamic Identities and Relations

This file develops relations between the *mathematical* objects defined in
`Basic.lean` and the *physical* thermodynamic quantities, together with
calculus identities for the canonical ensemble.

## Contents Overview

1. Helmholtz Free Energies
  * `mathematicalHelmholtzFreeEnergy`
  * Relation to physical `helmholtzFreeEnergy` with semi–classical correction.

2. Entropy Relations
  * Pointwise logarithm of (mathematical / physical) Boltzmann probabilities.
  * Key identity:
      `differentialEntropy = kB * β * meanEnergy + kB * log Z_math`
  * Fundamental link:
      `thermodynamicEntropy = differentialEntropy - kB * dof * log h`
    (semi–classical correction term).
  * Specializations removing the correction when `dof = 0` or `phaseSpaceUnit = 1`.

3. Fundamental Thermodynamic Identity
  * Proof of `F = U - T S_thermo`.
  * Equivalent rearrangements giving entropy from energies and free energy.
  * Discrete / normalized specialization (no correction).

4. Mean energy as
      `U = - d/dβ log Z_math`
      and likewise with the physical partition function (constant factor cancels).

## Design Notes

* All derivative statements are given as `derivWithin` on `Set.Ioi 0`, matching the physical
  domain β > 0.
* Assumptions (finiteness, integrability) are parameterized to keep lemmas reusable.
* Semi–classical correction appears systematically as
    `kB * dof * log phaseSpaceUnit`.

## References

* Same references as `Basic.lean`. [ref: landau_statphys1]
* Same references as `Basic.lean`, especially the identities `F = U - T S` and
  `U = -∂_β log Z`. [ref: tong_statistical_physics]
-/

@[expose] public section
set_option linter.unusedVariables.funArgs false

namespace CanonicalEnsemble

open MeasureTheory Real Temperature

open scoped ENNReal

variable {ι ι1 : Type} [MeasurableSpace ι]
  [MeasurableSpace ι1] (kB : BoltzmannConstant) (𝓒 : CanonicalEnsemble ι)
  (𝓒1 : CanonicalEnsemble ι1)

/-- An intermediate potential defined from the mathematical partition function. See
`helmholtzFreeEnergy` for the physical thermodynamic quantity. -/
noncomputable def mathematicalHelmholtzFreeEnergy (T : Temperature) : ℝ :=
  - (kB : ℝ) * T.val * Real.log (𝓒.mathematicalPartitionFunction kB T)

/-- The relationship between the physical Helmholtz Free Energy and the Helmholtz Potential. -/
lemma helmholtzFreeEnergy_eq_helmholtzMathematicalFreeEnergy_add_correction (T : Temperature)
    [IsFiniteMeasure (𝓒.μBolt kB T)] [NeZero 𝓒.μ] :
    𝓒.helmholtzFreeEnergy kB T = 𝓒.mathematicalHelmholtzFreeEnergy kB T +
      (kB : ℝ) * T.val * 𝓒.dof * Real.log (𝓒.phaseSpaceunit) := by
  simp only [helmholtzFreeEnergy, mathematicalHelmholtzFreeEnergy, log_partitionFunction]
  ring

/-- General identity: S_diff = kB β ⟨E⟩ + kB log Z_math.
This connects the differential entropy to the mean energy and the mathematical partition function.
Integrability of `log (probability …)` follows from the pointwise formula. -/
lemma differentialEntropy_eq_kB_beta_meanEnergy_add_kB_log_mathZ
    (T : Temperature) [IsFiniteMeasure (𝓒.μBolt kB T)] [NeZero 𝓒.μ]
    (hE : Integrable 𝓒.energy (𝓒.μProd kB T)) :
    𝓒.differentialEntropy kB T = (kB : ℝ) * (T.β kB : ℝ) * 𝓒.meanEnergy kB T +
      (kB : ℝ) * Real.log (𝓒.mathematicalPartitionFunction kB T) := by
  have h_log_prob : ∀ i, Real.log (𝓒.probability kB T i)
      = -(T.β kB : ℝ) * 𝓒.energy i - Real.log (𝓒.mathematicalPartitionFunction kB T) := fun i => by
    rw [probability, Real.log_div (Real.exp_pos _).ne'
      (mathematicalPartitionFunction_pos kB 𝓒 T).ne', Real.log_exp]
  simp only [differentialEntropy, meanEnergy]
  rw [integral_congr_ae (ae_of_all _ h_log_prob),
    integral_sub (hE.const_mul _) (integrable_const _), integral_const_mul, integral_const]
  simp only [probReal_univ, smul_eq_mul]
  ring

/-- Pointwise logarithm of the Boltzmann probability. -/
lemma log_probability
    (𝓒 : CanonicalEnsemble ι) (T : Temperature)
    [IsFiniteMeasure (𝓒.μBolt kB T)] [NeZero 𝓒.μ] (i : ι) :
    Real.log (𝓒.probability kB T i)
      = - (β kB T) * 𝓒.energy i - Real.log (𝓒.mathematicalPartitionFunction kB T) := by
  simp [probability, Real.log_div, (mathematicalPartitionFunction_pos kB (𝓒 := 𝓒) (T := T)).ne',
    Real.log_exp, sub_eq_add_neg]

/-- Auxiliary identity: `kB · β = 1 / T`.
`β` is defined as `1 / (kB · T)` (see `Temperature.β`). -/
@[simp]
lemma kB_mul_beta (T : Temperature) (hT : 0 < T.val) :
    (kB : ℝ) * (T.β kB : ℝ) = 1 / T.val := by
  have hT0 : (T.val : ℝ) ≠ 0 := by exact_mod_cast hT.ne'
  unfold Temperature.β
  change (kB : ℝ) * (1 / ((kB : ℝ) * (T.val : ℝ))) = 1 / (T.val : ℝ)
  field_simp [kB.val_ne_zero, hT0]

/-- Fundamental relation between thermodynamic and differential entropy:
`S_thermo = S_diff - kB * dof * log h`. -/
lemma thermodynamicEntropy_eq_differentialEntropy_sub_correction
    (T : Temperature)
    (hE : Integrable 𝓒.energy (𝓒.μProd kB T))
    [IsFiniteMeasure (𝓒.μBolt kB T)] [NeZero 𝓒.μ] :
    𝓒.thermodynamicEntropy kB T
      = 𝓒.differentialEntropy kB T
        - (kB : ℝ) * 𝓒.dof * Real.log 𝓒.phaseSpaceunit := by
  have h_int_log_prob : Integrable (fun i => Real.log (𝓒.probability kB T i)) (𝓒.μProd kB T) := by
    have h_eq : (fun i => Real.log (𝓒.probability kB T i))
        = fun i => -(T.β kB : ℝ) * 𝓒.energy i
            - Real.log (𝓒.mathematicalPartitionFunction kB T) :=
      funext fun i => 𝓒.log_probability kB T i
    rw [h_eq]
    exact (hE.const_mul _).sub (integrable_const _)
  simp only [thermodynamicEntropy_def, differentialEntropy]
  rw [integral_congr_ae (ae_of_all _ fun i => 𝓒.log_physicalProbability kB T i),
    integral_add h_int_log_prob (integrable_const _), integral_const]
  simp only [probReal_univ, smul_eq_mul]
  ring

/-- No semiclassical correction when `dof = 0`. -/
lemma thermodynamicEntropy_eq_differentialEntropy_of_dof_zero
    (T : Temperature) (hE : Integrable 𝓒.energy (𝓒.μProd kB T))
    (h0 : 𝓒.dof = 0)
    [IsFiniteMeasure (𝓒.μBolt kB T)] [NeZero 𝓒.μ] :
    𝓒.thermodynamicEntropy kB T = 𝓒.differentialEntropy kB T := by
  simpa [h0] using
    𝓒.thermodynamicEntropy_eq_differentialEntropy_sub_correction kB (T := T) hE

/-- No semiclassical correction when `phase_space_unit = 1`. -/
lemma thermodynamicEntropy_eq_differentialEntropy_of_phase_space_unit_one
    (T : Temperature) (hE : Integrable 𝓒.energy (𝓒.μProd kB T))
    (h1 : 𝓒.phaseSpaceunit = 1)
    [IsFiniteMeasure (𝓒.μBolt kB T)] [NeZero 𝓒.μ] :
    𝓒.thermodynamicEntropy kB T = 𝓒.differentialEntropy kB T := by
  simpa [h1] using
    𝓒.thermodynamicEntropy_eq_differentialEntropy_sub_correction kB (T := T) hE
/-

## Thermodynamic Identities

-/

/-!

## The Fundamental Thermodynamic Identity

-/

/-- The Helmholtz free energy `F` is related to the mean energy `U` and the absolute
thermodynamic entropy `S` by the identity `F = U - TS`. This theorem shows that the
statistically-defined quantities in this framework correctly satisfy this principle of
thermodynamics. -/
theorem helmholtzFreeEnergy_eq_meanEnergy_sub_temp_mul_thermodynamicEntropy
    (T : Temperature) (hT : 0 < T.val)
    [IsFiniteMeasure (𝓒.μBolt kB T)] [NeZero 𝓒.μ]
    (hE : Integrable 𝓒.energy (𝓒.μProd kB T)) :
    𝓒.helmholtzFreeEnergy kB T
      = 𝓒.meanEnergy kB T - T.val * 𝓒.thermodynamicEntropy kB T := by
  have hTne : (T.val : ℝ) ≠ 0 := by exact_mod_cast hT.ne'
  have hkβT : T.val * ((kB : ℝ) * (T.β kB : ℝ)) = 1 := by
    rw [kB_mul_beta kB T hT, mul_one_div, div_self hTne]
  rw [helmholtzFreeEnergy_def, log_partitionFunction,
    𝓒.thermodynamicEntropy_eq_differentialEntropy_sub_correction kB (T := T) hE,
    𝓒.differentialEntropy_eq_kB_beta_meanEnergy_add_kB_log_mathZ kB (T := T) hE]
  linear_combination 𝓒.meanEnergy kB T * hkβT

/-- **Theorem: Helmholtz identity with semi–classical correction term**.
Physical identity (always true for `T > 0`) :
  (U - F)/T = S_thermo
and:
  S_thermo = S_diff - kB * dof * log h.
Hence:
  S_diff = (U - F)/T + kB * dof * log h.
This theorem gives the correct relation for the (mathematical / differential) entropy.
(Removing the correction is only valid in normalized discrete cases
with `dof = 0` (or `phaseSpaceUnit = 1`).) -/
theorem differentialEntropy_eq_meanEnergy_sub_helmholtz_div_temp_add_correction
    (𝓒 : CanonicalEnsemble ι) (T : Temperature)
    [IsFiniteMeasure (𝓒.μBolt kB T)] [NeZero 𝓒.μ]
    (hT : 0 < T.val)
    (hE : Integrable 𝓒.energy (𝓒.μProd kB T)) :
    𝓒.differentialEntropy kB T
      = (𝓒.meanEnergy kB T - 𝓒.helmholtzFreeEnergy kB T) / T.val
        + (kB : ℝ) * 𝓒.dof * Real.log 𝓒.phaseSpaceunit := by
  have hTne : (T.val : ℝ) ≠ 0 := by exact_mod_cast hT.ne'
  rw [differentialEntropy_eq_kB_beta_meanEnergy_add_kB_log_mathZ kB 𝓒 T hE,
    helmholtzFreeEnergy_def, log_partitionFunction, kB_mul_beta kB T hT]
  field_simp
  ring

/-- Discrete / normalized specialization of the previous theorem.
If either `dof = 0` (no semiclassical correction) or `phaseSpaceUnit = 1`
(so `log h = 0`), the correction term vanishes and we recover the bare Helmholtz identity
for the (differential) entropy. -/
lemma differentialEntropy_eq_meanEnergy_sub_helmholtz_div_temp
    (𝓒 : CanonicalEnsemble ι) (T : Temperature)
    [IsFiniteMeasure (𝓒.μBolt kB T)] [NeZero 𝓒.μ]
    (hT : 0 < T.val)
    (hE : Integrable 𝓒.energy (𝓒.μProd kB T))
    (hNorm : 𝓒.dof = 0 ∨ 𝓒.phaseSpaceunit = 1) :
    𝓒.differentialEntropy kB T
      = (𝓒.meanEnergy kB T - 𝓒.helmholtzFreeEnergy kB T) / T.val := by
  have hmain :=
    differentialEntropy_eq_meanEnergy_sub_helmholtz_div_temp_add_correction kB
      (𝓒:=𝓒) (T:=T) hT hE
  rcases hNorm with h | h <;> simp [hmain, h]

/-- Chain rule convenience lemma for `log ∘ f` on a set. -/
lemma hasDerivWithinAt_log_comp
    {f : ℝ → ℝ} {f' : ℝ} {s : Set ℝ} {x : ℝ}
    (hf : HasDerivWithinAt f f' s x) (hx : f x ≠ 0) :
    HasDerivWithinAt (fun t => Real.log (f t)) ((f x)⁻¹ * f') s x :=
  (Real.hasDerivAt_log hx).comp_hasDerivWithinAt x hf

/-- A version rewriting the derivative value with `1 / f x`. -/
lemma hasDerivWithinAt_log_comp'
    {f : ℝ → ℝ} {f' : ℝ} {s : Set ℝ} {x : ℝ}
    (hf : HasDerivWithinAt f f' s x) (hx : f x ≠ 0) :
    HasDerivWithinAt (fun t => Real.log (f t))
      ((1 / f x) * f') s x := by
  simpa [one_div] using hasDerivWithinAt_log_comp hf hx

lemma integral_bolt_eq_integral_mul_exp
    {ι} [MeasurableSpace ι] (𝓒 : CanonicalEnsemble ι) (T : Temperature)
    (φ : ι → ℝ) :
    ∫ x, φ x ∂ 𝓒.μBolt kB T
      = ∫ x, φ x * Real.exp (-T.β kB * 𝓒.energy x) ∂ 𝓒.μ := by
  unfold μBolt
  set f : ι → ℝ≥0∞ := fun x => ENNReal.ofReal (Real.exp (-T.β kB * 𝓒.energy x))
  have hf_meas : Measurable f := by fun_prop
  have hf_lt_top : ∀ᵐ x ∂ 𝓒.μ, f x < ∞ := by simp [f]
  have h := integral_withDensity_eq_integral_toReal_smul (μ := 𝓒.μ) hf_meas hf_lt_top φ
  simpa [f, ENNReal.toReal_ofReal, Real.exp_nonneg, smul_eq_mul, mul_comm] using h

set_option linter.unusedVariables false in
/-- A specialization of `integral_bolt_eq_integral_mul_exp`
to the energy observable. -/
lemma integral_energy_bolt
    {ι} [MeasurableSpace ι] (𝓒 : CanonicalEnsemble ι) (T : Temperature) :
    ∫ x, 𝓒.energy x ∂ 𝓒.μBolt kB T
      = ∫ x, 𝓒.energy x * Real.exp (-T.β kB * 𝓒.energy x) ∂ 𝓒.μ :=
  integral_bolt_eq_integral_mul_exp kB 𝓒 T 𝓒.energy

/-- The mean energy can be expressed as a ratio of integrals. -/
lemma meanEnergy_eq_ratio_of_integrals
    (𝓒 : CanonicalEnsemble ι) (T : Temperature) :
    𝓒.meanEnergy kB T =
      (∫ i, 𝓒.energy i * Real.exp (- T.β kB * 𝓒.energy i) ∂ 𝓒.μ) /
        (∫ i, Real.exp (- T.β kB * 𝓒.energy i) ∂ 𝓒.μ) := by
  unfold meanEnergy μProd
  have h_den : (𝓒.μBolt kB T Set.univ).toReal = ∫ x, Real.exp (- T.β kB * 𝓒.energy x) ∂ 𝓒.μ :=
    mathematicalPartitionFunction_eq_integral kB (𝓒 := 𝓒) (T := T)
  rw [integral_smul_measure, smul_eq_mul, integral_energy_bolt, ENNReal.toReal_inv, h_den]
  ring

/-- The mean energy is the negative derivative of the logarithm of the
(mathematical) partition function with respect to β = 1/(kB T).
see: Tong (§1.3.2, §1.3.3), L&L (§31, implicitly, and §36)
Here the derivative is a `derivWithin` over `Set.Ioi 0`
since `β > 0`. -/
lemma meanEnergy_eq_neg_deriv_log_mathZ_of_beta
    (𝓒 : CanonicalEnsemble ι) (T : Temperature)
    (hT_pos : 0 < T.val) [IsFiniteMeasure (𝓒.μBolt kB T)] [NeZero 𝓒.μ]
    (h_deriv :
        HasDerivWithinAt
          (fun β : ℝ => ∫ i, Real.exp (-β * 𝓒.energy i) ∂ 𝓒.μ)
          (- ∫ i, 𝓒.energy i * Real.exp (-(T.β kB : ℝ) * 𝓒.energy i) ∂𝓒.μ)
          (Set.Ioi 0) (T.β kB : ℝ)) :
    𝓒.meanEnergy kB T =
      - (derivWithin
          (fun β : ℝ => Real.log (∫ i, Real.exp (-β * 𝓒.energy i) ∂𝓒.μ))
          (Set.Ioi 0) (T.β kB : ℝ)) := by
  set f : ℝ → ℝ := fun β => ∫ i, Real.exp (-β * 𝓒.energy i) ∂𝓒.μ
  have hβ_pos : 0 < (T.β kB : ℝ) := beta_pos kB T hT_pos
  have hZpos : 0 < f (T.β kB : ℝ) := by
    simpa [f, mathematicalPartitionFunction_eq_integral kB (𝓒 := 𝓒) (T := T)]
      using mathematicalPartitionFunction_pos kB (𝓒 := 𝓒) (T := T)
  have h_log : HasDerivWithinAt (fun β : ℝ => Real.log (f β))
      ((1 / f (T.β kB : ℝ)) * (- ∫ i, 𝓒.energy i * Real.exp (-(T.β kB : ℝ) * 𝓒.energy i) ∂𝓒.μ))
      (Set.Ioi 0) (T.β kB : ℝ) := by
    simpa [f] using hasDerivWithinAt_log_comp' (hf := h_deriv) (hx := hZpos.ne')
  have hUD : UniqueDiffWithinAt ℝ (Set.Ioi (0:ℝ)) (T.β kB : ℝ) :=
    isOpen_Ioi.uniqueDiffWithinAt hβ_pos
  rw [meanEnergy_eq_ratio_of_integrals, h_log.derivWithin hUD]
  simp only [f]
  ring

section Ratios

open Set

open scoped Topology Filter ENNReal

/-- Helper: equality (on `Set.Ioi 0`) between the β–parametrized logarithm of the
physical partition function and the β–parametrized logarithm of the *mathematical*
partition function up to the (β–independent) semiclassical correction. This is used only
to identify derivatives (the correction drops).
We add the hypothesis `h_fin` giving finiteness of the Boltzmann measure for every β > 0
(as needed to ensure the mathematical partition function is strictly positive). -/
lemma log_phys_eq_log_math_sub_const_on_Ioi
    (𝓒 : CanonicalEnsemble ι) [NeZero 𝓒.μ]
    (h_fin :
      ∀ β > 0,
        IsFiniteMeasure (𝓒.μBolt kB (Temperature.ofβ kB (Real.toNNReal β)))) :
    Set.EqOn
      (fun β : ℝ =>
        Real.log (𝓒.partitionFunction kB (Temperature.ofβ kB (Real.toNNReal β))))
      (fun β : ℝ =>
        Real.log (∫ i, Real.exp (-β * 𝓒.energy i) ∂ 𝓒.μ)
          - (𝓒.dof : ℝ) * Real.log 𝓒.phaseSpaceunit)
      (Set.Ioi (0 : ℝ)) := by
  intro β hβ
  have hβpos : 0 < β := hβ
  have _inst : IsFiniteMeasure (𝓒.μBolt kB (Temperature.ofβ kB (Real.toNNReal β))) :=
    h_fin β hβpos
  simp only [log_partitionFunction, log_mathematicalPartitionFunction_eq, β_ofβ,
    Real.coe_toNNReal β hβpos.le]

/-- Derivative equality needed in `meanEnergy_eq_neg_deriv_log_Z_of_beta`.
Adds `h_fin` (finiteness of the Boltzmann measure for every β > 0). -/
lemma derivWithin_log_phys_eq_derivWithin_log_math
    (𝓒 : CanonicalEnsemble ι) (T : Temperature)
    (hT_pos : 0 < T.val) [NeZero 𝓒.μ]
    (h_fin :
        ∀ β > 0,
          IsFiniteMeasure (𝓒.μBolt kB (Temperature.ofβ kB (Real.toNNReal β)))) :
    derivWithin
      (fun β : ℝ => Real.log (𝓒.partitionFunction kB (ofβ kB (Real.toNNReal β))))
      (Set.Ioi 0) (T.β kB : ℝ)
    =
    derivWithin
      (fun β : ℝ => Real.log (∫ i, Real.exp (-β * 𝓒.energy i) ∂ 𝓒.μ))
      (Set.Ioi 0) (T.β kB : ℝ) := by
  have h_eq := log_phys_eq_log_math_sub_const_on_Ioi kB (𝓒 := 𝓒) (h_fin := h_fin)
  rw [derivWithin_congr h_eq (h_eq (beta_pos kB T hT_pos)), derivWithin_sub_const]

/-- The mean energy can also be expressed as the negative derivative of the logarithm of the
*physical* partition function with respect to β. This follows from the fact that the physical and
mathematical partition functions differ only by a constant factor, which vanishes upon
differentiation. -/
theorem meanEnergy_eq_neg_deriv_log_Z_of_beta
    (𝓒 : CanonicalEnsemble ι) (T : Temperature)
    (hT_pos : 0 < T.val) [IsFiniteMeasure (𝓒.μBolt kB T)] [NeZero 𝓒.μ]
    (h_fin :
        ∀ β > 0,
          IsFiniteMeasure (𝓒.μBolt kB (Temperature.ofβ kB (Real.toNNReal β))))
    (h_deriv :
        HasDerivWithinAt
          (fun β : ℝ => ∫ i, Real.exp (-β * 𝓒.energy i) ∂ 𝓒.μ)
          (- ∫ i, 𝓒.energy i * Real.exp (-(T.β kB : ℝ) * 𝓒.energy i) ∂𝓒.μ)
          (Set.Ioi 0) (T.β kB : ℝ)) :
    𝓒.meanEnergy kB T =
      - (derivWithin
          (fun β : ℝ => Real.log (𝓒.partitionFunction kB (ofβ kB (Real.toNNReal β))))
          (Set.Ioi 0) (T.β kB : ℝ)) := by
  rw [derivWithin_log_phys_eq_derivWithin_log_math kB (𝓒 := 𝓒) (T := T) hT_pos h_fin]
  exact 𝓒.meanEnergy_eq_neg_deriv_log_mathZ_of_beta kB T hT_pos h_deriv

end Ratios

open scoped Topology Filter

/-! ## Fluctuations: variance identity -/

/-- The identity Var(E) = ⟨E²⟩ - ⟨E⟩². -/
theorem energyVariance_eq_meanSquareEnergy_sub_meanEnergy_sq
    (𝓒 : CanonicalEnsemble ι) (T : Temperature) [IsProbabilityMeasure (𝓒.μProd kB T)]
    (hE_int : Integrable 𝓒.energy (𝓒.μProd kB T))
    (hE2_int : Integrable (fun i => (𝓒.energy i)^2) (𝓒.μProd kB T)) :
    𝓒.energyVariance kB T = 𝓒.meanSquareEnergy kB T - (𝓒.meanEnergy kB T)^2 := by
  unfold energyVariance meanSquareEnergy meanEnergy
  set U := ∫ i, 𝓒.energy i ∂𝓒.μProd kB T with hU
  have h_expand : (fun i => (𝓒.energy i - U)^2)
      = (fun i => (𝓒.energy i)^2 - 2 * U * 𝓒.energy i + U^2) := by
    funext i; ring
  have h_int_E_mul_const : Integrable (fun i => 2 * U * 𝓒.energy i) (𝓒.μProd kB T) :=
    hE_int.const_mul (2 * U)
  rw [h_expand]
  rw [integral_add (hE2_int.sub' h_int_E_mul_const) (integrable_const _)]
  rw [integral_sub hE2_int h_int_E_mul_const]
  rw [integral_const_mul, integral_const, ← hU, probReal_univ, smul_eq_mul]
  ring

/-! ## Heat capacity and parametric FDT -/

-- We define functions from ℝ to handle derivatives smoothly, using Real.toNNReal

/-- The mean energy as a function of the real-valued temperature t. -/
noncomputable def meanEnergyT (𝓒 : CanonicalEnsemble ι) (t : ℝ) : ℝ :=
  𝓒.meanEnergy kB (Temperature.ofNNReal (Real.toNNReal t))

/-- The mean energy as a function of the real-valued inverse temperature b. -/
noncomputable def meanEnergyBeta (𝓒 : CanonicalEnsemble ι) (b : ℝ) : ℝ :=
  𝓒.meanEnergy kB (Temperature.ofβ kB (Real.toNNReal b))

/-- The heat capacity (at constant volume) C_V = ∂U/∂T (as a derivWithin on T > 0). -/
noncomputable def heatCapacity (𝓒 : CanonicalEnsemble ι) (T : Temperature) : ℝ :=
  derivWithin (𝓒.meanEnergyT kB) (Set.Ioi 0) (T.val : ℝ)

/-- Relates C_V = dU/dT to dU/dβ. C_V = dU/dβ * (-1/(kB T²)). -/
lemma heatCapacity_eq_deriv_meanEnergyBeta
    (𝓒 : CanonicalEnsemble ι) (T : Temperature) (hT_pos : 0 < T.val)
    (hU_deriv :
      HasDerivWithinAt (𝓒.meanEnergyBeta kB)
        (derivWithin (𝓒.meanEnergyBeta kB) (Set.Ioi 0) (T.β kB : ℝ))
        (Set.Ioi 0) (T.β kB : ℝ)) :
    𝓒.heatCapacity kB T
      = (derivWithin (𝓒.meanEnergyBeta kB) (Set.Ioi 0) (T.β kB : ℝ))
        * (-1 / ((kB : ℝ) * (T.val : ℝ)^2)) := by
  have h_U_eq_comp :
      (𝓒.meanEnergyT kB) = fun t : ℝ => (𝓒.meanEnergyBeta kB) (betaFromReal kB t) := by
    funext t
    simp [meanEnergyT, meanEnergyBeta, betaFromReal]
  have h_UD : UniqueDiffWithinAt ℝ (Set.Ioi (0 : ℝ)) (T.val : ℝ) :=
    isOpen_Ioi.uniqueDiffWithinAt hT_pos
  unfold heatCapacity
  rw [h_U_eq_comp]
  exact (chain_rule_T_beta kB (F := 𝓒.meanEnergyBeta kB) T hT_pos hU_deriv).derivWithin h_UD

/-- Parametric FDT: C_V = Var(E)/(kB T²), assuming Var(E) = - dU/dβ. -/
theorem fluctuation_dissipation_energy_parametric
    (𝓒 : CanonicalEnsemble ι) (T : Temperature) (hT_pos : 0 < T.val)
    (h_Var_eq_neg_dUdβ :
      𝓒.energyVariance kB T = - derivWithin (𝓒.meanEnergyBeta kB) (Set.Ioi 0) (T.β kB : ℝ))
    (hU_deriv :
      DifferentiableWithinAt ℝ (𝓒.meanEnergyBeta kB) (Set.Ioi 0) (T.β kB : ℝ)) :
    𝓒.heatCapacity kB T = 𝓒.energyVariance kB T / ((kB : ℝ) * (T.val : ℝ)^2) := by
  rw [heatCapacity_eq_deriv_meanEnergyBeta kB 𝓒 T hT_pos hU_deriv.hasDerivWithinAt,
    h_Var_eq_neg_dUdβ]
  ring

end CanonicalEnsemble
