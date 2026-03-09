/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina, Joseph Tooby-Smith
-/
module

public import PhysLean.Thermodynamics.Temperature.Basic
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import PhysLean.Meta.Informal.SemiFormal
public import PhysLean.Meta.Linters.Sorry
public import Mathlib.Analysis.SpecialFunctions.Log.Summable
public import Mathlib.MeasureTheory.Integral.Prod
/-!
# Canonical Ensemble: Core Definitions

A *canonical ensemble* describes a system in thermal equilibrium with a heat bath at fixed
temperature `T`. This file gives a measure–theoretic, semi–classical formalization intended to
work uniformly for discrete (counting measure) and continuous (Lebesgue–type) models.

## 1. Semi–Classical Normalization

Classical phase–space integrals produce *dimensionful* quantities. To obtain dimensionless
thermodynamic objects (and an absolute entropy) we introduce:

* `phaseSpaceUnit : ℝ` (physically Planck's constant `h`);
* `dof : ℕ` the number of degrees of freedom.

The *physical* partition function is obtained from the *mathematical* one by dividing by
`phaseSpaceUnit ^ dof`. This yields the standard semi–classical correction preventing
ambiguities such as the Gibbs paradox.

## 2. Mathematical vs Physical Quantities

We keep both layers:

* Mathematical / raw:
  - `mathematicalPartitionFunction (T)` : ∫ exp(-β E) dμ
  - `probability` (density w.r.t. `μ`)
  - `differentialEntropy` (can be negative, unit–dependent)

* Physical / dimensionless:
  - `partitionFunction` : `Z = Z_math / h^dof`
  - `physicalProbability` : dimensionless density
  - `helmholtzFreeEnergy` : `F = -kB T log Z`
  - `thermodynamicEntropy` : absolute entropy `(U - F)/T = -kB ∫ ρ_phys log ρ_phys`

Each physical quantity is expressed explicitly in terms of its mathematical ancestor.

## 3. Core Structure

We assume `phaseSpaceUnit > 0` and `μ` σ–finite. No probability assumption is imposed:
normalization is recovered via the Boltzmann weighted measure.

## 4. Boltzmann & Probability Measures

* `μBolt T` : Boltzmann (unnormalized) measure `withDensity exp(-β E)`
* `μProd T` : normalized probability measure (rescaled `μBolt T`)
* `probability T i` : the density `exp(-β E(i)) / Z_math`
* `physicalProbability` : `probability * (phase_space_unit ^ dof)`

## 5. Energies & Entropies

* `meanEnergy` : expectation of energy under `μProd`.
* `differentialEntropy` : `-kB ∫ log(probability) dμProd`
* `thermodynamicEntropy` : `-kB ∫ log(physicalProbability) dμProd`
  (proved later to coincide with the textbook `(U - F)/T`).

A helper lemma supplies positivity of the partition function under mild assumptions and
non–negativity criteria for the entropy when `probability ≤ 1` (automatic in finite discrete
settings, not in general continuous ones).

## 6. Algebraic Operations

We construct composite ensembles:

* Addition `(𝓒₁ + 𝓒₂)` on product microstates: energies add, measures take product,
  degrees of freedom add, and (physically) the same `phaseSpaceUnit` is reused.
* Multiplicity `nsmul n 𝓒`: `n` distinguishable, non–interacting copies (product of `n` copies).
* Transport along measurable equivalences via `congr`.

These operations respect partition functions, free energies, and (under suitable hypotheses)
mean energies and integrability.

## 7. Notational & Implementation Notes

* We work over an arbitrary measurable type `ι`, allowing both finite and continuous models.
* `β` is accessed through the `Temperature` structure (`T.β`).
* Most positivity / finiteness conditions are hypotheses on lemmas instead of global axioms,
  enabling reuse in formal derivations of fluctuation and response identities.

## 8. References

* L. D. Landau & E. M. Lifshitz, *Statistical Physics, Part 1*.
* D. Tong, Cambridge Lecture Notes (sections on canonical ensemble).
  - https://www.damtp.cam.ac.uk/user/tong/statphys/one.pdf
  - https://www.damtp.cam.ac.uk/user/tong/statphys/two.pdf

## 9. Roadmap

Subsequent files (`Lemmas.lean`) prove:
* Relations among entropies and free energies.
* Fundamental identity `F = U - T S`.
* Derivative (response) formulas: `U = -∂_β log Z`.
-/

@[expose] public section

open MeasureTheory Real Temperature
open scoped Temperature

/-- A Canonical ensemble is described by a type `ι`, corresponding to the type of microstates,
and a map `ι → ℝ` which associates which each microstate an energy
and physical constants needed to define dimensionless thermodynamic quantities. -/
structure CanonicalEnsemble (ι : Type) [MeasurableSpace ι] : Type where
  /-- The energy of associated with a microstate of the canonical ensemble. -/
  energy : ι → ℝ
  /-- The number of degrees of freedom, used to make the partition function dimensionless.
  For a classical system of N particles in 3D, this is `3N`. For a system of N spins,
  this is typically `0` as the state space is already discrete. -/
  dof : ℕ
  /-- The unit of action used to make the phase space volume dimensionless.
  This constant is necessary to define an absolute (rather than relative) thermodynamic
  entropy. In the semi-classical approach, this unit is identified with Planck's constant `h`.
  For discrete systems with a counting measure, this unit should be set to `1`. -/
  phaseSpaceunit : ℝ := 1
  /-- Assumption that the phase space unit is positive. -/
  hPos : 0 < phaseSpaceunit := by positivity
  energy_measurable : Measurable energy
  /-- The measure on the indexing set of microstates. -/
  μ : MeasureTheory.Measure ι := by volume_tac
  [μ_sigmaFinite : SigmaFinite μ]

namespace CanonicalEnsemble
open Real Temperature

variable {ι ι1 : Type} [MeasurableSpace ι]
  [MeasurableSpace ι1] (𝓒 : CanonicalEnsemble ι) (𝓒1 : CanonicalEnsemble ι1)

instance : SigmaFinite 𝓒.μ := 𝓒.μ_sigmaFinite

@[ext]
lemma ext {𝓒 𝓒' : CanonicalEnsemble ι} (h_energy : 𝓒.energy = 𝓒'.energy)
    (h_dof : 𝓒.dof = 𝓒'.dof) (h_h : 𝓒.phaseSpaceunit = 𝓒'.phaseSpaceunit)
    (h_μ : 𝓒.μ = 𝓒'.μ) : 𝓒 = 𝓒' := by
  cases 𝓒; cases 𝓒'; simp_all

@[fun_prop]
lemma energy_measurable' : Measurable 𝓒.energy := 𝓒.energy_measurable

/-- The addition of two `CanonicalEnsemble`. The degrees of freedom are added.
Note: This is only physically meaningful if the two systems share the same `phase_space_unit`. -/
noncomputable instance {ι1 ι2 : Type} [MeasurableSpace ι1] [MeasurableSpace ι2] :
    HAdd (CanonicalEnsemble ι1) (CanonicalEnsemble ι2)
    (CanonicalEnsemble (ι1 × ι2)) where
  hAdd := fun 𝓒1 𝓒2 => {
    energy := fun (i : ι1 × ι2) => 𝓒1.energy i.1 + 𝓒2.energy i.2
    dof := 𝓒1.dof + 𝓒2.dof
    phaseSpaceunit := 𝓒1.phaseSpaceunit
    hPos := 𝓒1.hPos
    μ := 𝓒1.μ.prod 𝓒2.μ
    energy_measurable := by fun_prop
  }

/-- The canonical ensemble with no microstates. -/
def empty : CanonicalEnsemble Empty where
  energy := isEmptyElim
  dof := 0
  μ := 0
  energy_measurable := by fun_prop

/-- Given a measurable equivalence `e : ι1 ≃ᵐ ι`, this is the corresponding canonical ensemble
on `ι1`. The physical properties (`dof`, `phase_space_unit`) are unchanged. -/
noncomputable def congr (e : ι1 ≃ᵐ ι) : CanonicalEnsemble ι1 where
  energy := fun i => 𝓒.energy (e i)
  dof := 𝓒.dof
  phaseSpaceunit := 𝓒.phaseSpaceunit
  hPos := 𝓒.hPos
  μ := 𝓒.μ.map e.symm
  energy_measurable := by
    apply Measurable.comp
    · fun_prop
    · exact MeasurableEquiv.measurable e
  μ_sigmaFinite := MeasurableEquiv.sigmaFinite_map e.symm

@[simp]
lemma congr_energy_comp_symmm (e : ι1 ≃ᵐ ι) :
    (𝓒.congr e).energy ∘ e.symm = 𝓒.energy := by
  funext i
  simp [congr]

/-- Scalar multiplication of `CanonicalEnsemble`, defined such that
`nsmul n 𝓒` represents `n` non-interacting, distinguishable copies of the ensemble `𝓒`. -/
noncomputable def nsmul (n : ℕ) (𝓒 : CanonicalEnsemble ι) : CanonicalEnsemble (Fin n → ι) where
  energy := fun f => ∑ i, 𝓒.energy (f i)
  dof := n * 𝓒.dof
  phaseSpaceunit := 𝓒.phaseSpaceunit
  hPos := 𝓒.hPos
  μ := MeasureTheory.Measure.pi fun _ => 𝓒.μ
  energy_measurable := by fun_prop

set_option linter.unusedVariables false in
/-- The microstates of a canonical ensemble. -/
@[nolint unusedArguments]
abbrev microstates (𝓒 : CanonicalEnsemble ι) : Type := ι

/-! ## Properties of physical parameters -/

@[simp]
lemma dof_add (𝓒1 : CanonicalEnsemble ι) (𝓒2 : CanonicalEnsemble ι1) :
    (𝓒1 + 𝓒2).dof = 𝓒1.dof + 𝓒2.dof := rfl

@[simp]
lemma phase_space_unit_add (𝓒1 : CanonicalEnsemble ι) (𝓒2 : CanonicalEnsemble ι1) :
    (𝓒1 + 𝓒2).phaseSpaceunit = 𝓒1.phaseSpaceunit := rfl

@[simp]
lemma dof_nsmul (n : ℕ) : (nsmul n 𝓒).dof = n * 𝓒.dof := rfl

@[simp]
lemma phase_space_unit_nsmul (n : ℕ) :
    (nsmul n 𝓒).phaseSpaceunit = 𝓒.phaseSpaceunit := rfl

@[simp]
lemma dof_congr (e : ι1 ≃ᵐ ι) :
    (𝓒.congr e).dof = 𝓒.dof := rfl

@[simp]
lemma phase_space_unit_congr (e : ι1 ≃ᵐ ι) :
    (𝓒.congr e).phaseSpaceunit = 𝓒.phaseSpaceunit := rfl

/-! ## The measure -/

lemma μ_add : (𝓒 + 𝓒1).μ = 𝓒.μ.prod 𝓒1.μ := rfl

lemma μ_nsmul (n : ℕ) : (nsmul n 𝓒).μ = MeasureTheory.Measure.pi fun _ => 𝓒.μ := rfl

lemma μ_nsmul_zero_eq : (nsmul 0 𝓒).μ = Measure.pi (fun _ => 0) := by
  simp [nsmul]
  congr
  funext x
  exact Fin.elim0 x

/-!

## The energy of the microstates

-/

@[simp]
lemma energy_add_apply (i : microstates (𝓒 + 𝓒1)) :
    (𝓒 + 𝓒1).energy i = 𝓒.energy i.1 + 𝓒1.energy i.2 := rfl

@[simp]
lemma energy_nsmul_apply (n : ℕ) (f : Fin n → microstates 𝓒) :
    (nsmul n 𝓒).energy f = ∑ i, 𝓒.energy (f i) := rfl

@[simp]
lemma energy_congr_apply (e : ι1 ≃ᵐ ι) (i : ι1) :
    (𝓒.congr e).energy i = 𝓒.energy (e i) := rfl

/-! ## Induction for nsmul -/

open MeasureTheory

lemma nsmul_succ (n : ℕ) [SigmaFinite 𝓒.μ] : nsmul n.succ 𝓒 = (𝓒 + nsmul n 𝓒).congr
    (MeasurableEquiv.piFinSuccAbove (fun _ => ι) 0) := by
  ext1
  · ext x
    simp only [Nat.succ_eq_add_one, energy_nsmul_apply]
    exact Fin.sum_univ_succAbove (fun i => 𝓒.energy (x i)) 0
  · simp [Nat.succ_eq_add_one, Nat.succ_mul, dof_nsmul, add_comm]
  · simp
  · refine Eq.symm (MeasureTheory.MeasurePreserving.map_eq ?_)
    refine MeasurePreserving.symm _ ?_
    exact MeasureTheory.measurePreserving_piFinSuccAbove (n := n) (fun _ => 𝓒.μ) 0

/-!

## Non zero nature of the measure

-/

instance [NeZero 𝓒.μ] [NeZero 𝓒1.μ] : NeZero (𝓒 + 𝓒1).μ := by
  simp [μ_add]
  refine { out := ?_ }
  rw [← @Measure.measure_univ_pos]
  have h1 : (𝓒.μ.prod (𝓒1.μ)) Set.univ =
      (𝓒.μ Set.univ) * (𝓒1.μ Set.univ) := by
    rw [← @Measure.prod_prod]
    simp
  rw [h1]
  exact NeZero.pos (𝓒.μ Set.univ * 𝓒1.μ Set.univ)

instance μ_neZero_congr [NeZero 𝓒.μ] (e : ι1 ≃ᵐ ι) :
    NeZero (𝓒.congr e).μ := by
  refine { out := ?_ }
  rw [← @Measure.measure_univ_pos]
  simp only [Measure.measure_univ_pos, ne_eq]
  refine (Measure.map_ne_zero_iff ?_).mpr ?_
  · fun_prop
  · exact Ne.symm (NeZero.ne' _)

instance [NeZero 𝓒.μ] (n : ℕ) : NeZero (nsmul n 𝓒).μ := by
  induction n with
  | zero =>
    rw [μ_nsmul_zero_eq]
    rw [@neZero_iff]
    simp only [ne_eq]
    refine Measure.measure_univ_ne_zero.mp ?_
    simp
  | succ n ih =>
    rw [nsmul_succ]
    infer_instance

/-!

## The Boltzmann measure

-/

/-- The Boltzmann measure on the space of microstates. -/
noncomputable def μBolt (T : Temperature) : MeasureTheory.Measure ι :=
  𝓒.μ.withDensity (fun i => ENNReal.ofReal (exp (- T.β * 𝓒.energy i)))

instance (T : Temperature) : SigmaFinite (𝓒.μBolt T) :=
  inferInstanceAs
    (SigmaFinite (𝓒.μ.withDensity (fun i => ENNReal.ofReal (exp (- β T * 𝓒.energy i)))))

@[simp]
lemma μBolt_add (T : Temperature) :
    (𝓒 + 𝓒1).μBolt T = (𝓒.μBolt T).prod (𝓒1.μBolt T) := by
  simp_rw [μBolt, μ_add]
  rw [MeasureTheory.prod_withDensity]
  congr
  funext i
  rw [← ENNReal.ofReal_mul, ← Real.exp_add]
  simp only [energy_add_apply, neg_mul]
  ring_nf
  · exact exp_nonneg _
  · fun_prop
  · fun_prop

lemma μBolt_congr (e : ι1 ≃ᵐ ι) (T : Temperature) : (𝓒.congr e).μBolt T =
    (𝓒.μBolt T).map e.symm := by
  simp [congr, μBolt]
  refine Measure.ext_of_lintegral _ fun φ hφ ↦ ?_
  rw [lintegral_withDensity_eq_lintegral_mul₀]
  rw [lintegral_map, lintegral_map, lintegral_withDensity_eq_lintegral_mul₀]
  congr
  funext i
  simp only [Pi.mul_apply, MeasurableEquiv.apply_symm_apply]
  repeat fun_prop

lemma μBolt_nsmul [SigmaFinite 𝓒.μ] (n : ℕ) (T : Temperature) :
    (nsmul n 𝓒).μBolt T = MeasureTheory.Measure.pi fun _ => (𝓒.μBolt T) := by
  induction n with
  | zero =>
    simp [nsmul, μBolt]
    congr
    funext x
    exact Fin.elim0 x
  | succ n ih =>
    rw [nsmul_succ, μBolt_congr]
    rw [μBolt_add]
    refine MeasurePreserving.map_eq ?_
    refine MeasurePreserving.symm _ ?_
    rw [ih]
    exact MeasureTheory.measurePreserving_piFinSuccAbove (fun _ => 𝓒.μBolt T) 0

lemma μBolt_ne_zero_of_μ_ne_zero (T : Temperature) (h : 𝓒.μ ≠ 0) :
    𝓒.μBolt T ≠ 0 := by
  simp [μBolt] at ⊢ h
  rw [Measure.ext_iff'] at ⊢ h
  simp only [Measure.coe_zero, Pi.zero_apply]
  have hs : {x | ENNReal.ofReal (rexp (-(↑T.β * 𝓒.energy x))) ≠ 0} = Set.univ := by
    ext i
    simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le, Set.mem_setOf_eq, Set.mem_univ, iff_true]
    exact exp_pos _
  conv =>
    enter [1, s]
    rw [MeasureTheory.withDensity_apply_eq_zero' (by fun_prop), hs]
    simp
  simpa using h

instance (T : Temperature) [NeZero 𝓒.μ] : NeZero (𝓒.μBolt T) := by
  refine { out := ?_ }
  apply μBolt_ne_zero_of_μ_ne_zero
  exact Ne.symm (NeZero.ne' 𝓒.μ)

instance (T : Temperature) [IsFiniteMeasure (𝓒.μBolt T)] [IsFiniteMeasure (𝓒1.μBolt T)] :
    IsFiniteMeasure ((𝓒 + 𝓒1).μBolt T) := by
  simp only [μBolt_add]; infer_instance

instance (T : Temperature) [IsFiniteMeasure (𝓒.μBolt T)] (n : ℕ) :
    IsFiniteMeasure ((nsmul n 𝓒).μBolt T) := by
  simp [μBolt_nsmul]; infer_instance

/-!

## The Mathematical Partition Function

-/

/-- The mathematical partition function, defined as the integral of the Boltzmann factor.
This quantity may have physical dimensions. See `CanonicalEnsemble.partitionFunction` for
the dimensionless physical version. -/
noncomputable def mathematicalPartitionFunction (T : Temperature) : ℝ := (𝓒.μBolt T).real Set.univ

lemma mathematicalPartitionFunction_eq_integral (T : Temperature) :
    mathematicalPartitionFunction 𝓒 T = ∫ i, exp (- T.β * 𝓒.energy i) ∂𝓒.μ := by
  trans ∫ i, 1 ∂𝓒.μBolt T
  · simp only [integral_const, smul_eq_mul, mul_one]
    rfl
  rw [μBolt]
  erw [integral_withDensity_eq_integral_smul]
  congr
  funext x
  simp [HSMul.hSMul, SMul.smul]
  · exact exp_nonneg _
  · fun_prop

lemma mathematicalPartitionFunction_add {T : Temperature} :
    (𝓒 + 𝓒1).mathematicalPartitionFunction T =
    𝓒.mathematicalPartitionFunction T * 𝓒1.mathematicalPartitionFunction T := by
  simp_rw [mathematicalPartitionFunction, μBolt_add]
  rw [← measureReal_prod_prod, Set.univ_prod_univ]

@[simp]
lemma mathematicalPartitionFunction_congr (e : ι1 ≃ᵐ ι) (T : Temperature) :
    (𝓒.congr e).mathematicalPartitionFunction T = 𝓒.mathematicalPartitionFunction T := by
  rw [mathematicalPartitionFunction_eq_integral, mathematicalPartitionFunction_eq_integral]
  simp only [congr]
  rw [integral_map_equiv]
  simp

/-- The `mathematicalPartitionFunction_nsmul` function of `n` copies of a canonical ensemble. -/
lemma mathematicalPartitionFunction_nsmul (n : ℕ) (T : Temperature) :
    (nsmul n 𝓒).mathematicalPartitionFunction T = (𝓒.mathematicalPartitionFunction T) ^ n := by
  simp_rw [mathematicalPartitionFunction, μBolt_nsmul, measureReal_def, Measure.pi_univ]
  simp

lemma mathematicalPartitionFunction_nonneg (T : Temperature) :
    0 ≤ 𝓒.mathematicalPartitionFunction T := by
  rw [mathematicalPartitionFunction]; exact measureReal_nonneg

lemma mathematicalPartitionFunction_eq_zero_iff (T : Temperature) [IsFiniteMeasure (𝓒.μBolt T)] :
    mathematicalPartitionFunction 𝓒 T = 0 ↔ 𝓒.μ = 0 := by
  simp [mathematicalPartitionFunction]
  rw [measureReal_def]
  rw [ENNReal.toReal_eq_zero_iff]
  simp only [measure_ne_top, or_false]
  rw [μBolt]
  rw [MeasureTheory.withDensity_apply_eq_zero']
  simp only [neg_mul, ne_eq, ENNReal.ofReal_eq_zero, not_le, Set.inter_univ]
  let s : Set ι := {x | 0 < rexp (-(T.β * 𝓒.energy x))}
  have h : s = Set.univ := by
    ext i
    simp [s]
    exact exp_pos (-(T.β * 𝓒.energy i))
  change 𝓒.μ s = 0 ↔ 𝓒.μ = 0
  rw [h]
  simp only [Measure.measure_univ_eq_zero]
  fun_prop

open NNReal

lemma mathematicalPartitionFunction_comp_ofβ_apply (β : ℝ≥0) :
    𝓒.mathematicalPartitionFunction (ofβ β) =
    (𝓒.μ.withDensity (fun i => ENNReal.ofReal (exp (- β * 𝓒.energy i)))).real Set.univ := by
  simp only [mathematicalPartitionFunction, μBolt, β_ofβ, neg_mul]

/-- The partition function is strictly positive provided the underlying
measure is non-zero and the Boltzmann measure is finite. -/
lemma mathematicalPartitionFunction_pos (T : Temperature)
    [IsFiniteMeasure (𝓒.μBolt T)] [NeZero 𝓒.μ] :
    0 < 𝓒.mathematicalPartitionFunction T := by
  simp [mathematicalPartitionFunction]

open NNReal Constants

/-! ## The probability density -/

/-- The probability density function of the canonical ensemble.
Note: In the general measure-theoretic case, this is a density with respect to the
underlying measure `𝓒.μ` and is not necessarily less than or equal to 1. In the
case of a finite ensemble with the counting measure, this value corresponds to the
probability of the microstate. -/
noncomputable def probability (T : Temperature) (i : ι) : ℝ :=
  (exp (- T.β * 𝓒.energy i)) / 𝓒.mathematicalPartitionFunction T

/-! ## The probability measure -/

lemma probability_add {T : Temperature} (i : ι × ι1) :
    (𝓒 + 𝓒1).probability T i = 𝓒.probability T i.1 * 𝓒1.probability T i.2 := by
  simp [probability, mathematicalPartitionFunction_add, mul_add, Real.exp_add]
  ring

@[simp]
lemma probability_congr (e : ι1 ≃ᵐ ι) (T : Temperature) (i : ι1) :
    (𝓒.congr e).probability T i = 𝓒.probability T (e i) := by
  simp [probability]

lemma probability_nsmul (n : ℕ) (T : Temperature) (f : Fin n → ι) :
    (nsmul n 𝓒).probability T f = ∏ i, 𝓒.probability T (f i) := by
  induction n with
  | zero =>
    simp [probability, mathematicalPartitionFunction_nsmul]
  | succ n ih =>
    rw [nsmul_succ]
    rw [probability_congr]
    rw [probability_add]
    simp only [MeasurableEquiv.piFinSuccAbove_apply, Fin.insertNthEquiv_zero,
      Fin.consEquiv_symm_apply]
    rw [ih]
    exact Eq.symm (Fin.prod_univ_succAbove (fun i => 𝓒.probability T (f i)) 0)

/-- The probability measure associated with the Boltzmann distribution of a
  canonical ensemble. -/
noncomputable def μProd (T : Temperature) : MeasureTheory.Measure ι :=
  (𝓒.μBolt T Set.univ)⁻¹ • 𝓒.μBolt T

instance (T : Temperature) : SigmaFinite (𝓒.μProd T) :=
  inferInstanceAs (SigmaFinite ((𝓒.μBolt T Set.univ)⁻¹ • 𝓒.μBolt T))

instance (T : Temperature) [IsFiniteMeasure (𝓒.μBolt T)]
  [NeZero 𝓒.μ] : IsProbabilityMeasure (𝓒.μProd T) := inferInstanceAs <|
  IsProbabilityMeasure ((𝓒.μBolt T Set.univ)⁻¹ • 𝓒.μBolt T)

instance {T} : IsFiniteMeasure (𝓒.μProd T) := by
  rw [μProd]
  infer_instance

lemma μProd_add {T : Temperature} [IsFiniteMeasure (𝓒.μBolt T)]
    [IsFiniteMeasure (𝓒1.μBolt T)] : (𝓒 + 𝓒1).μProd T = (𝓒.μProd T).prod (𝓒1.μProd T) := by
  rw [μProd, μProd, μProd, μBolt_add]
  rw [MeasureTheory.Measure.prod_smul_left, MeasureTheory.Measure.prod_smul_right]
  rw [smul_smul]
  congr
  trans ((𝓒.μBolt T) Set.univ * (𝓒1.μBolt T) Set.univ)⁻¹
  swap
  · by_cases h : (𝓒.μBolt T) Set.univ = 0
    · simp [h]
    by_cases h1 : (𝓒1.μBolt T) Set.univ = 0
    · simp [h1]
    rw [ENNReal.mul_inv]
    · simp
    · simp
  · rw [← @Measure.prod_prod]
    simp

lemma μProd_congr (e : ι1 ≃ᵐ ι) (T : Temperature) :
    (𝓒.congr e).μProd T = (𝓒.μProd T).map e.symm := by
  simp [μProd, μBolt_congr]
  congr 2
  rw [MeasurableEquiv.map_apply]
  simp

lemma μProd_nsmul (n : ℕ) (T : Temperature) [IsFiniteMeasure (𝓒.μBolt T)] :
    (nsmul n 𝓒).μProd T = MeasureTheory.Measure.pi fun _ => 𝓒.μProd T := by
  induction n with
  | zero =>
    simp [nsmul, μProd, μBolt]
    congr
    funext x
    exact Fin.elim0 x
  | succ n ih =>
    rw [nsmul_succ]
    rw [μProd_congr]
    rw [μProd_add]
    refine MeasurePreserving.map_eq ?_
    refine MeasurePreserving.symm _ ?_
    rw [ih]
    exact MeasureTheory.measurePreserving_piFinSuccAbove (fun _ => 𝓒.μProd T) 0

/-!

## Integrability of energy

-/

@[fun_prop]
lemma integrable_energy_add (T : Temperature) [IsFiniteMeasure (𝓒.μBolt T)]
    [IsFiniteMeasure (𝓒1.μBolt T)]
    (h : Integrable 𝓒.energy (𝓒.μProd T)) (h1 : Integrable 𝓒1.energy (𝓒1.μProd T)) :
    Integrable (𝓒 + 𝓒1).energy ((𝓒 + 𝓒1).μProd T) := by
  rw [μProd_add]
  refine Integrable.add'' ?_ ?_
  · have h1 : (fun (i : ι × ι1) => 𝓒.energy i.1)
      = fun (i : ι × ι1) => 𝓒.energy i.1 * (fun (i : ι1) => 1) i.2 := by
      funext i
      simp
    rw [h1]
    apply Integrable.mul_prod (f := 𝓒.energy) (g := (fun (i : ι1) => 1))
    · fun_prop
    · fun_prop
  · have h1 : (fun (i : ι × ι1) => 𝓒1.energy i.2)
      = fun (i : ι × ι1) => (fun (i : ι) => 1) i.1 * 𝓒1.energy i.2 := by
      funext i
      simp
    rw [h1]
    apply Integrable.mul_prod (f := (fun (i : ι) => 1)) (g := 𝓒1.energy)
    · fun_prop
    · fun_prop

@[fun_prop]
lemma integrable_energy_congr (T : Temperature) (e : ι1 ≃ᵐ ι)
    (h : Integrable 𝓒.energy (𝓒.μProd T)) :
    Integrable (𝓒.congr e).energy ((𝓒.congr e).μProd T) := by
  simp [μProd_congr]
  refine (integrable_map_equiv e.symm (𝓒.congr e).energy).mpr ?_
  simp only [congr_energy_comp_symmm]
  exact h

@[fun_prop]
lemma integrable_energy_nsmul (n : ℕ) (T : Temperature)
    [IsFiniteMeasure (𝓒.μBolt T)]
    (h : Integrable 𝓒.energy (𝓒.μProd T)) :
    Integrable (nsmul n 𝓒).energy ((nsmul n 𝓒).μProd T) := by
  induction n with
  | zero =>
    simp [nsmul]
  | succ n ih =>
    rw [nsmul_succ]
    apply integrable_energy_congr
    apply integrable_energy_add
    · exact h
    · exact ih

/-!

## The mean energy

-/

/-- The mean energy of the canonical ensemble at temperature `T`. -/
noncomputable def meanEnergy (T : Temperature) : ℝ := ∫ i, 𝓒.energy i ∂𝓒.μProd T

/-- The mean square energy ⟨E²⟩ of the canonical ensemble at temperature T. -/
noncomputable def meanSquareEnergy (T : Temperature) : ℝ :=
  ∫ i, (𝓒.energy i)^2 ∂ 𝓒.μProd T

/-- Energy variance at temperature `T`. -/
noncomputable def energyVariance (T : Temperature) : ℝ :=
  ∫ i, (𝓒.energy i - 𝓒.meanEnergy T)^2 ∂ 𝓒.μProd T

lemma meanEnergy_add {T : Temperature}
    [IsFiniteMeasure (𝓒1.μBolt T)] [IsFiniteMeasure (𝓒.μBolt T)]
    [NeZero 𝓒.μ] [NeZero 𝓒1.μ]
    (h1 : Integrable 𝓒.energy (𝓒.μProd T))
    (h2 : Integrable 𝓒1.energy (𝓒1.μProd T)) :
    (𝓒 + 𝓒1).meanEnergy T = 𝓒.meanEnergy T + 𝓒1.meanEnergy T := by
  rw [meanEnergy]
  simp only [energy_add_apply]
  rw [μProd_add]
  rw [MeasureTheory.integral_prod]
  simp only
  conv_lhs =>
    enter [2, x]
    rw [integral_add (integrable_const _) h2]
    rw [integral_const]
    simp
  rw [integral_add h1 (integrable_const _)]
  rw [integral_const]
  simp
  rfl
  · simpa [μProd_add] using integrable_energy_add 𝓒 𝓒1 T h1 h2

lemma meanEnergy_congr (e : ι1 ≃ᵐ ι) (T : Temperature) :
    (𝓒.congr e).meanEnergy T = 𝓒.meanEnergy T := by
  simp [meanEnergy, μProd_congr]
  refine MeasurePreserving.integral_comp' ?_ 𝓒.energy
  refine { measurable := ?_, map_eq := ?_ }
  · exact MeasurableEquiv.measurable e
  · exact MeasurableEquiv.map_map_symm e

lemma meanEnergy_nsmul (n : ℕ) (T : Temperature)
    [IsFiniteMeasure (𝓒.μBolt T)] [NeZero 𝓒.μ]
    (h1 : Integrable 𝓒.energy (𝓒.μProd T)) :
    (nsmul n 𝓒).meanEnergy T = n * 𝓒.meanEnergy T := by
  induction n with
  | zero =>
    simp [nsmul, meanEnergy]
  | succ n ih =>
    rw [nsmul_succ, meanEnergy_congr, meanEnergy_add, ih]
    simp only [Nat.cast_add, Nat.cast_one]
    ring
    · exact h1
    · exact integrable_energy_nsmul 𝓒 n T h1

/-!

## The differential entropy

-/

/-- The (differential) entropy of the canonical ensemble. In the continuous case, this quantity
is not absolute but depends on the choice of units for the measure. It can be negative.
See `thermodynamicEntropy` for the absolute physical quantity. -/
noncomputable def differentialEntropy (T : Temperature) : ℝ :=
  - kB * ∫ i, log (probability 𝓒 T i) ∂𝓒.μProd T

/-- Probabilities are non-negative, assuming a positive partition function. -/
lemma probability_nonneg
    (T : Temperature) [IsFiniteMeasure (𝓒.μBolt T)] [NeZero 𝓒.μ] (i : ι) :
    0 ≤ 𝓒.probability T i := by
  have hpos := mathematicalPartitionFunction_pos (𝓒:=𝓒) (T:=T)
  simp [CanonicalEnsemble.probability, div_nonneg, Real.exp_nonneg, hpos.le]

/-- Probabilities are strictly positive. -/
lemma probability_pos
    (T : Temperature) [IsFiniteMeasure (𝓒.μBolt T)] [NeZero 𝓒.μ] (i : ι) :
    0 < 𝓒.probability T i := by
  have hZpos := mathematicalPartitionFunction_pos (𝓒:=𝓒) (T:=T)
  simp [probability, Real.exp_pos, hZpos]

/-- General entropy non-negativity under a pointwise upper bound `probability ≤ 1`.
This assumption holds automatically in the finite/counting case (since sums bound each term),
but can fail in general (continuous) settings; hence we separate it as a hypothesis.
Finite case: see `CanonicalEnsemble.entropy_nonneg` in `Finite`. -/
lemma differentialEntropy_nonneg_of_prob_le_one
    (T : Temperature) [IsFiniteMeasure (𝓒.μBolt T)] [NeZero 𝓒.μ]
    (hInt : Integrable (fun i => Real.log (𝓒.probability T i)) (𝓒.μProd T))
    (hP_le_one : ∀ i, 𝓒.probability T i ≤ 1) :
    0 ≤ 𝓒.differentialEntropy T := by
  have hPoint :
      (fun i => Real.log (𝓒.probability T i)) ≤ᵐ[𝓒.μProd T] fun _ => 0 := by
    refine Filter.Eventually.of_forall ?_
    intro i
    have hpos := probability_pos (𝓒:=𝓒) (T:=T) i
    have hle := hP_le_one i
    have hle' : 𝓒.probability T i ≤ Real.exp 0 := by
      simpa [Real.exp_zero] using hle
    exact (log_le_iff_le_exp hpos).mpr hle'
  have hInt0 : Integrable (fun _ : ι => (0 : ℝ)) (𝓒.μProd T) := integrable_const _
  have hIntLe : (∫ i, Real.log (𝓒.probability T i) ∂𝓒.μProd T)
      ≤ (∫ _i, (0 : ℝ) ∂𝓒.μProd T) :=
    integral_mono_ae hInt hInt0 hPoint
  have hent :
      𝓒.differentialEntropy T
        = - kB * (∫ i, Real.log (𝓒.probability T i) ∂𝓒.μProd T) := rfl
  have hkB : 0 ≤ kB := kB_nonneg
  have hIle0 : (∫ i, Real.log (𝓒.probability T i) ∂𝓒.μProd T) ≤ 0 := by
    simpa [integral_const] using hIntLe
  have hProd :
      0 ≤ - kB * (∫ i, Real.log (𝓒.probability T i) ∂𝓒.μProd T) :=
    mul_nonneg_of_nonpos_of_nonpos (neg_nonpos.mpr hkB) hIle0
  simpa [hent] using hProd

/-!

## Thermodynamic Quantities

These are the dimensionless physical quantities derived from the mathematical definitions
by incorporating the phase space volume `𝓒.phaseSpaceUnit ^ 𝓒.dof`.
-/

open Constants

/-- The dimensionless thermodynamic partition function, `Z = Z_math / h^dof`. -/
noncomputable def partitionFunction (T : Temperature) : ℝ :=
  𝓒.mathematicalPartitionFunction T / (𝓒.phaseSpaceunit ^ 𝓒.dof)

@[simp]
lemma partitionFunction_def (𝓒 : CanonicalEnsemble ι) (T : Temperature) :
    𝓒.partitionFunction T =
      𝓒.mathematicalPartitionFunction T / (𝓒.phaseSpaceunit ^ 𝓒.dof) := rfl

lemma partitionFunction_pos
    (𝓒 : CanonicalEnsemble ι) (T : Temperature)
    [IsFiniteMeasure (𝓒.μBolt T)] [NeZero 𝓒.μ] :
    0 < 𝓒.partitionFunction T := by
  have hZ := 𝓒.mathematicalPartitionFunction_pos T
  have hden : 0 < 𝓒.phaseSpaceunit ^ 𝓒.dof := pow_pos 𝓒.hPos _
  simp [partitionFunction, hZ, hden]

lemma partitionFunction_congr
    (𝓒 : CanonicalEnsemble ι) (e : ι1 ≃ᵐ ι) (T : Temperature) :
    (𝓒.congr e).partitionFunction T = 𝓒.partitionFunction T := by
  simp [partitionFunction]

lemma partitionFunction_add
    (𝓒 : CanonicalEnsemble ι) (𝓒1 : CanonicalEnsemble ι1)
    (T : Temperature)
    (h : 𝓒.phaseSpaceunit = 𝓒1.phaseSpaceunit) :
    (𝓒 + 𝓒1).partitionFunction T
      = 𝓒.partitionFunction T * 𝓒1.partitionFunction T := by
  simp [partitionFunction, mathematicalPartitionFunction_add, h]
  ring_nf

lemma partitionFunction_nsmul
    (𝓒 : CanonicalEnsemble ι) (n : ℕ) (T : Temperature) :
    (nsmul n 𝓒).partitionFunction T
      = (𝓒.partitionFunction T) ^ n := by
  simp [partitionFunction, mathematicalPartitionFunction_nsmul,
        dof_nsmul, phase_space_unit_nsmul, pow_mul]
  ring_nf

lemma partitionFunction_dof_zero
    (𝓒 : CanonicalEnsemble ι) (T : Temperature) (h : 𝓒.dof = 0) :
    𝓒.partitionFunction T = 𝓒.mathematicalPartitionFunction T := by
  simp [partitionFunction, h]

lemma partitionFunction_phase_space_unit_one
    (𝓒 : CanonicalEnsemble ι) (T : Temperature) (h : 𝓒.phaseSpaceunit = 1) :
    𝓒.partitionFunction T = 𝓒.mathematicalPartitionFunction T := by
  simp [partitionFunction, h]

lemma log_partitionFunction
    (𝓒 : CanonicalEnsemble ι) (T : Temperature)
    [IsFiniteMeasure (𝓒.μBolt T)] [NeZero 𝓒.μ] :
    Real.log (𝓒.partitionFunction T)
      = Real.log (𝓒.mathematicalPartitionFunction T)
        - (𝓒.dof : ℝ) * Real.log 𝓒.phaseSpaceunit := by
  have hZ := 𝓒.mathematicalPartitionFunction_pos T
  have hden : 0 < 𝓒.phaseSpaceunit ^ 𝓒.dof := pow_pos 𝓒.hPos _
  have hlogpow :
      Real.log (𝓒.phaseSpaceunit ^ 𝓒.dof)
        = (𝓒.dof : ℝ) * Real.log 𝓒.phaseSpaceunit := by
    simp
  simp [partitionFunction, Real.log_div hZ.ne' hden.ne', hlogpow,
        sub_eq_add_neg]

/-- A rewriting form convenient under a coercion to a temperature obtained from an inverse
temperature. -/
lemma log_partitionFunction_ofβ
    (𝓒 : CanonicalEnsemble ι) (β : ℝ≥0)
    [IsFiniteMeasure (𝓒.μBolt (ofβ β))] [NeZero 𝓒.μ] :
    Real.log (𝓒.partitionFunction (ofβ β))
      = Real.log (𝓒.mathematicalPartitionFunction (ofβ β))
        - (𝓒.dof : ℝ) * Real.log 𝓒.phaseSpaceunit :=
  log_partitionFunction (𝓒:=𝓒) (T:=ofβ β)

/-- The logarithm of the mathematical partition function as an integral. -/
lemma log_mathematicalPartitionFunction_eq
    (𝓒 : CanonicalEnsemble ι) (T : Temperature) :
    Real.log (𝓒.mathematicalPartitionFunction T)
      = Real.log (∫ i, Real.exp (- T.β * 𝓒.energy i) ∂ 𝓒.μ) := by
  simp [mathematicalPartitionFunction_eq_integral]

/-- The Helmholtz free energy, `F = -k_B T log(Z)`. This is the central
quantity from which other thermodynamic properties are derived. -/
noncomputable def helmholtzFreeEnergy (T : Temperature) : ℝ :=
  - kB * T.val * Real.log (𝓒.partitionFunction T)

@[simp]
lemma helmholtzFreeEnergy_def
    (𝓒 : CanonicalEnsemble ι) (T : Temperature) :
    𝓒.helmholtzFreeEnergy T = - kB * T.val * Real.log (𝓒.partitionFunction T) := rfl

lemma helmholtzFreeEnergy_congr
    (𝓒 : CanonicalEnsemble ι) (e : ι1 ≃ᵐ ι) (T : Temperature) :
    (𝓒.congr e).helmholtzFreeEnergy T = 𝓒.helmholtzFreeEnergy T := by
  simp [helmholtzFreeEnergy]

lemma helmholtzFreeEnergy_dof_zero
    (𝓒 : CanonicalEnsemble ι) (T : Temperature) (h : 𝓒.dof = 0) :
    𝓒.helmholtzFreeEnergy T
      = -kB * T.val * Real.log (𝓒.mathematicalPartitionFunction T) := by
  simp [helmholtzFreeEnergy, partitionFunction, h]

lemma helmholtzFreeEnergy_phase_space_unit_one
    (𝓒 : CanonicalEnsemble ι) (T : Temperature) (h : 𝓒.phaseSpaceunit = 1) :
    𝓒.helmholtzFreeEnergy T
      = -kB * T.val * Real.log (𝓒.mathematicalPartitionFunction T) := by
  simp [helmholtzFreeEnergy, partitionFunction, h]

lemma helmholtzFreeEnergy_add
    (𝓒 : CanonicalEnsemble ι) (𝓒1 : CanonicalEnsemble ι1) (T : Temperature)
    [IsFiniteMeasure (𝓒.μBolt T)] [IsFiniteMeasure (𝓒1.μBolt T)]
    [NeZero 𝓒.μ] [NeZero 𝓒1.μ]
    (h : 𝓒.phaseSpaceunit = 𝓒1.phaseSpaceunit) :
    (𝓒 + 𝓒1).helmholtzFreeEnergy T
      = 𝓒.helmholtzFreeEnergy T + 𝓒1.helmholtzFreeEnergy T := by
  have hPF := partitionFunction_add (𝓒:=𝓒) (𝓒1:=𝓒1) (T:=T) h
  have hpf₁ : 0 < 𝓒.partitionFunction T := partitionFunction_pos (𝓒:=𝓒) (T:=T)
  have hpf₂ : 0 < 𝓒1.partitionFunction T := partitionFunction_pos (𝓒:=𝓒1) (T:=T)
  calc
    (𝓒 + 𝓒1).helmholtzFreeEnergy T
        = -kB * T.val * Real.log ((𝓒 + 𝓒1).partitionFunction T) := rfl
    _ = -kB * T.val * Real.log (𝓒.partitionFunction T * 𝓒1.partitionFunction T) := by
          rw [hPF]
    _ = -kB * T.val *
          (Real.log (𝓒.partitionFunction T) + Real.log (𝓒1.partitionFunction T)) := by
          rw [Real.log_mul hpf₁.ne' hpf₂.ne']
    _ = (-kB * T.val) * Real.log (𝓒.partitionFunction T)
        + (-kB * T.val) * Real.log (𝓒1.partitionFunction T) := by
          ring
    _ = 𝓒.helmholtzFreeEnergy T + 𝓒1.helmholtzFreeEnergy T := by
          simp [helmholtzFreeEnergy, mul_comm, mul_assoc]

lemma helmholtzFreeEnergy_nsmul
    (𝓒 : CanonicalEnsemble ι) (n : ℕ) (T : Temperature) :
    (nsmul n 𝓒).helmholtzFreeEnergy T
      = n * 𝓒.helmholtzFreeEnergy T := by
  have hPF := partitionFunction_nsmul (𝓒:=𝓒) (n:=n) (T:=T)
  have hlog :
      Real.log ((nsmul n 𝓒).partitionFunction T)
        = (n : ℝ) * Real.log (𝓒.partitionFunction T) := by
    rw [hPF]
    simp
  calc
    (nsmul n 𝓒).helmholtzFreeEnergy T
        = -kB * T.val * Real.log ((nsmul n 𝓒).partitionFunction T) := rfl
    _ = -kB * T.val * ((n : ℝ) * Real.log (𝓒.partitionFunction T)) := by
          rw [hlog]
    _ = (n : ℝ) * (-kB * T.val * Real.log (𝓒.partitionFunction T)) := by
          ring
    _ = n * 𝓒.helmholtzFreeEnergy T := by
          simp [helmholtzFreeEnergy, mul_comm, mul_left_comm, mul_assoc]

/-- The dimensionless physical probability density. This is is the probability density w.r.t. the
measure, obtained by dividing the phase space measure by the fundamental unit `h^dof`, making the
probability density `ρ_phys = ρ_math * h^dof` dimensionless. -/
noncomputable def physicalProbability (T : Temperature) (i : ι) : ℝ :=
  𝓒.probability T i * (𝓒.phaseSpaceunit ^ 𝓒.dof)

@[simp]
lemma physicalProbability_def (T : Temperature) (i : ι) :
    𝓒.physicalProbability T i
      = 𝓒.probability T i * (𝓒.phaseSpaceunit ^ 𝓒.dof) := rfl

lemma physicalProbability_measurable (T : Temperature) :
    Measurable (𝓒.physicalProbability T) := by
  let c : ℝ := (𝓒.phaseSpaceunit ^ 𝓒.dof) / 𝓒.mathematicalPartitionFunction T
  have h_energy_meas : Measurable fun i => 𝓒.energy i := 𝓒.energy_measurable
  have h_mul_meas : Measurable fun i => (-(T.β : ℝ)) * 𝓒.energy i := by
    simpa [mul_comm] using h_energy_meas.const_mul (-(T.β : ℝ))
  have h_exp_meas : Measurable fun i => Real.exp (-(T.β : ℝ) * 𝓒.energy i) :=
    (continuous_exp.measurable.comp h_mul_meas)
  have h_fun_meas : Measurable fun i => c * Real.exp (-(T.β : ℝ) * 𝓒.energy i) := by
    simpa [mul_comm] using (h_exp_meas.const_mul c)
  have h_eq :
      (fun i => 𝓒.physicalProbability T i)
        = fun i => c * Real.exp (-(T.β : ℝ) * 𝓒.energy i) := by
    funext i
    simp [physicalProbability, probability, c, div_eq_mul_inv,
          mul_comm, mul_assoc]
  simpa [h_eq] using h_fun_meas

lemma physicalProbability_nonneg
    (T : Temperature) [IsFiniteMeasure (𝓒.μBolt T)] [NeZero 𝓒.μ] (i : ι) :
    0 ≤ 𝓒.physicalProbability T i := by
  have hp := 𝓒.probability_nonneg (T:=T) i
  exact mul_nonneg hp (by exact pow_nonneg (le_of_lt 𝓒.hPos) _)

lemma physicalProbability_pos
    (T : Temperature) [IsFiniteMeasure (𝓒.μBolt T)] [NeZero 𝓒.μ] (i : ι) :
    0 < 𝓒.physicalProbability T i := by
  have hp := 𝓒.probability_pos (T:=T) i
  exact mul_pos hp (pow_pos 𝓒.hPos _)

lemma log_physicalProbability
    (T : Temperature) [IsFiniteMeasure (𝓒.μBolt T)] [NeZero 𝓒.μ] (i : ι) :
    Real.log (𝓒.physicalProbability T i)
      = Real.log (𝓒.probability T i) + (𝓒.dof : ℝ) * Real.log 𝓒.phaseSpaceunit := by
  have hppos := 𝓒.probability_pos (T:=T) i
  have hpowpos : 0 < 𝓒.phaseSpaceunit ^ 𝓒.dof := pow_pos 𝓒.hPos _
  simp [physicalProbability, Real.log_mul hppos.ne' hpowpos.ne', Real.log_pow]

lemma integral_probability
    (𝓒 : CanonicalEnsemble ι) (T : Temperature)
    [IsFiniteMeasure (𝓒.μBolt T)] [NeZero 𝓒.μ] :
    (∫ i, 𝓒.probability T i ∂ 𝓒.μ) = 1 := by
  classical
  have hZ :
      𝓒.mathematicalPartitionFunction T
        = ∫ i, Real.exp (- T.β * 𝓒.energy i) ∂ 𝓒.μ :=
    mathematicalPartitionFunction_eq_integral (𝓒:=𝓒) (T:=T)
  have hZpos : 0 < 𝓒.mathematicalPartitionFunction T :=
    𝓒.mathematicalPartitionFunction_pos T
  have h_int :
      (∫ i, 𝓒.probability T i ∂ 𝓒.μ)
        = (𝓒.mathematicalPartitionFunction T)⁻¹ *
          (∫ i, Real.exp (- T.β * 𝓒.energy i) ∂ 𝓒.μ) := by
    simp [probability, div_eq_mul_inv, integral_const_mul,
          mul_comm]
  calc
    (∫ i, 𝓒.probability T i ∂ 𝓒.μ)
        = (𝓒.mathematicalPartitionFunction T)⁻¹ *
          (∫ i, Real.exp (- T.β * 𝓒.energy i) ∂ 𝓒.μ) := h_int
    _ = (𝓒.mathematicalPartitionFunction T)⁻¹ *
          𝓒.mathematicalPartitionFunction T := by simp [hZ]
    _ = 1 := by simp [hZpos.ne']

/-- Normalization of the dimensionless physical probability density over the base measure. -/
lemma integral_physicalProbability_base
    (𝓒 : CanonicalEnsemble ι) (T : Temperature)
    [IsFiniteMeasure (𝓒.μBolt T)] [NeZero 𝓒.μ] :
    (∫ i, 𝓒.physicalProbability T i ∂ 𝓒.μ)
      = 𝓒.phaseSpaceunit ^ 𝓒.dof := by
  classical
  have hnorm := integral_probability (𝓒:=𝓒) (T:=T)
  calc
    (∫ i, 𝓒.physicalProbability T i ∂ 𝓒.μ)
        = (∫ i, 𝓒.probability T i * (𝓒.phaseSpaceunit ^ 𝓒.dof) ∂ 𝓒.μ) := by
              simp [physicalProbability]
    _ = (∫ i, 𝓒.probability T i ∂ 𝓒.μ) * (𝓒.phaseSpaceunit ^ 𝓒.dof) := by
              simp [integral_mul_const, mul_comm]
    _ = 1 * (𝓒.phaseSpaceunit ^ 𝓒.dof) := by simp [hnorm]
    _ = 𝓒.phaseSpaceunit ^ 𝓒.dof := by ring

lemma physicalProbability_dof_zero
    (T : Temperature) (h : 𝓒.dof = 0) (i : ι) :
    𝓒.physicalProbability T i = 𝓒.probability T i := by
  simp [physicalProbability, h]

lemma physicalProbability_phase_space_unit_one
    (T : Temperature) (h : 𝓒.phaseSpaceunit = 1) (i : ι) :
    𝓒.physicalProbability T i = 𝓒.probability T i := by
  simp [physicalProbability, h]

lemma physicalProbability_congr (e : ι1 ≃ᵐ ι) (T : Temperature) (i : ι1) :
    (𝓒.congr e).physicalProbability T i
      = 𝓒.physicalProbability T (e i) := by
  simp [physicalProbability, probability]

lemma physicalProbability_add
    {ι1} [MeasurableSpace ι1]
    (𝓒1 : CanonicalEnsemble ι1) (T : Temperature) (i : ι × ι1)
    (h : 𝓒.phaseSpaceunit = 𝓒1.phaseSpaceunit) :
    (𝓒 + 𝓒1).physicalProbability T i
      = 𝓒.physicalProbability T i.1 * 𝓒1.physicalProbability T i.2 := by
  simp [physicalProbability, probability_add, phase_space_unit_add, dof_add, h, pow_add]
  ring

/-- The absolute thermodynamic entropy, defined from its statistical mechanical foundation as
the Gibbs-Shannon entropy of the dimensionless physical probability distribution.
This corresponds to Landau & Lifshitz, Statistical Physics, §7, Eq. 7.12. -/
noncomputable def thermodynamicEntropy (T : Temperature) : ℝ :=
  -kB * ∫ i, Real.log (𝓒.physicalProbability T i) ∂(𝓒.μProd T)

@[simp]
lemma thermodynamicEntropy_def (T : Temperature) :
    𝓒.thermodynamicEntropy T = -kB * ∫ i, Real.log (𝓒.physicalProbability T i) ∂ 𝓒.μProd T := rfl

end CanonicalEnsemble
