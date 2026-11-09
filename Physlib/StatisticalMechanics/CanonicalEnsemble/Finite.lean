/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina, Joseph Tooby-Smith
-/
module

public import Physlib.StatisticalMechanics.CanonicalEnsemble.Lemmas
/-!
# Finite Canonical Ensemble

This file specializes the general measure-theoretic framework of the canonical ensemble to systems
with a finite number of discrete microstates. This is a common and important case in statistical
mechanics to study models like spin systems (e.g., the Ising model) and other systems with a
discrete quantum state space.

## Main Definitions and Results

The specialization is achieved through the `IsFinite` class, which asserts that:
1. The type of microstates `ι` is a `Fintype`.
2. The measure `μ` on `ι` is the standard counting measure.
3. The number of degrees of freedom `dof` is 0.
4. The `phaseSpaceunit` is 1.

These assumptions correspond to systems where the state space is fundamentally discrete, and no
semi-classical approximation from a continuous phase space is needed. Consequently, the
dimensionless physical quantities are directly equivalent to their mathematical counterparts.

The main results proved in this file are:
- The abstract integral definitions for thermodynamic quantities (partition function, mean energy)
  are shown to reduce to the familiar finite sums found in introductory texts. For example, the
  partition function becomes `Z = ∑ᵢ exp(-β Eᵢ)`.
- The abstract `thermodynamicEntropy`, defined generally for measure-theoretic systems, is proven
  to be equal to the standard `shannonEntropy` (`S = -k_B ∑ᵢ pᵢ log pᵢ`). The semi-classical
  correction terms from the general theory vanish under the `IsFinite` assumptions.
- The **fluctuation-dissipation theorem** in the form `C_V = Var(E) / (k_B T²)`, which connects the
  heat capacity `C_V` to the variance of energy fluctuations, is formally proven for these systems.

This file also confirms that the `IsFinite` property is preserved under the composition of
systems (addition, `nsmul`, and `congr`).

## References

* L. D. Landau & E. M. Lifshitz, Statistical Physics, Part 1, §31. [ref: landau_statphys1]
* D. Tong, Lectures on Statistical Physics, §1.3. [ref: tong_statistical_physics]
-/

@[expose] public section

namespace CanonicalEnsemble

open Real Temperature MeasureTheory
open scoped Temperature CanonicalEnsemble

variable {ι : Type} [Fintype ι] [MeasurableSpace ι]
  [MeasurableSingletonClass ι] (kB : BoltzmannConstant) (𝓒 : CanonicalEnsemble ι)

variable {ι1 : Type} [Fintype ι1] [MeasurableSpace ι1]
  [MeasurableSingletonClass ι1] (𝓒1 : CanonicalEnsemble ι1)

/-- A finite `CanonicalEnsemble` is one whose microstates form a finite type
and whose measure is the counting measure. For such systems, the state space is
inherently discrete and dimensionless, so we require `dof = 0` and
`phaseSpaceUnit = 1`. -/
class IsFinite (𝓒 : CanonicalEnsemble ι) [Fintype ι] : Prop where
  μ_eq_count : 𝓒.μ = Measure.count
  dof_eq_zero : 𝓒.dof = 0
  phase_space_unit_eq_one : 𝓒.phaseSpaceunit = 1

instance [IsFinite 𝓒] [IsFinite 𝓒1] : IsFinite (𝓒 + 𝓒1) where
  μ_eq_count := by
    rw [μ_add]
    rw [IsFinite.μ_eq_count (𝓒:=𝓒), IsFinite.μ_eq_count (𝓒:=𝓒1)]
    refine Measure.prod_eq ?_
    intro s t hs ht
    rw [Measure.count_apply, Measure.count_apply, Measure.count_apply]
    rw [← ENat.toENNReal_mul]
    congr
    simp only [Set.encard_prod]
    · exact ht
    · exact hs
    · exact MeasurableSet.prod hs ht
  dof_eq_zero := by
    simp [IsFinite.dof_eq_zero (𝓒:=𝓒), IsFinite.dof_eq_zero (𝓒:=𝓒1)]
  phase_space_unit_eq_one := by
    simp [IsFinite.phase_space_unit_eq_one (𝓒:=𝓒)]

instance [IsFinite 𝓒] (e : ι1 ≃ᵐ ι) : IsFinite (congr 𝓒 e) where
  μ_eq_count := by
    simp [congr]
    rw [IsFinite.μ_eq_count (𝓒:=𝓒)]
    refine Measure.ext_iff.mpr ?_
    intro s hs
    rw [@MeasurableEquiv.map_apply]
    rw [Measure.count_apply, Measure.count_apply]
    simp only [ENat.toENNReal_inj]
    rw [@MeasurableEquiv.preimage_symm]
    rw [← Set.Finite.cast_ncard_eq, ← Set.Finite.cast_ncard_eq]
    congr 1
    change (e.toEmbedding '' s).ncard = _
    rw [Set.ncard_map]
    · exact Set.toFinite s
    · exact Set.toFinite (⇑e '' s)
    · exact hs
    · exact (MeasurableEquiv.measurableSet_preimage e.symm).mpr hs
  dof_eq_zero := by
    simp [IsFinite.dof_eq_zero (𝓒:=𝓒)]
  phase_space_unit_eq_one := by
    simp [IsFinite.phase_space_unit_eq_one (𝓒:=𝓒)]

instance [IsFinite 𝓒] (n : ℕ) : IsFinite (nsmul n 𝓒) where
  μ_eq_count := by
    induction n with
    | zero =>
      have : Subsingleton (Fin 0 → ι) := ⟨by intro f g; funext i; exact Fin.elim0 i⟩
      have h_cases : ∀ s : Set (Fin 0 → ι), s = ∅ ∨ s = Set.univ := fun s =>
        s.eq_empty_or_nonempty.imp_right fun ⟨y, hy⟩ =>
          Set.eq_univ_of_forall fun x => by rwa [Subsingleton.elim x y]
      refine Measure.ext (fun s _ => ?_)
      rcases h_cases s with hs | hs
      · subst hs
        simp [CanonicalEnsemble.nsmul]
      · subst hs
        simp [CanonicalEnsemble.nsmul, IsFinite.μ_eq_count (𝓒:=𝓒)]
    | succ n ih =>
      have : IsFinite (nsmul n 𝓒) := {
        μ_eq_count := ih
        dof_eq_zero := by
          simp [CanonicalEnsemble.dof_nsmul, IsFinite.dof_eq_zero (𝓒:=𝓒)]
        phase_space_unit_eq_one := by
          simp [CanonicalEnsemble.phase_space_unit_nsmul,
            IsFinite.phase_space_unit_eq_one (𝓒:=𝓒)]
      }
      let : Fintype (Fin (n+1) → ι) := inferInstance
      have h :
        ((𝓒 + nsmul n 𝓒).congr
            (MeasurableEquiv.piFinSuccAbove (fun _ => ι) 0)).μ
          = Measure.count := by rw [IsFinite.μ_eq_count]; aesop
      rw [← h]; rw [← @nsmul_succ]
  dof_eq_zero := by
    simp [CanonicalEnsemble.dof_nsmul, IsFinite.dof_eq_zero (𝓒:=𝓒)]
  phase_space_unit_eq_one := by
    simp [CanonicalEnsemble.phase_space_unit_nsmul,
      IsFinite.phase_space_unit_eq_one (𝓒:=𝓒)]

instance [IsFinite 𝓒] : IsFiniteMeasure (𝓒.μ) := by
  rw [IsFinite.μ_eq_count]
  infer_instance

/-- In the finite (counting) case a nonempty index type gives a nonzero measure. -/
instance [IsFinite 𝓒] [Nonempty ι] : NeZero 𝓒.μ := by
  refine ⟨?_⟩
  intro hμ
  obtain ⟨i₀⟩ := (inferInstance : Nonempty ι)
  have hone : 𝓒.μ {i₀} = 1 := by
    simp [IsFinite.μ_eq_count (𝓒:=𝓒)]
  simp_all only [Measure.coe_zero, Pi.zero_apply, zero_ne_one]

/-- The Shannon entropy of a finite canonical ensemble.
This is defined by the formula `S = -k_B ∑ pᵢ log pᵢ`. It is proven to be
equivalent to the `differentialEntropy` and the `thermodynamicEntropy` for systems
satisfying the `IsFinite` property. -/
noncomputable def shannonEntropy (T : Temperature) : ℝ :=
  -(kB : ℝ) * ∑ i, 𝓒.probability kB T i * log (𝓒.probability kB T i)

lemma mathematicalPartitionFunction_of_fintype [IsFinite 𝓒] (T : Temperature) :
    𝓒.mathematicalPartitionFunction kB T = ∑ i, exp (- β kB T * 𝓒.energy i) := by
  rw [mathematicalPartitionFunction_eq_integral, MeasureTheory.integral_fintype]
  simp [IsFinite.μ_eq_count]
  · rw [IsFinite.μ_eq_count]
    exact Integrable.of_finite

lemma partitionFunction_of_fintype [IsFinite 𝓒] (T : Temperature) :
    𝓒.partitionFunction kB T = ∑ i, exp (- T.β kB * 𝓒.energy i) := by
  simp [partitionFunction, mathematicalPartitionFunction_of_fintype,
        IsFinite.dof_eq_zero, IsFinite.phase_space_unit_eq_one]

@[simp]
lemma μBolt_of_fintype (T : Temperature) [IsFinite 𝓒] (i : ι) :
    (𝓒.μBolt kB T).real {i} = Real.exp (- β kB T * 𝓒.energy i) := by
  rw [μBolt]
  simp only [neg_mul]
  rw [@measureReal_def]
  simp [IsFinite.μ_eq_count]
  exact Real.exp_nonneg _

instance {T} [IsFinite 𝓒] : IsFiniteMeasure (𝓒.μBolt kB T) := by
  rw [μBolt]
  refine isFiniteMeasure_withDensity_ofReal ?_
  exact HasFiniteIntegral.of_finite

@[simp]
lemma μProd_of_fintype (T : Temperature) [IsFinite 𝓒] (i : ι) :
    (𝓒.μProd kB T).real {i} = 𝓒.probability kB T i := by
  rw [μProd]
  simp [probability]
  rw [inv_mul_eq_div]
  rfl

lemma meanEnergy_of_fintype [IsFinite 𝓒] (T : Temperature) :
    𝓒.meanEnergy kB T = ∑ i, 𝓒.energy i * 𝓒.probability kB T i := by
  simp [meanEnergy]
  rw [MeasureTheory.integral_fintype]
  simp [mul_comm]
  exact Integrable.of_finite

end CanonicalEnsemble
namespace CanonicalEnsemble
open Real Temperature MeasureTheory
open scoped Temperature CanonicalEnsemble

variable {ι : Type} [Fintype ι] [MeasurableSpace ι]
  (kB : BoltzmannConstant) (𝓒 : CanonicalEnsemble ι)

variable {ι1 : Type} [Fintype ι1] [MeasurableSpace ι1]
  (𝓒1 : CanonicalEnsemble ι1)

lemma entropy_of_fintype (T : Temperature) :
    𝓒.shannonEntropy kB T =
      - (kB : ℝ) * ∑ i, 𝓒.probability kB T i * log (𝓒.probability kB T i) := by
  simp [shannonEntropy]

lemma probability_le_one
    [MeasurableSingletonClass ι] [IsFinite 𝓒] [Nonempty ι] (T : Temperature) (i : ι) :
    𝓒.probability kB T i ≤ 1 := by
  have hZpos : 0 < 𝓒.mathematicalPartitionFunction kB T := by
    rw [mathematicalPartitionFunction_of_fintype]
    exact Finset.sum_pos (fun j _ => Real.exp_pos _) Finset.univ_nonempty
  rw [probability, div_le_one hZpos, mathematicalPartitionFunction_of_fintype]
  simpa [neg_mul] using Finset.single_le_sum
    (f := fun j : ι => Real.exp (- β kB T * 𝓒.energy j)) (fun j _ => Real.exp_nonneg _)
    (Finset.mem_univ i)

/-- Finite specialization: strict positivity of the mathematical partition function. -/
lemma mathematicalPartitionFunction_pos_finite
    [MeasurableSingletonClass ι] [IsFinite 𝓒] [Nonempty ι] (T : Temperature) :
    0 < 𝓒.mathematicalPartitionFunction kB T := by
  simpa using (CanonicalEnsemble.mathematicalPartitionFunction_pos kB (𝓒:=𝓒) T)

/-- Finite specialization: strict positivity of the (physical) partition function. -/
lemma partitionFunction_pos_finite
    [MeasurableSingletonClass ι] [IsFinite 𝓒] [Nonempty ι] (T : Temperature) :
    0 < 𝓒.partitionFunction kB T := by
  simpa [partitionFunction, IsFinite.dof_eq_zero (𝓒:=𝓒),
        IsFinite.phase_space_unit_eq_one (𝓒:=𝓒), pow_zero]
    using mathematicalPartitionFunction_pos_finite kB (𝓒:=𝓒) (T:=T)

/-- Finite specialization: non-negativity (indeed positivity) of probabilities. -/
lemma probability_nonneg_finite
    [MeasurableSingletonClass ι] [IsFinite 𝓒] [Nonempty ι] (T : Temperature) (i : ι) :
    0 ≤ 𝓒.probability kB T i := by
  unfold probability
  have hZpos := mathematicalPartitionFunction_pos_finite kB (𝓒:=𝓒) (T:=T)
  exact div_nonneg (Real.exp_nonneg _) hZpos.le

/-- The sum of probabilities over all microstates is 1. -/
lemma sum_probability_eq_one
    [MeasurableSingletonClass ι] [IsFinite 𝓒] [Nonempty ι] (T : Temperature) :
    ∑ i, 𝓒.probability kB T i = 1 := by
  have hZne : 𝓒.mathematicalPartitionFunction kB T ≠ 0 :=
    (mathematicalPartitionFunction_pos_finite kB 𝓒 T).ne'
  simp_rw [probability, ← Finset.sum_div, ← mathematicalPartitionFunction_of_fintype]
  exact div_self hZne

/-- The entropy of a finite canonical ensemble (Shannon entropy) is non-negative. -/
lemma entropy_nonneg [MeasurableSingletonClass ι] [IsFinite 𝓒] [Nonempty ι] (T : Temperature) :
    0 ≤ 𝓒.shannonEntropy kB T := by
  have hsum : ∑ i, 𝓒.probability kB T i * log (𝓒.probability kB T i) ≤ 0 :=
    Fintype.sum_nonpos fun i =>
      mul_nonpos_iff.2 <| Or.inl ⟨probability_nonneg_finite kB 𝓒 T i,
        Real.log_nonpos (probability_nonneg_finite kB 𝓒 T i) (probability_le_one kB 𝓒 T i)⟩
  rw [shannonEntropy, neg_mul, neg_nonneg]
  exact mul_nonpos_iff.2 <| Or.inl ⟨kB.val_pos.le, hsum⟩

lemma shannonEntropy_eq_differentialEntropy
    [MeasurableSingletonClass ι] [IsFinite 𝓒] (T : Temperature) :
    𝓒.shannonEntropy kB T = 𝓒.differentialEntropy kB T := by
  simp [shannonEntropy, differentialEntropy, integral_fintype, μProd_of_fintype]

/-- In the finite, nonempty case the thermodynamic and Shannon entropies coincide.
All semi-classical correction factors vanish (`dof = 0`, `phaseSpaceUnit = 1`),
so the absolute thermodynamic entropy reduces to the discrete Shannon form. -/
theorem thermodynamicEntropy_eq_shannonEntropy [MeasurableSingletonClass ι] [IsFinite 𝓒]
    (T : Temperature) :-- (hT : 0 < T.val) :
    𝓒.thermodynamicEntropy kB T = 𝓒.shannonEntropy kB T := by
  have h_thermo_eq_diff :
      𝓒.thermodynamicEntropy kB T = 𝓒.differentialEntropy kB T := by
    unfold CanonicalEnsemble.thermodynamicEntropy
      CanonicalEnsemble.differentialEntropy
    have h_log :
        (fun i => Real.log (𝓒.physicalProbability kB T i))
          = (fun i => Real.log (𝓒.probability kB T i)) := by
      funext i
      simp [CanonicalEnsemble.physicalProbability,
            IsFinite.dof_eq_zero (𝓒:=𝓒),
            IsFinite.phase_space_unit_eq_one (𝓒:=𝓒)]
    simp_all only [physicalProbability_def]
  have h_shannon :
      𝓒.shannonEntropy kB T = 𝓒.differentialEntropy kB T :=
    (shannonEntropy_eq_differentialEntropy kB (𝓒:=𝓒) T)
  calc
    𝓒.thermodynamicEntropy kB T
        = 𝓒.differentialEntropy kB T := h_thermo_eq_diff
    _ = 𝓒.shannonEntropy kB T := h_shannon.symm

open Real Temperature MeasureTheory
open scoped Temperature CanonicalEnsemble BigOperators ENNReal NNReal

/-! ## Fluctuations in Finite Systems -/

section FluctuationsFinite

lemma meanSquareEnergy_of_fintype [MeasurableSingletonClass ι] [IsFinite 𝓒] (T : Temperature) :
    𝓒.meanSquareEnergy kB T = ∑ i, (𝓒.energy i)^2 * 𝓒.probability kB T i := by
  simp [CanonicalEnsemble.meanSquareEnergy]
  rw [MeasureTheory.integral_fintype]
  simp [μProd_of_fintype, mul_comm]
  exact Integrable.of_finite

lemma energyVariance_of_fintype
    [MeasurableSingletonClass ι] [IsFinite 𝓒] [Nonempty ι] (T : Temperature) :
    𝓒.energyVariance kB T =
      (∑ i, (𝓒.energy i)^2 * 𝓒.probability kB T i) - (𝓒.meanEnergy kB T)^2 := by
  have hE_int := Integrable.of_finite (f := 𝓒.energy) (μ := 𝓒.μProd kB T)
  have hE2_int := Integrable.of_finite (f := fun i => (𝓒.energy i)^2) (μ := 𝓒.μProd kB T)
  rw [CanonicalEnsemble.energyVariance_eq_meanSquareEnergy_sub_meanEnergy_sq kB 𝓒 T hE_int hE2_int]
  rw [meanSquareEnergy_of_fintype]

/-! ## β-parameterization for finite systems -/

/-- The finite-sum partition function as a real function of the inverse temperature `b = β`,
defined by `Z(b) = ∑ i exp (-b * 𝓒.energy i)`. -/
noncomputable def mathematicalPartitionFunctionBetaReal (b : ℝ) : ℝ :=
  ∑ i, Real.exp (-b * 𝓒.energy i)

lemma mathematicalPartitionFunctionBetaReal_pos [Nonempty ι] (b : ℝ) :
    0 < 𝓒.mathematicalPartitionFunctionBetaReal b := by
  apply Finset.sum_pos
  · intro i _; exact Real.exp_pos _
  · exact Finset.univ_nonempty

/-- For inverse temperature `b = β`, the (real-valued) Boltzmann probability of microstate `i`,
given by `exp (-b * E i) / Z(b)` where `Z(b) = ∑ i exp (-b * E i)`. -/
noncomputable def probabilityBetaReal (b : ℝ) (i : ι) : ℝ :=
  Real.exp (-b * 𝓒.energy i) / 𝓒.mathematicalPartitionFunctionBetaReal b

/-- The mean energy as a function of inverse temperature `b = β` in the finite case,
defined by `U(b) = ∑ i, E i * p_b i` with `p_b i = exp (-b * E i) / Z(b)` and `Z(b) = ∑ i,
exp (-b * E i)`. -/
noncomputable def meanEnergyBetaReal (b : ℝ) : ℝ :=
  ∑ i, 𝓒.energy i * 𝓒.probabilityBetaReal b i

lemma meanEnergy_Beta_eq_finite [MeasurableSingletonClass ι] [IsFinite 𝓒] (b : ℝ) (hb : 0 < b) :
    𝓒.meanEnergyBeta kB b = 𝓒.meanEnergyBetaReal b := by
  let T := Temperature.ofβ kB (Real.toNNReal b)
  have hT_beta : (T.β kB : ℝ) = b := by
    simp [T, Real.toNNReal_of_nonneg hb.le]
  rw [meanEnergyBeta, meanEnergy_of_fintype kB 𝓒 T, meanEnergyBetaReal]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [CanonicalEnsemble.probability, probabilityBetaReal,
        mathematicalPartitionFunction_of_fintype, mathematicalPartitionFunctionBetaReal, hT_beta]

lemma differentiable_meanEnergyBetaReal
    [Nonempty ι] : Differentiable ℝ 𝓒.meanEnergyBetaReal := by
  unfold meanEnergyBetaReal probabilityBetaReal mathematicalPartitionFunctionBetaReal
  refine Differentiable.fun_sum (by
    intro i _
    refine (Differentiable.div ?_ ?_ ?_).const_mul (𝓒.energy i)
    · apply Differentiable.exp; simp
    · refine Differentiable.fun_sum ?_; intro j _; apply Differentiable.exp; simp
    · intro x; exact (mathematicalPartitionFunctionBetaReal_pos 𝓒 x).ne')

/-! Derivatives of Z and numerator -/

lemma differentiable_mathematicalPartitionFunctionBetaReal :
    Differentiable ℝ 𝓒.mathematicalPartitionFunctionBetaReal := by
  unfold mathematicalPartitionFunctionBetaReal
  refine Differentiable.fun_sum ?_; intro i _; simp

/-- The numerator in the finite-sum expression of the mean energy as a function of the
inverse temperature `b = β`,
namely `∑ i, E i * exp (-b * E i)` (so that `U(b) = meanEnergyNumerator b / Z(b)`). -/
noncomputable def meanEnergyNumerator (b : ℝ) : ℝ :=
  ∑ i, 𝓒.energy i * Real.exp (-b * 𝓒.energy i)

lemma differentiable_meanEnergyNumerator :
    Differentiable ℝ 𝓒.meanEnergyNumerator := by
  unfold meanEnergyNumerator
  refine Differentiable.fun_sum ?_; intro i _; apply Differentiable.const_mul; simp

lemma deriv_mathematicalPartitionFunctionBetaReal (b : ℝ) :
    deriv 𝓒.mathematicalPartitionFunctionBetaReal b = -𝓒.meanEnergyNumerator b := by
  unfold mathematicalPartitionFunctionBetaReal meanEnergyNumerator
  have hd : ∀ c : ℝ, HasDerivAt (fun x => Real.exp (-x * c)) (-c * Real.exp (-b * c)) b := by
    intro c
    have h : HasDerivAt (fun x => -x * c) (-c) b := by
      simpa using (hasDerivAt_id b).neg.mul_const c
    simpa [mul_comm] using h.exp
  have h_sum : HasDerivAt (fun x => ∑ i, Real.exp (-x * 𝓒.energy i))
      (∑ i, -𝓒.energy i * Real.exp (-b * 𝓒.energy i)) b :=
    HasDerivAt.fun_sum fun i _ => hd (𝓒.energy i)
  simpa [Finset.sum_neg_distrib] using h_sum.deriv

lemma deriv_meanEnergyNumerator (b : ℝ) :
    deriv 𝓒.meanEnergyNumerator b =
      -∑ i, (𝓒.energy i)^2 * Real.exp (-b * 𝓒.energy i) := by
  unfold meanEnergyNumerator
  have hd : ∀ c : ℝ, HasDerivAt (fun x => Real.exp (-x * c)) (-c * Real.exp (-b * c)) b := by
    intro c
    have h : HasDerivAt (fun x => -x * c) (-c) b := by
      simpa using (hasDerivAt_id b).neg.mul_const c
    simpa [mul_comm] using h.exp
  have h_sum : HasDerivAt (fun x => ∑ i, 𝓒.energy i * Real.exp (-x * 𝓒.energy i))
      (∑ i, -(𝓒.energy i)^2 * Real.exp (-b * 𝓒.energy i)) b := by
    refine HasDerivAt.fun_sum fun i _ => ?_
    simpa [sq, mul_comm, mul_left_comm, mul_assoc] using
      (hd (𝓒.energy i)).const_mul (𝓒.energy i)
  simpa [Finset.sum_neg_distrib, sq, mul_comm, mul_left_comm, mul_assoc] using h_sum.deriv

/-! Quotient rule: dU/db = U^2 - ⟨E^2⟩_β -/

variable [Nonempty ι]

lemma deriv_meanEnergyBetaReal (b : ℝ) :
    deriv 𝓒.meanEnergyBetaReal b =
    (𝓒.meanEnergyBetaReal b)^2 - ∑ i, (𝓒.energy i)^2 * 𝓒.probabilityBetaReal b i := by
  have hN_diff := (differentiable_meanEnergyNumerator 𝓒) b
  have hZ_diff := (differentiable_mathematicalPartitionFunctionBetaReal 𝓒) b
  have hZ_ne : 𝓒.mathematicalPartitionFunctionBetaReal b ≠ 0 :=
    (mathematicalPartitionFunctionBetaReal_pos 𝓒 b).ne'
  have hU : 𝓒.meanEnergyBetaReal
      = 𝓒.meanEnergyNumerator / 𝓒.mathematicalPartitionFunctionBetaReal := by
    funext x
    simp [meanEnergyBetaReal, probabilityBetaReal, meanEnergyNumerator,
          mathematicalPartitionFunctionBetaReal, Pi.div_apply, Finset.sum_div, mul_div_assoc]
  have hprob : ∑ i, (𝓒.energy i)^2 * 𝓒.probabilityBetaReal b i
      = (∑ i, (𝓒.energy i)^2 * Real.exp (-b * 𝓒.energy i))
          / 𝓒.mathematicalPartitionFunctionBetaReal b := by
    simp [probabilityBetaReal, Finset.sum_div, mul_div_assoc]
  rw [hprob, hU, deriv_div hN_diff hZ_diff hZ_ne, deriv_meanEnergyNumerator,
      deriv_mathematicalPartitionFunctionBetaReal, Pi.div_apply]
  set S2 := ∑ i, (𝓒.energy i) ^ 2 * Real.exp (-b * 𝓒.energy i)
  field_simp
  ring

/-- (∂U/∂β) = -Var(E) for finite systems. -/
lemma derivWithin_meanEnergy_Beta_eq_neg_variance
    [MeasurableSingletonClass ι][𝓒.IsFinite] (T : Temperature) (hT_pos : 0 < T.val) :
    derivWithin (𝓒.meanEnergyBeta kB) (Set.Ioi 0) (T.β kB : ℝ) = - 𝓒.energyVariance kB T := by
  let β₀ := (T.β kB : ℝ)
  have hβ₀_pos : 0 < β₀ := beta_pos kB T hT_pos
  have h_eq_on : Set.EqOn (𝓒.meanEnergyBeta kB) 𝓒.meanEnergyBetaReal (Set.Ioi 0) := by
    intro b hb; exact meanEnergy_Beta_eq_finite kB 𝓒 b hb
  rw [derivWithin_congr h_eq_on (h_eq_on hβ₀_pos)]
  have h_diff : DifferentiableAt ℝ 𝓒.meanEnergyBetaReal β₀ :=
    (differentiable_meanEnergyBetaReal 𝓒) β₀
  rw [h_diff.derivWithin (uniqueDiffOn_Ioi 0 β₀ hβ₀_pos)]
  rw [deriv_meanEnergyBetaReal 𝓒 β₀]
  have h_U_eq : 𝓒.meanEnergyBetaReal β₀ = 𝓒.meanEnergy kB T := by
    rw [← meanEnergy_Beta_eq_finite kB 𝓒 β₀ hβ₀_pos]
    simp [meanEnergyBeta]
    simp_all only [NNReal.coe_pos, toNNReal_coe, ofβ_β, β₀]
  have h_prob_eq (i : ι) : 𝓒.probabilityBetaReal β₀ i = 𝓒.probability kB T i := by
    unfold probabilityBetaReal CanonicalEnsemble.probability
    congr 1
    · unfold mathematicalPartitionFunctionBetaReal
      rw [mathematicalPartitionFunction_of_fintype]
  rw [h_U_eq]
  simp_rw [h_prob_eq]
  rw [energyVariance_of_fintype kB 𝓒 T]
  ring

/-- FDT for finite canonical ensembles: C_V = Var(E) / (k_B T²). -/
theorem fluctuation_dissipation_theorem_finite
    [MeasurableSingletonClass ι] [𝓒.IsFinite] (T : Temperature) (hT_pos : 0 < T.val) :
    𝓒.heatCapacity kB T = 𝓒.energyVariance kB T / ((kB : ℝ) * (T.val : ℝ)^2) := by
  have hβ₀_pos : 0 < (T.β kB : ℝ) := beta_pos kB T hT_pos
  let β₀ := (T.β kB : ℝ)
  have h_diff_U_beta : DifferentiableWithinAt ℝ (𝓒.meanEnergyBeta kB) (Set.Ioi 0) β₀ := by
    have h_eq_on : Set.EqOn (𝓒.meanEnergyBeta kB) 𝓒.meanEnergyBetaReal (Set.Ioi 0) := by
      intro b hb; exact meanEnergy_Beta_eq_finite kB 𝓒 b hb
    have h_diff' := (differentiable_meanEnergyBetaReal 𝓒) (T.β kB : ℝ)
    exact DifferentiableWithinAt.congr_of_eventuallyEq h_diff'.differentiableWithinAt
      (eventuallyEq_nhdsWithin_of_eqOn h_eq_on) (h_eq_on hβ₀_pos)
  have h_Var_eq_neg_dUdβ := derivWithin_meanEnergy_Beta_eq_neg_variance kB 𝓒 T hT_pos
  exact CanonicalEnsemble.fluctuation_dissipation_energy_parametric kB 𝓒 T hT_pos
    (by simp_all only [NNReal.coe_pos, neg_neg, β₀]) h_diff_U_beta

end FluctuationsFinite

end CanonicalEnsemble
