/-
Copyright (c) 2025 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
-/
module

public import Physlib.StatisticalMechanics.MicroCanonicalEnsemble.ThermoQuantities
public import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
public import Physlib.Meta.Implementations
/-!

## Ideal gas as a Micro Canonical Ensemble

In this module we give the
-/
@[expose] public section

noncomputable section

other_implementation
  "https://github.com/ATOMSLab/LeanChemicalTheories/blob/020d0f78cfd0abd55947a3c940dfa4cc873e714d/src/thermodynamics/basic.lean#L127"
  "This provides another implementation of the ideal gas law."

--! Specializing to an ideal gas of distinguishable particles.

/-- The Hamiltonian for an ideal gas: particles live in a cube of volume V^(1/3), and each
  contributes an energy p^2/2. The per-particle mass is normalized to 1. -/
def IdealGas : NVEHamiltonian where
  --The dimension of the manifold is 6 times the number of particles: three for position, three for
  --momentum.
  dim := fun (n,_) ↦ Fin n × (Fin 3 ⊕ Fin 3)
  --The energy is ∞ if any positions are outside the cube, otherwise it's the sum of the momenta
  --squared over 2.
  H := fun {d} config ↦
    let (n,V) := d
    let R := V^(1/3:ℝ) / 2 --half-sidelength of a cubical box
    if ∀ (i : Fin n) (ax : Fin 3), |config (i,.inl ax)| <= R then
      ∑ (i : Fin n) (ax : Fin 3), config (i,.inr ax)^2 / (2 : ℝ)
    else
      ⊤
  measurable_H := by
    rintro ⟨n, V⟩
    dsimp
    refine Measurable.ite ?_ ?_ measurable_const
    · simp_rw [Set.ofPred_forall]
      exact MeasurableSet.iInter fun i => MeasurableSet.iInter fun ax =>
        measurableSet_le (by fun_prop) measurable_const
    · simp_rw [← WithTop.coe_sum]
      exact WithTop.isOpenEmbedding_coe.measurableEmbedding.measurable.comp (by fun_prop)

namespace IdealGas
open MicroHamiltonian
open NVEHamiltonian

variable (n : ℕ) {V β T : ℝ}

open MeasureTheory in
/-- The partition function Z for an ideal gas. -/
lemma partitionZ_eq (hV : 0 < V) (hβ : 0 < β) :
    IdealGas.partitionZ (n,V) β = V ^ n * (2 * Real.pi / β) ^ (3 * n / 2 : ℝ) := by
  rw [partitionZ, IdealGas]
  simp only [Finset.univ_product_univ, one_div, ite_eq_right_iff, WithTop.sum_eq_top,
    Finset.mem_univ, WithTop.coe_ne_top, and_false, exists_false, imp_false, not_forall, not_le,
    neg_mul]
  have h₀ : ∀ (config:Fin n × (Fin 3 ⊕ Fin 3) → ℝ) proof,
      ((if ∀ (i : Fin n) (ax : Fin 3), |config (i, Sum.inl ax)| ≤ V ^ (3 : ℝ)⁻¹ / 2 then
                  ∑ x : Fin n × Fin 3, config (x.1, Sum.inr x.2) ^ 2 / (2 :ℝ)
                else ⊤) : WithTop ℝ).untop proof =
                ∑ x : Fin n × Fin 3, config (x.1, Sum.inr x.2) ^ 2 / (2 :ℝ) := by
    intro config proof
    rw [WithTop.untop_eq_iff]
    split_ifs with h
    · simp
    · simp [h] at proof
  simp only [h₀, dite_eq_ite]; clear h₀
  let eq_pm : MeasurableEquiv ((Fin n × Fin 3 → ℝ) ×
      (Fin n × Fin 3 → ℝ)) (Fin n × (Fin 3 ⊕ Fin 3) → ℝ) :=
    let e1 := (MeasurableEquiv.sumPiEquivProdPi
      (α := fun (_ : (Fin n × Fin 3) ⊕ (Fin n × Fin 3)) ↦ ℝ))
    let e2 := (MeasurableEquiv.piCongrLeft _
      (MeasurableEquiv.prodSumDistrib (Fin n) (Fin 3) (Fin 3))).symm
    e1.symm.trans e2
  have h_preserve : MeasurePreserving eq_pm := by
    unfold eq_pm
    -- fun_prop --this *should* be a fun_prop!
    rw [MeasurableEquiv.coe_trans]
    apply MeasureTheory.MeasurePreserving.comp (μb := by volume_tac)
    · apply MeasurePreserving.symm
      apply MeasureTheory.volume_measurePreserving_piCongrLeft
    · apply MeasurePreserving.symm
      apply measurePreserving_sumPiEquivProdPi
  rw [← MeasurePreserving.integral_comp h_preserve eq_pm.measurableEmbedding]; clear h_preserve
  rw [show volume = Measure.prod volume volume from rfl]
  simp_rw [show ∀ (x y i p_i), eq_pm (x, y) (i, Sum.inl p_i) = x (i, p_i) from fun _ _ _ _ => rfl,
    show ∀ (x y i m_i), eq_pm (x, y) (i, Sum.inr m_i) = y (i, m_i) from fun _ _ _ _ => rfl]
  have h_measurable_box : Measurable fun (a : (Fin n × Fin 3 → ℝ))
      => ∃ x_1 x_2, V ^ (3⁻¹:ℝ) / 2 < |a (x_1, x_2)| := by
    refine Measurable.exists fun i => Measurable.exists fun j => ?_
    exact measurable_const.lt (by fun_prop)
  have h_measurability : Measurable fun x : (Fin n × Fin 3 → ℝ) × (Fin n × Fin 3 → ℝ) =>
      if ∃ x_1 x_2, V ^ (3⁻¹:ℝ) / 2 < |x.1 (x_1, x_2)| then 0
      else Real.exp (-(β * ∑ x_1 : Fin n × Fin 3, x.2 (x_1.1, x_1.2) ^ 2 / 2)) := by
    refine Measurable.ite (measurableSet_setOfPred.mpr ?_) (by fun_prop) (by fun_prop)
    exact h_measurable_box.comp measurable_fst
  rw [MeasureTheory.integral_eq_lintegral_of_nonneg_ae]
  rotate_left
  · exact Filter.Eventually.of_forall fun _ => by positivity
  · fun_prop
  rw [MeasureTheory.lintegral_prod]; swap
  · exact (Measurable.comp (g := ENNReal.ofReal)
      ENNReal.measurable_ofReal h_measurability).aemeasurable
  conv =>
    enter [1, 1, 2, x, 2, y]
    rw [← ite_not _ _ (0:ℝ), ← boole_mul _ (Real.exp _)]
    rw [ENNReal.ofReal_mul (by split_ifs <;> positivity)]
  dsimp
  conv =>
    enter [1, 1, 2, x]
    simp only [not_exists, not_lt, Prod.mk.eta]
    rw [MeasureTheory.lintegral_const_mul' _ _ (ENNReal.ofReal_ne_top)]
  rw [MeasureTheory.lintegral_mul_const, ENNReal.toReal_mul]
  rw [← MeasureTheory.integral_eq_lintegral_of_nonneg_ae]
  rw [← MeasureTheory.integral_eq_lintegral_of_nonneg_ae]
  rotate_left
  · exact Filter.Eventually.of_forall fun _ => by positivity
  · exact Measurable.aestronglyMeasurable (by fun_prop)
  · exact Filter.Eventually.of_forall fun _ => by positivity
  · refine (Measurable.ite ?_ measurable_const measurable_const).aestronglyMeasurable
    simp_rw [Set.ofPred_forall]
    exact MeasurableSet.iInter fun i => MeasurableSet.iInter fun j =>
      measurableSet_le (by fun_prop) measurable_const
  · refine (Measurable.ite ?_ measurable_const measurable_const).ennreal_ofReal
    simp_rw [Set.ofPred_forall]
    exact MeasurableSet.iInter fun i => MeasurableSet.iInter fun j =>
      measurableSet_le (by fun_prop) measurable_const
  congr 1
  · have h_integrand_prod : ∀ (a : Fin n × Fin 3 → ℝ),
        (if ∀ (x : Fin n) (x_1 : Fin 3), |a (x, x_1)| ≤ V ^ (3⁻¹ : ℝ) / 2 then 1 else 0) =
        (∏ xy, if |a xy| ≤ V ^ (3⁻¹ : ℝ) / 2 then 1 else 0 : ℝ) := by
      intro a
      simp_rw [← Prod.forall (p := fun xy ↦ |a xy| ≤ V ^ (3⁻¹ : ℝ) / 2)]
      exact Fintype.prod_boole.symm
    simp_rw [h_integrand_prod]
    convert! ← MeasureTheory.integral_fintype_prod_eq_prod (ι := Fin n × Fin 3) (𝕜 := ℝ)
      (f := fun _ r ↦ if |r| ≤ V ^ (3⁻¹ : ℝ) / 2 then 1 else 0)
    swap
    · infer_instance
    have h_integral_1d :
        (∫ (x : ℝ), if |x| ≤ V ^ (3⁻¹ : ℝ) / 2 then 1 else 0) = V ^ (3⁻¹ : ℝ) := by
      have h_indicator := integral_indicator (f := fun _ ↦ (1:ℝ)) (μ := by volume_tac)
        (measurableSet_Icc (a := -(V ^ (3⁻¹ : ℝ) / 2)) (b := (V ^ (3⁻¹ : ℝ) / 2)))
      simp_rw [Set.indicator] at h_indicator
      simp_rw [abs_le, ← Set.mem_Icc, h_indicator]
      simp only [integral_const, MeasurableSet.univ, measureReal_restrict_apply, Set.univ_inter,
        Real.volume_real_Icc, sub_neg_eq_add, add_halves, smul_eq_mul, mul_one, sup_eq_left,
        ge_iff_le]
      positivity
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin,
      h_integral_1d, ← Real.rpow_mul_natCast hV.le]
    field_simp
    simp
  · have h_gaussian :=
      GaussianFourier.integral_rexp_neg_mul_sq_norm
        (V := PiLp 2 (fun (_ : Fin n × Fin 3) ↦ ℝ)) (half_pos hβ)
    apply (Eq.trans ?_ h_gaussian).trans ?_
    · have := EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin n × Fin 3)
      rw [← this.integral_comp (MeasurableEquiv.measurableEmbedding _)]
      congr! 3 with x
      simp_rw [div_eq_inv_mul, ← Finset.mul_sum, ← mul_assoc, neg_mul, mul_comm,
        PiLp.norm_sq_eq_of_L2]
      congr! 3
      simp only [Real.norm_eq_abs, sq_abs]
      congr
    · field_simp
      congr
      simp only [finrank_euclideanSpace, Fintype.card_prod, Fintype.card_fin, Nat.cast_mul,
        Nat.cast_ofNat]
      ring_nf

/-- The Helmholtz Free Energy A for an ideal gas. -/
lemma helmholtzA_eq (hV : 0 < V) (hT : 0 < T) : IdealGas.helmholtzA (n,V) T =
    -n * T * (Real.log V + (3/2) * Real.log (2 * Real.pi * T)) := by
  rw [helmholtzA, partitionZT, partitionZ_eq n hV (one_div_pos.mpr hT), Real.log_mul,
    Real.log_pow, Real.log_rpow, one_div, div_inv_eq_mul]
  ring_nf
  all_goals positivity

lemma ZIntegrable (hV : 0 < V) (hβ : 0 < β) : IdealGas.ZIntegrable (n,V) β := by
  have hZpos : 0 < partitionZ IdealGas (n, V) β := by
    rw [partitionZ_eq n hV hβ]
    positivity
  constructor
  · apply MeasureTheory.Integrable.of_integral_ne_zero
    rw [← partitionZ]
    exact hZpos.ne'
  · exact hZpos.ne'

/-- The ideal gas law: PV = nRT. In our unitsless system, R = 1. -/
theorem ideal_gas_law (hV : 0 < V) (hT : 0 < T) :
    let P := IdealGas.pressure (n,V) T;
    let R := 1;
    P * V = n * R * T := by
  dsimp [pressure]
  rw [← derivWithin_of_isOpen (s := Set.Ioi 0) isOpen_Ioi hV]
  rw [derivWithin_congr (f := fun V' ↦ -n * T *
    (Real.log V' + (3/2) * Real.log (2 * Real.pi * T))) ?_ ?_]
  rw [derivWithin_of_isOpen (s := Set.Ioi 0) isOpen_Ioi hV]
  erw [deriv_mul (by fun_prop) (by fun_prop (disch := exact hV.ne'))]
  simp [field]
  ring_nf
  · intro _ hV'
    dsimp
    rw [helmholtzA_eq n hV' hT]
    ring_nf
  · exact helmholtzA_eq n hV hT

-- Now proving e.g. Boyle's Law ("for an ideal gas with a fixed particle number, P and V are
-- inversely proportional") is a trivial consequence of the ideal gas law.

end IdealGas
