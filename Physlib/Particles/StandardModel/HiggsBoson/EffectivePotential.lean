/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Particles.StandardModel.HiggsBoson.Basic
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
/-!
# The effective potential of the Higgs field

We define a general effective potential for the Higgs field.
For this we define two properties of the potential: invariance under the gauge group, and a
maximum mass dimension.

Given these, we prove that the potential can be expressed as a polynomial in the norm of the
Higgs field.

-/

@[expose] public section

noncomputable section

namespace StandardModel

namespace HiggsField

open SpaceTime


/-- A general potential of the Higgs field. -/
abbrev EffectivePotential : Type := HiggsVec → ℝ

namespace EffectivePotential

/-!

## A. The invariance of the general potential under the gauge group

-/

/-- The proposition that the general potential is invariant under
  the global action of the gauge group. -/
def IsInvariant (V : EffectivePotential) : Prop :=
  ∀ (g : GaugeGroupI), ∀ (φ : HiggsVec), V (HiggsVec.repGaugeGroupI g φ) = V φ

namespace IsInvariant

/-- An invariant potential is equal on gauge orbits. -/
lemma eq_on_orbits {φ1 φ2 : HiggsVec} {V : EffectivePotential} (h : IsInvariant V)
    (hφ : ∃ g : GaugeGroupI, HiggsVec.repGaugeGroupI g φ2 = φ1) :
    V φ1 = V φ2 := by
  obtain ⟨g, rfl⟩ := hφ
  exact h g φ2

/-- An invariant potential is equal on Higgs vectors with identical norms. -/
lemma eq_of_norm_eq {φ1 φ2 : HiggsVec} {V : EffectivePotential} (h : IsInvariant V)
    (hφ : ‖φ1‖ = ‖φ2‖) :
    V φ1 = V φ2 := h.eq_on_orbits <| (HiggsVec.exists_repGaugeGroupI_eq_iff_norm_eq φ2 φ1).mpr hφ

lemma factors_through_norm {V : EffectivePotential} (h : IsInvariant V) :
    ∃ (f : ℝ → ℝ), V = f ∘ norm := by
  use fun a => V !₂[a, 0]
  ext φ
  apply h.eq_of_norm_eq
  conv_rhs => rw [PiLp.norm_eq_of_L2]
  simp

end IsInvariant

/-!

## B. Maximum mass dimension

-/

/-- The proposition that the potential `V` has a maximum mass dimension
  less then or equal to `n` - also implying it is a polynomial. -/
def HasMaxMassDimLE (V : EffectivePotential) (n : ℕ) : Prop :=
  ∃ p : MvPolynomial (Fin 4) ℝ, (∀ φ : HiggsVec, V φ = p.eval φ.toRealScalars) ∧
    p.totalDegree ≤ n

/-- The polynomial associated to a potential `V` with a maximum mass dimension
  less than or equal to `n`. -/
def polynomial (V : EffectivePotential) {n : ℕ} (h : HasMaxMassDimLE V n) :
    MvPolynomial (Fin 4) ℝ := Classical.choose h

lemma polynomial_totalDegree {V : EffectivePotential} {n : ℕ} (h : HasMaxMassDimLE V n) :
    (polynomial V h).totalDegree ≤ n := (Classical.choose_spec h).2

lemma apply_eq_polynomial {V : EffectivePotential} {n : ℕ} (h : HasMaxMassDimLE V n)
    (φ : HiggsVec) : V φ = (polynomial V h).eval φ.toRealScalars := (Classical.choose_spec h).1 φ

TODO "Reformulate `HasMaxMassDimLE` (and `polynomial`) to use the basis-independent polynomial
  ring `MvPolynomial (Module.Dual ℝ HiggsVec) ℝ` rather than `MvPolynomial (Fin 4) ℝ`, so that the
  effective potential is expressed without reference to the explicit coordinate map
  `HiggsVec.toRealScalars`."

/-!

## C. Terms of a given mass dimension

-/

/-- The part of a potential at a given mass-dimension. -/
def termOfMassDim (V : EffectivePotential) {n : ℕ} (h : HasMaxMassDimLE V n) (m : ℕ) :
    HiggsVec → ℝ := fun φ => ((polynomial V h).homogeneousComponent m).eval φ.toRealScalars

lemma termOfMassDim_eq_zero_of_max_lt {V : EffectivePotential} {n : ℕ} (h : HasMaxMassDimLE V n)
    {m : ℕ} (hm : n < m) (φ : HiggsVec) :
    termOfMassDim V h m φ = 0 := by
  have h1 := polynomial_totalDegree h
  simp only [termOfMassDim]
  rw [MvPolynomial.homogeneousComponent_eq_zero _ _ (by omega), map_zero]

lemma termOfMassDim_homogeneity {V : EffectivePotential} {n : ℕ} (h : HasMaxMassDimLE V n) (m : ℕ)
    (φ : HiggsVec) (t : ℝ) : termOfMassDim V h m (t • φ) = t ^ m * termOfMassDim V h m φ := by
  rw [termOfMassDim, termOfMassDim, map_smul, MvPolynomial.eval_eq', MvPolynomial.eval_eq',
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hdeg : ∑ i, d i = m := by
    rw [MvPolynomial.support_homogeneousComponent, Finset.mem_filter] at hd
    rw [← Finsupp.degree_eq_sum]
    exact hd.2
  simp only [Pi.smul_apply, smul_eq_mul, mul_pow, Finset.prod_mul_distrib,
    Finset.prod_pow_eq_pow_sum, hdeg]
  ring

lemma apply_eq_sum_termOfMassDim {V : EffectivePotential} {n : ℕ} (h : HasMaxMassDimLE V n)
    (φ : HiggsVec) :
    V φ = ∑ m ∈ Finset.range (n + 1), termOfMassDim V h m φ := by
  rw [apply_eq_polynomial h, ← MvPolynomial.sum_homogeneousComponent (polynomial V h)]
  simp only [map_sum]
  change  ∑ x ∈ Finset.range ((V.polynomial h).totalDegree + 1), termOfMassDim V h x φ = _
  symm
  refine Finset.eventually_constant_sum ?_ ?_
  · intro m hm
    simp only [termOfMassDim]
    rw [MvPolynomial.homogeneousComponent_eq_zero _ _ (by omega), map_zero]
  · exact Nat.add_le_add_right (polynomial_totalDegree h) 1

lemma apply_smul_eq_sum_termOfMassDim {V : EffectivePotential} {n : ℕ} (h : HasMaxMassDimLE V n)
    (φ : HiggsVec) (t : ℝ) :
    V (t • φ) = ∑ m ∈ Finset.range (n + 1), t ^ m * termOfMassDim V h m φ := by
  rw [apply_eq_sum_termOfMassDim h]
  exact Finset.sum_congr rfl fun m _ => termOfMassDim_homogeneity h m φ t

lemma termOfMassDim_isInvariant {V : EffectivePotential} {n : ℕ} (h : HasMaxMassDimLE V n)
    (m : ℕ) (hV : IsInvariant V) : IsInvariant (termOfMassDim V h m) := by
  intro g φ
  have hV (t : ℝ) := hV g (t • φ)
  have h1 (t : ℝ) : ∑  m ∈ Finset.range (n + 1),
      t ^ m * (termOfMassDim V h m (HiggsVec.repGaugeGroupI g φ) -
      termOfMassDim V h m φ) = 0 := by
    simp [mul_sub, ← apply_smul_eq_sum_termOfMassDim]
    rw [← LinearMap.map_smul_of_tower, hV, sub_eq_zero]
  by_cases hmn : m ≤ n
  · have hp : (∑ k ∈ Finset.range (n + 1),
        Polynomial.C (termOfMassDim V h k (HiggsVec.repGaugeGroupI g φ) -
          termOfMassDim V h k φ) * Polynomial.X ^ k)
          = 0 := by
      apply Polynomial.funext
      intro x
      simp only [Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C,
        Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_zero]
      rw [← h1 x]
      exact Finset.sum_congr rfl fun k _ => by ring
    have hcoeff := congrArg (fun p => p.coeff m) hp
    simpa only [Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
      mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_range, Nat.lt_succ_iff, hmn,
      if_true, Polynomial.coeff_zero, sub_eq_zero] using hcoeff
  · rw [termOfMassDim_eq_zero_of_max_lt h (not_le.mp hmn),
      termOfMassDim_eq_zero_of_max_lt h (not_le.mp hmn)]

lemma termOfMassDim_eq_mul_norm {V : EffectivePotential} {n : ℕ}
    (h : HasMaxMassDimLE V n) (m : ℕ) (hV : IsInvariant V) (φ : HiggsVec) :
    ∃ c, termOfMassDim V h m φ = c * ‖φ‖ ^ m := by
  use termOfMassDim V h m !₂[1, 0]
  rw [(termOfMassDim_isInvariant h m hV).eq_of_norm_eq (φ2 := ‖φ‖ • !₂[1, 0])
    (by simp [PiLp.norm_eq_of_L2]), termOfMassDim_homogeneity h m !₂[1, 0] ‖φ‖]
  ring

lemma termOfMassDim_zero_of_odd {V : EffectivePotential} {n : ℕ} (h : HasMaxMassDimLE V n) (m : ℕ)
    (hV : IsInvariant V) (φ : HiggsVec) (hodd : Odd m)  :
    termOfMassDim V h m φ = 0 := by
  have h1 : termOfMassDim V h m φ = termOfMassDim V h m ((-1 : ℝ) • φ) :=
    (termOfMassDim_isInvariant h m hV).eq_of_norm_eq (by simp)
  rw [termOfMassDim_homogeneity h m φ (-1 : ℝ), hodd.neg_one_pow] at h1
  linarith

/-!

## D. Potential in terms of the norm of the Higgs field

-/

lemma apply_eq_sum_even_termOfMassDim {V : EffectivePotential} {n : ℕ} (h : HasMaxMassDimLE V n)
    (hV : IsInvariant V) (φ : HiggsVec) :
    V φ = ∑ m ∈ Finset.range (n / 2 + 1), termOfMassDim V h (2 * m) φ := by
  rw [apply_eq_sum_termOfMassDim h, ← Finset.sum_filter_add_sum_filter_not
    (Finset.range (n + 1)) Even]
  have hodd : ∑ m ∈ (Finset.range (n + 1)).filter (fun m => ¬ Even m),
      termOfMassDim V h m φ = 0 := by
    refine Finset.sum_eq_zero fun m hm => ?_
    simp only [Finset.mem_filter] at hm
    exact termOfMassDim_zero_of_odd h m hV φ (Nat.not_even_iff_odd.mp hm.2)
  rw [hodd, add_zero]
  have hset : (Finset.range (n / 2 + 1)).image (fun k => 2 * k)
      = (Finset.range (n + 1)).filter Even := by
    ext a
    simp only [Finset.mem_image, Finset.mem_range, Finset.mem_filter, Nat.even_iff]
    constructor
    · rintro ⟨k, hk, rfl⟩
      omega
    · rintro ⟨ha, hae⟩
      exact ⟨a / 2, by omega, by omega⟩
  rw [← hset, Finset.sum_image fun x _ y _ hxy => by omega]

lemma apply_eq_sum_even_termOfMassDim_fin {V : EffectivePotential} {n : ℕ} (h : HasMaxMassDimLE V n)
    (hV : IsInvariant V) (φ : HiggsVec) :
    V φ = ∑ m : Fin (n/2 + 1), termOfMassDim V h (2 * m) φ := by
  rw [apply_eq_sum_even_termOfMassDim h hV φ, Finset.sum_range]

/-- The potential is equal to the sum of norms to even powers. -/
lemma apply_eq_sum_norm_pow {V : EffectivePotential} {n : ℕ} (h : HasMaxMassDimLE V n)
    (hV : IsInvariant V) (φ : HiggsVec) :
    ∃ c : Fin (n/2 + 1) → ℝ, V φ = ∑ m, c m • ‖φ‖ ^ (2 * m.1) := by
  use fun m' => Classical.choose (termOfMassDim_eq_mul_norm h (2 * m'.1) hV φ)
  rw [apply_eq_sum_even_termOfMassDim_fin h hV φ]
  refine Finset.sum_congr rfl fun m _ => ?_
  simpa using Classical.choose_spec (termOfMassDim_eq_mul_norm h (2 * m.1) hV φ)

end EffectivePotential

end HiggsField

end StandardModel
end
