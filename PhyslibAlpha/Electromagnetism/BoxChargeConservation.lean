/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Electromagnetism.ThreeDimension.MaxwellEquations
public import Mathlib.MeasureTheory.Integral.DivergenceTheorem

/-!

# Charge conservation on a box from Maxwell's equations

Let `V` be an electromagnetic potential and `J₄` a Lorentz current density such that `V` is an
extremum of the free-space action with source `J₄`, i.e. Maxwell's equations hold. Taking the
divergence of Ampère's law, the divergence of the curl of the magnetic field vanishes, and the
divergence of the displacement current is, by Gauss's law, the time derivative of the charge
density. This gives the continuity equation `∂ₜ ρ + ∇ ⬝ J = 0`.

Integrating the continuity equation over a coordinate box `[a, b]` and applying the divergence
theorem, the net current leaving the box equals minus the rate of change of the charge it
contains. In particular, if no charge accumulates inside the box, the currents leaving through
its six faces sum to zero.

This is motivated by Kirchhoff's current law, but is not that law: Kirchhoff's current law is a
statement about the branch currents meeting at the nodes of a lumped-element circuit, whereas
the results here are the integral form of charge conservation on a single box.

## Main results

- `Space.integral_div_box` : the divergence theorem on a coordinate box in `Space`.
- `Electromagnetism.ThreeDimension.continuityEquation` : the continuity equation.
- `Electromagnetism.LorentzCurrentDensity.boxFaceCurrent`,
  `Electromagnetism.LorentzCurrentDensity.boxOutwardCurrent` : the current through a face of a
  coordinate box, and the net current leaving the box.
- `Electromagnetism.ThreeDimension.boxOutwardCurrent_eq` : the integral form of charge
  conservation.
- `Electromagnetism.ThreeDimension.boxOutwardCurrent_eq_zero_of_steady` : the net current
  leaving a box in which no charge accumulates is zero.

## Contents

- A. Vector calculus on `Space`
  - A.1. Time derivatives and the divergence
  - A.2. Smoothness of the curl
  - A.3. The divergence theorem on a coordinate box
- B. The continuity equation
  - B.1. The continuity equation from Gauss's and Ampère's laws
  - B.2. The continuity equation for an electromagnetic potential
- C. Charge conservation on a box
  - C.1. Currents through a box
  - C.2. The integral form of charge conservation
  - C.3. Steady charge in a box

-/

@[expose] public section

open Space Time MeasureTheory Set

namespace Space

/-!

## A. Vector calculus on `Space`

### A.1. Time derivatives and the divergence

-/

lemma div_differentiable_time {d} (f : Time → Space d → EuclideanSpace ℝ (Fin d))
    (hf : ContDiff ℝ 2 ↿f) (x : Space d) :
    Differentiable ℝ (fun t => (∇ ⬝ f t) x) := by
  have hfi (i : Fin d) : ContDiff ℝ 2 ↿(fun t x => f t x i) :=
    (ContinuousLinearMap.contDiff (𝕜 := ℝ) (EuclideanSpace.proj i)).comp hf
  simp only [div]
  exact Differentiable.fun_sum fun i _ => space_deriv_differentiable_time (hfi i) x

/-- The divergence and the time derivative commute. -/
lemma time_deriv_div_commute {d} (f : Time → Space d → EuclideanSpace ℝ (Fin d))
    (hf : ContDiff ℝ 2 ↿f) (t : Time) (x : Space d) :
    ∂ₜ (fun t => (∇ ⬝ f t) x) t = (∇ ⬝ fun x => ∂ₜ (fun t => f t x) t) x := by
  have hfi (i : Fin d) : ContDiff ℝ 2 ↿(fun t x => f t x i) :=
    (ContinuousLinearMap.contDiff (𝕜 := ℝ) (EuclideanSpace.proj i)).comp hf
  simp only [div]
  rw [Time.deriv_eq, fderiv_fun_sum fun i _ =>
    (space_deriv_differentiable_time (hfi i) x).differentiableAt]
  simp only [FunLike.coe_sum, Finset.sum_apply, ← Time.deriv_eq]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [time_deriv_comm_space_deriv (hfi i)]
  congr
  funext y
  rw [Time.deriv_euclid]
  exact fun t => ((hf.differentiable (by simp)).comp (f := fun t => (t, y)) (by fun_prop)) t

/-!

### A.2. Smoothness of the curl

-/

lemma curl_contDiff {n : WithTop ℕ∞} (f : Space → EuclideanSpace ℝ (Fin 3))
    (hf : ContDiff ℝ (n + 1) f) : ContDiff ℝ n (∇ ⨯ f) := by
  rw [contDiff_euclidean]
  intro i
  have hfi (j : Fin 3) : ContDiff ℝ (n + 1) (fun x => f x j) :=
    (ContinuousLinearMap.contDiff (𝕜 := ℝ) (EuclideanSpace.proj j)).comp hf
  have hd (j k : Fin 3) : ContDiff ℝ n (fun x => ∂[j] (fun x => f x k) x) :=
    (contDiff_apply ℝ ℝ j).comp (deriv_contDiff (hfi k))
  exact (hd _ _).sub (hd _ _)

/-!

### A.3. The divergence theorem on a coordinate box

The box `[a, b]` is given in coordinates, `a b : Fin (n + 1) → ℝ`. Its faces normal to the
`i`-th axis are parametrized, as in Mathlib's divergence theorem, by the remaining coordinates
`y ∈ [a ∘ i.succAbove, b ∘ i.succAbove]` through `i.insertNth c y` with `c = a i` or `c = b i`.

The divergence theorem below integrates over the box in coordinates, `x ∈ [a, b]`, rather than
over the image of the box in `Space`.

-/

lemma div_mk_eq_sum_fderiv {n : ℕ} (f : Space n → EuclideanSpace ℝ (Fin n))
    (hf : Differentiable ℝ f) (x : Fin n → ℝ) :
    (∇ ⬝ f) ⟨x⟩ = ∑ i, fderiv ℝ (fun y : Fin n → ℝ => f ⟨y⟩ i) x (Pi.single i 1) := by
  refine Finset.sum_congr rfl fun i _ => ?_
  have hfi : Differentiable ℝ (fun y : Space n => f y i) :=
    (EuclideanSpace.proj (𝕜 := ℝ) i).differentiable.comp hf
  rw [Space.deriv_eq_fderiv_basis, fderiv_fun_comp x (hfi _) (mk_differentiable x), fderiv_mk]
  simp only [ContinuousLinearMap.coe_comp, Function.comp_apply]
  congr 1
  ext j
  simp [equivPi, basis_apply, Pi.single_apply, eq_comm]

/-- The divergence theorem on a coordinate box in `Space`. -/
lemma integral_div_box {n : ℕ} (f : Space (n + 1) → EuclideanSpace ℝ (Fin (n + 1)))
    (hf : ContDiff ℝ 1 f) (a b : Fin (n + 1) → ℝ) (hle : a ≤ b) :
    ∫ x in Icc a b, (∇ ⬝ f) ⟨x⟩ =
      ∑ i, ((∫ y in Icc (a ∘ i.succAbove) (b ∘ i.succAbove), f ⟨i.insertNth (b i) y⟩ i) -
        ∫ y in Icc (a ∘ i.succAbove) (b ∘ i.succAbove), f ⟨i.insertNth (a i) y⟩ i) := by
  have hfi (i : Fin (n + 1)) : ContDiff ℝ 1 (fun y : Fin (n + 1) → ℝ => f ⟨y⟩ i) :=
    (EuclideanSpace.proj (𝕜 := ℝ) i).contDiff.comp (hf.comp mk_contDiff)
  simp only [div_mk_eq_sum_fderiv f (hf.differentiable (by simp))]
  refine integral_divergence_of_hasFDerivAt_off_countable' a b hle (fun i y => f ⟨y⟩ i)
    (fun i y => fderiv ℝ (fun y : Fin (n + 1) → ℝ => f ⟨y⟩ i) y) ∅ countable_empty
    (fun i => (hfi i).continuous.continuousOn)
    (fun y _ i => ((hfi i).differentiable (by simp) y).hasFDerivAt) ?_
  refine ContinuousOn.integrableOn_compact isCompact_Icc (Continuous.continuousOn ?_)
  exact continuous_finsetSum _ fun i _ =>
    ((hfi i).continuous_fderiv (by simp)).clm_apply continuous_const

end Space

namespace Electromagnetism
namespace ThreeDimension

open ElectromagneticPotential ContDiff

/-!

## B. The continuity equation

### B.1. The continuity equation from Gauss's and Ampère's laws

-/

/-- Fields `E`, `B`, `ρ` and `J` obeying Gauss's law for the electric field and Ampère's law
obey the continuity equation. -/
lemma continuity_of_gauss_ampere (𝓕 : FreeSpace)
    {E B J : Time → Space → EuclideanSpace ℝ (Fin 3)} {ρ : Time → Space → ℝ}
    (hE : ContDiff ℝ 2 ↿E) (hB : ∀ t, ContDiff ℝ 2 (B t))
    (hGauss : ∀ t x, (∇ ⬝ E t) x = ρ t x / 𝓕.ε₀)
    (hAmpere : ∀ t x, (∇ ⨯ B t) x = 𝓕.μ₀ • J t x + 𝓕.μ₀ • 𝓕.ε₀ • ∂ₜ (fun t => E t x) t)
    (t : Time) (x : Space) :
    ∂ₜ (fun t => ρ t x) t + (∇ ⬝ J t) x = 0 := by
  -- Solve Ampère's law for `J` and Gauss's law for `ρ`.
  have hJ : J t = 𝓕.μ₀⁻¹ • (∇ ⨯ B t) - 𝓕.ε₀ • fun x => ∂ₜ (fun t => E t x) t := by
    funext y
    rw [Pi.sub_apply, Pi.smul_apply, Pi.smul_apply, hAmpere, smul_add, smul_smul, smul_smul,
      inv_mul_cancel₀ 𝓕.μ₀_ne_zero, one_smul, one_smul, add_sub_cancel_right]
  have hρ : (fun t => ρ t x) = fun t => 𝓕.ε₀ * (∇ ⬝ E t) x := by
    funext s
    rw [hGauss, mul_div_cancel₀ _ 𝓕.ε₀_ne_zero]
  have hcurl : Differentiable ℝ (∇ ⨯ B t) :=
    (Space.curl_contDiff (n := 1) _ (hB t)).differentiable (by simp)
  have hdE : Differentiable ℝ fun x => ∂ₜ (fun t => E t x) t :=
    time_deriv_differentiable_space hE t
  -- The divergence of the curl vanishes; the displacement current carries `-∂ₜ ρ`.
  rw [hJ, sub_eq_add_neg, ← neg_smul, div_add _ _ (hcurl.const_smul _) (hdE.const_smul _),
    div_smul _ _ hcurl, div_smul _ _ hdE, div_of_curl_eq_zero _ (hB t), hρ, Time.deriv_eq,
    fderiv_const_mul ((div_differentiable_time E hE x) t)]
  simp [← Time.deriv_eq, time_deriv_div_commute E hE]

/-!

### B.2. The continuity equation for an electromagnetic potential

-/

variable {𝓕 : FreeSpace} (V : ElectromagneticPotential 3) (J₄ : LorentzCurrentDensity 3)

lemma magneticField_contDiff_space (hV : ContDiff ℝ ∞ V) (t : Time) :
    ContDiff ℝ 2 (V.magneticField 𝓕.c t) := by
  have hV3 : ContDiff ℝ (2 + 1) V := hV.of_le (WithTop.coe_le_coe.mpr le_top)
  simp only [magneticField_eq_3D]
  exact Space.curl_contDiff (n := 2) _ (by fun_prop)

/-- The continuity equation: Maxwell's equations imply local conservation of charge. -/
theorem continuityEquation (t : Time) (x : Space)
    (h : IsExtrema 𝓕 V J₄) (hV : ContDiff ℝ ∞ V) (hJ : ContDiff ℝ ∞ J₄) :
    ∂ₜ (fun t => J₄.chargeDensity 𝓕.c t x) t + (∇ ⬝ J₄.currentDensity 𝓕.c t) x = 0 :=
  continuity_of_gauss_ampere 𝓕 (electricField_contDiff (hV.of_le (WithTop.coe_le_coe.mpr le_top)))
    (magneticField_contDiff_space V hV) (fun t x => gaussLawElectric V J₄ t x h hV hJ)
    (fun t x => ampereLaw V J₄ t x h hV hJ) t x

/-!

## C. Charge conservation on a box

### C.1. Currents through a box

-/

/-- The electric current at time `t` through the face `x i = s` of the coordinate box `[a, b]`,
counted positively in the direction of increasing `x i`. -/
noncomputable def _root_.Electromagnetism.LorentzCurrentDensity.boxFaceCurrent
    (c : SpeedOfLight) (J : LorentzCurrentDensity 3) (t : Time) (a b : Fin 3 → ℝ) (i : Fin 3)
    (s : ℝ) : ℝ :=
  ∫ y in Icc (a ∘ i.succAbove) (b ∘ i.succAbove), J.currentDensity c t ⟨i.insertNth s y⟩ i

/-- The net electric current at time `t` leaving the coordinate box `[a, b]` through its six
faces. -/
noncomputable def _root_.Electromagnetism.LorentzCurrentDensity.boxOutwardCurrent
    (c : SpeedOfLight) (J : LorentzCurrentDensity 3) (t : Time) (a b : Fin 3 → ℝ) : ℝ :=
  ∑ i, (J.boxFaceCurrent c t a b i (b i) - J.boxFaceCurrent c t a b i (a i))

/-!

### C.2. The integral form of charge conservation

-/

/-- The net current leaving the coordinate box `[a, b]` equals minus the rate of change of the
charge inside it. -/
lemma boxOutwardCurrent_eq (t : Time) (a b : Fin 3 → ℝ) (hle : a ≤ b)
    (h : IsExtrema 𝓕 V J₄) (hV : ContDiff ℝ ∞ V) (hJ : ContDiff ℝ ∞ J₄) :
    J₄.boxOutwardCurrent 𝓕.c t a b =
      - ∫ x in Icc a b, ∂ₜ (fun t => J₄.chargeDensity 𝓕.c t ⟨x⟩) t := by
  have hJt : ContDiff ℝ 1 (J₄.currentDensity 𝓕.c t) :=
    (LorentzCurrentDensity.currentDensity_ContDiff
      (hJ.of_le (WithTop.coe_le_coe.mpr le_top))).comp (f := fun x => (t, x)) (by fun_prop)
  rw [LorentzCurrentDensity.boxOutwardCurrent]
  simp only [LorentzCurrentDensity.boxFaceCurrent]
  rw [← integral_div_box _ hJt a b hle, ← integral_neg]
  congr 1
  funext x
  exact eq_neg_of_add_eq_zero_right (continuityEquation V J₄ t ⟨x⟩ h hV hJ)

/-!

### C.3. Steady charge in a box

-/

/-- If no charge accumulates inside the coordinate box `[a, b]`, the net current leaving through
its six faces is zero. This is motivated by Kirchhoff's current law, with the box enclosing a
node of a circuit. -/
lemma boxOutwardCurrent_eq_zero_of_steady (t : Time) (a b : Fin 3 → ℝ) (hle : a ≤ b)
    (h : IsExtrema 𝓕 V J₄) (hV : ContDiff ℝ ∞ V) (hJ : ContDiff ℝ ∞ J₄)
    (hsteady : ∀ x ∈ Icc a b, ∂ₜ (fun t => J₄.chargeDensity 𝓕.c t ⟨x⟩) t = 0) :
    J₄.boxOutwardCurrent 𝓕.c t a b = 0 := by
  rw [boxOutwardCurrent_eq V J₄ t a b hle h hV hJ, setIntegral_eq_zero_of_forall_eq_zero hsteady,
    neg_zero]

end ThreeDimension
end Electromagnetism
