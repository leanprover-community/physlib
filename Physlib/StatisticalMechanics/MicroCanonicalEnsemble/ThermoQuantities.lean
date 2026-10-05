/-
Copyright (c) 2025 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
-/
module

public import Physlib.StatisticalMechanics.MicroCanonicalEnsemble.Basic
public import QuantumInfo.ForMathlib.ComplexLaplaceTransform
/-!

# The theormodynamical quantities of a microcanonical ensemble

-/
@[expose] public section

noncomputable section
namespace MicroHamiltonian

variable {D : Type} (H : MicroHamiltonian D) (d : D)

/-- The partition function corresponding to a given MicroHamiltonian. This is a function taking a
  thermodynamic β, not a temperature. It also depends on the data D defining the system extrinsincs.

  * Ideally this would be an NNReal, but ∫ (NNReal) doesn't work right now, so it would just be a
    separate proof anyway
-/
def partitionZ (β : ℝ) : ℝ :=
  ∫ (config : H.dim d → ℝ),
    let E := H.H config
    if h : E = ⊤ then 0 else Real.exp (-β * (E.untop h))

/-- The complexified partition function, viewed as a Laplace transform. -/
def PartitionZComplex (z : ℂ) : ℂ :=
  ComplexLaplaceTransform (fun config : H.dim d → ℝ => H.H config) z

/-- The complex convergence domain of the partition-function Laplace transform. -/
def ZComplexConvergenceDomain : Set ℂ :=
  ComplexLaplaceConvergenceDomain (fun config : H.dim d → ℝ => H.H config)

private theorem partitionZ_eq_re_partitionZComplex {β : ℝ}
    (hβ : (β : ℂ) ∈ H.ZComplexConvergenceDomain d) :
    H.partitionZ d β = (H.PartitionZComplex d β).re := by
  have hInt : MeasureTheory.Integrable (μ := MeasureTheory.volume)
      (ComplexLaplaceIntegrand (fun config : H.dim d → ℝ => H.H config) (β : ℂ)) := hβ
  rw [partitionZ, PartitionZComplex, ComplexLaplaceTransform]
  calc
    (∫ (config : H.dim d → ℝ),
        have E := H.H config
        if h : E = ⊤ then 0 else Real.exp (-β * E.untop h)) =
        ∫ x, RCLike.re (ComplexLaplaceIntegrand
          (fun config : H.dim d → ℝ => H.H config) (β : ℂ) x) := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards with config
      unfold ComplexLaplaceIntegrand
      by_cases h : H.H config = ⊤
      · simp [h]
      · simp only [h, dite_false]
        simpa [Complex.ofReal_mul] using
          (Complex.exp_ofReal_re (-(β * (H.H config).untop h))).symm
    _ = RCLike.re (∫ x, ComplexLaplaceIntegrand
        (fun config : H.dim d → ℝ => H.H config) (β : ℂ) x) := integral_re hInt

open scoped ContDiff Topology in
theorem contDiffAt_partitionZ_of_mem_interior_convergenceDomain {β : ℝ}
    (hβ : (β : ℂ) ∈ interior (H.ZComplexConvergenceDomain d)) :
    ContDiffAt ℝ ⊤ (H.partitionZ d) β := by
  refine (analyticAt_complexLaplaceTransform_of_mem_interior_convergenceDomain
    (E := fun config : H.dim d → ℝ => H.H config) (H.measurable_H d) hβ).contDiffAt
    |>.real_of_complex |>.congr_of_eventuallyEq ?_
  filter_upwards [(Complex.continuous_ofReal.tendsto β).eventually
    (IsOpen.mem_nhds isOpen_interior hβ)] with x hx using
    H.partitionZ_eq_re_partitionZComplex d (_root_.interior_subset hx)

/-- The partition function as a function of temperature T instead of β. -/
def partitionZT (T : ℝ) : ℝ :=
  partitionZ H d (1/T)

/-- The Internal Energy, U or E, defined as -∂(ln Z)/∂β. Parameterized here with β. -/
def internalU (β : ℝ) : ℝ :=
  -deriv (fun β' ↦ (partitionZ H d β').log) β

/-- The Helmholtz Free Energy, -T * ln Z. Also denoted F. Parameterized here with temperature T, not
  β. -/
def helmholtzA (T : ℝ) : ℝ :=
  -T * (partitionZT H d T).log

/-- The entropy, defined as the -∂A/∂T. Function of T. -/
def entropyS (T : ℝ) : ℝ :=
  -deriv (helmholtzA H d) T

/-- The entropy, defined as ln Z + β*U. Function of β. -/
def entropySβ (β : ℝ) : ℝ :=
  (partitionZ H d β).log + β * internalU H d β

/-- To be able to compute or define anything from a Hamiltonian, we need its partition function to
  be a computable integral. A Hamiltonian is ZIntegrable at β if PartitionZ is Lesbegue integrable
  and nonzero.
-/
def ZIntegrable (β : ℝ) : Prop :=
  MeasureTheory.Integrable (fun (config : H.dim d → ℝ) ↦
    let E := H.H config;
    if h : E = ⊤ then 0 else Real.exp (-β * (E.untop h))) ∧ (H.partitionZ d β ≠ 0)

/--
This Prop defines the most common case of ZIntegrable, that it is integrable at all finite
temperatures (aka all positive β).
-/
def PositiveβIntegrable : Prop :=
  ∀ β > 0, H.ZIntegrable d β

variable {H d}

/-
Need the fact that the partition function Z is differentiable. Assume it's integrable.
Letting μ⁻(H,E) be the measure of {x | H(x) ≤ E}, then for nonzero β,
∫_0..∞ exp(-βE) (dμ⁻/dE) dE =
∫ exp(-βH) dμ =
∫ (1/β * ∫_H..∞ exp(-βE) dE) dμ =
∫ (1/β * ∫_-∞..∞ exp(-βE) χ(E ≤ H) dE) dμ =
1/β * ∫ (∫ exp(-βE) χ(E ≤ H) dμ) dE =
1/β * ∫ exp(-βE) * μ⁻(H,E) dE

so this will be differentiable if
∫ exp(-βE) * μ⁻(H,E) dE
is, aka if the Laplace transform is differentiable.

For this we really want the fact that the Laplace transform is analytic wherever it's
absolutely convergent, which follows from the local domination estimate above,
Fubini's theorem, and Morera's theorem.
-/
/-- The two definitions of entropy, in terms of `T` or `β = 1 / T`, are equivalent. -/
theorem entropy_A_eq_entropy_Z (T : ℝ) (hT : T ≠ 0)
    (hZne : H.partitionZ d (1 / T) ≠ 0)
    (hZint : ((1 / T : ℝ) : ℂ) ∈ interior (H.ZComplexConvergenceDomain d)) :
    entropyS H d T = entropySβ H d (1 / T) := by
  have hZdiff : DifferentiableAt ℝ (H.partitionZ d) (1 / T) :=
    (H.contDiffAt_partitionZ_of_mem_interior_convergenceDomain d hZint).differentiableAt
      (by simp)
  dsimp [entropyS, entropySβ, internalU, partitionZT]
  unfold helmholtzA
  erw [deriv_mul]
  rw [deriv_neg'', neg_mul, one_mul, neg_add_rev, neg_neg, mul_neg, add_comm]
  congr 1
  simp_rw [partitionZT]
  have hdc := deriv_comp (h := fun T ↦ T⁻¹) (h₂ := fun β => Real.log (H.partitionZ d β)) T ?_ ?_
  unfold Function.comp at hdc
  simp only [hdc, one_div, deriv_inv', mul_neg, neg_inj]
  field_simp
  ring_nf
  --Show the differentiability side-goals
  · rw [← one_div]
    fun_prop (disch := assumption)
  · fun_prop (disch := assumption)
  · fun_prop
  · simp_rw [partitionZT]
    fun_prop (disch := assumption)

open scoped ContDiff in
/--
The "definition of temperature from entropy":
1/T = (∂S/∂U), when the derivative is at constant extrinsic d (typically N/V).
Here we use β instead of 1/T on the left, and express the right actually as (∂S/∂β)/(∂U/∂β),
as all our things are ultimately parameterized by β.

This identity requires the denominator `∂U/∂β` to be nonzero.
-/
theorem β_eq_deriv_S_U {β : ℝ}
    (hZne : H.partitionZ d β ≠ 0)
    (hZint : (β : ℂ) ∈ interior (H.ZComplexConvergenceDomain d))
    (hU' : deriv (H.internalU d) β ≠ 0) :
    β = (deriv (H.entropySβ d) β) / deriv (H.internalU d) β := by
  have hZ : ContDiffAt ℝ ⊤ (H.partitionZ d) β :=
    H.contDiffAt_partitionZ_of_mem_interior_convergenceDomain d hZint
  unfold entropySβ internalU

  --Show the differentiability side-goals
  have hlogDiff : DifferentiableAt ℝ (fun β => Real.log (H.partitionZ d β)) β :=
    (hZ.differentiableAt (by simp)).log hZne
  have hlogDerivDiff : DifferentiableAt ℝ (deriv fun β => Real.log (H.partitionZ d β)) β := by
    have := ((hZ.log hZne).fderiv_right (m := ⊤) (OrderTop.le_top _)).differentiableAt (by simp)
    unfold deriv
    fun_prop
  have hderiv : deriv (deriv fun β => Real.log (H.partitionZ d β)) β ≠ 0 := by
    intro hzero
    apply hU'
    change deriv (-fun β => deriv (fun β' => Real.log (H.partitionZ d β')) β) β = 0
    simp [deriv.neg, hzero]

  --Main goal
  simp only [mul_neg]
  erw [deriv.neg', deriv_add, deriv.neg']
  dsimp
  erw [deriv_mul]
  simp only [deriv_id'', one_mul, neg_add_rev, add_neg_cancel_comm_assoc, neg_div_neg_eq]
  exact (mul_div_cancel_right₀ β hderiv).symm
  --Discharge those side-goals
  · exact differentiableAt_id
  · exact hlogDerivDiff
  · fun_prop (disch := assumption)
  · fun_prop (disch := assumption)

open scoped ContDiff in
example (x : ℝ) (f : ℝ → ℝ) (hf : ContDiffAt ℝ ⊤ f x) : DifferentiableAt ℝ (deriv f) x := by
  have := (hf.fderiv_right (m := ⊤) (OrderTop.le_top _)).differentiableAt (by simp)
  unfold deriv
  fun_prop

end MicroHamiltonian

--! Specializing to a system of particles in space

namespace NVEHamiltonian
open MicroHamiltonian

variable (H : NVEHamiltonian) (d : ℕ × ℝ)

/-- Pressure, as a function of T. Defined as the conjugate variable to volume. -/
def pressure (T : ℝ) : ℝ :=
  let (n, V) := d;
  - deriv (fun V' ↦ helmholtzA H (n, V') T) V

end NVEHamiltonian
