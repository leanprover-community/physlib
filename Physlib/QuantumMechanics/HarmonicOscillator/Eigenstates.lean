/-
Copyright (c) 2026 Gregory J. Loges. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Philippe Kevorkian, Gregory J. Loges
-/
module

public import Physlib.Mathematics.InnerProductSpace.Gaussian
public import Physlib.Mathematics.HasTemperateGrowth
public import Physlib.Mathematics.KroneckerDelta.Basic
public import Physlib.Mathematics.SpecialFunctions.PhysHermite
public import Physlib.QuantumMechanics.HarmonicOscillator.Basic
public import Physlib.QuantumMechanics.HarmonicOscillator.LadderOperators
public import Physlib.Meta.Sorry
/-!

# Energy eigenstates of the quantum harmonic oscillator

## i. Overview

The quantum harmonic oscillator in `d` dimensions is exactly solvable - the energy eigenvalues
and eigenfunction can be computed analytically.

The ground-state wavefunction is a normalized Gaussian with covariance controlled
by the harmonic oscillator's characteristic lengths. A general state is then obtained by acting
on the ground state with the raising operators and is labelled by `d` integer quantum numbers.
Their wavefunctions are given by products of (physicist's) Hermite polynomials multiplying
the ground-state Gaussian. The ladder operators of `LadderOperators.lean` act on them by shifting
one quantum number, `aᵢ† ψₙ = √(nᵢ + 1) ψₙ₊ₑᵢ` and `aᵢ ψₙ = √nᵢ ψₙ₋ₑᵢ`, so that `Nᵢ ψₙ = nᵢ ψₙ` and
`H ψₙ = Eₙ ψₙ` with `Eₙ = ∑ᵢ ℏ ωᵢ (nᵢ + ½)`, both for the Hamiltonian in terms of the number
operators and for the kinetic-plus-potential Hamiltonian of `Basic.lean`.

When the potential is isotropic another description of the energy eigenstates is possible;
energy eigenspaces carry SO(d) representations and eigenfunctions can be written in terms of
hyperspherical harmonics. In such cases the energies only depend on the radial quantum number.

## ii. Key results

- `raising_eigenfunction`, `lowering_eigenfunction`: `aᵢ† ψₙ = √(nᵢ + 1) ψₙ₊ₑᵢ`,
  `aᵢ ψₙ = √nᵢ ψₙ₋ₑᵢ`; `lowering_eigenfunction_zero`: `aᵢ ψ₀ = 0`.
- `number_eigenfunction`: `Nᵢ ψₙ = nᵢ ψₙ`.
- `numberHamiltonianCLM_eigenfunction`, `hamiltonian_eigenstate`: `H ψₙ = Eₙ ψₙ`.

## iii. Table of contents

- A. Cartesian basis
  - A.1. Energy eigenvalues
  - A.2. Eigenfunctions
  - A.3. Eigenstates
- B. The ladder operators on the eigenfunctions
- C. The eigenvalue equation

## iv. References

* None.
-/
@[expose] public section

TODO "Prove that the QHO eigenstates in the Cartesian basis (Hermite polynomials) are orthonormal."

TODO "Prove that the (point) spectrum of the self-adjoint Hamiltonian is `Set.range Q.eigenEnergy`."

TODO "Prove that the ground-state of the QHO is non-degenerate."

TODO "Determine the energy eigenstates of the isotropic quantum harmonic oscillator
  in the 'spherical basis' in terms of spherical harmonics."

noncomputable section
namespace QuantumMechanics
namespace HarmonicOscillator

open Complex Constants Finset InnerProductSpace Polynomial SchwartzMap Space SpaceDHilbertSpace
open scoped Nat Real ComplexConjugate

variable {d : ℕ} (Q : HarmonicOscillator d) (n n' : Fin d → ℕ) (x : Space d)

/-!
## A. Cartesian basis
-/

/-!
## A.1. Energy eigenvalues
-/

/-- The energy eigenvalues, `∑ i, ℏ ωᵢ (nᵢ + ½)`. -/
def eigenEnergy : ℝ := ∑ i, ℏ * Q.ω i * (n i + 1 / 2)

lemma eigenEnergy_eq : Q.eigenEnergy n = ∑ i, ℏ * Q.ω i * (n i + 1 / 2) := rfl

lemma eigenEnergy_strictMono : StrictMono Q.eigenEnergy := by
  intro n n' h
  obtain ⟨h, i, hi⟩ := Pi.lt_def.mp h
  exact sum_lt_sum (fun i _ ↦ by simp [h i]) ⟨i, mem_univ i, by simp [hi]⟩

/-!
### A.2. Eigenfunctions
-/

/-- The `i`th normalization constant for `Q.eigenfunction n`, `1 / √(2 ^ nᵢ * nᵢ! * √π * ξᵢ)`. -/
def eigenCoeff (i : Fin d) : ℝ := 1 / √(2 ^ n i * (n i)! * √π * Q.ξ i)

lemma eigenCoeff_eq (i : Fin d) : Q.eigenCoeff n i = 1 / √(2 ^ n i * (n i)! * √π * Q.ξ i) := rfl

/-- `√(nᵢ + 1) c(n + eᵢ)ᵢ = c(n)ᵢ / √2`. -/
lemma eigenCoeff_update_succ (i : Fin d) (n : Fin d → ℕ) :
    √((n i : ℝ) + 1) * Q.eigenCoeff (Function.update n i (n i + 1)) i
      = (√2)⁻¹ * Q.eigenCoeff n i := by
  simp only [eigenCoeff_eq, Function.update_self]
  have hpos : 0 < (2 : ℝ) ^ n i * (n i)! * √π * Q.ξ i :=
    mul_pos (mul_pos (mul_pos (by positivity) (by positivity)) (by positivity)) (Q.ξ_pos i)
  have h1 : (2 : ℝ) ^ (n i + 1) * ((n i + 1)! : ℝ) * √π * Q.ξ i
      = (2 * ((n i : ℝ) + 1)) * (2 ^ n i * (n i)! * √π * Q.ξ i) := by
    push_cast [Nat.factorial_succ]
    ring
  rw [h1, Real.sqrt_mul (by positivity : (0 : ℝ) ≤ 2 * ((n i : ℝ) + 1)),
    Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
  have h2 := Real.sqrt_pos.mpr hpos
  have h3 : 0 < √((n i : ℝ) + 1) := Real.sqrt_pos.mpr (by positivity)
  have h4 : (0 : ℝ) < √2 := Real.sqrt_pos.mpr (by norm_num)
  field_simp

/-- `√nᵢ c(n - eᵢ)ᵢ = 2 nᵢ c(n)ᵢ / √2` (both sides vanish when `nᵢ = 0`). -/
lemma eigenCoeff_update_pred (i : Fin d) (n : Fin d → ℕ) :
    √(n i : ℝ) * Q.eigenCoeff (Function.update n i (n i - 1)) i
      = (√2)⁻¹ * (2 * n i) * Q.eigenCoeff n i := by
  rcases Nat.eq_zero_or_pos (n i) with h0 | hpos
  · simp [h0]
  · obtain ⟨m, hm⟩ : ∃ m, n i = m + 1 := ⟨n i - 1, by omega⟩
    simp only [eigenCoeff_eq, Function.update_self, hm, Nat.add_sub_cancel]
    have hp : 0 < (2 : ℝ) ^ m * (m)! * √π * Q.ξ i :=
      mul_pos (mul_pos (mul_pos (by positivity) (by positivity)) (by positivity)) (Q.ξ_pos i)
    have h1 : (2 : ℝ) ^ (m + 1) * ((m + 1)! : ℝ) * √π * Q.ξ i
        = (2 * ((m : ℝ) + 1)) * (2 ^ m * (m)! * √π * Q.ξ i) := by
      push_cast [Nat.factorial_succ]
      ring
    rw [h1, Real.sqrt_mul (by positivity : (0 : ℝ) ≤ 2 * ((m : ℝ) + 1)),
      Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
    have h2 := Real.sqrt_pos.mpr hp
    have h3 : 0 < √((m : ℝ) + 1) := Real.sqrt_pos.mpr (by positivity)
    have h4 : (0 : ℝ) < √2 := Real.sqrt_pos.mpr (by norm_num)
    push_cast
    field_simp
    rw [Real.sq_sqrt (by positivity), Real.sq_sqrt (by norm_num)]

/-- The eigenfunction labelled by the integer quantum numbers `n : Fin d → ℕ`, defined as a product
  of (physicist's) Hermite polynomials multiplying a Gaussian with covariance controlled
  by the characteristic lengths, `Q.ξ`. -/
def eigenfunction : 𝓢(Space d, ℂ) :=
  compCLMOfContinuousLinearEquiv ℂ Q.ξEquiv.symm <| smulLeftCLM ℂ
    (fun x ↦ ∏ i, Q.eigenCoeff n i * physHermite (n i) (x i)) (stdGaussian (Space d) ℂ)

lemma eigenfunction_eq :
    Q.eigenfunction n = compCLMOfContinuousLinearEquiv ℂ Q.ξEquiv.symm (smulLeftCLM ℂ
      (fun x ↦ ∏ i, Q.eigenCoeff n i * physHermite (n i) (x i)) (stdGaussian (Space d) ℂ)) := rfl

lemma eigenfunction_apply :
    Q.eigenfunction n x =
      ∏ i, Q.eigenCoeff n i *
        physHermite (n i) (x i / Q.ξ i) * cexp (-2⁻¹ * (x i / Q.ξ i) ^ 2) := by
  rw [eigenfunction_eq, compCLMOfContinuousLinearEquiv_apply, Function.comp_apply,
    smulLeftCLM_apply_apply (by fun_prop)]
  simp [div_eq_mul_inv, prod_mul_distrib, exp_neg, norm_sq_eq, mul_sum, mul_comm, exp_sum]

/-- The `j`th one-dimensional factor of `Q.eigenfunction n`,
  `y ↦ c(n)ⱼ Hₙⱼ(y / ξⱼ) exp(-½ (y / ξⱼ)²)`. -/
def eigenFactor (j : Fin d) (y : ℝ) : ℂ :=
  (Q.eigenCoeff n j : ℂ) * (physHermite (n j) (y / Q.ξ j) : ℂ) *
    cexp (-2⁻¹ * ((y : ℂ) / (Q.ξ j : ℂ)) ^ 2)

lemma eigenFactor_eq (j : Fin d) (y : ℝ) : Q.eigenFactor n j y =
    (Q.eigenCoeff n j : ℂ) * (physHermite (n j) (y / Q.ξ j) : ℂ) *
      cexp (-2⁻¹ * ((y : ℂ) / (Q.ξ j : ℂ)) ^ 2) := rfl

/-- The eigenfunction is the product of its one-dimensional factors. -/
lemma eigenfunction_eq_prod_eigenFactor : Q.eigenfunction n x = ∏ j, Q.eigenFactor n j (x j) := by
  rw [eigenfunction_apply]
  rfl

lemma eigenFactor_differentiable (j : Fin d) : Differentiable ℝ (Q.eigenFactor n j) := by
  unfold eigenFactor
  fun_prop

/-- The derivative of the `j`th factor, `c(n)ⱼ ((2 nⱼ/ξⱼ) Hₙⱼ₋₁(y/ξⱼ) - (y/ξⱼ²) Hₙⱼ(y/ξⱼ))
  exp(-½ (y/ξⱼ)²)`. -/
lemma deriv_eigenFactor (j : Fin d) (y : ℝ) :
    _root_.deriv (Q.eigenFactor n j) y
      = (Q.eigenCoeff n j : ℂ) *
        (((2 * n j / Q.ξ j : ℝ) : ℂ) * (physHermite (n j - 1) (y / Q.ξ j) : ℂ)
          - ((y / Q.ξ j ^ 2 : ℝ) : ℂ) * (physHermite (n j) (y / Q.ξ j) : ℂ)) *
        cexp (-2⁻¹ * ((y : ℂ) / (Q.ξ j : ℂ)) ^ 2) := by
  have h1 : HasDerivAt (fun y : ℝ => y / Q.ξ j) (1 / Q.ξ j) y :=
    ((hasDerivAt_id y).div_const (Q.ξ j)).congr_deriv (by simp)
  have hH : HasDerivAt (fun y : ℝ => (physHermite (n j) (y / Q.ξ j) : ℂ))
      ((2 * n j * physHermite (n j - 1) (y / Q.ξ j) / Q.ξ j : ℝ) : ℂ) y := by
    have h2 := ((physHermite_differentiable (n j)).differentiableAt.hasDerivAt
      (x := y / Q.ξ j)).comp y h1
    rw [deriv_physHermite] at h2
    refine h2.ofReal_comp.congr_deriv ?_
    simp only [Pi.mul_apply, Pi.ofNat_apply, Pi.natCast_apply]
    push_cast
    ring
  have hE : HasDerivAt (fun y : ℝ => cexp (-2⁻¹ * ((y : ℂ) / (Q.ξ j : ℂ)) ^ 2))
      (cexp (-2⁻¹ * ((y : ℂ) / (Q.ξ j : ℂ)) ^ 2) * (-(y / Q.ξ j ^ 2 : ℝ) : ℂ)) y := by
    have h2 := ((((hasDerivAt_id y).ofReal_comp.div_const (Q.ξ j : ℂ)).pow 2).const_mul
      (-2⁻¹ : ℂ)).cexp
    refine h2.congr_deriv ?_
    simp only [Pi.pow_apply, id]
    push_cast
    ring
  have := (hH.const_mul (Q.eigenCoeff n j : ℂ)).mul hE
  unfold eigenFactor
  rw [show (fun y : ℝ => (Q.eigenCoeff n j : ℂ) * (physHermite (n j) (y / Q.ξ j) : ℂ)
        * cexp (-2⁻¹ * ((y : ℂ) / (Q.ξ j : ℂ)) ^ 2))
      = (fun y : ℝ => (Q.eigenCoeff n j : ℂ) * (physHermite (n j) (y / Q.ξ j) : ℂ)) *
        fun y : ℝ => cexp (-2⁻¹ * ((y : ℂ) / (Q.ξ j : ℂ)) ^ 2) from rfl, this.deriv]
  push_cast
  ring

/-- Changing the `i`th quantum number does not change the other factors. -/
lemma eigenFactor_update_of_ne {i j : Fin d} (hj : j ≠ i) (k : ℕ) :
    Q.eigenFactor (Function.update n i k) j = Q.eigenFactor n j := by
  funext y
  simp only [eigenFactor, eigenCoeff_eq]
  rw [Function.update_of_ne hj]

/-- The eigenfunction with the `i`th quantum number changed to `k`, factor `i` set apart. -/
lemma eigenfunction_update_apply (i : Fin d) (k : ℕ) :
    Q.eigenfunction (Function.update n i k) x =
      Q.eigenFactor (Function.update n i k) i (x i) *
        ∏ j ∈ univ.erase i, Q.eigenFactor n j (x j) := by
  rw [eigenfunction_eq_prod_eigenFactor, ← Finset.mul_prod_erase univ _ (Finset.mem_univ i)]
  congr 1
  exact Finset.prod_congr rfl fun j hj => by
    rw [Q.eigenFactor_update_of_ne n (Finset.ne_of_mem_erase hj)]

/-- The `i`th spatial derivative of the eigenfunction, factor `i` differentiated. -/
lemma deriv_eigenfunction_apply (i : Fin d) :
    ∂[i] (Q.eigenfunction n) x =
      _root_.deriv (Q.eigenFactor n i) (x i) * ∏ j ∈ univ.erase i, Q.eigenFactor n j (x j) := by
  have h : (⇑(Q.eigenfunction n) : Space d → ℂ) = fun x => ∏ j, Q.eigenFactor n j (x j) := by
    funext x
    exact Q.eigenfunction_eq_prod_eigenFactor n x
  rw [h, Space.deriv_prod_coord _ (Q.eigenFactor_differentiable n)]

/-!
### A.3. Eigenstates
-/

/-- `Q.eigenfunction n` as an element of the Schwartz submodule of the Hilbert space. -/
def eigenstate : SchwartzSubmodule d := schwartzEquiv _ (Q.eigenfunction n)

lemma eigenstate_eq : Q.eigenstate n = schwartzEquiv _ (Q.eigenfunction n) := rfl

/-- The energy eigenstates are orthonormal. -/
@[simp, sorryful]
lemma eigenstates_orthonormal : ⟪(Q.eigenstate n : Q.HS), Q.eigenstate n'⟫_ℂ = δ[n,n'] :=
  -- It might help to first prove an analogue of
  -- `MeasureTheory.integral_fin_nat_prod_(volume_)eq_prod` for `Space d` in order to split
  -- `∫ x : Space d, Π i : Fin d, fᵢ (x i) = ∏ i : Fin d, ∫ xᵢ : ℝ, fᵢ xᵢ`, using `Space.equivPi`.
  sorry

/-!

## B. The ladder operators on the eigenfunctions

-/

/-- `aᵢ† ψₙ = √(nᵢ + 1) ψₙ₊ₑᵢ`: the raising operator raises the `i`th quantum number by one. -/
lemma raising_eigenfunction (i : Fin d) (n : Fin d → ℕ) :
    Q.raising i (Q.eigenfunction n) =
      ((Real.sqrt (n i + 1) : ℝ) : ℂ) • Q.eigenfunction (Function.update n i (n i + 1)) := by
  ext x
  simp only [raising_eq, _root_.smul_apply, _root_.sub_apply, positionCLM_apply, momentumCLM_apply,
    smul_eq_mul]
  rw [Q.deriv_eigenfunction_apply, Q.eigenfunction_update_apply,
    Q.eigenfunction_eq_prod_eigenFactor n x, ← Finset.mul_prod_erase univ _ (Finset.mem_univ i),
    Q.deriv_eigenFactor]
  set P : ℂ := ∏ j ∈ univ.erase i, Q.eigenFactor n j (x j) with hP
  simp only [eigenFactor, Function.update_self]
  have hcc := congrArg (Complex.ofReal) (Q.eigenCoeff_update_succ i n)
  have hHc := congrArg (Complex.ofReal) (physHermite_succ_apply' (n i) (x i / Q.ξ i))
  push_cast at hcc hHc ⊢
  rw [hHc]
  have hξ := Q.ξ_ofReal_ne_zero i
  have hℏ := ℏ_ofReal_ne_zero
  have hs : ((Real.sqrt 2 : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (by norm_num)).ne'
  have hcc' : ((Real.sqrt 2 : ℝ) : ℂ) * (((Real.sqrt ((n i : ℝ) + 1) : ℝ) : ℂ)
      * (Q.eigenCoeff (Function.update n i (n i + 1)) i : ℂ)) = (Q.eigenCoeff n i : ℂ) := by
    rw [hcc, mul_inv_cancel_left₀ hs]
  field_simp
  linear_combination ((Q.eigenCoeff n i : ℂ) * P * (2 * ((Q.ξ i : ℝ) : ℂ) * ((n i : ℕ) : ℂ)
      * ((physHermite (n i - 1) (x i / Q.ξ i) : ℝ) : ℂ)
      - ((x i : ℝ) : ℂ) * ((physHermite (n i) (x i / Q.ξ i) : ℝ) : ℂ))) * I_sq
    + (-2 * P * (((x i : ℝ) : ℂ) * ((physHermite (n i) (x i / Q.ξ i) : ℝ) : ℂ)
      - ((Q.ξ i : ℝ) : ℂ) * ((n i : ℕ) : ℂ)
        * ((physHermite (n i - 1) (x i / Q.ξ i) : ℝ) : ℂ))) * hcc'

/-- `aᵢ ψₙ = √nᵢ ψₙ₋ₑᵢ`: the lowering operator lowers the `i`th quantum number by one (and
  annihilates the eigenfunction when `nᵢ = 0`, since `√0 = 0`). -/
lemma lowering_eigenfunction (i : Fin d) (n : Fin d → ℕ) :
    Q.lowering i (Q.eigenfunction n) =
      ((Real.sqrt (n i) : ℝ) : ℂ) • Q.eigenfunction (Function.update n i (n i - 1)) := by
  ext x
  simp only [lowering_eq, _root_.smul_apply, _root_.add_apply, positionCLM_apply, momentumCLM_apply,
    smul_eq_mul]
  rw [Q.deriv_eigenfunction_apply, Q.eigenfunction_update_apply,
    Q.eigenfunction_eq_prod_eigenFactor n x, ← Finset.mul_prod_erase univ _ (Finset.mem_univ i),
    Q.deriv_eigenFactor]
  set P : ℂ := ∏ j ∈ univ.erase i, Q.eigenFactor n j (x j) with hP
  simp only [eigenFactor, Function.update_self]
  have hcc := congrArg (Complex.ofReal) (Q.eigenCoeff_update_pred i n)
  push_cast at hcc ⊢
  have hξ := Q.ξ_ofReal_ne_zero i
  have hℏ := ℏ_ofReal_ne_zero
  have hs : ((Real.sqrt 2 : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (by norm_num)).ne'
  have hcc' : ((Real.sqrt 2 : ℝ) : ℂ) * (((Real.sqrt (n i : ℝ) : ℝ) : ℂ)
      * (Q.eigenCoeff (Function.update n i (n i - 1)) i : ℂ))
      = 2 * ((n i : ℕ) : ℂ) * (Q.eigenCoeff n i : ℂ) := by
    rw [hcc]
    field_simp
  field_simp
  linear_combination (-((Q.eigenCoeff n i : ℂ) * P * (2 * ((Q.ξ i : ℝ) : ℂ) * ((n i : ℕ) : ℂ)
      * ((physHermite (n i - 1) (x i / Q.ξ i) : ℝ) : ℂ)
      - ((x i : ℝ) : ℂ) * ((physHermite (n i) (x i / Q.ξ i) : ℝ) : ℂ)))) * I_sq
    + (-(((Q.ξ i : ℝ) : ℂ) * P * ((physHermite (n i - 1) (x i / Q.ξ i) : ℝ) : ℂ))) * hcc'

/-- The ground state is annihilated by every lowering operator. -/
lemma lowering_eigenfunction_zero (i : Fin d) : Q.lowering i (Q.eigenfunction 0) = 0 := by
  rw [lowering_eigenfunction]
  simp

/-- `Nᵢ ψₙ = nᵢ ψₙ`: the eigenfunctions are eigenfunctions of the number operators. -/
lemma number_eigenfunction (i : Fin d) (n : Fin d → ℕ) :
    Q.number i (Q.eigenfunction n) = ((n i : ℕ) : ℂ) • Q.eigenfunction n := by
  rw [number_eq, ContinuousLinearMap.comp_apply, lowering_eigenfunction, map_smul,
    raising_eigenfunction, smul_smul, Function.update_self, Function.update_idem]
  rcases Nat.eq_zero_or_pos (n i) with h0 | hpos
  · simp [h0]
  · rw [Nat.sub_add_cancel hpos, Function.update_eq_self]
    congr 1
    rw [show (((n i - 1 : ℕ) : ℝ) + 1) = ((n i : ℕ) : ℝ) by exact_mod_cast Nat.sub_add_cancel hpos,
      ← Complex.ofReal_mul, Real.mul_self_sqrt (by positivity)]
    rfl

/-!

## C. The eigenvalue equation

-/

/-- `H_N ψₙ = Eₙ ψₙ` for the Hamiltonian in terms of the number operators. -/
lemma numberHamiltonianCLM_eigenfunction :
    Q.numberHamiltonianCLM (Q.eigenfunction n) = (Q.eigenEnergy n : ℂ) • Q.eigenfunction n := by
  simp only [numberHamiltonianCLM_eq, FunLike.coe_sum, Finset.sum_apply, _root_.smul_apply,
    _root_.add_apply, ContinuousLinearMap.id_apply, number_eigenfunction, eigenEnergy_eq]
  simp only [← add_smul, smul_smul, ← Finset.sum_smul, ofReal_sum]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  push_cast
  ring

/-- The eigenstates lie in the domain of the kinetic-plus-potential Hamiltonian. -/
lemma eigenstate_mem_hamiltonian_domain : (Q.eigenstate n : Q.HS) ∈ Q.hamiltonian.domain :=
  Q.numberHamiltonian_le_hamiltonian.1 (Q.eigenstate n).2

/-- `H ψₙ = Eₙ ψₙ`: the time-independent Schrodinger equation for the eigenstates, with the
  kinetic-plus-potential Hamiltonian of `Basic.lean`. -/
lemma hamiltonian_eigenstate (h : (Q.eigenstate n : Q.HS) ∈ Q.hamiltonian.domain) :
    Q.hamiltonian ⟨Q.eigenstate n, h⟩ = (Q.eigenEnergy n : ℂ) • (Q.eigenstate n : Q.HS) := by
  have h1 := Q.numberHamiltonian_le_hamiltonian.2 (x := Q.eigenstate n) (y := ⟨Q.eigenstate n, h⟩)
    rfl
  rw [← h1, eigenstate_eq, numberHamiltonian_apply, LinearEquiv.symm_apply_apply,
    numberHamiltonianCLM_eigenfunction, map_smul, Submodule.coe_smul]

end HarmonicOscillator
end QuantumMechanics
end
