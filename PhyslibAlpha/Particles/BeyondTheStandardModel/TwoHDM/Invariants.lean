/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import PhyslibAlpha.Particles.BeyondTheStandardModel.TwoHDM.EffectivePotential
public import PhyslibAlpha.Particles.BeyondTheStandardModel.TwoHDM.SwapDoublet
public import PhyslibAlpha.Particles.BeyondTheStandardModel.TwoHDM.GaugeSlice
public import PhyslibAlpha.Particles.BeyondTheStandardModel.TwoHDM.OrbitRepresentative
public import PhyslibAlpha.Particles.BeyondTheStandardModel.TwoHDM.ChargeBalance
public import Mathlib.Algebra.MvPolynomial.Funext
public import Mathlib.Algebra.MvPolynomial.Monad
public import Mathlib.Algebra.MvPolynomial.Division
public import Mathlib.RingTheory.MvPolynomial.Tower
public import Mathlib.Analysis.Real.Pi.Irrational
/-!
# The two Higgs doublet potential as a polynomial in the gauge invariants

## i. Overview

In the *bilinear formalism* of the two Higgs doublet model (hep-ph/0605184
[ref: arxiv_hep_ph_0605184]) the four gauge-invariant bilinears — the Gram vector `gramVector`
— describe the gauge orbits of the configuration space. This file proves the corresponding
statement for the potential: every
gauge-invariant polynomial effective potential is a polynomial in these four gauge-invariant
bilinears.

The proof gauge-fixes the potential to the polynomial family of orbit representatives `repHiggs X`
and runs the following physical pipeline:

1. **Charge balancing.** Invariance under the gauge torus forces the potential, written in
   hypercharge eigen-coordinates, to be supported only on hypercharge-neutral monomials.
2. **Generation.** Every neutral monomial is a product of the five neutral gauge-invariant
   quadratic bilinears, so the potential is a polynomial in them.
3. **Clearing the norms.** A power of `‖Φ1‖²` (resp. `‖Φ2‖²`, via the doublet swap) times the
   potential is a genuine polynomial in the Gram vector.
4. **Coprimality.** `‖Φ1‖²` and `‖Φ2‖²` are coprime in the (algebraically independent) Gram ring,
   which removes these factors and yields the Gram polynomial.

## ii. Key results

* `exists_polynomial_repHiggs_sliceBilinear` — on gauge representatives, the potential is a
  polynomial in the five real gauge-invariant bilinears.
* `exists_normSq_Φ1_clearing`, `exists_normSq_Φ2_clearing` — a power of `‖Φ1‖²` (resp. `‖Φ2‖²`)
  times the potential is a polynomial in the Gram vector.
* `exists_polynomial_on_repHiggs` — the potential on representatives is a polynomial in the Gram
  vector.
* `effectivePotential_is_polynomial_gramVector` — a gauge-invariant polynomial potential is a
  polynomial in the four gauge-invariant bilinears.

## iii. Table of contents

* A. Gauge-torus invariance of the potential on the slice
* B. Hypercharge eigen-coordinates and charge balancing
* C. Generation by the neutral gauge-invariant bilinears
* D. The potential on representatives as a polynomial in the bilinears
* E. Clearing the `‖Φ1‖²` and `‖Φ2‖²` factors
* F. Independence and coprimality of the Gram invariants
* G. The gauge-invariant potential as a polynomial in the Gram vector

## iv. References

* The bilinear formalism: https://arxiv.org/abs/hep-ph/0605184. [ref: arxiv_hep_ph_0605184]

Mathematically the result is the first fundamental theorem of invariant theory for `SU(2)`
acting on two doublets in `ℂ²`.
-/

@[expose] public section

noncomputable section

namespace TwoHiggsDoublet
open InnerProductSpace
open StandardModel

namespace EffectivePotential

open MvPolynomial in
/-- Pushing an evaluation through an `aeval` substitution. -/
lemma eval_aeval_comp {R : Type*} [CommRing R] {κ ι : Type*} (x : ι → R)
    (f : κ → MvPolynomial ι R) (G : MvPolynomial κ R) :
    eval x (aeval f G) = eval (fun i => eval x (f i)) G := by
  rw [show (aeval f) G = bind₁ f G from rfl, ← aeval_eq_eval x, aeval_bind₁]
  simp [aeval_eq_eval]

/-!
## A. Gauge-torus invariance of the potential on the slice

Invariance of the potential under the gauge torus forces the slice polynomial `P` to be invariant
under the hypercharge rotations of its variables: the Cartan rotation `cartanSubst` and the residual
`U(1)` rotation `residualSubst`.
-/

open MvPolynomial in
/-- The Cartan hypercharge rotation of the slice parameters, as a substitution of the polynomial
  variables. -/
noncomputable def cartanSubst (u : unitary ℂ) : Fin 6 → MvPolynomial (Fin 6) ℝ :=
  ![C (u : ℂ).re * X 0 - C (u : ℂ).im * X 1, C (u : ℂ).im * X 0 + C (u : ℂ).re * X 1,
    C (u : ℂ).re * X 2 - C (u : ℂ).im * X 3, C (u : ℂ).im * X 2 + C (u : ℂ).re * X 3,
    C (u : ℂ).re * X 4 + C (u : ℂ).im * X 5, C (u : ℂ).re * X 5 - C (u : ℂ).im * X 4]

open MvPolynomial in
lemma eval_cartanSubst (u : unitary ℂ) (a : Fin 6 → ℝ) :
    (fun k => MvPolynomial.eval a (cartanSubst u k)) = cartanRotParam u a := by
  funext k
  fin_cases k <;>
    simp [cartanSubst, cartanRotParam, Complex.mul_re, Complex.mul_im] <;> ring

open MvPolynomial in
/-- Gauge (Cartan) invariance of the potential forces the slice polynomial to be invariant under the
  hypercharge rotation of its variables. -/
lemma aeval_cartanSubst_eq {V : EffectivePotential} (hI : IsInvariant V)
    {P : MvPolynomial (Fin 6) ℝ} (hP : ∀ a, V (sliceR a) = P.eval a) (u : unitary ℂ) :
    aeval (cartanSubst u) P = P := by
  apply MvPolynomial.funext
  intro a
  have hcomp : eval a (aeval (cartanSubst u) P) = P.eval (fun k => eval a (cartanSubst u k)) := by
    rw [aeval_def, algebraMap_eq, ← MvPolynomial.eval_assoc]
    rfl
  rw [hcomp, eval_cartanSubst, ← hP (cartanRotParam u a), ← gaugeCartan_smul_sliceR,
    hI (StandardModel.GaugeGroupI.gaugeCartan u), hP a]

open MvPolynomial in
/-- The residual `U(1)` rotation of the perpendicular parameter, as a substitution. -/
noncomputable def residualSubst (c : unitary ℂ) : Fin 6 → MvPolynomial (Fin 6) ℝ :=
  ![X 0, X 1, X 2, X 3,
    C (((c : ℂ) ^ 6).re) * X 4 - C (((c : ℂ) ^ 6).im) * X 5,
    C (((c : ℂ) ^ 6).im) * X 4 + C (((c : ℂ) ^ 6).re) * X 5]

open MvPolynomial in
lemma eval_residualSubst (c : unitary ℂ) (a : Fin 6 → ℝ) :
    (fun k => MvPolynomial.eval a (residualSubst c k)) = resRotParam c a := by
  funext k
  fin_cases k <;> simp [residualSubst, resRotParam, Complex.mul_re, Complex.mul_im]
  ring

open MvPolynomial in
/-- Gauge (residual `U(1)`) invariance forces the slice polynomial to be invariant under the
  perpendicular rotation of its variables. -/
lemma aeval_residualSubst_eq {V : EffectivePotential} (hI : IsInvariant V)
    {P : MvPolynomial (Fin 6) ℝ} (hP : ∀ a, V (sliceR a) = P.eval a) (c : unitary ℂ) :
    aeval (residualSubst c) P = P := by
  apply MvPolynomial.funext
  intro a
  have hcomp : eval a (aeval (residualSubst c) P) = P.eval
      (fun k => eval a (residualSubst c k)) := by
    rw [aeval_def, algebraMap_eq, ← MvPolynomial.eval_assoc]; rfl
  rw [hcomp, eval_residualSubst, ← hP (resRotParam c a), ← ofU1Subgroup_smul_sliceR,
    hI (StandardModel.GaugeGroupI.ofU1Subgroup c), hP a]

/-!
## B. Hypercharge eigen-coordinates and charge balancing

Changing to hypercharge eigen-coordinates `z, z̄, w₀, w̄₀, w₁, w̄₁` diagonalises the gauge-torus
rotation into a scaling by the hypercharges `cartanCharge` (Cartan) and `hyperCharge` (residual).
Feeding an infinite-order phase into the invariance from part A shows that every monomial of the
potential carrying nonzero hypercharge has vanishing coefficient.
-/

open MvPolynomial in
/-- Change to hypercharge eigen-coordinates: `aₖ` in terms of `z, z̄, w₀, w̄₀, w₁, w̄₁`
  (indices `0..5`). This diagonalises the gauge-torus rotation into a scaling. -/
noncomputable def hyperchargeEigen : Fin 6 → MvPolynomial (Fin 6) ℂ :=
  ![(X 0 + X 1) * C (1 / 2), (X 0 - X 1) * C (-Complex.I / 2),
    (X 2 + X 3) * C (1 / 2), (X 2 - X 3) * C (-Complex.I / 2),
    (X 4 + X 5) * C (1 / 2), (X 4 - X 5) * C (-Complex.I / 2)]

open MvPolynomial in
/-- The Cartan hypercharge, diagonal in eigen-coordinates: charges `(1,-1,1,-1,-1,1)`. -/
noncomputable def diagCartan (u : unitary ℂ) : Fin 6 → MvPolynomial (Fin 6) ℂ :=
  ![C (u : ℂ) * X 0, C (star (u : ℂ)) * X 1, C (u : ℂ) * X 2, C (star (u : ℂ)) * X 3,
    C (star (u : ℂ)) * X 4, C (u : ℂ) * X 5]

open MvPolynomial in
/-- The residual `U(1)`, diagonal in eigen-coordinates: only the perpendicular pair is charged. -/
noncomputable def diagRes (c : unitary ℂ) : Fin 6 → MvPolynomial (Fin 6) ℂ :=
  ![X 0, X 1, X 2, X 3, C ((c : ℂ) ^ 6) * X 4, C (star ((c : ℂ) ^ 6)) * X 5]

open MvPolynomial in
/-- Conjugation identity: the diagonal Cartan scaling, pulled back through the eigen-coordinate
  change, is the (complexified) Cartan rotation substitution. -/
lemma bind₁_diagCartan_hyperchargeEigen (u : unitary ℂ) (k : Fin 6) :
    bind₁ (diagCartan u) (hyperchargeEigen k)
      = bind₁ hyperchargeEigen (map (algebraMap ℝ ℂ) (cartanSubst u k)) := by
  apply MvPolynomial.funext
  intro x
  fin_cases k <;>
    simp only [hyperchargeEigen, diagCartan, cartanSubst, Fin.isValue] <;>
    (apply Complex.ext <;>
      simp [Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.mul_re,
        Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
        Complex.conj_re, Complex.conj_im] <;> ring)

open MvPolynomial in
/-- Conjugation identity for the residual `U(1)`. -/
lemma bind₁_diagRes_hyperchargeEigen (c : unitary ℂ) (k : Fin 6) :
    bind₁ (diagRes c) (hyperchargeEigen k)
      = bind₁ hyperchargeEigen (map (algebraMap ℝ ℂ) (residualSubst c k)) := by
  apply MvPolynomial.funext
  intro x
  simp only [diagRes, residualSubst]
  generalize (c : ℂ) ^ 6 = μ
  fin_cases k <;>
    simp only [hyperchargeEigen, Fin.isValue] <;>
    (apply Complex.ext <;>
      simp [Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.mul_re,
        Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
        Complex.conj_re, Complex.conj_im] <;> ring)

/-- The Cartan hypercharges of `z, z̄, w₀, w̄₀, w₁, w̄₁`. -/
def cartanCharge : Fin 6 → ℤ := ![1, -1, 1, -1, -1, 1]

/-- The residual-`U(1)` hypercharges (only the perpendicular pair is charged). -/
def hyperCharge : Fin 6 → ℤ := ![0, 0, 0, 0, 1, -1]

open MvPolynomial in
/-- The slice potential, complexified and written in hypercharge eigen-coordinates. -/
noncomputable def Qslice (P : MvPolynomial (Fin 6) ℝ) : MvPolynomial (Fin 6) ℂ :=
  bind₁ hyperchargeEigen (map (algebraMap ℝ ℂ) P)

open MvPolynomial in
/-- The Cartan diagonal in the charge form consumed by the charge-balancing engine. -/
lemma diagCartan_eq (u : unitary ℂ) :
    diagCartan u = fun i => C ((u : ℂ) ^ (cartanCharge i)) * X i := by
  have hinv : star (u : ℂ) = (u : ℂ) ^ (-1 : ℤ) := by
    rw [zpow_neg_one]; exact (inv_eq_of_mul_eq_one_right u.2.2).symm
  funext i
  fin_cases i <;> simp [diagCartan, cartanCharge, hinv]

open MvPolynomial in
/-- The residual diagonal in the charge form consumed by the engine. -/
lemma diagRes_eq (c : unitary ℂ) :
    diagRes c = fun i => C (((c : ℂ) ^ 6) ^ (hyperCharge i)) * X i := by
  have hinv : star ((c : ℂ) ^ 6) = ((c : ℂ) ^ 6) ^ (-1 : ℤ) := by
    rw [zpow_neg_one]
    refine (inv_eq_of_mul_eq_one_right ?_).symm
    rw [star_pow, ← mul_pow, c.2.2, one_pow]
  funext i
  fin_cases i <;> simp [diagRes, hyperCharge, hinv]

open MvPolynomial in
/-- In eigen-coordinates, the Cartan hypercharge acts by the diagonal scaling, and the slice
  potential is invariant under it. -/
lemma bind₁_diagCartan_Qslice {V : EffectivePotential} (hI : IsInvariant V)
    {P : MvPolynomial (Fin 6) ℝ} (hP : ∀ a, V (sliceR a) = P.eval a) (u : unitary ℂ) :
    bind₁ (diagCartan u) (Qslice P) = Qslice P := by
  simp only [Qslice]
  rw [bind₁_bind₁]
  simp only [bind₁_diagCartan_hyperchargeEigen]
  rw [← bind₁_bind₁, ← map_bind₁]
  congr 2
  exact aeval_cartanSubst_eq hI hP u

open MvPolynomial in
/-- Likewise for the residual `U(1)`. -/
lemma bind₁_diagRes_Qslice {V : EffectivePotential} (hI : IsInvariant V)
    {P : MvPolynomial (Fin 6) ℝ} (hP : ∀ a, V (sliceR a) = P.eval a) (c : unitary ℂ) :
    bind₁ (diagRes c) (Qslice P) = Qslice P := by
  simp only [Qslice]
  rw [bind₁_bind₁]
  simp only [bind₁_diagRes_hyperchargeEigen]
  rw [← bind₁_bind₁, ← map_bind₁]
  congr 2
  exact aeval_residualSubst_eq hI hP c

/-- There is a gauge phase of infinite order (`exp i`), needed to run charge balancing. -/
lemma exists_infiniteOrder_unitary :
    ∃ ω : unitary ℂ, ∀ n : ℤ, (ω : ℂ) ^ n = 1 → n = 0 := by
  have key : star (Complex.exp Complex.I) * Complex.exp Complex.I = 1 := by
    rw [Complex.star_def, ← Complex.exp_conj, Complex.conj_I, ← Complex.exp_add]; simp
  have key2 : Complex.exp Complex.I * star (Complex.exp Complex.I) = 1 := by
    rw [Complex.star_def, ← Complex.exp_conj, Complex.conj_I, ← Complex.exp_add]; simp
  refine ⟨⟨Complex.exp Complex.I, key, key2⟩, fun n hn => ?_⟩
  simp only at hn
  rw [← Complex.exp_int_mul, Complex.exp_eq_one_iff] at hn
  obtain ⟨k, hk⟩ := hn
  have hc : (n : ℂ) = (k : ℂ) * (2 * Real.pi) := by
    have hI : (Complex.I) ≠ 0 := Complex.I_ne_zero
    apply mul_right_cancel₀ hI
    rw [hk]; ring
  have hr : (n : ℝ) = (k : ℝ) * (2 * Real.pi) := by exact_mod_cast hc
  rcases eq_or_ne k 0 with hk0 | hk0
  · simp [hk0] at hr; exact_mod_cast hr
  · exfalso
    have h2k : (2 * (k : ℝ)) ≠ 0 := by
      simp only [mul_ne_zero_iff]; exact ⟨two_ne_zero, by exact_mod_cast hk0⟩
    have hpi : Real.pi = (n : ℝ) / (2 * (k : ℝ)) := by rw [eq_div_iff h2k, hr]; ring
    exact irrational_pi.ne_rat ((n : ℚ) / (2 * (k : ℚ))) (by rw [hpi]; push_cast; ring)

open MvPolynomial in
/-- **Hypercharge balancing.** Every monomial of the slice potential `Qslice P` (in eigen-
  coordinates) that carries nonzero Cartan or residual hypercharge has vanishing coefficient. -/
lemma coeff_Qslice_eq_zero {V : EffectivePotential} (hI : IsInvariant V)
    {P : MvPolynomial (Fin 6) ℝ} (hP : ∀ a, V (sliceR a) = P.eval a) (m : Fin 6 →₀ ℕ)
    (hm : (∑ i ∈ m.support, (m i : ℤ) * cartanCharge i ≠ 0) ∨
          (∑ i ∈ m.support, (m i : ℤ) * hyperCharge i ≠ 0)) :
    (Qslice P).coeff m = 0 := by
  obtain ⟨ω, hω⟩ := exists_infiniteOrder_unitary
  have hω0 : (ω : ℂ) ≠ 0 := by intro h; have := ω.2.1; rw [h] at this; simp at this
  rcases hm with hmA | hmB
  · refine coeff_eq_zero_of_charge_ne_zero cartanCharge (ω : ℂ) hω0 hω ?_ hmA
    have h := bind₁_diagCartan_Qslice hI hP ω
    rwa [diagCartan_eq] at h
  · have hω6 : ((ω : ℂ) ^ 6) ≠ 0 := pow_ne_zero 6 hω0
    have hroot6 : ∀ n : ℤ, ((ω : ℂ) ^ 6) ^ n = 1 → n = 0 := by
      intro n hn
      rw [← zpow_natCast (ω : ℂ) 6, ← zpow_mul] at hn
      have := hω _ hn; omega
    refine coeff_eq_zero_of_charge_ne_zero hyperCharge ((ω : ℂ) ^ 6) hω6 hroot6 ?_ hmB
    have h := bind₁_diagRes_Qslice hI hP ω
    rwa [diagRes_eq] at h

/-!
## C. Generation by the neutral gauge-invariant bilinears

The hypercharge-neutral monomials of `Qslice P` are exactly the products of the five neutral
quadratic bilinears `z z̄, w₀ w̄₀, z w̄₀, z̄ w₀, w₁ w̄₁` — the gauge invariants.
This is the (abelian)generation step: combined Cartan- and residual-neutrality of a
monomial forces it to be a product of
these five, because every charged variable carries a unit Cartan charge and the residual charges
come in an exact `±1` pair.
-/

open MvPolynomial in
/-- The five hypercharge-neutral quadratic bilinears in eigen-coordinates:
  `z z̄`, `w₀ w̄₀`, `z w̄₀`, `z̄ w₀`, `w₁ w̄₁`. -/
noncomputable def neutralBilinear : Fin 5 → MvPolynomial (Fin 6) ℂ :=
  ![X 0 * X 1, X 2 * X 3, X 0 * X 3, X 1 * X 2, X 4 * X 5]

/-- The charge of a monomial, summed over the whole index set, equals the sum over its support. -/
lemma charge_univ_eq_support (w : Fin 6 → ℤ) (m : Fin 6 →₀ ℕ) :
    ∑ i, (m i : ℤ) * w i = ∑ i ∈ m.support, (m i : ℤ) * w i := by
  symm
  apply Finset.sum_subset (Finset.subset_univ _)
  intro i _ hi
  rw [Finsupp.notMem_support_iff.mp hi]; simp

/-- A charge sum is additive in the monomial. -/
lemma chargeSum_add (w : Fin 6 → ℤ) (a b : Fin 6 →₀ ℕ) :
    ∑ k, ((a + b) k : ℤ) * w k = (∑ k, (a k : ℤ) * w k) + ∑ k, (b k : ℤ) * w k := by
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  rw [Finsupp.add_apply]; push_cast; ring

/-- The charge sum of a single generator is the charge of that variable. -/
lemma chargeSum_single (w : Fin 6 → ℤ) (i : Fin 6) :
    ∑ k, ((Finsupp.single i (1 : ℕ)) k : ℤ) * w k = w i := by
  simp [Finsupp.single_apply, ite_mul, Finset.sum_ite_eq]

open MvPolynomial in
/-- **Generation.** Every hypercharge-neutral monomial is a product of the five bilinears. -/
lemma monomial_mem_adjoin_neutralBilinear (m : Fin 6 →₀ ℕ)
    (hA : ∑ i, (m i : ℤ) * cartanCharge i = 0) (hB : ∑ i, (m i : ℤ) * hyperCharge i = 0) :
    monomial m (1 : ℂ) ∈ Algebra.adjoin ℂ (Set.range neutralBilinear) := by
  suffices H : ∀ n : ℕ, ∀ m : Fin 6 →₀ ℕ, (∑ i, m i) = n →
      (∑ i, (m i : ℤ) * cartanCharge i = 0) → (∑ i, (m i : ℤ) * hyperCharge i = 0) →
      monomial m (1 : ℂ) ∈ Algebra.adjoin ℂ (Set.range neutralBilinear) by
    exact H (∑ i, m i) m rfl hA hB
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro m hsum hA hB
    -- The reduction step: pair up two variables whose bilinear is a generator.
    have reduce : ∀ i j : Fin 6, i ≠ j → m i ≠ 0 → m j ≠ 0 →
        X i * X j ∈ Algebra.adjoin ℂ (Set.range neutralBilinear) →
        cartanCharge i + cartanCharge j = 0 → hyperCharge i + hyperCharge j = 0 →
        monomial m (1 : ℂ) ∈ Algebra.adjoin ℂ (Set.range neutralBilinear) := by
      intro i j hij hmi hmj hgen hcA hcB
      have hle : Finsupp.single i 1 + Finsupp.single j 1 ≤ m := by
        intro k
        rw [Finsupp.add_apply, Finsupp.single_apply, Finsupp.single_apply]
        by_cases h1 : i = k
        · by_cases h2 : j = k
          · exact absurd (h1.trans h2.symm) hij
          · rw [ite_eq_left h1, ite_eq_right h2]; subst h1
            simpa using Nat.one_le_iff_ne_zero.mpr hmi
        · by_cases h2 : j = k
          · rw [ite_eq_right h1, ite_eq_left h2]; subst h2
            simpa using Nat.one_le_iff_ne_zero.mpr hmj
          · rw [ite_eq_right h1, ite_eq_right h2]; simp
      set m' := m - (Finsupp.single i 1 + Finsupp.single j 1) with hm'def
      have hdecomp : m = (Finsupp.single i 1 + Finsupp.single j 1) + m' := by
        rw [hm'def, add_tsub_cancel_of_le hle]
      -- m' is still neutral
      have hA' : ∑ k, (m' k : ℤ) * cartanCharge k = 0 := by
        have h := hA
        rw [hdecomp, chargeSum_add, chargeSum_add, chargeSum_single, chargeSum_single] at h
        omega
      have hB' : ∑ k, (m' k : ℤ) * hyperCharge k = 0 := by
        have h := hB
        rw [hdecomp, chargeSum_add, chargeSum_add, chargeSum_single, chargeSum_single] at h
        omega
      -- the degree drops by 2
      have hsum' : ∑ k, m' k < n := by
        have e : (∑ k, m k) = (∑ k, (Finsupp.single i 1) k) + (∑ k, (Finsupp.single j 1) k)
            + ∑ k, m' k := by
          rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro k _
          rw [← Finsupp.add_apply, ← Finsupp.add_apply, ← hdecomp]
        have e1 : ∑ k, (Finsupp.single i 1) k = 1 := by
          simp [Finsupp.single_apply, Finset.sum_ite_eq]
        have e2 : ∑ k, (Finsupp.single j 1) k = 1 := by
          simp [Finsupp.single_apply, Finset.sum_ite_eq]
        rw [hsum, e1, e2] at e
        omega
      -- factor and recurse
      have hfact : monomial m (1 : ℂ) = (X i * X j) * monomial m' 1 := by
        rw [hdecomp,
          show (X i : MvPolynomial (Fin 6) ℂ) = monomial (Finsupp.single i 1) 1 from
            by rw [← X_pow_eq_monomial, pow_one],
          show (X j : MvPolynomial (Fin 6) ℂ) = monomial (Finsupp.single j 1) 1 from
            by rw [← X_pow_eq_monomial, pow_one],
          monomial_mul_monomial, monomial_mul_monomial, one_mul, one_mul, add_assoc]
      rw [hfact]
      exact Subalgebra.mul_mem _ hgen (ih (∑ k, m' k) hsum' m' rfl hA' hB')
    -- main case split
    rcases eq_or_ne n 0 with hn0 | hn0
    · -- degree zero: m = 0, monomial is 1
      have hm0 : m = 0 := by
        ext k
        have hk : m k ≤ ∑ i, m i := Finset.single_le_sum (fun _ _ => Nat.zero_le _)
          (Finset.mem_univ k)
        rw [hsum, hn0] at hk
        simpa using Nat.le_zero.mp hk
      rw [hm0]
      have h1 : monomial (0 : Fin 6 →₀ ℕ) (1 : ℂ) = 1 := by simp
      rw [h1]; exact Subalgebra.one_mem _
    · -- positive degree: find a neutral pair
      rcases eq_or_ne (m 4) 0 with h4 | h4
      · -- m 4 = 0; then m 5 = 0 by residual neutrality
        have h5 : m 5 = 0 := by
          have h := hB
          simp [hyperCharge, Fin.sum_univ_six] at h
          omega
        -- Cartan neutrality on {0,1,2,3}: m0 + m2 = m1 + m3
        have hcart : (m 0 : ℤ) + (m 2 : ℤ) = (m 1 : ℤ) + (m 3 : ℤ) := by
          have h := hA
          simp [cartanCharge, Fin.sum_univ_six] at h
          omega
        -- total degree on {0,1,2,3} is n > 0
        have hposL : 0 < m 0 + m 2 := by
          rcases Nat.eq_zero_or_pos (m 0 + m 2) with hc | hc
          · exfalso
            have h02 : m 0 = 0 ∧ m 2 = 0 := by omega
            have h13 : m 1 = 0 ∧ m 3 = 0 := by omega
            have hz : ∑ i, m i = 0 := by
              simp [Fin.sum_univ_six, h02.1, h02.2, h13.1, h13.2, h4, h5]
            rw [hsum] at hz; exact hn0 hz
          · exact hc
        have hposR : 0 < m 1 + m 3 := by omega
        -- choose a positive index in {0,2} and one in {1,3}
        rcases Nat.eq_zero_or_pos (m 0) with hm0 | hm0
        · -- m 0 = 0, so m 2 > 0
          have hm2 : m 2 ≠ 0 := by omega
          rcases Nat.eq_zero_or_pos (m 1) with hm1 | hm1
          · -- m 1 = 0, so m 3 > 0 : pair (2,3) -> neutralBilinear 1
            have hm3 : m 3 ≠ 0 := by omega
            refine reduce 2 3 (by decide) hm2 hm3 ?_ (by decide) (by decide)
            exact Algebra.subset_adjoin ⟨1, rfl⟩
          · -- m 1 > 0 : pair (1,2) -> neutralBilinear 3
            refine reduce 1 2 (by decide) (by omega) hm2 ?_ (by decide) (by decide)
            exact Algebra.subset_adjoin ⟨3, rfl⟩
        · -- m 0 > 0
          rcases Nat.eq_zero_or_pos (m 1) with hm1 | hm1
          · -- m 1 = 0, so m 3 > 0 : pair (0,3) -> neutralBilinear 2
            have hm3 : m 3 ≠ 0 := by omega
            refine reduce 0 3 (by decide) (by omega) hm3 ?_ (by decide) (by decide)
            exact Algebra.subset_adjoin ⟨2, rfl⟩
          · -- m 1 > 0 : pair (0,1) -> neutralBilinear 0
            refine reduce 0 1 (by decide) (by omega) (by omega) ?_ (by decide) (by decide)
            exact Algebra.subset_adjoin ⟨0, rfl⟩
      · -- m 4 > 0; then m 5 > 0 : pair (4,5) -> neutralBilinear 4
        have h5 : m 5 ≠ 0 := by
          have h := hB
          simp [hyperCharge, Fin.sum_univ_six] at h
          omega
        refine reduce 4 5 (by decide) h4 h5 ?_ (by decide) (by decide)
        exact Algebra.subset_adjoin ⟨4, rfl⟩

open MvPolynomial in
/-- The slice potential lies in the subalgebra generated by the five bilinears: every monomial that
  survives is hypercharge-neutral, hence a product of the bilinears. -/
lemma Qslice_mem_adjoin_neutralBilinear {V : EffectivePotential} (hI : IsInvariant V)
    {P : MvPolynomial (Fin 6) ℝ} (hP : ∀ a, V (sliceR a) = P.eval a) :
    Qslice P ∈ Algebra.adjoin ℂ (Set.range neutralBilinear) := by
  rw [(Qslice P).as_sum]
  apply Subalgebra.sum_mem
  intro m hm
  have hcoeff : (Qslice P).coeff m ≠ 0 := MvPolynomial.mem_support_iff.mp hm
  have hsuppA : ∑ i ∈ m.support, (m i : ℤ) * cartanCharge i = 0 := by
    by_contra h0
    exact hcoeff (coeff_Qslice_eq_zero hI hP m (Or.inl h0))
  have hsuppB : ∑ i ∈ m.support, (m i : ℤ) * hyperCharge i = 0 := by
    by_contra h0
    exact hcoeff (coeff_Qslice_eq_zero hI hP m (Or.inr h0))
  have hmono : monomial m (1 : ℂ) ∈ Algebra.adjoin ℂ (Set.range neutralBilinear) :=
    monomial_mem_adjoin_neutralBilinear m
      ((charge_univ_eq_support cartanCharge m).trans hsuppA)
      ((charge_univ_eq_support hyperCharge m).trans hsuppB)
  have hrw : monomial m ((Qslice P).coeff m) = C ((Qslice P).coeff m) * monomial m 1 := by
    rw [C_mul_monomial, mul_one]
  rw [hrw]
  exact Subalgebra.mul_mem _
    (by rw [← MvPolynomial.algebraMap_eq]; exact Subalgebra.algebraMap_mem _ _) hmono

open MvPolynomial in
/-- Consequently the complexified slice potential is `aeval neutralBilinear G` for some polynomial
  `G` in the five bilinears. -/
lemma exists_aeval_neutralBilinear {V : EffectivePotential} (hI : IsInvariant V)
    {P : MvPolynomial (Fin 6) ℝ} (hP : ∀ a, V (sliceR a) = P.eval a) :
    ∃ G : MvPolynomial (Fin 5) ℂ, aeval neutralBilinear G = Qslice P := by
  have h := Qslice_mem_adjoin_neutralBilinear hI hP
  rw [Algebra.adjoin_range_eq_range_aeval ℂ neutralBilinear] at h
  obtain ⟨G, hG⟩ := h
  exact ⟨G, hG⟩

/-!
## D. The potential on representatives as a polynomial in the bilinears

Evaluating at the hypercharge eigen-point of a representative `repHiggs X`, and descending from the
complex value back to its real part, turns the generation result of part C into the statement that
the value `V (repHiggs X)` is a polynomial in the five real gauge-invariant bilinears
`‖Φ1‖², Re⟪⟫, Im⟪⟫, |Φ2₀|², |Φ2₁|²`.
-/

/-- The slice parameters realising `repHiggs X` as a point of the slice family. -/
def aRep (X : Fin 4 → ℝ) : Fin 6 → ℝ := ![X 0, 0, X 1, X 2, X 3, 0]

lemma repHiggs_eq_sliceR (X : Fin 4 → ℝ) : repHiggs X = sliceR (aRep X) := by
  rw [repHiggs_eq_sliceHiggs, sliceR_apply]
  simp [aRep]

/-- The hypercharge eigen-point `(z, z̄, w₀, w̄₀, w₁, w̄₁)` of `repHiggs X`: here `z = X₀` is real,
  `w₀ = X₁ + i X₂` and `w₁ = X₃` is real. -/
noncomputable def eigenPoint (X : Fin 4 → ℝ) : Fin 6 → ℂ :=
  ![(X 0 : ℂ), (X 0 : ℂ), (X 1 : ℂ) + Complex.I * (X 2 : ℂ), (X 1 : ℂ) - Complex.I * (X 2 : ℂ),
    (X 3 : ℂ), (X 3 : ℂ)]

open MvPolynomial in
/-- The eigen-coordinate change sends the eigen-point of `repHiggs X` back to its
  slice parameters. -/
lemma aeval_hyperchargeEigen_eigenPoint (X : Fin 4 → ℝ) (k : Fin 6) :
    aeval (eigenPoint X) (hyperchargeEigen k) = algebraMap ℝ ℂ (aRep X k) := by
  fin_cases k <;>
    simp only [hyperchargeEigen, eigenPoint, aRep, Fin.isValue] <;>
    (apply Complex.ext <;>
      simp [Complex.add_re, Complex.add_im, Complex.mul_re,
        Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im] <;> ring)

open MvPolynomial in
/-- The complexified slice potential, evaluated at the eigen-point of `repHiggs X`, returns the real
  value `V (repHiggs X)`. -/
lemma eval_Qslice_eigenPoint (P : MvPolynomial (Fin 6) ℝ) (X : Fin 4 → ℝ) :
    eval (eigenPoint X) (Qslice P) = algebraMap ℝ ℂ (P.eval (aRep X)) := by
  rw [Qslice, ← aeval_eq_eval, aeval_bind₁,
    show (fun i => aeval (eigenPoint X) (hyperchargeEigen i))
        = (fun i => (Algebra.ofId ℝ ℂ) (aRep X i)) from
      funext (fun i => (aeval_hyperchargeEigen_eigenPoint X i).trans
        (Algebra.ofId_apply ℂ (aRep X i)).symm),
    MvPolynomial.aeval_map_algebraMap ℂ, ← MvPolynomial.comp_aeval]
  simp [aeval_eq_eval, Algebra.ofId_apply]

open MvPolynomial in
/-- The real part of a complex polynomial, taken coefficient-wise. -/
noncomputable def realPart (H : MvPolynomial (Fin 5) ℂ) : MvPolynomial (Fin 5) ℝ :=
  .ofCoeff (Finsupp.mapRange Complex.re Complex.zero_re (AddMonoidAlgebra.coeff H))

open MvPolynomial in
@[simp] lemma realPart_coeff (H : MvPolynomial (Fin 5) ℂ) (m : Fin 5 →₀ ℕ) :
    (realPart H).coeff m = (H.coeff m).re := by
  simp only [realPart, AddMonoidAlgebra.coeff_ofCoeff, Finsupp.mapRange_apply]

open MvPolynomial in
lemma realPart_C (a : ℂ) : realPart (C a) = C a.re := by
  ext m; rw [realPart_coeff, coeff_C, coeff_C]; split_ifs <;> simp

open MvPolynomial in
lemma realPart_add (p q : MvPolynomial (Fin 5) ℂ) :
    realPart (p + q) = realPart p + realPart q := by
  ext m; simp [Complex.add_re]

open MvPolynomial in
lemma realPart_mul_X (p : MvPolynomial (Fin 5) ℂ) (i : Fin 5) :
    realPart (p * X i) = realPart p * X i := by
  ext m
  rw [realPart_coeff, coeff_mul_X', coeff_mul_X', realPart_coeff]
  split_ifs <;> simp

open MvPolynomial in
/-- Evaluating a complex polynomial at a real point and taking the real part is the same as
  evaluating its real part. -/
lemma realPart_eval (H : MvPolynomial (Fin 5) ℂ) (y : Fin 5 → ℝ) :
    (eval (fun j => (↑(y j) : ℂ)) H).re = (realPart H).eval y := by
  induction H using MvPolynomial.induction_on with
  | C a => rw [realPart_C]; simp
  | add p q hp hq => rw [realPart_add, map_add, map_add, Complex.add_re, hp, hq]
  | mul_X p i hp =>
    rw [realPart_mul_X, map_mul, map_mul, eval_X, eval_X, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, mul_zero, sub_zero, hp]

/-- The five real gauge-invariant bilinears, evaluated at `repHiggs X`:
  `‖Φ1‖², Re⟪⟫, Im⟪⟫, |Φ2₀|², |Φ2₁|²`. -/
def sliceBilinear (X : Fin 4 → ℝ) : Fin 5 → ℝ :=
  ![X 0 ^ 2, X 0 * X 1, X 0 * X 2, X 1 ^ 2 + X 2 ^ 2, X 3 ^ 2]

open MvPolynomial in
/-- The complex substitution expressing each bilinear, at the eigen-point, through the real
  generators (the off-diagonal pair `z w̄₀, z̄ w₀` mix `Re⟪⟫` and `Im⟪⟫`). -/
noncomputable def transf : Fin 5 → MvPolynomial (Fin 5) ℂ :=
  ![X 0, X 3, X 1 - C Complex.I * X 2, X 1 + C Complex.I * X 2, X 4]

open MvPolynomial in
/-- The bilinears at the eigen-point of `repHiggs X` are the real generators,
  read through `transf`. -/
lemma neutralBilinear_eval_eigenPoint (X : Fin 4 → ℝ) (i : Fin 5) :
    eval (eigenPoint X) (neutralBilinear i)
      = eval (fun j => (↑(sliceBilinear X j) : ℂ)) (transf i) := by
  fin_cases i <;>
    simp only [neutralBilinear, transf, eigenPoint, sliceBilinear, Fin.isValue] <;>
    (apply Complex.ext <;>
      simp [pow_two, Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.mul_re,
        Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im] <;> ring)

open MvPolynomial in
/-- **The potential on representatives, in the bilinears.** A gauge-invariant polynomial potential,
  on the representative family, is a polynomial in the five real gauge-invariant bilinears
  `‖Φ1‖², Re⟪⟫, Im⟪⟫, |Φ2₀|², |Φ2₁|²`. -/
lemma exists_polynomial_repHiggs_sliceBilinear {V : EffectivePotential} {n : ℕ}
    (hI : IsInvariant V) (h : HasMaxMassDimLE V n) :
    ∃ p : MvPolynomial (Fin 5) ℝ, ∀ X : Fin 4 → ℝ, V (repHiggs X) = p.eval (sliceBilinear X) := by
  obtain ⟨P, hP⟩ := h.exists_comp_linear_poly sliceR
  obtain ⟨G, hG⟩ := exists_aeval_neutralBilinear hI hP
  refine ⟨realPart (aeval transf G), fun X => ?_⟩
  have hval : (algebraMap ℝ ℂ) (V (repHiggs X))
      = eval (fun j => (↑(sliceBilinear X j) : ℂ)) (aeval transf G) := by
    rw [repHiggs_eq_sliceR, hP, ← eval_Qslice_eigenPoint, ← hG]
    simp only [eval_aeval_comp]
    rw [show (fun i => eval (eigenPoint X) (neutralBilinear i))
          = (fun i => eval (fun j => (↑(sliceBilinear X j) : ℂ)) (transf i)) from
        funext (neutralBilinear_eval_eigenPoint X)]
  have hre : V (repHiggs X) = (eval (fun j => (↑(sliceBilinear X j) : ℂ)) (
      aeval transf G)).re := by rw [← hval]; simp
  rw [hre, realPart_eval]

/-!
## E. Clearing the `‖Φ1‖²` and `‖Φ2‖²` factors

Part D expresses the value as a polynomial in the bilinears, but two of them — `|Φ2₀|²`
  and `|Φ2₁|²`
— are not directly Gram polynomials. Multiplying by a power of `‖Φ1‖²` clears these; the
doublet swap of `SwapDoublet` then gives the mirror statement with `‖Φ2‖²`.
-/

open MvPolynomial in
/-- The five bilinear generators, as polynomials in the four representative parameters. -/
noncomputable def sliceBilinearPoly : Fin 5 → MvPolynomial (Fin 4) ℝ :=
  ![X 0 ^ 2, X 0 * X 1, X 0 * X 2, X 1 ^ 2 + X 2 ^ 2, X 3 ^ 2]

open MvPolynomial in
/-- The four Gram components, as polynomials in the four representative parameters. -/
noncomputable def gramPoly : Fin 1 ⊕ Fin 3 → MvPolynomial (Fin 4) ℝ :=
  Sum.elim (fun _ => X 0 ^ 2 + (X 1 ^ 2 + X 2 ^ 2 + X 3 ^ 2))
    ![2 * (X 0 * X 1), 2 * (X 0 * X 2), X 0 ^ 2 - (X 1 ^ 2 + X 2 ^ 2 + X 3 ^ 2)]

open MvPolynomial in
@[simp] lemma sliceBilinearPoly_eval (X : Fin 4 → ℝ) (i : Fin 5) :
    (sliceBilinearPoly i).eval X = sliceBilinear X i := by
  fin_cases i <;> simp [sliceBilinearPoly, sliceBilinear]

open MvPolynomial in
@[simp] lemma gramPoly_eval (X : Fin 4 → ℝ) (μ : Fin 1 ⊕ Fin 3) :
    (gramPoly μ).eval X = (repHiggs X).gramVector μ := by
  match μ with
  | Sum.inl 0 => simp [gramPoly]
  | Sum.inr 0 => simp [gramPoly]; ring
  | Sum.inr 1 => simp [gramPoly]; ring
  | Sum.inr 2 => simp [gramPoly]

open MvPolynomial in
/-- Some power of `‖Φ1‖² = X₀²` times the value polynomial lies in the Gram
  subalgebra: multiplying by `X₀²` pairs each `X₁²+X₂²` into `(X₀X₁)²+(X₀X₂)²` and each `X₃²` into
  the determinant `X₀²X₃²`, both of which are Gram polynomials. -/
lemma exists_clearing_mem (p : MvPolynomial (Fin 5) ℝ) :
    ∃ N : ℕ, (X 0) ^ (2 * N) * aeval sliceBilinearPoly p ∈
      Algebra.adjoin ℝ (Set.range gramPoly) := by
  set S := Algebra.adjoin ℝ (Set.range gramPoly) with hS
  have hgmem : ∀ μ, gramPoly μ ∈ S := fun μ => Algebra.subset_adjoin ⟨μ, rfl⟩
  have hC : ∀ r : ℝ, (C r : MvPolynomial (Fin 4) ℝ) ∈ S := fun r => by
    rw [← MvPolynomial.algebraMap_eq]; exact Subalgebra.algebraMap_mem _ _
  have hX0sq : (X 0 ^ 2 : MvPolynomial (Fin 4) ℝ) ∈ S := by
    have e : (X 0 ^ 2 : MvPolynomial (Fin 4) ℝ)
        = C (1 / 2) * (gramPoly (Sum.inl 0) + gramPoly (Sum.inr 2)) := by
      apply MvPolynomial.funext; intro x; simp [gramPoly]; ring
    rw [e]; exact Subalgebra.mul_mem _ (hC _) (Subalgebra.add_mem _ (hgmem _) (hgmem _))
  have hX0X1 : (X 0 * X 1 : MvPolynomial (Fin 4) ℝ) ∈ S := by
    have e : (X 0 * X 1 : MvPolynomial (Fin 4) ℝ) = C (1 / 2) * gramPoly (Sum.inr 0) := by
      apply MvPolynomial.funext; intro x; simp [gramPoly]
    rw [e]; exact Subalgebra.mul_mem _ (hC _) (hgmem _)
  have hX0X2 : (X 0 * X 2 : MvPolynomial (Fin 4) ℝ) ∈ S := by
    have e : (X 0 * X 2 : MvPolynomial (Fin 4) ℝ) = C (1 / 2) * gramPoly (Sum.inr 1) := by
      apply MvPolynomial.funext; intro x; simp [gramPoly]
    rw [e]; exact Subalgebra.mul_mem _ (hC _) (hgmem _)
  have hmm : (X 1 ^ 2 + X 2 ^ 2 + X 3 ^ 2 : MvPolynomial (Fin 4) ℝ) ∈ S := by
    have e : (X 1 ^ 2 + X 2 ^ 2 + X 3 ^ 2 : MvPolynomial (Fin 4) ℝ)
        = C (1 / 2) * (gramPoly (Sum.inl 0) - gramPoly (Sum.inr 2)) := by
      apply MvPolynomial.funext; intro x; simp [gramPoly]; ring
    rw [e]; exact Subalgebra.mul_mem _ (hC _) (Subalgebra.sub_mem _ (hgmem _) (hgmem _))
  have her : (X 0 ^ 2 * (X 1 ^ 2 + X 2 ^ 2) : MvPolynomial (Fin 4) ℝ) ∈ S := by
    have e : (X 0 ^ 2 * (X 1 ^ 2 + X 2 ^ 2) : MvPolynomial (Fin 4) ℝ)
        = (X 0 * X 1) ^ 2 + (X 0 * X 2) ^ 2 := by ring
    rw [e]; exact Subalgebra.add_mem _ (pow_mem hX0X1 2) (pow_mem hX0X2 2)
  have hes : (X 0 ^ 2 * X 3 ^ 2 : MvPolynomial (Fin 4) ℝ) ∈ S := by
    have e : (X 0 ^ 2 * X 3 ^ 2 : MvPolynomial (Fin 4) ℝ)
        = X 0 ^ 2 * (X 1 ^ 2 + X 2 ^ 2 + X 3 ^ 2) - X 0 ^ 2 * (X 1 ^ 2 + X 2 ^ 2) := by ring
    rw [e]; exact Subalgebra.sub_mem _ (Subalgebra.mul_mem _ hX0sq hmm) her
  induction p using MvPolynomial.induction_on' with
  | monomial m c =>
    refine ⟨m 3 + m 4, ?_⟩
    have hmemRHS : C c * ((X 0 ^ 2) ^ m 0 * (X 0 * X 1) ^ m 1 * (X 0 * X 2) ^ m 2 *
        (X 0 ^ 2 * (X 1 ^ 2 + X 2 ^ 2)) ^ m 3 * (X 0 ^ 2 * X 3 ^ 2) ^ m 4) ∈ S :=
      Subalgebra.mul_mem _ (hC _) (Subalgebra.mul_mem _ (Subalgebra.mul_mem _
        (Subalgebra.mul_mem _ (Subalgebra.mul_mem _ (pow_mem hX0sq _) (pow_mem hX0X1 _))
          (pow_mem hX0X2 _)) (pow_mem her _)) (pow_mem hes _))
    rw [aeval_monomial, Finsupp.prod_fintype _ _ (fun i => by simp), Fin.prod_univ_five]
    simp only [sliceBilinearPoly, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
      Fin.isValue, MvPolynomial.algebraMap_eq]
    convert hmemRHS using 1
    rw [pow_mul, pow_add]
    simp only [mul_pow]
    ring
  | add p q hp hq =>
    obtain ⟨Np, hp'⟩ := hp
    obtain ⟨Nq, hq'⟩ := hq
    refine ⟨max Np Nq, ?_⟩
    rw [map_add, mul_add]
    apply Subalgebra.add_mem
    · rw [show 2 * max Np Nq = 2 * (max Np Nq - Np) + 2 * Np from by omega, pow_add, mul_assoc]
      exact Subalgebra.mul_mem _ (by rw [pow_mul]; exact pow_mem hX0sq _) hp'
    · rw [show 2 * max Np Nq = 2 * (max Np Nq - Nq) + 2 * Nq from by omega, pow_add, mul_assoc]
      exact Subalgebra.mul_mem _ (by rw [pow_mul]; exact pow_mem hX0sq _) hq'

open MvPolynomial in
/-- **Denominator clearing.** For the value polynomial `p`, some power of `‖Φ1‖² = X₀²`
  times `p ∘ sliceBilinear` is a polynomial in the Gram vector. -/
lemma exists_gram_clearing (p : MvPolynomial (Fin 5) ℝ) :
    ∃ (A : MvPolynomial (Fin 1 ⊕ Fin 3) ℝ) (N : ℕ), ∀ X : Fin 4 → ℝ,
      (X 0) ^ (2 * N) * p.eval (sliceBilinear X) = A.eval ((repHiggs X).gramVector) := by
  obtain ⟨N, hmem⟩ := exists_clearing_mem p
  rw [Algebra.adjoin_range_eq_range_aeval ℝ gramPoly] at hmem
  obtain ⟨A, hA⟩ := hmem
  change aeval gramPoly A = _ at hA
  refine ⟨A, N, fun X => ?_⟩
  have hL : eval X (aeval gramPoly A) = A.eval ((repHiggs X).gramVector) := by
    rw [eval_aeval_comp]; simp only [gramPoly_eval]
  have hR : eval X (MvPolynomial.X 0 ^ (2 * N) * aeval sliceBilinearPoly p)
      = (X 0) ^ (2 * N) * p.eval (sliceBilinear X) := by
    rw [map_mul, map_pow, eval_X, eval_aeval_comp]; simp only [sliceBilinearPoly_eval]
  rw [← hR, ← hL, hA]

open MvPolynomial in
/-- **`‖Φ1‖²`-clearing, on all configurations.** A power of `‖Φ1‖²` times a gauge-invariant
  polynomial potential is, everywhere, a polynomial in the Gram vector. -/
lemma exists_normSq_Φ1_clearing {V : EffectivePotential} {n : ℕ}
    (hI : IsInvariant V) (h : HasMaxMassDimLE V n) :
    ∃ (A : MvPolynomial (Fin 1 ⊕ Fin 3) ℝ) (N : ℕ), ∀ φ : TwoHiggsDoublet,
      (‖φ.Φ1‖ ^ 2) ^ N * V φ = A.eval φ.gramVector := by
  obtain ⟨p5, hp5⟩ := exists_polynomial_repHiggs_sliceBilinear hI h
  obtain ⟨A, N, hAN⟩ := exists_gram_clearing p5
  refine ⟨A, N, fun φ => ?_⟩
  obtain ⟨X, g, hg⟩ := exists_smul_eq_repHiggs φ
  have hV : V φ = V (repHiggs X) := by rw [← hg]; exact (hI g φ).symm
  have hgram : φ.gramVector = (repHiggs X).gramVector := by
    rw [← hg]; funext μ; exact (gaugeGroupI_smul_fst_gramVector g φ μ).symm
  have hΦ1 : ‖φ.Φ1‖ ^ 2 = (X 0) ^ 2 := by
    rw [normSq_Φ1_eq_gramVector, hgram, ← normSq_Φ1_eq_gramVector, normSq_repHiggs_Φ1]
  rw [hΦ1, hV, hgram, ← pow_mul, hp5]
  exact hAN X

open MvPolynomial in
/-- The Gram-vector substitution induced by swapping the doublets (sign flip on the imaginary and
  difference components). -/
noncomputable def swapSubst : (Fin 1 ⊕ Fin 3) → MvPolynomial (Fin 1 ⊕ Fin 3) ℝ :=
  Sum.elim (fun _ => X (Sum.inl 0)) ![X (Sum.inr 0), -X (Sum.inr 1), -X (Sum.inr 2)]

open MvPolynomial in
/-- **`‖Φ2‖²`-clearing, on all configurations.** A power of `‖Φ2‖²` times a gauge-invariant
  polynomial potential is, everywhere, a polynomial in the Gram vector. Obtained from
  `exists_normSq_Φ1_clearing` for the doublet-swapped potential. -/
lemma exists_normSq_Φ2_clearing {V : EffectivePotential} {n : ℕ}
    (hI : IsInvariant V) (h : HasMaxMassDimLE V n) :
    ∃ (B : MvPolynomial (Fin 1 ⊕ Fin 3) ℝ) (M : ℕ), ∀ φ : TwoHiggsDoublet,
      (‖φ.Φ2‖ ^ 2) ^ M * V φ = B.eval φ.gramVector := by
  obtain ⟨B0, M, hB0⟩ := exists_normSq_Φ1_clearing hI.comp_swapDoublet h.comp_swapDoublet
  refine ⟨aeval swapSubst B0, M, fun φ => ?_⟩
  have hb := hB0 (swapDoublet φ)
  simp only [swapDoublet_Φ1, swapDoublet_swapDoublet] at hb
  have hpt : (swapDoublet φ).gramVector = fun μ => eval φ.gramVector (swapSubst μ) := by
    funext μ
    match μ with
    | Sum.inl 0 => simp [swapSubst, gramVector_swapDoublet_inl]
    | Sum.inr 0 => simp [swapSubst, gramVector_swapDoublet_inr0]
    | Sum.inr 1 => simp [swapSubst, gramVector_swapDoublet_inr1]
    | Sum.inr 2 => simp [swapSubst, gramVector_swapDoublet_inr2]
  rw [hb, eval_aeval_comp, hpt]

/-!
## F. Independence and coprimality of the Gram invariants

The four Gram invariants are algebraically independent (`gramPoly_injective`), and the two linear
combinations `‖Φ1‖² = (g₀+g₃)/2` and `‖Φ2‖² = (g₀-g₃)/2` are coprime in the Gram ring
(`uPow_dvd`). Together these let the `‖Φ1‖²` and `‖Φ2‖²` factors be cancelled.
-/

open MvPolynomial in
/-- The four Gram invariants are algebraically independent: the Gram substitution is injective. -/
lemma gramPoly_injective :
    Function.Injective
      (aeval gramPoly : MvPolynomial (Fin 1 ⊕ Fin 3) ℝ → MvPolynomial (Fin 4) ℝ) := by
  rw [injective_iff_map_eq_zero]
  intro P hP
  -- `P` vanishes on every Gram vector of a representative.
  have hvanish : ∀ y : Fin 4 → ℝ, P.eval ((repHiggs y).gramVector) = 0 := by
    intro y
    have h := congrArg (eval y) hP
    rw [eval_aeval_comp, map_zero] at h
    rwa [show (fun μ => eval y (gramPoly μ)) = (repHiggs y).gramVector from
      funext (gramPoly_eval y)] at h
  -- The Gram cone contains an infinite box; `P` vanishes there, hence `P = 0`.
  refine MvPolynomial.funext_set
    (fun μ => Sum.elim (fun _ => Set.Ioi (2 : ℝ)) (fun _ => Set.Ioo (-1 : ℝ) 1) μ) ?_ ?_
  · intro μ
    rcases μ with _ | i
    · exact Set.Ioi_infinite _
    · exact Set.Ioo_infinite (by norm_num)
  · intro x hx
    rw [Set.mem_univ_pi] at hx
    have hxl : (2 : ℝ) < x (Sum.inl 0) := hx (Sum.inl 0)
    have hx0 : x (Sum.inr 0) ∈ Set.Ioo (-1 : ℝ) 1 := hx (Sum.inr 0)
    have hx1 : x (Sum.inr 1) ∈ Set.Ioo (-1 : ℝ) 1 := hx (Sum.inr 1)
    have hx2 : x (Sum.inr 2) ∈ Set.Ioo (-1 : ℝ) 1 := hx (Sum.inr 2)
    have hdpos : 0 < (x (Sum.inl 0) + x (Sum.inr 2)) / 2 := by have := hx2.1; linarith
    set y0 : ℝ := Real.sqrt ((x (Sum.inl 0) + x (Sum.inr 2)) / 2) with hy0def
    have hy0pos : 0 < y0 := Real.sqrt_pos.mpr hdpos
    have hy0sq : y0 ^ 2 = (x (Sum.inl 0) + x (Sum.inr 2)) / 2 :=
      Real.sq_sqrt hdpos.le
    set y1 : ℝ := x (Sum.inr 0) / (2 * y0) with hy1def
    set y2 : ℝ := x (Sum.inr 1) / (2 * y0) with hy2def
    -- the perpendicular component squared is nonnegative (PSD condition on the box)
    have hbound : x (Sum.inr 0) ^ 2 + x (Sum.inr 1) ^ 2
        ≤ x (Sum.inl 0) ^ 2 - x (Sum.inr 2) ^ 2 := by
      nlinarith [hx0.1, hx0.2, hx1.1, hx1.2, hx2.1, hx2.2, hxl]
    have h2y0sq : (2 * y0) ^ 2 = 2 * (x (Sum.inl 0) + x (Sum.inr 2)) := by
      rw [mul_pow, hy0sq]; ring
    have hsumpos : 0 < x (Sum.inl 0) + x (Sum.inr 2) := by linarith [hx2.1]
    have hkey : 2 * (x (Sum.inl 0) + x (Sum.inr 2)) * (y1 ^ 2 + y2 ^ 2)
        = x (Sum.inr 0) ^ 2 + x (Sum.inr 1) ^ 2 := by
      rw [hy1def, hy2def, div_pow, div_pow, ← h2y0sq]
      field_simp
    have hy3arg : 0 ≤ (x (Sum.inl 0) - x (Sum.inr 2)) / 2 - y1 ^ 2 - y2 ^ 2 := by
      nlinarith [hkey, hbound, hsumpos]
    set y3 : ℝ := Real.sqrt ((x (Sum.inl 0) - x (Sum.inr 2)) / 2 - y1 ^ 2 - y2 ^ 2) with hy3def
    have hy3sq : y3 ^ 2 = (x (Sum.inl 0) - x (Sum.inr 2)) / 2 - y1 ^ 2 - y2 ^ 2 :=
      Real.sq_sqrt hy3arg
    have hgram : (repHiggs ![y0, y1, y2, y3]).gramVector = x := by
      funext μ
      match μ with
      | Sum.inl 0 =>
        rw [gramVector_repHiggs_inl]
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, Fin.isValue]
        rw [hy0sq, hy3sq]; ring
      | Sum.inr 0 =>
        rw [gramVector_repHiggs_inr0]
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
        rw [hy1def]; field_simp
      | Sum.inr 1 =>
        rw [gramVector_repHiggs_inr1]
        simp only [Matrix.cons_val_zero, Matrix.cons_val, Fin.isValue]
        rw [hy2def]; field_simp
      | Sum.inr 2 =>
        rw [gramVector_repHiggs_inr2]
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, Fin.isValue]
        rw [hy0sq, hy3sq]; ring
    rw [map_zero, ← hgram]
    exact hvanish ![y0, y1, y2, y3]

open MvPolynomial in
/-- `‖Φ1‖²` and `‖Φ2‖²`, as the distinct linear forms `(g₀±g₃)/2` of the Gram ring, are coprime:
  if `‖Φ1‖²ᴺ · B = ‖Φ2‖²ᴹ · A` then `‖Φ1‖²ᴺ ∣ A`. -/
lemma uPow_dvd {N M : ℕ} {A B : MvPolynomial (Fin 1 ⊕ Fin 3) ℝ}
    (hAB : (C (1 / 2) * (X (Sum.inl 0) + X (Sum.inr 2))) ^ N * B
       = (C (1 / 2) * (X (Sum.inl 0) - X (Sum.inr 2))) ^ M * A) :
    (C (1 / 2) * (X (Sum.inl 0) + X (Sum.inr 2))) ^ N ∣ A := by
  -- `X (inl 0)` does not divide `X (inr 2)` (distinct variables).
  have hnd : ¬ ((X (Sum.inl 0) : MvPolynomial (Fin 1 ⊕ Fin 3) ℝ) ∣ X (Sum.inr 2)) := by
    rintro ⟨q, hq⟩
    have h0 := congrArg (eval (fun μ => if μ = Sum.inr 2 then (1 : ℝ) else 0)) hq
    simp [eval_mul, eval_X] at h0
  -- hence `X (inl 0)` and `X (inr 2)` are relatively prime.
  have hrelXX : IsRelPrime (X (Sum.inl 0) : MvPolynomial (Fin 1 ⊕ Fin 3) ℝ) (X (Sum.inr 2)) := by
    intro d hd1 hd2
    obtain ⟨c, hc⟩ := hd1
    rcases (MvPolynomial.X_prime).irreducible.isUnit_or_isUnit hc with h | h
    · exact h
    · exfalso
      apply hnd
      obtain ⟨e, he⟩ := hd2
      exact ⟨(↑h.unit⁻¹ : MvPolynomial (Fin 1 ⊕ Fin 3) ℝ) * e, by
        rw [he, ← mul_assoc]
        congr 1
        rw [hc, mul_assoc, IsUnit.mul_val_inv, mul_one]⟩
  -- `u` and `w` are relatively prime: any common divisor divides `u ± w = X inl0, X inr2`.
  have hsum : (X (Sum.inl 0) : MvPolynomial (Fin 1 ⊕ Fin 3) ℝ)
      = C (1 / 2) * (X (Sum.inl 0) + X (Sum.inr 2)) + C (1 / 2) *
        (X (Sum.inl 0) - X (Sum.inr 2)) := by
    apply MvPolynomial.funext; intro y
    simp only [eval_add, eval_mul, eval_sub, eval_C, eval_X]; ring
  have hdiff : (X (Sum.inr 2) : MvPolynomial (Fin 1 ⊕ Fin 3) ℝ)
      = C (1 / 2) * (X (Sum.inl 0) + X (Sum.inr 2)) - C (1 / 2) *
        (X (Sum.inl 0) - X (Sum.inr 2)) := by
    apply MvPolynomial.funext; intro y
    simp only [eval_add, eval_mul, eval_sub, eval_C, eval_X]; ring
  have hrel : IsRelPrime (C (1 / 2) * (X (Sum.inl 0) + X (Sum.inr 2)))
      (C (1 / 2) * (X (Sum.inl 0) - X (Sum.inr 2)) : MvPolynomial (Fin 1 ⊕ Fin 3) ℝ) := by
    intro d hdu hdw
    exact hrelXX (hsum ▸ dvd_add hdu hdw) (hdiff ▸ dvd_sub hdu hdw)
  exact (hrel.pow).dvd_of_dvd_mul_left (hAB ▸ Dvd.intro B rfl)

/-!
## G. The gauge-invariant potential as a polynomial in the Gram vector

Every configuration is gauge equivalent to a representative `repHiggs X`
(`exists_smul_eq_repHiggs`) whose Gram vector is polynomial in the parameters
(`gramVector_repHiggs_*`). Combining the two norm clearings of part E with the coprimality of part F
removes the `‖Φ1‖²`/`‖Φ2‖²` factors and produces the Gram polynomial on representatives
(`exists_polynomial_on_repHiggs`); gauge invariance then transports it to all configurations.
-/

open MvPolynomial in
/-- **On representatives.** A gauge-invariant polynomial potential, restricted to the polynomial
  family of orbit representatives `repHiggs X`, is a polynomial in the Gram components of that
  family. Proved by the doublet-swap argument: clearing the `‖Φ1‖²` factor (aligning `Φ1`) and the
  `‖Φ2‖²` factor (aligning `Φ2`, via the gauge-commuting swap), then using that `‖Φ1‖²` and `‖Φ2‖²`
  are coprime in the Gram ring. -/
lemma exists_polynomial_on_repHiggs {V : EffectivePotential} {n : ℕ}
    (hI : IsInvariant V) (h : HasMaxMassDimLE V n) :
    ∃ p : MvPolynomial (Fin 1 ⊕ Fin 3) ℝ,
      ∀ X : Fin 4 → ℝ, V (repHiggs X) = p.eval (repHiggs X).gramVector := by
  obtain ⟨p5, hp5⟩ := exists_polynomial_repHiggs_sliceBilinear hI h
  obtain ⟨A, N, hA'⟩ := exists_normSq_Φ1_clearing hI h
  obtain ⟨B, M, hB'⟩ := exists_normSq_Φ2_clearing hI h
  set F : MvPolynomial (Fin 4) ℝ := aeval sliceBilinearPoly p5 with hF_def
  have hFeval : ∀ x : Fin 4 → ℝ, F.eval x = V (repHiggs x) := by
    intro x; rw [hF_def, eval_aeval_comp]; simp only [sliceBilinearPoly_eval]; exact (hp5 x).symm
  have hgramfun : ∀ x : Fin 4 → ℝ,
      (fun μ => eval x (gramPoly μ)) = (repHiggs x).gramVector := fun x => funext (gramPoly_eval x)
  have hu : aeval gramPoly ((C (1 / 2) * (X (Sum.inl 0) + X (Sum.inr 2)) :
      MvPolynomial (Fin 1 ⊕ Fin 3) ℝ)) = X 0 ^ 2 := by
    apply MvPolynomial.funext; intro x
    rw [eval_aeval_comp, hgramfun, eval_mul, eval_C, eval_add, eval_X, eval_X,
      gramVector_repHiggs_inl, gramVector_repHiggs_inr2, eval_pow, eval_X]; ring
  have hw : aeval gramPoly ((C (1 / 2) * (X (Sum.inl 0) - X (Sum.inr 2)) :
      MvPolynomial (Fin 1 ⊕ Fin 3) ℝ)) = X 1 ^ 2 + X 2 ^ 2 + X 3 ^ 2 := by
    apply MvPolynomial.funext; intro x
    rw [eval_aeval_comp, hgramfun, eval_mul, eval_C, eval_sub, eval_X, eval_X,
      gramVector_repHiggs_inl, gramVector_repHiggs_inr2]
    simp only [eval_add, eval_pow, eval_X]; ring
  have hIp : aeval gramPoly A = (X 0 ^ 2) ^ N * F := by
    apply MvPolynomial.funext; intro x
    rw [eval_aeval_comp, hgramfun, ← hA' (repHiggs x), normSq_repHiggs_Φ1]
    simp only [eval_mul, eval_pow, eval_X, hFeval]
  have hIIp : aeval gramPoly B = (X 1 ^ 2 + X 2 ^ 2 + X 3 ^ 2) ^ M * F := by
    apply MvPolynomial.funext; intro x
    rw [eval_aeval_comp, hgramfun, ← hB' (repHiggs x), normSq_repHiggs_Φ2]
    simp only [eval_mul, eval_pow, eval_add, eval_X, hFeval]
  have hcross : (C (1 / 2) * (X (Sum.inl 0) + X (Sum.inr 2))) ^ N * B
      = (C (1 / 2) * (X (Sum.inl 0) - X (Sum.inr 2))) ^ M * A := by
    apply gramPoly_injective
    rw [map_mul, map_mul, map_pow, map_pow, hu, hw, hIp, hIIp]; ring
  obtain ⟨C0, hC0⟩ := uPow_dvd hcross
  refine ⟨C0, fun X => ?_⟩
  have key : (MvPolynomial.X 0 ^ 2) ^ N * F = (MvPolynomial.X 0 ^ 2) ^ N * aeval gramPoly C0 := by
    rw [← hIp, hC0, map_mul, map_pow, hu]
  have hFC : F = aeval gramPoly C0 := by
    have hne : ((MvPolynomial.X 0 : MvPolynomial (Fin 4) ℝ) ^ 2) ^ N ≠ 0 :=
      pow_ne_zero _ (pow_ne_zero _ (MvPolynomial.X_ne_zero 0))
    exact mul_left_cancel₀ hne key
  rw [← hFeval X, hFC, eval_aeval_comp, hgramfun]

/-- **The two Higgs doublet potential in the bilinear formalism.** A gauge-invariant polynomial
  effective potential of maximum mass dimension `n` is a polynomial in the four gauge-invariant
  bilinears — the entries of the Gram vector. -/
lemma effectivePotential_is_polynomial_gramVector {V : EffectivePotential} {n : ℕ}
    (hI: IsInvariant V) (h : HasMaxMassDimLE V n) :
    ∃ p : MvPolynomial (Fin 1 ⊕ Fin 3) ℝ, (∀ φ : TwoHiggsDoublet, V φ = p.eval φ.gramVector) := by
  obtain ⟨p, hp⟩ := exists_polynomial_on_repHiggs hI h
  refine ⟨p, fun φ => ?_⟩
  obtain ⟨X, g, hg⟩ := exists_smul_eq_repHiggs φ
  have hgram : φ.gramVector = (repHiggs X).gramVector := by
    rw [← hg]
    funext μ
    exact (gaugeGroupI_smul_fst_gramVector g φ μ).symm
  have hV : V φ = V (repHiggs X) := by
    rw [← hg]
    exact (hI g φ).symm
  rw [hV, hp X, hgram]

end EffectivePotential

end TwoHiggsDoublet
