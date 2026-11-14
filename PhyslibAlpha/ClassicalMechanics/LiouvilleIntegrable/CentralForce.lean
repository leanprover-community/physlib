/-
Copyright (c) 2026 Rithwik Ranganathan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rithwik Ranganathan
-/
module

public import Physlib.Mathematics.ForMathlib.Analytic
public import PhyslibAlpha.ClassicalMechanics.CentralForce.AngularMomentum
public import PhyslibAlpha.ClassicalMechanics.LiouvilleIntegrable.Basic
/-!

# Central-force systems are Liouville integrable

Independence and involution of the Hamiltonian, squared angular momentum and axial component.

## i. Overview

The Hamiltonian `H`, squared angular momentum `L²` and axial component `L_z` are independent
and in involution on the open dense domain where the radial momentum is non-zero and the
angular momentum is not parallel to the z-axis. This proves Liouville integrability for every
central-force system. The domain is sufficient; no maximality claim is made.

Independence follows by pairing a vanishing combination of gradients with radial changes of
momentum, infinitesimal rotations and momentum scaling, successively eliminating its coefficients.

## ii. Key results

- `CentralForce.integrabilityDomain` : the chosen domain in phase space.
- `CentralForce.isOpen_integrabilityDomain`, `CentralForce.dense_integrabilityDomain` : it is
  open and dense.
- `CentralForce.snd_ne_zero_of_mem_integrabilityDomain` : it excludes the centre of force.
- `CentralForce.linearIndependent_conservedQuantities` : the observables are independent there.
- `CentralForce.liouvilleIntegrable` : the resulting Liouville-integrability construction.

## iii. Table of contents

- A. The domain of integrability
- B. The conserved quantities
  - B.1. Involution
  - B.2. Functional independence
- C. Liouville integrability

## iv. References

* V. I. Arnold, *Mathematical Methods of Classical Mechanics*, 2nd edition, Chapter 10.
-/

@[expose] public section

namespace ClassicalMechanics.CentralForce

open InnerProductSpace
open scoped ContDiff

attribute [local fun_prop] analyticAt_fst analyticAt_snd

/-!

## A. The domain of integrability

-/

/-- The phase-space domain where the radial momentum is non-zero and the angular momentum
is not parallel to the z-axis, used to establish central-force integrability. -/
def integrabilityDomain : Set (EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)) :=
  {x | ⟪x.2, x.1⟫_ℝ ≠ 0 ∧ angularMomentum x.1 x.2 0 ^ 2 + angularMomentum x.1 x.2 1 ^ 2 ≠ 0}

/-- The domain is the non-vanishing set of a polynomial in the phase-space coordinates. -/
lemma integrabilityDomain_eq : integrabilityDomain =
    {x | (x.1 0 * x.2 0 + x.1 1 * x.2 1 + x.1 2 * x.2 2) *
      ((x.2 1 * x.1 2 - x.2 2 * x.1 1) ^ 2 + (x.2 2 * x.1 0 - x.2 0 * x.1 2) ^ 2) ≠ 0} := by
  ext x
  simp only [integrabilityDomain, Set.mem_ofPred_eq, mul_ne_zero_iff, angularMomentum_apply_zero,
    angularMomentum_apply_one, PiLp.inner_apply, Fin.sum_univ_three, RCLike.inner_apply,
    conj_trivial]

/-- The chosen central-force domain is open. -/
lemma isOpen_integrabilityDomain : IsOpen integrabilityDomain := by
  rw [integrabilityDomain_eq]
  exact isOpen_ne_fun (by fun_prop) continuous_const

/-- The chosen central-force domain is dense. -/
lemma dense_integrabilityDomain : Dense integrabilityDomain := by
  rw [integrabilityDomain_eq]
  refine AnalyticOnNhd.dense_setOf_ne_zero (𝕜 := ℝ) (fun z _ => by fun_prop)
    (x₀ := (!₂[1, 0, 1], !₂[1, 0, 0])) ?_
  norm_num [Matrix.cons_val_two]

/-- The chosen domain excludes the centre of force. -/
lemma snd_ne_zero_of_mem_integrabilityDomain
    {x : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)} (hx : x ∈ integrabilityDomain) :
    x.2 ≠ 0 := by
  intro h
  exact hx.1 (by rw [h, inner_zero_left])

/-!

## B. The conserved quantities

-/

variable (S : CentralForce)

/-- The three conserved quantities in involution of a central-force system: the Hamiltonian `H`,
the squared magnitude `L²` of the angular momentum, and its z-component `L_z`. -/
noncomputable def conservedQuantities :
    Fin 3 → EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) → ℝ :=
  ![S.hamiltonian, angularMomentumSq, angularMomentumZ]

/-!

### B.1. Involution

-/

/-- Away from the centre of force, the conserved quantities of a central-force system are pairwise
in involution. -/
lemma poissonBracket_conservedQuantities (i j : Fin 3) (p : EuclideanSpace ℝ (Fin 3))
    {q : EuclideanSpace ℝ (Fin 3)} (hq : q ≠ 0) :
    poissonBracket (S.conservedQuantities i) (S.conservedQuantities j) p q = 0 := by
  have hSqH := S.poissonBracket_angularMomentumSq_hamiltonian p hq
  have hZH := S.poissonBracket_angularMomentumZ_hamiltonian p hq
  have hSqZ := poissonBracket_angularMomentumSq_angularMomentumZ p q
  have hHSq : poissonBracket S.hamiltonian angularMomentumSq p q = 0 := by
    rw [poissonBracket_antisymm, hSqH, neg_zero]
  have hHZ : poissonBracket S.hamiltonian angularMomentumZ p q = 0 := by
    rw [poissonBracket_antisymm, hZH, neg_zero]
  have hZSq : poissonBracket angularMomentumZ angularMomentumSq p q = 0 := by
    rw [poissonBracket_antisymm, hSqZ, neg_zero]
  fin_cases i <;> fin_cases j <;> simp [conservedQuantities, poissonBracket_self, *]

/-!

### B.2. Functional independence

-/

/-- Away from the centre of force, the phase-space gradients of the conserved quantities of a
central-force system. -/
lemma gradient_conservedQuantities (p : EuclideanSpace ℝ (Fin 3)) {q : EuclideanSpace ℝ (Fin 3)}
    (hq : q ≠ 0) :
    (fun i => (gradient (fun p' => S.conservedQuantities i p' q) p,
      gradient (fun q' => S.conservedQuantities i p q') q)) =
    ![(S.m⁻¹ • p, (deriv S.V ‖q‖ / ‖q‖) • q),
      ((2 * ⟪q, q⟫_ℝ) • p - (2 * ⟪q, p⟫_ℝ) • q, (2 * ⟪p, p⟫_ℝ) • q - (2 * ⟪q, p⟫_ℝ) • p),
      (q 0 • EuclideanSpace.single 1 1 - q 1 • EuclideanSpace.single 0 1,
        p 1 • EuclideanSpace.single 0 1 - p 0 • EuclideanSpace.single 1 1)] := by
  funext i
  fin_cases i
  · exact Prod.ext (S.hasGradientAt_hamiltonian_momentum p q).gradient
      (S.hasGradientAt_hamiltonian_position p hq).gradient
  · exact Prod.ext (hasGradientAt_angularMomentumSq_momentum p q).gradient
      (hasGradientAt_angularMomentumSq_position p q).gradient
  · exact Prod.ext (hasGradientAt_angularMomentumZ_momentum p q).gradient
      (hasGradientAt_angularMomentumZ_position p q).gradient

/-- On the domain of integrability, a phase-space function whose momentum gradient is a non-zero
multiple `a • p` of the momentum and whose position gradient is a multiple `c • q` of the
position, such as the Hamiltonian of a central-force system, is functionally independent of `L²`
and `L_z`: the three phase-space gradients are linearly independent. -/
lemma linearIndependent_gradients {p q : EuclideanSpace ℝ (Fin 3)} {a c : ℝ} (ha : a ≠ 0)
    (hx : (p, q) ∈ integrabilityDomain) :
    LinearIndependent ℝ ![(a • p, c • q),
      ((2 * ⟪q, q⟫_ℝ) • p - (2 * ⟪q, p⟫_ℝ) • q, (2 * ⟪p, p⟫_ℝ) • q - (2 * ⟪q, p⟫_ℝ) • p),
      (q 0 • EuclideanSpace.single 1 1 - q 1 • EuclideanSpace.single 0 1,
        p 1 • EuclideanSpace.single 0 1 - p 0 • EuclideanSpace.single 1 1)] := by
  rw [integrabilityDomain_eq] at hx
  obtain ⟨hqp, hL⟩ := mul_ne_zero_iff.mp hx
  rw [Fintype.linearIndependent_iff]
  intro g hg
  obtain ⟨h1, h2⟩ := Prod.ext_iff.mp hg
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
    Prod.fst_zero, Prod.snd_zero] at h1 h2
  -- The six components of the vanishing combination of gradients.
  have A0 := congrArg (fun v => v 0) h1
  have A1 := congrArg (fun v => v 1) h1
  have A2 := congrArg (fun v => v 2) h1
  have B0 := congrArg (fun v => v 0) h2
  have B1 := congrArg (fun v => v 1) h2
  have B2 := congrArg (fun v => v 2) h2
  have h20 : (2 : Fin 3) ≠ 0 := by decide
  have h21 : (2 : Fin 3) ≠ 1 := by decide
  simp only [Fin.isValue, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, PiLp.sub_apply, ne_eq,
    zero_ne_one, one_ne_zero, h20, h21, not_false_eq_true, PiLp.single_eq_of_ne,
    PiLp.single_eq_same, mul_zero, mul_one, sub_zero, zero_sub, PiLp.zero_apply, PiLp.inner_apply,
    Fin.sum_univ_three, RCLike.inner_apply, conj_trivial] at A0 A1 A2 B0 B1 B2
  -- Pairing with the radial change of momentum `(q, 0)`.
  have hg0 : g 0 = 0 := by
    have h : g 0 * (a * (p 0 * q 0 + p 1 * q 1 + p 2 * q 2)) = 0 := by
      linear_combination q 0 * A0 + q 1 * A1 + q 2 * A2
    simpa [ha, hqp] using h
  -- Pairing with the infinitesimal rotations about the x- and y-axes.
  have hg2 : g 2 = 0 := by
    have h : g 2 * ((q 1 * p 2 - q 2 * p 1) ^ 2 + (q 2 * p 0 - q 0 * p 2) ^ 2) = 0 := by
      linear_combination (q 1 * p 2 - q 2 * p 1) * (-(p 2 * A0 - p 0 * A2 + q 2 * B0 - q 0 * B2)) +
        (q 2 * p 0 - q 0 * p 2) * (-p 2 * A1 + p 1 * A2 - q 2 * B1 + q 1 * B2)
    exact (mul_eq_zero.mp h).resolve_right hL
  -- Pairing with the scaling `(p, 0)` of the momentum.
  have hg1 : g 1 = 0 := by
    have h : g 1 * (2 * ((q 1 * p 2 - q 2 * p 1) ^ 2 + (q 2 * p 0 - q 0 * p 2) ^ 2 +
        (q 0 * p 1 - q 1 * p 0) ^ 2)) = 0 := by
      linear_combination p 0 * A0 + p 1 * A1 + p 2 * A2 -
        a * (p 0 ^ 2 + p 1 ^ 2 + p 2 ^ 2) * hg0 - (q 0 * p 1 - q 1 * p 0) * hg2
    refine (mul_eq_zero.mp h).resolve_right (mul_ne_zero two_ne_zero (ne_of_gt ?_))
    exact add_pos_of_pos_of_nonneg (lt_of_le_of_ne (by positivity) (Ne.symm hL)) (sq_nonneg _)
  intro i
  fin_cases i
  exacts [hg0, hg1, hg2]

/-- On the domain of integrability, the conserved quantities of a central-force system are
functionally independent: their phase-space gradients are linearly independent. -/
lemma linearIndependent_conservedQuantities
    {x : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)} (hx : x ∈ integrabilityDomain) :
    LinearIndependent ℝ (fun i => (gradient (fun p' => S.conservedQuantities i p' x.2) x.1,
      gradient (fun q' => S.conservedQuantities i x.1 q') x.2)) := by
  rw [S.gradient_conservedQuantities x.1 (snd_ne_zero_of_mem_integrabilityDomain hx)]
  exact linearIndependent_gradients (inv_ne_zero S.m_ne_zero) hx

/-!

## C. Liouville integrability

-/

/-- Every central-force system is Liouville integrable on the domain of integrability, with the
Hamiltonian, the squared magnitude of the angular momentum and its z-component as conserved
quantities. -/
noncomputable def liouvilleIntegrable :
    LiouvilleIntegrableOn integrabilityDomain S.hamiltonian where
  isOpen := isOpen_integrabilityDomain
  dense := dense_integrabilityDomain
  f := S.conservedQuantities
  contDiffOn i := by
    fin_cases i
    · exact S.contDiffOn_hamiltonian.mono fun _ hx => snd_ne_zero_of_mem_integrabilityDomain hx
    · exact contDiff_angularMomentumSq.contDiffOn
    · exact contDiff_angularMomentumZ.contDiffOn
  exists_hamiltonian := ⟨0, rfl⟩
  involutive i j x hx :=
    S.poissonBracket_conservedQuantities i j x.1 (snd_ne_zero_of_mem_integrabilityDomain hx)
  independent _ hx := S.linearIndependent_conservedQuantities hx

end ClassicalMechanics.CentralForce
