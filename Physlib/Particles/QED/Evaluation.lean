/-
Copyright (c) 2026 Jinzheng Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jinzheng Li
-/
module

public import Physlib.Particles.QED.Fields
public import Physlib.Particles.QED.FieldStrength
public import Physlib.Particles.QED.LorentzInvariance
public import Physlib.Electromagnetism.Kinematics.ElectricField
public import Physlib.Electromagnetism.Kinematics.MagneticField
public import Physlib.Electromagnetism.Dynamics.IsExtrema
/-!
# Evaluation of the photon jet algebra on a potential

## i. Overview

The theorems tying the formal photon jet algebra of QED to the honest
electromagnetism of `Physlib.Electromagnetism`, through the evaluation map
`Photon.JetAlgebra.evalPotential` of `Physlib.Particles.QED.Basic`:

* evaluated on any differentiable potential, the formal field strength is the
  field strength of the potential with both indices lowered;
* evaluated on any differentiable potential, the formal Maxwell term
  `F_{μν} F^{μν}` is `-4 μ₀` times `ElectromagneticPotential.kineticTerm`;
* the evaluation is compatible with concrete gauge transformations
  `A ↦ A + ∂χ`, matching the formal gauge invariance of
  `Physlib.Particles.QED.GaugeInvariance` on the concrete side.

Only the photon sector evaluates: fermionic jet coordinates would have to be
evaluated on anticommuting (Grassmann-valued) fields, which have no
realisation as honest functions on spacetime.

This file contains no definitions, only theorems.

## ii. Key results

- `Photon.JetAlgebra.evalPotential_fieldStrength_zero` : the formal field
  strength evaluates to the field strength.
- `Photon.JetAlgebra.evalPotential_maxwellTerm` : **the formal Maxwell term
  is the Maxwell Lagrangian**.
- `Photon.JetAlgebra.electricField_eq_evalPotential_fieldStrength`,
  `Photon.JetAlgebra.magneticField_eq_evalPotential_fieldStrength` : the
  time–space and space–space components of the evaluated formal field
  strength are the electric and magnetic fields.
- `Photon.JetAlgebra.evalPotential_neg_quarter_maxwellTerm` : the Maxwell
  part of the QED Lagrangian is `μ₀` times the electromagnetic kinetic term.
- `Photon.JetAlgebra.evalPotential_fieldStrength_gaugeTransform`,
  `Photon.JetAlgebra.evalPotential_maxwellTerm_gaugeTransform` :
  compatibility with concrete gauge transformations.
- `Photon.JetAlgebra.evalPotential_maxwell_homogeneous` : **the homogeneous
  Maxwell equations**, as the evaluation of the formal Bianchi identity.
- `Photon.JetAlgebra.evalPotential_fieldStrength_lorentzAction` :
  compatibility of the formal and concrete Lorentz actions.

## iii. Table of contents

- A. Evaluation of the field strength
- B. The Maxwell term is the Maxwell Lagrangian
- B'. The electric and magnetic fields from the jet algebra
- B''. The Maxwell part of the QED Lagrangian
- D. First-order jets and the homogeneous Maxwell equations
- E. Compatibility with concrete Lorentz transformations
- C. Compatibility with concrete gauge transformations

## iv. References

The evaluation map is defined in `Physlib.Particles.QED.Basic`; the concrete side is
`Physlib/Electromagnetism/Kinematics/GaugeTransformation.lean` and
`Physlib/Electromagnetism/Dynamics/KineticTerm.lean`.

-/

@[expose] public section

namespace QED

open Electromagnetism SpaceTime minkowskiMatrix ContDiff

attribute [-simp] Fintype.sum_sum_type

namespace Photon

namespace JetAlgebra

/-!

## A. Evaluation of the field strength

-/

/-- The derivative of a covariant component.  Differentiability is needed to move
  the constant `η_{νν}` through the derivative. -/
lemma deriv_coPotential (A : ElectromagneticPotential 3) (hA : Differentiable ℝ A)
    (μ ν : Fin 1 ⊕ Fin 3) (x : SpaceTime 3) :
    ∂_ μ (coPotential A ν) x = η ν ν * ∂_ μ A x ν := by
  have hd : Differentiable ℝ (fun y => A y ν) := (SpaceTime.differentiable_vector _).mpr hA ν
  rw [SpaceTime.deriv_apply_eq μ ν _ hA x]
  show fderiv ℝ (fun y => η ν ν * A y ν) x (Lorentz.Vector.basis μ) = _
  rw [fderiv_const_mul (hd x)]
  simp

lemma evalPotential_fieldStrength_zero_apply (A : ElectromagneticPotential 3)
    (hA : Differentiable ℝ A) (μ ν : Fin 1 ⊕ Fin 3) (x : SpaceTime 3) :
    evalPotential A (fieldStrength 0 μ ν) x = η ν ν * ∂_ μ A x ν - η μ μ * ∂_ ν A x μ := by
  rw [fieldStrength, map_sub]
  simp only [zero_add, evalPotential_coord, derivMultiset_singleton, Pi.sub_apply]
  rw [deriv_coPotential A hA μ ν x, deriv_coPotential A hA ν μ x]

/-- The formal field strength evaluates to the field strength of the potential
  with both indices lowered, `F_{μν} = η_{μμ} η_{νν} F^{μν}`. -/
theorem evalPotential_fieldStrength_zero (A : ElectromagneticPotential 3)
    (hA : Differentiable ℝ A) (μ ν : Fin 1 ⊕ Fin 3) (x : SpaceTime 3) :
    evalPotential A (fieldStrength 0 μ ν) x =
      η μ μ * η ν ν * A.fieldStrengthMatrix x (μ, ν) := by
  rw [evalPotential_fieldStrength_zero_apply A hA μ ν x,
    ElectromagneticPotential.toFieldStrength_basis_repr_apply_eq_single (μν := (μ, ν))]
  rcases mul_self_eq_one_iff.mp (minkowskiMatrix.η_apply_mul_η_apply_diag μ) with h1 | h1 <;>
    rcases mul_self_eq_one_iff.mp (minkowskiMatrix.η_apply_mul_η_apply_diag ν) with h2 | h2 <;>
    rw [h1, h2] <;> ring

/-!

## B. The Maxwell term is the Maxwell Lagrangian

-/

/-- **The formal Maxwell term is the Maxwell Lagrangian.**  Evaluated on any
  differentiable electromagnetic potential, the gauge-invariant jet polynomial
  `F_{μν} F^{μν}` is `-4 μ₀` times the kinetic term
  `- 1/(4 μ₀) F_{μν} F^{μν}` of `Physlib.Electromagnetism`. -/
theorem evalPotential_maxwellTerm (𝓕 : FreeSpace) (A : ElectromagneticPotential 3)
    (hA : Differentiable ℝ A) (x : SpaceTime 3) :
    evalPotential A maxwellTerm x = -(4 * 𝓕.μ₀) * A.kineticTerm 𝓕 x := by
  rw [ElectromagneticPotential.kineticTerm_eq_sum_potential, maxwellTerm, map_sum]
  simp only [Finset.sum_apply, map_sum, map_smul, Pi.smul_apply, smul_eq_mul, map_mul,
    Pi.mul_apply]
  simp only [evalPotential_fieldStrength_zero_apply A hA]
  /- Both sides are now explicit double sums in `∂_ μ A x ν`. -/
  have key : ∀ μ ν : Fin 1 ⊕ Fin 3,
      η μ μ * η ν ν * ((η ν ν * ∂_ μ A x ν - η μ μ * ∂_ ν A x μ) *
        (η ν ν * ∂_ μ A x ν - η μ μ * ∂_ ν A x μ)) =
      (η μ μ * η ν ν * (∂_ μ A x ν) ^ 2 - ∂_ μ A x ν * ∂_ ν A x μ) +
      (η ν ν * η μ μ * (∂_ ν A x μ) ^ 2 - ∂_ ν A x μ * ∂_ μ A x ν) := by
    intro μ ν
    rcases mul_self_eq_one_iff.mp (minkowskiMatrix.η_apply_mul_η_apply_diag μ) with h1 | h1 <;>
      rcases mul_self_eq_one_iff.mp (minkowskiMatrix.η_apply_mul_η_apply_diag ν) with h2 | h2 <;>
      rw [h1, h2] <;> ring
  rw [Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun ν _ => key μ ν]
  simp only [Finset.sum_add_distrib]
  rw [Finset.sum_comm (s := Finset.univ) (t := Finset.univ)
    (f := fun μ ν : Fin 1 ⊕ Fin 3 =>
      η ν ν * η μ μ * (∂_ ν A x μ) ^ 2 - ∂_ ν A x μ * ∂_ μ A x ν)]
  have hμ₀ : 𝓕.μ₀ ≠ 0 := ne_of_gt 𝓕.μ₀_pos
  field_simp
  ring

/-!

## B'. The electric and magnetic fields from the jet algebra

Splitting spacetime into time and space through `toTimeAndSpace`, the
time–space components of the evaluated formal field strength are the electric
field and the space–space components the magnetic field of
`Physlib.Electromagnetism`.

-/

/-- The electric field is (the speed of light times) the evaluated time–space
  components of the formal field strength: `E_i = c ∂_0 A_i - c ∂_i A_0`
  with lowered indices. -/
theorem electricField_eq_evalPotential_fieldStrength (c : SpeedOfLight)
    (A : ElectromagneticPotential 3) (hA : Differentiable ℝ A) (t : Time)
    (x : Space) (i : Fin 3) :
    A.electricField c t x i =
      c * evalPotential A (fieldStrength 0 (Sum.inl 0) (Sum.inr i))
        ((toTimeAndSpace c).symm (t, x)) := by
  rw [evalPotential_fieldStrength_zero A hA,
    ElectromagneticPotential.electricField_eq_fieldStrengthMatrix A t x i hA]
  simp only [inl_0_inl_0, inr_i_inr_i, one_mul, neg_mul]
  ring

/-- The magnetic field is the evaluated space–space components of the formal
  field strength, `B_i = - F_{(i+1)(i+2)}` with lowered indices. -/
theorem magneticField_eq_evalPotential_fieldStrength (c : SpeedOfLight)
    (A : ElectromagneticPotential 3) (hA : Differentiable ℝ A) (t : Time)
    (x : Space) (i : Fin 3) :
    A.magneticField c t x i =
      - evalPotential A (fieldStrength 0 (Sum.inr (i + 1)) (Sum.inr (i + 2)))
        ((toTimeAndSpace c).symm (t, x)) := by
  rw [evalPotential_fieldStrength_zero A hA,
    ElectromagneticPotential.magneticField_coord_eq_fieldStrengthMatrix A t x hA]
  simp only [inr_i_inr_i, neg_mul, one_mul, neg_neg]

/-!

## B''. The Maxwell part of the QED Lagrangian

-/

/-- The Maxwell part `- 1/4 F_{μν} F^{μν}` of the QED Lagrangian evaluates to
  `μ₀` times the electromagnetic kinetic term of
  `Physlib.Electromagnetism.Dynamics`: the two Lagrangians agree up to the
  choice of units absorbed into the field normalisation. -/
theorem evalPotential_neg_quarter_maxwellTerm (𝓕 : FreeSpace)
    (A : ElectromagneticPotential 3) (hA : Differentiable ℝ A) (x : SpaceTime 3) :
    evalPotential A ((-(1 : ℝ)/4) • maxwellTerm) x = 𝓕.μ₀ * A.kineticTerm 𝓕 x := by
  rw [map_smul]
  have h := evalPotential_maxwellTerm 𝓕 A hA x
  rw [Pi.smul_apply, smul_eq_mul, h]
  ring

/-!

## D. First-order jets and the homogeneous Maxwell equations

Evaluation intertwines the first-order jet of the field strength with the
honest spacetime derivative — for a `C²` potential the sorted iterated
derivative is symmetric by Clairaut's theorem — and hence the formal Bianchi
identity of `Physlib.Particles.QED.FieldStrength` evaluates to **the homogeneous
Maxwell equations** in covariant form.

-/

lemma contDiff_coPotential {A : ElectromagneticPotential 3} (hA : ContDiff ℝ 2 A)
    (ν : Fin 1 ⊕ Fin 3) : ContDiff ℝ 2 (coPotential A ν) := by
  have h : ContDiff ℝ 2 fun x => A x ν := (SpaceTime.contDiff_vector _).mpr hA ν
  exact contDiff_const.mul h

/-- The iterated derivative along a pair of directions, in either order: for a
  `C²` function the canonical sorted order is immaterial by Clairaut's
  theorem. -/
lemma derivMultiset_pair (a b : Fin 1 ⊕ Fin 3) (f : SpaceTime 3 → ℝ)
    (hf : ContDiff ℝ 2 f) :
    derivMultiset {a, b} f = ∂_ a (∂_ b f) := by
  have key : ∀ u v : Fin 1 ⊕ Fin 3,
      finSumFinEquiv (m := 1) (n := 3) u ≤ finSumFinEquiv (m := 1) (n := 3) v →
      derivMultiset {u, v} f = ∂_ u (∂_ v f) := by
    intro u v huv
    have hsort : ((finSumFinEquiv (m := 1) (n := 3) u ::ₘ
        {finSumFinEquiv (m := 1) (n := 3) v}).sort fun a b => a ≤ b) =
        [finSumFinEquiv (m := 1) (n := 3) u, finSumFinEquiv (m := 1) (n := 3) v] := by
      rw [Multiset.sort_cons]
      · rw [Multiset.sort_singleton]
      · intro c hc
        rw [Multiset.mem_singleton] at hc
        rw [hc]
        exact huv
    rw [derivMultiset, show ({u, v} : Multiset (Fin 1 ⊕ Fin 3)).map
        (finSumFinEquiv (m := 1) (n := 3)) =
        finSumFinEquiv (m := 1) (n := 3) u ::ₘ {finSumFinEquiv (m := 1) (n := 3) v} from by
      simp, hsort]
    simp
  rcases le_total (finSumFinEquiv (m := 1) (n := 3) a) (finSumFinEquiv (m := 1) (n := 3) b)
    with h | h
  · exact key a b h
  · rw [show ({a, b} : Multiset (Fin 1 ⊕ Fin 3)) = {b, a} from Multiset.pair_comm a b,
      key b a h, SpaceTime.deriv_commute b a f hf]

lemma deriv_sub_eq {f g : SpaceTime 3 → ℝ} (lam : Fin 1 ⊕ Fin 3)
    (hf : Differentiable ℝ f) (hg : Differentiable ℝ g) :
    ∂_ lam (f - g) = ∂_ lam f - ∂_ lam g := by
  ext x
  rw [Pi.sub_apply, SpaceTime.deriv_eq, SpaceTime.deriv_eq, SpaceTime.deriv_eq,
    fderiv_sub (hf x) (hg x)]
  simp

/-- Evaluation intertwines the first-order jet with the spacetime derivative:
  the evaluated `∂_lam F_{μν}` is the derivative of the evaluated `F_{μν}`. -/
theorem evalPotential_fieldStrength_singleton (A : ElectromagneticPotential 3)
    (hA : ContDiff ℝ 2 A) (lam μ ν : Fin 1 ⊕ Fin 3) :
    evalPotential A (fieldStrength {lam} μ ν) =
      ∂_ lam (evalPotential A (fieldStrength 0 μ ν)) := by
  have hsub : evalPotential A (fieldStrength 0 μ ν) =
      ∂_ μ (coPotential A ν) - ∂_ ν (coPotential A μ) := by
    rw [fieldStrength, map_sub]
    simp only [zero_add, evalPotential_coord, derivMultiset_singleton]
  rw [hsub, deriv_sub_eq lam
      (SpaceTime.differentiable_deriv μ _ (contDiff_coPotential hA ν))
      (SpaceTime.differentiable_deriv ν _ (contDiff_coPotential hA μ)),
    fieldStrength, map_sub]
  simp only [evalPotential_coord, Multiset.singleton_add]
  simp only [← Multiset.insert_eq_cons]
  rw [derivMultiset_pair lam μ _ (contDiff_coPotential hA ν),
    derivMultiset_pair lam ν _ (contDiff_coPotential hA μ)]

/-- **The homogeneous Maxwell equations** in covariant form,
  `∂_lam F_{μν} + ∂_μ F_{ν lam} + ∂_ν F_{lam μ} = 0`, as the evaluation of the
  formal Bianchi identity of `Physlib.Particles.QED.FieldStrength`: Faraday's law and
  the absence of magnetic monopoles are its time–space–space and
  space–space–space components. -/
theorem evalPotential_maxwell_homogeneous (A : ElectromagneticPotential 3)
    (hA : ContDiff ℝ 2 A) (lam μ ν : Fin 1 ⊕ Fin 3) :
    ∂_ lam (evalPotential A (fieldStrength 0 μ ν)) +
      ∂_ μ (evalPotential A (fieldStrength 0 ν lam)) +
      ∂_ ν (evalPotential A (fieldStrength 0 lam μ)) = 0 := by
  rw [← evalPotential_fieldStrength_singleton A hA lam μ ν,
    ← evalPotential_fieldStrength_singleton A hA μ ν lam,
    ← evalPotential_fieldStrength_singleton A hA ν lam μ, ← map_add, ← map_add,
    show fieldStrength {lam} μ ν + fieldStrength {μ} ν lam +
        fieldStrength {ν} lam μ = 0 from by
      simpa using fieldStrength_bianchi 0 lam μ ν,
    map_zero]

/-!

## D'. The inhomogeneous Maxwell equations and the action principle

The concrete side (`Physlib.Electromagnetism.Dynamics.IsExtrema`) proves
variationally that a potential extremises the electromagnetic action exactly
when `∂_μ F^{μν} = μ₀ J^ν`.  The left-hand side is the evaluation of the
formal Maxwell operator of `Physlib.Particles.QED.Fields`, so the action
principle can be read entirely through the jet algebra.

-/

lemma deriv_const_mul_apply (c : ℝ) {f : SpaceTime 3 → ℝ} (ρ : Fin 1 ⊕ Fin 3)
    (hf : Differentiable ℝ f) (x : SpaceTime 3) :
    ∂_ ρ (fun y => c * f y) x = c * ∂_ ρ f x := by
  rw [SpaceTime.deriv_eq, SpaceTime.deriv_eq, fderiv_const_mul (hf x)]
  simp

/-- **The action principle through the jet algebra**: an electromagnetic
  potential extremises the Maxwell action with source `J` exactly when the
  evaluated formal Maxwell operator equals `μ₀ J` — the inhomogeneous Maxwell
  equations `∂_μ F^{μν} = μ₀ J^ν`. -/
theorem isExtrema_iff_evalPotential_maxwellOperator (𝓕 : FreeSpace)
    (A : ElectromagneticPotential 3) (hA : ContDiff ℝ ∞ A)
    (J : LorentzCurrentDensity 3) (hJ : ContDiff ℝ ∞ J) :
    ElectromagneticPotential.IsExtrema 𝓕 A J ↔
      ∀ x ν, evalPotential A (maxwellOperator ν) x = 𝓕.μ₀ * J x ν := by
  have h2 : ContDiff ℝ 2 A := hA.of_le ENat.LEInfty.out
  have hdiffF : ∀ μ' ν' : Fin 1 ⊕ Fin 3,
      Differentiable ℝ (evalPotential A (fieldStrength 0 μ' ν')) := by
    intro μ' ν'
    rw [show evalPotential A (fieldStrength 0 μ' ν') =
        ∂_ μ' (coPotential A ν') - ∂_ ν' (coPotential A μ') from by
      rw [fieldStrength, map_sub]
      simp only [zero_add, evalPotential_coord, derivMultiset_singleton]]
    exact (SpaceTime.differentiable_deriv _ _ (contDiff_coPotential h2 ν')).sub
      (SpaceTime.differentiable_deriv _ _ (contDiff_coPotential h2 μ'))
  rw [ElectromagneticPotential.isExtrema_iff_fieldStrengthMatrix A hA J hJ]
  refine forall_congr' fun x => forall_congr' fun ν => Iff.of_eq ?_
  refine congrArg (· = 𝓕.μ₀ * J x ν) ?_
  have hFmat : ∀ μ' : Fin 1 ⊕ Fin 3, (fun y => A.fieldStrengthMatrix y (μ', ν)) =
      fun y => (η μ' μ' * η ν ν) * evalPotential A (fieldStrength 0 μ' ν) y := by
    intro μ'
    funext y
    rw [evalPotential_fieldStrength_zero A (h2.differentiable two_ne_zero) μ' ν y]
    rcases mul_self_eq_one_iff.mp (minkowskiMatrix.η_apply_mul_η_apply_diag μ') with
      h1 | h1 <;>
      rcases mul_self_eq_one_iff.mp (minkowskiMatrix.η_apply_mul_η_apply_diag ν) with
        h2' | h2' <;>
      rw [h1, h2'] <;> ring
  calc ∑ μ, ∂_ μ (A.fieldStrengthMatrix · (μ, ν)) x
      = ∑ μ, (η μ μ * η ν ν) * ∂_ μ (evalPotential A (fieldStrength 0 μ ν)) x := by
        refine Finset.sum_congr rfl fun μ _ => ?_
        rw [show (fun y => A.fieldStrengthMatrix y (μ, ν)) =
            fun y => (η μ μ * η ν ν) * evalPotential A (fieldStrength 0 μ ν) y from
          hFmat μ, deriv_const_mul_apply _ _ (hdiffF μ ν)]
    _ = evalPotential A (maxwellOperator ν) x := by
        rw [maxwellOperator, map_sum, Finset.sum_apply]
        refine Finset.sum_congr rfl fun μ _ => ?_
        rw [map_smul, Pi.smul_apply, smul_eq_mul,
          evalPotential_fieldStrength_singleton A h2 μ μ ν]

/-!

## E. Compatibility with concrete Lorentz transformations

The formal Lorentz action of `Physlib.Particles.QED.Basic` is matched by the concrete
action `(Λ • A) x = Λ • A (Λ⁻¹ • x)` of `Physlib.Electromagnetism`:
evaluating the field strength on the transformed potential is evaluating the
Lorentz-transformed jet on the original potential at the transformed point.

-/

/-- **Compatibility of the formal and concrete Lorentz actions**: the
  evaluation of the field strength on `Λ • A` at `x` is the evaluation of its
  formal Lorentz transform on `A` at `Λ⁻¹ • x`, matching the equivariance
  `Physlib.Electromagnetism.Kinematics.FieldStrength.toFieldStrength_equivariant`
  on the concrete side. -/
theorem evalPotential_fieldStrength_lorentzAction (Λ : LorentzGroup 3)
    (A : ElectromagneticPotential 3) (hA : Differentiable ℝ A)
    (μ ν : Fin 1 ⊕ Fin 3) (x : SpaceTime 3) :
    evalPotential (Λ • A) (fieldStrength 0 μ ν) x =
      evalPotential A (lorentzAction Λ (fieldStrength 0 μ ν)) (Λ⁻¹ • x) := by
  have hinv : ∀ a μ' : Fin 1 ⊕ Fin 3, (Λ⁻¹).1 a μ' = η a a * Λ.1 μ' a * η μ' μ' := by
    intro a μ'
    rw [LorentzGroup.inv_eq_dual]
    exact minkowskiMatrix.dual_apply _ a μ'
  have hΛA : Differentiable ℝ (Λ • A) :=
    ElectromagneticPotential.differentiable_action Λ A hA
  rw [evalPotential_fieldStrength_zero _ hΛA μ ν x,
    ElectromagneticPotential.fieldStrengthMatrix_equivariant A Λ hA,
    lorentzAction_fieldStrength_zero]
  simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  simp only [evalPotential_fieldStrength_zero A hA]
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rcases mul_self_eq_one_iff.mp (minkowskiMatrix.η_apply_mul_η_apply_diag a) with h1 | h1 <;>
    rcases mul_self_eq_one_iff.mp (minkowskiMatrix.η_apply_mul_η_apply_diag b) with h2 | h2 <;>
    rw [hinv a μ, hinv b ν, h1, h2] <;> ring

/-!

## C. Compatibility with concrete gauge transformations

The formal gauge invariance of `Physlib.Particles.QED.GaugeInvariance` is matched on
the concrete side: the evaluation of the field strength, and hence of the
Maxwell term, is unchanged when the potential is replaced by `A + ∂χ`.

-/

lemma differentiable_gaugeTransform {A : ElectromagneticPotential 3} {χ : SpaceTime 3 → ℝ}
    (hA : Differentiable ℝ A) (hχ : ContDiff ℝ 2 χ) :
    Differentiable ℝ (ElectromagneticPotential.gaugeTransform χ A) :=
  hA.add (ElectromagneticPotential.differentiable_ofGradient hχ)

/-- The evaluated field strength is invariant under the concrete gauge
  transformation `A ↦ A + ∂χ`, matching the formal gauge invariance
  `Physlib.Particles.QED.GaugeInvariance.Photon.JetAlgebra.gaugeAction_fieldStrength`. -/
theorem evalPotential_fieldStrength_gaugeTransform (A : ElectromagneticPotential 3)
    (χ : SpaceTime 3 → ℝ) (hA : Differentiable ℝ A) (hχ : ContDiff ℝ 2 χ)
    (μ ν : Fin 1 ⊕ Fin 3) (x : SpaceTime 3) :
    evalPotential (ElectromagneticPotential.gaugeTransform χ A) (fieldStrength 0 μ ν) x =
      evalPotential A (fieldStrength 0 μ ν) x := by
  rw [evalPotential_fieldStrength_zero _ (differentiable_gaugeTransform hA hχ),
    evalPotential_fieldStrength_zero A hA,
    ElectromagneticPotential.fieldStrengthMatrix_gaugeTransform A χ hA hχ]

/-- The Maxwell Lagrangian is gauge invariant, as read off from the jet algebra. -/
theorem evalPotential_maxwellTerm_gaugeTransform (A : ElectromagneticPotential 3)
    (χ : SpaceTime 3 → ℝ) (hA : Differentiable ℝ A) (hχ : ContDiff ℝ 2 χ)
    (x : SpaceTime 3) :
    evalPotential (ElectromagneticPotential.gaugeTransform χ A) maxwellTerm x =
      evalPotential A maxwellTerm x := by
  rw [maxwellTerm, map_sum, map_sum]
  simp only [Finset.sum_apply, map_sum, map_smul, Pi.smul_apply, smul_eq_mul, map_mul,
    Pi.mul_apply]
  refine Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun ν _ => ?_
  rw [evalPotential_fieldStrength_gaugeTransform A χ hA hχ]

end JetAlgebra

end Photon

end QED
