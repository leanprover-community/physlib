/-
Copyright (c) 2026 Nathaneal Sajan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathaneal Sajan
-/
module

public import Physlib.ClassicalFieldTheory.GaugeTheory.LocalGaugeData.InfinitesimalAction
public import Physlib.ClassicalFieldTheory.GaugeTheory.LocalGaugeData.Truncation
public import Physlib.Particles.StandardModel.GaugeGroup.MaurerCartan.Basic
/-!
# The Standard Model gauge group as local gauge data

## i. Overview

The generic theory of gauge and matter fields is stated against a supplied local-gauge-data
package `jets : LocalGaugeData G 𝔤 G₀ 𝔤J`. The Standard Model already carries all of its
data, for the jet gauge group `JetGaugeGroupI` of `SU(3) × SU(2) × U(1)` with jet Lie algebra
`JetGaugeAlgebra`, global group `GaugeGroupI` and gauge algebra `GaugeAlgebra`.

This file packages those existing constructions as the named term
`StandardModel.localGaugeData`, and records the rules that compute the generic interface
back to the Standard Model definition it came from, so that the existing Standard Model
lemmas apply to it unchanged. It is a term, not an instance: every generic construction
receives it as an argument. Its faithfulness — Taylor determinacy of the jet gauge algebra
and the vanishing of the Maurer–Cartan form exactly on constant jets — is a property of that
package rather than a choice, so it is an instance.

Everything the generic theory derives from a package is thereby available for the Standard
Model: the Taylor–Leibniz theorem for the adjoint action, the truncation filtration of the
jet gauge group by the Maurer–Cartan form, the covariance of the covariant derivative, and
the determination of a pure jet by its symmetrized Maurer–Cartan data. Its freeness, the
remaining power-series input to the classification of invariants, is
`instFreeLocalGaugeData` in `GaugeGroup/MaurerCartan/Freeness.lean`.

## ii. Key results

- `StandardModel.localGaugeData` : the Standard Model gauge group as local gauge data.
- `StandardModel.localGaugeData_eval`, `StandardModel.localGaugeData_deriv`,
  `StandardModel.localGaugeData_maurerCartan`, `StandardModel.localGaugeData_adjointCoeff_apply`,
  … : the generic interface computed back to the Standard Model definitions.
- `StandardModel.instFaithfulLocalGaugeData` : the package is faithful.

## iii. Table of contents

- A. The local-gauge-data package
- B. The generic interface in Standard Model terms
- C. Faithfulness

-/

@[expose] public section

namespace StandardModel

open JetGaugeAlgebra

/-!

## A. The local-gauge-data package

`LocalGaugeData` is an ordinary structure, so this is a named term supplied at each use site,
not an instance found by search. The four carriers do not determine it — a truncated jet
group over the same gauge group would be a second, equally canonical package — so nothing
is registered globally.

-/

/-- The Standard Model gauge group as local gauge data, for the jet gauge group
  `JetGaugeGroupI` and its Lie algebra `JetGaugeAlgebra` over the global group
  `GaugeGroupI` and gauge algebra `GaugeAlgebra`. Nothing is redefined. Every data field
  is an existing Standard Model construction and every proof field an existing Standard
  Model lemma. -/
noncomputable def localGaugeData :
    LocalGaugeData JetGaugeGroupI GaugeAlgebra GaugeGroupI JetGaugeAlgebra where
  eval := JetGaugeGroupI.eval
  ofConstant := JetGaugeGroupI.ofConstant
  eval_ofConstant := JetGaugeGroupI.eval_ofConstant
  evalLie := JetGaugeAlgebra.eval
  ofConstantLie := JetGaugeAlgebra.ofConstant
  ofConstantLie_lie := JetGaugeAlgebra.ofConstant_lie
  evalLie_ofConstantLie := JetGaugeAlgebra.eval_ofConstant
  deriv := JetGaugeAlgebra.deriv
  deriv_comm := JetGaugeAlgebra.deriv_comm
  deriv_bracket := JetGaugeAlgebra.deriv_bracket
  deriv_ofConstantLie := JetGaugeAlgebra.deriv_ofConstant
  coord := JetGaugeAlgebra.coord
  deriv_coord := JetGaugeAlgebra.deriv_coord
  evalLie_coord := JetGaugeAlgebra.eval_coord
  coord_lie := JetGaugeAlgebra.coord_lie
  adjoint := JetGaugeAlgebra.adjoint
  adjoint_lie := JetGaugeAlgebra.adjointMap_lie
  adjointValue := GaugeAlgebra.adjoint
  evalLie_adjoint := JetGaugeAlgebra.eval_adjointMap
  maurerCartan := maurerCartanForm
  maurerCartan_ofConstant := fun g μ => congrFun (maurerCartanForm_ofConstant g) μ
  maurerCartan_cocycle := maurerCartanForm_cocycle
  maurerCartan_structure := maurerCartanForm_structure
  deriv_adjoint := deriv_adjointMap

/-!

## B. The generic interface in Standard Model terms

These rules point from the generic interface to the Standard Model definitions, which is
the direction in which the existing Standard Model lemmas become applicable.

-/

@[simp]
lemma localGaugeData_eval : localGaugeData.eval = JetGaugeGroupI.eval := rfl

@[simp]
lemma localGaugeData_ofConstant : localGaugeData.ofConstant = JetGaugeGroupI.ofConstant := rfl

@[simp]
lemma localGaugeData_evalLie : localGaugeData.evalLie = JetGaugeAlgebra.eval := rfl

@[simp]
lemma localGaugeData_ofConstantLie :
    localGaugeData.ofConstantLie = JetGaugeAlgebra.ofConstant := rfl

@[simp]
lemma localGaugeData_adjointValue : localGaugeData.adjointValue = GaugeAlgebra.adjoint := rfl

@[simp]
lemma localGaugeData_deriv (μ : Fin 1 ⊕ Fin 3) :
    localGaugeData.deriv μ = JetGaugeAlgebra.deriv μ := rfl

/-- The generic iterated derivative is the Standard Model iterated derivative, both being
  the same fold of `JetGaugeAlgebra.deriv` over the multiset of directions. -/
@[simp]
lemma localGaugeData_iteratedDeriv (s : Multiset (Fin 1 ⊕ Fin 3)) :
    localGaugeData.iteratedDeriv s = JetGaugeAlgebra.iteratedDeriv s := rfl

@[simp]
lemma localGaugeData_coord (μ : Fin 1 ⊕ Fin 3) :
    localGaugeData.coord μ = JetGaugeAlgebra.coord μ := rfl

@[simp]
lemma localGaugeData_adjoint : localGaugeData.adjoint = JetGaugeAlgebra.adjoint := rfl

@[simp]
lemma localGaugeData_maurerCartan : localGaugeData.maurerCartan = maurerCartanForm := rfl

/-- The adjoint Taylor coefficients of the package, written out in Standard Model terms. -/
@[simp]
lemma localGaugeData_adjointCoeff_apply (U : JetGaugeGroupI) (x : Multiset (Fin 1 ⊕ Fin 3))
    (a : GaugeAlgebra) :
    localGaugeData.adjointCoeff U x a =
      JetGaugeAlgebra.eval (JetGaugeAlgebra.iteratedDeriv x
        (JetGaugeAlgebra.adjointMap U (JetGaugeAlgebra.ofConstant a))) := rfl

/-- The `su(3)` component of the adjoint Taylor coefficients. -/
lemma localGaugeData_adjointCoeff_toSU3Matrix (U : JetGaugeGroupI)
    (p : Multiset (Fin 1 ⊕ Fin 3)) (b : GaugeAlgebra) :
    (localGaugeData.adjointCoeff U p b).toSU3Matrix
      = ((U.1.1 * b.toSU3Matrix.map (MvPowerSeries.C : ℂ → JetRing) * star U.1.1).map fun f =>
          MvPowerSeries.constantCoeff (p.foldl (fun h ρ => MvPowerSeries.pderiv ℂ ρ h) f)) := by
  rw [localGaugeData_adjointCoeff_apply, eval_iteratedDeriv_toSU3Matrix, adjointMap_toSU3Matrix,
    ofConstant_toSU3Matrix]

/-- The `su(2)` component of the adjoint Taylor coefficients. -/
lemma localGaugeData_adjointCoeff_toSU2Matrix (U : JetGaugeGroupI)
    (p : Multiset (Fin 1 ⊕ Fin 3)) (b : GaugeAlgebra) :
    (localGaugeData.adjointCoeff U p b).toSU2Matrix
      = ((U.2.1.1 * b.toSU2Matrix.map (MvPowerSeries.C : ℂ → JetRing) * star U.2.1.1).map
          fun f => MvPowerSeries.constantCoeff
            (p.foldl (fun h ρ => MvPowerSeries.pderiv ℂ ρ h) f)) := by
  rw [localGaugeData_adjointCoeff_apply, eval_iteratedDeriv_toSU2Matrix, adjointMap_toSU2Matrix,
    ofConstant_toSU2Matrix]

/-- The `u(1)` component of the adjoint Taylor coefficients. -/
lemma localGaugeData_adjointCoeff_toU1Value (U : JetGaugeGroupI)
    (p : Multiset (Fin 1 ⊕ Fin 3)) (b : GaugeAlgebra) :
    (localGaugeData.adjointCoeff U p b).toU1Value
      = MvPowerSeries.constantCoeff (p.foldl (fun h ρ => MvPowerSeries.pderiv ℂ ρ h)
          (MvPowerSeries.C b.toU1Value)) := by
  rw [localGaugeData_adjointCoeff_apply, eval_iteratedDeriv_toU1Value, adjointMap_toU1Value,
    ofConstant_toU1Value]

/-!

## C. Faithfulness

-/

/-- The Standard Model package is faithful: an element of the jet gauge algebra is
  determined by the base-point values of its iterated derivatives, and a jet whose
  Maurer–Cartan form vanishes is the constant jet of its value. Both are statements about
  power series, proved from the matrix definitions in
  `JetGaugeAlgebra.ext_of_eval_iteratedDeriv` and `maurerCartanForm_eq_zero_iff_ofConstant`.
  Unlike the package itself this is a property of it and not a choice, so it is an
  instance. -/
instance instFaithfulLocalGaugeData : localGaugeData.Faithful where
  ext_of_evalLie_iteratedDeriv h := JetGaugeAlgebra.ext_of_eval_iteratedDeriv h
  eq_ofConstant_of_maurerCartan_eq_zero h := by
    obtain ⟨c, hc⟩ := (maurerCartanForm_eq_zero_iff_ofConstant _).mp h
    rw [hc, localGaugeData_eval, localGaugeData_ofConstant, JetGaugeGroupI.eval_ofConstant]

end StandardModel
