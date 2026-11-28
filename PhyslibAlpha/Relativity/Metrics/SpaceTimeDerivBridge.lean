/-
Copyright (c) 2026 Alex Vergara Gil. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Vergara Gil
-/
module

public import Physlib.SpaceAndTime.SpaceTime.Derivatives
public import PhyslibAlpha.Mathematics.Calculus.CoordDeriv

/-!

# Coordinate and spacetime derivative bridge

Bridge between coordinate partial derivatives on `Fin 4 → ℝ` and `SpaceTime.deriv`.

## i. Overview

Under the standard index equivalence `finSumFinEquiv : Fin 1 ⊕ Fin 3 ≃ Fin 4`, a coordinate
partial derivative agrees with Physlib's coordinate-free spacetime derivative.

## ii. Key results

- `CoordinateCurvature.coordDeriv_eq_spaceTime_deriv` : coordinate/spacetime derivative bridge.

## iii. Table of contents

- A. Spacetime derivative bridge

## iv. References

* R. M. Wald, *General Relativity* (1984), Ch. 3 (Sec. 3.1). [ref: wald_1984_general_relativity]
* S. M. Carroll, *Lecture Notes on General Relativity* (1997), Ch. 3 (Sec. 3.1)
  (https://arxiv.org/pdf/gr-qc/9712019#page=57). [ref: Carroll1997]
-/

@[expose] public section

namespace GeneralRelativity

namespace CoordinateCurvature

/-!

## A. Spacetime derivative bridge

The equivalence identifies the coordinate axis with the corresponding spacetime basis vector.

-/

/-- Coordinate partial derivatives on `Fin 4 → ℝ` agree with `Physlib`'s `SpaceTime.deriv` (`∂_`)
under the standard index equivalence `finSumFinEquiv : Fin 1 ⊕ Fin 3 ≃ Fin 4`. -/
lemma coordDeriv_eq_spaceTime_deriv {f : SpaceTime 3 → ℝ} (μ : Fin 1 ⊕ Fin 3) (y : SpaceTime 3)
    (hf : DifferentiableAt ℝ f y) :
    coordDeriv (finSumFinEquiv μ) (fun x : Fin 4 → ℝ => f (fun α => x (finSumFinEquiv α)))
        (fun k => y (finSumFinEquiv.symm k)) =
      SpaceTime.deriv μ f y := by
  let e : Fin 1 ⊕ Fin 3 ≃ Fin 4 := finSumFinEquiv
  let L : (Fin 4 → ℝ) →L[ℝ] SpaceTime 3 :=
    LinearMap.toContinuousLinearMap
      { toFun := fun x α => x (e α)
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
  have hLsingle : L (Pi.single (e μ) (1 : ℝ) : Fin 4 → ℝ) = Lorentz.Vector.basis μ := by
    ext ν
    simp [L, Pi.single_apply, e.injective.eq_iff, eq_comm, Lorentz.Vector.basis_apply]
  have hx : L (fun k => y (e.symm k)) = y := by
    ext α; simp [L, e]
  have hcomp : HasFDerivAt (f ∘ L) ((fderiv ℝ f y).comp L) (fun k => y (e.symm k)) := by
    have hy : HasFDerivAt f (fderiv ℝ f y) (L (fun k => y (e.symm k))) := by
      rw [hx]; exact hf.hasFDerivAt
    exact hy.comp _ L.hasFDerivAt
  show coordDeriv (e μ) (f ∘ L) (fun k => y (e.symm k)) = SpaceTime.deriv μ f y
  rw [coordDeriv_eq_fderiv hcomp.differentiableAt, hcomp.fderiv,
    ContinuousLinearMap.comp_apply, hLsingle]
  rfl

end CoordinateCurvature

end GeneralRelativity
