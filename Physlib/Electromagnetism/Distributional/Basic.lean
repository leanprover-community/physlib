/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.SpaceAndTime.TimeAndSpace.ConstantTimeDist
public import Physlib.Mathematics.VariationalCalculus.HasVarAdjDeriv
public import Physlib.SpaceAndTime.Space.DistOfFunction
public import Physlib.SpaceAndTime.SpaceTime.TimeSlice

/-!

# The Electromagnetic Potential

## i. Overview

The electromagnetic potential `A^μ` is the fundamental objects in
electromagnetism. Mathematically it is related to a connection
on a `U(1)`-bundle.

We define the electromagnetic potential as a distribution from
spacetime to contravariant Lorentz vectors.

## ii. Key results

- `DistElectromagneticPotential` : the type of electromagnetic potentials as distributions.

## iii. Table of contents

- A. The electromagnetic potential as a distribution
  - A.1. Constructors
  - A.2. The derivative of the electromagnetic potential as a distribution
  - A.3. The derivative in terms of the basis

## iv. References

* https://quantummechanics.ucsd.edu/ph130a/130_notes/node452.html. [ref: ucsd_ph130a_node452]
* https://ph.qmul.ac.uk/sites/default/files/EMT10new.pdf. [ref: qmul_emt10_notes]
-/

@[expose] public section

namespace Electromagnetism
open Module realLorentzTensor
open TensorSpecies
open Tensor

/-!

## A. The electromagnetic potential as a distribution

-/

/-- The electromagnetic potential as a distribution and as a tensor `A^μ`. -/
noncomputable abbrev DistElectromagneticPotential (d : ℕ := 3) :=
  (SpaceTime d) →d[ℝ] Lorentz.Vector d

namespace DistElectromagneticPotential
open TensorSpecies
open Tensor
open SpaceTime
open TensorProduct
open minkowskiMatrix SchwartzMap
attribute [-simp] Fintype.sum_sum_type
attribute [-simp] Nat.succ_eq_add_one

/-!

### A.1. Constructors

-/

/-- The creation of an electromagnetic potential from a scalar potential. -/
noncomputable def ofScalarPotential {d} (c : SpeedOfLight) :
    ((Time × Space d) →d[ℝ] ℝ) →ₗ[ℝ] DistElectromagneticPotential d where
  toFun φ := Lorentz.Vector.ofTemporalComponent ∘L (distTimeSlice c).symm (((1 : ℝ) / c.val) • φ)
  map_add' φ₁ φ₂ := by
    ext ε
    simp
  map_smul' r φ := by
    ext ε
    simp only [one_div, map_smul, ContinuousLinearMap.comp_smulₛₗ, map_inv₀, RingHom.id_apply,
      FunLike.coe_smul, ContinuousLinearMap.coe_comp, Pi.smul_apply,
      Function.comp_apply]
    rw [smul_comm]

/-- The creation of an electromagnetic potential from a static scalar potential. -/
noncomputable def ofStaticScalarPotential {d} (c : SpeedOfLight) :
    ((Space d) →d[ℝ] ℝ) →ₗ[ℝ] DistElectromagneticPotential d :=
  ofScalarPotential c ∘ₗ Space.constantTime

/-- The creation of an electromagnetic potential from a static scalar-potential function.

If the function is distribution-bounded, it is first promoted to a distribution using
`Space.distOfFunction`. Otherwise the constructor returns zero. -/
noncomputable def ofStaticScalarPotentialFunction {d} (c : SpeedOfLight)
    (φ : Space d → ℝ) : DistElectromagneticPotential d := by
  classical
  exact if hφ : Space.IsDistBounded φ then
    ofStaticScalarPotential c (Space.distOfFunction φ hφ) else 0

@[simp]
lemma ofStaticScalarPotentialFunction_of_isDistBounded {d} (c : SpeedOfLight)
    (φ : Space d → ℝ) (hφ : Space.IsDistBounded φ) :
    ofStaticScalarPotentialFunction c φ =
      ofStaticScalarPotential c (Space.distOfFunction φ hφ) := by
  classical
  simp [ofStaticScalarPotentialFunction, hφ]

@[simp]
lemma ofStaticScalarPotentialFunction_eq_zero_of_not_isDistBounded {d}
    (c : SpeedOfLight) (φ : Space d → ℝ) (hφ : ¬ Space.IsDistBounded φ) :
    ofStaticScalarPotentialFunction c φ = 0 := by
  classical
  simp [ofStaticScalarPotentialFunction, hφ]

/-- The creation of an electromagnetic potential from a vector potential. -/
noncomputable def ofVectorPotential {d} (c : SpeedOfLight) :
    ((Time × Space d) →d[ℝ] EuclideanSpace ℝ (Fin d)) →ₗ[ℝ]
    DistElectromagneticPotential d where
  toFun A := (distTimeSlice c).symm (Lorentz.Vector.ofSpatialComponent ∘L A)
  map_add' A₁ A₂ := by
    ext ε
    simp
  map_smul' r A := by
    ext ε
    simp

/-- The creation of an electromagnetic potential from a static vector potential. -/
noncomputable def ofStaticVectorPotential {d} (c : SpeedOfLight) :
    ((Space d) →d[ℝ] EuclideanSpace ℝ (Fin d)) →ₗ[ℝ] DistElectromagneticPotential d :=
  ofVectorPotential c ∘ₗ Space.constantTime

TODO "Add a constructor for DistElectromagneticPotential from electric and
  magnetic fields."

/-!

### A.2. The derivative of the electromagnetic potential as a distribution

-/

lemma distTensorDeriv_eq_sum_sum {d} (A : DistElectromagneticPotential d)
    (ε : 𝓢(SpaceTime d, ℝ)) :
    distTensorDeriv A ε =∑ μ, ∑ ν, (SpaceTime.distDeriv μ A ε ν) •
      Lorentz.CoVector.basis μ ⊗ₜ[ℝ] Lorentz.Vector.basis ν := by
  simp [distTensorDeriv_apply]
  congr
  funext μ
  conv_lhs => rw [← Lorentz.Vector.basis.sum_repr (SpaceTime.distDeriv μ A ε)]
  rw [tmul_sum]
  congr
  funext ν
  simp
  rfl

/-!

### A.3. The derivative in terms of the basis

-/

@[simp]
lemma distTensorDeriv_basis_repr_apply {d} {μν : (Fin 1 ⊕ Fin d) × (Fin 1 ⊕ Fin d)}
    (A : DistElectromagneticPotential d)
    (ε : 𝓢(SpaceTime d, ℝ)) :
    (Lorentz.CoVector.basis.tensorProduct Lorentz.Vector.basis).repr (distTensorDeriv A ε) μν =
    distDeriv μν.1 A ε μν.2 := by
  match μν with
  | (μ, ν) =>
  rw [distTensorDeriv_eq_sum_sum]
  simp only [map_sum, map_smul, Finsupp.coe_finsetSum, Finsupp.coe_smul, Finset.sum_apply,
    Pi.smul_apply, Basis.tensorProduct_repr_tmul_apply, Basis.repr_self, smul_eq_mul]
  rw [Finset.sum_eq_single μ, Finset.sum_eq_single ν]
  · simp
  · intro μ' _ h
    simp [h]
  · simp
  · intro ν' _ h
    simp [h]
  · simp

lemma toTensor_distTensorDeriv_basis_repr_apply {d} (A : DistElectromagneticPotential d)
    (ε : 𝓢(SpaceTime d, ℝ)) (b : ComponentIdx (S := realLorentzTensor d)
      (Fin.append ![Color.down] ![Color.up])) :
    (Tensor.basis _).repr (Tensorial.toTensor (distTensorDeriv A ε)) b =
    distDeriv (b 0) A ε (b 1) := by
  rw [Tensorial.basis_toTensor_apply]
  rw [Tensorial.basis_map_prod]
  simp only [Nat.reduceSucc, Nat.reduceAdd, Basis.repr_reindex, Fin.isValue]
  rw [Lorentz.Vector.tensor_basis_map_eq_basis_reindex,
    Lorentz.CoVector.tensor_basis_map_eq_basis_reindex]
  have hb : (((Lorentz.CoVector.basis (d := d)).reindex
      Lorentz.CoVector.indexEquiv.symm).tensorProduct
      (Lorentz.Vector.basis.reindex Lorentz.Vector.indexEquiv.symm)) =
      ((Lorentz.CoVector.basis (d := d)).tensorProduct (Lorentz.Vector.basis (d := d))).reindex
      (Lorentz.CoVector.indexEquiv.symm.prodCongr Lorentz.Vector.indexEquiv.symm) := by
    ext b
    match b with
    | ⟨i, j⟩ =>
    simp
  rw [hb]
  rw [Finsupp.equivMapDomain_apply, Module.Basis.repr_reindex_apply,
    distTensorDeriv_basis_repr_apply]
  rfl

end DistElectromagneticPotential

end Electromagnetism
