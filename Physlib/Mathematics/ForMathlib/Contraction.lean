/-
Copyright (c) 2026 Andrea Pari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrea Pari
-/
module

public import Mathlib.LinearAlgebra.Dual.Basis
public import Mathlib.LinearAlgebra.PerfectPairing.Basic

/-!

# The coordinate pairing of two bases

Two bases with the same labels pair two modules by their coordinates.

## i. Overview

Two modules `M` and `N` with bases `b` and `b'` labelled by the same finite type `ι` pair by their
coordinates, `(x, y) ↦ ∑_I (b x)_I (b' y)_I` (`coordPairing`). It is Mathlib's `b'.toDual`, applied
after the equivalence `b.equiv b'` that sends `b I` to `b' I`. The two bases are dual for this
pairing, and it is a perfect pairing in Mathlib's sense, so it identifies `N` with the dual of `M`.

For Lorentz tensors take `M = ℝ⁴` the vectors `x^μ` with the standard basis, and `N` the covectors
`w_μ` with the dual basis. The coordinate pairing is the contraction `x^μ w_μ`.

## ii. Key results

- `Module.Basis.coordPairing` : the coordinate pairing `∑_I (b x)_I (b' y)_I` of two bases with
  the same labels.
- `Module.Basis.coordPairing_basis_basis` : the two bases are dual for the coordinate pairing, and
  `Module.Basis.eq_coordPairing` : it is the only such pairing.
- `Module.Basis.isPerfPair_coordPairing` : the coordinate pairing is a perfect pairing.

## iii. Table of contents

- A. The coordinate pairing of two bases

## iv. References

There are no known references for the material in this module.

-/

@[expose] public section

namespace Module.Basis

open TensorProduct

/-!

## A. The coordinate pairing of two bases

-/

variable {R ι M N : Type*} [CommSemiring R] [Fintype ι] [DecidableEq ι] [AddCommMonoid M]
    [Module R M] [AddCommMonoid N] [Module R N]

/-- The coordinate pairing `M ⊗ N → R` of two bases with the same labels. It sends `x ⊗ y` to
`b'.toDual x' y`, where `x'` is the vector of `N` with the coordinates of `x`. -/
noncomputable def coordPairing (b : Module.Basis ι R M) (b' : Module.Basis ι R N) :
    M ⊗[R] N →ₗ[R] R :=
  TensorProduct.lift (b'.toDual ∘ₗ (b.equiv b' (Equiv.refl ι)).toLinearMap)

/-- Pairing with the second basis reads off a coordinate, `b.coordPairing b' (x ⊗ₜ b' J) = x_J`. -/
lemma coordPairing_tmul_basis (b : Module.Basis ι R M) (b' : Module.Basis ι R N) (x : M) (J : ι) :
    b.coordPairing b' (x ⊗ₜ[R] b' J) = b.equivFun x J := by
  simp [coordPairing, Module.Basis.toDual_eq_repr, Module.Basis.equiv]

/-- `b.coordPairing b' (x ⊗ₜ y) = ∑_I (b x)_I (b' y)_I`. -/
lemma coordPairing_tmul (b : Module.Basis ι R M) (b' : Module.Basis ι R N) (x : M) (y : N) :
    b.coordPairing b' (x ⊗ₜ[R] y) = ∑ I, b.equivFun x I * b'.equivFun y I := by
  conv_lhs => rw [← b'.sum_equivFun y, TensorProduct.tmul_sum, map_sum]
  simp_rw [TensorProduct.tmul_smul, map_smul, coordPairing_tmul_basis, smul_eq_mul, mul_comm]

/-- The two bases are dual, `b.coordPairing b' (b I ⊗ₜ b' J) = δ_{IJ}`. -/
lemma coordPairing_basis_basis (b : Module.Basis ι R M) (b' : Module.Basis ι R N) (I J : ι) :
    b.coordPairing b' (b I ⊗ₜ[R] b' J) = if I = J then 1 else 0 := by
  rw [coordPairing_tmul_basis, Module.Basis.equivFun_self]

/-- A pairing for which the two bases are dual is the coordinate pairing. -/
lemma eq_coordPairing (b : Module.Basis ι R M) (b' : Module.Basis ι R N) (p : M ⊗[R] N →ₗ[R] R)
    (h : ∀ I J, p (b I ⊗ₜ[R] b' J) = if I = J then 1 else 0) : p = b.coordPairing b' :=
  (b.tensorProduct b').ext fun IJ => by
    rw [Module.Basis.tensorProduct_apply, h, coordPairing_basis_basis]

/-- Swapping the factors swaps the bases,
`b.coordPairing b' (x ⊗ₜ y) = b'.coordPairing b (y ⊗ₜ x)`. -/
lemma coordPairing_comm (b : Module.Basis ι R M) (b' : Module.Basis ι R N) (x : M) (y : N) :
    b.coordPairing b' (x ⊗ₜ[R] y) = b'.coordPairing b (y ⊗ₜ[R] x) := by
  simp only [coordPairing_tmul, mul_comm]

/-- The coordinate pairing of two bases with the same labels is a perfect pairing. -/
instance isPerfPair_coordPairing (b : Module.Basis ι R M) (b' : Module.Basis ι R N) :
    (TensorProduct.curry (b.coordPairing b')).IsPerfPair where
  -- Curried, the pairing is `b'.toDualEquiv` after matching the bases, an equivalence.
  bijective_left := by
    rw [show TensorProduct.curry (b.coordPairing b') =
      ((b.equiv b' (Equiv.refl ι)).trans b'.toDualEquiv).toLinearMap from
        LinearMap.ext₂ fun _ _ => rfl]
    exact LinearEquiv.bijective _
  bijective_right := by
    rw [show (TensorProduct.curry (b.coordPairing b')).flip =
      ((b'.equiv b (Equiv.refl ι)).trans b.toDualEquiv).toLinearMap from
        LinearMap.ext₂ fun y x => (coordPairing_comm b b' x y).trans rfl]
    exact LinearEquiv.bijective _

end Module.Basis
