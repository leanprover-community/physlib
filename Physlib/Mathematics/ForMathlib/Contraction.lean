/-
Copyright (c) 2026 Andrea Pari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrea Pari
-/
module

public import Mathlib.LinearAlgebra.Matrix.SesquilinearForm
public import Mathlib.LinearAlgebra.PerfectPairing.Basic

/-!

# The coordinate pairing of two bases

Two bases with the same labels pair two modules by their coordinates.

## i. Overview

Two modules `M` and `N` with bases `b` and `b'` labelled by the same finite type `ι` pair by their
coordinates, `(x, y) ↦ ∑_I (b x)_I (b' y)_I` (`coordPairing`). The two bases are dual for this
pairing, and it is a perfect pairing in Mathlib's sense, so it identifies `N` with the dual of `M`.

For Lorentz tensors take `M = ℝ⁴` the vectors `x^μ` with the standard basis, and `N` the covectors
`w_μ` with the dual basis. The coordinate pairing is the contraction `x^μ w_μ`.

## ii. Key results

- `Module.Basis.coordPairing` : the coordinate pairing `∑_I (b x)_I (b' y)_I` of two bases with
  the same labels.
- `Module.Basis.coordPairing_basis_basis` : the two bases are dual for the coordinate pairing, and
  `Module.Basis.eq_coordPairing` : it is the only such pairing.
- `Module.Basis.isPerfPair_coordPairing` : the coordinate pairing is a perfect pairing, through
  `Module.Basis.curry_coordPairing` : it is Mathlib's `toDualEquiv` of the second basis.

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

/-- The coordinate pairing `M ⊗ N → R` of two bases with the same labels, Mathlib's
`Matrix.toLinearMap₂ b b'` of the identity matrix. -/
noncomputable def coordPairing (b : Module.Basis ι R M) (b' : Module.Basis ι R N) :
    M ⊗[R] N →ₗ[R] R :=
  TensorProduct.lift (Matrix.toLinearMap₂ b b' 1)

/-- `b.coordPairing b' (x ⊗ₜ y) = ∑_I (b x)_I (b' y)_I`. -/
lemma coordPairing_tmul (b : Module.Basis ι R M) (b' : Module.Basis ι R N) (x : M) (y : N) :
    b.coordPairing b' (x ⊗ₜ[R] y) = ∑ I, b.equivFun x I * b'.equivFun y I := by
  simp [coordPairing, Matrix.toLinearMap₂_apply, Matrix.one_apply]

/-- Pairing with the second basis reads off a coordinate, `b.coordPairing b' (x ⊗ₜ b' J) = x_J`. -/
lemma coordPairing_tmul_basis (b : Module.Basis ι R M) (b' : Module.Basis ι R N) (x : M) (J : ι) :
    b.coordPairing b' (x ⊗ₜ[R] b' J) = b.equivFun x J := by
  simp [coordPairing_tmul, Module.Basis.equivFun_self]

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

/-- Pairing with the first basis reads off a coordinate, `b.coordPairing b' (b I ⊗ₜ y) = y_I`. -/
lemma coordPairing_basis_tmul (b : Module.Basis ι R M) (b' : Module.Basis ι R N) (I : ι) (y : N) :
    b.coordPairing b' (b I ⊗ₜ[R] y) = b'.equivFun y I := by
  rw [coordPairing_comm, coordPairing_tmul_basis]

/-- The coordinate pairing, curried, sends `x` to the dual vector `b'.toDual` of the vector with
the same coordinates in `b'`. -/
lemma curry_coordPairing (b : Module.Basis ι R M) (b' : Module.Basis ι R N) :
    TensorProduct.curry (b.coordPairing b') =
      ((b.equiv b' (Equiv.refl ι)).trans b'.toDualEquiv).toLinearMap :=
  b.ext fun I => b'.ext fun J => by
    simp [coordPairing_basis_basis, Module.Basis.toDualEquiv_apply, Module.Basis.toDual_apply]

/-- The coordinate pairing of two bases with the same labels is a perfect pairing. -/
instance isPerfPair_coordPairing (b : Module.Basis ι R M) (b' : Module.Basis ι R N) :
    (TensorProduct.curry (b.coordPairing b')).IsPerfPair where
  bijective_left := by rw [curry_coordPairing]; exact LinearEquiv.bijective _
  bijective_right := by
    have : (TensorProduct.curry (b.coordPairing b')).flip =
        TensorProduct.curry (b'.coordPairing b) :=
      LinearMap.ext₂ fun y x => coordPairing_comm b b' x y
    rw [this, curry_coordPairing]; exact LinearEquiv.bijective _

end Module.Basis
