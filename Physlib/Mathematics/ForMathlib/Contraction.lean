/-
Copyright (c) 2026 Andrea Pari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrea Pari
-/
module

public import Mathlib.LinearAlgebra.Contraction
public import Mathlib.LinearAlgebra.Matrix.SesquilinearForm

/-!

# A tensor read as a linear map through a pairing

A pairing `p : V ⊗ W → R` reads a tensor `z` in `W ⊗ U` as a linear map from `V` to `U`.

## i. Overview

Here `V`, `W` and `U` are spaces, and `x`, `w`, `y` and `z` are elements. The pairing `p` contracts
an element `x` of `V` with an element `w` of `W` to the scalar `p (x ⊗ w)`. A tensor `z` in `W ⊗ U`
reads as the linear map from `V` to `U` that contracts its input with the first factor of `z` and
keeps the second. On a pure tensor this is `x ↦ p (x ⊗ w) • y` for `z = w ⊗ y`.

For Lorentz tensors take `V = ℝ⁴` the vectors `x^μ`, `W = (ℝ⁴)*` the covectors `w_μ`, and
`p (x ⊗ w) = x^μ w_μ`. In the standard basis of `ℝ⁴` and its dual basis, a tensor `z` in `W ⊗ U`
has components `z_μ^A`, where `A` labels a basis of `U`, and reads as the map `x^μ ↦ x^μ z_μ^A`.

- With `U = V` and `z` the Kronecker delta `δ_μ^ν`, the map is `x^μ ↦ x^μ δ_μ^ν = x^ν`, the
  identity.
- With `U = W` and `z` the Minkowski metric `η_μν`, the map is `x^μ ↦ x^μ η_μν = x_ν`, lowering
  the index.

## ii. Key results

- `TensorProduct.pairingToLinearMap` : a tensor in `W ⊗ U` as a linear map `V → U` through `p`.
- `TensorProduct.pairingToLinearMap_tmul` : its value on a pure tensor `w ⊗ y`.
- `TensorProduct.pairingToLinearMap_lTensor` : a linear map applied to the second factor of `z` is
  applied to the values.
- `TensorProduct.pairingToLinearMap_apply` : the value at `x` as `x ⊗ z` with its first two factors
  contracted.
- `Module.Basis.coordPairing`, `Module.Basis.coevaluation` : the coordinate pairing
  `∑_I (b x)_I (b' y)_I` of two bases with the same labels, and the delta `∑_I b_I ⊗ b'_I`.
- `Module.Basis.coordPairing_basis_basis` : the two bases are dual for the coordinate pairing, and
  `Module.Basis.eq_coordPairing` : it is the only such pairing.
- `Module.Basis.pairingToLinearMap_coordPairing_coevaluation` : the delta read through the
  coordinate pairing is the identity.

## iii. Table of contents

- A. Reading a tensor as a linear map
- B. The coordinate pairing of two bases

## iv. References

There are no known references for the material in this module.

-/

@[expose] public section

namespace TensorProduct

variable {R V W U U' : Type*} [CommSemiring R] [AddCommMonoid V] [Module R V] [AddCommMonoid W]
    [Module R W] [AddCommMonoid U] [Module R U] [AddCommMonoid U'] [Module R U']

/-!

## A. Reading a tensor as a linear map

-/

/-- The tensor `z` in `W ⊗ U` read through the pairing `p` as a linear map from `V` to `U`. The
pairing takes the input on the left, `p (x ⊗ w)`, and contracts it with the first factor of `z`.
It is Mathlib's `dualTensorHom R V U` with each `w` read as the form
`x ↦ p (x ⊗ w)`. -/
noncomputable def pairingToLinearMap (p : V ⊗[R] W →ₗ[R] R) : W ⊗[R] U →ₗ[R] V →ₗ[R] U :=
  dualTensorHom R V U ∘ₗ (TensorProduct.curry p).flip.rTensor U

/-- On a pure tensor, `(w ⊗ y)(x) = p (x ⊗ w) • y`. -/
@[simp]
lemma pairingToLinearMap_tmul (p : V ⊗[R] W →ₗ[R] R) (w : W) (y : U) (x : V) :
    pairingToLinearMap p (w ⊗ₜ y) x = p (x ⊗ₜ w) • y := rfl

/-- Applying a linear map `f : U → U'` to the second factor of `z` composes the map of `z` with
`f`. -/
lemma pairingToLinearMap_lTensor (p : V ⊗[R] W →ₗ[R] R) (f : U →ₗ[R] U') (z : W ⊗[R] U) :
    pairingToLinearMap p (f.lTensor W z) = f ∘ₗ pairingToLinearMap p z := by
  induction z using TensorProduct.inductionOn with
  | tmul w y => ext x; simp
  | add z z' hz hz' => simp only [map_add, hz, hz', LinearMap.comp_add]

/-- The value at `x` is `x ⊗ z` with its first two factors contracted by `p`,
`lid (p.rTensor U (assoc.symm (x ⊗ z)))`. This is the form of a contraction built from Mathlib's
associator `TensorProduct.assoc` and unitor `TensorProduct.lid`. -/
lemma pairingToLinearMap_apply (p : V ⊗[R] W →ₗ[R] R) (z : W ⊗[R] U) (x : V) :
    pairingToLinearMap p z x =
      TensorProduct.lid R U (p.rTensor U ((TensorProduct.assoc R V W U).symm (x ⊗ₜ z))) := by
  induction z using TensorProduct.inductionOn with
  | tmul w y => rfl
  | add z z' hz hz' => simp only [map_add, LinearMap.add_apply, tmul_add, hz, hz']

end TensorProduct

namespace Module.Basis

open TensorProduct

/-!

## B. The coordinate pairing of two bases

Two modules `M` and `N` with bases `b` and `b'` labelled by the same finite type `ι` pair by
their coordinates, `(x, y) ↦ ∑_I (b x)_I (b' y)_I` (`coordPairing`), with delta `∑_I b_I ⊗ b'_I`
(`coevaluation`).

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

/-- `b.coordPairing b' (x ⊗ₜ b' J) = x_J`: pairing with the second basis reads off a coordinate. -/
lemma coordPairing_tmul_basis (b : Module.Basis ι R M) (b' : Module.Basis ι R N) (x : M) (J : ι) :
    b.coordPairing b' (x ⊗ₜ[R] b' J) = b.equivFun x J := by
  simp [coordPairing_tmul, Module.Basis.equivFun_self]

/-- `b.coordPairing b' (b I ⊗ₜ b' J) = δ_{IJ}`: the two bases are dual. -/
lemma coordPairing_basis_basis (b : Module.Basis ι R M) (b' : Module.Basis ι R N) (I J : ι) :
    b.coordPairing b' (b I ⊗ₜ[R] b' J) = if I = J then 1 else 0 := by
  rw [coordPairing_tmul_basis, Module.Basis.equivFun_self]

/-- A pairing for which the two bases are dual is the coordinate pairing. -/
lemma eq_coordPairing (b : Module.Basis ι R M) (b' : Module.Basis ι R N) (p : M ⊗[R] N →ₗ[R] R)
    (h : ∀ I J, p (b I ⊗ₜ[R] b' J) = if I = J then 1 else 0) : p = b.coordPairing b' :=
  (b.tensorProduct b').ext fun IJ => by
    rw [Module.Basis.tensorProduct_apply, h, coordPairing_basis_basis]

/-- `b.coordPairing b' (x ⊗ₜ y) = b'.coordPairing b (y ⊗ₜ x)`: swapping slots swaps the bases. -/
lemma coordPairing_comm (b : Module.Basis ι R M) (b' : Module.Basis ι R N) (x : M) (y : N) :
    b.coordPairing b' (x ⊗ₜ[R] y) = b'.coordPairing b (y ⊗ₜ[R] x) := by
  rw [coordPairing_tmul, coordPairing_tmul]
  exact Finset.sum_congr rfl fun I _ => mul_comm _ _

/-- The delta `∑_I b_I ⊗ b'_I ∈ M ⊗ N` of two bases with the same labels. -/
noncomputable def coevaluation (b : Module.Basis ι R M) (b' : Module.Basis ι R N) : M ⊗[R] N :=
  ∑ I, b I ⊗ₜ[R] b' I

/-- The snake law: contracting `x ∈ M` with the first factor of `∑_I b'_I ⊗ b_I` gives `x`. -/
lemma pairingToLinearMap_coordPairing_coevaluation (b : Module.Basis ι R M)
    (b' : Module.Basis ι R N) :
    pairingToLinearMap (b.coordPairing b') (b'.coevaluation b) = LinearMap.id := by
  refine LinearMap.ext fun x => ?_
  rw [coevaluation, map_sum, LinearMap.sum_apply]
  simp only [pairingToLinearMap_tmul, coordPairing_tmul_basis, LinearMap.id_apply]
  exact b.sum_equivFun x

end Module.Basis
