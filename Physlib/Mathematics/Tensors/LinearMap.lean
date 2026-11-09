/-
Copyright (c) 2026 Andrea Pari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrea Pari
-/
module

public import Physlib.Mathematics.Tensors.Species
/-!

# Tensors of two factors as linear maps

A tensor in `V a ⊗ U` is read as a linear map `V a.dual → U`, and the delta is the identity map.

## i. Overview

A tensor `z` in `V a ⊗ U`, for a color `a` of a species `S` and any module `U`, is read as the
linear map `S.toLin z : V a.dual → U` that contracts its input with the first factor of `z`. On a
pure tensor `z = x ⊗ y` it is `v ↦ (v^μ x_μ) y`. Every linear map `V a.dual → U` is `toLin z` for
exactly one `z`. `toLin` is Mathlib's `dualTensorHomEquivOfBasis`, after `Species.dualEquiv`
reads `V a` as the dual of `V a.dual`.

This is how two-index tensors act as maps. A metric `g_μν` is the map `v^μ ↦ v^μ g_μν`, and the
inverse metric `g^μν` is the tensor of the inverse map. The delta
`S.delta c = ∑ μ, e^μ ⊗ e_μ` is the tensor of the identity map, `u^μ δ_μ^ν = u^ν`
(`toLin_delta`). The identity commutes with every group element, so the delta is invariant
(`delta_invariant`).

## ii. Key results

- `Species.toLin` : `V a ⊗ U` as the linear maps `V a.dual → U`, with `Species.toLin_map` : it
  commutes with the group action, `(Λz)(Λv) = Λ(z v)`, and `Species.toLin_lTensor` :
  `(id ⊗ f) z = f ∘ z`.
- `Species.delta` : the delta `δ_μ^ν`, with `Species.toLin_delta` : it is the identity map, and
  `Species.delta_invariant` : it is invariant.
- `Species.basis_repr_toLin` : `toLin` in components, `Species.toMatrix_toLin` : its matrix, and
  `Species.toLin_comp_toLin_of_mul_eq_one` : two such maps are inverse when their matrices are.

## iii. Table of contents

- A. Tensors of two factors as linear maps
- B. The delta
- C. Components

## iv. References

There are no known references for the material in this module.

-/

@[expose] public section

open TensorProduct

namespace Tensors

namespace Species

variable {k : Type} [CommRing k] {G : Type} [Group G] {K : Type} {basisIdx : K → Type}
    [∀ κ, Fintype (basisIdx κ)] [∀ κ, DecidableEq (basisIdx κ)] (S : Species k G K basisIdx)

/-!

## A. Tensors of two factors as linear maps

-/

/-- An element `z` of `V a ⊗ U` as the linear map `V a.dual → U` that contracts a vector with the
first factor of `z`. For a lower color `a` and `z = g` in `V a ⊗ V a` it is `v^μ ↦ v^μ g_μν`.
Every linear map arises so. -/
noncomputable def toLin {a : Color K} {U : Type} [AddCommGroup U] [Module k U] :
    S.V a ⊗[k] U ≃ₗ[k] (S.V a.dual →ₗ[k] U) :=
  -- Mathlib's `dualTensorHomEquivOfBasis`, after reading `V a` as the dual of `V a.dual`.
  (TensorProduct.congr (S.dualEquiv a.dual).toLinearEquiv (LinearEquiv.refl k U)).trans
    (dualTensorHomEquivOfBasis (S.basis a.dual))

/-- A pure tensor `x ⊗ y` acts as `v ↦ (v^μ x_μ) y`, contracting `v` with its first factor. -/
@[simp]
lemma toLin_tmul {a : Color K} {U : Type} [AddCommGroup U] [Module k U] (x : S.V a) (y : U)
    (v : S.V a.dual) : S.toLin (x ⊗ₜ y) v = S.contr a.dual (v ⊗ₜ x) • y :=
  rfl

/-- Applying a linear map `f` to the second factor of `z` composes the linear map of `z` with `f`,
`(id ⊗ f) z = f ∘ z`. -/
lemma toLin_lTensor {a : Color K} {U U' : Type} [AddCommGroup U] [Module k U] [AddCommGroup U']
    [Module k U'] (f : U →ₗ[k] U') (z : S.V a ⊗[k] U) :
    S.toLin (f.lTensor (S.V a) z) = f ∘ₗ S.toLin z := by
  induction z using TensorProduct.inductionOn with
  | tmul x y => ext v; simp
  | add z z' hz hz' => simp only [map_add, hz, hz', LinearMap.comp_add]

/-- `toLin` commutes with the group action, `((Λ ⊗ f) z)(Λx) = f (z x)` for every `Λ : G` and
linear map `f` on `U`. For `f = Λ` this is the equivariance `(Λz)(Λx) = Λ(z x)`. -/
lemma toLin_map (a : Color K) (g : G) {U U' : Type} [AddCommGroup U] [Module k U]
    [AddCommGroup U'] [Module k U'] (f : U →ₗ[k] U') (z : S.V a ⊗[k] U) (x : S.V a.dual) :
    S.toLin (TensorProduct.map (S.rep a g) f z) (S.rep a.dual g x) = f (S.toLin z x) := by
  induction z using TensorProduct.inductionOn with
  | tmul w y => simpa using congrArg (· • f y) (S.contr_invariant a.dual g x w)
  | add z z' hz hz' => simp only [map_add, LinearMap.add_apply, hz, hz']

/-- The linear map of `Λz` is `Λ ∘ z ∘ Λ⁻¹`. -/
lemma toLin_map_rep {a b : Color K} (z : S.V a ⊗[k] S.V b) (g : G) :
    S.toLin (TensorProduct.map (S.rep a g) (S.rep b g) z) =
      S.rep b g ∘ₗ S.toLin z ∘ₗ S.rep a.dual g⁻¹ :=
  LinearMap.ext fun x => by
    rw [LinearMap.comp_apply, LinearMap.comp_apply, ← S.toLin_map, Representation.self_inv_apply]

/-- The linear map of `Λz` is bijective when that of `z` is. -/
lemma toLin_map_rep_bijective {a b : Color K} (z : S.V a ⊗[k] S.V b)
    (h : Function.Bijective (S.toLin z)) (g : G) :
    Function.Bijective (S.toLin (TensorProduct.map (S.rep a g) (S.rep b g) z)) := by
  have hrep (c : Color K) (g : G) : Function.Bijective (S.rep c g) :=
    (Module.End.isUnit_iff _).1 ((Group.isUnit g).map (S.rep c))
  rw [toLin_map_rep, LinearMap.coe_comp, LinearMap.coe_comp]
  exact (hrep b g).comp (h.comp (hrep a.dual g⁻¹))

/-!

## B. The delta

-/

/-- The Kronecker delta `∑ μ, e^μ ⊗ e_μ ∈ V c.dual ⊗ V c`, with components `δ_μ^ν`. The factor of
the dual color is first. -/
noncomputable def delta (c : Color K) : S.V c.dual ⊗[k] S.V c :=
  ∑ μ, S.basis c.dual μ ⊗ₜ S.basis c μ

/-- The delta read as a linear map is the identity, `u^μ δ_μ^ν = u^ν`. -/
lemma toLin_delta (c : Color K) : S.toLin (S.delta c) = LinearMap.id :=
  LinearMap.ext fun v => by simp [delta, contr, Module.Basis.coordPairing_tmul_basis]

/-- The delta is invariant: `Λ` acting on both factors gives `Λ δ = δ`. -/
lemma delta_invariant (c : Color K) (g : G) :
    TensorProduct.map (S.rep c.dual g) (S.rep c g) (S.delta c) = S.delta c := by
  -- `(Λδ)(Λx) = Λ(δx)` by `toLin_map`, and `δx = x` by `toLin_delta`.
  apply S.toLin.injective
  ext x
  simpa [toLin_delta] using S.toLin_map c.dual g (S.rep c g) (S.delta c) (S.rep c g⁻¹ x)

/-!

## C. Components

-/

variable {S}

/-- `toLin` in components. For a lower color `c` and an upper color `d`, `(z v)^ν = v^μ z_μ^ν` for
`z = z_μ^ν e^μ ⊗ e_ν` in `V c ⊗ V d`. -/
lemma basis_repr_toLin (c : Color K) {d : Color K} (z : S.V c ⊗[k] S.V d) (v : S.V c.dual)
    (ν : basisIdx d.kind) :
    (S.basis d).repr (S.toLin z v) ν =
      ∑ μ, (S.basis c.dual).repr v μ * ((S.basis c).tensorProduct (S.basis d)).repr z (μ, ν) := by
  induction z using TensorProduct.inductionOn with
  | add x y hx hy =>
    simp only [map_add, LinearMap.add_apply, Finsupp.add_apply, hx, hy, mul_add,
      Finset.sum_add_distrib]
  | tmul x y =>
    simp [contr_tmul_eq_sum_basis, Finset.sum_mul, mul_assoc, mul_comm ((S.basis d).repr y ν)]

/-- The matrix of `toLin z` is the transpose of the matrix of components of `z`,
`(z v)^ν = z_μ^ν v^μ`. -/
lemma toMatrix_toLin (c : Color K) {d : Color K} (z : S.V c ⊗[k] S.V d) :
    LinearMap.toMatrix (S.basis c.dual) (S.basis d) (S.toLin z) =
      (Matrix.of fun μ ν => ((S.basis c).tensorProduct (S.basis d)).repr z (μ, ν)).transpose := by
  ext ν μ
  simp [LinearMap.toMatrix_apply, basis_repr_toLin, Finsupp.single_apply]

/-- For a lower color `c`, `toLin F ∘ₗ toLin F'` is the identity when the matrices of components of
`F'` and `F` multiply to the identity, `F'^μρ F_ρν = δ^μ_ν`. -/
lemma toLin_comp_toLin_of_mul_eq_one {c : Color K} (F : S.V c ⊗[k] S.V c)
    (F' : S.V c.dual ⊗[k] S.V c.dual)
    (h : Matrix.of (fun μ ν => ((S.basis c.dual).tensorProduct (S.basis c.dual)).repr F' (μ, ν)) *
      Matrix.of (fun μ ν => ((S.basis c).tensorProduct (S.basis c)).repr F (μ, ν)) = 1) :
    S.toLin F ∘ₗ S.toLin F' = LinearMap.id := by
  apply (LinearMap.toMatrix (S.basis c) (S.basis c)).injective
  rw [LinearMap.toMatrix_comp _ (S.basis c.dual), toMatrix_toLin, toMatrix_toLin c.dual,
    ← Matrix.transpose_mul, h, Matrix.transpose_one, LinearMap.toMatrix_id]

end Species

end Tensors
