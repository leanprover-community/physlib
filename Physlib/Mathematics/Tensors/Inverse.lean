/-
Copyright (c) 2026 Andrea Pari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrea Pari
-/
module

public import Physlib.Mathematics.Tensors.Metric
/-!

# The inverse of a tensor on two indices

The inverse `g^νμ` of a tensor `g_μν`, defined through the linear map that `g` defines.

## i. Overview

A tensor `g` in `V a ⊗ V b` is also a linear map `S.toLin g : V a.dual → V b`, `v^μ ↦ v^μ g_μν`.
When this map is invertible, its inverse is the tensor `S.inverse g` in `V b.dual ⊗ V a.dual`,
with components `g^νμ`. Otherwise `S.inverse g` is the junk value `0`, so every lemma about it
assumes that `S.toLin g` is bijective. It is `Module.Basis.coordInverse` for the bases, where its
algebra is proved, including `(g⁻¹)⁻¹ = g` (`Module.Basis.coordInverse_coordInverse`).

The inverse satisfies `g_μν g^νρ = δ_μ^ρ` and `g^νμ g_μρ = δ^ν_ρ`, it is unique, it commutes
with the group action, and the inverse of the form at `c` is the form at `c.dual`.

## ii. Key results

- `Species.inverse` is the inverse `g^νμ` of `g_μν`, and `Species.toLin_inverse` gives its
  linear map.
- `Species.contr_mul_inverse` and `Species.contr_inverse_mul` prove `g_μν g^νρ = δ_μ^ρ` and
  `g^νμ g_μρ = δ^ν_ρ`.
- `Species.inverse_eq_left_inv` characterises the inverse as a left inverse.
- `Species.inverse_map_rep` proves `(Λg)⁻¹ = Λ(g⁻¹)`, and `Species.inverse_invariant` that the
  inverse of an invariant tensor is invariant.
- `Species.inverse_form` proves that the inverse of the form at `c` is the form at `c.dual`.

## iii. Table of contents

- A. The inverse
- B. The contraction identities and uniqueness
- C. The inverse commutes with the group action
- D. The inverse of an invariant form

## iv. References

There are no known references for the material in this module.

-/

@[expose] public section

open TensorProduct

namespace Tensor

namespace Species

variable {k : Type} [RCLike k] {K : Type} {G : Type} [Group G] {basisIdx : K → Type}
    [∀ κ, Fintype (basisIdx κ)] [∀ κ, DecidableEq (basisIdx κ)] {S : Species k G K basisIdx}
    {a b : Color K}

/-!

## A. The inverse

-/

variable (S) in
/-- The inverse `g^νμ ∈ V b.dual ⊗ V a.dual` of `g_μν ∈ V a ⊗ V b`, the tensor whose linear map
inverts that of `g`, and the junk value `0` when `S.toLin g` is not bijective. Its first index is
the dual of the second index of `g`, so the inverse of a Hermitian metric `g_{IJ̄}` is `g^{J̄I}`,
the usual `g^{IJ̄}` with its indices swapped. It is `Module.Basis.coordInverse` for the bases. -/
noncomputable def inverse (g : S.V a ⊗[k] S.V b) : S.V b.dual ⊗[k] S.V a.dual :=
  (S.basis a).coordInverse (S.basis a.dual) (S.basis b) (S.basis b.dual) g

/-- The linear map of the inverse is the inverse of the linear map. -/
lemma toLin_inverse (g : S.V a ⊗[k] S.V b) (h : Function.Bijective (S.toLin g)) :
    S.toLin (S.inverse g) = (LinearEquiv.ofBijective _ h).symm.toLinearMap :=
  Module.Basis.coordTensorHomEquiv_coordInverse h

/-!

## B. The contraction identities and uniqueness

-/

/-- `g_μν g^νρ = δ_μ^ρ`, the contraction of `g` with its inverse on the adjacent indices. -/
lemma contr_mul_inverse (g : S.V a ⊗[k] S.V b) (h : Function.Bijective (S.toLin g)) :
    Tensor.contr (ColorEquiv.matMul a b a.dual)
        (S.tmulEquiv _ _ (S.twoIndexEquiv a b g ⊗ₜ S.twoIndexEquiv _ _ (S.inverse g))) =
      S.deltaTensor a.dual :=
  (Tensor.contr_matMul_eq_deltaTensor_iff g (S.inverse g)).2
    (Module.Basis.coordTensorHomEquiv_coordInverse_comp h)

/-- `g^νμ g_μρ = δ^ν_ρ`, the contraction of the inverse with `g` on the adjacent indices. -/
lemma contr_inverse_mul (g : S.V a ⊗[k] S.V b) (h : Function.Bijective (S.toLin g)) :
    Tensor.contr (ColorEquiv.matMul b.dual a.dual b)
        (S.tmulEquiv _ _ (S.twoIndexEquiv _ _ (S.inverse g) ⊗ₜ S.twoIndexEquiv a b g)) =
      S.deltaTensor b :=
  (Tensor.contr_matMul_eq_deltaTensor_iff (S.inverse g) g).2
    (Module.Basis.comp_coordTensorHomEquiv_coordInverse h)

/-- A tensor `N` with `N ∘ g = id`, as linear maps, is the inverse of `g`. -/
lemma inverse_eq_left_inv (g : S.V a ⊗[k] S.V b) (h : Function.Bijective (S.toLin g))
    {N : S.V b.dual ⊗[k] S.V a.dual} (hN : S.toLin N ∘ₗ S.toLin g = LinearMap.id) :
    S.inverse g = N :=
  Module.Basis.coordInverse_eq_of_comp_eq_id h hN

/-!

## C. The inverse commutes with the group action

-/

/-- The inverse of `Λg` is `Λ` applied to the inverse of `g`, `(Λg)⁻¹ = Λ(g⁻¹)`. -/
lemma inverse_map_rep (g : S.V a ⊗[k] S.V b) (h : Function.Bijective (S.toLin g)) (Λ : G) :
    S.inverse (TensorProduct.map (S.rep a Λ) (S.rep b Λ) g) =
      TensorProduct.map (S.rep b.dual Λ) (S.rep a.dual Λ) (S.inverse g) :=
  Module.Basis.coordInverse_map_rep (S.invariant a) (S.invariant b) h Λ

/-- The inverse of an invariant tensor is invariant, `Λg = g` implies `Λ(g⁻¹) = g⁻¹`. -/
lemma inverse_invariant (g : S.V a ⊗[k] S.V b) (h : Function.Bijective (S.toLin g)) (Λ : G)
    (hg : TensorProduct.map (S.rep a Λ) (S.rep b Λ) g = g) :
    TensorProduct.map (S.rep b.dual Λ) (S.rep a.dual Λ) (S.inverse g) = S.inverse g := by
  rw [← inverse_map_rep g h Λ, hg]

/-!

## D. The inverse of an invariant form

-/

/-- The inverse of the form at `c` is the form at `c.dual`, as `η^μν` is the inverse of
`η_μν`. -/
lemma inverse_form (c : Color K) [S.HasForm c.kind] : S.inverse (form c) = form c.dual :=
  inverse_eq_left_inv _ (toLin_form_bijective c) (form_inverse c.dual)

/-- `g^μν g_νρ = δ^μ_ρ` at an upper color `c`, the delta at `c.dual`. The second index of the form
at `c` contracted with the first index of the form at `c.dual` is the delta. -/
lemma contr_formTensor_formTensor (c : Color K) [S.HasForm c.kind] :
    Tensor.contr (ColorEquiv.matMul c c c.dual)
        (S.tmulEquiv _ _ (S.formTensor c ⊗ₜ S.formTensor c.dual)) =
      S.deltaTensor c.dual := by
  rw [formTensor, formTensor, ← inverse_form c]
  exact contr_mul_inverse _ (toLin_form_bijective c)

/-- `g^μν g_νρ = δ_ρ^μ` at an upper color `c`, with the delta read with its indices swapped. -/
lemma reindex_contr_formTensor_formTensor (c : Color K) [S.HasForm c.kind] :
    S.reindex (ColorEquiv.swapTwo c c.dual) (Tensor.contr (ColorEquiv.matMul c c c.dual)
        (S.tmulEquiv _ _ (S.formTensor c ⊗ₜ S.formTensor c.dual))) =
      S.deltaTensor c := by
  rw [contr_formTensor_formTensor, deltaTensor, reindex_twoIndexEquiv,
    show TensorProduct.comm k _ _ (S.delta c.dual) = S.delta c from
      Module.Basis.comm_coordDelta _ _]
  rfl

end Species

end Tensor
