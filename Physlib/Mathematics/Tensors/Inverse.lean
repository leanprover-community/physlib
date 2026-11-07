/-
Copyright (c) 2026 Andrea Pari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrea Pari
-/
module

public import Physlib.Mathematics.Tensors.Metric
/-!

# The inverse of a tensor on two slots

The inverse `g^νμ` of a tensor `g_μν`, defined through the linear map that `g` defines.

## i. Overview

A tensor `g` in `V a ⊗ V b` is also a linear map `S.toLin g : V a.dual → V b`, which contracts a
vector with the first index of `g`, `v^μ ↦ v^μ g_μν` for lower colors `a` and `b`. When this map
is invertible, its inverse is again a tensor, in `V b.dual ⊗ V a.dual`. That is the inverse
`S.inverse g`, with components `g^νμ`. Its first index is the dual of the second index of `g`, so
the inverse of a Hermitian metric `g_{IJ̄}` is `g^{J̄I}`, with its barred index first.

When `S.toLin g` is not invertible, `S.inverse g` is `0`, as Mathlib's inverse of a singular matrix
is. This junk value makes `inverse` a total function and is the inverse of nothing. Every lemma
about `S.inverse g` assumes that `S.toLin g` is bijective or derives it from its hypotheses.

The inverse satisfies the contraction laws `g_μν g^νρ = δ_μ^ρ` and `g^νμ g_μρ = δ^ν_ρ`, and
it is the only tensor whose linear map inverts that of `g`, so `(g⁻¹)⁻¹ = g`.

The inverse commutes with the group action, `(Λg)⁻¹ = Λ(g⁻¹)`, so the inverse of an invariant
tensor is invariant. The inverse of the form at `c` is the form at `c.dual`, so `g^μν` is the
inverse of `g_μν`.

## ii. Key results

- `Species.inverse` is the inverse `g^νμ` of `g_μν`, and `Species.toLin_inverse` gives its
  linear map.
- `Species.contr_mul_inverse` and `Species.contr_inverse_mul` prove `g_μν g^νρ = δ_μ^ρ` and
  `g^νμ g_μρ = δ^ν_ρ`.
- `Species.inverse_eq_left_inv`, `Species.inverse_eq_right_inv` and
  `Species.inverse_eq_of_contr_eq_deltaTensor` prove that the inverse is unique, and
  `Species.inverse_inverse` that `(g⁻¹)⁻¹ = g`.
- `Species.inverse_map_rep` proves `(Λg)⁻¹ = Λ(g⁻¹)`, and `Species.inverse_invariant` that the
  inverse of an invariant tensor is invariant.
- `Species.inverse_form` proves that the inverse of the form at `c` is the form at `c.dual`, and
  `Species.contr_formTensor_formTensor` that `g^μν g_νρ = δ^μ_ρ`.

## iii. Table of contents

- A. The inverse
- B. The contraction laws and uniqueness
- C. The inverse commutes with the group action
- D. The inverse of an invariant form

## iv. References

None.

-/

@[expose] public section

open TensorProduct

namespace Tensors

namespace Species

variable {k : Type} [CommRing k] {K : Type} {G : Type} [Group G] {basisIdx : K → Type}
    [∀ κ, Fintype (basisIdx κ)] [∀ κ, DecidableEq (basisIdx κ)] {S : Species k G K basisIdx}
    {a b : Color K}

/-!

## A. The inverse

-/

variable (S) in
open scoped Classical in
/-- The inverse `g^νμ ∈ V b.dual ⊗ V a.dual` of `g_μν ∈ V a ⊗ V b`, the tensor whose linear map
inverts that of `g`. When `S.toLin g` is not bijective it is the junk value `0`. Its first index
is the dual of the second index of `g`, so the inverse of a Hermitian metric `g_{IJ̄}` is `g^{J̄I}`,
the usual `g^{IJ̄}` with its indices swapped (`TensorProduct.comm`). -/
noncomputable def inverse (g : S.V a ⊗[k] S.V b) : S.V b.dual ⊗[k] S.V a.dual :=
  if h : Function.Bijective (S.toLin g) then
    S.toLin.symm (LinearEquiv.ofBijective _ h).symm.toLinearMap
  else 0

/-- The linear map of the inverse is the inverse of the linear map. -/
lemma toLin_inverse (g : S.V a ⊗[k] S.V b) (h : Function.Bijective (S.toLin g)) :
    S.toLin (S.inverse g) = (LinearEquiv.ofBijective _ h).symm.toLinearMap := by
  simp [inverse, h]

/-- The linear map of the inverse is bijective. -/
lemma toLin_inverse_bijective (g : S.V a ⊗[k] S.V b) (h : Function.Bijective (S.toLin g)) :
    Function.Bijective (S.toLin (S.inverse g)) := by
  rw [toLin_inverse g h]
  exact (LinearEquiv.ofBijective _ h).symm.bijective

/-!

## B. The contraction laws and uniqueness

-/

/-- Inverting after `g` is the identity, as linear maps. -/
lemma toLin_inverse_comp (g : S.V a ⊗[k] S.V b) (h : Function.Bijective (S.toLin g)) :
    S.toLin (S.inverse g) ∘ₗ S.toLin g = LinearMap.id :=
  LinearMap.ext fun x => by
    rw [toLin_inverse g h]
    exact (LinearEquiv.ofBijective _ h).symm_apply_apply x

/-- `g` after inverting is the identity, as linear maps. -/
lemma comp_toLin_inverse (g : S.V a ⊗[k] S.V b) (h : Function.Bijective (S.toLin g)) :
    S.toLin g ∘ₗ S.toLin (S.inverse g) = LinearMap.id :=
  LinearMap.ext fun x => by
    rw [toLin_inverse g h]
    exact (LinearEquiv.ofBijective _ h).apply_symm_apply x

/-- `g_μν g^νρ = δ_μ^ρ`, the contraction of `g` with its inverse on the adjacent indices. -/
lemma contr_mul_inverse (g : S.V a ⊗[k] S.V b) (h : Function.Bijective (S.toLin g)) :
    Tensor.contr (ColorEquiv.matMul a b a.dual)
        (S.tmulEquiv _ _ (S.twoSlotEquiv a b g ⊗ₜ S.twoSlotEquiv _ _ (S.inverse g))) =
      S.deltaTensor a.dual :=
  (Tensor.contr_matMul_eq_deltaTensor_iff g (S.inverse g)).2 (toLin_inverse_comp g h)

/-- `g^νμ g_μρ = δ^ν_ρ`, the contraction of the inverse with `g` on the adjacent indices. -/
lemma contr_inverse_mul (g : S.V a ⊗[k] S.V b) (h : Function.Bijective (S.toLin g)) :
    Tensor.contr (ColorEquiv.matMul b.dual a.dual b)
        (S.tmulEquiv _ _ (S.twoSlotEquiv _ _ (S.inverse g) ⊗ₜ S.twoSlotEquiv a b g)) =
      S.deltaTensor b :=
  (Tensor.contr_matMul_eq_deltaTensor_iff (S.inverse g) g).2 (comp_toLin_inverse g h)

/-- A tensor `N` with `N ∘ g = id`, as linear maps, is the inverse of `g`. -/
lemma inverse_eq_left_inv (g : S.V a ⊗[k] S.V b) (h : Function.Bijective (S.toLin g))
    {N : S.V b.dual ⊗[k] S.V a.dual} (hN : S.toLin N ∘ₗ S.toLin g = LinearMap.id) :
    S.inverse g = N :=
  Eq.symm <| S.toLin.injective <| by
    rw [toLin_inverse g h, ← LinearMap.id_comp (LinearEquiv.ofBijective _ h).symm.toLinearMap]
    exact (LinearEquiv.eq_comp_toLinearMap_symm _ _).2 hN

/-- A tensor `N` with `g ∘ N = id`, as linear maps, is the inverse of `g`. -/
lemma inverse_eq_right_inv (g : S.V a ⊗[k] S.V b) (h : Function.Bijective (S.toLin g))
    {N : S.V b.dual ⊗[k] S.V a.dual} (hN : S.toLin g ∘ₗ S.toLin N = LinearMap.id) :
    S.inverse g = N :=
  Eq.symm <| S.toLin.injective <| by
    rw [toLin_inverse g h, ← LinearMap.comp_id (LinearEquiv.ofBijective _ h).symm.toLinearMap]
    exact (LinearEquiv.eq_toLinearMap_symm_comp _ _).2 hN

/-- A tensor `N` with `g_μν N^νρ = δ_μ^ρ` is the inverse of `g`. -/
lemma inverse_eq_of_contr_eq_deltaTensor (g : S.V a ⊗[k] S.V b)
    (h : Function.Bijective (S.toLin g)) {N : S.V b.dual ⊗[k] S.V a.dual}
    (hN : Tensor.contr (ColorEquiv.matMul a b a.dual)
        (S.tmulEquiv _ _ (S.twoSlotEquiv a b g ⊗ₜ S.twoSlotEquiv _ _ N)) =
      S.deltaTensor a.dual) : S.inverse g = N :=
  inverse_eq_left_inv g h ((Tensor.contr_matMul_eq_deltaTensor_iff g N).1 hN)

/-- The inverse of the inverse is the tensor itself, `(g⁻¹)⁻¹ = g`. -/
lemma inverse_inverse (g : S.V a ⊗[k] S.V b) (h : Function.Bijective (S.toLin g)) :
    S.inverse (S.inverse g) = g :=
  inverse_eq_left_inv _ (toLin_inverse_bijective g h) (comp_toLin_inverse g h)

/-!

## C. The inverse commutes with the group action

-/

/-- The inverse of `Λg` is `Λ` applied to the inverse of `g`, `(Λg)⁻¹ = Λ(g⁻¹)`. -/
lemma inverse_map_rep (g : S.V a ⊗[k] S.V b) (h : Function.Bijective (S.toLin g)) (Λ : G) :
    S.inverse (TensorProduct.map (S.rep a Λ) (S.rep b Λ) g) =
      TensorProduct.map (S.rep b.dual Λ) (S.rep a.dual Λ) (S.inverse g) := by
  refine inverse_eq_left_inv _ (S.toLin_map_rep_bijective g h Λ) (LinearMap.ext fun x => ?_)
  obtain ⟨y, rfl⟩ : ∃ y, S.rep a.dual Λ y = x := ⟨S.rep a.dual Λ⁻¹ x, by simp⟩
  rw [LinearMap.comp_apply, S.toLin_map, S.toLin_map (a := b.dual) _ _ (S.inverse g),
    ← LinearMap.comp_apply (S.toLin (S.inverse g)), toLin_inverse_comp g h, LinearMap.id_apply,
    LinearMap.id_apply]

/-- The inverse of an invariant tensor is invariant, `Λg = g` implies `Λ(g⁻¹) = g⁻¹`. -/
lemma inverse_invariant (g : S.V a ⊗[k] S.V b) (h : Function.Bijective (S.toLin g)) (Λ : G)
    (hg : TensorProduct.map (S.rep a Λ) (S.rep b Λ) g = g) :
    TensorProduct.map (S.rep b.dual Λ) (S.rep a.dual Λ) (S.inverse g) = S.inverse g := by
  rw [← inverse_map_rep g h Λ, hg]

/-!

## D. The inverse of an invariant form

-/

/-- The linear map of the form at `c` is bijective. -/
lemma toLin_form_bijective (c : Color K) [S.HasForm c.kind] :
    Function.Bijective (S.toLin (form c)) :=
  (S.toDual c.dual).bijective

/-- The inverse of the form at `c` is the form at `c.dual`, as `η^μν` is the inverse of
`η_μν`. -/
lemma inverse_form (c : Color K) [S.HasForm c.kind] : S.inverse (form c) = form c.dual :=
  inverse_eq_left_inv _ (toLin_form_bijective c) (form_inverse c.dual)

/-- `g^μν g_νρ = δ^μ_ρ` at an upper color `c`. The second slot of the form at `c` contracted
with the first slot of the form at `c.dual` is the delta. -/
lemma contr_formTensor_formTensor (c : Color K) [S.HasForm c.kind] :
    Tensor.contr (ColorEquiv.matMul c c c.dual)
        (S.tmulEquiv _ _ (S.formTensor c ⊗ₜ S.formTensor c.dual)) =
      S.deltaTensor c.dual := by
  rw [formTensor, formTensor, ← inverse_form c]
  exact contr_mul_inverse _ (toLin_form_bijective c)

end Species

end Tensors
