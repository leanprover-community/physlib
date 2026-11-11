/-
Copyright (c) 2026 Andrea Pari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrea Pari
-/
module

public import Physlib.Mathematics.Tensors.Conjugation
public import Physlib.Mathematics.Tensors.Inverse
/-!

# Hermitian forms

A tensor `g_{IJ̄}` in `V a ⊗ V b` with `b = a.bar` read as a sesquilinear form, and its inverse.

## i. Overview

A tensor `g_{IJ̄}` whose second color is the conjugate of the first is a sesquilinear form on the
vectors (`sesqForm`), so that Hermiticity is Mathlib's `LinearMap.IsSymm` and
positive-definiteness is `LinearMap.IsPosDef` from `ForMathlib.SesquilinearForm`. The inverse
`g^{J̄I}` in `V b.dual ⊗ V a.dual` is again such a form, since `a.dual = b.dual.bar`
(`Color.dual_eq_bar_dual`). The inverse of an invertible Hermitian or positive-definite `g_{IJ̄}`
is again Hermitian or positive-definite, and a positive-definite `g_{IJ̄}` is invertible.

## ii. Key results

- `Species.sesqForm` reads a tensor `g_{IJ̄}` as the sesquilinear form `x, y ↦ g_{IJ̄} y^I x̄^J̄`.
- `Species.isSymm_sesqForm_inverse` and `Species.isPosDef_sesqForm_inverse` prove that the inverse
  of an invertible Hermitian or positive-definite `g_{IJ̄}` is Hermitian or positive-definite.
- `Species.toLin_injective_of_isPosDef` proves that the linear map of a positive-definite `g_{IJ̄}`
  is injective, and `Species.toLin_bijective_of_isPosDef` that it is bijective.

## iii. Table of contents

- A. Hermitian forms and their inverses
- B. Positive-definite forms are invertible

## iv. References

None.

-/

@[expose] public section

open TensorProduct
open scoped ComplexOrder

namespace Tensors

namespace Species

variable {K : Type} [InvolutiveStar K] {k : Type} [RCLike k] {G : Type} [Group G]
    {basisIdx : K → Type} [∀ κ, Fintype (basisIdx κ)] [∀ κ, DecidableEq (basisIdx κ)]
    {S : Species k G K basisIdx} [S.HasConjugation] {a b : Color K}

/-!

## A. Hermitian forms and their inverses

-/

variable (S) in
/-- A tensor `g_{IJ̄}` in `V a ⊗ V b` as the sesquilinear form `x, y ↦ g_{IJ̄} y^I x̄^J̄` on the
vectors of color `a.dual`. The color `b` is the conjugate of `a` by `hb`, which holds by `rfl` at
concrete colors. The form is conjugate-linear in its first argument, Mathlib's convention, so it is
the physicist's `g(y, x) = g_{IJ̄} y^I x̄^J̄` with the arguments swapped. -/
noncomputable def sesqForm (g : S.V a ⊗[k] S.V b) (hb : b = a.bar) :
    S.V a.dual →ₗ⋆[k] S.V a.dual →ₗ[k] k :=
  (((TensorProduct.mk k _ _).compr₂ (S.contr b.dual).toLinearMap).compl₂ (S.toLin g)).comp
    (S.conjEquiv (congrArg Color.dual hb)).toLinearMap

/-- The form on `x, y` contracts `x̄` with `g y`, where `g y` is the contraction of `g` with `y`. -/
lemma sesqForm_apply (g : S.V a ⊗[k] S.V b) (hb : b = a.bar) (x y : S.V a.dual) :
    S.sesqForm g hb x y =
      S.contr b.dual (S.conjEquiv (congrArg Color.dual hb) x ⊗ₜ S.toLin g y) :=
  rfl

/-- The form of the inverse on `g x` and `g y` is the conjugate of the form of `g` on `y` and `x`,
`g^{J̄I} (g y)_J̄ (g x)‾_I = (g_{IJ̄} x^I ȳ^J̄)*`. The inverse `g^{J̄I}` acts on barred
covectors, so its form is the conjugate of the usual `g^{IJ̄} w_I w̄'_J̄`. -/
lemma sesqForm_inverse_toLin (g : S.V a ⊗[k] S.V b) (h : Function.Bijective (S.toLin g))
    (x y : S.V a.dual) (hb : b = a.bar := by rfl)
    (ha : a.dual = b.dual.bar := Color.dual_eq_bar_dual hb) :
    S.sesqForm (S.inverse g) ha (S.toLin g x) (S.toLin g y) = star (S.sesqForm g hb y x) := by
  rw [sesqForm_apply, sesqForm_apply, toLin_inverse g h, LinearEquiv.coe_coe,
    LinearEquiv.ofBijective_symm_apply_apply, ← S.contr_tmul_symm, star_contr_conjEquiv ha,
    conjEquiv_conjEquiv]

/-- The inverse of a Hermitian `g_{IJ̄}` is Hermitian. -/
lemma isSymm_sesqForm_inverse (g : S.V a ⊗[k] S.V b) {hb : b = a.bar}
    (h : Function.Bijective (S.toLin g)) (hg : (S.sesqForm g hb).IsSymm)
    (ha : a.dual = b.dual.bar := Color.dual_eq_bar_dual hb) :
    (S.sesqForm (S.inverse g) ha).IsSymm := by
  refine ⟨fun u w => ?_⟩
  obtain ⟨x, rfl⟩ := h.2 u
  obtain ⟨y, rfl⟩ := h.2 w
  rw [sesqForm_inverse_toLin g h _ _ hb ha, sesqForm_inverse_toLin g h _ _ hb ha,
    starRingEnd_apply, star_star]
  exact (hg.eq x y).symm

/-- The linear map `y ↦ g y` of a positive-definite `g_{IJ̄}` is injective, since `g y = 0` gives
`g(y, y) = 0`. -/
lemma toLin_injective_of_isPosDef (g : S.V a ⊗[k] S.V b) {hb : b = a.bar}
    (hg : (S.sesqForm g hb).IsPosDef) : Function.Injective (S.toLin g) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro y hy
  by_contra hne
  simpa [sesqForm_apply, hy] using hg.pos y hne

/-- The inverse of a positive-definite `g_{IJ̄}` with bijective linear map is positive-definite. -/
lemma isPosDef_sesqForm_inverse_of_bijective (g : S.V a ⊗[k] S.V b) {hb : b = a.bar}
    (h : Function.Bijective (S.toLin g)) (hg : (S.sesqForm g hb).IsPosDef)
    (ha : a.dual = b.dual.bar := Color.dual_eq_bar_dual hb) :
    (S.sesqForm (S.inverse g) ha).IsPosDef := by
  refine ⟨isSymm_sesqForm_inverse g h hg.isSymm ha, fun u hu => ?_⟩
  obtain ⟨x, rfl⟩ := h.2 u
  rw [sesqForm_inverse_toLin g h _ _ hb ha, ← starRingEnd_apply, hg.isSymm.eq x x]
  exact hg.pos x fun hx => hu (by rw [hx, map_zero])

end Species

/-!

## B. Positive-definite forms are invertible

-/

namespace Species

variable {K : Type} [InvolutiveStar K] {k : Type} [RCLike k] {G : Type}
    [Group G] {basisIdx : K → Type}
    [∀ κ, Fintype (basisIdx κ)] [∀ κ, DecidableEq (basisIdx κ)]
    {S : Species k G K basisIdx} [S.HasConjugation] {a b : Color K}

/-- A positive-definite `g_{IJ̄}` is invertible. Its linear map `y ↦ g y` is bijective. -/
lemma toLin_bijective_of_isPosDef (g : S.V a ⊗[k] S.V b) {hb : b = a.bar}
    (hg : (S.sesqForm g hb).IsPosDef) : Function.Bijective (S.toLin g) := by
  -- Surjective since the dimensions agree, through the conjugation `V a.dual ≃ V b.dual`.
  have hi := toLin_injective_of_isPosDef g hg
  refine ⟨hi, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank ?_).1 hi⟩
  rw [← finrank_conj (congrArg Color.dual hb), Module.finrank_eq_card_basis (S.basis b.dual),
    Module.finrank_eq_card_basis (S.basis b)]

/-- The inverse of a positive-definite `g_{IJ̄}` is positive-definite. -/
lemma isPosDef_sesqForm_inverse (g : S.V a ⊗[k] S.V b) {hb : b = a.bar}
    (hg : (S.sesqForm g hb).IsPosDef) (ha : a.dual = b.dual.bar := Color.dual_eq_bar_dual hb) :
    (S.sesqForm (S.inverse g) ha).IsPosDef :=
  isPosDef_sesqForm_inverse_of_bijective g (toLin_bijective_of_isPosDef g hg) hg ha

end Species

end Tensors
