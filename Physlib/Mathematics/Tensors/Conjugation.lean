/-
Copyright (c) 2026 Andrea Pari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrea Pari
-/
module

public import Physlib.Mathematics.ForMathlib.SemilinearMaps
public import Physlib.Mathematics.ForMathlib.SesquilinearForm
public import Physlib.Mathematics.Tensors.Inverse
/-!

# Complex conjugation of tensors

The conjugate of a tensor conjugates its components and moves each index to the conjugate color.

## i. Overview

Conjugation conjugates the components of a tensor and moves each index to the conjugate kind,
keeping its variance. A left-handed spinor `ψ_α` becomes a right-handed spinor `ψ̄_α̇`, and a
vector index is its own conjugate, so `v̄^μ` is again a vector.

A species declares conjugation in two parts. First, its kind type has an instance of Mathlib's
`InvolutiveStar`, whose `star` says which kind is conjugate to which, with `star (star κ) = κ`.
Complex Lorentz lists its kinds and defines `star` by cases.

```lean
inductive Kind | left | right | vec

instance : InvolutiveStar Kind where
  star | left => right | right => left | vec => vec
  star_involutive κ := by cases κ <;> rfl
```

The conjugate color `c.bar = ⟨star c.kind, c.variance⟩` has the conjugate kind and the same
variance. Second, the species gives the conjugation maps as data, the class
`Species.HasConjugation`, with two laws. Conjugating twice gives back the vector, and conjugation
preserves the contraction, `(u^μ α_μ)* = ū^μ ᾱ_μ`. That it commutes with the group action,
`(Λv)‾ = Λ v̄`, is a separate property, `Species.IsEquivariantConjugation`, as symmetry is a
separate property of a form. Conjugation is structure that the species declares, not a consequence
of its bases, so the library assumes nothing about the basis labels of a kind and of its
conjugate.

The conjugate `S.conjEquiv h v` of a vector `v` of color `c` is a vector of color `c'`, and
`S.conjEquiv h` is a conjugate-linear equivalence `V c ≃ V c'`. The target color is given with
the equation `h : c' = c.bar`, which holds by `rfl` at concrete colors, as in
`S.conjEquiv rfl v`. The laws are stated in this form, so that conjugating twice gives back the
vector (`conjEquiv_conjEquiv`) with no cast along `c.bar.bar = c`.

Most species conjugate componentwise, `(v̄)^μ = (v^μ)*`. The constructor
`Species.HasConjugation.ofBasis` builds the conjugation from the bases of the species and a label
map from each kind to its conjugate kind. It commutes with the group action when the matrices of
the group at `c.bar` are the conjugates of those at `c`
(`HasConjugation.isEquivariantConjugation_ofBasis`), which is needed at the upper colors only.
The identification of the labels of a kind with those of its conjugate lives in this label map,
which the species gives, and not in the library. For complex Lorentz both kinds of spinor have the
labels `Fin 2` and the map is the identity.

The conjugate `Tensor.conj h T` of a tensor `T` applies the conjugation to every slot, with the
target colors given by `h`, slot by slot. It is conjugate-linear, an involution
(`Tensor.conj_conj`), commutes with contraction (`Tensor.conj_contr`), and for an equivariant
conjugation with the group action (`Tensor.conj_smul`). Its components are the conjugates of those
of `T` when the species conjugates componentwise (`Tensor.tensorBasis_repr_conj_of_basis`).

A tensor `g_{IJ̄}` in `V a ⊗ V b` with `b = a.bar` is read as a sesquilinear form on the vectors
(`sesqForm`), so that Hermiticity is Mathlib's `LinearMap.IsSymm` and positive-definiteness is
`LinearMap.IsPosDef` from `ForMathlib.SesquilinearForm`. The inverse `g^{J̄I}` in
`V b.dual ⊗ V a.dual` is again such a form, with `a.dual = b.dual.bar`
(`Color.dual_eq_bar_dual`). The inverse of an invertible Hermitian or positive-definite `g_{IJ̄}`
is again Hermitian or positive-definite, and over a field a positive-definite `g_{IJ̄}` is
invertible.

## ii. Key results

- `Color.bar` is the conjugate color, with `Color.bar_bar` and `Color.bar_dual`.
- `Species.HasConjugation` gives the conjugation of a species with its two laws, and
  `Species.conjEquiv` is the conjugate of a vector.
- `Species.IsEquivariantConjugation` says that the conjugation commutes with the group action, and
  `Species.rep_dual_of_star_contr` that equivariance at a color gives it at the dual color.
- `Species.conjEquiv_conjEquiv` proves that conjugating twice gives back the vector,
  `Species.star_contr` that conjugation preserves the contraction, and `Species.conjEquiv_rep`
  that an equivariant conjugation commutes with the group action.
- `Species.HasConjugation.ofBasis` builds a componentwise conjugation from a label map,
  `Species.HasConjugation.isEquivariantConjugation_ofBasis` gives its equivariance from the
  matrices of the group, and `Species.basis_repr_conjEquiv_of_basis` gives the components of the
  conjugate.
- `Species.Tensor.conj` is the conjugate of a tensor, with `Species.Tensor.conj_conj`,
  `Species.Tensor.conj_pure`, `Species.Tensor.conj_smul` and `Species.Tensor.conj_contr`.
- `Species.Tensor.tensorBasis_repr_conj_of_basis` proves that the components of the conjugate are
  the conjugates of the components.
- `Species.sesqForm` reads a tensor `g_{IJ̄}` as the sesquilinear form `x, y ↦ g_{IJ̄} y^I x̄^J̄`.
- `Species.isSymm_sesqForm_inverse` and `Species.isPosDef_sesqForm_inverse` prove that the inverse
  of an invertible Hermitian or positive-definite `g_{IJ̄}` is Hermitian or positive-definite.
- `Species.toLin_injective_of_isPosDef` proves that the linear map of a positive-definite `g_{IJ̄}`
  is injective, and `Species.toLin_bijective_of_isPosDef` that over a field it is bijective.

## iii. Table of contents

- A. Conjugate colors
- B. Species with a conjugation
- C. Componentwise conjugation
- D. Conjugation of tensors
  - D.1. The group action and contraction
  - D.2. Components
- E. Hermitian forms and their inverses
  - E.1. Positive-definite forms over a field

## iv. References

None.

-/

@[expose] public section

open TensorProduct PiTensorProduct

namespace Tensors

/-!

## A. Conjugate colors

-/

variable {K : Type} [InvolutiveStar K]

/-- The conjugate color, with the conjugate kind `star κ` and the same variance, as in
`ψ_α ↦ ψ̄_α̇`. -/
abbrev Color.bar (c : Color K) : Color K := ⟨star c.kind, c.variance⟩

/-- Conjugating twice gives back the color. -/
lemma Color.bar_bar (c : Color K) : c.bar.bar = c := by
  simp [Color.bar]

/-- Conjugation commutes with duality, by `rfl`. -/
lemma Color.bar_dual (c : Color K) : c.dual.bar = c.bar.dual := rfl

/-- If `b` is the conjugate of `a`, then `a.dual` is the conjugate of `b.dual`. This is the color
equation of the inverse of a form in `V a ⊗ V b`. -/
lemma Color.dual_eq_bar_dual {a b : Color K} (hb : b = a.bar) : a.dual = b.dual.bar := by
  subst hb
  simp [Color.bar]

/-!

## B. Species with a conjugation

-/

namespace Species

variable {k : Type} [CommRing k] [StarRing k] {G : Type} [Group G] {basisIdx : K → Type}
    [∀ κ, Fintype (basisIdx κ)] [∀ κ, DecidableEq (basisIdx κ)]
    {S : Species k G K basisIdx} {c c' : Color K}

variable (S) in
/-- A conjugation of the species, a conjugate-linear equivalence `v ↦ v̄` from each color `c` to
its conjugate `c'`. Conjugating twice gives back the vector, and conjugation preserves the
contraction. The conjugate color is given with an equation `h : c' = c.bar`, so that no law moves
a vector along `c.bar.bar = c`. Commuting with the group action is the separate property
`IsEquivariantConjugation`. -/
class HasConjugation where
  /-- The conjugate of a vector of color `c`, a vector of the conjugate color `c'`. -/
  conj {c c' : Color K} (h : c' = c.bar) : S.V c ≃ₗ⋆[k] S.V c'
  /-- Conjugating twice gives back the vector, `v̄̄ = v`. -/
  conj_conj {c c' : Color K} (h : c' = c.bar) (h' : c = c'.bar) (v : S.V c) :
    conj h' (conj h v) = v
  /-- Conjugation preserves the contraction, `(u^μ α_μ)* = ū^μ ᾱ_μ`. -/
  star_contr_conj {c c' : Color K} (h : c' = c.bar) (u : S.V c) (α : S.V c.dual) :
    star (S.contr c (u ⊗ₜ[k] α)) = S.contr c' (conj h u ⊗ₜ[k] conj (congrArg Color.dual h) α)

variable (S) in
/-- The conjugation commutes with the group action, `(Λv)‾ = Λ v̄`, so the representation at
`c.bar` is the conjugate of the one at `c`. -/
class IsEquivariantConjugation [S.HasConjugation] : Prop where
  /-- Conjugation commutes with the group action, `(Λv)‾ = Λ v̄`. -/
  conj_rep {c c' : Color K} (h : c' = c.bar) (g : G) (v : S.V c) :
    HasConjugation.conj h (S.rep c g v) = S.rep c' g (HasConjugation.conj h v)

section

variable [S.HasConjugation]

variable (S) in
/-- The conjugate `v̄` of a vector `v` of color `c`, a vector of color `c'`, the conjugate of `c`
by `h`, which holds by `rfl` at concrete colors. It is conjugate-linear. -/
def conjEquiv (h : c' = c.bar) : S.V c ≃ₗ⋆[k] S.V c' :=
  HasConjugation.conj h

/-- Conjugating twice gives back the vector, `v̄̄ = v`. -/
@[simp]
lemma conjEquiv_conjEquiv (h : c' = c.bar) (h' : c = c'.bar) (v : S.V c) :
    S.conjEquiv h' (S.conjEquiv h v) = v :=
  HasConjugation.conj_conj h h' v

/-- Conjugation preserves the contraction, `(u^μ α_μ)* = ū^μ ᾱ_μ`, for `u` of color `c` and `α` of
color `c.dual`. -/
lemma star_contr (h : c' = c.bar) (u : S.V c) (α : S.V c.dual) :
    star (S.contr c (u ⊗ₜ[k] α)) =
      S.contr c' (S.conjEquiv h u ⊗ₜ[k] S.conjEquiv (congrArg Color.dual h) α) :=
  HasConjugation.star_contr_conj h u α

/-- Conjugation commutes with the group action, `(Λv)‾ = Λ v̄`. -/
lemma conjEquiv_rep [S.IsEquivariantConjugation] (h : c' = c.bar) (g : G) (v : S.V c) :
    S.conjEquiv h (S.rep c g v) = S.rep c' g (S.conjEquiv h v) :=
  IsEquivariantConjugation.conj_rep h g v

/-- Moving the conjugate along an equality of colors conjugates to the new color. -/
lemma cast_conjEquiv {c'' : Color K} (q : c' = c'') (h : c' = c.bar) (x : S.V c) :
    S.cast q (S.conjEquiv h x) = S.conjEquiv (q.symm.trans h) x := by
  subst q
  rfl

/-- Conjugating a vector moved along an equality of colors conjugates the vector. -/
lemma conjEquiv_cast {b b' : Color K} (p : b = b') (h : c' = b'.bar) (x : S.V b) :
    S.conjEquiv h (S.cast p x) = S.conjEquiv (h.trans (congrArg Color.bar p.symm)) x := by
  subst p
  rfl

end

omit [InvolutiveStar K] in
/-- If conjugate-linear maps `f` at `c` and `f'` at `c.dual` preserve the contraction and `f`
commutes with the group action, then so does `f'`. Equivariance at a dual color follows from
equivariance at the color. -/
lemma rep_dual_of_star_contr (f : S.V c ≃ₗ⋆[k] S.V c') (f' : S.V c.dual ≃ₗ⋆[k] S.V c'.dual)
    (hf' : ∀ u α, star (S.contr c (u ⊗ₜ α)) = S.contr c' (f u ⊗ₜ f' α))
    (hf : ∀ g v, f (S.rep c g v) = S.rep c' g (f v)) (g : G) (α : S.V c.dual) :
    f' (S.rep c.dual g α) = S.rep c'.dual g (f' α) :=
  ext_contr fun u' => by
    obtain ⟨u, rfl⟩ := f.surjective u'
    rw [← hf', contr_tmul_rep, contr_tmul_rep, ← hf, hf']

/-!

## C. Componentwise conjugation

-/

variable (S) in
/-- The componentwise conjugation, `(v̄)^{e μ} = (v^μ)*`, which sends the basis vector `e_μ` of
`c` to the basis vector `e_{e μ}` of the conjugate color. The label map `e h` reads a label of a
kind `κ` as a label of its conjugate `κ'`, given with an equation `h : κ' = star κ`, and reading
it back gives the label (`e_e`). -/
@[instance_reducible]
noncomputable def HasConjugation.ofBasis
    (e : ∀ {κ κ' : K}, κ' = star κ → basisIdx κ ≃ basisIdx κ')
    (e_e : ∀ {κ κ' : K} (h : κ' = star κ) (h' : κ = star κ') (μ : basisIdx κ), e h' (e h μ) = μ) :
    S.HasConjugation where
  conj h := (S.basis _).starEquiv (S.basis _) (e (congrArg Color.kind h))
  conj_conj _ _ v := Module.Basis.starEquiv_starEquiv _ _ _ _ (e_e _ _) v
  star_contr_conj _ u α := Module.Basis.star_coordPairing_starEquiv _ _ _ _ _ u α

/-- The componentwise conjugation commutes with the group action when the matrix of each `g : G`
at `c.bar` is the conjugate of its matrix at `c`, `(Λ̄)^μ_ν = (Λ^μ_ν)*`. The law is needed at the
upper colors only, since it follows at the lower ones (`rep_dual_of_star_contr`). -/
lemma HasConjugation.isEquivariantConjugation_ofBasis
    (e : ∀ {κ κ' : K}, κ' = star κ → basisIdx κ ≃ basisIdx κ')
    (e_e : ∀ {κ κ' : K} (h : κ' = star κ) (h' : κ = star κ') (μ : basisIdx κ), e h' (e h μ) = μ)
    (rep_basis : ∀ (κ : K) (g : G) (μ ν : basisIdx κ),
      (S.basis ⟨star κ, .up⟩).repr (S.rep ⟨star κ, .up⟩ g (S.basis ⟨star κ, .up⟩ (e rfl μ)))
        (e rfl ν) = star ((S.basis ⟨κ, .up⟩).repr (S.rep ⟨κ, .up⟩ g (S.basis ⟨κ, .up⟩ μ)) ν)) :
    letI := ofBasis S e e_e
    S.IsEquivariantConjugation := by
  let := ofBasis S e e_e
  refine ⟨fun {c _} h g v => ?_⟩
  subst h
  obtain ⟨κ, ⟨_ | _, _ | _, hv⟩⟩ := c
  · exact absurd rfl hv
  · -- A lower color is the dual of `⟨κ, up⟩`, where the law holds.
    exact rep_dual_of_star_contr (c := ⟨κ, .up⟩) (c' := ⟨star κ, .up⟩) _ _
      (fun u α => Module.Basis.star_coordPairing_starEquiv _ _ _ _ _ u α)
      (fun g => Module.Basis.starEquiv_map_of_repr _ _ _ _ _ (rep_basis κ g)) g v
  · exact Module.Basis.starEquiv_map_of_repr _ _ _ _ _ (rep_basis κ g) v
  · exact absurd rfl hv

/-- The componentwise conjugate of the basis vector `e_μ` is the basis vector `e_{e μ}`. -/
lemma HasConjugation.ofBasis_conjEquiv_basis
    (e : ∀ {κ κ' : K}, κ' = star κ → basisIdx κ ≃ basisIdx κ')
    (e_e : ∀ {κ κ' : K} (h : κ' = star κ) (h' : κ = star κ') (μ : basisIdx κ), e h' (e h μ) = μ)
    (h : c' = c.bar) (μ : basisIdx c.kind) :
    letI := ofBasis S e e_e
    S.conjEquiv h (S.basis c μ) = S.basis c' (e (congrArg Color.kind h) μ) :=
  Module.Basis.starEquiv_apply_self _ _ _ μ

/-- The components of the conjugate are the conjugates of the components,
`(v̄)^μ = (v^{e⁻¹ μ})*`, when conjugation sends each basis vector `e_μ` of `c` to the basis vector
`e_{e μ}` of `c'`. -/
lemma basis_repr_conjEquiv_of_basis [S.HasConjugation] (h : c' = c.bar)
    (e : basisIdx c.kind ≃ basisIdx c'.kind)
    (he : ∀ μ, S.conjEquiv h (S.basis c μ) = S.basis c' (e μ)) (v : S.V c)
    (μ : basisIdx c'.kind) :
    (S.basis c').repr (S.conjEquiv h v) μ = star ((S.basis c).repr v (e.symm μ)) := by
  rw [Module.Basis.eq_starEquiv _ _ e (S.conjEquiv h) he v, Module.Basis.repr_starEquiv]

/-!

## D. Conjugation of tensors

-/

namespace Tensor

variable [S.HasConjugation] {ι : Type} {c c' : ι → Color K}

/-- The conjugate `T̄` of a tensor `T`, with every slot conjugated and moved to the conjugate color.
The colors `c'` of the result are the conjugates of `c` by `h`. For concrete colors `h` holds by
`rfl` slot by slot, `fun i => by fin_cases i <;> rfl`. It is conjugate-linear. -/
noncomputable def conj (h : ∀ i, c' i = (c i).bar) : S.Tensor c ≃ₗ⋆[k] S.Tensor c' :=
  (S.toPiTensor c).trans <| (PiTensorProduct.congrₛₗ fun i => S.conjEquiv (h i)).trans
    (S.toPiTensor c').symm

/-- The conjugate of a pure tensor conjugates each factor, `(u ⊗ α)‾ = ū ⊗ ᾱ`. -/
@[simp]
lemma conj_pure (h : ∀ i, c' i = (c i).bar) (f : Π i, S.V (c i)) :
    conj h (S.pure f) = S.pure fun i => S.conjEquiv (h i) (f i) :=
  congrₛₗ_tprod _ f

/-- Conjugating twice gives back the tensor. -/
lemma conj_conj (h : ∀ i, c' i = (c i).bar) (h' : ∀ i, c i = (c' i).bar) (t : S.Tensor c) :
    conj h' (conj h t) = t := by
  induction t using inductionOn_pure with
  | h f => simp
  | hsmul r t ht => rw [LinearEquiv.map_smulₛₗ, LinearEquiv.map_smulₛₗ, ht, starRingEnd_self_apply]
  | hadd x y hx hy => rw [map_add, map_add, hx, hy]

/-!

### D.1. The group action and contraction

-/

/-- Conjugation commutes with the action `Λ` of `g : G`, `(ΛT)‾ = Λ T̄`. -/
lemma conj_smul [S.IsEquivariantConjugation] (h : ∀ i, c' i = (c i).bar) (g : G)
    (t : S.Tensor c) :
    conj h (g • t) = g • conj h t :=
  map_smul_of_pure (conj h) g (fun f => by simp [conjEquiv_rep]) t

variable {κ J : Type} [Fintype J] {b b' : κ → Color K} {a a' : J → Color K}

/-- Conjugating a contraction is contracting the conjugate along the same pairs of slots,
`(T^ρμ_μ)‾ = T̄^ρμ_μ`. The relabeling `τ` of `T̄` moves the slots as `σ` does (`hτ`). -/
lemma conj_contr (h : ∀ i, c' i = (c i).bar) (hb : ∀ x, b' x = (b x).bar)
    (ha : ∀ j, a' j = (a j).bar) (σ : ColorEquiv c (contrColors b a))
    (τ : ColorEquiv c' (contrColors b' a')) (hτ : τ.toEquiv = σ.toEquiv) (t : S.Tensor c) :
    conj hb (contr σ t) = contr τ (conj h t) := by
  obtain rfl : c' = fun i => (c i).bar := funext h
  obtain rfl : b' = fun x => (b x).bar := funext hb
  obtain rfl : a' = fun j => (a j).bar := funext ha
  obtain ⟨τ, hτ'⟩ := τ
  subst hτ
  induction t using inductionOn_pure with
  | hsmul r t ht => rw [map_smul, LinearEquiv.map_smulₛₗ, ht, LinearEquiv.map_smulₛₗ, map_smul]
  | hadd x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]
  | h f =>
    simp only [contr_pure, conj_pure, LinearEquiv.map_smulₛₗ, starRingEnd_apply, star_prod,
      star_contr rfl, conjEquiv_cast, cast_conjEquiv]

/-!

### D.2. Components

-/

/-- The components of the conjugate are the conjugates of the components,
`(T̄)^μν = (T^{e⁻¹ μ, e⁻¹ ν})*`, when conjugation sends each basis vector `e_μ` at the slot `i` to
the basis vector `e_{e i μ}`. -/
lemma tensorBasis_repr_conj_of_basis [Fintype ι] (h : ∀ i, c' i = (c i).bar)
    (e : ∀ i, basisIdx (c i).kind ≃ basisIdx (c' i).kind)
    (he : ∀ i μ, S.conjEquiv (h i) (S.basis (c i) μ) = S.basis (c' i) (e i μ)) (t : S.Tensor c)
    (μ : Π i, basisIdx (c' i).kind) :
    (S.tensorBasis c').repr (conj h t) μ =
      star ((S.tensorBasis c).repr t fun i => (e i).symm (μ i)) := by
  rw [Module.Basis.eq_starEquiv (S.tensorBasis c) (S.tensorBasis c') (Equiv.piCongrRight e)
    (conj h) (fun ν => by simp [tensorBasis_apply, he]) t, Module.Basis.repr_starEquiv]
  rfl

end Tensor

/-!

## E. Hermitian forms and their inverses

-/

variable [S.HasConjugation] {a b : Color K}

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
    LinearEquiv.ofBijective_symm_apply_apply, ← S.contr_tmul_symm, star_contr ha,
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
lemma toLin_injective_of_isPosDef [Preorder k] (g : S.V a ⊗[k] S.V b) {hb : b = a.bar}
    (hg : (S.sesqForm g hb).IsPosDef) : Function.Injective (S.toLin g) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro y hy
  by_contra hne
  simpa [sesqForm_apply, hy] using hg.pos y hne

/-- The inverse of a positive-definite `g_{IJ̄}` with bijective linear map is positive-definite. -/
lemma isPosDef_sesqForm_inverse_of_bijective [LT k] (g : S.V a ⊗[k] S.V b) {hb : b = a.bar}
    (h : Function.Bijective (S.toLin g)) (hg : (S.sesqForm g hb).IsPosDef)
    (ha : a.dual = b.dual.bar := Color.dual_eq_bar_dual hb) :
    (S.sesqForm (S.inverse g) ha).IsPosDef := by
  refine ⟨isSymm_sesqForm_inverse g h hg.isSymm ha, fun u hu => ?_⟩
  obtain ⟨x, rfl⟩ := h.2 u
  rw [sesqForm_inverse_toLin g h _ _ hb ha, ← starRingEnd_apply, hg.isSymm.eq x x]
  exact hg.pos x fun hx => hu (by rw [hx, map_zero])

end Species

/-!

### E.1. Positive-definite forms over a field

-/

namespace Species

variable {k : Type} [Field k] [StarRing k] [Preorder k] {G : Type} [Group G] {basisIdx : K → Type}
    [∀ κ, Fintype (basisIdx κ)] [∀ κ, DecidableEq (basisIdx κ)]
    {S : Species k G K basisIdx} [S.HasConjugation] {a b : Color K}

/-- A positive-definite `g_{IJ̄}` is invertible. Its linear map `y ↦ g y` is bijective. -/
lemma toLin_bijective_of_isPosDef (g : S.V a ⊗[k] S.V b) {hb : b = a.bar}
    (hg : (S.sesqForm g hb).IsPosDef) : Function.Bijective (S.toLin g) := by
  -- Surjective since the dimensions agree, through the conjugation `V a.dual ≃ V b.dual`.
  have hi := toLin_injective_of_isPosDef g hg
  refine ⟨hi, ?_⟩
  have : ∀ c, Module.Finite k (S.V c) := fun c => Module.Finite.of_basis (S.basis c)
  refine (LinearMap.injective_iff_surjective_of_finrank_eq_finrank ?_).1 hi
  let f : S.V a.dual ≃ₗ⋆[k] S.V b.dual := S.conjEquiv (congrArg Color.dual hb)
  rw [Module.finrank, rank_eq_of_equiv_equiv (starRingEnd k) f.toAddEquiv
    (Function.Involutive.bijective fun r => by simp) (fun r m => map_smulₛₗ f r m),
    ← Module.finrank, Module.finrank_eq_card_basis (S.basis b.dual),
    Module.finrank_eq_card_basis (S.basis b)]

/-- The inverse of a positive-definite `g_{IJ̄}` is positive-definite. -/
lemma isPosDef_sesqForm_inverse (g : S.V a ⊗[k] S.V b) {hb : b = a.bar}
    (hg : (S.sesqForm g hb).IsPosDef) (ha : a.dual = b.dual.bar := Color.dual_eq_bar_dual hb) :
    (S.sesqForm (S.inverse g) ha).IsPosDef :=
  isPosDef_sesqForm_inverse_of_bijective g (toLin_bijective_of_isPosDef g hg) hg ha

end Species

end Tensors
