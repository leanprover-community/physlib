/-
Copyright (c) 2026 Andrea Pari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrea Pari
-/
module

public import Physlib.Mathematics.Tensors.Species
public import Mathlib.LinearAlgebra.PiTensorProduct.Basis
public import Physlib.Mathematics.ForMathlib.Representation
/-!

# Tensors of a species

The tensors of a species with colors `c : ι → Color K` form Mathlib's `⨂[k] i, V (c i)`, for any
index type `ι`, and the group acts on them index by index.

## i. Overview

A tensor of a species `S` has one index `i` for each `i : ι`, and the index `i` has the color `c i`.
The tensors with colors `c : ι → Color K` form the space `Tensor S c`, which is Mathlib's
`⨂[k] i, V (c i)`. The index type `ι` can be any type, such as `Fin n` or a sum `ι₁ ⊕ ι₂`.

A pure tensor takes one vector at each index, such as `u ⊗ α ⊗ β` with `u` in `V (c 0)`, `α` in
`V (c 1)` and `β` in `V (c 2)`. Its components are products, `(u ⊗ α ⊗ β)^μ_νρ = u^μ α_ν β_ρ`.
Most tensors are not pure. The metric `η = ∑ μ, η_μμ e^μ ⊗ e^μ` is a sum of pure tensors but not
a pure tensor itself. Every tensor is such a sum, so a linear map of tensors is fixed by its
values on pure tensors (`ext_pure`), and a property of all tensors follows from the pure case
(`inductionOn_pure`). Maps of tensors, starting with the group action, are given by their value on
pure tensors, and their properties are proved there first. `S.pure f` is Mathlib's
`⨂ₜ[k] i, f i` as an element of `Tensor S c`.

A group element `Λ` acts on every index by the representation of its color,
`Λ (u ⊗ α ⊗ β) = Λu ⊗ Λα ⊗ Λβ` (`smul_pure`). This is the representation
`Representation.piTprod` on `⨂[k] i, V (c i)`. A map that commutes with `Λ` on pure tensors
commutes with it on all tensors (`map_smul_of_pure`).

The components `T^μ_νρ` of a tensor `T` are its coordinates in the basis `e_μ ⊗ e^ν ⊗ e^ρ`
(`tensorBasis`), which is Mathlib's `Basis.piTensorProduct`. Each basis tensor is a pure tensor of
basis vectors.

For example, the Lorentz colors `![⟨vec, up⟩, ⟨vec, down⟩, ⟨vec, down⟩]` give the space
`ℝ⁴ ⊗ (ℝ⁴)* ⊗ (ℝ⁴)*` of tensors `T = T^μ_νρ e_μ ⊗ e^ν ⊗ e^ρ`. A Lorentz transformation `Λ` acts
as `(ΛT)^μ_νρ = Λ^μ_σ (Λ⁻¹)^τ_ν (Λ⁻¹)^λ_ρ T^σ_τλ` (`tensorBasis_repr_smul`). Lower indices
transform with `Λ⁻¹`, which keeps `u^μ α_μ` invariant.

A linear equivalence `f` from the space of one color to that of another acts on tensors through a
single index. `S.congrAt i f` applies `f` at the index `i` and the identity at the other indices,
`u ⊗ v ⊗ w ↦ u ⊗ f v ⊗ w`.

## ii. Key results

- `Tensor` and `Species.pure` are the tensors and the pure tensors, and
  `Species.inductionOn_pure` is induction through pure tensors.
- `Species.ext_pure` proves that linear maps of tensors that agree on pure tensors are equal. It is
  an `ext` lemma, so `ext p q` also reduces maps out of products `Tensor S c ⊗ Tensor S c₂`, and
  intertwining maps, to pure tensors. `Species.equiv_ext_pure` does the same for equivalences of
  representations.
- `Species.smul_pure` proves that the group acts on a pure tensor index by index.
- `Species.map_smul_of_pure` proves that a map of tensors that commutes with the group on pure
  tensors commutes with it on all tensors.
- `Species.tensorRep` is the action on tensors as a Mathlib representation. Maps of tensors that
  commute with the group are Mathlib's `Representation.Equiv` and `Representation.IntertwiningMap`
  of it, built by `Species.equivOfPure` and `Species.intertwiningMapOfPure` from a check on pure
  tensors, and `Species.equiv_smul` and `Species.intertwiningMap_smul` give `φ (g • t) = g • φ t`.
- `Species.smul_eq_self_of_isEmpty` proves that a tensor with no indices is invariant.
- `Species.tensorBasis` is the basis of tensors, and `Species.tensorBasis_repr_pure` gives the
  components of a pure tensor. `Species.finrank_tensor` gives the dimension of tensors.
- `Species.tensorBasis_repr_smul` gives the components of `g • t`.
- `Species.mapIndices` applies a linear map at every index, with `Species.mapIndices_comp` and
  `Species.mapIndices_id`, and `Species.mapIndices_smul` proves that it commutes with the group when
  every index map does.
- `Species.congrIndices` applies an equivalence of representations at every index. It is
  `Representation.Equiv.piTensorCongr`.
- `Species.indexMapsAt` is the family of a linear map at one index and the identity at the others,
  and `Species.mapAt` applies it, with `Species.mapAt_pure`, `Species.mapAt_comp` and
  `Species.mapAt_id`.
- `Species.congrAt` is `mapAt` of an equivalence of representations, as an equivalence of
  representations, with `Species.congrAt_symm`.

## iii. Table of contents

- A. Tensors
- B. The group action
- C. The basis of tensors
- D. Linear maps at the indices

## iv. References

There are no known references for the material in this module.

-/

@[expose] public section

open TensorProduct PiTensorProduct

namespace Tensor

namespace Species

variable {k : Type} [RCLike k] {K : Type} {G : Type} [Group G] {basisIdx : K → Type}
    [∀ κ, Fintype (basisIdx κ)] [∀ κ, DecidableEq (basisIdx κ)]

/-!

## A. Tensors

-/

/-- The space `⨂[k] i, S.V (c i)` of tensors with colors `c` on the indices `ι`. It is a `def`, not
an `abbrev`, so that the type `Tensor S c` keeps the species and the colors instead of unfolding to
`⨂[k] i, S.V (c i)`. -/
def _root_.Tensor (S : Species k G K basisIdx) {ι : Type} (c : ι → Color K) : Type :=
  ⨂[k] i, S.V (c i)

noncomputable instance {S : Species k G K basisIdx} {ι : Type} {c : ι → Color K} :
    AddCommGroup (Tensor S c) :=
  inferInstanceAs (AddCommGroup (⨂[k] i, S.V (c i)))

noncomputable instance {S : Species k G K basisIdx} {ι : Type} {c : ι → Color K} :
    Module k (Tensor S c) :=
  inferInstanceAs (Module k (⨂[k] i, S.V (c i)))

variable {ι : Type} {c : ι → Color K}

/-- The identity from `Tensor S c` to Mathlib's `⨂[k] i, S.V (c i)`, as a linear equivalence.
Mathlib's constructions on `⨂` are composed with it. -/
noncomputable def toPiTensor (S : Species k G K basisIdx) (c : ι → Color K) :
    Tensor S c ≃ₗ[k] ⨂[k] i, S.V (c i) :=
  LinearEquiv.refl k _

/-- The pure tensor of a family of vectors, one per index, such as `u ⊗ α ⊗ β` with components
`u^μ α_ν β_ρ`. It is Mathlib's `⨂ₜ[k] i, f i`. -/
noncomputable def pure (S : Species k G K basisIdx) (f : Π i, S.V (c i)) : Tensor S c :=
  (S.toPiTensor c).symm (⨂ₜ[k] i, f i)

variable {S : Species k G K basisIdx}

@[simp]
lemma toPiTensor_pure (f : Π i, S.V (c i)) : S.toPiTensor c (S.pure f) = ⨂ₜ[k] i, f i := rfl

@[simp]
lemma toPiTensor_symm_tprod (f : Π i, S.V (c i)) :
    (S.toPiTensor c).symm (⨂ₜ[k] i, f i) = S.pure f := rfl

/-- Induction on tensors through pure tensors: every tensor is a sum of pure tensors. -/
lemma inductionOn_pure {P : Tensor S c → Prop}
    (h : ∀ f : Π i, S.V (c i), P (S.pure f)) (hsmul : ∀ (r : k) t, P t → P (r • t))
    (hadd : ∀ t₁ t₂, P t₁ → P t₂ → P (t₁ + t₂)) (t : Tensor S c) : P t :=
  PiTensorProduct.induction_on (motive := P) t (fun r f => hsmul r _ (h f)) hadd

/-- Two linear maps out of tensors are equal when they agree on pure tensors. -/
@[ext]
lemma ext_pure {E : Type} [AddCommGroup E] [Module k E] {f g : Tensor S c →ₗ[k] E}
    (h : ∀ p : Π i, S.V (c i), f (S.pure p) = g (S.pure p)) : f = g :=
  PiTensorProduct.ext (MultilinearMap.ext h)

/-!

## B. The group action

-/

/-- The group acts on every index by the representation of its color,
`Λ (u ⊗ α ⊗ …) = Λu ⊗ Λα ⊗ …`. It is `Representation.piTprod` of the representations of the
colors. -/
noncomputable instance : DistribMulAction G (Tensor S c) :=
  DistribMulAction.compHom (M := Module.End k (Tensor S c)) _
    (Representation.piTprod fun i => S.rep (c i))

@[simp]
lemma smul_pure (g : G) (f : Π i, S.V (c i)) :
    g • S.pure f = S.pure fun i => S.rep (c i) g (f i) :=
  Representation.piTprod_tprod _ _ _

noncomputable instance : SMulCommClass G k (Tensor S c) where
  smul_comm g r t := map_smul (Representation.piTprod (fun i => S.rep (c i)) g) r t

noncomputable instance : SMulCommClass k G (Tensor S c) := .symm _ _ _

variable (S) in
/-- The action of the group on tensors as Mathlib's representation, `Λ ↦ (T ↦ Λ • T)`. Maps of
tensors that commute with the action are Mathlib's `Representation.Equiv` and
`Representation.IntertwiningMap` for it. -/
noncomputable abbrev tensorRep (c : ι → Color K) : Representation k G (Tensor S c) :=
  Representation.ofDistribMulAction k G (Tensor S c)

/-- An intertwining map from or to tensors commutes with the actions, `φ (Λ v) = Λ φ v`. -/
lemma intertwiningMap_smul {ι' : Type} {c' : ι' → Color K}
    (φ : (S.tensorRep c).IntertwiningMap (S.tensorRep c')) (g : G) (t : Tensor S c) :
    φ (g • t) = g • φ t :=
  Representation.IntertwiningMap.isIntertwining _ _ φ g t

/-- An equivalence of representations of tensors commutes with the actions, `φ (Λ T) = Λ φ T`. -/
lemma equiv_smul {ι' : Type} {c' : ι' → Color K}
    (φ : (S.tensorRep c).Equiv (S.tensorRep c')) (g : G) (t : Tensor S c) :
    φ (g • t) = g • φ t :=
  intertwiningMap_smul φ.toIntertwiningMap g t

/-- A linear or conjugate-linear map of tensors that commutes with `Λ` on pure tensors commutes
with `Λ` on all tensors. -/
lemma map_smul_of_pure {ι' : Type} {c' : ι' → Color K} {σ : k →+* k} {F : Type}
    [FunLike F (Tensor S c) (Tensor S c')] [SemilinearMapClass F σ (Tensor S c) (Tensor S c')]
    (f : F) (g : G) (h : ∀ p : Π i, S.V (c i), f (g • S.pure p) = g • f (S.pure p))
    (t : Tensor S c) : f (g • t) = g • f t := by
  induction t using inductionOn_pure with
  | h p => exact h p
  | hsmul r t ht => rw [smul_comm, map_smulₛₗ, ht, map_smulₛₗ, smul_comm]
  | hadd x y hx hy => rw [smul_add, map_add, hx, hy, map_add, smul_add]

variable {ι' : Type} {c' : ι' → Color K} in
/-- A linear equivalence of tensors that commutes with `Λ` on pure tensors, as an equivalence of
representations. -/
noncomputable def equivOfPure (e : Tensor S c ≃ₗ[k] Tensor S c')
    (h : ∀ (g : G) (p : Π i, S.V (c i)), e (g • S.pure p) = g • e (S.pure p)) :
    (S.tensorRep c).Equiv (S.tensorRep c') :=
  .mk e fun g => LinearMap.ext fun t => map_smul_of_pure e g (h g) t

variable {ι' : Type} {c' : ι' → Color K} in
@[simp]
lemma equivOfPure_apply (e : Tensor S c ≃ₗ[k] Tensor S c')
    (h : ∀ (g : G) (p : Π i, S.V (c i)), e (g • S.pure p) = g • e (S.pure p)) (t : Tensor S c) :
    equivOfPure e h t = e t := rfl

variable {ι' : Type} {c' : ι' → Color K} in
/-- A linear map of tensors that commutes with `Λ` on pure tensors, as an intertwining map. -/
noncomputable def intertwiningMapOfPure (f : Tensor S c →ₗ[k] Tensor S c')
    (h : ∀ (g : G) (p : Π i, S.V (c i)), f (g • S.pure p) = g • f (S.pure p)) :
    (S.tensorRep c).IntertwiningMap (S.tensorRep c') :=
  ⟨f, fun g => LinearMap.ext fun t => map_smul_of_pure f g (h g) t⟩

variable {ι' : Type} {c' : ι' → Color K} in
@[simp]
lemma intertwiningMapOfPure_apply (f : Tensor S c →ₗ[k] Tensor S c')
    (h : ∀ (g : G) (p : Π i, S.V (c i)), f (g • S.pure p) = g • f (S.pure p)) (t : Tensor S c) :
    intertwiningMapOfPure f h t = f t := rfl

/-- Two equivalences of representations out of tensors are equal when they agree on pure
tensors. -/
lemma equiv_ext_pure {W : Type} [AddCommGroup W] [Module k W] {ρ : Representation k G W}
    {φ ψ : (S.tensorRep c).Equiv ρ} (h : ∀ p : Π i, S.V (c i), φ (S.pure p) = ψ (S.pure p)) :
    φ = ψ :=
  Representation.Equiv.ext <|
    funext <| LinearMap.congr_fun (ext_pure (f := φ.toLinearMap) (g := ψ.toLinearMap) h)

/-- A tensor with no indices is invariant, `Λ s = s`. -/
lemma smul_eq_self_of_isEmpty [IsEmpty ι] (g : G) (t : Tensor S c) : g • t = t := by
  induction t using inductionOn_pure with
  | h f => rw [smul_pure]; exact congrArg _ (funext isEmptyElim)
  | hsmul r t ht => rw [smul_comm, ht]
  | hadd t t' ht ht' => rw [smul_add, ht, ht']

/-!

## C. The basis of tensors

-/

/-- The basis `e_μ ⊗ e^ν ⊗ …` of tensors, Mathlib's `Basis.piTensorProduct` of the bases of the
colors. -/
noncomputable def tensorBasis (S : Species k G K basisIdx) [Fintype ι] (c : ι → Color K) :
    Module.Basis (Π i, basisIdx (c i).kind) k (Tensor S c) :=
  (Basis.piTensorProduct fun i => S.basis (c i)).map (S.toPiTensor c).symm

/-- A basis tensor is the pure tensor of basis vectors, `e_μ ⊗ e^ν ⊗ …`. -/
lemma tensorBasis_apply [Fintype ι] (x : Π i, basisIdx (c i).kind) :
    S.tensorBasis c x = S.pure fun i => S.basis (c i) (x i) := by
  simp [tensorBasis, Basis.piTensorProduct_apply]

/-- The components of a pure tensor are products, `(u ⊗ α)^μ_ν = u^μ α_ν`. -/
lemma tensorBasis_repr_pure [Fintype ι] (f : Π i, S.V (c i))
    (x : Π i, basisIdx (c i).kind) :
    (S.tensorBasis c).repr (S.pure f) x = ∏ i, (S.basis (c i)).repr (f i) (x i) := by
  simp [tensorBasis, Basis.piTensorProduct_repr_tprod_apply]

/-- Tensors on finitely many indices are a finite-dimensional space. -/
noncomputable instance [Fintype ι] : Module.Finite k (Tensor S c) :=
  .of_basis (S.tensorBasis c)

/-- The dimension of tensors is the product of the dimensions of their indices. -/
lemma finrank_tensor [Fintype ι] [DecidableEq ι] (c : ι → Color K) :
    Module.finrank k (Tensor S c) = ∏ i, Fintype.card (basisIdx (c i).kind) := by
  rw [Module.finrank_eq_card_basis (S.tensorBasis c), Fintype.card_pi]

/-- The components of `g • t`, `(g t)^φ = ∑ ψ, (∏ i, g^{φ i}_{ψ i}) t^ψ`, with one matrix entry of
`g` per index, in the color of that index. -/
lemma tensorBasis_repr_smul [Fintype ι] [DecidableEq ι] (g : G) (t : Tensor S c)
    (φ : Π i, basisIdx (c i).kind) :
    (S.tensorBasis c).repr (g • t) φ = ∑ ψ, (∏ i, LinearMap.toMatrix (S.basis (c i))
      (S.basis (c i)) (S.rep (c i) g) (φ i) (ψ i)) * (S.tensorBasis c).repr t ψ := by
  conv_lhs => rw [← (S.tensorBasis c).sum_repr t, Finset.smul_sum]
  simp_rw [smul_comm g, map_sum, map_smul, Finsupp.coe_finsetSum, Finset.sum_apply,
    Finsupp.smul_apply, tensorBasis_apply, smul_pure, tensorBasis_repr_pure,
    LinearMap.toMatrix_apply, smul_eq_mul, mul_comm]

/-!

## D. Linear maps at the indices

-/

section

variable {c' : ι → Color K}

variable (S) in
/-- A linear map `f x` at every index `x`, as in `u ⊗ v ↦ f₀ u ⊗ f₁ v`. It is Mathlib's
`PiTensorProduct.map`. -/
noncomputable def mapIndices (f : Π x, S.V (c x) →ₗ[k] S.V (c' x)) : Tensor S c →ₗ[k] Tensor S c' :=
  (S.toPiTensor c').symm.toLinearMap ∘ₗ PiTensorProduct.map f ∘ₗ (S.toPiTensor c).toLinearMap

/-- On a pure tensor, `mapIndices` applies `f x` to the vector at each index `x`. -/
lemma mapIndices_pure (f : Π x, S.V (c x) →ₗ[k] S.V (c' x)) (p : Π x, S.V (c x)) :
    S.mapIndices f (S.pure p) = S.pure fun x => f x (p x) := by
  simp only [mapIndices, LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe,
    toPiTensor_pure, PiTensorProduct.map_tprod, toPiTensor_symm_tprod]

/-- Two index-wise maps in sequence are the index-wise map of the composites. -/
lemma mapIndices_comp {c'' : ι → Color K} (f : Π x, S.V (c x) →ₗ[k] S.V (c' x))
    (g : Π x, S.V (c' x) →ₗ[k] S.V (c'' x)) :
    S.mapIndices g ∘ₗ S.mapIndices f = S.mapIndices fun x => g x ∘ₗ f x :=
  ext_pure fun p => by simp only [LinearMap.comp_apply, mapIndices_pure]

/-- Two index-wise maps in sequence are the index-wise map of the composites, on a tensor. -/
lemma mapIndices_mapIndices {c'' : ι → Color K} (f : Π x, S.V (c x) →ₗ[k] S.V (c' x))
    (g : Π x, S.V (c' x) →ₗ[k] S.V (c'' x)) (t : Tensor S c) :
    S.mapIndices g (S.mapIndices f t) = S.mapIndices (fun x => g x ∘ₗ f x) t :=
  LinearMap.congr_fun (mapIndices_comp f g) t

/-- The index-wise map of the identities is the identity. -/
lemma mapIndices_id : S.mapIndices (c := c) (fun _ => LinearMap.id) = LinearMap.id :=
  ext_pure fun p => mapIndices_pure _ p

/-- The index-wise map of the identities is the identity, on a tensor. -/
lemma mapIndices_id_apply (t : Tensor S c) : S.mapIndices (fun _ => LinearMap.id) t = t :=
  LinearMap.congr_fun mapIndices_id t

/-- Linear maps that commute with the group action at every index commute with it on tensors,
`f (Λ T) = Λ f T`. -/
lemma mapIndices_smul {f : Π x, S.V (c x) →ₗ[k] S.V (c' x)}
    (hf : ∀ x g v, f x (S.rep (c x) g v) = S.rep (c' x) g (f x v)) (g : G) (t : Tensor S c) :
    S.mapIndices f (g • t) = g • S.mapIndices f t :=
  (Representation.IsIntertwiningMap.piTensorMap fun x => ⟨hf x⟩).isIntertwining g t

variable (S) in
/-- Equivalences of representations `f x` at every index `x`, as an equivalence of representations
of tensors, `u ⊗ v ↦ f₀ u ⊗ f₁ v`. It is `Representation.Equiv.piTensorCongr`. -/
noncomputable def congrIndices (f : Π x, (S.rep (c x)).Equiv (S.rep (c' x))) :
    (S.tensorRep c).Equiv (S.tensorRep c') :=
  Representation.Equiv.piTensorCongr f

/-- On a pure tensor, `congrIndices` applies `f x` to the vector at each index `x`. -/
lemma congrIndices_pure (f : Π x, (S.rep (c x)).Equiv (S.rep (c' x))) (p : Π x, S.V (c x)) :
    S.congrIndices f (S.pure p) = S.pure fun x => f x (p x) :=
  Representation.Equiv.piTensorCongr_tprod f p

section

variable [DecidableEq ι]

variable (S) in
/-- The family of linear maps with `f` at the index `i` and the identity, moved along `h x`, at
every other index `x`. `mapAt` applies it index by index. -/
noncomputable def indexMapsAt (i : ι) (f : S.V (c i) →ₗ[k] S.V (c' i))
    (h : ∀ x, x ≠ i → c x = c' x) : Π x, S.V (c x) →ₗ[k] S.V (c' x) :=
  Function.update (fun x => if hx : x = i then 0 else (S.cast (h x hx)).toLinearMap) i f

@[simp]
lemma indexMapsAt_apply_self (i : ι) (f : S.V (c i) →ₗ[k] S.V (c' i))
    (h : ∀ x, x ≠ i → c x = c' x) : S.indexMapsAt i f h i = f :=
  Function.update_self _ _ _

@[simp]
lemma indexMapsAt_apply_ne (i : ι) (f : S.V (c i) →ₗ[k] S.V (c' i))
    (h : ∀ x, x ≠ i → c x = c' x) {x : ι} (hx : x ≠ i) :
    S.indexMapsAt i f h x = (S.cast (h x hx)).toLinearMap := by
  rw [indexMapsAt, Function.update_of_ne hx, dite_eq_right hx]

/-- A family with `f` at the index `i` and the moves along `h x` at the other indices is
`indexMapsAt i f h`. -/
lemma eq_indexMapsAt {F : Π x, S.V (c x) →ₗ[k] S.V (c' x)} (i : ι)
    (f : S.V (c i) →ₗ[k] S.V (c' i)) (h : ∀ x, x ≠ i → c x = c' x) (hi : F i = f)
    (hne : ∀ x (hx : x ≠ i), F x = (S.cast (h x hx)).toLinearMap) : F = S.indexMapsAt i f h :=
  Function.eq_update_iff.2 ⟨hi, fun x hx => by rw [hne x hx, dite_eq_right hx]⟩

/-- `indexMapsAt i f h` commutes with the group action at every index when `f` does. -/
lemma indexMapsAt_rep (i : ι) (f : S.V (c i) →ₗ[k] S.V (c' i)) (h : ∀ x, x ≠ i → c x = c' x)
    (hf : ∀ g v, f (S.rep (c i) g v) = S.rep (c' i) g (f v)) (x : ι) (g : G) (v : S.V (c x)) :
    S.indexMapsAt i f h x (S.rep (c x) g v) = S.rep (c' x) g (S.indexMapsAt i f h x v) := by
  by_cases hx : x = i
  · subst hx
    simpa using hf g v
  · simpa [hx] using cast_rep (h x hx) g v

variable (S) in
/-- The linear map `f` at the index `i`, and the identity, moved along `h x`, at every other index
`x`, as in `u ⊗ v ⊗ w ↦ u ⊗ f v ⊗ w`. -/
noncomputable def mapAt (i : ι) (f : S.V (c i) →ₗ[k] S.V (c' i))
    (h : ∀ x, x ≠ i → c x = c' x) : Tensor S c →ₗ[k] Tensor S c' :=
  S.mapIndices (S.indexMapsAt i f h)

/-- On a pure tensor, `mapAt` applies `f` to the vector at `i` and keeps the others,
`u ⊗ v ⊗ w ↦ u ⊗ f v ⊗ w`. -/
lemma mapAt_pure (i : ι) (f : S.V (c i) →ₗ[k] S.V (c' i)) (h : ∀ x, x ≠ i → c x = c' x)
    (p : Π x, S.V (c x)) (q : Π x, S.V (c' x)) (hqi : q i = f (p i))
    (hq : ∀ x (hx : x ≠ i), q x = S.cast (h x hx) (p x)) :
    S.mapAt i f h (S.pure p) = S.pure q := by
  rw [mapAt, mapIndices_pure]
  refine congrArg S.pure (funext fun x => ?_)
  by_cases hx : x = i
  · subst hx
    rw [indexMapsAt_apply_self, hqi]
  · rw [indexMapsAt_apply_ne _ _ _ hx, hq x hx]
    rfl

/-- `mapAt` of `f` and then of `g` at the same index is `mapAt` of `g ∘ₗ f`. -/
lemma mapAt_comp {c'' : ι → Color K} (i : ι) (f : S.V (c i) →ₗ[k] S.V (c' i))
    (g : S.V (c' i) →ₗ[k] S.V (c'' i)) (h : ∀ x, x ≠ i → c x = c' x)
    (h' : ∀ x, x ≠ i → c' x = c'' x) :
    S.mapAt i g h' ∘ₗ S.mapAt i f h = S.mapAt i (g ∘ₗ f) fun x hx => (h x hx).trans (h' x hx) := by
  rw [mapAt, mapAt, mapAt, mapIndices_comp]
  refine congrArg _ (eq_indexMapsAt i _ _ (by simp) fun x hx => LinearMap.ext fun v => ?_)
  simp [hx]

/-- `mapAt` of the identity is the identity. -/
lemma mapAt_id (i : ι) (h : ∀ x, x ≠ i → c x = c x) :
    S.mapAt i LinearMap.id h = LinearMap.id := by
  rw [mapAt, ← eq_indexMapsAt (F := fun _ => LinearMap.id) i _ h rfl
    fun _ _ => LinearMap.ext fun _ => rfl, mapIndices_id]

/-- `mapAt` in components, `(f t)^…ν… = ∑ μ, f^ν_μ t^…μ…`, with `f^ν_μ` the matrix of `f`. -/
lemma tensorBasis_repr_mapAt [Fintype ι] (i : ι) (f : S.V (c i) →ₗ[k] S.V (c' i))
    (h : ∀ x, x ≠ i → c x = c' x) (t : Tensor S c) (φ : Π x, basisIdx (c' x).kind)
    (ψ : Π x, basisIdx (c x).kind)
    (hψ : ∀ x (hx : x ≠ i), ψ x = cast (congrArg (basisIdx ∘ Color.kind) (h x hx).symm) (φ x)) :
    (S.tensorBasis c').repr (S.mapAt i f h t) φ = ∑ μ : basisIdx (c i).kind,
      LinearMap.toMatrix (S.basis (c i)) (S.basis (c' i)) f (φ i) μ *
        (S.tensorBasis c).repr t (Function.update ψ i μ) := by
  induction t using inductionOn_pure with
  | hsmul r t ht =>
    simp only [map_smul, Finsupp.smul_apply, ht, smul_eq_mul, Finset.mul_sum, mul_left_comm r]
  | hadd t t' ht ht' =>
    simp only [map_add, Finsupp.add_apply, ht, ht', mul_add, Finset.sum_add_distrib]
  | h p =>
    -- Split off the index `i`, where `f` acts, from the indices where the label is only moved.
    rw [mapAt, mapIndices_pure, tensorBasis_repr_pure,
      ← Finset.mul_prod_erase _ _ (Finset.mem_univ i), indexMapsAt_apply_self,
      ← LinearMap.toMatrix_mulVec_repr (S.basis (c i)) (S.basis (c' i)), Matrix.mulVec, dotProduct,
      Finset.sum_mul]
    refine Finset.sum_congr rfl fun μ _ => ?_
    rw [tensorBasis_repr_pure, ← Finset.mul_prod_erase _ _ (Finset.mem_univ i),
      Function.update_self, mul_assoc]
    refine congrArg _ (congrArg _ (Finset.prod_congr rfl fun x hx => ?_))
    have hx := Finset.ne_of_mem_erase hx
    rw [indexMapsAt_apply_ne _ _ _ hx, Function.update_of_ne hx, hψ x hx]
    exact basis_repr_cast _ _ _

variable (S) in
/-- The equivalence of representations `f` at the index `i`, and the identity, moved along `h x`,
at every other index `x`. On a pure tensor, `u ⊗ v ⊗ w ↦ u ⊗ f v ⊗ w`. Its linear map is `mapAt`
of `f`. -/
noncomputable def congrAt (i : ι) (f : (S.rep (c i)).Equiv (S.rep (c' i)))
    (h : ∀ x, x ≠ i → c x = c' x) : (S.tensorRep c).Equiv (S.tensorRep c') :=
  equivOfPure (.ofLinearMap (S.mapAt i f.toLinearMap h)
    (S.mapAt i f.symm.toLinearMap fun x hx => (h x hx).symm)
    (by rw [mapAt_comp, show f.toLinearMap ∘ₗ f.symm.toLinearMap = LinearMap.id from
      LinearMap.ext f.apply_symm_apply, mapAt_id])
    (by rw [mapAt_comp, show f.symm.toLinearMap ∘ₗ f.toLinearMap = LinearMap.id from
      LinearMap.ext f.symm_apply_apply, mapAt_id])) fun g p =>
    mapIndices_smul (indexMapsAt_rep i _ h (f.toIntertwiningMap.isIntertwining _ _)) g (S.pure p)

/-- `congrAt` is `mapAt` of the underlying linear map. -/
lemma congrAt_eq_mapAt (i : ι) (f : (S.rep (c i)).Equiv (S.rep (c' i)))
    (h : ∀ x, x ≠ i → c x = c' x) (t : Tensor S c) :
    S.congrAt i f h t = S.mapAt i f.toLinearMap h t := rfl

/-- The inverse of `congrAt` of `f` is `congrAt` of `f.symm`. -/
lemma congrAt_symm (i : ι) (f : (S.rep (c i)).Equiv (S.rep (c' i)))
    (h : ∀ x, x ≠ i → c x = c' x) :
    (S.congrAt i f h).symm = S.congrAt i f.symm (fun x hx => (h x hx).symm) :=
  Representation.Equiv.ext rfl

end

end

end Species

end Tensor
