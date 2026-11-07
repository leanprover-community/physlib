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
slot type `ι`, and the group acts on them slot by slot.

## i. Overview

A tensor of a species `S` has one slot for each label `i : ι`, and slot `i` has the color `c i`.
The tensors with colors `c : ι → Color K` form the space `S.Tensor c`, which is Mathlib's
`⨂[k] i, V (c i)`. The slots `ι` can be any type, so later files label slots by `Fin n`, sums or
options without renumbering.

A pure tensor takes one vector in each slot, such as `u ⊗ α ⊗ β` with `u` in `V (c 0)`, `α` in
`V (c 1)` and `β` in `V (c 2)`. Its components are products, `(u ⊗ α ⊗ β)^μ_νρ = u^μ α_ν β_ρ`.
Most tensors are not pure. The metric `η = ∑ μ, η_μμ e^μ ⊗ e^μ` is a sum of pure tensors but not
a pure tensor itself. Every tensor is such a sum, so a linear map of tensors is fixed by its
values on pure tensors (`ext_pure`), and a property of all tensors follows from the pure case
(`inductionOn_pure`). The group action, relabeling, products and contraction are each given by
their value on pure tensors, and their laws are proved there first. `S.pure f` is Mathlib's
`⨂ₜ[k] i, f i` as an element of `S.Tensor c`.

A group element `Λ` acts on every slot by the representation of its color,
`Λ (u ⊗ α ⊗ β) = Λu ⊗ Λα ⊗ Λβ` (`smul_pure`). A map that commutes with `Λ` on pure tensors
commutes with it on all tensors (`map_smul_of_pure`).

The components `T^μ_νρ` of a tensor `T` are its coordinates in the basis `e_μ ⊗ e^ν ⊗ e^ρ`
(`tensorBasis`), which is Mathlib's `Basis.piTensorProduct`. Each basis tensor is a pure tensor of
basis vectors.

For example, the Lorentz colors `![⟨vec, up⟩, ⟨vec, down⟩, ⟨vec, down⟩]` give the space
`ℝ⁴ ⊗ (ℝ⁴)* ⊗ (ℝ⁴)*` of tensors `T = T^μ_νρ e_μ ⊗ e^ν ⊗ e^ρ`. A Lorentz transformation `Λ` acts
as `(ΛT)^μ_νρ = Λ^μ_σ (Λ⁻¹)^τ_ν (Λ⁻¹)^λ_ρ T^σ_τλ` (`tensorBasis_repr_smul`). Lower indices
transform with `Λ⁻¹`, which keeps `u^μ α_μ` invariant.

A linear equivalence `f` from the space of one color to that of another acts on tensors through a
single slot. `S.congrAt i f` applies `f` at the slot `i` and the identity at the other slots,
`u ⊗ v ⊗ w ↦ u ⊗ f v ⊗ w`, as lowering one index of a tensor does.

## ii. Key results

- `Species.Tensor` and `Species.pure` are the tensors and the pure tensors, and
  `Species.inductionOn_pure` is induction through pure tensors.
- `Species.ext_pure` proves that linear maps of tensors that agree on pure tensors are equal.
- `Species.smul_pure` proves that the group acts on a pure tensor slot by slot.
- `Species.map_smul_of_pure` proves that a map of tensors that commutes with the group on pure
  tensors commutes with it on all tensors.
- `Species.tensorRep` is the action on tensors as a Mathlib representation. Maps of tensors that
  commute with the group are Mathlib's `Representation.Equiv` and `Representation.IntertwiningMap`
  of it, built by `Species.equivOfPure` and `Species.intertwiningMapOfPure` from a check on pure
  tensors, and `Species.equiv_smul` and `Species.intertwiningMap_smul` give `φ (g • t) = g • φ t`.
- `Species.smul_eq_self_of_isEmpty` proves that a tensor with no slots is invariant.
- `Species.tensorBasis` is the basis of tensors, and `Species.tensorBasis_repr_pure` gives the
  components of a pure tensor.
- `Species.tensorBasis_repr_smul` gives the components of `g • t`.
- `Species.mapSlots` applies a linear map at every slot, with `Species.mapSlots_mapSlots` and
  `Species.mapSlots_id`, and `Species.mapAt` applies one at a single slot and the identity at the
  others.
- `Species.congrSlots` applies an equivalence of representations at every slot.
- `Species.congrAt` applies an equivalence of representations at one slot of a tensor and the
  identity at the others, with `Species.congrAt_pure` and `Species.congrAt_symm`, and
  `Species.congrAt_eq_mapAt` proves that `congrAt` is `mapAt` of the underlying map.

## iii. Table of contents

- A. Tensors
- B. The group action
- C. The basis of tensors
- D. A linear map at one slot

## iv. References

None.

-/

@[expose] public section

open TensorProduct PiTensorProduct

namespace Tensors

namespace Species

variable {k : Type} [CommRing k] {K : Type} {G : Type} [Group G] {basisIdx : K → Type}
    [∀ κ, Fintype (basisIdx κ)] [∀ κ, DecidableEq (basisIdx κ)]

/-!

## A. Tensors

-/

/-- The space `⨂[k] i, S.V (c i)` of tensors with colors `c` on the slots `ι`. It is a `def`, not
an `abbrev`, so that the type `S.Tensor c` keeps the species and the colors, which index notation
reads off the type of a tensor. -/
def Tensor (S : Species k G K basisIdx) {ι : Type} (c : ι → Color K) : Type :=
  ⨂[k] i, S.V (c i)

noncomputable instance {S : Species k G K basisIdx} {ι : Type} {c : ι → Color K} :
    AddCommGroup (S.Tensor c) :=
  inferInstanceAs (AddCommGroup (⨂[k] i, S.V (c i)))

noncomputable instance {S : Species k G K basisIdx} {ι : Type} {c : ι → Color K} :
    Module k (S.Tensor c) :=
  inferInstanceAs (Module k (⨂[k] i, S.V (c i)))

variable {ι : Type} {c : ι → Color K}

/-- The identity from `S.Tensor c` to Mathlib's `⨂[k] i, S.V (c i)`, as a linear equivalence.
Mathlib's constructions on `⨂` are composed with it. -/
noncomputable def toPiTensor (S : Species k G K basisIdx) (c : ι → Color K) :
    S.Tensor c ≃ₗ[k] ⨂[k] i, S.V (c i) :=
  LinearEquiv.refl k _

/-- The pure tensor of a family of vectors, one per slot, such as `u ⊗ α ⊗ β` with components
`u^μ α_ν β_ρ`. It is Mathlib's `⨂ₜ[k] i, f i`. -/
noncomputable def pure (S : Species k G K basisIdx) (f : Π i, S.V (c i)) : S.Tensor c :=
  (S.toPiTensor c).symm (⨂ₜ[k] i, f i)

variable {S : Species k G K basisIdx}

@[simp]
lemma toPiTensor_pure (f : Π i, S.V (c i)) : S.toPiTensor c (S.pure f) = ⨂ₜ[k] i, f i := rfl

@[simp]
lemma toPiTensor_symm_tprod (f : Π i, S.V (c i)) :
    (S.toPiTensor c).symm (⨂ₜ[k] i, f i) = S.pure f := rfl

/-- Induction on tensors through pure tensors: every tensor is a sum of pure tensors. -/
lemma inductionOn_pure {P : S.Tensor c → Prop}
    (h : ∀ f : Π i, S.V (c i), P (S.pure f)) (hsmul : ∀ (r : k) t, P t → P (r • t))
    (hadd : ∀ t₁ t₂, P t₁ → P t₂ → P (t₁ + t₂)) (t : S.Tensor c) : P t :=
  PiTensorProduct.induction_on (motive := P) t (fun r f => hsmul r _ (h f)) hadd

/-- Two linear maps out of tensors are equal when they agree on pure tensors. -/
lemma ext_pure {E : Type} [AddCommGroup E] [Module k E] {f g : S.Tensor c →ₗ[k] E}
    (h : ∀ p : Π i, S.V (c i), f (S.pure p) = g (S.pure p)) : f = g :=
  PiTensorProduct.ext (MultilinearMap.ext h)

/-!

## B. The group action

-/

/-- The group acts on every slot by the representation of its color,
`Λ (u ⊗ α ⊗ …) = Λu ⊗ Λα ⊗ …`. -/
noncomputable instance : DistribMulAction G (S.Tensor c) :=
  DistribMulAction.compHom (M := Module.End k (S.Tensor c)) _
    (PiTensorProduct.mapMonoidHom.comp (MonoidHom.pi fun i => S.rep (c i)))

@[simp]
lemma smul_pure (g : G) (f : Π i, S.V (c i)) :
    g • S.pure f = S.pure fun i => S.rep (c i) g (f i) :=
  PiTensorProduct.map_tprod _ _

noncomputable instance : SMulCommClass G k (S.Tensor c) where
  smul_comm g r t := by
    change PiTensorProduct.map (fun i => S.rep (c i) g) (r • t) = r • PiTensorProduct.map _ t
    exact map_smul _ r t

noncomputable instance : SMulCommClass k G (S.Tensor c) := .symm _ _ _

variable (S) in
/-- The action of the group on tensors as Mathlib's representation, `Λ ↦ (T ↦ Λ • T)`. Maps of
tensors that commute with the action are Mathlib's `Representation.Equiv` and
`Representation.IntertwiningMap` for it. -/
noncomputable abbrev tensorRep (c : ι → Color K) : Representation k G (S.Tensor c) :=
  Representation.ofDistribMulAction k G (S.Tensor c)

/-- An intertwining map from or to tensors commutes with the actions, `φ (Λ v) = Λ φ v`. -/
lemma intertwiningMap_smul {ι' : Type} {c' : ι' → Color K}
    (φ : (S.tensorRep c).IntertwiningMap (S.tensorRep c')) (g : G) (t : S.Tensor c) :
    φ (g • t) = g • φ t :=
  Representation.IntertwiningMap.isIntertwining _ _ φ g t

/-- An equivalence of representations of tensors commutes with the actions, `φ (Λ T) = Λ φ T`. -/
lemma equiv_smul {ι' : Type} {c' : ι' → Color K}
    (φ : (S.tensorRep c).Equiv (S.tensorRep c')) (g : G) (t : S.Tensor c) :
    φ (g • t) = g • φ t :=
  intertwiningMap_smul φ.toIntertwiningMap g t

/-- A linear or conjugate-linear map of tensors that commutes with `Λ` on pure tensors commutes
with `Λ` on all tensors. -/
lemma map_smul_of_pure {ι' : Type} {c' : ι' → Color K} {σ : k →+* k} {F : Type}
    [FunLike F (S.Tensor c) (S.Tensor c')] [SemilinearMapClass F σ (S.Tensor c) (S.Tensor c')]
    (f : F) (g : G) (h : ∀ p : Π i, S.V (c i), f (g • S.pure p) = g • f (S.pure p))
    (t : S.Tensor c) : f (g • t) = g • f t := by
  induction t using inductionOn_pure with
  | h p => exact h p
  | hsmul r t ht => rw [smul_comm, map_smulₛₗ, ht, map_smulₛₗ, smul_comm]
  | hadd x y hx hy => rw [smul_add, map_add, hx, hy, map_add, smul_add]

variable {ι' : Type} {c' : ι' → Color K} in
/-- A linear equivalence of tensors that commutes with `Λ` on pure tensors, as an equivalence of
representations. -/
noncomputable def equivOfPure (e : S.Tensor c ≃ₗ[k] S.Tensor c')
    (h : ∀ (g : G) (p : Π i, S.V (c i)), e (g • S.pure p) = g • e (S.pure p)) :
    (S.tensorRep c).Equiv (S.tensorRep c') :=
  .mk e fun g => LinearMap.ext fun t => map_smul_of_pure e g (h g) t

variable {ι' : Type} {c' : ι' → Color K} in
@[simp]
lemma equivOfPure_apply (e : S.Tensor c ≃ₗ[k] S.Tensor c')
    (h : ∀ (g : G) (p : Π i, S.V (c i)), e (g • S.pure p) = g • e (S.pure p)) (t : S.Tensor c) :
    equivOfPure e h t = e t := rfl

variable {ι' : Type} {c' : ι' → Color K} in
/-- A linear map of tensors that commutes with `Λ` on pure tensors, as an intertwining map. -/
noncomputable def intertwiningMapOfPure (f : S.Tensor c →ₗ[k] S.Tensor c')
    (h : ∀ (g : G) (p : Π i, S.V (c i)), f (g • S.pure p) = g • f (S.pure p)) :
    (S.tensorRep c).IntertwiningMap (S.tensorRep c') :=
  ⟨f, fun g => LinearMap.ext fun t => map_smul_of_pure f g (h g) t⟩

variable {ι' : Type} {c' : ι' → Color K} in
@[simp]
lemma intertwiningMapOfPure_apply (f : S.Tensor c →ₗ[k] S.Tensor c')
    (h : ∀ (g : G) (p : Π i, S.V (c i)), f (g • S.pure p) = g • f (S.pure p)) (t : S.Tensor c) :
    intertwiningMapOfPure f h t = f t := rfl

/-- A tensor with no slots is invariant, `Λ s = s`. -/
lemma smul_eq_self_of_isEmpty [IsEmpty ι] (g : G) (t : S.Tensor c) : g • t = t := by
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
    Module.Basis (Π i, basisIdx (c i).kind) k (S.Tensor c) :=
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

/-- The coefficient of `e_ψ` in `g • e_φ` is the product over the indices of the matrix entries of
`g` in the color of that index. -/
lemma tensorBasis_repr_smul_tensorBasis [Fintype ι] (g : G) (φ ψ : Π i, basisIdx (c i).kind) :
    (S.tensorBasis c).repr (g • S.tensorBasis c φ) ψ =
      ∏ i, LinearMap.toMatrix (S.basis (c i)) (S.basis (c i)) (S.rep (c i) g) (ψ i) (φ i) := by
  simp [tensorBasis_apply, tensorBasis_repr_pure, LinearMap.toMatrix_apply]

/-- The action of `g` on a basis tensor, `g e_φ = ∑ ψ, (∏ i, g^{ψ i}_{φ i}) e_ψ`, with one matrix
entry of `g` per index, in the color of that index. -/
lemma smul_tensorBasis_eq_sum [Fintype ι] [DecidableEq ι] (g : G) (φ : Π i, basisIdx (c i).kind) :
    g • S.tensorBasis c φ = ∑ ψ, (∏ i, LinearMap.toMatrix (S.basis (c i)) (S.basis (c i))
      (S.rep (c i) g) (ψ i) (φ i)) • S.tensorBasis c ψ := by
  conv_lhs => rw [← (S.tensorBasis c).sum_repr (g • S.tensorBasis c φ)]
  simp_rw [tensorBasis_repr_smul_tensorBasis]

/-- The components of `g • t`, `(g t)^φ = ∑ ψ, (∏ i, g^{φ i}_{ψ i}) t^ψ`, with one matrix entry of
`g` per index, in the color of that index. -/
lemma tensorBasis_repr_smul [Fintype ι] [DecidableEq ι] (g : G) (t : S.Tensor c)
    (φ : Π i, basisIdx (c i).kind) :
    (S.tensorBasis c).repr (g • t) φ = ∑ ψ, (∏ i, LinearMap.toMatrix (S.basis (c i))
      (S.basis (c i)) (S.rep (c i) g) (φ i) (ψ i)) * (S.tensorBasis c).repr t ψ := by
  conv_lhs => rw [← (S.tensorBasis c).sum_repr t, Finset.smul_sum]
  simp_rw [smul_comm g, map_sum, map_smul, Finsupp.coe_finsetSum, Finset.sum_apply,
    Finsupp.smul_apply, tensorBasis_repr_smul_tensorBasis, smul_eq_mul, mul_comm]

/-!

## D. A linear map at one slot

-/

section

variable [DecidableEq ι] {c' : ι → Color K}

variable (S) in
/-- Equivalences of representations `f x` at every slot `x`, as an equivalence of representations
of tensors, `u ⊗ v ↦ f₀ u ⊗ f₁ v`. It is Mathlib's `PiTensorProduct.congr`. -/
noncomputable def congrSlots (f : Π x, (S.rep (c x)).Equiv (S.rep (c' x))) :
    (S.tensorRep c).Equiv (S.tensorRep c') :=
  equivOfPure (S.toPiTensor c ≪≫ₗ PiTensorProduct.congr (fun x => (f x).toLinearEquiv) ≪≫ₗ
    (S.toPiTensor c').symm) fun g p => by
      simp only [smul_pure, LinearEquiv.trans_apply, toPiTensor_pure, congr_tprod,
        toPiTensor_symm_tprod]
      exact congrArg S.pure (funext fun x =>
        Representation.IntertwiningMap.isIntertwining _ _ (f x).toIntertwiningMap g (p x))

omit [DecidableEq ι] in
/-- On a pure tensor, `congrSlots` applies `f x` to the vector at each slot `x`. -/
lemma congrSlots_pure (f : Π x, (S.rep (c x)).Equiv (S.rep (c' x))) (p : Π x, S.V (c x)) :
    S.congrSlots f (S.pure p) = S.pure fun x => f x (p x) := by
  simp [congrSlots, congr_tprod]

variable (S) in
/-- The equivalence of representations `f` at the slot `i`, and the identity, moved along `h x`,
at every other slot `x`. On a pure tensor, `u ⊗ v ⊗ w ↦ u ⊗ f v ⊗ w`. -/
noncomputable def congrAt (i : ι) (f : (S.rep (c i)).Equiv (S.rep (c' i)))
    (h : ∀ x, x ≠ i → c x = c' x) : (S.tensorRep c).Equiv (S.tensorRep c') :=
  S.congrSlots fun x => if hx : x = i then hx ▸ f else S.cast (h x hx)

/-- On a pure tensor, `congrAt` applies `f` to the vector at `i`, `u ⊗ v ⊗ w ↦ u ⊗ f v ⊗ w`.
The result is given by its vectors `q`, `f (p i)` at `i` and `p x` moved along `h x` elsewhere. -/
lemma congrAt_pure (i : ι) (f : (S.rep (c i)).Equiv (S.rep (c' i)))
    (h : ∀ x, x ≠ i → c x = c' x) (p : Π x, S.V (c x)) (q : Π x, S.V (c' x))
    (hqi : q i = f (p i))
    (hq : ∀ x (hx : x ≠ i), q x = S.cast (h x hx) (p x)) :
    S.congrAt i f h (S.pure p) = S.pure q := by
  rw [congrAt, congrSlots_pure]
  congr 1
  funext x
  by_cases hx : x = i
  · subst hx
    simp [hqi]
  · simp [hx, hq x hx]

/-- The inverse of `congrAt` of `f` is `congrAt` of `f.symm`. -/
lemma congrAt_symm (i : ι) (f : (S.rep (c i)).Equiv (S.rep (c' i)))
    (h : ∀ x, x ≠ i → c x = c' x) :
    (S.congrAt i f h).symm = S.congrAt i f.symm (fun x hx => (h x hx).symm) := by
  refine Representation.Equiv.ext (funext fun t => ?_)
  refine (S.congrAt i f h).toLinearEquiv.symm_apply_eq.2 ?_
  induction t using inductionOn_pure with
  | h p =>
    change _ = S.congrSlots _ (S.congrSlots _ (S.pure p))
    rw [congrSlots_pure, congrSlots_pure]
    congr 1
    funext x
    by_cases hx : x = i
    · subst hx
      simp
    · simp [hx]
  | hsmul r t ht => rw [map_smul, map_smul, ← ht]
  | hadd x y hx hy => rw [map_add, map_add, ← hx, ← hy]

variable (S) in
/-- A linear map `f x` at every slot `x`, as in `u ⊗ v ↦ f₀ u ⊗ f₁ v`. It is Mathlib's
`PiTensorProduct.map`. -/
noncomputable def mapSlots (f : Π x, S.V (c x) →ₗ[k] S.V (c' x)) : S.Tensor c →ₗ[k] S.Tensor c' :=
  (S.toPiTensor c').symm.toLinearMap ∘ₗ PiTensorProduct.map f ∘ₗ (S.toPiTensor c).toLinearMap

omit [DecidableEq ι] in
/-- On a pure tensor, `mapSlots` applies `f x` to the vector at each slot `x`. -/
lemma mapSlots_pure (f : Π x, S.V (c x) →ₗ[k] S.V (c' x)) (p : Π x, S.V (c x)) :
    S.mapSlots f (S.pure p) = S.pure fun x => f x (p x) := by
  simp only [mapSlots, LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe,
    toPiTensor_pure, PiTensorProduct.map_tprod, toPiTensor_symm_tprod]

omit [DecidableEq ι] in
/-- Two slotwise maps in sequence are the slotwise map of the composites. -/
lemma mapSlots_mapSlots {c'' : ι → Color K} (f : Π x, S.V (c x) →ₗ[k] S.V (c' x))
    (g : Π x, S.V (c' x) →ₗ[k] S.V (c'' x)) (t : S.Tensor c) :
    S.mapSlots g (S.mapSlots f t) = S.mapSlots (fun x => g x ∘ₗ f x) t := by
  simp only [mapSlots, LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.apply_symm_apply, ← LinearMap.comp_apply (PiTensorProduct.map g),
    ← PiTensorProduct.map_comp]

omit [DecidableEq ι] in
/-- The slotwise map of the identities is the identity. -/
lemma mapSlots_id (t : S.Tensor c) : S.mapSlots (fun _ => LinearMap.id) t = t := by
  simp [mapSlots, PiTensorProduct.map_id]

variable (S) in
/-- The linear map `f` at the slot `i`, and the identity, moved along `h x`, at every other slot
`x`, as in `u ⊗ v ⊗ w ↦ u ⊗ f v ⊗ w`. -/
noncomputable def mapAt (i : ι) (f : S.V (c i) →ₗ[k] S.V (c' i))
    (h : ∀ x, x ≠ i → c x = c' x) : S.Tensor c →ₗ[k] S.Tensor c' :=
  S.mapSlots
    (Function.update (fun x => if hx : x = i then 0 else (S.cast (h x hx)).toLinearMap) i f)

/-- On a pure tensor, `mapAt` applies `f` to the vector at `i`, `u ⊗ v ⊗ w ↦ u ⊗ f v ⊗ w`. The
result is given by its vectors `q`, `f (p i)` at `i` and `p x` moved along `h x` elsewhere. -/
lemma mapAt_pure (i : ι) (f : S.V (c i) →ₗ[k] S.V (c' i)) (h : ∀ x, x ≠ i → c x = c' x)
    (p : Π x, S.V (c x)) (q : Π x, S.V (c' x)) (hqi : q i = f (p i))
    (hq : ∀ x (hx : x ≠ i), q x = S.cast (h x hx) (p x)) :
    S.mapAt i f h (S.pure p) = S.pure q := by
  rw [mapAt, mapSlots_pure]
  congr 1
  funext x
  by_cases hx : x = i
  · subst hx
    simp [hqi]
  · simp [hx, hq x hx]

/-- `congrAt` is `mapAt` of the underlying linear map. -/
lemma congrAt_eq_mapAt (i : ι) (f : (S.rep (c i)).Equiv (S.rep (c' i)))
    (h : ∀ x, x ≠ i → c x = c' x) (t : S.Tensor c) :
    S.congrAt i f h t = S.mapAt i f.toLinearMap h t := by
  induction t using inductionOn_pure with
  | h p =>
    let q : Π x, S.V (c' x) := fun x => if hx : x = i then hx ▸ f (p i) else S.cast (h x hx) (p x)
    rw [congrAt_pure i f h p q (by simp [q]) (fun x hx => by simp [q, hx]),
      mapAt_pure i _ h p q (by simp [q]) (fun x hx => by simp [q, hx])]
  | hsmul r t ht => rw [map_smul, map_smul, ht]
  | hadd x y hx hy => rw [map_add, map_add, hx, hy]

end

end Species

end Tensors
