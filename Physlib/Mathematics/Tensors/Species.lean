/-
Copyright (c) 2026 Andrea Pari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrea Pari
-/
module

public import Physlib.Mathematics.ForMathlib.Contraction
public import Physlib.Mathematics.Tensors.Color
public import Mathlib.RepresentationTheory.Intertwining
public import Mathlib.LinearAlgebra.Basis.Bilinear
/-!

# Tensor species

A species assigns to each color a representation with a basis whose coordinate pairing with the
basis of the dual color is invariant.

## i. Overview

A species `S : Species k G K basisIdx` assigns to each color `c` a `k`-module `S.V c`, a
representation `S.rep c` of `G` and a basis `S.basis c`. The data is indexed by colors, so that
one definition covers both variances. The contraction `S.contr c : V c ⊗ V c.dual → k` is
`u^μ α_μ` for `c = ⟨vec, up⟩` and `α_μ u^μ` for `c = ⟨vec, down⟩`.

The basis of a color `c` is labelled by `basisIdx c.kind`, the values that an index of that kind
runs over. For Lorentz tensors `basisIdx vec = Fin 1 ⊕ Fin d`, one time label and `d` space
labels, and the number of labels is the dimension. The labels depend on the kind alone, so an
index and its dual share them, as `μ` in `v^μ` and `α_μ`. `basisIdx` is a parameter of the
structure, not a field, so that a conjugate species gives conjugate kinds the same labels
(`Conjugation.lean`).

The space of a lower index is data of the species, not `Module.Dual` of the upper one, so that
existing types such as `CoVector d` serve as covectors. The one law of a species (`invariant`) says
that the coordinate pairing `u ⊗ α ↦ ∑ μ, u^μ α_μ` of the bases of `c` and `c.dual` is invariant,
which makes `V c.dual` the dual of `V c`.

The contraction `S.contr c` is this pairing, and the delta `S.delta c` is `∑ μ, e^μ ⊗ e_μ` in
`V c.dual ⊗ V c`. The bases of `c` and `c.dual` are then dual (`contr_basis`), the contraction is
symmetric (`contr_tmul_symm`), the delta acts as the identity, `u^μ δ_μ^ν = u^ν` (`snake`), and
both are invariant. Indices name slots, as in abstract index notation, so `u^μ α_μ` is
`S.contr c (u ⊗ α)`.

## ii. Key results

- `Species` is the data and the law of a tensor species.
- `Species.contr` and `Species.delta` are the contraction `u^μ α_μ` and the delta `δ_μ^ν`, with
  `Species.contr_basis`, `Species.contr_tmul_symm` and `Species.snake`.
- `Species.contr_tmul_eq_sum_basis` gives the contraction of two vectors in components, and
  `Species.ext_contr` proves that the contraction is nondegenerate.
- `Species.coordPairing_rep_of_contr` gives the law `invariant` from an invariant pairing for
  which the bases are dual.
- `Species.contr_invariant` and `Species.delta_invariant` prove that `u^μ α_μ` and `δ_μ^ν` are
  invariant.
- `Species.delta_eq_comm_delta_dual` proves that the delta of `c` is the delta of `c.dual` with
  its factors swapped.
- `Species.toLin` identifies `V a ⊗ U` with the linear maps `V a.dual → U`, and
  `Species.toLin_map_rep` proves that it commutes with the group action, `(Λg)(Λv) = Λ(g v)`.
- `Species.basis_repr_pairingToLinearMap_contr` gives the components of a tensor in
  `V c.dual ⊗ V d` read as a linear map, and `Species.toLin_comp_toLin_of_mul_eq_one` proves that
  two such maps are inverse when their matrices are.
- `Species.cast` moves a vector along an equality of colors, `Species.cast_rep` proves that this
  commutes with the group action, and `Species.basis_repr_cast` that it keeps components.
- `Species.contr_cast_tmul_cast` and `Species.contr_cast_tmul_cast_symm` prove that the
  contraction does not depend on the colors its two vectors are moved to.

## iii. Table of contents

- A. Species, the contraction and the delta
- B. Invariance, symmetry of the delta, and tensors of two factors as linear maps
- C. Components of a tensor of two factors read as a linear map
- D. Moving a vector along an equality of colors

## iv. References

None.

-/

@[expose] public section

open TensorProduct

namespace Tensors

/-!

## A. Species, the contraction and the delta

-/

/-- A tensor species, which gives each color a representation with a basis such that the
coordinate pairing `u ⊗ α ↦ ∑ μ, u^μ α_μ` with the basis of the dual color is invariant. The basis
of a color of kind `κ` is labelled by `basisIdx κ`, the values that an index of kind `κ` runs
over, and a color and its dual share these labels. -/
structure Species (k : Type) [CommRing k] (G : Type) [Group G] (K : Type)
    (basisIdx : K → Type) [∀ κ, Fintype (basisIdx κ)] [∀ κ, DecidableEq (basisIdx κ)] where
  /-- The vector space of a color. -/
  V : Color K → Type
  /-- The vector spaces are additive groups. -/
  [addCommGroup : ∀ c, AddCommGroup (V c)]
  /-- The vector spaces are modules over `k`. -/
  [module : ∀ c, Module k (V c)]
  /-- The representation of a color. -/
  rep : (c : Color K) → Representation k G (V c)
  /-- The basis of a color. -/
  basis : (c : Color K) → Module.Basis (basisIdx c.kind) k (V c)
  /-- The coordinate pairing `u ⊗ α ↦ ∑ μ, u^μ α_μ` of the bases of `c` and `c.dual` is
  invariant, `(Λu)^μ (Λα)_μ = u^μ α_μ`. -/
  invariant : ∀ c g x y, (basis c).coordPairing (basis c.dual) (rep c g x ⊗ₜ rep c.dual g y) =
    (basis c).coordPairing (basis c.dual) (x ⊗ₜ y)

attribute [instance] Species.addCommGroup Species.module

namespace Species

variable {k : Type} [CommRing k] {K : Type} {G : Type} [Group G] {basisIdx : K → Type}
    [∀ κ, Fintype (basisIdx κ)] [∀ κ, DecidableEq (basisIdx κ)]

/-- The invariant contraction `V c ⊗ V c.dual → k`, `u ⊗ α ↦ u^μ α_μ`, the coordinate pairing of
the bases. The vector of color `c` is the first factor. -/
noncomputable def contr (S : Species k G K basisIdx) (c : Color K) :
    ((S.rep c).tprod (S.rep c.dual)).IntertwiningMap (Representation.trivial k G k) :=
  ⟨(S.basis c).coordPairing (S.basis c.dual), fun g =>
    TensorProduct.ext' fun x y => S.invariant c g x y⟩

/-- The Kronecker delta `∑ μ, e^μ ⊗ e_μ ∈ V c.dual ⊗ V c`, with components `δ_μ^ν`. The factor of
the dual color is first. -/
noncomputable def delta (S : Species k G K basisIdx) (c : Color K) : S.V c.dual ⊗[k] S.V c :=
  (S.basis c.dual).coevaluation (S.basis c)

/-- The bases of a color and its dual are dual, `e^μ(e_ν) = δ^μ_ν`. -/
lemma contr_basis (S : Species k G K basisIdx) (c : Color K) (μ ν : basisIdx c.kind) :
    S.contr c (S.basis c μ ⊗ₜ S.basis c.dual ν) = if μ = ν then 1 else 0 :=
  Module.Basis.coordPairing_basis_basis _ _ _ _

/-- The contraction in components, `S.contr c (u ⊗ α) = ∑ μ, u^μ α_μ`. -/
lemma contr_tmul_eq_sum_basis {S : Species k G K basisIdx} (c : Color K) (x : S.V c)
    (y : S.V c.dual) :
    S.contr c (x ⊗ₜ y) = ∑ μ, (S.basis c).repr x μ * (S.basis c.dual).repr y μ :=
  Module.Basis.coordPairing_tmul _ _ x y

/-- The contraction is symmetric, `u^μ α_μ = α_μ u^μ`. -/
lemma contr_tmul_symm (S : Species k G K basisIdx) (c : Color K) (x : S.V c) (y : S.V c.dual) :
    S.contr c (x ⊗ₜ[k] y) = S.contr c.dual (y ⊗ₜ[k] x) :=
  Module.Basis.coordPairing_comm _ _ _ _

/-- Contracting a basis vector `e_μ` with `α` reads off its component `α_μ`. -/
lemma contr_basis_tmul (S : Species k G K basisIdx) (c : Color K) (μ : basisIdx c.kind)
    (α : S.V c.dual) : S.contr c (S.basis c μ ⊗ₜ α) = (S.basis c.dual).repr α μ := by
  rw [contr_tmul_symm]
  exact Module.Basis.coordPairing_tmul_basis _ _ _ _

/-- The contraction is nondegenerate in its second argument. Two vectors of `c.dual` with the
same contraction against every vector of `c` are equal. -/
lemma ext_contr {S : Species k G K basisIdx} {c : Color K} {α α' : S.V c.dual}
    (h : ∀ u, S.contr c (u ⊗ₜ α) = S.contr c (u ⊗ₜ α')) : α = α' :=
  (S.basis c.dual).repr.injective <| Finsupp.ext fun μ => by
    simpa [contr_basis_tmul] using h (S.basis c μ)

/-- The snake law `u^μ δ_μ^ν = u^ν`: the delta, read as a linear map through the contraction
(`pairingToLinearMap`), is the identity. The vector `u` is contracted with the first factor of
the delta. -/
lemma snake (S : Species k G K basisIdx) (c : Color K) :
    pairingToLinearMap (S.contr c).toLinearMap (S.delta c) = LinearMap.id :=
  Module.Basis.pairingToLinearMap_coordPairing_coevaluation _ _

/-- The invariance `Species.invariant`, from an invariant pairing for which the bases are dual. -/
lemma coordPairing_rep_of_contr {ι M N : Type} [Fintype ι] [DecidableEq ι] [AddCommGroup M]
    [Module k M] [AddCommGroup N] [Module k N] {ρ : Representation k G M}
    {ρ' : Representation k G N} {b : Module.Basis ι k M} {b' : Module.Basis ι k N}
    (p : (ρ.tprod ρ').IntertwiningMap (Representation.trivial k G k))
    (h : ∀ I J, p (b I ⊗ₜ b' J) = if I = J then 1 else 0) (g : G) (x : M) (y : N) :
    b.coordPairing b' (ρ g x ⊗ₜ ρ' g y) = b.coordPairing b' (x ⊗ₜ y) := by
  rw [← b.eq_coordPairing b' p.toLinearMap h]
  simpa using Representation.IntertwiningMap.isIntertwining _ _ p g (x ⊗ₜ y)

/-!

## B. Invariance, symmetry of the delta, and tensors of two factors as linear maps

-/

/-- The contraction is invariant, `(Λu)^μ (Λα)_μ = u^μ α_μ` for every `Λ : G`. -/
lemma contr_invariant (S : Species k G K basisIdx) (c : Color K) (g : G) (x : S.V c)
    (y : S.V c.dual) : S.contr c (S.rep c g x ⊗ₜ[k] S.rep c.dual g y) = S.contr c (x ⊗ₜ[k] y) := by
  change S.contr c ((S.rep c).tprod (S.rep c.dual) g (x ⊗ₜ[k] y)) = _
  rw [(S.contr c).isIntertwining]
  simp

/-- Contracting `u` with `Λα` is contracting `Λ⁻¹u` with `α`. -/
lemma contr_tmul_rep (S : Species k G K basisIdx) (c : Color K) (g : G) (u : S.V c)
    (α : S.V c.dual) : S.contr c (u ⊗ₜ S.rep c.dual g α) = S.contr c (S.rep c g⁻¹ u ⊗ₜ α) := by
  conv_lhs => rw [← Representation.self_inv_apply (S.rep c) g u]
  exact S.contr_invariant c g _ α

/-- A tensor `z ∈ V c.dual ⊗ U` read through the contraction as a linear map `x ↦ z x` from
`V c` to `U` satisfies `((Λ ⊗ f) z)(Λx) = f (z x)` for every `Λ : G` and linear map `f` on `U`.
For `f = Λ` this is the equivariance `(Λz)(Λx) = Λ(z x)`. -/
lemma pairingToLinearMap_contr_map_rep (S : Species k G K basisIdx) (c : Color K) (g : G)
    {U U' : Type} [AddCommGroup U] [Module k U] [AddCommGroup U'] [Module k U'] (f : U →ₗ[k] U')
    (z : S.V c.dual ⊗[k] U) (x : S.V c) :
    pairingToLinearMap (S.contr c).toLinearMap (TensorProduct.map (S.rep c.dual g) f z)
      (S.rep c g x) = f (pairingToLinearMap (S.contr c).toLinearMap z x) := by
  induction z using TensorProduct.inductionOn with
  | tmul w y =>
    simp only [TensorProduct.map_tmul, pairingToLinearMap_tmul, map_smul,
      Representation.IntertwiningMap.toLinearMap_apply, S.contr_invariant]
  | add z z' hz hz' => simp only [map_add, LinearMap.add_apply, hz, hz']

/-- A tensor `z ∈ V c.dual ⊗ U` is recovered from its linear map `x ↦ z x` by applying the map
to the `V c` factor of the delta of `c.dual` with its factors swapped, `z = e^μ ⊗ z(e_μ)`. -/
lemma lTensor_pairingToLinearMap_comm_delta_dual (S : Species k G K basisIdx) (c : Color K)
    {U : Type} [AddCommGroup U] [Module k U] (z : S.V c.dual ⊗[k] U) :
    (pairingToLinearMap (S.contr c).toLinearMap z).lTensor (S.V c.dual)
      (TensorProduct.comm k _ _ (S.delta c.dual)) = z := by
  induction z using TensorProduct.inductionOn with
  | add z₁ z₂ h₁ h₂ => simp only [map_add, LinearMap.lTensor_add, LinearMap.add_apply, h₁, h₂]
  | tmul w y =>
    -- On `w ⊗ y` this is the snake law at `c.dual`, applied to `w`, with `contr_tmul_symm`.
    conv_rhs => rw [← LinearMap.id_apply (R := k) w, ← S.snake c.dual]
    induction S.delta c.dual using TensorProduct.inductionOn with
    | add D₁ D₂ h₁ h₂ => simp only [map_add, LinearMap.add_apply, add_tmul, h₁, h₂]
    | tmul e₁ e₂ =>
      simp only [TensorProduct.comm_tmul, LinearMap.lTensor_tmul, pairingToLinearMap_tmul,
        Representation.IntertwiningMap.toLinearMap_apply, tmul_smul, smul_tmul']
      rw [S.contr_tmul_symm c e₁ w]

/-- The delta of `c` is the delta of `c.dual ∈ V c ⊗ V c.dual` with its factors swapped. -/
lemma delta_eq_comm_delta_dual (S : Species k G K basisIdx) (c : Color K) :
    S.delta c = TensorProduct.comm k _ _ (S.delta c.dual) := by
  simp only [delta, Module.Basis.coevaluation, map_sum, TensorProduct.comm_tmul]

/-- An element `z` of `V a ⊗ U` as the linear map `V a.dual → U` that contracts a vector with the
first factor of `z`, as `v^μ ↦ v^μ g_μν` for `g` in `V a ⊗ V b`. Every linear map arises so. -/
noncomputable def toLin (S : Species k G K basisIdx) {a : Color K} {U : Type} [AddCommGroup U]
    [Module k U] : S.V a ⊗[k] U ≃ₗ[k] (S.V a.dual →ₗ[k] U) :=
  -- The inverse sends `f` to `(id ⊗ f) δ`, by the snake law.
  LinearEquiv.ofLinearMap (pairingToLinearMap (S.contr a.dual).toLinearMap)
    ((LinearMap.lTensorHom (S.V a.dual.dual)).flip (S.delta a.dual))
    (LinearMap.ext fun f => by simp [pairingToLinearMap_lTensor, S.snake])
    (LinearMap.ext fun z => by simpa [S.delta_eq_comm_delta_dual a.dual] using
      S.lTensor_pairingToLinearMap_comm_delta_dual a.dual z)

/-- The delta is invariant, `Λ δ = δ`. -/
lemma delta_invariant (S : Species k G K basisIdx) (c : Color K) (g : G) :
    TensorProduct.map (S.rep c.dual g) (S.rep c g) (S.delta c) = S.delta c := by
  -- Both act as the identity: `(Λδ)(Λx) = Λx` by the snake law.
  apply (S.toLin (a := c.dual)).injective
  change pairingToLinearMap (S.contr c).toLinearMap _ = pairingToLinearMap (S.contr c).toLinearMap _
  ext x
  conv_lhs => rw [← Representation.self_inv_apply (S.rep c) g x]
  rw [S.pairingToLinearMap_contr_map_rep, S.snake c, LinearMap.id_apply, LinearMap.id_apply,
    Representation.self_inv_apply]

/-- The linear map of `Λg` sends `Λv` to `Λ(g v)`, as `(Λg)_μν (Λv)^μ = Λ(g_μν v^μ)`. -/
lemma toLin_map_rep (S : Species k G K basisIdx) {a b : Color K} (g : S.V a ⊗[k] S.V b) (Λ : G)
    (x : S.V a.dual) :
    S.toLin (TensorProduct.map (S.rep a Λ) (S.rep b Λ) g) (S.rep a.dual Λ x) =
      S.rep b Λ (S.toLin g x) :=
  S.pairingToLinearMap_contr_map_rep a.dual Λ (S.rep b Λ) g x

/-- The linear map of `Λg` is bijective when that of `g` is. -/
lemma toLin_map_rep_bijective (S : Species k G K basisIdx) {a b : Color K}
    (g : S.V a ⊗[k] S.V b) (h : Function.Bijective (S.toLin g)) (Λ : G) :
    Function.Bijective (S.toLin (TensorProduct.map (S.rep a Λ) (S.rep b Λ) g)) := by
  -- The map of `Λg` is `Λ ∘ g ∘ Λ⁻¹`, a composite of bijections.
  have e : ⇑(S.toLin (TensorProduct.map (S.rep a Λ) (S.rep b Λ) g)) =
      S.rep b Λ ∘ S.toLin g ∘ S.rep a.dual Λ⁻¹ := by
    funext x
    simp only [Function.comp_apply, ← S.toLin_map_rep, Representation.self_inv_apply]
  rw [e]
  refine (?_ : Function.Bijective (S.rep b Λ)).comp (h.comp ?_)
  · exact ⟨fun x y hxy => by simpa using congrArg (S.rep b Λ⁻¹) hxy,
      fun y => ⟨S.rep b Λ⁻¹ y, Representation.self_inv_apply _ _ _⟩⟩
  · exact ⟨fun x y hxy => by simpa using congrArg (S.rep a.dual Λ) hxy,
      fun y => ⟨S.rep a.dual Λ y, Representation.inv_self_apply _ _ _⟩⟩

/-!

## C. Components of a tensor of two factors read as a linear map

-/

variable {S : Species k G K basisIdx}

/-- A tensor `F = F_μ^ν e^μ ⊗ e_ν` in `V c.dual ⊗ V d`, read through the contraction as a linear
map, sends `v` to `v^μ F_μ^ν e_ν`. -/
lemma basis_repr_pairingToLinearMap_contr (c : Color K) {d : Color K}
    (F : S.V c.dual ⊗[k] S.V d) (v : S.V c) (ν : basisIdx d.kind) :
    (S.basis d).repr (pairingToLinearMap (S.contr c).toLinearMap F v) ν =
      ∑ μ, (S.basis c).repr v μ * ((S.basis c.dual).tensorProduct (S.basis d)).repr F (μ, ν) := by
  induction F using TensorProduct.inductionOn with
  | add x y hx hy =>
    simp only [map_add, LinearMap.add_apply, Finsupp.add_apply, hx, hy, mul_add,
      Finset.sum_add_distrib]
  | tmul x y =>
    rw [pairingToLinearMap_tmul, map_smul, Finsupp.smul_apply, smul_eq_mul]
    change S.contr c (v ⊗ₜ x) * _ = _
    simp only [contr_tmul_eq_sum_basis, Module.Basis.tensorProduct_repr_tmul_apply, smul_eq_mul,
      Finset.sum_mul]
    exact Finset.sum_congr rfl fun _ _ => by ring

/-- `toLin F ∘ₗ toLin F'` is the identity when the matrices of components of `F'` and `F` multiply
to the identity, `F'^μρ F_ρν = δ^μ_ν`. -/
lemma toLin_comp_toLin_of_mul_eq_one {c : Color K} (F : S.V c ⊗[k] S.V c)
    (F' : S.V c.dual ⊗[k] S.V c.dual)
    (h : Matrix.of (fun μ ν => ((S.basis c.dual).tensorProduct (S.basis c.dual)).repr F' (μ, ν)) *
      Matrix.of (fun μ ν => ((S.basis c).tensorProduct (S.basis c)).repr F (μ, ν)) = 1) :
    S.toLin F ∘ₗ S.toLin F' = LinearMap.id := by
  refine (S.basis c).ext fun μ => (S.basis c).repr.injective (Finsupp.ext fun ν => ?_)
  have hμν := congrFun (congrFun h μ) ν
  rw [Matrix.mul_apply, Matrix.one_apply] at hμν
  change (S.basis c).repr (pairingToLinearMap (S.contr c.dual).toLinearMap F
    (pairingToLinearMap (S.contr c).toLinearMap F' (S.basis c μ))) ν = _
  simp only [basis_repr_pairingToLinearMap_contr, Module.Basis.repr_self, Finsupp.single_apply,
    ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true, LinearMap.id_apply]
  exact hμν

/-!

## D. Moving a vector along an equality of colors

-/

variable (S) in
/-- Moving a vector along an equality of colors `a = a'`, Mathlib's `LinearEquiv.cast`. -/
protected abbrev cast {a a' : Color K} (p : a = a') : S.V a ≃ₗ[k] S.V a' :=
  LinearEquiv.cast p

/-- Moving a vector along an equality of colors `a = a'` commutes with the group action. -/
lemma cast_rep {a a' : Color K} (p : a = a') (g : G) (x : S.V a) :
    S.cast p (S.rep a g x) = S.rep a' g (S.cast p x) := by
  subst p
  rfl

/-- Moving a vector along an equality of colors `a = b` keeps its components, with the label cast
back to a label at `a`. -/
lemma basis_repr_cast {a b : Color K} (p : a = b) (v : S.V a) (μ : basisIdx b.kind) :
    (S.basis b).repr (S.cast p v) μ =
      (S.basis a).repr v (cast (congrArg (basisIdx ∘ Color.kind) p.symm) μ) := by
  subst p
  rfl

/-- Moving the vector of a family `f` at the slot `s` depends only on the slot, so it may be read
at any slot `s'` equal to `s`. -/
lemma cast_eq_cast_of_eq {ι : Type} {d : ι → Color K} (f : Π s, S.V (d s)) {s s' : ι}
    (e : s = s') {b : Color K} (p : d s = b) : S.cast p (f s) = S.cast (e ▸ p) (f s') := by
  subst e
  rfl

/-- The contraction of two vectors does not depend on the colors they are moved to. -/
lemma contr_cast_tmul_cast {d e a b : Color K} (x : S.V d) (y : S.V e) (p : d = a)
    (q : e = a.dual) (p' : d = b) (q' : e = b.dual) :
    S.contr a (S.cast p x ⊗ₜ S.cast q y) = S.contr b (S.cast p' x ⊗ₜ S.cast q' y) := by
  subst p p'
  rfl

/-- `contr_tmul_symm` for vectors moved along equalities of colors, `u^μ α_μ = α_μ u^μ`. -/
lemma contr_cast_tmul_cast_symm {d e a b : Color K} (x : S.V d) (y : S.V e) (p : d = a)
    (q : e = a.dual) (p' : e = b) (q' : d = b.dual) :
    S.contr a (S.cast p x ⊗ₜ S.cast q y) = S.contr b (S.cast p' y ⊗ₜ S.cast q' x) := by
  subst p p'
  subst q
  exact S.contr_tmul_symm _ _ _

end Species

end Tensors
