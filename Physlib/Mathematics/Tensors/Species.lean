/-
Copyright (c) 2026 Andrea Pari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrea Pari
-/
module

public import Physlib.Mathematics.ForMathlib.Contraction
public import Physlib.Mathematics.Tensors.Color
public import Mathlib.RepresentationTheory.Intertwining
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
structure, not a field, so that a conjugate species can give conjugate kinds the same labels.

The space of a lower index is data of the species, not `Module.Dual` of the upper one, so that
existing types such as `CoVector d` serve as covectors. The one law of a species (`invariant`) says
that the coordinate pairing `u ⊗ α ↦ ∑ μ, u^μ α_μ` of the bases of `c` and `c.dual` is invariant,
which makes `V c.dual` the dual of `V c` (`dualEquiv`). The law is stated at every color,
so that lemmas about a general color `c` use it directly. At a lower color it is the law at the
upper color with the factors swapped, and `invariant_of_up` proves it so.

The contraction `S.contr c` is this pairing, and the delta `S.delta c` is `∑ μ, e^μ ⊗ e_μ` in
`V c.dual ⊗ V c`. The bases of `c` and `c.dual` are then dual (`contr_basis`) and the contraction
is symmetric (`contr_tmul_symm`). A tensor `z` in `V a ⊗ U` is read as the linear map
`S.toLin z : V a.dual → U` that contracts a vector with the first factor of `z`, and the delta is
then the identity, `u^μ δ_μ^ν = u^ν` (`snake`). Indices name slots, as in abstract index notation,
so `u^μ α_μ` is `S.contr c (u ⊗ α)`.

## ii. Key results

- `Species` is the data and the law of a tensor species, and `Species.invariant_of_up` gives the
  law from its upper colors.
- `Species.contr` is the contraction `u^μ α_μ`, with `Species.contr_basis`,
  `Species.contr_tmul_symm` and `Species.contr_invariant`.
- `Species.contr_tmul_eq_sum_basis` gives the contraction of two vectors in components,
  `Species.contr_basis_tmul` reads off a component, and `Species.ext_contr` proves that the
  contraction is nondegenerate.
- `Species.isPerfPair_contr` : the contraction is a perfect pairing, and `Species.dualEquiv`
  identifies `V c.dual` with the dual representation of `V c`.
- `Species.invariant_of_contr` gives the law `invariant` from an invariant pairing for which the
  bases are dual.
- `Species.delta` is the delta `δ_μ^ν`, with `Species.delta_eq_comm_delta_dual` and
  `Species.delta_invariant`.
- `Species.toLin` identifies `V a ⊗ U` with the linear maps `V a.dual → U`, `Species.snake` proves
  that the delta is the identity, `Species.toLin_map` that `toLin` commutes with the group
  action, `(Λz)(Λv) = Λ(z v)`, and `Species.toLin_lTensor` that `(id ⊗ f) z = f ∘ z`.
- `Species.basis_repr_toLin` gives `toLin` in components, `Species.toMatrix_toLin` its matrix,
  and `Species.toLin_comp_toLin_of_mul_eq_one` proves that two such maps are inverse when their
  matrices are.
- `Species.cast` moves a vector along an equality of colors, `Species.cast_rep` proves that this
  commutes with the group action, and `Species.basis_repr_cast` that it keeps components.
- `Species.contr_cast_tmul_cast` and `Species.contr_cast_tmul_cast_symm` prove that the
  contraction does not depend on the colors its two vectors are moved to.

## iii. Table of contents

- A. Species
- B. The contraction
- C. The delta, and tensors of two factors as linear maps
- D. Moving a vector along an equality of colors

## iv. References

None.

-/

@[expose] public section

open TensorProduct

namespace Tensors

/-!

## A. Species

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

variable {k : Type} [CommRing k] {G : Type} [Group G] {K : Type} {basisIdx : K → Type}
    [∀ κ, Fintype (basisIdx κ)] [∀ κ, DecidableEq (basisIdx κ)]

/-- The law `invariant` at every color from the law at the upper colors. At a lower color the
pairing is the pairing at the dual, upper color with its factors swapped. -/
lemma invariant_of_up {V : Color K → Type} [∀ c, AddCommGroup (V c)] [∀ c, Module k (V c)]
    (rep : (c : Color K) → Representation k G (V c))
    (basis : (c : Color K) → Module.Basis (basisIdx c.kind) k (V c))
    (h : ∀ κ g x y, (basis ⟨κ, .up⟩).coordPairing (basis ⟨κ, .down⟩)
      (rep ⟨κ, .up⟩ g x ⊗ₜ rep ⟨κ, .down⟩ g y) =
        (basis ⟨κ, .up⟩).coordPairing (basis ⟨κ, .down⟩) (x ⊗ₜ y)) :
    ∀ c g x y, (basis c).coordPairing (basis c.dual) (rep c g x ⊗ₜ rep c.dual g y) =
      (basis c).coordPairing (basis c.dual) (x ⊗ₜ y)
  | ⟨κ, .up⟩, g, x, y => h κ g x y
  | ⟨κ, .down⟩, g, x, y => (Module.Basis.coordPairing_comm _ _ _ _).trans <|
      (h κ g y x).trans (Module.Basis.coordPairing_comm _ _ _ _)

/-!

## B. The contraction

-/

variable (S : Species k G K basisIdx)

/-- The invariant contraction `V c ⊗ V c.dual → k`, `u ⊗ α ↦ u^μ α_μ`, the coordinate pairing of
the bases. The vector of color `c` is the first factor. -/
noncomputable def contr (c : Color K) :
    ((S.rep c).tprod (S.rep c.dual)).IntertwiningMap (Representation.trivial k G k) :=
  ⟨(S.basis c).coordPairing (S.basis c.dual), fun g =>
    TensorProduct.ext' fun x y => S.invariant c g x y⟩

/-- The bases of a color and its dual are dual, `e^ν(e_μ) = δ_μ^ν`. -/
lemma contr_basis (c : Color K) (μ ν : basisIdx c.kind) :
    S.contr c (S.basis c μ ⊗ₜ S.basis c.dual ν) = if μ = ν then 1 else 0 :=
  Module.Basis.coordPairing_basis_basis _ _ _ _

variable {S} in
/-- The contraction in components, `S.contr c (u ⊗ α) = ∑ μ, u^μ α_μ`. -/
lemma contr_tmul_eq_sum_basis (c : Color K) (x : S.V c) (y : S.V c.dual) :
    S.contr c (x ⊗ₜ y) = ∑ μ, (S.basis c).repr x μ * (S.basis c.dual).repr y μ :=
  Module.Basis.coordPairing_tmul _ _ x y

/-- The contraction is symmetric, `u^μ α_μ = α_μ u^μ`. -/
lemma contr_tmul_symm (c : Color K) (x : S.V c) (y : S.V c.dual) :
    S.contr c (x ⊗ₜ[k] y) = S.contr c.dual (y ⊗ₜ[k] x) :=
  Module.Basis.coordPairing_comm _ _ _ _

/-- Contracting the basis vector `e_μ` with `α` reads off the component `α_μ`. -/
lemma contr_basis_tmul (c : Color K) (μ : basisIdx c.kind) (α : S.V c.dual) :
    S.contr c (S.basis c μ ⊗ₜ α) = (S.basis c.dual).repr α μ :=
  (S.contr_tmul_symm c _ α).trans (Module.Basis.coordPairing_tmul_basis _ _ _ _)

variable {S} in
/-- The contraction is nondegenerate in its second argument. Two vectors of `c.dual` with the
same contraction against every vector of `c` are equal. -/
lemma ext_contr {c : Color K} {α α' : S.V c.dual}
    (h : ∀ u, S.contr c (u ⊗ₜ α) = S.contr c (u ⊗ₜ α')) : α = α' :=
  (S.basis c.dual).repr.injective <| Finsupp.ext fun μ => by
    simpa [contr_basis_tmul] using h (S.basis c μ)

/-- The contraction is a perfect pairing, so `V c.dual` is the dual of `V c`. -/
instance isPerfPair_contr (c : Color K) :
    (TensorProduct.curry (S.contr c).toLinearMap).IsPerfPair :=
  Module.Basis.isPerfPair_coordPairing _ _

/-- The contraction is invariant, `(Λu)^μ (Λα)_μ = u^μ α_μ` for every `Λ : G`. -/
lemma contr_invariant (c : Color K) (g : G) (x : S.V c) (y : S.V c.dual) :
    S.contr c (S.rep c g x ⊗ₜ[k] S.rep c.dual g y) = S.contr c (x ⊗ₜ[k] y) :=
  S.invariant c g x y

/-- Contracting `u` with `Λα` is contracting `Λ⁻¹u` with `α`. -/
lemma contr_tmul_rep (c : Color K) (g : G) (u : S.V c) (α : S.V c.dual) :
    S.contr c (u ⊗ₜ S.rep c.dual g α) = S.contr c (S.rep c g⁻¹ u ⊗ₜ α) := by
  simpa using S.contr_invariant c g (S.rep c g⁻¹ u) α

/-- The space of `c.dual` is the dual representation of the space of `c`, a vector `α` read as the
linear form `u ↦ u^μ α_μ`. -/
noncomputable def dualEquiv (c : Color K) : (S.rep c.dual).Equiv (S.rep c).dual :=
  .mk (TensorProduct.curry (S.contr c).toLinearMap).flip.toPerfPair fun g =>
    LinearMap.ext fun α => LinearMap.ext fun u => S.contr_tmul_rep c g u α

/-- `dualEquiv c α` is the linear form `u ↦ u^μ α_μ`. -/
@[simp]
lemma dualEquiv_apply (c : Color K) (α : S.V c.dual) (u : S.V c) :
    S.dualEquiv c α u = S.contr c (u ⊗ₜ α) :=
  rfl

omit S in
/-- The law `invariant`, from an invariant pairing `p` for which the bases are dual. It is how a
species is built from a pairing that is known to be invariant. -/
lemma invariant_of_contr {ι M N : Type} [Fintype ι] [DecidableEq ι] [AddCommGroup M]
    [Module k M] [AddCommGroup N] [Module k N] {ρ : Representation k G M}
    {ρ' : Representation k G N} {b : Module.Basis ι k M} {b' : Module.Basis ι k N}
    (p : (ρ.tprod ρ').IntertwiningMap (Representation.trivial k G k))
    (h : ∀ I J, p (b I ⊗ₜ b' J) = if I = J then 1 else 0) (g : G) (x : M) (y : N) :
    b.coordPairing b' (ρ g x ⊗ₜ ρ' g y) = b.coordPairing b' (x ⊗ₜ y) := by
  rw [← b.eq_coordPairing b' p.toLinearMap h]
  simpa using Representation.IntertwiningMap.isIntertwining _ _ p g (x ⊗ₜ y)

/-!

## C. The delta, and tensors of two factors as linear maps

-/

/-- The Kronecker delta `∑ μ, e^μ ⊗ e_μ ∈ V c.dual ⊗ V c`, with components `δ_μ^ν`. The factor of
the dual color is first. -/
noncomputable def delta (c : Color K) : S.V c.dual ⊗[k] S.V c :=
  (S.basis c.dual).coevaluation (S.basis c)

/-- The delta of `c` is the delta of `c.dual ∈ V c ⊗ V c.dual` with its factors swapped. -/
lemma delta_eq_comm_delta_dual (c : Color K) :
    S.delta c = TensorProduct.comm k _ _ (S.delta c.dual) := by
  simp only [delta, Module.Basis.coevaluation, map_sum, TensorProduct.comm_tmul]

/-- An element `z` of `V a ⊗ U` as the linear map `V a.dual → U` that contracts a vector with the
first factor of `z`. For a lower color `a` and `z = g` in `V a ⊗ V a` it is `v^μ ↦ v^μ g_μν`.
Every linear map arises so. -/
noncomputable def toLin {a : Color K} {U : Type} [AddCommGroup U] [Module k U] :
    S.V a ⊗[k] U ≃ₗ[k] (S.V a.dual →ₗ[k] U) :=
  -- The inverse sends `f` to `(id ⊗ f) δ`. Both composites are the identity, by the two halves of
  -- the snake law for dual bases.
  LinearEquiv.ofLinearMap (pairingToLinearMap (S.contr a.dual).toLinearMap)
    ((LinearMap.lTensorHom (S.V a.dual.dual)).flip (S.delta a.dual))
    (LinearMap.ext fun f => by
      simp [pairingToLinearMap_lTensor, delta, contr,
        Module.Basis.pairingToLinearMap_coordPairing_coevaluation])
    (LinearMap.ext fun z => Module.Basis.lTensor_pairingToLinearMap_coevaluation _ _ z)

/-- A pure tensor `x ⊗ y` acts as `v ↦ (v^μ x_μ) y`, contracting `v` with its first factor. -/
@[simp]
lemma toLin_tmul {a : Color K} {U : Type} [AddCommGroup U] [Module k U] (x : S.V a) (y : U)
    (v : S.V a.dual) : S.toLin (x ⊗ₜ y) v = S.contr a.dual (v ⊗ₜ x) • y :=
  rfl

/-- Applying a linear map `f` to the second factor of `z` composes the linear map of `z` with `f`,
`(id ⊗ f) z = f ∘ z`. -/
lemma toLin_lTensor {a : Color K} {U U' : Type} [AddCommGroup U] [Module k U] [AddCommGroup U']
    [Module k U'] (f : U →ₗ[k] U') (z : S.V a ⊗[k] U) :
    S.toLin (f.lTensor (S.V a) z) = f ∘ₗ S.toLin z :=
  pairingToLinearMap_lTensor _ f z

/-- The snake law `u^μ δ_μ^ν = u^ν`, the delta read as a linear map is the identity. -/
lemma snake (c : Color K) : S.toLin (S.delta c) = LinearMap.id :=
  Module.Basis.pairingToLinearMap_coordPairing_coevaluation _ _

/-- `toLin` commutes with the group action, `((Λ ⊗ f) z)(Λx) = f (z x)` for every `Λ : G` and
linear map `f` on `U`. For `f = Λ` this is the equivariance `(Λz)(Λx) = Λ(z x)`. -/
lemma toLin_map (a : Color K) (g : G) {U U' : Type} [AddCommGroup U] [Module k U]
    [AddCommGroup U'] [Module k U'] (f : U →ₗ[k] U') (z : S.V a ⊗[k] U) (x : S.V a.dual) :
    S.toLin (TensorProduct.map (S.rep a g) f z) (S.rep a.dual g x) = f (S.toLin z x) := by
  induction z using TensorProduct.inductionOn with
  | tmul w y => simpa using congrArg (· • f y) (S.contr_invariant a.dual g x w)
  | add z z' hz hz' => simp only [map_add, LinearMap.add_apply, hz, hz']

/-- The delta is invariant, `Λ δ = δ`. -/
lemma delta_invariant (c : Color K) (g : G) :
    TensorProduct.map (S.rep c.dual g) (S.rep c g) (S.delta c) = S.delta c := by
  -- `(Λδ)(Λx) = Λ(δx)` by `toLin_map`, and `δx = x` by `snake`.
  apply S.toLin.injective
  ext x
  simpa [snake] using S.toLin_map c.dual g (S.rep c g) (S.delta c) (S.rep c g⁻¹ x)

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

variable {S}

/-- `toLin` in components, `(z v)^ν = v^μ z_μ^ν` for `z = z_μ^ν e^μ ⊗ e_ν` in `V c ⊗ V d`. -/
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

/-- `toLin F ∘ₗ toLin F'` is the identity when the matrices of components of `F'` and `F` multiply
to the identity, `F'^μρ F_ρν = δ^μ_ν`. -/
lemma toLin_comp_toLin_of_mul_eq_one {c : Color K} (F : S.V c ⊗[k] S.V c)
    (F' : S.V c.dual ⊗[k] S.V c.dual)
    (h : Matrix.of (fun μ ν => ((S.basis c.dual).tensorProduct (S.basis c.dual)).repr F' (μ, ν)) *
      Matrix.of (fun μ ν => ((S.basis c).tensorProduct (S.basis c)).repr F (μ, ν)) = 1) :
    S.toLin F ∘ₗ S.toLin F' = LinearMap.id := by
  apply (LinearMap.toMatrix (S.basis c) (S.basis c)).injective
  rw [LinearMap.toMatrix_comp _ (S.basis c.dual), toMatrix_toLin, toMatrix_toLin c.dual,
    ← Matrix.transpose_mul, h, Matrix.transpose_one, LinearMap.toMatrix_id]

/-!

## D. Moving a vector along an equality of colors

-/

variable (S) in
/-- Moving a vector along an equality of colors `a = a'`, Mathlib's `LinearEquiv.cast`, as an
equivalence of representations. -/
protected def cast {a a' : Color K} (p : a = a') : (S.rep a).Equiv (S.rep a') :=
  .mk (LinearEquiv.cast p) fun _ => by subst p; rfl

/-- `S.cast p` is Mathlib's `cast` of the vector. -/
@[simp]
lemma cast_apply {a a' : Color K} (p : a = a') (x : S.V a) :
    S.cast p x = cast (congrArg S.V p) x := rfl

/-- Moving a vector along an equality of colors `a = a'` commutes with the group action. -/
lemma cast_rep {a a' : Color K} (p : a = a') (g : G) (x : S.V a) :
    S.cast p (S.rep a g x) = S.rep a' g (S.cast p x) :=
  Representation.IntertwiningMap.isIntertwining _ _ (S.cast p).toIntertwiningMap g x

/-- Moving a vector along an equality of colors `a = b` keeps its components, with the label cast
back to a label at `a`. -/
lemma basis_repr_cast {a b : Color K} (p : a = b) (v : S.V a) (μ : basisIdx b.kind) :
    (S.basis b).repr (S.cast p v) μ =
      (S.basis a).repr v (cast (congrArg (basisIdx ∘ Color.kind) p.symm) μ) := by
  subst p
  rfl

/-- Moving the vector of a family `f` at the slot `s` depends only on the slot, so it may be read
at any slot `s'` equal to `s`. -/
lemma cast_apply_congr {ι : Type} {d : ι → Color K} (f : Π s, S.V (d s)) {s s' : ι}
    (e : s = s') {b : Color K} (p : d s = b) : S.cast p (f s) = S.cast (e ▸ p) (f s') := by
  subst e
  rfl

/-- The contraction of two vectors does not depend on the colors they are moved to. -/
lemma contr_cast_tmul_cast {d e a b : Color K} (x : S.V d) (y : S.V e) (p : d = a)
    (q : e = a.dual) (p' : d = b) (q' : e = b.dual) :
    S.contr a (S.cast p x ⊗ₜ S.cast q y) = S.contr b (S.cast p' x ⊗ₜ S.cast q' y) := by
  subst p p'
  rfl

/-- The contraction of two vectors moved along equalities of colors is symmetric,
`u^μ α_μ = α_μ u^μ`. -/
lemma contr_cast_tmul_cast_symm {d e a b : Color K} (x : S.V d) (y : S.V e) (p : d = a)
    (q : e = a.dual) (p' : e = b) (q' : d = b.dual) :
    S.contr a (S.cast p x ⊗ₜ S.cast q y) = S.contr b (S.cast p' y ⊗ₜ S.cast q' x) := by
  subst p p'
  subst q
  exact S.contr_tmul_symm _ _ _

end Species

end Tensors
