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

The space of a lower index is data of the species, not `Module.Dual` of the upper one, so that
existing types such as `CoVector d` serve as covectors. The coordinate pairing
`u ⊗ α ↦ ∑ μ, u^μ α_μ` of the bases of `c` and `c.dual` makes `V c.dual` the dual of `V c`. The
one law of a species (`invariant`) says that this pairing is invariant, which makes `V c.dual` the
dual representation (`dualEquiv`).

The contraction `S.contr c` is this pairing. The bases of `c` and `c.dual` are then dual
(`contr_basis`) and the contraction is symmetric (`contr_tmul_symm`). A repeated index is
contracted, so `u^μ α_μ` is `S.contr c (u ⊗ α) = ∑ μ, u^μ α_μ` (`contr_tmul_eq_sum_basis`).

## ii. Key results

- `Species` is the data and the law of a tensor species, and `Species.invariant_of_up` gives the
  law from its upper colors.
- `Species.contr` is the contraction `u^μ α_μ`, with `Species.contr_basis`,
  `Species.contr_tmul_symm` and `Species.contr_invariant`.
- `Species.contr_tmul_eq_sum_basis` gives the contraction of two vectors in components, and
  `Species.ext_contr` proves that the contraction is nondegenerate.
- `Species.isPerfPair_contr` : the contraction is a perfect pairing, and `Species.dualEquiv`
  identifies `V c.dual` with the dual representation of `V c`.
- `Species.invariant_of_contr` gives the law `invariant` from an invariant pairing for which the
  bases are dual.
- `Species.cast` moves a vector along an equality of colors, `Species.cast_rep` proves that this
  commutes with the group action, and `Species.basis_repr_cast` that it keeps components.
- `Species.contr_cast_tmul_cast` and `Species.contr_cast_tmul_cast_symm` prove that the
  contraction does not depend on the colors its two vectors are moved to.

## iii. Table of contents

- A. Species
- B. The contraction
- C. Moving a vector along an equality of colors

## iv. References

There are no known references for the material in this module.

-/

@[expose] public section

open TensorProduct

namespace Tensors

/-!

## A. Species

The basis of a color `c` is labelled by `basisIdx c.kind`, the values that an index of that kind
runs over, as `Fin 1 ⊕ Fin d` for a Lorentz index. A color and its dual share labels, as `μ` in
`v^μ` and `α_μ`. `basisIdx` is a parameter, not a field, so that a conjugate species can give
conjugate kinds the same labels. The law is stated at every color, so that lemmas about a general
color `c` use it directly. `invariant_of_up` proves it from the upper colors.

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

The contraction is not a field of `Species`. It is defined from the bases, as their coordinate
pairing. The bases of `c` and `c.dual` are then dual by construction, and components need no
dual-basis matching. Its invariance is the law of the species. `dualEquiv` identifies `V c.dual`
with Mathlib's dual representation of `V c`, and `invariant_of_contr` builds the law from a pairing
known to be invariant.

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

variable {S} in
/-- The contraction is nondegenerate in its second argument. Two vectors of `c.dual` with the
same contraction against every vector of `c` are equal. -/
lemma ext_contr {c : Color K} {α α' : S.V c.dual}
    (h : ∀ u, S.contr c (u ⊗ₜ α) = S.contr c (u ⊗ₜ α')) : α = α' :=
  (S.dualEquiv c).toLinearEquiv.injective (LinearMap.ext h)

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

variable {S}

/-!

## C. Moving a vector along an equality of colors

A relabeling of slots matches colors only through a proof, `c (σ.symm j) = c' j`, not by
definition. A vector of one color is then read at an equal color through `S.cast`. The lemmas say
that this keeps the group action, the components and the contraction.

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
