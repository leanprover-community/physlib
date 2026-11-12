/-
Copyright (c) 2026 Andrea Pari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrea Pari
-/
module

public import Mathlib.Analysis.RCLike.Basic
public import Physlib.Mathematics.ForMathlib.Contraction
public import Physlib.Mathematics.Tensors.Color
public import Mathlib.RepresentationTheory.Intertwining
/-!

# Tensor species

A species gives each color of index a space, an action of the symmetry group and a basis. Its
tensors are built from these.

## i. Overview

A species `S : Species k G K basisIdx` over `k = ℝ` or `ℂ` (`RCLike k`) gives each color `c` a
`k`-vector space `S.V c`, a representation `S.rep c` of the group `G` on it, and a basis
`S.basis c`. A tensor of `S` with index colors `c₁, …, cₙ` is an element of `V c₁ ⊗ ⋯ ⊗ V cₙ`,
with the action of `G` on each factor.

For real Lorentz tensors in `1 + d` dimensions, `k = ℝ`, `G` is the Lorentz group, and there is
one kind `vec`, whose basis labels are `basisIdx vec = Fin 1 ⊕ Fin d`. The space of `⟨vec, up⟩`
is `Vector d`, the vectors with `1 + d` components, with the action `v^μ ↦ Λ^μ_ν v^ν` and the
standard basis `e_μ`. The space of `⟨vec, down⟩` is `CoVector d`, also with `1 + d` components,
with the action `w_μ ↦ w_ν (Λ⁻¹)^ν_μ` and the dual basis `e^μ`.

Each lower space is given by the species, not built as `Module.Dual` of the upper space, so that
a covector is an element of `CoVector d` itself rather than a linear form on `Vector d`. The bases
fix the contraction, which identifies `V c.dual` with the dual space of `V c`, and the condition on
the species makes this identification respect the group action:

- The contraction `S.contr c : V c ⊗ V c.dual → k` multiplies the components of its two arguments
  in the bases of `c` and `c.dual` and adds them up, `S.contr c (u ⊗ α) = ∑ μ, u^μ α_μ`. A basis
  vector has one component equal to `1` and the others `0`, so `S.contr c (e_μ ⊗ e^ν) = δ_μ^ν` and
  the two bases are dual. Every linear form on `V c` is `u ↦ u^μ α_μ` for exactly one `α`, with
  `α_μ` its value on `e_μ`, so the contraction identifies `V c.dual` with the dual space of `V c`
  (`isPerfPair_contr`).
- The condition on a species (`invariant`) says that the contraction is invariant,
  `(Λu)^μ (Λα)_μ = u^μ α_μ` for every `Λ : G`. Equivalently `u^μ (Λα)_μ = (Λ⁻¹u)^μ α_μ`
  (`contr_tmul_rep`), which is how `G` acts on linear forms on `V c`. So the identification
  respects the action, and `V c.dual` is the dual representation of `V c` (`dualEquiv`).

A repeated index is contracted, so `u^μ α_μ` is `S.contr c (u ⊗ α)`.

## ii. Key results

- `Species` : the data of a tensor species and the condition on it, and
  `Species.invariant_of_up` : the condition from the upper colors alone.
- `Species.contr` : the contraction `u^μ α_μ`, with `Species.contr_tmul_eq_sum_basis` : its
  formula in components, `Species.contr_basis` : the bases are dual, `Species.contr_tmul_symm` :
  it is symmetric, and `Species.contr_invariant` : it is invariant.
- `Species.isPerfPair_contr` : the contraction is a perfect pairing, `Species.ext_contr` : a
  vector of `V c.dual` is determined by its contractions, and `Species.dualEquiv` : `V c.dual` is
  the dual representation of `V c`.
- `Species.cast` : a vector moved along an equality of colors, with `Species.cast_rep`,
  `Species.basis_repr_cast`, `Species.contr_cast_tmul_cast` and
  `Species.contr_cast_tmul_cast_symm` : this keeps the action, the components and the
  contraction.

## iii. Table of contents

- A. Species
- B. The contraction
- C. Moving a vector along an equality of colors

## iv. References

There are no known references for the material in this module.

-/

@[expose] public section

open TensorProduct

namespace Tensor

/-!

## A. Species

The basis of a color `c` is labelled by `basisIdx c.kind`, the values that an index of that kind
runs over. A color and its dual share labels, as `μ` in `v^μ` and `α_μ`. `basisIdx` is a
parameter of `Species`.

The condition is stated at every color, so that lemmas about a general color `c` use it directly.
At a lower color it is the condition at the upper color with the factors swapped, and
`invariant_of_up` proves it from the upper colors.

-/

/-- A tensor species gives each color `c` a space `V c`, a representation `rep c` of `G` on it and
a basis `basis c` labelled by `basisIdx c.kind`, so that a color and its dual share labels. Its one
condition, `invariant`, says that the coordinate pairing `u ⊗ α ↦ ∑ μ, u^μ α_μ` of the bases of
`c` and `c.dual` is invariant. -/
structure Species (k : Type) [RCLike k] (G : Type) [Group G] (K : Type)
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

variable {k : Type} [RCLike k] {G : Type} [Group G] {K : Type} {basisIdx : K → Type}
    [∀ κ, Fintype (basisIdx κ)] [∀ κ, DecidableEq (basisIdx κ)]

/-- The condition `invariant` at every color from the condition at the upper colors. At a lower
color the pairing is the pairing at the dual, upper color with its factors swapped. -/
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

/-- The space of each color is finite-dimensional, since it has a finite basis. -/
instance finiteDimensional (S : Species k G K basisIdx) (c : Color K) :
    FiniteDimensional k (S.V c) :=
  Module.Finite.of_basis (S.basis c)

/-!

## B. The contraction

The contraction is not a field of `Species`. It is defined from the bases, as
`u ⊗ α ↦ ∑ μ, u^μ α_μ`, so the bases of `c` and `c.dual` are dual by definition
(`contr_basis`). Its invariance is the condition on the species. It is a perfect pairing in
Mathlib's sense, and `dualEquiv` identifies `V c.dual` with Mathlib's dual representation of
`V c`, so Mathlib's results on duals apply. When an invariant pairing for which the bases are
dual is already known, `Module.Basis.coordPairing_invariant` gives the condition.

-/

variable (S : Species k G K basisIdx)

/-- The invariant contraction `V c ⊗ V c.dual → k`, `u ⊗ α ↦ u^μ α_μ`, the coordinate pairing of
the bases. The vector of color `c` is the first factor. -/
noncomputable def contr (c : Color K) :
    ((S.rep c).tprod (S.rep c.dual)).IntertwiningMap (Representation.trivial k G k) :=
  ⟨(S.basis c).coordPairing (S.basis c.dual), fun g =>
    TensorProduct.ext' fun x y => S.invariant c g x y⟩

/-- The bases of a color and its dual are dual, `S.contr c (e_μ ⊗ e^ν) = δ_μ^ν`. -/
lemma contr_basis (c : Color K) (μ ν : basisIdx c.kind) :
    S.contr c (S.basis c μ ⊗ₜ S.basis c.dual ν) = if μ = ν then 1 else 0 :=
  Module.Basis.coordPairing_basis_basis _ _ _ _

variable {S} in
/-- The contraction in components, `S.contr c (u ⊗ α) = ∑ μ, u^μ α_μ`. -/
lemma contr_tmul_eq_sum_basis (c : Color K) (x : S.V c) (y : S.V c.dual) :
    S.contr c (x ⊗ₜ y) = ∑ μ, (S.basis c).repr x μ * (S.basis c.dual).repr y μ :=
  Module.Basis.coordPairing_tmul _ _ x y

/-- The contraction is symmetric. `u^μ α_μ` at `c` is `α_μ u^μ` at `c.dual`, with the factors
swapped. -/
lemma contr_tmul_symm (c : Color K) (x : S.V c) (y : S.V c.dual) :
    S.contr c (x ⊗ₜ[k] y) = S.contr c.dual (y ⊗ₜ[k] x) :=
  Module.Basis.coordPairing_comm _ _ _ _

/-- The contraction is a perfect pairing, so it identifies `V c.dual` with the dual of `V c`. -/
instance isPerfPair_contr (c : Color K) :
    (TensorProduct.curry (S.contr c).toLinearMap).IsPerfPair :=
  Module.Basis.isPerfPair_coordPairing _ _

variable {S} in
/-- The contraction is nondegenerate in its second argument. Two vectors of `c.dual` with the
same contraction against every vector of `c` are equal. -/
lemma ext_contr {c : Color K} {α α' : S.V c.dual}
    (h : ∀ u, S.contr c (u ⊗ₜ α) = S.contr c (u ⊗ₜ α')) : α = α' :=
  (LinearMap.IsPerfPair.bijective_right
    (p := TensorProduct.curry (S.contr c).toLinearMap)).injective (LinearMap.ext h)

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

variable {S}

/-!

## C. Moving a vector along an equality of colors

When two colors are equal by computation, as `c.dual.dual` and `c`, their spaces are the same
type. When they are equal only through a proof `p : a = a'`, Lean cannot use a vector of `S.V a`
where one of `S.V a'` is expected. This happens for a hypothesis such as `c i = a`, and for the
colors `c s` and `c s'` of two indices with `s = s'`. `S.cast p` moves the vector from `S.V a` to
`S.V a'` without changing it. The lemmas below say that `S.cast` keeps the group action, the
components and the contraction, so that proofs can remove it.

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

/-- For a family `f` of vectors on indices, moving `f s` to the color `b` is moving `f s'`, for
any index `s'` equal to `s`. -/
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

end Tensor
