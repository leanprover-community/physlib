/-
Copyright (c) 2026 Andrea Pari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrea Pari
-/
module

public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.LinearAlgebra.Matrix.Dual
public import Mathlib.LinearAlgebra.PerfectPairing.Basic
public import Physlib.Mathematics.ForMathlib.Representation
public import Physlib.Mathematics.Tensors.Color
/-!

# Tensor species

A species gives each kind of index a vector space and an action of the symmetry group. Its
tensors are built from these.

## i. Overview

A species associates the color of each index with a vector space and a representation of the
group on it. A color (`Color.lean`) is the label of an index. It gives the kind of the index and
whether it is up or down, and nothing else.

A species `S : Species k G K` over `k = ℝ` or `ℂ` (`RCLike k`) gives each kind `κ : K` of index a
finite-dimensional `k`-vector space `S.W κ` and a representation `S.repW κ` of the group `G` on it.
These are the vector space and the action of an upper index. From them each color `c` gets a
vector space `S.V c` and a representation `S.rep c`. A tensor of `S` with index colors
`c₁, …, cₙ` is an element of `V c₁ ⊗ ⋯ ⊗ V cₙ`, with the action of `G` on each factor.

So the colors and the species answer different questions. Two indices can be contracted when the
color of one is the dual of the color of the other. What the contraction is, and how a tensor
transforms, come from the species.

For real Lorentz tensors in `1 + d` dimensions there is one kind `vec`. The colors are
`⟨vec, up⟩` for the index of `v^μ` and `⟨vec, down⟩` for the index of `α_μ`, and they say that
the two indices of `v^μ α_μ` can be contracted. The species has `k = ℝ`, `G` the Lorentz group,
and `W vec` the vector space of the `v^μ`, with `1 + d` components and the action
`v^μ ↦ Λ^μ_ν v^ν` of a Lorentz transformation `Λ`. It says that `v^μ α_μ` is a number and that
it does not change under `Λ`.

The vector space of a color is built from that of its kind (A). The vector space of `⟨κ, up⟩`
is `S.W κ`. The vector space of `⟨κ, down⟩` is Mathlib's dual space `Module.Dual k (S.W κ)`,
with the dual representation. So a covector `α_μ` is a linear form on vectors, with the action
`α_μ ↦ α_ν (Λ⁻¹)^ν_μ`. A vector and a covector have different types, and Lean rejects one where
the other is expected. Vectors of two kinds have different types only when the species gives the
kinds different vector spaces.

The contraction `u^μ α_μ` of an upper and a lower index (B) is the covector applied to the
vector. It is invariant, `(Λu)^μ (Λα)_μ = u^μ α_μ`, because `G` acts on linear forms by the dual
representation. When two colors are equal only through a proof, `S.cast` moves a vector of one to
the other (C), keeping the action and the contraction.

A basis is a choice on top of a species, the class `S.HasBasis basisIdx` (D). It is needed only
for components. For Lorentz vectors it is the standard basis `e_μ`, labelled by
`basisIdx vec = Fin 1 ⊕ Fin d`. The basis of a lower color is the dual basis `e^μ`, so
`S.contr c (e_μ ⊗ e^ν) = δ_μ^ν` and the contraction is the sum `∑ μ, u^μ α_μ`.

## ii. Key results

- `Species` : the vector spaces and representations of the kinds of a species.
- `Species.V`, `Species.rep` : the vector space and the representation of a color.
- `Species.contr` : the contraction `u^μ α_μ`, with `Species.contr_invariant` : it is invariant,
  `Species.isPerfPair_contr` : it is a perfect pairing, and `Species.dualEquiv` : the
  representation of `c.dual` is equivalent to the dual of the representation of `c`.
- `Species.cast` : a vector moved along an equality of colors.
- `Species.HasBasis`, `Species.basis` : a basis of each kind, and the basis of a color, with
  `Species.contr_basis` : the bases of `c` and `c.dual` are dual, and
  `Species.contr_tmul_eq_sum_basis` : the contraction in components.

## iii. Table of contents

- A. Species
  - A.1. The vector space of a color
- B. The contraction
- C. Moving a vector along an equality of colors
- D. Bases

## iv. References

There are no known references for the material in this module.

-/

@[expose] public section

open TensorProduct

namespace Tensor

/-!

## A. Species

-/

/-- A tensor species gives each kind `κ` of index a finite-dimensional vector space `W κ` and a
representation `repW κ` of `G` on it. These are the vector space and the action of an upper
index. -/
structure Species (k : Type) [RCLike k] (G : Type) [Group G] (K : Type) where
  /-- The vector space of an upper index of the kind `κ`. -/
  W : K → Type
  /-- The vector spaces are additive groups. -/
  [addCommGroup : ∀ κ, AddCommGroup (W κ)]
  /-- The vector spaces are modules over `k`. -/
  [module : ∀ κ, Module k (W κ)]
  /-- The vector spaces are finite-dimensional. -/
  [finite : ∀ κ, Module.Finite k (W κ)]
  /-- The representation at an upper index of the kind `κ`. -/
  repW : (κ : K) → Representation k G (W κ)

attribute [instance] Species.addCommGroup Species.module Species.finite

namespace Species

variable {k : Type} [RCLike k] {G : Type} [Group G] {K : Type}

variable (S : Species k G K)

/-!

### A.1. The vector space of a color

`V` is reducible, so instance search and unification see `S.V ⟨κ, down⟩` as
`Module.Dual k (S.W κ)`, and Mathlib's lemmas on linear forms apply.

This has a cost for `simp`. A color is written out when its variance is visible, as `⟨vec, up⟩`
and `⟨vec, down⟩` in `T^μ_ν`. At a written-out color `simp` computes `S.V ⟨κ, up⟩` to `S.W κ` in
the goal, but it files each lemma with `S.V` not computed. At a variable color `c` nothing can be
computed, and lemma and goal agree.

So a `simp` lemma that applies a map between vector spaces `S.V c`, such as `S.contr c` or
`S.dualEquiv c`, misses goals at written-out colors, whether it is stated at a written-out color or
for a variable `c`.

The solution we use is to file such a lemma without the parts where the two differ. The lemma
marks the type of the map, its domain and its argument `no_index`, so `simp` files it under the map
alone and finds it at every color. `simp` then checks that the lemma applies with `S.V` computed.
`contr_up_tmul` does this for `u^μ α_μ = α(u)`.

-/

-- `@[reducible] def`, not `abbrev`. To compare `S.V a` with `S.V b`, Lean then compares the colors
-- `a` and `b` first, and unfolds `V` only if that fails. With `abbrev` it unfolds `V` on both sides
-- first, which is slower for equal colors written differently, as `c.dual.dual` and `c`.
/-- The vector space of a color, `S.W κ` at `⟨κ, up⟩` and its dual `Module.Dual k (S.W κ)` at
`⟨κ, down⟩`. -/
@[reducible] def V : Color K → Type
  | ⟨κ, .up⟩ => S.W κ
  | ⟨κ, .down⟩ => Module.Dual k (S.W κ)

/-- The vector space of each color is an additive commutative group. -/
instance instAddCommGroupV : ∀ c, AddCommGroup (S.V c)
  | ⟨κ, .up⟩ => inferInstanceAs (AddCommGroup (S.W κ))
  | ⟨κ, .down⟩ => inferInstanceAs (AddCommGroup (Module.Dual k (S.W κ)))

/-- The vector space of each color is a module over `k`. -/
instance instModuleV : ∀ c, Module k (S.V c)
  | ⟨κ, .up⟩ => inferInstanceAs (Module k (S.W κ))
  | ⟨κ, .down⟩ => inferInstanceAs (Module k (Module.Dual k (S.W κ)))

/-- The vector space of each color is finite-dimensional. -/
instance instFiniteV : ∀ c, Module.Finite k (S.V c)
  | ⟨κ, .up⟩ => inferInstanceAs (Module.Finite k (S.W κ))
  | ⟨κ, .down⟩ => inferInstanceAs (Module.Finite k (Module.Dual k (S.W κ)))

/-- The representation of a color, `repW κ` at `⟨κ, up⟩` and the dual representation
`(repW κ).dual` at `⟨κ, down⟩`, `α ↦ α ∘ Λ⁻¹`. -/
noncomputable def rep : (c : Color K) → Representation k G (S.V c)
  | ⟨κ, .up⟩ => S.repW κ
  | ⟨κ, .down⟩ => (S.repW κ).dual

/-- The representation of an upper color is `repW κ`. -/
lemma rep_up (κ : K) : S.rep ⟨κ, .up⟩ = S.repW κ := rfl

/-- The representation of a lower color is the dual representation `(repW κ).dual`. -/
lemma rep_down (κ : K) : S.rep ⟨κ, .down⟩ = (S.repW κ).dual := rfl

/-!

## B. The contraction

-/

/-- The contraction `V c ⊗ V c.dual → k` of a vector and a covector, Mathlib's evaluation of the
linear form on the vector, as a map of representations to the trivial one. The first factor has the
color `c`. At `⟨κ, up⟩` it is `u ⊗ α ↦ α u` (`Representation.contractRight`), at `⟨κ, down⟩`
it is `α ⊗ u ↦ α u` (`Representation.contractLeft`). For Lorentz vectors this is `u^μ α_μ`. -/
noncomputable def contr : (c : Color K) →
    ((S.rep c).tprod (S.rep c.dual)).IntertwiningMap (Representation.trivial k G k)
  | ⟨κ, .up⟩ => (S.repW κ).contractRight
  | ⟨κ, .down⟩ => (S.repW κ).contractLeft

/-- At an upper color the contraction evaluates the covector on the vector, `u ⊗ α ↦ α u`. -/
@[simp]
lemma contr_up_tmul (κ : K) (x : S.V ⟨κ, .up⟩) (y : S.V ⟨κ, .down⟩) :
    @DFunLike.coe (no_index _) (no_index _) _ _ (S.contr ⟨κ, .up⟩)
      (no_index (x ⊗ₜ y)) = y x := rfl

/-- At a lower color the contraction evaluates the covector on the vector, `α ⊗ u ↦ α u`. -/
@[simp]
lemma contr_down_tmul (κ : K) (x : S.V ⟨κ, .down⟩) (y : S.V ⟨κ, .up⟩) :
    @DFunLike.coe (no_index _) (no_index _) _ _ (S.contr ⟨κ, .down⟩)
      (no_index (x ⊗ₜ y)) = x y := rfl

/-- The contraction is symmetric. `u^μ α_μ` at `c` is `α_μ u^μ` at `c.dual`, with the factors
swapped. -/
lemma contr_tmul_symm : ∀ (c : Color K) (x : S.V c) (y : S.V c.dual),
    S.contr c (x ⊗ₜ[k] y) = S.contr c.dual (y ⊗ₜ[k] x)
  | ⟨_, .up⟩, _, _ => rfl
  | ⟨_, .down⟩, _, _ => rfl

/-- The contraction is a perfect pairing, so it identifies `V c.dual` with the dual of `V c`. -/
instance isPerfPair_contr : ∀ c : Color K,
    (TensorProduct.curry (S.contr c).toLinearMap).IsPerfPair
  | ⟨_, .up⟩ => LinearMap.IsPerfPair.dualEval
  | ⟨_, .down⟩ => LinearMap.IsPerfPair.id

/-- The contraction is invariant, `(Λu)^μ (Λα)_μ = u^μ α_μ` for every `Λ : G`. -/
lemma contr_invariant (c : Color K) (g : G) (x : S.V c) (y : S.V c.dual) :
    S.contr c (S.rep c g x ⊗ₜ[k] S.rep c.dual g y) = S.contr c (x ⊗ₜ[k] y) :=
  Representation.IntertwiningMap.isIntertwining _ _ (S.contr c) g (x ⊗ₜ y)

/-- Contracting `u` with `Λα` is contracting `Λ⁻¹u` with `α`. -/
lemma contr_tmul_rep (c : Color K) (g : G) (u : S.V c) (α : S.V c.dual) :
    S.contr c (u ⊗ₜ S.rep c.dual g α) = S.contr c (S.rep c g⁻¹ u ⊗ₜ α) := by
  simpa using S.contr_invariant c g (S.rep c g⁻¹ u) α

/-- The representation of `c.dual` is equivalent to the dual of the representation of `c`, a
vector `α` read as the linear form `u ↦ u^μ α_μ`. -/
noncomputable def dualEquiv (c : Color K) : (S.rep c.dual).Equiv (S.rep c).dual :=
  .mk (TensorProduct.curry (S.contr c).toLinearMap).flip.toPerfPair fun g =>
    LinearMap.ext fun α => LinearMap.ext fun u => S.contr_tmul_rep c g u α

/-- `dualEquiv c α` is the linear form `u ↦ u^μ α_μ`. -/
@[simp]
lemma dualEquiv_apply (c : Color K) (α : S.V c.dual) (u : S.V c) :
    @DFunLike.coe (no_index _) (no_index _) _ _
      (@DFunLike.coe (no_index _) (no_index _) _ _ (S.dualEquiv c) α) u =
        S.contr c (u ⊗ₜ α) :=
  rfl

variable {S}

/-- The contraction is nondegenerate in its second argument. Two vectors of `c.dual` with the
same contraction against every vector of `c` are equal. -/
lemma ext_contr {c : Color K} {α α' : S.V c.dual}
    (h : ∀ u, S.contr c (u ⊗ₜ α) = S.contr c (u ⊗ₜ α')) : α = α' :=
  (S.dualEquiv c).injective (LinearMap.ext h)

/-!

## C. Moving a vector along an equality of colors

When two colors are equal by computation, as `c.dual.dual` and `c`, their vector spaces are the
same type. When they are equal only through a proof `p : a = a'`, Lean cannot use a vector of
`S.V a` where one of `S.V a'` is expected. This happens for a hypothesis such as `c i = a`, and
for the colors `c s` and `c s'` of two indices with `s = s'`. `S.cast p` moves the vector from
`S.V a` to `S.V a'` without changing it. It is an equivalence of representations, so it keeps the
group action. The lemmas below say that it keeps the contraction, so that proofs can remove it.

-/

variable (S) in
/-- Moving a vector along an equality of colors `a = a'`, `Representation.Equiv.cast` of the
representations of the colors. -/
protected noncomputable abbrev cast {a a' : Color K} (p : a = a') : (S.rep a).Equiv (S.rep a') :=
  Representation.Equiv.cast S.rep p

/-- For a family `f` of vectors on indices, moving `f s` to the color `b` is moving `f s'`, for
any index `s'` equal to `s`. -/
lemma cast_apply_congr {ι : Type} {d : ι → Color K} (f : Π s, S.V (d s)) {s s' : ι}
    (e : s = s') {b : Color K} (p : d s = b) :
    S.cast p (f s) = S.cast (a := d s') (a' := b) (e ▸ p) (f s') := by
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
  subst p p' q
  exact S.contr_tmul_symm _ _ _

/-!

## D. Bases

A basis is an optional layer on a species, the class `S.HasBasis basisIdx`. The basis of a kind `κ`
is labelled by `basisIdx κ`, the values that an index of that kind runs over, such as
`Fin 1 ⊕ Fin d` for a Lorentz index. A color and its dual share labels, as `μ` in `v^μ` and `α_μ`.
`basisIdx` is an `outParam`, so the labels are found from the species. A statement about
components takes `[S.HasBasis basisIdx]` as a hypothesis. The labels of a kind are finitely many
(`Finite`). A statement with a sum over the labels or with a matrix also takes their list
(`Fintype`).

-/

/-- A choice of basis of `S.W κ` for every kind `κ`, labelled by `basisIdx κ`. -/
class HasBasis (S : Species k G K) (basisIdx : outParam (K → Type)) where
  /-- The basis of the vector space of an upper index of the kind `κ`. -/
  basisW : (κ : K) → Module.Basis (basisIdx κ) k (S.W κ)

variable (S) {basisIdx : K → Type} [S.HasBasis basisIdx]

/-- The chosen basis `e_μ` of `S.W κ`. -/
noncomputable abbrev basisW (κ : K) : Module.Basis (basisIdx κ) k (S.W κ) := HasBasis.basisW κ

section Finite

variable [∀ κ, Finite (basisIdx κ)] [∀ κ, DecidableEq (basisIdx κ)]

/-- The basis of a color, `e_μ = basisW κ` at `⟨κ, up⟩` and its dual basis `e^μ` at
`⟨κ, down⟩`. -/
noncomputable def basis : (c : Color K) → Module.Basis (basisIdx c.kind) k (S.V c)
  | ⟨κ, .up⟩ => S.basisW κ
  | ⟨κ, .down⟩ => (S.basisW κ).dualBasis

/-- The basis of an upper color is `basisW κ`. -/
@[simp] lemma basis_up (κ : K) : S.basis ⟨κ, .up⟩ = S.basisW κ := rfl

/-- The basis of a lower color is the dual basis of `basisW κ`. -/
@[simp] lemma basis_down (κ : K) : S.basis ⟨κ, .down⟩ = (S.basisW κ).dualBasis := rfl

/-- The components at an upper color are those in `basisW κ`. It applies before `basis_up`, so
that the result has the types `S.W κ` and Mathlib's lemmas on the basis of `S.W κ` fire. -/
@[simp↓] lemma basis_up_repr (κ : K) (v : S.V ⟨κ, .up⟩) :
    @DFunLike.coe (no_index _) (no_index _) _ _ (S.basis ⟨κ, .up⟩).repr v =
      (S.basisW κ).repr v := rfl

/-- The bases of a color and its dual are dual, `S.contr c (e_μ ⊗ e^ν) = δ_μ^ν`. -/
lemma contr_basis : ∀ (c : Color K) (μ ν : basisIdx c.kind),
    S.contr c (S.basis c μ ⊗ₜ S.basis c.dual ν) = if μ = ν then 1 else 0
  | ⟨κ, .up⟩, μ, ν => by simp [Color.dual_mk, Variance.dual_up, Finsupp.single_apply]
  | ⟨κ, .down⟩, μ, ν => by simp [Color.dual_mk, Variance.dual_down, Finsupp.single_apply, eq_comm]

variable {S} in
/-- Moving a vector along an equality of colors `a = b` keeps its components, with the label cast
back to a label at `a`. -/
lemma basis_repr_cast {a b : Color K} (p : a = b) (v : S.V a) (μ : basisIdx b.kind) :
    (S.basis b).repr (S.cast p v) μ =
      (S.basis a).repr v (cast (congrArg (basisIdx ∘ Color.kind) p.symm) μ) := by
  subst p
  rfl

end Finite

variable [∀ κ, Fintype (basisIdx κ)] [∀ κ, DecidableEq (basisIdx κ)]

/-- The matrix of `Λ` at a lower color is the transpose of the matrix of `Λ⁻¹` at the upper
color, `α_μ ↦ α_ν (Λ⁻¹)^ν_μ`. -/
lemma toMatrix_rep_down (κ : K) (g : G) :
    LinearMap.toMatrix (S.basis ⟨κ, .down⟩) (S.basis ⟨κ, .down⟩) (S.rep ⟨κ, .down⟩ g) =
      (LinearMap.toMatrix (S.basis ⟨κ, .up⟩) (S.basis ⟨κ, .up⟩) (S.rep ⟨κ, .up⟩ g⁻¹)).transpose :=
  LinearMap.toMatrix_transpose (B₁ := S.basis ⟨κ, .up⟩) (B₂ := S.basis ⟨κ, .up⟩) _

variable {S} in
/-- The contraction in components, `S.contr c (u ⊗ α) = ∑ μ, u^μ α_μ`. -/
lemma contr_tmul_eq_sum_basis (c : Color K) (x : S.V c) (y : S.V c.dual) :
    S.contr c (x ⊗ₜ y) = ∑ μ, (S.basis c).repr x μ * (S.basis c.dual).repr y μ := by
  conv_lhs => rw [← (S.basis c).sum_repr x, ← (S.basis c.dual).sum_repr y]
  simp only [sum_tmul, tmul_sum, smul_tmul_smul, map_sum, map_smul, contr_basis, smul_eq_mul,
    mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]

end Species

end Tensor
