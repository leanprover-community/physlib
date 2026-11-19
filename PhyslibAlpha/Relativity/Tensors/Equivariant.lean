/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jinzheng Li, Nathaneal Sajan, Joseph Tooby-Smith
-/
module

public import Physlib.Relativity.Tensors.Basic
public import Physlib.Relativity.Tensors.Constructors
public import PhyslibAlpha.Mathematics.RepresentationTheory.Invariants
public import PhyslibAlpha.Mathematics.InvariantReduction
/-!
# Equivariant maps out of the tensors of a species

Families of vectors carrying tensor indices, and how their invariants come from invariant tensors.

## i. Overview

A family of vectors in a representation `ρ` of the group `G` of a tensor species `S`, carrying
indices of colors `c`, is packaged as a linear map `f : S.Tensor c →ₗ[k] B`, and
`S.IsEquivariant c ρ f` says that `f` intertwines the action of `G` on tensors with `ρ` (A).

Over `ℂ`, the invariants in the range of such a map come from invariant tensors (C): every
invariant of `LinearMap.range f ⊔ W`, for `W` a `G`-stable submodule, is `f t + y` with `t` an
invariant tensor and `y ∈ W`. This holds whenever the colors are closed under adjoints (B): for
every `g` some `g'` acts on each color by the conjugate transpose of the matrix of `g`. The
classification of the invariants in the range of `f` is thereby reduced to that of the invariant
tensors of `S.Tensor c`, `IsEquivariant.invariantReductionToSpan`.

A map is specified by its values on the basis tensors with `Basis.constr`, and
`isEquivariant_constr` turns a transformation law of those values into equivariance (D). With
the component indices relabelled by `e`, the map of a family `T` is `familyMap e T`, and it is
equivariant exactly when `T` obeys that law, `isEquivariant_familyMap_iff`.

A tensor with two indices is `fromPairT` of exactly one element of the tensor product of the two
representations, and `fromPairT` is equivariant, so the invariant tensors with two indices are the
images of the invariants of that tensor product; likewise for three indices and `fromTripleT` (E).
A classification of the invariants of a tensor product of representations is thereby one of the
invariant tensors.

The action on `S.Tensor c` is a representation `S.tensorRep c`, so the invariant tensors are the
Mathlib submodule `(S.tensorRep c).invariants` (F). A linear equivalence onto the tensors which
intertwines a representation `σ` with this action carries the invariants of `σ` onto those of the
tensors, as `fromPairTEquiv` and `fromTripleTEquiv` do for tensor products. When the colors are
closed under adjoints, the invariants in the range of an intertwining map out of the tensors are
the image of the invariant tensors.

## ii. Key results

- `TensorSpecies.IsEquivariant` : equivariant linear maps out of `S.Tensor c`.
- `TensorSpecies.smul_basis_eq_sum` : the action on the basis tensors.
- `TensorSpecies.IsAdjointClosed` : the colors are closed under conjugate transposition.
- `TensorSpecies.IsEquivariant.exists_invariant_add_of_mem_sup` : invariants of the range come from
  invariant tensors.
- `TensorSpecies.IsEquivariant.reducesInvariantsTo_map` : the reduction to the image of a
  submodule containing the invariant tensors.
- `TensorSpecies.IsEquivariant.invariantReductionToSpan` : the reduction to one invariant tensor.
- `TensorSpecies.isEquivariant_familyMap_iff` : the map of a family is equivariant exactly when
  the family obeys the transformation law of the components.
- `TensorSpecies.Tensor.exists_fromPairT_of_invariant`,
  `TensorSpecies.Tensor.exists_fromTripleT_of_invariant` : invariant tensors with two or three
  indices are the images of invariants of the tensor product of the representations.
- `TensorSpecies.Tensor.exists_eq_smul_fromPairT_of_invariant` : a line of invariants of the
  tensor product gives the invariant tensors.
- `TensorSpecies.tensorRep` : the action on tensors as a representation.
- `TensorSpecies.invariants_eq_map_of_equiv` : the invariants of a representation identified with
  the tensors are the invariant tensors.
- `TensorSpecies.IsAdjointClosed.invariants_inf_range_eq_map` : the invariants in the range of an
  intertwining map out of the tensors are the image of the invariant tensors.

## iii. Table of contents

- A. Equivariant maps and the action on basis tensors
- B. Colors closed under adjoints
- C. Invariants in the range come from invariant tensors
- D. Building equivariant maps
- E. Invariant tensors with two and three indices
- F. The tensors as a representation

## iv. References

* None.

-/

@[expose] public section

namespace TensorSpecies

open Module Matrix Tensor

/-!

## A. Equivariant maps and the action on basis tensors

-/

section General

variable {k : Type} [CommRing k] {C G : Type} [Group G]
  {V : C → Type} [∀ c, AddCommGroup (V c)] [∀ c, Module k (V c)]
  {basisIdx : C → Type} [∀ c, Fintype (basisIdx c)] [∀ c, DecidableEq (basisIdx c)]
  {rep : (c : C) → Representation k G (V c)} {b : (c : C) → Basis (basisIdx c) k (V c)}

/-- A linear map `f` from the tensors of the species `S` with index colors `c` to a
  representation `ρ` of the group of the species, which is equivariant, that is, it intertwines
  the action of the group on tensors with `ρ`. -/
structure IsEquivariant (S : TensorSpecies k C G V basisIdx rep b) {n : ℕ} (c : Fin n → C)
    {B : Type*} [AddCommMonoid B] [Module k B] (ρ : Representation k G B)
    (f : S.Tensor c →ₗ[k] B) : Prop where
  equivariant : ∀ (g : G) (t : S.Tensor c), f (g • t) = ρ g (f t)

variable {S : TensorSpecies k C G V basisIdx rep b}

/-- The action of `g` on a basis tensor. The coefficient of `e_ψ` in `g • e_φ` is the product over
  the indices of the matrix entries of `g` in the color of that index. -/
lemma smul_basis_eq_sum {n : ℕ} (c : Fin n → C) (g : G) (φ : ComponentIdx (S := S) c) :
    g • Tensor.basis (S := S) c φ
      = ∑ ψ : ComponentIdx (S := S) c,
        (∏ i, LinearMap.toMatrix (b (c i)) (b (c i)) (rep (c i) g) (ψ i) (φ i)) •
        Tensor.basis (S := S) c ψ := by
  simp only [Tensor.basis_apply, LinearMap.toMatrix_apply]
  rw [actionT_pure]
  have h : g • Pure.basisVector (S := S) c φ
      = (fun i => ∑ j, (b (c i)).repr (rep (c i) g (b (c i) (φ i))) j • b (c i) j :
        Pure S c) := by
    funext i
    exact ((b (c i)).sum_repr _).symm
  rw [h]
  unfold Pure.toTensor
  rw [MultilinearMap.map_sum]
  refine Finset.sum_congr rfl fun ψ _ => ?_
  rw [← MultilinearMap.map_smul_univ]
  rfl

/-- The components of `g • t`, the matrix of products of the matrix entries of `g`, one factor
  per index, applied to the components of `t`. -/
lemma basis_repr_smul {n : ℕ} (c : Fin n → C) (g : G) (t : S.Tensor c)
    (φ : ComponentIdx (S := S) c) :
    (Tensor.basis c).repr (g • t) φ
      = ∑ ψ, (∏ i, LinearMap.toMatrix (b (c i)) (b (c i)) (rep (c i) g) (φ i) (ψ i)) *
        (Tensor.basis c).repr t ψ := by
  conv_lhs => rw [← (Tensor.basis (S := S) c).sum_repr t]
  rw [actionT_eq, map_sum, map_sum, Finsupp.coe_finsetSum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun ψ _ => ?_
  rw [map_smul, map_smul, Finsupp.smul_apply, smul_eq_mul, mul_comm]
  congr 1
  have h := smul_basis_eq_sum c g ψ
  rw [actionT_eq] at h
  rw [h, map_sum]
  simp [Finsupp.single_apply]

namespace IsEquivariant

variable {n : ℕ} {c : Fin n → C} {B : Type*} [AddCommGroup B] [Module k B]
  {ρ : Representation k G B} {f : S.Tensor c →ₗ[k] B} (hf : S.IsEquivariant c ρ f)

include hf in
/-- The range of an equivariant map is stable under the group. -/
lemma isStableUnder_range : IsStableUnder (fun g : G => ρ g) (LinearMap.range f) := by
  rintro g _ ⟨t, rfl⟩
  exact ⟨g • t, hf.equivariant g t⟩

include hf in
/-- The image of an invariant tensor under an equivariant map is invariant. -/
lemma rep_map_of_invariant {t : S.Tensor c} (ht : ∀ g : G, g • t = t) (g : G) :
    ρ g (f t) = f t := by
  rw [← hf.equivariant, ht]

/-- A sum of equivariant maps is equivariant. -/
lemma sum {ι : Type*} (s : Finset ι) {F : ι → S.Tensor c →ₗ[k] B}
    (hF : ∀ i ∈ s, S.IsEquivariant c ρ (F i)) : S.IsEquivariant c ρ (∑ i ∈ s, F i) where
  equivariant g t := by
    rw [LinearMap.sum_apply, LinearMap.sum_apply, map_sum]
    exact Finset.sum_congr rfl fun i hi => (hF i hi).equivariant g t

include hf in
/-- Composing with a linear map that intertwines `ρ` with `ρ'` keeps a map equivariant. -/
lemma comp {B' : Type*} [AddCommGroup B'] [Module k B'] {ρ' : Representation k G B'}
    (σ : B →ₗ[k] B') (hσ : ∀ (g : G) (y : B), σ (ρ g y) = ρ' g (σ y)) :
    S.IsEquivariant c ρ' (σ ∘ₗ f) where
  equivariant g t := by
    rw [LinearMap.comp_apply, LinearMap.comp_apply, hf.equivariant, hσ]

include hf in
/-- A difference of equivariant maps is equivariant. -/
lemma sub {f' : S.Tensor c →ₗ[k] B} (hf' : S.IsEquivariant c ρ f') :
    S.IsEquivariant c ρ (f - f') where
  equivariant g t := by
    rw [LinearMap.sub_apply, LinearMap.sub_apply, map_sub, hf.equivariant, hf'.equivariant]

end IsEquivariant

end General

/-!

## B. Colors closed under adjoints

-/

section Complex

variable {C G : Type} [Group G]
  {V : C → Type} [∀ c, AddCommGroup (V c)] [∀ c, Module ℂ (V c)]
  {basisIdx : C → Type} [∀ c, Fintype (basisIdx c)] [∀ c, DecidableEq (basisIdx c)]
  {rep : (c : C) → Representation ℂ G (V c)} {b : (c : C) → Basis (basisIdx c) ℂ (V c)}

set_option linter.unusedVariables false in
/-- The colors `c` of a complex species are closed under adjoints when for every `g` some `g'`
  acts on each of them by the conjugate transpose of the matrix of `g`. For a unitary group
  `g' = g⁻¹` and orthonormal bases; for `SL(2,ℂ)` on the Weyl colors, `g' = g†`. -/
@[nolint unusedArguments]
def IsAdjointClosed (S : TensorSpecies ℂ C G V basisIdx rep b) {n : ℕ} (c : Fin n → C) :
    Prop :=
  ∀ g : G, ∃ g' : G, ∀ i,
    LinearMap.toMatrix (b (c i)) (b (c i)) (rep (c i) g')
      = (LinearMap.toMatrix (b (c i)) (b (c i)) (rep (c i) g))ᴴ

/-!

## C. Invariants in the range come from invariant tensors

-/

namespace IsEquivariant

variable {S : TensorSpecies ℂ C G V basisIdx rep b} {n : ℕ} {c : Fin n → C} {B : Type*}
  [AddCommGroup B] [Module ℂ B] {ρ : Representation ℂ G B} {f : S.Tensor c →ₗ[ℂ] B}
  (hf : S.IsEquivariant c ρ f)

include hf in
/-- An invariant in the range of `f` is the image of an invariant tensor, when the colors are
  closed under adjoints. The adjoint of the action of `g` on the coefficients is that of `g'`. -/
lemma exists_invariant_eq_of_mem_range (hc : S.IsAdjointClosed c) {x : B}
    (hx : x ∈ LinearMap.range f) (hinv : ∀ g : G, ρ g x = x) :
    ∃ t : S.Tensor c, (∀ g : G, g • t = t) ∧ f t = x := by
  rw [LinearMap.range_eq_span_range_basis (Tensor.basis c)] at hx
  obtain ⟨a, rfl, ha⟩ := Fintype.exists_mulVec_eq_of_conjTranspose_mem
    (fun ψ => f (Tensor.basis c ψ)) (fun g => ρ g)
    (fun g => Matrix.of fun ψ φ => ∏ i, LinearMap.toMatrix (b (c i)) (b (c i))
      (rep (c i) g) (ψ i) (φ i))
    (fun g φ => by
      rw [← hf.equivariant, smul_basis_eq_sum, map_sum]
      exact Finset.sum_congr rfl fun ψ _ => map_smul _ _ _)
    (fun g => by
      obtain ⟨g', hg'⟩ := hc g
      refine ⟨g', Matrix.ext fun ψ φ => ?_⟩
      simp only [Matrix.of_apply, Matrix.conjTranspose_apply, star_prod]
      exact Finset.prod_congr rfl fun i _ => by rw [hg' i]; rfl) hx hinv
  refine ⟨∑ ψ, a ψ • Tensor.basis c ψ, fun g => ?_, by simp [map_sum]⟩
  apply (Tensor.basis (S := S) c).repr.injective
  ext φ
  rw [basis_repr_smul, Module.Basis.repr_sum_self]
  conv_rhs => rw [← ha g]
  simp only [Matrix.mulVec, dotProduct, Matrix.of_apply]

include hf in
/-- An invariant of `LinearMap.range f ⊔ W`, for `W` a stable submodule, is the image of an
  invariant tensor plus an element of `W`. -/
lemma exists_invariant_add_of_mem_sup (hc : S.IsAdjointClosed c) (W : Submodule ℂ B)
    (hW : ∀ g : G, ∀ y ∈ W, ρ g y ∈ W) {x : B} (hx : x ∈ LinearMap.range f ⊔ W)
    (hinv : ∀ g : G, ρ g x = x) :
    ∃ t : S.Tensor c, (∀ g : G, g • t = t) ∧ ∃ y ∈ W, x = f t + y := by
  have hq : S.IsEquivariant c (ρ.quotient W fun g y hy => hW g y hy) (W.mkQ ∘ₗ f) :=
    ⟨fun g t => by
      simp only [LinearMap.comp_apply]
      rw [hf.equivariant]
      rfl⟩
  obtain ⟨t, ht, hft⟩ := hq.exists_invariant_eq_of_mem_range hc (x := W.mkQ x) (by
      rw [LinearMap.range_comp]
      have h := Submodule.mem_map_of_mem (f := W.mkQ) hx
      rwa [Submodule.map_sup, Submodule.mkQ_map_self, sup_bot_eq] at h)
    (fun g => by
      change W.mkQ (ρ g x) = W.mkQ x
      rw [hinv])
  exact ⟨t, ht, x - f t, (Submodule.Quotient.eq W).1 hft.symm, by abel⟩

include hf in
/-- When every invariant tensor of `S.Tensor c` lies in `I`, the invariants of the range of `f`
  reduce to the image of `I`. -/
lemma reducesInvariantsTo_map (hc : S.IsAdjointClosed c) (I : Submodule ℂ (S.Tensor c))
    (hI : ∀ t : S.Tensor c, (∀ g : G, g • t = t) → t ∈ I) :
    ReducesInvariantsTo (fun g : G => ρ g) (LinearMap.range f) (I.map f) := by
  intro W hW x hx hinv
  obtain ⟨t, ht, y, hy, rfl⟩ := hf.exists_invariant_add_of_mem_sup hc W hW hx hinv
  exact Submodule.add_mem_sup (Submodule.mem_map_of_mem (hI t ht)) hy

include hf in
/-- When the only invariant tensor of `S.Tensor c` is zero, the range of `f` reduces to `⊥`. -/
lemma reducesInvariantsTo_bot (hc : S.IsAdjointClosed c)
    (hI : ∀ t : S.Tensor c, (∀ g : G, g • t = t) → t = 0) :
    ReducesInvariantsTo (fun g : G => ρ g) (LinearMap.range f) ⊥ := by
  have h := hf.reducesInvariantsTo_map hc ⊥ fun t ht => (Submodule.mem_bot ℂ).2 (hI t ht)
  rwa [Submodule.map_bot] at h

include hf in
/-- When the only invariant tensor of `S.Tensor c` is zero, so is every invariant in the range
  of `f`. -/
lemma eq_zero_of_invariant (hc : S.IsAdjointClosed c)
    (hI : ∀ t : S.Tensor c, (∀ g : G, g • t = t) → t = 0) {x : B}
    (hx : x ∈ LinearMap.range f) (hinv : ∀ g : G, ρ g x = x) : x = 0 := by
  obtain ⟨t, ht, rfl⟩ := hf.exists_invariant_eq_of_mem_range hc hx hinv
  rw [hI t ht, map_zero]

include hf in
/-- When the invariant tensors of `S.Tensor c` are the multiples of one tensor `t₀`, the
  invariants of the range of `f` reduce to the span of `f t₀`. -/
noncomputable def invariantReductionToSpan (hc : S.IsAdjointClosed c) (t₀ : S.Tensor c)
    (ht₀ : ∀ g : G, g • t₀ = t₀)
    (hclass : ∀ t : S.Tensor c, (∀ g : G, g • t = t) → ∃ a : ℂ, t = a • t₀) :
    InvariantReductionToSpan (fun g : G => ρ g) (LinearMap.range f) where
  spanningVector := f t₀
  stable := hf.isStableUnder_range
  spanningVector_fixed := hf.rep_map_of_invariant ht₀
  reduce W hW _ hx hinv := by
    obtain ⟨t, ht, y, hy, rfl⟩ := hf.exists_invariant_add_of_mem_sup hc W hW hx hinv
    obtain ⟨a, rfl⟩ := hclass t ht
    exact ⟨a, y, hy, by rw [map_smul]⟩

include hf in
/-- The reduction of `invariantReductionToSpan`, stated for a submodule `V` equal to the range of
  `f` and with the spanning vector given by any expression `v` for `f t₀`. -/
noncomputable def invariantReductionToSpanOfEq (hc : S.IsAdjointClosed c) (t₀ : S.Tensor c)
    (ht₀ : ∀ g : G, g • t₀ = t₀)
    (hclass : ∀ t : S.Tensor c, (∀ g : G, g • t = t) → ∃ a : ℂ, t = a • t₀)
    {V : Submodule ℂ B} (hV : LinearMap.range f = V) (v : B) (hv : f t₀ = v) :
    InvariantReductionToSpan (fun g : G => ρ g) V where
  spanningVector := v
  stable := hV ▸ hf.isStableUnder_range
  spanningVector_fixed := hv ▸ hf.rep_map_of_invariant ht₀
  reduce W hW x hx hinv := by
    subst hV hv
    exact (hf.invariantReductionToSpan hc t₀ ht₀ hclass).reduce W hW x hx hinv

end IsEquivariant

end Complex

/-!

## D. Building equivariant maps

-/

section Constr

variable {k : Type} [CommRing k] {C G : Type} [Group G]
  {V : C → Type} [∀ c, AddCommGroup (V c)] [∀ c, Module k (V c)]
  {basisIdx : C → Type} [∀ c, Fintype (basisIdx c)] [∀ c, DecidableEq (basisIdx c)]
  {rep : (c : C) → Representation k G (V c)} {b : (c : C) → Basis (basisIdx c) k (V c)}
  {S : TensorSpecies k C G V basisIdx rep b}

/-- The linear map with prescribed values `T ψ` on the basis tensors is equivariant when the
  values are moved by `ρ` as the basis tensors are moved by the group. -/
lemma isEquivariant_constr {n : ℕ} {c : Fin n → C} {B : Type*} [AddCommGroup B] [Module k B]
    {ρ : Representation k G B} (T : ComponentIdx (S := S) c → B)
    (hT : ∀ (g : G) φ, ρ g (T φ)
      = ∑ ψ, (∏ i, LinearMap.toMatrix (b (c i)) (b (c i)) (rep (c i) g) (ψ i) (φ i)) • T ψ) :
    S.IsEquivariant c ρ ((Tensor.basis c).constr k T) where
  equivariant g t := by
    have h : (Tensor.basis c).constr k T ∘ₗ PiTensorProduct.map (fun i => rep (c i) g)
        = ρ g ∘ₗ (Tensor.basis c).constr k T := by
      refine (Tensor.basis (S := S) c).ext fun φ => ?_
      have h1 := smul_basis_eq_sum (S := S) c g φ
      rw [actionT_eq] at h1
      simp only [LinearMap.comp_apply, h1, map_sum, map_smul, Module.Basis.constr_basis, hT]
    exact LinearMap.congr_fun h t

variable {n : ℕ} {c : Fin n → C} {ι : Type*} {B : Type*} [AddCommGroup B] [Module k B]

/-- The linear map out of `S.Tensor c` sending the basis tensor with components `e.symm l` to
  `T l`, for a relabelling `e` of the component indices by `ι`. -/
noncomputable def familyMap (e : ComponentIdx (S := S) c ≃ ι) (T : ι → B) :
    S.Tensor c →ₗ[k] B :=
  (Tensor.basis c).constr k (T ∘ e)

@[simp]
lemma familyMap_basis (e : ComponentIdx (S := S) c ≃ ι) (T : ι → B) (l : ι) :
    familyMap e T (Tensor.basis c (e.symm l)) = T l := by
  simp [familyMap]

/-- The range of `familyMap e T` is the span of the vectors `T l`. -/
lemma range_familyMap (e : ComponentIdx (S := S) c ≃ ι) (T : ι → B) :
    LinearMap.range (familyMap e T) = Submodule.span k (Set.range T) := by
  rw [familyMap, Module.Basis.constr_range]
  exact congrArg _ (e.surjective.range_comp T)

/-- `familyMap` of a sum of families is the sum of the maps. -/
lemma familyMap_sum (e : ComponentIdx (S := S) c ≃ ι) {α : Type*} (s : Finset α)
    (T : α → ι → B) :
    familyMap e (fun l => ∑ i ∈ s, T i l) = ∑ i ∈ s, familyMap e (T i) :=
  (Tensor.basis c).ext fun φ => by simp [familyMap, LinearMap.sum_apply]

/-- A linear map moving a family as `g` moves the basis tensors intertwines the map of the family
  with the action of `g`. -/
lemma familyMap_smul_of_law (e : ComponentIdx (S := S) c ≃ ι) [Fintype ι] (T : ι → B)
    {σ : B →ₗ[k] B} (g : G)
    (hσ : ∀ l : ι, σ (T l) = ∑ a, (∏ i, LinearMap.toMatrix (b (c i)) (b (c i)) (rep (c i) g)
      (e.symm a i) (e.symm l i)) • T a) (t : S.Tensor c) :
    σ (familyMap e T t) = familyMap e T (g • t) := by
  have h : σ ∘ₗ familyMap e T = familyMap e T ∘ₗ PiTensorProduct.map (fun i => rep (c i) g) := by
    refine (Tensor.basis (S := S) c).ext fun φ => ?_
    obtain ⟨l, rfl⟩ := e.symm.surjective φ
    have h1 := smul_basis_eq_sum (S := S) c g (e.symm l)
    rw [actionT_eq] at h1
    simp only [LinearMap.comp_apply, h1, map_sum, map_smul, familyMap_basis, hσ,
      ← e.symm.sum_comp]
  exact (LinearMap.congr_fun h t).trans (by rw [actionT_eq]; rfl)

/-- The map of a family is equivariant exactly when the family is moved as the basis tensors
  are, with one matrix entry of `g` per index and the summed index first in each factor. -/
lemma isEquivariant_familyMap_iff (e : ComponentIdx (S := S) c ≃ ι) [Fintype ι]
    {ρ : Representation k G B} (T : ι → B) :
    S.IsEquivariant c ρ (familyMap e T) ↔ ∀ (g : G) (l : ι), ρ g (T l)
      = ∑ a, (∏ i, LinearMap.toMatrix (b (c i)) (b (c i)) (rep (c i) g)
        (e.symm a i) (e.symm l i)) • T a := by
  constructor
  · intro hf g l
    have h := hf.equivariant g (Tensor.basis c (e.symm l))
    rw [smul_basis_eq_sum, ← e.symm.sum_comp, map_sum] at h
    simpa [familyMap] using h.symm
  · exact fun hT => ⟨fun g t => (familyMap_smul_of_law e T g (hT g) t).symm⟩

end Constr

/-!

## E. Invariant tensors with two and three indices

-/

namespace Tensor

open TensorProduct

variable {k : Type} [CommRing k] {C G : Type} [Group G]
  {V : C → Type} [∀ c, AddCommGroup (V c)] [∀ c, Module k (V c)]
  {basisIdx : C → Type} [∀ c, Fintype (basisIdx c)] [∀ c, DecidableEq (basisIdx c)]
  {rep : (c : C) → Representation k G (V c)} {b : (c : C) → Basis (basisIdx c) k (V c)}
  {S : TensorSpecies k C G V basisIdx rep b}

/-- A tensor with two indices determines the element of `V c1 ⊗ V c2` it comes from. -/
lemma fromPairT_injective {c1 c2 : C} :
    Function.Injective (fromPairT (S := S) (c1 := c1) (c2 := c2)) := by
  intro x y h
  apply (Basis.tensorProduct (b c1) (b c2)).repr.injective
  ext ⟨i, j⟩
  have h' := congrArg (fun t => (Tensor.basis ![c1, c2]).repr t (fun | 0 => i | 1 => j)) h
  simpa only [fromPairT_basis_repr] using h'

/-- Every tensor with two indices comes from `V c1 ⊗ V c2`, since the basis tensors do. -/
lemma fromPairT_surjective {c1 c2 : C} :
    Function.Surjective (fromPairT (S := S) (c1 := c1) (c2 := c2)) := by
  rw [← LinearMap.range_eq_top, eq_top_iff, ← (Tensor.basis (S := S) ![c1, c2]).span_eq,
    Submodule.span_le]
  rintro _ ⟨φ, rfl⟩
  refine ⟨_, (fromPairT_apply_basis_repr (S := S) (c := c1) (c1 := c2) (φ 0) (φ 1)).trans
    (congrArg _ ?_)⟩
  funext j
  fin_cases j <;> rfl

/-- An invariant tensor with two indices is `fromPairT` of an invariant of the tensor product of
  the two representations. -/
lemma exists_fromPairT_of_invariant {c1 c2 : C} {t : S.Tensor ![c1, c2]}
    (ht : ∀ g : G, g • t = t) :
    ∃ x ∈ ((rep c1).tprod (rep c2)).invariants, fromPairT x = t := by
  obtain ⟨x, rfl⟩ := fromPairT_surjective t
  refine ⟨x, fun g => fromPairT_injective (S := S) ?_, rfl⟩
  change fromPairT (TensorProduct.map (rep c1 g) (rep c2 g) x) = _
  rw [← actionT_fromPairT, ht]

/-- When the invariants of `V c1 ⊗ V c2` are the line through `v`, the invariant tensors with two
  indices are the multiples of `fromPairT v`. -/
lemma exists_eq_smul_fromPairT_of_invariant {c1 c2 : C} {v : V c1 ⊗[k] V c2}
    (hv : ((rep c1).tprod (rep c2)).invariants = Submodule.span k {v}) {t : S.Tensor ![c1, c2]}
    (ht : ∀ g : G, g • t = t) : ∃ a : k, t = a • fromPairT v := by
  obtain ⟨x, hx, rfl⟩ := exists_fromPairT_of_invariant ht
  rw [hv, Submodule.mem_span_singleton] at hx
  obtain ⟨a, rfl⟩ := hx
  exact ⟨a, map_smul _ _ _⟩

/-- When `V c1 ⊗ V c2` has no invariants but zero, neither do the tensors with two indices. -/
lemma eq_zero_of_invariant_of_invariants_eq_bot {c1 c2 : C}
    (hv : ((rep c1).tprod (rep c2)).invariants = ⊥) {t : S.Tensor ![c1, c2]}
    (ht : ∀ g : G, g • t = t) : t = 0 := by
  obtain ⟨x, hx, rfl⟩ := exists_fromPairT_of_invariant ht
  rw [hv, Submodule.mem_bot] at hx
  rw [hx, map_zero]

/-- A tensor with three indices determines the element of `V c1 ⊗ (V c2 ⊗ V c3)` it comes
  from. -/
lemma fromTripleT_injective {c1 c2 c3 : C} :
    Function.Injective (fromTripleT (S := S) (c1 := c1) (c2 := c2) (c3 := c3)) := by
  intro x y h
  apply (Basis.tensorProduct (b c1) (Basis.tensorProduct (b c2) (b c3))).repr.injective
  ext ⟨i, j, l⟩
  have h' := congrArg
    (fun t => (Tensor.basis ![c1, c2, c3]).repr t (fun | 0 => i | 1 => j | 2 => l)) h
  simpa only [fromTripleT_basis_repr] using h'

/-- Every tensor with three indices comes from `V c1 ⊗ (V c2 ⊗ V c3)`, since the basis tensors
  do. -/
lemma fromTripleT_surjective {c1 c2 c3 : C} :
    Function.Surjective (fromTripleT (S := S) (c1 := c1) (c2 := c2) (c3 := c3)) := by
  rw [← LinearMap.range_eq_top, eq_top_iff, ← (Tensor.basis (S := S) ![c1, c2, c3]).span_eq,
    Submodule.span_le]
  rintro _ ⟨φ, rfl⟩
  refine ⟨_, (fromTripleT_apply_basis (S := S) (c := c1) (c1 := c2) (c2 := c3) (φ 0) (φ 1)
    (φ 2)).trans (congrArg _ ?_)⟩
  funext j
  fin_cases j <;> rfl

/-- An invariant tensor with three indices is `fromTripleT` of an invariant of the tensor
  product of the three representations. -/
lemma exists_fromTripleT_of_invariant {c1 c2 c3 : C} {t : S.Tensor ![c1, c2, c3]}
    (ht : ∀ g : G, g • t = t) :
    ∃ x ∈ ((rep c1).tprod ((rep c2).tprod (rep c3))).invariants, fromTripleT x = t := by
  obtain ⟨x, rfl⟩ := fromTripleT_surjective t
  refine ⟨x, fun g => fromTripleT_injective (S := S) ?_, rfl⟩
  change fromTripleT (TensorProduct.map (rep c1 g) (TensorProduct.map (rep c2 g) (rep c3 g)) x) = _
  rw [← actionT_fromTripleT, ht]

/-- When the invariants of `V c1 ⊗ (V c2 ⊗ V c3)` are the line through `v`, the invariant tensors
  with three indices are the multiples of `fromTripleT v`. -/
lemma exists_eq_smul_fromTripleT_of_invariant {c1 c2 c3 : C} {v : V c1 ⊗[k] (V c2 ⊗[k] V c3)}
    (hv : ((rep c1).tprod ((rep c2).tprod (rep c3))).invariants = Submodule.span k {v})
    {t : S.Tensor ![c1, c2, c3]} (ht : ∀ g : G, g • t = t) : ∃ a : k, t = a • fromTripleT v := by
  obtain ⟨x, hx, rfl⟩ := exists_fromTripleT_of_invariant ht
  rw [hv, Submodule.mem_span_singleton] at hx
  obtain ⟨a, rfl⟩ := hx
  exact ⟨a, map_smul _ _ _⟩

end Tensor

/-!

## F. The tensors as a representation

-/

section TensorRep

open TensorProduct

variable {k : Type} [CommRing k] {C G : Type} [Group G]
  {V : C → Type} [∀ c, AddCommGroup (V c)] [∀ c, Module k (V c)]
  {basisIdx : C → Type} [∀ c, Fintype (basisIdx c)] [∀ c, DecidableEq (basisIdx c)]
  {rep : (c : C) → Representation k G (V c)} {b : (c : C) → Basis (basisIdx c) k (V c)}
  {S : TensorSpecies k C G V basisIdx rep b} {n : ℕ} {c : Fin n → C}

variable (S) in
/-- The action of the group on the tensors with index colors `c`, as a representation. -/
noncomputable def tensorRep (c : Fin n → C) : Representation k G (S.Tensor c) where
  toFun g := PiTensorProduct.map fun i => rep (c i) g
  map_one' := LinearMap.ext fun (t : S.Tensor c) => one_smul G t
  map_mul' g h := LinearMap.ext fun (t : S.Tensor c) => mul_smul g h t

@[simp]
lemma tensorRep_apply (g : G) (t : S.Tensor c) : S.tensorRep c g t = g • t := rfl

/-- The invariant tensors are the line through an invariant tensor `t₀` when every invariant
  tensor is a multiple of it. -/
lemma invariants_tensorRep_eq_span_singleton {t₀ : S.Tensor c} (ht₀ : ∀ g : G, g • t₀ = t₀)
    (h : ∀ t : S.Tensor c, (∀ g : G, g • t = t) → ∃ a : k, t = a • t₀) :
    (S.tensorRep c).invariants = k ∙ t₀ := by
  refine le_antisymm (fun t ht => ?_) ((Submodule.span_singleton_le_iff_mem _ _).2 ht₀)
  obtain ⟨a, rfl⟩ := h t ht
  exact Submodule.smul_mem _ a (Submodule.mem_span_singleton_self t₀)

/-- There are no invariant tensors but zero when every invariant tensor vanishes. -/
lemma invariants_tensorRep_eq_bot (h : ∀ t : S.Tensor c, (∀ g : G, g • t = t) → t = 0) :
    (S.tensorRep c).invariants = ⊥ :=
  eq_bot_iff.2 fun t ht => (Submodule.mem_bot k).2 (h t ht)

/-- For a linear equivalence `e` onto the tensors intertwining `σ` with the action on tensors, the
  invariants of `σ` are the images of the invariant tensors under `e⁻¹`. -/
lemma invariants_eq_map_of_equiv {W : Type*} [AddCommGroup W] [Module k W]
    {σ : Representation k G W} (e : W ≃ₗ[k] S.Tensor c)
    (he : ∀ (g : G) (w : W), e (σ g w) = g • e w) :
    σ.invariants = (S.tensorRep c).invariants.map (e.symm : S.Tensor c →ₗ[k] W) := by
  ext w
  rw [Submodule.mem_map_equiv, LinearEquiv.symm_symm]
  refine ⟨fun hw g => ?_, fun hw g => e.injective ?_⟩
  · change g • e w = e w
    rw [← he, hw g]
  · rw [he]
    exact hw g

/-- For a linear equivalence `e` onto the tensors intertwining `σ` with the action on tensors, the
  invariant tensors are the images under `e` of the invariants of `σ`. -/
lemma invariants_tensorRep_eq_map_of_equiv {W : Type*} [AddCommGroup W] [Module k W]
    {σ : Representation k G W} (e : W ≃ₗ[k] S.Tensor c)
    (he : ∀ (g : G) (w : W), e (σ g w) = g • e w) :
    (S.tensorRep c).invariants = σ.invariants.map (e : W →ₗ[k] S.Tensor c) := by
  ext t
  rw [Submodule.mem_map_equiv]
  refine ⟨fun ht g => e.injective ?_, fun ht g => ?_⟩
  · rw [he, e.apply_symm_apply]
    exact ht g
  · change g • t = t
    have h := he g (e.symm t)
    rw [ht g, e.apply_symm_apply] at h
    exact h.symm

/-- The tensors with two indices as the tensor product of the two representations. -/
noncomputable def fromPairTEquiv {c1 c2 : C} : V c1 ⊗[k] V c2 ≃ₗ[k] S.Tensor ![c1, c2] :=
  LinearEquiv.ofBijective Tensor.fromPairT ⟨Tensor.fromPairT_injective, Tensor.fromPairT_surjective⟩

@[simp]
lemma fromPairTEquiv_apply {c1 c2 : C} (x : V c1 ⊗[k] V c2) :
    fromPairTEquiv (S := S) x = Tensor.fromPairT x := rfl

/-- `fromPairTEquiv` intertwines the tensor product of the two representations with the action on
  tensors. -/
lemma fromPairTEquiv_tprod {c1 c2 : C} (g : G) (x : V c1 ⊗[k] V c2) :
    fromPairTEquiv (S := S) (((rep c1).tprod (rep c2)) g x) = g • fromPairTEquiv x :=
  (Tensor.actionT_fromPairT x g).symm

/-- The invariants of the tensor product of two representations are the line through `v` when the
  invariant tensors with two indices are the line through `fromPairT v`. -/
lemma invariants_tprod_eq_span_singleton {c1 c2 : C} {v : V c1 ⊗[k] V c2}
    (h : (S.tensorRep ![c1, c2]).invariants = k ∙ Tensor.fromPairT v) :
    ((rep c1).tprod (rep c2)).invariants = k ∙ v := by
  rw [invariants_eq_map_of_equiv (fromPairTEquiv (S := S)) fromPairTEquiv_tprod, h,
    Submodule.map_span, Set.image_singleton, ← fromPairTEquiv_apply]
  rw [LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]

/-- The tensors with three indices as the tensor product of the three representations. -/
noncomputable def fromTripleTEquiv {c1 c2 c3 : C} :
    V c1 ⊗[k] (V c2 ⊗[k] V c3) ≃ₗ[k] S.Tensor ![c1, c2, c3] :=
  LinearEquiv.ofBijective Tensor.fromTripleT
    ⟨Tensor.fromTripleT_injective, Tensor.fromTripleT_surjective⟩

@[simp]
lemma fromTripleTEquiv_apply {c1 c2 c3 : C} (x : V c1 ⊗[k] (V c2 ⊗[k] V c3)) :
    fromTripleTEquiv (S := S) x = Tensor.fromTripleT x := rfl

/-- `fromTripleTEquiv` intertwines the tensor product of the three representations with the action
  on tensors. -/
lemma fromTripleTEquiv_tprod {c1 c2 c3 : C} (g : G) (x : V c1 ⊗[k] (V c2 ⊗[k] V c3)) :
    fromTripleTEquiv (S := S) (((rep c1).tprod ((rep c2).tprod (rep c3))) g x)
      = g • fromTripleTEquiv x :=
  (Tensor.actionT_fromTripleT x g).symm

end TensorRep

/-! The invariants in the range of an intertwining map out of the tensors. -/

section TensorRepComplex

variable {C G : Type} [Group G]
  {V : C → Type} [∀ c, AddCommGroup (V c)] [∀ c, Module ℂ (V c)]
  {basisIdx : C → Type} [∀ c, Fintype (basisIdx c)] [∀ c, DecidableEq (basisIdx c)]
  {rep : (c : C) → Representation ℂ G (V c)} {b : (c : C) → Basis (basisIdx c) ℂ (V c)}
  {S : TensorSpecies ℂ C G V basisIdx rep b} {n : ℕ} {c : Fin n → C} {B : Type*}
  [AddCommGroup B] [Module ℂ B] {ρ : Representation ℂ G B}

/-- When the colors are closed under adjoints, the invariants in the range of an intertwining map
  `f` out of the tensors are the images of the invariant tensors. -/
lemma IsAdjointClosed.invariants_inf_range_eq_map (hc : S.IsAdjointClosed c)
    (f : (S.tensorRep c).IntertwiningMap ρ) :
    ρ.invariants ⊓ f.range.toSubmodule = (S.tensorRep c).invariants.map f.toLinearMap := by
  refine le_antisymm (fun x hx => ?_) ?_
  · have hf : S.IsEquivariant c ρ f.toLinearMap := ⟨fun g t => f.isIntertwining _ _ g t⟩
    obtain ⟨t, ht, rfl⟩ := hf.exists_invariant_eq_of_mem_range hc hx.2 hx.1
    exact ⟨t, ht, rfl⟩
  · rintro _ ⟨t, ht, rfl⟩
    exact ⟨f.apply_mem_invariants ht, t, rfl⟩

/-- When the colors are closed under adjoints and `e` identifies `σ` with the tensors, the
  invariants in the range of an intertwining map `f` out of `σ` are the images under `f ∘ e⁻¹` of
  the invariant tensors. -/
lemma IsAdjointClosed.invariants_inf_range_eq_map_of_equiv (hc : S.IsAdjointClosed c)
    {W : Type*} [AddCommGroup W] [Module ℂ W] {σ : Representation ℂ G W}
    (e : W ≃ₗ[ℂ] S.Tensor c) (he : ∀ (g : G) (w : W), e (σ g w) = g • e w)
    (f : σ.IntertwiningMap ρ) :
    ρ.invariants ⊓ f.range.toSubmodule
      = (S.tensorRep c).invariants.map (f.toLinearMap ∘ₗ (e.symm : S.Tensor c →ₗ[ℂ] W)) := by
  let E : (S.tensorRep c).IntertwiningMap σ :=
    (e.symm : S.Tensor c →ₗ[ℂ] W).intertwiningMap_of_isIntertwiningMap _ _ fun g t =>
      e.injective (by rw [he, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply,
        LinearEquiv.apply_symm_apply, tensorRep_apply])
  rw [← Representation.invariants_inf_range_comp_of_surjective f E e.symm.surjective,
    hc.invariants_inf_range_eq_map]
  rfl

/-- The invariants in the range of an intertwining map `f` out of the tensors are the line through
  `f t₀` when the invariant tensors are the line through `t₀`. -/
lemma IsAdjointClosed.invariants_inf_range_eq_span (hc : S.IsAdjointClosed c) {t₀ : S.Tensor c}
    (h : (S.tensorRep c).invariants = ℂ ∙ t₀) (f : (S.tensorRep c).IntertwiningMap ρ) :
    ρ.invariants ⊓ f.range.toSubmodule = ℂ ∙ f t₀ := by
  rw [hc.invariants_inf_range_eq_map, h, Submodule.map_span, Set.image_singleton]
  rfl

/-- The invariants in the range of an intertwining map `f` out of the tensors are zero when there
  are no invariant tensors but zero. -/
lemma IsAdjointClosed.invariants_inf_range_eq_bot (hc : S.IsAdjointClosed c)
    (h : (S.tensorRep c).invariants = ⊥) (f : (S.tensorRep c).IntertwiningMap ρ) :
    ρ.invariants ⊓ f.range.toSubmodule = ⊥ := by
  rw [hc.invariants_inf_range_eq_map, h, Submodule.map_bot]

/-- When `e` identifies `σ` with the tensors and the invariant tensors are the line through `e v`,
  the invariants in the range of an intertwining map `f` out of `σ` are the line through `f v`. -/
lemma IsAdjointClosed.invariants_inf_range_eq_span_of_equiv (hc : S.IsAdjointClosed c)
    {W : Type*} [AddCommGroup W] [Module ℂ W] {σ : Representation ℂ G W}
    (e : W ≃ₗ[ℂ] S.Tensor c) (he : ∀ (g : G) (w : W), e (σ g w) = g • e w) {v : W}
    (h : (S.tensorRep c).invariants = ℂ ∙ e v) (f : σ.IntertwiningMap ρ) :
    ρ.invariants ⊓ f.range.toSubmodule = ℂ ∙ f v := by
  rw [hc.invariants_inf_range_eq_map_of_equiv e he, h, Submodule.map_span, Set.image_singleton]
  simp

/-- When `e` identifies `σ` with the tensors and there are no invariant tensors but zero, the
  invariants in the range of an intertwining map out of `σ` are zero. -/
lemma IsAdjointClosed.invariants_inf_range_eq_bot_of_equiv (hc : S.IsAdjointClosed c)
    {W : Type*} [AddCommGroup W] [Module ℂ W] {σ : Representation ℂ G W}
    (e : W ≃ₗ[ℂ] S.Tensor c) (he : ∀ (g : G) (w : W), e (σ g w) = g • e w)
    (h : (S.tensorRep c).invariants = ⊥) (f : σ.IntertwiningMap ρ) :
    ρ.invariants ⊓ f.range.toSubmodule = ⊥ := by
  rw [hc.invariants_inf_range_eq_map_of_equiv e he, h, Submodule.map_bot]

end TensorRepComplex

end TensorSpecies
