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
public import PhyslibAlpha.Mathematics.RepresentationTheory.Reynolds.Compact
/-!
# Equivariant maps out of the tensors of a species

Families of vectors carrying tensor indices, and how their invariants come from invariant tensors.

## i. Overview

A family of vectors in a representation `ρ` of the group `G` of a tensor species `S`, carrying
indices of colors `c`, is packaged as a linear map `f : S.Tensor c →ₗ[k] B`, and
`S.IsEquivariant c ρ f` says that `f` intertwines the action of `G` on tensors with `ρ`. The action
on `S.Tensor c` is a representation `S.tensorRep c`, so the invariant tensors are the Mathlib
submodule `(S.tensorRep c).invariants` (A). Every classification of invariant tensors is stated as
`(S.tensorRep c).invariants = ℂ ∙ t₀`, `= Submodule.span ℂ s` or `= ⊥`.

Over `ℂ`, the invariants in the range of such a map come from invariant tensors (C): every
invariant of `LinearMap.range f ⊔ W`, for `W` a `G`-stable submodule, is `f t + y` with `t` an
invariant tensor and `y ∈ W`. This holds whenever the tensors have a Reynolds element,
`HasReynolds` (B): an element of the group algebra with coefficients summing to one which maps
every tensor to an invariant one. Applied to any preimage of an invariant `f t`, it gives an
invariant tensor with the same image. The Reynolds elements of a group are produced from the
continuity of its action, which `continuousMatrixCoeff_top_comp` reads off the matrix entries of
the colors. A classification of the invariant tensors thereby classifies the invariants in the
range of `f`, `IsEquivariant.invariantReductionToSpan`, and the invariants in the range of an
intertwining map out of the tensors, `HasReynolds.invariants_inf_range_eq_span`.

A family `T` of vectors indexed by the component indices of `S.Tensor c` is the map
`ofComponents T`, sending each basis tensor to the matching component, and it is equivariant
exactly when the components obey the transformation law of the components of a tensor in the
basis of the species, `isEquivariant_ofComponents_iff` (D). A family indexed by other labels is
first relabelled by an equivalence `e` with the component indices, as `ofComponents (T ∘ e)`.

A tensor with two indices is `fromPairT` of exactly one element of the tensor product of the two
representations, and `fromPairTEquiv` intertwines the two actions, so the invariant tensors with
two indices are the image of the invariants of that tensor product; likewise for three indices and
`fromTripleTEquiv` (E). A classification of the invariants of a tensor product of
representations is thereby one of the invariant tensors. A family with two indices `T x y`,
relabelled by `pairIdx`, gives an equivariant map when each index moves by the matrix of its
colour, `isEquivariant_ofComponents_pair`.

## ii. Key results

- `TensorSpecies.IsEquivariant` : equivariant linear maps out of `S.Tensor c`.
- `TensorSpecies.tensorRep` : the action on tensors as a representation.
- `TensorSpecies.HasReynolds` : the tensors have a Reynolds element.
- `TensorSpecies.continuousMatrixCoeff_top_comp` : continuity of the action on the tensors from
  that of the colors.
- `TensorSpecies.IsEquivariant.exists_invariant_add_of_mem_sup` : invariants of the range come from
  invariant tensors.
- `TensorSpecies.IsEquivariant.reducesInvariantsTo_span`,
  `TensorSpecies.IsEquivariant.reducesInvariantsTo_bot` : the reductions given by the invariant
  tensors.
- `TensorSpecies.IsEquivariant.invariantReductionToSpan` : the reduction to one invariant tensor.
- `TensorSpecies.HasReynolds.invariants_inf_range_eq_map` : the invariants in the range of an
  intertwining map out of the tensors are the image of the invariant tensors.
- `TensorSpecies.ofComponents` : the linear map out of the tensors sending each basis tensor to the
  matching member of a family.
- `TensorSpecies.isEquivariant_ofComponents_iff` : the map of a family is equivariant exactly when
  the family obeys the transformation law of the components.
- `TensorSpecies.invariants_tensorRep_pair_eq_span`,
  `TensorSpecies.invariants_tensorRep_triple_eq_span` : invariant tensors with two or three
  indices from the invariants of the tensor product of the representations.

## iii. Table of contents

- A. Equivariant maps and the tensors as a representation
- B. Reynolds elements for the tensors
- C. Invariants in the range come from invariant tensors
- D. Maps from components
- E. Invariant tensors with two and three indices

## iv. References

* None.

-/

@[expose] public section

namespace TensorSpecies

open Module Matrix Tensor

/-!

## A. Equivariant maps and the tensors as a representation

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

variable (S) in
/-- The action of the group on the tensors with index colors `c`, as a representation. -/
noncomputable def tensorRep {n : ℕ} (c : Fin n → C) : Representation k G (S.Tensor c) where
  toFun g := PiTensorProduct.map fun i => rep (c i) g
  map_one' := LinearMap.ext fun (t : S.Tensor c) => one_smul G t
  map_mul' g h := LinearMap.ext fun (t : S.Tensor c) => mul_smul g h t

@[simp]
lemma tensorRep_apply {n : ℕ} {c : Fin n → C} (g : G) (t : S.Tensor c) :
    S.tensorRep c g t = g • t := rfl

/-- The invariant tensors are the line through an invariant tensor `t₀` when every invariant
  tensor is a multiple of it. -/
lemma invariants_tensorRep_eq_span_singleton {n : ℕ} {c : Fin n → C} {t₀ : S.Tensor c}
    (ht₀ : ∀ g : G, g • t₀ = t₀)
    (h : ∀ t : S.Tensor c, (∀ g : G, g • t = t) → ∃ a : k, t = a • t₀) :
    (S.tensorRep c).invariants = k ∙ t₀ := by
  refine le_antisymm (fun t ht => ?_) ((Submodule.span_singleton_le_iff_mem _ _).2 ht₀)
  obtain ⟨a, rfl⟩ := h t ht
  exact Submodule.smul_mem _ a (Submodule.mem_span_singleton_self t₀)

/-- There are no invariant tensors but zero when every invariant tensor vanishes. -/
lemma invariants_tensorRep_eq_bot {n : ℕ} {c : Fin n → C}
    (h : ∀ t : S.Tensor c, (∀ g : G, g • t = t) → t = 0) : (S.tensorRep c).invariants = ⊥ :=
  eq_bot_iff.2 fun t ht => (Submodule.mem_bot k).2 (h t ht)

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

## B. Reynolds elements for the tensors

-/

section Complex

variable {C G : Type} [Group G]
  {V : C → Type} [∀ c, AddCommGroup (V c)] [∀ c, Module ℂ (V c)]
  {basisIdx : C → Type} [∀ c, Fintype (basisIdx c)] [∀ c, DecidableEq (basisIdx c)]
  {rep : (c : C) → Representation ℂ G (V c)} {b : (c : C) → Basis (basisIdx c) ℂ (V c)}

/-- The tensors of `S` with index colors `c` have a Reynolds element: an element of the group
  algebra, with coefficients summing to one, which maps every tensor to an invariant tensor. -/
def HasReynolds (S : TensorSpecies ℂ C G V basisIdx rep b) {n : ℕ} (c : Fin n → C) : Prop :=
  ∃ r, (S.tensorRep c).IsReynolds ⊤ r

variable {S : TensorSpecies ℂ C G V basisIdx rep b} {n : ℕ} {c : Fin n → C}

/-- The tensors have a Reynolds element when they have one for the action restricted along a
  surjective homomorphism `φ` onto the group of the species. -/
lemma HasReynolds.of_comp {H : Type*} [Group H] {φ : H →* G} (hφ : Function.Surjective φ)
    (h : ∃ r, Representation.IsReynolds ((S.tensorRep c).comp φ) ⊤ r) : S.HasReynolds c :=
  h.elim fun _ hr => ⟨_, hr.of_comp hφ⟩

/-- The action on the tensors, restricted along `φ : H →* G`, has continuous matrix coefficients
  when the matrix entries of every color are continuous on `H`. -/
lemma continuousMatrixCoeff_top_comp {H : Type*} [Group H] [TopologicalSpace H] (φ : H →* G)
    (hφ : ∀ (k : C) (x y : basisIdx k),
      Continuous fun h => LinearMap.toMatrix (b k) (b k) (rep k (φ h)) x y) :
    Representation.ContinuousMatrixCoeff (⊤ : Subrepresentation ((S.tensorRep c).comp φ)) :=
  Representation.continuousMatrixCoeff_of_span ⊤ (Tensor.basis c) (fun _ => Submodule.mem_top)
    (by rw [Module.Basis.span_eq]; exact le_top)
    (fun φ' ψ h => ∏ i, LinearMap.toMatrix (b (c i)) (b (c i)) (rep (c i) (φ h)) (ψ i) (φ' i))
    (fun _ _ => continuous_finsetProd _ fun i _ => hφ _ _ _)
    (fun h φ' => smul_basis_eq_sum c (φ h) φ')

/-!

## C. Invariants in the range come from invariant tensors

-/

namespace IsEquivariant

variable {S : TensorSpecies ℂ C G V basisIdx rep b} {n : ℕ} {c : Fin n → C} {B : Type*}
  [AddCommGroup B] [Module ℂ B] {ρ : Representation ℂ G B} {f : S.Tensor c →ₗ[ℂ] B}
  (hf : S.IsEquivariant c ρ f)

include hf in
/-- An invariant in the range of `f` is the image of an invariant tensor, the Reynolds element
  applied to any preimage. -/
lemma exists_invariant_eq_of_mem_range (hc : S.HasReynolds c) {x : B}
    (hx : x ∈ LinearMap.range f) (hinv : ∀ g : G, ρ g x = x) :
    ∃ t : S.Tensor c, (∀ g : G, g • t = t) ∧ f t = x := by
  obtain ⟨r, hr⟩ := hc
  obtain ⟨t, rfl⟩ := hx
  obtain ⟨t', ht', hft'⟩ := hr.exists_mem_invariants_map_eq (σ := ρ) (f := f)
    (fun g t => hf.equivariant g t) Submodule.mem_top hinv
  exact ⟨t', ht'.2, hft'⟩

include hf in
/-- An invariant of `LinearMap.range f ⊔ W`, for `W` a stable submodule, is the image of an
  invariant tensor plus an element of `W`. -/
lemma exists_invariant_add_of_mem_sup (hc : S.HasReynolds c) (W : Submodule ℂ B)
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
lemma reducesInvariantsTo_map (hc : S.HasReynolds c) {I : Submodule ℂ (S.Tensor c)}
    (hI : (S.tensorRep c).invariants ≤ I) :
    ReducesInvariantsTo (fun g : G => ρ g) (LinearMap.range f) (I.map f) := by
  intro W hW x hx hinv
  obtain ⟨t, ht, y, hy, rfl⟩ := hf.exists_invariant_add_of_mem_sup hc W hW hx hinv
  exact Submodule.add_mem_sup (Submodule.mem_map_of_mem (hI ht)) hy

include hf in
/-- When the invariant tensors are the span of `s`, the invariants of the range of `f` reduce to
  the span of the image of `s`. -/
lemma reducesInvariantsTo_span (hc : S.HasReynolds c) {s : Set (S.Tensor c)}
    (h : (S.tensorRep c).invariants = Submodule.span ℂ s) :
    ReducesInvariantsTo (fun g : G => ρ g) (LinearMap.range f) (Submodule.span ℂ (f '' s)) := by
  rw [← Submodule.map_span]
  exact hf.reducesInvariantsTo_map hc h.le

include hf in
/-- When the only invariant tensor of `S.Tensor c` is zero, the range of `f` reduces to `⊥`. -/
lemma reducesInvariantsTo_bot (hc : S.HasReynolds c) (h : (S.tensorRep c).invariants = ⊥) :
    ReducesInvariantsTo (fun g : G => ρ g) (LinearMap.range f) ⊥ := by
  rw [← Submodule.map_bot f]
  exact hf.reducesInvariantsTo_map hc h.le

include hf in
/-- When the only invariant tensor of `S.Tensor c` is zero, so is every invariant in the range
  of `f`. -/
lemma eq_zero_of_invariant (hc : S.HasReynolds c) (h : (S.tensorRep c).invariants = ⊥)
    {x : B} (hx : x ∈ LinearMap.range f) (hinv : ∀ g : G, ρ g x = x) : x = 0 := by
  obtain ⟨t, ht, rfl⟩ := hf.exists_invariant_eq_of_mem_range hc hx hinv
  rw [Representation.eq_zero_of_invariants_eq_bot h ht, map_zero]

include hf in
/-- When the invariant tensors of `S.Tensor c` are the line through `t₀`, the invariants of the
  range of `f` reduce to the span of `f t₀`. -/
noncomputable def invariantReductionToSpan (hc : S.HasReynolds c) {t₀ : S.Tensor c}
    (h : (S.tensorRep c).invariants = ℂ ∙ t₀) :
    InvariantReductionToSpan (fun g : G => ρ g) (LinearMap.range f) where
  spanningVector := f t₀
  stable := hf.isStableUnder_range
  spanningVector_fixed := hf.rep_map_of_invariant (h.ge (Submodule.mem_span_singleton_self t₀))
  reduce W hW _ hx hinv := by
    obtain ⟨t, ht, y, hy, rfl⟩ := hf.exists_invariant_add_of_mem_sup hc W hW hx hinv
    obtain ⟨a, rfl⟩ := Representation.exists_eq_smul_of_invariants_eq_span h ht
    exact ⟨a, y, hy, by rw [map_smul]⟩

include hf in
/-- The reduction of `invariantReductionToSpan`, stated for a submodule `V` equal to the range of
  `f` and with the spanning vector given by any expression `v` for `f t₀`. -/
noncomputable def invariantReductionToSpanOfEq (hc : S.HasReynolds c) {t₀ : S.Tensor c}
    (h : (S.tensorRep c).invariants = ℂ ∙ t₀) {V : Submodule ℂ B}
    (hV : LinearMap.range f = V) (v : B) (hv : f t₀ = v) :
    InvariantReductionToSpan (fun g : G => ρ g) V where
  spanningVector := v
  stable := hV ▸ hf.isStableUnder_range
  spanningVector_fixed := hv ▸ (hf.invariantReductionToSpan hc h).spanningVector_fixed
  reduce W hW x hx hinv := by
    subst hV hv
    exact (hf.invariantReductionToSpan hc h).reduce W hW x hx hinv

end IsEquivariant

variable {B : Type*} [AddCommGroup B] [Module ℂ B] {ρ : Representation ℂ G B}

/-- With a Reynolds element, the invariants in the range of an intertwining map `f` out of the
  tensors are the images of the invariant tensors. -/
lemma HasReynolds.invariants_inf_range_eq_map (hc : S.HasReynolds c)
    (f : (S.tensorRep c).IntertwiningMap ρ) :
    ρ.invariants ⊓ f.range.toSubmodule = (S.tensorRep c).invariants.map f.toLinearMap :=
  hc.elim fun _ hr => hr.invariants_inf_range_eq_map f

/-- The invariants in the range of an intertwining map `f` out of the tensors are the line through
  `f t₀` when the invariant tensors are the line through `t₀`. -/
lemma HasReynolds.invariants_inf_range_eq_span (hc : S.HasReynolds c) {t₀ : S.Tensor c}
    (h : (S.tensorRep c).invariants = ℂ ∙ t₀) (f : (S.tensorRep c).IntertwiningMap ρ) :
    ρ.invariants ⊓ f.range.toSubmodule = ℂ ∙ f t₀ := by
  rw [hc.invariants_inf_range_eq_map, h, Submodule.map_span, Set.image_singleton]
  rfl

/-- The invariants in the range of an intertwining map `f` out of the tensors are zero when there
  are no invariant tensors but zero. -/
lemma HasReynolds.invariants_inf_range_eq_bot (hc : S.HasReynolds c)
    (h : (S.tensorRep c).invariants = ⊥) (f : (S.tensorRep c).IntertwiningMap ρ) :
    ρ.invariants ⊓ f.range.toSubmodule = ⊥ := by
  rw [hc.invariants_inf_range_eq_map, h, Submodule.map_bot]

end Complex

/-!

## D. Maps from components

-/

section Constr

variable {k : Type} [CommRing k] {C G : Type} [Group G]
  {V : C → Type} [∀ c, AddCommGroup (V c)] [∀ c, Module k (V c)]
  {basisIdx : C → Type} [∀ c, Fintype (basisIdx c)] [∀ c, DecidableEq (basisIdx c)]
  {rep : (c : C) → Representation k G (V c)} {b : (c : C) → Basis (basisIdx c) k (V c)}
  {S : TensorSpecies k C G V basisIdx rep b}

variable {n : ℕ} {c : Fin n → C} {B : Type*} [AddCommGroup B] [Module k B]

/-- The linear map out of `S.Tensor c` sending each basis tensor to the matching component `T φ`
  of a family indexed by the component indices. -/
noncomputable def ofComponents (T : ComponentIdx (S := S) c → B) : S.Tensor c →ₗ[k] B :=
  (Tensor.basis c).constr k T

@[simp]
lemma ofComponents_basis (T : ComponentIdx (S := S) c → B) (φ : ComponentIdx (S := S) c) :
    ofComponents T (Tensor.basis c φ) = T φ := by
  simp [ofComponents]

/-- The range of `ofComponents T` is the span of the components. -/
lemma range_ofComponents (T : ComponentIdx (S := S) c → B) :
    LinearMap.range (ofComponents T) = Submodule.span k (Set.range T) :=
  Module.Basis.constr_range _ _

/-- The range of the map of a family relabelled by an equivalence `e` is the span of the
  family. -/
lemma range_ofComponents_comp {ι : Type*} (e : ComponentIdx (S := S) c ≃ ι) (T : ι → B) :
    LinearMap.range (ofComponents (T ∘ e)) = Submodule.span k (Set.range T) := by
  rw [range_ofComponents, e.surjective.range_comp]

/-- The image of `ofComponents T` lies in every submodule containing the components. -/
lemma ofComponents_mem (T : ComponentIdx (S := S) c → B) {M : Submodule k B}
    (hT : ∀ φ, T φ ∈ M) (t : S.Tensor c) : ofComponents T t ∈ M := by
  have h : LinearMap.range (ofComponents T) ≤ M := by
    rw [range_ofComponents, Submodule.span_le]
    rintro _ ⟨φ, rfl⟩
    exact hT φ
  exact h (LinearMap.mem_range_self _ t)

/-- The image of the map of a family relabelled by an equivalence `e` lies in the span of the
  family. -/
lemma ofComponents_comp_mem_span {ι : Type*} (e : ComponentIdx (S := S) c ≃ ι) (T : ι → B)
    (t : S.Tensor c) : ofComponents (T ∘ e) t ∈ Submodule.span k (Set.range T) := by
  rw [← range_ofComponents_comp e T]
  exact LinearMap.mem_range_self _ t

/-- The image of the map of a relabelled family lies in every submodule containing the
  family. -/
lemma ofComponents_comp_mem {ι : Type*} (e : ComponentIdx (S := S) c ≃ ι) (T : ι → B)
    {M : Submodule k B} (hT : ∀ l, T l ∈ M) (t : S.Tensor c) : ofComponents (T ∘ e) t ∈ M :=
  ofComponents_mem _ (fun φ => hT (e φ)) t

/-- `ofComponents` of a sum of families is the sum of the maps. -/
lemma ofComponents_sum {α : Type*} (s : Finset α) (T : α → ComponentIdx (S := S) c → B) :
    ofComponents (fun φ => ∑ i ∈ s, T i φ) = ∑ i ∈ s, ofComponents (T i) :=
  (Tensor.basis c).ext fun φ => by simp [LinearMap.sum_apply]

/-- `ofComponents` of a difference of families is the difference of the maps. -/
lemma ofComponents_sub (T T' : ComponentIdx (S := S) c → B) :
    ofComponents (fun φ => T φ - T' φ) = ofComponents T - ofComponents T' :=
  (Tensor.basis c).ext fun φ => by simp

/-- A linear map applied after `ofComponents T` is `ofComponents` of its values on the
  components. -/
lemma comp_ofComponents {B' : Type*} [AddCommGroup B'] [Module k B'] (σ : B →ₗ[k] B')
    (T : ComponentIdx (S := S) c → B) :
    σ ∘ₗ ofComponents T = ofComponents fun φ => σ (T φ) :=
  (Tensor.basis c).ext fun φ => by simp

/-- A linear map applied to `ofComponents T t` is `ofComponents` of its values on the components,
  applied to `t`. -/
lemma map_ofComponents {B' : Type*} [AddCommGroup B'] [Module k B'] (σ : B →ₗ[k] B')
    (T : ComponentIdx (S := S) c → B) (t : S.Tensor c) :
    σ (ofComponents T t) = ofComponents (fun φ => σ (T φ)) t :=
  LinearMap.congr_fun (comp_ofComponents σ T) t

/-- `ofComponents` of a sum of relabelled families is the sum of the maps. -/
lemma ofComponents_comp_sum {ι α : Type*} (e : ComponentIdx (S := S) c ≃ ι) (s : Finset α)
    (T : α → ι → B) :
    ofComponents ((fun l => ∑ i ∈ s, T i l) ∘ e) = ∑ i ∈ s, ofComponents (T i ∘ e) :=
  ofComponents_sum s fun i => T i ∘ e

/-- `ofComponents` of a difference of relabelled families is the difference of the maps. -/
lemma ofComponents_comp_sub {ι : Type*} (e : ComponentIdx (S := S) c ≃ ι) (T T' : ι → B) :
    ofComponents ((fun l => T l - T' l) ∘ e) = ofComponents (T ∘ e) - ofComponents (T' ∘ e) :=
  ofComponents_sub (T ∘ e) (T' ∘ e)

/-- A linear map applied to the map of a relabelled family is the map of its values on the
  family. -/
lemma map_ofComponents_comp {ι : Type*} {B' : Type*} [AddCommGroup B'] [Module k B']
    (σ : B →ₗ[k] B') (e : ComponentIdx (S := S) c ≃ ι) (T : ι → B) (t : S.Tensor c) :
    σ (ofComponents (T ∘ e) t) = ofComponents ((fun l => σ (T l)) ∘ e) t :=
  map_ofComponents σ (T ∘ e) t

/-- A linear map moving the components as `g` moves the basis tensors intertwines
  `ofComponents T` with the action of `g`. -/
lemma ofComponents_smul_of_law (T : ComponentIdx (S := S) c → B) {σ : B →ₗ[k] B} (g : G)
    (hσ : ∀ φ, σ (T φ)
      = ∑ ψ, (∏ i, LinearMap.toMatrix (b (c i)) (b (c i)) (rep (c i) g) (ψ i) (φ i)) • T ψ)
    (t : S.Tensor c) :
    σ (ofComponents T t) = ofComponents T (g • t) := by
  have h : σ ∘ₗ ofComponents T = ofComponents T ∘ₗ PiTensorProduct.map (fun i => rep (c i) g) := by
    refine (Tensor.basis (S := S) c).ext fun φ => ?_
    have h1 := smul_basis_eq_sum (S := S) c g φ
    rw [actionT_eq] at h1
    simp only [LinearMap.comp_apply, h1, map_sum, map_smul, ofComponents_basis, hσ]
  exact (LinearMap.congr_fun h t).trans (by rw [actionT_eq]; rfl)

/-- The map of a family is equivariant exactly when the components are moved as the basis
  tensors are, with one matrix entry of `g` per index and the summed index first in each
  factor. -/
lemma isEquivariant_ofComponents_iff {ρ : Representation k G B}
    (T : ComponentIdx (S := S) c → B) :
    S.IsEquivariant c ρ (ofComponents T) ↔ ∀ (g : G) (φ : ComponentIdx (S := S) c), ρ g (T φ)
      = ∑ ψ, (∏ i, LinearMap.toMatrix (b (c i)) (b (c i)) (rep (c i) g) (ψ i) (φ i)) • T ψ := by
  constructor
  · intro hf g φ
    have h := hf.equivariant g (Tensor.basis c φ)
    rw [smul_basis_eq_sum, map_sum] at h
    simpa using h.symm
  · exact fun hT => ⟨fun g t => (ofComponents_smul_of_law T g (hT g) t).symm⟩

/-- The map of a finite sum of families is equivariant when the map of each family is. -/
lemma isEquivariant_ofComponents_sum {ρ : Representation k G B} {α : Type*} (s : Finset α)
    {T : α → ComponentIdx (S := S) c → B} (hT : ∀ i ∈ s, S.IsEquivariant c ρ (ofComponents (T i))) :
    S.IsEquivariant c ρ (ofComponents fun φ => ∑ i ∈ s, T i φ) := by
  rw [ofComponents_sum]
  exact IsEquivariant.sum s hT

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

end Tensor

section TensorRep

open TensorProduct

variable {k : Type} [CommRing k] {C G : Type} [Group G]
  {V : C → Type} [∀ c, AddCommGroup (V c)] [∀ c, Module k (V c)]
  {basisIdx : C → Type} [∀ c, Fintype (basisIdx c)] [∀ c, DecidableEq (basisIdx c)]
  {rep : (c : C) → Representation k G (V c)} {b : (c : C) → Basis (basisIdx c) k (V c)}
  {S : TensorSpecies k C G V basisIdx rep b} {n : ℕ} {c : Fin n → C}

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

/-- The component indices of a tensor with two indices, as the pair of their labels. -/
def pairIdx {c1 c2 : C} : ComponentIdx (S := S) ![c1, c2] ≃ basisIdx c1 × basisIdx c2 where
  toFun φ := (φ 0, φ 1)
  invFun p := fun | 0 => p.1 | 1 => p.2
  left_inv φ := by
    funext i
    fin_cases i <;> rfl
  right_inv p := rfl

/-- The map of a family `T x y` with two indices is equivariant when each index is moved by the
  matrix of `g` in its colour, the summed index first in each factor. -/
lemma isEquivariant_ofComponents_pair {c1 c2 : C} {B : Type*} [AddCommGroup B] [Module k B]
    {ρ : Representation k G B} (T : basisIdx c1 → basisIdx c2 → B)
    (hT : ∀ (g : G) x y, ρ g (T x y) = ∑ x', ∑ y',
      (LinearMap.toMatrix (b c1) (b c1) (rep c1 g) x' x *
        LinearMap.toMatrix (b c2) (b c2) (rep c2 g) y' y) • T x' y') :
    S.IsEquivariant ![c1, c2] ρ (ofComponents ((fun p => T p.1 p.2) ∘ pairIdx)) :=
  (isEquivariant_ofComponents_iff _).2 fun g φ => (hT g (φ 0) (φ 1)).trans <| by
    rw [← pairIdx.symm.sum_comp, Fintype.sum_prod_type]
    simp only [Fin.prod_univ_two]
    rfl

/-- The range of the map of a family `T x y` with two indices is the span of its members. -/
lemma range_ofComponents_pair {c1 c2 : C} {B : Type*} [AddCommGroup B] [Module k B]
    (T : basisIdx c1 → basisIdx c2 → B) :
    LinearMap.range (ofComponents (S := S) ((fun p => T p.1 p.2) ∘ pairIdx))
      = Submodule.span k (Set.range fun m : basisIdx c1 × basisIdx c2 => T m.1 m.2) :=
  range_ofComponents_comp _ _

/-- The invariant tensors with two indices are the line through `fromPairT v` when the invariants
  of the tensor product of the two representations are the line through `v`. -/
lemma invariants_tensorRep_pair_eq_span {c1 c2 : C} {v : V c1 ⊗[k] V c2}
    (h : ((rep c1).tprod (rep c2)).invariants = k ∙ v) :
    (S.tensorRep ![c1, c2]).invariants = k ∙ Tensor.fromPairT v := by
  rw [invariants_tensorRep_eq_map_of_equiv fromPairTEquiv fromPairTEquiv_tprod, h,
    Submodule.map_span, Set.image_singleton]
  rfl

/-- There are no invariant tensors with two indices but zero when the tensor product of the two
  representations has none. -/
lemma invariants_tensorRep_pair_eq_bot {c1 c2 : C} (h : ((rep c1).tprod (rep c2)).invariants = ⊥) :
    (S.tensorRep ![c1, c2]).invariants = ⊥ := by
  rw [invariants_tensorRep_eq_map_of_equiv fromPairTEquiv fromPairTEquiv_tprod, h,
    Submodule.map_bot]

/-- The invariant tensors with three indices are the line through `fromTripleT v` when the
  invariants of the tensor product of the three representations are the line through `v`. -/
lemma invariants_tensorRep_triple_eq_span {c1 c2 c3 : C} {v : V c1 ⊗[k] (V c2 ⊗[k] V c3)}
    (h : ((rep c1).tprod ((rep c2).tprod (rep c3))).invariants = k ∙ v) :
    (S.tensorRep ![c1, c2, c3]).invariants = k ∙ Tensor.fromTripleT v := by
  rw [invariants_tensorRep_eq_map_of_equiv fromTripleTEquiv fromTripleTEquiv_tprod, h,
    Submodule.map_span, Set.image_singleton]
  rfl

end TensorRep

end TensorSpecies
