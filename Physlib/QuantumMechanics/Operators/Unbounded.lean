/-
Copyright (c) 2026 Gregory J. Loges. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann, Gregory J. Loges
-/
module

public import Physlib.Mathematics.InnerProductSpace.Submodule
public import Physlib.Mathematics.LinearPMap
public import Physlib.Meta.TODO.Basic
/-!

# Unbounded operators

## i. Overview

The appropriate mathematical objects for discussing operators in non-relativistic quantum mechanics
are partially-defined linear map (`LinearPMap`) between complex Hilbert spaces, `H →ₗ.[ℂ] H'`.
An import class of operators in NRQM are those which are both densely defined and closable,
which we refer to as _unbounded_. When `H = H'` operators may also be symmetric, self-adjoint or
essentially self-adjoint (closure is self-adjoint).

In this module we collect results on how the properties `HasDenseDomain`, `IsUnbounded`,
`IsSymmetric`, `IsSelfAdjoint` and `IsEssentiallySelfAdjoint` interact with the basic algebraic
operations, closure, adjoints, unitary conjugation and each other.

### Notes

- Naming convention : Definitions of `LinearPMap`s for quantum mechanical unbounded operators should
    have a name of the form `[…]Operator` and notation should use calligraphic capital letters,
    e.g. `mulOperator f` (`𝓜 f`) for the multiplication operator associated with the function `f`.

- Implementation : Although operators encountered in quantum mechanics are almost always unbounded,
    we opt to implement unbounded operators via the property `IsUnbounded` on `LinearPMap` rather
    than as a structure `UnboundedOperator` extending `LinearPMap`. The basic reason for this
    is that addition/subtraction and composition of unbounded operators in general does not result
    in another unbounded operator. This means, for example, that any attempt to define addition of
    `UnboundedOperator`s would inevitably require introducing junk values that spoil associativity.

## ii. Key results

Definitions
- `HasDenseDomain` : An operator `U : H →ₗ.[ℂ] H'` has dense domain if `U.domain` is dense in `H`.
- `IsUnbounded` : An operator is unbounded if it is both densely defined and closable.
- `IsSymmetric` : An operator `T : H →ₗ.[ℂ] H` is symmetric if `⟪T x, y⟫_ℂ = ⟪x, T y⟫_ℂ` holds
    for all `x y : T.domain`.
- `IsEssentiallySelfAdjoint` : An operator `T : H →ₗ.[ℂ] H` is essentially self-adjoint if
    its closure is self-adjoint.

Results
- `adjoint_add_le_add_adjoint` : The inequality `U₁† + U₂† ≤ (U₁ + U₂)†` when `U₁ + U₂` has
    dense domain.
- `unitaryConj` : The conjugation `u A u⁻¹ : H' →ₗ.[ℂ] H'` of `A` by a unitary `u`, with domain
    `u (A.domain)`.
- `IsFormalAdjoint.unitaryConj` : Unitary conjugation preserves formal-adjoint pairs.
- `HasDenseDomain.unitaryConj_dense_domain` : If `A` has dense domain, then so does `u A u⁻¹`.
- `unitaryConj_sub_smul_surjective` : If `A - z` is surjective for a scalar `z : ℂ`,
    then so is `u A u⁻¹ - z`.
- `adjoint_compRestricted_le_compRestricted_adjoint` : The inequality `U† ∘ᵣ V† ≤ (V ∘ᵣ U)†`
    when `V` and `V ∘ᵣ U` have dense domain.
- `IsUnbounded.adjoint` : The adjoint of an unbounded operator is also unbounded.
- `IsUnbounded.adjoint_closure_eq_adjoint` : An unbounded operator and its closure have
    the same adjoint.
- `IsUnbounded.adjoint_adjoint_eq_closure` : An unbounded operator `U` satisfies `U†† = U.closure`.
- `IsEssentiallySelfAdjoint.unique_self_adjoint_extension` : The closure of an essentially
    self-adjoint unbounded operator is its unique self-adjoint extension.

## iii. Table of contents

- A. Definitions
- B. Basic properties
  - B.1. Dense domain
  - B.2. Closability
  - B.3. Adjoints
  - B.4. Continuity / boundedness
  - B.5. Unitary conjugation
- C. Classes of operators
  - C.1. Unbounded operators
  - C.2. Symmetric operators
  - C.3. Self-adjoint operators
  - C.4. Essentially self-adjoint operators

## iv. References

* Reed and Simon, Methods of Modern Mathematical Physics, Vol. I: Functional Analysis.
  [ref: Reed1972]
* Konrad Schmüdgen, Unbounded Self-Adjoint Operators on Hilbert Space. [ref: Schmudgen2012]
-/

TODO "Prove that `IsStarNormal (T : H →ₗ.[ℂ] H)` is equivalent
  to `T.domain = T†.domain` and `‖T x‖ = ‖T† x‖` for all `x ∈ T.domain`."

TODO "Prove basic properties of `IsStarNormal (T : H →ₗ.[ℂ] H)`,
  paralleling those for `IsSelfAdjoint (T : H →ₗ.[ℂ] H)`."

@[expose] public section

namespace LinearPMap

open Submodule
open InnerProductSpace
open InnerProductSpaceSubmodule
open Complex ComplexConjugate

variable
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {H' : Type*} [NormedAddCommGroup H'] [InnerProductSpace ℂ H']
  {H'' : Type*} [NormedAddCommGroup H''] [InnerProductSpace ℂ H'']
  {α : Type*} [Fintype α]
  {T T₁ T₂ : H →ₗ.[ℂ] H} {S : α → H →ₗ.[ℂ] H}
  {U U₁ U₂ : H →ₗ.[ℂ] H'} {W : α → H →ₗ.[ℂ] H'}
  {V V₁ V₂ : H' →ₗ.[ℂ] H''}

/-!
## A. Definitions

See `LinearPMap.instStar` and `LinearPMap.isSelfAdjoint_def` for the definition of `IsSelfAdjoint`
for `LinearPMap`s.
-/

/-- A LinearPMap `U` has dense domain iff `U.domain` is dense in `H`. -/
def HasDenseDomain (U : H →ₗ.[ℂ] H') : Prop := Dense (U.domain : Set H)

lemma hasDenseDomain_def : U.HasDenseDomain ↔ Dense (U.domain : Set H) := Iff.rfl

/-- A LinearPMap is an unbounded operator iff it has dense domain and is closable. -/
def IsUnbounded (U : H →ₗ.[ℂ] H') : Prop := U.HasDenseDomain ∧ U.IsClosable

lemma isUnbounded_def : U.IsUnbounded ↔ U.HasDenseDomain ∧ U.IsClosable := Iff.rfl

/-- A LinearPMap `T` is symmetric iff `⟪T x, y⟫_ℂ = ⟪x, T y⟫_ℂ` for all `x y : T.domain`. -/
def IsSymmetric (T : H →ₗ.[ℂ] H) : Prop := T.IsFormalAdjoint T

lemma isSymmetric_def : T.IsSymmetric ↔ T.IsFormalAdjoint T := Iff.rfl

/-- A LinearPMap is essentially self-adjoint iff its closure is self-adjoint. -/
def IsEssentiallySelfAdjoint [CompleteSpace H] (T : H →ₗ.[ℂ] H) : Prop := IsSelfAdjoint T.closure

lemma isEssentiallySelfAdjoint_def [CompleteSpace H] :
    T.IsEssentiallySelfAdjoint ↔ IsSelfAdjoint T.closure := Iff.rfl

lemma isStarNormal_def [CompleteSpace H] : IsStarNormal T ↔ T† * T = T * T† := isStarNormal_iff _

/-!
## B. Basic properties
-/

/-!
### B.1. Dense domain
-/

lemma HasDenseDomain.isUnbounded_iff_isClosable (h : U.HasDenseDomain) :
    U.IsUnbounded ↔ U.IsClosable :=
  and_iff_right h

lemma HasDenseDomain.closure (h : U.HasDenseDomain) : U.closure.HasDenseDomain :=
  h.mono U.le_closure.1

lemma closure_domain_le_domain_closure (U : H →ₗ.[ℂ] H') : U.closure.domain ≤ U.domain.closure := by
  by_cases h_cl : U.IsClosable
  · intro ψ hψ
    obtain ⟨φ, hψφ⟩ := h_cl.graph_closure_eq_closure_graph ▸ mem_domain_iff.mp hψ
    obtain ⟨b, hb, hb'⟩ := mem_closure_iff_seq_limit.mp hψφ
    refine mem_closure_iff_seq_limit.mpr
      ⟨fun n ↦ (b n).1, fun n ↦ ?_, (nhds_prod_eq (x := ψ) (y := φ) ▸ hb').fst⟩
    simp only [coe_toAddSubmonoid, SetLike.mem_coe, mem_graph_iff, Subtype.exists,
      exists_and_left, exists_eq_left] at hb
    exact (hb n).choose
  · simp [closure_def' h_cl, closure_le.mp]

lemma hasDenseDomain_iff_closure_hasDenseDomain : U.HasDenseDomain ↔ U.closure.HasDenseDomain :=
  ⟨HasDenseDomain.closure, fun h ↦ dense_closure.mp (h.mono U.closure_domain_le_domain_closure)⟩

lemma HasDenseDomain.neg (h : U.HasDenseDomain) : (-U).HasDenseDomain := h

lemma HasDenseDomain.smul (h : U.HasDenseDomain) (c : ℂ) : (c • U).HasDenseDomain := h

lemma HasDenseDomain.add_of_le (h₁ : U₁.HasDenseDomain) (h_le : U₁.domain ≤ U₂.domain) :
    (U₁ + U₂).HasDenseDomain :=
  h₁.mono (by simp [h_le, add_domain])

lemma HasDenseDomain.sub_of_le (h₁ : U₁.HasDenseDomain) (h_le : U₁.domain ≤ U₂.domain) :
    (U₁ - U₂).HasDenseDomain :=
  h₁.mono (by simp [h_le, sub_domain])

lemma HasDenseDomain.sum_of_le
    {E : Submodule ℂ H} (hE : Dense (E : Set H)) (h : ∀ a, E ≤ (W a).domain) :
    (sum W).HasDenseDomain :=
  hE.mono (by simp [sum_domain, h])

lemma HasDenseDomain.pow
    (h : T.HasDenseDomain) (h_range : ∀ x : T.domain, T x ∈ T.domain) (n : ℕ) :
    (T ^ n).HasDenseDomain := by
  apply h.mono
  induction n with
  | zero => simp
  | succ n ih => exact fun x hx ↦ mem_compRestricted_domain_iff.mpr ⟨hx, ih (h_range ⟨x, hx⟩)⟩

lemma pow_hasDenseDomain_of_le
    {n : ℕ} (h : (T ^ n).HasDenseDomain) {k : ℕ} (hle : k ≤ n) : (T ^ k).HasDenseDomain :=
  h.mono <| pow_sub_mul_pow T hle ▸ compRestricted_domain_le _ _

/-- `U.rangeᗮ = U†.ker`

  c.f. `LinearMap.orthogonal_range` and `ContinuousLinearMap.orthogonal_range` -/
lemma HasDenseDomain.orthogonal_range [CompleteSpace H] (h : U.HasDenseDomain) :
    U.toFun.rangeᗮ = U†.toFun.ker.map U†.domain.subtype := by
  ext u
  simp only [mem_orthogonal', Subtype.exists, mem_map, LinearMap.mem_ker, subtype_apply,
    exists_and_right, exists_eq_right, toFun_eq_coe]
  constructor
  · intro h'
    exact ⟨mem_adjoint_domain_of_exists u ⟨0, by simp [h']⟩, adjoint_apply_eq h _ (by simp [h'])⟩
  · intro ⟨hu, hu'⟩ v ⟨x, hxv⟩
    simp [← hxv, ← adjoint_isFormalAdjoint h ⟨u, hu⟩, hu']

/-- `U†.kerᗮ = U.range.closure` -/
lemma HasDenseDomain.orthogonal_adjoint_ker [CompleteSpace H] [CompleteSpace H']
    (h : U.HasDenseDomain) :
    (U†.toFun.ker.map U†.domain.subtype)ᗮ = U.toFun.range.closure :=
  h.orthogonal_range ▸ orthogonal_orthogonal_eq_closure _

/-!
### B.2. Closability
-/

lemma IsClosed.closure_eq (h : U.IsClosed) : U.closure = U :=
  eq_of_eq_graph (h.isClosable.graph_closure_eq_closure_graph ▸ h.submodule_topologicalClosure_eq)

lemma IsClosable.isClosed_iff (h : U.IsClosable) : U.IsClosed ↔ U.closure = U :=
  ⟨IsClosed.closure_eq, fun h' ↦ h' ▸ h.closure_isClosed⟩

/-- A LinearPMap with densely-defined formal adjoint is closable. -/
lemma isClosable_of_exists_dense_formalAdjoint [CompleteSpace H] [CompleteSpace H']
    (h : U.HasDenseDomain) (h_fadj : ∃ U' : H' →ₗ.[ℂ] H, U'.HasDenseDomain ∧ U'.IsFormalAdjoint U) :
    U.IsClosable := by
  have h_adj : U†.HasDenseDomain := by
    obtain ⟨U', hU', hU''⟩ := h_fadj
    exact hU'.mono (hU''.symm.le_adjoint h).1
  use U††
  ext
  rw [adjoint_graph_eq_graph_adjoint h_adj, adjoint_graph_eq_graph_adjoint h,
    mem_submodule_adjoint_adjoint_iff_mem_submoduleToLp_orthogonal_orthogonal,
    orthogonal_orthogonal_eq_closure, mem_submodule_iff_mem_submoduleToLp, submoduleToLp_closure]

/-- A zero LinearPMap (any domain) is closable. -/
lemma isClosable_of_zero (h_zero : ⇑U = 0) : U.IsClosable := by
  use U.graph.topologicalClosure.toLinearPMap
  refine (toLinearPMap_graph_eq _ fun x hx hx₁ ↦ ?_).symm
  obtain ⟨b, hb, hb'⟩ := mem_closure_iff_seq_limit.mp hx
  have hbn : ∀ n, (b n).snd = 0 := fun n ↦ by specialize hb n; simp_all
  rw [nhds_prod_eq, Filter.tendsto_prod_iff'] at hb'
  simp_all

@[aesop safe apply]
lemma IsClosable.smul (h : U.IsClosable) (c : ℂ) : (c • U).IsClosable := by
  rcases eq_zero_or_neZero c with (rfl | hc)
  · exact isClosable_of_zero (by simp)
  · use (c • U).graph.topologicalClosure.toLinearPMap
    refine (toLinearPMap_graph_eq _ fun x hx hx₁ ↦ ?_).symm
    rw [← smul_zero c, ← inv_smul_eq_iff₀ hc.ne]
    refine graph_fst_eq_zero_snd U.closure ?_ rfl
    rw [← h.graph_closure_eq_closure_graph]
    apply mem_closure_iff_seq_limit.mpr
    obtain ⟨b, hb, hb'⟩ := mem_closure_iff_seq_limit.mp hx
    use fun n ↦ ((b n).fst, c⁻¹ • (b n).snd)
    rw [nhds_prod_eq, Filter.tendsto_prod_iff'] at *
    refine ⟨fun n ↦ ?_, hx₁ ▸ hb'.1, hb'.2.const_smul c⁻¹⟩
    obtain ⟨u, hu, hu'⟩ := hb n
    simp only [coe_toAddSubmonoid, SetLike.mem_coe, mem_graph_iff, Subtype.exists, ← hu']
    exact ⟨u.1, u.1.2, rfl, ((inv_smul_eq_iff₀ hc.ne).mpr hu).symm⟩

lemma IsClosable.smul_iff {c : ℂ} (hc : c ≠ 0) : (c • U).IsClosable ↔ U.IsClosable :=
  ⟨fun h ↦ one_smul ℂ U ▸ inv_mul_cancel₀ hc ▸ smul_smul c⁻¹ c U ▸ h.smul c⁻¹, fun h ↦ h.smul c⟩

lemma neg_eq_neg_one_smul (U : H →ₗ.[ℂ] H') : -U = (-1 : ℂ) • U := ext (by simp) (by simp)

@[aesop safe apply]
lemma IsClosable.neg (h : U.IsClosable) : (-U).IsClosable := neg_eq_neg_one_smul U ▸ h.smul _

lemma closure_smul (U : H →ₗ.[ℂ] H') {c : ℂ} (hc : c ≠ 0) : (c • U).closure = c • U.closure := by
  by_cases h : U.IsClosable
  · apply eq_of_eq_graph
    ext ⟨x₁, x₂⟩
    simp only [← (h.smul c).graph_closure_eq_closure_graph, smul_graph, ← SetLike.mem_coe,
      topologicalClosure_coe, map_coe, LinearMap.prodMap_apply, LinearMap.id_coe, id_eq,
      LinearMap.smul_apply, mem_closure_iff_seq_limit, Set.mem_image, Prod.exists, nhds_prod_eq,
      Filter.tendsto_prod_iff', ← h.graph_closure_eq_closure_graph, Prod.mk.injEq,
      (eq_inv_smul_iff₀ hc).symm, exists_eq_right_right, exists_eq_right]
    constructor <;> intro ⟨b, hb, hb₁, hb₂⟩
    · refine ⟨fun n ↦ ⟨(b n).1, c⁻¹ • (b n).2⟩, fun n ↦ ?_, hb₁, hb₂.const_smul c⁻¹⟩
      obtain ⟨u, v, huv, huv'⟩ := hb n
      have hu := mem_domain_of_mem_graph huv
      use ⟨⟨u, hu⟩, v⟩
      simp [← huv', smul_smul, inv_mul_cancel₀ hc, (image_iff hu).mpr huv]
    · refine ⟨fun n ↦ ⟨(b n).1, c • (b n).2⟩, fun n ↦ ?_, hb₁, ?_⟩
      · obtain ⟨u, hu, hu'⟩ := hb n
        exact ⟨u.1, u.2, by simp_all, by simp [← hu']⟩
      · exact one_smul ℂ x₂ ▸ mul_inv_cancel₀ hc ▸ smul_smul c c⁻¹ x₂ ▸ hb₂.const_smul c
  · rw [closure_def' h, closure_def' <| (not_congr <| IsClosable.smul_iff hc).mpr h]

/-!
### B.3. Adjoints
-/

@[simp]
lemma adjoint_one [CompleteSpace H] : (1 : H →ₗ.[ℂ] H)† = 1 := by
  ext x
  · simp only [one_domain, mem_top, iff_true]
    exact mem_adjoint_domain_of_exists _ ⟨x, fun _ ↦ rfl⟩
  · exact adjoint_apply_eq dense_univ _ fun _ ↦ rfl

/-- The adjoint of a zero LinearPMap (any domain) is zero (domain `⊤`). -/
lemma adjoint_of_zero [CompleteSpace H] (h_zero : ⇑U = 0) : U† = 0 := by
  refine dExt ?_ fun x y hxy ↦ ?_
  · ext
    simp only [zero_domain, mem_top, iff_true]
    exact (mem_adjoint_domain_iff _ _).mpr (continuous_of_const (by simp [h_zero]))
  · by_cases h : U.HasDenseDomain
    · exact adjoint_apply_eq h x (by simp [h_zero])
    · exact adjoint_apply_of_not_dense h x

@[simp]
lemma adjoint_zero [CompleteSpace H] : (0 : H →ₗ.[ℂ] H')† = 0 := adjoint_of_zero rfl

@[simp]
lemma adjoint_smul [CompleteSpace H] (U : H →ₗ.[ℂ] H') {c : ℂ} (hc : c ≠ 0) :
    (c • U)† = conj c • U† := by
  refine dExt ?_ fun x y hxy ↦ ?_
  · ext x
    change Continuous (fun w ↦ ⟪x, c • U w⟫_ℂ) ↔ Continuous (fun w ↦ ⟪x, U w⟫_ℂ)
    exact Iff.trans (by simp [inner_smul_right]) (continuous_const_smul_iff₀ hc)
  · by_cases h : U.HasDenseDomain
    · refine adjoint_apply_eq (smul_domain c U ▸ h) x fun w ↦ ?_
      simp [inner_smul_left, inner_smul_right, adjoint_isFormalAdjoint h y w, hxy]
    · simp [adjoint_apply_of_not_dense h y, adjoint_apply_of_not_dense (smul_domain c U ▸ h) x]

@[simp]
lemma adjoint_neg [CompleteSpace H] (U : H →ₗ.[ℂ] H') : (-U)† = -U† := by
  simp [neg_eq_neg_one_smul, adjoint_smul]

lemma adjoint_antitone [CompleteSpace H]
    (h₁₂ : U₁.HasDenseDomain ∨ ¬U₂.HasDenseDomain) (h_le : U₁ ≤ U₂) : U₂† ≤ U₁† := by
  have h_agree : ∀ w : U₁.domain, U₁ w = U₂ ⟨w, h_le.1 w.2⟩ := fun w ↦ @h_le.2 w ⟨w, h_le.1 w.2⟩ rfl
  constructor
  · intro v
    let f₁ : U₁.domain → ℂ := fun w ↦ ⟪v, U₁ w⟫_ℂ
    let f₂ : U₂.domain → ℂ := fun w ↦ ⟪v, U₂ w⟫_ℂ
    change Continuous f₂ → Continuous f₁
    suffices f₁ = fun w : U₁.domain ↦ f₂ ⟨w, h_le.1 w.2⟩ by rw [this]; fun_prop
    simp [f₁, f₂, h_agree]
  · intro u v huv
    rcases h₁₂ with (h₁ | h₂)
    · have h₂ : U₂.HasDenseDomain := h₁.mono h_le.1
      refine (adjoint_apply_eq h₁ v fun w ↦ ?_).symm
      rw [adjoint_isFormalAdjoint h₂ u ⟨w, h_le.1 w.2⟩, h_agree, huv]
    · have h₁ : ¬U₁.HasDenseDomain := fun h ↦ h₂ (h.mono h_le.1)
      rw [adjoint_apply_of_not_dense h₁ v, adjoint_apply_of_not_dense h₂ u]

lemma adjoint_add_le_add_adjoint [CompleteSpace H]
    (U₁ U₂ : H →ₗ.[ℂ] H') (h₁₂ : (U₁ + U₂).HasDenseDomain) : U₁† + U₂† ≤ (U₁ + U₂)† := by
  have h₁ : U₁.HasDenseDomain := h₁₂.mono Set.inter_subset_left
  have h₂ : U₂.HasDenseDomain := h₁₂.mono Set.inter_subset_right
  constructor
  · intro u hu
    refine mem_adjoint_domain_of_exists _ ⟨U₁† ⟨u, hu.1⟩ + U₂† ⟨u, hu.2⟩, fun x ↦ ?_⟩
    simp only [add_apply, inner_add_left, inner_add_right,
      adjoint_isFormalAdjoint h₁ ⟨u, hu.1⟩ ⟨x, x.2.1⟩,
      adjoint_isFormalAdjoint h₂ ⟨u, hu.2⟩ ⟨x, x.2.2⟩]
  · intro u v huv
    refine (adjoint_apply_eq h₁₂ _ fun w ↦ ?_).symm
    simp only [add_apply, inner_add_left, inner_add_right, ← huv,
      adjoint_isFormalAdjoint h₁ ⟨u, u.2.1⟩ ⟨w, w.2.1⟩,
      adjoint_isFormalAdjoint h₂ ⟨u, u.2.2⟩ ⟨w, w.2.2⟩]

lemma adjoint_sub_le_sub_adjoint [CompleteSpace H]
    (U₁ U₂ : H →ₗ.[ℂ] H') (h₁₂ : (U₁ - U₂).HasDenseDomain) : U₁† - U₂† ≤ (U₁ - U₂)† := by
  simp only [sub_eq_add_neg, ← adjoint_neg]
  exact adjoint_add_le_add_adjoint U₁ (-U₂) h₁₂

lemma adjoint_compRestricted_le_compRestricted_adjoint [CompleteSpace H] [CompleteSpace H']
    (hV : V.HasDenseDomain) (hVU : (V ∘ᵣ U).HasDenseDomain) : U† ∘ᵣ V† ≤ (V ∘ᵣ U)† := by
  have hU : U.HasDenseDomain := hVU.mono (compRestricted_domain_le V U)
  have h : (U† ∘ᵣ V†).IsFormalAdjoint (V ∘ᵣ U) := by
    intro x y
    have hx := mem_domain_of_mem_compRestricted_domain x
    have hy := mem_domain_of_mem_compRestricted_domain y
    trans ⟪V† ⟨x, x.2.2⟩, U ⟨y, y.2.2⟩⟫_ℂ
    · exact adjoint_isFormalAdjoint hU ⟨V† ⟨x, x.2.2⟩, hx⟩ ⟨y, y.2.2⟩
    exact adjoint_isFormalAdjoint hV ⟨x, x.2.2⟩ ⟨U ⟨y, y.2.2⟩, hy⟩
  exact ⟨fun x hx ↦ mem_adjoint_domain_of_exists _ ⟨(U† ∘ᵣ V†) ⟨x, hx⟩, h ⟨x, hx⟩⟩,
    fun x y hxy ↦ (adjoint_apply_eq hVU y <| hxy ▸ h x).symm⟩

lemma adjoint_pow_le_pow_adjoint [CompleteSpace H] {n : ℕ} (h : (T ^ n).HasDenseDomain) :
    T† ^ n ≤ (T ^ n)† := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hTn : (T ^ n).HasDenseDomain := pow_hasDenseDomain_of_le h n.le_succ
    refine le_trans ?_ (adjoint_compRestricted_le_compRestricted_adjoint hTn h)
    exact pow_succ' T† n ▸ compRestricted_mono_right T† (ih hTn)

/-!
### B.4. Continuity / boundedness
-/

/-- `f : E →ₗ[𝕜] F` is continuous iff there exists `M > 0` s.t. `‖f x‖ ≤ M * ‖x‖` for all `x : E`.

  This is a (convenient) immediate consequence of
  `IsBoundedLinearMap.isLinearMap_and_continuous_iff_isBoundedLinearMap`. -/
lemma _root_.LinearMap.continuous_iff_bounded {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
    [SeminormedAddCommGroup E] [NormedSpace 𝕜 E] [SeminormedAddCommGroup F] [NormedSpace 𝕜 F]
    {f : E →ₗ[𝕜] F} : Continuous f ↔ ∃ M, 0 < M ∧ ∀ x : E, ‖f x‖ ≤ M * ‖x‖ := by
  refine (and_congr_right_iff (a := IsLinearMap 𝕜 f)).mp ?_ f.isLinear
  rw [← isBoundedLinearMap_iff]
  exact IsBoundedLinearMap.isLinearMap_and_continuous_iff_isBoundedLinearMap f

/-- Continuous operators are closable. -/
lemma isClosable_of_continuous (h : Continuous U) : U.IsClosable := by
  use U.graph.topologicalClosure.toLinearPMap
  refine (toLinearPMap_graph_eq _ fun x hx hx₁ ↦ ?_).symm
  obtain ⟨b, hb, hbx⟩ := mem_closure_iff_seq_limit.mp hx
  rw [nhds_prod_eq] at hbx
  refine norm_eq_zero.mp (tendsto_nhds_unique hbx.snd.norm ?_)
  obtain ⟨M, hM, h_bound⟩ := LinearMap.continuous_iff_bounded.mp h
  refine squeeze_zero (g := fun n ↦ M * ‖(b n).1‖) (fun _ ↦ norm_nonneg _) (fun n ↦ ?_) ?_
  · obtain ⟨y, hy₁, hy₂⟩ := (mem_graph_iff _).mp (hb n)
    simp only [← hy₁, ← hy₂]
    exact h_bound y
  · exact mul_zero M ▸ (norm_eq_zero.mpr hx₁) ▸ hbx.fst.norm.const_mul M

/-- A strengthening of `closure_domain_le_domain_closure` for continuous operators. -/
lemma closure_domain_eq_domain_closure_of_continuous [CompleteSpace H'] (h : Continuous U) :
    U.closure.domain = U.domain.closure := by
  refine eq_of_le_of_ge U.closure_domain_le_domain_closure fun x hx ↦ ?_
  obtain ⟨M, hM, h_bound⟩ := LinearMap.continuous_iff_bounded.mp h
  obtain ⟨b, hb, hb'⟩ := mem_closure_iff_seq_limit.mp hx
  simp only [coe_toAddSubmonoid, SetLike.mem_coe] at hb
  let Ub : ℕ → H' := fun n ↦ U ⟨b n, hb n⟩
  have hCS : CauchySeq Ub := by
    refine Metric.cauchySeq_iff'.mpr fun ε hε ↦ ?_
    obtain ⟨N, hN⟩ := Metric.cauchySeq_iff'.mp hb'.cauchySeq (M⁻¹ * ε) (by positivity)
    refine ⟨N, fun n hn ↦ ?_⟩
    refine lt_of_le_of_lt ?_ ((lt_inv_mul_iff₀ hM).mp (hN n hn))
    calc
      _ = ‖Ub n - Ub N‖ := dist_eq_norm _ _
      _ = ‖U (⟨b n, hb n⟩ - ⟨b N, hb N⟩)‖ := by simp [Ub, map_sub]
      _ ≤ M * ‖b n - b N‖ := h_bound _
      _ = M * dist (b n) (b N) := by rw [dist_eq_norm]
  obtain ⟨y, hy⟩ := CompleteSpace.complete hCS
  apply mem_domain_iff.mpr
  rw [← (isClosable_of_continuous h).graph_closure_eq_closure_graph]
  use y
  refine mem_closure_iff_seq_limit.mpr ⟨fun n ↦ (b n, Ub n), fun n ↦ ?_, ?_⟩
  · simp [hb n, Ub]
  · rw [nhds_prod_eq]
    exact Filter.Tendsto.prodMk hb' hy

/-- A continuous operator is closed iff its domain is closed. -/
lemma isClosed_iff_isClosed_domain_of_continuous [CompleteSpace H'] (h : Continuous U) :
    U.IsClosed ↔ _root_.IsClosed (U.domain : Set H) := by
  rw [(isClosable_of_continuous h).isClosed_iff]
  have h_domain := closure_domain_eq_domain_closure_of_continuous h
  constructor <;> intro hcl
  · exact hcl ▸ h_domain ▸ isClosed_closure
  · refine (eq_of_le_of_domain_eq U.le_closure ?_).symm
    exact h_domain ▸ hcl.submodule_topologicalClosure_eq.symm

lemma IsClosed.isClosed_toFun_graph (hU : U.IsClosed) :
    _root_.IsClosed (U.toFun.graph : Set (U.domain × H')) := by
  refine isClosed_of_closure_subset fun ⟨x₁, x₂⟩ hx ↦ ?_
  simp only [SetLike.mem_coe, LinearMap.mem_graph_iff, toFun_eq_coe]
  suffices (↑x₁, x₂) ∈ U.graph.topologicalClosure by
    simp_all [hU.isClosable.graph_closure_eq_closure_graph, hU.closure_eq]
  obtain ⟨b, hb, hbx⟩ := mem_closure_iff_seq_limit.mp hx
  apply mem_closure_iff_seq_limit.mpr
  rw [nhds_prod_eq] at *
  refine ⟨fun n ↦ (↑(b n).1, (b n).2), by simp_all,
    Filter.Tendsto.prodMk (tendsto_subtype_rng.mp hbx.fst) hbx.snd⟩

/-- The **closed graph theorem** for partial linear maps:
  a closed operator with closed domain is continuous.

  This follows immediately from `LinearMap.continuous_of_isClosed_graph`
  and the completeness of `H` and `H'`. -/
lemma IsClosed.continuous_of_isClosed_domain [CompleteSpace H] [CompleteSpace H']
    (hU : U.IsClosed) (h : _root_.IsClosed (U.domain : Set H)) :
    Continuous U := by
  have : CompleteSpace U.domain := instCompleteSpaceSubtypeMemSubmoduleOfIsClosedCoe U.domain
  exact LinearMap.continuous_of_isClosed_graph U.toFun hU.isClosed_toFun_graph

/-- Closability is preserved upon adding a continuous operator. -/
lemma IsClosable.add_continuous
    (h₁ : U₁.IsClosable) (h₂ : Continuous U₂) (h : U₁.domain ≤ U₂.domain) :
    (U₁ + U₂).IsClosable := by
  use (U₁ + U₂).graph.topologicalClosure.toLinearPMap
  refine (toLinearPMap_graph_eq _ fun ⟨x₁, x₂⟩ hx hx₁ ↦ ?_).symm
  subst hx₁
  refine graph_fst_eq_zero_snd U₁.closure ?_ rfl
  rw [← h₁.graph_closure_eq_closure_graph]
  apply mem_closure_iff_seq_limit.mpr
  obtain ⟨b, hb, hbx⟩ := mem_closure_iff_seq_limit.mp hx
  simp only [coe_toAddSubmonoid, SetLike.mem_coe, mem_graph_iff, add_domain, add_apply,
    Subtype.exists, exists_and_left, exists_eq_left, nhds_prod_eq] at *
  refine ⟨fun n ↦ ((b n).1, (b n).2 - U₂ ⟨(b n).1, h (hb n).choose.1⟩), fun n ↦ ?_, ?_⟩
  · exact ⟨(hb n).choose.1, eq_sub_of_add_eq (hb n).choose_spec⟩
  · refine Filter.Tendsto.prodMk hbx.fst ?_
    refine sub_zero x₂ ▸ hbx.snd.sub ?_
    exact map_zero U₂ ▸ (h₂.tendsto 0).comp (tendsto_subtype_rng.mpr hbx.fst)

/-- Closability is preserved upon subtracting a continuous operator. -/
lemma IsClosable.sub_continuous
    (h₁ : U₁.IsClosable) (h₂ : Continuous U₂) (h : U₁.domain ≤ U₂.domain) : (U₁ - U₂).IsClosable :=
  sub_eq_add_neg U₁ U₂ ▸ h₁.add_continuous h₂.neg h

/-- Closedness is preserved upon adding a continuous operator. -/
lemma IsClosed.add_continuous [CompleteSpace H']
    (h₁ : U₁.IsClosed) (h₂ : Continuous U₂) (h : U₁.domain ≤ U₂.domain) : (U₁ + U₂).IsClosed := by
  have hcl : (U₁ + U₂).IsClosable := h₁.isClosable.add_continuous h₂ h
  refine hcl.isClosed_iff.mpr (eq_of_le_of_ge (le_of_le_graph ?_) (U₁ + U₂).le_closure)
  rw [← hcl.graph_closure_eq_closure_graph]
  intro ⟨x₁, x₂⟩ hx
  obtain ⟨b, hb, hbx⟩ := mem_closure_iff_seq_limit.mp hx
  simp only [coe_toAddSubmonoid, SetLike.mem_coe, mem_graph_iff, Subtype.exists, exists_and_left,
    exists_eq_left, add_domain, inf_of_le_left h] at hb
  rw [nhds_prod_eq] at hbx
  have hb₁U₂ : ∀ n, (b n).1 ∈ U₂.domain := fun n ↦ h (hb n).choose
  have hCS : CauchySeq fun n ↦ U₂ ⟨(b n).1, hb₁U₂ n⟩ := by
    obtain ⟨M, hM, h_bound⟩ := LinearMap.continuous_iff_bounded.mp h₂
    refine Metric.cauchySeq_iff'.mpr fun ε hε ↦ ?_
    obtain ⟨N, hN⟩ := Metric.cauchySeq_iff'.mp hbx.fst.cauchySeq (M⁻¹ * ε) (by positivity)
    refine ⟨N, fun n hn ↦ ?_⟩
    calc
      _ = ‖U₂ (⟨(b n).1, hb₁U₂ n⟩ - ⟨(b N).1, hb₁U₂ N⟩)‖ := by rw [map_sub, dist_eq_norm]
      _ ≤ M * ‖(b n).1 - (b N).1‖ := h_bound _
      _ < ε := dist_eq_norm (b n).1 (b N).1 ▸ (lt_inv_mul_iff₀ hM).mp (hN n hn)
  obtain ⟨y, hy⟩ := CompleteSpace.complete hCS
  have hU₁ : (x₁, x₂ - y) ∈ U₁.graph := by
    rw [← h₁.closure_eq, ← h₁.isClosable.graph_closure_eq_closure_graph]
    apply mem_closure_iff_seq_limit.mpr
    refine ⟨fun n ↦ ((b n).1, (b n).2 - U₂ ⟨(b n).1, hb₁U₂ n⟩), fun n ↦ ?_, ?_⟩
    · simp_all [add_apply, eq_sub_iff_add_eq]
    · rw [nhds_prod_eq]
      exact hbx.fst.prodMk (hbx.snd.sub hy)
  have hx₁ : x₁ ∈ U₁.domain := mem_domain_of_mem_graph hU₁
  have hU₂y : U₂ ⟨x₁, h hx₁⟩ = y := by
    refine tendsto_nhds_unique ((h₂.tendsto ⟨x₁, h hx₁⟩).comp ?_) (Filter.tendsto_map'_iff.mp hy)
    exact tendsto_subtype_rng.mpr hbx.fst
  simp_all [add_domain, add_apply]

/-- Closedness is preserved upon subtracting a continuous operator. -/
lemma IsClosed.sub_continuous [CompleteSpace H']
    (h₁ : U₁.IsClosed) (h₂ : Continuous U₂) (h : U₁.domain ≤ U₂.domain) : (U₁ - U₂).IsClosed :=
  sub_eq_add_neg U₁ U₂ ▸ h₁.add_continuous h₂.neg h

lemma adjoint_domain_of_continuous [CompleteSpace H] (h : Continuous U) : U†.domain = ⊤ := by
  ext
  simp only [mem_top, iff_true, mem_adjoint_domain_iff, LinearMap.coe_comp, coe_innerₛₗ_apply]
  exact Continuous.comp (by fun_prop) h

lemma HasDenseDomain.adjoint_add_continuous [CompleteSpace H]
    (h₁ : T₁.HasDenseDomain) (h₂ : Continuous T₂) (h : T₁.domain ≤ T₂.domain) :
    (T₁ + T₂)† = T₁† + T₂† := by
  have h₂' : T₂†.domain = ⊤ := adjoint_domain_of_continuous h₂
  have h₁₂ : (T₁ + T₂).HasDenseDomain := h₁.mono <| by simp [add_domain, h]
  refine (eq_of_le_of_domain_eq ?_ ?_).symm
  · exact adjoint_add_le_add_adjoint T₁ T₂ h₁₂
  · ext x
    simp only [add_domain, h₂', inf_top_eq]
    constructor <;> intro h'
    · apply mem_adjoint_domain_of_exists
      use T₁† ⟨x, h'⟩ + T₂† ⟨x, h₂' ▸ mem_top⟩
      intro y
      simp [add_apply, inner_add_left, inner_add_right,
        adjoint_isFormalAdjoint h₁ ⟨x, h'⟩ ⟨y, y.2.1⟩,
        adjoint_isFormalAdjoint (h₁.mono h) ⟨x, h₂' ▸ mem_top⟩ ⟨y, y.2.2⟩]
    · apply mem_adjoint_domain_of_exists
      use (T₁ + T₂)† ⟨x, h'⟩ - T₂† ⟨x, h₂' ▸ mem_top⟩
      intro y
      simp [add_apply, inner_add_right, inner_sub_left,
        adjoint_isFormalAdjoint h₁₂ ⟨x, h'⟩ ⟨y, ⟨y.2, h y.2⟩⟩,
        adjoint_isFormalAdjoint (h₁.mono h) ⟨x, h₂' ▸ mem_top⟩ ⟨y, h y.2⟩]

lemma HasDenseDomain.adjoint_sub_continuous [CompleteSpace H]
    (h₁ : T₁.HasDenseDomain) (h₂ : Continuous T₂) (h : T₁.domain ≤ T₂.domain) :
    (T₁ - T₂)† = T₁† - T₂† := by
  simp only [sub_eq_add_neg, ← adjoint_neg]
  exact h₁.adjoint_add_continuous (continuous_neg_iff.mpr h₂) h

/-!
### B.5. Unitary conjugation
-/

variable (u : H ≃ₗᵢ[ℂ] H') (A : H →ₗ.[ℂ] H)

/-- The conjugation `u A u⁻¹` of a partially-defined operator `A : H →ₗ.[ℂ] H` by a unitary
`u : H ≃ₗᵢ[ℂ] H'`, with domain `u (A.domain) = u⁻¹ ⁻¹' (A.domain)` and action
`y ↦ u (A (u⁻¹ y))`. Since `u` and `u⁻¹` are `ℂ`-linear, the result is again `ℂ`-linear. -/
def unitaryConj : H' →ₗ.[ℂ] H' where
  domain := A.domain.comap (u.symm.toLinearEquiv : H' →ₗ[ℂ] H)
  toFun := u.toLinearEquiv.toLinearMap.comp <| A.toFun.comp
    (((u.symm.toLinearEquiv : H' →ₗ[ℂ] H).comp
      (A.domain.comap (u.symm.toLinearEquiv : H' →ₗ[ℂ] H)).subtype).codRestrict A.domain
        fun x => x.2)

/-- Membership in the conjugated domain: `x ∈ D(u A u⁻¹) ↔ u⁻¹ x ∈ D(A)`. -/
lemma mem_unitaryConj_domain_iff {x : H'} :
    x ∈ (unitaryConj u A).domain ↔ u.symm x ∈ A.domain := Iff.rfl

/-- The defining formula `(u A u⁻¹) x = u (A (u⁻¹ x))`. -/
lemma unitaryConj_apply (x : (unitaryConj u A).domain) :
    unitaryConj u A x = u (A ⟨u.symm (x : H'), (mem_unitaryConj_domain_iff u A).mp x.2⟩) := rfl

/-- `u` maps `D(A)` into `D(u A u⁻¹)`. -/
lemma map_mem_unitaryConj_domain (y : A.domain) : u (y : H) ∈ (unitaryConj u A).domain := by
  simpa only [mem_unitaryConj_domain_iff, u.symm_apply_apply] using y.2

/-- The action on the image domain: `(u A u⁻¹)(u y) = u (A y)` for `y ∈ D(A)`. -/
lemma unitaryConj_apply_map (y : A.domain) :
    unitaryConj u A ⟨u (y : H), map_mem_unitaryConj_domain u A y⟩ = u (A y) := by
  simp only [unitaryConj_apply, u.symm_apply_apply]

/-- Unitary conjugation is monotone for the extension order on partial linear maps. -/
lemma unitaryConj_mono (u : H ≃ₗᵢ[ℂ] H') {A B : H →ₗ.[ℂ] H} (h : A ≤ B) :
    unitaryConj u A ≤ unitaryConj u B :=
  ⟨fun _ hx => h.1 hx, fun x y hxy =>
    congrArg u (h.2 (x := ⟨u.symm ↑x, x.2⟩) (y := ⟨u.symm ↑y, y.2⟩) (congrArg u.symm hxy))⟩

/-- Conjugating by `u` and then by `u⁻¹` recovers the original operator. -/
@[simp]
lemma unitaryConj_symm_unitaryConj (u : H ≃ₗᵢ[ℂ] H') (A : H →ₗ.[ℂ] H) :
    unitaryConj u.symm (unitaryConj u A) = A := by
  ext x hx hx'
  · simp [mem_unitaryConj_domain_iff]
  · simp [unitaryConj_apply]

/-- Conjugating by `u⁻¹` and then by `u` recovers the original operator. -/
@[simp]
lemma unitaryConj_unitaryConj_symm (u : H ≃ₗᵢ[ℂ] H') (B : H' →ₗ.[ℂ] H') :
    unitaryConj u (unitaryConj u.symm B) = B := unitaryConj_symm_unitaryConj u.symm B

variable {u A}

open scoped InnerProductSpace in
/-- Unitary conjugation preserves formal adjointness. If `A` is a formal adjoint of `B`, then
`u A u⁻¹` is a formal adjoint of `u B u⁻¹`. Unitary conjugation preserves symmetry when `A = B`. -/
lemma IsFormalAdjoint.unitaryConj {B : H →ₗ.[ℂ] H} (h : A.IsFormalAdjoint B) :
    (unitaryConj u A).IsFormalAdjoint (unitaryConj u B) := by
  intro x y
  let x' : A.domain := ⟨u.symm (x : H'), (mem_unitaryConj_domain_iff u A).mp x.2⟩
  let y' : B.domain := ⟨u.symm (y : H'), (mem_unitaryConj_domain_iff u B).mp y.2⟩
  calc ⟪LinearPMap.unitaryConj u A x, (y : H')⟫_ℂ
      = ⟪A x', (y' : H)⟫_ℂ := u.inner_map_eq_flip _ _
    _ = ⟪(x' : H), B y'⟫_ℂ := h x' y'
    _ = ⟪(x : H'), LinearPMap.unitaryConj u B y⟫_ℂ := u.symm.inner_map_eq_flip _ _

/-- If `A` has dense domain, then so does `u A u⁻¹`: the domain `u⁻¹ ⁻¹' (A.domain)` is the
preimage of a dense set under a homeomorphism. -/
lemma HasDenseDomain.unitaryConj_dense_domain (hdense : A.HasDenseDomain) :
    (unitaryConj u A).HasDenseDomain := hdense.preimage u.symm.toHomeomorph.isOpenMap

/-- The conjugated operator `u A u⁻¹` is densely defined iff `A` is: its domain is the preimage
of `D(A)` under the homeomorphism `u⁻¹`. -/
@[simp]
lemma unitaryConj_hasDenseDomain_iff :
    (unitaryConj u A).HasDenseDomain ↔ A.HasDenseDomain :=
  ⟨fun h ↦ by simpa using h.unitaryConj_dense_domain (u := u.symm),
   fun h ↦ h.unitaryConj_dense_domain⟩

/-- Unitary conjugation commutes with the adjoint: `(u A u⁻¹)† = u A† u⁻¹`. -/
@[simp]
lemma unitaryConj_adjoint [CompleteSpace H] [CompleteSpace H'] (u : H ≃ₗᵢ[ℂ] H') :
    (unitaryConj u A)† = unitaryConj u A† := by
  by_cases hdense : A.HasDenseDomain
  · have hd' : (unitaryConj u A).HasDenseDomain := hdense.unitaryConj_dense_domain
    refine le_antisymm ?_ (((adjoint_isFormalAdjoint hdense).symm.unitaryConj).le_adjoint hd')
    have h₁ : unitaryConj u.symm ((unitaryConj u A)†) ≤ (unitaryConj u.symm (unitaryConj u A))† :=
      ((adjoint_isFormalAdjoint hd').symm.unitaryConj).le_adjoint hd'.unitaryConj_dense_domain
    rw [unitaryConj_symm_unitaryConj] at h₁
    have h₂ := unitaryConj_mono u h₁
    rwa [unitaryConj_unitaryConj_symm] at h₂
  · have hnd : ¬(unitaryConj u A).HasDenseDomain :=
      fun hc ↦ hdense (unitaryConj_hasDenseDomain_iff.mp hc)
    refine dExt ?_ fun x y hxy ↦ ?_
    · ext ξ
      change Continuous (fun w : (unitaryConj u A).domain ↦ ⟪ξ, unitaryConj u A w⟫_ℂ)
        ↔ Continuous (fun w : A.domain ↦ ⟪u.symm ξ, A w⟫_ℂ)
      constructor
      · intro hc
        suffices hfun : (fun w : A.domain ↦ ⟪u.symm ξ, A w⟫_ℂ)
            = (fun w : (unitaryConj u A).domain ↦ ⟪ξ, unitaryConj u A w⟫_ℂ)
              ∘ fun w : A.domain ↦ (⟨u ↑w, map_mem_unitaryConj_domain u A w⟩ :
                (unitaryConj u A).domain) by
          rw [hfun]
          exact hc.comp ((u.continuous.comp continuous_subtype_val).subtype_mk _)
        funext w
        simp [unitaryConj_apply_map, u.symm.inner_map_eq_flip]
      · intro hc
        suffices hfun : (fun w : (unitaryConj u A).domain ↦ ⟪ξ, unitaryConj u A w⟫_ℂ)
            = (fun w : A.domain ↦ ⟪u.symm ξ, A w⟫_ℂ)
              ∘ fun w : (unitaryConj u A).domain ↦ (⟨u.symm ↑w, w.2⟩ : A.domain) by
          rw [hfun]
          exact hc.comp ((u.symm.continuous.comp continuous_subtype_val).subtype_mk _)
        funext w
        simp [unitaryConj_apply, u.symm.inner_map_eq_flip]
    · simp [adjoint_apply_of_not_dense hnd x, unitaryConj_apply,
        adjoint_apply_of_not_dense hdense]

/-- If `A - z` is surjective for a scalar `z : ℂ`, then so is `u A u⁻¹ - z`. -/
lemma unitaryConj_sub_smul_surjective {z : ℂ} (h : Function.Surjective (A - z • 1).toFun) :
    Function.Surjective (unitaryConj u A - z • 1).toFun := by
  intro φ
  obtain ⟨ξ, hξ⟩ := h (u.symm φ)
  obtain ⟨w, hw⟩ : ∃ w : A.domain, A w - z • (w : H) = u.symm φ :=
    ⟨⟨(ξ : H), (Submodule.mem_inf.mp ξ.2).1⟩, hξ⟩
  refine ⟨⟨u (w : H), Submodule.mem_inf.mpr
    ⟨map_mem_unitaryConj_domain u A w, Submodule.mem_top⟩⟩, ?_⟩
  show unitaryConj u A ⟨u (w : H), map_mem_unitaryConj_domain u A w⟩ - z • (u (w : H)) = φ
  rw [unitaryConj_apply_map, ← _root_.map_smul u, ← _root_.map_sub, hw, u.apply_symm_apply]

/-!
## C. Classes of operators
-/

/-!
### C.1. Unbounded operators
-/

lemma IsUnbounded.hasDenseDomain (h : U.IsUnbounded) : U.HasDenseDomain := h.1

lemma IsUnbounded.isClosable (h : U.IsUnbounded) : U.IsClosable := h.2

lemma IsUnbounded.adjoint [CompleteSpace H] [CompleteSpace H'] (h : U.IsUnbounded) :
    U†.IsUnbounded := by
  refine ⟨?_, (adjoint_isClosed h.1).isClosable⟩
  by_contra h_adj
  obtain ⟨y, hy⟩ := not_forall.mp h_adj
  have h_ne_bot : U†.domainᗮ = ⊥ → False := by
    rw [← orthogonal_eq_top_iff, orthogonal_orthogonal_eq_closure]
    exact fun a ↦ ne_of_mem_of_not_mem' mem_top hy a.symm
  obtain ⟨x, hx, hx'⟩ := exists_mem_ne_zero_of_ne_bot h_ne_bot
  apply hx'
  refine graph_fst_eq_zero_snd U.closure ?_ rfl
  rw [← IsClosable.graph_closure_eq_closure_graph h.2,
    mem_submodule_closure_iff_mem_submoduleToLp_closure, ← orthogonal_orthogonal_eq_closure,
    ← mem_submodule_adjoint_adjoint_iff_mem_submoduleToLp_orthogonal_orthogonal,
    ← adjoint_graph_eq_graph_adjoint h.1, mem_submodule_adjoint_iff_mem_submoduleToLp_orthogonal]
  rintro ⟨y, Uy⟩ hy
  simp only [neg_zero, WithLp.prod_inner_apply, inner_zero_right, add_zero]
  exact hx y (mem_domain_of_mem_graph hy)

lemma IsUnbounded.closure (h : U.IsUnbounded) : U.closure.IsUnbounded :=
  ⟨h.1.closure, h.2.closureIsClosable⟩

@[simp]
lemma IsUnbounded.adjoint_closure_eq_adjoint [CompleteSpace H] (h : U.IsUnbounded) :
    U.closure† = U† := by
  refine eq_of_eq_graph ?_
  ext
  rw [adjoint_graph_eq_graph_adjoint h.1, adjoint_graph_eq_graph_adjoint h.1.closure,
    ← IsClosable.graph_closure_eq_closure_graph h.2,
    mem_submodule_closure_adjoint_iff_mem_submoduleToLp_closure_orthogonal, orthogonal_closure,
    mem_submodule_adjoint_iff_mem_submoduleToLp_orthogonal]

@[simp]
lemma IsUnbounded.adjoint_adjoint_eq_closure [CompleteSpace H] [CompleteSpace H']
    (h : U.IsUnbounded) :
    U†† = U.closure := by
  refine eq_of_eq_graph ?_
  ext
  rw [adjoint_graph_eq_graph_adjoint h.adjoint.1, adjoint_graph_eq_graph_adjoint h.1,
    ← IsClosable.graph_closure_eq_closure_graph h.2,
    mem_submodule_adjoint_adjoint_iff_mem_submoduleToLp_orthogonal_orthogonal,
    orthogonal_orthogonal_eq_closure, mem_submodule_closure_iff_mem_submoduleToLp_closure]

lemma IsUnbounded.le_adjoint_adjoint [CompleteSpace H] [CompleteSpace H'] (h : U.IsUnbounded) :
    U ≤ U†† :=
  h.adjoint_adjoint_eq_closure ▸ U.le_closure

lemma IsUnbounded.isClosed_iff [CompleteSpace H] [CompleteSpace H'] (h : U.IsUnbounded) :
    U.IsClosed ↔ U†† = U :=
  h.adjoint_adjoint_eq_closure ▸ h.2.isClosed_iff

/-- `U†.rangeᗮ = U.closure.ker` -/
lemma IsUnbounded.orthogonal_adjoint_range [CompleteSpace H] [CompleteSpace H']
    (h : U.IsUnbounded) : U†.toFun.rangeᗮ = U.closure.toFun.ker.map U.closure.domain.subtype :=
  h.adjoint_adjoint_eq_closure ▸ h.adjoint.hasDenseDomain.orthogonal_range

/-- `U.closure.kerᗮ = U†.range` -/
lemma IsUnbounded.orthogonal_closure_ker [CompleteSpace H] [CompleteSpace H'] (h : U.IsUnbounded) :
    (U.closure.toFun.ker.map U.closure.domain.subtype)ᗮ = U†.toFun.range.closure :=
  h.adjoint_adjoint_eq_closure ▸ h.adjoint.hasDenseDomain.orthogonal_adjoint_ker

/-!
### C.2. Symmetric operators
-/

/-- The analogue of `inner_map_polarization` for LinearPMap. -/
lemma inner_map_polarization (x y : T.domain) :
    ⟪T y, x⟫_ℂ = (⟪T (x + y), ↑(x + y)⟫_ℂ - ⟪T (x - y), ↑(x - y)⟫_ℂ
      + I * ⟪T (x + I • y), ↑(x + I • y)⟫_ℂ - I * ⟪T (x - I • y), ↑(x - I • y)⟫_ℂ) / 4 := by
  simp only [map_add, coe_add, inner_add_right, inner_add_left, map_sub, AddSubgroupClass.coe_sub,
    inner_sub_right, inner_sub_left, sub_sub, map_smul, SetLike.val_smul, inner_smul_left, conj_I,
    neg_mul, inner_smul_right, mul_add, mul_neg, ← mul_assoc, ← pow_two, I_sq, one_mul, neg_neg,
    sub_neg_eq_add, mul_sub]
  ring

/-- The analogue of `inner_map_polarization'` for LinearPMap. -/
theorem inner_map_polarization' (x y : T.domain) :
    ⟪T x, y⟫_ℂ = (⟪T (x + y), ↑(x + y)⟫_ℂ - ⟪T (x - y), ↑(x - y)⟫_ℂ
      - I * ⟪T (x + I • y), ↑(x + I • y)⟫_ℂ + I * ⟪T (x - I • y), ↑(x - I • y)⟫_ℂ) / 4 := by
  simp only [map_add, coe_add, inner_add_right, inner_add_left, map_sub, AddSubgroupClass.coe_sub,
    inner_sub_right, inner_sub_left, sub_sub, map_smul, SetLike.val_smul, inner_smul_left, conj_I,
    neg_mul, inner_smul_right, mul_add, mul_neg, ← mul_assoc, ← pow_two, I_sq, one_mul, neg_neg,
    sub_neg_eq_add, mul_sub]
  ring

-- The analogue of `LinearMap.isSymmetric_iff_inner_map_self_real` for LinearPMap.
lemma isSymmetric_iff_inner_map_self_real :
    T.IsSymmetric ↔ ∀ x : T.domain, conj ⟪T x, x⟫_ℂ = ⟪T x, x⟫_ℂ := by
  refine ⟨fun h_symm x ↦ by simp [h_symm x x], fun h_re x y ↦ ?_⟩
  nth_rw 2 [← inner_conj_symm, inner_map_polarization]
  simp only [map_div₀, _root_.map_sub, _root_.map_add, map_mul, neg_mul, conj_ofNat, conj_I, h_re]
  rw [inner_map_polarization']
  simp [sub_eq_add_neg]

lemma IsSymmetric.isClosable [CompleteSpace H] (h : T.IsSymmetric) (h' : T.HasDenseDomain) :
    T.IsClosable :=
  isClosable_iff_exists_closed_extension.mpr ⟨T†, adjoint_isClosed h', h.le_adjoint h'⟩

lemma IsSymmetric.isUnbounded_iff_hasDenseDomain [CompleteSpace H] (h : T.IsSymmetric) :
    T.IsUnbounded ↔ T.HasDenseDomain :=
  and_iff_left_of_imp h.isClosable

lemma isSymmetric_iff_le_adjoint [CompleteSpace H] (h : T.HasDenseDomain) :
    T.IsSymmetric ↔ T ≤ T† := by
  refine ⟨fun h_symm ↦ h_symm.le_adjoint h, fun h_le x y ↦ ?_⟩
  have h_eq : T x = T† ⟨x, h_le.1 x.2⟩ := @h_le.2 x ⟨x, h_le.1 x.2⟩ rfl
  exact h_eq ▸ adjoint_isFormalAdjoint h _ _

lemma IsSymmetric.closure_le_adjoint [CompleteSpace H] (h : T.IsSymmetric) (h' : T.HasDenseDomain) :
    T.closure ≤ T† := by
  have h_adj : T†.IsClosed := adjoint_isClosed h'
  exact h_adj.closure_eq ▸ h_adj.isClosable.closure_mono (h.le_adjoint h')

lemma IsSymmetric.isEssentiallySelfAdjoint_iff [CompleteSpace H]
    (h : T.IsSymmetric) (h' : T.HasDenseDomain) :
    T.IsEssentiallySelfAdjoint ↔ T†.domain = T.closure.domain := by
  rw [isEssentiallySelfAdjoint_def, isSelfAdjoint_def,
    (h.isUnbounded_iff_hasDenseDomain.mpr h').adjoint_closure_eq_adjoint]
  constructor <;> intro h''
  · congr
  · exact (eq_of_le_of_domain_eq (h.closure_le_adjoint h') h''.symm).symm

lemma IsSymmetric.isSelfAdjoint_iff [CompleteSpace H] (h : T.IsSymmetric) (h' : T.HasDenseDomain) :
    IsSelfAdjoint T ↔ T†.domain = T.domain := by
  constructor <;> intro h''
  · congr
  · exact (eq_of_le_of_domain_eq ((isSymmetric_iff_le_adjoint h').mp h) h''.symm).symm

lemma add_adjoint_isSymmetric [CompleteSpace H] (h : T.HasDenseDomain) :
    (T + T.adjoint).IsSymmetric := by
  intro x y
  have h₁ := adjoint_isFormalAdjoint h ⟨x, x.2.2⟩ ⟨y, y.2.1⟩
  have h₂ := congrArg conj (adjoint_isFormalAdjoint h ⟨y, y.2.2⟩ ⟨x, x.2.1⟩)
  simp only [inner_conj_symm] at h₂
  simp only [add_apply, inner_add_left, inner_add_right, h₁, h₂]
  exact add_comm _ _

@[aesop safe apply]
lemma IsSymmetric.pow (h : T.IsSymmetric) (n : ℕ) : (T ^ n).IsSymmetric := by
  induction n with
  | zero => exact fun _ _ ↦ rfl
  | succ n ih =>
    intro x y
    let y' : (T * T ^ n).domain := ⟨y, pow_succ' T n ▸ y.2⟩
    let Tx : (T ^ n).domain := ⟨T ⟨x, x.2.2⟩, mem_domain_of_mem_compRestricted_domain x⟩
    let Tny : T.domain := ⟨(T ^ n) ⟨y', y'.2.2⟩, mem_domain_of_mem_compRestricted_domain y'⟩
    have h_eq : T Tny = (T ^ (n + 1)) y := by
      change (T * T ^ n) y' = (T ^ (n + 1)) y
      congr 1
      · exact (pow_succ' T n).symm
      · exact (Subtype.heq_iff_coe_eq <| by simp [pow_succ']).mpr rfl
    exact (ih Tx ⟨y', y'.2.2⟩).trans (h_eq ▸ h ⟨x, x.2.2⟩ Tny)

@[aesop safe apply]
lemma IsSymmetric.neg (h : T.IsSymmetric) : (-T).IsSymmetric := fun x y ↦ by simp [h x y]

@[aesop safe apply]
lemma IsSymmetric.add (h₁ : T₁.IsSymmetric) (h₂ : T₂.IsSymmetric) : (T₁ + T₂).IsSymmetric := by
  intro x y
  simp [h₁ ⟨x, x.2.1⟩ ⟨y, y.2.1⟩, h₂ ⟨x, x.2.2⟩ ⟨y, y.2.2⟩, add_apply, inner_add_left,
    inner_add_right]

@[aesop safe apply]
lemma IsSymmetric.sub (h₁ : T₁.IsSymmetric) (h₂ : T₂.IsSymmetric) : (T₁ - T₂).IsSymmetric :=
  sub_eq_add_neg T₁ T₂ ▸ h₁.add h₂.neg

@[aesop safe apply]
lemma IsSymmetric.smul (h : T.IsSymmetric) {c : ℂ} (hc : conj c = c) : (c • T).IsSymmetric :=
  fun x y ↦ by simp only [smul_apply, inner_smul_left, inner_smul_right, hc, h x y]

@[aesop safe apply]
lemma IsSymmetric.real_smul (h : T.IsSymmetric) (r : ℝ) : (r • T).IsSymmetric :=
  h.smul (conj_ofReal r)

@[aesop safe apply]
lemma IsSymmetric.sum (h : ∀ a, (S a).IsSymmetric) : (sum S).IsSymmetric := by
  intro x y
  simp [sum_apply, sum_inner, inner_sum, h _ ⟨x, sum_domain_le S _ x.2⟩ ⟨y, sum_domain_le S _ y.2⟩]

lemma IsSymmetric.of_le (h₁ : T₁.IsSymmetric) (h_le : T₂ ≤ T₁) : T₂.IsSymmetric := by
  intro x y
  have hx : T₂ x = T₁ ⟨x, h_le.1 x.2⟩ := @h_le.2 x ⟨x, h_le.1 x.2⟩ rfl
  have hy : T₂ y = T₁ ⟨y, h_le.1 y.2⟩ := @h_le.2 y ⟨y, h_le.1 y.2⟩ rfl
  exact hx ▸ hy ▸ h₁ ⟨x, h_le.1 x.2⟩ ⟨y, h_le.1 y.2⟩

/-- The closure of a symmetric densely-defined operator is symmetric: `T††` is a symmetric
closed extension of `T`, so it extends `T.closure`, whose symmetry then descends. -/
lemma IsSymmetric.closure [CompleteSpace H] (hsym : T.IsSymmetric) (hdense : T.HasDenseDomain) :
    T.closure.IsSymmetric := by
  have hle : T ≤ T† := (isSymmetric_def.mp hsym).le_adjoint hdense
  have hadj_dense : T†.HasDenseDomain := hdense.mono hle.1
  have hT_le : T ≤ T†† := (adjoint_isFormalAdjoint hdense).le_adjoint hadj_dense
  have hc : (T††).IsClosed := adjoint_isClosed hadj_dense
  have h1 : (T††).IsSymmetric :=
    (isSymmetric_iff_le_adjoint (hdense.mono hT_le.1)).mpr
      (adjoint_antitone (Or.inl (hdense.mono hT_le.1)) (adjoint_antitone (Or.inl hdense) hle))
  exact h1.of_le (hc.closure_eq ▸ hc.isClosable.closure_mono hT_le)

/-- A LinearPMap constructed from a symmetric LinearMap with dense domain
  is an unbounded operator. -/
lemma isUnbounded_of_dense_of_isSymmetric [CompleteSpace H] {E : Submodule ℂ H}
    (hE : Dense (E : Set H)) {f : E →ₗ[ℂ] H} (h : ∀ x y : E, ⟪f x, ↑y⟫_ℂ = ⟪↑x, f y⟫_ℂ) :
    (mk E f).IsUnbounded :=
  ⟨hE, IsSymmetric.isClosable h hE⟩

/-- Variant of `of_dense_of_isSymmetric` for an endomorphism satisfying `LinearMap.IsSymmetric`. -/
lemma isUnbounded_of_dense_of_isSymmetric' [CompleteSpace H]
    {E : Submodule ℂ H} (hE : Dense (E : Set H)) {f : E →ₗ[ℂ] E} (h : f.IsSymmetric) :
    (mk E (E.subtype ∘ₗ f)).IsUnbounded :=
  ⟨hE, IsSymmetric.isClosable h hE⟩

/-!
### C.3. Self-adjoint operators
-/

lemma IsSelfAdjoint.isSymmetric [CompleteSpace H] (h : IsSelfAdjoint T) : T.IsSymmetric := by
  rw [isSymmetric_def]
  nth_rw 1 [← h]
  exact adjoint_isFormalAdjoint h.dense_domain

lemma IsSelfAdjoint.isClosed [CompleteSpace H] (h : IsSelfAdjoint T) : T.IsClosed :=
  h ▸ adjoint_isClosed h.dense_domain

lemma IsSelfAdjoint.isClosable [CompleteSpace H] (h : IsSelfAdjoint T) : T.IsClosable :=
  (isClosed h).isClosable

lemma IsSelfAdjoint.isUnbounded [CompleteSpace H] (h : IsSelfAdjoint T) : T.IsUnbounded :=
  ⟨h.dense_domain, isClosable h⟩

lemma IsSelfAdjoint.isEssentiallySelfAdjoint [CompleteSpace H] (h : IsSelfAdjoint T) :
    T.IsEssentiallySelfAdjoint :=
  isEssentiallySelfAdjoint_def.mpr (h.isClosed.closure_eq.symm ▸ h)

@[aesop safe apply]
lemma IsSelfAdjoint.adjoint [CompleteSpace H] (h : IsSelfAdjoint T) : IsSelfAdjoint T† := by
  apply isSelfAdjoint_def.mp at h
  exact h.symm ▸ h

@[aesop safe apply]
lemma IsSelfAdjoint.smul [CompleteSpace H]
    (h : IsSelfAdjoint T) {c : ℂ} (hc : c ≠ 0) (hc' : conj c = c) :
    IsSelfAdjoint (c • T) := by
  rw [isSelfAdjoint_def, T.adjoint_smul hc, hc', isSelfAdjoint_def.mp h]

@[aesop safe apply]
lemma IsSelfAdjoint.real_smul [CompleteSpace H] (h : IsSelfAdjoint T) {r : ℝ} (hr : r ≠ 0) :
    IsSelfAdjoint (r • T) :=
  smul h (ofReal_ne_zero.mpr hr) (conj_ofReal r)

@[aesop safe apply]
lemma IsSelfAdjoint.neg [CompleteSpace H] (h : IsSelfAdjoint T) : IsSelfAdjoint (-T) :=
  neg_eq_neg_one_smul T ▸ smul h (by norm_num) (by norm_num)

/-- Self-adjointness from surjectivity of `T ± i`: a symmetric, densely-defined operator `T` for
which `T + I • 1` and `T - I • 1` both have full range is self-adjoint. -/
lemma IsSymmetric.isSelfAdjoint_of_range_eq_top [CompleteSpace H] (hsym : T.IsSymmetric)
    (hdense : T.HasDenseDomain)
    (hadd : (T + I • 1).toFun.range = ⊤) (hsub : (T - I • 1).toFun.range = ⊤) :
    IsSelfAdjoint T := by
  have hplus : ∀ φ : H, ∃ ψ : T.domain, T ψ + I • (ψ : H) = φ := fun φ => by
    obtain ⟨ψ, hψ⟩ := LinearMap.range_eq_top.mp hadd φ
    exact ⟨⟨(ψ : H), (Submodule.mem_inf.mp ψ.2).1⟩, hψ⟩
  have hminus : ∀ φ : H, ∃ ψ : T.domain, T ψ - I • (ψ : H) = φ := fun φ => by
    obtain ⟨ψ, hψ⟩ := LinearMap.range_eq_top.mp hsub φ
    exact ⟨⟨(ψ : H), (Submodule.mem_inf.mp ψ.2).1⟩, hψ⟩
  rw [isSelfAdjoint_def]
  have hle : T ≤ T.adjoint := (isSymmetric_def.mp hsym).le_adjoint hdense
  apply le_antisymm _ hle
  apply le_of_eqLocus_ge
  intro w hw
  let W : T.adjoint.domain := ⟨w, hw⟩
  obtain ⟨x, hx⟩ := hminus (T.adjoint W - I • (W : H))
  set X : T.adjoint.domain := ⟨x, hle.1 x.2⟩ with hX
  have hxeq : T.adjoint X = T x := (hle.2 (x := x) (y := X) rfl).symm
  have hdiff : T.adjoint (W - X) = I • ((W - X) : H) := by
    rw [LinearPMap.map_sub, hxeq, hX, Subtype.coe_mk, smul_sub, sub_eq_sub_iff_sub_eq_sub, hx]
  have hker : ∀ w : T.adjoint.domain, T.adjoint w = I • (w : H) → (w : H) = 0 := by
    intro w hw
    obtain ⟨v, hv⟩ := hplus (w : H)
    suffices ⟪↑w, T v + I • v⟫_ℂ = 0 by
      exact inner_self_eq_zero.mp (hv ▸ this)
    rw [inner_add_right, inner_smul_right, ← adjoint_isFormalAdjoint hdense w v, hw,
      inner_smul_left, conj_I]
    ring
  obtain rfl : w = (x : H) := sub_eq_zero.mp (hker (W - X) hdiff)
  exact ⟨hw, x.2, hxeq⟩

/-!
### C.4. Essentially self-adjoint operators
-/

lemma IsEssentiallySelfAdjoint.hasDenseDomain [CompleteSpace H] (h : T.IsEssentiallySelfAdjoint) :
    T.HasDenseDomain :=
  hasDenseDomain_iff_closure_hasDenseDomain.mpr h.dense_domain

lemma IsEssentiallySelfAdjoint.isSymmetric [CompleteSpace H] (h : T.IsEssentiallySelfAdjoint) :
    T.IsSymmetric :=
  (IsSelfAdjoint.isSymmetric h).of_le T.le_closure

lemma IsEssentiallySelfAdjoint.isClosable [CompleteSpace H] (h : T.IsEssentiallySelfAdjoint) :
    T.IsClosable :=
  h.isSymmetric.isClosable h.hasDenseDomain

lemma IsEssentiallySelfAdjoint.isUnbounded [CompleteSpace H] (h : T.IsEssentiallySelfAdjoint) :
    T.IsUnbounded :=
  h.isSymmetric.isUnbounded_iff_hasDenseDomain.mpr h.hasDenseDomain

/-- The closure is the unique self-adjoint extension of an essentially self-adjoint operator. -/
lemma IsEssentiallySelfAdjoint.unique_self_adjoint_extension [CompleteSpace H]
    (h : T.IsEssentiallySelfAdjoint) {T₂ : H →ₗ.[ℂ] H} (h_le : T ≤ T₂) (h₂ : IsSelfAdjoint T₂) :
    T₂ = T.closure := by
  have h_cl : T₂.IsClosed := IsSelfAdjoint.isClosed h₂
  have h_le' : T.closure ≤ T₂ := h_cl.closure_eq ▸ h_cl.isClosable.closure_mono h_le
  exact eq_of_le_of_ge (h ▸ h₂ ▸ adjoint_antitone (Or.inl h.hasDenseDomain.closure) h_le') h_le'

@[aesop safe apply]
lemma IsEssentiallySelfAdjoint.smul [CompleteSpace H]
    (h : T.IsEssentiallySelfAdjoint) {c : ℂ} (hc : c ≠ 0) (hc' : conj c = c) :
    (c • T).IsEssentiallySelfAdjoint := by
  simp_all [isEssentiallySelfAdjoint_def, isSelfAdjoint_def, closure_smul _ hc, adjoint_smul _ hc]

@[aesop safe apply]
lemma IsEssentiallySelfAdjoint.real_smul [CompleteSpace H]
    (h : T.IsEssentiallySelfAdjoint) {r : ℝ} (hr : r ≠ 0) :
    (r • T).IsEssentiallySelfAdjoint :=
  h.smul (ofReal_ne_zero.mpr hr) (conj_ofReal r)

@[aesop safe apply]
lemma IsEssentiallySelfAdjoint.neg [CompleteSpace H] (h : T.IsEssentiallySelfAdjoint) :
    (-T).IsEssentiallySelfAdjoint :=
  neg_eq_neg_one_smul T ▸ h.smul (by norm_num) (by norm_num)

end LinearPMap
