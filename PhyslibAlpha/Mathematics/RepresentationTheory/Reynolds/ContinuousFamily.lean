/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import PhyslibAlpha.Mathematics.RepresentationTheory.Reynolds.Compact
public import PhyslibAlpha.Mathematics.Modules.ConjModule
/-!
# Continuous families of a representation

Finite families of vectors on which a representation acts with continuous coefficients, and the
finite-dimensional subrepresentations they span.

## i. Overview

A Reynolds element of a compact group or of `SL(2,ℂ)` exists on a finite-dimensional
subrepresentation on which the group acts continuously. This file gives a way to produce such
subrepresentations by generation.

An operator family `σ : H → Module.End 𝕜 D` has continuous coefficients when every matrix
coefficient `h ↦ ψ (σ h x)` is continuous. A finite family of vectors `v` is a continuous family
for a representation `ρ` when each `ρ h` maps every `v i` to a combination of the family with
coefficients depending continuously on `h`. Its span is then a finite-dimensional
subrepresentation with continuous matrix coefficients. For two commuting representations the span
of a family continuous for both is a subrepresentation of the product group.

Continuous families are closed under the operations of an algebra. The scalars form one, the
union of two is one, and when the group acts by algebra maps so are the pairwise products of two.

## ii. Key results

- `Representation.ContinuousCoeff` : continuity of an operator family through its matrix
  coefficients.
- `Representation.IsContinuousFamily` : a finite family on which a representation acts with
  continuous coefficients.
- `Representation.HasContinuousSpan` : lying in the span of a continuous family for two
  representations.
- `Representation.exists_subrepresentation_of_isContinuousFamily` : the span of a continuous
  family for two commuting representations is a finite-dimensional subrepresentation of the
  product with continuous matrix coefficients.

## iii. Table of contents

- A. Operator families with continuous coefficients
- B. Families with continuous coefficients
- C. Elements spanned by continuous families
- D. Finite-dimensional subrepresentations

## iv. References

* None.

-/

@[expose] public section

namespace Representation

/-!

## A. Operator families with continuous coefficients

-/

section ContinuousCoeff

variable {𝕜 H H' D : Type*} [Field 𝕜] [TopologicalSpace 𝕜] [TopologicalSpace H]
  [TopologicalSpace H'] [AddCommGroup D] [Module 𝕜 D]

/-- A family `σ` of operators on `D` has continuous coefficients if every matrix coefficient
`h ↦ ψ (σ h x)`, with `ψ` a linear functional on `D`, is continuous. For a finite-dimensional
`D` this is continuity of `σ` for the unique vector space topology on its operators. -/
def ContinuousCoeff (σ : H → Module.End 𝕜 D) : Prop :=
  ∀ (x : D) (ψ : Module.Dual 𝕜 D), Continuous fun h => ψ (σ h x)

/-- Continuous coefficients stay continuous after precomposing with a continuous map. -/
lemma ContinuousCoeff.comp {σ : H → Module.End 𝕜 D} (hσ : ContinuousCoeff σ) {f : H' → H}
    (hf : Continuous f) : ContinuousCoeff fun h => σ (f h) :=
  fun x ψ => (hσ x ψ).comp hf

/-- The transposes of an operator family with continuous coefficients on a finite-dimensional
space have continuous coefficients. -/
lemma ContinuousCoeff.dualMap [FiniteDimensional 𝕜 D] {σ : H → Module.End 𝕜 D}
    (hσ : ContinuousCoeff σ) : ContinuousCoeff fun h => (σ h).dualMap := by
  intro x Ψ
  obtain ⟨d, rfl⟩ := (Module.evalEquiv 𝕜 D).surjective Ψ
  simpa using hσ d x

/-- The coefficients of an operator family in a basis are continuous. -/
lemma ContinuousCoeff.continuous_coord {ι : Type*} {σ : H → Module.End 𝕜 D}
    (hσ : ContinuousCoeff σ) (b : Module.Basis ι 𝕜 D) (i j : ι) :
    Continuous fun h => b.coord j (σ h (b i)) :=
  hσ (b i) (b.coord j)

end ContinuousCoeff

/-- The conjugates of an operator family with continuous coefficients have continuous
coefficients. -/
lemma ContinuousCoeff.endConj {H D : Type*} [TopologicalSpace H] [AddCommGroup D] [Module ℂ D]
    {σ : H → Module.End ℂ D} (hσ : ContinuousCoeff σ) :
    ContinuousCoeff fun h => ConjModule.endConj (σ h) := by
  intro x ψ
  have h := (hσ ((conjEquiv (k := ℂ) (M := D)).symm x) (conjDualEquiv.symm ψ)).star
  refine h.congr fun g => ?_
  simp [conjDualEquiv, ConjModule.endConj_apply]

/-!

## B. Families with continuous coefficients

-/

section Family

variable {H V A : Type*} [Group H] [TopologicalSpace H] [AddCommMonoid V] [Module ℂ V]
  [Semiring A] [Algebra ℂ A] {ρ : Representation ℂ H A} {ρV : Representation ℂ H V}

/-- The representation acts on the finite family `v` by continuous coefficients,
`ρ h (v i) = Σ j, a i j h • v j`. -/
def IsContinuousFamily (ρ : Representation ℂ H V) {ι : Type*} [Fintype ι] (v : ι → V) : Prop :=
  ∃ a : ι → ι → H → ℂ, (∀ i j, Continuous (a i j)) ∧ ∀ h i, ρ h (v i) = ∑ j, a i j h • v j

/-- The family consisting of the unit, for a representation fixing the unit. -/
lemma isContinuousFamily_one (h1 : ∀ h, ρ h 1 = 1) :
    IsContinuousFamily ρ fun _ : Unit => (1 : A) :=
  ⟨fun _ _ _ => 1, fun _ _ => continuous_const, fun h _ => by simp [h1]⟩

/-- The union of two families with continuous coefficients has continuous coefficients. -/
lemma IsContinuousFamily.sumElim {ι ι' : Type*} [Fintype ι] [Fintype ι'] {v : ι → V}
    {u : ι' → V} (hv : IsContinuousFamily ρV v) (hu : IsContinuousFamily ρV u) :
    IsContinuousFamily ρV (Sum.elim v u) := by
  obtain ⟨a, ha, ha_v⟩ := hv
  obtain ⟨b, hb, hbu⟩ := hu
  refine ⟨Sum.elim (fun i => Sum.elim (a i) 0) (fun j => Sum.elim 0 (b j)), ?_, ?_⟩
  · rintro (i | j) (i' | j') <;> simp only [Sum.elim_inl, Sum.elim_inr] <;>
      first | exact ha _ _ | exact hb _ _ | exact continuous_const
  · rintro h (i | j) <;> simp [Fintype.sum_sum_type, ha_v, hbu]

/-- For a representation acting by algebra maps, the products of two families with continuous
coefficients have continuous coefficients. -/
lemma IsContinuousFamily.mul (hmul : ∀ h x y, ρ h (x * y) = ρ h x * ρ h y) {ι ι' : Type*}
    [Fintype ι] [Fintype ι'] {v : ι → A} {u : ι' → A} (hv : IsContinuousFamily ρ v)
    (hu : IsContinuousFamily ρ u) : IsContinuousFamily ρ fun p : ι × ι' => v p.1 * u p.2 := by
  obtain ⟨a, ha, ha_v⟩ := hv
  obtain ⟨b, hb, hbu⟩ := hu
  refine ⟨fun p q h => a p.1 q.1 h * b p.2 q.2 h, fun p q => (ha _ _).mul (hb _ _),
    fun h p => ?_⟩
  rw [hmul, ha_v, hbu, Finset.sum_mul_sum]
  simp only [Fintype.sum_prod_type, smul_mul_smul_comm]

/-- A tower `t p x`, linear in `x` up to the scalar map `ι𝕜`, on which the representation acts
by continuous coefficients on the label `p` and by an operator family with continuous
coefficients on `x`, gives a family with continuous coefficients over a basis of `x`. -/
lemma isContinuousFamily_tower {𝕜 D P : Type*} [Field 𝕜] [TopologicalSpace 𝕜] [AddCommGroup D]
    [Module 𝕜 D] [FiniteDimensional 𝕜 D] [Fintype P] (ι𝕜 : 𝕜 → ℂ) (hι𝕜 : Continuous ι𝕜)
    (t : P → D → V)
    (ht : ∀ p x, t p x = ∑ j, ι𝕜 (Module.finBasis 𝕜 D |>.repr x j) •
      t p (Module.finBasis 𝕜 D j))
    (σ : H → Module.End 𝕜 D) (hσ : ContinuousCoeff σ) (c : P → P → H → ℂ)
    (hc : ∀ p p', Continuous (c p p'))
    (hρ : ∀ h p x, ρV h (t p x) = ∑ p', c p p' h • t p' (σ h x)) :
    IsContinuousFamily ρV fun q : P × Fin (Module.finrank 𝕜 D) =>
      t q.1 (Module.finBasis 𝕜 D q.2) := by
  set b := Module.finBasis 𝕜 D
  refine ⟨fun q q' h => c q.1 q'.1 h * ι𝕜 (b.coord q'.2 (σ h (b q.2))),
    fun q q' => (hc _ _).mul (hι𝕜.comp (hσ.continuous_coord b _ _)), fun h q => ?_⟩
  rw [hρ, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun p' _ => ?_
  rw [ht p' (σ h (b q.2)), Finset.smul_sum]
  simp only [mul_smul, Module.Basis.coord_apply]

end Family

/-!

## C. Elements spanned by continuous families

-/

section Span

variable {H₁ H₂ A : Type*} [Group H₁] [TopologicalSpace H₁] [Group H₂] [TopologicalSpace H₂]
  [Semiring A] [Algebra ℂ A] {ρ₁ : Representation ℂ H₁ A} {ρ₂ : Representation ℂ H₂ A}

/-- The element `a` lies in the span of a finite family on which both representations act by
continuous coefficients. -/
def HasContinuousSpan (ρ₁ : Representation ℂ H₁ A) (ρ₂ : Representation ℂ H₂ A) (a : A) : Prop :=
  ∃ (ι : Type) (_ : Fintype ι) (v : ι → A), a ∈ Submodule.span ℂ (Set.range v) ∧
    IsContinuousFamily ρ₁ v ∧ IsContinuousFamily ρ₂ v

/-- An element of the span of a family continuous for both representations has a
  continuous span. -/
lemma HasContinuousSpan.of_mem_span {ι : Type} [Fintype ι] {v : ι → A}
    (h₁ : IsContinuousFamily ρ₁ v) (h₂ : IsContinuousFamily ρ₂ v) {a : A}
    (ha : a ∈ Submodule.span ℂ (Set.range v)) : HasContinuousSpan ρ₁ ρ₂ a :=
  ⟨ι, inferInstance, v, ha, h₁, h₂⟩

/-- The scalars have a continuous span, for representations fixing the unit. -/
lemma hasContinuousSpan_smul_one (h₁ : ∀ h, ρ₁ h 1 = 1) (h₂ : ∀ h, ρ₂ h 1 = 1) (z : ℂ) :
    HasContinuousSpan ρ₁ ρ₂ (z • 1) :=
  .of_mem_span (isContinuousFamily_one h₁) (isContinuousFamily_one h₂)
    (Submodule.smul_mem _ z (Submodule.subset_span ⟨(), rfl⟩))

/-- Having a continuous span is closed under addition. -/
lemma HasContinuousSpan.add {a b : A} (ha : HasContinuousSpan ρ₁ ρ₂ a)
    (hb : HasContinuousSpan ρ₁ ρ₂ b) : HasContinuousSpan ρ₁ ρ₂ (a + b) := by
  obtain ⟨ι, _, v, ha_v, hv₁, hv₂⟩ := ha
  obtain ⟨ι', _, u, hbu, hu₁, hu₂⟩ := hb
  refine .of_mem_span (hv₁.sumElim hu₁) (hv₂.sumElim hu₂) (Submodule.add_mem _ ?_ ?_)
  · exact Submodule.span_mono (Set.range_subset_iff.2 fun i =>
      Set.mem_range.2 ⟨Sum.inl i, rfl⟩ : Set.range v ⊆ Set.range (Sum.elim v u)) ha_v
  · exact Submodule.span_mono (Set.range_subset_iff.2 fun i =>
      Set.mem_range.2 ⟨Sum.inr i, rfl⟩ : Set.range u ⊆ Set.range (Sum.elim v u)) hbu

/-- Having a continuous span is closed under multiplication when both representations
  are multiplicative. -/
lemma HasContinuousSpan.mul (hmul₁ : ∀ h x y, ρ₁ h (x * y) = ρ₁ h x * ρ₁ h y)
    (hmul₂ : ∀ h x y, ρ₂ h (x * y) = ρ₂ h x * ρ₂ h y) {a b : A}
    (ha : HasContinuousSpan ρ₁ ρ₂ a) (hb : HasContinuousSpan ρ₁ ρ₂ b) :
    HasContinuousSpan ρ₁ ρ₂ (a * b) := by
  obtain ⟨ι, _, v, ha_v, hv₁, hv₂⟩ := ha
  obtain ⟨ι', _, u, hbu, hu₁, hu₂⟩ := hb
  refine .of_mem_span (hv₁.mul hmul₁ hu₁) (hv₂.mul hmul₂ hu₂) ?_
  have hab := Submodule.mul_mem_mul ha_v hbu
  rw [Submodule.span_mul_span] at hab
  refine Submodule.span_mono ?_ hab
  rintro _ ⟨_, ⟨i, rfl⟩, _, ⟨j, rfl⟩, rfl⟩
  exact ⟨(i, j), rfl⟩

end Span

/-!

## D. Finite-dimensional subrepresentations

-/

/-- A subrepresentation restricted along a monoid homomorphism, as a subrepresentation of the
restricted representation with the same underlying subspace. It is reducible, so that
instances on the underlying subspace, such as finite-dimensionality, carry over. -/
abbrev _root_.Subrepresentation.comp {k H H' V : Type*} [Semiring k] [Monoid H] [Monoid H']
    [AddCommMonoid V] [Module k V] {ρ : Representation k H V} (W : Subrepresentation ρ)
    (f : H' →* H) : Subrepresentation (ρ.comp f) where
  toSubmodule := W.toSubmodule
  apply_mem_toSubmodule g _ hv := W.apply_mem_toSubmodule (f g) hv

@[simp]
lemma _root_.Subrepresentation.toSubmodule_comp {k H H' V : Type*} [Semiring k] [Monoid H]
    [Monoid H'] [AddCommMonoid V] [Module k V] {ρ : Representation k H V}
    (W : Subrepresentation ρ) (f : H' →* H) : (W.comp f).toSubmodule = W.toSubmodule := rfl

section Subrep

variable {H H₁ H₂ V : Type*} [Group H] [TopologicalSpace H] [Group H₁] [TopologicalSpace H₁]
  [Group H₂] [TopologicalSpace H₂] [AddCommGroup V] [Module ℂ V]

/-- The span of a family with continuous coefficients is stable. -/
lemma IsContinuousFamily.apply_mem_span {ρ : Representation ℂ H V} {ι : Type*} [Fintype ι]
    {v : ι → V} (hv : IsContinuousFamily ρ v) (h : H) {x : V}
    (hx : x ∈ Submodule.span ℂ (Set.range v)) : ρ h x ∈ Submodule.span ℂ (Set.range v) := by
  obtain ⟨a, -, ha_v⟩ := hv
  refine (Submodule.span_le (p := (Submodule.span ℂ (Set.range v)).comap (ρ h))).2 ?_ hx
  rintro _ ⟨i, rfl⟩
  rw [SetLike.mem_coe, Submodule.mem_comap, ha_v]
  exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)

/-- The subrepresentation of the product spanned by a family with continuous coefficients
for both factors. -/
def spanSubrepresentation {ρ₁ : Representation ℂ H₁ V} {ρ₂ : Representation ℂ H₂ V}
    (hc : ∀ a b, Commute (ρ₁ a) (ρ₂ b)) {ι : Type*} [Fintype ι] {v : ι → V}
    (h₁ : IsContinuousFamily ρ₁ v) (h₂ : IsContinuousFamily ρ₂ v) :
    Subrepresentation (prodOfCommute ρ₁ ρ₂ hc) where
  toSubmodule := Submodule.span ℂ (Set.range v)
  apply_mem_toSubmodule g _ hx := by
    rw [prodOfCommute_apply, mul_apply_eq_comp]
    exact h₁.apply_mem_span _ (h₂.apply_mem_span _ hx)

/-- A finite family with continuous coefficients gives a subrepresentation with continuous
matrix coefficients. -/
lemma continuousMatrixCoeff_of_isContinuousFamily {ρ : Representation ℂ H V}
    (W : Subrepresentation ρ) {ι : Type*} [Fintype ι] {v : ι → V}
    (hW : W.toSubmodule = Submodule.span ℂ (Set.range v)) (hv : IsContinuousFamily ρ v) :
    ContinuousMatrixCoeff W := by
  obtain ⟨a, ha, ha_v⟩ := hv
  exact continuousMatrixCoeff_of_span W v (fun i => hW ▸ Submodule.subset_span ⟨i, rfl⟩)
    hW.le a ha ha_v

/-- A vector in the span of a finite family with continuous coefficients for two commuting
representations lies in a finite-dimensional subrepresentation of the product, on which both
factors act with continuous matrix coefficients. -/
lemma exists_subrepresentation_of_isContinuousFamily {ρ₁ : Representation ℂ H₁ V}
    {ρ₂ : Representation ℂ H₂ V} (hc : ∀ a b, Commute (ρ₁ a) (ρ₂ b)) {ι : Type*} [Fintype ι]
    {v : ι → V} (h₁ : IsContinuousFamily ρ₁ v) (h₂ : IsContinuousFamily ρ₂ v) {a : V}
    (ha_v : a ∈ Submodule.span ℂ (Set.range v)) :
    ∃ W : Subrepresentation (prodOfCommute ρ₁ ρ₂ hc), a ∈ W.toSubmodule ∧
      FiniteDimensional ℂ W.toSubmodule ∧
      ContinuousMatrixCoeff (W.comp (MonoidHom.inl H₁ H₂)) ∧
      ContinuousMatrixCoeff (W.comp (MonoidHom.inr H₁ H₂)) := by
  refine ⟨spanSubrepresentation hc h₁ h₂, ha_v,
    FiniteDimensional.span_of_finite ℂ (Set.finite_range v), ?_, ?_⟩
  · exact continuousMatrixCoeff_of_isContinuousFamily _ rfl
      ((prodOfCommute_comp_inl ρ₁ ρ₂ hc).symm ▸ h₁)
  · exact continuousMatrixCoeff_of_isContinuousFamily _ rfl
      ((prodOfCommute_comp_inr ρ₁ ρ₂ hc).symm ▸ h₂)

end Subrep

end Representation
