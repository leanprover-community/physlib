/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Mathlib.RepresentationTheory.Invariants
public import Mathlib.RepresentationTheory.Subrepresentation
public import Mathlib.GroupTheory.NoncommCoprod
/-!

# Reynolds elements

Elements of the monoid algebra that project a stable subspace onto its invariants.

## i. Overview

Let `ρ` be a representation of a monoid `H` on a vector space `V` and `W` a subspace of `V`.
A Reynolds element for `ρ` on `W` is an element `r` of the monoid algebra `k[H]` whose
coefficients sum to one, and which maps every vector of `W` to an invariant vector of `W`. For a
finite group the average `(1/|H|) Σ_h h` is a Reynolds element on all of `V`, and for a compact
group the Haar average plays the same role on each finite-dimensional stable subspace.

The point of the coefficients summing to one is that `r` then fixes every invariant vector, in any
representation. This gives the descent property. If `f : V → B` intertwines `ρ` with a
representation `σ` on `B`, `a ∈ W` and `f a` is `σ`-invariant, then `a' = r • a` is a
`ρ`-invariant vector with `f a' = r • f a = f a`. So invariants in the image of `f` come from
invariants in `V`.

Reynolds elements are usually produced as an operator `P` on a finite-dimensional stable subspace
which projects onto the invariants and lies in `1 + span {ρ h - 1}`. We show that every such
operator comes from a Reynolds element.

Finally, for two commuting representations, packaged as one representation of `H₁ × H₂`,
Reynolds elements for each factor multiply to a Reynolds element for the product.

## ii. Key results

- `Representation.augmentation` is the sum of the coefficients of an element of `k[H]`.
- `Representation.IsReynolds` is the property of being a Reynolds element on a subspace.
- `Representation.IsReynolds.of_comp` pushes a Reynolds element forward along a surjective
  homomorphism of groups.
- `Representation.IsReynolds.exists_mem_invariants_map_eq` is the descent property along
  intertwining maps.
- `Representation.exists_isReynolds_of_sub_one_mem_span` produces a Reynolds element from an
  operator on a stable subspace in `1 + span {ρ h - 1}` with image in the invariants.
- `Representation.IsReynolds.mul_mapDomain` multiplies Reynolds elements of the two factors of
  a representation of `H₁ × H₂`.

## iii. Table of contents

- A. The augmentation
- B. The monoid algebra acting on invariants and through intertwiners
- C. Reynolds elements
  - C.1. The definition
  - C.2. Descent along intertwining maps
- D. Reynolds elements from operators on stable subspaces
  - D.1. Operators in one plus the span of the group image
  - D.2. Subrepresentations
- E. Reynolds elements for products
  - E.1. Commuting representations
  - E.2. The product of Reynolds elements

## iv. References

- The Reynolds operator in invariant theory, see for example
  B. Sturmfels, *Algorithms in Invariant Theory*.

-/

@[expose] public section

open scoped MonoidAlgebra

namespace Representation

/-!

## A. The augmentation

-/

section Augmentation

variable (k H : Type*) [CommSemiring k] [Monoid H]

/-- The augmentation of the monoid algebra `k[H]`, sending a formal linear combination of
elements of `H` to the sum of its coefficients. -/
noncomputable def augmentation : k[H] →ₐ[k] k := MonoidAlgebra.lift k k H 1

variable {k H}

@[simp]
lemma augmentation_single (h : H) (c : k) :
    augmentation k H (MonoidAlgebra.single h c) = c := by
  simp [augmentation]

/-- The augmentation is unchanged by pushing an element along a monoid map. -/
lemma augmentation_mapDomainAlgHom {H' : Type*} [Monoid H'] (f : H →* H') (r : k[H]) :
    augmentation k H' (MonoidAlgebra.mapDomainAlgHom k k f r) = augmentation k H r := by
  induction r using MonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy => rw [map_add, map_add, map_add, hx, hy]
  | single h c => simp [MonoidAlgebra.mapDomain_single]

end Augmentation

/-!

## B. The monoid algebra acting on invariants and through intertwiners

-/

variable {k H V B : Type*} [CommRing k] [Group H] [AddCommGroup V] [Module k V]
  [AddCommGroup B] [Module k B]

/-- An element of the monoid algebra acts on an invariant vector by its augmentation. -/
lemma asAlgebraHom_apply_of_mem_invariants (ρ : Representation k H V) (r : k[H]) {v : V}
    (hv : v ∈ ρ.invariants) : ρ.asAlgebraHom r v = augmentation k H r • v := by
  induction r using MonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy => simp [hx, hy, add_smul]
  | single h c => simp [(ρ.mem_invariants v).1 hv h]

/-- A linear map intertwining two representations also intertwines the actions of the monoid
algebra. -/
lemma map_asAlgebraHom_apply (ρ : Representation k H V) (σ : Representation k H B)
    (f : V →ₗ[k] B) (hf : ∀ h v, f (ρ h v) = σ h (f v)) (r : k[H]) (v : V) :
    f (ρ.asAlgebraHom r v) = σ.asAlgebraHom r (f v) := by
  induction r using MonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy => simp [hx, hy]
  | single h c => simp [hf]

/-- Restricting a representation along a monoid homomorphism corresponds to pushing elements of
the monoid algebra forward along it. -/
lemma asAlgebraHom_comp {H' : Type*} [Group H'] (ρ : Representation k H' V) (f : H →* H')
    (r : k[H]) :
    asAlgebraHom (ρ.comp f) r = ρ.asAlgebraHom (MonoidAlgebra.mapDomainAlgHom k k f r) := by
  induction r using MonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy => rw [map_add, map_add, map_add, hx, hy]
  | single h c => simp [MonoidAlgebra.mapDomain_single]

/-!

## C. Reynolds elements

### C.1. The definition

-/

/-- An element `r` of the monoid algebra is a Reynolds element for the representation on the
subspace `W` if its coefficients sum to one and it maps every vector of `W` to an invariant
vector of `W`. By `IsReynolds.apply_of_mem_invariants` it then fixes every invariant vector,
so it acts on `W` as a projection onto the invariants of `W`. -/
structure IsReynolds (ρ : Representation k H V) (W : Submodule k V) (r : k[H]) : Prop where
  /-- The coefficients of the Reynolds element sum to one. -/
  augmentation_eq_one : augmentation k H r = 1
  /-- The Reynolds element maps the subspace into itself. -/
  apply_mem : ∀ w ∈ W, ρ.asAlgebraHom r w ∈ W
  /-- The Reynolds element maps the subspace into the invariants. -/
  apply_mem_invariants : ∀ w ∈ W, ρ.asAlgebraHom r w ∈ ρ.invariants

namespace IsReynolds

variable {ρ : Representation k H V} {W : Submodule k V} {r : k[H]}

/-- A Reynolds element fixes every invariant vector, inside or outside the subspace. -/
lemma apply_of_mem_invariants (hr : ρ.IsReynolds W r) {v : V} (hv : v ∈ ρ.invariants) :
    ρ.asAlgebraHom r v = v := by
  rw [asAlgebraHom_apply_of_mem_invariants ρ r hv, hr.augmentation_eq_one, one_smul]

/-- A Reynolds element maps the subspace onto its invariant vectors. -/
lemma apply_mem_inf (hr : ρ.IsReynolds W r) {w : V} (hw : w ∈ W) :
    ρ.asAlgebraHom r w ∈ W ⊓ ρ.invariants :=
  ⟨hr.apply_mem w hw, hr.apply_mem_invariants w hw⟩

/-- A Reynolds element for a subspace is one for every smaller subspace stable under it. -/
lemma mono {W' : Submodule k V} (hr : ρ.IsReynolds W r) (hW : W' ≤ W)
    (hW' : ∀ w ∈ W', ρ.asAlgebraHom r w ∈ W') : ρ.IsReynolds W' r :=
  ⟨hr.augmentation_eq_one, hW', fun w hw => hr.apply_mem_invariants w (hW hw)⟩

/-- A Reynolds element for a representation restricted along a surjective homomorphism `f` pushes
forward along `f` to a Reynolds element for the representation. -/
lemma of_comp {H' : Type*} [Group H'] {f : H' →* H} (hf : Function.Surjective f) {r : k[H']}
    (hr : IsReynolds (ρ.comp f) W r) : ρ.IsReynolds W (MonoidAlgebra.mapDomainAlgHom k k f r) where
  augmentation_eq_one := by rw [augmentation_mapDomainAlgHom, hr.augmentation_eq_one]
  apply_mem w hw := by
    rw [← asAlgebraHom_comp]
    exact hr.apply_mem w hw
  apply_mem_invariants w hw g := by
    obtain ⟨g', rfl⟩ := hf g
    rw [← asAlgebraHom_comp]
    exact hr.apply_mem_invariants w hw g'

/-!

### C.2. Descent along intertwining maps

-/

/-- The descent property of Reynolds elements. If `f` intertwines `ρ` with `σ`, the vector `a`
lies in a subspace with a Reynolds element, and `f a` is `σ`-invariant, then `f a` is the image of
a `ρ`-invariant vector of that subspace, namely the Reynolds element applied to `a`. -/
lemma exists_mem_invariants_map_eq (hr : ρ.IsReynolds W r) {σ : Representation k H B}
    {f : V →ₗ[k] B} (hf : ∀ h v, f (ρ h v) = σ h (f v)) {a : V} (ha : a ∈ W)
    (hfa : f a ∈ σ.invariants) : ∃ a' ∈ W ⊓ ρ.invariants, f a' = f a := by
  refine ⟨ρ.asAlgebraHom r a, hr.apply_mem_inf ha, ?_⟩
  rw [map_asAlgebraHom_apply ρ σ f hf, asAlgebraHom_apply_of_mem_invariants σ r hfa,
    hr.augmentation_eq_one, one_smul]

end IsReynolds

/-!

## D. Reynolds elements from operators on stable subspaces

### D.1. Operators in one plus the span of the group image

-/

/-- An operator in `1 + span {σ h - 1}` is the action of an element of the monoid algebra whose
coefficients sum to one. -/
lemma exists_asAlgebraHom_eq_of_sub_one_mem_span (σ : Representation k H V)
    {P : Module.End k V} (hP : P - 1 ∈ Submodule.span k (Set.range fun h => σ h - 1)) :
    ∃ r : k[H], augmentation k H r = 1 ∧ σ.asAlgebraHom r = P := by
  let N : Submodule k (Module.End k V) := (LinearMap.ker (augmentation k H).toLinearMap).map
    σ.asAlgebraHom.toLinearMap
  have hle : Submodule.span k (Set.range fun h => σ h - 1) ≤ N := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨h, rfl⟩
    refine ⟨MonoidAlgebra.single h 1 - 1, ?_, ?_⟩
    · simp
    · simp
  obtain ⟨r₀, hr₀, hPr₀⟩ := hle hP
  refine ⟨r₀ + 1, ?_, ?_⟩
  · simpa using hr₀
  · have h : σ.asAlgebraHom r₀ = P - 1 := hPr₀
    rw [map_add, map_one, h, sub_add_cancel]

/-!

### D.2. Subrepresentations

-/

variable {ρ : Representation k H V}

/-- The monoid algebra acts on a subrepresentation by the restriction of its action on the
ambient space. -/
lemma coe_asAlgebraHom_toRepresentation_apply (W : Subrepresentation ρ) (r : k[H])
    (w : W.toSubmodule) : (W.toRepresentation.asAlgebraHom r w : V) = ρ.asAlgebraHom r w :=
  map_asAlgebraHom_apply W.toRepresentation ρ W.toSubmodule.subtype (fun _ _ => rfl) r w

/-- A vector of a subrepresentation is invariant there exactly when it is invariant in the
ambient space. -/
lemma mem_invariants_toRepresentation_iff (W : Subrepresentation ρ) (w : W.toSubmodule) :
    w ∈ W.toRepresentation.invariants ↔ (w : V) ∈ ρ.invariants := by
  simp only [mem_invariants, Subrepresentation.toRepresentation_apply_coe]

/-- An element of the monoid algebra whose coefficients sum to one, and which maps a
subrepresentation into its invariants, is a Reynolds element on it. -/
lemma isReynolds_of_toRepresentation (W : Subrepresentation ρ) {r : k[H]}
    (hr : augmentation k H r = 1)
    (hinv : ∀ w, W.toRepresentation.asAlgebraHom r w ∈ W.toRepresentation.invariants) :
    ρ.IsReynolds W.toSubmodule r where
  augmentation_eq_one := hr
  apply_mem w hw := by
    rw [← coe_asAlgebraHom_toRepresentation_apply W r ⟨w, hw⟩]
    exact Submodule.coe_mem _
  apply_mem_invariants w hw := by
    rw [← coe_asAlgebraHom_toRepresentation_apply W r ⟨w, hw⟩,
      ← mem_invariants_toRepresentation_iff]
    exact hinv _

/-- An operator on a subrepresentation which lies in `1 + span {ρ h - 1}` and maps into the
invariants comes from a Reynolds element. This is the form in which Reynolds elements are
produced on finite-dimensional stable subspaces, for example by averaging over a compact group or
from Casimir operators. -/
lemma exists_isReynolds_of_sub_one_mem_span (W : Subrepresentation ρ)
    {P : Module.End k W.toSubmodule}
    (hP : P - 1 ∈ Submodule.span k (Set.range fun h => W.toRepresentation h - 1))
    (hinv : ∀ w, P w ∈ W.toRepresentation.invariants) :
    ∃ r : k[H], ρ.IsReynolds W.toSubmodule r ∧
      ∀ w : W.toSubmodule, ρ.asAlgebraHom r w = P w := by
  obtain ⟨r, hr, rfl⟩ := exists_asAlgebraHom_eq_of_sub_one_mem_span W.toRepresentation hP
  exact ⟨r, isReynolds_of_toRepresentation W hr hinv,
    fun w => (coe_asAlgebraHom_toRepresentation_apply W r w).symm⟩

/-!

## E. Reynolds elements for products

### E.1. Commuting representations

-/

variable {H₁ H₂ : Type*} [Group H₁] [Group H₂]

/-- The representation of `H₁ × H₂` built from two representations on the same space whose
actions commute. -/
noncomputable def prodOfCommute (ρ₁ : Representation k H₁ V) (ρ₂ : Representation k H₂ V)
    (h : ∀ a b, Commute (ρ₁ a) (ρ₂ b)) : Representation k (H₁ × H₂) V :=
  ρ₁.noncommCoprod ρ₂ h

@[simp]
lemma prodOfCommute_apply (ρ₁ : Representation k H₁ V) (ρ₂ : Representation k H₂ V)
    (h : ∀ a b, Commute (ρ₁ a) (ρ₂ b)) (x : H₁ × H₂) :
    prodOfCommute ρ₁ ρ₂ h x = ρ₁ x.1 * ρ₂ x.2 := rfl

@[simp]
lemma prodOfCommute_comp_inl (ρ₁ : Representation k H₁ V) (ρ₂ : Representation k H₂ V)
    (h : ∀ a b, Commute (ρ₁ a) (ρ₂ b)) :
    (prodOfCommute ρ₁ ρ₂ h).comp (MonoidHom.inl H₁ H₂) = ρ₁ :=
  MonoidHom.noncommCoprod_comp_inl ρ₁ ρ₂ h

@[simp]
lemma prodOfCommute_comp_inr (ρ₁ : Representation k H₁ V) (ρ₂ : Representation k H₂ V)
    (h : ∀ a b, Commute (ρ₁ a) (ρ₂ b)) :
    (prodOfCommute ρ₁ ρ₂ h).comp (MonoidHom.inr H₁ H₂) = ρ₂ :=
  MonoidHom.noncommCoprod_comp_inr ρ₁ ρ₂ h

/-- A vector is invariant under a representation of `H₁ × H₂` exactly when it is invariant under
both factors. -/
lemma mem_invariants_iff_comp_inl_inr (ρ : Representation k (H₁ × H₂) V) (v : V) :
    v ∈ ρ.invariants ↔ v ∈ invariants (ρ.comp (MonoidHom.inl H₁ H₂)) ∧
      v ∈ invariants (ρ.comp (MonoidHom.inr H₁ H₂)) := by
  simp only [mem_invariants, MonoidHom.coe_comp, Function.comp_apply, MonoidHom.inl_apply,
    MonoidHom.inr_apply]
  refine ⟨fun hv => ⟨fun a => hv _, fun b => hv _⟩, fun ⟨h₁, h₂⟩ x => ?_⟩
  have hx : x = (x.1, 1) * (1, x.2) := by simp
  rw [hx, map_mul, mul_apply_eq_comp, h₂, h₁]

/-- A vector is invariant under the representation built from two commuting representations
exactly when it is invariant under both. -/
lemma mem_invariants_prodOfCommute_iff (ρ₁ : Representation k H₁ V)
    (ρ₂ : Representation k H₂ V) (h : ∀ a b, Commute (ρ₁ a) (ρ₂ b)) (v : V) :
    v ∈ (prodOfCommute ρ₁ ρ₂ h).invariants ↔ v ∈ ρ₁.invariants ∧ v ∈ ρ₂.invariants := by
  rw [mem_invariants_iff_comp_inl_inr, prodOfCommute_comp_inl, prodOfCommute_comp_inr]

/-!

### E.2. The product of Reynolds elements

-/

/-- The action of the second factor commutes with the action of the monoid algebra of the first
factor. -/
lemma comp_inr_apply_asAlgebraHom_comp_inl (ρ : Representation k (H₁ × H₂) V) (b : H₂)
    (r : k[H₁]) (v : V) :
    ρ (1, b) (asAlgebraHom (ρ.comp (MonoidHom.inl H₁ H₂)) r v) =
      asAlgebraHom (ρ.comp (MonoidHom.inl H₁ H₂)) r (ρ (1, b) v) := by
  refine map_asAlgebraHom_apply _ _ (ρ (1, b)) (fun a w => ?_) r v
  simp only [MonoidHom.coe_comp, Function.comp_apply, MonoidHom.inl_apply,
    ← mul_apply_eq_comp, ← map_mul, Prod.mk_mul_mk, one_mul, mul_one]

/-- Reynolds elements for the two factors of a representation of `H₁ × H₂` on the same subspace
multiply to a Reynolds element for the representation of the product. -/
lemma IsReynolds.mul_mapDomain {ρ : Representation k (H₁ × H₂) V} {W : Submodule k V}
    {r₁ : k[H₁]} {r₂ : k[H₂]} (hr₁ : IsReynolds (ρ.comp (MonoidHom.inl H₁ H₂)) W r₁)
    (hr₂ : IsReynolds (ρ.comp (MonoidHom.inr H₁ H₂)) W r₂) :
    ρ.IsReynolds W (MonoidAlgebra.mapDomainAlgHom k k (MonoidHom.inl H₁ H₂) r₁ *
      MonoidAlgebra.mapDomainAlgHom k k (MonoidHom.inr H₁ H₂) r₂) := by
  have happ (w : V) : ρ.asAlgebraHom (MonoidAlgebra.mapDomainAlgHom k k (MonoidHom.inl H₁ H₂) r₁ *
      MonoidAlgebra.mapDomainAlgHom k k (MonoidHom.inr H₁ H₂) r₂) w =
      asAlgebraHom (ρ.comp (MonoidHom.inl H₁ H₂)) r₁
        (asAlgebraHom (ρ.comp (MonoidHom.inr H₁ H₂)) r₂ w) := by
    rw [map_mul, mul_apply_eq_comp, asAlgebraHom_comp, asAlgebraHom_comp]
  refine ⟨?_, fun w hw => ?_, fun w hw => ?_⟩
  · rw [map_mul, augmentation_mapDomainAlgHom, augmentation_mapDomainAlgHom,
      hr₁.augmentation_eq_one, hr₂.augmentation_eq_one, one_mul]
  · rw [happ]
    exact hr₁.apply_mem _ (hr₂.apply_mem w hw)
  · rw [happ, mem_invariants_iff_comp_inl_inr]
    refine ⟨hr₁.apply_mem_invariants _ (hr₂.apply_mem w hw), ?_⟩
    rw [mem_invariants]
    intro b
    simp only [MonoidHom.coe_comp, Function.comp_apply, MonoidHom.inr_apply]
    rw [comp_inr_apply_asAlgebraHom_comp_inl,
      show ρ (1, b) _ = _ from (mem_invariants _ _).1 (hr₂.apply_mem_invariants w hw) b]

end Representation
