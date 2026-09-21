/-
Copyright (c) 2026 Gregory J. Loges. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregory J. Loges
-/
module

public import Mathlib.Analysis.InnerProductSpace.LinearPMap
/-!

# LinearPMap

## i. Overview

In this module we collect some basic results about `LinearPMap`s.

Most important is the definition of restricted composition.
The composition of two partial linear maps `g : F →ₗ.[R] G` and `f : E →ₗ.[R] F` is defined
only if the range of `f` is contained in the domain of `g` (c.f. `LinearPMap.comp`).
`g.compRestricted f` (`g ∘ᵣ f`) is defined to be the composition of `g` with the restriction of `f`
to exactly those `x : f.domain` for which `f x ∈ g.domain`. This allows one to work with the
composition of partial linear maps while having the domain implicitly accounted for.

## ii. Key results

- `LinearPMap.sum` : The finite sum of partial linear maps.
- `LinearPMap.compRestricted` (`∘ᵣ`) : For two partial linear maps
    `g : F →ₗ[R] G` and `f : E →ₗ[R] F`, the composition of `g` with `f`
    with natural domain `{x : f.domain | f x ∈ g.domain}`.
- `LinearPMap.instMonoid` : Partial linear maps `E →ₗ.[R] E` with `compRestricted`
    for multiplication and the identity map for `1` comprise a monoid.

## iii. Table of contents

- A. Inequalities
- B. Zero smul
- C. Finite sums
- D. Restricted composition
- E. Monoid
- F. Inverses

## iv. References

* None.
-/

@[expose] public section

namespace LinearPMap

open Submodule

variable {R : Type*} [Ring R]
variable {E : Type*} [AddCommGroup E] [Module R E]
variable {F : Type*} [AddCommGroup F] [Module R F]

/-!
## A. Inequalities
-/

section Inequalities

variable (f f₁ f₂ f₃ : E →ₗ.[R] F) {g g₁ g₂ : E →ₗ.[R] F}

lemma sub_le_zero : f - f ≤ 0 := ⟨le_top, by simp [sub_apply]⟩

lemma neg_add_le_zero : -f + f ≤ 0 := ⟨le_top, by simp [add_apply]⟩

lemma le_iff_neg_le_neg : g₁ ≤ g₂ ↔ -g₁ ≤ -g₂ :=
  ⟨fun ⟨h, h'⟩ ↦ ⟨h, fun _ _ h'' ↦ by simp [h' h'']⟩, fun ⟨h, _⟩ ↦ ⟨h, fun _ _ _ ↦ by aesop⟩⟩

lemma le_neg_iff_neg_le : g₁ ≤ -g₂ ↔ -g₁ ≤ g₂ := by rw [le_iff_neg_le_neg, neg_neg]

lemma add_sub_le_cancel : f₁ + (f₂ - f₁) ≤ f₂ :=
  ⟨by simp [add_domain, sub_domain], fun _ _ h ↦ by simp [add_apply, sub_apply, h]⟩

lemma add_sub_le_cancel_left : f₁ + f₂ - f₁ ≤ f₂ := add_sub_assoc f₁ f₂ f₁ ▸ add_sub_le_cancel f₁ f₂

lemma add_sub_le_cancel_right : f₁ + f₂ - f₂ ≤ f₁ := add_comm f₁ f₂ ▸ add_sub_le_cancel_left f₂ f₁

lemma add_add_sub_le_cancel : f₁ + f₂ + (f₃ - f₂) ≤ f₁ + f₃ :=
  ⟨fun _ _ ↦ by simp_all [add_domain, sub_domain], fun _ _ h ↦ by simp [add_apply, sub_apply, h]⟩

lemma add_sub_sub_le_cancel : f₁ + f₂ - (f₁ - f₃) ≤ f₂ + f₃ :=
  ⟨fun _ _ ↦ by simp_all [add_domain, sub_domain], fun _ _ h ↦ by simp [add_apply, sub_apply, h]⟩

lemma sub_sub_sub_le_cancel_right : f₁ - f₂ - (f₃ - f₂) ≤ f₁ - f₃ := by
  simp only [sub_eq_add_neg, neg_add]
  exact sub_eq_add_neg (-f₃) (-f₂) ▸ add_add_sub_le_cancel f₁ (-f₂) (-f₃)

lemma sub_sub_sub_le_cancel_left : f₁ - f₂ - (f₁ - f₃) ≤ f₃ - f₂ :=
  sub_eq_add_neg f₁ f₂ ▸ neg_add_eq_sub f₂ f₃ ▸ add_sub_sub_le_cancel f₁ (-f₂) f₃

lemma sub_le_of_le_add (h : g ≤ g₁ + g₂) : g - g₂ ≤ g₁ := by
  constructor
  · exact (inf_le_of_left_le le_rfl).trans (le_inf_iff.mp <| add_domain g₁ g₂ ▸ h.1).1
  · intro ⟨x, hx⟩ ⟨y, hy⟩ rfl
    simp [sub_apply, @h.2 ⟨x, hx.1⟩ ⟨x, ⟨hy, hx.2⟩⟩ rfl, add_apply]

lemma sub_add_le_cancel : f₁ - f₂ + f₂ ≤ f₁ :=
  sub_eq_add_neg f₁ f₂ ▸ sub_neg_eq_add _ f₂ ▸ add_sub_le_cancel_right f₁ (-f₂)

lemma add_le_of_le_sub (h : g ≤ g₁ - g₂) : g + g₂ ≤ g₁ :=
  sub_neg_eq_add g g₂ ▸ sub_le_of_le_add (sub_eq_add_neg g₁ g₂ ▸ h)

lemma add_left_le_of_le (h : g₁ ≤ g₂) : f + g₁ ≤ f + g₂ := by
  constructor
  · simp only [add_domain, le_inf_iff, inf_le_left, true_and]
    exact (inf_le_of_right_le le_rfl).trans h.1
  · intro x y hxy
    simp_rw [add_apply, @h.2 ⟨x, x.2.2⟩ ⟨y, y.2.2⟩ hxy, hxy]

lemma add_right_le_of_le (h : g₁ ≤ g₂) : g₁ + f ≤ g₂ + f :=
  add_comm f g₁ ▸ add_comm f g₂ ▸ add_left_le_of_le f h

lemma sub_right_le_of_le (h : g₁ ≤ g₂) : g₁ - f ≤ g₂ - f :=
  sub_eq_add_neg g₁ f ▸ sub_eq_add_neg g₂ f ▸ add_right_le_of_le (-f) h

lemma sub_left_le_of_le (h : g₁ ≤ g₂) : f - g₁ ≤ f - g₂ :=
  neg_sub g₁ f ▸ neg_sub g₂ f ▸ le_iff_neg_le_neg.mp (sub_right_le_of_le f h)

end Inequalities

/-!
## B. Zero smul
-/

section

variable {𝕜 : Type*} [Field 𝕜] [Module 𝕜 E] [Module 𝕜 F]

lemma zero_smul_le (f : E →ₗ.[𝕜] F) : (0 : 𝕜) • f ≤ 0 := ⟨le_top, by simp⟩

@[simp]
lemma zero_smul_eq {f : E →ₗ.[𝕜] F} (h : f.domain = ⊤) : (0 : 𝕜) • f = 0 :=
  eq_of_le_of_domain_eq f.zero_smul_le h

end

/-!
## C. Finite sums
-/

section Sums

variable {α : Type*} [Fintype α] (f : α → E →ₗ.[R] F)

/-- A finite sum of partial linear maps.

  `sum f` and `∑ a, f a` are equal, but not by definition.
  With `sum f` both `domain` and `toFun` are made explicit. -/
def sum : E →ₗ.[R] F where
  domain := ⨅ a, (f a).domain
  toFun := ∑ a, (f a).toFun ∘ₗ inclusion (fun _ _ ↦ by simp_all only [mem_iInf])

lemma sum_domain : (sum f).domain = ⨅ a, (f a).domain := rfl

lemma sum_domain_le (a : α) : (sum f).domain ≤ (f a).domain := fun _ _ ↦ by simp_all [sum, mem_iInf]

@[simp]
lemma sum_apply (ψ : (sum f).domain) : sum f ψ = ∑ a, f a ⟨ψ, sum_domain_le f a ψ.2⟩ :=
  LinearMap.sum_apply Finset.univ (fun a ↦ (f a).toFun ∘ₗ inclusion (sum_domain_le f a)) ψ

end Sums

/-!
## D. Restricted composition
-/

section Composition

variable {G : Type*} [AddCommGroup G] [Module R G]
variable (g g₁ g₂ : F →ₗ.[R] G) (f f₁ f₂ : E →ₗ.[R] F)
variable {v : F →ₗ.[R] G} {u : E →ₗ.[R] F}

/-- `g ∘ᵣ f` is the composition of `g` with `f` restricted to a domain consisting of exactly those
  `x : f.domain` for which `f x ∈ g.domain`. -/
def compRestricted : E →ₗ.[R] G :=
  g.comp (f.domRestrict <| (g.domain.comap f.toFun).map f.domain.subtype) (by
    intro x
    have h : (x : E) ∈ (g.domain.comap f.toFun).map f.domain.subtype := x.2.1
    simp only [mem_map, mem_comap, toFun_eq_coe, subtype_apply] at h
    obtain ⟨y, hy, hy'⟩ := h
    rw [domRestrict_apply hy'.symm]
    exact hy)

@[inherit_doc compRestricted]
infixr:80 " ∘ᵣ " => compRestricted

lemma compRestricted_domain_le : (g ∘ᵣ f).domain ≤ f.domain := fun _ h ↦ h.2

lemma compRestricted_domain : (g ∘ᵣ f).domain = (g.domain.comap f.toFun).map f.domain.subtype := by
  change (f.domRestrict <| (g.domain.comap f.toFun).map f.domain.subtype).domain = _
  rw [domRestrict_domain]
  refine inf_of_le_left ?_
  intro x h
  simp only [mem_map, mem_comap, toFun_eq_coe, subtype_apply, Subtype.exists, exists_and_right,
    exists_eq_right] at h
  exact h.choose

lemma mem_compRestricted_domain_iff {x : E} :
    x ∈ (v ∘ᵣ u).domain ↔ ∃ h : x ∈ u.domain, u ⟨x, h⟩ ∈ v.domain := by
  simp [compRestricted_domain]

lemma mem_compRestricted_domain_iff' {x : E} :
    x ∈ (v ∘ᵣ u).domain ↔ ∃ y : u.domain, x = y ∧ ∃ y' : v.domain, u y = y' := by
  simp [mem_compRestricted_domain_iff]

lemma mem_domain_of_mem_compRestricted_domain (x : (v ∘ᵣ u).domain) : u ⟨x, x.2.2⟩ ∈ v.domain :=
  (mem_compRestricted_domain_iff.mp x.2).choose_spec

@[simp]
lemma compRestricted_apply (x : (v ∘ᵣ u).domain) :
    (v ∘ᵣ u) x = v ⟨u ⟨x, x.2.2⟩, mem_domain_of_mem_compRestricted_domain x⟩ := rfl

/-- The zero map is right-absorbing. -/
@[simp]
lemma compRestricted_zero : g ∘ᵣ (0 : E →ₗ.[R] F) = 0 := by
  ext
  · simp [mem_compRestricted_domain_iff]
  · exact g.map_zero

lemma compRestricted_assoc {H : Type*} [AddCommGroup H] [Module R H]
    (f₁ : G →ₗ.[R] H) (f₂ : F →ₗ.[R] G) (f₃ : E →ₗ.[R] F) :
    (f₁ ∘ᵣ f₂) ∘ᵣ f₃ = f₁ ∘ᵣ f₂ ∘ᵣ f₃ := by
  ext
  · simp only [mem_compRestricted_domain_iff]
    tauto
  · rfl

/-- `compRestricted` is the same as `comp` when the range of `u` is contained in `v.domain`. -/
lemma compRestricted_eq_comp (h : ∀ x : u.domain, u x ∈ v.domain) :
    v ∘ᵣ u = v.comp u h := by
  ext x
  · change _ ↔ x ∈ u.domain
    simp [mem_compRestricted_domain_iff, h]
  · rfl

/-- `compRestricted` is maximal amongst compositions of `v` with domain restrictions of `u`. -/
lemma comp_le_compRestricted
    {S : Submodule R E} (h : ∀ x : (u.domRestrict S).domain, u ⟨x, x.2.2⟩ ∈ v.domain) :
    v.comp (u.domRestrict S) h ≤ v ∘ᵣ u :=
  ⟨fun x hx ↦ mem_compRestricted_domain_iff.mpr ⟨hx.2, h ⟨x, hx⟩⟩, by aesop⟩

lemma compRestricted_mono_left {g g' : F →ₗ.[R] G} (h : g ≤ g') (f : E →ₗ.[R] F) :
    g ∘ᵣ f ≤ g' ∘ᵣ f := by
  constructor
  · intro x hx
    obtain ⟨hx', hfx⟩ := mem_compRestricted_domain_iff.mp hx
    exact mem_compRestricted_domain_iff.mpr ⟨hx', h.1 hfx⟩
  · intro x y hxy
    exact @h.2 ⟨f ⟨x, x.2.2⟩, mem_domain_of_mem_compRestricted_domain x⟩
      ⟨f ⟨y, y.2.2⟩, mem_domain_of_mem_compRestricted_domain y⟩ (by simp [hxy])

lemma compRestricted_mono_right (g : F →ₗ.[R] G) {f f' : E →ₗ.[R] F} (h : f ≤ f') :
    g ∘ᵣ f ≤ g ∘ᵣ f' := by
  constructor
  · intro x hx
    obtain ⟨hx', hfx⟩ := mem_compRestricted_domain_iff.mp hx
    exact mem_compRestricted_domain_iff.mpr ⟨h.1 hx', (@h.2 ⟨x, hx'⟩ ⟨x, h.1 hx'⟩ rfl) ▸ hfx⟩
  · intro x y hxy
    simp only [compRestricted_apply, @h.2 ⟨x, x.2.2⟩ ⟨y, y.2.2⟩ hxy]

@[simp]
lemma neg_compRestricted : (-g) ∘ᵣ f = -g ∘ᵣ f := rfl

@[simp]
lemma compRestricted_neg : g ∘ᵣ (-f) = -g ∘ᵣ f := by
  ext x hx hx'
  · simp [mem_compRestricted_domain_iff]
  · obtain ⟨h, h'⟩ := mem_compRestricted_domain_iff.mp (neg_domain (g ∘ᵣ f) ▸ hx')
    exact g.toFun.map_neg ⟨f ⟨x, h⟩, h'⟩

lemma add_compRestricted : (g₁ + g₂) ∘ᵣ f = g₁ ∘ᵣ f + g₂ ∘ᵣ f := by
  ext x hx hx'
  · simp only [mem_compRestricted_domain_iff, add_domain, mem_inf]
    tauto
  · simp [add_apply]

lemma sub_compRestricted : (g₁ - g₂) ∘ᵣ f = g₁ ∘ᵣ f - g₂ ∘ᵣ f := by
  simp [sub_eq_add_neg, add_compRestricted]

lemma compRestricted_add_ge : g ∘ᵣ f₁ + g ∘ᵣ f₂ ≤ g ∘ᵣ (f₁ + f₂) := by
  constructor
  · intro x hx
    obtain ⟨h₁, h₁'⟩ := mem_compRestricted_domain_iff.mp hx.1
    obtain ⟨h₂, h₂'⟩ := mem_compRestricted_domain_iff.mp hx.2
    exact mem_compRestricted_domain_iff.mpr ⟨⟨h₁, h₂⟩, add_mem h₁' h₂'⟩
  · intro x y hxy
    obtain ⟨h₁, h₁'⟩ := mem_compRestricted_domain_iff.mp x.2.1
    obtain ⟨h₂, h₂'⟩ := mem_compRestricted_domain_iff.mp x.2.2
    simp [← hxy, add_apply, ← g.map_add ⟨f₁ ⟨x, h₁⟩, h₁'⟩ ⟨f₂ ⟨x, h₂⟩, h₂'⟩]

lemma compRestricted_sub_ge : g ∘ᵣ f₁ - g ∘ᵣ f₂ ≤ g ∘ᵣ (f₁ - f₂) := by
  simp only [sub_eq_add_neg, ← compRestricted_neg]
  exact compRestricted_add_ge g f₁ (-f₂)

lemma compRestricted_smul {S : Type*} [DivisionRing S]
    [Module S E] [Module S F] [Module S G] [SMulCommClass S S F] [SMulCommClass S S G]
    {c : S} (hc : c ≠ 0) (g : F →ₗ.[S] G) (f : E →ₗ.[S] F) :
    g ∘ᵣ (c • f) = c • (g ∘ᵣ f) := by
  ext x hx hx'
  · simp [mem_compRestricted_domain_iff, g.domain.smul_mem_iff hc]
  · obtain ⟨h, h'⟩ := mem_compRestricted_domain_iff.mp (smul_domain c (g ∘ᵣ f) ▸ hx')
    exact g.toFun.map_smul c ⟨f ⟨x, h⟩, h'⟩

@[simp]
lemma smul_compRestricted {M : Type*} [Monoid M] [DistribMulAction M G] [SMulCommClass R M G]
    (c : M) (g : F →ₗ.[R] G) (f : E →ₗ.[R] F) :
    (c • g) ∘ᵣ f = c • (g ∘ᵣ f) := by
  ext
  · simp [compRestricted_domain]
  · simp

end Composition

/-!
## E. Monoid

Partial linear maps `E →ₗ.[R] E` with `compRestricted` for multiplication and
the identity map (domain `⊤`) for `1` comprise a monoid.
-/

section Monoid

instance instMonoid : Monoid (E →ₗ.[R] E) where
  mul := compRestricted
  mul_assoc := compRestricted_assoc
  one := ⟨⊤, topEquiv.toLinearMap⟩
  one_mul f := by
    change ⟨⊤, topEquiv.toLinearMap⟩ ∘ᵣ f = f
    ext
    · simp [mem_compRestricted_domain_iff]
    · rfl
  mul_one f := by
    change f ∘ᵣ ⟨⊤, topEquiv.toLinearMap⟩ = f
    ext
    · simp [mem_compRestricted_domain_iff]
    · rfl

lemma mul_def (f₁ f₂ : E →ₗ.[R] E) : f₁ * f₂ = f₁ ∘ᵣ f₂ := rfl

@[simp]
lemma one_domain : (1 : E →ₗ.[R] E).domain = ⊤ := rfl

@[simp]
lemma one_toFun : (1 : E →ₗ.[R] E).toFun = topEquiv.toLinearMap := rfl

@[simp]
lemma one_coe : (1 : E →ₗ.[R] E).toFun' = ⇑topEquiv.toLinearMap := rfl

end Monoid

/-!
## F. Inverses
-/

section Inverses

/-- The kernel of `f.toFun` is trivial exactly when the kernel of `f` is. -/
lemma toFun_ker_eq_bot_iff {f : E →ₗ.[R] F} : f.toFun.ker = ⊥ ↔ f.ker = ⊥ := by
  rw [LinearMap.ker_eq_bot', LinearPMap.ker_eq_bot']
  rfl

variable {f : E →ₗ.[R] F} (h_ker : f.toFun.ker = ⊥)
include h_ker

lemma inverse_ker : f.inverse.toFun.ker = ⊥ := by
  refine LinearMap.ker_eq_bot'.mpr fun ⟨y, hy⟩ hy' ↦ ?_
  obtain ⟨x, hx⟩ := inverse_domain (f := f) ▸ hy
  simp_all [inverse_apply_eq (x := x) (y := ⟨y, hy⟩) (toFun_ker_eq_bot_iff.mp h_ker) hx]

lemma inverse_inverse : f.inverse.inverse = f := by
  ext x hx hx'
  · rw [inverse_domain, inverse_range (toFun_ker_eq_bot_iff.mp h_ker)]
  · refine inverse_apply_eq (y := ⟨x, hx⟩) (x := ⟨f ⟨x, hx'⟩, by simp [inverse_domain]⟩) ?_ ?_
    · exact toFun_ker_eq_bot_iff.mp (inverse_ker h_ker)
    · exact inverse_apply_eq (y := ⟨f ⟨x, hx'⟩, by simp [inverse_domain]⟩) (x := ⟨x, hx'⟩)
        (toFun_ker_eq_bot_iff.mp h_ker) rfl

lemma inverse_compRestricted_eq : f.inverse ∘ᵣ f = domRestrict 1 f.domain := by
  ext x hx hx'
  · simp [mem_compRestricted_domain_iff, inverse_domain, ← toFun_eq_coe, -coe_toFun_eq_coe]
  · exact inverse_apply_eq (x := ⟨x, hx.2⟩) (toFun_ker_eq_bot_iff.mp h_ker) rfl

lemma compRestricted_inverse_eq : f ∘ᵣ f.inverse = domRestrict 1 f.inverse.domain := by
  nth_rw 1 [← inverse_inverse h_ker]
  exact inverse_compRestricted_eq (inverse_ker h_ker)

end Inverses

end LinearPMap
