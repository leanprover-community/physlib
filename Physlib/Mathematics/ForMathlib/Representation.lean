/-
Copyright (c) 2026 Andrea Pari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrea Pari
-/
module

public import Mathlib.LinearAlgebra.PiTensorProduct.Basic
public import Mathlib.RepresentationTheory.Intertwining

/-!

# Constructions on representations

The tensor product of a family of representations, the evaluation of a linear form on a vector, and
the cast along an equality of indices.

## i. Overview

`piTprod ρ` is the representation of a monoid `G` on the tensor product `⨂[k] i, M i` of a family
of representations `ρ i` on the `k`-modules `M i`. An element `g` of `G` acts by `ρ i g` on every
factor at once. Mathlib has this for two factors, `Representation.tprod`.

For a Lorentz tensor `T^μ_ν` the two factors are the vectors, where a Lorentz transformation `Λ`
acts by `v^μ ↦ Λ^μ_σ v^σ`, and the covectors, where it acts by `α_ν ↦ α_τ (Λ⁻¹)^τ_ν`. Then
`piTprod ρ Λ` sends the pure tensor `v ⊗ α` to `Λv ⊗ Λα` (`piTprod_tprod`), so
`(ΛT)^μ_ν = Λ^μ_σ (Λ⁻¹)^τ_ν T^σ_τ`.

Pure tensors span the tensor product. So a map out of it that commutes with the action on pure
tensors commutes with it on all tensors (`map_piTprod_of_tprod`).

The evaluation of a linear form on a vector, `v ⊗ α ↦ α v` (`contractRight`) or `α ⊗ v ↦ α v`
(`contractLeft`), is an intertwining map to the trivial representation (B). For a Lorentz vector
`v^μ` and a covector `α_μ` it says that `v^μ α_μ` does not change under `Λ`.

For a family of representations `ρ i`, an equality `i = j` moves a vector of `M i` to `M j` without
changing it, `Representation.Equiv.cast` (C).

## ii. Key results

- `Representation.piTprod` : the representation on `⨂[k] i, M i` of a family of representations.
- `Representation.map_piTprod_of_tprod` : a map that commutes with `piTprod ρ` on pure tensors
  commutes with it on all tensors.
- `Representation.contractRight`, `Representation.contractLeft` : the evaluation of a linear form
  on a vector as an intertwining map to the trivial representation.
- `Representation.Equiv.cast` : Mathlib's `LinearEquiv.cast` as an equivalence of representations.

## iii. Table of contents

- A. The representation on a tensor product of a family
- B. The evaluation of linear forms
- C. Moving a vector along an equality of indices

## iv. References

There are no known references for the material in this module.

-/

@[expose] public section

open TensorProduct

/-!

## A. The representation on a tensor product of a family

`piTprod ρ` transforms each factor by its own representation.

-/

namespace Representation

variable {k G ι : Type*} [CommSemiring k] [Monoid G] {M : ι → Type*} [∀ i, AddCommMonoid (M i)]
  [∀ i, Module k (M i)]

/-- `piTprod ρ` is the representation `g ↦ ⨂ i, ρ i g` on `⨂[k] i, M i`. Each `g` acts on every
factor at once. -/
def piTprod (ρ : Π i, Representation k G (M i)) : Representation k G (⨂[k] i, M i) :=
  PiTensorProduct.mapMonoidHom.comp (MonoidHom.pi ρ)

/-- `piTprod ρ g` is Mathlib's `PiTensorProduct.map` of the `ρ i g`. -/
lemma piTprod_apply (ρ : Π i, Representation k G (M i)) (g : G) :
    piTprod ρ g = PiTensorProduct.map fun i => ρ i g :=
  rfl

/-- On a pure tensor, `piTprod ρ g` acts by `ρ i g` on the vector at each index `i`. -/
@[simp]
lemma piTprod_tprod (ρ : Π i, Representation k G (M i)) (g : G) (m : Π i, M i) :
    piTprod ρ g (⨂ₜ[k] i, m i) = ⨂ₜ[k] i, ρ i g (m i) :=
  PiTensorProduct.map_tprod _ _

/-- A `σ`-semilinear map `f` out of `⨂[k] i, M i` with `f (piTprod ρ g t) = τ g (f t)` for every
pure tensor `t` has it for every tensor `t`. The ring map `σ : k →+* l` can be complex
conjugation. -/
lemma map_piTprod_of_tprod {l U : Type*} [Semiring l] [AddCommMonoid U] [Module l U]
    {τ : Representation l G U} {σ : k →+* l} {ρ : Π i, Representation k G (M i)}
    (f : (⨂[k] i, M i) →ₛₗ[σ] U) (g : G)
    (h : ∀ m : Π i, M i, f (piTprod ρ g (⨂ₜ[k] i, m i)) = τ g (f (⨂ₜ[k] i, m i)))
    (t : ⨂[k] i, M i) : f (piTprod ρ g t) = τ g (f t) :=
  LinearMap.congr_fun (LinearMap.ext_on_range PiTensorProduct.span_tprod_eq_top h :
    f ∘ₛₗ piTprod ρ g = τ g ∘ₛₗ f) t

end Representation

/-!

## B. The evaluation of linear forms

The evaluation `v ⊗ α ↦ α v` of a linear form on a vector does not change when `g` acts on both,
by `ρ g` on `v` and by the dual representation on `α`. For a vector `v^μ` and a covector `α_μ` it
is the invariance of `v^μ α_μ`.

-/

namespace Representation

variable {k G V : Type*} [CommSemiring k] [Group G] [AddCommMonoid V] [Module k V]

/-- Mathlib's `contractRight`, `v ⊗ α ↦ α v`, as an intertwining map from `ρ ⊗ ρ.dual` to the
trivial representation. -/
def contractRight (ρ : Representation k G V) :
    (ρ.tprod ρ.dual).IntertwiningMap (trivial k G k) :=
  ⟨_root_.contractRight k V, fun g => TensorProduct.ext' fun v α => by
    simp [Module.Dual.transpose_apply]⟩

/-- `ρ.contractRight` evaluates the linear form on the vector, `v ⊗ α ↦ α v`. -/
@[simp]
lemma contractRight_tmul (ρ : Representation k G V) (v : V) (α : Module.Dual k V) :
    ρ.contractRight (v ⊗ₜ α) = α v :=
  rfl

/-- Mathlib's `contractLeft`, `α ⊗ v ↦ α v`, as an intertwining map from `ρ.dual ⊗ ρ` to the
trivial representation. -/
def contractLeft (ρ : Representation k G V) :
    (ρ.dual.tprod ρ).IntertwiningMap (trivial k G k) :=
  ⟨_root_.contractLeft k V, fun g => TensorProduct.ext' fun α v => by
    simp [Module.Dual.transpose_apply]⟩

/-- `ρ.contractLeft` evaluates the linear form on the vector, `α ⊗ v ↦ α v`. -/
@[simp]
lemma contractLeft_tmul (ρ : Representation k G V) (α : Module.Dual k V) (v : V) :
    ρ.contractLeft (α ⊗ₜ v) = α v :=
  rfl

end Representation

/-!

## C. Moving a vector along an equality of indices

For a family of representations `ρ i`, an equality `i = j` gives an equivalence of `ρ i` with
`ρ j`, Mathlib's `LinearEquiv.cast` with the actions kept.

-/

namespace Representation

variable {k G ι : Type*} [CommSemiring k] [Monoid G] {M : ι → Type*} [∀ i, AddCommMonoid (M i)]
  [∀ i, Module k (M i)]

/-- `Representation.Equiv.cast ρ h` is Mathlib's `LinearEquiv.cast h` as an equivalence of the
representations `ρ i` and `ρ j` of a family, for `h : i = j`. -/
protected def Equiv.cast (ρ : Π i, Representation k G (M i)) {i j : ι} (h : i = j) :
    (ρ i).Equiv (ρ j) :=
  .mk (LinearEquiv.cast h) fun _ => by subst h; rfl

/-- `Representation.Equiv.cast ρ h` is Mathlib's `cast` of the vector. -/
@[simp]
lemma Equiv.cast_apply (ρ : Π i, Representation k G (M i)) {i j : ι} (h : i = j) (x : M i) :
    Representation.Equiv.cast ρ h x = cast (congrArg M h) x :=
  rfl

end Representation
