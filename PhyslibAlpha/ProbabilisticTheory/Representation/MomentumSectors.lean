/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Mathlib.Algebra.Module.Submodule.Range
public import Mathlib.LinearAlgebra.Span.Basic
public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.Algebra.Group.Hom.Defs

/-!

# Crystal momentum sectors

Sectors and fibers of definite crystal momentum for a translation-invariant system, and their
conservation.

## i. Overview

The translation symmetry of a crystal has a basic consequence: a time evolution, a
Hamiltonian, or a response function that commutes with lattice translations conserves crystal
momentum. Let translations `g` act linearly on a vector space `V`, the states or the observables of
the crystal, by `β g`, and let `χ g` be the phase picked up by a translation: for a lattice
translation `n` and wavevector `k`, `χ n = exp (i k n)`. Two spaces are attached to `χ`:

* the *sector of momentum `χ`*, the vectors with `β g v = χ g v` for all `g`: the Bloch waves;
* the *fiber at momentum `χ`*, `V` modulo the differences `β g v - χ g v`.

In an infinite crystal a configuration of finite extent contains no Bloch wave, so the sector can
be zero, whereas the fiber is the space of Fourier transforms evaluated at momentum `χ`. A linear
map that commutes with the translations, such as the Hamiltonian, preserves every sector and acts
on every fiber. Both statements are purely algebraic. No claim is made that the space decomposes
into a sum of momentum sectors; that needs analysis and is a separate matter.

## ii. Key results

- `sector` : the Bloch waves of crystal momentum `χ`.
- `Fiber` : the space of crystal momentum `χ`, a quotient of the whole space.
- `IsEquivariant` : a linear map commuting with the translations.
- `IsEquivariant.mapsTo_sector` : a translation-invariant map conserves crystal momentum.
- `IsEquivariant.fiberMap` : a translation-invariant map acts within each fiber.
- `fiberMap_id`, `fiberMap_comp` : the action on fibers respects composition.
- `sectorToFiber` : a Bloch wave defines a vector of the fiber of the same momentum.

## iii. Table of contents

- A. Sectors and fibers
- B. Equivariant maps
- C. Functoriality
- D. From sectors to fibers

## iv. References

* N. Ashcroft & N. D. Mermin, Solid State Physics, Chapters 4 and 8.
* F. Bloch, Über die Quantenmechanik der Elektronen in Kristallgittern, Z. Phys. 52 (1929). [ref:
  bloch_1929]

-/

@[expose] public section

namespace ProbabilisticTheory

namespace Representation

variable {G K V W X : Type*} [Monoid G] [CommRing K]
  [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W] [AddCommGroup X] [Module K X]

/-!

## A. Sectors and fibers

-/

/-- The momentum sector of the character `χ`: vectors on which `g` acts as the scalar `χ g`. -/
def sector (β : G →* Module.End K V) (χ : G → K) : Submodule K V where
  carrier := {v | ∀ g, β g v = χ g • v}
  add_mem' ha hb g := by simp [ha g, hb g]
  zero_mem' g := by simp
  smul_mem' c v hv g := by rw [map_smul, hv g, smul_comm]

lemma mem_sector {β : G →* Module.End K V} {χ : G → K} {v : V} :
    v ∈ sector β χ ↔ ∀ g, β g v = χ g • v := Iff.rfl

/-- The submodule `span {β g v - χ g • v}` whose quotient is the momentum fiber. It is the
"coboundary" submodule of the twisted action. -/
def cobound (β : G →* Module.End K V) (χ : G → K) : Submodule K V :=
  Submodule.span K {w | ∃ g v, w = β g v - χ g • v}

lemma sub_smul_mem_cobound (β : G →* Module.End K V) (χ : G → K) (g : G) (v : V) :
    β g v - χ g • v ∈ cobound β χ :=
  Submodule.subset_span ⟨g, v, rfl⟩

/-- The momentum fiber of the character `χ`: `V` modulo the vectors `β g v - χ g • v`. -/
abbrev Fiber (β : G →* Module.End K V) (χ : G → K) : Type _ := V ⧸ cobound β χ

/-- The canonical projection `V → V(χ)`. -/
def Fiber.mk (β : G →* Module.End K V) (χ : G → K) : V →ₗ[K] Fiber β χ :=
  (cobound β χ).mkQ

/-- In the fiber, `g` acts as the scalar `χ g`. -/
lemma Fiber.mk_action (β : G →* Module.End K V) (χ : G → K) (g : G) (v : V) :
    Fiber.mk β χ (β g v) = χ g • Fiber.mk β χ v := by
  rw [← map_smul, ← sub_eq_zero, ← map_sub]
  exact (Submodule.Quotient.mk_eq_zero _).2 (sub_smul_mem_cobound β χ g v)

/-!

## B. Equivariant maps

-/

/-- A linear map intertwining two actions of the same monoid. -/
def IsEquivariant (β : G →* Module.End K V) (β' : G →* Module.End K W)
    (T : V →ₗ[K] W) : Prop :=
  ∀ g v, T (β g v) = β' g (T v)

variable {β : G →* Module.End K V} {β' : G →* Module.End K W} {β'' : G →* Module.End K X}
  {T : V →ₗ[K] W} {S : W →ₗ[K] X} {χ : G → K}

/-- Every equivariant linear map preserves each momentum sector. -/
lemma IsEquivariant.mapsTo_sector (hT : IsEquivariant β β' T) {v : V}
    (hv : v ∈ sector β χ) : T v ∈ sector β' χ := fun g => by
  rw [← hT, hv g, map_smul]

/-- The restriction of an equivariant map to a momentum sector. -/
def IsEquivariant.sectorMap (hT : IsEquivariant β β' T) (χ : G → K) :
    sector β χ →ₗ[K] sector β' χ :=
  T.restrict fun _ hv => hT.mapsTo_sector hv

@[simp]
lemma IsEquivariant.coe_sectorMap (hT : IsEquivariant β β' T) (v : sector β χ) :
    (hT.sectorMap χ v : W) = T v := rfl

/-- An equivariant map sends the span defining the fiber of `V` into the span defining the fiber
of `W`. -/
lemma IsEquivariant.cobound_le_comap (hT : IsEquivariant β β' T) (χ : G → K) :
    cobound β χ ≤ (cobound β' χ).comap T := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨g, v, rfl⟩
  have : T (β g v - χ g • v) = β' g (T v) - χ g • T v := by rw [map_sub, map_smul, hT]
  simpa [this] using sub_smul_mem_cobound β' χ g (T v)

/-- Every equivariant linear map induces a well-defined linear map on each momentum fiber. -/
def IsEquivariant.fiberMap (hT : IsEquivariant β β' T) (χ : G → K) :
    Fiber β χ →ₗ[K] Fiber β' χ :=
  Submodule.mapQ _ _ T (hT.cobound_le_comap χ)

@[simp]
lemma IsEquivariant.fiberMap_mk (hT : IsEquivariant β β' T) (χ : G → K) (v : V) :
    hT.fiberMap χ (Fiber.mk β χ v) = Fiber.mk β' χ (T v) := rfl

/-- The fiber map is the unique map making the square with the projections commute. -/
lemma IsEquivariant.fiberMap_comp_mk (hT : IsEquivariant β β' T) (χ : G → K) :
    (hT.fiberMap χ).comp (Fiber.mk β χ) = (Fiber.mk β' χ).comp T := rfl

/-!

## C. Functoriality

-/

lemma isEquivariant_id (β : G →* Module.End K V) : IsEquivariant β β LinearMap.id :=
  fun _ _ => rfl

lemma IsEquivariant.comp (hS : IsEquivariant β' β'' S) (hT : IsEquivariant β β' T) :
    IsEquivariant β β'' (S ∘ₗ T) := fun g v => by
  simp [hT g v, hS g (T v)]

lemma fiberMap_id (χ : G → K) :
    (isEquivariant_id β).fiberMap χ = LinearMap.id := by
  ext v; rfl

lemma IsEquivariant.fiberMap_comp (hS : IsEquivariant β' β'' S) (hT : IsEquivariant β β' T)
    (χ : G → K) :
    (hS.comp hT).fiberMap χ = (hS.fiberMap χ) ∘ₗ (hT.fiberMap χ) := by
  ext v; rfl

/-- Equivariant maps commute with the dynamics they generate: if `D` is an equivariant
endomorphism, it preserves every sector and descends to every fiber. This is the form used for
translation-invariant evolution. -/
lemma IsEquivariant.mapsTo_sector_self {D : V →ₗ[K] V} (hD : IsEquivariant β β D) {v : V}
    (hv : v ∈ sector β χ) : D v ∈ sector β χ := hD.mapsTo_sector hv

/-!

## D. From sectors to fibers

-/

/-- The canonical map from the sector of `χ` to the fiber of `χ`. -/
def sectorToFiber (β : G →* Module.End K V) (χ : G → K) :
    sector β χ →ₗ[K] Fiber β χ :=
  (Fiber.mk β χ).comp (sector β χ).subtype

/-- The canonical map from sector to fiber is natural for equivariant maps. -/
lemma IsEquivariant.fiberMap_comp_sectorToFiber (hT : IsEquivariant β β' T) (χ : G → K) :
    (hT.fiberMap χ).comp (sectorToFiber β χ)
      = (sectorToFiber β' χ).comp (hT.sectorMap χ) := rfl

end Representation

end ProbabilisticTheory
