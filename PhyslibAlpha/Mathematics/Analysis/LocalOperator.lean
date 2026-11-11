/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Mathlib.Topology.Algebra.Support
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Ker
public import Mathlib.Tactic.Bound.Init

/-!

# Linear operators that do not enlarge support

A linear operator on a space of functions with support contained in the support of the argument.

## i. Overview

A linear operator on a space of functions with support contained in the support of the argument. It
acts on compactly supported functions and has a kernel. Such operators agree at a point when their
arguments agree near it.

## ii. Key results

- `compactFields` : Compactly supported admissible fields form the source space of Green operators.
- `compactSources` : The compact test-field space depends on the admissible fields rather than the
  operator.
- `compactOperator` : The restriction of the equation to compactly supported admissible fields.
- `solutionSpace` : Homogeneous admissible fields are the kernel of the field operator.
- `IsLocalFieldSpace` : Admissibility is local when a function locally agreeing with admissible
  fields is admissible.
- `FieldIntertwiner` : A local linear map that commutes with two field equations.
- `compactMap` : Restrict the local intertwiner to compact test fields.

## iii. Table of contents

- A. Linear field equations and compact sources
- B. Local field equations and causal agreement
- C. Differential constraints and Green responses

## iv. References

None.

## A. Linear field equations and compact sources

- `compactFields` : Compactly supported admissible fields form the source space of Green operators.
- `compactSources` : The compact test-field space depends on the admissible fields rather than the
  operator.
- `compactOperator` : The restriction of the equation to compactly supported admissible fields.
- `solutionSpace` : Homogeneous admissible fields are the kernel of the field operator.

Lemmas: `operator_mem_compactSources`, `compactOperator_coe`, `mem_solutionSpace`.

## B. Local field equations and causal agreement

- `IsLocalFieldSpace` : Admissibility is local when a function locally agreeing with admissible
  fields is admissible.

Lemmas: `notMem_tsupport_sub_iff_eventuallyEq`, `operator_eventuallyEq`,
`operator_eq_of_eventuallyEq`.

## C. Differential constraints and Green responses

- `FieldIntertwiner` : A local linear map that commutes with two field equations.
- `compactMap` : Restrict the local intertwiner to compact test fields.

-/

@[expose] public section

noncomputable section

open scoped Topology

section
variable {𝕜 M V : Type*} [Ring 𝕜] [TopologicalSpace M] [AddCommGroup V] [Module 𝕜 V]

/-- A linear equation on admissible fields with the support locality of a differential operator.
Smoothness is supplied by the admissible field submodule in each application. -/
structure LocalOperator (S : Submodule 𝕜 (M → V)) where
  /-- The field differential operator on admissible fields. -/
  operator : S →ₗ[𝕜] S
  /-- A local field equation cannot create support away from the field. -/
  support_operator : ∀ u : S, tsupport (operator u : M → V) ⊆ tsupport (u : M → V)

/-- Compactly supported admissible fields form the source space of Green operators. -/
def compactFields (S : Submodule 𝕜 (M → V)) : Submodule 𝕜 S where
  carrier := {u | HasCompactSupport (u : M → V)}
  zero_mem' := by
    change IsCompact (tsupport (0 : M → V))
    simp
  add_mem' := fun hu hv => hu.add hv
  smul_mem' := fun a u hu => by
    change IsCompact (tsupport (fun x => a • (u : M → V) x))
    exact hu.of_isClosed_subset (isClosed_tsupport _) (tsupport_smul_subset_right _ _)
end

namespace LocalOperator

section
variable {𝕜 M V : Type*} [Ring 𝕜] [TopologicalSpace M] [AddCommGroup V] [Module 𝕜 V]
variable {S : Submodule 𝕜 (M → V)} (P : LocalOperator S)

/-- The compact test-field space depends on the admissible fields rather than the operator. -/
abbrev compactSources (_P : LocalOperator S) : Submodule 𝕜 S := compactFields S

/-- The equation preserves compact sources by locality. -/
lemma operator_mem_compactSources (u : P.compactSources) :
    P.operator u.val ∈ P.compactSources :=
  u.property.of_isClosed_subset (isClosed_tsupport _) (P.support_operator u.val)

/-- The restriction of the equation to compactly supported admissible fields. -/
def compactOperator : P.compactSources →ₗ[𝕜] P.compactSources :=
  (P.operator.comp P.compactSources.subtype).codRestrict P.compactSources
    P.operator_mem_compactSources

@[simp]
lemma compactOperator_coe (u : P.compactSources) :
    (P.compactOperator u).val = P.operator u.val := rfl

/-- Homogeneous admissible fields are the kernel of the field operator. -/
def solutionSpace : Submodule 𝕜 S := P.operator.ker

@[simp]
lemma mem_solutionSpace (u : S) : u ∈ P.solutionSpace ↔ P.operator u = 0 := Iff.rfl
end

end LocalOperator

section
variable {𝕜 M V : Type*} [Ring 𝕜] [TopologicalSpace M] [AddCommGroup V] [Module 𝕜 V] {S : Submodule
    𝕜 (M → V)}

/-- Admissibility is local when a function locally agreeing with admissible fields is admissible. -/
def IsLocalFieldSpace (S : Submodule 𝕜 (M → V)) : Prop :=
  ∀ u : M → V, (∀ x : M, ∃ v : S, u =ᶠ[𝓝 x] (v : M → V)) → u ∈ S

/-- Vanishing support of a difference at a point is exactly equality of field germs. -/
lemma notMem_tsupport_sub_iff_eventuallyEq {f g : M → V} {x : M} :
    x ∉ tsupport (f - g) ↔ f =ᶠ[𝓝 x] g := by
  rw [notMem_tsupport_iff_eventuallyEq]
  constructor
  · exact fun h => h.mono (fun _ hy => sub_eq_zero.mp hy)
  · exact fun h => h.mono (fun _ hy => sub_eq_zero.mpr hy)
end

namespace LocalOperator

section
variable {𝕜 M V : Type*} [Ring 𝕜] [TopologicalSpace M] [AddCommGroup V] [Module 𝕜 V] {S : Submodule
    𝕜 (M → V)}
variable (P : LocalOperator S)

/-- A local field operator preserves equality of germs. -/
lemma operator_eventuallyEq {u v : S} {x : M}
    (h : (u : M → V) =ᶠ[𝓝 x] (v : M → V)) :
    (P.operator u : M → V) =ᶠ[𝓝 x] (P.operator v : M → V) := by
  have hx : x ∉ tsupport ((u - v : S) : M → V) :=
    notMem_tsupport_sub_iff_eventuallyEq.mpr h
  have hPx : x ∉ tsupport (P.operator (u - v) : M → V) :=
    fun hm => hx (P.support_operator _ hm)
  rw [map_sub] at hPx
  exact notMem_tsupport_sub_iff_eventuallyEq.mp hPx

/-- Equality of field germs implies equality of their equations at the observation point. -/
lemma operator_eq_of_eventuallyEq {u v : S} {x : M}
    (h : (u : M → V) =ᶠ[𝓝 x] (v : M → V)) :
    (P.operator u : M → V) x = (P.operator v : M → V) x :=
  (P.operator_eventuallyEq h).eq_of_nhds
end

end LocalOperator

section
variable {𝕜 M V W : Type*} [Ring 𝕜] [TopologicalSpace M] [AddCommGroup V] [Module 𝕜 V] [AddCommGroup
    W] [Module 𝕜 W] {S : Submodule 𝕜 (M → V)} {T : Submodule 𝕜 (M → W)}

/-- A local linear map that commutes with two field equations.
The two equations may act on different field types, as for divergence of a vector wave equation. -/
structure FieldIntertwiner (P : LocalOperator S) (R : LocalOperator T) where
  /-- The differential constraint or transformation of fields. -/
  toLinearMap : S →ₗ[𝕜] T
  /-- Differential constraints do not enlarge support. -/
  support : ∀ u, tsupport (toLinearMap u : M → W) ⊆ tsupport (u : M → V)
  /-- Apply the constraint before or after the corresponding field equation. -/
  commutes : ∀ u, R.operator (toLinearMap u) = toLinearMap (P.operator u)
end

namespace FieldIntertwiner

section
variable {𝕜 M V W : Type*} [Ring 𝕜] [TopologicalSpace M] [AddCommGroup V] [Module 𝕜 V] [AddCommGroup
    W] [Module 𝕜 W] {S : Submodule 𝕜 (M → V)} {T : Submodule 𝕜 (M → W)}
variable {P : LocalOperator S} {R : LocalOperator T} (Q : FieldIntertwiner P R)

/-- Restrict the local intertwiner to compact test fields. -/
def compactMap : P.compactSources →ₗ[𝕜] R.compactSources :=
  (Q.toLinearMap.comp P.compactSources.subtype).codRestrict _
    (fun f => f.property.of_isClosed_subset (isClosed_tsupport _) (Q.support f.val))
end

end FieldIntertwiner
