/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RepresentationTheory.Continuous.Basic
public import Mathlib.Topology.Algebra.Module.Spaces.ContinuousLinearMap

/-!
# Restricting a continuous representation to an invariant submodule

This file restricts a continuous representation of a monoid to a submodule preserved by every
action operator, the continuous counterpart of Mathlib's `Representation.subrepresentation`.

## Main definitions

* `TauCeti.ContRepresentation.subrepresentation`: the restriction of a continuous representation to
  an invariant submodule.

## Main results

* `TauCeti.ContRepresentation.mem_invariants_subrepresentation`: a vector of the submodule is
  invariant for the restricted representation exactly when it is invariant for the ambient one.
* `TauCeti.ContRepresentation.toRepresentation_subrepresentation`: the underlying representation of
  a restricted continuous representation is the restriction of the underlying representation.
* `TauCeti.ContRepresentation.continuous_subrepresentation`: the restriction of a continuous
  representation to an invariant submodule is again continuous.
-/

public section

namespace TauCeti

namespace ContRepresentation

section Restriction

variable {R G V : Type*} [Ring R] [Monoid G] [AddCommGroup V] [TopologicalSpace V]
  [IsTopologicalAddGroup V] [Module R V]

/-- The restriction of a continuous representation to an invariant submodule. This is the
continuous counterpart of `Representation.subrepresentation`. -/
def subrepresentation (π : ContRepresentation R G V) (W : Submodule R V)
    (hW : ∀ g, ∀ v ∈ W, π g v ∈ W) : ContRepresentation R G W :=
  .ofMonoidHom
    { toFun g := (π g).restrict (hW g)
      map_one' := by ext v; simp
      map_mul' g h := by ext v; simp }

variable {π : ContRepresentation R G V} {W : Submodule R V} {hW : ∀ g, ∀ v ∈ W, π g v ∈ W}

/-- The restricted action is the ambient action, read on the underlying vectors. -/
@[simp]
theorem coe_subrepresentation_apply (g : G) (v : W) :
    ((subrepresentation π W hW g v : W) : V) = π g (v : V) :=
  (rfl)

-- Not `@[simp]`: Mathlib's `@[simp] ContRepresentation.mem_invariants` already rewrites the
-- left-hand side to `∀ g, subrepresentation π W hW g x = x`, so the attribute would be a `simpNF`
-- violation ("Left-hand side simplifies … using `ContRepresentation.mem_invariants`"). This is the
-- `rw`-usable form of that normalization, as `ContRepresentation.mem_invariants_restrict` is for
-- the restriction along a subgroup.
/-- A vector of an invariant submodule is invariant for the restricted representation exactly when
it is invariant for the ambient one: the restricted action is the ambient action. -/
theorem mem_invariants_subrepresentation {x : W} :
    x ∈ (subrepresentation π W hW).invariants ↔ (x : V) ∈ π.invariants := by
  simp [ContRepresentation.mem_invariants, Subtype.ext_iff]

/-- The underlying representation of a restricted continuous representation is the restriction of
the underlying representation. -/
@[simp]
theorem toRepresentation_subrepresentation : (subrepresentation π W hW).toRepresentation
      = π.toRepresentation.subrepresentation W fun g _ hv => hW g _ hv := by
  rfl

end Restriction

section Continuity

variable {𝕜 G V : Type*} [NormedField 𝕜] [Monoid G] [TopologicalSpace G] [AddCommGroup V]
  [TopologicalSpace V] [IsTopologicalAddGroup V] [Module 𝕜 V] [ContinuousConstSMul 𝕜 V]
  {π : ContRepresentation 𝕜 G V} {W : Submodule 𝕜 V} {hW : ∀ g, ∀ v ∈ W, π g v ∈ W}

/-- Restricting a continuous representation to an invariant submodule preserves continuity: from
continuity of `g ↦ π g` as a map into the continuous linear endomorphisms of `V`, the restricted
action `g ↦ subrepresentation π W hW g` is continuous into those of `W`. This supplies the
continuity argument that `matrixCoeff` and the rest of the continuous-representation API take
explicitly, so a subrepresentation can be used wherever a continuous representation is expected. -/
theorem continuous_subrepresentation (hπ : Continuous π) :
    Continuous (subrepresentation π W hW) := by
  rw [(ContinuousLinearMap.isInducing_postcomp W.subtypeL
    Topology.IsInducing.subtypeVal).continuous_iff]
  exact (ContinuousLinearMap.precomp V W.subtypeL).continuous.comp hπ

end Continuity

end ContRepresentation

end TauCeti
