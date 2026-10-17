/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RepresentationTheory.Continuous.Basic
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Quotient
public import Mathlib.Topology.Algebra.Module.Spaces.ContinuousLinearMap

/-!
# Restricting a continuous representation to an invariant submodule

This file restricts a continuous representation of a monoid to a submodule preserved by every action
operator, the continuous counterpart of Mathlib's `Representation.subrepresentation`, and descends
it to the quotient by such a submodule, the continuous counterpart of `Representation.quotient`.

## i. Overview

This file restricts a continuous representation of a monoid to a submodule preserved by every
action operator, the continuous counterpart of Mathlib's `Representation.subrepresentation`, and
descends it to the quotient by such a submodule, the continuous counterpart of
`Representation.quotient`.

## ii. Key results

* `ContRepresentation.subrepresentation`: the restriction of a continuous representation to
  an invariant submodule.
* `ContRepresentation.subrepresentationInclusion`: the continuous intertwiner including a
  subrepresentation into its ambient representation.
* `ContRepresentation.quotient`: a continuous representation descended to the quotient by an
  invariant submodule, the continuous counterpart of `Representation.quotient`.

* `ContRepresentation.mem_invariants_subrepresentation`: a vector of the submodule is
  invariant for the restricted representation exactly when it is invariant for the ambient one.
* `ContRepresentation.toRepresentation_subrepresentation`: the underlying representation of
  a restricted continuous representation is the restriction of the underlying representation.
* `Subrepresentation.toRepresentation_subrepresentation_toSubmodule`: restricting to the
  submodule a subrepresentation carries has that subrepresentation's own representation underneath.
* `ContRepresentation.toRepresentation_quotient`: the underlying representation of a descended
  continuous representation is the descended underlying representation.
* `ContRepresentation.continuous_subrepresentation`: the restriction of a continuous
  representation to an invariant submodule is again continuous.

## iii. Table of contents

- A. Development

## iv. References

* Standard material; the statements and proofs are original to this formalization.
-/

public section

/-! ## A. Development -/

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
lemma coe_subrepresentation_apply (g : G) (v : W) :
    ((subrepresentation π W hW g v : W) : V) = π g (v : V) :=
  (rfl)

/-- The inclusion of a subrepresentation into its ambient continuous representation, packaged as a
continuous intertwiner. -/
noncomputable def subrepresentationInclusion
    (π : ContRepresentation R G V) (σ : Subrepresentation π.toRepresentation) :
    ContIntertwiningMap
      (subrepresentation π σ.toSubmodule
        (fun g _ hv ↦ σ.apply_mem_toSubmodule g hv)) π :=
  { toContinuousLinearMap := σ.toSubmodule.subtypeL
    isIntertwining' := fun g ↦ by
      ext v
      rfl }

/-- The subrepresentation inclusion sends a vector to the same vector in the ambient space. -/
@[simp]
lemma subrepresentationInclusion_apply (π : ContRepresentation R G V)
    (σ : Subrepresentation π.toRepresentation) (v : σ.toSubmodule) :
    π.subrepresentationInclusion σ v = (v : V) :=
  (rfl)

-- Not `@[simp]`: Mathlib's `@[simp] ContRepresentation.mem_invariants` already rewrites the
-- left-hand side to `∀ g, subrepresentation π W hW g x = x`, so the attribute would be a `simpNF`
-- violation ("Left-hand side simplifies … using `ContRepresentation.mem_invariants`"). This is the
-- `rw`-usable form of that normalization, as `ContRepresentation.mem_invariants_restrict` is for
-- the restriction along a subgroup.
/-- A vector of an invariant submodule is invariant for the restricted representation exactly when
it is invariant for the ambient one: the restricted action is the ambient action. -/
lemma mem_invariants_subrepresentation {x : W} :
    x ∈ (subrepresentation π W hW).invariants ↔ (x : V) ∈ π.invariants := by
  simp [ContRepresentation.mem_invariants, Subtype.ext_iff]

/-- The underlying representation of a restricted continuous representation is the restriction of
the underlying representation. -/
@[simp]
lemma toRepresentation_subrepresentation :
    (subrepresentation π W hW).toRepresentation
      = π.toRepresentation.subrepresentation W fun g _ hv => hW g _ hv := by
  rfl

-- Not `@[simp]`: `toRepresentation_subrepresentation` already rewrites the left-hand side to
-- `π.toRepresentation.subrepresentation σ.toSubmodule _`, so the attribute would be a `simpNF`
-- violation. This is the one-step form, which is what an argument about a subrepresentation of
-- `π.toRepresentation` needs.
/-- Restricting `π` to the submodule a subrepresentation `σ` of `π.toRepresentation` carries has
`σ.toRepresentation` as its underlying representation: both restrict the ambient action to the
same submodule. -/
lemma _root_.Subrepresentation.toRepresentation_subrepresentation_toSubmodule
    (σ : Subrepresentation π.toRepresentation) :
    (subrepresentation π σ.toSubmodule
      (fun g _ hv ↦ σ.apply_mem_toSubmodule g hv)).toRepresentation = σ.toRepresentation := by
  exact toRepresentation_subrepresentation.trans (by ext g v; rfl)

end Restriction

section Quotient

variable {R G V : Type*} [Ring R] [Monoid G] [AddCommGroup V] [TopologicalSpace V]
  [IsTopologicalAddGroup V] [Module R V]

/-- A continuous representation descended to the quotient by an invariant submodule, which
carries the quotient topology. This is the continuous counterpart of `Representation.quotient`. -/
def quotient (π : ContRepresentation R G V) (W : Submodule R V)
    (hW : ∀ g, ∀ v ∈ W, π g v ∈ W) : ContRepresentation R G (V ⧸ W) :=
  .ofMonoidHom
    { toFun g := W.liftQL (W.mkQL ∘L π g) fun v hv ↦ by simpa using hW g v hv
      map_one' := by
        ext v
        obtain ⟨v, rfl⟩ := W.mkQ_surjective v
        simp
      map_mul' g h := by
        ext v
        obtain ⟨v, rfl⟩ := W.mkQ_surjective v
        simp }

variable {π : ContRepresentation R G V} {W : Submodule R V} {hW : ∀ g, ∀ v ∈ W, π g v ∈ W}

/-- The descended action on the class of `v` is the class of the ambient action on `v`. -/
@[simp]
lemma quotient_apply_mk (g : G) (v : V) :
    quotient π W hW g (Submodule.Quotient.mk v) = Submodule.Quotient.mk (π g v) :=
  (rfl)

/-- The underlying representation of a descended continuous representation is the descended
underlying representation. -/
@[simp]
lemma toRepresentation_quotient :
    (quotient π W hW).toRepresentation
      = π.toRepresentation.quotient W fun g _ hv => hW g _ hv := by
  ext g v
  rfl

end Quotient

section Continuity

variable {𝕜 G V : Type*} [NormedField 𝕜] [Monoid G] [TopologicalSpace G] [AddCommGroup V]
  [TopologicalSpace V] [IsTopologicalAddGroup V] [Module 𝕜 V] [ContinuousConstSMul 𝕜 V]
  {π : ContRepresentation 𝕜 G V} {W : Submodule 𝕜 V} {hW : ∀ g, ∀ v ∈ W, π g v ∈ W}

/-- Restricting a continuous representation to an invariant submodule preserves continuity: from
continuity of `g ↦ π g` as a map into the continuous linear endomorphisms of `V`, the restricted
action `g ↦ subrepresentation π W hW g` is continuous into those of `W`. This supplies the
continuity argument that `matrixCoeff` and the rest of the continuous-representation API take
explicitly, so a subrepresentation can be used wherever a continuous representation is expected. -/
lemma continuous_subrepresentation (hπ : Continuous π) :
    Continuous (subrepresentation π W hW) := by
  rw [(ContinuousLinearMap.isInducing_postcomp W.subtypeL
    Topology.IsInducing.subtypeVal).continuous_iff]
  exact (ContinuousLinearMap.precomp V W.subtypeL).continuous.comp hπ

end Continuity

end ContRepresentation
