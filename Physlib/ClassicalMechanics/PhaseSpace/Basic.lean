/-
Copyright (c) 2026 Rithwik Ranganathan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rithwik Ranganathan
-/
module

public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.Geometry.Manifold.VectorBundle.Hom
public import Physlib.ClassicalMechanics.ConfigurationSpace.Basic

/-!
# Canonical phase spaces

The cotangent phase space of a configuration space and its momentum-position coordinates.

## i. Overview

A phase-space state consists of a configuration `q` and a momentum covector at `q`.
The cotangent bundle inherits its topology and smooth structure from Mathlib's bundle of
continuous linear maps from the tangent bundle to the trivial real line bundle.

For a normed configuration space, the phase space has global coordinates `(p, q)` with
`p` in the continuous dual. On a real Hilbert space, the Riesz identification represents
momentum by a vector, matching the momentum-first convention of Hamilton's equations.
The constructors `PhaseSpace.ofNormedSpace` and `PhaseSpace.ofInnerProductSpace` build
states directly from these momentum-position coordinates.

## ii. Key results

- `PhaseSpace` : the cotangent phase space of a configuration space.
- `PhaseSpace.contMDiff_position` : the configuration projection is smooth.
- `PhaseSpace.contMDiff_zeroMomentum` : the zero-momentum section is smooth.
- `PhaseSpace.normedSpaceDiffeomorph` : global covector-position coordinates.
- `PhaseSpace.innerProductSpaceDiffeomorph` : global momentum-vector-position coordinates.

## iii. Table of contents

- A. States and their configurations
- B. Global momentum-position coordinates

## iv. References

* V. I. Arnold, Mathematical Methods of Classical Mechanics. [ref: arnold_mechanics]
-/

@[expose] public section

namespace ClassicalMechanics

noncomputable section

open Bundle
open scoped Manifold ContDiff Bundle

section NormedSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {H : Type*} [TopologicalSpace H]
  (I : ModelWithCorners ℝ E H) (Q : ConfigurationSpace I)

/-!
## A. States and their configurations
-/

/-- The canonical phase space `T*Q`, whose states pair a configuration with a momentum covector. -/
abbrev PhaseSpace :=
  Bundle.TotalSpace (E →L[ℝ] ℝ) (fun q : Q ↦ TangentSpace I q →L[ℝ] Bundle.Trivial Q ℝ q)

end NormedSpace

namespace PhaseSpace

section NormedSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {Q : ConfigurationSpace I}

/-- The configuration of a phase-space state. -/
abbrev position (s : PhaseSpace I Q) : Q := s.proj

/-- The momentum covector of a state, acting on tangent vectors at its configuration. -/
abbrev momentum (s : PhaseSpace I Q) : TangentSpace I s.position →L[ℝ] ℝ := s.2

/-- Construct a state from a configuration and its momentum covector. -/
def mk (q : Q) (p : TangentSpace I q →L[ℝ] ℝ) : PhaseSpace I Q := ⟨q, p⟩

@[simp]
lemma position_mk (q : Q) (p : TangentSpace I q →L[ℝ] ℝ) : (mk q p).position = q := rfl

@[simp]
lemma momentum_mk (q : Q) (p : TangentSpace I q →L[ℝ] ℝ) : (mk q p).momentum = p := rfl

/-- The configuration projection from phase space is smooth. -/
lemma contMDiff_position :
    ContMDiff (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) I ∞ (position : PhaseSpace I Q → Q) :=
  contMDiff_proj _

/-- The state with zero momentum at a given configuration. -/
def zeroMomentum (q : Q) : PhaseSpace I Q := mk q 0

/-- Assigning zero momentum to each configuration is a smooth section of phase space. -/
lemma contMDiff_zeroMomentum :
    ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) ∞ (zeroMomentum : Q → PhaseSpace I Q) :=
  contMDiff_zeroSection ℝ _

/-!
## B. Global momentum-position coordinates
-/

variable (E)

set_option backward.isDefEq.respectTransparency false in
private lemma momentum_inCoordinates (q₀ : E) (s : PhaseSpace 𝓘(ℝ, E) ⟨E⟩) :
    ContinuousLinearMap.inCoordinates E (TangentSpace 𝓘(ℝ, E)) ℝ (Trivial E ℝ)
      q₀ s.position q₀ s.position s.momentum =
      s.momentum.comp (NormedSpace.fromTangentSpace s.position).symm.toContinuousLinearMap := by
  simp only [ContinuousLinearMap.inCoordinates, TangentBundle.symmL_model_space]
  change ((Trivial.trivialization E ℝ).continuousLinearMapAt ℝ s.position).comp
    (s.momentum.comp (1 : E →L[ℝ] E)) = _
  simp only [Trivial.continuousLinearMapAt_trivialization, ContinuousLinearMap.id_comp,
    ContinuousLinearMap.one_def, ContinuousLinearMap.comp_id]
  rfl

/-- Global covector-position coordinates on the phase space of a real normed space. -/
noncomputable def normedSpaceDiffeomorph :
    PhaseSpace 𝓘(ℝ, E) ⟨E⟩ ≃ₘ^∞ ⟮(𝓘(ℝ, E)).prod 𝓘(ℝ, E →L[ℝ] ℝ),
      𝓘(ℝ, (E →L[ℝ] ℝ) × E)⟯ (E →L[ℝ] ℝ) × E where
  toFun s := (s.momentum.comp (NormedSpace.fromTangentSpace s.position).symm.toContinuousLinearMap,
    s.position)
  invFun x := mk x.2 (x.1.comp (NormedSpace.fromTangentSpace x.2).toContinuousLinearMap)
  left_inv s := by cases s; rfl
  right_inv x := by cases x; rfl
  contMDiff_toFun := by
    intro s
    have h := (contMDiffAt_hom_bundle (IB := 𝓘(ℝ, E))
      (id : PhaseSpace 𝓘(ℝ, E) ⟨E⟩ → _)).mp
      (contMDiffAt_id : ContMDiffAt ((𝓘(ℝ, E)).prod 𝓘(ℝ, E →L[ℝ] ℝ))
        ((𝓘(ℝ, E)).prod 𝓘(ℝ, E →L[ℝ] ℝ)) ∞ id s)
    simp only [momentum_inCoordinates] at h
    exact h.2.prodMk_space h.1
  contMDiff_invFun := by
    intro x
    apply (contMDiffAt_hom_bundle _).mpr
    constructor
    · exact contDiffAt_snd.contMDiffAt
    · simp only [momentum_inCoordinates]
      exact contDiffAt_fst.contMDiffAt

@[simp]
lemma normedSpaceDiffeomorph_apply (s : PhaseSpace 𝓘(ℝ, E) ⟨E⟩) :
    normedSpaceDiffeomorph E s =
      (s.momentum.comp (NormedSpace.fromTangentSpace s.position).symm.toContinuousLinearMap,
        s.position) := rfl

@[simp]
lemma normedSpaceDiffeomorph_symm_apply (p : E →L[ℝ] ℝ) (q : E) :
    (normedSpaceDiffeomorph E).symm (p, q) =
      mk q (p.comp (NormedSpace.fromTangentSpace q).toContinuousLinearMap) := rfl

variable {E}

/-- The phase-space state on a normed space with momentum covector `p` and position `q`.
The argument order agrees with the momentum-position coordinates of Hamilton's equations. -/
def ofNormedSpace (p : E →L[ℝ] ℝ) (q : E) : PhaseSpace 𝓘(ℝ, E) ⟨E⟩ :=
  (normedSpaceDiffeomorph E).symm (p, q)

@[simp]
lemma position_ofNormedSpace (p : E →L[ℝ] ℝ) (q : E) :
    (ofNormedSpace p q).position = q := rfl

/-- The constructed momentum covector acts on tangent vectors through their normed-space
coordinates. -/
-- Fix the coercion's tangent-space index at `q` to keep the statement in simp normal form.
@[simp]
lemma momentum_ofNormedSpace_apply (p : E →L[ℝ] ℝ) (q : E) (v : TangentSpace 𝓘(ℝ, E) q) :
    DFunLike.coe (F := TangentSpace 𝓘(ℝ, E) q →L[ℝ] ℝ) (ofNormedSpace p q).momentum v =
      p (NormedSpace.fromTangentSpace q v) := rfl

end NormedSpace

section InnerProductSpace

variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Global momentum-vector-position coordinates, using the real Hilbert-space Riesz map. -/
noncomputable def innerProductSpaceDiffeomorph :
    PhaseSpace 𝓘(ℝ, E) ⟨E⟩ ≃ₘ^∞ ⟮(𝓘(ℝ, E)).prod 𝓘(ℝ, E →L[ℝ] ℝ),
      𝓘(ℝ, E × E)⟯ E × E :=
  (normedSpaceDiffeomorph E).trans
    (((InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv.prodCongr
      (ContinuousLinearEquiv.refl ℝ E)).toDiffeomorph)

/-- A coordinate momentum vector acts on velocities by the real inner product. -/
@[simp]
lemma innerProductSpaceDiffeomorph_symm_apply (p q : E) :
    (innerProductSpaceDiffeomorph E).symm (p, q) =
      mk q ((InnerProductSpace.toDual ℝ E p).comp
        (NormedSpace.fromTangentSpace q).toContinuousLinearMap) := rfl

variable {E}

/-- The phase-space state on a real Hilbert space with momentum vector `p` and position `q`.
The Riesz map turns `p` into a momentum covector, with the same argument order as Hamilton's
equations. -/
def ofInnerProductSpace (p q : E) : PhaseSpace 𝓘(ℝ, E) ⟨E⟩ :=
  (innerProductSpaceDiffeomorph E).symm (p, q)

@[simp]
lemma position_ofInnerProductSpace (p q : E) :
    (ofInnerProductSpace p q).position = q := rfl

/-- The momentum covector associated to `p` acts by taking the inner product with `p`. -/
@[simp]
lemma momentum_ofInnerProductSpace_apply (p q : E) (v : TangentSpace 𝓘(ℝ, E) q) :
    DFunLike.coe (F := TangentSpace 𝓘(ℝ, E) q →L[ℝ] ℝ) (ofInnerProductSpace p q).momentum v =
      inner ℝ p (NormedSpace.fromTangentSpace q v) := by
  change (InnerProductSpace.toDual ℝ E p) (NormedSpace.fromTangentSpace q v) = _
  exact InnerProductSpace.toDual_apply_apply

end InnerProductSpace

end PhaseSpace

end

end ClassicalMechanics
