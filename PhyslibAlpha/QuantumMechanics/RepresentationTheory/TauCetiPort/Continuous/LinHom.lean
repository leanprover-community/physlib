/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import PhyslibAlpha.QuantumMechanics.RepresentationTheory.TauCetiPort.Continuous.Character

/-!
# The Hom representation of two continuous representations

Given continuous representations `π` on `V` and `ρ` on `W` of a group `G`, the operators
`V →L[𝕜] W` carry the conjugation action `T ↦ ρ g ∘ T ∘ π g⁻¹`. This file builds it as a
`ContRepresentation` on the operator space, the continuous counterpart of Mathlib's
`Representation.linHom` on `V →ₗ[𝕜] W`.

Two facts make the construction worth naming. Its **invariants are exactly the continuous
intertwiners**: `ρ g ∘ T ∘ π g⁻¹ = T` for every `g` says precisely that `T` intertwines, so
`Mathlib`'s `ContIntertwiningMap π ρ` is the invariant subspace of this representation. And its
**character is `χ_π(g⁻¹) · χ_ρ(g)`**, because the operator space is the finite-dimensional
`V →ₗ[𝕜] W` with the conjugation action, whose character Mathlib computes
(`Representation.char_linHom`).

Together these turn a character integral into the dimension of a space of intertwiners: over a
compact group, Haar-averaging this representation counts its invariants, which is what
`TauCeti/RepresentationTheory/Compact/Intertwiner/Dimension.lean` does.

The carrier is the operator space `V →L[𝕜] W`, not `V →ₗ[𝕜] W`: a `ContRepresentation` acts by
continuous linear maps on a topological module, and the operator norm is what makes the operators
one. In finite dimension the two carriers agree, and `ContRepresentation.conj_linHom` is
that comparison, stated as the identity that transports Mathlib's algebraic conjugation action to
this one along `LinearMap.toContinuousLinearMap`.

## Main definitions

* `ContRepresentation.linHom`: the Hom representation `T ↦ ρ g ∘ T ∘ π g⁻¹` on
  `V →L[𝕜] W`.
* `ContRepresentation.invariantsEquivContIntertwiningMap`: its invariant subspace is the
  space of continuous intertwiners `π →ⁱL ρ`.

## Main statements

* `ContRepresentation.continuous_linHom`: the Hom representation of two representations
  with continuous operator-valued action again has one.
* `ContRepresentation.linHom_apply_eq_self_iff_isIntertwining`: an operator is fixed by the
  conjugation action exactly when it intertwines, and
  `ContRepresentation.mem_linHom_invariants_iff_isIntertwining`: the same read on the invariant
  subspace.
* `ContRepresentation.character_linHom`: its character is `χ_π(g⁻¹) · χ_ρ(g)`.

## References

The algebraic originals are Mathlib's: `Representation.linHom` for the conjugation action,
`Representation.mem_linHom_invariants_iff_isIntertwining` and
`Representation.invariantsEquivIntertwiningMap` for the identification of its invariants with the
intertwiners — of which `ContRepresentation.linHom_apply_eq_self_iff_isIntertwining` and
`ContRepresentation.invariantsEquivContIntertwiningMap` are the continuous analogues, the first
proved by transporting the algebraic one — and `Representation.char_linHom` for the character.

This supplies the Hom representation that Layer 6 of the
[compact-groups roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/CompactGroups/README.md)
needs to read a character integral as a dimension of intertwiners, the compact-group form of
Mathlib's finite-group `Representation.card_inv_mul_sum_char_mul_char_eq_finrank`. The mathematical
development follows Daniel Bump, *Lie Groups*, second edition, Chapter 2.
-/

public section

open TauCeti TauCeti.ContRepresentation

namespace ContRepresentation

section Definition

variable {𝕜 G V W : Type*} [NontriviallyNormedField 𝕜] [Group G]
  [NormedAddCommGroup V] [NormedSpace 𝕜 V] [NormedAddCommGroup W] [NormedSpace 𝕜 W]

/-- **The Hom representation** of two continuous representations: `G` acts on the operators
`V →L[𝕜] W` by conjugation, `T ↦ ρ g ∘ T ∘ π g⁻¹`.

This is the continuous counterpart of Mathlib's `Representation.linHom`, with the operator space
in place of the space of all linear maps; the two agree in finite dimension by
`ContRepresentation.conj_linHom`. -/
noncomputable def linHom (π : ContRepresentation 𝕜 G V) (ρ : ContRepresentation 𝕜 G W) :
    ContRepresentation 𝕜 G (V →L[𝕜] W) :=
  .ofMonoidHom
    { toFun g := (ContinuousLinearMap.compL 𝕜 V W W (ρ g)).comp
        ((ContinuousLinearMap.compL 𝕜 V V W).flip (π g⁻¹))
      map_one' := by
        ext T v
        simp [ContinuousLinearMap.compL_apply, ContinuousLinearMap.one_def]
      map_mul' g h := by
        ext T v
        simp [ContinuousLinearMap.compL_apply, mul_inv_rev, map_mul π, map_mul ρ,
          mul_apply_eq_comp] }

variable (π : ContRepresentation 𝕜 G V) (ρ : ContRepresentation 𝕜 G W)

/-- The action operators of the Hom representation are conjugation. -/
@[simp]
theorem linHom_apply (g : G) (T : V →L[𝕜] W) :
    (linHom π ρ) g T = (ρ g).comp (T.comp (π g⁻¹)) :=
  (rfl)

/-- The Hom representation, evaluated at an operator and a vector. -/
theorem linHom_apply_apply (g : G) (T : V →L[𝕜] W) (v : V) :
    (linHom π ρ) g T v = ρ g (T (π g⁻¹ v)) := by
  rw [linHom_apply]
  rfl

variable [TopologicalSpace G] [IsTopologicalGroup G]

/-- **The Hom representation has a continuous operator-valued action.** Conjugation is the
composition of the two contractions of `ContinuousLinearMap.compL` by the separate actions, and
inversion is continuous on a topological group. -/
theorem continuous_linHom (hπ : Continuous π) (hρ : Continuous ρ) : Continuous (linHom π ρ) :=
  ((ContinuousLinearMap.compL 𝕜 V W W).continuous.comp hρ).clm_comp
    ((ContinuousLinearMap.compL 𝕜 V V W).flip.continuous.comp (hπ.comp continuous_inv))

end Definition

section Invariants

variable {𝕜 G V W : Type*} [NontriviallyNormedField 𝕜] [Group G]
  [NormedAddCommGroup V] [NormedSpace 𝕜 V] [NormedAddCommGroup W] [NormedSpace 𝕜 W]
  (π : ContRepresentation 𝕜 G V) (ρ : ContRepresentation 𝕜 G W)

/-- **An operator fixed by the conjugation action is exactly one that intertwines.** This is
Mathlib's `Representation.mem_linHom_invariants_iff_isIntertwining` for the algebraic Hom
representation, read on the operator space: the invariance equation `ρ g ∘ T ∘ π g⁻¹ = T` and the
intertwining equation `T ∘ π g = ρ g ∘ T` are equations of continuous linear maps exactly when
their underlying linear maps agree.

The left-hand side is the simp-normal form of `T ∈ (linHom π ρ).invariants`, which
`ContRepresentation.mem_invariants` and `ContRepresentation.linHom_apply` — both `simp` lemmas —
reduce to it; stating the lemma this way, exactly as Mathlib states its algebraic original, is what
makes it usable by `simp`. `ContRepresentation.mem_linHom_invariants_iff_isIntertwining` is the
same fact phrased in terms of the invariant subspace. -/
@[simp]
theorem linHom_apply_eq_self_iff_isIntertwining (T : V →L[𝕜] W) :
    (∀ g : G, (ρ g).comp (T.comp (π g⁻¹)) = T) ↔ ∀ g : G, T.comp (π g) = (ρ g).comp T := by
  have key := Representation.mem_linHom_invariants_iff_isIntertwining (ρ := π.toRepresentation)
    (σ := ρ.toRepresentation) (T : V →ₗ[𝕜] W)
  rw [Representation.isIntertwiningMap_iff] at key
  simp only [LinearMap.ext_iff, LinearMap.comp_apply, ContinuousLinearMap.coe_coe] at key
  simp only [ContinuousLinearMap.ext_iff, ContinuousLinearMap.comp_apply]
  exact key

/-- **An operator is invariant in the Hom representation exactly when it intertwines.** This is
`ContRepresentation.linHom_apply_eq_self_iff_isIntertwining` phrased in terms of the invariant
subspace, the form in which the invariants of the Hom representation are consumed.

This is not a `simp` lemma: `ContRepresentation.mem_invariants` is one, so the left-hand side is
not in simp-normal form, and tagging it makes `simpNF` report "left-hand side simplifies". -/
theorem mem_linHom_invariants_iff_isIntertwining (T : V →L[𝕜] W) :
    T ∈ (linHom π ρ).invariants ↔ ∀ g : G, T.comp (π g) = (ρ g).comp T := by
  simp only [ContRepresentation.mem_invariants, linHom_apply,
    linHom_apply_eq_self_iff_isIntertwining]

/-- A continuous intertwiner is an invariant operator of the Hom representation. -/
theorem toContinuousLinearMap_mem_invariants_linHom (f : ContIntertwiningMap π ρ) :
    f.toContinuousLinearMap ∈ (linHom π ρ).invariants :=
  (mem_linHom_invariants_iff_isIntertwining π ρ _).2 f.isIntertwining'

/-- **The invariants of the Hom representation are the continuous intertwiners.** -/
noncomputable def invariantsEquivContIntertwiningMap :
    (linHom π ρ).invariants ≃ₗ[𝕜] ContIntertwiningMap π ρ where
  toFun T := ⟨(T : V →L[𝕜] W), (mem_linHom_invariants_iff_isIntertwining π ρ _).1 T.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun f := ⟨f.toContinuousLinearMap, toContinuousLinearMap_mem_invariants_linHom π ρ f⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The equivalence with the intertwiners forgets the invariance proof. -/
@[simp]
theorem invariantsEquivContIntertwiningMap_apply (T : (linHom π ρ).invariants) :
    (invariantsEquivContIntertwiningMap π ρ T).toContinuousLinearMap = (T : V →L[𝕜] W) :=
  (rfl)

/-- The inverse of the equivalence with the intertwiners forgets the intertwining proof. -/
@[simp]
theorem invariantsEquivContIntertwiningMap_symm_apply (f : ContIntertwiningMap π ρ) :
    ((invariantsEquivContIntertwiningMap π ρ).symm f : V →L[𝕜] W) = f.toContinuousLinearMap :=
  (rfl)

end Invariants

section Character

variable {𝕜 G V W : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜] [Group G]
  [TopologicalSpace G] [IsTopologicalGroup G]
  [NormedAddCommGroup V] [NormedSpace 𝕜 V] [FiniteDimensional 𝕜 V]
  [NormedAddCommGroup W] [NormedSpace 𝕜 W] [FiniteDimensional 𝕜 W]
  (π : ContRepresentation 𝕜 G V) (ρ : ContRepresentation 𝕜 G W)

omit [TopologicalSpace G] [IsTopologicalGroup G] [FiniteDimensional 𝕜 W] in
/-- **The Hom representation is Mathlib's `Representation.linHom`, transported along
`LinearMap.toContinuousLinearMap`.** In finite dimension every linear map is continuous, and the
resulting identification of `V →ₗ[𝕜] W` with `V →L[𝕜] W` conjugates the algebraic conjugation
action into the one built here. -/
theorem conj_linHom (g : G) :
    (LinearMap.toContinuousLinearMap : (V →ₗ[𝕜] W) ≃ₗ[𝕜] V →L[𝕜] W).conj
        (Representation.linHom π.toRepresentation ρ.toRepresentation g)
      = ((linHom π ρ g : (V →L[𝕜] W) →L[𝕜] V →L[𝕜] W) : (V →L[𝕜] W) →ₗ[𝕜] V →L[𝕜] W) := by
  ext T v
  simp only [ContinuousLinearMap.coe_coe, linHom_apply_apply]
  simp [LinearEquiv.conj_apply, ContRepresentation.toMonoidHom_apply]

/-- **The character of the Hom representation is `χ_π(g⁻¹) · χ_ρ(g)`.** The trace is unchanged by
transporting along `LinearMap.toContinuousLinearMap`, so this is Mathlib's
`Representation.char_linHom` read on the operator space. -/
theorem character_linHom (hπ : Continuous π) (hρ : Continuous ρ) (g : G) :
    character (linHom π ρ) (continuous_linHom π ρ hπ hρ) g
      = character π hπ g⁻¹ * character ρ hρ g := by
  have h : character (linHom π ρ) (continuous_linHom π ρ hπ hρ) g
      = (Representation.linHom π.toRepresentation ρ.toRepresentation).character g := by
    rw [character_apply, ← conj_linHom π ρ g, LinearMap.trace_conj', Representation.character]
  rw [h, Representation.char_linHom, coe_character, coe_character]

end Character

end ContRepresentation
