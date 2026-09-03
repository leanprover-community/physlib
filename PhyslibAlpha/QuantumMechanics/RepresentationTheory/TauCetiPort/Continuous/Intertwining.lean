/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RepresentationTheory.Continuous.Basic
public import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Continuous and algebraic intertwiners

For finite-dimensional Hausdorff topological vector spaces, automatic continuity identifies
continuous intertwiners and equivalences with their algebraic counterparts. The object and
character side is already supplied by the universe-polymorphic `FDRep.ofShrink`,
`FDRep.ofShrinkEquiv`, and `FDRep.character_ofShrink`; this file adds only the missing intertwiner
side.

## Main declarations

* `ContRepresentation.intertwiningMapEquiv`: continuous intertwiners are linearly equivalent to
  algebraic intertwiners.
* `ContRepresentation.nonempty_equiv_iff`: continuous and algebraic representation equivalence
  agree.

## References

* [Representations of compact groups and the Peter-Weyl theorem](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/CompactGroups/README.md),
  continuous-representation-to-`FDRep` correspondence.
-/

public section

namespace ContRepresentation

section Intertwiners

universe u v w x y

variable {𝕜 : Type u} {G : Type v} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜] [Monoid G]
  {V : Type w} {W : Type x} {U : Type y}
  [AddCommGroup V] [Module 𝕜 V] [TopologicalSpace V] [IsTopologicalAddGroup V]
  [ContinuousSMul 𝕜 V] [T2Space V] [FiniteDimensional 𝕜 V]
  [AddCommGroup W] [Module 𝕜 W] [TopologicalSpace W] [IsTopologicalAddGroup W]
  [ContinuousSMul 𝕜 W]
  [AddCommGroup U] [Module 𝕜 U] [TopologicalSpace U] [IsTopologicalAddGroup U]
  [ContinuousSMul 𝕜 U]
  {π : ContRepresentation 𝕜 G V} {ρ : ContRepresentation 𝕜 G W}
  {τ : ContRepresentation 𝕜 G U}

/-- In finite dimensions, forgetting continuity identifies continuous intertwining maps with
algebraic intertwining maps. The inverse equips the underlying linear map with its automatic
continuity. -/
noncomputable def intertwiningMapEquiv :
    ContIntertwiningMap π ρ ≃ₗ[𝕜]
      Representation.IntertwiningMap π.toRepresentation ρ.toRepresentation where
  toFun f := f.toIntertwiningMap
  invFun f :=
    { toContinuousLinearMap := LinearMap.toContinuousLinearMap f.toLinearMap
      isIntertwining' := fun g => by
        ext v
        exact Representation.IntertwiningMap.isIntertwining _ _ f g v }
  left_inv f := by
    apply ContIntertwiningMap.ext
    rfl
  right_inv f := by
    apply Representation.IntertwiningMap.ext
    rfl
  map_add' f g := by
    apply Representation.IntertwiningMap.ext
    rfl
  map_smul' c f := by
    apply Representation.IntertwiningMap.ext
    rfl

/-- The forward intertwiner identification is the existing forgetful map. -/
theorem intertwiningMapEquiv_apply (f : ContIntertwiningMap π ρ) :
    intertwiningMapEquiv f = f.toIntertwiningMap :=
  (rfl)

/-- The forward intertwiner identification preserves pointwise evaluation. -/
@[simp]
theorem intertwiningMapEquiv_apply_apply (f : ContIntertwiningMap π ρ) (v : V) :
    intertwiningMapEquiv f v = f v :=
  (rfl)

/-- The inverse intertwiner identification preserves pointwise evaluation. -/
@[simp]
theorem intertwiningMapEquiv_symm_apply_apply
    (f : Representation.IntertwiningMap π.toRepresentation ρ.toRepresentation) (v : V) :
    intertwiningMapEquiv.symm f v = f v :=
  (rfl)

/-- The intertwiner identification preserves identity maps. -/
@[simp high]
theorem intertwiningMapEquiv_id :
    intertwiningMapEquiv (ContIntertwiningMap.id : ContIntertwiningMap π π) =
      Representation.IntertwiningMap.id π.toRepresentation :=
  (rfl)

/-- The intertwiner identification preserves composition. -/
@[simp high]
theorem intertwiningMapEquiv_comp [T2Space W] [FiniteDimensional 𝕜 W]
    (f : ContIntertwiningMap ρ τ) (g : ContIntertwiningMap π ρ) :
    intertwiningMapEquiv (f.comp g) =
      (intertwiningMapEquiv f).comp (intertwiningMapEquiv g) :=
  (rfl)

/-- The inverse intertwiner identification preserves identity maps. -/
@[simp high]
theorem intertwiningMapEquiv_symm_id :
    intertwiningMapEquiv.symm (Representation.IntertwiningMap.id π.toRepresentation) =
      (ContIntertwiningMap.id : ContIntertwiningMap π π) := by
  apply ContIntertwiningMap.ext
  rfl

/-- The inverse intertwiner identification preserves composition. -/
@[simp high]
theorem intertwiningMapEquiv_symm_comp [T2Space W] [FiniteDimensional 𝕜 W]
    (f : Representation.IntertwiningMap ρ.toRepresentation τ.toRepresentation)
    (g : Representation.IntertwiningMap π.toRepresentation ρ.toRepresentation) :
    intertwiningMapEquiv.symm (f.comp g) =
      (intertwiningMapEquiv.symm f).comp (intertwiningMapEquiv.symm g) := by
  apply ContIntertwiningMap.ext
  rfl

end Intertwiners

section Equivalence

variable {𝕜 G V W : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜] [Monoid G]
  [AddCommGroup V] [Module 𝕜 V] [TopologicalSpace V] [IsTopologicalAddGroup V]
  [ContinuousSMul 𝕜 V] [T2Space V] [FiniteDimensional 𝕜 V]
  [AddCommGroup W] [Module 𝕜 W] [TopologicalSpace W] [IsTopologicalAddGroup W]
  [ContinuousSMul 𝕜 W] [T2Space W]
  {π : ContRepresentation 𝕜 G V} {ρ : ContRepresentation 𝕜 G W}

/-- Two finite-dimensional Hausdorff continuous representations over a complete field are
continuously equivalent exactly when their underlying algebraic representations are equivalent. -/
theorem nonempty_equiv_iff :
    Nonempty (_root_.ContRepresentation.Equiv π ρ) ↔
      Nonempty (Representation.Equiv π.toRepresentation ρ.toRepresentation) := by
  constructor
  · rintro ⟨φ⟩
    refine ⟨Representation.Equiv.mk φ.toContinuousLinearEquiv.toLinearEquiv fun g ↦ ?_⟩
    ext v
    exact congr($(φ.isIntertwining g) v)
  · rintro ⟨φ⟩
    refine ⟨_root_.ContRepresentation.Equiv.mk φ.toLinearEquiv.toContinuousLinearEquiv fun g ↦ ?_⟩
    ext v
    exact congr($(φ.isIntertwining' g) v)

end Equivalence

end ContRepresentation
