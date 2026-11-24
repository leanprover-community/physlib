/-
Copyright (c) 2026 Gregory J. Loges. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregory J. Loges
-/
module

public import Physlib.QuantumMechanics.HilbertSpaces.SpaceD.SchwartzSubmodule
/-!

# Dirichlet submodule

## i. Overview

In this module we define the Dirichlet submodule of `SpaceDHilbertSpaceOn Ω μ` consisting of
equivalence classes of Schwartz maps which vanish on `frontier Ω`. The frontier (or boundary)
of a set `Ω` contains all points whose neighborhoods always intersect with both `Ω` and `Ωᶜ`.

These serve as a convenient dense domain for operators acting on wavefunctions satisfying
homogeneous Dirichlet boundary conditions on `Ω`.

## ii. Key results

- `DirichletSubmoduleOn Ω μ`: The subspace of `SchwartzSubmodule d μ` consisting of Schwartz maps
  which vanish on the frontier of `Ω`.

## iii. Table of contents

- A. Definitions
- B. Contained in SchwartzSubmoduleOn
- C. Density

## iv. References

* None.
-/

@[expose] public section

noncomputable section
namespace QuantumMechanics
namespace SpaceDHilbertSpaceOn

open MeasureTheory SchwartzMap SpaceDHilbertSpace

variable {d : ℕ} (Ω : Set (Space d)) (μ : Measure (Space d)) [μ.HasTemperateGrowth]

/-!
## A. Definitions
-/

/-- The Schwartz maps which vanish on `frontier Ω`. -/
def DirichletSchwartzMap : Submodule ℂ 𝓢(Space d, ℂ) where
  carrier := {f : 𝓢(Space d, ℂ) | ∀ x : frontier Ω, f x = 0}
  add_mem' := by simp_all
  zero_mem' := by simp
  smul_mem' := by simp_all

/-- The submodule of the Hilbert space on `Ω` consisting of the equivalence classes
  of Schwartz maps which vanish on `frontier Ω`. -/
abbrev DirichletSubmoduleOn : Submodule ℂ (SpaceDHilbertSpaceOn Ω μ) :=
  (DirichletSchwartzMap Ω).map (subspaceProjection Ω μ ∘L schwartzIncl μ).toLinearMap

namespace DirichletSubmoduleOn

variable {Ω μ} in
lemma mem_iff {ψ : SpaceDHilbertSpaceOn Ω μ} :
    ψ ∈ DirichletSubmoduleOn Ω μ ↔
      ∃ f : DirichletSchwartzMap Ω, subspaceProjection Ω μ (schwartzIncl μ f) = ψ := by
  simp

/-!
## B. Contained in SchwartzSubmoduleOn
-/

lemma le_schwartzSubmoduleOn : DirichletSubmoduleOn Ω μ ≤ SchwartzSubmoduleOn Ω μ := by
  intro ψ hψ
  obtain ⟨f, hf⟩ := mem_iff.mp hψ
  apply SchwartzSubmoduleOn.mem_iff.mpr ⟨⟨schwartzIncl μ f, by simp⟩, hf⟩

/-!
## C. Density
-/

TODO "Prove that `DirichletSubmoduleOn Ω μ` is dense in `SpaceDHilbertSpaceOn Ω μ`
  (perhaps with some assumptions on Ω and μ)."

end DirichletSubmoduleOn
end SpaceDHilbertSpaceOn
end QuantumMechanics
end
