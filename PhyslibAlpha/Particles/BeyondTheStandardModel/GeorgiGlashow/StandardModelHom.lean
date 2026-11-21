/-
Copyright (c) 2026 Sabrina Pasterski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sabrina Pasterski
-/
module

public import Physlib.Particles.StandardModel.GaugeGroup.Basic

/-!
# The Standard Model gauge homomorphism into SU(5)

The weak and colour factors act on complementary subspaces of the Georgi–Glashow fundamental
representation.

## i. Overview

Write a Standard Model gauge transformation as `(h, g, α)` with `h ∈ SU(3)`, `g ∈ SU(2)`
and `α ∈ U(1)`. On the decomposition `ℂ⁵ = ℂ² ⊕ ℂ³`, the weak doublet transforms by
`α³ g` and the colour triplet by `α⁻² h`. The two blocks are unitary. Their determinants
are `α⁶` and `α⁻⁶`, so the transformation belongs to `SU(5)`.

## ii. Key results

- `GeorgiGlashow.standardModelHom` is the group homomorphism from the unquotiented Standard
  Model gauge group to `SU(5)`.

## iii. Table of contents

- A. The Standard Model gauge homomorphism

## iv. References

* J. Baez and J. Huerta, [The Algebra of Grand Unified Theories, p. 37](
  https://math.ucr.edu/home/baez/guts.pdf#page=37). [ref: baez_guts_notes]

-/

@[expose] public section

namespace GeorgiGlashow

open Matrix

/-!

## A. The Standard Model gauge homomorphism

-/

/-- The gauge transformation on the weak doublet and the colour triplet, in block coordinates. -/
noncomputable def standardModelBlocks (g : StandardModel.GaugeGroupI) :
    Matrix (Fin 2 ⊕ Fin 3) (Fin 2 ⊕ Fin 3) ℂ :=
  fromBlocks (((g.toU1 ^ 3 : unitary ℂ) : ℂ) • g.toSU2.1) 0 0
    ((((g.toU1 ^ 2)⁻¹ : unitary ℂ) : ℂ) • g.toSU3.1)

private lemma standardModelBlocks_unitary (g : StandardModel.GaugeGroupI) :
    standardModelBlocks g ∈ unitaryGroup (Fin 2 ⊕ Fin 3) ℂ := by
  have hw : ((g.toU1 ^ 3 : unitary ℂ) : ℂ) • g.toSU2.1 ∈ unitaryGroup (Fin 2) ℂ :=
    Unitary.smul_mem_of_mem (a := g.toSU2.1) (g.toU1 ^ 3).prop g.toSU2.prop.1
  have hc : (((g.toU1 ^ 2)⁻¹ : unitary ℂ) : ℂ) • g.toSU3.1 ∈ unitaryGroup (Fin 3) ℂ :=
    Unitary.smul_mem_of_mem (a := g.toSU3.1) ((g.toU1 ^ 2)⁻¹).prop g.toSU3.prop.1
  rw [mem_unitaryGroup_iff, standardModelBlocks, star_eq_conjTranspose,
    fromBlocks_conjTranspose, fromBlocks_multiply]
  simp only [conjTranspose_zero, Matrix.zero_mul, Matrix.mul_zero, zero_add, add_zero,
    ← star_eq_conjTranspose, hw.2, hc.2, fromBlocks_one]

private lemma standardModelBlocks_det (g : StandardModel.GaugeGroupI) :
    (standardModelBlocks g).det = 1 := by
  rw [standardModelBlocks, det_fromBlocks_zero₂₁, det_smul, det_smul]
  simp only [Fintype.card_fin, (mem_specialUnitaryGroup_iff.mp g.toSU2.prop).2,
    (mem_specialUnitaryGroup_iff.mp g.toSU3.prop).2, mul_one]
  have h : (g.toU1 ^ 3) ^ 2 * ((g.toU1 ^ 2)⁻¹) ^ 3 = 1 := by group
  simpa only [Submonoid.coe_mul, SubmonoidClass.coe_pow, OneMemClass.coe_one] using
    congrArg ((↑) : unitary ℂ → ℂ) h

private lemma standardModelBlocks_mul (g h : StandardModel.GaugeGroupI) :
    standardModelBlocks (g * h) = standardModelBlocks g * standardModelBlocks h := by
  simp [standardModelBlocks, mul_pow, fromBlocks_multiply, smul_smul,
    mul_comm (h.toU1 ^ 2)⁻¹ (g.toU1 ^ 2)⁻¹]
  constructor <;> congr 1 <;> apply mul_comm

/-- The Georgi–Glashow homomorphism from the unquotiented Standard Model gauge group to `SU(5)`.
The first two coordinates carry weak isospin and the last three carry colour. -/
noncomputable def standardModelHom :
    StandardModel.GaugeGroupI →* specialUnitaryGroup (Fin 5) ℂ where
  toFun g := ⟨reindex finSumFinEquiv finSumFinEquiv (standardModelBlocks g), by
    refine mem_specialUnitaryGroup_iff.mpr ⟨?_, ?_⟩
    · rw [mem_unitaryGroup_iff, star_eq_conjTranspose, conjTranspose_reindex,
        ← coe_reindexAlgEquiv ℂ ℂ, ← map_mul, ← star_eq_conjTranspose,
        (standardModelBlocks_unitary g).2, map_one]
    · rw [det_reindex_self, standardModelBlocks_det]⟩
  map_one' := by
    apply Subtype.ext
    simp [standardModelBlocks]
  map_mul' g h := by
    apply Subtype.ext
    simp only [← coe_reindexAlgEquiv ℂ ℂ, standardModelBlocks_mul, map_mul]
    rfl

/-- In the weak and colour basis the homomorphism has two diagonal blocks. -/
lemma standardModelHom_val (g : StandardModel.GaugeGroupI) :
    (standardModelHom g).1 = reindex finSumFinEquiv finSumFinEquiv (standardModelBlocks g) :=
  rfl

end GeorgiGlashow
