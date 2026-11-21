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
are `α⁶` and `α⁻⁶`, so the transformation belongs to `SU(5)`. Both blocks are the identity
precisely for the central `ℤ₆` subgroup, so the homomorphism embeds the quotient by `ℤ₆`
into `SU(5)`.

## ii. Key results

- `GeorgiGlashow.standardModelHom` is the group homomorphism from the unquotiented Standard
  Model gauge group to `SU(5)`.
- `GeorgiGlashow.standardModelHom_ker` identifies the kernel with the central `ℤ₆` subgroup.
- `GeorgiGlashow.standardModelQuotientHom_injective` gives faithfulness on the quotient.

## iii. Table of contents

- A. The Standard Model gauge homomorphism
- B. The kernel and the quotient embedding

## iv. References

* J. Baez and J. Huerta, [The Algebra of Grand Unified Theories, pp. 34, 37](
  https://math.ucr.edu/home/baez/guts.pdf#page=34). [ref: baez_guts_notes]

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

/-!

## B. The kernel and the quotient embedding

-/

open StandardModel

private lemma mem_gaugeGroupℤ₆SubGroup_of_standardModelHom_eq_one (g : GaugeGroupI)
    (h : standardModelHom g = 1) : g ∈ gaugeGroupℤ₆SubGroup := by
  have hb : standardModelBlocks g = 1 := by
    apply (reindexAlgEquiv ℂ ℂ finSumFinEquiv).injective
    rw [map_one]
    exact congrArg (fun x : specialUnitaryGroup (Fin 5) ℂ => x.1) h
  rw [standardModelBlocks, ← fromBlocks_one, fromBlocks_inj] at hb
  obtain ⟨hw, _, _, hc⟩ := hb
  have h6 : (g.toU1 : ℂ) ^ 6 = 1 := by
    simpa [det_smul, (mem_specialUnitaryGroup_iff.mp g.toSU2.prop).2, ← pow_mul] using
      congrArg det hw
  refine (mem_gaugeGroupℤ₆SubGroup_iff g).mpr ⟨rootsOfUnity.mkOfPowEq _ h6, ?_⟩
  apply GaugeGroupI.ext
  · apply Subtype.ext
    rw [gaugeGroupℤ₆OfRoot_toSU3, gaugeGroupℤ₆SU3OfRoot_eq_mul_id, rootsOfUnity.coe_mkOfPowEq]
    change (g.toU1 ^ 2)⁻¹ • g.toSU3.1 = (1 : Matrix (Fin 3) (Fin 3) ℂ) at hc
    simpa only [Submonoid.smul_def, SubmonoidClass.coe_pow] using (inv_smul_eq_iff.mp hc).symm
  · apply Subtype.ext
    rw [gaugeGroupℤ₆OfRoot_toSU2, gaugeGroupℤ₆SU2OfRoot_eq_mul_id, rootsOfUnity.coe_mkOfPowEq]
    change (g.toU1 ^ 3) • g.toSU2.1 = (1 : Matrix (Fin 2) (Fin 2) ℂ) at hw
    rw [← star_pow]
    exact ((smul_eq_iff_eq_inv_smul _).mp hw).symm
  · rfl

/-- Each central sixth root of unity acts trivially on the weak and colour blocks. -/
@[simp]
lemma standardModelHom_gaugeGroupℤ₆OfRoot (α : rootsOfUnity 6 ℂ) :
    standardModelHom (gaugeGroupℤ₆OfRoot α) = 1 := by
  let u := gaugeGroupℤ₆UnitaryOfRoot α
  have hweak : ((u ^ 3 : unitary ℂ) : ℂ) * star ((α : ℂˣ) : ℂ) ^ 3 = 1 := by
    rw [← star_pow]
    exact (u ^ 3 : unitary ℂ).prop.2
  have hcolour : (((u ^ 2)⁻¹ : unitary ℂ) : ℂ) * ((α : ℂˣ) : ℂ) ^ 2 = 1 :=
    (u ^ 2 : unitary ℂ).prop.1
  apply Subtype.ext
  rw [standardModelHom_val, standardModelBlocks]
  simp only [gaugeGroupℤ₆OfRoot_toU1, gaugeGroupℤ₆OfRoot_toSU2, gaugeGroupℤ₆OfRoot_toSU3,
    gaugeGroupℤ₆SU2OfRoot_eq_mul_id, gaugeGroupℤ₆SU3OfRoot_eq_mul_id, smul_smul]
  change reindex finSumFinEquiv finSumFinEquiv (fromBlocks (_ • _) 0 0 (_ • _)) = 1
  rw [hweak, hcolour, one_smul, one_smul, fromBlocks_one]
  exact (reindexAlgEquiv ℂ ℂ finSumFinEquiv).map_one

/-- The kernel of the Georgi–Glashow homomorphism is the central `ℤ₆` of the Standard Model. -/
lemma standardModelHom_ker : standardModelHom.ker = gaugeGroupℤ₆SubGroup := by
  ext g
  constructor
  · exact mem_gaugeGroupℤ₆SubGroup_of_standardModelHom_eq_one g
  · rintro ⟨α, rfl⟩
    exact standardModelHom_gaugeGroupℤ₆OfRoot α

/-- The homomorphism of the Standard Model gauge group modulo `ℤ₆` into `SU(5)`. -/
noncomputable def standardModelQuotientHom : GaugeGroupℤ₆ →* specialUnitaryGroup (Fin 5) ℂ :=
  QuotientGroup.lift gaugeGroupℤ₆SubGroup standardModelHom standardModelHom_ker.ge

@[simp]
lemma standardModelQuotientHom_mk (g : GaugeGroupI) :
    standardModelQuotientHom (GaugeGroupℤ₆.mk g) = standardModelHom g := rfl

/-- The induced homomorphism embeds the quotient gauge group in `SU(5)`. -/
lemma standardModelQuotientHom_injective : Function.Injective standardModelQuotientHom :=
  (QuotientGroup.injective_lift_iff _ _ standardModelHom_ker.ge).mpr standardModelHom_ker.symm

end GeorgiGlashow
