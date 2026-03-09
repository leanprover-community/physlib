/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import PhysLean.QFT.AnomalyCancellation.Basic
/-!

# Anomaly cancellation conditions for the Standard Model with right-handed neutrinos

This directory is related to the anomaly cancellation conditions (ACCs) for the Standard Model with
right-handed neutrinos (SMν).

-/

@[expose] public section

open Nat
open BigOperators

/-- The vector space of charges corresponding to the SM fermions with RHN. -/
@[simps!]
def SMνCharges (n : ℕ) : ACCSystemCharges := ACCSystemChargesMk (6 * n)

/-- The vector spaces of charges of one species of fermions in the SM. -/
@[simps!]
def SMνSpecies (n : ℕ) : ACCSystemCharges := ACCSystemChargesMk n

namespace SMνCharges

variable {n : ℕ}

/-- An equivalence between `(SMνCharges n).charges` and `(Fin 6 → Fin n → ℚ)`
splitting the charges into species. -/
@[simps!]
def toSpeciesEquiv : (SMνCharges n).Charges ≃ (Fin 6 → Fin n → ℚ) :=
  ((Equiv.curry _ _ _).symm.trans ((@finProdFinEquiv 6 n).arrowCongr (Equiv.refl ℚ))).symm

/-- Given an `i ∈ Fin 6`, the projection of charges onto a given species. -/
@[simps!]
def toSpecies (i : Fin 6) : (SMνCharges n).Charges →ₗ[ℚ] (SMνSpecies n).Charges where
  toFun S := toSpeciesEquiv S i
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

lemma charges_eq_toSpecies_eq (S T : (SMνCharges n).Charges) :
    S = T ↔ ∀ i, toSpecies i S = toSpecies i T := by
  refine Iff.intro (fun h => ?_) (fun h => ?_)
  · exact fun i => congrArg (⇑(toSpecies i)) h
  · apply toSpeciesEquiv.injective
    exact funext (fun i => h i)

lemma toSMSpecies_toSpecies_inv (i : Fin 6) (f : Fin 6 → Fin n → ℚ) :
    (toSpecies i) (toSpeciesEquiv.symm f) = f i := by
  change (toSpeciesEquiv ∘ toSpeciesEquiv.symm) _ i = f i
  simp

lemma toSpecies_one (S : (SMνCharges 1).Charges) (j : Fin 6) :
    toSpecies j S ⟨0, zero_lt_succ 0⟩ = S j := by
  match j with
  | 0 => rfl
  | 1 => rfl
  | 2 => rfl
  | 3 => rfl
  | 4 => rfl
  | 5 => rfl

/-- The `Q` charges as a map `Fin n → ℚ`. -/
abbrev Q := @toSpecies n 0
/-- The `U` charges as a map `Fin n → ℚ`. -/
abbrev U := @toSpecies n 1
/-- The `D` charges as a map `Fin n → ℚ`. -/
abbrev D := @toSpecies n 2
/-- The `L` charges as a map `Fin n → ℚ`. -/
abbrev L := @toSpecies n 3
/-- The `E` charges as a map `Fin n → ℚ`. -/
abbrev E := @toSpecies n 4
/-- The `N` charges as a map `Fin n → ℚ`. -/
abbrev N := @toSpecies n 5

end SMνCharges

namespace SMνACCs

open SMνCharges

variable {n : ℕ}

/-- The gravitational anomaly equation. -/
@[simp]
def accGrav : (SMνCharges n).Charges →ₗ[ℚ] ℚ where
  toFun S := ∑ i, (6 * Q S i + 3 * U S i + 3 * D S i + 2 * L S i + E S i + N S i)
  map_add' S T := by
    repeat rw [map_add]
    simp only [SMνSpecies_numberCharges, ACCSystemCharges.chargesAddCommMonoid_add, toSpecies_apply,
      Fin.isValue, mul_add]
    repeat erw [Finset.sum_add_distrib]
    ring
  map_smul' a S := by
    repeat erw [map_smul]
    simp only [SMνSpecies_numberCharges, HSMul.hSMul, SMul.smul, toSpecies_apply, Fin.isValue,
      eq_ratCast, Rat.cast_eq_id, id_eq]
    repeat erw [Finset.sum_add_distrib]
    repeat erw [← Finset.mul_sum]
    -- rw [show Rat.cast a = a from rfl]
    ring

lemma accGrav_decomp (S : (SMνCharges n).Charges) :
    accGrav S = 6 * ∑ i, Q S i + 3 * ∑ i, U S i + 3 * ∑ i, D S i + 2 * ∑ i, L S i + ∑ i, E S i +
      ∑ i, N S i := by
  simp only [accGrav, SMνSpecies_numberCharges, toSpecies_apply, Fin.isValue, LinearMap.coe_mk,
    AddHom.coe_mk]
  repeat rw [Finset.sum_add_distrib]
  repeat rw [← Finset.mul_sum]

/-- Extensionality lemma for `accGrav`. -/
lemma accGrav_ext {S T : (SMνCharges n).Charges}
    (hj : ∀ (j : Fin 6), ∑ i, (toSpecies j) S i = ∑ i, (toSpecies j) T i) :
    accGrav S = accGrav T := by
  rw [accGrav_decomp, accGrav_decomp]
  repeat rw [hj]

/-- The `SU(2)` anomaly equation. -/
@[simp]
def accSU2 : (SMνCharges n).Charges →ₗ[ℚ] ℚ where
  toFun S := ∑ i, (3 * Q S i + L S i)
  map_add' S T := by
    repeat rw [map_add]
    simp only [SMνSpecies_numberCharges, ACCSystemCharges.chargesAddCommMonoid_add, toSpecies_apply,
      Fin.isValue, mul_add]
    repeat rw [Finset.sum_add_distrib]
    ring
  map_smul' a S := by
    repeat rw [map_smul]
    simp only [SMνSpecies_numberCharges, HSMul.hSMul, SMul.smul, toSpecies_apply, Fin.isValue,
      eq_ratCast, Rat.cast_eq_id, id_eq]
    repeat rw [Finset.sum_add_distrib]
    repeat rw [← Finset.mul_sum]
    -- rw [show Rat.cast a = a from rfl]
    ring

lemma accSU2_decomp (S : (SMνCharges n).Charges) :
    accSU2 S = 3 * ∑ i, Q S i + ∑ i, L S i := by
  simp only [accSU2, SMνSpecies_numberCharges, toSpecies_apply, Fin.isValue, LinearMap.coe_mk,
    AddHom.coe_mk]
  repeat rw [Finset.sum_add_distrib]
  repeat rw [← Finset.mul_sum]

/-- Extensionality lemma for `accSU2`. -/
lemma accSU2_ext {S T : (SMνCharges n).Charges}
    (hj : ∀ (j : Fin 6), ∑ i, (toSpecies j) S i = ∑ i, (toSpecies j) T i) :
    accSU2 S = accSU2 T := by
  rw [accSU2_decomp, accSU2_decomp]
  repeat rw [hj]

/-- The `SU(3)` anomaly equations. -/
@[simp]
def accSU3 : (SMνCharges n).Charges →ₗ[ℚ] ℚ where
  toFun S := ∑ i, (2 * Q S i + U S i + D S i)
  map_add' S T := by
    repeat rw [map_add]
    simp only [SMνSpecies_numberCharges, ACCSystemCharges.chargesAddCommMonoid_add, toSpecies_apply,
      Fin.isValue, mul_add]
    repeat erw [Finset.sum_add_distrib]
    ring
  map_smul' a S := by
    repeat erw [map_smul]
    simp only [SMνSpecies_numberCharges, HSMul.hSMul, SMul.smul, toSpecies_apply, Fin.isValue,
      eq_ratCast, Rat.cast_eq_id, id_eq]
    repeat rw [Finset.sum_add_distrib]
    repeat rw [← Finset.mul_sum]
    -- rw [show Rat.cast a = a from rfl]
    ring

lemma accSU3_decomp (S : (SMνCharges n).Charges) :
    accSU3 S = 2 * ∑ i, Q S i + ∑ i, U S i + ∑ i, D S i := by
  simp only [accSU3, SMνSpecies_numberCharges, toSpecies_apply, Fin.isValue, LinearMap.coe_mk,
    AddHom.coe_mk]
  repeat rw [Finset.sum_add_distrib]
  repeat rw [← Finset.mul_sum]

/-- Extensionality lemma for `accSU3`. -/
lemma accSU3_ext {S T : (SMνCharges n).Charges}
    (hj : ∀ (j : Fin 6), ∑ i, (toSpecies j) S i = ∑ i, (toSpecies j) T i) :
    accSU3 S = accSU3 T := by
  rw [accSU3_decomp, accSU3_decomp]
  repeat rw [hj]

/-- The `Y²` anomaly equation. -/
@[simp]
def accYY : (SMνCharges n).Charges →ₗ[ℚ] ℚ where
  toFun S := ∑ i, (Q S i + 8 * U S i + 2 * D S i + 3 * L S i
    + 6 * E S i)
  map_add' S T := by
    repeat rw [map_add]
    simp only [SMνSpecies_numberCharges, ACCSystemCharges.chargesAddCommMonoid_add, toSpecies_apply,
      Fin.isValue, mul_add]
    repeat erw [Finset.sum_add_distrib]
    ring
  map_smul' a S := by
    repeat rw [map_smul]
    simp only [SMνSpecies_numberCharges, HSMul.hSMul, SMul.smul, toSpecies_apply, Fin.isValue,
      eq_ratCast, Rat.cast_eq_id, id_eq]
    repeat erw [Finset.sum_add_distrib]
    repeat erw [← Finset.mul_sum]
    -- rw [show Rat.cast a = a from rfl]
    ring

lemma accYY_decomp (S : (SMνCharges n).Charges) :
    accYY S = ∑ i, Q S i + 8 * ∑ i, U S i + 2 * ∑ i, D S i + 3 * ∑ i, L S i + 6 * ∑ i, E S i := by
  simp only [accYY, SMνSpecies_numberCharges, toSpecies_apply, Fin.isValue, LinearMap.coe_mk,
    AddHom.coe_mk]
  repeat rw [Finset.sum_add_distrib]
  repeat rw [← Finset.mul_sum]

/-- Extensionality lemma for `accYY`. -/
lemma accYY_ext {S T : (SMνCharges n).Charges}
    (hj : ∀ (j : Fin 6), ∑ i, (toSpecies j) S i = ∑ i, (toSpecies j) T i) :
    accYY S = accYY T := by
  rw [accYY_decomp, accYY_decomp]
  repeat rw [hj]

/-- The quadratic bilinear map. -/
@[simps!]
def quadBiLin : BiLinearSymm (SMνCharges n).Charges := BiLinearSymm.mk₂
  (fun S => ∑ i, (Q S.1 i * Q S.2 i +
    - 2 * (U S.1 i * U S.2 i) +
    D S.1 i * D S.2 i +
    (- 1) * (L S.1 i * L S.2 i) +
    E S.1 i * E S.2 i))
  (by
    intro a S T
    simp only
    rw [Finset.mul_sum]
    refine Fintype.sum_congr _ _ fun i ↦ ?_
    repeat erw [map_smul]
    simp only [HSMul.hSMul, SMul.smul, toSpecies_apply, Fin.isValue, neg_mul, one_mul]
    ring)
  (by
    intro S T R
    simp only
    rw [← Finset.sum_add_distrib]
    refine Fintype.sum_congr _ _ fun i ↦ ?_
    repeat rw [map_add]
    simp only [ACCSystemCharges.chargesAddCommMonoid_add, toSpecies_apply, Fin.isValue, neg_mul,
      one_mul]
    ring)
  (by
    intro S T
    simp only [SMνSpecies_numberCharges, toSpecies_apply, Fin.isValue, neg_mul, one_mul]
    refine Fintype.sum_congr _ _ fun i ↦ ?_
    ring)

lemma quadBiLin_decomp (S T : (SMνCharges n).Charges) :
    quadBiLin S T = ∑ i, Q S i * Q T i - 2 * ∑ i, U S i * U T i +
        ∑ i, D S i * D T i - ∑ i, L S i * L T i + ∑ i, E S i * E T i := by
  erw [← quadBiLin.toFun_eq_coe]
  rw [quadBiLin]
  simp only [BiLinearSymm.mk₂, AddHom.toFun_eq_coe, AddHom.coe_mk, LinearMap.coe_mk]
  repeat rw [Finset.sum_add_distrib]
  repeat rw [← Finset.mul_sum]
  simp only [SMνSpecies_numberCharges, toSpecies_apply, Fin.isValue, neg_mul, one_mul, add_left_inj]
  ring

/-- The quadratic anomaly cancellation condition. -/
@[simp]
def accQuad : HomogeneousQuadratic (SMνCharges n).Charges :=
  (@quadBiLin n).toHomogeneousQuad

lemma accQuad_decomp (S : (SMνCharges n).Charges) :
    accQuad S = ∑ i, (Q S i)^2 - 2 * ∑ i, (U S i)^2 + ∑ i, (D S i)^2 - ∑ i, (L S i)^2
    + ∑ i, (E S i)^2 := by
  erw [quadBiLin_decomp]
  ring_nf

/-- Extensionality lemma for `accQuad`. -/
lemma accQuad_ext {S T : (SMνCharges n).Charges}
    (h : ∀ j, ∑ i, ((fun a => a^2) ∘ toSpecies j S) i =
    ∑ i, ((fun a => a^2) ∘ toSpecies j T) i) :
    accQuad S = accQuad T := by
  rw [accQuad_decomp, accQuad_decomp]
  erw [h 0, h 1, h 2, h 3, h 4]
  rfl

/-- The symmetric trilinear form used to define the cubic acc. -/
@[simps!]
def cubeTriLin : TriLinearSymm (SMνCharges n).Charges := TriLinearSymm.mk₃
  (fun S => ∑ i, (6 * ((Q S.1 i) * (Q S.2.1 i) * (Q S.2.2 i))
    + 3 * ((U S.1 i) * (U S.2.1 i) * (U S.2.2 i))
    + 3 * ((D S.1 i) * (D S.2.1 i) * (D S.2.2 i))
    + 2 * ((L S.1 i) * (L S.2.1 i) * (L S.2.2 i))
    + ((E S.1 i) * (E S.2.1 i) * (E S.2.2 i))
    + ((N S.1 i) * (N S.2.1 i) * (N S.2.2 i))))
  (by
    intro a S T R
    simp only
    rw [Finset.mul_sum]
    refine Fintype.sum_congr _ _ fun i ↦ ?_
    repeat erw [map_smul]
    simp only [HSMul.hSMul, SMul.smul, toSpecies_apply, Fin.isValue]
    ring)
  (by
    intro S T R L
    simp only
    rw [← Finset.sum_add_distrib]
    refine Fintype.sum_congr _ _ fun i ↦ ?_
    repeat erw [map_add]
    simp only [ACCSystemCharges.chargesAddCommMonoid_add, toSpecies_apply, Fin.isValue]
    ring)
  (by
    intro S T L
    simp only [SMνSpecies_numberCharges, toSpecies_apply, Fin.isValue]
    refine Fintype.sum_congr _ _ fun i ↦ ?_
    ring)
  (by
    intro S T L
    simp only [SMνSpecies_numberCharges, toSpecies_apply, Fin.isValue]
    refine Fintype.sum_congr _ _ fun i ↦ ?_
    ring)

lemma cubeTriLin_decomp (S T R : (SMνCharges n).Charges) :
    cubeTriLin S T R = 6 * ∑ i, (Q S i * Q T i * Q R i) + 3 * ∑ i, (U S i * U T i * U R i) +
      3 * ∑ i, (D S i * D T i * D R i) + 2 * ∑ i, (L S i * L T i * L R i) +
      ∑ i, (E S i * E T i * E R i) + ∑ i, (N S i * N T i * N R i) := by
  erw [← cubeTriLin.toFun_eq_coe]
  rw [cubeTriLin]
  simp only [TriLinearSymm.mk₃, BiLinearSymm.mk₂, SMνSpecies_numberCharges, toSpecies_apply,
    Fin.isValue, AddHom.toFun_eq_coe, AddHom.coe_mk, LinearMap.coe_mk]
  repeat erw [Finset.sum_add_distrib]
  repeat erw [← Finset.mul_sum]

/-- The cubic ACC. -/
@[simp]
def accCube : HomogeneousCubic (SMνCharges n).Charges := cubeTriLin.toCubic

lemma accCube_decomp (S : (SMνCharges n).Charges) :
    accCube S = 6 * ∑ i, (Q S i)^3 + 3 * ∑ i, (U S i)^3 + 3 * ∑ i, (D S i)^3 + 2 * ∑ i, (L S i)^3 +
      ∑ i, (E S i)^3 + ∑ i, (N S i)^3 := by
  change cubeTriLin S S S = _
  rw [cubeTriLin_decomp]
  ring_nf

/-- Extensionality lemma for `accCube`. -/
lemma accCube_ext {S T : (SMνCharges n).Charges}
    (h : ∀ j, ∑ i, ((fun a => a^3) ∘ toSpecies j S) i =
    ∑ i, ((fun a => a^3) ∘ toSpecies j T) i) :
    accCube S = accCube T := by
  rw [accCube_decomp]
  have h1 : ∀ j, ∑ i, (toSpecies j S i) ^ 3 = ∑ i, (toSpecies j T i) ^ 3 := by
    intro j
    erw [h]
    rfl
  repeat rw [h1]
  rw [accCube_decomp]

end SMνACCs
