/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import PhysLean.QFT.AnomalyCancellation.Basic
/-!
# The MSSM with 3 families and RHNs

We define the system of ACCs for the MSSM with 3 families and RHNs.
We define the system of charges for 1-species. We prove some basic lemmas about them.

-/

@[expose] public section

open Nat
open BigOperators

/-- The vector space of charges corresponding to the MSSM fermions. -/
@[simps!]
def MSSMCharges : ACCSystemCharges := ACCSystemChargesMk 20

/-- The vector spaces of charges of one species of fermions in the MSSM. -/
@[simps!]
def MSSMSpecies : ACCSystemCharges := ACCSystemChargesMk 3

namespace MSSMCharges

/-- An equivalence between `MSSMCharges.charges` and the space of maps
`(Fin 18 ⊕ Fin 2 → ℚ)`. The first 18 factors corresponds to the SM fermions, while the last two
are the higgsions. -/
@[simps!]
def toSMPlusH : MSSMCharges.Charges ≃ (Fin 18 ⊕ Fin 2 → ℚ) :=
  ((@finSumFinEquiv 18 2).arrowCongr (Equiv.refl ℚ)).symm

/-- An equivalence between `Fin 18 ⊕ Fin 2 → ℚ` and `(Fin 18 → ℚ) × (Fin 2 → ℚ)`. -/
@[simps!]
def splitSMPlusH : (Fin 18 ⊕ Fin 2 → ℚ) ≃ (Fin 18 → ℚ) × (Fin 2 → ℚ) where
  toFun f := (f ∘ Sum.inl, f ∘ Sum.inr)
  invFun f := Sum.elim f.1 f.2
  left_inv f := Sum.elim_comp_inl_inr f
  right_inv _ := rfl

/-- An equivalence between `MSSMCharges.charges` and `(Fin 18 → ℚ) × (Fin 2 → ℚ)`. This
splits the charges up into the SM and the additional ones for the MSSM. -/
@[simps!]
def toSplitSMPlusH : MSSMCharges.Charges ≃ (Fin 18 → ℚ) × (Fin 2 → ℚ) :=
  toSMPlusH.trans splitSMPlusH

/-- An equivalence between `(Fin 18 → ℚ)` and `(Fin 6 → Fin 3 → ℚ)`. -/
@[simps!]
def toSpeciesMaps' : (Fin 18 → ℚ) ≃ (Fin 6 → Fin 3 → ℚ) :=
  ((Equiv.curry _ _ _).symm.trans
    ((@finProdFinEquiv 6 3).arrowCongr (Equiv.refl ℚ))).symm

/-- An equivalence between `MSSMCharges.charges` and `(Fin 6 → Fin 3 → ℚ) × (Fin 2 → ℚ))`.
This splits charges up into the SM and additional fermions, and further splits the SM into
species. -/
@[simps!]
def toSpecies : MSSMCharges.Charges ≃ (Fin 6 → Fin 3 → ℚ) × (Fin 2 → ℚ) :=
  toSplitSMPlusH.trans (Equiv.prodCongr toSpeciesMaps' (Equiv.refl _))

/-- For a given `i ∈ Fin 6` the projection of `MSSMCharges.charges` down to the
corresponding SM species of charges. -/
@[simps!]
def toSMSpecies (i : Fin 6) : MSSMCharges.Charges →ₗ[ℚ] MSSMSpecies.Charges where
  toFun S := (Prod.fst ∘ toSpecies) S i
  map_add' _ _ := by rfl
  map_smul' _ _ := by rfl

lemma toSMSpecies_toSpecies_inv (i : Fin 6) (f : (Fin 6 → Fin 3 → ℚ) × (Fin 2 → ℚ)) :
    (toSMSpecies i) (toSpecies.symm f) = f.1 i := by
  change (Prod.fst ∘ toSpecies ∘ toSpecies.symm) _ i= f.1 i
  simp

/-- The `Q` charges as a map `Fin 3 → ℚ`. -/
abbrev Q := toSMSpecies 0
/-- The `U` charges as a map `Fin 3 → ℚ`. -/
abbrev U := toSMSpecies 1
/-- The `D` charges as a map `Fin 3 → ℚ`. -/
abbrev D := toSMSpecies 2
/-- The `L` charges as a map `Fin 3 → ℚ`. -/
abbrev L := toSMSpecies 3
/-- The `E` charges as a map `Fin 3 → ℚ`. -/
abbrev E := toSMSpecies 4
/-- The `N` charges as a map `Fin 3 → ℚ`. -/
abbrev N := toSMSpecies 5

/-- The charge `Hd`. -/
@[simps!]
def Hd : MSSMCharges.Charges →ₗ[ℚ] ℚ where
  toFun S := S ⟨18, Nat.lt_of_sub_eq_succ rfl⟩
  map_add' _ _ := by rfl
  map_smul' _ _ := by rfl

/-- The charge `Hu`. -/
@[simps!]
def Hu : MSSMCharges.Charges →ₗ[ℚ] ℚ where
  toFun S := S ⟨19, Nat.lt_of_sub_eq_succ rfl⟩
  map_add' _ _ := by rfl
  map_smul' _ _ := by rfl

lemma charges_eq_toSpecies_eq (S T : MSSMCharges.Charges) :
    S = T ↔ (∀ i, toSMSpecies i S = toSMSpecies i T) ∧ Hd S = Hd T ∧ Hu S = Hu T := by
  refine Iff.intro (fun h => ?_) (fun h => ?_)
  · rw [h]
    simp only [forall_const, Hd_apply, Fin.reduceFinMk, Fin.isValue, Hu_apply, and_self]
  · apply toSpecies.injective
    apply Prod.ext
    · funext i
      exact h.1 i
    · funext i
      match i with
      | 0 => exact h.2.1
      | 1 => exact h.2.2

lemma Hd_toSpecies_inv (f : (Fin 6 → Fin 3 → ℚ) × (Fin 2 → ℚ)) :
    Hd (toSpecies.symm f) = f.2 0 := by
  rfl

lemma Hu_toSpecies_inv (f : (Fin 6 → Fin 3 → ℚ) × (Fin 2 → ℚ)) :
    Hu (toSpecies.symm f) = f.2 1 := by
  rfl

end MSSMCharges

namespace MSSMACCs

open MSSMCharges

/-- The gravitational anomaly equation. -/
@[simp]
def accGrav : MSSMCharges.Charges →ₗ[ℚ] ℚ where
  toFun S := ∑ i, (6 * Q S i + 3 * U S i + 3 * D S i
    + 2 * L S i + E S i + N S i) + 2 * (Hd S + Hu S)
  map_add' S T := by
    repeat rw [map_add]
    simp only [MSSMSpecies_numberCharges, ACCSystemCharges.chargesAddCommMonoid_add,
      toSMSpecies_apply, reduceMul, Fin.isValue, mul_add, Hd_apply, Fin.reduceFinMk, Hu_apply]
    repeat rw [Finset.sum_add_distrib]
    ring
  map_smul' a S := by
    repeat rw [(toSMSpecies _).map_smul]
    erw [Hd.map_smul, Hu.map_smul]
    simp only [MSSMSpecies_numberCharges, HSMul.hSMul, SMul.smul, Fin.isValue, toSMSpecies_apply,
      reduceMul, Hd_apply, Fin.reduceFinMk, Hu_apply, eq_ratCast, Rat.cast_eq_id, id_eq]
    repeat rw [Finset.sum_add_distrib]
    repeat rw [← Finset.mul_sum]
    ring

/-- Extensionality lemma for `accGrav`. -/
lemma accGrav_ext {S T : MSSMCharges.Charges}
    (hj : ∀ (j : Fin 6), ∑ i, (toSMSpecies j) S i = ∑ i, (toSMSpecies j) T i)
    (hd : Hd S = Hd T) (hu : Hu S = Hu T) :
    accGrav S = accGrav T := by
  simp only [accGrav, MSSMSpecies_numberCharges, toSMSpecies_apply, Fin.isValue,
    LinearMap.coe_mk, AddHom.coe_mk]
  repeat erw [Finset.sum_add_distrib]
  repeat erw [← Finset.mul_sum]
  repeat erw [hj]
  rw [hd, hu]
  rfl

/-- The anomaly cancellation condition for SU(2) anomaly. -/
@[simp]
def accSU2 : MSSMCharges.Charges →ₗ[ℚ] ℚ where
  toFun S := ∑ i, (3 * Q S i + L S i) + Hd S + Hu S
  map_add' S T := by
    repeat rw [map_add]
    simp only [MSSMSpecies_numberCharges, ACCSystemCharges.chargesAddCommMonoid_add,
      toSMSpecies_apply, reduceMul, Fin.isValue, mul_add, Hd_apply, Fin.reduceFinMk, Hu_apply]
    repeat erw [Finset.sum_add_distrib]
    ring
  map_smul' a S := by
    repeat rw [(toSMSpecies _).map_smul]
    erw [Hd.map_smul, Hu.map_smul]
    simp only [MSSMSpecies_numberCharges, HSMul.hSMul, SMul.smul, Fin.isValue, toSMSpecies_apply,
      reduceMul, Hd_apply, Fin.reduceFinMk, Hu_apply, eq_ratCast, Rat.cast_eq_id, id_eq]
    repeat erw [Finset.sum_add_distrib]
    repeat erw [← Finset.mul_sum]
    --rw [show Rat.cast a = a from rfl]
    ring

/-- Extensionality lemma for `accSU2`. -/
lemma accSU2_ext {S T : MSSMCharges.Charges}
    (hj : ∀ (j : Fin 6), ∑ i, (toSMSpecies j) S i = ∑ i, (toSMSpecies j) T i)
    (hd : Hd S = Hd T) (hu : Hu S = Hu T) :
    accSU2 S = accSU2 T := by
  simp only [accSU2, MSSMSpecies_numberCharges, toSMSpecies_apply, Fin.isValue,
    LinearMap.coe_mk, AddHom.coe_mk]
  repeat erw [Finset.sum_add_distrib]
  repeat erw [← Finset.mul_sum]
  repeat erw [hj]
  rw [hd, hu]
  rfl

/-- The anomaly cancellation condition for SU(3) anomaly. -/
@[simp]
def accSU3 : MSSMCharges.Charges →ₗ[ℚ] ℚ where
  toFun S := ∑ i, (2 * (Q S i) + (U S i) + (D S i))
  map_add' S T := by
    repeat rw [map_add]
    simp only [MSSMSpecies_numberCharges, ACCSystemCharges.chargesAddCommMonoid_add,
      toSMSpecies_apply, reduceMul, Fin.isValue, mul_add]
    repeat erw [Finset.sum_add_distrib]
    ring
  map_smul' a S := by
    repeat rw [(toSMSpecies _).map_smul]
    simp only [MSSMSpecies_numberCharges, HSMul.hSMul, SMul.smul, Fin.isValue, toSMSpecies_apply,
      reduceMul, eq_ratCast, Rat.cast_eq_id, id_eq]
    repeat erw [Finset.sum_add_distrib]
    repeat erw [← Finset.mul_sum]
    --rw [show Rat.cast a = a from rfl]
    ring

/-- Extensionality lemma for `accSU3`. -/
lemma accSU3_ext {S T : MSSMCharges.Charges}
    (hj : ∀ (j : Fin 6), ∑ i, (toSMSpecies j) S i = ∑ i, (toSMSpecies j) T i) :
    accSU3 S = accSU3 T := by
  simp only [accSU3, MSSMSpecies_numberCharges, toSMSpecies_apply, Fin.isValue, LinearMap.coe_mk,
    AddHom.coe_mk]
  repeat erw [Finset.sum_add_distrib]
  repeat erw [← Finset.mul_sum]
  repeat erw [hj]
  rfl

/-- The ACC for `Y²`. -/
@[simp]
def accYY : MSSMCharges.Charges →ₗ[ℚ] ℚ where
  toFun S := ∑ i, ((Q S) i + 8 * (U S) i + 2 * (D S) i + 3 * (L S) i
    + 6 * (E S) i) + 3 * (Hd S + Hu S)
  map_add' S T := by
    repeat rw [map_add]
    simp only [MSSMSpecies_numberCharges, ACCSystemCharges.chargesAddCommMonoid_add,
      toSMSpecies_apply, reduceMul, Fin.isValue, mul_add, Hd_apply, Fin.reduceFinMk, Hu_apply]
    repeat erw [Finset.sum_add_distrib]
    ring
  map_smul' a S := by
    repeat rw [(toSMSpecies _).map_smul]
    erw [Hd.map_smul, Hu.map_smul]
    simp only [MSSMSpecies_numberCharges, HSMul.hSMul, SMul.smul, Fin.isValue, toSMSpecies_apply,
      reduceMul, Hd_apply, Fin.reduceFinMk, Hu_apply, eq_ratCast, Rat.cast_eq_id, id_eq]
    repeat erw [Finset.sum_add_distrib]
    repeat erw [← Finset.mul_sum]
    -- rw [show Rat.cast a = a from rfl]
    ring

/-- Extensionality lemma for `accGrav`. -/
lemma accYY_ext {S T : MSSMCharges.Charges}
    (hj : ∀ (j : Fin 6), ∑ i, (toSMSpecies j) S i = ∑ i, (toSMSpecies j) T i)
    (hd : Hd S = Hd T) (hu : Hu S = Hu T) :
    accYY S = accYY T := by
  simp only [accYY, MSSMSpecies_numberCharges, toSMSpecies_apply, Fin.isValue,
    LinearMap.coe_mk, AddHom.coe_mk]
  repeat erw [Finset.sum_add_distrib]
  repeat erw [← Finset.mul_sum]
  repeat erw [hj]
  rw [hd, hu]
  rfl

/-- The symmetric bilinear function used to define the quadratic ACC. -/
@[simps!]
def quadBiLin : BiLinearSymm MSSMCharges.Charges := BiLinearSymm.mk₂
  (fun (S, T) => ∑ i, (Q S i * Q T i + (- 2) * (U S i * U T i) +
    D S i * D T i + (- 1) * (L S i * L T i) + E S i * E T i) +
    (- Hd S * Hd T + Hu S * Hu T))
  (by
    intro a S T
    simp only
    rw [mul_add]
    congr 1
    · rw [Finset.mul_sum]
      apply Fintype.sum_congr
      intro i
      repeat erw [map_smul]
      simp only [HSMul.hSMul, SMul.smul, toSMSpecies_apply, Fin.isValue, neg_mul, one_mul]
      ring
    · simp only [map_smul, Hd_apply, Fin.reduceFinMk, Fin.isValue, smul_eq_mul, neg_mul, Hu_apply]
      ring)
  (by
    intro S T R
    simp only
    rw [add_assoc, ← add_assoc (-Hd S * Hd R + Hu S * Hu R) _ _]
    rw [add_comm (-Hd S * Hd R + Hu S * Hu R) _]
    rw [add_assoc]
    rw [← add_assoc _ _ (-Hd S * Hd R + Hu S * Hu R + (-Hd T * Hd R + Hu T * Hu R))]
    congr 1
    · rw [← Finset.sum_add_distrib]
      apply Fintype.sum_congr
      intro i
      repeat erw [map_add]
      simp only [ACCSystemCharges.chargesAddCommMonoid_add, toSMSpecies_apply, Fin.isValue, neg_mul,
        one_mul]
      ring
    · rw [Hd.map_add, Hu.map_add]
      ring)
  (by
    intro S L
    simp only [MSSMSpecies_numberCharges, toSMSpecies_apply, Fin.isValue, neg_mul, one_mul,
      Hd_apply, Fin.reduceFinMk, Hu_apply]
    congr 1
    · rw [Fin.sum_univ_three, Fin.sum_univ_three]
      simp only [reduceMul, Fin.isValue, Prod.mk_zero_zero, Prod.mk_one_one]
      ring
    · ring)

/-- The quadratic ACC. -/
@[simp]
def accQuad : HomogeneousQuadratic MSSMCharges.Charges := quadBiLin.toHomogeneousQuad

/-- Extensionality lemma for `accQuad`. -/
lemma accQuad_ext {S T : (MSSMCharges).Charges}
    (h : ∀ j, ∑ i, ((fun a => a^2) ∘ toSMSpecies j S) i =
    ∑ i, ((fun a => a^2) ∘ toSMSpecies j T) i)
    (hd : Hd S = Hd T) (hu : Hu S = Hu T) :
    accQuad S = accQuad T := by
  simp only [HomogeneousQuadratic, accQuad, BiLinearSymm.toHomogeneousQuad_apply]
  erw [← quadBiLin.toFun_eq_coe]
  simp only [quadBiLin, BiLinearSymm.mk₂, AddHom.toFun_eq_coe, AddHom.coe_mk, LinearMap.coe_mk]
  repeat erw [Finset.sum_add_distrib]
  repeat erw [← Finset.mul_sum]
  ring_nf
  have h1 : ∀ j, ∑ i, (toSMSpecies j S i)^2 = ∑ i, (toSMSpecies j T i)^2 := fun j => h j
  repeat rw [h1]
  rw [hd, hu]

/-- The function underlying the symmetric trilinear form used to define the cubic ACC. -/
@[simp]
def cubeTriLinToFun
    (S : MSSMCharges.Charges × MSSMCharges.Charges × MSSMCharges.Charges) : ℚ :=
  ∑ i, (6 * (Q S.1 i * Q S.2.1 i * Q S.2.2 i)
    + 3 * (U S.1 i * U S.2.1 i * U S.2.2 i)
    + 3 * (D S.1 i * D S.2.1 i * D S.2.2 i)
    + 2 * (L S.1 i * L S.2.1 i * L S.2.2 i)
    + E S.1 i * E S.2.1 i * E S.2.2 i
    + N S.1 i * N S.2.1 i * N S.2.2 i)
    + (2 * Hd S.1 * Hd S.2.1 * Hd S.2.2
    + 2 * Hu S.1 * Hu S.2.1 * Hu S.2.2)

lemma cubeTriLinToFun_map_smul₁ (a : ℚ) (S T R : MSSMCharges.Charges) :
    cubeTriLinToFun (a • S, T, R) = a * cubeTriLinToFun (S, T, R) := by
  simp only [cubeTriLinToFun]
  rw [mul_add]
  congr 1
  · rw [Finset.mul_sum]
    apply Fintype.sum_congr
    intro i
    repeat erw [map_smul]
    simp only [HSMul.hSMul, SMul.smul, toSMSpecies_apply, Fin.isValue]
    ring
  · simp only [map_smul, Hd_apply, Fin.reduceFinMk, Fin.isValue, smul_eq_mul, Hu_apply]
    ring

lemma cubeTriLinToFun_map_add₁ (S T R L : MSSMCharges.Charges) :
    cubeTriLinToFun (S + T, R, L) = cubeTriLinToFun (S, R, L) + cubeTriLinToFun (T, R, L) := by
  simp only [cubeTriLinToFun]
  rw [add_assoc, ← add_assoc (2 * Hd S * Hd R * Hd L + 2 * Hu S * Hu R * Hu L) _ _]
  rw [add_comm (2 * Hd S * Hd R * Hd L + 2 * Hu S * Hu R * Hu L) _]
  rw [add_assoc]
  rw [← add_assoc _ _ (2 * Hd S * Hd R * Hd L + 2 * Hu S * Hu R * Hu L +
    (2 * Hd T * Hd R * Hd L + 2 * Hu T * Hu R * Hu L))]
  congr 1
  · rw [← Finset.sum_add_distrib]
    apply Fintype.sum_congr
    intro i
    repeat erw [map_add]
    simp only [ACCSystemCharges.chargesAddCommMonoid_add, toSMSpecies_apply, Fin.isValue]
    ring
  · rw [Hd.map_add, Hu.map_add]
    ring

lemma cubeTriLinToFun_swap1 (S T R : MSSMCharges.Charges) :
    cubeTriLinToFun (S, T, R) = cubeTriLinToFun (T, S, R) := by
  simp only [cubeTriLinToFun, MSSMSpecies_numberCharges, toSMSpecies_apply, Fin.isValue, Hd_apply,
    Fin.reduceFinMk, Hu_apply]
  congr 1
  · rw [Fin.sum_univ_three, Fin.sum_univ_three]
    simp only [reduceMul, Fin.isValue, Prod.mk_zero_zero, Prod.mk_one_one]
    ring
  · ring

lemma cubeTriLinToFun_swap2 (S T R : MSSMCharges.Charges) :
    cubeTriLinToFun (S, T, R) = cubeTriLinToFun (S, R, T) := by
  simp only [cubeTriLinToFun, MSSMSpecies_numberCharges, toSMSpecies_apply, Fin.isValue, Hd_apply,
    Fin.reduceFinMk, Hu_apply]
  congr 1
  · rw [Fin.sum_univ_three, Fin.sum_univ_three]
    simp only [reduceMul, Fin.isValue, Prod.mk_zero_zero, Prod.mk_one_one]
    ring
  · ring

/-- The symmetric trilinear form used to define the cubic ACC. -/
@[simps!]
def cubeTriLin : TriLinearSymm MSSMCharges.Charges := TriLinearSymm.mk₃
  cubeTriLinToFun
  cubeTriLinToFun_map_smul₁
  cubeTriLinToFun_map_add₁
  cubeTriLinToFun_swap1
  cubeTriLinToFun_swap2

/-- The cubic ACC. -/
@[simp]
def accCube : HomogeneousCubic MSSMCharges.Charges := cubeTriLin.toCubic

/-- Extensionality lemma for `accCube`. -/
lemma accCube_ext {S T : MSSMCharges.Charges}
    (h : ∀ j, ∑ i, ((fun a => a^3) ∘ toSMSpecies j S) i =
    ∑ i, ((fun a => a^3) ∘ toSMSpecies j T) i)
    (hd : Hd S = Hd T) (hu : Hu S = Hu T) :
    accCube S = accCube T := by
  simp only [HomogeneousCubic, accCube, cubeTriLin, TriLinearSymm.toCubic_apply,
    TriLinearSymm.mk₃_toFun_apply_apply, cubeTriLinToFun]
  repeat erw [Finset.sum_add_distrib]
  repeat erw [← Finset.mul_sum]
  ring_nf
  have h1 : ∀ j, ∑ i, (toSMSpecies j S i)^3 = ∑ i, (toSMSpecies j T i)^3 := by
    intro j
    erw [h]
    rfl
  repeat rw [h1]
  rw [hd, hu]

end MSSMACCs

open MSSMACCs

/-- The ACCSystem for the MSSM without RHN. -/
@[simps!]
def MSSMACC : ACCSystem where
  toACCSystemCharges := MSSMCharges
  numberLinear := 4
  linearACCs := fun i =>
    match i with
    | 0 => accGrav
    | 1 => accSU2
    | 2 => accSU3
    | 3 => accYY
  numberQuadratic := 1
  quadraticACCs := fun i =>
    match i with
    | 0 => accQuad
  cubicACC := accCube

namespace MSSMACC
open MSSMCharges

lemma quadSol (S : MSSMACC.QuadSols) : accQuad S.val = 0 := by
  have hS := S.quadSol
  simp only [MSSMACC_numberQuadratic, HomogeneousQuadratic, MSSMACC_quadraticACCs] at hS
  exact hS 0

/-- A solution from a charge satisfying the ACCs. -/
@[simp]
def AnomalyFreeMk (S : MSSMACC.Charges) (hg : accGrav S = 0)
    (hsu2 : accSU2 S = 0) (hsu3 : accSU3 S = 0) (hyy : accYY S = 0)
    (hquad : accQuad S = 0) (hcube : accCube S = 0) : MSSMACC.Sols :=
  ⟨⟨⟨S, by
    intro i
    simp only [MSSMACC_numberLinear] at i
    match i with
    | 0 => exact hg
    | 1 => exact hsu2
    | 2 => exact hsu3
    | 3 => exact hyy⟩, by
    intro i
    simp only [MSSMACC_numberQuadratic] at i
    match i with
    | 0 => exact hquad⟩, hcube⟩

lemma AnomalyFreeMk_val (S : MSSMACC.Charges) (hg : accGrav S = 0)
    (hsu2 : accSU2 S = 0) (hsu3 : accSU3 S = 0) (hyy : accYY S = 0)
    (hquad : accQuad S = 0) (hcube : accCube S = 0) :
    (AnomalyFreeMk S hg hsu2 hsu3 hyy hquad hcube).val = S := by
  rfl

/-- A `QuadSol` from a `LinSol` satisfying the quadratic ACC. -/
@[simp]
def AnomalyFreeQuadMk' (S : MSSMACC.LinSols) (hquad : accQuad S.val = 0) :
    MSSMACC.QuadSols :=
  ⟨S, by
    intro i
    simp only [MSSMACC_numberQuadratic] at i
    match i with
    | 0 => exact hquad⟩

/-- A `Sol` from a `LinSol` satisfying the quadratic and cubic ACCs. -/
@[simp]
def AnomalyFreeMk' (S : MSSMACC.LinSols) (hquad : accQuad S.val = 0)
    (hcube : accCube S.val = 0) : MSSMACC.Sols :=
  ⟨⟨S, by
    intro i
    simp only [MSSMACC_numberQuadratic] at i
    match i with
    | 0 => exact hquad⟩, hcube⟩

/-- A `Sol` from a `QuadSol` satisfying the cubic ACCs. -/
@[simp]
def AnomalyFreeMk'' (S : MSSMACC.QuadSols) (hcube : accCube S.val = 0) : MSSMACC.Sols :=
  ⟨S, hcube⟩

lemma AnomalyFreeMk''_val (S : MSSMACC.QuadSols)
    (hcube : accCube S.val = 0) :
    (AnomalyFreeMk'' S hcube).val = S.val := by
  rfl

/-- The dot product on the vector space of charges. -/
@[simps!]
def dot : BiLinearSymm MSSMCharges.Charges := BiLinearSymm.mk₂
  (fun S => ∑ i, (Q S.1 i * Q S.2 i + U S.1 i * U S.2 i +
    D S.1 i * D S.2 i + L S.1 i * L S.2 i + E S.1 i * E S.2 i
    + N S.1 i * N S.2 i) + Hd S.1 * Hd S.2 + Hu S.1 * Hu S.2)
  (by
    intro a S T
    simp only [MSSMSpecies_numberCharges]
    repeat rw [(toSMSpecies _).map_smul]
    rw [Hd.map_smul, Hu.map_smul]
    rw [Fin.sum_univ_three, Fin.sum_univ_three]
    simp only [HSMul.hSMul, SMul.smul, Fin.isValue, toSMSpecies_apply, Hd_apply, Fin.reduceFinMk,
      Hu_apply]
    ring)
  (by
    intro S1 S2 T
    simp only [MSSMSpecies_numberCharges, toSMSpecies_apply, Fin.isValue,
      ACCSystemCharges.chargesAddCommMonoid_add, map_add, Hd_apply, Fin.reduceFinMk, Hu_apply]
    rw [Fin.sum_univ_three, Fin.sum_univ_three, Fin.sum_univ_three]
    simp only [reduceMul, Fin.isValue, Prod.mk_zero_zero, Prod.mk_one_one]
    ring)
  (by
    intro S T
    simp only [MSSMSpecies_numberCharges, toSMSpecies_apply, Fin.isValue, Hd_apply, Fin.reduceFinMk,
      Hu_apply]
    rw [Fin.sum_univ_three, Fin.sum_univ_three]
    simp only [reduceMul, Fin.isValue, Prod.mk_zero_zero, Prod.mk_one_one]
    ring)

end MSSMACC
