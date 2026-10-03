/-
Copyright (c) 2026 Jinzheng Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jinzheng Li
-/
module

public import Physlib.ClassicalFieldTheory.GaugeTheory.LocalGaugeData.SU.Algebra
public import Physlib.ClassicalFieldTheory.GaugeTheory.LocalGaugeData.MatrixJets
public import Physlib.SpaceAndTime.SpaceTime.SpaceTimeAlgebra.Jacobi
public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
/-!
# The local gauge data of `SU(n)`

## i. Overview

The gauge group `SU(n)`, with its jets, its Lie algebra and the jets of its Lie algebra,
packaged as local gauge data `LocalGaugeData.su n`. The jets of gauge transformations are
the special unitary matrices of formal power series, the Lie algebra `su(n)` is the
traceless hermitian matrices (`SUAlgebraOver ℂ n`) and its jets the traceless hermitian
matrices of power series. Evaluation and the constant inclusion act entrywise, the adjoint
action is conjugation, and the Maurer–Cartan form is `i (∂_μ U) U⁻¹`, hermitian by the
differentiated unitarity relation and traceless by Jacobi's formula.

This is a presentation by matrices of jets, `LocalGaugeData.suMatrixJets n`, so the laws of
the local gauge data, its canonical `SUFactor` and its faithfulness come from
`Physlib.ClassicalFieldTheory.GaugeTheory.LocalGaugeData.MatrixJets`. What this file
supplies is the carriers and the structure maps on them.

## ii. Key results

- `SU`, `JetSU`, `SUAlgebra`, `JetSUAlgebra` : the carriers.
- `JetSUAlgebra.mc` : the Maurer–Cartan form.
- `LocalGaugeData.suMatrixJets` : the presentation of `SU(n)` by matrices of jets.
- `LocalGaugeData.su` : the local gauge data of `SU(n)`.
- `LocalGaugeData.suFactor` : its canonical `SU(n)` factor.
- `LocalGaugeData.instFaithfulSU` : the package is faithful.
- `LocalGaugeData.instFreeSU` : the package is free.

## iii. Table of contents

- A. The carriers
- B. The structure maps on the group
- C. The structure maps on the Lie algebra
- D. The Maurer–Cartan form
- E. The presentation and the local gauge data

-/

@[expose] public section

open Matrix MatrixGroups MvPowerSeries

/-!

## A. The carriers

-/

/-- The gauge group `SU(n)`. -/
abbrev SU (n : ℕ) : Type := specialUnitaryGroup (Fin n) ℂ

/-- Jets of `SU(n)` gauge transformations: special unitary matrices of formal power
  series. -/
abbrev JetSU (n : ℕ) : Type := specialUnitaryGroup (Fin n) SpaceTimeAlgebra

/-- The Lie algebra `su(n)`: traceless hermitian matrices. -/
abbrev SUAlgebra (n : ℕ) : Type := SUAlgebraOver ℂ n

/-- Jets of the Lie algebra `su(n)`: traceless hermitian matrices of formal power series. -/
abbrev JetSUAlgebra (n : ℕ) : Type := SUAlgebraOver SpaceTimeAlgebra n

namespace JetSU

variable {n : ℕ}

/-!

## B. The structure maps on the group

-/

lemma val_mul_star (U : JetSU n) : U.1 * star U.1 = 1 :=
  mem_unitaryGroup_iff.mp (mem_specialUnitaryGroup_iff.mp U.2).1

lemma star_mul_val (U : JetSU n) : star U.1 * U.1 = 1 :=
  mem_unitaryGroup_iff'.mp (mem_specialUnitaryGroup_iff.mp U.2).1

lemma det_val (U : JetSU n) : U.1.det = 1 := (mem_specialUnitaryGroup_iff.mp U.2).2

/-- For a special unitary matrix, the conjugate transpose is the adjugate. -/
lemma star_val_eq_adjugate (U : JetSU n) : star U.1 = U.1.adjugate := by
  calc star U.1 = star U.1 * (U.1 * U.1.adjugate) := by
        rw [Matrix.mul_adjugate, det_val, one_smul, mul_one]
    _ = star U.1 * U.1 * U.1.adjugate := by rw [mul_assoc]
    _ = U.1.adjugate := by rw [star_mul_val, one_mul]

/-- Evaluation of a jet of an `SU(n)` gauge transformation at the base point: the entrywise
  constant coefficient. -/
noncomputable def eval : JetSU n →* SU n where
  toFun U := ⟨(constantCoeff : SpaceTimeAlgebra →+* ℂ).mapMatrix U.1, by
    obtain ⟨h1, h2⟩ := mem_specialUnitaryGroup_iff.mp U.2
    rw [mem_specialUnitaryGroup_iff]
    constructor
    · rw [mem_unitaryGroup_iff] at h1 ⊢
      rw [show star ((constantCoeff : SpaceTimeAlgebra →+* ℂ).mapMatrix U.1) =
          (constantCoeff : SpaceTimeAlgebra →+* ℂ).mapMatrix (star U.1) from
          (SpaceTimeAlgebra.mapMatrix_constantCoeff_star U.1).symm, ← map_mul, h1, map_one]
    · rw [← RingHom.map_det, h2, map_one]⟩
  map_one' := Subtype.ext (map_one ((constantCoeff : SpaceTimeAlgebra →+* ℂ).mapMatrix))
  map_mul' U V := Subtype.ext (map_mul ((constantCoeff : SpaceTimeAlgebra →+* ℂ).mapMatrix) U.1 V.1)

@[simp]
lemma eval_val (U : JetSU n) : (eval U).1 =
    (constantCoeff : SpaceTimeAlgebra →+* ℂ).mapMatrix U.1 := rfl

/-- The jet of a constant `SU(n)` gauge transformation: the entrywise inclusion of
  constants. -/
noncomputable def ofConstant : SU n →* JetSU n where
  toFun u := ⟨(C : ℂ →+* SpaceTimeAlgebra).mapMatrix u.1, by
    obtain ⟨h1, h2⟩ := mem_specialUnitaryGroup_iff.mp u.2
    rw [mem_specialUnitaryGroup_iff]
    constructor
    · rw [mem_unitaryGroup_iff] at h1 ⊢
      rw [show star ((C : ℂ →+* SpaceTimeAlgebra).mapMatrix u.1) =
          (C : ℂ →+* SpaceTimeAlgebra).mapMatrix (star u.1) from
          (SpaceTimeAlgebra.mapMatrix_C_star u.1).symm, ← map_mul, h1, map_one]
    · rw [← RingHom.map_det, h2, map_one]⟩
  map_one' := Subtype.ext (map_one ((C : ℂ →+* SpaceTimeAlgebra).mapMatrix))
  map_mul' u v := Subtype.ext (map_mul ((C : ℂ →+* SpaceTimeAlgebra).mapMatrix) u.1 v.1)

@[simp]
lemma ofConstant_val (u : SU n) : (ofConstant u).1 =
    (C : ℂ →+* SpaceTimeAlgebra).mapMatrix u.1 := rfl

/-- The Maurer–Cartan matrix `i (∂_μ U) U†` is traceless, by Jacobi's formula and
  `det U = 1`. -/
lemma trace_mcMatrix (μ : Fin 1 ⊕ Fin 3) (U : JetSU n) :
    (Complex.I • (U.1.map (pderiv μ) * star U.1)).trace = 0 := by
  rw [Matrix.trace_smul, star_val_eq_adjugate, ← SpaceTimeAlgebra.jacobi, det_val, pderiv_one,
    smul_zero]

end JetSU

namespace JetSUAlgebra

variable {n : ℕ}

/-!

## C. The structure maps on the Lie algebra

-/

/-- The formal derivative in the direction `μ`, entrywise. -/
noncomputable def deriv (μ : Fin 1 ⊕ Fin 3) : JetSUAlgebra n →ₗ[ℝ] JetSUAlgebra n where
  toFun a := SUAlgebraOver.ofMatrix (a.1.map (pderiv μ))
    (by rw [SpaceTimeAlgebra.star_map_pderiv, a.star_val])
    (by rw [← AddMonoidHom.map_trace, a.trace_val, map_zero])
  map_add' a b := Subtype.ext (by
    ext i j : 1
    simp [Matrix.map_apply])
  map_smul' r a := Subtype.ext (by
    ext i j : 1
    simp only [SUAlgebraOver.ofMatrix_val, Submodule.coe_smul, Matrix.map_apply,
      Matrix.smul_apply, RingHom.id_apply]
    exact SpaceTimeAlgebra.pderiv_real_smul μ r _)

@[simp]
lemma deriv_val (μ : Fin 1 ⊕ Fin 3) (a : JetSUAlgebra n) :
    (deriv μ a).1 = a.1.map (pderiv μ) := rfl

/-- Multiplication by the coordinate `x_μ`, entrywise. -/
noncomputable def coord (μ : Fin 1 ⊕ Fin 3) : JetSUAlgebra n →ₗ[ℝ] JetSUAlgebra n where
  toFun a := SUAlgebraOver.ofMatrix ((X μ : SpaceTimeAlgebra) • a.1)
    (by rw [star_smul, SpaceTimeAlgebra.star_X, a.star_val])
    (by rw [Matrix.trace_smul, a.trace_val, smul_zero])
  map_add' a b := Subtype.ext (by simp [smul_add])
  map_smul' r a := Subtype.ext (by simp [smul_comm r])

@[simp]
lemma coord_val (μ : Fin 1 ⊕ Fin 3) (a : JetSUAlgebra n) :
    (coord μ a).1 = (X μ : SpaceTimeAlgebra) • a.1 := rfl

lemma star_mapMatrix_constantCoeff (a : JetSUAlgebra n) :
    star ((constantCoeff : SpaceTimeAlgebra →+* ℂ).mapMatrix a.1)
      = (constantCoeff : SpaceTimeAlgebra →+* ℂ).mapMatrix a.1 := by
  rw [← SpaceTimeAlgebra.mapMatrix_constantCoeff_star, a.star_val]

lemma trace_mapMatrix_constantCoeff (a : JetSUAlgebra n) :
    ((constantCoeff : SpaceTimeAlgebra →+* ℂ).mapMatrix a.1).trace = 0 := by
  rw [RingHom.mapMatrix_apply, ← AddMonoidHom.map_trace, a.trace_val, map_zero]

/-- Evaluation at the base point: the entrywise constant coefficient. -/
noncomputable def evalLie : JetSUAlgebra n →ₗ[ℝ] SUAlgebra n where
  toFun a := SUAlgebraOver.ofMatrix ((constantCoeff : SpaceTimeAlgebra →+* ℂ).mapMatrix a.1)
    (star_mapMatrix_constantCoeff a) (trace_mapMatrix_constantCoeff a)
  map_add' a b := Subtype.ext (by
    simp only [SUAlgebraOver.ofMatrix_val, Submodule.coe_add]
    exact map_add _ _ _)
  map_smul' r a := Subtype.ext (by
    simp only [SUAlgebraOver.ofMatrix_val, Submodule.coe_smul, RingHom.id_apply]
    ext i j
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.smul_apply]
    exact SpaceTimeAlgebra.constantCoeff_real_smul r _)

@[simp]
lemma evalLie_val (a : JetSUAlgebra n) :
    (evalLie a).1 = (constantCoeff : SpaceTimeAlgebra →+* ℂ).mapMatrix a.1 := rfl

lemma star_mapMatrix_C (a : SUAlgebra n) :
    star ((C : ℂ →+* SpaceTimeAlgebra).mapMatrix a.1) =
        (C : ℂ →+* SpaceTimeAlgebra).mapMatrix a.1 := by
  rw [← SpaceTimeAlgebra.mapMatrix_C_star, a.star_val]

lemma trace_mapMatrix_C (a : SUAlgebra n) :
    ((C : ℂ →+* SpaceTimeAlgebra).mapMatrix a.1).trace = 0 := by
  rw [RingHom.mapMatrix_apply, ← AddMonoidHom.map_trace, a.trace_val, map_zero]

/-- A constant as a jet: the entrywise constant power series. -/
noncomputable def ofConstantLie : SUAlgebra n →ₗ[ℝ] JetSUAlgebra n where
  toFun a := SUAlgebraOver.ofMatrix ((C : ℂ →+* SpaceTimeAlgebra).mapMatrix a.1)
    (star_mapMatrix_C a) (trace_mapMatrix_C a)
  map_add' a b := Subtype.ext (by
    simp only [SUAlgebraOver.ofMatrix_val, Submodule.coe_add]
    exact map_add _ _ _)
  map_smul' r a := Subtype.ext (by
    simp only [SUAlgebraOver.ofMatrix_val, Submodule.coe_smul, RingHom.id_apply]
    ext i j : 1
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.smul_apply]
    exact SpaceTimeAlgebra.C_real_smul r _)

@[simp]
lemma ofConstantLie_val (a : SUAlgebra n) :
    (ofConstantLie a).1 = (C : ℂ →+* SpaceTimeAlgebra).mapMatrix a.1 := rfl

/-- The adjoint action `a ↦ U a U†` of the jets of `SU(n)` on the jets of `su(n)`. -/
noncomputable def adjoint : Representation ℝ (JetSU n) (JetSUAlgebra n) :=
  (SUAlgebraOver.conj (R := SpaceTimeAlgebra)).comp
    (Submonoid.inclusion specialUnitaryGroup_le_unitaryGroup)

@[simp]
lemma adjoint_val (U : JetSU n) (a : JetSUAlgebra n) :
    (adjoint U a).1 = U.1 * a.1 * star U.1 := rfl

/-- The adjoint action `a ↦ U a U†` of `SU(n)` on `su(n)`. -/
noncomputable def adjointValue : Representation ℝ (SU n) (SUAlgebra n) :=
  (SUAlgebraOver.conj (R := ℂ)).comp
    (Submonoid.inclusion specialUnitaryGroup_le_unitaryGroup)

@[simp]
lemma adjointValue_val (U : SU n) (a : SUAlgebra n) :
    (adjointValue U a).1 = U.1 * a.1 * star U.1 := rfl

/-!

## D. The Maurer–Cartan form

-/

/-- The Maurer–Cartan form `i (∂_μ U) U†` of an `SU(n)` gauge jet. -/
noncomputable def mc (U : JetSU n) (μ : Fin 1 ⊕ Fin 3) : JetSUAlgebra n :=
  SUAlgebraOver.ofMatrix (Complex.I • (U.1.map (pderiv μ) * star U.1))
    (SpaceTimeAlgebra.star_mcMatrix μ (JetSU.val_mul_star U) (JetSU.star_mul_val U))
    (JetSU.trace_mcMatrix μ U)

@[simp]
lemma mc_val (U : JetSU n) (μ : Fin 1 ⊕ Fin 3) :
    (mc U μ).1 = Complex.I • (U.1.map (pderiv μ) * star U.1) := rfl

end JetSUAlgebra

/-!

## E. The presentation and the local gauge data

-/

namespace LocalGaugeData

/-- **The presentation of `SU(n)` by matrices of jets**: the carriers are subtypes of
  matrices and every structure map is the matrix one. -/
noncomputable def suMatrixJets (n : ℕ) :
    MatrixJets (Fin n) (SU n) (SUAlgebra n) (JetSU n) (JetSUAlgebra n) where
  toMat₀ := (specialUnitaryGroup (Fin n) ℂ).subtype
  toMat₀_injective _ _ h := Subtype.ext h
  toMatJ := (specialUnitaryGroup (Fin n) SpaceTimeAlgebra).subtype
  toMatJ_injective _ _ h := Subtype.ext h
  toMatJ_mul_star := JetSU.val_mul_star
  star_toMatJ_mul := JetSU.star_mul_val
  lie₀ := (SUAlgebraOver.submodule ℂ n).subtype
  lie₀_injective _ _ h := Subtype.ext h
  lie₀_bracket _ _ := rfl
  lieJ := (SUAlgebraOver.submodule SpaceTimeAlgebra n).subtype
  lieJ_injective _ _ h := Subtype.ext h
  lieJ_bracket _ _ := rfl
  eval := JetSU.eval
  toMat₀_eval _ := rfl
  ofConstant := JetSU.ofConstant
  toMatJ_ofConstant _ := rfl
  evalLie := JetSUAlgebra.evalLie
  lie₀_evalLie _ := rfl
  ofConstantLie := JetSUAlgebra.ofConstantLie
  lieJ_ofConstantLie _ := rfl
  deriv := JetSUAlgebra.deriv
  lieJ_deriv _ _ := rfl
  coord := JetSUAlgebra.coord
  lieJ_coord _ _ := rfl
  adjoint := JetSUAlgebra.adjoint
  lieJ_adjoint _ _ := rfl
  adjointValue := JetSUAlgebra.adjointValue
  lie₀_adjointValue _ _ := rfl
  maurerCartan := JetSUAlgebra.mc
  lieJ_maurerCartan _ _ := rfl

/-- **The local gauge data of `SU(n)`**: special unitary jets, traceless hermitian jets
  with the bracket `i (a b − b a)` and the conjugation action, and the Maurer–Cartan form
  `i (∂_μ U) U⁻¹`. -/
noncomputable def su (n : ℕ) : LocalGaugeData (SU n) (SUAlgebra n) (JetSU n) (JetSUAlgebra n) :=
  (suMatrixJets n).toLocalGaugeData

variable {n : ℕ}

@[simp] lemma su_eval : (su n).eval = JetSU.eval := rfl
@[simp] lemma su_ofConstant : (su n).ofConstant = JetSU.ofConstant := rfl
@[simp] lemma su_evalLie_apply (a : JetSUAlgebra n) : (su n).evalLie a = JetSUAlgebra.evalLie a :=
  rfl
@[simp] lemma su_ofConstantLie : (su n).ofConstantLie = JetSUAlgebra.ofConstantLie := rfl
@[simp] lemma su_deriv (μ : Fin 1 ⊕ Fin 3) : (su n).deriv μ = JetSUAlgebra.deriv μ := rfl
@[simp] lemma su_adjoint : (su n).adjoint = JetSUAlgebra.adjoint := rfl
@[simp] lemma su_maurerCartan : (su n).maurerCartan = JetSUAlgebra.mc := rfl

/-- The canonical `SU(n)` factor of the local gauge data of `SU(n)`. -/
noncomputable def suFactor (n : ℕ) : SUFactor (su n) (Fin n) := (suMatrixJets n).suFactor

/-- The local gauge data of `SU(n)` is faithful. -/
instance instFaithfulSU : (su n).Faithful := (suMatrixJets n).faithful

/-- The local gauge data of `SU(n)` is free. Traceless hermitian Taylor data give a
  traceless hermitian matrix of jets, and the unitary Euler transport of a traceless
  hermitian jet has unit determinant by Jacobi's formula. -/
instance instFreeSU : (su n).Free :=
  (suMatrixJets n).free
    (fun c => ⟨SUAlgebraOver.ofMatrix _ (SpaceTimeAlgebra.star_taylorMatrix fun s => (c s).2.1)
      (SpaceTimeAlgebra.trace_taylorMatrix fun s => (c s).2.2), rfl⟩)
    (fun a => a.2.1)
    (fun ρ V hV0 hVu hEV => ⟨⟨V, mem_specialUnitaryGroup_iff.mpr ⟨mem_unitaryGroup_iff.mpr hVu,
      SpaceTimeAlgebra.eulerTransport_det SpaceTimeAlgebra.jacobi
        (by rw [Matrix.trace_smul, show ((suMatrixJets n).lieJ ρ).trace = 0 from ρ.2.2,
          smul_zero]) hV0 hEV⟩⟩, rfl⟩)

end LocalGaugeData
