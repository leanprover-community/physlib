/-
Copyright (c) 2026 Jinzheng Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jinzheng Li
-/
module

public import Physlib.ClassicalFieldTheory.GaugeTheory.LocalGaugeData.Factor
public import Physlib.ClassicalFieldTheory.GaugeTheory.LocalGaugeData.Truncation
public import Physlib.SpaceAndTime.SpaceTime.SpaceTimeAlgebra.Matrix
public import Physlib.SpaceAndTime.SpaceTime.SpaceTimeAlgebra.Taylor
/-!
# Matrix jet groups

## i. Overview

`U(1)` and `SU(n)` present their local gauge data in the same way: the gauge jets are
unitary matrices of jets, the Lie algebra jets are hermitian matrices of jets, evaluation is
the entrywise constant coefficient, constants embed entrywise, the derivative and the
coordinates act entrywise, the adjoint action is conjugation `U a U†` and the Maurer–Cartan
form is `i (∂_μ U) U†`. Every law of `LocalGaugeData` then follows from matrix identities
over the jet ring.

`MatrixJets` records such a presentation: injective maps of the four carriers into matrices,
and what each structure map is in matrices. From it, `MatrixJets.toLocalGaugeData` proves
the laws once, `MatrixJets.faithful` shows the package is faithful, `MatrixJets.free`
reduces its freeness to three conditions on the carriers, and `MatrixJets.suFactor` is its
canonical `SU`-type factor. The concrete packages `u1` and
`su n` are instances.

## ii. Key results

- `LocalGaugeData.MatrixJets` : a presentation of gauge jets by matrices of jets.
- `LocalGaugeData.MatrixJets.toLocalGaugeData` : the local gauge data it presents.
- `LocalGaugeData.MatrixJets.faithful` : that local gauge data is faithful.
- `LocalGaugeData.MatrixJets.suFactor` : its canonical `SU`-type factor.
- `LocalGaugeData.MatrixJets.free` : a criterion for that local gauge data to be free.

## iii. Table of contents

- A. The presentation
- B. The local gauge data
- C. The iterated derivative and faithfulness
- D. The canonical factor
- E. Freeness

-/

@[expose] public section

open MvPowerSeries

namespace LocalGaugeData

/-!

## A. The presentation

-/

variable {G₀ : Type} [Group G₀] {𝔤 : Type} [LieRing 𝔤] [LieAlgebra ℝ 𝔤]
  {GJ : Type} [Group GJ] {𝔤J : Type} [LieRing 𝔤J] [LieAlgebra ℝ 𝔤J]

/-- **A presentation of gauge jets by matrices**: the value group, its Lie algebra, the jet
  group and its Lie algebra of jets embed into `κ × κ` matrices, and every structure map of
  the local gauge data is what it is for matrices: the entrywise constant coefficient,
  inclusion of constants, derivative and coordinate multiplication, conjugation for the
  adjoint actions and `i (∂_μ U) U†` for the Maurer–Cartan form. -/
structure MatrixJets (κ : Type) [Fintype κ] [DecidableEq κ] (G₀ : Type) [Group G₀]
    (𝔤 : Type) [LieRing 𝔤] [LieAlgebra ℝ 𝔤] (GJ : Type) [Group GJ]
    (𝔤J : Type) [LieRing 𝔤J] [LieAlgebra ℝ 𝔤J] where
  /-- The matrix of a value. -/
  toMat₀ : G₀ →* Matrix κ κ ℂ
  toMat₀_injective : Function.Injective toMat₀
  /-- The matrix of jets of a gauge jet. -/
  toMatJ : GJ →* Matrix κ κ SpaceTimeAlgebra
  toMatJ_injective : Function.Injective toMatJ
  toMatJ_mul_star : ∀ U, toMatJ U * star (toMatJ U) = 1
  star_toMatJ_mul : ∀ U, star (toMatJ U) * toMatJ U = 1
  /-- The matrix of a Lie algebra element. -/
  lie₀ : 𝔤 →ₗ[ℝ] Matrix κ κ ℂ
  lie₀_injective : Function.Injective lie₀
  lie₀_bracket : ∀ a b, lie₀ ⁅a, b⁆ = Complex.I • (lie₀ a * lie₀ b - lie₀ b * lie₀ a)
  /-- The matrix of jets of a Lie algebra jet. -/
  lieJ : 𝔤J →ₗ[ℝ] Matrix κ κ SpaceTimeAlgebra
  lieJ_injective : Function.Injective lieJ
  lieJ_bracket : ∀ a b, lieJ ⁅a, b⁆ = Complex.I • (lieJ a * lieJ b - lieJ b * lieJ a)
  /-- Evaluation of a gauge jet at the base point. -/
  eval : GJ →* G₀
  toMat₀_eval : ∀ U, toMat₀ (eval U) = (constantCoeff : SpaceTimeAlgebra →+* ℂ).mapMatrix (toMatJ U)
  /-- A constant gauge transformation as a jet. -/
  ofConstant : G₀ →* GJ
  toMatJ_ofConstant : ∀ g, toMatJ (ofConstant g) = (C : ℂ →+* SpaceTimeAlgebra).mapMatrix (toMat₀ g)
  /-- Evaluation of a Lie algebra jet at the base point. -/
  evalLie : 𝔤J →ₗ[ℝ] 𝔤
  lie₀_evalLie : ∀ a, lie₀ (evalLie a) = (constantCoeff : SpaceTimeAlgebra →+* ℂ).mapMatrix (lieJ a)
  /-- A constant Lie algebra element as a jet. -/
  ofConstantLie : 𝔤 →ₗ[ℝ] 𝔤J
  lieJ_ofConstantLie : ∀ a, lieJ (ofConstantLie a) = (C : ℂ →+* SpaceTimeAlgebra).mapMatrix (lie₀ a)
  /-- The formal derivative in the direction `μ`. -/
  deriv : (Fin 1 ⊕ Fin 3) → 𝔤J →ₗ[ℝ] 𝔤J
  lieJ_deriv : ∀ μ a, lieJ (deriv μ a) = (lieJ a).map (pderiv μ)
  /-- Multiplication of a jet by the spacetime coordinate `x_μ`. -/
  coord : (Fin 1 ⊕ Fin 3) → 𝔤J →ₗ[ℝ] 𝔤J
  lieJ_coord : ∀ μ a, lieJ (coord μ a) = (X μ : SpaceTimeAlgebra) • lieJ a
  /-- The adjoint action of the jet group on the jet Lie algebra. -/
  adjoint : Representation ℝ GJ 𝔤J
  lieJ_adjoint : ∀ U a, lieJ (adjoint U a) = toMatJ U * lieJ a * star (toMatJ U)
  /-- The adjoint representation of the value group on its Lie algebra. -/
  adjointValue : Representation ℝ G₀ 𝔤
  lie₀_adjointValue : ∀ g a, lie₀ (adjointValue g a) = toMat₀ g * lie₀ a * star (toMat₀ g)
  /-- The Maurer–Cartan form `i (∂_μ U) U⁻¹` of a gauge jet. -/
  maurerCartan : GJ → (Fin 1 ⊕ Fin 3) → 𝔤J
  lieJ_maurerCartan : ∀ U μ, lieJ (maurerCartan U μ)
    = Complex.I • ((toMatJ U).map (pderiv μ) * star (toMatJ U))

namespace MatrixJets

variable {κ : Type} [Fintype κ] [DecidableEq κ] (M : MatrixJets κ G₀ 𝔤 GJ 𝔤J)

/-!

## B. The local gauge data

Every law is an identity of matrices, read through the injective maps `lieJ` and `toMat₀`.

-/

lemma eval_ofConstant (g : G₀) : M.eval (M.ofConstant g) = g := by
  refine M.toMat₀_injective ?_
  rw [M.toMat₀_eval, M.toMatJ_ofConstant]
  ext i j
  simp [RingHom.mapMatrix_apply, Matrix.map_apply, constantCoeff_C]

lemma evalLie_lie (a b : 𝔤J) : M.evalLie ⁅a, b⁆ = ⁅M.evalLie a, M.evalLie b⁆ := by
  refine M.lie₀_injective ?_
  rw [M.lie₀_bracket, M.lie₀_evalLie, M.lie₀_evalLie, M.lie₀_evalLie, M.lieJ_bracket,
    SpaceTimeAlgebra.mapMatrix_constantCoeff_smul, map_sub, map_mul, map_mul]

lemma ofConstantLie_lie (a b : 𝔤) :
    M.ofConstantLie ⁅a, b⁆ = ⁅M.ofConstantLie a, M.ofConstantLie b⁆ := by
  refine M.lieJ_injective ?_
  rw [M.lieJ_bracket, M.lieJ_ofConstantLie, M.lieJ_ofConstantLie, M.lieJ_ofConstantLie,
    M.lie₀_bracket, SpaceTimeAlgebra.mapMatrix_C_smul, map_sub, map_mul, map_mul]

lemma evalLie_ofConstantLie (a : 𝔤) : M.evalLie (M.ofConstantLie a) = a := by
  refine M.lie₀_injective ?_
  rw [M.lie₀_evalLie, M.lieJ_ofConstantLie]
  ext i j
  simp [RingHom.mapMatrix_apply, Matrix.map_apply, constantCoeff_C]

lemma deriv_comm (μ ν : Fin 1 ⊕ Fin 3) (a : 𝔤J) :
    M.deriv μ (M.deriv ν a) = M.deriv ν (M.deriv μ a) := by
  refine M.lieJ_injective ?_
  rw [M.lieJ_deriv, M.lieJ_deriv, M.lieJ_deriv, M.lieJ_deriv]
  ext i j : 1
  simp [Matrix.map_apply, SpaceTimeAlgebra.pderiv_comm μ ν]

lemma deriv_bracket (μ : Fin 1 ⊕ Fin 3) (x y : 𝔤J) :
    M.deriv μ ⁅x, y⁆ = ⁅M.deriv μ x, y⁆ + ⁅x, M.deriv μ y⁆ := by
  refine M.lieJ_injective ?_
  rw [map_add, M.lieJ_deriv, M.lieJ_bracket, M.lieJ_bracket, M.lieJ_bracket, M.lieJ_deriv,
    M.lieJ_deriv, SpaceTimeAlgebra.map_pderiv_smul, SpaceTimeAlgebra.map_pderiv_sub,
        SpaceTimeAlgebra.matrix_map_pderiv_mul,
    SpaceTimeAlgebra.matrix_map_pderiv_mul, ← smul_add]
  congr 1
  abel

lemma deriv_ofConstantLie (μ : Fin 1 ⊕ Fin 3) (a : 𝔤) : M.deriv μ (M.ofConstantLie a) = 0 := by
  refine M.lieJ_injective ?_
  rw [M.lieJ_deriv, M.lieJ_ofConstantLie, map_zero]
  ext i j : 1
  simp [Matrix.map_apply, RingHom.mapMatrix_apply, pderiv_C]

lemma deriv_coord (μ ν : Fin 1 ⊕ Fin 3) (a : 𝔤J) :
    M.deriv μ (M.coord ν a) = M.coord ν (M.deriv μ a) + if μ = ν then a else 0 := by
  refine M.lieJ_injective ?_
  by_cases h : μ = ν
  · subst h
    rw [ite_eq_left rfl, map_add, M.lieJ_deriv, M.lieJ_coord, M.lieJ_coord, M.lieJ_deriv]
    ext i j
    simp only [Matrix.map_apply, Matrix.smul_apply, Matrix.add_apply, smul_eq_mul,
      Derivation.leibniz, pderiv_X_self]
    ring_nf
  · rw [ite_eq_right h, add_zero, M.lieJ_deriv, M.lieJ_coord, M.lieJ_coord, M.lieJ_deriv]
    ext i j
    simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, Derivation.leibniz,
      pderiv_X_of_ne (Ne.symm h), mul_zero, add_zero]

lemma evalLie_coord (μ : Fin 1 ⊕ Fin 3) (a : 𝔤J) : M.evalLie (M.coord μ a) = 0 := by
  refine M.lie₀_injective ?_
  rw [M.lie₀_evalLie, M.lieJ_coord, map_zero]
  ext i j
  simp [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.smul_apply]

lemma coord_lie (μ : Fin 1 ⊕ Fin 3) (a b : 𝔤J) : ⁅M.coord μ a, b⁆ = M.coord μ ⁅a, b⁆ := by
  refine M.lieJ_injective ?_
  rw [M.lieJ_bracket, M.lieJ_coord, M.lieJ_coord, M.lieJ_bracket]
  simp only [Matrix.smul_mul, Matrix.mul_smul, smul_sub, smul_comm
      (X μ : SpaceTimeAlgebra) Complex.I]

/-- Conjugation by a unitary matrix respects products. -/
lemma conj_mul_conj (U : GJ) (A B : Matrix κ κ SpaceTimeAlgebra) :
    (M.toMatJ U * A * star (M.toMatJ U)) * (M.toMatJ U * B * star (M.toMatJ U))
      = M.toMatJ U * (A * B) * star (M.toMatJ U) := by
  simp only [mul_assoc]
  rw [show star (M.toMatJ U) * (M.toMatJ U * (B * star (M.toMatJ U))) = B * star (M.toMatJ U)
    from by rw [← mul_assoc, M.star_toMatJ_mul, one_mul]]

lemma adjoint_lie (U : GJ) (x y : 𝔤J) :
    M.adjoint U ⁅x, y⁆ = ⁅M.adjoint U x, M.adjoint U y⁆ := by
  refine M.lieJ_injective ?_
  rw [M.lieJ_adjoint, M.lieJ_bracket, M.lieJ_bracket, M.lieJ_adjoint, M.lieJ_adjoint,
    M.conj_mul_conj, M.conj_mul_conj]
  simp only [mul_smul_comm, smul_mul_assoc, mul_sub, sub_mul]

lemma evalLie_adjoint (U : GJ) (x : 𝔤J) :
    M.evalLie (M.adjoint U x) = M.adjointValue (M.eval U) (M.evalLie x) := by
  refine M.lie₀_injective ?_
  rw [M.lie₀_evalLie, M.lieJ_adjoint, M.lie₀_adjointValue, M.toMat₀_eval, M.lie₀_evalLie,
    map_mul, map_mul, SpaceTimeAlgebra.mapMatrix_constantCoeff_star]

lemma maurerCartan_ofConstant (g : G₀) (μ : Fin 1 ⊕ Fin 3) :
    M.maurerCartan (M.ofConstant g) μ = 0 := by
  refine M.lieJ_injective ?_
  rw [M.lieJ_maurerCartan, M.toMatJ_ofConstant, map_zero]
  ext i j : 1
  simp [Matrix.mul_apply, Matrix.map_apply, RingHom.mapMatrix_apply, pderiv_C]

lemma maurerCartan_cocycle (U V : GJ) (μ : Fin 1 ⊕ Fin 3) :
    M.maurerCartan (U * V) μ = M.maurerCartan U μ + M.adjoint U (M.maurerCartan V μ) := by
  refine M.lieJ_injective ?_
  rw [map_add, M.lieJ_maurerCartan, M.lieJ_maurerCartan, M.lieJ_adjoint, M.lieJ_maurerCartan,
    map_mul, SpaceTimeAlgebra.matrix_map_pderiv_mul, star_mul, add_mul, smul_add, mul_smul_comm,
    smul_mul_assoc]
  congr 1
  · rw [mul_assoc, ← mul_assoc (M.toMatJ V), M.toMatJ_mul_star, one_mul]
  · simp only [mul_assoc]

lemma maurerCartan_structure (U : GJ) (μ ν : Fin 1 ⊕ Fin 3) :
    M.deriv μ (M.maurerCartan U ν) - M.deriv ν (M.maurerCartan U μ)
      + ⁅M.maurerCartan U μ, M.maurerCartan U ν⁆ = 0 := by
  set A := M.toMatJ U with hA
  have hU : A * star A = 1 := M.toMatJ_mul_star U
  have hU' : star A * A = 1 := M.star_toMatJ_mul U
  have key : (A.map (pderiv ν) * star A).map (pderiv μ) -
        (A.map (pderiv μ) * star A).map (pderiv ν) =
      A.map (pderiv μ) * star A * (A.map (pderiv ν) * star A) -
        A.map (pderiv ν) * star A * (A.map (pderiv μ) * star A) := by
    rw [SpaceTimeAlgebra.matrix_map_pderiv_mul, SpaceTimeAlgebra.matrix_map_pderiv_mul,
      show (A.map (pderiv ν)).map (pderiv μ) = (A.map (pderiv μ)).map (pderiv ν)
        from Matrix.ext fun _ _ => SpaceTimeAlgebra.pderiv_comm μ ν _,
      SpaceTimeAlgebra.map_pderiv_star_of_unitary μ hU hU',
          SpaceTimeAlgebra.map_pderiv_star_of_unitary ν hU hU']
    simp only [mul_neg, ← mul_assoc]
    abel
  have hcancel : ∀ P Q : Matrix κ κ SpaceTimeAlgebra, (P - Q) + (-P - -Q) = 0 :=
    fun P Q => by abel
  refine M.lieJ_injective ?_
  rw [map_add, map_sub, M.lieJ_deriv, M.lieJ_deriv, M.lieJ_bracket, M.lieJ_maurerCartan,
    M.lieJ_maurerCartan, map_zero, SpaceTimeAlgebra.map_pderiv_smul,
        SpaceTimeAlgebra.map_pderiv_smul, ← smul_sub,
    ← hA, key]
  simp only [smul_mul_smul_comm, Complex.I_mul_I, neg_one_smul, ← smul_add, hcancel, smul_zero]

lemma deriv_adjoint (U : GJ) (μ : Fin 1 ⊕ Fin 3) (x : 𝔤J) :
    M.deriv μ (M.adjoint U x) = M.adjoint U (M.deriv μ x)
      - ⁅M.maurerCartan U μ, M.adjoint U x⁆ := by
  set V := M.toMatJ U with hV
  have hVV : star V * V = 1 := M.star_toMatJ_mul U
  have hq : (star V).map (pderiv μ) = -(star V * V.map (pderiv μ) * star V) :=
    SpaceTimeAlgebra.map_pderiv_star_of_unitary μ (M.toMatJ_mul_star U) hVV
  refine M.lieJ_injective ?_
  rw [map_sub, M.lieJ_deriv, M.lieJ_adjoint, M.lieJ_adjoint, M.lieJ_bracket,
    M.lieJ_maurerCartan, M.lieJ_adjoint, M.lieJ_deriv, SpaceTimeAlgebra.matrix_map_pderiv_mul,
    SpaceTimeAlgebra.matrix_map_pderiv_mul, hq]
  simp only [smul_mul_assoc, mul_smul_comm, ← smul_sub, smul_smul, Complex.I_mul_I,
    neg_one_smul, sub_neg_eq_add, add_mul, mul_neg, ← mul_assoc]
  rw [mul_assoc (V.map (pderiv μ)) (star V) V, hVV, mul_one]
  abel

/-- Evaluation of Lie algebra jets, as a morphism of Lie algebras. -/
noncomputable def evalLieHom : 𝔤J →ₗ⁅ℝ⁆ 𝔤 where
  toLinearMap := M.evalLie
  map_lie' := M.evalLie_lie _ _

@[simp]
lemma evalLieHom_apply (a : 𝔤J) : M.evalLieHom a = M.evalLie a := rfl

/-- **The local gauge data presented by matrices of jets.** -/
noncomputable def toLocalGaugeData : LocalGaugeData G₀ 𝔤 GJ 𝔤J where
  eval := M.eval
  ofConstant := M.ofConstant
  eval_ofConstant := M.eval_ofConstant
  evalLie := M.evalLieHom
  ofConstantLie := M.ofConstantLie
  ofConstantLie_lie := M.ofConstantLie_lie
  evalLie_ofConstantLie := M.evalLie_ofConstantLie
  deriv := M.deriv
  deriv_comm := M.deriv_comm
  deriv_bracket := M.deriv_bracket
  deriv_ofConstantLie := M.deriv_ofConstantLie
  coord := M.coord
  deriv_coord := M.deriv_coord
  evalLie_coord := M.evalLie_coord
  coord_lie := M.coord_lie
  adjoint := M.adjoint
  adjoint_lie := M.adjoint_lie
  adjointValue := M.adjointValue
  evalLie_adjoint := M.evalLie_adjoint
  maurerCartan := M.maurerCartan
  maurerCartan_ofConstant := M.maurerCartan_ofConstant
  maurerCartan_cocycle := M.maurerCartan_cocycle
  maurerCartan_structure := M.maurerCartan_structure
  deriv_adjoint := M.deriv_adjoint

@[simp] lemma toLocalGaugeData_eval : M.toLocalGaugeData.eval = M.eval := rfl
@[simp] lemma toLocalGaugeData_ofConstant : M.toLocalGaugeData.ofConstant = M.ofConstant := rfl
@[simp] lemma toLocalGaugeData_evalLie_apply (a : 𝔤J) :
    M.toLocalGaugeData.evalLie a = M.evalLie a := rfl
@[simp] lemma toLocalGaugeData_ofConstantLie :
    M.toLocalGaugeData.ofConstantLie = M.ofConstantLie := rfl
@[simp] lemma toLocalGaugeData_deriv (μ : Fin 1 ⊕ Fin 3) :
    M.toLocalGaugeData.deriv μ = M.deriv μ := rfl
@[simp] lemma toLocalGaugeData_coord (μ : Fin 1 ⊕ Fin 3) :
    M.toLocalGaugeData.coord μ = M.coord μ := rfl
@[simp] lemma toLocalGaugeData_adjoint : M.toLocalGaugeData.adjoint = M.adjoint := rfl
@[simp] lemma toLocalGaugeData_adjointValue :
    M.toLocalGaugeData.adjointValue = M.adjointValue := rfl
@[simp] lemma toLocalGaugeData_maurerCartan :
    M.toLocalGaugeData.maurerCartan = M.maurerCartan := rfl

/-!

## C. The iterated derivative and faithfulness

-/

/-- The iterated derivative is the entrywise iterated formal derivative. -/
lemma lieJ_iteratedDeriv (s : Multiset (Fin 1 ⊕ Fin 3)) (a : 𝔤J) :
    M.lieJ (M.toLocalGaugeData.iteratedDeriv s a)
      = (M.lieJ a).map fun f => SpaceTimeAlgebra.iteratedPDeriv s f := by
  induction s using Multiset.induction_on generalizing a with
  | empty =>
    rw [iteratedDeriv_zero, LinearMap.id_apply]
    ext i j : 1
    simp [Matrix.map_apply]
  | cons μ t ih =>
    rw [iteratedDeriv_cons, LinearMap.comp_apply, toLocalGaugeData_deriv, M.lieJ_deriv, ih,
      Matrix.map_map]
    ext i j : 1
    simp only [Matrix.map_apply, Function.comp_apply, SpaceTimeAlgebra.iteratedPDeriv_cons]
    exact (SpaceTimeAlgebra.iteratedPDeriv_pderiv t μ _).symm

/-- The base-point value of the iterated derivative, entrywise. -/
lemma lie₀_evalLie_iteratedDeriv (s : Multiset (Fin 1 ⊕ Fin 3)) (a : 𝔤J) :
    M.lie₀ (M.toLocalGaugeData.evalLie (M.toLocalGaugeData.iteratedDeriv s a))
      = (M.lieJ a).map fun f => constantCoeff (SpaceTimeAlgebra.iteratedPDeriv s f) := by
  rw [toLocalGaugeData_evalLie_apply, M.lie₀_evalLie, M.lieJ_iteratedDeriv,
    RingHom.mapMatrix_apply, Matrix.map_map]
  rfl

/-- **A package presented by matrices is faithful**: a jet is determined entrywise by the
  constant coefficients of its derivatives, and a jet with vanishing Maurer–Cartan form has
  constant entries. -/
lemma faithful : M.toLocalGaugeData.Faithful where
  ext_of_evalLie_iteratedDeriv {x y} h := by
    refine M.lieJ_injective (Matrix.ext fun i j => ?_)
    refine SpaceTimeAlgebra.ext_of_constantCoeff_iteratedPDeriv fun s => ?_
    have hs := congrArg M.lie₀ (h s)
    rw [M.lie₀_evalLie_iteratedDeriv, M.lie₀_evalLie_iteratedDeriv] at hs
    simpa only [Matrix.map_apply] using congrArg (fun A => A i j) hs
  eq_ofConstant_of_maurerCartan_eq_zero {U} h := by
    have hU : M.toMatJ U * star (M.toMatJ U) = 1 := M.toMatJ_mul_star U
    have hd : ∀ μ, (M.toMatJ U).map (pderiv μ) = 0 := fun μ => by
      have h1 : Complex.I • ((M.toMatJ U).map (pderiv μ) * star (M.toMatJ U)) = 0 := by
        rw [← M.lieJ_maurerCartan, show M.maurerCartan U μ = 0 from congrFun h μ, map_zero]
      have h2 : (M.toMatJ U).map (pderiv μ) * star (M.toMatJ U) = 0 := by
        have := congrArg (fun A => (-Complex.I) • A) h1
        simpa [smul_smul, Complex.I_mul_I] using this
      calc (M.toMatJ U).map (pderiv μ)
          = (M.toMatJ U).map (pderiv μ) * (star (M.toMatJ U) * M.toMatJ U) := by
            rw [M.star_toMatJ_mul, mul_one]
        _ = 0 := by rw [← mul_assoc, h2, zero_mul]
    refine M.toMatJ_injective (Matrix.ext fun i j => ?_)
    rw [toLocalGaugeData_ofConstant, toLocalGaugeData_eval, M.toMatJ_ofConstant, M.toMat₀_eval,
      RingHom.mapMatrix_apply, RingHom.mapMatrix_apply, Matrix.map_map]
    show M.toMatJ U i j = C (constantCoeff (M.toMatJ U i j))
    exact SpaceTimeAlgebra.eq_C_of_pderiv_eq_zero fun μ => congrArg (fun A => A i j) (hd μ)

/-!

## D. The canonical factor

-/

/-- **The canonical `SU`-type factor** of a package presented by matrices: the matrices of
  jets themselves. -/
noncomputable def suFactor : SUFactor M.toLocalGaugeData κ where
  u := M.toMatJ
  u_unitary := M.star_toMatJ_mul
  φ := M.lie₀
  φJ := M.lieJ
  φJ_ofConstantLie a := M.lieJ_ofConstantLie a
  φJ_cc_foldl p a := (M.lie₀_evalLie_iteratedDeriv p a).symm
  φJ_maurerCartan U μ := M.lieJ_maurerCartan U μ
  φJ_adjoint U c := M.lieJ_adjoint U (M.ofConstantLie c)

/-!

## E. Freeness

A presentation by matrices is free when its carriers are large enough: the Lie algebra
jets contain every matrix of jets with Taylor data in the Lie algebra, and the gauge jets
contain the unitary fundamental solution `V` of the radial system `E V = −i P V` for every
Lie algebra jet `P`. Taylor completeness and radial integrability then hold because they
hold for matrices of jets.

-/

/-- The radial component of the Maurer–Cartan form, in matrices:
  `∑_μ x_μ · i (∂_μ U) U†`. -/
lemma lieJ_radial (U : GJ) :
    M.lieJ (M.toLocalGaugeData.radial U) =
      ∑ μ, (X μ : SpaceTimeAlgebra) •
          (Complex.I • ((M.toMatJ U).map (pderiv μ) * star (M.toMatJ U))) := by
  simp only [radial, map_sum, toLocalGaugeData_coord, toLocalGaugeData_maurerCartan,
    M.lieJ_coord, M.lieJ_maurerCartan]

/-- A gauge jet is pure exactly when its matrix is the identity at the base point. -/
lemma mem_truncationKer_zero_iff (U : GJ) :
    U ∈ M.toLocalGaugeData.truncationKer 0 ↔
      (constantCoeff : SpaceTimeAlgebra →+* ℂ).mapMatrix (M.toMatJ U) = 1 := by
  rw [LocalGaugeData.mem_truncationKer_zero_iff, toLocalGaugeData_eval, ← M.toMat₀_eval,
    ← map_one M.toMat₀]
  exact M.toMat₀_injective.eq_iff.symm

/-- **A criterion for freeness.** A presentation by matrices is free when every matrix of
  jets built entrywise from Taylor data in `𝔤` is a Lie algebra jet, the Lie algebra jets
  are hermitian, and every unitary solution `V` of `E V = −i P V`, `V(0) = 1`, for a Lie
  algebra jet `P`, is a gauge jet. -/
lemma free
    (hTaylor : ∀ c : Multiset (Fin 1 ⊕ Fin 3) → 𝔤,
      ∃ Y, M.lieJ Y = SpaceTimeAlgebra.taylorMatrix fun s => M.lie₀ (c s))
    (hherm : ∀ a, star (M.lieJ a) = M.lieJ a)
    (hlift : ∀ (ρ : 𝔤J) (V : Matrix κ κ SpaceTimeAlgebra),
      (constantCoeff : SpaceTimeAlgebra →+* ℂ).mapMatrix V = 1 → V * star V = 1 →
      ∑ μ, (X μ : SpaceTimeAlgebra) • V.map (pderiv μ) = ((-Complex.I) • M.lieJ ρ) * V →
      ∃ U, M.toMatJ U = V) :
    M.toLocalGaugeData.Free where
  toFaithful := M.faithful
  exists_evalLie_iteratedDeriv_eq c := by
    obtain ⟨Y, hY⟩ := hTaylor c
    refine ⟨Y, fun s => M.lie₀_injective ?_⟩
    rw [M.lie₀_evalLie_iteratedDeriv, hY,
        SpaceTimeAlgebra.map_constantCoeff_iteratedPDeriv_taylorMatrix]
  exists_radial_eq ρ hρ := by
    -- The matrix `R = −i P` of `P = lieJ ρ` is anti-hermitian and vanishes at the base point.
    have hR0 : ∀ i j, constantCoeff (((-Complex.I) • M.lieJ ρ) i j) = 0 := fun i j => by
      have h := congrArg (fun A => A i j) (congrArg M.lie₀ hρ)
      simp only [toLocalGaugeData_evalLie_apply, M.lie₀_evalLie, map_zero] at h
      rw [Matrix.smul_apply, ← coeff_zero_eq_constantCoeff, map_smul,
        coeff_zero_eq_constantCoeff]
      simpa using congrArg ((-Complex.I) • ·) h
    have hRstar : star ((-Complex.I) • M.lieJ ρ) = -((-Complex.I) • M.lieJ ρ) := by
      rw [star_smul, hherm]
      simp
    -- Its Euler transport is unitary, hence a pure gauge jet with radial component `P`.
    obtain ⟨V, hV0, hEV⟩ := SpaceTimeAlgebra.exists_matrix_eulerTransport _ hR0
    have hVu := SpaceTimeAlgebra.eulerTransport_mul_star hRstar hR0 hV0 hEV
    obtain ⟨U, rfl⟩ := hlift ρ V hV0 hVu hEV
    refine ⟨⟨U, (M.mem_truncationKer_zero_iff U).2 hV0⟩, M.lieJ_injective ?_⟩
    rw [M.lieJ_radial]
    exact SpaceTimeAlgebra.sum_X_smul_mcMatrix_of_eulerTransport hVu hEV

end MatrixJets

end LocalGaugeData
