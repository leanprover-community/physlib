/-
Copyright (c) 2026 Jinzheng Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jinzheng Li
-/
module

public import Physlib.ClassicalFieldTheory.GaugeTheory.LocalGaugeData.SU.Algebra
public import Physlib.ClassicalFieldTheory.GaugeTheory.MatterField.MatrixRep.Factors
public import Physlib.Relativity.JetRing.Jacobi
public import Physlib.Relativity.JetRing.Taylor
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

The package comes with its canonical `SUFactor` and is faithful.

## ii. Key results

- `SU`, `JetSU`, `SUAlgebra`, `JetSUAlgebra` : the carriers.
- `JetSUAlgebra.mc` : the Maurer–Cartan form, with `mc_cocycle`, `mc_structure` and
  `deriv_adjoint`.
- `LocalGaugeData.su` : the local gauge data of `SU(n)`.
- `LocalGaugeData.suFactor` : its canonical `SU(n)` factor.
- `LocalGaugeData.instFaithfulSU` : the package is faithful.

## iii. Table of contents

- A. The carriers
- B. The structure maps on the group
- C. The structure maps on the Lie algebra
- D. The Maurer–Cartan form and the identities
- E. The local gauge data
- F. The canonical factor and faithfulness

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
abbrev JetSU (n : ℕ) : Type := specialUnitaryGroup (Fin n) JetRing

/-- The Lie algebra `su(n)`: traceless hermitian matrices. -/
abbrev SUAlgebra (n : ℕ) : Type := SUAlgebraOver ℂ n

/-- Jets of the Lie algebra `su(n)`: traceless hermitian matrices of formal power series. -/
abbrev JetSUAlgebra (n : ℕ) : Type := SUAlgebraOver JetRing n

instance (n : ℕ) : Module.Finite ℝ (SUAlgebra n) := by infer_instance

/-- The inclusion of the special unitary group into the unitary group. -/
def specialUnitaryToUnitary (R : Type) [CommRing R] [StarRing R] (n : ℕ) :
    specialUnitaryGroup (Fin n) R →* unitaryGroup (Fin n) R where
  toFun U := ⟨U.1, (mem_specialUnitaryGroup_iff.mp U.2).1⟩
  map_one' := rfl
  map_mul' _ _ := rfl

@[simp]
lemma specialUnitaryToUnitary_val {R : Type} [CommRing R] [StarRing R] {n : ℕ}
    (U : specialUnitaryGroup (Fin n) R) : (specialUnitaryToUnitary R n U).1 = U.1 := rfl

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

/-- Entrywise inclusion of constants commutes with the conjugate transpose. -/
lemma mapMatrix_C_star {κ : Type} [Fintype κ] [DecidableEq κ] (A : Matrix κ κ ℂ) :
    (C : ℂ →+* JetRing).mapMatrix (star A) = star ((C : ℂ →+* JetRing).mapMatrix A) := by
  ext i j
  simp [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.star_apply]

/-- Evaluation of a jet of an `SU(n)` gauge transformation at the base point: the entrywise
  constant coefficient. -/
noncomputable def eval : JetSU n →* SU n where
  toFun U := ⟨(constantCoeff : JetRing →+* ℂ).mapMatrix U.1, by
    obtain ⟨h1, h2⟩ := mem_specialUnitaryGroup_iff.mp U.2
    rw [mem_specialUnitaryGroup_iff]
    constructor
    · rw [mem_unitaryGroup_iff] at h1 ⊢
      rw [show star ((constantCoeff : JetRing →+* ℂ).mapMatrix U.1) =
          (constantCoeff : JetRing →+* ℂ).mapMatrix (star U.1) from
          (JetRing.mapMatrix_constantCoeff_star U.1).symm, ← map_mul, h1, map_one]
    · rw [← RingHom.map_det, h2, map_one]⟩
  map_one' := Subtype.ext (map_one ((constantCoeff : JetRing →+* ℂ).mapMatrix))
  map_mul' U V := Subtype.ext (map_mul ((constantCoeff : JetRing →+* ℂ).mapMatrix) U.1 V.1)

@[simp]
lemma eval_val (U : JetSU n) : (eval U).1 = (constantCoeff : JetRing →+* ℂ).mapMatrix U.1 := rfl

/-- The jet of a constant `SU(n)` gauge transformation: the entrywise inclusion of
  constants. -/
noncomputable def ofConstant : SU n →* JetSU n where
  toFun u := ⟨(C : ℂ →+* JetRing).mapMatrix u.1, by
    obtain ⟨h1, h2⟩ := mem_specialUnitaryGroup_iff.mp u.2
    rw [mem_specialUnitaryGroup_iff]
    constructor
    · rw [mem_unitaryGroup_iff] at h1 ⊢
      rw [show star ((C : ℂ →+* JetRing).mapMatrix u.1) =
          (C : ℂ →+* JetRing).mapMatrix (star u.1) from (mapMatrix_C_star u.1).symm,
        ← map_mul, h1, map_one]
    · rw [← RingHom.map_det, h2, map_one]⟩
  map_one' := Subtype.ext (map_one ((C : ℂ →+* JetRing).mapMatrix))
  map_mul' u v := Subtype.ext (map_mul ((C : ℂ →+* JetRing).mapMatrix) u.1 v.1)

@[simp]
lemma ofConstant_val (u : SU n) : (ofConstant u).1 = (C : ℂ →+* JetRing).mapMatrix u.1 := rfl

@[simp]
lemma eval_ofConstant (g : SU n) : eval (ofConstant g) = g := by
  refine Subtype.ext ?_
  ext i j
  simp [RingHom.mapMatrix_apply, Matrix.map_apply]

/-- The entrywise derivative commutes with the conjugate transpose. -/
lemma star_map_pderiv {κ : Type} [Fintype κ] (μ : Fin 1 ⊕ Fin 3) (A : Matrix κ κ JetRing) :
    star (A.map (pderiv μ)) = (star A).map (pderiv μ) := by
  ext i j : 1
  simp only [Matrix.star_apply, Matrix.map_apply]
  exact (JetRing.pderiv_star μ (A j i)).symm

/-- The entrywise derivative of the conjugate transpose of a unitary matrix, through the
  differentiated unitarity relation. -/
lemma map_pderiv_star_val (μ : Fin 1 ⊕ Fin 3) (U : JetSU n) :
    (star U.1).map (pderiv μ) = -(star U.1 * U.1.map (pderiv μ) * star U.1) := by
  have h1 : U.1 * (star U.1).map (pderiv μ) = -(U.1.map (pderiv μ) * star U.1) :=
    eq_neg_of_add_eq_zero_right (by
      rw [← JetRing.matrix_map_pderiv_mul, val_mul_star]
      exact Matrix.ext fun i j => by
        simp [Matrix.map_apply, Matrix.one_apply, apply_ite (pderiv μ)])
  calc (star U.1).map (pderiv μ)
      = star U.1 * U.1 * (star U.1).map (pderiv μ) := by rw [star_mul_val, one_mul]
    _ = -(star U.1 * U.1.map (pderiv μ) * star U.1) := by
        rw [mul_assoc, h1, mul_neg, ← mul_assoc]

/-- The Maurer–Cartan matrix `i (∂_μ U) U†` is hermitian. -/
lemma star_mcMatrix (μ : Fin 1 ⊕ Fin 3) (U : JetSU n) :
    star (Complex.I • (U.1.map (pderiv μ) * star U.1))
      = Complex.I • (U.1.map (pderiv μ) * star U.1) := by
  rw [star_smul, star_mul, star_star, star_map_pderiv, map_pderiv_star_val, Complex.star_def,
    Complex.conj_I, neg_smul, mul_neg, smul_neg, neg_neg, ← mul_assoc, ← mul_assoc,
    val_mul_star, one_mul]

/-- The Maurer–Cartan matrix `i (∂_μ U) U†` is traceless, by Jacobi's formula and
  `det U = 1`. -/
lemma trace_mcMatrix (μ : Fin 1 ⊕ Fin 3) (U : JetSU n) :
    (Complex.I • (U.1.map (pderiv μ) * star U.1)).trace = 0 := by
  rw [Matrix.trace_smul, star_val_eq_adjugate, ← JetRing.jacobi, det_val, pderiv_one,
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
    (by rw [JetSU.star_map_pderiv, a.star_val])
    (by rw [← AddMonoidHom.map_trace, a.trace_val, map_zero])
  map_add' a b := Subtype.ext (by
    ext i j : 1
    simp [Matrix.map_apply])
  map_smul' r a := Subtype.ext (by
    ext i j : 1
    simp only [SUAlgebraOver.ofMatrix_val, Submodule.coe_smul, Matrix.map_apply,
      Matrix.smul_apply, RingHom.id_apply]
    rw [← algebraMap_smul ℂ r, Derivation.map_smul, algebraMap_smul])

@[simp]
lemma deriv_val (μ : Fin 1 ⊕ Fin 3) (a : JetSUAlgebra n) :
    (deriv μ a).1 = a.1.map (pderiv μ) := rfl

/-- Multiplication by the coordinate `x_μ`, entrywise. -/
noncomputable def coord (μ : Fin 1 ⊕ Fin 3) : JetSUAlgebra n →ₗ[ℝ] JetSUAlgebra n where
  toFun a := SUAlgebraOver.ofMatrix ((X μ : JetRing) • a.1)
    (by rw [star_smul, JetRing.star_X, a.star_val])
    (by rw [Matrix.trace_smul, a.trace_val, smul_zero])
  map_add' a b := Subtype.ext (by simp [smul_add])
  map_smul' r a := Subtype.ext (by simp [smul_comm r])

@[simp]
lemma coord_val (μ : Fin 1 ⊕ Fin 3) (a : JetSUAlgebra n) :
    (coord μ a).1 = (X μ : JetRing) • a.1 := rfl

lemma mapMatrix_constantCoeff_smul {κ : Type} [Fintype κ] [DecidableEq κ] (c : ℂ)
    (M : Matrix κ κ JetRing) :
    (constantCoeff : JetRing →+* ℂ).mapMatrix (c • M)
      = c • (constantCoeff : JetRing →+* ℂ).mapMatrix M := by
  ext i j
  simp [RingHom.mapMatrix_apply, Matrix.map_apply]

lemma star_mapMatrix_constantCoeff (a : JetSUAlgebra n) :
    star ((constantCoeff : JetRing →+* ℂ).mapMatrix a.1)
      = (constantCoeff : JetRing →+* ℂ).mapMatrix a.1 := by
  rw [← JetRing.mapMatrix_constantCoeff_star, a.star_val]

lemma trace_mapMatrix_constantCoeff (a : JetSUAlgebra n) :
    ((constantCoeff : JetRing →+* ℂ).mapMatrix a.1).trace = 0 := by
  rw [RingHom.mapMatrix_apply, ← AddMonoidHom.map_trace, a.trace_val, map_zero]

/-- Evaluation at the base point: the entrywise constant coefficient, a morphism of Lie
  algebras. -/
noncomputable def evalLie : JetSUAlgebra n →ₗ⁅ℝ⁆ SUAlgebra n where
  toFun a := SUAlgebraOver.ofMatrix ((constantCoeff : JetRing →+* ℂ).mapMatrix a.1)
    (star_mapMatrix_constantCoeff a) (trace_mapMatrix_constantCoeff a)
  map_add' a b := Subtype.ext (by
    simp only [SUAlgebraOver.ofMatrix_val, Submodule.coe_add]
    exact map_add _ _ _)
  map_smul' r a := Subtype.ext (by
    simp only [SUAlgebraOver.ofMatrix_val, Submodule.coe_smul, RingHom.id_apply]
    ext i j
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.smul_apply]
    rw [← algebraMap_smul ℂ r, constantCoeff_smul, algebraMap_smul])
  map_lie' := by
    intro a b
    refine Subtype.ext ?_
    simp only [SUAlgebraOver.ofMatrix_val, SUAlgebraOver.bracket_val]
    rw [mapMatrix_constantCoeff_smul, map_sub, map_mul, map_mul]

@[simp]
lemma evalLie_val (a : JetSUAlgebra n) :
    (evalLie a).1 = (constantCoeff : JetRing →+* ℂ).mapMatrix a.1 := rfl

lemma C_smul (r : ℝ) (x : ℂ) : (C (r • x) : JetRing) = r • C x := by
  rw [Algebra.smul_def, Algebra.smul_def, map_mul, MvPowerSeries.algebraMap_apply]

lemma star_mapMatrix_C (a : SUAlgebra n) :
    star ((C : ℂ →+* JetRing).mapMatrix a.1) = (C : ℂ →+* JetRing).mapMatrix a.1 := by
  rw [← JetSU.mapMatrix_C_star, a.star_val]

lemma trace_mapMatrix_C (a : SUAlgebra n) : ((C : ℂ →+* JetRing).mapMatrix a.1).trace = 0 := by
  rw [RingHom.mapMatrix_apply, ← AddMonoidHom.map_trace, a.trace_val, map_zero]

/-- A constant as a jet: the entrywise constant power series. -/
noncomputable def ofConstantLie : SUAlgebra n →ₗ[ℝ] JetSUAlgebra n where
  toFun a := SUAlgebraOver.ofMatrix ((C : ℂ →+* JetRing).mapMatrix a.1)
    (star_mapMatrix_C a) (trace_mapMatrix_C a)
  map_add' a b := Subtype.ext (by
    simp only [SUAlgebraOver.ofMatrix_val, Submodule.coe_add]
    exact map_add _ _ _)
  map_smul' r a := Subtype.ext (by
    simp only [SUAlgebraOver.ofMatrix_val, Submodule.coe_smul, RingHom.id_apply]
    ext i j : 1
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.smul_apply]
    exact C_smul r _)

@[simp]
lemma ofConstantLie_val (a : SUAlgebra n) :
    (ofConstantLie a).1 = (C : ℂ →+* JetRing).mapMatrix a.1 := rfl

lemma mapMatrix_C_smul {κ : Type} [Fintype κ] [DecidableEq κ] (c : ℂ) (M : Matrix κ κ ℂ) :
    (C : ℂ →+* JetRing).mapMatrix (c • M) = c • (C : ℂ →+* JetRing).mapMatrix M := by
  ext i j : 1
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.smul_apply,
    MvPowerSeries.smul_eq_C_mul, smul_eq_mul, map_mul]

/-- The constant inclusion is a morphism of Lie algebras. -/
lemma ofConstantLie_lie (a b : SUAlgebra n) :
    ofConstantLie ⁅a, b⁆ = ⁅ofConstantLie a, ofConstantLie b⁆ := by
  refine Subtype.ext ?_
  simp only [ofConstantLie_val, SUAlgebraOver.bracket_val]
  rw [mapMatrix_C_smul, map_sub, map_mul, map_mul]

@[simp]
lemma evalLie_ofConstantLie (a : SUAlgebra n) : evalLie (ofConstantLie a) = a := by
  refine Subtype.ext ?_
  ext i j
  simp [RingHom.mapMatrix_apply, Matrix.map_apply, constantCoeff_C]

/-- The adjoint action `a ↦ U a U†` of the jets of `SU(n)` on the jets of `su(n)`. -/
noncomputable def adjoint : Representation ℝ (JetSU n) (JetSUAlgebra n) :=
  (SUAlgebraOver.conj (R := JetRing)).comp (specialUnitaryToUnitary JetRing n)

@[simp]
lemma adjoint_val (U : JetSU n) (a : JetSUAlgebra n) :
    (adjoint U a).1 = U.1 * a.1 * star U.1 := rfl

/-- The adjoint action `a ↦ U a U†` of `SU(n)` on `su(n)`. -/
noncomputable def adjointValue : Representation ℝ (SU n) (SUAlgebra n) :=
  (SUAlgebraOver.conj (R := ℂ)).comp (specialUnitaryToUnitary ℂ n)

@[simp]
lemma adjointValue_val (U : SU n) (a : SUAlgebra n) :
    (adjointValue U a).1 = U.1 * a.1 * star U.1 := rfl

/-!

## D. The Maurer–Cartan form and the identities

-/

/-- The Maurer–Cartan form `i (∂_μ U) U†` of an `SU(n)` gauge jet. -/
noncomputable def mc (U : JetSU n) (μ : Fin 1 ⊕ Fin 3) : JetSUAlgebra n :=
  SUAlgebraOver.ofMatrix (Complex.I • (U.1.map (pderiv μ) * star U.1))
    (JetSU.star_mcMatrix μ U) (JetSU.trace_mcMatrix μ U)

@[simp]
lemma mc_val (U : JetSU n) (μ : Fin 1 ⊕ Fin 3) :
    (mc U μ).1 = Complex.I • (U.1.map (pderiv μ) * star U.1) := rfl

lemma deriv_comm (μ ν : Fin 1 ⊕ Fin 3) (a : JetSUAlgebra n) :
    deriv μ (deriv ν a) = deriv ν (deriv μ a) := by
  refine Subtype.ext ?_
  ext i j : 1
  simp [Matrix.map_apply, JetRing.pderiv_comm μ ν]

/-- Pulling a complex scalar out of the entrywise derivative. -/
lemma map_pderiv_smul {κ : Type} (μ : Fin 1 ⊕ Fin 3) (c : ℂ) (M : Matrix κ κ JetRing) :
    (c • M).map (pderiv μ) = c • M.map (pderiv μ) :=
  Matrix.ext fun _ _ => Derivation.map_smul _ _ _

lemma map_pderiv_sub {κ : Type} (μ : Fin 1 ⊕ Fin 3) (M N : Matrix κ κ JetRing) :
    (M - N).map (pderiv μ) = M.map (pderiv μ) - N.map (pderiv μ) := by
  ext i j : 1
  simp only [Matrix.map_apply, Matrix.sub_apply, map_sub]

/-- The derivative is a derivation of the bracket. -/
lemma deriv_bracket (μ : Fin 1 ⊕ Fin 3) (x y : JetSUAlgebra n) :
    deriv μ ⁅x, y⁆ = ⁅deriv μ x, y⁆ + ⁅x, deriv μ y⁆ := by
  refine Subtype.ext ?_
  simp only [deriv_val, SUAlgebraOver.bracket_val, Submodule.coe_add, map_pderiv_smul,
    map_pderiv_sub, JetRing.matrix_map_pderiv_mul]
  rw [← smul_add]
  congr 1
  abel

@[simp]
lemma deriv_ofConstantLie (μ : Fin 1 ⊕ Fin 3) (a : SUAlgebra n) :
    deriv μ (ofConstantLie a) = 0 := by
  refine Subtype.ext ?_
  ext i j : 1
  simp [Matrix.map_apply, RingHom.mapMatrix_apply, pderiv_C]

/-- The Leibniz rule for a coordinate: `∂_μ (x_ν a) = x_ν ∂_μ a + δ_{μν} a`. -/
lemma deriv_coord (μ ν : Fin 1 ⊕ Fin 3) (a : JetSUAlgebra n) :
    deriv μ (coord ν a) = coord ν (deriv μ a) + if μ = ν then a else 0 := by
  by_cases h : μ = ν
  · subst h
    rw [ite_eq_left rfl]
    refine Subtype.ext ?_
    ext i j
    simp only [deriv_val, coord_val, Submodule.coe_add, Matrix.map_apply, Matrix.smul_apply,
      Matrix.add_apply, smul_eq_mul, Derivation.leibniz, pderiv_X_self]
    ring
  · rw [ite_eq_right h, add_zero]
    refine Subtype.ext ?_
    ext i j
    simp only [deriv_val, coord_val, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul,
      Derivation.leibniz, pderiv_X_of_ne (Ne.symm h), mul_zero, add_zero]

/-- A coordinate vanishes at the base point. -/
lemma evalLie_coord (μ : Fin 1 ⊕ Fin 3) (a : JetSUAlgebra n) : evalLie (coord μ a) = 0 := by
  refine Subtype.ext ?_
  ext i j
  simp [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.smul_apply]

/-- The coordinates are central for the bracket. -/
lemma coord_lie (μ : Fin 1 ⊕ Fin 3) (a b : JetSUAlgebra n) :
    ⁅coord μ a, b⁆ = coord μ ⁅a, b⁆ := by
  refine Subtype.ext ?_
  simp only [SUAlgebraOver.bracket_val, coord_val, Matrix.smul_mul, Matrix.mul_smul, smul_sub,
    smul_comm (X μ : JetRing) Complex.I]

lemma adjoint_lie (U : JetSU n) (x y : JetSUAlgebra n) :
    adjoint U ⁅x, y⁆ = ⁅adjoint U x, adjoint U y⁆ :=
  SUAlgebraOver.conj_lie _ x y

/-- At the base point the adjoint action of a jet is the adjoint action of its value. -/
lemma evalLie_adjoint (U : JetSU n) (x : JetSUAlgebra n) :
    evalLie (adjoint U x) = adjointValue (JetSU.eval U) (evalLie x) := by
  refine Subtype.ext ?_
  simp only [evalLie_val, adjoint_val, adjointValue_val, JetSU.eval_val, map_mul,
    JetRing.mapMatrix_constantCoeff_star]

@[simp]
lemma mc_ofConstant (g : SU n) (μ : Fin 1 ⊕ Fin 3) : mc (JetSU.ofConstant g) μ = 0 := by
  refine Subtype.ext ?_
  ext i j : 1
  simp [Matrix.mul_apply, Matrix.map_apply, RingHom.mapMatrix_apply, pderiv_C]

/-- The Maurer–Cartan form is a cocycle for the adjoint action. -/
lemma mc_cocycle (U V : JetSU n) (μ : Fin 1 ⊕ Fin 3) :
    mc (U * V) μ = mc U μ + adjoint U (mc V μ) := by
  refine Subtype.ext ?_
  simp only [mc_val, Submodule.coe_add, adjoint_val, Submonoid.coe_mul]
  rw [JetRing.matrix_map_pderiv_mul, star_mul, add_mul, smul_add, mul_smul_comm,
    smul_mul_assoc]
  congr 1
  · rw [mul_assoc, ← mul_assoc V.1, JetSU.val_mul_star, one_mul]
  · simp only [mul_assoc]

/-- The Maurer–Cartan form is flat: `∂_μ ω_ν − ∂_ν ω_μ + ⁅ω_μ, ω_ν⁆ = 0`. -/
lemma mc_structure (U : JetSU n) (μ ν : Fin 1 ⊕ Fin 3) :
    deriv μ (mc U ν) - deriv ν (mc U μ) + ⁅mc U μ, mc U ν⁆ = 0 := by
  set A := U.1 with hA
  have key : (A.map (pderiv ν) * star A).map (pderiv μ) -
        (A.map (pderiv μ) * star A).map (pderiv ν) =
      A.map (pderiv μ) * star A * (A.map (pderiv ν) * star A) -
        A.map (pderiv ν) * star A * (A.map (pderiv μ) * star A) := by
    rw [JetRing.matrix_map_pderiv_mul, JetRing.matrix_map_pderiv_mul,
      show (A.map (pderiv ν)).map (pderiv μ) = (A.map (pderiv μ)).map (pderiv ν)
        from Matrix.ext fun _ _ => JetRing.pderiv_comm μ ν _,
      JetSU.map_pderiv_star_val μ, JetSU.map_pderiv_star_val ν]
    simp only [mul_neg, ← mul_assoc]
    abel
  have hcancel : ∀ P Q : Matrix (Fin n) (Fin n) JetRing, (P - Q) + (-P - -Q) = 0 :=
    fun P Q => by abel
  refine Subtype.ext ?_
  simp only [Submodule.coe_add, Submodule.coe_sub, deriv_val, SUAlgebraOver.bracket_val, mc_val,
    map_pderiv_smul, smul_mul_smul_comm, Submodule.coe_zero]
  rw [← smul_sub, key, Complex.I_mul_I, neg_one_smul, neg_one_smul, ← smul_add, hcancel,
    smul_zero]

/-- The derivative of the adjoint action: `∂_μ (Ad_U x) = Ad_U (∂_μ x) − ⁅ω_μ(U), Ad_U x⁆`. -/
lemma deriv_adjoint (U : JetSU n) (μ : Fin 1 ⊕ Fin 3) (x : JetSUAlgebra n) :
    deriv μ (adjoint U x) = adjoint U (deriv μ x) - ⁅mc U μ, adjoint U x⁆ := by
  set V := U.1 with hV
  have hVV : star V * V = 1 := JetSU.star_mul_val U
  have hq : (star V).map (pderiv μ) = -(star V * V.map (pderiv μ) * star V) :=
    JetSU.map_pderiv_star_val μ U
  refine Subtype.ext ?_
  simp only [deriv_val, adjoint_val, Submodule.coe_sub, SUAlgebraOver.bracket_val, mc_val]
  rw [JetRing.matrix_map_pderiv_mul, JetRing.matrix_map_pderiv_mul, hq]
  simp only [smul_mul_assoc, mul_smul_comm, ← smul_sub, smul_smul, Complex.I_mul_I,
    neg_one_smul, sub_neg_eq_add, add_mul, mul_neg, ← mul_assoc]
  rw [mul_assoc (V.map (pderiv μ)) (star V) V, hVV, mul_one]
  abel

end JetSUAlgebra

/-!

## E. The local gauge data

-/

namespace LocalGaugeData

/-- **The local gauge data of `SU(n)`**: special unitary jets, traceless hermitian jets
  with the bracket `i (a b − b a)` and the conjugation action, and the Maurer–Cartan form
  `i (∂_μ U) U⁻¹`. -/
noncomputable def su (n : ℕ) : LocalGaugeData (SU n) (SUAlgebra n) (JetSU n) (JetSUAlgebra n)
    where
  eval := JetSU.eval
  ofConstant := JetSU.ofConstant
  eval_ofConstant := JetSU.eval_ofConstant
  evalLie := JetSUAlgebra.evalLie
  ofConstantLie := JetSUAlgebra.ofConstantLie
  ofConstantLie_lie := JetSUAlgebra.ofConstantLie_lie
  evalLie_ofConstantLie := JetSUAlgebra.evalLie_ofConstantLie
  deriv := JetSUAlgebra.deriv
  deriv_comm := JetSUAlgebra.deriv_comm
  deriv_bracket := JetSUAlgebra.deriv_bracket
  deriv_ofConstantLie := JetSUAlgebra.deriv_ofConstantLie
  coord := JetSUAlgebra.coord
  deriv_coord := JetSUAlgebra.deriv_coord
  evalLie_coord := JetSUAlgebra.evalLie_coord
  coord_lie := JetSUAlgebra.coord_lie
  adjoint := JetSUAlgebra.adjoint
  adjoint_lie := JetSUAlgebra.adjoint_lie
  adjointValue := JetSUAlgebra.adjointValue
  evalLie_adjoint := JetSUAlgebra.evalLie_adjoint
  maurerCartan := JetSUAlgebra.mc
  maurerCartan_ofConstant := JetSUAlgebra.mc_ofConstant
  maurerCartan_cocycle := JetSUAlgebra.mc_cocycle
  maurerCartan_structure := JetSUAlgebra.mc_structure
  deriv_adjoint := JetSUAlgebra.deriv_adjoint

variable {n : ℕ}

@[simp] lemma su_eval : (su n).eval = JetSU.eval := rfl
@[simp] lemma su_ofConstant : (su n).ofConstant = JetSU.ofConstant := rfl
@[simp] lemma su_evalLie : (su n).evalLie = JetSUAlgebra.evalLie := rfl
@[simp] lemma su_ofConstantLie : (su n).ofConstantLie = JetSUAlgebra.ofConstantLie := rfl
@[simp] lemma su_deriv (μ : Fin 1 ⊕ Fin 3) : (su n).deriv μ = JetSUAlgebra.deriv μ := rfl
@[simp] lemma su_adjoint : (su n).adjoint = JetSUAlgebra.adjoint := rfl
@[simp] lemma su_maurerCartan : (su n).maurerCartan = JetSUAlgebra.mc := rfl

/-- The iterated derivative on `su(n)` jets is the entrywise iterated formal derivative. -/
lemma su_iteratedDeriv_val (s : Multiset (Fin 1 ⊕ Fin 3)) (a : JetSUAlgebra n) :
    ((su n).iteratedDeriv s a).1 = a.1.map fun f => s.foldl (fun h ρ => pderiv ρ h) f := by
  induction s using Multiset.induction_on generalizing a with
  | empty =>
    rw [iteratedDeriv_zero, LinearMap.id_apply]
    ext i j : 1
    simp [Matrix.map_apply]
  | cons μ t ih =>
    rw [iteratedDeriv_cons, LinearMap.comp_apply, su_deriv, JetSUAlgebra.deriv_val, ih,
      Matrix.map_map]
    ext i j : 1
    simp only [Matrix.map_apply, Function.comp_apply, Multiset.foldl_cons]
    exact (JetRing.foldl_pderiv_pderiv t μ _).symm

/-- The base-point value of the iterated derivative on `su(n)` jets, entrywise. -/
lemma su_evalLie_iteratedDeriv_val (s : Multiset (Fin 1 ⊕ Fin 3)) (a : JetSUAlgebra n) :
    ((su n).evalLie ((su n).iteratedDeriv s a)).1
      = a.1.map fun f => constantCoeff (s.foldl (fun h ρ => pderiv ρ h) f) := by
  rw [su_evalLie, JetSUAlgebra.evalLie_val, su_iteratedDeriv_val, RingHom.mapMatrix_apply,
    Matrix.map_map]
  rfl

/-!

## F. The canonical factor and faithfulness

-/

/-- The canonical `SU(n)` factor of the local gauge data of `SU(n)`. -/
noncomputable def suFactor (n : ℕ) : SUFactor (su n) (Fin n) where
  u U := U.1
  u_one := rfl
  u_mul _ _ := rfl
  u_unitary := JetSU.star_mul_val
  φ := (SUAlgebraOver.submodule ℂ n).subtype
  φJ a := a.1
  φJ_ofConstantLie _ := rfl
  φJ_cc_foldl p a := (su_evalLie_iteratedDeriv_val p a).symm
  φJ_maurerCartan _ _ := rfl
  φJ_adjoint _ _ := rfl

/-- The local gauge data of `SU(n)` is faithful. -/
instance instFaithfulSU : (su n).Faithful where
  ext_of_evalLie_iteratedDeriv {x y} h := by
    refine Subtype.ext (Matrix.ext fun i j => ?_)
    refine JetRing.ext_of_constantCoeff_foldl_pderiv fun s => ?_
    have hs := congrArg (fun a : SUAlgebra n => a.1 i j) (h s)
    simpa only [su_evalLie_iteratedDeriv_val, Matrix.map_apply] using hs
  eq_ofConstant_of_maurerCartan_eq_zero {U} h := by
    have hd : ∀ μ, U.1.map (pderiv μ) = 0 := fun μ => by
      have h1 : Complex.I • (U.1.map (pderiv μ) * star U.1) = 0 :=
        congrArg Subtype.val (congrFun h μ)
      have h2 : U.1.map (pderiv μ) * star U.1 = 0 := by
        have := congrArg (fun M => (-Complex.I) • M) h1
        simpa [smul_smul, Complex.I_mul_I] using this
      calc U.1.map (pderiv μ)
          = U.1.map (pderiv μ) * (star U.1 * U.1) := by rw [JetSU.star_mul_val, mul_one]
        _ = 0 := by rw [← mul_assoc, h2, zero_mul]
    refine Subtype.ext (Matrix.ext fun i j => ?_)
    show U.1 i j = C (constantCoeff (U.1 i j))
    exact JetRing.eq_C_of_pderiv_eq_zero fun μ => congrArg (fun M => M i j) (hd μ)

end LocalGaugeData
