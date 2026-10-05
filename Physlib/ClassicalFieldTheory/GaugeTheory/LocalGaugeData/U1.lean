/-
Copyright (c) 2026 Jinzheng Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jinzheng Li
-/
module

public import Physlib.ClassicalFieldTheory.GaugeTheory.LocalGaugeData.MatrixJets
public import Physlib.Mathematics.ForMathlib.DataStructures.Matrix.Scalar
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.Tactic.LinearCombination
/-!
# The local gauge data of `U(1)`

## i. Overview

The abelian gauge group `U(1)`, with its jets, its Lie algebra and the jets of its Lie
algebra, packaged as local gauge data `LocalGaugeData.u1`. The jets of gauge
transformations are the unitary formal power series, the Lie algebra is the self-adjoint
(real) scalars and its jets the self-adjoint power series, with vanishing bracket and
trivial adjoint action. The Maurer–Cartan form is `i (∂_μ u) u⁻¹`.

Read as `1 × 1` matrices, this is a presentation by matrices of jets,
`LocalGaugeData.u1MatrixJets`, so the laws of the local gauge data and its faithfulness come
from `Physlib.ClassicalFieldTheory.GaugeTheory.LocalGaugeData.MatrixJets`. What this file
supplies is the carriers, the structure maps on them, and the canonical `U1Factor`.

## ii. Key results

- `U1`, `JetU1`, `U1Algebra`, `JetU1Algebra` : the carriers.
- `LocalGaugeData.u1MatrixJets` : the presentation of `U(1)` by `1 × 1` matrices of jets.
- `LocalGaugeData.u1` : the local gauge data of `U(1)`.
- `LocalGaugeData.u1Factor` : its canonical `U(1)` factor.
- `LocalGaugeData.instFaithfulU1` : the package is faithful.
- `LocalGaugeData.instFreeU1` : the package is free.

## iii. Table of contents

- A. The carriers
- B. The structure maps
- C. The Maurer–Cartan form
- D. The presentation and the local gauge data
- E. The canonical factor

-/

@[expose] public section

open MvPowerSeries

/-!

## A. The carriers

-/

/-- The gauge group `U(1)`. -/
abbrev U1 : Type := ↥(unitary ℂ)

/-- Jets of `U(1)` gauge transformations: unitary formal power series. -/
abbrev JetU1 : Type := ↥(unitary SpaceTimeAlgebra)

/-- The Lie algebra `u(1)` over a `*`-ring: the self-adjoint elements, with vanishing
  bracket. -/
abbrev U1AlgebraOver (R : Type) [Ring R] [StarRing R] : Type := ↥(selfAdjoint R)

/-- The Lie algebra `u(1)`: the self-adjoint (real) scalars. -/
abbrev U1Algebra : Type := U1AlgebraOver ℂ

/-- Jets of the Lie algebra `u(1)`: the self-adjoint formal power series. -/
abbrev JetU1Algebra : Type := U1AlgebraOver SpaceTimeAlgebra

namespace U1AlgebraOver

variable {R : Type} [CommRing R] [StarRing R]

instance : Bracket (U1AlgebraOver R) (U1AlgebraOver R) := ⟨fun _ _ => 0⟩

@[simp]
lemma bracket_eq_zero (a b : U1AlgebraOver R) : ⁅a, b⁆ = 0 := rfl

instance : LieRing (U1AlgebraOver R) where
  add_lie _ _ _ := by simp
  lie_add _ _ _ := by simp
  lie_self _ := rfl
  leibniz_lie _ _ _ := by simp

instance [Algebra ℝ R] [StarModule ℝ R] : LieAlgebra ℝ (U1AlgebraOver R) where
  lie_smul _ _ _ := by simp

end U1AlgebraOver

instance : Module.Finite ℝ U1Algebra :=
  inferInstanceAs (Module.Finite ℝ (selfAdjoint.submodule ℝ ℂ))

namespace JetU1

/-!

## B. The structure maps

-/

/-- Evaluation of a jet of a `U(1)` gauge transformation at the base point. -/
noncomputable def eval : JetU1 →* U1 where
  toFun u := ⟨constantCoeff u.1, by
    obtain ⟨h1, h2⟩ := Unitary.mem_iff.mp u.2
    exact Unitary.mem_iff.mpr
      ⟨by rw [← SpaceTimeAlgebra.constantCoeff_star, ← map_mul, h1, map_one],
        by rw [← SpaceTimeAlgebra.constantCoeff_star, ← map_mul, h2, map_one]⟩⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' u v := Subtype.ext (map_mul _ u.1 v.1)

@[simp]
lemma eval_val (u : JetU1) : (eval u : ℂ) = constantCoeff (u : SpaceTimeAlgebra) := rfl

/-- The jet of a constant `U(1)` gauge transformation. -/
noncomputable def ofConstant : U1 →* JetU1 where
  toFun u := ⟨C u.1, by
    obtain ⟨h1, h2⟩ := Unitary.mem_iff.mp u.2
    exact Unitary.mem_iff.mpr
      ⟨by rw [SpaceTimeAlgebra.star_C, ← map_mul, h1, map_one],
        by rw [SpaceTimeAlgebra.star_C, ← map_mul, h2, map_one]⟩⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' u v := Subtype.ext (map_mul _ u.1 v.1)

@[simp]
lemma ofConstant_val (u : U1) : (ofConstant u : SpaceTimeAlgebra) = C (u : ℂ) := rfl

/-- The formal derivative of a `u(1)` jet. -/
noncomputable def deriv (μ : Fin 1 ⊕ Fin 3) : JetU1Algebra →ₗ[ℝ] JetU1Algebra where
  toFun a := ⟨pderiv μ a.1, by
    show star (pderiv μ a.1) = pderiv μ a.1
    rw [← SpaceTimeAlgebra.pderiv_star, a.2]⟩
  map_add' a b := Subtype.ext (map_add _ _ _)
  map_smul' r a := Subtype.ext (by
    show pderiv μ (r • a.1) = r • pderiv μ a.1
    exact SpaceTimeAlgebra.pderiv_real_smul μ r _)

@[simp]
lemma deriv_val (μ : Fin 1 ⊕ Fin 3) (a : JetU1Algebra) :
    (deriv μ a : SpaceTimeAlgebra) = pderiv μ a :=
  rfl

/-- Multiplication of a `u(1)` jet by the coordinate `x_μ`. -/
noncomputable def coord (μ : Fin 1 ⊕ Fin 3) : JetU1Algebra →ₗ[ℝ] JetU1Algebra where
  toFun a := ⟨(X μ : SpaceTimeAlgebra) * a.1, by
    show star ((X μ : SpaceTimeAlgebra) * a.1) = (X μ : SpaceTimeAlgebra) * a.1
    rw [star_mul', SpaceTimeAlgebra.star_X, a.2]⟩
  map_add' a b := Subtype.ext (mul_add _ _ _)
  map_smul' r a := Subtype.ext (mul_smul_comm _ _ _)

@[simp]
lemma coord_val (μ : Fin 1 ⊕ Fin 3) (a : JetU1Algebra) :
    (coord μ a : SpaceTimeAlgebra) = (X μ : SpaceTimeAlgebra) * a := rfl

/-- Evaluation of a `u(1)` jet at the base point. -/
noncomputable def evalLie : JetU1Algebra →ₗ[ℝ] U1Algebra where
  toFun a := ⟨constantCoeff a.1, by
    show star (constantCoeff a.1) = constantCoeff a.1
    rw [← SpaceTimeAlgebra.constantCoeff_star, a.2]⟩
  map_add' a b := Subtype.ext (map_add _ _ _)
  map_smul' r a := Subtype.ext (by
    show constantCoeff (r • a.1) = r • constantCoeff a.1
    exact SpaceTimeAlgebra.constantCoeff_real_smul r _)

@[simp]
lemma evalLie_val (a : JetU1Algebra) : (evalLie a : ℂ) = constantCoeff (a : SpaceTimeAlgebra) := rfl

/-- A constant as a `u(1)` jet. -/
noncomputable def ofConstantLie : U1Algebra →ₗ[ℝ] JetU1Algebra where
  toFun a := ⟨C a.1, by
    show star (C a.1 : SpaceTimeAlgebra) = C a.1
    rw [SpaceTimeAlgebra.star_C, a.2]⟩
  map_add' a b := Subtype.ext (map_add _ _ _)
  map_smul' r a := Subtype.ext (by
    show (C (r • a.1) : SpaceTimeAlgebra) = r • C a.1
    exact SpaceTimeAlgebra.C_real_smul r _)

@[simp]
lemma ofConstantLie_val (a : U1Algebra) : (ofConstantLie a : SpaceTimeAlgebra) = C (a : ℂ) := rfl

/-!

## C. The Maurer–Cartan form

-/

/-- The Maurer–Cartan scalar `i (∂_μ u) u⁻¹` of a unitary jet is self-adjoint. -/
lemma star_mcVal (u : JetU1) (μ : Fin 1 ⊕ Fin 3) :
    star (Complex.I • (pderiv μ (u : SpaceTimeAlgebra) * star (u : SpaceTimeAlgebra)))
      = Complex.I • (pderiv μ (u : SpaceTimeAlgebra) * star (u : SpaceTimeAlgebra)) := by
  have hu : (u : SpaceTimeAlgebra) * star (u : SpaceTimeAlgebra) = 1 :=
      Unitary.mul_star_self_of_mem u.2
  have h0 : pderiv μ ((u : SpaceTimeAlgebra) * star (u : SpaceTimeAlgebra)) = 0 := by
    rw [hu, pderiv_one]
  rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul] at h0
  rw [star_smul, star_mul', star_star, ← SpaceTimeAlgebra.pderiv_star, Complex.star_def,
      Complex.conj_I,
    neg_smul, show pderiv μ (star (u : SpaceTimeAlgebra)) * (u : SpaceTimeAlgebra)
      = -(pderiv μ (u : SpaceTimeAlgebra) * star (u : SpaceTimeAlgebra)) from by
          linear_combination h0,
    smul_neg, neg_neg]

/-- The Maurer–Cartan form `i (∂_μ u) u⁻¹` of a `U(1)` jet. -/
noncomputable def mc (u : JetU1) (μ : Fin 1 ⊕ Fin 3) : JetU1Algebra :=
  ⟨Complex.I • (pderiv μ (u : SpaceTimeAlgebra) * star (u : SpaceTimeAlgebra)), star_mcVal u μ⟩

@[simp]
lemma mc_val (u : JetU1) (μ : Fin 1 ⊕ Fin 3) :
    (mc u μ : SpaceTimeAlgebra) = Complex.I •
        (pderiv μ (u : SpaceTimeAlgebra) * star (u : SpaceTimeAlgebra)) := rfl


end JetU1

/-!

## D. The presentation and the local gauge data

-/

namespace LocalGaugeData

open JetU1

/-- **The presentation of `U(1)` by `1 × 1` matrices of jets.** -/
noncomputable def u1MatrixJets : MatrixJets (Fin 1) U1 U1Algebra JetU1 JetU1Algebra where
  toMat₀ := (Matrix.scalar (Fin 1) : ℂ →+* _).toMonoidHom.comp (unitary ℂ).subtype
  toMat₀_injective _ _ h := Subtype.ext (Matrix.scalar_inj.mp h)
  toMatJ := (Matrix.scalar (Fin 1) : SpaceTimeAlgebra →+* _).toMonoidHom.comp
      (unitary SpaceTimeAlgebra).subtype
  toMatJ_injective _ _ h := Subtype.ext (Matrix.scalar_inj.mp h)
  toMatJ_mul_star u := by
    show Matrix.scalar (Fin 1) u.1 * star (Matrix.scalar (Fin 1) u.1) = 1
    rw [Matrix.star_scalar, ← map_mul, Unitary.mul_star_self_of_mem u.2, map_one]
  star_toMatJ_mul u := by
    show star (Matrix.scalar (Fin 1) u.1) * Matrix.scalar (Fin 1) u.1 = 1
    rw [Matrix.star_scalar, ← map_mul, Unitary.star_mul_self_of_mem u.2, map_one]
  lie₀ := Matrix.scalarSelfAdjoint
  lie₀_injective _ _ h := Subtype.ext (Matrix.scalar_inj.mp h)
  lie₀_bracket a b := by
    show Matrix.scalar (Fin 1) ((0 : U1Algebra) : ℂ) = Complex.I • _
    rw [Matrix.scalarSelfAdjoint_apply, Matrix.scalarSelfAdjoint_apply,
      (Matrix.scalar_commute _ (fun _ => Commute.all _ _) _).eq, sub_self, smul_zero,
      ZeroMemClass.coe_zero, map_zero]
  lieJ := Matrix.scalarSelfAdjoint
  lieJ_injective _ _ h := Subtype.ext (Matrix.scalar_inj.mp h)
  lieJ_bracket a b := by
    show Matrix.scalar (Fin 1) ((0 : JetU1Algebra) : SpaceTimeAlgebra) = Complex.I • _
    rw [Matrix.scalarSelfAdjoint_apply, Matrix.scalarSelfAdjoint_apply,
      (Matrix.scalar_commute _ (fun _ => Commute.all _ _) _).eq, sub_self, smul_zero,
      ZeroMemClass.coe_zero, map_zero]
  eval := JetU1.eval
  toMat₀_eval u := (Matrix.map_scalar constantCoeff (map_zero _) u.1).symm
  ofConstant := JetU1.ofConstant
  toMatJ_ofConstant u := (Matrix.map_scalar C (map_zero _) u.1).symm
  evalLie := JetU1.evalLie
  lie₀_evalLie a := (Matrix.map_scalar constantCoeff (map_zero _) a.1).symm
  ofConstantLie := JetU1.ofConstantLie
  lieJ_ofConstantLie a := (Matrix.map_scalar C (map_zero _) a.1).symm
  deriv := JetU1.deriv
  lieJ_deriv μ a := (Matrix.map_scalar (pderiv μ) (map_zero _) a.1).symm
  coord := JetU1.coord
  lieJ_coord μ a := by
    show Matrix.scalar (Fin 1) ((X μ : SpaceTimeAlgebra) * a.1) = (X μ : SpaceTimeAlgebra) •
        Matrix.scalar (Fin 1) a.1
    rw [← smul_eq_mul, Matrix.scalar_smul]
  adjoint := Representation.trivial ℝ JetU1 JetU1Algebra
  lieJ_adjoint u a := Matrix.scalar_eq_conj (Unitary.mul_star_self_of_mem u.2) a.1
  adjointValue := Representation.trivial ℝ U1 U1Algebra
  lie₀_adjointValue u a := Matrix.scalar_eq_conj (Unitary.mul_star_self_of_mem u.2) a.1
  maurerCartan := JetU1.mc
  lieJ_maurerCartan u μ := by
    show Matrix.scalar (Fin 1) (Complex.I • (pderiv μ u.1 * star u.1))
      = Complex.I • ((Matrix.scalar (Fin 1) u.1).map (pderiv μ) * star (Matrix.scalar (Fin 1) u.1))
    rw [Matrix.scalar_smul, map_mul, Matrix.star_scalar, Matrix.map_scalar _ (map_zero _)]

/-- **The local gauge data of `U(1)`**: unitary jets, self-adjoint scalar jets with
  vanishing bracket and trivial adjoint action, and the Maurer–Cartan form
  `i (∂_μ u) u⁻¹`. -/
noncomputable def u1 : LocalGaugeData U1 U1Algebra JetU1 JetU1Algebra :=
  u1MatrixJets.toLocalGaugeData

@[simp] lemma u1_eval : u1.eval = JetU1.eval := rfl
@[simp] lemma u1_ofConstant : u1.ofConstant = JetU1.ofConstant := rfl
@[simp] lemma u1_evalLie_apply (a : JetU1Algebra) : u1.evalLie a = JetU1.evalLie a := rfl
@[simp] lemma u1_ofConstantLie : u1.ofConstantLie = JetU1.ofConstantLie := rfl
@[simp] lemma u1_deriv (μ : Fin 1 ⊕ Fin 3) : u1.deriv μ = JetU1.deriv μ := rfl
@[simp] lemma u1_maurerCartan : u1.maurerCartan = JetU1.mc := rfl
@[simp] lemma u1_adjoint (u : JetU1) (a : JetU1Algebra) : u1.adjoint u a = a := rfl

/-- The iterated derivative on `u(1)` jets is the iterated formal derivative. -/
lemma u1_iteratedDeriv_val (s : Multiset (Fin 1 ⊕ Fin 3)) (a : JetU1Algebra) :
    (u1.iteratedDeriv s a : SpaceTimeAlgebra) =
      SpaceTimeAlgebra.iteratedPDeriv s (a : SpaceTimeAlgebra) := by
  induction s using Multiset.induction_on generalizing a with
  | empty => rw [iteratedDeriv_zero, LinearMap.id_apply, SpaceTimeAlgebra.iteratedPDeriv_zero]
  | cons μ t ih =>
    rw [iteratedDeriv_cons, LinearMap.comp_apply, u1_deriv, JetU1.deriv_val, ih,
      SpaceTimeAlgebra.iteratedPDeriv_cons]
    exact (SpaceTimeAlgebra.iteratedPDeriv_pderiv t μ _).symm

/-- The local gauge data of `U(1)` is faithful. -/
instance instFaithfulU1 : u1.Faithful := u1MatrixJets.faithful

/-- The local gauge data of `U(1)` is free. Real Taylor data give a self-adjoint jet, and
  the unitary Euler transport of a `1 × 1` matrix is a unitary jet. -/
instance instFreeU1 : u1.Free :=
  u1MatrixJets.free
    (fun c => ⟨⟨SpaceTimeAlgebra.ofDerivValues fun s => ((c s : U1Algebra) : ℂ), by
      rw [selfAdjoint.mem_iff, SpaceTimeAlgebra.star_ofDerivValues]
      exact congrArg _ (funext fun s => (c s).2)⟩, by
      rw [Matrix.eq_scalar_fin_one (SpaceTimeAlgebra.taylorMatrix _),
          SpaceTimeAlgebra.taylorMatrix_apply]
      rfl⟩)
    (fun a => by
      show star (Matrix.scalar (Fin 1) a.1) = Matrix.scalar (Fin 1) a.1
      rw [Matrix.star_scalar, a.2])
    (fun ρ V hV0 hVu hEV => by
      have hu : V 0 0 * star (V 0 0) = 1 := by
        simpa [Matrix.mul_apply] using congrArg (fun A => A 0 0) hVu
      exact ⟨⟨V 0 0, Unitary.mem_iff.mpr ⟨by rw [mul_comm]; exact hu, hu⟩⟩,
        (Matrix.eq_scalar_fin_one V).symm⟩)

/-!

## E. The canonical factor

-/

/-- The canonical `U(1)` factor of the local gauge data of `U(1)`. -/
noncomputable def u1Factor : U1Factor u1 where
  u := MonoidHom.id JetU1
  φ :=
    { toFun a := (a : ℂ)
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }
  φJ a := (a : SpaceTimeAlgebra)
  φJ_ofConstantLie _ := rfl
  φJ_cc_foldl p a := by
    show constantCoeff (SpaceTimeAlgebra.iteratedPDeriv p (a : SpaceTimeAlgebra))
      = constantCoeff (u1.iteratedDeriv p a : SpaceTimeAlgebra)
    rw [u1_iteratedDeriv_val]
  φJ_maurerCartan _ _ := rfl
  φJ_adjoint _ _ := rfl

end LocalGaugeData
