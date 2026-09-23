/-
Copyright (c) 2026 Jinzheng Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jinzheng Li
-/
module

public import Physlib.ClassicalFieldTheory.GaugeTheory.MatterField.MatrixRep.Factors
public import Physlib.Relativity.JetRing.Taylor
/-!
# The local gauge data of `U(1)`

## i. Overview

The abelian gauge group `U(1)`, with its jets, its Lie algebra and the jets of its Lie
algebra, packaged as local gauge data `LocalGaugeData.u1`. The jets of gauge
transformations are the unitary formal power series, the Lie algebra is the self-adjoint
(real) scalars and its jets the self-adjoint power series, with vanishing bracket and
trivial adjoint action. The Maurer–Cartan form is `i (∂_μ u) u⁻¹`.

The package comes with its canonical `U1Factor` and is faithful.

## ii. Key results

- `U1`, `JetU1`, `U1Algebra`, `JetU1Algebra` : the carriers.
- `LocalGaugeData.u1` : the local gauge data of `U(1)`.
- `LocalGaugeData.u1Factor` : its canonical `U(1)` factor.
- `LocalGaugeData.instFaithfulU1` : the package is faithful.

## iii. Table of contents

- A. The carriers
- B. The structure maps
- C. The Maurer–Cartan form
- D. The local gauge data
- E. The canonical factor and faithfulness

-/

@[expose] public section

open MvPowerSeries

/-!

## A. The carriers

-/

/-- The gauge group `U(1)`. -/
abbrev U1 : Type := ↥(unitary ℂ)

/-- Jets of `U(1)` gauge transformations: unitary formal power series. -/
abbrev JetU1 : Type := ↥(unitary JetRing)

/-- The Lie algebra `u(1)` over a `*`-ring: the self-adjoint elements, with vanishing
  bracket. -/
abbrev U1AlgebraOver (R : Type) [Ring R] [StarRing R] : Type := ↥(selfAdjoint R)

/-- The Lie algebra `u(1)`: the self-adjoint (real) scalars. -/
abbrev U1Algebra : Type := U1AlgebraOver ℂ

/-- Jets of the Lie algebra `u(1)`: the self-adjoint formal power series. -/
abbrev JetU1Algebra : Type := U1AlgebraOver JetRing

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
      ⟨by rw [← JetRing.constantCoeff_star, ← map_mul, h1, map_one],
        by rw [← JetRing.constantCoeff_star, ← map_mul, h2, map_one]⟩⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' u v := Subtype.ext (map_mul _ u.1 v.1)

@[simp]
lemma eval_val (u : JetU1) : (eval u : ℂ) = constantCoeff (u : JetRing) := rfl

/-- The jet of a constant `U(1)` gauge transformation. -/
noncomputable def ofConstant : U1 →* JetU1 where
  toFun u := ⟨C u.1, by
    obtain ⟨h1, h2⟩ := Unitary.mem_iff.mp u.2
    exact Unitary.mem_iff.mpr
      ⟨by rw [JetRing.star_C, ← map_mul, h1, map_one],
        by rw [JetRing.star_C, ← map_mul, h2, map_one]⟩⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' u v := Subtype.ext (map_mul _ u.1 v.1)

@[simp]
lemma ofConstant_val (u : U1) : (ofConstant u : JetRing) = C (u : ℂ) := rfl

@[simp]
lemma eval_ofConstant (u : U1) : eval (ofConstant u) = u :=
  Subtype.ext (constantCoeff_C u.1)

/-- The formal derivative of a `u(1)` jet. -/
noncomputable def deriv (μ : Fin 1 ⊕ Fin 3) : JetU1Algebra →ₗ[ℝ] JetU1Algebra where
  toFun a := ⟨pderiv μ a.1, by
    show star (pderiv μ a.1) = pderiv μ a.1
    rw [← JetRing.pderiv_star, a.2]⟩
  map_add' a b := Subtype.ext (map_add _ _ _)
  map_smul' r a := Subtype.ext (by
    show pderiv μ (r • a.1) = r • pderiv μ a.1
    rw [← algebraMap_smul ℂ r, Derivation.map_smul, algebraMap_smul])

@[simp]
lemma deriv_val (μ : Fin 1 ⊕ Fin 3) (a : JetU1Algebra) : (deriv μ a : JetRing) = pderiv μ a :=
  rfl

/-- Multiplication of a `u(1)` jet by the coordinate `x_μ`. -/
noncomputable def coord (μ : Fin 1 ⊕ Fin 3) : JetU1Algebra →ₗ[ℝ] JetU1Algebra where
  toFun a := ⟨(X μ : JetRing) * a.1, by
    show star ((X μ : JetRing) * a.1) = (X μ : JetRing) * a.1
    rw [star_mul', JetRing.star_X, a.2]⟩
  map_add' a b := Subtype.ext (mul_add _ _ _)
  map_smul' r a := Subtype.ext (mul_smul_comm _ _ _)

@[simp]
lemma coord_val (μ : Fin 1 ⊕ Fin 3) (a : JetU1Algebra) :
    (coord μ a : JetRing) = (X μ : JetRing) * a := rfl

/-- Evaluation of a `u(1)` jet at the base point. -/
noncomputable def evalLie : JetU1Algebra →ₗ⁅ℝ⁆ U1Algebra where
  toFun a := ⟨constantCoeff a.1, by
    show star (constantCoeff a.1) = constantCoeff a.1
    rw [← JetRing.constantCoeff_star, a.2]⟩
  map_add' a b := Subtype.ext (map_add _ _ _)
  map_smul' r a := Subtype.ext (by
    show constantCoeff (r • a.1) = r • constantCoeff a.1
    rw [← algebraMap_smul ℂ r, constantCoeff_smul, algebraMap_smul])
  map_lie' := by intro a b; simp

@[simp]
lemma evalLie_val (a : JetU1Algebra) : (evalLie a : ℂ) = constantCoeff (a : JetRing) := rfl

/-- A constant as a `u(1)` jet. -/
noncomputable def ofConstantLie : U1Algebra →ₗ[ℝ] JetU1Algebra where
  toFun a := ⟨C a.1, by
    show star (C a.1 : JetRing) = C a.1
    rw [JetRing.star_C, a.2]⟩
  map_add' a b := Subtype.ext (map_add _ _ _)
  map_smul' r a := Subtype.ext (by
    show (C (r • a.1) : JetRing) = r • C a.1
    rw [Algebra.smul_def, Algebra.smul_def, map_mul, MvPowerSeries.algebraMap_apply])

@[simp]
lemma ofConstantLie_val (a : U1Algebra) : (ofConstantLie a : JetRing) = C (a : ℂ) := rfl

/-!

## C. The Maurer–Cartan form

-/

/-- The Maurer–Cartan scalar `i (∂_μ u) u⁻¹` of a unitary jet is self-adjoint. -/
lemma star_mcVal (u : JetU1) (μ : Fin 1 ⊕ Fin 3) :
    star (Complex.I • (pderiv μ (u : JetRing) * star (u : JetRing)))
      = Complex.I • (pderiv μ (u : JetRing) * star (u : JetRing)) := by
  have hu : (u : JetRing) * star (u : JetRing) = 1 := Unitary.mul_star_self_of_mem u.2
  have h0 : pderiv μ ((u : JetRing) * star (u : JetRing)) = 0 := by rw [hu, pderiv_one]
  rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul] at h0
  rw [star_smul, star_mul', star_star, ← JetRing.pderiv_star, Complex.star_def, Complex.conj_I,
    neg_smul, show pderiv μ (star (u : JetRing)) * (u : JetRing)
      = -(pderiv μ (u : JetRing) * star (u : JetRing)) from by linear_combination h0,
    smul_neg, neg_neg]

/-- The Maurer–Cartan form `i (∂_μ u) u⁻¹` of a `U(1)` jet. -/
noncomputable def mc (u : JetU1) (μ : Fin 1 ⊕ Fin 3) : JetU1Algebra :=
  ⟨Complex.I • (pderiv μ (u : JetRing) * star (u : JetRing)), star_mcVal u μ⟩

@[simp]
lemma mc_val (u : JetU1) (μ : Fin 1 ⊕ Fin 3) :
    (mc u μ : JetRing) = Complex.I • (pderiv μ (u : JetRing) * star (u : JetRing)) := rfl

lemma mc_ofConstant (g : U1) (μ : Fin 1 ⊕ Fin 3) : mc (ofConstant g) μ = 0 :=
  Subtype.ext (by simp [pderiv_C])

/-- The Maurer–Cartan form of `U(1)` is additive: the abelian cocycle law. -/
lemma mc_mul (u v : JetU1) (μ : Fin 1 ⊕ Fin 3) : mc (u * v) μ = mc u μ + mc v μ := by
  refine Subtype.ext ?_
  have hu : (u : JetRing) * star (u : JetRing) = 1 := Unitary.mul_star_self_of_mem u.2
  have hv : (v : JetRing) * star (v : JetRing) = 1 := Unitary.mul_star_self_of_mem v.2
  show Complex.I • (pderiv μ ((u : JetRing) * (v : JetRing))
      * star ((u : JetRing) * (v : JetRing)))
    = Complex.I • (pderiv μ (u : JetRing) * star (u : JetRing))
      + Complex.I • (pderiv μ (v : JetRing) * star (v : JetRing))
  rw [← smul_add, Derivation.leibniz, star_mul', smul_eq_mul, smul_eq_mul]
  congr 1
  linear_combination (pderiv μ (u : JetRing) * star (u : JetRing)) * hv
    + (pderiv μ (v : JetRing) * star (v : JetRing)) * hu

/-- The Maurer–Cartan form of `U(1)` is flat: the derivatives of a phase commute. -/
lemma pderiv_mcVal_comm (u : JetU1) (μ ν : Fin 1 ⊕ Fin 3) :
    pderiv μ (pderiv ν (u : JetRing) * star (u : JetRing))
      = pderiv ν (pderiv μ (u : JetRing) * star (u : JetRing)) := by
  have hu : (u : JetRing) * star (u : JetRing) = 1 := Unitary.mul_star_self_of_mem u.2
  have hstar : ∀ ρ : Fin 1 ⊕ Fin 3, pderiv ρ (star (u : JetRing))
      = -(star (u : JetRing) * pderiv ρ (u : JetRing) * star (u : JetRing)) := by
    intro ρ
    have h0 : pderiv ρ ((u : JetRing) * star (u : JetRing)) = 0 := by rw [hu, pderiv_one]
    rw [Derivation.leibniz] at h0
    simp only [smul_eq_mul] at h0
    linear_combination star (u : JetRing) * h0
      - pderiv ρ (star (u : JetRing)) * ((mul_comm _ _).trans hu)
  simp only [Derivation.leibniz, smul_eq_mul]
  rw [hstar μ, hstar ν, JetRing.pderiv_comm μ ν]
  ring

end JetU1

/-!

## D. The local gauge data

-/

namespace LocalGaugeData

/-- **The local gauge data of `U(1)`**: unitary jets, self-adjoint scalar jets with
  vanishing bracket and trivial adjoint action, and the Maurer–Cartan form
  `i (∂_μ u) u⁻¹`. -/
noncomputable def u1 : LocalGaugeData U1 U1Algebra JetU1 JetU1Algebra where
  eval := JetU1.eval
  ofConstant := JetU1.ofConstant
  eval_ofConstant := JetU1.eval_ofConstant
  evalLie := JetU1.evalLie
  ofConstantLie := JetU1.ofConstantLie
  ofConstantLie_lie _ _ := by simp
  evalLie_ofConstantLie a := Subtype.ext (by simp)
  deriv := JetU1.deriv
  deriv_comm μ ν a := Subtype.ext (JetRing.pderiv_comm μ ν a.1)
  deriv_bracket _ _ _ := by simp
  deriv_ofConstantLie μ a := Subtype.ext (by simp [pderiv_C])
  coord := JetU1.coord
  deriv_coord μ ν a := by
    refine Subtype.ext ?_
    by_cases h : μ = ν
    · subst h
      rw [ite_eq_left rfl]
      show pderiv μ ((X μ : JetRing) * a.1) = (X μ : JetRing) * pderiv μ a.1 + a.1
      rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul, pderiv_X_self]
      ring
    · rw [ite_eq_right h, add_zero]
      show pderiv μ ((X ν : JetRing) * a.1) = (X ν : JetRing) * pderiv μ a.1
      rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul, pderiv_X_of_ne (Ne.symm h)]
      ring
  evalLie_coord μ a := Subtype.ext (by simp)
  coord_lie _ _ _ := by simp
  adjoint := Representation.trivial ℝ JetU1 JetU1Algebra
  adjoint_lie _ _ _ := by simp
  adjointValue := Representation.trivial ℝ U1 U1Algebra
  evalLie_adjoint _ _ := rfl
  maurerCartan := JetU1.mc
  maurerCartan_ofConstant := JetU1.mc_ofConstant
  maurerCartan_cocycle u v μ := by
    rw [JetU1.mc_mul]
    rfl
  maurerCartan_structure u μ ν := by
    refine Subtype.ext ?_
    show pderiv μ (Complex.I • (pderiv ν (u : JetRing) * star (u : JetRing)))
      - pderiv ν (Complex.I • (pderiv μ (u : JetRing) * star (u : JetRing))) + 0 = 0
    rw [Derivation.map_smul, Derivation.map_smul, JetU1.pderiv_mcVal_comm, sub_self, add_zero]
  deriv_adjoint _ _ _ := by simp

@[simp] lemma u1_eval : u1.eval = JetU1.eval := rfl
@[simp] lemma u1_ofConstant : u1.ofConstant = JetU1.ofConstant := rfl
@[simp] lemma u1_evalLie : u1.evalLie = JetU1.evalLie := rfl
@[simp] lemma u1_ofConstantLie : u1.ofConstantLie = JetU1.ofConstantLie := rfl
@[simp] lemma u1_deriv (μ : Fin 1 ⊕ Fin 3) : u1.deriv μ = JetU1.deriv μ := rfl
@[simp] lemma u1_maurerCartan : u1.maurerCartan = JetU1.mc := rfl
@[simp] lemma u1_adjoint (u : JetU1) (a : JetU1Algebra) : u1.adjoint u a = a := rfl

/-- The iterated derivative on `u(1)` jets is the iterated formal derivative. -/
lemma u1_iteratedDeriv_val (s : Multiset (Fin 1 ⊕ Fin 3)) (a : JetU1Algebra) :
    (u1.iteratedDeriv s a : JetRing) = s.foldl (fun h ρ => pderiv ρ h) (a : JetRing) := by
  induction s using Multiset.induction_on generalizing a with
  | empty => rw [iteratedDeriv_zero, LinearMap.id_apply, Multiset.foldl_zero]
  | cons μ t ih =>
    rw [iteratedDeriv_cons, LinearMap.comp_apply, u1_deriv, JetU1.deriv_val, ih,
      Multiset.foldl_cons, JetRing.foldl_pderiv_pderiv]

/-!

## E. The canonical factor and faithfulness

-/

/-- The canonical `U(1)` factor of the local gauge data of `U(1)`. -/
noncomputable def u1Factor : U1Factor u1 where
  u := MonoidHom.id JetU1
  φ :=
    { toFun a := (a : ℂ)
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }
  φJ a := (a : JetRing)
  φJ_ofConstantLie _ := rfl
  φJ_cc_foldl p a := by
    show constantCoeff (p.foldl (fun h ρ => pderiv ρ h) (a : JetRing))
      = constantCoeff (u1.iteratedDeriv p a : JetRing)
    rw [u1_iteratedDeriv_val]
  φJ_maurerCartan _ _ := rfl
  φJ_adjoint _ _ := rfl

/-- The local gauge data of `U(1)` is faithful. -/
instance instFaithfulU1 : u1.Faithful where
  ext_of_evalLie_iteratedDeriv {x y} h := Subtype.ext <|
    JetRing.ext_of_constantCoeff_foldl_pderiv fun s => by
      have hs := congrArg Subtype.val (h s)
      simpa only [u1_evalLie, JetU1.evalLie_val, u1_iteratedDeriv_val] using hs
  eq_ofConstant_of_maurerCartan_eq_zero {u} h := by
    have hu : (u : JetRing) * star (u : JetRing) = 1 := Unitary.mul_star_self_of_mem u.2
    have hd : ∀ μ, pderiv μ (u : JetRing) = 0 := fun μ => by
      have h1 : Complex.I • (pderiv μ (u : JetRing) * star (u : JetRing)) = 0 :=
        congrArg Subtype.val (congrFun h μ)
      have h2 : pderiv μ (u : JetRing) * star (u : JetRing) = 0 := by
        have := congrArg (fun z => (-Complex.I) • z) h1
        simpa [smul_smul, Complex.I_mul_I] using this
      calc pderiv μ (u : JetRing)
          = pderiv μ (u : JetRing) * ((u : JetRing) * star (u : JetRing)) := by
            rw [hu, mul_one]
        _ = 0 := by rw [mul_comm (u : JetRing), ← mul_assoc, h2, zero_mul]
    exact Subtype.ext (JetRing.eq_C_of_pderiv_eq_zero hd)

end LocalGaugeData
