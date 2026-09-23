/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.ClassicalFieldTheory.GaugeTheory.LocalFieldAlgebra.Jet
public import Physlib.Relativity.Tensors.ComplexTensor.Vector.Pre.Basic
public import Physlib.Relativity.IsLorentzDeriv
public import Mathlib.RepresentationTheory.Basic
public import Mathlib.LinearAlgebra.Contraction
public import Mathlib.LinearAlgebra.TensorProduct.Prod
public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
/-!
# Fibrewise actions on `V`-valued jets

## i. Overview

A gauge transformation acts on the jets `JetRing ⊗[ℂ] V` of a `V`-valued field. What makes
that action local is that it is *fibrewise*: it commutes with multiplication by scalar
jets, so it acts on the values of the field over the identity on spacetime. This file
collects what follows from fibrewise-linearity alone, before any component space is built:

* a fibrewise action is determined by its values on constant jets, and for
  finite-dimensional `V` that restriction is a matrix of power series, its *coefficient*
  `jetCoeff` in `JetRing ⊗ End V`, which is multiplicative;
* the conjugate action `repConj` on the jets of the conjugate field, again fibrewise;
* the naturality of both in the value space: a linear map of value spaces intertwining two
  fibrewise actions intertwines their coefficients, and their conjugate actions.

These are the ingredients from which the action on the jet component space is assembled in
`Physlib.ClassicalFieldTheory.GaugeTheory.MatterField.JetComponentSpace.GaugeAction`; they
live here, upstream of `MatterField`, because the infinitesimal-action theory that
`MatterField` is stated over already needs `repConj`.

## ii. Key results

- `JetComponentSpace.jetCoeff` : the coefficient of a fibrewise action, in `JetRing ⊗ End V`.
- `JetComponentSpace.coeff_mul_of_smul_comm` : the coefficient is multiplicative.
- `JetComponentSpace.repConj`, `repConj_smul_comm` : the action on the jets of the
  conjugate field.
- `JetComponentSpace.jetCoeff_naturality` : the coefficient is natural in the value space.
- `JetComponentSpace.lTensor_comp_repConj` : so is the conjugate action.

-/

@[expose] public section

open Matrix MatrixGroups TensorProduct

namespace JetComponentSpace

open Matrix MatrixGroups TensorProduct

variable {V : Type _} [AddCommGroup V] [Module ℂ V]
variable {W : Type _} [AddCommGroup W] [Module ℂ W]
variable {G : Type*} [Group G]

/-- **A fibrewise action is determined by its values on constant jets.** If the gauge
action commutes with multiplication by scalar jets — the statement that it acts on the
values of the field, over the identity on spacetime — then its value on a general jet
`f ⊗ₜ v` is the constant-jet value `rep U (1 ⊗ₜ v)` scaled by `f`. -/
lemma rep_tmul_of_smul_comm
    {rep : Representation ℂ G (JetRing ⊗[ℂ] V)}
    (hlin : ∀ (U : G) (χ : JetRing) (z : JetRing ⊗[ℂ] V),
      rep U (χ • z) = χ • rep U z)
    (U : G) (f : JetRing) (v : V) :
    rep U (f ⊗ₜ[ℂ] v) = f • rep U (jetOfConstant v) := by
  rw [← hlin U f (jetOfConstant v), jetOfConstant_apply,
    show f • ((1 : JetRing) ⊗ₜ[ℂ] v) = f ⊗ₜ[ℂ] v from by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]]

/-- **The canonical evaluation is a right module map.** Writing `ev` for the canonical
`JetRing ⊗ End V → (V →ₗ JetRing ⊗ V)`, `g ⊗ T ↦ (v ↦ g ⊗ₜ T v)`, multiplying on the
right by `b ⊗ T` applies `T` to the argument and scales the value by `b`. -/
lemma lift_mul_tmul (x : JetRing ⊗[ℂ] Module.End ℂ V)
    (b : JetRing) (T : Module.End ℂ V) (v : V) :
    TensorProduct.lift ((LinearMap.llcomp ℂ V V (JetRing ⊗[ℂ] V)).comp
        (TensorProduct.mk ℂ JetRing V)) (x * (b ⊗ₜ[ℂ] T)) v
      = b • TensorProduct.lift ((LinearMap.llcomp ℂ V V (JetRing ⊗[ℂ] V)).comp
        (TensorProduct.mk ℂ JetRing V)) x (T v) := by
  induction x using TensorProduct.induction_on with
  | zero =>
      have h0 : (0 : JetRing ⊗[ℂ] Module.End ℂ V) * (b ⊗ₜ[ℂ] T) = 0 := by exact zero_mul (b ⊗ₜ[ℂ] T)
      rw [h0]
      simp
  | tmul a S =>
      rw [Algebra.TensorProduct.tmul_mul_tmul]
      show (a * b) ⊗ₜ[ℂ] (S * T) v = b • (a ⊗ₜ[ℂ] S (T v))
      rw [Module.End.mul_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_comm b a]
  | add p q hp hq =>
      have hd : (p + q) * (b ⊗ₜ[ℂ] T) = p * (b ⊗ₜ[ℂ] T) + q * (b ⊗ₜ[ℂ] T) := by
        exact Distrib.right_distrib p q (b ⊗ₜ[ℂ] T)
      rw [hd, map_add, LinearMap.add_apply, hp, hq, map_add, LinearMap.add_apply,
        smul_add]

/-- **A fibrewise action is the `JetRing`-linear extension of its coefficient.** If the
element `x` of `JetRing ⊗ End V` records `rep U` on constant jets, then `rep U` agrees
with left multiplication by `x` on every coefficient `y`. -/
lemma rep_lift_of_smul_comm
    {rep : Representation ℂ G (JetRing ⊗[ℂ] V)}
    (hlin : ∀ (U : G) (χ : JetRing) (z : JetRing ⊗[ℂ] V),
      rep U (χ • z) = χ • rep U z)
    (U : G) (x : JetRing ⊗[ℂ] Module.End ℂ V)
    (hx : ∀ v : V, TensorProduct.lift ((LinearMap.llcomp ℂ V V (JetRing ⊗[ℂ] V)).comp
      (TensorProduct.mk ℂ JetRing V)) x v = rep U (jetOfConstant v))
    (y : JetRing ⊗[ℂ] Module.End ℂ V) (v : V) :
    rep U (TensorProduct.lift ((LinearMap.llcomp ℂ V V (JetRing ⊗[ℂ] V)).comp
        (TensorProduct.mk ℂ JetRing V)) y v)
      = TensorProduct.lift ((LinearMap.llcomp ℂ V V (JetRing ⊗[ℂ] V)).comp
        (TensorProduct.mk ℂ JetRing V)) (x * y) v := by
  induction y using TensorProduct.induction_on with
  | zero =>
      have h0 : x * (0 : JetRing ⊗[ℂ] Module.End ℂ V) = 0 := by exact mul_zero x
      rw [h0]
      simp
  | tmul b T =>
      rw [lift_mul_tmul x b T v,
        show TensorProduct.lift ((LinearMap.llcomp ℂ V V (JetRing ⊗[ℂ] V)).comp
          (TensorProduct.mk ℂ JetRing V)) (b ⊗ₜ[ℂ] T) v = b ⊗ₜ[ℂ] T v from rfl,
        rep_tmul_of_smul_comm hlin U b (T v), hx (T v)]
  | add p q hp hq =>
      have hd : x * (p + q) = x * p + x * q := by exact Distrib.left_distrib x p q
      rw [hd, map_add, LinearMap.add_apply, map_add, map_add, LinearMap.add_apply,
        hp, hq]

/-- **The coefficient of a fibrewise action is multiplicative.** Recording `rep` on
constant jets as a family `c` in `JetRing ⊗ End V`, group multiplication becomes
multiplication in that algebra. This is the identity that makes the induced action on
the symbols a representation, and it needs no basis. -/
lemma coeff_mul_of_smul_comm
    {rep : Representation ℂ G (JetRing ⊗[ℂ] V)}
    (hlin : ∀ (U : G) (χ : JetRing) (z : JetRing ⊗[ℂ] V),
      rep U (χ • z) = χ • rep U z)
    (c : G → JetRing ⊗[ℂ] Module.End ℂ V)
    (hc : ∀ (U : G) (v : V),
      TensorProduct.lift ((LinearMap.llcomp ℂ V V (JetRing ⊗[ℂ] V)).comp
        (TensorProduct.mk ℂ JetRing V)) (c U) v = rep U (jetOfConstant v))
    (U W : G) (v : V) :
    TensorProduct.lift ((LinearMap.llcomp ℂ V V (JetRing ⊗[ℂ] V)).comp
        (TensorProduct.mk ℂ JetRing V)) (c U * c W) v
      = rep (U * W) (jetOfConstant v) := by
  rw [← rep_lift_of_smul_comm hlin U (c U) (hc U) (c W) v, hc W v, map_mul,
    Module.End.mul_apply]

/-- **The symbol action of a coefficient is an anti-homomorphism.** Let `Θ` send a
coefficient `g ⊗ T` in `JetRing ⊗ End V` to the endomorphism `jetRingAction g ⊗ Tᵀ` of
the symbol space `DerivAlgebraComplex ⊗ Dual V`. Then `Θ` reverses products: the jet-ring
factor is multiplicative (`jetRingAction_mul`, and `JetRing` is commutative) while the
target factor is contravariant (`Module.Dual.transpose_comp`). Composed with `U ↦ U⁻¹`
this is exactly what makes the induced action a representation, with no induction over
the antidiagonal. -/
lemma symbolAction_mul
    (Θ : (JetRing ⊗[ℂ] Module.End ℂ V) →ₗ[ℂ]
      Module.End ℂ (DerivAlgebraComplex ⊗[ℂ] Module.Dual ℂ V))
    (hΘ : ∀ (g : JetRing) (T : Module.End ℂ V),
      Θ (g ⊗ₜ[ℂ] T) = TensorProduct.map (DerivAlgebraComplex.jetRingAction g)
        (Module.Dual.transpose T))
    (x y : JetRing ⊗[ℂ] Module.End ℂ V) :
    Θ (x * y) = Θ y ∘ₗ Θ x := by
  induction x using TensorProduct.induction_on with
  | zero =>
      have h0 : (0 : JetRing ⊗[ℂ] Module.End ℂ V) * y = 0 := by exact zero_mul y
      rw [h0, map_zero]
      simp
  | tmul a S =>
      induction y using TensorProduct.induction_on with
      | zero =>
          have h0 : (a ⊗ₜ[ℂ] S) * (0 : JetRing ⊗[ℂ] Module.End ℂ V) = 0 := by
            exact mul_zero (a ⊗ₜ[ℂ] S)
          rw [h0, map_zero]
          simp
      | tmul b T =>
          rw [Algebra.TensorProduct.tmul_mul_tmul, hΘ, hΘ, hΘ,
            ← TensorProduct.map_comp, ← DerivAlgebraComplex.jetRingAction_mul,
            ← Module.Dual.transpose_comp, Module.End.mul_eq_comp, mul_comm a b]
      | add p q hp hq =>
          have hd : (a ⊗ₜ[ℂ] S) * (p + q) = (a ⊗ₜ[ℂ] S) * p + (a ⊗ₜ[ℂ] S) * q := by
            exact Distrib.left_distrib (a ⊗ₜ[ℂ] S) p q
          rw [hd, map_add, map_add, LinearMap.add_comp, hp, hq]
  | add p q hp hq =>
      have hd : (p + q) * y = p * y + q * y := by exact Distrib.right_distrib p q y
      rw [hd, map_add, map_add, LinearMap.comp_add, hp, hq]

/-- **The coefficient of a linear map, canonically.** For finite-dimensional `V` the
canonical `JetRing ⊗ (V →ₗ W) → (V →ₗ JetRing ⊗ W)` is inverted by reassociating the
contraction `Dual V ⊗ (JetRing ⊗ W) ≃ JetRing ⊗ (Dual V ⊗ W) ≃ JetRing ⊗ (V →ₗ W)`. This
is the finite-rank input, obtained from `dualTensorHomEquiv` rather than from a basis. Only
the source `V` has to be finite-dimensional; the target is arbitrary, which is what lets
the naturality statements below compare two different value spaces. -/
lemma lift_congr_leftComm [Module.Free ℂ V] [Module.Finite ℂ V]
    (G : Module.Dual ℂ V ⊗[ℂ] (JetRing ⊗[ℂ] W)) (v : V) :
    TensorProduct.lift ((LinearMap.llcomp ℂ V W (JetRing ⊗[ℂ] W)).comp
        (TensorProduct.mk ℂ JetRing W))
        ((TensorProduct.congr (LinearEquiv.refl ℂ JetRing) (dualTensorHomEquiv ℂ V W))
          (TensorProduct.leftComm ℂ (Module.Dual ℂ V) JetRing W G)) v
      = dualTensorHom ℂ V (JetRing ⊗[ℂ] W) G v := by
  induction G using TensorProduct.induction_on with
  | zero => simp
  | tmul phi z =>
      induction z using TensorProduct.induction_on with
      | zero => simp
      | tmul g w =>
          rw [TensorProduct.leftComm_tmul, TensorProduct.congr_tmul,
            LinearEquiv.refl_apply]
          show g ⊗ₜ[ℂ] (dualTensorHomEquiv ℂ V W (phi ⊗ₜ[ℂ] w)) v = _
          rw [show dualTensorHomEquiv ℂ V W (phi ⊗ₜ[ℂ] w)
              = dualTensorHom ℂ V W (phi ⊗ₜ[ℂ] w) from rfl,
            dualTensorHom_apply, dualTensorHom_apply, TensorProduct.tmul_smul]
      | add z₁ z₂ h₁ h₂ =>
          rw [TensorProduct.tmul_add, map_add, map_add, map_add, LinearMap.add_apply,
            map_add, LinearMap.add_apply, h₁, h₂]
  | add G₁ G₂ h₁ h₂ =>
      rw [map_add, map_add, map_add, LinearMap.add_apply, map_add,
        LinearMap.add_apply, h₁, h₂]

/-- **The conjugate jet action.** Given a gauge action on the jets of a `V`-valued field,
this is the induced action on the jets of the *conjugate* field.

It is `Representation.conj rep` — the same underlying maps, read on `ConjModule` — carried
across the identification

  `ConjModule (JetRing ⊗[ℂ] V) ≃ₗ[ℂ] JetRing ⊗[ℂ] ConjModule V`

which is `ConjModule.tensorEquiv` (conjugation is monoidal) followed by
`JetRing.starConjEquiv` on the jet-ring factor (the real structure of the jet ring). On
pure tensors the composite is `f ⊗ₜ v ↦ star f ⊗ₜ v`, so `repConj` carries the conjugate
gauge matrix — the physicists' `ψ̄ ↦ ψ̄ U†`.

Being a representation is free: `LinearEquiv.conjRingEquiv` is a ring equivalence of
endomorphism rings, hence multiplicative. -/
noncomputable def repConj (rep : Representation ℂ G (JetRing ⊗[ℂ] V)) :
    Representation ℂ G (JetRing ⊗[ℂ] ConjModule V) where
  toFun U := LinearEquiv.conjRingEquiv
    ((ConjModule.tensorEquiv (k := ℂ) (M := JetRing) (N := V)).symm.trans
      (TensorProduct.congr JetRing.starConjEquiv (LinearEquiv.refl ℂ (ConjModule V))))
    (rep.conj U)
  map_one' := by rw [map_one, map_one]
  map_mul' U W := by rw [map_mul, map_mul]


/-- On pure tensors the conjugate jet action conjugates the jet factor: it is `rep`
evaluated at `star f ⊗ₜ v`, read back through the same identification. -/
lemma repConj_apply_tmul (rep : Representation ℂ G (JetRing ⊗[ℂ] V))
    (U : G) (f : JetRing) (v : V) :
    repConj rep U (f ⊗ₜ[ℂ] conjEquiv (k := ℂ) (M := V) v)
      = ((ConjModule.tensorEquiv (k := ℂ) (M := JetRing) (N := V)).symm.trans
          (TensorProduct.congr JetRing.starConjEquiv (LinearEquiv.refl ℂ (ConjModule V))))
        (conjEquiv (k := ℂ) (M := JetRing ⊗[ℂ] V) (rep U (star f ⊗ₜ[ℂ] v))) := rfl

/-- **The identification conjugates the jet-ring action.** Carrying a `V`-valued jet over
to the conjugate side turns multiplication by `star χ` into multiplication by `χ`: the
`star` on the jet-ring factor is exactly what absorbs the conjugation. -/
lemma tensorEquiv_congr_conjEquiv_smul (χ : JetRing) (y : JetRing ⊗[ℂ] V) :
    ((ConjModule.tensorEquiv (k := ℂ) (M := JetRing) (N := V)).symm.trans
        (TensorProduct.congr JetRing.starConjEquiv (LinearEquiv.refl ℂ (ConjModule V))))
          (conjEquiv (k := ℂ) (M := JetRing ⊗[ℂ] V) (star χ • y))
      = χ • ((ConjModule.tensorEquiv (k := ℂ) (M := JetRing) (N := V)).symm.trans
        (TensorProduct.congr JetRing.starConjEquiv (LinearEquiv.refl ℂ (ConjModule V))))
          (conjEquiv (k := ℂ) (M := JetRing ⊗[ℂ] V) y) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul g w =>
      rw [TensorProduct.smul_tmul', smul_eq_mul]
      simp only [LinearEquiv.trans_apply, ConjModule.tensorEquiv_symm_conjEquiv_tmul,
        TensorProduct.congr_tmul, LinearEquiv.refl_apply, JetRing.starConjEquiv_apply,
        LinearEquiv.symm_apply_apply, TensorProduct.smul_tmul', smul_eq_mul]
      rw [star_mul', star_star, mul_comm]
  | add a b ha hb =>
      rw [smul_add, map_add, map_add, ha, hb, map_add, map_add, smul_add]

/-- The conjugate jet action is the original one, read through the identification. On
a jet carried over to the conjugate side, `repConj rep U` is `rep U` applied on the
original side and carried over again. Everything about `repConj` beyond its definition
follows from this. -/
lemma repConj_apply_conjEquiv (rep : Representation ℂ G (JetRing ⊗[ℂ] V)) (U : G)
    (y : JetRing ⊗[ℂ] V) :
    repConj rep U (((ConjModule.tensorEquiv (k := ℂ) (M := JetRing) (N := V)).symm.trans
        (TensorProduct.congr JetRing.starConjEquiv (LinearEquiv.refl ℂ (ConjModule V))))
        (conjEquiv (k := ℂ) (M := JetRing ⊗[ℂ] V) y))
      = ((ConjModule.tensorEquiv (k := ℂ) (M := JetRing) (N := V)).symm.trans
          (TensorProduct.congr JetRing.starConjEquiv (LinearEquiv.refl ℂ (ConjModule V))))
        (conjEquiv (k := ℂ) (M := JetRing ⊗[ℂ] V) (rep U y)) := by
  show ((ConjModule.tensorEquiv (k := ℂ) (M := JetRing) (N := V)).symm.trans
      (TensorProduct.congr JetRing.starConjEquiv (LinearEquiv.refl ℂ (ConjModule V))))
        ((rep.conj U) ((((ConjModule.tensorEquiv (k := ℂ) (M := JetRing) (N := V)).symm.trans
      (TensorProduct.congr JetRing.starConjEquiv (LinearEquiv.refl ℂ (ConjModule V))))).symm
    (((ConjModule.tensorEquiv (k := ℂ) (M := JetRing) (N := V)).symm.trans
      (TensorProduct.congr JetRing.starConjEquiv (LinearEquiv.refl ℂ (ConjModule V))))
        (conjEquiv (k := ℂ) (M := JetRing ⊗[ℂ] V) y)))) = _
  rw [LinearEquiv.symm_apply_apply, Representation.conj_apply,
    LinearEquiv.symm_apply_apply]

/-- **The conjugate jet action is fibrewise-linear whenever the original is.** This is
what lets the coefficient machinery of `coeff_mul_of_smul_comm` be instantiated at
`ConjModule V`, giving the conjugate half of the symbol action. -/
lemma repConj_smul_comm
    {rep : Representation ℂ G (JetRing ⊗[ℂ] V)}
    (hlin : ∀ (U : G) (χ : JetRing) (z : JetRing ⊗[ℂ] V),
      rep U (χ • z) = χ • rep U z)
    (U : G) (χ : JetRing) (z : JetRing ⊗[ℂ] ConjModule V) :
    repConj rep U (χ • z) = χ • repConj rep U z := by
  obtain ⟨y, rfl⟩ : ∃ y : JetRing ⊗[ℂ] V,
      z = ((ConjModule.tensorEquiv (k := ℂ) (M := JetRing) (N := V)).symm.trans
        (TensorProduct.congr JetRing.starConjEquiv (LinearEquiv.refl ℂ (ConjModule V))))
          (conjEquiv (k := ℂ) (M := JetRing ⊗[ℂ] V) y) :=
    ⟨(conjEquiv (k := ℂ) (M := JetRing ⊗[ℂ] V)).symm ((((ConjModule.tensorEquiv (k := ℂ)
      (M := JetRing) (N := V)).symm.trans
        (TensorProduct.congr JetRing.starConjEquiv (LinearEquiv.refl ℂ
          (ConjModule V))))).symm z),
      by rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]⟩
  rw [← tensorEquiv_congr_conjEquiv_smul, repConj_apply_conjEquiv,
    repConj_apply_conjEquiv, hlin, tensorEquiv_congr_conjEquiv_smul]

/-- The identification of the conjugate of the jets with the jets of the conjugate is
natural in the value space. A linear map of value spaces acts on either side by the same
underlying map, so carrying a jet over to the conjugate side commutes with it. -/
lemma lTensor_conjEquiv_naturality (f : V →ₗ[ℂ] W) (y : JetRing ⊗[ℂ] V) :
    (LinearMap.lTensor JetRing (ConjModule.map (k := ℂ) f))
        (((ConjModule.tensorEquiv (k := ℂ) (M := JetRing) (N := V)).symm.trans
          (TensorProduct.congr JetRing.starConjEquiv (LinearEquiv.refl ℂ (ConjModule V))))
          (conjEquiv (k := ℂ) (M := JetRing ⊗[ℂ] V) y))
      = ((ConjModule.tensorEquiv (k := ℂ) (M := JetRing) (N := W)).symm.trans
          (TensorProduct.congr JetRing.starConjEquiv (LinearEquiv.refl ℂ (ConjModule W))))
        (conjEquiv (k := ℂ) (M := JetRing ⊗[ℂ] W) ((LinearMap.lTensor JetRing f) y)) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul g v =>
      simp only [LinearEquiv.trans_apply, ConjModule.tensorEquiv_symm_conjEquiv_tmul,
        TensorProduct.congr_tmul, LinearEquiv.refl_apply, JetRing.starConjEquiv_apply,
        LinearEquiv.symm_apply_apply, LinearMap.lTensor_tmul]
      rfl
  | add a b ha hb => simp only [map_add, ha, hb]

/-- The conjugate jet action is natural in the value space. A linear map of value
spaces intertwining two fibrewise jet actions intertwines the actions on the jets of the
conjugate fields, through the induced map of conjugate modules. This is what supplies the
conjugate half of the naturality of the gauge action on the jet component space, which
does not follow from the unconjugated half. -/
lemma lTensor_comp_repConj (repV : Representation ℂ G (JetRing ⊗[ℂ] V))
    (repW : Representation ℂ G (JetRing ⊗[ℂ] W)) (f : V →ₗ[ℂ] W)
    (hf : ∀ U : G, (LinearMap.lTensor JetRing f).comp (repV U)
      = (repW U).comp (LinearMap.lTensor JetRing f)) (U : G) :
    (LinearMap.lTensor JetRing (ConjModule.map (k := ℂ) f)).comp (repConj repV U)
      = (repConj repW U).comp (LinearMap.lTensor JetRing (ConjModule.map (k := ℂ) f)) := by
  refine LinearMap.ext fun z => ?_
  obtain ⟨y, rfl⟩ : ∃ y : JetRing ⊗[ℂ] V,
      z = ((ConjModule.tensorEquiv (k := ℂ) (M := JetRing) (N := V)).symm.trans
        (TensorProduct.congr JetRing.starConjEquiv (LinearEquiv.refl ℂ (ConjModule V))))
          (conjEquiv (k := ℂ) (M := JetRing ⊗[ℂ] V) y) :=
    ⟨(conjEquiv (k := ℂ) (M := JetRing ⊗[ℂ] V)).symm ((((ConjModule.tensorEquiv (k := ℂ)
      (M := JetRing) (N := V)).symm.trans
        (TensorProduct.congr JetRing.starConjEquiv (LinearEquiv.refl ℂ
          (ConjModule V))))).symm z),
      by rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]⟩
  rw [LinearMap.comp_apply, LinearMap.comp_apply, repConj_apply_conjEquiv,
    lTensor_conjEquiv_naturality, lTensor_conjEquiv_naturality, repConj_apply_conjEquiv,
    ← LinearMap.comp_apply, hf U, LinearMap.comp_apply]

/-- **The coefficient is determined by its action on constants.** For finite-dimensional
`V` the canonical evaluation `JetRing ⊗ (V →ₗ W) → (V →ₗ JetRing ⊗ W)` is injective. -/
lemma lift_injective [Module.Free ℂ V] [Module.Finite ℂ V]
    {x y : JetRing ⊗[ℂ] (V →ₗ[ℂ] W)}
    (h : ∀ v : V, TensorProduct.lift ((LinearMap.llcomp ℂ V W (JetRing ⊗[ℂ] W)).comp
      (TensorProduct.mk ℂ JetRing W)) x v = TensorProduct.lift ((LinearMap.llcomp ℂ V W
        (JetRing ⊗[ℂ] W)).comp
      (TensorProduct.mk ℂ JetRing W)) y v) : x = y := by
  obtain ⟨G, rfl⟩ := ((TensorProduct.leftComm ℂ (Module.Dual ℂ V) JetRing W).trans
      (TensorProduct.congr (LinearEquiv.refl ℂ JetRing)
        (dualTensorHomEquiv ℂ V W))).surjective x
  obtain ⟨G', rfl⟩ := ((TensorProduct.leftComm ℂ (Module.Dual ℂ V) JetRing W).trans
      (TensorProduct.congr (LinearEquiv.refl ℂ JetRing)
        (dualTensorHomEquiv ℂ V W))).surjective y
  refine congrArg _ ((dualTensorHomEquiv ℂ V (JetRing ⊗[ℂ] W)).injective
    (LinearMap.ext fun v => ?_))
  rw [show (dualTensorHomEquiv ℂ V (JetRing ⊗[ℂ] W)) G
        = dualTensorHom ℂ V (JetRing ⊗[ℂ] W) G from rfl,
    show (dualTensorHomEquiv ℂ V (JetRing ⊗[ℂ] W)) G'
        = dualTensorHom ℂ V (JetRing ⊗[ℂ] W) G' from rfl,
    ← lift_congr_leftComm, ← lift_congr_leftComm]
  exact h v

/-- **The coefficient of a fibrewise gauge action.** For finite-dimensional `V`, the
restriction of `rep U` to constant jets is an element of `JetRing ⊗ End V` — a matrix of
power series, obtained canonically from `dualTensorHomEquiv` rather than from a basis. -/
noncomputable def jetCoeff [Module.Free ℂ V] [Module.Finite ℂ V]
    (rep : Representation ℂ G (JetRing ⊗[ℂ] V)) (U : G) :
    JetRing ⊗[ℂ] Module.End ℂ V :=
  ((TensorProduct.leftComm ℂ (Module.Dual ℂ V) JetRing V).trans
      (TensorProduct.congr (LinearEquiv.refl ℂ JetRing) (dualTensorHomEquiv ℂ V V)))
    ((dualTensorHomEquiv ℂ V (JetRing ⊗[ℂ] V)).symm ((rep U).comp jetOfConstant))

/-- The coefficient reproduces `rep U` on constant jets. -/
lemma jetCoeff_spec [Module.Free ℂ V] [Module.Finite ℂ V]
    (rep : Representation ℂ G (JetRing ⊗[ℂ] V)) (U : G) (v : V) :
    TensorProduct.lift ((LinearMap.llcomp ℂ V V (JetRing ⊗[ℂ] V)).comp
      (TensorProduct.mk ℂ JetRing V)) (jetCoeff rep U) v = rep U (jetOfConstant v) := by
  rw [jetCoeff, LinearEquiv.trans_apply, lift_congr_leftComm,
    show dualTensorHom ℂ V (JetRing ⊗[ℂ] V)
        ((dualTensorHomEquiv ℂ V (JetRing ⊗[ℂ] V)).symm ((rep U).comp jetOfConstant))
        = (rep U).comp jetOfConstant from
      (dualTensorHomEquiv ℂ V (JetRing ⊗[ℂ] V)).apply_symm_apply _]
  rfl

/-!

## Naturality of the coefficient in the value space

A linear map `f : V →ₗ W` of value spaces intertwining two fibrewise jet actions relates
their coefficients, but not as an equation between elements of two different modules: the
comparison takes place in `JetRing ⊗ (V →ₗ W)`, into which `JetRing ⊗ End V` maps by
postcomposition with `f` and `JetRing ⊗ End W` by precomposition. The two images agree,
and that single identity is what carries the gauge action across a map of value spaces.

-/

/-- Postcomposing a coefficient with `f` evaluates as applying `f` to the value. -/
lemma lift_lTensor_llcomp (f : V →ₗ[ℂ] W) (x : JetRing ⊗[ℂ] Module.End ℂ V) (v : V) :
    TensorProduct.lift ((LinearMap.llcomp ℂ V W (JetRing ⊗[ℂ] W)).comp
        (TensorProduct.mk ℂ JetRing W))
        (LinearMap.lTensor JetRing (LinearMap.llcomp ℂ V V W f) x) v
      = LinearMap.lTensor JetRing f
        (TensorProduct.lift ((LinearMap.llcomp ℂ V V (JetRing ⊗[ℂ] V)).comp
          (TensorProduct.mk ℂ JetRing V)) x v) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul g S => rfl
  | add a b ha hb => simp only [map_add, LinearMap.add_apply, ha, hb]

/-- Precomposing a coefficient with `f` evaluates as evaluating at the image of the
  argument. -/
lemma lift_lTensor_lcomp (f : V →ₗ[ℂ] W) (y : JetRing ⊗[ℂ] Module.End ℂ W) (v : V) :
    TensorProduct.lift ((LinearMap.llcomp ℂ V W (JetRing ⊗[ℂ] W)).comp
        (TensorProduct.mk ℂ JetRing W))
        (LinearMap.lTensor JetRing (LinearMap.lcomp ℂ W f) y) v
      = TensorProduct.lift ((LinearMap.llcomp ℂ W W (JetRing ⊗[ℂ] W)).comp
        (TensorProduct.mk ℂ JetRing W)) y (f v) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul g T => rfl
  | add a b ha hb => simp only [map_add, LinearMap.add_apply, ha, hb]

/-- The coefficient of a fibrewise action is natural in the value space. If `f` maps
the values of one field to the values of another and intertwines their jet actions, then
the coefficient of the first followed by `f` is `f` followed by the coefficient of the
second, as elements of `JetRing ⊗ (V →ₗ W)`. Both value spaces have to be
finite-dimensional, since both coefficients have to exist; no fibrewise-linearity is used
here, the coefficient being defined for any action. -/
lemma jetCoeff_naturality [Module.Free ℂ V] [Module.Finite ℂ V]
    [Module.Free ℂ W] [Module.Finite ℂ W]
    (repV : Representation ℂ G (JetRing ⊗[ℂ] V))
    (repW : Representation ℂ G (JetRing ⊗[ℂ] W)) (f : V →ₗ[ℂ] W)
    (hf : ∀ U : G, (LinearMap.lTensor JetRing f).comp (repV U)
      = (repW U).comp (LinearMap.lTensor JetRing f)) (U : G) :
    LinearMap.lTensor JetRing (LinearMap.llcomp ℂ V V W f) (jetCoeff repV U)
      = LinearMap.lTensor JetRing (LinearMap.lcomp ℂ W f) (jetCoeff repW U) := by
  refine lift_injective fun v => ?_
  rw [lift_lTensor_llcomp, lift_lTensor_lcomp, jetCoeff_spec, jetCoeff_spec,
    ← LinearMap.comp_apply, hf U]
  rfl

end JetComponentSpace
