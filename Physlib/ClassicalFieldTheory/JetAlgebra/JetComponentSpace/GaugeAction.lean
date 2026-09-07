/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module


public import Physlib.ClassicalFieldTheory.JetAlgebra.JetComponentSpace.Basic
/-!
# The gauge action on the jet component space

## i. Overview

For a matter field valued in `V` with an action of a group `G` on its jets
`JetRing ⊗[ℂ] V`, this file constructs the induced action of `G` on the jet component
space. Here `G` is any group — for the Standard Model it is the jet gauge group
`JetGaugeGroupI`, but nothing here depends on that.

The construction needs two hypotheses on the jet action `rep`:

* `hlin` — that `rep` is *fibrewise*, `rep U (χ • z) = χ • rep U z`, the statement that a
  gauge transformation acts on the values of the field over the identity on spacetime.
  This is what makes the induced action local (a finite Leibniz convolution) and what
  makes `rep` determined by its restriction to constant jets.
* finite dimensionality of `V`, which makes that restriction a *matrix of power series*,
  an element of `JetRing ⊗ End V`.

## ii. Key results

- `JetComponentSpace.jetCoeff` : the coefficient of a fibrewise action, in `JetRing ⊗ End V`.
- `JetComponentSpace.coeff_mul_of_smul_comm` : the coefficient is multiplicative.
- `JetComponentSpace.symbolAction`, `symbolAction_mul` : its action on symbols, an
  anti-homomorphism.
- `JetComponentSpace.repDual` : the induced action on the unconjugated symbols.
- `JetComponentSpace.repConj`, `repConj_smul_comm` : the action on the jets of the
  conjugate field.
- `JetComponentSpace.repJet` : the action on the full component space.

-/

@[expose] public section

namespace JetComponentSpace

open Matrix MatrixGroups TensorProduct

variable {V : Type _} [AddCommGroup V] [Module ℂ V]
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
canonical `JetRing ⊗ End V → (V →ₗ JetRing ⊗ V)` is inverted by reassociating the
contraction `Dual V ⊗ (JetRing ⊗ V) ≃ JetRing ⊗ (Dual V ⊗ V) ≃ JetRing ⊗ End V`. This is
the finite-rank input, obtained from `dualTensorHomEquiv` rather than from a basis. -/
lemma lift_congr_leftComm [Module.Free ℂ V] [Module.Finite ℂ V]
    (G : Module.Dual ℂ V ⊗[ℂ] (JetRing ⊗[ℂ] V)) (v : V) :
    TensorProduct.lift ((LinearMap.llcomp ℂ V V (JetRing ⊗[ℂ] V)).comp
        (TensorProduct.mk ℂ JetRing V))
        ((TensorProduct.congr (LinearEquiv.refl ℂ JetRing) (dualTensorHomEquiv ℂ V V))
          (TensorProduct.leftComm ℂ (Module.Dual ℂ V) JetRing V G)) v
      = dualTensorHom ℂ V (JetRing ⊗[ℂ] V) G v := by
  induction G using TensorProduct.induction_on with
  | zero => simp
  | tmul phi z =>
      induction z using TensorProduct.induction_on with
      | zero => simp
      | tmul g w =>
          rw [TensorProduct.leftComm_tmul, TensorProduct.congr_tmul,
            LinearEquiv.refl_apply]
          show g ⊗ₜ[ℂ] (dualTensorHomEquiv ℂ V V (phi ⊗ₜ[ℂ] w)) v = _
          rw [show dualTensorHomEquiv ℂ V V (phi ⊗ₜ[ℂ] w)
              = dualTensorHom ℂ V V (phi ⊗ₜ[ℂ] w) from rfl,
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

/-- **The conjugate jet action is fibrewise-linear whenever the original is.** This is
what lets the coefficient machinery of `coeff_mul_of_smul_comm` be instantiated at
`ConjModule V`, giving the conjugate half of the symbol action. -/
lemma repConj_smul_comm
    {rep : Representation ℂ G (JetRing ⊗[ℂ] V)}
    (hlin : ∀ (U : G) (χ : JetRing) (z : JetRing ⊗[ℂ] V),
      rep U (χ • z) = χ • rep U z)
    (U : G) (χ : JetRing) (z : JetRing ⊗[ℂ] ConjModule V) :
    repConj rep U (χ • z) = χ • repConj rep U z := by
  have key : ∀ w : JetRing ⊗[ℂ] V,
      repConj rep U (((ConjModule.tensorEquiv (k := ℂ) (M := JetRing) (N := V)).symm.trans
        (TensorProduct.congr JetRing.starConjEquiv (LinearEquiv.refl ℂ (ConjModule V))))
          (conjEquiv (k := ℂ) (M := JetRing ⊗[ℂ] V) w))
        = ((ConjModule.tensorEquiv (k := ℂ) (M := JetRing) (N := V)).symm.trans
        (TensorProduct.congr JetRing.starConjEquiv (LinearEquiv.refl ℂ (ConjModule V))))
          (conjEquiv (k := ℂ) (M := JetRing ⊗[ℂ] V) (rep U w)) := by
    intro w
    show ((ConjModule.tensorEquiv (k := ℂ) (M := JetRing) (N := V)).symm.trans
        (TensorProduct.congr JetRing.starConjEquiv (LinearEquiv.refl ℂ (ConjModule V))))
          ((rep.conj U) ((((ConjModule.tensorEquiv (k := ℂ) (M := JetRing) (N := V)).symm.trans
        (TensorProduct.congr JetRing.starConjEquiv (LinearEquiv.refl ℂ (ConjModule V))))).symm
      (((ConjModule.tensorEquiv (k := ℂ) (M := JetRing) (N := V)).symm.trans
        (TensorProduct.congr JetRing.starConjEquiv (LinearEquiv.refl ℂ (ConjModule V))))
          (conjEquiv (k := ℂ) (M := JetRing ⊗[ℂ] V) w)))) = _
    rw [LinearEquiv.symm_apply_apply, Representation.conj_apply,
      LinearEquiv.symm_apply_apply]
  obtain ⟨y, rfl⟩ : ∃ y : JetRing ⊗[ℂ] V,
      z = ((ConjModule.tensorEquiv (k := ℂ) (M := JetRing) (N := V)).symm.trans
        (TensorProduct.congr JetRing.starConjEquiv (LinearEquiv.refl ℂ (ConjModule V))))
          (conjEquiv (k := ℂ) (M := JetRing ⊗[ℂ] V) y) :=
    ⟨(conjEquiv (k := ℂ) (M := JetRing ⊗[ℂ] V)).symm ((((ConjModule.tensorEquiv (k := ℂ)
      (M := JetRing) (N := V)).symm.trans
        (TensorProduct.congr JetRing.starConjEquiv (LinearEquiv.refl ℂ
          (ConjModule V))))).symm z), by simp⟩
  rw [← tensorEquiv_congr_conjEquiv_smul, key, key, hlin,
    tensorEquiv_congr_conjEquiv_smul]

/-- **The coefficient is determined by its action on constants.** For finite-dimensional
`V` the canonical evaluation `JetRing ⊗ End V → (V →ₗ JetRing ⊗ V)` is injective. -/
lemma lift_injective [Module.Free ℂ V] [Module.Finite ℂ V]
    {x y : JetRing ⊗[ℂ] Module.End ℂ V}
    (h : ∀ v : V, TensorProduct.lift ((LinearMap.llcomp ℂ V V (JetRing ⊗[ℂ] V)).comp
      (TensorProduct.mk ℂ JetRing V)) x v = TensorProduct.lift ((LinearMap.llcomp ℂ V V
        (JetRing ⊗[ℂ] V)).comp
      (TensorProduct.mk ℂ JetRing V)) y v) : x = y := by
  obtain ⟨G, rfl⟩ := ((TensorProduct.leftComm ℂ (Module.Dual ℂ V) JetRing V).trans
      (TensorProduct.congr (LinearEquiv.refl ℂ JetRing) (dualTensorHomEquiv ℂ V V))).surjective x
  obtain ⟨G', rfl⟩ := ((TensorProduct.leftComm ℂ (Module.Dual ℂ V) JetRing V).trans
      (TensorProduct.congr (LinearEquiv.refl ℂ JetRing) (dualTensorHomEquiv ℂ V V))).surjective y
  refine congrArg _ ((dualTensorHomEquiv ℂ V (JetRing ⊗[ℂ] V)).injective
    (LinearMap.ext fun v => ?_))
  rw [show (dualTensorHomEquiv ℂ V (JetRing ⊗[ℂ] V)) G
        = dualTensorHom ℂ V (JetRing ⊗[ℂ] V) G from rfl,
    show (dualTensorHomEquiv ℂ V (JetRing ⊗[ℂ] V)) G'
        = dualTensorHom ℂ V (JetRing ⊗[ℂ] V) G' from rfl,
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

/-- **The action of a coefficient on the symbols.** A coefficient `g ⊗ T` acts by
`jetRingAction g` on the derivative label — the Leibniz convolution redistributing
derivatives between the gauge transformation and the field — and by the transpose `Tᵀ` on
the target index. -/
noncomputable def symbolAction :
    (JetRing ⊗[ℂ] Module.End ℂ V) →ₗ[ℂ]
      Module.End ℂ (DerivAlgebraComplex ⊗[ℂ] Module.Dual ℂ V) :=
  TensorProduct.lift
    { toFun := fun g =>
        { toFun := fun T => TensorProduct.map (DerivAlgebraComplex.jetRingAction g)
            (Module.Dual.transpose T)
          map_add' := fun T₁ T₂ => by rw [map_add, TensorProduct.map_add_right]
          map_smul' := fun c T => by
            rw [map_smul, TensorProduct.map_smul_right, RingHom.id_apply] }
      map_add' := fun g₁ g₂ => by
        refine LinearMap.ext fun T => ?_
        show TensorProduct.map (DerivAlgebraComplex.jetRingAction (g₁ + g₂)) _ = _
        rw [DerivAlgebraComplex.jetRingAction_add, TensorProduct.map_add_left]
        rfl
      map_smul' := fun c g => by
        refine LinearMap.ext fun T => ?_
        show TensorProduct.map (DerivAlgebraComplex.jetRingAction (c • g)) _ = _
        rw [show DerivAlgebraComplex.jetRingAction (c • g)
              = c • DerivAlgebraComplex.jetRingAction g from by
            rw [Algebra.smul_def, MvPowerSeries.algebraMap_apply,
              DerivAlgebraComplex.jetRingAction_mul, DerivAlgebraComplex.jetRingAction_C,
              LinearMap.smul_comp, LinearMap.id_comp, Algebra.algebraMap_self_apply],
          TensorProduct.map_smul_left]
        rfl }

@[simp]
lemma symbolAction_tmul (g : JetRing) (T : Module.End ℂ V) :
    symbolAction (g ⊗ₜ[ℂ] T)
      = TensorProduct.map (DerivAlgebraComplex.jetRingAction g) (Module.Dual.transpose T) :=
  rfl

/-- **A coefficient acts on the undifferentiated symbol through its value at the base
point.** On `1 ⊗ φ` — the symbol `ψ_φ` carrying no derivatives — only the constant term of
the power-series coefficient survives, so the result is again undifferentiated and the
target index is acted on by the transpose of the base-point value. -/
lemma symbolAction_one_tmul (c : JetRing ⊗[ℂ] Module.End ℂ V) (φ : Module.Dual ℂ V) :
    symbolAction c ((1 : DerivAlgebraComplex) ⊗ₜ[ℂ] φ)
      = (1 : DerivAlgebraComplex) ⊗ₜ[ℂ]
        Module.Dual.transpose (jetEval ∘ₗ TensorProduct.lift
          ((LinearMap.llcomp ℂ V V (JetRing ⊗[ℂ] V)).comp
            (TensorProduct.mk ℂ JetRing V)) c) φ := by
  induction c using TensorProduct.induction_on with
  | zero => simp
  | add c₁ c₂ h₁ h₂ =>
    rw [map_add, LinearMap.add_apply, h₁, h₂, map_add, LinearMap.comp_add, map_add,
      LinearMap.add_apply, TensorProduct.tmul_add]
  | tmul g T =>
    rw [symbolAction_tmul, TensorProduct.map_tmul,
      DerivAlgebraComplex.jetRingAction_apply_one, TensorProduct.smul_tmul]
    congr 1
    refine LinearMap.ext fun v => ?_
    simp [Module.Dual.transpose]

/-- **The gauge action on the symbols.** Given a fibrewise gauge action on the jets of a
`V`-valued field, this is the induced (contragredient) action on the derivative symbols
`∂_s ψ_α`, which span `DerivAlgebraComplex ⊗ Module.Dual ℂ V`.

Multiplicativity is bookkeeping: `coeff_mul_of_smul_comm` makes the coefficient
multiplicative, `symbolAction_mul` makes its action an anti-homomorphism, and the inverse
flips that back. -/
noncomputable def repDual [Module.Free ℂ V] [Module.Finite ℂ V]
    (rep : Representation ℂ G (JetRing ⊗[ℂ] V))
    (hlin : ∀ (U : G) (χ : JetRing) (z : JetRing ⊗[ℂ] V),
      rep U (χ • z) = χ • rep U z) :
    Representation ℂ G (DerivAlgebraComplex ⊗[ℂ] Module.Dual ℂ V) where
  toFun U := symbolAction (jetCoeff rep U⁻¹)
  map_one' := by
    have h1 : jetCoeff rep (1 : G)⁻¹ = 1 := by
      refine lift_injective fun v => ?_
      rw [jetCoeff_spec rep]
      show rep (1 : G)⁻¹ ((1 : JetRing) ⊗ₜ[ℂ] v) = (1 : JetRing) ⊗ₜ[ℂ] v
      rw [inv_one, map_one]
      rfl
    rw [h1, Algebra.TensorProduct.one_def, symbolAction_tmul,
      DerivAlgebraComplex.jetRingAction_one,
      show Module.Dual.transpose (1 : Module.End ℂ V) = LinearMap.id from rfl,
      TensorProduct.map_id]
    rfl
  map_mul' U W := by
    have hmul : jetCoeff rep (U * W)⁻¹ = jetCoeff rep W⁻¹ * jetCoeff rep U⁻¹ := by
      refine lift_injective fun v => ?_
      rw [jetCoeff_spec,
        coeff_mul_of_smul_comm hlin (fun A => jetCoeff rep A) (jetCoeff_spec rep) W⁻¹ U⁻¹ v,
        _root_.mul_inv_rev]
    rw [hmul, symbolAction_mul symbolAction (fun g T => rfl)]
    rfl

/-- **The undifferentiated symbol transforms by the value of the gauge transformation at
the base point.** No derivative of the gauge jet contributes: the symbol `ψ_φ` is acted on
by the contragredient of `rep U⁻¹` restricted to constant jets and evaluated at the base
point. -/
lemma repDual_one_tmul [Module.Free ℂ V] [Module.Finite ℂ V]
    (rep : Representation ℂ G (JetRing ⊗[ℂ] V))
    (hlin : ∀ (U : G) (χ : JetRing) (z : JetRing ⊗[ℂ] V),
      rep U (χ • z) = χ • rep U z)
    (U : G) (φ : Module.Dual ℂ V) :
    repDual rep hlin U ((1 : DerivAlgebraComplex) ⊗ₜ[ℂ] φ)
      = (1 : DerivAlgebraComplex) ⊗ₜ[ℂ]
        Module.Dual.transpose (jetEval ∘ₗ (rep U⁻¹).comp jetOfConstant) φ := by
  have h : jetEval ∘ₗ TensorProduct.lift ((LinearMap.llcomp ℂ V V (JetRing ⊗[ℂ] V)).comp
        (TensorProduct.mk ℂ JetRing V)) (jetCoeff rep U⁻¹)
      = jetEval ∘ₗ (rep U⁻¹).comp jetOfConstant :=
    LinearMap.ext fun v => congrArg jetEval (jetCoeff_spec rep U⁻¹ v)
  rw [show repDual rep hlin U = symbolAction (jetCoeff rep U⁻¹) from rfl,
    symbolAction_one_tmul, h]


/-- **The gauge action on the jet component space.** Given a fibrewise gauge action on the
jets of a `V`-valued field, this is the induced action on the full space of component
functions — the symbols `∂_s ψ_α` together with their conjugates `∂_s ψ̄_α`.

The unconjugated half is `repDual rep`, the contragredient action on the symbols. The
conjugate half is the *same* construction applied to `repConj rep`, the action on the jets
of the conjugate field; `repConj_smul_comm` supplies the fibrewise-linearity it needs. The
conjugate half therefore carries `star` of the gauge matrix, which is the physicists'
`ψ̄ ↦ ψ̄ U†`. -/
noncomputable def repJet [Module.Free ℂ V] [Module.Finite ℂ V]
    (rep : Representation ℂ G (JetRing ⊗[ℂ] V))
    (hlin : ∀ (U : G) (χ : JetRing) (z : JetRing ⊗[ℂ] V),
      rep U (χ • z) = χ • rep U z) :
    Representation ℂ G (JetComponentSpace V) :=
  (repDual rep hlin).prod (repDual (repConj rep) (repConj_smul_comm hlin))

@[simp]
lemma repJet_fst [Module.Free ℂ V] [Module.Finite ℂ V]
    (rep : Representation ℂ G (JetRing ⊗[ℂ] V))
    (hlin : ∀ (U : G) (χ : JetRing) (z : JetRing ⊗[ℂ] V),
      rep U (χ • z) = χ • rep U z)
    (U : G) (x : JetComponentSpace V) :
    (repJet rep hlin U x).1 = repDual rep hlin U x.1 := rfl

@[simp]
lemma repJet_snd [Module.Free ℂ V] [Module.Finite ℂ V]
    (rep : Representation ℂ G (JetRing ⊗[ℂ] V))
    (hlin : ∀ (U : G) (χ : JetRing) (z : JetRing ⊗[ℂ] V),
      rep U (χ • z) = χ • rep U z)
    (U : G) (x : JetComponentSpace V) :
    (repJet rep hlin U x).2
      = repDual (repConj rep) (repConj_smul_comm hlin) U x.2 := rfl

end JetComponentSpace
