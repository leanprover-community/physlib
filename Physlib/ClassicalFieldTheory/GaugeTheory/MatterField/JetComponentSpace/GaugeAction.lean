/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module


public import Physlib.ClassicalFieldTheory.GaugeTheory.MatterField.JetComponentSpace.Basic
public import Physlib.ClassicalFieldTheory.JetAlgebra.JetRep
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
