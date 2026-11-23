/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jinzheng Li, Nathaneal Sajan, Joseph Tooby-Smith
-/
module


public import PhyslibAlpha.ClassicalFieldTheory.GaugeTheory.MatterField.FieldDerivSpace.Basic
/-!
# The gauge action on the field-derivative space

The action of gauge jets on the derivative symbols of a matter field and their conjugates.

## i. Overview

For a matter field valued in `V` with an action `rep` of the jet gauge group
`G.gaugeJetGroup` on its jets `SpaceTimeAlgebra ⊗[ℂ] V`, this file constructs the induced
action of `G.gaugeJetGroup` on the field-derivative space. The construction needs two
hypotheses on `rep`.

* It is fibrewise, `rep U (χ • z) = χ • rep U z`. A gauge transformation acts on the values
  of the field over the identity on spacetime. This makes the induced action local (a finite
  Leibniz convolution) and makes `rep` determined by its restriction to constant jets.
* The value space `V` is finite-dimensional, so that this restriction is a matrix of power
  series, the coefficient `FieldDerivSpace.jetCoeff rep U` in `SpaceTimeAlgebra ⊗ End V`.

The coefficient, its multiplicativity and the conjugate action `FieldDerivSpace.repConj` are
set up in `PhyslibAlpha.ClassicalFieldTheory.GaugeTheory.LocalFieldAlgebra.JetRep`. Here a
coefficient acts on the symbols by `symbolAction`, the induced action on the unconjugated
symbols is `repDual`, and the action on the whole field-derivative space of a matter field,
conjugate symbols included, is `repJet`. All of these are natural in the value space.

## ii. Key results

- `FieldDerivSpace.symbolAction` : the action of a coefficient on the symbols.
- `FieldDerivSpace.symbolAction_one_tmul` : a coefficient acts on the undifferentiated symbol
  through its value at the base point.
- `FieldDerivSpace.repDual` : the gauge action on the symbols.
- `FieldDerivSpace.repJet` : the gauge action on the field-derivative space of a matter field.
- `FieldDerivSpace.comap_comp_repDual`, `FieldDerivSpace.comap_comp_repJet` : both actions are
  natural in the value space.

## iii. Table of contents

- A. The action of a coefficient on the symbols
- B. The gauge action on the field-derivative space
- C. Naturality in the value space

## iv. References

* None.

-/

@[expose] public section

namespace FieldDerivSpace

open Matrix MatrixGroups TensorProduct

variable {V : Type _} [AddCommGroup V] [Module ℂ V]
variable {W : Type _} [AddCommGroup W] [Module ℂ W]
variable {κ : Type} [Fintype κ] [DecidableEq κ] {G : GlobalGaugeGroup κ}

/-!

## A. The action of a coefficient on the symbols

-/

/-- The action of a coefficient on the symbols. A coefficient `g ⊗ T` acts by
`jetRingAction g` on the derivative label — the Leibniz convolution redistributing
derivatives between the gauge transformation and the field — and by the transpose `Tᵀ` on
the target index.

A coefficient is allowed to change the value space, so that the symbol action of an
endomorphism and the pullback along a map of value spaces are the same construction; at
`W = V` this is the action on `Module.End ℂ (SpaceTimeDerivAlgebraℂ ⊗ Module.Dual ℂ V)` that
`repDual` uses. -/
noncomputable def symbolAction :
    (SpaceTimeAlgebra ⊗[ℂ] (V →ₗ[ℂ] W)) →ₗ[ℂ]
      ((SpaceTimeDerivAlgebraℂ ⊗[ℂ] Module.Dual ℂ W) →ₗ[ℂ]
        (SpaceTimeDerivAlgebraℂ ⊗[ℂ] Module.Dual ℂ V)) :=
  TensorProduct.lift
    { toFun := fun g =>
        { toFun := fun T => TensorProduct.map (SpaceTimeDerivAlgebraℂ.jetRingAction g)
            (Module.Dual.transpose T)
          map_add' := fun T₁ T₂ => by rw [map_add, TensorProduct.map_add_right]
          map_smul' := fun c T => by
            rw [map_smul, TensorProduct.map_smul_right, RingHom.id_apply] }
      map_add' := fun g₁ g₂ => by
        refine LinearMap.ext fun T => ?_
        show TensorProduct.map (SpaceTimeDerivAlgebraℂ.jetRingAction (g₁ + g₂)) _ = _
        rw [SpaceTimeDerivAlgebraℂ.jetRingAction_add, TensorProduct.map_add_left]
        rfl
      map_smul' := fun c g => by
        refine LinearMap.ext fun T => ?_
        show TensorProduct.map (SpaceTimeDerivAlgebraℂ.jetRingAction (c • g)) _ = _
        rw [show SpaceTimeDerivAlgebraℂ.jetRingAction (c • g)
              = c • SpaceTimeDerivAlgebraℂ.jetRingAction g from by
            rw [Algebra.smul_def, MvPowerSeries.algebraMap_apply,
              SpaceTimeDerivAlgebraℂ.jetRingAction_mul, SpaceTimeDerivAlgebraℂ.jetRingAction_C,
              LinearMap.smul_comp, LinearMap.id_comp, Algebra.algebraMap_self_apply],
          TensorProduct.map_smul_left]
        rfl }

@[simp]
lemma symbolAction_tmul (g : SpaceTimeAlgebra) (T : V →ₗ[ℂ] W) :
    symbolAction (g ⊗ₜ[ℂ] T)
      = TensorProduct.map (SpaceTimeDerivAlgebraℂ.jetRingAction g) (Module.Dual.transpose T) :=
  rfl

/-- A coefficient acts on the undifferentiated symbol through its value at the base
point. On `1 ⊗ φ` — the symbol `ψ_φ` carrying no derivatives — only the constant term of
the power-series coefficient survives, so the result is again undifferentiated and the
target index is acted on by the transpose of the base-point value. -/
lemma symbolAction_one_tmul (c : SpaceTimeAlgebra ⊗[ℂ] Module.End ℂ V) (φ : Module.Dual ℂ V) :
    symbolAction c ((1 : SpaceTimeDerivAlgebraℂ) ⊗ₜ[ℂ] φ)
      = (1 : SpaceTimeDerivAlgebraℂ) ⊗ₜ[ℂ]
        Module.Dual.transpose (jetEval ∘ₗ TensorProduct.lift
          ((LinearMap.llcomp ℂ V V (SpaceTimeAlgebra ⊗[ℂ] V)).comp
            (TensorProduct.mk ℂ SpaceTimeAlgebra V)) c) φ := by
  induction c using TensorProduct.inductionOn with
  | add c₁ c₂ h₁ h₂ =>
    rw [map_add, LinearMap.add_apply, h₁, h₂, map_add, LinearMap.comp_add, map_add,
      LinearMap.add_apply, TensorProduct.tmul_add]
  | tmul g T =>
    rw [symbolAction_tmul, TensorProduct.map_tmul,
      SpaceTimeDerivAlgebraℂ.jetRingAction_apply_one, TensorProduct.smul_tmul]
    congr 1
    refine LinearMap.ext fun v => ?_
    simp [Module.Dual.transpose]

/-!

## B. The gauge action on the field-derivative space

-/

/-- The gauge action on the symbols. Given a fibrewise gauge action on the jets of a
`V`-valued field, this is the induced (contragredient) action on the derivative symbols
`∂_s ψ_α`, which span `SpaceTimeDerivAlgebraℂ ⊗ Module.Dual ℂ V`.

Multiplicativity is bookkeeping. `coeff_mul_of_smul_comm` makes the coefficient
multiplicative, `symbolAction_mul` makes its action an anti-homomorphism, and the inverse
flips that back. -/
noncomputable def repDual [Module.Free ℂ V] [Module.Finite ℂ V]
    (rep : Representation ℂ G.gaugeJetGroup (SpaceTimeAlgebra ⊗[ℂ] V))
    (hlin : ∀ (U : G.gaugeJetGroup) (χ : SpaceTimeAlgebra) (z : SpaceTimeAlgebra ⊗[ℂ] V),
      rep U (χ • z) = χ • rep U z) :
    Representation ℂ G.gaugeJetGroup (SpaceTimeDerivAlgebraℂ ⊗[ℂ] Module.Dual ℂ V) where
  toFun U := symbolAction (jetCoeff rep U⁻¹)
  map_one' := by
    have h1 : jetCoeff rep (1 : G.gaugeJetGroup)⁻¹ = 1 := by
      refine lift_injective fun v => ?_
      rw [jetCoeff_spec rep]
      show rep (1 : G.gaugeJetGroup)⁻¹ ((1 : SpaceTimeAlgebra) ⊗ₜ[ℂ] v) =
        (1 : SpaceTimeAlgebra) ⊗ₜ[ℂ] v
      rw [inv_one, map_one]
      rfl
    rw [h1, Algebra.TensorProduct.one_def, symbolAction_tmul,
      SpaceTimeDerivAlgebraℂ.jetRingAction_one,
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

/-- The undifferentiated symbol transforms by the value of the gauge transformation at
the base point. No derivative of the gauge jet contributes, and the symbol `ψ_φ` is acted on
by the contragredient of `rep U⁻¹` restricted to constant jets and evaluated at the base
point. -/
lemma repDual_one_tmul [Module.Free ℂ V] [Module.Finite ℂ V]
    (rep : Representation ℂ G.gaugeJetGroup (SpaceTimeAlgebra ⊗[ℂ] V))
    (hlin : ∀ (U : G.gaugeJetGroup) (χ : SpaceTimeAlgebra) (z : SpaceTimeAlgebra ⊗[ℂ] V),
      rep U (χ • z) = χ • rep U z)
    (U : G.gaugeJetGroup) (φ : Module.Dual ℂ V) :
    repDual rep hlin U ((1 : SpaceTimeDerivAlgebraℂ) ⊗ₜ[ℂ] φ)
      = (1 : SpaceTimeDerivAlgebraℂ) ⊗ₜ[ℂ]
        Module.Dual.transpose (jetEval ∘ₗ (rep U⁻¹).comp jetOfConstant) φ := by
  have h : jetEval ∘ₗ TensorProduct.lift ((LinearMap.llcomp ℂ V V (SpaceTimeAlgebra ⊗[ℂ] V)).comp
        (TensorProduct.mk ℂ SpaceTimeAlgebra V)) (jetCoeff rep U⁻¹)
      = jetEval ∘ₗ (rep U⁻¹).comp jetOfConstant :=
    LinearMap.ext fun v => congrArg jetEval (jetCoeff_spec rep U⁻¹ v)
  rw [show repDual rep hlin U = symbolAction (jetCoeff rep U⁻¹) from rfl,
    symbolAction_one_tmul, h]

/-- The gauge action on the field-derivative space. The induced action of the jets of
gauge transformations on the full space of component functions of the matter field `M` —
the symbols `∂_s ψ_α` together with their conjugates `∂_s ψ̄_α`.

The unconjugated half is `repDual M.repJet`, the contragredient action on the symbols. The
conjugate half is the same construction applied to `repConj M.repJet`, the action on the
jets of the conjugate field; `repConj_smul_comm` supplies the fibrewise-linearity it needs.
The conjugate half therefore carries `star` of the gauge matrix, which is the physicists'
`ψ̄ ↦ ψ̄ U†`.

Everything the construction needs is carried by the matter field, namely the jet action `M.repJet`,
its fibrewise linearity `M.repJet_smul`, and the freeness and finiteness of `M.V`. Taking
the matter field rather than a bare value space is what removes all three from the
argument list. -/
noncomputable def repJet (M : G.MatterField) :
    Representation ℂ G.gaugeJetGroup (FieldDerivSpace M) :=
  (repDual M.repJet M.repJet_smul).prod
    (repDual (repConj M.repJet) (repConj_smul_comm M.repJet_smul))

@[simp]
lemma repJet_fst (M : G.MatterField) (U : G.gaugeJetGroup) (x : FieldDerivSpace M) :
    (repJet M U x).1 = repDual M.repJet M.repJet_smul U x.1 := rfl

@[simp]
lemma repJet_snd (M : G.MatterField) (U : G.gaugeJetGroup) (x : FieldDerivSpace M) :
    (repJet M U x).2
      = repDual (repConj M.repJet) (repConj_smul_comm M.repJet_smul) U x.2 := rfl

/-!

## C. Naturality in the value space

A component function is a covector on the value space, so a linear map `f : V →ₗ W` of
value spaces pulls the symbols of a `W`-valued field back to those of a `V`-valued field.
If `f` intertwines two fibrewise jet actions then that pullback is equivariant, in the
opposite direction. This is the gauge counterpart of
`FieldDerivSpace.comap_comp_repLorentzGroup`, and unlike it, it needs the value spaces to
be finite-dimensional, because the gauge action is defined through the coefficient.

Both halves have to be proved. The unconjugated half is the naturality of `repDual` at
`f`; the conjugate half is the naturality of `repDual` at `ConjModule.map f`, for the
conjugate actions, and is supplied by `FieldDerivSpace.lTensor_comp_repConj`. A conjugate
symbol carries `star` of the gauge matrix, so nothing about it follows from the
unconjugated half.

-/

/-- Pulling back and then acting is acting and then pulling back, on the symbols of a
coefficient. Precomposing the symbol action of a coefficient of `W` with the pullback
along `f` is the symbol action of the coefficient precomposed with `f`. -/
lemma map_transpose_comp_symbolAction (f : V →ₗ[ℂ] W) (y : SpaceTimeAlgebra ⊗[ℂ] Module.End ℂ W) :
    (TensorProduct.map LinearMap.id (Module.Dual.transpose f)).comp (symbolAction y)
      = symbolAction (LinearMap.lTensor SpaceTimeAlgebra (LinearMap.lcomp ℂ W f) y) := by
  induction y using TensorProduct.inductionOn with
  | add a b ha hb => rw [map_add, LinearMap.comp_add, ha, hb, map_add, map_add]
  | tmul g T =>
    rw [symbolAction_tmul, ← TensorProduct.map_comp, LinearMap.id_comp,
      ← Module.Dual.transpose_comp, LinearMap.lTensor_tmul, symbolAction_tmul]
    rfl

/-- The companion of `map_transpose_comp_symbolAction` on the other side. Postcomposing
  the symbol action of a coefficient of `V` with the pullback along `f` is the symbol
  action of the coefficient postcomposed with `f`. -/
lemma symbolAction_comp_map_transpose (f : V →ₗ[ℂ] W) (x : SpaceTimeAlgebra ⊗[ℂ] Module.End ℂ V) :
    (symbolAction x).comp (TensorProduct.map LinearMap.id (Module.Dual.transpose f))
      = symbolAction (LinearMap.lTensor SpaceTimeAlgebra (LinearMap.llcomp ℂ V V W f) x) := by
  induction x using TensorProduct.inductionOn with
  | add a b ha hb => rw [map_add, LinearMap.add_comp, ha, hb, map_add, map_add]
  | tmul g S =>
    rw [symbolAction_tmul, ← TensorProduct.map_comp, LinearMap.comp_id,
      ← Module.Dual.transpose_comp, LinearMap.lTensor_tmul, symbolAction_tmul]
    rfl

/-- The gauge action on the unconjugated symbols is natural in the value space. A
linear map of value spaces intertwining two fibrewise jet actions makes the pullback of
symbols equivariant for the two contragredient actions. The whole content is the naturality
of the coefficient, `FieldDerivSpace.jetCoeff_naturality`, read through the symbol
action; the group element is inverted on both sides alike, so no convention is disturbed
by it. -/
lemma comap_comp_repDual [Module.Free ℂ V] [Module.Finite ℂ V]
    [Module.Free ℂ W] [Module.Finite ℂ W]
    (repV : Representation ℂ G.gaugeJetGroup (SpaceTimeAlgebra ⊗[ℂ] V))
    (hV : ∀ (U : G.gaugeJetGroup) (χ : SpaceTimeAlgebra) (z : SpaceTimeAlgebra ⊗[ℂ] V), repV U
        (χ • z) = χ • repV U z)
    (repW : Representation ℂ G.gaugeJetGroup (SpaceTimeAlgebra ⊗[ℂ] W))
    (hW : ∀ (U : G.gaugeJetGroup) (χ : SpaceTimeAlgebra) (z : SpaceTimeAlgebra ⊗[ℂ] W), repW U
        (χ • z) = χ • repW U z)
    (f : V →ₗ[ℂ] W)
    (hf : ∀ U : G.gaugeJetGroup, (LinearMap.lTensor SpaceTimeAlgebra f).comp (repV U)
      = (repW U).comp (LinearMap.lTensor SpaceTimeAlgebra f)) (U : G.gaugeJetGroup) :
    (TensorProduct.map LinearMap.id (Module.Dual.transpose f)).comp (repDual repW hW U)
      = (repDual repV hV U).comp
        (TensorProduct.map LinearMap.id (Module.Dual.transpose f)) := by
  rw [show repDual repW hW U = symbolAction (jetCoeff repW U⁻¹) from rfl,
    show repDual repV hV U = symbolAction (jetCoeff repV U⁻¹) from rfl,
    map_transpose_comp_symbolAction, symbolAction_comp_map_transpose,
    jetCoeff_naturality repV repW f hf U⁻¹]

/-- The gauge action on the field-derivative space is natural in the value space. If
`f : M.V →ₗ N.V` intertwines the two fields' actions on the jets, then the pullback of component
functions along `f` intertwines the induced actions on the component spaces, in the
opposite direction — the pullback of a component function of a `W`-valued field being a
component function of a `V`-valued field.

Both halves are covered and every derivative label is carried. The statement is an equality
of linear maps on the whole component space, not a statement about undifferentiated
symbols. The conjugate half is the unconjugated argument applied to `repConj M.repJet` and
`repConj N.repJet`, whose intertwining is `FieldDerivSpace.lTensor_comp_repConj`. -/
lemma comap_comp_repJet {M N : G.MatterField} (f : M.V →ₗ[ℂ] N.V)
    (hf : ∀ U : G.gaugeJetGroup, (LinearMap.lTensor SpaceTimeAlgebra f).comp (M.repJet U)
      = (N.repJet U).comp (LinearMap.lTensor SpaceTimeAlgebra f)) (U : G.gaugeJetGroup) :
    (comap f).comp (repJet N U) = (repJet M U).comp (comap f) := by
  show (LinearMap.prodMap (TensorProduct.map LinearMap.id (Module.Dual.transpose f))
      (TensorProduct.map LinearMap.id
        (Module.Dual.transpose (ConjModule.map (k := ℂ) f)))).comp
      (LinearMap.prodMap (repDual N.repJet N.repJet_smul U)
        (repDual (repConj N.repJet) (repConj_smul_comm N.repJet_smul) U))
    = (LinearMap.prodMap (repDual M.repJet M.repJet_smul U)
        (repDual (repConj M.repJet) (repConj_smul_comm M.repJet_smul) U)).comp
      (LinearMap.prodMap (TensorProduct.map LinearMap.id (Module.Dual.transpose f))
        (TensorProduct.map LinearMap.id
          (Module.Dual.transpose (ConjModule.map (k := ℂ) f))))
  rw [LinearMap.prodMap_comp, LinearMap.prodMap_comp,
    comap_comp_repDual M.repJet M.repJet_smul N.repJet N.repJet_smul f hf U,
    comap_comp_repDual (repConj M.repJet) (repConj_smul_comm M.repJet_smul) (repConj N.repJet)
      (repConj_smul_comm N.repJet_smul) (ConjModule.map (k := ℂ) f)
      (lTensor_comp_repConj M.repJet N.repJet f hf) U]

end FieldDerivSpace
