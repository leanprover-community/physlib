/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jinzheng Li, Nathaneal Sajan, Joseph Tooby-Smith
-/
module

public import PhyslibAlpha.ClassicalFieldTheory.GaugeTheory.LocalFieldAlgebra.Jet
public import PhyslibAlpha.ClassicalFieldTheory.GaugeTheory.GaugeBoson.AdjointFamily.CovariantDeriv
/-!
# The covariant derivative of a matter family

The covariant derivative tower of a family of matter symbols in an algebra of symbols.

## i. Overview

A matter field valued in a complex vector space `V` has derivative symbols `[∂_s ψ]`,
indexed by a multiset `s` of directions and contracted against the dual of `V`. This file
works with such families `F : Multiset (Fin 1 ⊕ Fin 3) → Module.Dual ℂ V →ₗ[ℂ] B` in an
algebra of symbols `B`, together with a family `A` of gauge-field symbols `[∂_s A_μ]`.

Under a jet gauge transformation the value of `rep U` at a constant vector depends on the
spacetime point, so the derivative symbols see its Taylor coefficients at the base point.
These are `repCoeff rep U x`, and their transposes to the dual of `V` are
`repDualCoeff rep U x`, the analogue of `adjointDualCoeff` for a general representation.

The covariant derivative `∇_ρ F = ∂_ρ F + A_ρ · F` needs the infinitesimal action
`act : G.lieSubalgebra →ₗ[ℝ] V →ₗ[ℂ] V` of the gauge algebra on `V`, the physicists'
`i dρ(T^a)`. Here it is an argument. For a matter field it is the derivative of the group
representation, `MatterField.repAlgebra`. The derived action `A_ρ · F` is the Leibniz
convolution of the action of the gauge-field symbols on the matter symbols, and
`covDerivIter` iterates `∇` along an ordered tuple of directions.

The covariant tower and the plain derivative symbols generate the same algebra together with
the gauge-field symbols (the span lemma). The tower is natural under multiplicative linear maps
of the algebra and inherits mass weights and anticommutation from the bare family. That the
covariant derivative preserves the transformation law is proved in
`PhyslibAlpha.ClassicalFieldTheory.GaugeTheory.MatterField.InfinitesimalAction`.

## ii. Key results

- `repDualCoeff` : the physicists' `∂_x (rep U)^i_j|₀` acting on the complex dual index of a
  matter-field symbol, the transpose of `repCoeff`
- `covDerivIter` : the iterated covariant derivative of a matter family
- `adjoin_symbols_eq_adjoin_covDerivIter` : the span lemma, and its membership form
  `apply_mem_of_covDerivIter_mem`
- `covDerivIter_map` : the covariant tower is natural in the algebra
- `covDerivIter_mem_massWeightEigenspace` : the covariant tower of a family of weight
  `c + 2 * |t|` has weight `c + 2 * n + 2 * |s|`
- `covDerivIter_mem_anticommuteSubmodule` : anything commuting with the gauge-field symbols and
  anticommuting with the bare family anticommutes with its covariant tower

## iii. Table of contents

- A. The dual representation coefficients and gauge tensors in a representation
- B. The covariant derivative through an infinitesimal action
- C. The span lemma
- D. Naturality in the algebra
- E. Mass weights and statistics of the tower

## iv. References

* None.

-/

@[expose] public section

set_option linter.unusedSectionVars false

open Matrix MatrixGroups TensorProduct MvPowerSeries
variable {B : Type} [Ring B] [Algebra ℂ B]
variable {κ : Type} [Fintype κ] [DecidableEq κ] {G : GlobalGaugeGroup κ}
variable {V : Type} [AddCommGroup V] [Module ℂ V]

namespace GlobalGaugeGroup

open GaugeBoson (dualPairEquiv dualPairEquiv_tmul symm_comp_left massWeightEigenspace
  mul_mem_massWeightEigenspace anticommuteSubmodule mul_mem_anticommuteSubmodule)

variable {repGauge : Representation ℂ G.gaugeJetGroup B}
variable {A : Multiset (Fin 1 ⊕ Fin 3) → (Fin 1 ⊕ Fin 3) → Module.Dual ℝ G.lieSubalgebra →ₗ[ℝ] B}

/-!

## A. The dual representation coefficients and gauge tensors in a representation

-/

/-- The base-point Taylor coefficient of the representation. It includes the constant
  vector into `V`-valued jets, acts by `rep U`, differentiates `x` times and evaluates at
  the base point. The composite is the physicists' `∂_x (rep U)^i_j|₀` as a ℂ-linear map on
  the value space. -/
noncomputable def repCoeff (rep : Representation ℂ G.gaugeJetGroup (SpaceTimeAlgebra ⊗[ℂ] V))
    (U : G.gaugeJetGroup) (x : Multiset (Fin 1 ⊕ Fin 3)) : V →ₗ[ℂ] V :=
  jetEval ∘ₗ jetIteratedDeriv x ∘ₗ rep U ∘ₗ jetOfConstant

/-- The physicists' `∂_x (rep U)^i_j|₀` acting on the complex dual index of a
  matter-field symbol, the transpose of `repCoeff`. This is the analogue of
  `adjointDualCoeff` for a general representation of the jet gauge group; for `x = 0`
  it is the dual (contragredient) action of the value of `U`, and for `x ≠ 0` it sees
  the derivatives of the gauge transformation. -/
noncomputable def repDualCoeff (rep : Representation ℂ G.gaugeJetGroup (SpaceTimeAlgebra ⊗[ℂ] V))
    (U : G.gaugeJetGroup) (x : Multiset (Fin 1 ⊕ Fin 3)) :
    Module.Dual ℂ V →ₗ[ℂ] Module.Dual ℂ V :=
  (repCoeff rep U x).dualMap

/-- For a fibrewise representation, evaluating the transform of a jet at the base point
  is the zeroth Taylor coefficient of the transform of its base-point value. The jet
  ring factor passes through the action and is then evaluated. -/
lemma jetEval_rep_of_smul (rep : Representation ℂ G.gaugeJetGroup (SpaceTimeAlgebra ⊗[ℂ] V))
    (hlin : ∀ (U : G.gaugeJetGroup) (χ : SpaceTimeAlgebra) (z : SpaceTimeAlgebra ⊗[ℂ] V), rep U
        (χ • z) = χ • rep U z)
    (U : G.gaugeJetGroup) (z : SpaceTimeAlgebra ⊗[ℂ] V) :
    jetEval (rep U z) = repCoeff rep U 0 (jetEval z) := by
  induction z using TensorProduct.inductionOn with
  | add a b ha hb => rw [map_add, map_add, ha, hb, map_add, map_add]
  | tmul f v =>
    rw [show f ⊗ₜ[ℂ] v = f • jetOfConstant v from by
        rw [jetOfConstant_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one],
      hlin, jetEval_smul, jetEval_smul, jetEval_jetOfConstant, map_smul]
    simp only [repCoeff, LinearMap.comp_apply, jetIteratedDeriv_zero, LinearMap.id_apply]

/-- The zeroth Taylor coefficients of a fibrewise representation are multiplicative, so they
  form a representation of the jet gauge group on the value space. -/
lemma repCoeff_zero_mul (rep : Representation ℂ G.gaugeJetGroup (SpaceTimeAlgebra ⊗[ℂ] V))
    (hlin : ∀ (U : G.gaugeJetGroup) (χ : SpaceTimeAlgebra) (z : SpaceTimeAlgebra ⊗[ℂ] V), rep U
        (χ • z) = χ • rep U z)
    (U W : G.gaugeJetGroup) : repCoeff rep (U * W) 0 = repCoeff rep U 0 ∘ₗ repCoeff rep W 0 := by
  refine LinearMap.ext fun v => ?_
  have h := jetEval_rep_of_smul rep hlin U (rep W (jetOfConstant v))
  simp only [repCoeff, LinearMap.comp_apply, jetIteratedDeriv_zero, LinearMap.id_apply, map_mul,
    mul_apply_eq_comp] at h ⊢
  exact h

/-!

## B. The covariant derivative through an infinitesimal action

The covariant derivative `∇_ρ F = [∂_ρ F] + A_ρ · F` requires the infinitesimal
action of the gauge algebra on the value space, the physicists' `i dρ(T^a)`. Here it is an
argument `act : G.lieSubalgebra →ₗ[ℝ] V →ₗ[ℂ] V`, real-linear in the algebra slot (the
gauge algebra is a real Lie algebra) and complex-linear in the value slot, matching
the complex duals indexing the matter families. For a matter field it is
`MatterField.repAlgebra`, the derivative of the group representation.

-/

section Action

variable {act : G.lieSubalgebra →ₗ[ℝ] V →ₗ[ℂ] V}

/-- The action of an adjoint-valued field on a matter field at the tensor level. It is
  multiplication in `B` on the first factors and the ℂ-linear infinitesimal action `act`
  of the gauge algebra on `V` on the second factors, so that on pure tensors
  `(b₁ ⊗ c) · (b₂ ⊗ v) = (b₁ b₂) ⊗ act c v`. -/
noncomputable def tensorAction (act : G.lieSubalgebra →ₗ[ℝ] V →ₗ[ℂ] V) :
    (B ⊗[ℝ] G.lieSubalgebra) →ₗ[ℝ] (B ⊗[ℂ] V) →ₗ[ℂ] B ⊗[ℂ] V :=
  TensorProduct.lift
    { toFun := fun b₁ =>
        { toFun := fun c => TensorProduct.map (LinearMap.mulLeft ℂ b₁) (act c)
          map_add' := fun c₁ c₂ => TensorProduct.ext' fun b₂ v => by
            simp [TensorProduct.tmul_add]
          map_smul' := fun r c => TensorProduct.ext' fun b₂ v => by
            simp [TensorProduct.tmul_smul] }
      map_add' := fun b₁ b₁' => LinearMap.ext fun c => TensorProduct.ext' fun b₂ v => by
        simp [add_mul, TensorProduct.add_tmul]
      map_smul' := fun r b₁ => LinearMap.ext fun c => TensorProduct.ext' fun b₂ v => by
        simp [TensorProduct.smul_tmul'] }

@[simp]
lemma tensorAction_tmul (act : G.lieSubalgebra →ₗ[ℝ] V →ₗ[ℂ] V) (b₁ b₂ : B)
    (c : G.lieSubalgebra) (v : V) :
    tensorAction act (b₁ ⊗ₜ[ℝ] c) (b₂ ⊗ₜ[ℂ] v) = (b₁ * b₂) ⊗ₜ[ℂ] act c v := rfl

lemma tensorAction_map_left (act : G.lieSubalgebra →ₗ[ℝ] V →ₗ[ℂ] V) (Φ : B →ₗ[ℂ] B)
    (hΦ : ∀ b₁ b₂, Φ (b₁ * b₂) = Φ b₁ * Φ b₂) (s : B ⊗[ℝ] G.lieSubalgebra)
    (t : B ⊗[ℂ] V) :
    tensorAction act ((TensorProduct.map (Φ.restrictScalars ℝ) LinearMap.id) s)
        ((TensorProduct.map Φ LinearMap.id) t) =
      (TensorProduct.map Φ LinearMap.id) (tensorAction act s t) := by
  induction s using TensorProduct.inductionOn with
  | tmul b₁ a₁ =>
      induction t using TensorProduct.inductionOn with
      | tmul b₂ a₂ => simp [hΦ]
      | add x y hx hy =>
          simp only [map_add]
          rw [hx, hy]
  | add x y hx hy => simp [hx, hy]

lemma tensorAction_one_left (act : G.lieSubalgebra →ₗ[ℝ] V →ₗ[ℂ] V) (c : G.lieSubalgebra)
    (t : B ⊗[ℂ] V) :
    tensorAction act ((1 : B) ⊗ₜ[ℝ] c) t =
      (TensorProduct.map LinearMap.id (act c)) t := by
  induction t using TensorProduct.inductionOn with
  | tmul b a => simp
  | add x y hx hy => simp [hx, hy]

/-- `tensorAction` under an antidiagonal pair of transport families. If the
  `V`-transports intertwine `act` with the `G.lieSubalgebra`-transports as an
  antidiagonal convolution, so do `id ⊗ ·` over `tensorAction`. -/
lemma tensorAction_map_right_antidiagonal (act : G.lieSubalgebra →ₗ[ℝ] V →ₗ[ℂ] V)
    (Tg : Multiset (Fin 1 ⊕ Fin 3) → G.lieSubalgebra →ₗ[ℝ] G.lieSubalgebra)
    (Tv : Multiset (Fin 1 ⊕ Fin 3) → V →ₗ[ℂ] V) (x : Multiset (Fin 1 ⊕ Fin 3))
    (hT : ∀ (c : G.lieSubalgebra) (w : V), Tv x (act c w) =
      (x.antidiagonal.map fun p => act (Tg p.1 c) (Tv p.2 w)).sum)
    (s : B ⊗[ℝ] G.lieSubalgebra) (t : B ⊗[ℂ] V) :
    (x.antidiagonal.map fun p =>
      tensorAction act ((TensorProduct.map LinearMap.id (Tg p.1)) s)
        ((TensorProduct.map LinearMap.id (Tv p.2)) t)).sum =
      (TensorProduct.map LinearMap.id (Tv x)) (tensorAction act s t) := by
  induction s using TensorProduct.inductionOn with
  | tmul b₁ a₁ =>
      induction t using TensorProduct.inductionOn with
      | tmul b₂ a₂ =>
          simp only [tensorAction_tmul, TensorProduct.map_tmul, LinearMap.id_coe, id_eq]
          rw [hT, Multiset.tmul_sum, Multiset.map_map]
          exact congrArg Multiset.sum (Multiset.map_congr rfl fun p hp => by
            simp)
      | add y z hy hz =>
          rw [Multiset.map_congr rfl (fun p hp => by rw [map_add, map_add]),
            Multiset.sum_map_add, hy, hz, ← map_add, ← map_add]
  | add y z hy hz =>
      rw [Multiset.map_congr rfl (fun p hp => by
          rw [map_add, map_add, LinearMap.add_apply]),
        Multiset.sum_map_add, hy, hz, ← map_add, ← LinearMap.add_apply, ← map_add]

variable [FiniteDimensional ℂ V]

/-- The canonical equivalence between matter fields `B ⊗[ℂ] V` and their component
  families `φ ↦ F^φ` over the complex dual — `dualPairEquiv` for a general
  finite-dimensional complex value space. -/
noncomputable def dualPairEquivC : (B ⊗[ℂ] V) ≃ₗ[ℂ] (Module.Dual ℂ V →ₗ[ℂ] B) :=
  TensorProduct.comm ℂ B V ≪≫ₗ
    TensorProduct.congr (Module.evalEquiv ℂ V) (LinearEquiv.refl ℂ B) ≪≫ₗ
    dualTensorHomEquiv ℂ (Module.Dual ℂ V) B

@[simp]
lemma dualPairEquivC_tmul (b : B) (v : V) (φ : Module.Dual ℂ V) :
    dualPairEquivC (b ⊗ₜ[ℂ] v) φ = φ v • b := by
  simp [dualPairEquivC, dualTensorHomEquiv, Module.evalEquiv_apply]

lemma dualPairEquivC_map_left (Φ : B →ₗ[ℂ] B) (t : B ⊗[ℂ] V)
    (φ : Module.Dual ℂ V) :
    dualPairEquivC ((TensorProduct.map Φ LinearMap.id) t) φ =
      Φ (dualPairEquivC t φ) := by
  induction t using TensorProduct.inductionOn with
  | tmul b w => simp
  | add x y hx hy => simp [hx, hy]

lemma dualPairEquivC_map_right (T : V →ₗ[ℂ] V) (t : B ⊗[ℂ] V)
    (φ : Module.Dual ℂ V) :
    dualPairEquivC ((TensorProduct.map LinearMap.id T) t) φ =
      dualPairEquivC t (T.dualMap φ) := by
  induction t using TensorProduct.inductionOn with
  | tmul b w => simp
  | add x y hx hy => simp [hx, hy]

lemma symm_comp_left_C (Φ : B →ₗ[ℂ] B) (g : Module.Dual ℂ V →ₗ[ℂ] B) :
    dualPairEquivC.symm (Φ ∘ₗ g) =
      (TensorProduct.map Φ LinearMap.id) (dualPairEquivC.symm g) := by
  apply dualPairEquivC.injective
  rw [LinearEquiv.apply_symm_apply]
  refine LinearMap.ext fun φ => ?_
  rw [dualPairEquivC_map_left, LinearEquiv.apply_symm_apply]
  rfl

lemma symm_comp_right_C (T : V →ₗ[ℂ] V) (g : Module.Dual ℂ V →ₗ[ℂ] B) :
    dualPairEquivC.symm (g ∘ₗ T.dualMap) =
      (TensorProduct.map LinearMap.id T) (dualPairEquivC.symm g) := by
  apply dualPairEquivC.injective
  rw [LinearEquiv.apply_symm_apply]
  refine LinearMap.ext fun φ => ?_
  rw [dualPairEquivC_map_right, LinearEquiv.apply_symm_apply]
  rfl

/-- The action of an adjoint-indexed component family on a matter one, through the
  infinitesimal action `act`. Both are assembled into fields, acted on by `tensorAction`
  and read back out as components. This is the physicists' `f^a (T_a)^i_j g^j` with `T = act`,
  basis-free. -/
noncomputable def actionFam (act : G.lieSubalgebra →ₗ[ℝ] V →ₗ[ℂ] V)
    (f : Module.Dual ℝ G.lieSubalgebra →ₗ[ℝ] B) (g : Module.Dual ℂ V →ₗ[ℂ] B) :
    Module.Dual ℂ V →ₗ[ℂ] B :=
  dualPairEquivC (tensorAction act (dualPairEquiv.symm f) (dualPairEquivC.symm g))

lemma actionFam_add_left (f₁ f₂ : Module.Dual ℝ G.lieSubalgebra →ₗ[ℝ] B)
    (g : Module.Dual ℂ V →ₗ[ℂ] B) :
    actionFam act (f₁ + f₂) g = actionFam act f₁ g + actionFam act f₂ g := by
  simp only [actionFam, map_add, LinearMap.add_apply]

lemma actionFam_add_right (f : Module.Dual ℝ G.lieSubalgebra →ₗ[ℝ] B)
    (g₁ g₂ : Module.Dual ℂ V →ₗ[ℂ] B) :
    actionFam act f (g₁ + g₂) = actionFam act f g₁ + actionFam act f g₂ := by
  simp only [actionFam, map_add]

lemma actionFam_zero_left (g : Module.Dual ℂ V →ₗ[ℂ] B) :
    actionFam act 0 g = 0 := by
  simp [actionFam]

lemma actionFam_zero_right (f : Module.Dual ℝ G.lieSubalgebra →ₗ[ℝ] B) :
    actionFam act f 0 = 0 := by
  simp [actionFam]

lemma actionFam_sum_left (S : Multiset (Module.Dual ℝ G.lieSubalgebra →ₗ[ℝ] B))
    (g : Module.Dual ℂ V →ₗ[ℂ] B) :
    actionFam act S.sum g = (S.map fun f => actionFam act f g).sum := by
  induction S using Multiset.induction_on with
  | empty => simp [actionFam_zero_left]
  | cons f S ih => simp [actionFam_add_left, ih]

lemma actionFam_sum_right (f : Module.Dual ℝ G.lieSubalgebra →ₗ[ℝ] B)
    (S : Multiset (Module.Dual ℂ V →ₗ[ℂ] B)) :
    actionFam act f S.sum = (S.map fun g => actionFam act f g).sum := by
  induction S using Multiset.induction_on with
  | empty => simp [actionFam_zero_right]
  | cons g S ih => simp [actionFam_add_right, ih]

/-- The gauge transformation of the action of an affinely-transforming
  adjoint-indexed family on a linearly-transforming matter family. It is the action of the
  transformed families plus one `act`-type cross term. This is `GaugeBoson.repGauge_bracketFam`
  with a homogeneous second slot and the bracket replaced by a general action. Only the
  multiplicativity of the action of `U` is used. -/
lemma repGauge_actionFam
    (U : G.gaugeJetGroup)
    (hmul : ∀ b₁ b₂ : B, repGauge U (b₁ * b₂) = repGauge U b₁ * repGauge U b₂)
    {f f' : Module.Dual ℝ G.lieSubalgebra →ₗ[ℝ] B}
    {g g' : Module.Dual ℂ V →ₗ[ℂ] B} {cf : G.lieSubalgebra}
    (hf : ∀ ψ : Module.Dual ℝ G.lieSubalgebra,
      repGauge U (f ψ) = f' ψ + algebraMap ℂ B (ψ cf))
    (hg : ∀ ψ : Module.Dual ℂ V, repGauge U (g ψ) = g' ψ)
    (φ : Module.Dual ℂ V) :
    repGauge U (actionFam act f g φ) =
      actionFam act f' g' φ + g' (φ ∘ₗ act cf) := by
  set Φ : B →ₗ[ℂ] B := repGauge U with hΦdef
  have hΦmul : ∀ b₁ b₂ : B, Φ (b₁ * b₂) = Φ b₁ * Φ b₂ := hmul
  set s : B ⊗[ℝ] G.lieSubalgebra := dualPairEquiv.symm f with hs
  set t : B ⊗[ℂ] V := dualPairEquivC.symm g with ht
  set s' : B ⊗[ℝ] G.lieSubalgebra := dualPairEquiv.symm f' with hs'
  set t' : B ⊗[ℂ] V := dualPairEquivC.symm g' with ht'
  have hfm : (TensorProduct.map (Φ.restrictScalars ℝ) LinearMap.id) s
      = s' + (1 : B) ⊗ₜ[ℝ] cf := by
    rw [hs, hs']; exact GaugeBoson.map_dualPairEquiv_symm_of_affine (Φ.restrictScalars ℝ) hf
  have hgm : (TensorProduct.map Φ LinearMap.id) t = t' := by
    rw [ht, ht', ← symm_comp_left_C,
      show Φ ∘ₗ g = g' from LinearMap.ext fun ψ => by
        simp only [LinearMap.comp_apply, hΦdef]
        rw [hg ψ]]
  have hact : dualPairEquivC (tensorAction act s t) = actionFam act f g := by
    rw [hs, ht]; rfl
  have hact' : dualPairEquivC (tensorAction act s' t') = actionFam act f' g' := by
    rw [hs', ht']; rfl
  have hπt' : dualPairEquivC t' = g' := by
    rw [ht']; exact dualPairEquivC.apply_symm_apply _
  clear_value Φ s t s' t'
  have htensor : (TensorProduct.map Φ LinearMap.id) (tensorAction act s t) =
      tensorAction act s' t'
      + (TensorProduct.map LinearMap.id (act cf)) t' := by
    refine (tensorAction_map_left act Φ hΦmul s t).symm.trans
      ((congrArg₂ (fun X Y => tensorAction act X Y) hfm hgm).trans ?_)
    rw [map_add, LinearMap.add_apply, tensorAction_one_left]
  have hread := congrArg (fun z => dualPairEquivC z φ) htensor
  simp only [map_add, LinearMap.add_apply, dualPairEquivC_map_left,
    dualPairEquivC_map_right] at hread
  rw [show Φ (actionFam act f g φ) =
      Φ (dualPairEquivC (tensorAction act s t) φ) from by rw [hact],
    hread, hact', hπt']
  rfl

/-- The derived action family `A_ρ · F`, the `s`-derivative of the action of the
  gauge field on a matter family, given by the Leibniz convolution of the derivative
  symbols over the multiset antidiagonal — the matter analogue of `GaugeBoson.bracketFamConv`. -/
noncomputable def actionFamConv
    (A : Multiset (Fin 1 ⊕ Fin 3) → (Fin 1 ⊕ Fin 3) → Module.Dual ℝ G.lieSubalgebra →ₗ[ℝ] B)
    (act : G.lieSubalgebra →ₗ[ℝ] V →ₗ[ℂ] V) (ρ : Fin 1 ⊕ Fin 3)
    (F : Multiset (Fin 1 ⊕ Fin 3) → Module.Dual ℂ V →ₗ[ℂ] B)
    (s : Multiset (Fin 1 ⊕ Fin 3)) : Module.Dual ℂ V →ₗ[ℂ] B :=
  (s.antidiagonal.map fun p => actionFam act (A p.1 ρ) (F p.2)).sum

/-- The covariant derivative `∇_ρ F = [∂_ρ F] + A_ρ · F` of a matter family of
  derivative symbols, in the single direction `ρ`, the extra derivative on the symbol
  plus the derived action of the gauge field on the value index. With the physicists'
  factor of `i` absorbed into `act` (as it is in the gauge-algebra bracket), this is
  `∂_ρ F + i A_ρ^a T_a F` in the `D = ∂ + i A` convention. -/
noncomputable def covDerivAction
    (A : Multiset (Fin 1 ⊕ Fin 3) → (Fin 1 ⊕ Fin 3) → Module.Dual ℝ G.lieSubalgebra →ₗ[ℝ] B)
    (act : G.lieSubalgebra →ₗ[ℝ] V →ₗ[ℂ] V)
    (F : Multiset (Fin 1 ⊕ Fin 3) → Module.Dual ℂ V →ₗ[ℂ] B)
    (ρ : Fin 1 ⊕ Fin 3) (s : Multiset (Fin 1 ⊕ Fin 3)) : Module.Dual ℂ V →ₗ[ℂ] B :=
  F (ρ ::ₘ s) + actionFamConv A act ρ F s

@[simp]
lemma covDerivAction_apply
    (A : Multiset (Fin 1 ⊕ Fin 3) → (Fin 1 ⊕ Fin 3) → Module.Dual ℝ G.lieSubalgebra →ₗ[ℝ] B)
    (act : G.lieSubalgebra →ₗ[ℝ] V →ₗ[ℂ] V)
    (F : Multiset (Fin 1 ⊕ Fin 3) → Module.Dual ℂ V →ₗ[ℂ] B)
    (ρ : Fin 1 ⊕ Fin 3) (s : Multiset (Fin 1 ⊕ Fin 3)) (φ : Module.Dual ℂ V) :
    covDerivAction A act F ρ s φ = F (ρ ::ₘ s) φ + actionFamConv A act ρ F s φ := rfl

/-- The iterated covariant derivative `∇_{l 0} ⋯ ∇_{l (n-1)} F` of a matter family
  along an ordered tuple of directions. Covariant derivatives do not commute (their
  commutator is the action of the field strength), so the iteration is order-dependent
  and indexed by `(n : ℕ)` and `l : Fin n → (Fin 1 ⊕ Fin 3)`. The result is again a
  family of derivative symbols; the physical iterated covariant derivative is its
  value at the empty multiset. -/
noncomputable def covDerivIter
    (A : Multiset (Fin 1 ⊕ Fin 3) → (Fin 1 ⊕ Fin 3) → Module.Dual ℝ G.lieSubalgebra →ₗ[ℝ] B)
    (act : G.lieSubalgebra →ₗ[ℝ] V →ₗ[ℂ] V)
    (F : Multiset (Fin 1 ⊕ Fin 3) → Module.Dual ℂ V →ₗ[ℂ] B) :
    (n : ℕ) → (Fin n → (Fin 1 ⊕ Fin 3)) →
      Multiset (Fin 1 ⊕ Fin 3) → Module.Dual ℂ V →ₗ[ℂ] B
  | 0, _ => F
  | n + 1, l => covDerivAction A act (covDerivIter A act F n fun i => l i.succ) (l 0)

@[simp]
lemma covDerivIter_zero (act : G.lieSubalgebra →ₗ[ℝ] V →ₗ[ℂ] V)
    (F : Multiset (Fin 1 ⊕ Fin 3) → Module.Dual ℂ V →ₗ[ℂ] B)
    (l : Fin 0 → (Fin 1 ⊕ Fin 3)) :
    covDerivIter A act F 0 l = F := rfl

@[simp]
lemma covDerivIter_succ (act : G.lieSubalgebra →ₗ[ℝ] V →ₗ[ℂ] V)
    (F : Multiset (Fin 1 ⊕ Fin 3) → Module.Dual ℂ V →ₗ[ℂ] B)
    {n : ℕ} (l : Fin (n + 1) → (Fin 1 ⊕ Fin 3)) :
    covDerivIter A act F (n + 1) l =
      covDerivAction A act (covDerivIter A act F n fun i => l i.succ) (l 0) := rfl

/-!

## C. The span lemma

Replacing derivatives of a matter family by covariant derivatives does not change
the generated algebra of symbols: the correction terms are products of gauge-field
components with matter components. Note the statement is about generated
*subalgebras*, not linear spans — `∇_ρ F − ∂_ρ F` is a sum of products `A · F`,
which lies in the algebra generated by the symbols but not in their linear span.

-/

/-- Decomposition of an assembled adjoint-indexed family along a basis of the gauge
  algebra, as the components against the dual basis, tensored with the basis vectors. -/
lemma dualPairEquiv_symm_eq_sum {ι : Type*} [Fintype ι]
    (bW : Module.Basis ι ℝ G.lieSubalgebra)
    (g : Module.Dual ℝ G.lieSubalgebra →ₗ[ℝ] B) :
    dualPairEquiv.symm g = ∑ i, g (bW.coord i) ⊗ₜ[ℝ] bW i := by
  apply dualPairEquiv.injective
  rw [LinearEquiv.apply_symm_apply]
  refine LinearMap.ext fun φ => ?_
  symm
  rw [map_sum, LinearMap.sum_apply]
  simp only [dualPairEquiv_tmul]
  have hdual : (∑ i, φ (bW i) • bW.coord i) = φ := by
    refine bW.ext fun j => ?_
    rw [LinearMap.sum_apply]
    simp only [LinearMap.smul_apply, Module.Basis.coord_apply, Module.Basis.repr_self,
      smul_eq_mul]
    rw [Finset.sum_eq_single j
      (fun i _ hij => by simp [Ne.symm hij])
      (fun h => absurd (Finset.mem_univ j) h)]
    simp
  calc ∑ i, φ (bW i) • g (bW.coord i)
      = g (∑ i, φ (bW i) • bW.coord i) := by rw [map_sum]; simp
    _ = g φ := by rw [hdual]

/-- Decomposition of an assembled matter family along a basis of the value space. -/
lemma dualPairEquivC_symm_eq_sum {ι : Type*} [Fintype ι] (bW : Module.Basis ι ℂ V)
    (g : Module.Dual ℂ V →ₗ[ℂ] B) :
    dualPairEquivC.symm g = ∑ i, g (bW.coord i) ⊗ₜ[ℂ] bW i := by
  apply dualPairEquivC.injective
  rw [LinearEquiv.apply_symm_apply]
  refine LinearMap.ext fun φ => ?_
  symm
  rw [map_sum, LinearMap.sum_apply]
  simp only [dualPairEquivC_tmul]
  have hdual : (∑ i, φ (bW i) • bW.coord i) = φ := by
    refine bW.ext fun j => ?_
    rw [LinearMap.sum_apply]
    simp only [LinearMap.smul_apply, Module.Basis.coord_apply, Module.Basis.repr_self,
      smul_eq_mul]
    rw [Finset.sum_eq_single j
      (fun i _ hij => by simp [Ne.symm hij])
      (fun h => absurd (Finset.mem_univ j) h)]
    simp
  calc ∑ i, φ (bW i) • g (bW.coord i)
      = g (∑ i, φ (bW i) • bW.coord i) := by rw [map_sum]; simp
    _ = g φ := by rw [hdual]

/-- The value of an action of families lies in any subalgebra containing the values
  of both families, since the action is a finite sum of products of components. -/
lemma actionFam_apply_mem {act : G.lieSubalgebra →ₗ[ℝ] V →ₗ[ℂ] V} {P : Subalgebra ℂ B}
    {f : Module.Dual ℝ G.lieSubalgebra →ₗ[ℝ] B} {g : Module.Dual ℂ V →ₗ[ℂ] B}
    (hf : ∀ ψ, f ψ ∈ P) (hg : ∀ χ, g χ ∈ P) (φ : Module.Dual ℂ V) :
    actionFam act f g φ ∈ P := by
  rw [actionFam, dualPairEquiv_symm_eq_sum (Module.finBasis ℝ G.lieSubalgebra) f,
    dualPairEquivC_symm_eq_sum (Module.finBasis ℂ V) g]
  simp only [map_sum, LinearMap.sum_apply, tensorAction_tmul, dualPairEquivC_tmul]
  refine sum_mem fun i _ => sum_mem fun j _ => ?_
  exact P.smul_mem (mul_mem (hf _) (hg _)) _

omit [FiniteDimensional ℂ V] in
/-- The subalgebra generated by the gauge-field symbols and the matter symbols of order below
  `k` grows with `k`. -/
private lemma adjoin_lowerSymbols_mono (F : Multiset (Fin 1 ⊕ Fin 3) → Module.Dual ℂ V →ₗ[ℂ] B)
    {k m : ℕ} (hkm : k ≤ m) :
    Algebra.adjoin ℂ
      ({b : B | ∃ u μ ψ, b = A u μ ψ} ∪
        {b : B | ∃ (t : Multiset (Fin 1 ⊕ Fin 3)) (χ : Module.Dual ℂ V),
          t.card < k ∧ b = F t χ}) ≤
    Algebra.adjoin ℂ
      ({b : B | ∃ u μ ψ, b = A u μ ψ} ∪
        {b : B | ∃ (t : Multiset (Fin 1 ⊕ Fin 3)) (χ : Module.Dual ℂ V),
          t.card < m ∧ b = F t χ}) := by
  refine Algebra.adjoin_mono (Set.union_subset_union_right _ ?_)
  rintro b ⟨t, χ, ht, rfl⟩
  exact ⟨t, χ, by omega, rfl⟩

/-- Moving the first direction of a tuple into the multiset of derivatives. -/
private lemma ofFn_add_eq_ofFn_succ_add_cons {n : ℕ} (l : Fin (n + 1) → (Fin 1 ⊕ Fin 3))
    (s : Multiset (Fin 1 ⊕ Fin 3)) :
    ((List.ofFn l : List (Fin 1 ⊕ Fin 3)) : Multiset (Fin 1 ⊕ Fin 3)) + s =
      ((List.ofFn fun i : Fin n => l i.succ : List (Fin 1 ⊕ Fin 3)) :
        Multiset (Fin 1 ⊕ Fin 3)) + (l 0 ::ₘ s) := by
  rw [List.ofFn_succ,
    show (((l 0 :: List.ofFn fun i : Fin n => l i.succ : List (Fin 1 ⊕ Fin 3))) :
        Multiset (Fin 1 ⊕ Fin 3))
      = l 0 ::ₘ ((List.ofFn fun i : Fin n => l i.succ : List (Fin 1 ⊕ Fin 3)) :
        Multiset (Fin 1 ⊕ Fin 3)) from rfl,
    Multiset.cons_add, Multiset.add_cons]

/-- One step of the unitriangular expansion. The difference between a covariant symbol with
  `n + 1` directions and the plain symbol of the same total order is the difference one step
  lower plus the derived action of the gauge field on the lower tower. -/
lemma covDerivIter_succ_sub (act : G.lieSubalgebra →ₗ[ℝ] V →ₗ[ℂ] V)
    (F : Multiset (Fin 1 ⊕ Fin 3) → Module.Dual ℂ V →ₗ[ℂ] B)
    {n : ℕ} (l : Fin (n + 1) → (Fin 1 ⊕ Fin 3)) (s : Multiset (Fin 1 ⊕ Fin 3))
    (φ : Module.Dual ℂ V) :
    covDerivIter A act F (n + 1) l s φ - F (List.ofFn l + s) φ =
      (covDerivIter A act F n (fun i => l i.succ) (l 0 ::ₘ s) φ -
          F (List.ofFn (fun i : Fin n => l i.succ) + (l 0 ::ₘ s)) φ) +
        actionFamConv A act (l 0) (covDerivIter A act F n fun i => l i.succ) s φ := by
  rw [covDerivIter_succ, covDerivAction_apply, ofFn_add_eq_ofFn_succ_add_cons]
  abel

/-- Unitriangularity of the covariant matter tower. The covariant and plain
  derivative symbols of a matter family differ by an element of the subalgebra
  generated by the gauge-field symbols and the strictly lower-order matter symbols.
  Stated at every derivative multiset `s`, as needed for the induction. -/
lemma covDerivIter_sub_mem (act : G.lieSubalgebra →ₗ[ℝ] V →ₗ[ℂ] V)
    (F : Multiset (Fin 1 ⊕ Fin 3) → Module.Dual ℂ V →ₗ[ℂ] B)
    (n : ℕ) (l : Fin n → (Fin 1 ⊕ Fin 3)) (s : Multiset (Fin 1 ⊕ Fin 3))
    (φ : Module.Dual ℂ V) :
    covDerivIter A act F n l s φ - F (List.ofFn l + s) φ ∈
      Algebra.adjoin ℂ
        ({b : B | ∃ (u : Multiset (Fin 1 ⊕ Fin 3)) (μ : Fin 1 ⊕ Fin 3)
            (ψ : Module.Dual ℝ G.lieSubalgebra), b = A u μ ψ} ∪
          {b : B | ∃ (t : Multiset (Fin 1 ⊕ Fin 3)) (χ : Module.Dual ℂ V),
            t.card < n + s.card ∧ b = F t χ}) := by
  induction n generalizing s φ with
  | zero =>
      simp only [covDerivIter_zero, List.ofFn_zero,
        show ((([] : List (Fin 1 ⊕ Fin 3)) : Multiset (Fin 1 ⊕ Fin 3)) = 0) from rfl,
        zero_add, sub_self]
      exact zero_mem _
  | succ n ih =>
      rw [covDerivIter_succ_sub]
      refine add_mem ?_ ?_
      · refine adjoin_lowerSymbols_mono F ?_ (ih (fun i => l i.succ) (l 0 ::ₘ s) φ)
        simp only [Multiset.card_cons]
        omega
      · rw [actionFamConv, Multiset.sum_linearMap_apply, Multiset.map_map]
        refine multiset_sum_mem _ fun x hx => ?_
        obtain ⟨p, hp, rfl⟩ := Multiset.mem_map.mp hx
        have hle := Multiset.mem_antidiagonal.mp hp
        have h2 : p.2.card ≤ s.card :=
          hle ▸ Multiset.card_le_card (Multiset.le_add_left _ _)
        refine actionFam_apply_mem (fun ψ => ?_) (fun χ => ?_) _
        · exact Algebra.subset_adjoin (Or.inl ⟨p.1, l 0, ψ, rfl⟩)
        · rw [← sub_add_cancel (covDerivIter A act F n (fun i => l i.succ) p.2 χ)
            (F (List.ofFn (fun i : Fin n => l i.succ) + p.2) χ)]
          refine add_mem (adjoin_lowerSymbols_mono F ?_ (ih (fun i => l i.succ) p.2 χ)) ?_
          · omega
          · refine Algebra.subset_adjoin
              (Or.inr ⟨List.ofFn (fun i : Fin n => l i.succ) + p.2, χ, ?_, rfl⟩)
            simp only [Multiset.card_add, Multiset.coe_card, List.length_ofFn]
            omega

/-- Every derivative symbol of the covariant tower is a polynomial in the gauge-field
  symbols and the matter symbols. -/
lemma covDerivIter_mem_adjoin_symbols (act : G.lieSubalgebra →ₗ[ℝ] V →ₗ[ℂ] V)
    (F : Multiset (Fin 1 ⊕ Fin 3) → Module.Dual ℂ V →ₗ[ℂ] B)
    (n : ℕ) (l : Fin n → (Fin 1 ⊕ Fin 3)) (s : Multiset (Fin 1 ⊕ Fin 3))
    (φ : Module.Dual ℂ V) :
    covDerivIter A act F n l s φ ∈ Algebra.adjoin ℂ
      ({b : B | ∃ (s : Multiset (Fin 1 ⊕ Fin 3)) (μ : Fin 1 ⊕ Fin 3)
          (ψ : Module.Dual ℝ G.lieSubalgebra), b = A s μ ψ} ∪
        {b : B | ∃ (s : Multiset (Fin 1 ⊕ Fin 3)) (φ : Module.Dual ℂ V),
          b = F s φ}) := by
  induction n generalizing s φ with
  | zero => exact Algebra.subset_adjoin (Or.inr ⟨s, φ, rfl⟩)
  | succ n ih =>
      rw [covDerivIter_succ, covDerivAction_apply]
      refine add_mem (ih (fun i => l i.succ) (l 0 ::ₘ s) φ) ?_
      rw [actionFamConv, Multiset.sum_linearMap_apply, Multiset.map_map]
      refine multiset_sum_mem _ fun x hx => ?_
      obtain ⟨p, hp, rfl⟩ := Multiset.mem_map.mp hx
      refine actionFam_apply_mem (fun ψ' => ?_) (fun χ => ?_) _
      · exact Algebra.subset_adjoin (Or.inl ⟨p.1, l 0, ψ', rfl⟩)
      · exact ih (fun i => l i.succ) p.2 χ

/-- The span lemma. The algebra of symbols generated by the gauge field together
  with a matter family's derivative symbols equals the one generated by the gauge
  field together with the matter family's covariant derivative tower. The
  correction `∇_ρ − ∂_ρ` is the derived action of the gauge field — a sum of products
  of symbols, absorbed by the algebra structure. -/
lemma adjoin_symbols_eq_adjoin_covDerivIter (act : G.lieSubalgebra →ₗ[ℝ] V →ₗ[ℂ] V)
    (F : Multiset (Fin 1 ⊕ Fin 3) → Module.Dual ℂ V →ₗ[ℂ] B) :
    Algebra.adjoin ℂ
      ({b : B | ∃ (s : Multiset (Fin 1 ⊕ Fin 3)) (μ : Fin 1 ⊕ Fin 3)
          (ψ : Module.Dual ℝ G.lieSubalgebra), b = A s μ ψ} ∪
        {b : B | ∃ (s : Multiset (Fin 1 ⊕ Fin 3)) (φ : Module.Dual ℂ V),
          b = F s φ}) =
    Algebra.adjoin ℂ
      ({b : B | ∃ (s : Multiset (Fin 1 ⊕ Fin 3)) (μ : Fin 1 ⊕ Fin 3)
          (ψ : Module.Dual ℝ G.lieSubalgebra), b = A s μ ψ} ∪
        {b : B | ∃ (n : ℕ) (l : Fin n → (Fin 1 ⊕ Fin 3)) (φ : Module.Dual ℂ V),
          b = covDerivIter A act F n l 0 φ}) := by
  refine le_antisymm (Algebra.adjoin_le ?_) (Algebra.adjoin_le ?_)
  · rintro x (⟨s, μ, ψ, rfl⟩ | ⟨s, φ, rfl⟩)
    · exact Algebra.subset_adjoin (Or.inl ⟨s, μ, ψ, rfl⟩)
    · -- express a matter symbol through the covariant tower, by strong induction on
      -- the order
      have main : ∀ n, ∀ (s : Multiset (Fin 1 ⊕ Fin 3)) (φ : Module.Dual ℂ V),
          s.card ≤ n →
          F s φ ∈ Algebra.adjoin ℂ
            ({b : B | ∃ (s : Multiset (Fin 1 ⊕ Fin 3)) (μ : Fin 1 ⊕ Fin 3)
                (ψ : Module.Dual ℝ G.lieSubalgebra), b = A s μ ψ} ∪
              {b : B | ∃ (n : ℕ) (l : Fin n → (Fin 1 ⊕ Fin 3)) (φ : Module.Dual ℂ V),
                b = covDerivIter A act F n l 0 φ}) := by
        intro n
        induction n using Nat.strong_induction_on with
        | _ n ih =>
          intro s φ hs
          set L := s.toList with hL'
          have hL : Multiset.ofList L = s := Multiset.coe_toList _
          have hofFn : List.ofFn L.get = L := List.ofFn_get L
          rw [show F s φ = covDerivIter A act F L.length L.get 0 φ -
              (covDerivIter A act F L.length L.get 0 φ -
                F (List.ofFn L.get + 0) φ) from by
            rw [add_zero, hofFn, hL]; abel]
          refine sub_mem (Algebra.subset_adjoin (Or.inr ⟨L.length, L.get, φ, rfl⟩)) ?_
          refine IsConcreteLE.le_iff.mp (Algebra.adjoin_le ?_)
            (covDerivIter_sub_mem act F L.length L.get 0 φ)
          rintro b (⟨u, μ, ψ, rfl⟩ | ⟨t, χ, htc, rfl⟩)
          · exact Algebra.subset_adjoin (Or.inl ⟨u, μ, ψ, rfl⟩)
          · have htn : t.card < n := by
              have hlen : L.length = s.card := Multiset.length_toList s
              simp only [Multiset.card_zero] at htc
              omega
            exact ih t.card htn t χ (le_refl _)
      exact main s.card s φ (le_refl _)
  · rintro x (⟨s, μ, ψ, rfl⟩ | ⟨n, l, φ, rfl⟩)
    · exact Algebra.subset_adjoin (Or.inl ⟨s, μ, ψ, rfl⟩)
    · exact covDerivIter_mem_adjoin_symbols act F n l 0 φ

/-- A derivative symbol of a matter family lies in every subalgebra containing the gauge-field
symbols and the covariant tower of the family. This is the span lemma
`adjoin_symbols_eq_adjoin_covDerivIter` read as a membership statement. -/
lemma apply_mem_of_covDerivIter_mem (act : G.lieSubalgebra →ₗ[ℝ] V →ₗ[ℂ] V)
    (F : Multiset (Fin 1 ⊕ Fin 3) → Module.Dual ℂ V →ₗ[ℂ] B) {P : Subalgebra ℂ B}
    (hA : ∀ s μ ψ, A s μ ψ ∈ P)
    (hF : ∀ n (l : Fin n → (Fin 1 ⊕ Fin 3)) φ, covDerivIter A act F n l 0 φ ∈ P)
    (s : Multiset (Fin 1 ⊕ Fin 3)) (φ : Module.Dual ℂ V) : F s φ ∈ P := by
  refine Algebra.adjoin_le ?_ ((adjoin_symbols_eq_adjoin_covDerivIter (A := A) act F).le
    (Algebra.subset_adjoin (Or.inr ⟨s, φ, rfl⟩)))
  rintro b (⟨p, μ, ψ, rfl⟩ | ⟨n, l, ψ, rfl⟩)
  exacts [hA p μ ψ, hF n l ψ]

/-!

## D. Naturality in the algebra

The matter analogue of `bracketFam_map` and `iteratedCovDerivAdjoint_map`: a
multiplicative linear map into another algebra carries the derived action, and hence
the whole covariant matter tower, to the tower of the image families. The derived
action is a finite sum of products of components, so only multiplicativity is needed;
no derivative operator on the target is involved.

-/

section Naturality

variable {B' : Type} [Ring B'] [Algebra ℂ B'] (Φ : B →ₗ[ℂ] B')
  (hΦ : ∀ b₁ b₂, Φ (b₁ * b₂) = Φ b₁ * Φ b₂)

include hΦ

/-- The action of an adjoint-indexed family on a matter family is natural in the
  algebra. -/
lemma actionFam_map (act : G.lieSubalgebra →ₗ[ℝ] V →ₗ[ℂ] V)
    (f : Module.Dual ℝ G.lieSubalgebra →ₗ[ℝ] B)
    (g : Module.Dual ℂ V →ₗ[ℂ] B) :
    actionFam act (Φ.restrictScalars ℝ ∘ₗ f) (Φ ∘ₗ g) = Φ ∘ₗ actionFam act f g := by
  refine LinearMap.ext fun φ => ?_
  rw [actionFam, actionFam,
    dualPairEquiv_symm_eq_sum (Module.finBasis ℝ G.lieSubalgebra) (Φ.restrictScalars ℝ ∘ₗ f),
    dualPairEquivC_symm_eq_sum (Module.finBasis ℂ V) (Φ ∘ₗ g),
    dualPairEquiv_symm_eq_sum (Module.finBasis ℝ G.lieSubalgebra) f,
    dualPairEquivC_symm_eq_sum (Module.finBasis ℂ V) g]
  simp only [map_sum, LinearMap.sum_apply, tensorAction_tmul, dualPairEquivC_tmul,
    LinearMap.comp_apply, LinearMap.coe_restrictScalars, map_smul, hΦ]

/-- The derived action family is natural in the algebra. -/
lemma actionFamConv_map
    (A : Multiset (Fin 1 ⊕ Fin 3) → (Fin 1 ⊕ Fin 3) → Module.Dual ℝ G.lieSubalgebra →ₗ[ℝ] B)
    (act : G.lieSubalgebra →ₗ[ℝ] V →ₗ[ℂ] V) (ρ : Fin 1 ⊕ Fin 3)
    (F : Multiset (Fin 1 ⊕ Fin 3) → Module.Dual ℂ V →ₗ[ℂ] B)
    (s : Multiset (Fin 1 ⊕ Fin 3)) :
    actionFamConv (fun p σ => Φ.restrictScalars ℝ ∘ₗ A p σ) act ρ (fun p => Φ ∘ₗ F p) s
      = Φ ∘ₗ actionFamConv A act ρ F s := by
  refine LinearMap.ext fun φ => ?_
  rw [LinearMap.comp_apply, actionFamConv, actionFamConv, Multiset.sum_linearMap_apply,
    Multiset.sum_linearMap_apply, Multiset.map_map, Multiset.map_map, map_multiset_sum,
    Multiset.map_map]
  refine congrArg Multiset.sum (Multiset.map_congr rfl fun p _ => ?_)
  simp only [Function.comp_apply]
  rw [actionFam_map Φ hΦ]
  rfl

/-- The covariant derivative of a matter family is natural in the algebra. -/
lemma covDerivAction_map
    (A : Multiset (Fin 1 ⊕ Fin 3) → (Fin 1 ⊕ Fin 3) → Module.Dual ℝ G.lieSubalgebra →ₗ[ℝ] B)
    (act : G.lieSubalgebra →ₗ[ℝ] V →ₗ[ℂ] V)
    (F : Multiset (Fin 1 ⊕ Fin 3) → Module.Dual ℂ V →ₗ[ℂ] B)
    (ρ : Fin 1 ⊕ Fin 3) (s : Multiset (Fin 1 ⊕ Fin 3)) :
    covDerivAction (fun p σ => Φ.restrictScalars ℝ ∘ₗ A p σ) act (fun p => Φ ∘ₗ F p) ρ s
      = Φ ∘ₗ covDerivAction A act F ρ s := by
  rw [covDerivAction, covDerivAction, actionFamConv_map Φ hΦ, LinearMap.comp_add]

/-- The iterated covariant derivative of a matter family is natural in the algebra. The
  image of the tower is the tower of the image families, at every ordered tuple of
  directions and every derivative multiset. -/
lemma covDerivIter_map
    (A : Multiset (Fin 1 ⊕ Fin 3) → (Fin 1 ⊕ Fin 3) → Module.Dual ℝ G.lieSubalgebra →ₗ[ℝ] B)
    (act : G.lieSubalgebra →ₗ[ℝ] V →ₗ[ℂ] V)
    (F : Multiset (Fin 1 ⊕ Fin 3) → Module.Dual ℂ V →ₗ[ℂ] B)
    (n : ℕ) (l : Fin n → (Fin 1 ⊕ Fin 3)) :
    covDerivIter (fun p σ => Φ.restrictScalars ℝ ∘ₗ A p σ) act (fun p => Φ ∘ₗ F p) n l
      = fun s => Φ ∘ₗ covDerivIter A act F n l s := by
  induction n with
  | zero => rfl
  | succ n ih =>
    funext s
    show covDerivAction (fun p σ => Φ.restrictScalars ℝ ∘ₗ A p σ) act
        (covDerivIter (fun p σ => Φ.restrictScalars ℝ ∘ₗ A p σ) act (fun p => Φ ∘ₗ F p) n
          fun i => l i.succ) (l 0) s
      = Φ ∘ₗ covDerivAction A act (covDerivIter A act F n fun i => l i.succ) (l 0) s
    rw [ih, covDerivAction_map Φ hΦ]

end Naturality

/-!

## E. Mass weights and statistics of the tower

Each term of a covariant tower is a product of gauge-field symbols with a single bare symbol
of the family, so a property of the bare family that is a submodule and is stable under
multiplication by the gauge-field symbols passes to the tower. Two such properties matter:
the mass weight, and anticommutation with a fixed element.

-/

/-- The action pairing of two families lands in any submodule containing the products of
  their components, since expanded in bases it is a finite sum of scalar multiples of them. -/
lemma actionFam_apply_mem_submodule {act : G.lieSubalgebra →ₗ[ℝ] V →ₗ[ℂ] V}
    {M : Submodule ℂ B} {f : Module.Dual ℝ G.lieSubalgebra →ₗ[ℝ] B}
    {g : Module.Dual ℂ V →ₗ[ℂ] B} (hfg : ∀ ψ χ, f ψ * g χ ∈ M) (φ : Module.Dual ℂ V) :
    actionFam act f g φ ∈ M := by
  rw [actionFam, dualPairEquiv_symm_eq_sum (Module.finBasis ℝ G.lieSubalgebra) f,
    dualPairEquivC_symm_eq_sum (Module.finBasis ℂ V) g]
  simp only [map_sum, LinearMap.sum_apply, tensorAction_tmul, dualPairEquivC_tmul]
  exact sum_mem fun i _ => sum_mem fun j _ => M.smul_mem _ (hfg _ _)

/-- The mass weight of a matter covariant tower. If the gauge-field symbols `∂_p A_μ` have
  weight `2 * (1 + |p|)` and the bare family has weight `c + 2 * |t|` at the derivative
  multiset `t`, then the `n`-fold covariant derivative has weight `c + 2 * n + 2 * |s|` at
  `s`. Each covariant derivative costs two units, whether it lands on the derivative index or
  brings down a gauge-field factor. -/
lemma covDerivIter_mem_massWeightEigenspace (act : G.lieSubalgebra →ₗ[ℝ] V →ₗ[ℂ] V)
    (F : Multiset (Fin 1 ⊕ Fin 3) → Module.Dual ℂ V →ₗ[ℂ] B) (P : B →ₐ[ℂ] Polynomial B)
    (c : ℕ)
    (hA : ∀ (p : Multiset (Fin 1 ⊕ Fin 3)) (μ : Fin 1 ⊕ Fin 3) (ψ : Module.Dual ℝ G.lieSubalgebra),
      A p μ ψ ∈ massWeightEigenspace P (2 * (1 + Multiset.card p)))
    (hF : ∀ (t : Multiset (Fin 1 ⊕ Fin 3)) (χ : Module.Dual ℂ V),
      F t χ ∈ massWeightEigenspace P (c + 2 * Multiset.card t))
    {n : ℕ} (l : Fin n → (Fin 1 ⊕ Fin 3)) (s : Multiset (Fin 1 ⊕ Fin 3))
    (φ : Module.Dual ℂ V) :
    covDerivIter A act F n l s φ ∈ massWeightEigenspace P (c + 2 * n + 2 * Multiset.card s) := by
  induction n generalizing s φ with
  | zero =>
      rw [covDerivIter_zero]
      simpa using hF s φ
  | succ n ih =>
      rw [covDerivIter_succ, covDerivAction_apply]
      refine add_mem ?_ ?_
      · have hstep := ih (fun i => l i.succ) (l 0 ::ₘ s) φ
        rwa [Multiset.card_cons, show c + 2 * n + 2 * (Multiset.card s + 1)
            = c + 2 * (n + 1) + 2 * Multiset.card s by ring] at hstep
      · rw [actionFamConv, Multiset.sum_linearMap_apply, Multiset.map_map]
        refine multiset_sum_mem _ fun x hx => ?_
        obtain ⟨p, hp, rfl⟩ := Multiset.mem_map.mp hx
        have hle : Multiset.card p.1 + Multiset.card p.2 = Multiset.card s := by
          rw [← Multiset.card_add, Multiset.mem_antidiagonal.mp hp]
        simp only [Function.comp_apply]
        refine actionFam_apply_mem_submodule (fun ψ χ => ?_) _
        have hmul := mul_mem_massWeightEigenspace (hA p.1 (l 0) ψ)
          (ih (fun i => l i.succ) p.2 χ)
        rwa [show 2 * (1 + Multiset.card p.1) + (c + 2 * n + 2 * Multiset.card p.2)
          = c + 2 * (n + 1) + 2 * Multiset.card s by omega] at hmul

/-- Anything commuting with every gauge-field symbol and anticommuting with every bare symbol
  of the family anticommutes with every symbol of its covariant tower, since each term of the
  tower is a product of gauge-field symbols with a single bare symbol. -/
lemma covDerivIter_mem_anticommuteSubmodule (act : G.lieSubalgebra →ₗ[ℝ] V →ₗ[ℂ] V)
    (F : Multiset (Fin 1 ⊕ Fin 3) → Module.Dual ℂ V →ₗ[ℂ] B) {x : B}
    (hxA : ∀ (p : Multiset (Fin 1 ⊕ Fin 3)) (μ : Fin 1 ⊕ Fin 3)
      (ψ : Module.Dual ℝ G.lieSubalgebra), Commute x (A p μ ψ))
    (hxF : ∀ (t : Multiset (Fin 1 ⊕ Fin 3)) (χ : Module.Dual ℂ V),
      F t χ ∈ anticommuteSubmodule x) :
    ∀ (n : ℕ) (l : Fin n → (Fin 1 ⊕ Fin 3)) (s : Multiset (Fin 1 ⊕ Fin 3))
      (φ : Module.Dual ℂ V), covDerivIter A act F n l s φ ∈ anticommuteSubmodule x := by
  intro n
  induction n with
  | zero => exact fun l s φ => hxF s φ
  | succ n ih =>
      intro l s φ
      rw [covDerivIter_succ, covDerivAction_apply]
      refine add_mem (ih _ _ _) ?_
      rw [actionFamConv, Multiset.sum_linearMap_apply, Multiset.map_map]
      refine multiset_sum_mem _ fun z hz => ?_
      obtain ⟨p, hp, rfl⟩ := Multiset.mem_map.mp hz
      simp only [Function.comp_apply]
      exact actionFam_apply_mem_submodule
        (fun ψ χ => mul_mem_anticommuteSubmodule (hxA p.1 (l 0) ψ) (ih _ p.2 χ)) _

end Action


end GlobalGaugeGroup


