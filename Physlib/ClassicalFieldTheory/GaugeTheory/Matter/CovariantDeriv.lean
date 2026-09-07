/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.ClassicalFieldTheory.GaugeTheory.GaugeField.Basic
public import Physlib.ClassicalFieldTheory.JetAlgebra.Jet
public import Physlib.ClassicalFieldTheory.GaugeTheory.GaugeField.TransformsInAdjoint
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.Dimension.Free
/-!

# Gauge tensors in a general representation

The adjoint story of `TransformsInAdjoint` generalizes to an arbitrary representation
of the jet gauge group: a matter field valued in a representation space `V` has
symbols `[∂_s ψ^i]` contracted against duals of `V`, and its transformation law is
the Leibniz convolution of the base-point Taylor coefficients of the representation.

Since the gauge transformations are jets, the representation must act on `V`-valued
jets `JetRing ⊗[ℂ] V` — the value of `rep U` at a constant vector is spacetime
dependent, and the derivative symbols see its Taylor coefficients. This file provides
the toolkit for `V`-valued jets:

* `jetOfConstant` — the inclusion of constants, `v ↦ 1 ⊗ v`;
* `jetDeriv`/`jetIteratedDeriv` — the formal derivative, acting on the jet factor;
* `jetEval` — evaluation at the base point, `f ⊗ v ↦ (constant coefficient of f) • v`;

and with them

* `repDualCoeff rep U x` — the physicists' `∂_x (rep U)^i_j|₀` transposed to the dual
  of `V`, the analogue of `adjointDualCoeff` for a general representation;
* `TransformsIn` — the generalization of `TransformsInAdjoint`: the derivative
  symbols of the family transform by the Leibniz convolution of `repDualCoeff`, with
  no inhomogeneous term.

## The covariant derivative

The covariant derivative `∇_ρ F = D_ρ F + (A_ρ acting on the value index)` requires
the *infinitesimal* action of the gauge algebra on the value space — physicists'
`i dρ(T^a)` — which cannot be extracted from the abstract group representation `rep`
(there is no differentiable structure to differentiate it). It is therefore taken as
data: an `ℝ`-bilinear action `act : GaugeAlgebra →ₗ[ℝ] W →ₗ[ℝ] W`. The layer is
built for an arbitrary finite-dimensional real value space `W`, so that the adjoint
case `act = adAction` (the bracket as a bilinear map) literally specializes:
`covDerivAction A adAction F D ρ = covDerivAdjoint A F D ρ` holds definitionally
(`covDerivAction_adAction`).

The compatibility between `rep` and `act` — the structure `IsInfinitesimalActionOf` —
and the theorem that under it the covariant derivative preserves the gauge tensors live
in `Physlib.Particles.StandardModel.GaugeAlgebra.InfinitesimalAction`.

-/

@[expose] public section

set_option linter.unusedSectionVars false

open Matrix MatrixGroups TensorProduct MvPowerSeries
variable {B : Type} [Ring B] [Algebra ℂ B]
variable {G : Type} [Group G] {𝔤 : Type} [LieRing 𝔤] [LieAlgebra ℝ 𝔤] [Module.Finite ℝ 𝔤]
variable {G₀ : Type} [Group G₀] {𝔤J : Type} [LieRing 𝔤J] [LieAlgebra ℝ 𝔤J]
variable [GaugeJet G 𝔤 G₀ 𝔤J]
variable {V : Type} [AddCommGroup V] [Module ℂ V]

namespace IsGaugeField

variable {repLorentz : Representation ℂ SL(2,ℂ) B}
variable {repGauge : Representation ℂ G B}
variable {repLorentz : Representation ℂ SL(2,ℂ) B}
variable {repGauge : Representation ℂ G B}
variable {A : Multiset (Fin 1 ⊕ Fin 3) → (Fin 1 ⊕ Fin 3) → Module.Dual ℝ 𝔤 →ₗ[ℝ] B}

/-!

## The dual representation coefficients and gauge tensors in a representation

-/

/-- The base-point adjoint transport at `x` derivatives, un-dualized: the map on the
  gauge algebra whose transpose is `adjointDualCoeff`. -/
noncomputable def adjointCoeff (U : G) (x : Multiset (Fin 1 ⊕ Fin 3)) :
    𝔤 →ₗ[ℝ] 𝔤 :=
  (GaugeJet.evalLie G (𝔤 := 𝔤)).toLinearMap ∘ₗ GaugeJet.iteratedDeriv G 𝔤 x ∘ₗ
    GaugeJet.adjoint 𝔤 (G := G) U ∘ₗ GaugeJet.ofConstantLie G (𝔤 := 𝔤)

lemma adjointDualCoeff_eq_dualMap (U : G) (x : Multiset (Fin 1 ⊕ Fin 3)) :
    adjointDualCoeff (𝔤 := 𝔤) U x = (adjointCoeff U x).dualMap := rfl

/-- The base-point Taylor coefficient of the representation: include the constant
  vector into `V`-valued jets, act by `rep U`, differentiate `x` times, evaluate at
  the base point. The composite is complex-linear: the physicists'
  `∂_x (rep U)^i_j|₀` as a ℂ-linear map on the value space. -/
noncomputable def repCoeff (rep : Representation ℂ G (JetRing ⊗[ℂ] V))
    (U : G) (x : Multiset (Fin 1 ⊕ Fin 3)) : V →ₗ[ℂ] V :=
  jetEval ∘ₗ jetIteratedDeriv x ∘ₗ rep U ∘ₗ jetOfConstant

/-- The physicists' `∂_x (rep U)^i_j|₀` acting on the complex dual index of a
  matter-field symbol: the transpose of `repCoeff`. This is the analogue of
  `adjointDualCoeff` for a general representation of the jet gauge group; for `x = 0`
  it is the dual (contragredient) action of the value of `U`, and for `x ≠ 0` it sees
  the derivatives of the gauge transformation. -/
noncomputable def repDualCoeff (rep : Representation ℂ G (JetRing ⊗[ℂ] V))
    (U : G) (x : Multiset (Fin 1 ⊕ Fin 3)) :
    Module.Dual ℂ V →ₗ[ℂ] Module.Dual ℂ V :=
  (repCoeff rep U x).dualMap

/-- A component family `F`, valued in `B` and indexed by the complex dual of the
  representation space `V`, *transforms in* the representation `rep` of the jet gauge
  group — with the ambient action `repGauge` on `B` — when each derivative symbol
  `[∂_s F^φ]` transforms by the Leibniz convolution of the dual representation
  coefficients against lower symbols, with no inhomogeneous term — the generalization
  of `TransformsInAdjoint` from the adjoint representation to an arbitrary one, and
  the form consumed by `AlgebraRealization`. -/
def _root_.TransformsIn (repGauge : Representation ℂ G B)
    (rep : Representation ℂ G (JetRing ⊗[ℂ] V))
    (F : Multiset (Fin 1 ⊕ Fin 3) → Module.Dual ℂ V →ₗ[ℂ] B) : Prop :=
  ∀ (U : G) (φ : Module.Dual ℂ V) (s : Multiset (Fin 1 ⊕ Fin 3)),
    repGauge U (F s φ) =
      (s.antidiagonal.map fun p => F p.2 (repDualCoeff rep U⁻¹ p.1 φ)).sum

/-!

## The covariant derivative through an infinitesimal action

The covariant derivative `∇_ρ F = [∂_ρ F] + A_ρ · F` requires the *infinitesimal*
action of the gauge algebra on the value space — physicists' `i dρ(T^a)` — which
cannot be extracted from the abstract group representation `rep` (there is no
differentiable structure to differentiate it). It is therefore taken as data: an
action `act : 𝔤 →ₗ[ℝ] V →ₗ[ℂ] V`, real-linear in the algebra slot (the
gauge algebra is a real Lie algebra) and complex-linear in the value slot, matching
the complex duals indexing the matter families.

-/

section Action

variable {act : 𝔤 →ₗ[ℝ] V →ₗ[ℂ] V}

/-- The action of an adjoint-valued field on a matter field at the tensor level:
  multiplication in `B` on the first factors, the ℂ-linear infinitesimal action `act`
  of the gauge algebra on `V` on the second, so that on pure tensors
  `(b₁ ⊗ c) · (b₂ ⊗ v) = (b₁ b₂) ⊗ act c v`. -/
noncomputable def tensorAction (act : 𝔤 →ₗ[ℝ] V →ₗ[ℂ] V) :
    (B ⊗[ℝ] 𝔤) →ₗ[ℝ] (B ⊗[ℂ] V) →ₗ[ℂ] B ⊗[ℂ] V :=
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
lemma tensorAction_tmul (act : 𝔤 →ₗ[ℝ] V →ₗ[ℂ] V) (b₁ b₂ : B)
    (c : 𝔤) (v : V) :
    tensorAction act (b₁ ⊗ₜ[ℝ] c) (b₂ ⊗ₜ[ℂ] v) = (b₁ * b₂) ⊗ₜ[ℂ] act c v := rfl

lemma tensorAction_map_left (act : 𝔤 →ₗ[ℝ] V →ₗ[ℂ] V) (Φ : B →ₗ[ℂ] B)
    (hΦ : ∀ b₁ b₂, Φ (b₁ * b₂) = Φ b₁ * Φ b₂) (s : B ⊗[ℝ] 𝔤)
    (t : B ⊗[ℂ] V) :
    tensorAction act ((TensorProduct.map (Φ.restrictScalars ℝ) LinearMap.id) s)
        ((TensorProduct.map Φ LinearMap.id) t) =
      (TensorProduct.map Φ LinearMap.id) (tensorAction act s t) := by
  induction s using TensorProduct.induction_on with
  | zero => simp
  | tmul b₁ a₁ =>
      induction t using TensorProduct.induction_on with
      | zero => simp
      | tmul b₂ a₂ => simp [hΦ]
      | add x y hx hy =>
          simp only [map_add]
          rw [hx, hy]
  | add x y hx hy => simp [hx, hy]

lemma tensorAction_one_left (act : 𝔤 →ₗ[ℝ] V →ₗ[ℂ] V) (c : 𝔤)
    (t : B ⊗[ℂ] V) :
    tensorAction act ((1 : B) ⊗ₜ[ℝ] c) t =
      (TensorProduct.map LinearMap.id (act c)) t := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul b a => simp
  | add x y hx hy => simp [hx, hy]

/-- `tensorAction` under an antidiagonal pair of transport families: if the
  `V`-transports intertwine `act` with the `𝔤`-transports as an
  antidiagonal convolution, so do `id ⊗ ·` over `tensorAction`. -/
lemma tensorAction_map_right_antidiagonal (act : 𝔤 →ₗ[ℝ] V →ₗ[ℂ] V)
    (Tg : Multiset (Fin 1 ⊕ Fin 3) → 𝔤 →ₗ[ℝ] 𝔤)
    (Tv : Multiset (Fin 1 ⊕ Fin 3) → V →ₗ[ℂ] V) (x : Multiset (Fin 1 ⊕ Fin 3))
    (hT : ∀ (c : 𝔤) (w : V), Tv x (act c w) =
      (x.antidiagonal.map fun p => act (Tg p.1 c) (Tv p.2 w)).sum)
    (s : B ⊗[ℝ] 𝔤) (t : B ⊗[ℂ] V) :
    (x.antidiagonal.map fun p =>
      tensorAction act ((TensorProduct.map LinearMap.id (Tg p.1)) s)
        ((TensorProduct.map LinearMap.id (Tv p.2)) t)).sum =
      (TensorProduct.map LinearMap.id (Tv x)) (tensorAction act s t) := by
  induction s using TensorProduct.induction_on with
  | zero => simp
  | tmul b₁ a₁ =>
      induction t using TensorProduct.induction_on with
      | zero => simp
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
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul b w => simp
  | add x y hx hy => simp [hx, hy]

lemma dualPairEquivC_map_right (T : V →ₗ[ℂ] V) (t : B ⊗[ℂ] V)
    (φ : Module.Dual ℂ V) :
    dualPairEquivC ((TensorProduct.map LinearMap.id T) t) φ =
      dualPairEquivC t (T.dualMap φ) := by
  induction t using TensorProduct.induction_on with
  | zero => simp
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
  infinitesimal action `act`: assemble both into fields, act by `tensorAction`, read
  back out as components. This is the physicists' `f^a (T_a)^i_j g^j` with `T = act`,
  basis-free. -/
noncomputable def actionFam (act : 𝔤 →ₗ[ℝ] V →ₗ[ℂ] V)
    (f : Module.Dual ℝ 𝔤 →ₗ[ℝ] B) (g : Module.Dual ℂ V →ₗ[ℂ] B) :
    Module.Dual ℂ V →ₗ[ℂ] B :=
  dualPairEquivC (tensorAction act (dualPairEquiv.symm f) (dualPairEquivC.symm g))

lemma actionFam_add_left (f₁ f₂ : Module.Dual ℝ 𝔤 →ₗ[ℝ] B)
    (g : Module.Dual ℂ V →ₗ[ℂ] B) :
    actionFam act (f₁ + f₂) g = actionFam act f₁ g + actionFam act f₂ g := by
  simp only [actionFam, map_add, LinearMap.add_apply]

lemma actionFam_add_right (f : Module.Dual ℝ 𝔤 →ₗ[ℝ] B)
    (g₁ g₂ : Module.Dual ℂ V →ₗ[ℂ] B) :
    actionFam act f (g₁ + g₂) = actionFam act f g₁ + actionFam act f g₂ := by
  simp only [actionFam, map_add]

lemma actionFam_zero_left (g : Module.Dual ℂ V →ₗ[ℂ] B) :
    actionFam act 0 g = 0 := by
  simp [actionFam]

lemma actionFam_zero_right (f : Module.Dual ℝ 𝔤 →ₗ[ℝ] B) :
    actionFam act f 0 = 0 := by
  simp [actionFam]

lemma actionFam_sum_left (S : Multiset (Module.Dual ℝ 𝔤 →ₗ[ℝ] B))
    (g : Module.Dual ℂ V →ₗ[ℂ] B) :
    actionFam act S.sum g = (S.map fun f => actionFam act f g).sum := by
  induction S using Multiset.induction_on with
  | empty => simp [actionFam_zero_left]
  | cons f S ih => simp [actionFam_add_left, ih]

lemma actionFam_sum_right (f : Module.Dual ℝ 𝔤 →ₗ[ℝ] B)
    (S : Multiset (Module.Dual ℂ V →ₗ[ℂ] B)) :
    actionFam act f S.sum = (S.map fun g => actionFam act f g).sum := by
  induction S using Multiset.induction_on with
  | empty => simp [actionFam_zero_right]
  | cons g S ih => simp [actionFam_add_right, ih]

set_option maxHeartbeats 1000000 in
/-- The gauge transformation of the action of an affinely-transforming
  adjoint-indexed family on a linearly-transforming matter family: the action of the
  transformed families plus one `act`-type cross term. This is `repGauge_bracketFam`
  with a homogeneous second slot and the bracket replaced by a general action. -/
lemma repGauge_actionFam (hA : IsGaugeField repLorentz repGauge A)
    (U : G) {f f' : Module.Dual ℝ 𝔤 →ₗ[ℝ] B}
    {g g' : Module.Dual ℂ V →ₗ[ℂ] B} {cf : 𝔤}
    (hf : ∀ ψ : Module.Dual ℝ 𝔤,
      repGauge U (f ψ) = f' ψ + algebraMap ℂ B (ψ cf))
    (hg : ∀ ψ : Module.Dual ℂ V, repGauge U (g ψ) = g' ψ)
    (φ : Module.Dual ℂ V) :
    repGauge U (actionFam act f g φ) =
      actionFam act f' g' φ + g' (φ ∘ₗ act cf) := by
  set Φ : B →ₗ[ℂ] B := repGauge U with hΦdef
  have hΦmul : ∀ b₁ b₂ : B, Φ (b₁ * b₂) = Φ b₁ * Φ b₂ := fun b₁ b₂ =>
    hA.gauge_mul U b₁ b₂
  set s : B ⊗[ℝ] 𝔤 := dualPairEquiv.symm f with hs
  set t : B ⊗[ℂ] V := dualPairEquivC.symm g with ht
  set s' : B ⊗[ℝ] 𝔤 := dualPairEquiv.symm f' with hs'
  set t' : B ⊗[ℂ] V := dualPairEquivC.symm g' with ht'
  have hfm : (TensorProduct.map (Φ.restrictScalars ℝ) LinearMap.id) s
      = s' + (1 : B) ⊗ₜ[ℝ] cf := by
    rw [hs, hs', ← symm_comp_left,
      show Φ.restrictScalars ℝ ∘ₗ f = f' + dualPairEquiv ((1 : B) ⊗ₜ[ℝ] cf) from
        LinearMap.ext fun ψ => by
          simp only [LinearMap.comp_apply, LinearMap.add_apply, hΦdef,
            LinearMap.restrictScalars_apply]
          rw [hf ψ, dualPairEquiv_one_tmul],
      map_add, LinearEquiv.symm_apply_apply]
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

/-- The derived action family `A_ρ · F`: the `s`-derivative of the action of the
  gauge field on a matter family, given by the Leibniz convolution of the derivative
  symbols over the multiset antidiagonal — the matter analogue of `bracketFamConv`. -/
noncomputable def actionFamConv
    (A : Multiset (Fin 1 ⊕ Fin 3) → (Fin 1 ⊕ Fin 3) → Module.Dual ℝ 𝔤 →ₗ[ℝ] B)
    (act : 𝔤 →ₗ[ℝ] V →ₗ[ℂ] V) (ρ : Fin 1 ⊕ Fin 3)
    (F : Multiset (Fin 1 ⊕ Fin 3) → Module.Dual ℂ V →ₗ[ℂ] B)
    (s : Multiset (Fin 1 ⊕ Fin 3)) : Module.Dual ℂ V →ₗ[ℂ] B :=
  (s.antidiagonal.map fun p => actionFam act (A p.1 ρ) (F p.2)).sum

/-- The covariant derivative `∇_ρ F = [∂_ρ F] + A_ρ · F` of a matter family of
  derivative symbols, in the single direction `ρ`: the extra derivative on the symbol
  plus the derived action of the gauge field on the value index. With the physicists'
  factor of `i` absorbed into `act` (as it is in the gauge-algebra bracket), this is
  `∂_ρ F + i A_ρ^a T_a F` in the `D = ∂ + i A` convention. -/
noncomputable def covDerivAction
    (A : Multiset (Fin 1 ⊕ Fin 3) → (Fin 1 ⊕ Fin 3) → Module.Dual ℝ 𝔤 →ₗ[ℝ] B)
    (act : 𝔤 →ₗ[ℝ] V →ₗ[ℂ] V)
    (F : Multiset (Fin 1 ⊕ Fin 3) → Module.Dual ℂ V →ₗ[ℂ] B)
    (ρ : Fin 1 ⊕ Fin 3) (s : Multiset (Fin 1 ⊕ Fin 3)) : Module.Dual ℂ V →ₗ[ℂ] B :=
  F (ρ ::ₘ s) + actionFamConv A act ρ F s

@[simp]
lemma covDerivAction_apply
    (A : Multiset (Fin 1 ⊕ Fin 3) → (Fin 1 ⊕ Fin 3) → Module.Dual ℝ 𝔤 →ₗ[ℝ] B)
    (act : 𝔤 →ₗ[ℝ] V →ₗ[ℂ] V)
    (F : Multiset (Fin 1 ⊕ Fin 3) → Module.Dual ℂ V →ₗ[ℂ] B)
    (ρ : Fin 1 ⊕ Fin 3) (s : Multiset (Fin 1 ⊕ Fin 3)) (φ : Module.Dual ℂ V) :
    covDerivAction A act F ρ s φ = F (ρ ::ₘ s) φ + actionFamConv A act ρ F s φ := rfl

/-- **The iterated covariant derivative** `∇_{l 0} ⋯ ∇_{l (n-1)} F` of a matter family
  along an ordered tuple of directions: covariant derivatives do not commute (their
  commutator is the action of the field strength), so the iteration is order-dependent
  and indexed by `(n : ℕ)` and `l : Fin n → (Fin 1 ⊕ Fin 3)` — the same ordered-tuple
  indexing as the derivative labels of `IsHiggsAlgebraValued`. The result is again a
  family of derivative symbols; the physical iterated covariant derivative is its
  value at the empty multiset. -/
noncomputable def covDerivIter
    (A : Multiset (Fin 1 ⊕ Fin 3) → (Fin 1 ⊕ Fin 3) → Module.Dual ℝ 𝔤 →ₗ[ℝ] B)
    (act : 𝔤 →ₗ[ℝ] V →ₗ[ℂ] V)
    (F : Multiset (Fin 1 ⊕ Fin 3) → Module.Dual ℂ V →ₗ[ℂ] B) :
    (n : ℕ) → (Fin n → (Fin 1 ⊕ Fin 3)) →
      Multiset (Fin 1 ⊕ Fin 3) → Module.Dual ℂ V →ₗ[ℂ] B
  | 0, _ => F
  | n + 1, l => covDerivAction A act (covDerivIter A act F n fun i => l i.succ) (l 0)

@[simp]
lemma covDerivIter_zero (act : 𝔤 →ₗ[ℝ] V →ₗ[ℂ] V)
    (F : Multiset (Fin 1 ⊕ Fin 3) → Module.Dual ℂ V →ₗ[ℂ] B)
    (l : Fin 0 → (Fin 1 ⊕ Fin 3)) :
    covDerivIter A act F 0 l = F := rfl

@[simp]
lemma covDerivIter_succ (act : 𝔤 →ₗ[ℝ] V →ₗ[ℂ] V)
    (F : Multiset (Fin 1 ⊕ Fin 3) → Module.Dual ℂ V →ₗ[ℂ] B)
    {n : ℕ} (l : Fin (n + 1) → (Fin 1 ⊕ Fin 3)) :
    covDerivIter A act F (n + 1) l =
      covDerivAction A act (covDerivIter A act F n fun i => l i.succ) (l 0) := rfl

/-!

## The span lemma

Replacing derivatives of a matter family by covariant derivatives does not change
the generated algebra of symbols: the correction terms are products of gauge-field
components with matter components. Note the statement is about generated
*subalgebras*, not linear spans — `∇_ρ F − ∂_ρ F` is a sum of products `A · F`,
which lies in the algebra generated by the symbols but not in their linear span.

-/

/-- Decomposition of an assembled adjoint-indexed family along a basis of the gauge
  algebra: the components against the dual basis, tensored with the basis vectors. -/
lemma dualPairEquiv_symm_eq_sum {ι : Type*} [Fintype ι]
    (bW : Module.Basis ι ℝ 𝔤)
    (g : Module.Dual ℝ 𝔤 →ₗ[ℝ] B) :
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
  of both families: the action is a finite sum of products of components. -/
lemma actionFam_apply_mem {act : 𝔤 →ₗ[ℝ] V →ₗ[ℂ] V} {P : Subalgebra ℂ B}
    {f : Module.Dual ℝ 𝔤 →ₗ[ℝ] B} {g : Module.Dual ℂ V →ₗ[ℂ] B}
    (hf : ∀ ψ, f ψ ∈ P) (hg : ∀ χ, g χ ∈ P) (φ : Module.Dual ℂ V) :
    actionFam act f g φ ∈ P := by
  rw [actionFam, dualPairEquiv_symm_eq_sum (Module.finBasis ℝ 𝔤) f,
    dualPairEquivC_symm_eq_sum (Module.finBasis ℂ V) g]
  simp only [map_sum, LinearMap.sum_apply, tensorAction_tmul, dualPairEquivC_tmul]
  refine sum_mem fun i _ => sum_mem fun j _ => ?_
  exact P.smul_mem (mul_mem (hf _) (hg _)) _

/-- **Unitriangularity of the covariant matter tower**: the covariant and plain
  derivative symbols of a matter family differ by an element of the subalgebra
  generated by the gauge-field symbols and the strictly lower-order matter symbols.
  Stated at every derivative multiset `s`, as needed for the induction. -/
lemma covDerivIter_sub_mem (act : 𝔤 →ₗ[ℝ] V →ₗ[ℂ] V)
    (F : Multiset (Fin 1 ⊕ Fin 3) → Module.Dual ℂ V →ₗ[ℂ] B)
    (n : ℕ) (l : Fin n → (Fin 1 ⊕ Fin 3)) (s : Multiset (Fin 1 ⊕ Fin 3))
    (φ : Module.Dual ℂ V) :
    covDerivIter A act F n l s φ - F (List.ofFn l + s) φ ∈
      Algebra.adjoin ℂ
        ({b : B | ∃ (u : Multiset (Fin 1 ⊕ Fin 3)) (μ : Fin 1 ⊕ Fin 3)
            (ψ : Module.Dual ℝ 𝔤), b = A u μ ψ} ∪
          {b : B | ∃ (t : Multiset (Fin 1 ⊕ Fin 3)) (χ : Module.Dual ℂ V),
            t.card < n + s.card ∧ b = F t χ}) := by
  induction n generalizing s φ with
  | zero =>
      simp only [covDerivIter_zero, List.ofFn_zero,
        show ((([] : List (Fin 1 ⊕ Fin 3)) : Multiset (Fin 1 ⊕ Fin 3)) = 0) from rfl,
        zero_add, sub_self]
      exact zero_mem _
  | succ n ih =>
      have hmono : ∀ {k m : ℕ}, k ≤ m →
          Algebra.adjoin ℂ
            ({b : B | ∃ u μ ψ, b = A u μ ψ} ∪
              {b : B | ∃ (t : Multiset (Fin 1 ⊕ Fin 3)) (χ : Module.Dual ℂ V),
                t.card < k ∧ b = F t χ}) ≤
          Algebra.adjoin ℂ
            ({b : B | ∃ u μ ψ, b = A u μ ψ} ∪
              {b : B | ∃ (t : Multiset (Fin 1 ⊕ Fin 3)) (χ : Module.Dual ℂ V),
                t.card < m ∧ b = F t χ}) := by
        intro k m hkm
        refine Algebra.adjoin_mono (Set.union_subset_union_right _ ?_)
        rintro b ⟨t, χ, ht, rfl⟩
        exact ⟨t, χ, by omega, rfl⟩
      have hms : ((List.ofFn l : List (Fin 1 ⊕ Fin 3)) : Multiset (Fin 1 ⊕ Fin 3)) + s =
          ((List.ofFn fun i : Fin n => l i.succ : List (Fin 1 ⊕ Fin 3)) :
            Multiset (Fin 1 ⊕ Fin 3)) + (l 0 ::ₘ s) := by
        rw [List.ofFn_succ,
          show (((l 0 :: List.ofFn fun i : Fin n => l i.succ : List (Fin 1 ⊕ Fin 3))) :
              Multiset (Fin 1 ⊕ Fin 3))
            = l 0 ::ₘ ((List.ofFn fun i : Fin n => l i.succ : List (Fin 1 ⊕ Fin 3)) :
              Multiset (Fin 1 ⊕ Fin 3)) from rfl,
          Multiset.cons_add, Multiset.add_cons]
      have hsplit : covDerivIter A act F (n + 1) l s φ -
          F (List.ofFn l + s) φ =
        (covDerivIter A act F n (fun i => l i.succ) (l 0 ::ₘ s) φ -
            F (List.ofFn (fun i : Fin n => l i.succ) + (l 0 ::ₘ s)) φ) +
          actionFamConv A act (l 0) (covDerivIter A act F n fun i => l i.succ) s φ := by
        rw [show covDerivIter A act F (n + 1) l s φ =
              covDerivIter A act F n (fun i => l i.succ) (l 0 ::ₘ s) φ +
                actionFamConv A act (l 0)
                  (covDerivIter A act F n fun i => l i.succ) s φ
            from rfl, hms]
        abel
      rw [hsplit]
      refine add_mem ?_ ?_
      · refine hmono ?_ (ih (fun i => l i.succ) (l 0 ::ₘ s) φ)
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
        · have h3 : covDerivIter A act F n (fun i => l i.succ) p.2 χ =
              (covDerivIter A act F n (fun i => l i.succ) p.2 χ -
                F (List.ofFn (fun i : Fin n => l i.succ) + p.2) χ) +
              F (List.ofFn (fun i : Fin n => l i.succ) + p.2) χ := by abel
          rw [h3]
          refine add_mem (hmono ?_ (ih (fun i => l i.succ) p.2 χ)) ?_
          · omega
          · refine Algebra.subset_adjoin
              (Or.inr ⟨List.ofFn (fun i : Fin n => l i.succ) + p.2, χ, ?_, rfl⟩)
            simp only [Multiset.card_add, Multiset.coe_card, List.length_ofFn]
            omega

/-- Every derivative symbol of the covariant tower is a polynomial in the gauge-field
  symbols and the matter symbols. -/
lemma covDerivIter_mem_adjoin_symbols (act : 𝔤 →ₗ[ℝ] V →ₗ[ℂ] V)
    (F : Multiset (Fin 1 ⊕ Fin 3) → Module.Dual ℂ V →ₗ[ℂ] B)
    (n : ℕ) (l : Fin n → (Fin 1 ⊕ Fin 3)) (s : Multiset (Fin 1 ⊕ Fin 3))
    (φ : Module.Dual ℂ V) :
    covDerivIter A act F n l s φ ∈ Algebra.adjoin ℂ
      ({b : B | ∃ (s : Multiset (Fin 1 ⊕ Fin 3)) (μ : Fin 1 ⊕ Fin 3)
          (ψ : Module.Dual ℝ 𝔤), b = A s μ ψ} ∪
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

/-- **The span lemma**: the algebra of symbols generated by the gauge field together
  with a matter family's *derivative* symbols equals the one generated by the gauge
  field together with the matter family's *covariant* derivative tower. The
  correction `∇_ρ − ∂_ρ` is the derived action of the gauge field — a sum of products
  of symbols, absorbed by the algebra structure. -/
theorem adjoin_symbols_eq_adjoin_covDerivIter (act : 𝔤 →ₗ[ℝ] V →ₗ[ℂ] V)
    (F : Multiset (Fin 1 ⊕ Fin 3) → Module.Dual ℂ V →ₗ[ℂ] B) :
    Algebra.adjoin ℂ
      ({b : B | ∃ (s : Multiset (Fin 1 ⊕ Fin 3)) (μ : Fin 1 ⊕ Fin 3)
          (ψ : Module.Dual ℝ 𝔤), b = A s μ ψ} ∪
        {b : B | ∃ (s : Multiset (Fin 1 ⊕ Fin 3)) (φ : Module.Dual ℂ V),
          b = F s φ}) =
    Algebra.adjoin ℂ
      ({b : B | ∃ (s : Multiset (Fin 1 ⊕ Fin 3)) (μ : Fin 1 ⊕ Fin 3)
          (ψ : Module.Dual ℝ 𝔤), b = A s μ ψ} ∪
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
                (ψ : Module.Dual ℝ 𝔤), b = A s μ ψ} ∪
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
          refine SetLike.le_def.mp (Algebra.adjoin_le ?_)
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

end Action


/-!

## E. Multiplicativity of the adjoint Taylor coefficients

-/

section Leibniz

variable [GaugeJetLeibniz G 𝔤 G₀ 𝔤J]

/-- **The adjoint Taylor coefficients are multiplicative up to convolution**: the
  coefficient of a product of jets of gauge transformations is the antidiagonal
  convolution of the coefficients of the factors. -/
lemma adjointCoeff_mul (U V : G) (x : Multiset (Fin 1 ⊕ Fin 3)) :
    adjointCoeff (𝔤 := 𝔤) (U * V) x
      = (x.antidiagonal.map fun p => adjointCoeff U p.1 ∘ₗ adjointCoeff V p.2).sum := by
  refine LinearMap.ext fun a => ?_
  rw [Multiset.sum_linearMap_apply, Multiset.map_map,
    show adjointCoeff (U * V) x a
      = GaugeJet.evalLie G (𝔤 := 𝔤) (GaugeJet.iteratedDeriv G 𝔤 x (GaugeJet.adjoint 𝔤 (G := G) U
          (GaugeJet.adjoint 𝔤 (G := G) V (GaugeJet.ofConstantLie G (𝔤 := 𝔤) a)))) from by
      rw [adjointCoeff]
      simp only [LinearMap.coe_comp, Function.comp_apply, LieHom.coe_toLinearMap, map_mul,
        Module.End.mul_apply],
    GaugeJetLeibniz.evalLie_iteratedDeriv_adjoint]
  exact congrArg Multiset.sum (Multiset.map_congr rfl fun p hp => by
    rw [Function.comp_apply, LinearMap.comp_apply]
    rfl)

/-- The adjoint Taylor coefficient of the identity: only the base point survives. -/
lemma adjointCoeff_one (p : Multiset (Fin 1 ⊕ Fin 3)) :
    adjointCoeff (𝔤 := 𝔤) (1 : G) p = if p = 0 then LinearMap.id else 0 := by
  refine LinearMap.ext fun a => ?_
  rw [adjointCoeff]
  simp only [LinearMap.coe_comp, Function.comp_apply, LieHom.coe_toLinearMap, map_one,
    Module.End.one_apply]
  rcases eq_or_ne p 0 with rfl | hp
  · rw [GaugeJet.iteratedDeriv_zero, LinearMap.id_apply, GaugeJet.evalLie_ofConstantLie,
      if_pos rfl, LinearMap.id_apply]
  · rw [GaugeJet.iteratedDeriv_ofConstantLie_of_ne_zero hp, map_zero, if_neg hp,
      LinearMap.zero_apply]

end Leibniz

end IsGaugeField


