/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.ClassicalFieldTheory.GaugeTheory.GaugeBoson.Realization.Basic
public import Physlib.Relativity.Tensors.ComplexTensor.Basic
public import Physlib.Relativity.Tensors.RealTensor.Vector.Basic
public import Physlib.Relativity.Tensors.RealTensor.Vector.Representation
public import Physlib.Relativity.SL2C.Basic
/-!
# The gauge law on brackets and iterated derivatives

## i. Overview

The gauge law of a realization, `GaugeAlgebraRealization.gauge_apply_deriv`, gives the
action of a jet `U` on a single derivative symbol `∂_s A_μ^φ`. This file works out what it
does to the expressions built from the symbols: their brackets, the commutator families
`[A_μ, A_ν]` and the derivatives of those. The tools are the tensor-level bookkeeping
`dualPairEquiv` and `tensorBracket`, which let the adjoint index be contracted with a
bracket of the gauge algebra, and the bracket of component families `bracketFam`, whose
gauge transformation `repGauge_bracketFam` is the convolution of the transformations of the
factors against the adjoint Taylor coefficients.

Everything here is stated for a realization `h`; the definitions on families of symbols
(`bracketFam`, `commutatorFam`) take an arbitrary family, so that they also apply to the
covariant families built later.

## ii. Key results

- `GaugeAlgebraRealization.dualPairEquiv`, `GaugeAlgebraRealization.tensorBracket` : the
  tensor bookkeeping of the adjoint index.
- `GaugeAlgebraRealization.bracketFam`, `GaugeAlgebraRealization.commutatorFam` : the
  bracket of two component families, and the derived commutators `∂_s [A_μ, A_ν]`.
- `GaugeAlgebraRealization.repGauge_bracketFam` : the gauge transformation of a bracket.
- `GaugeAlgebraRealization.repGauge_commutatorFam` : the gauge transformation of the derived
  commutators.

-/

@[expose] public section

set_option linter.unusedSectionVars false

open Matrix MatrixGroups TensorProduct MvPowerSeries
variable {B : Type} [Ring B]
variable {G₀ : Type} [Group G₀] {𝔤 : Type} [LieRing 𝔤] [LieAlgebra ℝ 𝔤] [Module.Finite ℝ 𝔤]
variable {GJ : Type} [Group GJ] {𝔤J : Type} [LieRing 𝔤J] [LieAlgebra ℝ 𝔤J]
variable {jets : LocalGaugeData G₀ 𝔤 GJ 𝔤J}


open Lorentz

namespace GaugeAlgebraRealization

section RealScalars

variable [Module ℝ B] [SMulCommClass ℝ B B] [IsScalarTower ℝ B B]

/-- The canonical equivalence, through finite-dimensional duality, between
  algebra-valued fields `B ⊗ 𝔤` and their component families `φ ↦ A^φ`: the element
  `b ⊗ a` corresponds to the family `φ ↦ φ(a) b`. -/
noncomputable def dualPairEquiv :
    (B ⊗[ℝ] 𝔤) ≃ₗ[ℝ] (Module.Dual ℝ 𝔤 →ₗ[ℝ] B) :=
  TensorProduct.comm ℝ B 𝔤 ≪≫ₗ
    TensorProduct.congr (Module.evalEquiv ℝ 𝔤) (LinearEquiv.refl ℝ B) ≪≫ₗ
    dualTensorHomEquiv ℝ (Module.Dual ℝ 𝔤) B

/-- The bracket of two algebra-valued fields: multiplication in `B` on the first
  factors, the Lie bracket of the gauge algebra on the second, so that on pure
  tensors `⁅b₁ ⊗ a₁, b₂ ⊗ a₂⁆ = (b₁ b₂) ⊗ ⁅a₁, a₂⁆`. -/
noncomputable def tensorBracket :
    (B ⊗[ℝ] 𝔤) →ₗ[ℝ] (B ⊗[ℝ] 𝔤) →ₗ[ℝ] B ⊗[ℝ] 𝔤 :=
  TensorProduct.curry
    ((TensorProduct.map (TensorProduct.lift (LinearMap.mul ℝ B))
        (TensorProduct.lift (LinearMap.mk₂ ℝ (fun a b => ⁅a, b⁆)
          (fun a a' b => add_lie a a' b) (fun t a b => smul_lie t a b)
          (fun a b b' => lie_add a b b') (fun t a b => lie_smul t a b)))) ∘ₗ
      (TensorProduct.tensorTensorTensorComm ℝ B 𝔤 B 𝔤).toLinearMap)

/-- The commutator term `⁅A_μ, A_ν⁆` of the field strength, as a component family:
  the physicists' `f^a_{bc} A_μ^b A_ν^c` contracted with a dual adjoint vector, but
  basis-free — the two fields are assembled into `B ⊗ 𝔤` by `dualPairEquiv.symm`,
  bracketed there by `tensorBracket`, and read back out as components. -/
noncomputable def commutator
    (A : Multiset (Fin 1 ⊕ Fin 3) → (Fin 1 ⊕ Fin 3) → Module.Dual ℝ 𝔤 →ₗ[ℝ] B)
    (μ ν : Fin 1 ⊕ Fin 3) : Module.Dual ℝ 𝔤 →ₗ[ℝ] B :=
  dualPairEquiv (tensorBracket (dualPairEquiv.symm (A 0 μ)) (dualPairEquiv.symm (A 0 ν)))

end RealScalars

section ComplexScalars

variable [Algebra ℂ B] {repLorentz : Representation ℂ SL(2,ℂ) B}
  {repGauge : Representation ℂ GJ B}
  {A : Multiset (Fin 1 ⊕ Fin 3) → (Fin 1 ⊕ Fin 3) → Module.Dual ℝ 𝔤 →ₗ[ℝ] B}
  (h : GaugeAlgebraRealization jets B repGauge repLorentz)

/-- The gauge transformation of the underived symbol `A_μ^φ`: the special case `s = 0`
  of `gauge_apply_deriv`, with no Leibniz convolution left over — the dual adjoint
  action of the value of `U⁻¹` plus the Maurer–Cartan shift. -/
lemma repGauge_apply (U : GJ)
    (μ : Fin 1 ⊕ Fin 3) (φ : Module.Dual ℝ 𝔤) :
    repGauge U (h.A 0 μ φ) = h.A 0 μ (jets.adjointDualCoeff U⁻¹ ∅ φ) +
      algebraMap ℂ B (φ (jets.evalLie (jets.maurerCartan U⁻¹ μ))) := by
  simpa [show (∅ : Multiset (Fin 1 ⊕ Fin 3)) = 0 from rfl] using
    h.gauge_apply_deriv U 0 μ φ


/-- The gauge transformation of the once-derived symbol `∂_ρ A_σ`: the case `s = {ρ}`
  of `gauge_apply_deriv` — the two Leibniz splittings of one derivative, plus the
  base-point value of the derived Maurer–Cartan form. -/
lemma repGauge_deriv_apply
    (U : GJ) (ρ σ : Fin 1 ⊕ Fin 3) (φ : Module.Dual ℝ 𝔤) :
    repGauge U (h.A {ρ} σ φ) =
      h.A {ρ} σ (jets.adjointDualCoeff U⁻¹ 0 φ) + h.A 0 σ (jets.adjointDualCoeff U⁻¹ {ρ} φ) +
      algebraMap ℂ B (φ (jets.evalLie
        (jets.deriv ρ (jets.maurerCartan U⁻¹ σ)))) := by
  have hanti : ({ρ} : Multiset (Fin 1 ⊕ Fin 3)).antidiagonal =
      {((0 : Multiset (Fin 1 ⊕ Fin 3)), ({ρ} : Multiset (Fin 1 ⊕ Fin 3))),
        (({ρ} : Multiset (Fin 1 ⊕ Fin 3)), (0 : Multiset (Fin 1 ⊕ Fin 3)))} := by
    rw [show ({ρ} : Multiset (Fin 1 ⊕ Fin 3)) = ρ ::ₘ 0 from rfl,
      Multiset.antidiagonal_cons, Multiset.antidiagonal_zero]
    simp
  have h := h.gauge_apply_deriv U {ρ} σ φ
  rw [hanti] at h
  simp only [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton,
    Multiset.sum_cons, Multiset.sum_singleton,
    LocalGaugeData.iteratedDeriv_singleton] at h
  refine h.trans ?_
  abel

end ComplexScalars

/-!

## Pure-tensor computations for `dualPairEquiv` and `tensorBracket`

-/

section RealScalars

variable [Module ℝ B] [SMulCommClass ℝ B B] [IsScalarTower ℝ B B]

@[simp]
lemma dualPairEquiv_tmul (b : B) (a : 𝔤) (φ : Module.Dual ℝ 𝔤) :
    dualPairEquiv (b ⊗ₜ[ℝ] a) φ = φ a • b := by
  simp [dualPairEquiv, dualTensorHomEquiv, Module.evalEquiv_apply]

@[simp]
lemma tensorBracket_tmul (b₁ b₂ : B) (a₁ a₂ : 𝔤) :
    tensorBracket (b₁ ⊗ₜ[ℝ] a₁) (b₂ ⊗ₜ[ℝ] a₂) = (b₁ * b₂) ⊗ₜ[ℝ] ⁅a₁, a₂⁆ := by
  simp [tensorBracket, TensorProduct.tensorTensorTensorComm_tmul]

lemma dualPairEquiv_map_left (Φ : B →ₗ[ℝ] B) (t : B ⊗[ℝ] 𝔤)
    (φ : Module.Dual ℝ 𝔤) :
    dualPairEquiv ((TensorProduct.map Φ LinearMap.id) t) φ = Φ (dualPairEquiv t φ) := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul b a => simp
  | add x y hx hy => simp [hx, hy]

lemma dualPairEquiv_map_right (T : 𝔤 →ₗ[ℝ] 𝔤)
    (t : B ⊗[ℝ] 𝔤) (φ : Module.Dual ℝ 𝔤) :
    dualPairEquiv ((TensorProduct.map LinearMap.id T) t) φ =
      dualPairEquiv t (T.dualMap φ) := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul b a => simp
  | add x y hx hy => simp [hx, hy]

lemma symm_comp_left (Φ : B →ₗ[ℝ] B) (f : Module.Dual ℝ 𝔤 →ₗ[ℝ] B) :
    dualPairEquiv.symm (Φ ∘ₗ f) =
      (TensorProduct.map Φ LinearMap.id) (dualPairEquiv.symm f) := by
  apply dualPairEquiv.injective
  rw [LinearEquiv.apply_symm_apply]
  refine LinearMap.ext fun φ => ?_
  rw [dualPairEquiv_map_left, LinearEquiv.apply_symm_apply]
  rfl

lemma symm_comp_right (T : 𝔤 →ₗ[ℝ] 𝔤)
    (f : Module.Dual ℝ 𝔤 →ₗ[ℝ] B) :
    dualPairEquiv.symm (f ∘ₗ T.dualMap) =
      (TensorProduct.map LinearMap.id T) (dualPairEquiv.symm f) := by
  apply dualPairEquiv.injective
  rw [LinearEquiv.apply_symm_apply]
  refine LinearMap.ext fun φ => ?_
  rw [dualPairEquiv_map_right, LinearEquiv.apply_symm_apply]
  rfl

lemma tensorBracket_map_left (Φ : B →ₗ[ℝ] B)
    (hΦ : ∀ b₁ b₂, Φ (b₁ * b₂) = Φ b₁ * Φ b₂) (s t : B ⊗[ℝ] 𝔤) :
    tensorBracket ((TensorProduct.map Φ LinearMap.id) s)
        ((TensorProduct.map Φ LinearMap.id) t) =
      (TensorProduct.map Φ LinearMap.id) (tensorBracket s t) := by
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

lemma tensorBracket_map_right (T : 𝔤 →ₗ[ℝ] 𝔤)
    (hT : ∀ a b, T ⁅a, b⁆ = ⁅T a, T b⁆) (s t : B ⊗[ℝ] 𝔤) :
    tensorBracket ((TensorProduct.map LinearMap.id T) s)
        ((TensorProduct.map LinearMap.id T) t) =
      (TensorProduct.map LinearMap.id T) (tensorBracket s t) := by
  induction s using TensorProduct.induction_on with
  | zero => simp
  | tmul b₁ a₁ =>
      induction t using TensorProduct.induction_on with
      | zero => simp
      | tmul b₂ a₂ => simp [hT]
      | add x y hx hy =>
          simp only [map_add]
          rw [hx, hy]
  | add x y hx hy => simp [hx, hy]

lemma tensorBracket_one_right (c : 𝔤) (s : B ⊗[ℝ] 𝔤) :
    tensorBracket s ((1 : B) ⊗ₜ[ℝ] c) =
      -(TensorProduct.map LinearMap.id (LieAlgebra.ad ℝ 𝔤 c)) s := by
  induction s using TensorProduct.induction_on with
  | zero => simp
  | tmul b a =>
      rw [tensorBracket_tmul, mul_one, ← lie_skew, TensorProduct.tmul_neg]
      simp
  | add x y hx hy =>
      simp only [map_add, LinearMap.add_apply]
      rw [hx, hy]
      abel

lemma tensorBracket_one_left (c : 𝔤) (t : B ⊗[ℝ] 𝔤) :
    tensorBracket ((1 : B) ⊗ₜ[ℝ] c) t =
      (TensorProduct.map LinearMap.id (LieAlgebra.ad ℝ 𝔤 c)) t := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul b a => simp
  | add x y hx hy => simp [hx, hy]

end RealScalars

/-!

## The gauge transformation of the commutator

-/

section ComplexScalars

variable [Algebra ℂ B] {repLorentz : Representation ℂ SL(2,ℂ) B}
  {repGauge : Representation ℂ GJ B}
  {A : Multiset (Fin 1 ⊕ Fin 3) → (Fin 1 ⊕ Fin 3) → Module.Dual ℝ 𝔤 →ₗ[ℝ] B}
  (h : GaugeAlgebraRealization jets B repGauge repLorentz)

lemma dualPairEquiv_one_tmul (c : 𝔤) (φ : Module.Dual ℝ 𝔤) :
    dualPairEquiv ((1 : B) ⊗ₜ[ℝ] c) φ = algebraMap ℂ B (φ c) := by
  rw [dualPairEquiv_tmul, Algebra.algebraMap_eq_smul_one,
    show ((φ c : ℝ) : ℂ) = algebraMap ℝ ℂ (φ c) from rfl, algebraMap_smul]

set_option maxHeartbeats 1000000 in
/-- The gauge transformation law of the commutator term: writing the field law as
  `A_μ ↦ Ad₀ A_μ + c_μ` with `Ad₀` the base-point adjoint of `U₀⁻¹` and
  `c_μ = maurerCartan(U⁻¹)_μ|₀` the constant Maurer–Cartan shift, bilinearity of the bracket
  gives

  `⁅A_μ, A_ν⁆ ↦ Ad₀ ⁅A_μ, A_ν⁆ + ⁅Ad₀ A_μ, c_ν⁆ + ⁅c_μ, Ad₀ A_ν⁆ + ⁅c_μ, c_ν⁆`:

  the adjoint-transported commutator, two cross terms linear in the field (the
  bracket against `c` acting on the dual index through `ad`), and the constant
  commutator of the two Maurer–Cartan shifts. Uses that the gauge action is by
  algebra homomorphisms (`gauge_mul`) and that the base-point adjoint transport is a
  morphism of Lie algebras. -/
lemma repGauge_commutator
    (U : GJ) (μ ν : Fin 1 ⊕ Fin 3) (φ : Module.Dual ℝ 𝔤) :
    repGauge U (commutator h.A μ ν φ) =
      commutator h.A μ ν (jets.adjointDualCoeff U⁻¹ 0 φ)
      - h.A 0 μ (jets.adjointDualCoeff U⁻¹ 0 (φ ∘ₗ LieAlgebra.ad ℝ 𝔤
          (jets.evalLie (jets.maurerCartan U⁻¹ ν))))
      + h.A 0 ν (jets.adjointDualCoeff U⁻¹ 0 (φ ∘ₗ LieAlgebra.ad ℝ 𝔤
          (jets.evalLie (jets.maurerCartan U⁻¹ μ))))
      + algebraMap ℂ B (φ ⁅jets.evalLie (jets.maurerCartan U⁻¹ μ),
          jets.evalLie (jets.maurerCartan U⁻¹ ν)⁆) := by
  -- the linear maps and constants of the transformation law
  set Φ : B →ₗ[ℝ] B := (repGauge U).restrictScalars ℝ with hΦdef
  set T₀ : 𝔤 →ₗ[ℝ] 𝔤 :=
    (jets.evalLie).toLinearMap ∘ₗ jets.iteratedDeriv 0 ∘ₗ
      jets.adjoint U⁻¹ ∘ₗ jets.ofConstantLie with hT₀def
  set cμ : 𝔤 := jets.evalLie (jets.maurerCartan U⁻¹ μ) with hcμ
  set cν : 𝔤 := jets.evalLie (jets.maurerCartan U⁻¹ ν) with hcν
  set s : B ⊗[ℝ] 𝔤 := dualPairEquiv.symm (h.A 0 μ) with hs
  set t : B ⊗[ℝ] 𝔤 := dualPairEquiv.symm (h.A 0 ν) with ht
  have hcoeff : jets.adjointDualCoeff U⁻¹ 0 = T₀.dualMap := by rw [hT₀def]; rfl
  -- the base-point adjoint transport is a Lie algebra morphism
  have hT₀lie : ∀ a b : 𝔤, T₀ ⁅a, b⁆ = ⁅T₀ a, T₀ b⁆ := by
    intro a b
    simp [hT₀def, jets.ofConstantLie_lie,
      jets.adjoint_lie,
      LieHom.map_lie]
  -- the transformed component families in tensor form
  have hfam : ∀ (ρ : Fin 1 ⊕ Fin 3),
      Φ ∘ₗ h.A 0 ρ = h.A 0 ρ ∘ₗ T₀.dualMap +
        dualPairEquiv ((1 : B) ⊗ₜ[ℝ] jets.evalLie
          (jets.maurerCartan U⁻¹ ρ)) := by
    intro ρ
    refine LinearMap.ext fun ψ => ?_
    simp only [LinearMap.comp_apply, LinearMap.add_apply, hΦdef,
      LinearMap.restrictScalars_apply]
    rw [h.repGauge_apply U ρ ψ, dualPairEquiv_one_tmul, ← hcoeff]
    rfl
  have hsμ : (TensorProduct.map Φ LinearMap.id) s =
      (TensorProduct.map LinearMap.id T₀) s + (1 : B) ⊗ₜ[ℝ] cμ := by
    rw [hs, ← symm_comp_left, hfam μ, map_add, symm_comp_right,
      LinearEquiv.symm_apply_apply, hcμ]
  have htν : (TensorProduct.map Φ LinearMap.id) t =
      (TensorProduct.map LinearMap.id T₀) t + (1 : B) ⊗ₜ[ℝ] cν := by
    rw [ht, ← symm_comp_left, hfam ν, map_add, symm_comp_right,
      LinearEquiv.symm_apply_apply, hcν]
  -- record the pairing identities, then make the local definitions opaque
  have hcomm_pair : dualPairEquiv (tensorBracket s t) = commutator h.A μ ν := by
    rw [hs, ht]; rfl
  have hπs : dualPairEquiv s = h.A 0 μ := by
    rw [hs]; exact dualPairEquiv.apply_symm_apply _
  have hπt : dualPairEquiv t = h.A 0 ν := by
    rw [ht]; exact dualPairEquiv.apply_symm_apply _
  have hΦmul : ∀ b₁ b₂ : B, Φ (b₁ * b₂) = Φ b₁ * Φ b₂ := fun b₁ b₂ =>
    h.gauge_mul U b₁ b₂
  clear_value Φ T₀ cμ cν s t
  -- the tensor-level transformation of the bracket
  have htensor : (TensorProduct.map Φ LinearMap.id) (tensorBracket s t) =
      (TensorProduct.map LinearMap.id T₀) (tensorBracket s t)
      - (TensorProduct.map LinearMap.id (LieAlgebra.ad ℝ 𝔤 cν))
          ((TensorProduct.map LinearMap.id T₀) s)
      + (TensorProduct.map LinearMap.id (LieAlgebra.ad ℝ 𝔤 cμ))
          ((TensorProduct.map LinearMap.id T₀) t)
      + (1 : B) ⊗ₜ[ℝ] ⁅cμ, cν⁆ := by
    refine (tensorBracket_map_left Φ hΦmul s t).symm.trans
      ((congrArg₂ (fun X Y => tensorBracket X Y) hsμ htν).trans ?_)
    simp only [map_add, LinearMap.add_apply]
    rw [tensorBracket_map_right T₀ hT₀lie, tensorBracket_one_right,
      tensorBracket_one_left, tensorBracket_tmul, one_mul]
    abel
  -- read the tensor identity back through the pairing
  have hread := congrArg (fun z => dualPairEquiv z φ) htensor
  simp only [map_add, map_sub, LinearMap.add_apply, LinearMap.sub_apply,
    dualPairEquiv_map_left, dualPairEquiv_map_right,
    dualPairEquiv_one_tmul] at hread
  rw [show repGauge U (commutator h.A μ ν φ) = Φ (dualPairEquiv (tensorBracket s t) φ) from by
      rw [← hcomm_pair, hΦdef]; rfl,
    hread, hcoeff, hcomm_pair, hπs, hπt]
  rfl

/-!

## Second derivatives of the gauge field

-/

/-- The gauge transformation of the twice-derived symbol `∂_ρ ∂_σ A_τ`: the case
  `s = ρ ::ₘ {σ}` of `gauge_apply_deriv` — the four Leibniz splittings of two
  derivatives, plus the base-point value of the twice-derived Maurer–Cartan form. -/
lemma repGauge_deriv_deriv_apply
    (U : GJ) (ρ σ τ : Fin 1 ⊕ Fin 3) (φ : Module.Dual ℝ 𝔤) :
    repGauge U (h.A (ρ ::ₘ {σ}) τ φ) =
      h.A (ρ ::ₘ {σ}) τ (jets.adjointDualCoeff U⁻¹ 0 φ)
      + h.A {ρ} τ (jets.adjointDualCoeff U⁻¹ {σ} φ)
      + h.A {σ} τ (jets.adjointDualCoeff U⁻¹ {ρ} φ)
      + h.A 0 τ (jets.adjointDualCoeff U⁻¹ (ρ ::ₘ {σ}) φ)
      + algebraMap ℂ B (φ (jets.evalLie (jets.deriv ρ
          (jets.deriv σ (jets.maurerCartan U⁻¹ τ))))) := by
  have hanti₁ : ({σ} : Multiset (Fin 1 ⊕ Fin 3)).antidiagonal =
      {((0 : Multiset (Fin 1 ⊕ Fin 3)), ({σ} : Multiset (Fin 1 ⊕ Fin 3))),
        (({σ} : Multiset (Fin 1 ⊕ Fin 3)), (0 : Multiset (Fin 1 ⊕ Fin 3)))} := by
    rw [show ({σ} : Multiset (Fin 1 ⊕ Fin 3)) = σ ::ₘ 0 from rfl,
      Multiset.antidiagonal_cons, Multiset.antidiagonal_zero]
    simp
  have hanti : (ρ ::ₘ ({σ} : Multiset (Fin 1 ⊕ Fin 3))).antidiagonal =
      {(({ρ} : Multiset (Fin 1 ⊕ Fin 3)), ({σ} : Multiset (Fin 1 ⊕ Fin 3))),
        ((0 : Multiset (Fin 1 ⊕ Fin 3)), ρ ::ₘ ({σ} : Multiset (Fin 1 ⊕ Fin 3))),
        (({σ} : Multiset (Fin 1 ⊕ Fin 3)), ({ρ} : Multiset (Fin 1 ⊕ Fin 3))),
        (ρ ::ₘ ({σ} : Multiset (Fin 1 ⊕ Fin 3)), (0 : Multiset (Fin 1 ⊕ Fin 3)))} := by
    rw [Multiset.antidiagonal_cons, hanti₁]
    simp [Multiset.insert_eq_cons]
  have h := h.gauge_apply_deriv U (ρ ::ₘ {σ}) τ φ
  rw [hanti] at h
  simp only [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton,
    Multiset.sum_cons, Multiset.sum_singleton, LocalGaugeData.iteratedDeriv_cons,
    LinearMap.comp_apply, LocalGaugeData.iteratedDeriv_singleton] at h
  refine h.trans ?_
  abel

end ComplexScalars

/-!

## The bracket of general component families

-/

section RealScalars

variable [Module ℝ B] [SMulCommClass ℝ B B] [IsScalarTower ℝ B B]

/-- The bracket of two arbitrary component families, generalizing `commutator` (which
  is the case of two field symbols): assemble into `B ⊗ 𝔤` by `dualPairEquiv.symm`,
  bracket by `tensorBracket`, read back out as components. -/
noncomputable def bracketFam (f g : Module.Dual ℝ 𝔤 →ₗ[ℝ] B) :
    Module.Dual ℝ 𝔤 →ₗ[ℝ] B :=
  dualPairEquiv (tensorBracket (dualPairEquiv.symm f) (dualPairEquiv.symm g))

lemma commutator_eq_bracketFam
    (A : Multiset (Fin 1 ⊕ Fin 3) → (Fin 1 ⊕ Fin 3) → Module.Dual ℝ 𝔤 →ₗ[ℝ] B)
    (μ ν : Fin 1 ⊕ Fin 3) : commutator A μ ν = bracketFam (A 0 μ) (A 0 ν) := rfl

/-- **The derived commutator family**: the `s`-derivative of the commutator term, given
  by the Leibniz convolution of the derivative symbols over the multiset antidiagonal.
  With the derivative symbols as primitives this convolution is the definition; for
  `s = 0` it is the commutator itself (`commutatorFam_zero`). -/
noncomputable def commutatorFam
    (A : Multiset (Fin 1 ⊕ Fin 3) → (Fin 1 ⊕ Fin 3) → Module.Dual ℝ 𝔤 →ₗ[ℝ] B)
    (μ ν : Fin 1 ⊕ Fin 3) (s : Multiset (Fin 1 ⊕ Fin 3)) :
    Module.Dual ℝ 𝔤 →ₗ[ℝ] B :=
  (s.antidiagonal.map fun p => bracketFam (A p.1 μ) (A p.2 ν)).sum

lemma commutatorFam_zero
    (A : Multiset (Fin 1 ⊕ Fin 3) → (Fin 1 ⊕ Fin 3) → Module.Dual ℝ 𝔤 →ₗ[ℝ] B)
    (μ ν : Fin 1 ⊕ Fin 3) : commutatorFam A μ ν 0 = commutator A μ ν := by
  rw [commutatorFam, Multiset.antidiagonal_zero, Multiset.map_singleton,
    Multiset.sum_singleton, commutator_eq_bracketFam]

lemma bracketFam_add_left (f₁ f₂ g : Module.Dual ℝ 𝔤 →ₗ[ℝ] B) :
    bracketFam (f₁ + f₂) g = bracketFam f₁ g + bracketFam f₂ g := by
  simp only [bracketFam, map_add, LinearMap.add_apply]

lemma bracketFam_add_right (f g₁ g₂ : Module.Dual ℝ 𝔤 →ₗ[ℝ] B) :
    bracketFam f (g₁ + g₂) = bracketFam f g₁ + bracketFam f g₂ := by
  simp only [bracketFam, map_add]

lemma bracketFam_smul_left (c : ℝ) (f g : Module.Dual ℝ 𝔤 →ₗ[ℝ] B) :
    bracketFam (c • f) g = c • bracketFam f g := by
  simp only [bracketFam, map_smul, LinearMap.smul_apply]

lemma bracketFam_smul_right (c : ℝ) (f g : Module.Dual ℝ 𝔤 →ₗ[ℝ] B) :
    bracketFam f (c • g) = c • bracketFam f g := by
  simp only [bracketFam, map_smul]

/-- The bracket of two component families expanded through a basis of the gauge
  algebra: the physicists' `f^a_{bc} f^b g^c`, with `φ⁅e_j, e_k⁆` the structure
  constants contracted with the dual vector. -/
lemma bracketFam_apply_eq_sum (f g : Module.Dual ℝ 𝔤 →ₗ[ℝ] B)
    (φ : Module.Dual ℝ 𝔤) :
    bracketFam f g φ = ∑ j, ∑ k,
      φ ⁅Module.Free.chooseBasis ℝ 𝔤 j,
          Module.Free.chooseBasis ℝ 𝔤 k⁆ •
        (f ((Module.Free.chooseBasis ℝ 𝔤).coord j) *
          g ((Module.Free.chooseBasis ℝ 𝔤).coord k)) := by
  classical
  set bv := Module.Free.chooseBasis ℝ 𝔤 with hbv
  have hdual : ∀ ψ : Module.Dual ℝ 𝔤, ∑ j, ψ (bv j) • bv.coord j = ψ := by
    intro ψ
    refine LinearMap.ext fun x => ?_
    conv_rhs => rw [← bv.sum_repr x, map_sum]
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, Module.Basis.coord_apply,
      smul_eq_mul, map_smul]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  have hbasis : ∀ h : Module.Dual ℝ 𝔤 →ₗ[ℝ] B,
      dualPairEquiv.symm h = ∑ j, h (bv.coord j) ⊗ₜ[ℝ] bv j := by
    intro h
    apply dualPairEquiv.injective
    rw [LinearEquiv.apply_symm_apply]
    refine LinearMap.ext fun ψ => ?_
    calc h ψ = h (∑ j, ψ (bv j) • bv.coord j) := by rw [hdual]
      _ = ∑ j, ψ (bv j) • h (bv.coord j) := by
          rw [map_sum]
          exact Finset.sum_congr rfl fun j _ => map_smul h _ _
      _ = dualPairEquiv (∑ j, h (bv.coord j) ⊗ₜ[ℝ] bv j) ψ := by simp
  rw [bracketFam, hbasis f, hbasis g]
  simp [tensorBracket_tmul, dualPairEquiv_tmul]
  rw [Finset.sum_comm]

/-- The bracket of families is natural in the algebra: a multiplicative linear map carries
  the bracket of two families to the bracket of their images. -/
lemma bracketFam_map {B' : Type} [Ring B'] [Module ℝ B'] [SMulCommClass ℝ B' B']
    [IsScalarTower ℝ B' B'] (Φ : B →ₗ[ℝ] B') (hΦ : ∀ b₁ b₂, Φ (b₁ * b₂) = Φ b₁ * Φ b₂)
    (f g : Module.Dual ℝ 𝔤 →ₗ[ℝ] B) :
    bracketFam (Φ ∘ₗ f) (Φ ∘ₗ g) = Φ ∘ₗ bracketFam f g := by
  refine LinearMap.ext fun φ => ?_
  rw [LinearMap.comp_apply, bracketFam_apply_eq_sum, bracketFam_apply_eq_sum, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_smul, hΦ]
  rfl

/-- The derived commutator family is natural in the algebra. -/
lemma commutatorFam_map {B' : Type} [Ring B'] [Module ℝ B'] [SMulCommClass ℝ B' B']
    [IsScalarTower ℝ B' B'] (Φ : B →ₗ[ℝ] B') (hΦ : ∀ b₁ b₂, Φ (b₁ * b₂) = Φ b₁ * Φ b₂)
    (A : Multiset (Fin 1 ⊕ Fin 3) → (Fin 1 ⊕ Fin 3) → Module.Dual ℝ 𝔤 →ₗ[ℝ] B)
    (μ ν : Fin 1 ⊕ Fin 3) (s : Multiset (Fin 1 ⊕ Fin 3)) :
    commutatorFam (fun p ρ => Φ ∘ₗ A p ρ) μ ν s = Φ ∘ₗ commutatorFam A μ ν s := by
  refine LinearMap.ext fun φ => ?_
  rw [LinearMap.comp_apply, commutatorFam, commutatorFam, Multiset.sum_linearMap_apply,
    Multiset.sum_linearMap_apply, Multiset.map_map, Multiset.map_map, map_multiset_sum,
    Multiset.map_map]
  refine congrArg Multiset.sum (Multiset.map_congr rfl fun p _ => ?_)
  simp only [Function.comp_apply]
  rw [bracketFam_map Φ hΦ]
  rfl

/-- The bracket of families against a common Lie-algebra morphism on the dual index. -/
lemma bracketFam_comp_dualMap (T : 𝔤 →ₗ[ℝ] 𝔤)
    (hT : ∀ a b, T ⁅a, b⁆ = ⁅T a, T b⁆) (f g : Module.Dual ℝ 𝔤 →ₗ[ℝ] B) :
    bracketFam (f ∘ₗ T.dualMap) (g ∘ₗ T.dualMap) = bracketFam f g ∘ₗ T.dualMap := by
  refine LinearMap.ext fun φ => ?_
  show dualPairEquiv (tensorBracket (dualPairEquiv.symm (f ∘ₗ T.dualMap))
      (dualPairEquiv.symm (g ∘ₗ T.dualMap))) φ = bracketFam f g (T.dualMap φ)
  rw [symm_comp_right, symm_comp_right, tensorBracket_map_right T hT,
    dualPairEquiv_map_right]
  rfl

/-- `tensorBracket` is a derivation in the algebra factor: for `Δ` satisfying the
  Leibniz rule on `B`, applying `Δ ⊗ id` to a bracket distributes over the two
  arguments. -/
lemma tensorBracket_map_left_derivation (Δ : B →ₗ[ℝ] B)
    (hΔ : ∀ b₁ b₂, Δ (b₁ * b₂) = Δ b₁ * b₂ + b₁ * Δ b₂) (s t : B ⊗[ℝ] 𝔤) :
    (TensorProduct.map Δ LinearMap.id) (tensorBracket s t) =
      tensorBracket ((TensorProduct.map Δ LinearMap.id) s) t +
      tensorBracket s ((TensorProduct.map Δ LinearMap.id) t) := by
  induction s using TensorProduct.induction_on with
  | zero => simp
  | tmul b₁ a₁ =>
      induction t using TensorProduct.induction_on with
      | zero => simp
      | tmul b₂ a₂ => simp [hΔ, TensorProduct.add_tmul]
      | add x y hx hy =>
          simp only [map_add, hx, hy]
          abel
  | add x y hx hy =>
      simp only [map_add, LinearMap.add_apply, hx, hy]
      abel

/-- The bracket of families under a derivation of the algebra: the Leibniz rule, in
  family form. -/
lemma bracketFam_derivation (Δ : B →ₗ[ℝ] B)
    (hΔ : ∀ b₁ b₂, Δ (b₁ * b₂) = Δ b₁ * b₂ + b₁ * Δ b₂) (f g : Module.Dual ℝ 𝔤 →ₗ[ℝ] B) :
    Δ ∘ₗ bracketFam f g = bracketFam (Δ ∘ₗ f) g + bracketFam f (Δ ∘ₗ g) := by
  refine LinearMap.ext fun φ => ?_
  show Δ (dualPairEquiv (tensorBracket (dualPairEquiv.symm f) (dualPairEquiv.symm g)) φ) = _
  rw [← dualPairEquiv_map_left, tensorBracket_map_left_derivation Δ hΔ, map_add,
    LinearMap.add_apply, ← symm_comp_left, ← symm_comp_left]
  rfl

/-- `tensorBracket` under a relative derivation on the Lie factor: if
  `T₁ ⁅a, b⁆ = ⁅T₁ a, T₀ b⁆ + ⁅T₀ a, T₁ b⁆`, the two mixed brackets sum to the
  `T₁`-image of the bracket. This is how the once-derived adjoint transport
  distributes over the commutator. -/
lemma tensorBracket_map_right_derivation (T₀ T₁ : 𝔤 →ₗ[ℝ] 𝔤)
    (hT : ∀ a b, T₁ ⁅a, b⁆ = ⁅T₁ a, T₀ b⁆ + ⁅T₀ a, T₁ b⁆) (s t : B ⊗[ℝ] 𝔤) :
    tensorBracket ((TensorProduct.map LinearMap.id T₁) s)
        ((TensorProduct.map LinearMap.id T₀) t) +
      tensorBracket ((TensorProduct.map LinearMap.id T₀) s)
        ((TensorProduct.map LinearMap.id T₁) t) =
      (TensorProduct.map LinearMap.id T₁) (tensorBracket s t) := by
  induction s using TensorProduct.induction_on with
  | zero => simp
  | tmul b₁ a₁ =>
      induction t using TensorProduct.induction_on with
      | zero => simp
      | tmul b₂ a₂ => simp [hT, TensorProduct.tmul_add]
      | add x y hx hy =>
          simp only [map_add]
          rw [← hx, ← hy]
          abel
  | add x y hx hy =>
      simp only [map_add, LinearMap.add_apply]
      rw [← hx, ← hy]
      abel

/-- The family-level form of `tensorBracket_map_right_derivation`: a relative
  derivation on the dual index distributes over the bracket of families. -/
lemma bracketFam_dualMap_derivation (T₀ T₁ : 𝔤 →ₗ[ℝ] 𝔤)
    (hT : ∀ a b, T₁ ⁅a, b⁆ = ⁅T₁ a, T₀ b⁆ + ⁅T₀ a, T₁ b⁆)
    (f g : Module.Dual ℝ 𝔤 →ₗ[ℝ] B) :
    bracketFam (f ∘ₗ T₁.dualMap) (g ∘ₗ T₀.dualMap) +
      bracketFam (f ∘ₗ T₀.dualMap) (g ∘ₗ T₁.dualMap) =
      bracketFam f g ∘ₗ T₁.dualMap := by
  refine LinearMap.ext fun φ => ?_
  show dualPairEquiv (tensorBracket (dualPairEquiv.symm (f ∘ₗ T₁.dualMap))
        (dualPairEquiv.symm (g ∘ₗ T₀.dualMap))) φ +
      dualPairEquiv (tensorBracket (dualPairEquiv.symm (f ∘ₗ T₀.dualMap))
        (dualPairEquiv.symm (g ∘ₗ T₁.dualMap))) φ =
      bracketFam f g (T₁.dualMap φ)
  rw [symm_comp_right, symm_comp_right, symm_comp_right, symm_comp_right,
    ← LinearMap.add_apply, ← map_add, tensorBracket_map_right_derivation T₀ T₁ hT,
    dualPairEquiv_map_right]
  rfl

end RealScalars

section ComplexScalars

variable [Algebra ℂ B] {repLorentz : Representation ℂ SL(2,ℂ) B}
  {repGauge : Representation ℂ GJ B}
  {A : Multiset (Fin 1 ⊕ Fin 3) → (Fin 1 ⊕ Fin 3) → Module.Dual ℝ 𝔤 →ₗ[ℝ] B}
  (h : GaugeAlgebraRealization jets B repGauge repLorentz)

include h in
set_option maxHeartbeats 1000000 in
/-- The gauge transformation of the bracket of two component families with affine
  transformation laws `f ↦ f' + φ(c_f)·1` and `g ↦ g' + φ(c_g)·1`: the bracket of the
  transformed families, two `ad` cross terms, and the constant bracket `⁅c_f, c_g⁆`.
  Pure bilinearity, with `tensorBracket_one_left/right` computing the cross terms;
  `repGauge_commutator` is the special case of two field symbols. -/
lemma repGauge_bracketFam
    (U : GJ) {f g f' g' : Module.Dual ℝ 𝔤 →ₗ[ℝ] B}
    {cf cg : 𝔤}
    (hf : ∀ ψ : Module.Dual ℝ 𝔤,
      repGauge U (f ψ) = f' ψ + algebraMap ℂ B (ψ cf))
    (hg : ∀ ψ : Module.Dual ℝ 𝔤,
      repGauge U (g ψ) = g' ψ + algebraMap ℂ B (ψ cg))
    (φ : Module.Dual ℝ 𝔤) :
    repGauge U (bracketFam f g φ) =
      bracketFam f' g' φ
      + g' (φ ∘ₗ LieAlgebra.ad ℝ 𝔤 cf)
      - f' (φ ∘ₗ LieAlgebra.ad ℝ 𝔤 cg)
      + algebraMap ℂ B (φ ⁅cf, cg⁆) := by
  set Φ : B →ₗ[ℝ] B := (repGauge U).restrictScalars ℝ with hΦdef
  have hΦmul : ∀ b₁ b₂ : B, Φ (b₁ * b₂) = Φ b₁ * Φ b₂ := fun b₁ b₂ =>
    h.gauge_mul U b₁ b₂
  set s : B ⊗[ℝ] 𝔤 := dualPairEquiv.symm f with hs
  set t : B ⊗[ℝ] 𝔤 := dualPairEquiv.symm g with ht
  set s' : B ⊗[ℝ] 𝔤 := dualPairEquiv.symm f' with hs'
  set t' : B ⊗[ℝ] 𝔤 := dualPairEquiv.symm g' with ht'
  have hfm : (TensorProduct.map Φ LinearMap.id) s = s' + (1 : B) ⊗ₜ[ℝ] cf := by
    rw [hs, hs', ← symm_comp_left,
      show Φ ∘ₗ f = f' + dualPairEquiv ((1 : B) ⊗ₜ[ℝ] cf) from
        LinearMap.ext fun ψ => by
          simp only [LinearMap.comp_apply, LinearMap.add_apply, hΦdef,
            LinearMap.restrictScalars_apply]
          rw [hf ψ, dualPairEquiv_one_tmul],
      map_add, LinearEquiv.symm_apply_apply]
  have hgm : (TensorProduct.map Φ LinearMap.id) t = t' + (1 : B) ⊗ₜ[ℝ] cg := by
    rw [ht, ht', ← symm_comp_left,
      show Φ ∘ₗ g = g' + dualPairEquiv ((1 : B) ⊗ₜ[ℝ] cg) from
        LinearMap.ext fun ψ => by
          simp only [LinearMap.comp_apply, LinearMap.add_apply, hΦdef,
            LinearMap.restrictScalars_apply]
          rw [hg ψ, dualPairEquiv_one_tmul],
      map_add, LinearEquiv.symm_apply_apply]
  have hbra : dualPairEquiv (tensorBracket s t) = bracketFam f g := by
    rw [hs, ht]; rfl
  have hbra' : dualPairEquiv (tensorBracket s' t') = bracketFam f' g' := by
    rw [hs', ht']; rfl
  have hπs' : dualPairEquiv s' = f' := by
    rw [hs']; exact dualPairEquiv.apply_symm_apply _
  have hπt' : dualPairEquiv t' = g' := by
    rw [ht']; exact dualPairEquiv.apply_symm_apply _
  clear_value Φ s t s' t'
  have htensor : (TensorProduct.map Φ LinearMap.id) (tensorBracket s t) =
      tensorBracket s' t'
      + (TensorProduct.map LinearMap.id (LieAlgebra.ad ℝ 𝔤 cf)) t'
      - (TensorProduct.map LinearMap.id (LieAlgebra.ad ℝ 𝔤 cg)) s'
      + (1 : B) ⊗ₜ[ℝ] ⁅cf, cg⁆ := by
    refine (tensorBracket_map_left Φ hΦmul s t).symm.trans
      ((congrArg₂ (fun X Y => tensorBracket X Y) hfm hgm).trans ?_)
    simp only [map_add, LinearMap.add_apply]
    rw [tensorBracket_one_right, tensorBracket_one_left, tensorBracket_tmul, one_mul]
    abel
  have hread := congrArg (fun z => dualPairEquiv z φ) htensor
  simp only [map_add, map_sub, LinearMap.add_apply, LinearMap.sub_apply,
    dualPairEquiv_map_left, dualPairEquiv_map_right, dualPairEquiv_one_tmul] at hread
  rw [show repGauge U (bracketFam f g φ) = Φ (dualPairEquiv (tensorBracket s t) φ) from by
      rw [hbra, hΦdef]; rfl,
    hread, hbra', hπs', hπt']
  rfl


/-!

## Multiset combinatorics for iterated Leibniz sums

The convolution sums of the iterated transformation laws are indexed by the multiset
antidiagonal. The two lemmas below are the coassociativity and cocommutativity-exchange
of this "comultiplication": a sum over splittings-of-splittings does not depend on the
grouping. Both are proven by a cons-induction with the summand universally quantified,
so that the inductive hypothesis absorbs the modified summands.

-/

/-- Every derived commutator term is a polynomial in derivative symbols of order at
  most that of the derivative: each Leibniz splitting contributes a product of two
  lower-order symbols. -/
lemma commutatorFam_mem
    (A : Multiset (Fin 1 ⊕ Fin 3) → (Fin 1 ⊕ Fin 3) → Module.Dual ℝ 𝔤 →ₗ[ℝ] B)
    (s' : Multiset (Fin 1 ⊕ Fin 3)) (ν lam : Fin 1 ⊕ Fin 3)
    (φ : Module.Dual ℝ 𝔤) :
    commutatorFam A ν lam s' φ ∈
      Algebra.adjoin ℂ {b : B | ∃ (p : Multiset (Fin 1 ⊕ Fin 3)) (μ : Fin 1 ⊕ Fin 3)
        (φ : Module.Dual ℝ 𝔤), p.card ≤ s'.card ∧ b = A p μ φ} := by
  classical
  rw [commutatorFam, Multiset.sum_linearMap_apply, Multiset.map_map]
  refine multiset_sum_mem _ fun x hx => ?_
  obtain ⟨p, hp, rfl⟩ := Multiset.mem_map.mp hx
  have hle := Multiset.mem_antidiagonal.mp hp
  rw [Function.comp_apply, bracketFam_apply_eq_sum]
  refine Subalgebra.sum_mem _ fun j _ => Subalgebra.sum_mem _ fun k _ => ?_
  rw [← algebraMap_smul ℂ (φ ⁅Module.Free.chooseBasis ℝ 𝔤 j,
      Module.Free.chooseBasis ℝ 𝔤 k⁆)]
  refine Subalgebra.smul_mem _ ?_ _
  refine mul_mem
    (Algebra.subset_adjoin ⟨p.1, ν, (Module.Free.chooseBasis ℝ 𝔤).coord j, ?_, rfl⟩)
    (Algebra.subset_adjoin ⟨p.2, lam, (Module.Free.chooseBasis ℝ 𝔤).coord k, ?_, rfl⟩)
  · exact hle ▸ Multiset.card_le_card (Multiset.le_add_right _ _)
  · exact hle ▸ Multiset.card_le_card (Multiset.le_add_left _ _)

end ComplexScalars

/-!

## Iterated Leibniz expansions

-/

section RealScalars

variable [Module ℝ B] [SMulCommClass ℝ B B] [IsScalarTower ℝ B B]

lemma bracketFam_zero_left (g : Module.Dual ℝ 𝔤 →ₗ[ℝ] B) :
    bracketFam 0 g = 0 := by
  simp [bracketFam]

lemma bracketFam_zero_right (f : Module.Dual ℝ 𝔤 →ₗ[ℝ] B) :
    bracketFam f 0 = 0 := by
  simp [bracketFam]

lemma bracketFam_sum_left (S : Multiset (Module.Dual ℝ 𝔤 →ₗ[ℝ] B))
    (g : Module.Dual ℝ 𝔤 →ₗ[ℝ] B) :
    bracketFam S.sum g = (S.map fun f => bracketFam f g).sum := by
  induction S using Multiset.induction_on with
  | empty => simp [bracketFam_zero_left]
  | cons f S ih => simp [bracketFam_add_left, ih]

lemma bracketFam_sum_right (f : Module.Dual ℝ 𝔤 →ₗ[ℝ] B)
    (S : Multiset (Module.Dual ℝ 𝔤 →ₗ[ℝ] B)) :
    bracketFam f S.sum = (S.map fun g => bracketFam f g).sum := by
  induction S using Multiset.induction_on with
  | empty => simp [bracketFam_zero_right]
  | cons g S ih => simp [bracketFam_add_right, ih]

lemma bracketFam_finset_sum_left {ι : Type*} (S : Finset ι)
    (f : ι → Module.Dual ℝ 𝔤 →ₗ[ℝ] B) (g : Module.Dual ℝ 𝔤 →ₗ[ℝ] B) :
    bracketFam (∑ i ∈ S, f i) g = ∑ i ∈ S, bracketFam (f i) g := by
  simp only [bracketFam, map_sum, LinearMap.sum_apply]

lemma bracketFam_finset_sum_right {ι : Type*} (S : Finset ι)
    (f : Module.Dual ℝ 𝔤 →ₗ[ℝ] B) (g : ι → Module.Dual ℝ 𝔤 →ₗ[ℝ] B) :
    bracketFam f (∑ i ∈ S, g i) = ∑ i ∈ S, bracketFam f (g i) := by
  simp only [bracketFam, map_sum]

/-!

## The bracket of families against the adjoint coefficients

-/

/-- `tensorBracket` under an antidiagonal family of transports on the Lie factor:
  if `T x` distributes over the bracket as the antidiagonal convolution of the
  `T m`, so does `id ⊗ T x` over `tensorBracket`. -/
lemma tensorBracket_map_right_antidiagonal
    (T : Multiset (Fin 1 ⊕ Fin 3) → 𝔤 →ₗ[ℝ] 𝔤)
    (x : Multiset (Fin 1 ⊕ Fin 3))
    (hT : ∀ a b : 𝔤, T x ⁅a, b⁆ =
      (x.antidiagonal.map fun p => ⁅T p.1 a, T p.2 b⁆).sum)
    (s t : B ⊗[ℝ] 𝔤) :
    (x.antidiagonal.map fun p =>
      tensorBracket ((TensorProduct.map LinearMap.id (T p.1)) s)
        ((TensorProduct.map LinearMap.id (T p.2)) t)).sum =
      (TensorProduct.map LinearMap.id (T x)) (tensorBracket s t) := by
  induction s using TensorProduct.induction_on with
  | zero => simp
  | tmul b₁ a₁ =>
      induction t using TensorProduct.induction_on with
      | zero => simp
      | tmul b₂ a₂ =>
          simp only [tensorBracket_tmul, TensorProduct.map_tmul, LinearMap.id_coe, id_eq]
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

/-- The bracket of families against an iterated dual adjoint coefficient: the
  antidiagonal convolution — the all-orders form of `bracketFam_comp_dualMap` and
  `bracketFam_dualMap_derivation`. -/
lemma bracketFam_adjointDualCoeff (U : GJ) (x : Multiset (Fin 1 ⊕ Fin 3))
    (f g : Module.Dual ℝ 𝔤 →ₗ[ℝ] B) (φ : Module.Dual ℝ 𝔤) :
    bracketFam f g (jets.adjointDualCoeff U x φ) =
      (x.antidiagonal.map fun p =>
        bracketFam (f ∘ₗ jets.adjointDualCoeff U p.1)
          (g ∘ₗ jets.adjointDualCoeff U p.2) φ).sum := by
  have hcoeff : ∀ m, jets.adjointDualCoeff U m = (jets.adjointCoeff U m).dualMap :=
    fun m => rfl
  rw [hcoeff x,
    show bracketFam f g ((jets.adjointCoeff U x).dualMap φ) =
      dualPairEquiv ((TensorProduct.map LinearMap.id (jets.adjointCoeff U x)) (tensorBracket
        (dualPairEquiv.symm f) (dualPairEquiv.symm g))) φ from
      (dualPairEquiv_map_right (jets.adjointCoeff U x) _ φ).symm,
    ← tensorBracket_map_right_antidiagonal (jets.adjointCoeff U) x (jets.adjointCoeff_lie U x),
    map_multiset_sum, Multiset.map_map, Multiset.sum_linearMap_apply, Multiset.map_map]
  refine congrArg Multiset.sum (Multiset.map_congr rfl fun p hp => ?_)
  simp only [Function.comp_apply]
  rw [← symm_comp_right, ← symm_comp_right, hcoeff p.1, hcoeff p.2]
  rfl

end RealScalars

/-!

## The gauge transformation of iterated derivatives

-/

section ComplexScalars

variable [Algebra ℂ B] {repLorentz : Representation ℂ SL(2,ℂ) B}
  {repGauge : Representation ℂ GJ B}
  {A : Multiset (Fin 1 ⊕ Fin 3) → (Fin 1 ⊕ Fin 3) → Module.Dual ℝ 𝔤 →ₗ[ℝ] B}
  (h : GaugeAlgebraRealization jets B repGauge repLorentz)

/-- The `κ ::ₘ s` case of `gauge_apply_deriv` with the extra derivative traced through:
  the Leibniz splittings where `κ` stays a derivative, minus (by
  `LocalGaugeData.adjointDualCoeff_cons`) the splittings where `κ` hits the adjoint — an `ad` of the
  derived Maurer–Cartan form — plus the derived Maurer–Cartan shift. -/
lemma repGauge_cons_apply
    (U : GJ) (κ : Fin 1 ⊕ Fin 3) (s : Multiset (Fin 1 ⊕ Fin 3))
    (τ : Fin 1 ⊕ Fin 3) (φ : Module.Dual ℝ 𝔤) :
    repGauge U (h.A (κ ::ₘ s) τ φ) =
      (s.antidiagonal.map fun p =>
        h.A (κ ::ₘ p.2) τ (jets.adjointDualCoeff U⁻¹ p.1 φ)).sum
      - (s.antidiagonal.map fun p =>
          (p.1.antidiagonal.map fun q =>
            h.A p.2 τ (jets.adjointDualCoeff U⁻¹ q.2
              (φ ∘ₗ LieAlgebra.ad ℝ 𝔤 (jets.evalLie
                (jets.iteratedDeriv q.1 (jets.maurerCartan U⁻¹ κ)))))).sum).sum
      + algebraMap ℂ B (φ (jets.evalLie (jets.iteratedDeriv (κ ::ₘ s)
          (jets.maurerCartan U⁻¹ τ)))) := by
  rw [h.gauge_apply_deriv U (κ ::ₘ s) τ φ]
  congr 1
  simp only [Multiset.antidiagonal_cons, Multiset.map_add, Multiset.sum_add,
    Multiset.map_map, Function.comp_apply, Prod.map_fst, Prod.map_snd, id_eq]
  have hsec : (Multiset.map (fun p =>
        h.A p.2 τ (jets.adjointDualCoeff U⁻¹ (κ ::ₘ p.1) φ)) s.antidiagonal).sum =
      -(s.antidiagonal.map fun p =>
          (p.1.antidiagonal.map fun q =>
            h.A p.2 τ (jets.adjointDualCoeff U⁻¹ q.2
              (φ ∘ₗ LieAlgebra.ad ℝ 𝔤 (jets.evalLie
                (jets.iteratedDeriv q.1 (jets.maurerCartan U⁻¹ κ)))))).sum).sum := by
    rw [← Multiset.sum_map_neg'']
    refine congrArg Multiset.sum (Multiset.map_congr rfl fun p hp => ?_)
    rw [jets.adjointDualCoeff_cons U⁻¹ κ p.1 φ, map_neg, map_multiset_sum, Multiset.map_map]
    exact congrArg Neg.neg (congrArg Multiset.sum (Multiset.map_congr rfl fun q hq => rfl))
  rw [hsec, sub_eq_add_neg]

set_option maxHeartbeats 2000000 in
/-- The all-orders gauge transformation of the derived commutator term: the Leibniz
  convolution of the transformed commutator, the two `ad` cross-term convolutions,
  and the convolution of Maurer–Cartan bracket shifts. This is `repGauge_commutator`
  at every derivative order simultaneously; the regrouping of the four-fold splitting
  is `Multiset.sum_antidiagonal_exchange`. -/
lemma repGauge_commutatorFam
    (U : GJ) (s : Multiset (Fin 1 ⊕ Fin 3)) (μ ν : Fin 1 ⊕ Fin 3)
    (φ : Module.Dual ℝ 𝔤) :
    repGauge U (commutatorFam h.A μ ν s φ) =
      (s.antidiagonal.map fun p =>
        commutatorFam h.A μ ν p.2 (jets.adjointDualCoeff U⁻¹ p.1 φ)).sum
      + (s.antidiagonal.map fun p =>
          (p.2.antidiagonal.map fun r =>
            h.A r.2 ν (jets.adjointDualCoeff U⁻¹ r.1
              (φ ∘ₗ LieAlgebra.ad ℝ 𝔤 (jets.evalLie
                (jets.iteratedDeriv p.1 (jets.maurerCartan U⁻¹ μ)))))).sum).sum
      - (s.antidiagonal.map fun p =>
          (p.1.antidiagonal.map fun q =>
            h.A q.2 μ (jets.adjointDualCoeff U⁻¹ q.1
              (φ ∘ₗ LieAlgebra.ad ℝ 𝔤 (jets.evalLie
                (jets.iteratedDeriv p.2 (jets.maurerCartan U⁻¹ ν)))))).sum).sum
      + (s.antidiagonal.map fun p =>
          algebraMap ℂ B (φ ⁅jets.evalLie (jets.iteratedDeriv p.1
              (jets.maurerCartan U⁻¹ μ)),
            jets.evalLie (jets.iteratedDeriv p.2
              (jets.maurerCartan U⁻¹ ν))⁆)).sum := by
  -- the affine transformation law of the derived symbols, with the Leibniz sum as a map
  have hAlaw : ∀ (τ : Fin 1 ⊕ Fin 3) (u : Multiset (Fin 1 ⊕ Fin 3))
      (ψ : Module.Dual ℝ 𝔤),
      repGauge U (h.A u τ ψ) =
        ((u.antidiagonal.map fun q => h.A q.2 τ ∘ₗ jets.adjointDualCoeff U⁻¹ q.1).sum) ψ
        + algebraMap ℂ B (ψ (jets.evalLie
            (jets.iteratedDeriv u (jets.maurerCartan U⁻¹ τ)))) := by
    intro τ u ψ
    rw [h.gauge_apply_deriv U u τ ψ, Multiset.sum_linearMap_apply, Multiset.map_map]
    congr 1
  -- the convolution triple sum in its two groupings
  have hMa : (s.antidiagonal.map fun p =>
      bracketFam ((p.1.antidiagonal.map fun q => h.A q.2 μ ∘ₗ jets.adjointDualCoeff U⁻¹ q.1).sum)
        ((p.2.antidiagonal.map fun r => h.A r.2 ν ∘ₗ jets.adjointDualCoeff U⁻¹ r.1).sum) φ).sum =
      (s.antidiagonal.map fun p =>
        (p.1.antidiagonal.map fun q =>
          (p.2.antidiagonal.map fun r =>
            bracketFam (h.A q.2 μ ∘ₗ jets.adjointDualCoeff U⁻¹ q.1)
              (h.A r.2 ν ∘ₗ jets.adjointDualCoeff U⁻¹ r.1) φ).sum).sum).sum := by
    refine congrArg Multiset.sum (Multiset.map_congr rfl fun p hp => ?_)
    rw [bracketFam_sum_left, Multiset.sum_linearMap_apply, Multiset.map_map,
      Multiset.map_map]
    refine congrArg Multiset.sum (Multiset.map_congr rfl fun q hq => ?_)
    simp only [Function.comp_apply]
    rw [bracketFam_sum_right, Multiset.sum_linearMap_apply, Multiset.map_map,
      Multiset.map_map]
    refine congrArg Multiset.sum (Multiset.map_congr rfl fun r hr => ?_)
    simp only [Function.comp_apply]
  have hMc : (s.antidiagonal.map fun p =>
      commutatorFam h.A μ ν p.2 (jets.adjointDualCoeff U⁻¹ p.1 φ)).sum =
      (s.antidiagonal.map fun p =>
        (p.1.antidiagonal.map fun q =>
          (p.2.antidiagonal.map fun r =>
            bracketFam (h.A r.1 μ ∘ₗ jets.adjointDualCoeff U⁻¹ q.1)
              (h.A r.2 ν ∘ₗ jets.adjointDualCoeff U⁻¹ q.2) φ).sum).sum).sum := by
    refine congrArg Multiset.sum (Multiset.map_congr rfl fun p hp => ?_)
    rw [commutatorFam, Multiset.sum_linearMap_apply, Multiset.map_map,
      Multiset.map_congr rfl (fun r hr => by
        rw [Function.comp_apply,
          bracketFam_adjointDualCoeff U⁻¹ p.1 (h.A r.1 μ) (h.A r.2 ν) φ]),
      Multiset.sum_map_sum_map]
  have hM := hMa.trans ((Multiset.sum_antidiagonal_exchange s fun a b c d =>
      bracketFam (h.A b μ ∘ₗ jets.adjointDualCoeff U⁻¹ a)
        (h.A d ν ∘ₗ jets.adjointDualCoeff U⁻¹ c) φ).trans hMc.symm)
  -- the cross-term sums, applied
  have hCg : ∀ p : Multiset (Fin 1 ⊕ Fin 3) × Multiset (Fin 1 ⊕ Fin 3),
      ((p.2.antidiagonal.map fun r => h.A r.2 ν ∘ₗ jets.adjointDualCoeff U⁻¹ r.1).sum)
        (φ ∘ₗ LieAlgebra.ad ℝ 𝔤 (jets.evalLie
          (jets.iteratedDeriv p.1 (jets.maurerCartan U⁻¹ μ)))) =
      (p.2.antidiagonal.map fun r =>
        h.A r.2 ν (jets.adjointDualCoeff U⁻¹ r.1
          (φ ∘ₗ LieAlgebra.ad ℝ 𝔤 (jets.evalLie
            (jets.iteratedDeriv p.1 (jets.maurerCartan U⁻¹ μ)))))).sum := by
    intro p
    rw [Multiset.sum_linearMap_apply, Multiset.map_map]
    refine congrArg Multiset.sum (Multiset.map_congr rfl fun r hr => ?_)
    simp only [Function.comp_apply, LinearMap.coe_comp]
  have hCf : ∀ p : Multiset (Fin 1 ⊕ Fin 3) × Multiset (Fin 1 ⊕ Fin 3),
      ((p.1.antidiagonal.map fun q => h.A q.2 μ ∘ₗ jets.adjointDualCoeff U⁻¹ q.1).sum)
        (φ ∘ₗ LieAlgebra.ad ℝ 𝔤 (jets.evalLie
          (jets.iteratedDeriv p.2 (jets.maurerCartan U⁻¹ ν)))) =
      (p.1.antidiagonal.map fun q =>
        h.A q.2 μ (jets.adjointDualCoeff U⁻¹ q.1
          (φ ∘ₗ LieAlgebra.ad ℝ 𝔤 (jets.evalLie
            (jets.iteratedDeriv p.2 (jets.maurerCartan U⁻¹ ν)))))).sum := by
    intro p
    rw [Multiset.sum_linearMap_apply, Multiset.map_map]
    refine congrArg Multiset.sum (Multiset.map_congr rfl fun q hq => ?_)
    simp only [Function.comp_apply, LinearMap.coe_comp]
  -- expand the left side and split the four convolutions
  rw [commutatorFam, Multiset.sum_linearMap_apply, Multiset.map_map, map_multiset_sum,
    Multiset.map_map,
    Multiset.map_congr rfl (fun p hp => by
      rw [Function.comp_apply, Function.comp_apply,
        h.repGauge_bracketFam U (hAlaw μ p.1) (hAlaw ν p.2) φ, hCg p, hCf p]),
    Multiset.sum_map_add, Multiset.sum_map_sub, Multiset.sum_map_add, hM]

end ComplexScalars

end GaugeAlgebraRealization

