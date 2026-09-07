/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Particles.StandardModel.Basic
public import Physlib.Particles.StandardModel.GaugeGroup.Jet.Truncation
public import Physlib.Particles.StandardModel.GaugeAlgebra.JetGaugeAlgebra
public import Physlib.Particles.StandardModel.GaugeGroup.MaurerCartan.Basic
public import Physlib.Relativity.IsLorentzDeriv
public import Physlib.Relativity.Tensors.ComplexTensor.Basic
public import Physlib.Relativity.Tensors.RealTensor.Vector.Basic
public import Physlib.Relativity.Tensors.RealTensor.Vector.Representation
public import Physlib.Relativity.SL2C.Basic
/-!
# Algebra valued gauge bosons

An algebra `B` (for instance a jet algebra of Lagrangian terms) may contain a family of
elements playing the role of the gauge-field symbols `[∂_s A_μ^a]`. This file defines
what it means for such a family to *be* a set of gauge bosons: the structure
`IsGaugeField` records the transformation laws that the physicists' gauge field
satisfies, with nothing postulated beyond them.

## The physics

Let `A_μ^a` be a gauge field for the gauge group `G`, with `μ` a spacetime (covector)
index and `a` an adjoint index. Under a gauge transformation `g` the field transforms as

  `A_μ ↦ Ad_g A_μ + mc(g)_μ`,

where `mc(g)_μ = i (∂_μ g) g⁻¹` is the Maurer–Cartan form. The symbols `[∂_s A_μ^a]`
are coordinate functions on the space of field configurations, so the induced (left)
action is the pullback along `g⁻¹`: one substitutes `g⁻¹` into the field law and
differentiates `s` times with the Leibniz rule:

  `g • [∂_s A_μ^a] = ∑_{x+y=s} C(x,y) (∂_x (Ad_{g⁻¹})^a_b)| [∂_y A_μ^b]`
  `                  + (∂_s mc(g⁻¹)_μ^a)|`,

where `C(x,y)` is the multinomial coefficient of the splitting and `|` denotes
evaluation at the base point. All the data on the right is carried by the *jet* of the
gauge transformation, which is why the gauge representation below is a representation
of `JetGaugeGroupI` and not merely of `GaugeGroupI`.

## The formalization dictionary

* `A μ φ` is the symbol `A_μ^a` contracted with a dual adjoint vector `φ`; the
  derivative symbols `[∂_s A_μ^a]` are its images `iteratedD D deriv_comm s (A μ φ)` under the
  total derivative `D`.
* `∂_x (Ad_{g⁻¹})^a_b|` acting on the dual index is `adjointDualCoeff g⁻¹ x φ`:
  include the constant algebra element into jets, act by the adjoint of `g⁻¹`,
  differentiate `x` times, evaluate at the base point, and pair with `φ`.
* The sum `∑_{x+y=s} C(x,y)` is the sum over `s.antidiagonal`: a splitting `(x, y)`
  occurs in the antidiagonal of the multiset `s` with multiplicity exactly `C(x,y)`.
* `(∂_s mc(g⁻¹)_μ)|` is `JetGaugeAlgebra.eval (iteratedDeriv s (maurerCartanForm g⁻¹ μ))`,
  a constant algebra element, paired with `φ` and embedded in `B` as a scalar.

-/

@[expose] public section

namespace StandardModel
open Matrix MatrixGroups TensorProduct MvPowerSeries
variable {B : Type} [Ring B] [Algebra ℂ B]


/-- The physicists' `∂_x (Ad_{U})^a_b|` acting on the dual adjoint index of a
  gauge-field symbol: precomposition of `φ` with the constant inclusion into jets,
  followed by the adjoint action of `U`, `x` formal derivatives, and evaluation at
  the base point. For `x = 0` this is the dual (contragredient) adjoint action of
  the value `U₀`; for `x ≠ 0` it sees the derivatives of the gauge transformation. -/
noncomputable def adjointDualCoeff (U : JetGaugeGroupI) (x : Multiset (Fin 1 ⊕ Fin 3)) :
    Module.Dual ℝ GaugeAlgebra →ₗ[ℝ] Module.Dual ℝ GaugeAlgebra :=
  (JetGaugeAlgebra.eval.toLinearMap ∘ₗ JetGaugeAlgebra.iteratedDeriv x ∘ₗ
    JetGaugeAlgebra.adjointMap U ∘ₗ JetGaugeAlgebra.ofConstant).dualMap

/-- The zeroth dual adjoint coefficient is the dual of the adjoint action of the
  base-point value of the gauge jet. -/
lemma adjointDualCoeff_zero (U : JetGaugeGroupI) :
    adjointDualCoeff U 0 = (GaugeAlgebra.adjoint U.eval).dualMap := by
  rw [adjointDualCoeff]
  refine congrArg LinearMap.dualMap (LinearMap.ext fun a => ?_)
  simp only [LinearMap.coe_comp, Function.comp_apply, LieHom.coe_toLinearMap,
    JetGaugeAlgebra.iteratedDeriv_zero, LinearMap.id_coe, id_eq]
  exact JetGaugeAlgebra.eval_adjointMap_ofConstant U a

/-- For a gauge jet whose value at the base point is the identity, the zeroth dual
  adjoint coefficient is trivial: the base-point adjoint action `Ad_{U₀}` is the
  identity. -/
lemma adjointDualCoeff_zero_of_eval_eq_one {U : JetGaugeGroupI} (hU : U.eval = 1) :
    adjointDualCoeff U 0 = LinearMap.id := by
  rw [adjointDualCoeff_zero, hU, map_one, Module.End.one_eq_id, LinearMap.dualMap_id]

/-- The dual adjoint coefficient at a single derivative: since
  `∂_μ (Ad_U x) = Ad_U (∂_μ x) − ⁅ω_μ(U), Ad_U x⁆` (`deriv_adjointMap`) and constants
  have vanishing derivative, the once-derived coefficient is minus the underived
  coefficient precomposed (on the dual index) with `ad` of the base-point
  Maurer–Cartan form. This is what cancels the Leibniz cross terms of
  `gauge_apply_deriv` against the commutator cross terms in the field strength. -/
lemma adjointDualCoeff_singleton (U : JetGaugeGroupI)
    (μ : Fin 1 ⊕ Fin 3) (φ : Module.Dual ℝ GaugeAlgebra) :
    adjointDualCoeff U {μ} φ =
      -adjointDualCoeff U 0 (φ ∘ₗ LieAlgebra.ad ℝ GaugeAlgebra
        (JetGaugeAlgebra.eval (maurerCartanForm U μ))) := by
  refine LinearMap.ext fun a => ?_
  simp only [adjointDualCoeff, LinearMap.dualMap_apply, LinearMap.neg_apply,
    LinearMap.coe_comp, Function.comp_apply, LieHom.coe_toLinearMap,
    JetGaugeAlgebra.iteratedDeriv_singleton, JetGaugeAlgebra.iteratedDeriv_zero,
    LinearMap.id_coe, id_eq]
  rw [deriv_adjointMap, JetGaugeAlgebra.deriv_ofConstant, map_zero, zero_sub, map_neg,
    map_neg, LieHom.map_lie]
  simp

/-- **Deep kernels kill the positive dual adjoint coefficients**: for a jet trivial to order `n`, all derivatives of the
  adjoint action up to order `n` vanish. -/
lemma adjointDualCoeff_eq_zero_of_mem_truncationKer {U : JetGaugeGroupI} {n : ℕ}
    (hU : U ∈ JetGaugeGroupI.truncationKer n) {x : Multiset (Fin 1 ⊕ Fin 3)}
    (hx : x ≠ 0) (hxn : x.card ≤ n) : adjointDualCoeff U x = 0 := by
  have hprod := JetGaugeGroupI.mem_truncationKer_iff.mp hU
  -- the truncations of the matrix factors of `U` agree with `1`
  have h3 : U.1.1.map (JetRing.truncation n) =
      (1 : Matrix (Fin 3) (Fin 3) JetRing).map (JetRing.truncation n) :=
    congrArg (fun p => p.1) hprod
  have h2 : U.2.1.1.map (JetRing.truncation n) =
      (1 : Matrix (Fin 2) (Fin 2) JetRing).map (JetRing.truncation n) :=
    congrArg (fun p => p.2.1) hprod
  have hs3 : (star U.1.1).map (JetRing.truncation n) =
      (1 : Matrix (Fin 3) (Fin 3) JetRing).map (JetRing.truncation n) := by
    rw [JetRing.matrix_truncation_star, h3, ← JetRing.matrix_truncation_star, star_one]
  have hs2 : (star U.2.1.1).map (JetRing.truncation n) =
      (1 : Matrix (Fin 2) (Fin 2) JetRing).map (JetRing.truncation n) := by
    rw [JetRing.matrix_truncation_star, h2, ← JetRing.matrix_truncation_star, star_one]
  -- conjugation by `U` is invisible to the `n`-th truncation
  have hconj3 : ∀ M : Matrix (Fin 3) (Fin 3) JetRing,
      ((U.1.1 * M) * star U.1.1).map (JetRing.truncation n) =
        M.map (JetRing.truncation n) := by
    intro M
    rw [JetRing.matrix_truncation_mul_congr
      (JetRing.matrix_truncation_mul_congr h3 rfl) hs3, one_mul, mul_one]
  have hconj2 : ∀ M : Matrix (Fin 2) (Fin 2) JetRing,
      ((U.2.1.1 * M) * star U.2.1.1).map (JetRing.truncation n) =
        M.map (JetRing.truncation n) := by
    intro M
    rw [JetRing.matrix_truncation_mul_congr
      (JetRing.matrix_truncation_mul_congr h2 rfl) hs2, one_mul, mul_one]
  -- the multiset `x` sits in the truncation window, in nonzero degree
  have hdeg : Finsupp.degree (Multiset.toFinsupp x) ≤ n := by
    rw [JetRing.degree_toFinsupp_eq_card]; exact hxn
  have hne : Multiset.toFinsupp x ≠ 0 := fun hc =>
    hx (by simpa using congrArg Finsupp.toMultiset hc)
  -- the underlying derivative of the adjoint transport vanishes at the base point
  have key : ∀ b : GaugeAlgebra,
      JetGaugeAlgebra.eval (JetGaugeAlgebra.iteratedDeriv x
        (JetGaugeAlgebra.adjointMap U (JetGaugeAlgebra.ofConstant b))) = 0 := by
    intro b
    refine GaugeAlgebra.ext_of_matrix ?_ ?_ ?_
    · ext i j : 1
      rw [JetGaugeAlgebra.eval_toSU3Matrix_apply, JetGaugeAlgebra.iteratedDeriv_toSU3Matrix,
        Matrix.map_apply, JetRing.constantCoeff_foldl_pderiv,
        JetGaugeAlgebra.adjointMap_toSU3Matrix, JetGaugeAlgebra.ofConstant_toSU3Matrix]
      have h1 := congrArg (fun M : Matrix (Fin 3) (Fin 3) JetRing => M i j)
        (hconj3 (b.toSU3Matrix.map (C : ℂ → JetRing)))
      simp only [Matrix.map_apply] at h1
      have hcoeff := congrArg (fun f => coeff (Multiset.toFinsupp x) f) h1
      simp only [JetRing.coeff_truncation_of_le hdeg] at hcoeff
      rw [hcoeff, coeff_C, if_neg hne, mul_zero,
        GaugeAlgebra.zero_toSU3Matrix, Matrix.zero_apply]
    · ext i j : 1
      rw [JetGaugeAlgebra.eval_toSU2Matrix_apply, JetGaugeAlgebra.iteratedDeriv_toSU2Matrix,
        Matrix.map_apply, JetRing.constantCoeff_foldl_pderiv,
        JetGaugeAlgebra.adjointMap_toSU2Matrix, JetGaugeAlgebra.ofConstant_toSU2Matrix]
      have h1 := congrArg (fun M : Matrix (Fin 2) (Fin 2) JetRing => M i j)
        (hconj2 (b.toSU2Matrix.map (C : ℂ → JetRing)))
      simp only [Matrix.map_apply] at h1
      have hcoeff := congrArg (fun f => coeff (Multiset.toFinsupp x) f) h1
      simp only [JetRing.coeff_truncation_of_le hdeg] at hcoeff
      rw [hcoeff, coeff_C, if_neg hne, mul_zero,
        GaugeAlgebra.zero_toSU2Matrix, Matrix.zero_apply]
    · rw [JetGaugeAlgebra.eval_toU1Value_eq, JetGaugeAlgebra.iteratedDeriv_toU1Value,
        JetGaugeAlgebra.adjointMap_toU1Value, JetGaugeAlgebra.ofConstant_toU1Value,
        JetRing.constantCoeff_foldl_pderiv, coeff_C, if_neg hne, mul_zero,
        GaugeAlgebra.zero_toU1Value]
  refine LinearMap.ext fun φ => LinearMap.ext fun b => ?_
  simp only [LinearMap.zero_apply]
  show φ (JetGaugeAlgebra.eval (JetGaugeAlgebra.iteratedDeriv x
    (JetGaugeAlgebra.adjointMap U (JetGaugeAlgebra.ofConstant b)))) = 0
  rw [key b, map_zero]

open Lorentz
/-- The family `A` of symbols in the algebra `B` is a gauge field for the total
  derivative `D`, the Lorentz representation `repLorentz` and the gauge representation
  `repGauge`, when it satisfies the transformation laws of the physicists' gauge field:

  * it presupposes (as arguments, not fields) that `D` is a Lorentz derivative — the
    instance `Lorentz.IsLorentzDeriv repLorentz D` — and that its components commute
    (`deriv_comm`), as total derivatives do;
  * the symbol `A_μ^a` carries one covector index, transforming through the columns of
    the Lorentz matrix (`lorentz_A`);
  * under a gauge jet `U` the derivative symbols `[∂_s A_μ^a]` transform by the
    Leibniz expansion of `A_μ ↦ Ad_{U⁻¹} A_μ + mc(U⁻¹)_μ` (`gauge_A`) — the adjoint
    convolution plus the inhomogeneous Maurer–Cartan shift. The inverse makes the
    action a left action, exactly as in `φ'(x) = φ(Λ⁻¹ x)`. -/
structure IsGaugeField (repLorentz : Representation ℂ SL(2,ℂ) B)
    (repGauge : Representation ℂ JetGaugeGroupI B)
    (A : Multiset (Fin 1 ⊕ Fin 3)  → (Fin 1 ⊕ Fin 3) → Module.Dual ℝ GaugeAlgebra →ₗ[ℝ] B) : Prop where
  /-- The gauge-field symbol carries one covector Lorentz index. -/
  lorentz_apply : ∀ (Λ : SL(2,ℂ)) (n : ℕ) (l : Fin n → (Fin 1 ⊕ Fin 3)) (μ : Fin 1 ⊕ Fin 3) (φ : Module.Dual ℝ GaugeAlgebra),
    repLorentz Λ (A (List.ofFn l) μ φ) =
      ∑ (p : Fin n → (Fin 1 ⊕ Fin 3)),
        (∏ (i : Fin n), (((SL2C.toLorentzGroup Λ).1 (p i) (l i) : ℝ) : ℂ))  •
      ∑ a, (((Lorentz.SL2C.toLorentzGroup Λ).1 a μ : ℝ) : ℂ) • A (List.ofFn p) a φ
  /-- The gauge transformation of the derivative symbols `[∂_s A_μ^a]`: the Leibniz
    convolution of the dual adjoint action of `U⁻¹` against lower derivative symbols
    (the multiset antidiagonal carries the multinomial coefficients), plus the
    base-point value of the `s`-th derivative of the Maurer–Cartan form of `U⁻¹`. -/
  gauge_apply_deriv : ∀ (U : JetGaugeGroupI) (s : Multiset (Fin 1 ⊕ Fin 3)) (μ : Fin 1 ⊕ Fin 3)
      (φ : Module.Dual ℝ GaugeAlgebra),
    repGauge U (A s μ φ) =
      (s.antidiagonal.map fun p => (A p.2 μ (adjointDualCoeff U⁻¹ p.1 φ))).sum
      + algebraMap ℂ B
          (φ (JetGaugeAlgebra.eval (JetGaugeAlgebra.iteratedDeriv s (maurerCartanForm U⁻¹ μ))))
  /-- The gauge action preserves products: gauge transformations act on the algebra of
    local expressions as algebra homomorphisms. -/
  gauge_mul : ∀ (U : JetGaugeGroupI) (b₁ b₂ : B),
    repGauge U (b₁ * b₂) = repGauge U b₁ * repGauge U b₂

namespace IsGaugeField

variable {repLorentz : Representation ℂ SL(2,ℂ) B}
variable {repGauge : Representation ℂ JetGaugeGroupI B}
variable {A : Multiset (Fin 1 ⊕ Fin 3) → (Fin 1 ⊕ Fin 3) → Module.Dual ℝ GaugeAlgebra →ₗ[ℝ] B}

/-- The canonical equivalence, through finite-dimensional duality, between
  algebra-valued fields `B ⊗ 𝔤` and their component families `φ ↦ A^φ`: the element
  `b ⊗ a` corresponds to the family `φ ↦ φ(a) b`. -/
noncomputable def dualPairEquiv :
    (B ⊗[ℝ] GaugeAlgebra) ≃ₗ[ℝ] (Module.Dual ℝ GaugeAlgebra →ₗ[ℝ] B) :=
  TensorProduct.comm ℝ B GaugeAlgebra ≪≫ₗ
    TensorProduct.congr (Module.evalEquiv ℝ GaugeAlgebra) (LinearEquiv.refl ℝ B) ≪≫ₗ
    dualTensorHomEquiv ℝ (Module.Dual ℝ GaugeAlgebra) B

/-- The bracket of two algebra-valued fields: multiplication in `B` on the first
  factors, the Lie bracket of the gauge algebra on the second, so that on pure
  tensors `⁅b₁ ⊗ a₁, b₂ ⊗ a₂⁆ = (b₁ b₂) ⊗ ⁅a₁, a₂⁆`. -/
noncomputable def tensorBracket :
    (B ⊗[ℝ] GaugeAlgebra) →ₗ[ℝ] (B ⊗[ℝ] GaugeAlgebra) →ₗ[ℝ] B ⊗[ℝ] GaugeAlgebra :=
  TensorProduct.curry
    ((TensorProduct.map (TensorProduct.lift (LinearMap.mul ℝ B))
        (TensorProduct.lift (LinearMap.mk₂ ℝ (fun a b => ⁅a, b⁆)
          (fun a a' b => add_lie a a' b) (fun t a b => smul_lie t a b)
          (fun a b b' => lie_add a b b') (fun t a b => lie_smul t a b)))) ∘ₗ
      (TensorProduct.tensorTensorTensorComm ℝ B GaugeAlgebra B GaugeAlgebra).toLinearMap)

/-- The commutator term `⁅A_μ, A_ν⁆` of the field strength, as a component family:
  the physicists' `f^a_{bc} A_μ^b A_ν^c` contracted with a dual adjoint vector, but
  basis-free — the two fields are assembled into `B ⊗ 𝔤` by `dualPairEquiv.symm`,
  bracketed there by `tensorBracket`, and read back out as components. -/
noncomputable def commutator
    (A : Multiset (Fin 1 ⊕ Fin 3) → (Fin 1 ⊕ Fin 3) → Module.Dual ℝ GaugeAlgebra →ₗ[ℝ] B)
    (μ ν : Fin 1 ⊕ Fin 3) : Module.Dual ℝ GaugeAlgebra →ₗ[ℝ] B :=
  dualPairEquiv (tensorBracket (dualPairEquiv.symm (A 0 μ)) (dualPairEquiv.symm (A 0 ν)))

/-- The gauge transformation of the underived symbol `A_μ^φ`: the special case `s = 0`
  of `gauge_apply_deriv`, with no Leibniz convolution left over — the dual adjoint
  action of the value of `U⁻¹` plus the Maurer–Cartan shift. -/
lemma repGauge_apply (hA : IsGaugeField repLorentz repGauge A) (U : JetGaugeGroupI)
    (μ : Fin 1 ⊕ Fin 3) (φ : Module.Dual ℝ GaugeAlgebra) :
    repGauge U (A 0 μ φ) = A 0 μ (adjointDualCoeff U⁻¹ ∅ φ) +
      algebraMap ℂ B (φ (JetGaugeAlgebra.eval (maurerCartanForm U⁻¹ μ))) := by
  simpa [show (∅ : Multiset (Fin 1 ⊕ Fin 3)) = 0 from rfl] using
    hA.gauge_apply_deriv U 0 μ φ


/-- The gauge transformation of the once-derived symbol `∂_ρ A_σ`: the case `s = {ρ}`
  of `gauge_apply_deriv` — the two Leibniz splittings of one derivative, plus the
  base-point value of the derived Maurer–Cartan form. -/
lemma repGauge_deriv_apply (hA : IsGaugeField repLorentz repGauge A)
    (U : JetGaugeGroupI) (ρ σ : Fin 1 ⊕ Fin 3) (φ : Module.Dual ℝ GaugeAlgebra) :
    repGauge U (A {ρ} σ φ) =
      A {ρ} σ (adjointDualCoeff U⁻¹ 0 φ) + A 0 σ (adjointDualCoeff U⁻¹ {ρ} φ) +
      algebraMap ℂ B (φ (JetGaugeAlgebra.eval
        (JetGaugeAlgebra.deriv ρ (maurerCartanForm U⁻¹ σ)))) := by
  have hanti : ({ρ} : Multiset (Fin 1 ⊕ Fin 3)).antidiagonal =
      {((0 : Multiset (Fin 1 ⊕ Fin 3)), ({ρ} : Multiset (Fin 1 ⊕ Fin 3))),
        (({ρ} : Multiset (Fin 1 ⊕ Fin 3)), (0 : Multiset (Fin 1 ⊕ Fin 3)))} := by
    rw [show ({ρ} : Multiset (Fin 1 ⊕ Fin 3)) = ρ ::ₘ 0 from rfl,
      Multiset.antidiagonal_cons, Multiset.antidiagonal_zero]
    simp
  have h := hA.gauge_apply_deriv U {ρ} σ φ
  rw [hanti] at h
  simp only [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton,
    Multiset.sum_cons, Multiset.sum_singleton,
    JetGaugeAlgebra.iteratedDeriv_singleton] at h
  refine h.trans ?_
  abel

/-!

## Pure-tensor computations for `dualPairEquiv` and `tensorBracket`

-/

@[simp]
lemma dualPairEquiv_tmul (b : B) (a : GaugeAlgebra) (φ : Module.Dual ℝ GaugeAlgebra) :
    dualPairEquiv (b ⊗ₜ[ℝ] a) φ = φ a • b := by
  simp [dualPairEquiv, dualTensorHomEquiv, Module.evalEquiv_apply]

@[simp]
lemma tensorBracket_tmul (b₁ b₂ : B) (a₁ a₂ : GaugeAlgebra) :
    tensorBracket (b₁ ⊗ₜ[ℝ] a₁) (b₂ ⊗ₜ[ℝ] a₂) = (b₁ * b₂) ⊗ₜ[ℝ] ⁅a₁, a₂⁆ := by
  simp [tensorBracket, TensorProduct.tensorTensorTensorComm_tmul]

lemma dualPairEquiv_map_left (Φ : B →ₗ[ℝ] B) (t : B ⊗[ℝ] GaugeAlgebra)
    (φ : Module.Dual ℝ GaugeAlgebra) :
    dualPairEquiv ((TensorProduct.map Φ LinearMap.id) t) φ = Φ (dualPairEquiv t φ) := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul b a => simp
  | add x y hx hy => simp [hx, hy]

lemma dualPairEquiv_map_right (T : GaugeAlgebra →ₗ[ℝ] GaugeAlgebra)
    (t : B ⊗[ℝ] GaugeAlgebra) (φ : Module.Dual ℝ GaugeAlgebra) :
    dualPairEquiv ((TensorProduct.map LinearMap.id T) t) φ =
      dualPairEquiv t (T.dualMap φ) := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul b a => simp
  | add x y hx hy => simp [hx, hy]

lemma dualPairEquiv_one_tmul (c : GaugeAlgebra) (φ : Module.Dual ℝ GaugeAlgebra) :
    dualPairEquiv ((1 : B) ⊗ₜ[ℝ] c) φ = algebraMap ℂ B (φ c) := by
  rw [dualPairEquiv_tmul, Algebra.algebraMap_eq_smul_one,
    show ((φ c : ℝ) : ℂ) = algebraMap ℝ ℂ (φ c) from rfl, algebraMap_smul]

lemma symm_comp_left (Φ : B →ₗ[ℝ] B) (f : Module.Dual ℝ GaugeAlgebra →ₗ[ℝ] B) :
    dualPairEquiv.symm (Φ ∘ₗ f) =
      (TensorProduct.map Φ LinearMap.id) (dualPairEquiv.symm f) := by
  apply dualPairEquiv.injective
  rw [LinearEquiv.apply_symm_apply]
  refine LinearMap.ext fun φ => ?_
  rw [dualPairEquiv_map_left, LinearEquiv.apply_symm_apply]
  rfl

lemma symm_comp_right (T : GaugeAlgebra →ₗ[ℝ] GaugeAlgebra)
    (f : Module.Dual ℝ GaugeAlgebra →ₗ[ℝ] B) :
    dualPairEquiv.symm (f ∘ₗ T.dualMap) =
      (TensorProduct.map LinearMap.id T) (dualPairEquiv.symm f) := by
  apply dualPairEquiv.injective
  rw [LinearEquiv.apply_symm_apply]
  refine LinearMap.ext fun φ => ?_
  rw [dualPairEquiv_map_right, LinearEquiv.apply_symm_apply]
  rfl

lemma tensorBracket_map_left (Φ : B →ₗ[ℝ] B)
    (hΦ : ∀ b₁ b₂, Φ (b₁ * b₂) = Φ b₁ * Φ b₂) (s t : B ⊗[ℝ] GaugeAlgebra) :
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

lemma tensorBracket_map_right (T : GaugeAlgebra →ₗ[ℝ] GaugeAlgebra)
    (hT : ∀ a b, T ⁅a, b⁆ = ⁅T a, T b⁆) (s t : B ⊗[ℝ] GaugeAlgebra) :
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

lemma tensorBracket_one_right (c : GaugeAlgebra) (s : B ⊗[ℝ] GaugeAlgebra) :
    tensorBracket s ((1 : B) ⊗ₜ[ℝ] c) =
      -(TensorProduct.map LinearMap.id (LieAlgebra.ad ℝ GaugeAlgebra c)) s := by
  induction s using TensorProduct.induction_on with
  | zero => simp
  | tmul b a =>
      rw [tensorBracket_tmul, mul_one, ← lie_skew, TensorProduct.tmul_neg]
      simp
  | add x y hx hy =>
      simp only [map_add, LinearMap.add_apply]
      rw [hx, hy]
      abel

lemma tensorBracket_one_left (c : GaugeAlgebra) (t : B ⊗[ℝ] GaugeAlgebra) :
    tensorBracket ((1 : B) ⊗ₜ[ℝ] c) t =
      (TensorProduct.map LinearMap.id (LieAlgebra.ad ℝ GaugeAlgebra c)) t := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul b a => simp
  | add x y hx hy => simp [hx, hy]

/-!

## The gauge transformation of the commutator

-/

set_option maxHeartbeats 1000000 in
/-- The gauge transformation law of the commutator term: writing the field law as
  `A_μ ↦ Ad₀ A_μ + c_μ` with `Ad₀` the base-point adjoint of `U₀⁻¹` and
  `c_μ = mc(U⁻¹)_μ|₀` the constant Maurer–Cartan shift, bilinearity of the bracket
  gives

  `⁅A_μ, A_ν⁆ ↦ Ad₀ ⁅A_μ, A_ν⁆ + ⁅Ad₀ A_μ, c_ν⁆ + ⁅c_μ, Ad₀ A_ν⁆ + ⁅c_μ, c_ν⁆`:

  the adjoint-transported commutator, two cross terms linear in the field (the
  bracket against `c` acting on the dual index through `ad`), and the constant
  commutator of the two Maurer–Cartan shifts. Uses that the gauge action is by
  algebra homomorphisms (`gauge_mul`) and that the base-point adjoint transport is a
  morphism of Lie algebras. -/
lemma repGauge_commutator (hA : IsGaugeField repLorentz repGauge A)
    (U : JetGaugeGroupI) (μ ν : Fin 1 ⊕ Fin 3) (φ : Module.Dual ℝ GaugeAlgebra) :
    repGauge U (commutator A μ ν φ) =
      commutator A μ ν (adjointDualCoeff U⁻¹ 0 φ)
      - A 0 μ (adjointDualCoeff U⁻¹ 0 (φ ∘ₗ LieAlgebra.ad ℝ GaugeAlgebra
          (JetGaugeAlgebra.eval (maurerCartanForm U⁻¹ ν))))
      + A 0 ν (adjointDualCoeff U⁻¹ 0 (φ ∘ₗ LieAlgebra.ad ℝ GaugeAlgebra
          (JetGaugeAlgebra.eval (maurerCartanForm U⁻¹ μ))))
      + algebraMap ℂ B (φ ⁅JetGaugeAlgebra.eval (maurerCartanForm U⁻¹ μ),
          JetGaugeAlgebra.eval (maurerCartanForm U⁻¹ ν)⁆) := by
  -- the linear maps and constants of the transformation law
  set Φ : B →ₗ[ℝ] B := (repGauge U).restrictScalars ℝ with hΦdef
  set T₀ : GaugeAlgebra →ₗ[ℝ] GaugeAlgebra :=
    JetGaugeAlgebra.eval.toLinearMap ∘ₗ JetGaugeAlgebra.iteratedDeriv 0 ∘ₗ
      JetGaugeAlgebra.adjointMap U⁻¹ ∘ₗ JetGaugeAlgebra.ofConstant with hT₀def
  set cμ : GaugeAlgebra := JetGaugeAlgebra.eval (maurerCartanForm U⁻¹ μ) with hcμ
  set cν : GaugeAlgebra := JetGaugeAlgebra.eval (maurerCartanForm U⁻¹ ν) with hcν
  set s : B ⊗[ℝ] GaugeAlgebra := dualPairEquiv.symm (A 0 μ) with hs
  set t : B ⊗[ℝ] GaugeAlgebra := dualPairEquiv.symm (A 0 ν) with ht
  have hcoeff : adjointDualCoeff U⁻¹ 0 = T₀.dualMap := by rw [hT₀def]; rfl
  -- the base-point adjoint transport is a Lie algebra morphism
  have hT₀lie : ∀ a b : GaugeAlgebra, T₀ ⁅a, b⁆ = ⁅T₀ a, T₀ b⁆ := by
    intro a b
    simp [hT₀def, JetGaugeAlgebra.ofConstant_lie, JetGaugeAlgebra.adjointMap_lie,
      LieHom.map_lie]
  -- the transformed component families in tensor form
  have hfam : ∀ (ρ : Fin 1 ⊕ Fin 3),
      Φ ∘ₗ A 0 ρ = A 0 ρ ∘ₗ T₀.dualMap +
        dualPairEquiv ((1 : B) ⊗ₜ[ℝ] JetGaugeAlgebra.eval (maurerCartanForm U⁻¹ ρ)) := by
    intro ρ
    refine LinearMap.ext fun ψ => ?_
    simp only [LinearMap.comp_apply, LinearMap.add_apply, hΦdef,
      LinearMap.restrictScalars_apply]
    rw [hA.repGauge_apply U ρ ψ, dualPairEquiv_one_tmul, ← hcoeff]
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
  have hcomm_pair : dualPairEquiv (tensorBracket s t) = commutator A μ ν := by
    rw [hs, ht]; rfl
  have hπs : dualPairEquiv s = A 0 μ := by
    rw [hs]; exact dualPairEquiv.apply_symm_apply _
  have hπt : dualPairEquiv t = A 0 ν := by
    rw [ht]; exact dualPairEquiv.apply_symm_apply _
  have hΦmul : ∀ b₁ b₂ : B, Φ (b₁ * b₂) = Φ b₁ * Φ b₂ := fun b₁ b₂ =>
    hA.gauge_mul U b₁ b₂
  clear_value Φ T₀ cμ cν s t
  -- the tensor-level transformation of the bracket
  have htensor : (TensorProduct.map Φ LinearMap.id) (tensorBracket s t) =
      (TensorProduct.map LinearMap.id T₀) (tensorBracket s t)
      - (TensorProduct.map LinearMap.id (LieAlgebra.ad ℝ GaugeAlgebra cν))
          ((TensorProduct.map LinearMap.id T₀) s)
      + (TensorProduct.map LinearMap.id (LieAlgebra.ad ℝ GaugeAlgebra cμ))
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
  rw [show repGauge U (commutator A μ ν φ) = Φ (dualPairEquiv (tensorBracket s t) φ) from by
      rw [← hcomm_pair, hΦdef]; rfl,
    hread, hcoeff, hcomm_pair, hπs, hπt]
  rfl

/-!

## Second derivatives of the gauge field

-/

/-- The dual adjoint coefficient at two derivatives: iterating
  `∂ (Ad_U x) = Ad_U (∂ x) − ⁅ω(U), Ad_U x⁆` once more, the twice-derived coefficient
  decomposes into the underived coefficient against `ad` of the derived Maurer–Cartan
  form, and the once-derived coefficient against `ad` of the Maurer–Cartan form
  itself. This is the two-derivative analogue of `adjointDualCoeff_singleton`. -/
lemma _root_.StandardModel.adjointDualCoeff_pair (U : JetGaugeGroupI)
    (ρ μ : Fin 1 ⊕ Fin 3) (φ : Module.Dual ℝ GaugeAlgebra) :
    adjointDualCoeff U (ρ ::ₘ {μ}) φ =
      -adjointDualCoeff U 0 (φ ∘ₗ LieAlgebra.ad ℝ GaugeAlgebra
        (JetGaugeAlgebra.eval (JetGaugeAlgebra.deriv ρ (maurerCartanForm U μ))))
      - adjointDualCoeff U {ρ} (φ ∘ₗ LieAlgebra.ad ℝ GaugeAlgebra
        (JetGaugeAlgebra.eval (maurerCartanForm U μ))) := by
  refine LinearMap.ext fun a => ?_
  have hderiv : ∀ τ : Fin 1 ⊕ Fin 3,
      JetGaugeAlgebra.deriv τ (JetGaugeAlgebra.adjointMap U (JetGaugeAlgebra.ofConstant a)) =
        -⁅maurerCartanForm U τ,
          JetGaugeAlgebra.adjointMap U (JetGaugeAlgebra.ofConstant a)⁆ :=
    fun τ => by rw [deriv_adjointMap, JetGaugeAlgebra.deriv_ofConstant, map_zero, zero_sub]
  have hkey : JetGaugeAlgebra.iteratedDeriv (ρ ::ₘ {μ})
      (JetGaugeAlgebra.adjointMap U (JetGaugeAlgebra.ofConstant a)) =
      -⁅JetGaugeAlgebra.deriv ρ (maurerCartanForm U μ),
        JetGaugeAlgebra.adjointMap U (JetGaugeAlgebra.ofConstant a)⁆
      + ⁅maurerCartanForm U μ, ⁅maurerCartanForm U ρ,
          JetGaugeAlgebra.adjointMap U (JetGaugeAlgebra.ofConstant a)⁆⁆ := by
    rw [JetGaugeAlgebra.iteratedDeriv_cons, LinearMap.comp_apply,
      JetGaugeAlgebra.iteratedDeriv_singleton, hderiv μ, map_neg,
      JetGaugeAlgebra.deriv_bracket, hderiv ρ, lie_neg]
    abel
  simp only [adjointDualCoeff, LinearMap.dualMap_apply, LinearMap.sub_apply,
    LinearMap.neg_apply, LinearMap.coe_comp, Function.comp_apply, LieHom.coe_toLinearMap,
    JetGaugeAlgebra.iteratedDeriv_zero, JetGaugeAlgebra.iteratedDeriv_singleton,
    LinearMap.id_coe, id_eq]
  rw [hkey, map_add, map_neg, LieHom.map_lie, LieHom.map_lie, LieHom.map_lie,
    hderiv ρ, map_neg, LieHom.map_lie]
  simp only [map_add, map_neg, LieAlgebra.ad_apply]
  abel

/-- The gauge transformation of the twice-derived symbol `∂_ρ ∂_σ A_τ`: the case
  `s = ρ ::ₘ {σ}` of `gauge_apply_deriv` — the four Leibniz splittings of two
  derivatives, plus the base-point value of the twice-derived Maurer–Cartan form. -/
lemma repGauge_deriv_deriv_apply (hA : IsGaugeField repLorentz repGauge A)
    (U : JetGaugeGroupI) (ρ σ τ : Fin 1 ⊕ Fin 3) (φ : Module.Dual ℝ GaugeAlgebra) :
    repGauge U (A (ρ ::ₘ {σ}) τ φ) =
      A (ρ ::ₘ {σ}) τ (adjointDualCoeff U⁻¹ 0 φ)
      + A {ρ} τ (adjointDualCoeff U⁻¹ {σ} φ)
      + A {σ} τ (adjointDualCoeff U⁻¹ {ρ} φ)
      + A 0 τ (adjointDualCoeff U⁻¹ (ρ ::ₘ {σ}) φ)
      + algebraMap ℂ B (φ (JetGaugeAlgebra.eval (JetGaugeAlgebra.deriv ρ
          (JetGaugeAlgebra.deriv σ (maurerCartanForm U⁻¹ τ))))) := by
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
  have h := hA.gauge_apply_deriv U (ρ ::ₘ {σ}) τ φ
  rw [hanti] at h
  simp only [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton,
    Multiset.sum_cons, Multiset.sum_singleton, JetGaugeAlgebra.iteratedDeriv_cons,
    LinearMap.comp_apply, JetGaugeAlgebra.iteratedDeriv_singleton] at h
  refine h.trans ?_
  abel

/-!

## The bracket of general component families

-/

/-- The bracket of two arbitrary component families, generalizing `commutator` (which
  is the case of two field symbols): assemble into `B ⊗ 𝔤` by `dualPairEquiv.symm`,
  bracket by `tensorBracket`, read back out as components. -/
noncomputable def bracketFam (f g : Module.Dual ℝ GaugeAlgebra →ₗ[ℝ] B) :
    Module.Dual ℝ GaugeAlgebra →ₗ[ℝ] B :=
  dualPairEquiv (tensorBracket (dualPairEquiv.symm f) (dualPairEquiv.symm g))

lemma commutator_eq_bracketFam
    (A : Multiset (Fin 1 ⊕ Fin 3) → (Fin 1 ⊕ Fin 3) → Module.Dual ℝ GaugeAlgebra →ₗ[ℝ] B)
    (μ ν : Fin 1 ⊕ Fin 3) : commutator A μ ν = bracketFam (A 0 μ) (A 0 ν) := rfl

/-- **The derived commutator family**: the `s`-derivative of the commutator term, given
  by the Leibniz convolution of the derivative symbols over the multiset antidiagonal.
  With the derivative symbols as primitives this convolution is the definition; for
  `s = 0` it is the commutator itself (`commutatorFam_zero`). -/
noncomputable def commutatorFam
    (A : Multiset (Fin 1 ⊕ Fin 3) → (Fin 1 ⊕ Fin 3) → Module.Dual ℝ GaugeAlgebra →ₗ[ℝ] B)
    (μ ν : Fin 1 ⊕ Fin 3) (s : Multiset (Fin 1 ⊕ Fin 3)) :
    Module.Dual ℝ GaugeAlgebra →ₗ[ℝ] B :=
  (s.antidiagonal.map fun p => bracketFam (A p.1 μ) (A p.2 ν)).sum

lemma commutatorFam_zero
    (A : Multiset (Fin 1 ⊕ Fin 3) → (Fin 1 ⊕ Fin 3) → Module.Dual ℝ GaugeAlgebra →ₗ[ℝ] B)
    (μ ν : Fin 1 ⊕ Fin 3) : commutatorFam A μ ν 0 = commutator A μ ν := by
  rw [commutatorFam, Multiset.antidiagonal_zero, Multiset.map_singleton,
    Multiset.sum_singleton, commutator_eq_bracketFam]

lemma bracketFam_add_left (f₁ f₂ g : Module.Dual ℝ GaugeAlgebra →ₗ[ℝ] B) :
    bracketFam (f₁ + f₂) g = bracketFam f₁ g + bracketFam f₂ g := by
  simp only [bracketFam, map_add, LinearMap.add_apply]

lemma bracketFam_add_right (f g₁ g₂ : Module.Dual ℝ GaugeAlgebra →ₗ[ℝ] B) :
    bracketFam f (g₁ + g₂) = bracketFam f g₁ + bracketFam f g₂ := by
  simp only [bracketFam, map_add]

/-- The bracket of two component families expanded through a basis of the gauge
  algebra: the physicists' `f^a_{bc} f^b g^c`, with `φ⁅e_j, e_k⁆` the structure
  constants contracted with the dual vector. -/
lemma bracketFam_apply_eq_sum (f g : Module.Dual ℝ GaugeAlgebra →ₗ[ℝ] B)
    (φ : Module.Dual ℝ GaugeAlgebra) :
    bracketFam f g φ = ∑ j, ∑ k,
      φ ⁅Module.Free.chooseBasis ℝ GaugeAlgebra j,
          Module.Free.chooseBasis ℝ GaugeAlgebra k⁆ •
        (f ((Module.Free.chooseBasis ℝ GaugeAlgebra).coord j) *
          g ((Module.Free.chooseBasis ℝ GaugeAlgebra).coord k)) := by
  classical
  set bv := Module.Free.chooseBasis ℝ GaugeAlgebra with hbv
  have hdual : ∀ ψ : Module.Dual ℝ GaugeAlgebra, ∑ j, ψ (bv j) • bv.coord j = ψ := by
    intro ψ
    refine LinearMap.ext fun x => ?_
    conv_rhs => rw [← bv.sum_repr x, map_sum]
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, Module.Basis.coord_apply,
      smul_eq_mul, map_smul]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  have hbasis : ∀ h : Module.Dual ℝ GaugeAlgebra →ₗ[ℝ] B,
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

/-- The bracket of families against a common Lie-algebra morphism on the dual index. -/
lemma bracketFam_comp_dualMap (T : GaugeAlgebra →ₗ[ℝ] GaugeAlgebra)
    (hT : ∀ a b, T ⁅a, b⁆ = ⁅T a, T b⁆) (f g : Module.Dual ℝ GaugeAlgebra →ₗ[ℝ] B) :
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
    (hΔ : ∀ b₁ b₂, Δ (b₁ * b₂) = Δ b₁ * b₂ + b₁ * Δ b₂) (s t : B ⊗[ℝ] GaugeAlgebra) :
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

/-- `tensorBracket` under a relative derivation on the Lie factor: if
  `T₁ ⁅a, b⁆ = ⁅T₁ a, T₀ b⁆ + ⁅T₀ a, T₁ b⁆`, the two mixed brackets sum to the
  `T₁`-image of the bracket. This is how the once-derived adjoint transport
  distributes over the commutator. -/
lemma tensorBracket_map_right_derivation (T₀ T₁ : GaugeAlgebra →ₗ[ℝ] GaugeAlgebra)
    (hT : ∀ a b, T₁ ⁅a, b⁆ = ⁅T₁ a, T₀ b⁆ + ⁅T₀ a, T₁ b⁆) (s t : B ⊗[ℝ] GaugeAlgebra) :
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
lemma bracketFam_dualMap_derivation (T₀ T₁ : GaugeAlgebra →ₗ[ℝ] GaugeAlgebra)
    (hT : ∀ a b, T₁ ⁅a, b⁆ = ⁅T₁ a, T₀ b⁆ + ⁅T₀ a, T₁ b⁆)
    (f g : Module.Dual ℝ GaugeAlgebra →ₗ[ℝ] B) :
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

set_option maxHeartbeats 1000000 in
/-- The gauge transformation of the bracket of two component families with affine
  transformation laws `f ↦ f' + φ(c_f)·1` and `g ↦ g' + φ(c_g)·1`: the bracket of the
  transformed families, two `ad` cross terms, and the constant bracket `⁅c_f, c_g⁆`.
  Pure bilinearity, with `tensorBracket_one_left/right` computing the cross terms;
  `repGauge_commutator` is the special case of two field symbols. -/
lemma repGauge_bracketFam (hA : IsGaugeField repLorentz repGauge A)
    (U : JetGaugeGroupI) {f g f' g' : Module.Dual ℝ GaugeAlgebra →ₗ[ℝ] B}
    {cf cg : GaugeAlgebra}
    (hf : ∀ ψ : Module.Dual ℝ GaugeAlgebra,
      repGauge U (f ψ) = f' ψ + algebraMap ℂ B (ψ cf))
    (hg : ∀ ψ : Module.Dual ℝ GaugeAlgebra,
      repGauge U (g ψ) = g' ψ + algebraMap ℂ B (ψ cg))
    (φ : Module.Dual ℝ GaugeAlgebra) :
    repGauge U (bracketFam f g φ) =
      bracketFam f' g' φ
      + g' (φ ∘ₗ LieAlgebra.ad ℝ GaugeAlgebra cf)
      - f' (φ ∘ₗ LieAlgebra.ad ℝ GaugeAlgebra cg)
      + algebraMap ℂ B (φ ⁅cf, cg⁆) := by
  set Φ : B →ₗ[ℝ] B := (repGauge U).restrictScalars ℝ with hΦdef
  have hΦmul : ∀ b₁ b₂ : B, Φ (b₁ * b₂) = Φ b₁ * Φ b₂ := fun b₁ b₂ =>
    hA.gauge_mul U b₁ b₂
  set s : B ⊗[ℝ] GaugeAlgebra := dualPairEquiv.symm f with hs
  set t : B ⊗[ℝ] GaugeAlgebra := dualPairEquiv.symm g with ht
  set s' : B ⊗[ℝ] GaugeAlgebra := dualPairEquiv.symm f' with hs'
  set t' : B ⊗[ℝ] GaugeAlgebra := dualPairEquiv.symm g' with ht'
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
      + (TensorProduct.map LinearMap.id (LieAlgebra.ad ℝ GaugeAlgebra cf)) t'
      - (TensorProduct.map LinearMap.id (LieAlgebra.ad ℝ GaugeAlgebra cg)) s'
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

/-- Coassociativity of antidiagonal sums: summing over `s = u + v` and then `u = x + y`
  is summing over `s = x + t` and then `t = y + v`. -/
lemma _root_.Multiset.sum_antidiagonal_assoc {ι M : Type*} [AddCommMonoid M]
    (s : Multiset ι) (h : Multiset ι → Multiset ι → Multiset ι → M) :
    (s.antidiagonal.map fun p =>
      (p.1.antidiagonal.map fun q => h q.1 q.2 p.2).sum).sum =
    (s.antidiagonal.map fun p =>
      (p.2.antidiagonal.map fun q => h p.1 q.1 q.2).sum).sum := by
  induction s using Multiset.induction_on generalizing h with
  | empty => simp
  | cons κ s ih =>
      simp only [Multiset.antidiagonal_cons, Multiset.map_add, Multiset.sum_add,
        Multiset.map_map, Function.comp_apply, Prod.map_fst, Prod.map_snd, id_eq,
        Multiset.sum_map_add]
      rw [ih (fun x y v => h x y (κ ::ₘ v)), ih (fun x y v => h x (κ ::ₘ y) v),
        ih (fun x y v => h (κ ::ₘ x) y v)]
      abel

/-- The exchange law of doubly-split antidiagonal sums: splitting `s = u + v` and then
  `u = x + y`, `v = z + w` is, with the middle parts exchanged, splitting `s = u' + v'`
  and then `u' = x + z`, `v' = y + w`. -/
lemma _root_.Multiset.sum_antidiagonal_exchange {ι M : Type*} [AddCommMonoid M]
    (s : Multiset ι) (h : Multiset ι → Multiset ι → Multiset ι → Multiset ι → M) :
    (s.antidiagonal.map fun p =>
      (p.1.antidiagonal.map fun q =>
        (p.2.antidiagonal.map fun r => h q.1 q.2 r.1 r.2).sum).sum).sum =
    (s.antidiagonal.map fun p =>
      (p.1.antidiagonal.map fun q =>
        (p.2.antidiagonal.map fun r => h q.1 r.1 q.2 r.2).sum).sum).sum := by
  induction s using Multiset.induction_on generalizing h with
  | empty => simp
  | cons κ s ih =>
      simp only [Multiset.antidiagonal_cons, Multiset.map_add, Multiset.sum_add,
        Multiset.map_map, Function.comp_apply, Prod.map_fst, Prod.map_snd, id_eq,
        Multiset.sum_map_add]
      rw [ih (fun x y z w => h x y z (κ ::ₘ w)), ih (fun x y z w => h x y (κ ::ₘ z) w),
        ih (fun x y z w => h x (κ ::ₘ y) z w), ih (fun x y z w => h (κ ::ₘ x) y z w)]
      abel

/-- A multiset sum of linear maps, applied: the sum of the applications. -/
lemma _root_.Multiset.sum_linearMap_apply {R M N : Type*} [Semiring R] [AddCommMonoid M]
    [AddCommMonoid N] [Module R M] [Module R N] (S : Multiset (M →ₗ[R] N)) (x : M) :
    S.sum x = (S.map fun f => f x).sum := by
  induction S using Multiset.induction_on with
  | empty => simp
  | cons f S ih => simp [ih]

/-- Every derived commutator term is a polynomial in derivative symbols of order at
  most that of the derivative: each Leibniz splitting contributes a product of two
  lower-order symbols. -/
lemma commutatorFam_mem
    (A : Multiset (Fin 1 ⊕ Fin 3) → (Fin 1 ⊕ Fin 3) → Module.Dual ℝ GaugeAlgebra →ₗ[ℝ] B)
    (s' : Multiset (Fin 1 ⊕ Fin 3)) (ν lam : Fin 1 ⊕ Fin 3)
    (φ : Module.Dual ℝ GaugeAlgebra) :
    commutatorFam A ν lam s' φ ∈
      Algebra.adjoin ℂ {b : B | ∃ (p : Multiset (Fin 1 ⊕ Fin 3)) (μ : Fin 1 ⊕ Fin 3)
        (φ : Module.Dual ℝ GaugeAlgebra), p.card ≤ s'.card ∧ b = A p μ φ} := by
  classical
  rw [commutatorFam, Multiset.sum_linearMap_apply, Multiset.map_map]
  refine multiset_sum_mem _ fun x hx => ?_
  obtain ⟨p, hp, rfl⟩ := Multiset.mem_map.mp hx
  have hle := Multiset.mem_antidiagonal.mp hp
  rw [Function.comp_apply, bracketFam_apply_eq_sum]
  refine Subalgebra.sum_mem _ fun j _ => Subalgebra.sum_mem _ fun k _ => ?_
  rw [← algebraMap_smul ℂ (φ ⁅Module.Free.chooseBasis ℝ GaugeAlgebra j,
      Module.Free.chooseBasis ℝ GaugeAlgebra k⁆)]
  refine Subalgebra.smul_mem _ ?_ _
  refine mul_mem
    (Algebra.subset_adjoin ⟨p.1, ν, (Module.Free.chooseBasis ℝ GaugeAlgebra).coord j, ?_, rfl⟩)
    (Algebra.subset_adjoin ⟨p.2, lam, (Module.Free.chooseBasis ℝ GaugeAlgebra).coord k, ?_, rfl⟩)
  · exact hle ▸ Multiset.card_le_card (Multiset.le_add_right _ _)
  · exact hle ▸ Multiset.card_le_card (Multiset.le_add_left _ _)


/-- A pure tensor against a multiset sum distributes over the sum. -/
lemma _root_.Multiset.tmul_sum {R M N : Type*} [CommSemiring R] [AddCommMonoid M]
    [AddCommMonoid N] [Module R M] [Module R N] (m : M) (S : Multiset N) :
    m ⊗ₜ[R] S.sum = (S.map fun n => m ⊗ₜ[R] n).sum := by
  induction S using Multiset.induction_on with
  | empty => simp
  | cons n S ih => simp [TensorProduct.tmul_add, ih]

/-!

## Iterated Leibniz expansions

-/

lemma bracketFam_zero_left (g : Module.Dual ℝ GaugeAlgebra →ₗ[ℝ] B) :
    bracketFam 0 g = 0 := by
  simp [bracketFam]

lemma bracketFam_zero_right (f : Module.Dual ℝ GaugeAlgebra →ₗ[ℝ] B) :
    bracketFam f 0 = 0 := by
  simp [bracketFam]

lemma bracketFam_sum_left (S : Multiset (Module.Dual ℝ GaugeAlgebra →ₗ[ℝ] B))
    (g : Module.Dual ℝ GaugeAlgebra →ₗ[ℝ] B) :
    bracketFam S.sum g = (S.map fun f => bracketFam f g).sum := by
  induction S using Multiset.induction_on with
  | empty => simp [bracketFam_zero_left]
  | cons f S ih => simp [bracketFam_add_left, ih]

lemma bracketFam_sum_right (f : Module.Dual ℝ GaugeAlgebra →ₗ[ℝ] B)
    (S : Multiset (Module.Dual ℝ GaugeAlgebra →ₗ[ℝ] B)) :
    bracketFam f S.sum = (S.map fun g => bracketFam f g).sum := by
  induction S using Multiset.induction_on with
  | empty => simp [bracketFam_zero_right]
  | cons g S ih => simp [bracketFam_add_right, ih]

/-!

## The all-orders transport, coefficient, and structural identities

-/

/-- The all-orders derivation property of the base-point adjoint transport: the
  transport of a bracket is the antidiagonal convolution of transports, by the
  iterated Leibniz rule for the jet bracket. -/
lemma _root_.StandardModel.adjointTransport_bracket (U : JetGaugeGroupI)
    (x : Multiset (Fin 1 ⊕ Fin 3)) (a b : GaugeAlgebra) :
    JetGaugeAlgebra.eval (JetGaugeAlgebra.iteratedDeriv x
      (JetGaugeAlgebra.adjointMap U (JetGaugeAlgebra.ofConstant ⁅a, b⁆))) =
      (x.antidiagonal.map fun p =>
        ⁅JetGaugeAlgebra.eval (JetGaugeAlgebra.iteratedDeriv p.1
            (JetGaugeAlgebra.adjointMap U (JetGaugeAlgebra.ofConstant a))),
          JetGaugeAlgebra.eval (JetGaugeAlgebra.iteratedDeriv p.2
            (JetGaugeAlgebra.adjointMap U (JetGaugeAlgebra.ofConstant b)))⁆).sum := by
  rw [JetGaugeAlgebra.ofConstant_lie, JetGaugeAlgebra.adjointMap_lie,
    JetGaugeAlgebra.iteratedDeriv_bracket, map_multiset_sum, Multiset.map_map]
  exact congrArg Multiset.sum (Multiset.map_congr rfl fun p hp => by
    rw [Function.comp_apply, LieHom.map_lie])

/-- `tensorBracket` under an antidiagonal family of transports on the Lie factor:
  if `T x` distributes over the bracket as the antidiagonal convolution of the
  `T m`, so does `id ⊗ T x` over `tensorBracket`. -/
lemma tensorBracket_map_right_antidiagonal
    (T : Multiset (Fin 1 ⊕ Fin 3) → GaugeAlgebra →ₗ[ℝ] GaugeAlgebra)
    (x : Multiset (Fin 1 ⊕ Fin 3))
    (hT : ∀ a b : GaugeAlgebra, T x ⁅a, b⁆ =
      (x.antidiagonal.map fun p => ⁅T p.1 a, T p.2 b⁆).sum)
    (s t : B ⊗[ℝ] GaugeAlgebra) :
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
lemma bracketFam_adjointDualCoeff (U : JetGaugeGroupI) (x : Multiset (Fin 1 ⊕ Fin 3))
    (f g : Module.Dual ℝ GaugeAlgebra →ₗ[ℝ] B) (φ : Module.Dual ℝ GaugeAlgebra) :
    bracketFam f g (adjointDualCoeff U x φ) =
      (x.antidiagonal.map fun p =>
        bracketFam (f ∘ₗ adjointDualCoeff U p.1) (g ∘ₗ adjointDualCoeff U p.2) φ).sum := by
  set T : Multiset (Fin 1 ⊕ Fin 3) → GaugeAlgebra →ₗ[ℝ] GaugeAlgebra := fun m =>
    JetGaugeAlgebra.eval.toLinearMap ∘ₗ JetGaugeAlgebra.iteratedDeriv m ∘ₗ
      JetGaugeAlgebra.adjointMap U ∘ₗ JetGaugeAlgebra.ofConstant with hTdef
  have hcoeff : ∀ m, adjointDualCoeff U m = (T m).dualMap := fun m => rfl
  have hT : ∀ a b : GaugeAlgebra, T x ⁅a, b⁆ =
      (x.antidiagonal.map fun p => ⁅T p.1 a, T p.2 b⁆).sum := by
    intro a b
    simp only [hTdef, LinearMap.coe_comp, Function.comp_apply, LieHom.coe_toLinearMap]
    exact adjointTransport_bracket U x a b
  rw [hcoeff x,
    show bracketFam f g ((T x).dualMap φ) =
      dualPairEquiv ((TensorProduct.map LinearMap.id (T x)) (tensorBracket
        (dualPairEquiv.symm f) (dualPairEquiv.symm g))) φ from
      (dualPairEquiv_map_right (T x) _ φ).symm,
    ← tensorBracket_map_right_antidiagonal T x hT, map_multiset_sum,
    Multiset.map_map, Multiset.sum_linearMap_apply, Multiset.map_map]
  refine congrArg Multiset.sum (Multiset.map_congr rfl fun p hp => ?_)
  simp only [Function.comp_apply]
  rw [← symm_comp_right, ← symm_comp_right, hcoeff p.1, hcoeff p.2]
  rfl

/-- The all-orders decomposition of the dual adjoint coefficient with one extra
  derivative — the generalization of `adjointDualCoeff_singleton` and
  `adjointDualCoeff_pair`: differentiating the adjoint once produces minus the
  bracket with the Maurer–Cartan form, and the remaining derivatives distribute over
  it by the Leibniz rule. -/
lemma _root_.StandardModel.adjointDualCoeff_cons (U : JetGaugeGroupI)
    (μ : Fin 1 ⊕ Fin 3) (x : Multiset (Fin 1 ⊕ Fin 3)) (φ : Module.Dual ℝ GaugeAlgebra) :
    adjointDualCoeff U (μ ::ₘ x) φ =
      -((x.antidiagonal.map fun p =>
        adjointDualCoeff U p.2 (φ ∘ₗ LieAlgebra.ad ℝ GaugeAlgebra
          (JetGaugeAlgebra.eval (JetGaugeAlgebra.iteratedDeriv p.1
            (maurerCartanForm U μ))))).sum) := by
  refine LinearMap.ext fun a => ?_
  have hkey : JetGaugeAlgebra.iteratedDeriv (μ ::ₘ x)
      (JetGaugeAlgebra.adjointMap U (JetGaugeAlgebra.ofConstant a)) =
      -((x.antidiagonal.map fun p =>
        ⁅JetGaugeAlgebra.iteratedDeriv p.1 (maurerCartanForm U μ),
          JetGaugeAlgebra.iteratedDeriv p.2
            (JetGaugeAlgebra.adjointMap U (JetGaugeAlgebra.ofConstant a))⁆).sum) := by
    rw [show (μ ::ₘ x : Multiset (Fin 1 ⊕ Fin 3)) = x + {μ} from by
        rw [add_comm, Multiset.singleton_add],
      JetGaugeAlgebra.iteratedDeriv_add, LinearMap.comp_apply,
      JetGaugeAlgebra.iteratedDeriv_singleton, deriv_adjointMap,
      JetGaugeAlgebra.deriv_ofConstant, map_zero, zero_sub, map_neg,
      JetGaugeAlgebra.iteratedDeriv_bracket]
  simp only [adjointDualCoeff, LinearMap.dualMap_apply, LinearMap.neg_apply,
    LinearMap.coe_comp, Function.comp_apply, LieHom.coe_toLinearMap]
  rw [hkey, map_neg, map_neg, map_multiset_sum, map_multiset_sum,
    Multiset.map_map, Multiset.map_map, Multiset.sum_linearMap_apply, Multiset.map_map]
  refine congrArg Neg.neg (congrArg Multiset.sum (Multiset.map_congr rfl fun p hp => ?_))
  simp only [Function.comp_apply, LieHom.map_lie]
  rfl

/-- The all-orders structural equation of the Maurer–Cartan form, at the base point:
  the `s`-th derivative of `∂_μ ω_ν − ∂_ν ω_μ + ⁅ω_μ, ω_ν⁆ = 0`, with the bracket
  expanded by the iterated Leibniz rule. -/
lemma _root_.StandardModel.eval_iteratedDeriv_maurerCartan_structure
    (U : JetGaugeGroupI) (s : Multiset (Fin 1 ⊕ Fin 3)) (μ ν : Fin 1 ⊕ Fin 3) :
    JetGaugeAlgebra.eval (JetGaugeAlgebra.iteratedDeriv (μ ::ₘ s) (maurerCartanForm U ν)) =
      JetGaugeAlgebra.eval (JetGaugeAlgebra.iteratedDeriv (ν ::ₘ s) (maurerCartanForm U μ))
      - (s.antidiagonal.map fun p =>
          ⁅JetGaugeAlgebra.eval (JetGaugeAlgebra.iteratedDeriv p.1 (maurerCartanForm U μ)),
            JetGaugeAlgebra.eval (JetGaugeAlgebra.iteratedDeriv p.2
              (maurerCartanForm U ν))⁆).sum := by
  have hconv : ∀ (κ : Fin 1 ⊕ Fin 3) (z : JetGaugeAlgebra),
      JetGaugeAlgebra.iteratedDeriv s (JetGaugeAlgebra.deriv κ z) =
        JetGaugeAlgebra.iteratedDeriv (κ ::ₘ s) z := by
    intro κ z
    rw [show (κ ::ₘ s : Multiset (Fin 1 ⊕ Fin 3)) = s + {κ} from by
        rw [add_comm, Multiset.singleton_add],
      JetGaugeAlgebra.iteratedDeriv_add, LinearMap.comp_apply,
      JetGaugeAlgebra.iteratedDeriv_singleton]
  have h0 := congrArg (fun z => JetGaugeAlgebra.eval (JetGaugeAlgebra.iteratedDeriv s z))
    (maurerCartanForm_structure U μ ν)
  simp only [map_add, map_sub, map_zero] at h0
  rw [hconv, hconv, JetGaugeAlgebra.iteratedDeriv_bracket, map_multiset_sum,
    Multiset.map_map] at h0
  rw [Multiset.map_congr rfl (fun p hp => by rw [Function.comp_apply, LieHom.map_lie])] at h0
  refine eq_sub_of_add_eq ?_
  calc JetGaugeAlgebra.eval (JetGaugeAlgebra.iteratedDeriv (μ ::ₘ s) (maurerCartanForm U ν))
        + (s.antidiagonal.map fun p =>
          ⁅JetGaugeAlgebra.eval (JetGaugeAlgebra.iteratedDeriv p.1 (maurerCartanForm U μ)),
            JetGaugeAlgebra.eval (JetGaugeAlgebra.iteratedDeriv p.2
              (maurerCartanForm U ν))⁆).sum
      = (JetGaugeAlgebra.eval (JetGaugeAlgebra.iteratedDeriv (μ ::ₘ s) (maurerCartanForm U ν))
        - JetGaugeAlgebra.eval (JetGaugeAlgebra.iteratedDeriv (ν ::ₘ s) (maurerCartanForm U μ))
        + (s.antidiagonal.map fun p =>
          ⁅JetGaugeAlgebra.eval (JetGaugeAlgebra.iteratedDeriv p.1 (maurerCartanForm U μ)),
            JetGaugeAlgebra.eval (JetGaugeAlgebra.iteratedDeriv p.2
              (maurerCartanForm U ν))⁆).sum)
        + JetGaugeAlgebra.eval (JetGaugeAlgebra.iteratedDeriv (ν ::ₘ s) (maurerCartanForm U μ)) := by
        abel
    _ = JetGaugeAlgebra.eval (JetGaugeAlgebra.iteratedDeriv (ν ::ₘ s) (maurerCartanForm U μ)) := by
        rw [h0, zero_add]

/-- Antidiagonal sums are symmetric under swapping the two parts. -/
lemma _root_.Multiset.sum_antidiagonal_swap {ι M : Type*} [AddCommMonoid M]
    (s : Multiset ι) (h : Multiset ι → Multiset ι → M) :
    (s.antidiagonal.map fun p => h p.1 p.2).sum =
    (s.antidiagonal.map fun p => h p.2 p.1).sum := by
  induction s using Multiset.induction_on generalizing h with
  | empty => simp
  | cons κ s ih =>
      simp only [Multiset.antidiagonal_cons, Multiset.map_add, Multiset.sum_add,
        Multiset.map_map, Function.comp_apply, Prod.map_fst, Prod.map_snd, id_eq]
      rw [ih (fun a b => h a (κ ::ₘ b)), ih (fun a b => h (κ ::ₘ a) b)]
      abel

/-- A multiset sum of negations is the negation of the sum. -/
lemma _root_.Multiset.sum_map_neg'' {ι M : Type*} [AddCommGroup M]
    (s : Multiset ι) (f : ι → M) :
    (s.map fun i => -f i).sum = -(s.map f).sum := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons i s ih =>
      simp only [Multiset.map_cons, Multiset.sum_cons, ih]
      abel

/-!

## The gauge transformation of iterated derivatives

-/

/-- The `κ ::ₘ s` case of `gauge_apply_deriv` with the extra derivative traced through:
  the Leibniz splittings where `κ` stays a derivative, minus (by
  `adjointDualCoeff_cons`) the splittings where `κ` hits the adjoint — an `ad` of the
  derived Maurer–Cartan form — plus the derived Maurer–Cartan shift. -/
lemma repGauge_cons_apply (hA : IsGaugeField repLorentz repGauge A)
    (U : JetGaugeGroupI) (κ : Fin 1 ⊕ Fin 3) (s : Multiset (Fin 1 ⊕ Fin 3))
    (τ : Fin 1 ⊕ Fin 3) (φ : Module.Dual ℝ GaugeAlgebra) :
    repGauge U (A (κ ::ₘ s) τ φ) =
      (s.antidiagonal.map fun p =>
        A (κ ::ₘ p.2) τ (adjointDualCoeff U⁻¹ p.1 φ)).sum
      - (s.antidiagonal.map fun p =>
          (p.1.antidiagonal.map fun q =>
            A p.2 τ (adjointDualCoeff U⁻¹ q.2
              (φ ∘ₗ LieAlgebra.ad ℝ GaugeAlgebra (JetGaugeAlgebra.eval
                (JetGaugeAlgebra.iteratedDeriv q.1 (maurerCartanForm U⁻¹ κ)))))).sum).sum
      + algebraMap ℂ B (φ (JetGaugeAlgebra.eval (JetGaugeAlgebra.iteratedDeriv (κ ::ₘ s)
          (maurerCartanForm U⁻¹ τ)))) := by
  rw [hA.gauge_apply_deriv U (κ ::ₘ s) τ φ]
  congr 1
  simp only [Multiset.antidiagonal_cons, Multiset.map_add, Multiset.sum_add,
    Multiset.map_map, Function.comp_apply, Prod.map_fst, Prod.map_snd, id_eq]
  have hsec : (Multiset.map (fun p =>
        A p.2 τ (adjointDualCoeff U⁻¹ (κ ::ₘ p.1) φ)) s.antidiagonal).sum =
      -(s.antidiagonal.map fun p =>
          (p.1.antidiagonal.map fun q =>
            A p.2 τ (adjointDualCoeff U⁻¹ q.2
              (φ ∘ₗ LieAlgebra.ad ℝ GaugeAlgebra (JetGaugeAlgebra.eval
                (JetGaugeAlgebra.iteratedDeriv q.1 (maurerCartanForm U⁻¹ κ)))))).sum).sum := by
    rw [← Multiset.sum_map_neg'']
    refine congrArg Multiset.sum (Multiset.map_congr rfl fun p hp => ?_)
    rw [adjointDualCoeff_cons U⁻¹ κ p.1 φ, map_neg, map_multiset_sum, Multiset.map_map]
    exact congrArg Neg.neg (congrArg Multiset.sum (Multiset.map_congr rfl fun q hq => rfl))
  rw [hsec, sub_eq_add_neg]

set_option maxHeartbeats 2000000 in
/-- The all-orders gauge transformation of the derived commutator term: the Leibniz
  convolution of the transformed commutator, the two `ad` cross-term convolutions,
  and the convolution of Maurer–Cartan bracket shifts. This is `repGauge_commutator`
  at every derivative order simultaneously; the regrouping of the four-fold splitting
  is `Multiset.sum_antidiagonal_exchange`. -/
lemma repGauge_commutatorFam (hA : IsGaugeField repLorentz repGauge A)
    (U : JetGaugeGroupI) (s : Multiset (Fin 1 ⊕ Fin 3)) (μ ν : Fin 1 ⊕ Fin 3)
    (φ : Module.Dual ℝ GaugeAlgebra) :
    repGauge U (commutatorFam A μ ν s φ) =
      (s.antidiagonal.map fun p =>
        commutatorFam A μ ν p.2 (adjointDualCoeff U⁻¹ p.1 φ)).sum
      + (s.antidiagonal.map fun p =>
          (p.2.antidiagonal.map fun r =>
            A r.2 ν (adjointDualCoeff U⁻¹ r.1
              (φ ∘ₗ LieAlgebra.ad ℝ GaugeAlgebra (JetGaugeAlgebra.eval
                (JetGaugeAlgebra.iteratedDeriv p.1 (maurerCartanForm U⁻¹ μ)))))).sum).sum
      - (s.antidiagonal.map fun p =>
          (p.1.antidiagonal.map fun q =>
            A q.2 μ (adjointDualCoeff U⁻¹ q.1
              (φ ∘ₗ LieAlgebra.ad ℝ GaugeAlgebra (JetGaugeAlgebra.eval
                (JetGaugeAlgebra.iteratedDeriv p.2 (maurerCartanForm U⁻¹ ν)))))).sum).sum
      + (s.antidiagonal.map fun p =>
          algebraMap ℂ B (φ ⁅JetGaugeAlgebra.eval (JetGaugeAlgebra.iteratedDeriv p.1
              (maurerCartanForm U⁻¹ μ)),
            JetGaugeAlgebra.eval (JetGaugeAlgebra.iteratedDeriv p.2
              (maurerCartanForm U⁻¹ ν))⁆)).sum := by
  -- the affine transformation law of the derived symbols, with the Leibniz sum as a map
  have hAlaw : ∀ (τ : Fin 1 ⊕ Fin 3) (u : Multiset (Fin 1 ⊕ Fin 3))
      (ψ : Module.Dual ℝ GaugeAlgebra),
      repGauge U (A u τ ψ) =
        ((u.antidiagonal.map fun q => A q.2 τ ∘ₗ adjointDualCoeff U⁻¹ q.1).sum) ψ
        + algebraMap ℂ B (ψ (JetGaugeAlgebra.eval
            (JetGaugeAlgebra.iteratedDeriv u (maurerCartanForm U⁻¹ τ)))) := by
    intro τ u ψ
    rw [hA.gauge_apply_deriv U u τ ψ, Multiset.sum_linearMap_apply, Multiset.map_map]
    congr 1
  -- the convolution triple sum in its two groupings
  have hMa : (s.antidiagonal.map fun p =>
      bracketFam ((p.1.antidiagonal.map fun q => A q.2 μ ∘ₗ adjointDualCoeff U⁻¹ q.1).sum)
        ((p.2.antidiagonal.map fun r => A r.2 ν ∘ₗ adjointDualCoeff U⁻¹ r.1).sum) φ).sum =
      (s.antidiagonal.map fun p =>
        (p.1.antidiagonal.map fun q =>
          (p.2.antidiagonal.map fun r =>
            bracketFam (A q.2 μ ∘ₗ adjointDualCoeff U⁻¹ q.1)
              (A r.2 ν ∘ₗ adjointDualCoeff U⁻¹ r.1) φ).sum).sum).sum := by
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
      commutatorFam A μ ν p.2 (adjointDualCoeff U⁻¹ p.1 φ)).sum =
      (s.antidiagonal.map fun p =>
        (p.1.antidiagonal.map fun q =>
          (p.2.antidiagonal.map fun r =>
            bracketFam (A r.1 μ ∘ₗ adjointDualCoeff U⁻¹ q.1)
              (A r.2 ν ∘ₗ adjointDualCoeff U⁻¹ q.2) φ).sum).sum).sum := by
    refine congrArg Multiset.sum (Multiset.map_congr rfl fun p hp => ?_)
    rw [commutatorFam, Multiset.sum_linearMap_apply, Multiset.map_map,
      Multiset.map_congr rfl (fun r hr => by
        rw [Function.comp_apply,
          bracketFam_adjointDualCoeff U⁻¹ p.1 (A r.1 μ) (A r.2 ν) φ]),
      Multiset.sum_map_sum_map]
  have hM := hMa.trans ((Multiset.sum_antidiagonal_exchange s fun a b c d =>
      bracketFam (A b μ ∘ₗ adjointDualCoeff U⁻¹ a)
        (A d ν ∘ₗ adjointDualCoeff U⁻¹ c) φ).trans hMc.symm)
  -- the cross-term sums, applied
  have hCg : ∀ p : Multiset (Fin 1 ⊕ Fin 3) × Multiset (Fin 1 ⊕ Fin 3),
      ((p.2.antidiagonal.map fun r => A r.2 ν ∘ₗ adjointDualCoeff U⁻¹ r.1).sum)
        (φ ∘ₗ LieAlgebra.ad ℝ GaugeAlgebra (JetGaugeAlgebra.eval
          (JetGaugeAlgebra.iteratedDeriv p.1 (maurerCartanForm U⁻¹ μ)))) =
      (p.2.antidiagonal.map fun r =>
        A r.2 ν (adjointDualCoeff U⁻¹ r.1
          (φ ∘ₗ LieAlgebra.ad ℝ GaugeAlgebra (JetGaugeAlgebra.eval
            (JetGaugeAlgebra.iteratedDeriv p.1 (maurerCartanForm U⁻¹ μ)))))).sum := by
    intro p
    rw [Multiset.sum_linearMap_apply, Multiset.map_map]
    refine congrArg Multiset.sum (Multiset.map_congr rfl fun r hr => ?_)
    simp only [Function.comp_apply, LinearMap.coe_comp]
  have hCf : ∀ p : Multiset (Fin 1 ⊕ Fin 3) × Multiset (Fin 1 ⊕ Fin 3),
      ((p.1.antidiagonal.map fun q => A q.2 μ ∘ₗ adjointDualCoeff U⁻¹ q.1).sum)
        (φ ∘ₗ LieAlgebra.ad ℝ GaugeAlgebra (JetGaugeAlgebra.eval
          (JetGaugeAlgebra.iteratedDeriv p.2 (maurerCartanForm U⁻¹ ν)))) =
      (p.1.antidiagonal.map fun q =>
        A q.2 μ (adjointDualCoeff U⁻¹ q.1
          (φ ∘ₗ LieAlgebra.ad ℝ GaugeAlgebra (JetGaugeAlgebra.eval
            (JetGaugeAlgebra.iteratedDeriv p.2 (maurerCartanForm U⁻¹ ν)))))).sum := by
    intro p
    rw [Multiset.sum_linearMap_apply, Multiset.map_map]
    refine congrArg Multiset.sum (Multiset.map_congr rfl fun q hq => ?_)
    simp only [Function.comp_apply, LinearMap.coe_comp]
  -- expand the left side and split the four convolutions
  rw [commutatorFam, Multiset.sum_linearMap_apply, Multiset.map_map, map_multiset_sum,
    Multiset.map_map,
    Multiset.map_congr rfl (fun p hp => by
      rw [Function.comp_apply, Function.comp_apply,
        hA.repGauge_bracketFam U (hAlaw μ p.1) (hAlaw ν p.2) φ, hCg p, hCf p]),
    Multiset.sum_map_add, Multiset.sum_map_sub, Multiset.sum_map_add, hM]

end IsGaugeField

end StandardModel
