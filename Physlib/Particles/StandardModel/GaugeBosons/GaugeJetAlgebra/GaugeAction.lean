/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Particles.StandardModel.GaugeBosons.GaugeJetAlgebra.JetDeriv
public import Physlib.Particles.StandardModel.Matter.JetComponentSpace.CovariantDeriv
public import Physlib.Particles.StandardModel.GaugeGroup.MaurerCartan.Basic
/-!
# The gauge action on the gauge-boson jet algebra

## i. Overview

A jet of gauge transformations `U` acts on the gauge field by
`A_μ ↦ Ad_U A_μ + mc(U)_μ`, so on a component function `∂_s A_μ^φ` it acts affinely: the
linear part is the all-orders Leibniz convolution of the Taylor coefficients of `Ad(U⁻¹)`
against lower component functions, and the constant part is the Taylor coefficient of the
Maurer–Cartan form of `U⁻¹`. The action extends to the whole jet algebra as the
substitution homomorphism determined by this affine action on the generators.

The heart of the file is the *Taylor–Leibniz theorem* for the adjoint action
(`JetGaugeAlgebra.eval_iteratedDeriv_adjointMap`): the base-point Taylor coefficients of
`Ad_U Y` are the convolution of the coefficients of `Ad_U` — the `adjointCoeff` of the
covariance machinery — with those of `Y`. Multiplicativity of the transport and the
cocycle identity for the Maurer–Cartan shift are both corollaries.

## ii. Key results

- `JetGaugeAlgebra.eval_iteratedDeriv_adjointMap` : the Taylor–Leibniz theorem for the
  adjoint action on jets.
- `IsGaugeField.adjointCoeff_mul` : the Taylor coefficients of `Ad` are multiplicative up
  to convolution.
- `GaugeJetAlgebra.transport` : the linear part of the gauge action on the component
  space.
- `GaugeJetAlgebra.mcShift` : the Maurer–Cartan shift.
- `GaugeJetAlgebra.repJetGaugeGroupI` : the action of the jet gauge group on the jet
  algebra.
- `GaugeJetAlgebra.repJetGaugeGroupI_iteratedJetDeriv_ofA` : the transformation law of
  the derivative generators, in the form used by `IsGaugeField`.

## iii. Table of contents

- A. Taylor–Leibniz for jets
  - A.1. The matrix Leibniz rule at the base point
- B. The Taylor–Leibniz theorem for the adjoint action
  - B.1. Collapsing convolutions against constants
  - B.2. The theorem
  - B.3. Multiplicativity of the adjoint Taylor coefficients
- C. The transport on the component space
- D. The Maurer–Cartan shift
- E. The action of the jet gauge group
  - E.1. The transformation law of the generators

-/

@[expose] public section

set_option maxHeartbeats 1000000

namespace StandardModel

open TensorProduct MvPowerSeries

/-!

## A. Taylor–Leibniz for jets

-/

/-!

### A.1. The matrix Leibniz rule at the base point

-/

/-- The exchange of a finite sum with a multiset sum. -/
lemma _root_.Multiset.sum_map_finsetSum {α β M : Type*} [AddCommMonoid M]
    (m : Multiset α) (t : Finset β) (f : β → α → M) :
    (m.map fun a => ∑ b ∈ t, f b a).sum = ∑ b ∈ t, (m.map (f b)).sum := by
  induction m using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    rw [Multiset.map_cons, Multiset.sum_cons, ih, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun b _ => by rw [Multiset.map_cons, Multiset.sum_cons]

/-- The entry of a multiset sum of matrices is the multiset sum of the entries. -/
lemma matrix_multiset_sum_apply {κ α : Type*} [AddCommMonoid α]
    (m : Multiset (Matrix κ κ α)) (i j : κ) :
    m.sum i j = (m.map fun A => A i j).sum := by
  induction m using Multiset.induction_on with
  | empty => rfl
  | cons A t ih =>
    rw [Multiset.sum_cons, Multiset.map_cons, Multiset.sum_cons, ← ih, Matrix.add_apply]

/-- **The matrix Leibniz rule at the base point**: the base-point Taylor coefficients of
  a product of matrices of jets are the convolution of the base-point coefficients of the
  factors. -/
lemma matrix_constantCoeff_foldl_pderiv_mul {κ : Type} [Fintype κ] [DecidableEq κ]
    (s : Multiset (Fin 1 ⊕ Fin 3)) (M N : Matrix κ κ JetRing) :
    ((M * N).map fun f => constantCoeff (s.foldl (fun h ρ => pderiv ℂ ρ h) f))
      = (s.antidiagonal.map fun p =>
          (M.map fun f => constantCoeff (p.1.foldl (fun h ρ => pderiv ℂ ρ h) f)) *
            (N.map fun f => constantCoeff (p.2.foldl (fun h ρ => pderiv ℂ ρ h) f))).sum := by
  ext i j
  rw [Matrix.map_apply, Matrix.mul_apply, JetRing.foldl_pderiv_sum, map_sum]
  simp only [JetRing.constantCoeff_foldl_pderiv_mul]
  rw [← Multiset.sum_map_finsetSum, matrix_multiset_sum_apply, Multiset.map_map]
  refine congrArg Multiset.sum (Multiset.map_congr rfl fun p hp => ?_)
  rw [Function.comp_apply, Matrix.mul_apply]
  exact Finset.sum_congr rfl fun k _ => by rw [Matrix.map_apply, Matrix.map_apply]

/-!

## B. The Taylor–Leibniz theorem for the adjoint action

-/

/-!

### B.1. Collapsing convolutions against constants

-/

/-- A sum over the antidiagonal of a family vanishing off `p.1 = 0` collapses to the
  single term at `(0, s)`. -/
lemma _root_.Multiset.sum_antidiagonal_eq_of_fst_ne_zero {ι M : Type*} [AddCommMonoid M]
    (s : Multiset ι) (F : Multiset ι × Multiset ι → M)
    (hF : ∀ p : Multiset ι × Multiset ι, p.1 ≠ 0 → F p = 0) :
    (s.antidiagonal.map F).sum = F (0, s) := by
  induction s using Multiset.induction_on generalizing F with
  | empty => simp [Multiset.antidiagonal_zero]
  | cons a t ih =>
    rw [Multiset.antidiagonal_cons, Multiset.map_add, Multiset.sum_add, Multiset.map_map,
      Multiset.map_map,
      show ((t.antidiagonal.map (F ∘ Prod.map (Multiset.cons a) id)).sum) = 0 from
        Multiset.sum_eq_zero fun x hx => by
          obtain ⟨p, hp, rfl⟩ := Multiset.mem_map.mp hx
          exact hF _ (Multiset.cons_ne_zero),
      add_zero, ih (F ∘ Prod.map id (Multiset.cons a)) fun p hp => hF _ hp]
    rfl

/-- A sum over the antidiagonal of a family vanishing off `p.2 = 0` collapses to the
  single term at `(s, 0)`. -/
lemma _root_.Multiset.sum_antidiagonal_eq_of_snd_ne_zero {ι M : Type*} [AddCommMonoid M]
    (s : Multiset ι) (F : Multiset ι × Multiset ι → M)
    (hF : ∀ p : Multiset ι × Multiset ι, p.2 ≠ 0 → F p = 0) :
    (s.antidiagonal.map F).sum = F (s, 0) := by
  rw [show (s.antidiagonal.map F).sum
      = (s.antidiagonal.map fun p => (fun a b => F (b, a)) p.2 p.1).sum from rfl,
    ← Multiset.sum_antidiagonal_swap s (fun a b => F (b, a))]
  exact Multiset.sum_antidiagonal_eq_of_fst_ne_zero s (fun p => F (p.2, p.1))
    fun p hp => hF _ hp

/-- The exchange of the second and third slot in a nested antidiagonal sum. -/
lemma _root_.Multiset.sum_antidiagonal_middle_exchange {ι M : Type*} [AddCommMonoid M]
    (s : Multiset ι) (h : Multiset ι → Multiset ι → Multiset ι → M) :
    (s.antidiagonal.map fun p =>
        (p.1.antidiagonal.map fun q => h q.1 q.2 p.2).sum).sum
      = (s.antidiagonal.map fun p =>
        (p.1.antidiagonal.map fun q => h q.1 p.2 q.2).sum).sum := by
  rw [Multiset.sum_antidiagonal_assoc s h,
    Multiset.sum_antidiagonal_assoc s (fun a b c => h a c b)]
  refine congrArg Multiset.sum (Multiset.map_congr rfl fun p hp => ?_)
  exact Multiset.sum_antidiagonal_swap p.2 (fun a b => h p.1 a b)

/-- The convolution against a constant middle matrix: only the empty derivative multiset
  survives on the constant factor. -/
lemma matrix_cc_foldl_conj_const {κ : Type} [Fintype κ] [DecidableEq κ]
    (p : Multiset (Fin 1 ⊕ Fin 3)) (P Q : Matrix κ κ JetRing) (b : Matrix κ κ ℂ) :
    ((P * b.map (C : ℂ → JetRing) * Q).map fun f =>
        constantCoeff (p.foldl (fun h ρ => pderiv ℂ ρ h) f))
      = (p.antidiagonal.map fun r =>
          (P.map fun f => constantCoeff (r.1.foldl (fun h ρ => pderiv ℂ ρ h) f)) * b *
            (Q.map fun f => constantCoeff (r.2.foldl (fun h ρ => pderiv ℂ ρ h) f))).sum := by
  have hconst : ∀ m : Multiset (Fin 1 ⊕ Fin 3),
      ((b.map (C : ℂ → JetRing)).map fun f =>
        constantCoeff (m.foldl (fun h ρ => pderiv ℂ ρ h) f))
      = if m = 0 then b else 0 := by
    intro m
    rcases eq_or_ne m 0 with rfl | hm
    · ext i j
      simp [Matrix.map_apply, constantCoeff_C]
    · ext i j
      simp [Matrix.map_apply, JetRing.foldl_pderiv_C_of_ne_zero hm, hm]
  rw [matrix_constantCoeff_foldl_pderiv_mul,
    Multiset.map_congr rfl (fun q hq => by
      rw [matrix_constantCoeff_foldl_pderiv_mul,
        Multiset.map_congr rfl (fun r hr => by rw [hconst r.2]),
        Multiset.sum_antidiagonal_eq_of_snd_ne_zero q.1
          (fun r => (P.map fun f =>
            constantCoeff (r.1.foldl (fun h ρ => pderiv ℂ ρ h) f)) *
              (if r.2 = 0 then b else 0))
          (fun r hr => by rw [if_neg hr, Matrix.mul_zero]),
        if_pos rfl])]

/-!

### B.2. The theorem

-/

namespace GaugeAlgebra

/-- The `su(3)` component of a multiset sum. -/
lemma multiset_sum_toSU3Matrix (m : Multiset GaugeAlgebra) :
    m.sum.toSU3Matrix = (m.map GaugeAlgebra.toSU3Matrix).sum := by
  induction m using Multiset.induction_on with
  | empty => rfl
  | cons a t ih => rw [Multiset.sum_cons, Multiset.map_cons, Multiset.sum_cons, ← ih,
      GaugeAlgebra.add_toSU3Matrix]

/-- The `su(2)` component of a multiset sum. -/
lemma multiset_sum_toSU2Matrix (m : Multiset GaugeAlgebra) :
    m.sum.toSU2Matrix = (m.map GaugeAlgebra.toSU2Matrix).sum := by
  induction m using Multiset.induction_on with
  | empty => rfl
  | cons a t ih => rw [Multiset.sum_cons, Multiset.map_cons, Multiset.sum_cons, ← ih,
      GaugeAlgebra.add_toSU2Matrix]

/-- The `u(1)` component of a multiset sum. -/
lemma multiset_sum_toU1Value (m : Multiset GaugeAlgebra) :
    m.sum.toU1Value = (m.map GaugeAlgebra.toU1Value).sum := by
  induction m using Multiset.induction_on with
  | empty => rfl
  | cons a t ih => rw [Multiset.sum_cons, Multiset.map_cons, Multiset.sum_cons, ← ih,
      GaugeAlgebra.add_toU1Value]

end GaugeAlgebra

namespace JetGaugeAlgebra

/-- The `su(3)` component of the base-point Taylor coefficients. -/
lemma eval_iteratedDeriv_toSU3Matrix (x : Multiset (Fin 1 ⊕ Fin 3)) (a : JetGaugeAlgebra) :
    (eval (iteratedDeriv x a)).toSU3Matrix
      = a.toSU3Matrix.map fun f =>
          constantCoeff (x.foldl (fun h ρ => pderiv ℂ ρ h) f) := by
  ext i j
  rw [eval_toSU3Matrix_apply, iteratedDeriv_toSU3Matrix, Matrix.map_apply, Matrix.map_apply]

/-- The `su(2)` component of the base-point Taylor coefficients. -/
lemma eval_iteratedDeriv_toSU2Matrix (x : Multiset (Fin 1 ⊕ Fin 3)) (a : JetGaugeAlgebra) :
    (eval (iteratedDeriv x a)).toSU2Matrix
      = a.toSU2Matrix.map fun f =>
          constantCoeff (x.foldl (fun h ρ => pderiv ℂ ρ h) f) := by
  ext i j
  rw [eval_toSU2Matrix_apply, iteratedDeriv_toSU2Matrix, Matrix.map_apply, Matrix.map_apply]

/-- The `u(1)` component of the base-point Taylor coefficients. -/
lemma eval_iteratedDeriv_toU1Value (x : Multiset (Fin 1 ⊕ Fin 3)) (a : JetGaugeAlgebra) :
    (eval (iteratedDeriv x a)).toU1Value
      = constantCoeff (x.foldl (fun h ρ => pderiv ℂ ρ h) a.toU1Value) := by
  rw [eval_toU1Value_eq, iteratedDeriv_toU1Value]

/-- The `su(3)` component of the adjoint Taylor coefficient. -/
lemma _root_.StandardModel.IsGaugeField.adjointCoeff_toSU3Matrix (U : JetGaugeGroupI)
    (p : Multiset (Fin 1 ⊕ Fin 3)) (b : GaugeAlgebra) :
    (IsGaugeField.adjointCoeff U p b).toSU3Matrix
      = ((U.1.1 * b.toSU3Matrix.map (C : ℂ → JetRing) * star U.1.1).map fun f =>
          constantCoeff (p.foldl (fun h ρ => pderiv ℂ ρ h) f)) := by
  rw [IsGaugeField.adjointCoeff]
  simp only [LinearMap.coe_comp, Function.comp_apply, LieHom.coe_toLinearMap]
  rw [eval_iteratedDeriv_toSU3Matrix, adjointMap_toSU3Matrix, ofConstant_toSU3Matrix]

/-- The `su(2)` component of the adjoint Taylor coefficient. -/
lemma _root_.StandardModel.IsGaugeField.adjointCoeff_toSU2Matrix (U : JetGaugeGroupI)
    (p : Multiset (Fin 1 ⊕ Fin 3)) (b : GaugeAlgebra) :
    (IsGaugeField.adjointCoeff U p b).toSU2Matrix
      = ((U.2.1.1 * b.toSU2Matrix.map (C : ℂ → JetRing) * star U.2.1.1).map fun f =>
          constantCoeff (p.foldl (fun h ρ => pderiv ℂ ρ h) f)) := by
  rw [IsGaugeField.adjointCoeff]
  simp only [LinearMap.coe_comp, Function.comp_apply, LieHom.coe_toLinearMap]
  rw [eval_iteratedDeriv_toSU2Matrix, adjointMap_toSU2Matrix, ofConstant_toSU2Matrix]

/-- The `u(1)` component of the adjoint Taylor coefficient. -/
lemma _root_.StandardModel.IsGaugeField.adjointCoeff_toU1Value (U : JetGaugeGroupI)
    (p : Multiset (Fin 1 ⊕ Fin 3)) (b : GaugeAlgebra) :
    (IsGaugeField.adjointCoeff U p b).toU1Value
      = constantCoeff (p.foldl (fun h ρ => pderiv ℂ ρ h) (C b.toU1Value)) := by
  rw [IsGaugeField.adjointCoeff]
  simp only [LinearMap.coe_comp, Function.comp_apply, LieHom.coe_toLinearMap]
  rw [eval_iteratedDeriv_toU1Value, adjointMap_toU1Value, ofConstant_toU1Value]

/-- **The Taylor–Leibniz theorem for the adjoint action on jets**: the base-point Taylor
  coefficients of `Ad_U Y` are the antidiagonal convolution of the Taylor coefficients of
  `Ad_U` — the `IsGaugeField.adjointCoeff` of the covariance machinery — with those of
  `Y`. -/
theorem eval_iteratedDeriv_adjointMap (U : JetGaugeGroupI)
    (x : Multiset (Fin 1 ⊕ Fin 3)) (Y : JetGaugeAlgebra) :
    eval (iteratedDeriv x (adjointMap U Y))
      = (x.antidiagonal.map fun p =>
          IsGaugeField.adjointCoeff U p.1 (eval (iteratedDeriv p.2 Y))).sum := by
  have hmat : ∀ {κ : Type} [Fintype κ] [DecidableEq κ]
      (P Q W : Matrix κ κ JetRing),
      ((P * W * Q).map fun f => constantCoeff (x.foldl (fun h ρ => pderiv ℂ ρ h) f))
        = (x.antidiagonal.map fun p =>
            (p.1.antidiagonal.map fun r =>
              (P.map fun f => constantCoeff (r.1.foldl (fun h ρ => pderiv ℂ ρ h) f)) *
                (W.map fun f => constantCoeff (p.2.foldl (fun h ρ => pderiv ℂ ρ h) f)) *
                (Q.map fun f =>
                  constantCoeff (r.2.foldl (fun h ρ => pderiv ℂ ρ h) f))).sum).sum := by
    intro κ _ _ P Q W
    rw [matrix_constantCoeff_foldl_pderiv_mul,
      Multiset.map_congr rfl (fun p hp => by
        rw [matrix_constantCoeff_foldl_pderiv_mul, ← Multiset.sum_map_mul_right])]
    exact Multiset.sum_antidiagonal_middle_exchange x fun a b c =>
      (P.map fun f => constantCoeff (a.foldl (fun h ρ => pderiv ℂ ρ h) f)) *
        (W.map fun f => constantCoeff (b.foldl (fun h ρ => pderiv ℂ ρ h) f)) *
        (Q.map fun f => constantCoeff (c.foldl (fun h ρ => pderiv ℂ ρ h) f))
  refine GaugeAlgebra.ext_of_matrix ?_ ?_ ?_
  · rw [GaugeAlgebra.multiset_sum_toSU3Matrix, Multiset.map_map,
      eval_iteratedDeriv_toSU3Matrix, adjointMap_toSU3Matrix, hmat U.1.1 (star U.1.1)
        Y.toSU3Matrix]
    refine congrArg Multiset.sum (Multiset.map_congr rfl fun p hp => ?_)
    rw [Function.comp_apply, IsGaugeField.adjointCoeff_toSU3Matrix,
      matrix_cc_foldl_conj_const, eval_iteratedDeriv_toSU3Matrix]
  · rw [GaugeAlgebra.multiset_sum_toSU2Matrix, Multiset.map_map,
      eval_iteratedDeriv_toSU2Matrix, adjointMap_toSU2Matrix, hmat U.2.1.1 (star U.2.1.1)
        Y.toSU2Matrix]
    refine congrArg Multiset.sum (Multiset.map_congr rfl fun p hp => ?_)
    rw [Function.comp_apply, IsGaugeField.adjointCoeff_toSU2Matrix,
      matrix_cc_foldl_conj_const, eval_iteratedDeriv_toSU2Matrix]
  · rw [GaugeAlgebra.multiset_sum_toU1Value, Multiset.map_map,
      eval_iteratedDeriv_toU1Value, adjointMap_toU1Value,
      Multiset.map_congr rfl (fun p hp => by
        rw [Function.comp_apply, IsGaugeField.adjointCoeff_toU1Value]),
      Multiset.sum_antidiagonal_eq_of_fst_ne_zero x
        (fun p => constantCoeff (p.1.foldl (fun h ρ => pderiv ℂ ρ h)
          (C ((eval (iteratedDeriv p.2 Y)).toU1Value))))
        (fun p hp => by rw [JetRing.foldl_pderiv_C_of_ne_zero hp, map_zero]),
      show ((0 : Multiset (Fin 1 ⊕ Fin 3)).foldl (fun h ρ => pderiv ℂ ρ h)
          (C ((eval (iteratedDeriv x Y)).toU1Value)))
        = C ((eval (iteratedDeriv x Y)).toU1Value) from rfl,
      constantCoeff_C, eval_iteratedDeriv_toU1Value]

/-!

### B.3. Multiplicativity of the adjoint Taylor coefficients

-/

/-- **The adjoint Taylor coefficients are multiplicative up to convolution**: the
  coefficient of a product of jets of gauge transformations is the antidiagonal
  convolution of the coefficients of the factors. -/
lemma _root_.StandardModel.IsGaugeField.adjointCoeff_mul (U V : JetGaugeGroupI)
    (x : Multiset (Fin 1 ⊕ Fin 3)) :
    IsGaugeField.adjointCoeff (U * V) x
      = (x.antidiagonal.map fun p =>
          IsGaugeField.adjointCoeff U p.1 ∘ₗ IsGaugeField.adjointCoeff V p.2).sum := by
  refine LinearMap.ext fun a => ?_
  rw [Multiset.sum_linearMap_apply, Multiset.map_map,
    show IsGaugeField.adjointCoeff (U * V) x a
      = eval (iteratedDeriv x (adjointMap U (adjointMap V (ofConstant a)))) from by
      rw [IsGaugeField.adjointCoeff]
      simp only [LinearMap.coe_comp, Function.comp_apply, LieHom.coe_toLinearMap]
      rw [show adjointMap (U * V) (ofConstant a)
          = adjointMap U (adjointMap V (ofConstant a)) from by
        rw [show adjointMap (U * V) = JetGaugeAlgebra.adjoint (U * V) from rfl, map_mul]
        rfl],
    eval_iteratedDeriv_adjointMap]
  exact congrArg Multiset.sum (Multiset.map_congr rfl fun p hp => by
    rw [Function.comp_apply, LinearMap.comp_apply]
    rfl)

/-- The iterated derivative of a constant jet vanishes for a nonempty multiset of
  directions. -/
lemma iteratedDeriv_ofConstant_of_ne_zero {p : Multiset (Fin 1 ⊕ Fin 3)} (hp : p ≠ 0)
    (a : GaugeAlgebra) : iteratedDeriv p (ofConstant a) = 0 := by
  induction p using Multiset.induction_on with
  | empty => exact absurd rfl hp
  | cons μ t ih =>
    rw [iteratedDeriv_cons, LinearMap.comp_apply]
    rcases eq_or_ne t 0 with rfl | ht
    · rw [iteratedDeriv_zero, LinearMap.id_apply, JetGaugeAlgebra.deriv_ofConstant]
    · rw [ih ht, map_zero]

/-- The adjoint Taylor coefficient of the identity: only the base point survives. -/
lemma _root_.StandardModel.IsGaugeField.adjointCoeff_one (p : Multiset (Fin 1 ⊕ Fin 3)) :
    IsGaugeField.adjointCoeff (1 : JetGaugeGroupI) p
      = if p = 0 then LinearMap.id else 0 := by
  refine LinearMap.ext fun a => ?_
  rw [IsGaugeField.adjointCoeff]
  simp only [LinearMap.coe_comp, Function.comp_apply, LieHom.coe_toLinearMap]
  rw [show adjointMap (1 : JetGaugeGroupI) (ofConstant a) = ofConstant a from by
    rw [show adjointMap (1 : JetGaugeGroupI) = JetGaugeAlgebra.adjoint 1 from rfl, map_one]
    rfl]
  rcases eq_or_ne p 0 with rfl | hp
  · rw [iteratedDeriv_zero, LinearMap.id_apply, eval_ofConstant, if_pos rfl,
      LinearMap.id_apply]
  · rw [iteratedDeriv_ofConstant_of_ne_zero hp, map_zero, if_neg hp, LinearMap.zero_apply]

end JetGaugeAlgebra

/-!

## C. The transport on the component space

-/

namespace GaugeBoson

/-- The adjoint transport on the gauge-boson target space at `p` derivatives: the adjoint
  Taylor coefficient on the gauge-algebra factor, the identity on the spacetime index. -/
noncomputable def adjointTransport (U : JetGaugeGroupI) (p : Multiset (Fin 1 ⊕ Fin 3)) :
    GaugeBoson →ₗ[ℝ] GaugeBoson :=
  valLinEquiv.symm.toLinearMap ∘ₗ
    TensorProduct.map LinearMap.id (IsGaugeField.adjointCoeff U p) ∘ₗ
    valLinEquiv.toLinearMap

lemma adjointTransport_mk_tmul (U : JetGaugeGroupI) (p : Multiset (Fin 1 ⊕ Fin 3))
    (v : Lorentz.CoVector) (a : GaugeAlgebra) :
    adjointTransport U p ⟨v ⊗ₜ[ℝ] a⟩ = ⟨v ⊗ₜ[ℝ] IsGaugeField.adjointCoeff U p a⟩ := rfl

/-- The adjoint transport at the identity: only the base point survives. -/
lemma adjointTransport_one (p : Multiset (Fin 1 ⊕ Fin 3)) :
    adjointTransport 1 p = if p = 0 then LinearMap.id else 0 := by
  rw [adjointTransport, IsGaugeField.adjointCoeff_one]
  rcases eq_or_ne p 0 with rfl | hp
  · rw [if_pos rfl, if_pos rfl, TensorProduct.map_id]
    refine LinearMap.ext fun v => ?_
    simp
  · rw [if_neg hp, if_neg hp]
    refine LinearMap.ext fun v => ?_
    rw [show TensorProduct.map (LinearMap.id (M := Lorentz.CoVector))
        (0 : GaugeAlgebra →ₗ[ℝ] GaugeAlgebra) = 0 from by
      refine TensorProduct.ext' fun x a => ?_
      rw [TensorProduct.map_tmul, LinearMap.zero_apply, TensorProduct.tmul_zero]
      rfl]
    simp

/-- The adjoint transport of a product: the antidiagonal convolution of transports. -/
lemma adjointTransport_mul (U V : JetGaugeGroupI) (p : Multiset (Fin 1 ⊕ Fin 3)) :
    adjointTransport (U * V) p
      = (p.antidiagonal.map fun r =>
          adjointTransport U r.1 ∘ₗ adjointTransport V r.2).sum := by
  refine LinearMap.ext fun v => ?_
  rw [Multiset.sum_linearMap_apply, Multiset.map_map]
  obtain ⟨m⟩ := v
  induction m using TensorProduct.induction_on with
  | zero =>
    rw [show (⟨0⟩ : GaugeBoson) = 0 from rfl, map_zero]
    refine (Multiset.sum_eq_zero fun x hx => ?_).symm
    obtain ⟨r, hr, rfl⟩ := Multiset.mem_map.mp hx
    simp
  | tmul x a =>
    apply valLinEquiv.injective
    rw [adjointTransport_mk_tmul, map_multiset_sum, Multiset.map_map, valLinEquiv_apply,
      show ((⟨x ⊗ₜ[ℝ] IsGaugeField.adjointCoeff (U * V) p a⟩ : GaugeBoson)).val
        = x ⊗ₜ[ℝ] IsGaugeField.adjointCoeff (U * V) p a from rfl,
      IsGaugeField.adjointCoeff_mul, Multiset.sum_linearMap_apply, Multiset.map_map,
      Multiset.tmul_sum, Multiset.map_map]
    refine congrArg Multiset.sum (Multiset.map_congr rfl fun r hr => ?_)
    simp only [Function.comp_apply, LinearMap.comp_apply, adjointTransport_mk_tmul,
      valLinEquiv_apply]
  | add m₁ m₂ h₁ h₂ =>
    rw [show (⟨m₁ + m₂⟩ : GaugeBoson) = (⟨m₁⟩ : GaugeBoson) + ⟨m₂⟩ from rfl, map_add, h₁,
      h₂, ← Multiset.sum_map_add]
    refine congrArg Multiset.sum (Multiset.map_congr rfl fun r hr => ?_)
    simp only [Function.comp_apply]
    exact (map_add _ _ _).symm

/-- The dual transport carries a component covector to the component covector of the
  transported adjoint index: the spacetime slot is untouched. -/
lemma dualMap_adjointTransport_componentDual (U : JetGaugeGroupI)
    (p : Multiset (Fin 1 ⊕ Fin 3)) (ω : Module.Dual ℝ Lorentz.CoVector)
    (φ : Module.Dual ℝ GaugeAlgebra) :
    (adjointTransport U p).dualMap (componentDual ω φ)
      = componentDual ω (φ ∘ₗ IsGaugeField.adjointCoeff U p) := by
  refine LinearMap.ext fun v => ?_
  obtain ⟨m⟩ := v
  induction m using TensorProduct.induction_on with
  | zero =>
    rw [show (⟨0⟩ : GaugeBoson) = 0 from rfl, map_zero, map_zero]
  | tmul x a =>
    rw [LinearMap.dualMap_apply, adjointTransport_mk_tmul,
      componentDual_apply_val_tmul, componentDual_apply_val_tmul]
    rfl
  | add m₁ m₂ h₁ h₂ =>
    rw [show (⟨m₁ + m₂⟩ : GaugeBoson) = (⟨m₁⟩ : GaugeBoson) + ⟨m₂⟩ from rfl, map_add,
      map_add, h₁, h₂]

end GaugeBoson

namespace GaugeJetAlgebra

/-- The value of the transport on the derivative symbol at `s`: the all-orders Leibniz
  convolution of the dual adjoint transports against lower derivative symbols. -/
noncomputable def transportFun (U : JetGaugeGroupI) (s : Multiset (Fin 1 ⊕ Fin 3)) :
    Module.Dual ℝ GaugeBoson →ₗ[ℝ] GaugeBoson.JetComponentSpace :=
  (s.antidiagonal.map fun p =>
    (TensorProduct.mk ℝ DerivAlgebraReal (Module.Dual ℝ GaugeBoson)
        (LagrangianTheory.dualRealJetAlgebraBasis p.2)).comp
      ((GaugeBoson.adjointTransport U p.1).dualMap)).sum

/-- **The linear part of the gauge action on the jet component space**: on a component
  function `∂_s A^ψ` it is the all-orders Leibniz convolution of the Taylor coefficients
  of the adjoint action of `U` against the lower component functions. -/
noncomputable def transport (U : JetGaugeGroupI) :
    GaugeBoson.JetComponentSpace →ₗ[ℝ] GaugeBoson.JetComponentSpace :=
  TensorProduct.lift (LagrangianTheory.dualRealJetAlgebraBasis.constr ℝ (transportFun U))

lemma transport_basis_tmul (U : JetGaugeGroupI) (s : Multiset (Fin 1 ⊕ Fin 3))
    (ψ : Module.Dual ℝ GaugeBoson) :
    transport U (LagrangianTheory.dualRealJetAlgebraBasis s ⊗ₜ[ℝ] ψ)
      = (s.antidiagonal.map fun p =>
          LagrangianTheory.dualRealJetAlgebraBasis p.2 ⊗ₜ[ℝ]
            (GaugeBoson.adjointTransport U p.1).dualMap ψ).sum := by
  rw [transport, TensorProduct.lift.tmul, Module.Basis.constr_basis, transportFun,
    Multiset.sum_linearMap_apply, Multiset.map_map]
  rfl

/-- Two maps out of the jet component space agree if they agree on the components
  `∂_s A^ψ` with `s` a derivative multiset and `ψ` an arbitrary covector. -/
lemma _root_.StandardModel.GaugeBoson.JetComponentSpace.ext_of_basis
    {M : Type*} [AddCommMonoid M] [Module ℝ M]
    {F G : GaugeBoson.JetComponentSpace →ₗ[ℝ] M}
    (h : ∀ (s : Multiset (Fin 1 ⊕ Fin 3)) (ψ : Module.Dual ℝ GaugeBoson),
      F (LagrangianTheory.dualRealJetAlgebraBasis s ⊗ₜ[ℝ] ψ)
        = G (LagrangianTheory.dualRealJetAlgebraBasis s ⊗ₜ[ℝ] ψ)) : F = G := by
  refine LinearMap.ext fun x => ?_
  induction x using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | add a b ha hb => rw [map_add, map_add, ha, hb]
  | tmul a ψ =>
    have ha : a ∈ Submodule.span ℝ
        (Set.range LagrangianTheory.dualRealJetAlgebraBasis) := by
      rw [LagrangianTheory.dualRealJetAlgebraBasis.span_eq]; trivial
    induction ha using Submodule.span_induction with
    | mem b hb => obtain ⟨s, rfl⟩ := hb; exact h s ψ
    | zero => rw [TensorProduct.zero_tmul, map_zero, map_zero]
    | add b c _ _ hb hc => rw [TensorProduct.add_tmul, map_add, map_add, hb, hc]
    | smul c b _ hb => rw [← TensorProduct.smul_tmul', map_smul, map_smul, hb]

/-- The transport of the identity is the identity. -/
lemma transport_one : transport (1 : JetGaugeGroupI) = LinearMap.id := by
  refine GaugeBoson.JetComponentSpace.ext_of_basis fun s ψ => ?_
  rw [transport_basis_tmul,
    Multiset.map_congr rfl (fun p hp => by rw [GaugeBoson.adjointTransport_one]),
    Multiset.sum_antidiagonal_eq_of_fst_ne_zero s
      (fun p => LagrangianTheory.dualRealJetAlgebraBasis p.2 ⊗ₜ[ℝ]
        ((if p.1 = 0 then LinearMap.id else 0) :
          GaugeBoson →ₗ[ℝ] GaugeBoson).dualMap ψ)
      (fun p hp => by
        rw [if_neg hp, show ((0 : GaugeBoson →ₗ[ℝ] GaugeBoson)).dualMap ψ = 0 from
            LinearMap.ext fun v => by simp, TensorProduct.tmul_zero]),
    if_pos rfl, LinearMap.id_apply,
    show (LinearMap.id : GaugeBoson →ₗ[ℝ] GaugeBoson).dualMap ψ = ψ from
      LinearMap.ext fun v => rfl]

/-- **The transport is an anti-homomorphism**: the transport of a product is the reverse
  composite. Composed with the inverse, it becomes the linear part of the gauge
  representation. -/
lemma transport_mul (U V : JetGaugeGroupI) :
    transport (U * V) = transport V ∘ₗ transport U := by
  refine GaugeBoson.JetComponentSpace.ext_of_basis fun s ψ => ?_
  have hdual : ∀ (p : Multiset (Fin 1 ⊕ Fin 3) × Multiset (Fin 1 ⊕ Fin 3)),
      (GaugeBoson.adjointTransport (U * V) p.1).dualMap ψ
        = (p.1.antidiagonal.map fun r =>
            (GaugeBoson.adjointTransport V r.2).dualMap
              ((GaugeBoson.adjointTransport U r.1).dualMap ψ)).sum := by
    intro p
    rw [GaugeBoson.adjointTransport_mul]
    refine LinearMap.ext fun v => ?_
    rw [LinearMap.dualMap_apply, Multiset.sum_linearMap_apply, Multiset.map_map,
      map_multiset_sum, Multiset.map_map, Multiset.sum_linearMap_apply, Multiset.map_map]
    rfl
  have hLHS : transport (U * V) (LagrangianTheory.dualRealJetAlgebraBasis s ⊗ₜ[ℝ] ψ)
      = (s.antidiagonal.map fun p =>
          (p.1.antidiagonal.map fun q =>
            LagrangianTheory.dualRealJetAlgebraBasis p.2 ⊗ₜ[ℝ]
              (GaugeBoson.adjointTransport V q.2).dualMap
                ((GaugeBoson.adjointTransport U q.1).dualMap ψ)).sum).sum := by
    rw [transport_basis_tmul]
    refine congrArg Multiset.sum (Multiset.map_congr rfl fun p hp => ?_)
    rw [hdual p, Multiset.tmul_sum, Multiset.map_map]
    exact congrArg Multiset.sum (Multiset.map_congr rfl fun q hq => rfl)
  have hRHS : (transport V ∘ₗ transport U)
        (LagrangianTheory.dualRealJetAlgebraBasis s ⊗ₜ[ℝ] ψ)
      = (s.antidiagonal.map fun p =>
          (p.2.antidiagonal.map fun q =>
            LagrangianTheory.dualRealJetAlgebraBasis q.2 ⊗ₜ[ℝ]
              (GaugeBoson.adjointTransport V q.1).dualMap
                ((GaugeBoson.adjointTransport U p.1).dualMap ψ)).sum).sum := by
    rw [LinearMap.comp_apply, transport_basis_tmul, map_multiset_sum, Multiset.map_map]
    refine congrArg Multiset.sum (Multiset.map_congr rfl fun p hp => ?_)
    exact transport_basis_tmul V p.2 _
  rw [hLHS, hRHS]
  exact Multiset.sum_antidiagonal_assoc s fun a b c =>
    LagrangianTheory.dualRealJetAlgebraBasis c ⊗ₜ[ℝ]
      (GaugeBoson.adjointTransport V b).dualMap
        ((GaugeBoson.adjointTransport U a).dualMap ψ)

end GaugeJetAlgebra

/-!

## D. The Maurer–Cartan shift

-/

namespace GaugeJetAlgebra

/-- The Taylor coefficient of the Maurer–Cartan form of `U` at the derivative multiset
  `s`, packaged as a gauge boson: the spacetime index runs over the coordinate
  directions, the adjoint index over the base-point Taylor coefficients of the
  Maurer–Cartan form. -/
noncomputable def mcBosonCoeff (U : JetGaugeGroupI) (s : Multiset (Fin 1 ⊕ Fin 3)) :
    GaugeBoson :=
  ⟨∑ μ, Lorentz.CoVector.basis μ ⊗ₜ[ℝ]
    JetGaugeAlgebra.eval (JetGaugeAlgebra.iteratedDeriv s (maurerCartanForm U μ))⟩

@[simp]
lemma mcBosonCoeff_one (s : Multiset (Fin 1 ⊕ Fin 3)) : mcBosonCoeff 1 s = 0 := by
  rw [show (0 : GaugeBoson) = ⟨0⟩ from rfl, mcBosonCoeff]
  congr 1
  refine Finset.sum_eq_zero fun μ _ => ?_
  rw [show maurerCartanForm 1 μ = 0 from congrFun maurerCartanForm_one μ, map_zero,
    map_zero, TensorProduct.tmul_zero]

/-- The Maurer–Cartan Taylor coefficients of a product: the cocycle identity, with the
  adjoint transport convoluted in by the Taylor–Leibniz theorem. -/
lemma mcBosonCoeff_mul (U V : JetGaugeGroupI) (s : Multiset (Fin 1 ⊕ Fin 3)) :
    mcBosonCoeff (U * V) s
      = mcBosonCoeff U s
        + (s.antidiagonal.map fun p =>
            GaugeBoson.adjointTransport U p.1 (mcBosonCoeff V p.2)).sum := by
  apply GaugeBoson.valLinEquiv.injective
  have hE : ∀ (W : JetGaugeGroupI) (t : Multiset (Fin 1 ⊕ Fin 3)),
      GaugeBoson.valLinEquiv (mcBosonCoeff W t)
        = ∑ μ, Lorentz.CoVector.basis μ ⊗ₜ[ℝ]
            JetGaugeAlgebra.eval (JetGaugeAlgebra.iteratedDeriv t
              (maurerCartanForm W μ)) := fun W t => rfl
  have hB : ∀ p q : Multiset (Fin 1 ⊕ Fin 3),
      GaugeBoson.valLinEquiv (GaugeBoson.adjointTransport U p (mcBosonCoeff V q))
        = ∑ μ, Lorentz.CoVector.basis μ ⊗ₜ[ℝ]
            IsGaugeField.adjointCoeff U p (JetGaugeAlgebra.eval
              (JetGaugeAlgebra.iteratedDeriv q (maurerCartanForm V μ))) := by
    intro p q
    rw [show GaugeBoson.valLinEquiv (GaugeBoson.adjointTransport U p (mcBosonCoeff V q))
        = TensorProduct.map LinearMap.id (IsGaugeField.adjointCoeff U p)
            (GaugeBoson.valLinEquiv (mcBosonCoeff V q)) from by
        rw [GaugeBoson.adjointTransport]
        simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
          LinearEquiv.apply_symm_apply],
      hE, map_sum]
    exact Finset.sum_congr rfl fun μ _ => by
      rw [TensorProduct.map_tmul, LinearMap.id_apply]
  have hA : GaugeBoson.valLinEquiv (mcBosonCoeff (U * V) s)
      = ∑ μ, (Lorentz.CoVector.basis μ ⊗ₜ[ℝ]
          JetGaugeAlgebra.eval (JetGaugeAlgebra.iteratedDeriv s (maurerCartanForm U μ))
        + (s.antidiagonal.map fun p =>
            Lorentz.CoVector.basis μ ⊗ₜ[ℝ]
              IsGaugeField.adjointCoeff U p.1 (JetGaugeAlgebra.eval
                (JetGaugeAlgebra.iteratedDeriv p.2 (maurerCartanForm V μ)))).sum) := by
    rw [hE]
    refine Finset.sum_congr rfl fun μ _ => ?_
    rw [show maurerCartanForm (U * V) μ
        = maurerCartanForm U μ + JetGaugeAlgebra.adjoint U (maurerCartanForm V μ) from
        maurerCartanForm_cocycle U V μ,
      map_add, map_add,
      show JetGaugeAlgebra.adjoint U (maurerCartanForm V μ)
        = JetGaugeAlgebra.adjointMap U (maurerCartanForm V μ) from rfl,
      JetGaugeAlgebra.eval_iteratedDeriv_adjointMap, TensorProduct.tmul_add,
      Multiset.tmul_sum, Multiset.map_map]
    exact congrArg (fun z => _ + z)
      (congrArg Multiset.sum (Multiset.map_congr rfl fun p hp => rfl))
  rw [hA, Finset.sum_add_distrib, map_add, map_multiset_sum, Multiset.map_map, ← hE,
    ← Multiset.sum_map_finsetSum]
  congr 1

/-- **The Maurer–Cartan shift**: the linear functional on the component space pairing a
  component `∂_s A^ψ` with the Taylor coefficient of the Maurer–Cartan form of `U`. It is
  the constant part of the affine gauge action. -/
noncomputable def mcShift (U : JetGaugeGroupI) : GaugeBoson.JetComponentSpace →ₗ[ℝ] ℝ :=
  TensorProduct.lift (LagrangianTheory.dualRealJetAlgebraBasis.constr ℝ fun s =>
    Module.Dual.eval ℝ GaugeBoson (mcBosonCoeff U s))

lemma mcShift_basis_tmul (U : JetGaugeGroupI) (s : Multiset (Fin 1 ⊕ Fin 3))
    (ψ : Module.Dual ℝ GaugeBoson) :
    mcShift U (LagrangianTheory.dualRealJetAlgebraBasis s ⊗ₜ[ℝ] ψ)
      = ψ (mcBosonCoeff U s) := by
  rw [mcShift, TensorProduct.lift.tmul, Module.Basis.constr_basis]
  rfl

@[simp]
lemma mcShift_one : mcShift (1 : JetGaugeGroupI) = 0 := by
  refine GaugeBoson.JetComponentSpace.ext_of_basis fun s ψ => ?_
  rw [mcShift_basis_tmul, mcBosonCoeff_one, map_zero, LinearMap.zero_apply]

/-- **The cocycle identity for the Maurer–Cartan shift.** -/
lemma mcShift_mul (U V : JetGaugeGroupI) :
    mcShift (U * V) = mcShift V ∘ₗ transport U + mcShift U := by
  refine GaugeBoson.JetComponentSpace.ext_of_basis fun s ψ => ?_
  rw [LinearMap.add_apply, LinearMap.comp_apply, mcShift_basis_tmul, mcBosonCoeff_mul,
    map_add, add_comm]
  congr 1
  · rw [map_multiset_sum, Multiset.map_map, transport_basis_tmul, map_multiset_sum,
      Multiset.map_map]
    refine congrArg Multiset.sum (Multiset.map_congr rfl fun p hp => ?_)
    rw [Function.comp_apply, Function.comp_apply, mcShift_basis_tmul]
    rfl
  · exact (mcShift_basis_tmul U s ψ).symm

/-!

## E. The action of the jet gauge group

-/

/-- The affine action of a jet of gauge transformations on the generators of the jet
  algebra: the transported component plus the Maurer–Cartan shift, both of `U⁻¹` — the
  contragredient convention for an action on component functions. -/
noncomputable def gaugeGen (U : JetGaugeGroupI) :
    GaugeBoson.JetComponentSpace →ₗ[ℝ] GaugeJetAlgebra :=
  (SymmetricAlgebra.ι ℝ GaugeBoson.JetComponentSpace).comp (transport U⁻¹)
    + (Algebra.linearMap ℝ GaugeJetAlgebra).comp (mcShift U⁻¹)

lemma gaugeGen_apply (U : JetGaugeGroupI) (x : GaugeBoson.JetComponentSpace) :
    gaugeGen U x = SymmetricAlgebra.ι ℝ _ (transport U⁻¹ x)
      + algebraMap ℝ GaugeJetAlgebra (mcShift U⁻¹ x) := rfl

/-- **The action of the jet gauge group on the gauge-boson jet algebra**: the substitution
  homomorphism determined by the affine action on the generators, `∂_s A^ψ` going to its
  transported convolution plus the Maurer–Cartan shift of `U⁻¹`. -/
noncomputable def repJetGaugeGroupI : Representation ℝ JetGaugeGroupI GaugeJetAlgebra where
  toFun U := (SymmetricAlgebra.lift (gaugeGen U)).toLinearMap
  map_one' := by
    suffices h : SymmetricAlgebra.lift (gaugeGen 1) = AlgHom.id ℝ GaugeJetAlgebra by
      rw [h]; rfl
    refine SymmetricAlgebra.algHom_ext (LinearMap.ext fun x => ?_)
    show SymmetricAlgebra.lift (gaugeGen 1) (SymmetricAlgebra.ι ℝ _ x)
      = AlgHom.id ℝ GaugeJetAlgebra (SymmetricAlgebra.ι ℝ _ x)
    rw [SymmetricAlgebra.lift_ι_apply, gaugeGen_apply, inv_one, transport_one,
      mcShift_one, LinearMap.id_apply, LinearMap.zero_apply, map_zero, add_zero]
    rfl
  map_mul' U V := by
    suffices h : SymmetricAlgebra.lift (gaugeGen (U * V))
        = (SymmetricAlgebra.lift (gaugeGen U)).comp (SymmetricAlgebra.lift (gaugeGen V)) by
      rw [h]; rfl
    refine SymmetricAlgebra.algHom_ext (LinearMap.ext fun x => ?_)
    show SymmetricAlgebra.lift (gaugeGen (U * V)) (SymmetricAlgebra.ι ℝ _ x)
      = ((SymmetricAlgebra.lift (gaugeGen U)).comp (SymmetricAlgebra.lift (gaugeGen V)))
          (SymmetricAlgebra.ι ℝ _ x)
    rw [SymmetricAlgebra.lift_ι_apply, gaugeGen_apply, AlgHom.comp_apply,
      SymmetricAlgebra.lift_ι_apply, gaugeGen_apply, map_add,
      SymmetricAlgebra.lift_ι_apply, gaugeGen_apply, AlgHom.commutes,
      mul_inv_rev, transport_mul, mcShift_mul, LinearMap.comp_apply,
      LinearMap.add_apply, LinearMap.comp_apply, map_add, add_assoc]

/-- The action of `U` as an algebra homomorphism: a jet of gauge transformations acts on
  a Lagrangian term factor by factor. -/
noncomputable def repJetGaugeGroupIAlgHom (U : JetGaugeGroupI) :
    GaugeJetAlgebra →ₐ[ℝ] GaugeJetAlgebra :=
  SymmetricAlgebra.lift (gaugeGen U)

@[simp]
lemma repJetGaugeGroupI_ι (U : JetGaugeGroupI) (x : GaugeBoson.JetComponentSpace) :
    repJetGaugeGroupI U (SymmetricAlgebra.ι ℝ _ x)
      = SymmetricAlgebra.ι ℝ _ (transport U⁻¹ x)
        + algebraMap ℝ GaugeJetAlgebra (mcShift U⁻¹ x) := by
  rw [show repJetGaugeGroupI U (SymmetricAlgebra.ι ℝ _ x)
      = SymmetricAlgebra.lift (gaugeGen U) (SymmetricAlgebra.ι ℝ _ x) from rfl,
    SymmetricAlgebra.lift_ι_apply, gaugeGen_apply]

@[simp]
lemma repJetGaugeGroupI_apply_one (U : JetGaugeGroupI) :
    repJetGaugeGroupI U (1 : GaugeJetAlgebra) = 1 := by
  rw [show repJetGaugeGroupI U (1 : GaugeJetAlgebra)
    = SymmetricAlgebra.lift (gaugeGen U) 1 from rfl, map_one]

lemma repJetGaugeGroupI_apply_mul (U : JetGaugeGroupI) (x y : GaugeJetAlgebra) :
    repJetGaugeGroupI U (x * y) = repJetGaugeGroupI U x * repJetGaugeGroupI U y := by
  rw [show repJetGaugeGroupI U (x * y)
    = SymmetricAlgebra.lift (gaugeGen U) (x * y) from rfl, map_mul]
  rfl

@[simp]
lemma repJetGaugeGroupI_algebraMap (U : JetGaugeGroupI) (r : ℝ) :
    repJetGaugeGroupI U (algebraMap ℝ GaugeJetAlgebra r)
      = algebraMap ℝ GaugeJetAlgebra r := by
  rw [show repJetGaugeGroupI U (algebraMap ℝ GaugeJetAlgebra r)
    = SymmetricAlgebra.lift (gaugeGen U) (algebraMap ℝ GaugeJetAlgebra r) from rfl,
    AlgHom.commutes]

/-!

### E.1. The transformation law of the generators

-/

/-- The component covector at `μ` picks the `μ`-th Maurer–Cartan Taylor coefficient out
  of the shift. -/
lemma componentDual_dualBasis_mcBosonCoeff (W : JetGaugeGroupI)
    (s : Multiset (Fin 1 ⊕ Fin 3)) (μ : Fin 1 ⊕ Fin 3) (φ : Module.Dual ℝ GaugeAlgebra) :
    GaugeBoson.componentDual (Lorentz.CoVector.basis.dualBasis μ) φ (mcBosonCoeff W s)
      = φ (JetGaugeAlgebra.eval (JetGaugeAlgebra.iteratedDeriv s
          (maurerCartanForm W μ))) := by
  have hsum : mcBosonCoeff W s
      = ∑ ν, (⟨Lorentz.CoVector.basis ν ⊗ₜ[ℝ]
          JetGaugeAlgebra.eval (JetGaugeAlgebra.iteratedDeriv s
            (maurerCartanForm W ν))⟩ : GaugeBoson) := by
    apply GaugeBoson.valLinEquiv.injective
    rw [map_sum]
    rfl
  rw [hsum, map_sum]
  rw [Finset.sum_congr rfl fun ν _ => GaugeBoson.componentDual_apply_val_tmul _ _ _ _]
  rw [Finset.sum_congr rfl fun ν _ => by
    rw [Module.Basis.dualBasis_apply_self, ite_mul, one_mul, zero_mul]]
  rw [Finset.sum_ite_eq' Finset.univ μ
    (fun ν => φ (JetGaugeAlgebra.eval (JetGaugeAlgebra.iteratedDeriv s
      (maurerCartanForm W ν)))), if_pos (Finset.mem_univ μ)]

/-- **The transformation law of the derivative generators**, in the form used by
  `IsGaugeField`: a jet of gauge transformations acts on `∂_s A_μ^φ` by the all-orders
  Leibniz convolution of the adjoint Taylor coefficients of `U⁻¹` against lower
  generators, plus the Taylor coefficient of the Maurer–Cartan form of `U⁻¹`. -/
theorem repJetGaugeGroupI_iteratedJetDeriv_ofA (U : JetGaugeGroupI)
    (s : Multiset (Fin 1 ⊕ Fin 3)) (μ : Fin 1 ⊕ Fin 3) (φ : Module.Dual ℝ GaugeAlgebra) :
    repJetGaugeGroupI U (iteratedJetDeriv s (ofA μ φ))
      = (s.antidiagonal.map fun p =>
          iteratedJetDeriv p.2 (ofA μ (adjointDualCoeff U⁻¹ p.1 φ))).sum
        + algebraMap ℝ GaugeJetAlgebra
            (φ (JetGaugeAlgebra.eval (JetGaugeAlgebra.iteratedDeriv s
              (maurerCartanForm U⁻¹ μ)))) := by
  rw [iteratedJetDeriv_ofA, repJetGaugeGroupI_ι, transport_basis_tmul, mcShift_basis_tmul,
    componentDual_dualBasis_mcBosonCoeff, map_multiset_sum, Multiset.map_map]
  congr 1
  refine congrArg Multiset.sum (Multiset.map_congr rfl fun p hp => ?_)
  rw [Function.comp_apply, GaugeBoson.dualMap_adjointTransport_componentDual,
    iteratedJetDeriv_ofA]
  rfl

/-!

### E.2. The complexified action

-/

/-- The action of the jet gauge group on the complexified gauge-boson jet algebra, by
  base change. -/
noncomputable def complexRepJetGaugeGroupI :
    Representation ℂ JetGaugeGroupI (ℂ ⊗[ℝ] GaugeJetAlgebra) where
  toFun U := LinearMap.baseChange ℂ (repJetGaugeGroupI U)
  map_one' := by
    rw [map_one, Module.End.one_eq_id, LinearMap.baseChange_id, Module.End.one_eq_id]
  map_mul' U V := by
    rw [map_mul, Module.End.mul_eq_comp, LinearMap.baseChange_comp, Module.End.mul_eq_comp]

@[simp]
lemma complexRepJetGaugeGroupI_tmul (U : JetGaugeGroupI) (z : ℂ) (x : GaugeJetAlgebra) :
    complexRepJetGaugeGroupI U (z ⊗ₜ[ℝ] x) = z ⊗ₜ[ℝ] repJetGaugeGroupI U x := rfl

lemma complexRepJetGaugeGroupI_apply_mul (U : JetGaugeGroupI)
    (x y : ℂ ⊗[ℝ] GaugeJetAlgebra) :
    complexRepJetGaugeGroupI U (x * y)
      = complexRepJetGaugeGroupI U x * complexRepJetGaugeGroupI U y := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x₁ x₂ h₁ h₂ => rw [add_mul, map_add, map_add, h₁, h₂, add_mul]
  | tmul z₁ a₁ =>
    induction y using TensorProduct.induction_on with
    | zero => simp
    | add y₁ y₂ h₁ h₂ => rw [mul_add, map_add, map_add, h₁, h₂, mul_add]
    | tmul z₂ a₂ =>
      rw [Algebra.TensorProduct.tmul_mul_tmul, complexRepJetGaugeGroupI_tmul,
        complexRepJetGaugeGroupI_tmul, complexRepJetGaugeGroupI_tmul,
        repJetGaugeGroupI_apply_mul, Algebra.TensorProduct.tmul_mul_tmul]

/-- The iterated complexified derivative of a real element is the complexification of the
  iterated real derivative. -/
lemma iteratedD_complexJetDeriv_one_tmul (s : Multiset (Fin 1 ⊕ Fin 3))
    (x : GaugeJetAlgebra) :
    Lorentz.iteratedD complexJetDeriv complexJetDeriv_comm s ((1 : ℂ) ⊗ₜ[ℝ] x)
      = (1 : ℂ) ⊗ₜ[ℝ] iteratedJetDeriv s x := by
  induction s using Multiset.induction_on generalizing x with
  | empty => rw [Lorentz.iteratedD_zero, iteratedJetDeriv_zero]; rfl
  | cons μ s ih =>
    rw [Lorentz.iteratedD_cons, LinearMap.comp_apply, ih, complexJetDeriv_tmul,
      iteratedJetDeriv_cons, LinearMap.comp_apply]

/-- A real scalar in the complexified jet algebra is the corresponding complex scalar. -/
lemma one_tmul_algebraMap (r : ℝ) :
    (1 : ℂ) ⊗ₜ[ℝ] (algebraMap ℝ GaugeJetAlgebra r)
      = algebraMap ℂ (ℂ ⊗[ℝ] GaugeJetAlgebra) ((r : ℝ) : ℂ) := by
  rw [Algebra.algebraMap_eq_smul_one, TensorProduct.tmul_smul,
    Algebra.algebraMap_eq_smul_one,
    show ((r : ℝ) • ((1 : ℂ) ⊗ₜ[ℝ] (1 : GaugeJetAlgebra)))
      = (((r : ℝ) : ℂ)) • ((1 : ℂ) ⊗ₜ[ℝ] (1 : GaugeJetAlgebra)) from
      (algebraMap_smul ℂ r _).symm, Algebra.TensorProduct.one_def]

/-- **The transformation law of the derivative generators on the complexification**: the
  form consumed by the `IsGaugeField` structure of the ambient Lagrangian theory. -/
theorem complexRepJetGaugeGroupI_iteratedD_one_tmul_ofA (U : JetGaugeGroupI)
    (s : Multiset (Fin 1 ⊕ Fin 3)) (μ : Fin 1 ⊕ Fin 3) (φ : Module.Dual ℝ GaugeAlgebra) :
    complexRepJetGaugeGroupI U (Lorentz.iteratedD complexJetDeriv complexJetDeriv_comm s
        ((1 : ℂ) ⊗ₜ[ℝ] ofA μ φ))
      = (s.antidiagonal.map fun p =>
          Lorentz.iteratedD complexJetDeriv complexJetDeriv_comm p.2
            ((1 : ℂ) ⊗ₜ[ℝ] ofA μ (adjointDualCoeff U⁻¹ p.1 φ))).sum
        + algebraMap ℂ (ℂ ⊗[ℝ] GaugeJetAlgebra)
            (((φ (JetGaugeAlgebra.eval (JetGaugeAlgebra.iteratedDeriv s
              (maurerCartanForm U⁻¹ μ))) : ℝ)) : ℂ) := by
  rw [iteratedD_complexJetDeriv_one_tmul, complexRepJetGaugeGroupI_tmul,
    repJetGaugeGroupI_iteratedJetDeriv_ofA, TensorProduct.tmul_add, Multiset.tmul_sum,
    Multiset.map_map, one_tmul_algebraMap]
  congr 1
  exact congrArg Multiset.sum (Multiset.map_congr rfl fun p hp => by
    rw [Function.comp_apply, iteratedD_complexJetDeriv_one_tmul])

end GaugeJetAlgebra

end StandardModel
