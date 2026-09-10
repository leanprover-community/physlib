/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Particles.StandardModel.Matter.BosonicAlgebra.MassDim
/-!
# The mass-weight polynomial on the bosonic algebra

## i. Overview

The mass-weight scaling of `Physlib.Particles.StandardModel.Matter.BosonicAlgebra.MassDim`
records the mass dimension of a homogeneous element in a scalar. Replacing that scalar by a
formal variable turns the scaling into a grading: `massWeightPoly w` is the algebra map
sending a generator `∂_s ψ_φ` of a field of mass weight `w` to `X ^ (w + 2 |s|)` times
itself, so the coefficient of `X ^ n` in `massWeightPoly w a` is the part of `a` of mass
weight `n`.

The target `Polynomial (BosonicAlgebra V)` is commutative, so the universal property of the
symmetric algebra applies with no side condition: the grading is the lift of a single linear
map on the jet component space. That map is assembled from the two halves of the component
space, and on each half from the multiset basis of the derivative symbols, which is where
the exponent `w + 2 |s|` is read off.

## ii. Key results

- `BosonicAlgebra.massWeightPoly` : the mass-weight polynomial grading.
- `BosonicAlgebra.massWeightPoly_iteratedJetDeriv_ofField` : `∂_s ψ_φ` is a monomial
  eigenvector of weight `w + 2 |s|`.
- `BosonicAlgebra.massWeightPoly_iteratedJetDeriv_ofConjField` : the same for the conjugate
  field.
- `BosonicAlgebra.massWeightPoly_eval_one` : setting the variable to one recovers the
  element.

## iii. Table of contents

- A. The mass-weight polynomial of a component function
- B. The mass-weight polynomial on the bosonic algebra
- C. The mass weight of the field and its derivatives
- D. Recovering an element from its mass-weight polynomial

-/

@[expose] public section

namespace StandardModel

namespace BosonicAlgebra

open TensorProduct

variable {V : Type} [AddCommGroup V] [Module ℂ V]

/-!

## A. The mass-weight polynomial of a component function

-/

/-- The monomial map into polynomials over the bosonic algebra, as a map of `ℂ`-modules
  rather than of `BosonicAlgebra V`-modules. -/
noncomputable def monomialₗ (n : ℕ) :
    BosonicAlgebra V →ₗ[ℂ] Polynomial (BosonicAlgebra V) :=
  (Polynomial.monomial n).restrictScalars ℂ

@[simp]
lemma monomialₗ_apply (n : ℕ) (x : BosonicAlgebra V) :
    monomialₗ n x = Polynomial.monomial n x := rfl

/-- One half of the mass-weight polynomial on the jet component space, for a field of mass
  weight `w`: the linear map sending the symbol `∂_s φ` to `X ^ (w + 2 |s|)` times its
  image under `k`. The two halves of the component space differ only in the inclusion `k`
  of the symbols into the bosonic algebra, so both are instances of this map. -/
noncomputable def halfPoly {W : Type} [AddCommGroup W] [Module ℂ W] (w : ℕ)
    (k : DerivAlgebraComplex ⊗[ℂ] W →ₗ[ℂ] BosonicAlgebra V) :
    DerivAlgebraComplex ⊗[ℂ] W →ₗ[ℂ] Polynomial (BosonicAlgebra V) :=
  TensorProduct.lift (DerivAlgebraComplex.basis.constr ℂ fun s =>
    (monomialₗ (w + 2 * Multiset.card s)).comp
      (k.comp (TensorProduct.mk ℂ DerivAlgebraComplex W (DerivAlgebraComplex.basis s))))

/-- On the symbol `∂_s φ` the half mass-weight polynomial is the monomial of degree
  `w + 2 |s|`: the field contributes `w` and each derivative two. -/
lemma halfPoly_basis_tmul {W : Type} [AddCommGroup W] [Module ℂ W] (w : ℕ)
    (k : DerivAlgebraComplex ⊗[ℂ] W →ₗ[ℂ] BosonicAlgebra V)
    (s : Multiset (Fin 1 ⊕ Fin 3)) (x : W) :
    halfPoly w k (DerivAlgebraComplex.basis s ⊗ₜ[ℂ] x) =
      Polynomial.monomial (w + 2 * Multiset.card s)
        (k (DerivAlgebraComplex.basis s ⊗ₜ[ℂ] x)) := by
  rw [halfPoly, TensorProduct.lift.tmul, Module.Basis.constr_basis]
  rfl

/-- The inclusion of the unconjugated symbols into the bosonic algebra. -/
noncomputable def ιFst : DerivAlgebraComplex ⊗[ℂ] Module.Dual ℂ V →ₗ[ℂ] BosonicAlgebra V :=
  (SymmetricAlgebra.ι ℂ (JetComponentSpace V)).comp (LinearMap.inl ℂ _ _)

/-- The inclusion of the conjugate symbols into the bosonic algebra. -/
noncomputable def ιSnd :
    DerivAlgebraComplex ⊗[ℂ] Module.Dual ℂ (ConjModule V) →ₗ[ℂ] BosonicAlgebra V :=
  (SymmetricAlgebra.ι ℂ (JetComponentSpace V)).comp (LinearMap.inr ℂ _ _)

/-- The mass-weight polynomial of a component function of a field of mass weight `w`: the
  sum of the two half maps, one for the field and one for its conjugate. -/
noncomputable def jetComponentPoly (w : ℕ) :
    JetComponentSpace V →ₗ[ℂ] Polynomial (BosonicAlgebra V) :=
  (halfPoly w ιFst).comp (LinearMap.fst ℂ _ _) +
    (halfPoly w ιSnd).comp (LinearMap.snd ℂ _ _)

lemma jetComponentPoly_apply (w : ℕ) (x : JetComponentSpace V) :
    jetComponentPoly w x = halfPoly w ιFst x.1 + halfPoly w ιSnd x.2 := rfl

/-- On an unconjugated derivative monomial the component map is a monomial eigenvector. -/
@[simp]
lemma jetComponentPoly_inl (w : ℕ) (s : Multiset (Fin 1 ⊕ Fin 3)) (φ : Module.Dual ℂ V) :
    jetComponentPoly w ((DerivAlgebraComplex.basis s ⊗ₜ[ℂ] φ, 0) : JetComponentSpace V) =
      Polynomial.monomial (w + 2 * Multiset.card s)
        (SymmetricAlgebra.ι ℂ (JetComponentSpace V)
          ((DerivAlgebraComplex.basis s ⊗ₜ[ℂ] φ, 0) : JetComponentSpace V)) := by
  rw [jetComponentPoly_apply, halfPoly_basis_tmul, map_zero, add_zero]
  rfl

/-- On a conjugate derivative monomial the component map is a monomial eigenvector. -/
@[simp]
lemma jetComponentPoly_inr (w : ℕ) (s : Multiset (Fin 1 ⊕ Fin 3))
    (φ : Module.Dual ℂ (ConjModule V)) :
    jetComponentPoly w ((0, DerivAlgebraComplex.basis s ⊗ₜ[ℂ] φ) : JetComponentSpace V) =
      Polynomial.monomial (w + 2 * Multiset.card s)
        (SymmetricAlgebra.ι ℂ (JetComponentSpace V)
          ((0, DerivAlgebraComplex.basis s ⊗ₜ[ℂ] φ) : JetComponentSpace V)) := by
  rw [jetComponentPoly_apply, halfPoly_basis_tmul, map_zero, zero_add]
  rfl

/-!

## B. The mass-weight polynomial on the bosonic algebra

-/

/-- The mass-weight polynomial on the bosonic algebra of a field of mass weight `w`: the
  `ℂ`-algebra map sending a generator of mass weight `n` to `X ^ n` times itself. It is
  `BosonicAlgebra.massWeightScale` with the scalar replaced by the formal variable `X`, and
  needs no side condition because `Polynomial (BosonicAlgebra V)` is commutative. -/
noncomputable def massWeightPoly (w : ℕ) :
    BosonicAlgebra V →ₐ[ℂ] Polynomial (BosonicAlgebra V) :=
  SymmetricAlgebra.lift (jetComponentPoly w)

/-- On a component function the mass-weight polynomial is the component-function map. -/
@[simp]
lemma massWeightPoly_ι (w : ℕ) (x : JetComponentSpace V) :
    massWeightPoly w (SymmetricAlgebra.ι ℂ (JetComponentSpace V) x) =
      jetComponentPoly w x :=
  SymmetricAlgebra.lift_ι_apply _ x

/-!

## C. The mass weight of the field and its derivatives

-/

/-- The generator `∂_s ψ_φ` is a monomial eigenvector of mass weight `w + 2 |s|`: the field
  carries its own mass weight and each derivative adds two. -/
lemma massWeightPoly_iteratedJetDeriv_ofField (w : ℕ) (s : Multiset (Fin 1 ⊕ Fin 3))
    (φ : Module.Dual ℂ V) :
    massWeightPoly w (iteratedJetDeriv s (ofField φ)) =
      Polynomial.monomial (w + 2 * Multiset.card s) (iteratedJetDeriv s (ofField φ)) := by
  rw [iteratedJetDeriv_ofField, massWeightPoly_ι, jetComponentPoly_inl]

/-- The conjugate generator `∂_s ψ̄_φ` is a monomial eigenvector of the same mass weight
  `w + 2 |s|` as the generator it conjugates. -/
lemma massWeightPoly_iteratedJetDeriv_ofConjField (w : ℕ) (s : Multiset (Fin 1 ⊕ Fin 3))
    (φ : Module.Dual ℂ (ConjModule V)) :
    massWeightPoly w (iteratedJetDeriv s (ofConjField φ)) =
      Polynomial.monomial (w + 2 * Multiset.card s)
        (iteratedJetDeriv s (ofConjField φ)) := by
  rw [iteratedJetDeriv_ofConjField, massWeightPoly_ι, jetComponentPoly_inr]

/-- The undifferentiated field has mass weight `w`. -/
lemma massWeightPoly_ofField (w : ℕ) (φ : Module.Dual ℂ V) :
    massWeightPoly w (ofField φ) = Polynomial.monomial w (ofField φ) := by
  have h := massWeightPoly_iteratedJetDeriv_ofField w (0 : Multiset (Fin 1 ⊕ Fin 3)) φ
  rwa [iteratedJetDeriv_zero, LinearMap.id_apply, Multiset.card_zero, Nat.mul_zero,
    Nat.add_zero] at h

/-- The undifferentiated conjugate field has mass weight `w`. -/
lemma massWeightPoly_ofConjField (w : ℕ) (φ : Module.Dual ℂ (ConjModule V)) :
    massWeightPoly w (ofConjField φ) = Polynomial.monomial w (ofConjField φ) := by
  have h := massWeightPoly_iteratedJetDeriv_ofConjField w (0 : Multiset (Fin 1 ⊕ Fin 3)) φ
  rwa [iteratedJetDeriv_zero, LinearMap.id_apply, Multiset.card_zero, Nat.mul_zero,
    Nat.add_zero] at h

/-!

## D. Recovering an element from its mass-weight polynomial

-/

/-- Setting the formal variable to one collapses a half mass-weight polynomial back to the
  symbol it graded. The derivative monomials span, so it is enough to check this on the
  multiset basis. -/
lemma halfPoly_eval_one {W : Type} [AddCommGroup W] [Module ℂ W] (w : ℕ)
    (k : DerivAlgebraComplex ⊗[ℂ] W →ₗ[ℂ] BosonicAlgebra V)
    (y : DerivAlgebraComplex ⊗[ℂ] W) : (halfPoly w k y).eval 1 = k y := by
  induction y using TensorProduct.induction_on with
  | zero => rw [map_zero, Polynomial.eval_zero, map_zero]
  | add a b ha hb => rw [map_add, Polynomial.eval_add, ha, hb, map_add]
  | tmul a x =>
    have ha : a ∈ Submodule.span ℂ (Set.range DerivAlgebraComplex.basis) := by
      rw [DerivAlgebraComplex.basis.span_eq]
      trivial
    induction ha using Submodule.span_induction with
    | mem b hb =>
      obtain ⟨s, rfl⟩ := hb
      rw [halfPoly_basis_tmul, Polynomial.eval_monomial, one_pow, mul_one]
    | zero => rw [TensorProduct.zero_tmul, map_zero, Polynomial.eval_zero, map_zero]
    | add b c _ _ hb hc =>
      rw [TensorProduct.add_tmul, map_add, Polynomial.eval_add, hb, hc, map_add]
    | smul c b _ hb =>
      rw [← TensorProduct.smul_tmul', map_smul, Polynomial.eval_smul, hb, map_smul]

/-- Setting the formal variable to one recovers the component function. -/
lemma jetComponentPoly_eval_one (w : ℕ) (x : JetComponentSpace V) :
    (jetComponentPoly w x).eval 1 = SymmetricAlgebra.ι ℂ (JetComponentSpace V) x := by
  rw [jetComponentPoly_apply, Polynomial.eval_add, halfPoly_eval_one, halfPoly_eval_one,
    ιFst, ιSnd, LinearMap.comp_apply, LinearMap.comp_apply, ← map_add]
  congr 1
  exact Prod.ext (by simp) (by simp)

/-- Setting the formal variable to one recovers the original element: the mass-weight
  pieces of an element sum back to it. -/
lemma massWeightPoly_eval_one (w : ℕ) (a : BosonicAlgebra V) :
    (massWeightPoly w a).eval 1 = a := by
  have h : (Polynomial.eval₂AlgHom (AlgHom.id ℂ (BosonicAlgebra V)) 1
      fun b => Commute.one_right b).comp (massWeightPoly w) =
      AlgHom.id ℂ (BosonicAlgebra V) := by
    refine SymmetricAlgebra.algHom_ext (LinearMap.ext fun x => ?_)
    simp
    change Polynomial.eval₂ (RingHom.id _) 1 (jetComponentPoly w x) = _
    rw [Polynomial.eval₂_id]
    exact jetComponentPoly_eval_one w x
  exact AlgHom.congr_fun h a

/-- The mass-weight polynomial is injective: an element is recovered from its graded
  pieces. It is not surjective, since a monomial of the wrong degree is not the grading of
  anything. -/
lemma massWeightPoly_injective (w : ℕ) :
    Function.Injective (massWeightPoly (V := V) w) := by
  intro x y h
  rw [← massWeightPoly_eval_one w x, ← massWeightPoly_eval_one w y, h]

end BosonicAlgebra

end StandardModel
