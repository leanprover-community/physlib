/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Particles.StandardModel.Matter.FermionicAlgebra.MassDim
/-!
# The mass-weight polynomial on the fermionic algebra

## i. Overview

The mass-weight scaling of
`Physlib.Particles.StandardModel.Matter.FermionicAlgebra.MassDim` records the mass
dimension of a homogeneous element in a scalar. Replacing that scalar by a formal variable
turns the scaling into a grading: `massWeightPoly w` is the algebra map sending a generator
`∂_s ψ_φ` of a field of mass weight `w` to `X ^ (w + 2 |s|)` times itself, so the
coefficient of `X ^ n` in `massWeightPoly w a` is the part of `a` of mass weight `n`.

Unlike the bosonic case the target `Polynomial (FermionicAlgebra V)` is not commutative, so
the universal property of the exterior algebra comes with a side condition: the linear map
on the jet component space must square to zero. That is proved by the standard bilinear-form
argument — the symmetrised square vanishes, and two is invertible in `ℂ` — with the
symmetrised square checked on the derivative monomials, which span the component space.

## ii. Key results

- `FermionicAlgebra.massWeightPoly` : the mass-weight polynomial grading.
- `FermionicAlgebra.massWeightPoly_iteratedJetDeriv_ofField` : `∂_s ψ_φ` is a monomial
  eigenvector of weight `w + 2 |s|`.
- `FermionicAlgebra.massWeightPoly_iteratedJetDeriv_ofConjField` : the same for the
  conjugate field.
- `FermionicAlgebra.massWeightPoly_eval_one` : setting the variable to one recovers the
  element.

## iii. Table of contents

- A. The mass-weight polynomial of a component function
- B. The square-zero condition
- C. The mass-weight polynomial on the fermionic algebra
- D. The mass weight of the field and its derivatives
- E. Recovering an element from its mass-weight polynomial

-/

@[expose] public section

namespace StandardModel

namespace FermionicAlgebra

open TensorProduct

variable {V : Type} [AddCommGroup V] [Module ℂ V]

/-!

## A. The mass-weight polynomial of a component function

-/

/-- The monomial map into polynomials over the fermionic algebra, as a map of `ℂ`-modules
  rather than of `FermionicAlgebra V`-modules. -/
noncomputable def monomialₗ (n : ℕ) :
    FermionicAlgebra V →ₗ[ℂ] Polynomial (FermionicAlgebra V) :=
  (Polynomial.monomial n).restrictScalars ℂ

@[simp]
lemma monomialₗ_apply (n : ℕ) (x : FermionicAlgebra V) :
    monomialₗ n x = Polynomial.monomial n x := rfl

/-- One half of the mass-weight polynomial on the jet component space, for a field of mass
  weight `w`: the linear map sending the symbol `∂_s ψ` to `X ^ (w + 2 |s|)` times its image
  under `k`. The two halves of the component space differ only in the inclusion `k` of the
  symbols into the fermionic algebra, so both are instances of this map. -/
noncomputable def halfPoly {W : Type} [AddCommGroup W] [Module ℂ W] (w : ℕ)
    (k : DerivAlgebraComplex ⊗[ℂ] W →ₗ[ℂ] FermionicAlgebra V) :
    DerivAlgebraComplex ⊗[ℂ] W →ₗ[ℂ] Polynomial (FermionicAlgebra V) :=
  TensorProduct.lift (DerivAlgebraComplex.basis.constr ℂ fun s =>
    (monomialₗ (w + 2 * Multiset.card s)).comp
      (k.comp (TensorProduct.mk ℂ DerivAlgebraComplex W (DerivAlgebraComplex.basis s))))

/-- On the symbol `∂_s ψ` the half mass-weight polynomial is the monomial of degree
  `w + 2 |s|`: the field contributes `w` and each derivative two. -/
lemma halfPoly_basis_tmul {W : Type} [AddCommGroup W] [Module ℂ W] (w : ℕ)
    (k : DerivAlgebraComplex ⊗[ℂ] W →ₗ[ℂ] FermionicAlgebra V)
    (s : Multiset (Fin 1 ⊕ Fin 3)) (x : W) :
    halfPoly w k (DerivAlgebraComplex.basis s ⊗ₜ[ℂ] x) =
      Polynomial.monomial (w + 2 * Multiset.card s)
        (k (DerivAlgebraComplex.basis s ⊗ₜ[ℂ] x)) := by
  rw [halfPoly, TensorProduct.lift.tmul, Module.Basis.constr_basis]
  rfl

/-- The inclusion of the unconjugated symbols into the fermionic algebra. -/
noncomputable def ιFst : DerivAlgebraComplex ⊗[ℂ] Module.Dual ℂ V →ₗ[ℂ] FermionicAlgebra V :=
  (ExteriorAlgebra.ι ℂ).comp (LinearMap.inl ℂ _ _)

/-- The inclusion of the conjugate symbols into the fermionic algebra. -/
noncomputable def ιSnd :
    DerivAlgebraComplex ⊗[ℂ] Module.Dual ℂ (ConjModule V) →ₗ[ℂ] FermionicAlgebra V :=
  (ExteriorAlgebra.ι ℂ).comp (LinearMap.inr ℂ _ _)

/-- The mass-weight polynomial of a component function of a field of mass weight `w`: the
  sum of the two half maps, one for the field and one for its conjugate. -/
noncomputable def jetComponentPoly (w : ℕ) :
    JetComponentSpace V →ₗ[ℂ] Polynomial (FermionicAlgebra V) :=
  (halfPoly w ιFst).comp (LinearMap.fst ℂ _ _) +
    (halfPoly w ιSnd).comp (LinearMap.snd ℂ _ _)

lemma jetComponentPoly_apply (w : ℕ) (x : JetComponentSpace V) :
    jetComponentPoly w x = halfPoly w ιFst x.1 + halfPoly w ιSnd x.2 := rfl

/-- On an unconjugated derivative monomial the component map is a monomial eigenvector. -/
@[simp]
lemma jetComponentPoly_inl (w : ℕ) (s : Multiset (Fin 1 ⊕ Fin 3)) (φ : Module.Dual ℂ V) :
    jetComponentPoly w ((DerivAlgebraComplex.basis s ⊗ₜ[ℂ] φ, 0) : JetComponentSpace V) =
      Polynomial.monomial (w + 2 * Multiset.card s)
        (ExteriorAlgebra.ι ℂ
          ((DerivAlgebraComplex.basis s ⊗ₜ[ℂ] φ, 0) : JetComponentSpace V)) := by
  rw [jetComponentPoly_apply, halfPoly_basis_tmul, map_zero, add_zero]
  rfl

/-- On a conjugate derivative monomial the component map is a monomial eigenvector. -/
@[simp]
lemma jetComponentPoly_inr (w : ℕ) (s : Multiset (Fin 1 ⊕ Fin 3))
    (φ : Module.Dual ℂ (ConjModule V)) :
    jetComponentPoly w ((0, DerivAlgebraComplex.basis s ⊗ₜ[ℂ] φ) : JetComponentSpace V) =
      Polynomial.monomial (w + 2 * Multiset.card s)
        (ExteriorAlgebra.ι ℂ
          ((0, DerivAlgebraComplex.basis s ⊗ₜ[ℂ] φ) : JetComponentSpace V)) := by
  rw [jetComponentPoly_apply, halfPoly_basis_tmul, map_zero, zero_add]
  rfl

/-!

## B. The square-zero condition

-/

/-- The derivative monomials span a tensor product with the derivative algebra: this is the
  spanning set on which the square-zero condition is checked. -/
private lemma basisTmul_span_top {W : Type} [AddCommGroup W] [Module ℂ W] :
    Submodule.span ℂ (Set.range fun p : Multiset (Fin 1 ⊕ Fin 3) × W =>
      DerivAlgebraComplex.basis p.1 ⊗ₜ[ℂ] p.2) = ⊤ := by
  rw [eq_top_iff]
  rintro y -
  induction y using TensorProduct.induction_on with
  | zero => exact Submodule.zero_mem _
  | add a b ha hb => exact Submodule.add_mem _ ha hb
  | tmul a x =>
    have ha : a ∈ Submodule.span ℂ (Set.range DerivAlgebraComplex.basis) := by
      rw [DerivAlgebraComplex.basis.span_eq]
      trivial
    induction ha using Submodule.span_induction with
    | mem b hb =>
      obtain ⟨s, rfl⟩ := hb
      exact Submodule.subset_span ⟨(s, x), rfl⟩
    | zero => rw [TensorProduct.zero_tmul]; exact Submodule.zero_mem _
    | add b c _ _ hb hc => rw [TensorProduct.add_tmul]; exact Submodule.add_mem _ hb hc
    | smul c b _ hb => rw [← TensorProduct.smul_tmul']; exact Submodule.smul_mem _ c hb

/-- The set of derivative monomials in the jet component space: the unconjugated symbols
  `∂_s ψ_φ` together with the conjugate symbols `∂_s ψ̄_φ`. -/
def generators (V : Type) [AddCommGroup V] [Module ℂ V] : Set (JetComponentSpace V) :=
  (Set.range fun p : Multiset (Fin 1 ⊕ Fin 3) × Module.Dual ℂ V =>
      ((DerivAlgebraComplex.basis p.1 ⊗ₜ[ℂ] p.2, 0) : JetComponentSpace V)) ∪
    Set.range fun p : Multiset (Fin 1 ⊕ Fin 3) × Module.Dual ℂ (ConjModule V) =>
      ((0, DerivAlgebraComplex.basis p.1 ⊗ₜ[ℂ] p.2) : JetComponentSpace V)

/-- The derivative monomials span the jet component space: every component function is the
  sum of its two halves, and each half is spanned by derivative monomials. -/
lemma span_generators_eq_top : Submodule.span ℂ (generators V) = ⊤ := by
  rw [eq_top_iff]
  rintro v -
  have hv : v = LinearMap.inl ℂ _ _ v.1 + LinearMap.inr ℂ _ _ v.2 :=
    Prod.ext (by simp) (by simp)
  rw [hv]
  refine Submodule.add_mem _ ?_ ?_
  · have hle : Submodule.span ℂ (Set.range fun p : Multiset (Fin 1 ⊕ Fin 3) ×
        Module.Dual ℂ V => DerivAlgebraComplex.basis p.1 ⊗ₜ[ℂ] p.2) ≤
        Submodule.comap (LinearMap.inl ℂ (DerivAlgebraComplex ⊗[ℂ] Module.Dual ℂ V)
          (DerivAlgebraComplex ⊗[ℂ] Module.Dual ℂ (ConjModule V)))
          (Submodule.span ℂ (generators V)) := by
      rw [Submodule.span_le]
      rintro _ ⟨p, rfl⟩
      exact Submodule.subset_span (Or.inl ⟨p, rfl⟩)
    exact hle (by rw [basisTmul_span_top]; trivial)
  · have hle : Submodule.span ℂ (Set.range fun p : Multiset (Fin 1 ⊕ Fin 3) ×
        Module.Dual ℂ (ConjModule V) => DerivAlgebraComplex.basis p.1 ⊗ₜ[ℂ] p.2) ≤
        Submodule.comap (LinearMap.inr ℂ (DerivAlgebraComplex ⊗[ℂ] Module.Dual ℂ V)
          (DerivAlgebraComplex ⊗[ℂ] Module.Dual ℂ (ConjModule V)))
          (Submodule.span ℂ (generators V)) := by
      rw [Submodule.span_le]
      rintro _ ⟨p, rfl⟩
      exact Submodule.subset_span (Or.inr ⟨p, rfl⟩)
    exact hle (by rw [basisTmul_span_top]; trivial)

/-- Every derivative monomial is a monomial eigenvector of the component map: this is the
  only property of the component map that the square-zero argument uses. -/
lemma exists_jetComponentPoly_eq_monomial (w : ℕ) {v : JetComponentSpace V}
    (hv : v ∈ generators V) :
    ∃ n : ℕ, jetComponentPoly w v = Polynomial.monomial n (ExteriorAlgebra.ι ℂ v) := by
  rcases hv with ⟨p, rfl⟩ | ⟨p, rfl⟩
  · exact ⟨w + 2 * Multiset.card p.1, jetComponentPoly_inl w p.1 p.2⟩
  · exact ⟨w + 2 * Multiset.card p.1, jetComponentPoly_inr w p.1 p.2⟩

set_option maxHeartbeats 800000 in
/-- The component map squares to zero, as the universal property of the exterior algebra
  demands. The symmetrised square is a bilinear form, so it is enough to check that it
  vanishes on the derivative monomials, where it is a monomial multiple of
  `ExteriorAlgebra.ι_add_mul_swap`; halving then gives the square itself. -/
lemma jetComponentPoly_mul_self (w : ℕ) (v : JetComponentSpace V) :
    jetComponentPoly w v * jetComponentPoly w v = 0 := by
  have key : ((LinearMap.mul ℂ (Polynomial (FermionicAlgebra V))).compl₁₂
        (jetComponentPoly (V := V) w) (jetComponentPoly (V := V) w)) +
      ((LinearMap.mul ℂ (Polynomial (FermionicAlgebra V))).compl₁₂
        (jetComponentPoly (V := V) w) (jetComponentPoly (V := V) w)).flip = 0 := by
    refine LinearMap.ext_on span_generators_eq_top fun x hx => ?_
    refine LinearMap.ext_on span_generators_eq_top fun y hy => ?_
    obtain ⟨n, hn⟩ := exists_jetComponentPoly_eq_monomial w hx
    obtain ⟨m, hm⟩ := exists_jetComponentPoly_eq_monomial w hy
    simp only [LinearMap.add_apply, LinearMap.compl₁₂_apply, LinearMap.flip_apply,
      LinearMap.mul_apply', LinearMap.zero_apply]
    rw [hn, hm, Polynomial.monomial_mul_monomial, Polynomial.monomial_mul_monomial,
      Nat.add_comm m n, ← map_add, ExteriorAlgebra.ι_add_mul_swap, map_zero]
  have h2 := LinearMap.congr_fun (LinearMap.congr_fun key v) v
  simp only [LinearMap.add_apply, LinearMap.compl₁₂_apply, LinearMap.flip_apply,
    LinearMap.mul_apply', LinearMap.zero_apply] at h2
  have h3 : (2 : ℂ) • (jetComponentPoly w v * jetComponentPoly w v) = 0 := by
    rw [two_smul]
    exact h2
  have h4 : (2⁻¹ : ℂ) • ((2 : ℂ) • (jetComponentPoly w v * jetComponentPoly w v)) =
      jetComponentPoly w v * jetComponentPoly w v := by
    rw [smul_smul, show ((2 : ℂ)⁻¹ * 2) = 1 by norm_num, one_smul]
  rw [← h4, h3, smul_zero]

/-!

## C. The mass-weight polynomial on the fermionic algebra

-/

/-- The mass-weight polynomial on the fermionic algebra of a field of mass weight `w`: the
  `ℂ`-algebra map sending a generator of mass weight `n` to `X ^ n` times itself. It is
  `FermionicAlgebra.massWeightScale` with the scalar replaced by the formal variable `X`. -/
noncomputable def massWeightPoly (w : ℕ) :
    FermionicAlgebra V →ₐ[ℂ] Polynomial (FermionicAlgebra V) :=
  ExteriorAlgebra.lift ℂ ⟨jetComponentPoly w, jetComponentPoly_mul_self w⟩

/-- On a component function the mass-weight polynomial is the component-function map. -/
@[simp]
lemma massWeightPoly_ι (w : ℕ) (x : JetComponentSpace V) :
    massWeightPoly w (ExteriorAlgebra.ι ℂ x) = jetComponentPoly w x := by
  rw [massWeightPoly, ExteriorAlgebra.lift_ι_apply]

/-!

## D. The mass weight of the field and its derivatives

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

## E. Recovering an element from its mass-weight polynomial

-/

/-- Setting the formal variable to one collapses a half mass-weight polynomial back to the
  symbol it graded. The derivative monomials span, so it is enough to check this on the
  multiset basis. -/
lemma halfPoly_eval_one {W : Type} [AddCommGroup W] [Module ℂ W] (w : ℕ)
    (k : DerivAlgebraComplex ⊗[ℂ] W →ₗ[ℂ] FermionicAlgebra V)
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
    (jetComponentPoly w x).eval 1 = ExteriorAlgebra.ι ℂ x := by
  rw [jetComponentPoly_apply, Polynomial.eval_add, halfPoly_eval_one, halfPoly_eval_one,
    ιFst, ιSnd, LinearMap.comp_apply, LinearMap.comp_apply, ← map_add]
  congr 1
  exact Prod.ext (by simp) (by simp)

/-- Setting the formal variable to one recovers the original element: the mass-weight
  pieces of an element sum back to it. -/
lemma massWeightPoly_eval_one (w : ℕ) (a : FermionicAlgebra V) :
    (massWeightPoly w a).eval 1 = a := by
  have h : (Polynomial.eval₂AlgHom (AlgHom.id ℂ (FermionicAlgebra V)) 1
      fun b => Commute.one_right b).comp (massWeightPoly w) =
      AlgHom.id ℂ (FermionicAlgebra V) := by
    refine ExteriorAlgebra.hom_ext (LinearMap.ext fun x => ?_)
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

end FermionicAlgebra

end StandardModel
