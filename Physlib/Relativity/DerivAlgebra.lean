/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Mathlib.RingTheory.TensorProduct.Basic
public import Physlib.Relativity.Tensors.ComplexTensor.Basic
public import Physlib.Mathematics.ConjModule
public import Mathlib.LinearAlgebra.ExteriorAlgebra.Basis
public import Mathlib.Algebra.TrivSqZeroExt.Basic
public import Mathlib.Data.Finsupp.Multiset
public import Mathlib.Data.Finsupp.Weight
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.SymmetricAlgebra.Basic
public import Mathlib.LinearAlgebra.SymmetricAlgebra.Basis
public import Mathlib.RepresentationTheory.Basic
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.MvPowerSeries.Derivative
public import Physlib.Relativity.JetRing.Matrix
public import Physlib.Relativity.Tensors.ComplexTensor.Vector.Pre.Basic
public import Physlib.Relativity.Tensors.RealTensor.CoVector.Representation
/-!
# Derivative algebras

-/

@[expose] public section

/-!

## B. The complex derivative algebra

-/

abbrev DerivAlgebraComplex := SymmetricAlgebra ℂ (Module.Dual ℂ Lorentz.CoℂModule)

namespace DerivAlgebraComplex

/-!

### B.1. The basis indexed by multisets

-/

/-- The basis of the algebra of derivative symbols, indexed by multisets of
  spacetime indices: the multiset `s` labels the monomial `∂_s`. -/
noncomputable def basis :
    Module.Basis (Multiset (Fin 1 ⊕ Fin 3)) ℂ DerivAlgebraComplex :=
  Lorentz.complexCoBasis.dualBasis.symmetricAlgebra.reindex Multiset.toFinsupp.toEquiv.symm

/-- The basis vector at a multiset of derivative indices is the corresponding
  basis monomial of the symmetric algebra of dual symbols. -/
lemma basis_apply (s : Multiset (Fin 1 ⊕ Fin 3)) :
    basis s =
      Lorentz.complexCoBasis.dualBasis.symmetricAlgebra (Multiset.toFinsupp s) := by
  rw [basis, Module.Basis.reindex_apply, Equiv.symm_symm]
  rfl

/-- The basis vector at the empty multiset is the unit of the algebra: the
  zeroth-order symbol carries no derivatives. -/
lemma basis_nil :
    basis ({} : Multiset (Fin 1 ⊕ Fin 3)) = 1 := by
  have h : (MvPolynomial.basisMonomials (Fin 1 ⊕ Fin 3) ℂ) ((0 : (Fin 1 ⊕ Fin 3) →₀ ℕ)) = 1 := by
    rw [MvPolynomial.coe_basisMonomials]
    simp [MvPolynomial.monomial_zero']
  rw [basis, Module.Basis.reindex_apply, Equiv.symm_symm,
    show Multiset.toFinsupp.toEquiv ({} : Multiset (Fin 1 ⊕ Fin 3)) = 0 by simp,
    Module.Basis.symmetricAlgebra, Module.Basis.map_apply, h]
  simp

/-- The basis vector at a singleton multiset is the corresponding first-order
  derivative symbol. -/
lemma basis_singleton (μ : Fin 1 ⊕ Fin 3) :
    basis ({μ} : Multiset (Fin 1 ⊕ Fin 3)) =
      SymmetricAlgebra.ι ℂ (Module.Dual ℂ Lorentz.CoℂModule)
        (Lorentz.complexCoBasis.dualBasis μ) := by
  have h : (MvPolynomial.basisMonomials (Fin 1 ⊕ Fin 3) ℂ) (Finsupp.single μ 1) =
      MvPolynomial.X μ := rfl
  rw [basis, Module.Basis.reindex_apply, Equiv.symm_symm,
    show Multiset.toFinsupp.toEquiv ({μ} : Multiset (Fin 1 ⊕ Fin 3)) =
      Finsupp.single μ 1 by simp,
    Module.Basis.symmetricAlgebra, Module.Basis.map_apply, h]
  simp

/-- Basis monomials multiply by adding the multisets of derivative indices:
  `∂_s ∂_t = ∂_{s + t}`. -/
lemma basis_mul (s t : Multiset (Fin 1 ⊕ Fin 3)) :
    basis s * basis t = basis (s + t) := by
  rw [basis_apply, basis_apply, basis_apply, map_add]
  simp only [Module.Basis.symmetricAlgebra, Module.Basis.map_apply,
    show ∀ p, (SymmetricAlgebra.equivMvPolynomial
        Lorentz.complexCoBasis.dualBasis).symm.toLinearEquiv p =
      (SymmetricAlgebra.equivMvPolynomial Lorentz.complexCoBasis.dualBasis).symm p
      from fun _ => rfl,
    ← map_mul, MvPolynomial.coe_basisMonomials]
  simp only [MvPolynomial.monomial_mul, mul_one]

/-!

### B.2. The derivative operator

-/

/-- The derivative of an element in `DerivAlgebraComplex` taking e.g.
  `∂_s` to `∂_μ ∂_s`. -/
noncomputable def deriv (μ : Fin 1 ⊕ Fin 3) : DerivAlgebraComplex →ₗ[ℂ] DerivAlgebraComplex :=
  Lorentz.complexCoBasis.dualBasis.symmetricAlgebra.constr ℂ fun m =>
    Lorentz.complexCoBasis.dualBasis.symmetricAlgebra (m + Finsupp.single μ 1)

lemma deriv_basis (μ : Fin 1 ⊕ Fin 3) (m : (Fin 1 ⊕ Fin 3) →₀ ℕ) :
    deriv μ (Lorentz.complexCoBasis.dualBasis.symmetricAlgebra m) =
      Lorentz.complexCoBasis.dualBasis.symmetricAlgebra (m + Finsupp.single μ 1) := by
  rw [deriv, Module.Basis.constr_basis]

lemma deriv_comm_apply (μ ν : Fin 1 ⊕ Fin 3) (x : DerivAlgebraComplex) :
    deriv μ (deriv ν x) = deriv ν (deriv μ x) := by
  have h : (deriv μ) ∘ₗ (deriv ν) = (deriv ν) ∘ₗ (deriv μ) := by
    refine Lorentz.complexCoBasis.dualBasis.symmetricAlgebra.ext fun m => ?_
    simp only [LinearMap.coe_comp, Function.comp_apply, deriv_basis]
    rw [add_assoc, add_assoc, add_comm (Finsupp.single ν 1)]
  exact LinearMap.congr_fun h x

/-- The derivative operator on the multiset basis: appending the derivative
  index to the multiset. -/
lemma deriv_basis_multiset (μ : Fin 1 ⊕ Fin 3) (s : Multiset (Fin 1 ⊕ Fin 3)) :
    deriv μ (basis s) = basis (s + {μ}) := by
  rw [basis_apply, deriv_basis, basis_apply,
    show Multiset.toFinsupp (s + {μ}) = Multiset.toFinsupp s + Finsupp.single μ 1 from by
      rw [map_add, Multiset.toFinsupp_singleton]]

/-- The derivative operator is right multiplication by the first-order derivative
  symbol. -/
lemma deriv_apply_eq_mul (μ : Fin 1 ⊕ Fin 3) (a : DerivAlgebraComplex) :
    deriv μ a = a * basis ({μ} : Multiset (Fin 1 ⊕ Fin 3)) := by
  have h : deriv μ = LinearMap.mulRight ℂ (basis ({μ} : Multiset (Fin 1 ⊕ Fin 3))) := by
    refine basis.ext fun s => ?_
    rw [deriv_basis_multiset, LinearMap.mulRight_apply, basis_mul]
  rw [LinearMap.congr_fun h a, LinearMap.mulRight_apply]

/-!

### B.2. Evaluating on the Jet ring

-/
open Nat

/-- Formal partial derivatives of a multivariate power series commute: each is given on
  coefficients by a shift and a multiplication, and the two shifts commute. -/
lemma _root_.MvPowerSeries.pderiv_comm {σ R : Type*} [CommSemiring R] (i j : σ)
    (f : MvPowerSeries σ R) :
    MvPowerSeries.pderiv R i (MvPowerSeries.pderiv R j f) =
      MvPowerSeries.pderiv R j (MvPowerSeries.pderiv R i f) := by
  ext n
  rw [MvPowerSeries.coeff_pderiv, MvPowerSeries.coeff_pderiv, MvPowerSeries.coeff_pderiv,
    MvPowerSeries.coeff_pderiv, add_right_comm n (Finsupp.single i 1) (Finsupp.single j 1)]
  rcases eq_or_ne i j with rfl | h
  · ring
  · rw [Finsupp.add_apply, Finsupp.add_apply, Finsupp.single_eq_of_ne h,
      Finsupp.single_eq_of_ne h.symm]
    push_cast
    ring

/-- Differentiating a jet along a multiset of directions is well defined: the partial
  derivatives commute, so the fold over a multiset does not depend on the order. -/
instance : RightCommutative
    (fun (f : JetRing) (μ : Fin 1 ⊕ Fin 3) => MvPowerSeries.pderiv ℂ μ f) where
  right_comm f μ ν := MvPowerSeries.pderiv_comm ν μ f

/-- The evaluation map taking a function `f : JetRing` to `∂_μ f`. -/
noncomputable def eval : DerivAlgebraComplex →ₗ[ℂ] JetRing →ₗ[ℂ] ℂ :=
  Lorentz.complexCoBasis.dualBasis.symmetricAlgebra.constr ℂ fun m =>
    (∏ μ, (m μ)! : ℕ) • MvPowerSeries.coeff m


@[simp]
lemma eval_basis (m : (Fin 1 ⊕ Fin 3) →₀ ℕ) (f : JetRing) :
    eval (Lorentz.complexCoBasis.dualBasis.symmetricAlgebra m) f =
      (∏ μ, (m μ)! : ℕ) • MvPowerSeries.coeff m f := by
  rw [eval, Module.Basis.constr_basis]
  rfl

lemma eval_monomial (p : DerivAlgebraComplex) (m : (Fin 1 ⊕ Fin 3) →₀ ℕ) :
    eval p (MvPowerSeries.monomial m 1) =
      ((∏ μ, (m μ)! : ℕ) : ℂ) * Lorentz.complexCoBasis.dualBasis.symmetricAlgebra.repr p m := by
  classical
  rw [eval, Module.Basis.constr_apply, Finsupp.sum, LinearMap.sum_apply]
  simp only [LinearMap.smul_apply, MvPowerSeries.coeff_monomial]
  rw [Finset.sum_eq_single m]
  · by_cases hm : m ∈ (Lorentz.complexCoBasis.dualBasis.symmetricAlgebra.repr p).support
    · simp [mul_comm]
    · rw [Finsupp.notMem_support_iff.mp hm]
      simp
  · intro i _ hi
    simp [hi]
  · intro hm
    rw [Finsupp.notMem_support_iff.mp hm]
    simp

lemma eval_injective {p q : DerivAlgebraComplex}
    (h : ∀ f, eval p f = eval q f) : p = q := by
  refine Lorentz.complexCoBasis.dualBasis.symmetricAlgebra.ext_elem fun m => ?_
  have hf := h (MvPowerSeries.monomial m 1)
  rw [eval_monomial, eval_monomial] at hf
  have hfac : ((∏ μ, (m μ)! : ℕ) : ℂ) ≠ 0 := by
    rw [Nat.cast_ne_zero]
    exact Finset.prod_ne_zero_iff.mpr fun μ _ => Nat.factorial_ne_zero (m μ)
  exact mul_left_cancel₀ hfac hf

/-- Adjointness: the shift of derivative symbols is the transpose of the formal
  partial derivative under the divided-power pairing. -/
lemma eval_deriv (ν : Fin 1 ⊕ Fin 3) (p : DerivAlgebraComplex) (f : JetRing) :
    eval (deriv ν p) f = eval p (MvPowerSeries.pderiv ℂ ν f) := by
  have h : (eval.flip f) ∘ₗ deriv ν =
      eval.flip (MvPowerSeries.pderiv ℂ ν f) := by
    refine Lorentz.complexCoBasis.dualBasis.symmetricAlgebra.ext fun m => ?_
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.flip_apply,
      deriv_basis, eval_basis, MvPowerSeries.coeff_pderiv]
    have hfac : (∏ ρ, (((m + Finsupp.single ν 1) : (Fin 1 ⊕ Fin 3) →₀ ℕ) ρ)!) =
        (m ν + 1) * ∏ ρ, (m ρ)! := by
      rw [show (∏ ρ : Fin 1 ⊕ Fin 3,
          (((m + Finsupp.single ν 1) : (Fin 1 ⊕ Fin 3) →₀ ℕ) ρ)!) =
          ∏ ρ, ((if ρ = ν then m ν + 1 else 1) * (m ρ)!) from
        Finset.prod_congr rfl fun ρ _ => by
          rcases eq_or_ne ρ ν with rfl | h
          · rw [Finsupp.add_apply, Finsupp.single_eq_same, Nat.factorial_succ, if_pos rfl]
          · rw [Finsupp.add_apply, Finsupp.single_eq_of_ne h, add_zero, if_neg h, one_mul],
        Finset.prod_mul_distrib, Finset.prod_ite_eq' Finset.univ ν]
      simp
    rw [nsmul_eq_mul, nsmul_eq_mul, hfac]
    push_cast
    ring
  exact LinearMap.congr_fun h p

/-- The pairing of the unit derivative symbol with a jet is its value at the base
  point: the empty derivative multiset reads off the constant term. -/
lemma eval_one (f : JetRing) :
    eval (1 : DerivAlgebraComplex) f = MvPowerSeries.constantCoeff f := by
  rw [show (1 : DerivAlgebraComplex) = basis (0 : Multiset (Fin 1 ⊕ Fin 3)) from basis_nil.symm,
    basis_apply]
  simp

/-- Iterating adjointness: the pairing of the basis monomial `∂_s` with a jet is the
  constant term of the iterated formal partial derivative `∂_s f`. This is the concrete
  description of the divided-power pairing that `eval_deriv` encodes one derivative at a
  time. -/
lemma eval_basis_eq_constantCoeff_foldl_pderiv (s : Multiset (Fin 1 ⊕ Fin 3)) (f : JetRing) :
    eval (basis s) f =
      MvPowerSeries.constantCoeff (s.foldl (fun g μ => MvPowerSeries.pderiv ℂ μ g) f) := by
  induction s using Multiset.induction_on generalizing f with
  | empty =>
    rw [Multiset.foldl_zero, show (0 : Multiset (Fin 1 ⊕ Fin 3)) = {} from rfl, basis_nil,
      eval_one]
  | cons μ t ih =>
    rw [Multiset.foldl_cons, ← ih,
      show basis (μ ::ₘ t) = deriv μ (basis t) by
        rw [deriv_basis_multiset, ← Multiset.singleton_add, add_comm],
      eval_deriv]

/-!

### B.2. The action of the Jet ring

-/

/-- The action of `χ` on the derivatives, this takes `∂_μ ·` to `∂_μ (χ ·)`,
  expanded out explicitly. -/
noncomputable def jetRingAction (χ : JetRing) : DerivAlgebraComplex →ₗ[ℂ] DerivAlgebraComplex :=
  Lorentz.complexCoBasis.dualBasis.symmetricAlgebra.constr ℂ fun m =>
    ∑ p ∈ Finset.antidiagonal m,
      ((∏ μ, (m μ).descFactorial (p.1 μ) : ℕ) : ℂ) • MvPowerSeries.coeff p.1 χ •
        Lorentz.complexCoBasis.dualBasis.symmetricAlgebra p.2

lemma jetRingAction_basis (χ : JetRing) (m : (Fin 1 ⊕ Fin 3) →₀ ℕ) :
    jetRingAction χ (Lorentz.complexCoBasis.dualBasis.symmetricAlgebra m) =
      ∑ p ∈ Finset.antidiagonal m,
        ((∏ μ, (m μ).descFactorial (p.1 μ) : ℕ) : ℂ) • MvPowerSeries.coeff p.1 χ •
          Lorentz.complexCoBasis.dualBasis.symmetricAlgebra p.2 := by
  rw [jetRingAction, Module.Basis.constr_basis]

lemma eval_jetRingAction (χ f : JetRing) (p : DerivAlgebraComplex) :
    eval (jetRingAction χ p) f = eval p (χ * f) := by
  classical
  have h : (eval.flip f) ∘ₗ jetRingAction χ = eval.flip (χ * f) := by
    refine Lorentz.complexCoBasis.dualBasis.symmetricAlgebra.ext fun m => ?_
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.flip_apply]
    rw [jetRingAction, Module.Basis.constr_basis]
    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply,
      eval_basis, smul_eq_mul, nsmul_eq_mul]
    rw [MvPowerSeries.coeff_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun q hq => ?_
    have hm : q.1 + q.2 = m := Finset.mem_antidiagonal.mp hq
    have hfac : ((∏ μ, (m μ).descFactorial (q.1 μ) : ℕ) : ℂ) *
        ((∏ μ, (q.2 μ)! : ℕ) : ℂ) = ((∏ μ, (m μ)! : ℕ) : ℂ) := by
      rw [← Nat.cast_mul, ← Finset.prod_mul_distrib]
      congr 1
      refine Finset.prod_congr rfl fun μ _ => ?_
      rw [mul_comm]
      have h1 : q.1 μ ≤ m μ := by
        rw [← hm]; simp
      have h2 : m μ - q.1 μ = q.2 μ := by
        rw [← hm]; simp
      rw [← h2]
      exact Nat.factorial_mul_descFactorial h1
    rw [← hfac]
    ring
  exact LinearMap.congr_fun h p

/-- The action of a jet on a derivative monomial, in multiset form: `∂_s` is sent to the
  all-orders Leibniz convolution, each splitting `s = s₁ + s₂` of the derivative multiset
  contributing the base-point Taylor coefficient `(∂_{s₁} χ)(0)` against the lower monomial
  `∂_{s₂}`.

  This is `jetRingAction_basis` with the `Nat.choose` bookkeeping traded for the
  divided-power pairing: both sides are compared through `eval`, where the identity is the
  Leibniz rule `JetRing.constantCoeff_foldl_pderiv_mul` at the base point. It is the form
  in which the transformation law of a matter field is stated. -/
lemma jetRingAction_basis_multiset (χ : JetRing) (s : Multiset (Fin 1 ⊕ Fin 3)) :
    jetRingAction χ (basis s) =
      (s.antidiagonal.map fun p =>
        MvPowerSeries.constantCoeff
            (p.1.foldl (fun h ρ => MvPowerSeries.pderiv ℂ ρ h) χ) • basis p.2).sum := by
  refine eval_injective fun f => ?_
  rw [eval_jetRingAction, eval_basis_eq_constantCoeff_foldl_pderiv,
    JetRing.constantCoeff_foldl_pderiv_mul,
    show eval ((s.antidiagonal.map fun p =>
        MvPowerSeries.constantCoeff
          (p.1.foldl (fun h ρ => MvPowerSeries.pderiv ℂ ρ h) χ) • basis p.2).sum) f
      = (eval.flip f) ((s.antidiagonal.map fun p =>
        MvPowerSeries.constantCoeff
          (p.1.foldl (fun h ρ => MvPowerSeries.pderiv ℂ ρ h) χ) • basis p.2).sum) from rfl,
    map_multiset_sum, Multiset.map_map]
  refine congrArg Multiset.sum (Multiset.map_congr rfl fun p _ => ?_)
  rw [Function.comp_apply, map_smul, LinearMap.flip_apply, smul_eq_mul,
    eval_basis_eq_constantCoeff_foldl_pderiv]

/-- Constant jets act on the derivative symbols by their value: `C c` has no
  derivative coordinates. -/
@[simp]
lemma jetRingAction_C (c : ℂ) :
    jetRingAction (MvPowerSeries.C c) = c • LinearMap.id := by
  refine LinearMap.ext fun p => eval_injective fun f => ?_
  rw [eval_jetRingAction,
    show (MvPowerSeries.C c : JetRing) * f = c • f from
      (algebraMap_smul JetRing c f).symm ▸ (Algebra.smul_def c f).symm]
  simp

@[simp]
lemma jetRingAction_one : jetRingAction (1 : JetRing) = LinearMap.id := by
  rw [show (1 : JetRing) = MvPowerSeries.C 1 from (map_one _).symm, jetRingAction_C, one_smul]

/-- The derivative action is multiplicative: it is the transpose of multiplication
  in the commutative jet ring. This makes `χ ↦ χ(∂)` a monoid homomorphism and
  hence yields representations of the jet gauge group on polynomial jet spaces. -/
lemma jetRingAction_mul (χ ψ : JetRing) :
    jetRingAction (χ * ψ) = jetRingAction χ ∘ₗ jetRingAction ψ := by
  refine LinearMap.ext fun p => eval_injective fun f => ?_
  simp only [LinearMap.coe_comp, Function.comp_apply]
  rw [eval_jetRingAction, eval_jetRingAction, eval_jetRingAction]
  ring_nf


@[simp]
lemma jetRingAction_zero : jetRingAction (0 : JetRing) = 0 := by
  simp only [jetRingAction, Fintype.prod_sum_type, Finset.univ_unique, Fin.default_eq_zero,
    Fin.isValue, Finset.prod_singleton, Nat.cast_mul, Nat.cast_prod, MvPowerSeries.coeff_zero,
    zero_smul, smul_zero, Finset.sum_const_zero, EmbeddingLike.map_eq_zero_iff]
  rfl

lemma jetRingAction_add (χ ψ : JetRing) :
    jetRingAction (χ + ψ) = jetRingAction χ + jetRingAction ψ := by
  refine LinearMap.ext fun p => eval_injective fun f => ?_
  simp only [LinearMap.add_apply, map_add, eval_jetRingAction]
  rw [add_mul, map_add]

/-- The derivative action as a ring homomorphism from the jet ring to the
  endomorphisms of the algebra of derivative symbols: the module structure of the
  jet ring on its graded dual. -/
noncomputable def jetRingActionHom : JetRing →+* Module.End ℂ DerivAlgebraComplex where
  toFun := jetRingAction
  map_one' := jetRingAction_one
  map_mul' χ ψ := jetRingAction_mul χ ψ
  map_zero' := jetRingAction_zero
  map_add' := jetRingAction_add

/-- The actions of two jets commute: the jet ring is commutative. -/
lemma jetRingAction_comm (χ ψ : JetRing) (a : DerivAlgebraComplex) :
    jetRingAction χ (jetRingAction ψ a) = jetRingAction ψ (jetRingAction χ a) := by
  rw [← LinearMap.comp_apply, ← jetRingAction_mul, mul_comm, jetRingAction_mul,
    LinearMap.comp_apply]

/-- The derivative action on the zeroth-order (field) symbol: it is scaled by the
  value of the jet at the base point. -/
@[simp]
lemma jetRingAction_apply_one (χ : JetRing) :
    jetRingAction χ (1 : DerivAlgebraComplex) =
      MvPowerSeries.constantCoeff χ • 1 := by
  have h0 : Lorentz.complexCoBasis.dualBasis.symmetricAlgebra (0 : (Fin 1 ⊕ Fin 3) →₀ ℕ) =
      1 := by
    rw [show (0 : (Fin 1 ⊕ Fin 3) →₀ ℕ) =
        Multiset.toFinsupp ({} : Multiset (Fin 1 ⊕ Fin 3)) by simp,
      ← basis_apply, basis_nil]
  rw [show (1 : DerivAlgebraComplex) =
      Lorentz.complexCoBasis.dualBasis.symmetricAlgebra 0 from h0.symm,
    jetRingAction, Module.Basis.constr_basis, Finsupp.antidiagonal_zero, Finset.sum_singleton]
  simp

/-- The derivative action on a first-order derivative symbol implements the Leibniz
  rule: `∂_μ ↦ χ(0) ∂_μ + (∂_μχ)(0) 1`. The value of the jet multiplies the
  first-derivative symbol, and its first derivative feeds the zeroth-order
  symbol. -/
lemma jetRingAction_apply_ι (χ : JetRing) (μ : Fin 1 ⊕ Fin 3) :
    jetRingAction χ (SymmetricAlgebra.ι ℂ (Module.Dual ℂ Lorentz.CoℂModule)
        (Lorentz.complexCoBasis.dualBasis μ)) =
      MvPowerSeries.constantCoeff χ •
        SymmetricAlgebra.ι ℂ (Module.Dual ℂ Lorentz.CoℂModule)
          (Lorentz.complexCoBasis.dualBasis μ) +
        MvPowerSeries.coeff (Finsupp.single μ 1) χ • 1 := by
  classical
  have h0 : Lorentz.complexCoBasis.dualBasis.symmetricAlgebra (0 : (Fin 1 ⊕ Fin 3) →₀ ℕ) =
      1 := by
    rw [show (0 : (Fin 1 ⊕ Fin 3) →₀ ℕ) =
        Multiset.toFinsupp ({} : Multiset (Fin 1 ⊕ Fin 3)) by simp,
      ← basis_apply, basis_nil]
  have hs : Lorentz.complexCoBasis.dualBasis.symmetricAlgebra (Finsupp.single μ 1) =
      SymmetricAlgebra.ι ℂ (Module.Dual ℂ Lorentz.CoℂModule)
        (Lorentz.complexCoBasis.dualBasis μ) := by
    rw [show (Finsupp.single μ 1 : (Fin 1 ⊕ Fin 3) →₀ ℕ) =
        Multiset.toFinsupp ({μ} : Multiset (Fin 1 ⊕ Fin 3)) by simp,
      ← basis_apply, basis_singleton]
  rw [show SymmetricAlgebra.ι ℂ (Module.Dual ℂ Lorentz.CoℂModule)
      (Lorentz.complexCoBasis.dualBasis μ) =
      Lorentz.complexCoBasis.dualBasis.symmetricAlgebra (Finsupp.single μ 1) from hs.symm,
    jetRingAction, Module.Basis.constr_basis, Finsupp.antidiagonal_single,
    show Finset.antidiagonal (1 : ℕ) = {(0, 1), (1, 0)} by decide, Finset.map_insert,
    Finset.map_singleton, Finset.sum_insert (by simp [Finsupp.single_eq_zero]),
    Finset.sum_singleton]
  have h1 : (∏ ν, ((Finsupp.single μ 1) ν).descFactorial ((Finsupp.single μ 1) ν)) = 1 :=
    Finset.prod_eq_one fun ν _ => by
      rcases eq_or_ne μ ν with h | h
      · subst h; simp
      · simp [h]
  simp only [Function.Embedding.coe_prodMap, Function.Embedding.coeFn_mk, Prod.map_apply,
    Finsupp.single_zero, Finsupp.coe_zero, Pi.zero_apply, Nat.descFactorial_zero,
    Finset.prod_const_one, Nat.cast_one, one_smul, MvPowerSeries.coeff_zero_eq_constantCoeff,
    h1, hs, h0]

/-- The commutation of the jet-ring action with the derivative operator: acting by
  `χ` after differentiating equals differentiating after acting, plus the action
  of the derivative `∂_ν χ`. This is the operator form of the Leibniz rule
  `∂_ν (χ f) = χ ∂_ν f + (∂_ν χ) f` under the divided-power pairing. -/
lemma jetRingAction_deriv (χ : JetRing) (ν : Fin 1 ⊕ Fin 3) (a : DerivAlgebraComplex) :
    jetRingAction χ (deriv ν a) =
      deriv ν (jetRingAction χ a) + jetRingAction (MvPowerSeries.pderiv ℂ ν χ) a := by
  refine eval_injective fun f => ?_
  rw [eval_jetRingAction, eval_deriv, Derivation.leibniz, smul_eq_mul, smul_eq_mul,
    map_add, map_add, LinearMap.add_apply, eval_deriv, eval_jetRingAction,
    eval_jetRingAction, mul_comm f]

/-!

### B.5. The action of the Lorentz group

-/

/-- The components of a dual representation on a dual basis: if `ρ g⁻¹` has
  matrix `M` in the basis `b` (columns indexing the argument), then `ρ.dual g`
  acts on the dual basis by the rows of `M`. -/
lemma _root_.Representation.dual_apply_dualBasis {k G V ι : Type*} [CommRing k]
    [Group G] [AddCommGroup V] [Module k V] [Fintype ι] [DecidableEq ι]
    (ρ : Representation k G V) (b : Module.Basis ι k V) (g : G) (i : ι)
    (M : Matrix ι ι k) (hM : ∀ j, ρ g⁻¹ (b j) = ∑ l, M l j • b l) :
    ρ.dual g (b.dualBasis i) = ∑ j, M i j • b.dualBasis j := by
  refine b.ext fun j => ?_
  rw [Representation.dual_apply, Module.Dual.transpose_apply, LinearMap.comp_apply, hM]
  simp [Finsupp.single_apply, Finset.sum_ite_eq, Finset.sum_ite_eq']

open Matrix MatrixGroups

/-- The representation of the Lorentz group `SL(2,ℂ)` on the algebra of derivative
  symbols, extending the dual covector representation multiplicatively. -/
noncomputable def repLorentzGroup : Representation ℂ SL(2,ℂ) DerivAlgebraComplex where
  toFun Λ := (SymmetricAlgebra.lift
    (SymmetricAlgebra.ι ℂ _ ∘ₗ Lorentz.CoℂModule.SL2CRep.dual Λ)).toLinearMap
  map_one' := by
    suffices h : SymmetricAlgebra.lift
        (SymmetricAlgebra.ι ℂ _ ∘ₗ Lorentz.CoℂModule.SL2CRep.dual 1) =
        AlgHom.id ℂ (SymmetricAlgebra ℂ (Module.Dual ℂ Lorentz.CoℂModule)) by
      rw [h]; rfl
    refine SymmetricAlgebra.algHom_ext (LinearMap.ext fun x => ?_)
    simp
    rfl
  map_mul' Λ1 Λ2 := by
    suffices h : SymmetricAlgebra.lift
        (SymmetricAlgebra.ι ℂ _ ∘ₗ Lorentz.CoℂModule.SL2CRep.dual (Λ1 * Λ2)) =
        (SymmetricAlgebra.lift
          (SymmetricAlgebra.ι ℂ _ ∘ₗ Lorentz.CoℂModule.SL2CRep.dual Λ1)).comp
        (SymmetricAlgebra.lift
          (SymmetricAlgebra.ι ℂ _ ∘ₗ Lorentz.CoℂModule.SL2CRep.dual Λ2)) by
      rw [h]; rfl
    refine SymmetricAlgebra.algHom_ext (LinearMap.ext fun x => ?_)
    simp [map_mul, Module.End.mul_apply]

@[simp]
lemma repLorentzGroup_apply_one (Λ : SL(2,ℂ)) : repLorentzGroup Λ 1 = 1:= by
  simp [repLorentzGroup]

lemma repLorentzGroup_apply_mul (Λ : SL(2,ℂ)) (a b : DerivAlgebraComplex) :
    repLorentzGroup Λ (a * b) = repLorentzGroup Λ a * repLorentzGroup Λ b := by
  simp [repLorentzGroup, map_mul]

/-- The Lorentz action on a generator. -/
@[simp]
lemma repLorentzGroup_apply_ι (Λ : SL(2,ℂ)) (x : Module.Dual ℂ Lorentz.CoℂModule) :
    repLorentzGroup Λ (SymmetricAlgebra.ι ℂ (Module.Dual ℂ Lorentz.CoℂModule) x) =
      SymmetricAlgebra.ι ℂ (Module.Dual ℂ Lorentz.CoℂModule)
        (Lorentz.CoℂModule.SL2CRep.dual Λ x) := by
  simp [repLorentzGroup]

/-- The Lorentz action on a derivative: the derivative symbol transforms as a
  covector, mixing the spacetime directions by the components of `Λ` in the dual
  covector representation. -/
lemma repLorentzGroup_deriv (Λ : SL(2,ℂ)) (μ : Fin 1 ⊕ Fin 3) (a : DerivAlgebraComplex) :
    repLorentzGroup Λ (deriv μ a) =
      ∑ ν, (Lorentz.CoℂModule.SL2CRep.dual Λ (Lorentz.complexCoBasis.dualBasis μ))
        (Lorentz.complexCoBasis ν) • deriv ν (repLorentzGroup Λ a) := by
  have hb : repLorentzGroup Λ (basis ({μ} : Multiset (Fin 1 ⊕ Fin 3))) =
      ∑ ν, (Lorentz.CoℂModule.SL2CRep.dual Λ (Lorentz.complexCoBasis.dualBasis μ))
        (Lorentz.complexCoBasis ν) • basis ({ν} : Multiset (Fin 1 ⊕ Fin 3)) := by
    rw [basis_singleton, repLorentzGroup_apply_ι]
    conv_lhs => rw [← Lorentz.complexCoBasis.dualBasis.sum_repr
      (Lorentz.CoℂModule.SL2CRep.dual Λ (Lorentz.complexCoBasis.dualBasis μ))]
    rw [map_sum]
    refine Finset.sum_congr rfl fun ν _ => ?_
    rw [map_smul, Module.Basis.dualBasis_repr, basis_singleton]
  rw [deriv_apply_eq_mul, repLorentzGroup_apply_mul, hb, Finset.mul_sum]
  refine Finset.sum_congr rfl fun ν _ => ?_
  rw [mul_smul_comm, ← deriv_apply_eq_mul]

/-- The components of the complex dual covector action on the dual basis: the
  dual derivative slots transform contravariantly, by the columns of the
  (complexified) Lorentz matrix. The complex analogue of
  `Lorentz.CoVector.sl2Rep_dual_dualBasis`. -/
lemma _root_.Lorentz.CoℂModule.SL2CRep_dual_dualBasis (Λ : SL(2,ℂ))
    (μ : Fin 1 ⊕ Fin 3) :
    Lorentz.CoℂModule.SL2CRep.dual Λ (Lorentz.complexCoBasis.dualBasis μ) =
      ∑ j, (((Lorentz.SL2C.toLorentzGroup Λ).1 j μ : ℝ) : ℂ) •
        Lorentz.complexCoBasis.dualBasis j := by
  refine Representation.dual_apply_dualBasis _ _ _ _
    (Matrix.of fun l j => (((Lorentz.SL2C.toLorentzGroup Λ).1 j l : ℝ) : ℂ))
    (fun j => ?_)
  have hexp : Lorentz.CoℂModule.SL2CRep Λ⁻¹ (Lorentz.complexCoBasis j) =
      ∑ l, (LinearMap.toMatrix Lorentz.complexCoBasis Lorentz.complexCoBasis
        (Lorentz.CoℂModule.SL2CRep Λ⁻¹)) l j • Lorentz.complexCoBasis l := by
    conv_lhs => rw [← Lorentz.complexCoBasis.sum_repr
      (Lorentz.CoℂModule.SL2CRep Λ⁻¹ (Lorentz.complexCoBasis j))]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [LinearMap.toMatrix_apply]
  rw [hexp]
  refine Finset.sum_congr rfl fun l _ => ?_
  congr 1
  rw [Lorentz.complexCoBasis_ρ_apply, map_inv, Matrix.transpose_apply,
    ← LorentzGroup.toComplex_inv, Matrix.inv_inv_of_invertible]
  rfl

/-- The Lorentz action on the singleton derivative monomial: the derivative
  slot transforms by the columns of the Lorentz matrix. -/
lemma repLorentzGroup_basis_singleton (Λ : SL(2,ℂ)) (μ : Fin 1 ⊕ Fin 3) :
    repLorentzGroup Λ (basis ({μ} : Multiset (Fin 1 ⊕ Fin 3))) =
      ∑ ν, (((Lorentz.SL2C.toLorentzGroup Λ).1 ν μ : ℝ) : ℂ) •
        basis ({ν} : Multiset (Fin 1 ⊕ Fin 3)) := by
  rw [basis_singleton, repLorentzGroup_apply_ι,
    Lorentz.CoℂModule.SL2CRep_dual_dualBasis, map_sum]
  refine Finset.sum_congr rfl fun ν _ => ?_
  rw [map_smul, basis_singleton]

/-!

### B.6. The derivative-degree scaling

-/

/-- The derivative-degree scaling on the algebra of derivative symbols: the
  algebra map multiplying each generator by `t`, hence each degree-`n` monomial
  by `t ^ n`. -/
noncomputable def gradeScale (t : ℂ) : DerivAlgebraComplex →ₐ[ℂ] DerivAlgebraComplex :=
  SymmetricAlgebra.lift (t • SymmetricAlgebra.ι ℂ (Module.Dual ℂ Lorentz.CoℂModule))

@[simp]
lemma gradeScale_ι (t : ℂ) (x : Module.Dual ℂ Lorentz.CoℂModule) :
    gradeScale t (SymmetricAlgebra.ι ℂ (Module.Dual ℂ Lorentz.CoℂModule) x) =
      t • SymmetricAlgebra.ι ℂ (Module.Dual ℂ Lorentz.CoℂModule) x := by
  rw [gradeScale, SymmetricAlgebra.lift_ι_apply]
  rfl

/-- The degree scaling multiplies the basis monomial at `s` by `t ^ |s|`. -/
lemma gradeScale_basis (t : ℂ) (s : Multiset (Fin 1 ⊕ Fin 3)) :
    gradeScale t (basis s) = t ^ s.card • basis s := by
  induction s using Multiset.induction_on with
  | empty =>
    rw [show basis (0 : Multiset (Fin 1 ⊕ Fin 3)) = 1 from basis_nil, map_one]
    simp
  | cons a s ih =>
    rw [← Multiset.singleton_add, ← basis_mul, map_mul, ih, basis_singleton,
      gradeScale_ι, smul_mul_smul_comm, ← _root_.pow_succ', ← basis_singleton,
      basis_mul, Multiset.singleton_add, Multiset.card_cons]

/-- The degree scaling commutes with the Lorentz action: the Lorentz action
  preserves the derivative degree. -/
lemma gradeScale_repLorentzGroup (t : ℂ) (Λ : SL(2,ℂ)) (a : DerivAlgebraComplex) :
    gradeScale t (repLorentzGroup Λ a) = repLorentzGroup Λ (gradeScale t a) := by
  have h : (gradeScale t).comp (SymmetricAlgebra.lift
      (SymmetricAlgebra.ι ℂ _ ∘ₗ Lorentz.CoℂModule.SL2CRep.dual Λ)) =
      (SymmetricAlgebra.lift
        (SymmetricAlgebra.ι ℂ _ ∘ₗ Lorentz.CoℂModule.SL2CRep.dual Λ)).comp
        (gradeScale t) := by
    refine SymmetricAlgebra.algHom_ext (LinearMap.ext fun x => ?_)
    simp
  exact DFunLike.congr_fun h a

/-!

### B.7. The derivative-degree polynomial

The degree scaling of the previous section records the derivative degree in a scalar. The
same construction with the scalar replaced by a formal variable records it in a polynomial:
`gradePoly` is the linear map sending the basis monomial `∂_s` to `X ^ |s| ∂_s`, so the
coefficient of `X ^ n` in `gradePoly a` is the part of `a` of derivative degree `n`.

-/

/-- The derivative-degree polynomial on the algebra of derivative symbols: the linear map
  sending the basis monomial `∂_s` to `X ^ |s|` times itself. It is `gradeScale` with the
  scalar replaced by the formal variable `X`. -/
noncomputable def gradePoly : DerivAlgebraComplex →ₗ[ℂ] Polynomial DerivAlgebraComplex :=
  basis.constr ℂ fun s => Polynomial.monomial (Multiset.card s) (basis s)

/-- The derivative-degree polynomial of a basis monomial is the monomial of degree `|s|`. -/
@[simp]
lemma gradePoly_basis (s : Multiset (Fin 1 ⊕ Fin 3)) :
    gradePoly (basis s) = Polynomial.monomial (Multiset.card s) (basis s) := by
  rw [gradePoly, Module.Basis.constr_basis]

/-- Evaluating the derivative-degree polynomial at a scalar is the derivative-degree
  scaling by that scalar: the two descriptions of the grading agree. -/
lemma eval_algebraMap_gradePoly (t : ℂ) (a : DerivAlgebraComplex) :
    (gradePoly a).eval (algebraMap ℂ DerivAlgebraComplex t) = gradeScale t a := by
  have h : (Polynomial.eval₂AlgHom (AlgHom.id ℂ DerivAlgebraComplex)
      (algebraMap ℂ DerivAlgebraComplex t)
      (fun b => (Algebra.commutes t b).symm)).toLinearMap ∘ₗ gradePoly =
      (gradeScale t).toLinearMap := by
    refine basis.ext fun s => ?_
    simp only [LinearMap.coe_comp, Function.comp_apply, gradePoly_basis,
      AlgHom.toLinearMap_apply, gradeScale_basis]
    show (Polynomial.monomial (Multiset.card s) (basis s)).eval
      (algebraMap ℂ DerivAlgebraComplex t) = _
    rw [Polynomial.eval_monomial, ← map_pow, ← Algebra.commutes, ← Algebra.smul_def]
  exact LinearMap.congr_fun h a

/-- Setting the formal variable to one recovers the original element: the pieces of a
  graded decomposition sum to the element. -/
lemma gradePoly_eval_one (a : DerivAlgebraComplex) : (gradePoly a).eval 1 = a := by
  have h := eval_algebraMap_gradePoly 1 a
  rw [map_one] at h
  rw [h, gradeScale, show (1 : ℂ) • SymmetricAlgebra.ι ℂ (Module.Dual ℂ Lorentz.CoℂModule)
    = SymmetricAlgebra.ι ℂ (Module.Dual ℂ Lorentz.CoℂModule) from one_smul _ _,
    SymmetricAlgebra.lift_ι, AlgHom.id_apply]

end DerivAlgebraComplex


/-!

## C. The real derivative algebra

-/

abbrev DerivAlgebraReal := SymmetricAlgebra ℝ (Module.Dual ℝ Lorentz.CoVector)

namespace DerivAlgebraReal
open Matrix MatrixGroups

/-- The representation of the Lorentz group on the real Lorentz-covector derivative
  slots, obtained from the real Lorentz-vector representation through the covering
  map `SL(2,ℂ) →* LorentzGroup 3`. -/
noncomputable def _root_.Lorentz.CoVector.sl2Rep : Representation ℝ SL(2,ℂ) Lorentz.CoVector :=
  MonoidHom.comp Lorentz.CoVector.rep Lorentz.SL2C.toLorentzGroup


/-- The representation of the Lorentz group `SL(2,ℂ)` on the algebra of derivative
  symbols, extending the dual covector representation multiplicatively. -/
noncomputable def repLorentzGroup : Representation ℝ SL(2,ℂ) DerivAlgebraReal where
  toFun Λ := (SymmetricAlgebra.lift
    (SymmetricAlgebra.ι ℝ _ ∘ₗ Lorentz.CoVector.sl2Rep.dual Λ)).toLinearMap
  map_one' := by
    suffices h : SymmetricAlgebra.lift
        (SymmetricAlgebra.ι ℝ _ ∘ₗ Lorentz.CoVector.sl2Rep.dual 1) =
        AlgHom.id ℝ (SymmetricAlgebra ℝ (Module.Dual ℝ Lorentz.CoVector)) by
      rw [h]; rfl
    refine SymmetricAlgebra.algHom_ext (LinearMap.ext fun x => ?_)
    simp
    rfl
  map_mul' Λ1 Λ2 := by
    suffices h : SymmetricAlgebra.lift
        (SymmetricAlgebra.ι ℝ _ ∘ₗ Lorentz.CoVector.sl2Rep.dual (Λ1 * Λ2)) =
        (SymmetricAlgebra.lift
          (SymmetricAlgebra.ι ℝ _ ∘ₗ Lorentz.CoVector.sl2Rep.dual Λ1)).comp
        (SymmetricAlgebra.lift
          (SymmetricAlgebra.ι ℝ _ ∘ₗ Lorentz.CoVector.sl2Rep.dual Λ2)) by
      rw [h]; rfl
    refine SymmetricAlgebra.algHom_ext (LinearMap.ext fun x => ?_)
    simp [map_mul, Module.End.mul_apply]

/-- The Lorentz action on a generator of the real derivative algebra. -/
@[simp]
lemma repLorentzGroup_apply_ι (Λ : SL(2,ℂ)) (x : Module.Dual ℝ Lorentz.CoVector) :
    repLorentzGroup Λ (SymmetricAlgebra.ι ℝ (Module.Dual ℝ Lorentz.CoVector) x) =
      SymmetricAlgebra.ι ℝ (Module.Dual ℝ Lorentz.CoVector)
        (Lorentz.CoVector.sl2Rep.dual Λ x) := by
  simp [repLorentzGroup]

/-- The real derivative-algebra representation is multiplicative: it is the lift of a linear
  map to the symmetric algebra. -/
lemma repLorentzGroup_apply_mul (Λ : SL(2,ℂ))
    (a b : DerivAlgebraReal) :
    DerivAlgebraReal.repLorentzGroup Λ (a * b) =
      DerivAlgebraReal.repLorentzGroup Λ a * DerivAlgebraReal.repLorentzGroup Λ b := by
  simp [DerivAlgebraReal.repLorentzGroup]

@[simp]
lemma repLorentzGroup_apply_one (Λ : SL(2,ℂ)) :
    DerivAlgebraReal.repLorentzGroup Λ 1 = 1 := by
  simp [DerivAlgebraReal.repLorentzGroup]

/-- The components of the dual covector action on the dual basis: the dual
  derivative slots transform contravariantly, by the columns of the Lorentz
  matrix. -/
lemma _root_.Lorentz.CoVector.sl2Rep_dual_dualBasis (Λ : SL(2,ℂ)) (μ : Fin 1 ⊕ Fin 3) :
    Lorentz.CoVector.sl2Rep.dual Λ (Lorentz.CoVector.basis.dualBasis μ) =
      ∑ j, (Lorentz.SL2C.toLorentzGroup Λ).1 j μ •
        Lorentz.CoVector.basis.dualBasis j := by
  refine Representation.dual_apply_dualBasis _ _ _ _
    (Matrix.of fun l j => (Lorentz.SL2C.toLorentzGroup Λ).1 j l) (fun j => ?_)
  rw [show Lorentz.CoVector.sl2Rep Λ⁻¹ =
      Lorentz.CoVector.rep (Lorentz.SL2C.toLorentzGroup Λ⁻¹) from rfl,
    Lorentz.CoVector.rep_apply_basis, ← LorentzGroup.coe_inv, map_inv, inv_inv]
  rfl

/-- The derivative-degree scaling on the real algebra of derivative symbols:
  the algebra map multiplying each generator by `t`. -/
noncomputable def gradeScale (t : ℝ) : DerivAlgebraReal →ₐ[ℝ] DerivAlgebraReal :=
  SymmetricAlgebra.lift (t • SymmetricAlgebra.ι ℝ (Module.Dual ℝ Lorentz.CoVector))

@[simp]
lemma gradeScale_ι (t : ℝ) (x : Module.Dual ℝ Lorentz.CoVector) :
    gradeScale t (SymmetricAlgebra.ι ℝ (Module.Dual ℝ Lorentz.CoVector) x) =
      t • SymmetricAlgebra.ι ℝ (Module.Dual ℝ Lorentz.CoVector) x := by
  rw [gradeScale, SymmetricAlgebra.lift_ι_apply]
  rfl

/-- The degree scaling commutes with the Lorentz action on the real derivative
  symbols. -/
lemma gradeScale_repLorentzGroup (t : ℝ) (Λ : SL(2,ℂ)) (a : DerivAlgebraReal) :
    gradeScale t (repLorentzGroup Λ a) = repLorentzGroup Λ (gradeScale t a) := by
  have h : (gradeScale t).comp (SymmetricAlgebra.lift
      (SymmetricAlgebra.ι ℝ _ ∘ₗ Lorentz.CoVector.sl2Rep.dual Λ)) =
      (SymmetricAlgebra.lift
        (SymmetricAlgebra.ι ℝ _ ∘ₗ Lorentz.CoVector.sl2Rep.dual Λ)).comp
        (gradeScale t) := by
    refine SymmetricAlgebra.algHom_ext (LinearMap.ext fun x => ?_)
    simp
  exact DFunLike.congr_fun h a

/-!

## The multiset basis of `DerivAlgebraReal`

-/

open Module

/-- The basis of the symmetric algebra of dual real jet slots, indexed by multisets of
  spacetime indices. -/
noncomputable def basisMultiset :
    Basis (Multiset (Fin 1 ⊕ Fin 3)) ℝ (SymmetricAlgebra ℝ (Module.Dual ℝ Lorentz.CoVector)) :=
  Lorentz.CoVector.basis.dualBasis.symmetricAlgebra.reindex Multiset.toFinsupp.toEquiv.symm

/-- The multiset basis of the dual derivative symbols, as a basis vector of the
  symmetric algebra at the corresponding multi-index. -/
lemma basisMultiset_apply (s : Multiset (Fin 1 ⊕ Fin 3)) :
    basisMultiset s =
      Lorentz.CoVector.basis.dualBasis.symmetricAlgebra (Multiset.toFinsupp s) := by
  rw [basisMultiset, Basis.reindex_apply, Equiv.symm_symm]
  rfl

/-- The multiset basis vectors of the real dual derivative slots multiply by adding the
  multisets. -/
lemma basisMultiset_mul (s t : Multiset (Fin 1 ⊕ Fin 3)) :
    basisMultiset s * basisMultiset t =
      basisMultiset (s + t) := by
  rw [basisMultiset_apply, basisMultiset_apply,
    basisMultiset_apply, map_add]
  simp only [Basis.symmetricAlgebra, Basis.map_apply,
    show ∀ p, (SymmetricAlgebra.equivMvPolynomial
        Lorentz.CoVector.basis.dualBasis).symm.toLinearEquiv p =
      (SymmetricAlgebra.equivMvPolynomial Lorentz.CoVector.basis.dualBasis).symm p
      from fun _ => rfl,
    ← map_mul, MvPolynomial.coe_basisMonomials]
  simp only [MvPolynomial.monomial_mul, mul_one]

/-- The multiset basis of the real dual derivative slots at the empty multiset is the
  unit. -/
lemma basisMultiset_nil :
    basisMultiset (0 : Multiset (Fin 1 ⊕ Fin 3)) = 1 := by
  rw [basisMultiset_apply,
    show Multiset.toFinsupp (0 : Multiset (Fin 1 ⊕ Fin 3)) = 0 by simp,
    Basis.symmetricAlgebra, Basis.map_apply,
    show (SymmetricAlgebra.equivMvPolynomial
        Lorentz.CoVector.basis.dualBasis).symm.toLinearEquiv
        ((MvPolynomial.basisMonomials (Fin 1 ⊕ Fin 3) ℝ) 0) =
      (SymmetricAlgebra.equivMvPolynomial Lorentz.CoVector.basis.dualBasis).symm
        ((MvPolynomial.basisMonomials (Fin 1 ⊕ Fin 3) ℝ) 0) from rfl,
    show (MvPolynomial.basisMonomials (Fin 1 ⊕ Fin 3) ℝ) (0 : (Fin 1 ⊕ Fin 3) →₀ ℕ)
        = 1 from by
      rw [MvPolynomial.coe_basisMonomials]
      show MvPolynomial.monomial 0 1 = 1
      rw [MvPolynomial.monomial_zero', MvPolynomial.C_1],
    map_one]

/-- The multiset basis of the real dual derivative slots at a singleton index. -/
lemma basisMultiset_singleton (μ : Fin 1 ⊕ Fin 3) :
    basisMultiset ({μ} : Multiset (Fin 1 ⊕ Fin 3)) =
      SymmetricAlgebra.ι ℝ (Module.Dual ℝ Lorentz.CoVector)
        (Lorentz.CoVector.basis.dualBasis μ) := by
  have h : (MvPolynomial.basisMonomials (Fin 1 ⊕ Fin 3) ℝ) (Finsupp.single μ 1) =
      MvPolynomial.X μ := rfl
  rw [basisMultiset, Basis.reindex_apply, Equiv.symm_symm,
    show Multiset.toFinsupp.toEquiv ({μ} : Multiset (Fin 1 ⊕ Fin 3)) =
      Finsupp.single μ 1 by simp,
    Basis.symmetricAlgebra, Basis.map_apply, h]
  simp

/-!

## The derivative-degree polynomial on the real derivative algebra

-/

/-- The degree scaling multiplies the real basis monomial at `s` by `t ^ |s|`. -/
lemma gradeScale_basisMultiset (t : ℝ) (s : Multiset (Fin 1 ⊕ Fin 3)) :
    gradeScale t (basisMultiset s) = t ^ Multiset.card s • basisMultiset s := by
  induction s using Multiset.induction_on with
  | empty =>
    rw [show basisMultiset (0 : Multiset (Fin 1 ⊕ Fin 3)) = 1 from basisMultiset_nil, map_one]
    simp
  | cons a s ih =>
    rw [← Multiset.singleton_add, ← basisMultiset_mul, map_mul, ih, basisMultiset_singleton,
      gradeScale_ι, smul_mul_smul_comm, ← _root_.pow_succ', ← basisMultiset_singleton,
      basisMultiset_mul, Multiset.singleton_add, Multiset.card_cons]

/-- The derivative-degree polynomial on the real algebra of derivative symbols: the linear
  map sending the basis monomial `∂_s` to `X ^ |s|` times itself. -/
noncomputable def gradePoly : DerivAlgebraReal →ₗ[ℝ] Polynomial DerivAlgebraReal :=
  basisMultiset.constr ℝ fun s => Polynomial.monomial (Multiset.card s) (basisMultiset s)

/-- The derivative-degree polynomial of a real basis monomial is the monomial of degree
  `|s|`. -/
@[simp]
lemma gradePoly_basisMultiset (s : Multiset (Fin 1 ⊕ Fin 3)) :
    gradePoly (basisMultiset s) =
      Polynomial.monomial (Multiset.card s) (basisMultiset s) := by
  rw [gradePoly, Module.Basis.constr_basis]

/-- Evaluating the real derivative-degree polynomial at a scalar is the derivative-degree
  scaling by that scalar. -/
lemma eval_algebraMap_gradePoly (t : ℝ) (a : DerivAlgebraReal) :
    (gradePoly a).eval (algebraMap ℝ DerivAlgebraReal t) = gradeScale t a := by
  have h : (Polynomial.eval₂AlgHom (AlgHom.id ℝ DerivAlgebraReal)
      (algebraMap ℝ DerivAlgebraReal t)
      (fun b => (Algebra.commutes t b).symm)).toLinearMap ∘ₗ gradePoly =
      (gradeScale t).toLinearMap := by
    refine basisMultiset.ext fun s => ?_
    simp only [LinearMap.coe_comp, Function.comp_apply, gradePoly_basisMultiset,
      AlgHom.toLinearMap_apply, gradeScale_basisMultiset]
    show (Polynomial.monomial (Multiset.card s) (basisMultiset s)).eval
      (algebraMap ℝ DerivAlgebraReal t) = _
    rw [Polynomial.eval_monomial, ← map_pow, ← Algebra.commutes, ← Algebra.smul_def]
  exact LinearMap.congr_fun h a

/-- Setting the formal variable to one recovers the original element of the real
  derivative algebra. -/
lemma gradePoly_eval_one (a : DerivAlgebraReal) : (gradePoly a).eval 1 = a := by
  have h := eval_algebraMap_gradePoly 1 a
  rw [map_one] at h
  rw [h, gradeScale, show (1 : ℝ) • SymmetricAlgebra.ι ℝ (Module.Dual ℝ Lorentz.CoVector)
    = SymmetricAlgebra.ι ℝ (Module.Dual ℝ Lorentz.CoVector) from one_smul _ _,
    SymmetricAlgebra.lift_ι, AlgHom.id_apply]

end DerivAlgebraReal
