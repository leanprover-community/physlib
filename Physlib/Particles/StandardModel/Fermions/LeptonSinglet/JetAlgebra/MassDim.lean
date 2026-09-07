/-
Copyright (c) 2026 Nathaneal Sajan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathaneal Sajan
-/
module

public import Physlib.Particles.StandardModel.Fermions.LeptonSinglet.JetAlgebra.GaugeAction
public import Physlib.Particles.StandardModel.Fermions.LeptonSinglet.JetAlgebra.LorentzAction
public import Physlib.Particles.StandardModel.Fermions.LeptonSinglet.JetAlgebra.JetDeriv
public import Physlib.Mathematics.PolynomialEval
/-!
# Mass dimension on the charged-lepton jet algebra

## i. Overview

*Note*: In this file we use the notion 'mass weight'. The idea being that the
'mass weight' is twice the mass dimension. This is because it is easier to work
exclusively with integers, and the mass dimension of the fermion fields is 3/2.

The mass-weight polynomial records the mass weight of each homogeneous piece of
an element of the jet algebra in a formal variable. It gives the mass-weight
grading of the jet algebra, and its coefficientwise behaviour under the total
derivative shows that a derivative raises the mass weight by two.

## ii. Key results

- `JetAlgebra.massWeightPoly` : the mass-weight polynomial.
- `JetAlgebra.jetDeriv_massWeightPoly_coeff` : a derivative raises the mass weight by two.
- `JetAlgebra.massWeightSubmodule` : the submodule of elements of a given mass weight.
- `JetAlgebra.massWeightSubmodule_isInternal` : the mass-weight decomposition is direct.
- `JetAlgebra.massWeightScale` : the mass-dimension scaling.

## iii. Table of contents

- A. The mass-weight polynomial and the mass-weight grading
- B. The mass-weight scaling on the jet algebra

-/

@[expose] public section

namespace StandardModel

namespace LeptonSinglet

namespace JetAlgebra

open Matrix MatrixGroups LagrangianTheory

/-!

## A. The mass-weight polynomial and the mass-weight grading

-/


/-- The mass-weight polynomial on the charged-lepton factor: the `ℂ`-algebra map
  sending each generator `j` to `X ^ w * j`, where `w` is the mass weight of `j`.
  It is `LeptonSinglet.JetAlgebra.massWeightScale` with the scalar `c` replaced by
  the formal variable `X`. -/
noncomputable def massWeightPoly : JetAlgebra →ₐ[ℂ] Polynomial JetAlgebra :=
  ExteriorAlgebra.lift ℂ
    ⟨JetComponentSpace.basis.constr ℂ fun j =>
      Polynomial.monomial j.massWeight (ofGenerator j), by
      set f := JetComponentSpace.basis.constr ℂ fun j =>
        Polynomial.monomial j.massWeight (ofGenerator j) with hf
      set B := (LinearMap.mul ℂ (Polynomial JetAlgebra)).compl₁₂ f f with hBdef
      have hB : B + B.flip = 0 :=
        LinearMap.ext_basis JetComponentSpace.basis JetComponentSpace.basis fun j k => by
          simp only [hBdef, LinearMap.add_apply, LinearMap.compl₁₂_apply, LinearMap.flip_apply,
            LinearMap.mul_apply', LinearMap.zero_apply, hf, Module.Basis.constr_basis,
            ofGenerator, Polynomial.monomial_mul_monomial,
            Nat.add_comm k.massWeight j.massWeight, ← map_add,
            ExteriorAlgebra.ι_add_mul_swap, map_zero]
      intro v
      have h2 : (2 : ℂ) • (f v * f v) = 0 := by
        rw [two_smul]
        exact LinearMap.congr_fun (LinearMap.congr_fun hB v) v
      simpa [smul_smul] using congrArg (fun y => (2⁻¹ : ℂ) • y) h2⟩

/-- Setting the formal variable to one recovers the original element. -/
lemma massWeightPoly_eval_one (x : JetAlgebra) :
    (massWeightPoly x).eval 1 = x := by
  have h : (Polynomial.eval₂AlgHom (AlgHom.id ℂ JetAlgebra) 1
      fun a => Commute.one_right a).comp massWeightPoly = AlgHom.id ℂ JetAlgebra := by
    refine ExteriorAlgebra.hom_ext (Module.Basis.ext JetComponentSpace.basis fun j => ?_)
    simp [massWeightPoly, ofGenerator]
    change Polynomial.eval₂ (RingHom.id _) 1
      (Polynomial.monomial j.massWeight (ExteriorAlgebra.ι ℂ (JetComponentSpace.basis j))) = _
    rw [Polynomial.eval₂_id]
    simp
  exact AlgHom.congr_fun h x

lemma eq_sum_massWeightPoly_coeff (x : JetAlgebra) :
    x = ∑ n ∈ Polynomial.support (massWeightPoly x), (massWeightPoly x).coeff n := by
  conv_lhs => rw [← massWeightPoly_eval_one x]
  rw [Polynomial.eval_eq_sum, Polynomial.sum_def]
  simp

/-- Each generator is sent to `j * X ^ w`, where `w` is its mass weight. -/
lemma massWeightPoly_ofGenerator (j : JetGenerators) :
    massWeightPoly (ofGenerator j) = Polynomial.monomial j.massWeight (ofGenerator j) := by
  rw [massWeightPoly, ofGenerator, ExteriorAlgebra.lift_ι_apply, Module.Basis.constr_basis]
  rfl

/-- `massWeightPoly` is injective, however, it is not surjective. -/
lemma massWeightPoly_injective : Function.Injective massWeightPoly := by
  intro x y h
  rw [← massWeightPoly_eval_one x, ← massWeightPoly_eval_one y]
  simp [h]

/-- The total derivative of a linear generator: `massWeightPoly (∂_μ (ι v))` is
  `X ^ 2` times a polynomial whose coefficients are the total derivatives of the
  coefficients of `massWeightPoly (ι v)`. -/
lemma exists_massWeightPoly_jetDeriv_ι (μ : Fin 1 ⊕ Fin 3) (v : JetComponentSpace) :
    ∃ q : Polynomial JetAlgebra,
      massWeightPoly (jetDeriv μ (ExteriorAlgebra.ι ℂ v)) = Polynomial.X ^ 2 * q ∧
      ∀ n, q.coeff n =
        jetDeriv μ ((massWeightPoly (ExteriorAlgebra.ι ℂ v)).coeff n) := by
  have hv : v ∈ Submodule.span ℂ (Set.range JetComponentSpace.basis) := by
    rw [JetComponentSpace.basis.span_eq]
    trivial
  induction hv using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨j, rfl⟩ := hy
    refine ⟨Polynomial.monomial j.massWeight (ofGenerator (JetGenerators.shift μ j)), ?_,
      fun n => ?_⟩
    · rw [show ExteriorAlgebra.ι ℂ (JetComponentSpace.basis j) = ofGenerator j from rfl,
        jetDeriv_ofGenerator, massWeightPoly_ofGenerator, JetGenerators.massWeight_shift,
        Polynomial.X_pow_eq_monomial, Polynomial.monomial_mul_monomial, one_mul,
        Nat.add_comm 2 j.massWeight]
    · rw [show ExteriorAlgebra.ι ℂ (JetComponentSpace.basis j) = ofGenerator j from rfl,
        massWeightPoly_ofGenerator, Polynomial.coeff_monomial, Polynomial.coeff_monomial]
      split_ifs with h
      · rw [jetDeriv_ofGenerator]
      · rw [map_zero]
  | zero => exact ⟨0, by simp, fun n => by simp⟩
  | add y z _ _ hy hz =>
    obtain ⟨qy, hqy, cy⟩ := hy
    obtain ⟨qz, hqz, cz⟩ := hz
    refine ⟨qy + qz, ?_, fun n => ?_⟩
    · simp only [map_add, hqy, hqz, mul_add]
    · simp only [map_add, Polynomial.coeff_add, cy, cz]
  | smul c y _ hy =>
    obtain ⟨qy, hqy, cy⟩ := hy
    refine ⟨c • qy, ?_, fun n => ?_⟩
    · simp only [map_smul, hqy, mul_smul_comm]
    · simp only [map_smul, Polynomial.coeff_smul, cy]

/-- Rearrangement used for the Leibniz step: `X ^ 2` is central, so it can be
  pulled out of a Leibniz combination. -/
private lemma X_sq_mul_leibniz {R : Type} [Semiring R] (p q r s : Polynomial R) :
    Polynomial.X ^ 2 * p * q + r * (Polynomial.X ^ 2 * s) =
      Polynomial.X ^ 2 * (p * q + r * s) := by
  rw [mul_add, mul_assoc, ← mul_assoc r, ← Polynomial.X_pow_mul, mul_assoc]

/-- The polynomial half of the Leibniz step: the mass-weight polynomial of
  `∂_μ (a * b)` is `X ^ 2` times the Leibniz combination. -/
lemma massWeightPoly_jetDeriv_mul (μ : Fin 1 ⊕ Fin 3) {a b : JetAlgebra}
    {qa qb : Polynomial JetAlgebra}
    (hqa : massWeightPoly (jetDeriv μ a) = Polynomial.X ^ 2 * qa)
    (hqb : massWeightPoly (jetDeriv μ b) = Polynomial.X ^ 2 * qb) :
    massWeightPoly (jetDeriv μ (a * b)) =
      Polynomial.X ^ 2 * (qa * massWeightPoly b + massWeightPoly a * qb) := by
  rw [jetDeriv_mul, map_add massWeightPoly, map_mul massWeightPoly, map_mul massWeightPoly,
    hqa, hqb, X_sq_mul_leibniz]

/-- The coefficient half of the Leibniz step: the coefficients of the Leibniz
  combination are the total derivatives of the coefficients of `a * b`. -/
lemma coeff_mul_jetDeriv (μ : Fin 1 ⊕ Fin 3) {a b : JetAlgebra}
    {qa qb : Polynomial JetAlgebra}
    (ca : ∀ n, qa.coeff n = jetDeriv μ ((massWeightPoly a).coeff n))
    (cb : ∀ n, qb.coeff n = jetDeriv μ ((massWeightPoly b).coeff n)) (n : ℕ) :
    (qa * massWeightPoly b + massWeightPoly a * qb).coeff n =
      jetDeriv μ ((massWeightPoly (a * b)).coeff n) := by
  rw [Polynomial.coeff_add, Polynomial.coeff_mul, Polynomial.coeff_mul,
    ← Finset.sum_add_distrib, map_mul massWeightPoly, Polynomial.coeff_mul,
    map_sum (jetDeriv μ)]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [jetDeriv_mul, ca, cb]

/-- The Leibniz rule propagates the shift: if the mass-weight polynomials of the
  total derivatives of `a` and `b` are `X ^ 2` times the coefficientwise total
  derivatives, then so is that of `a * b`. -/
lemma exists_massWeightPoly_jetDeriv_mul (μ : Fin 1 ⊕ Fin 3) {a b : JetAlgebra}
    {qa qb : Polynomial JetAlgebra}
    (hqa : massWeightPoly (jetDeriv μ a) = Polynomial.X ^ 2 * qa)
    (ca : ∀ n, qa.coeff n = jetDeriv μ ((massWeightPoly a).coeff n))
    (hqb : massWeightPoly (jetDeriv μ b) = Polynomial.X ^ 2 * qb)
    (cb : ∀ n, qb.coeff n = jetDeriv μ ((massWeightPoly b).coeff n)) :
    ∃ q : Polynomial JetAlgebra, massWeightPoly (jetDeriv μ (a * b)) = Polynomial.X ^ 2 * q ∧
      ∀ n, q.coeff n = jetDeriv μ ((massWeightPoly (a * b)).coeff n) :=
  ⟨qa * massWeightPoly b + massWeightPoly a * qb,
    massWeightPoly_jetDeriv_mul μ hqa hqb, coeff_mul_jetDeriv μ ca cb⟩

/-- The mass-weight polynomial of a total derivative is `X ^ 2` times a polynomial
  whose coefficients are the total derivatives of the coefficients: the total
  derivative raises the mass weight by two. -/
lemma exists_massWeightPoly_jetDeriv (μ : Fin 1 ⊕ Fin 3) (x : JetAlgebra) :
    ∃ q : Polynomial JetAlgebra, massWeightPoly (jetDeriv μ x) = Polynomial.X ^ 2 * q ∧
      ∀ n, q.coeff n = jetDeriv μ ((massWeightPoly x).coeff n) := by
  induction x using ExteriorAlgebra.induction with
  | algebraMap r =>
    have hr : jetDeriv μ (algebraMap ℂ JetAlgebra r) = 0 := by
      rw [Algebra.algebraMap_eq_smul_one, map_smul (jetDeriv μ), jetDeriv_one, smul_zero]
    refine ⟨0, ?_, fun n => ?_⟩
    · rw [hr, map_zero massWeightPoly, mul_zero]
    · rw [Polynomial.coeff_zero, AlgHom.commutes, Polynomial.algebraMap_apply,
        Polynomial.coeff_C]
      split_ifs with h
      · rw [hr]
      · rw [map_zero (jetDeriv μ)]
  | ι v => exact exists_massWeightPoly_jetDeriv_ι μ v
  | mul a b ha hb =>
    obtain ⟨qa, hqa, ca⟩ := ha
    obtain ⟨qb, hqb, cb⟩ := hb
    exact exists_massWeightPoly_jetDeriv_mul μ hqa ca hqb cb
  | add a b ha hb =>
    obtain ⟨qa, hqa, ca⟩ := ha
    obtain ⟨qb, hqb, cb⟩ := hb
    refine ⟨qa + qb, ?_, fun n => ?_⟩
    · simp only [map_add, hqa, hqb, mul_add]
    · simp only [map_add, Polynomial.coeff_add, ca, cb]

/-- The total derivative raises the mass weight by two: it takes the part of `x` of
  mass weight `n` to the part of `∂_μ x` of mass weight `n + 2`. -/
lemma jetDeriv_massWeightPoly_coeff (μ : Fin 1 ⊕ Fin 3) (x : JetAlgebra) (n : ℕ) :
    jetDeriv μ ((massWeightPoly x).coeff n) = (massWeightPoly (jetDeriv μ x)).coeff (n + 2) := by
  obtain ⟨q, hq, hc⟩ := exists_massWeightPoly_jetDeriv μ x
  rw [hq, Polynomial.coeff_X_pow_mul, hc]


/-- The coefficients of the mass-weight polynomial of a linear generator are
  homogeneous: each basis vector is homogeneous, and a general vector is a
  combination of basis vectors. -/
lemma massWeightPoly_coeff_massWeightPoly_ι (n : ℕ) (v : JetComponentSpace) :
    massWeightPoly ((massWeightPoly (ExteriorAlgebra.ι ℂ v)).coeff n) =
      Polynomial.monomial n ((massWeightPoly (ExteriorAlgebra.ι ℂ v)).coeff n) := by
  have hv : v ∈ Submodule.span ℂ (Set.range JetComponentSpace.basis) := by
    rw [JetComponentSpace.basis.span_eq]
    trivial
  induction hv using Submodule.span_induction generalizing n with
  | mem y hy =>
    obtain ⟨j, rfl⟩ := hy
    rw [show ExteriorAlgebra.ι ℂ (JetComponentSpace.basis j) = ofGenerator j from rfl,
      massWeightPoly_ofGenerator, Polynomial.coeff_monomial]
    split_ifs with h
    · rw [← h, massWeightPoly_ofGenerator]
    · simp only [map_zero]
  | zero => simp only [map_zero, Polynomial.coeff_zero]
  | add y z _ _ hy hz =>
    simp only [map_add, Polynomial.coeff_add]
    rw [hy n, hz n]
  | smul c y _ hy =>
    simp only [map_smul, Polynomial.coeff_smul]
    rw [hy n, Polynomial.smul_monomial]

/-- Homogeneity of the coefficients is inherited by products: the `n`-th coefficient
  of a product is a sum of products of coefficients of complementary degrees. -/
lemma massWeightPoly_coeff_massWeightPoly_mul {a b : JetAlgebra}
    (ha : ∀ n, massWeightPoly ((massWeightPoly a).coeff n) =
      Polynomial.monomial n ((massWeightPoly a).coeff n))
    (hb : ∀ n, massWeightPoly ((massWeightPoly b).coeff n) =
      Polynomial.monomial n ((massWeightPoly b).coeff n)) (n : ℕ) :
    massWeightPoly ((massWeightPoly (a * b)).coeff n) =
      Polynomial.monomial n ((massWeightPoly (a * b)).coeff n) := by
  rw [map_mul massWeightPoly a b, Polynomial.coeff_mul, map_sum massWeightPoly,
    map_sum (Polynomial.monomial n)]
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [Finset.mem_antidiagonal] at hp
  subst hp
  rw [map_mul massWeightPoly, ha p.1, hb p.2, Polynomial.monomial_mul_monomial]

/-- The coefficients of a mass-weight polynomial are homogeneous: the coefficient of
  `X ^ n` in `massWeightPoly x` is sent by `massWeightPoly` to `X ^ n` times itself.

  This fails for a general `p : Polynomial JetAlgebra` in place of `massWeightPoly x`:
  for `p = Polynomial.monomial 5 1` it would say `1 = X ^ 5`. -/
lemma massWeightPoly_coeff_massWeightPoly (n : ℕ) (x : JetAlgebra) :
    massWeightPoly ((massWeightPoly x).coeff n) =
      Polynomial.monomial n ((massWeightPoly x).coeff n) := by
  induction x using ExteriorAlgebra.induction generalizing n with
  | algebraMap r =>
    rw [AlgHom.commutes, Polynomial.algebraMap_apply, Polynomial.coeff_C]
    split_ifs with h
    · subst h
      rw [AlgHom.commutes, Polynomial.algebraMap_apply, Polynomial.monomial_zero_left]
    · simp only [map_zero]
  | ι v => exact massWeightPoly_coeff_massWeightPoly_ι n v
  | mul a b ha hb => exact massWeightPoly_coeff_massWeightPoly_mul ha hb n
  | add a b ha hb =>
    rw [map_add massWeightPoly a b, Polynomial.coeff_add, map_add massWeightPoly, ha n, hb n]
    exact (map_add (Polynomial.monomial n) _ _).symm


/-- The submodule of elements of mass weight `n`: those `x` whose mass-weight
  polynomial is `x * X ^ n`. -/
def massWeightSubmodule (n : ℕ) : Submodule ℂ JetAlgebra where
  carrier := {x | massWeightPoly x = Polynomial.monomial n x}
  add_mem' {a b} ha hb := by
    simp only [Set.mem_setOf_eq, map_add] at ha hb ⊢
    rw [ha, hb]
  zero_mem' := by simp
  smul_mem' c x hx := by
    simp only [Set.mem_setOf_eq, map_smul] at hx ⊢
    rw [hx, Polynomial.smul_monomial]

@[simp]
lemma mem_massWeightSubmodule {n : ℕ} {x : JetAlgebra} :
    x ∈ massWeightSubmodule n ↔ massWeightPoly x = Polynomial.monomial n x := Iff.rfl

/-- The generator `j` has mass weight `j.massWeight`. -/
lemma ofGenerator_mem_massWeightSubmodule (j : JetGenerators) :
    ofGenerator j ∈ massWeightSubmodule j.massWeight :=
  massWeightPoly_ofGenerator j

/-- Mass weights add under multiplication, and `1` has mass weight zero. -/
instance : SetLike.GradedMonoid massWeightSubmodule where
  one_mem := by simp
  mul_mem {m n x y} hx hy := by
    simp only [mem_massWeightSubmodule, map_mul] at hx hy ⊢
    rw [hx, hy, Polynomial.monomial_mul_monomial]

/-- The coefficient of `X ^ n` in the mass-weight polynomial of `x` has mass
  weight `n`. -/
lemma coeff_massWeightPoly_mem_massWeightSubmodule (n : ℕ) (x : JetAlgebra) :
    (massWeightPoly x).coeff n ∈ massWeightSubmodule n :=
  massWeightPoly_coeff_massWeightPoly n x

/-- On an element of mass weight `n`, the `n`-th coefficient of the mass-weight
  polynomial is the element itself. -/
lemma coeff_massWeightPoly_of_mem {n : ℕ} {x : JetAlgebra}
    (hx : x ∈ massWeightSubmodule n) : (massWeightPoly x).coeff n = x := by
  rw [mem_massWeightSubmodule.mp hx, Polynomial.coeff_monomial, if_pos rfl]

/-- On an element of mass weight `m`, every other coefficient of the mass-weight
  polynomial vanishes. -/
lemma coeff_massWeightPoly_of_mem_ne {m n : ℕ} {x : JetAlgebra} (hmn : m ≠ n)
    (hx : x ∈ massWeightSubmodule m) : (massWeightPoly x).coeff n = 0 := by
  rw [mem_massWeightSubmodule.mp hx, Polynomial.coeff_monomial, if_neg hmn]

/-- The `i`-th coefficient of the mass-weight polynomial vanishes on the span of
  all the *other* weight submodules. This is the separation property that makes
  the weight decomposition direct. -/
lemma coeff_massWeightPoly_eq_zero_of_mem_iSup_ne (i : ℕ) {x : JetAlgebra}
    (hx : x ∈ ⨆ (j : ℕ) (_ : j ≠ i), massWeightSubmodule j) :
    (massWeightPoly x).coeff i = 0 := by
  induction hx using Submodule.iSup_induction' with
  | mem j x hj =>
    by_cases hne : j ≠ i
    · rw [iSup_pos hne] at hj
      exact coeff_massWeightPoly_of_mem_ne hne hj
    · rw [iSup_neg hne, Submodule.mem_bot] at hj
      rw [hj, map_zero, Polynomial.coeff_zero]
  | zero => simp
  | add a b _ _ ha hb => rw [map_add, Polynomial.coeff_add, ha, hb, add_zero]

/-- The weight submodules span the whole jet algebra. -/
lemma iSup_massWeightSubmodule_eq_top :
    ⨆ n : ℕ, massWeightSubmodule n = ⊤ := by
  rw [eq_top_iff]
  intro x _
  rw [eq_sum_massWeightPoly_coeff x]
  exact Submodule.sum_mem _ fun n _ => Submodule.mem_iSup_of_mem n
    (coeff_massWeightPoly_mem_massWeightSubmodule n x)

/-- The weight submodules are independent: an element of weight `i` lying in the
  span of the other weights is zero, since taking the `i`-th coefficient of the
  mass-weight polynomial returns it on the one and kills it on the other. -/
lemma iSupIndep_massWeightSubmodule : iSupIndep massWeightSubmodule := by
  intro i
  rw [Submodule.disjoint_def]
  intro x hx hx'
  rw [← coeff_massWeightPoly_of_mem hx]
  exact coeff_massWeightPoly_eq_zero_of_mem_iSup_ne i hx'

/-- The jet algebra is the internal direct sum of its mass-weight submodules. -/
lemma massWeightSubmodule_isInternal : DirectSum.IsInternal massWeightSubmodule :=
  (DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top _).mpr
    ⟨iSupIndep_massWeightSubmodule, iSup_massWeightSubmodule_eq_top⟩

noncomputable instance : GradedAlgebra massWeightSubmodule :=
  DirectSum.IsInternal.gradedAlgebra massWeightSubmodule_isInternal


/-!

## B. The mass-weight scaling on the jet algebra

-/

/-- The mass-dimension scaling on the jet algebra of the charged-lepton singlet:
  the (linear map underlying the) algebra map multiplying each generator by
  `c ^ w`, where `w` is twice its mass dimension. -/
noncomputable def massWeightScale (c : ℂ) : JetAlgebra →ₐ[ℂ] JetAlgebra :=
  (ExteriorAlgebra.map (JetComponentSpace.massWeightScale c))

lemma massWeightScale_apply (c : ℂ) (x : JetAlgebra) :
    massWeightScale c x =
      ExteriorAlgebra.map (JetComponentSpace.massWeightScale c) x := rfl

/-- Each generator scales by `c` to the power of its mass weight. -/
@[simp]
lemma massWeightScale_ofGenerator (c : ℂ) (j : JetGenerators) :
    massWeightScale c (ofGenerator j) = c ^ j.massWeight • ofGenerator j := by
  rw [ofGenerator, massWeightScale_apply, ExteriorAlgebra.map_apply_ι,
    JetComponentSpace.massWeightScale_basis, map_smul]

@[simp]
lemma massWeightScale_ι (c : ℂ) (v : JetComponentSpace) :
    massWeightScale c (ExteriorAlgebra.ι ℂ v) =
      ExteriorAlgebra.ι ℂ (JetComponentSpace.massWeightScale c v) := by
  rw [massWeightScale_apply, ExteriorAlgebra.map_apply_ι]


/-- The total derivative raises the mass weight by two: the scaling and the
  derivative commute up to `c ^ 2`. -/
lemma massWeightScale_jetDeriv (c : ℂ) (μ : Fin 1 ⊕ Fin 3) (x : JetAlgebra) :
    massWeightScale c (jetDeriv μ x) = c ^ 2 • jetDeriv μ (massWeightScale c x) := by
  induction x using ExteriorAlgebra.induction with
  | algebraMap r =>
    simp [Algebra.algebraMap_eq_smul_one]
  | ι v =>
    rw [jetDeriv_ι, massWeightScale_ι, JetComponentSpace.massWeightScale_jetDeriv,
      map_smul, massWeightScale_ι, jetDeriv_ι]
  | mul x y hx hy =>
    simp [map_mul, jetDeriv_mul, hx, hy, smul_add]
  | add x y hx hy =>
    simp only [map_add, hx, hy, smul_add]

/-- The mass-dimension scaling commutes with the gauge action of jets of
  constant gauge transformations. This fails for a general jet: the gauge action
  sends `∂ψ` to `u(0)⁶ ∂ψ + (∂u⁶)(0) ψ + …`, mixing derivative degrees
  downwards, while the scaling weights each degree differently, so the two
  compositions already differ on first-derivative generators. -/
lemma massWeightScale_repJetGaugeGroupI_ofConstant (c : ℂ) (g : GaugeGroupI) :
    massWeightScale c ∘ₗ JetAlgebra.repJetGaugeGroupI (JetGaugeGroupI.ofConstant g) =
      JetAlgebra.repJetGaugeGroupI (JetGaugeGroupI.ofConstant g) ∘ₗ massWeightScale c := by
  have h : (massWeightScale c).comp
      (ExteriorAlgebra.map (JetComponentSpace.repJetGaugeGroupI
        (JetGaugeGroupI.ofConstant g))) =
      (ExteriorAlgebra.map (JetComponentSpace.repJetGaugeGroupI
        (JetGaugeGroupI.ofConstant g))).comp (massWeightScale c) := by
    rw [massWeightScale, ExteriorAlgebra.map_comp_map, ExteriorAlgebra.map_comp_map,
      JetComponentSpace.massWeightScale_repJetGaugeGroupI_ofConstant]
  have h2 := congrArg AlgHom.toLinearMap h
  rw [AlgHom.comp_toLinearMap, AlgHom.comp_toLinearMap] at h2
  exact h2

lemma massWeightScale_repLorentzGroup (c : ℂ) (g : SL(2,ℂ)) :
    massWeightScale c ∘ₗ JetAlgebra.repLorentzGroup g =
      JetAlgebra.repLorentzGroup g ∘ₗ massWeightScale c := by
  have h : (massWeightScale c).comp
      (ExteriorAlgebra.map (JetComponentSpace.repLorentzGroup g)) =
      (ExteriorAlgebra.map (JetComponentSpace.repLorentzGroup g)).comp
        (massWeightScale c) := by
    rw [massWeightScale, ExteriorAlgebra.map_comp_map, ExteriorAlgebra.map_comp_map,
      JetComponentSpace.massWeightScale_repLorentzGroup]
  have h2 := congrArg AlgHom.toLinearMap h
  rw [AlgHom.comp_toLinearMap, AlgHom.comp_toLinearMap] at h2
  exact h2

lemma massWeightScale_repJetGaugeGroupI_ofConstant_apply (c : ℂ) (g : GaugeGroupI)
    (x : JetAlgebra) :
    massWeightScale c
        (JetAlgebra.repJetGaugeGroupI (JetGaugeGroupI.ofConstant g) x) =
      JetAlgebra.repJetGaugeGroupI (JetGaugeGroupI.ofConstant g)
        (massWeightScale c x) :=
  DFunLike.congr_fun (massWeightScale_repJetGaugeGroupI_ofConstant c g) x

lemma massWeightScale_repLorentzGroup_apply (c : ℂ) (g : SL(2,ℂ)) (x : JetAlgebra) :
    massWeightScale c (JetAlgebra.repLorentzGroup g x) =
      JetAlgebra.repLorentzGroup g (massWeightScale c x) := by
  have h := massWeightScale_repLorentzGroup c g
  exact DFunLike.congr_fun h x

/-!

## C. Evaluating the mass-weight polynomial

The mass-weight polynomial and the mass-weight scaling are two descriptions of the same
grading: evaluating the polynomial at a scalar gives the scaling by that scalar. Since a
polynomial with coefficients in an algebra over an infinite field is determined by its
values at the scalars, statements proved for one description transfer to the other.

-/

/-- Evaluating the mass-weight polynomial at a scalar is the mass-weight scaling by that
  scalar. Both send a generator of weight `w` to `c ^ w` times itself, and both are
  algebra maps. -/
lemma eval_massWeightPoly (c : ℂ) (x : JetAlgebra) :
    (massWeightPoly x).eval (algebraMap ℂ JetAlgebra c) = massWeightScale c x := by
  have h : (Polynomial.eval₂AlgHom (AlgHom.id ℂ JetAlgebra)
      (algebraMap ℂ JetAlgebra c)
      (fun a => (Algebra.commutes c a).symm)).comp massWeightPoly =
      (massWeightScale c : JetAlgebra →ₐ[ℂ] JetAlgebra) := by
    refine ExteriorAlgebra.hom_ext (Module.Basis.ext JetComponentSpace.basis fun j => ?_)
    show (massWeightPoly (ofGenerator j)).eval (algebraMap ℂ JetAlgebra c) =
      massWeightScale c (ofGenerator j)
    rw [massWeightPoly_ofGenerator, massWeightScale_ofGenerator, Polynomial.eval_monomial,
      ← map_pow, ← Algebra.commutes, ← Algebra.smul_def]
  exact AlgHom.congr_fun h x

/-!

## D. The mass weight of derivatives and of transformed elements

-/

/-- The total derivative raises the mass weight by two: its mass-weight polynomial is
  `X ^ 2` times the coefficientwise total derivative. -/
lemma massWeightPoly_jetDeriv (μ : Fin 1 ⊕ Fin 3) (x : JetAlgebra) :
    massWeightPoly (jetDeriv μ x) =
      Polynomial.X ^ 2 * Polynomial.mapCoeffs (jetDeriv μ) (massWeightPoly x) := by
  obtain ⟨q, hq, hc⟩ := exists_massWeightPoly_jetDeriv μ x
  rw [hq]
  congr 1
  refine Polynomial.ext fun n => ?_
  rw [Polynomial.coeff_mapCoeffs (map_zero (jetDeriv μ)), hc]

/-- The Lorentz action preserves mass weights: the mass-weight polynomial of a transformed
  element is the transform of its mass-weight polynomial. -/
lemma massWeightPoly_repLorentzGroup (Λ : SL(2,ℂ)) (x : JetAlgebra) :
    massWeightPoly (repLorentzGroup Λ x) =
      Polynomial.mapAlgHom (repLorentzGroupAlgHom Λ) (massWeightPoly x) := by
  refine Polynomial.ext_of_forall_eval_algebraMap (k := ℂ) fun c => ?_
  rw [eval_massWeightPoly, Polynomial.eval_algebraMap_mapAlgHom, eval_massWeightPoly,
    massWeightScale_repLorentzGroup_apply]
  rfl

/-- Jets of constant gauge transformations preserve mass weights. This fails for a general
  jet: the higher Taylor coefficients of the hypercharge character lower the derivative
  degree, mixing weights. -/
lemma massWeightPoly_repJetGaugeGroupI_ofConstant (g : GaugeGroupI) (x : JetAlgebra) :
    massWeightPoly (repJetGaugeGroupI (JetGaugeGroupI.ofConstant g) x) =
      Polynomial.mapAlgHom (repJetGaugeGroupIAlgHom (JetGaugeGroupI.ofConstant g))
        (massWeightPoly x) := by
  refine Polynomial.ext_of_forall_eval_algebraMap (k := ℂ) fun c => ?_
  rw [eval_massWeightPoly, Polynomial.eval_algebraMap_mapAlgHom, eval_massWeightPoly,
    massWeightScale_repJetGaugeGroupI_ofConstant_apply]
  rfl

end JetAlgebra

end LeptonSinglet

end StandardModel
