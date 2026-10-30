/-
Copyright (c) 2026 Daniel Leonforte. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Leonforte
-/
module

public import PhyslibAlpha.QuantumMechanics.Hydrogen.Eigenfunctions
public import Mathlib.Algebra.MvPolynomial.Funext
public import Mathlib.Data.Sym.Card
public import Mathlib.Data.Finsupp.Multiset
public import Mathlib.RingTheory.MvPolynomial.EulerIdentity
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.Algebra.MvPolynomial.PDeriv

/-!
# The degeneracy of the hydrogen bound states

## i. Overview

The bound states `boundState H N l P` of `Eigenfunctions.lean` at the Bohr level `n = N + l` are
built from homogeneous harmonic polynomials `P` of degree `l ≤ n`. The space of such polynomials
in `d` variables has dimension `C(l + d - 1, d - 1) - C(l + d - 3, d - 1)`, which is `2l + 1` for
`d = 3`. The bound states for different `l` and linearly independent `P` are linearly
independent, so the level `n` carries at least `Σ_{l ≤ n} (2l + 1) = (n + 1)²` independent
eigenfunctions in three dimensions.

## ii. Key results

- `harmonicSubmodule` : homogeneous harmonic polynomials of degree `l` in `d` variables.
- `finrank_harmonicSubmodule` : their dimension.
- `boundState_eigen_of_mem_harmonicSubmodule` : such polynomials give bound states.
- `boundStateMap_injective` : the bound states of one level are linearly independent.
- `finrank_range_boundStateMap` : they span a space of dimension `Σ_{l ≤ n} dim Harm_l`.
- `finrank_range_boundStateMap_three` : `(n + 1)²` independent bound states in three dimensions.

## iii. Table of contents

- A. Homogeneous harmonic polynomials
- B. Polynomials as functions on space
- C. Linear independence of the bound states

## iv. References

- S. Axler, P. Bourdon and W. Ramey, *Harmonic Function Theory*, 2nd ed., Graduate Texts in
  Mathematics 137, Springer (2001), chapter 5 (Harmonic Polynomials),
  doi:10.1007/978-1-4757-8137-3_5.
-/

@[expose] public section

noncomputable section

namespace PhyslibAlpha.Hydrogen

open MvPolynomial Space
open scoped ContDiff

/-!

## A. Homogeneous harmonic polynomials

-/

/-- The Laplacian `Σᵢ ∂ᵢ² P` of a polynomial in `d` variables. -/
def polyLaplacian (d : ℕ) : MvPolynomial (Fin d) ℝ →ₗ[ℝ] MvPolynomial (Fin d) ℝ :=
  ∑ i, (pderiv i).toLinearMap ∘ₗ (pderiv i).toLinearMap

/-- The homogeneous harmonic polynomials of degree `l` in `d` variables. -/
def harmonicSubmodule (d l : ℕ) : Submodule ℝ (MvPolynomial (Fin d) ℝ) :=
  homogeneousSubmodule (Fin d) ℝ l ⊓ LinearMap.ker (polyLaplacian d)

instance (d l : ℕ) : FiniteDimensional ℝ (harmonicSubmodule d l) :=
  haveI : FiniteDimensional ℝ (homogeneousSubmodule (Fin d) ℝ l) :=
    Module.Finite.iff_fg.mpr (homogeneousSubmodule_fg (σ := Fin d) (R := ℝ) l)
  Submodule.finiteDimensional_of_le inf_le_left

/-- The homogeneous polynomials of degree `l` in `d ≥ 1` variables form a space of dimension
`C(l + d - 1, d - 1)`: their monomials correspond to multisets of size `l` in `d` letters. -/
lemma finrank_homogeneousSubmodule {d : ℕ} (hd : 1 ≤ d) (l : ℕ) :
    Module.finrank ℝ (homogeneousSubmodule (Fin d) ℝ l) = (l + d - 1).choose (d - 1) := by
  classical
  let s : Set (Fin d →₀ ℕ) := {m | m.degree = l}
  let e1 : ↥(homogeneousSubmodule (Fin d) ℝ l) ≃ₗ[ℝ] (s →₀ ℝ) :=
    (LinearEquiv.ofEq _ _ (homogeneousSubmodule_eq_finsupp_supported (σ := Fin d) (R := ℝ) l)).trans
      (AddMonoidAlgebra.supportedEquivFinsupp s)
  let e2 : Sym (Fin d) l ≃ s :=
    (Sym.equivNatSum (Fin d) l).trans
      (Equiv.subtypeEquivRight fun m => by simp only [Finsupp.sum, id, s, Set.mem_ofPred_eq]; rfl)
  let _ : Fintype s := Fintype.ofEquiv _ e2
  rw [e1.finrank_eq, Module.finrank_finsupp_self, ← Fintype.card_congr e2,
    Sym.card_sym_eq_multichoose, Fintype.card_fin, Nat.multichoose_eq,
    show d + l - 1 = l + d - 1 by omega]
  exact Nat.choose_symm_of_eq_add (by omega)

lemma polyLaplacian_apply {d : ℕ} (P : MvPolynomial (Fin d) ℝ) :
    polyLaplacian d P = ∑ i, pderiv i (pderiv i P) := by
  simp [polyLaplacian]

/-- The Laplacian lowers the degree of a homogeneous polynomial by two. -/
lemma polyLaplacian_isHomogeneous {d l : ℕ} {P : MvPolynomial (Fin d) ℝ}
    (hP : P.IsHomogeneous (l + 2)) : (polyLaplacian d P).IsHomogeneous l := by
  rw [polyLaplacian_apply]
  exact IsHomogeneous.sum _ _ _ fun i _ => by simpa using (hP.pderiv (i := i)).pderiv (i := i)

/-- A homogeneous polynomial of degree `0` is constant, so its derivatives vanish. -/
lemma pderiv_eq_zero_of_isHomogeneous_zero {d : ℕ} {Q : MvPolynomial (Fin d) ℝ}
    (hQ : Q.IsHomogeneous 0) (i : Fin d) : pderiv i Q = 0 := by
  ext m
  rw [coeff_pderiv, AddMonoidAlgebra.coeff_zero, Finsupp.coe_zero, Pi.zero_apply]
  by_contra h
  have := hQ (left_ne_zero_of_mul h)
  simp only [map_add, Nat.add_eq_zero_iff] at this
  exact absurd this.2 (by simp [Finsupp.weight_apply, Finsupp.sum_single_index])

/-- The Laplacian vanishes on homogeneous polynomials of degree `0` and `1`. -/
lemma polyLaplacian_eq_zero_of_lt_two {d l : ℕ} {P : MvPolynomial (Fin d) ℝ}
    (hP : P.IsHomogeneous l) (hl : l < 2) : polyLaplacian d P = 0 := by
  rw [polyLaplacian_apply]
  refine Finset.sum_eq_zero fun i _ => pderiv_eq_zero_of_isHomogeneous_zero ?_ i
  simpa [show l - 1 = 0 by omega] using hP.pderiv (i := i)

/-- The weight `m! = Πⱼ mⱼ!` of a monomial exponent `m`. -/
noncomputable def fischerWeight (m : Fin d →₀ ℕ) : ℝ := ∏ j, ((m j).factorial : ℝ)

lemma fischerWeight_pos (m : Fin d →₀ ℕ) : 0 < fischerWeight m :=
  Finset.prod_pos fun j _ => by exact_mod_cast (m j).factorial_pos

lemma fischerWeight_add_single (m : Fin d →₀ ℕ) (i : Fin d) :
    fischerWeight (m + Finsupp.single i 1) = fischerWeight m * ((m i : ℝ) + 1) := by
  classical
  unfold fischerWeight
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i),
    ← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
  have h : ∏ j ∈ Finset.univ.erase i, (((m + Finsupp.single i 1 : Fin d →₀ ℕ) j).factorial : ℝ) =
      ∏ j ∈ Finset.univ.erase i, ((m j).factorial : ℝ) :=
    Finset.prod_congr rfl fun j hj => by
      simp [(Finset.ne_of_mem_erase hj).symm]
  rw [h]
  simp only [Finsupp.coe_add, Pi.add_apply, Finsupp.single_eq_same, Nat.factorial_succ]
  push_cast
  ring

/-- The Fischer inner product `Σₘ m! Pₘ Qₘ` of two polynomials. -/
noncomputable def fischer (P Q : MvPolynomial (Fin d) ℝ) : ℝ :=
  ∑ m ∈ P.support, fischerWeight m * P.coeff m * Q.coeff m

lemma fischer_eq_sum {d : ℕ} {P Q : MvPolynomial (Fin d) ℝ} {S : Finset (Fin d →₀ ℕ)}
    (hS : P.support ⊆ S) :
    fischer P Q = ∑ m ∈ S, fischerWeight m * P.coeff m * Q.coeff m :=
  Finset.sum_subset hS fun m _ hm => by simp [notMem_support_iff.mp hm]

lemma fischer_zero_left (Q : MvPolynomial (Fin d) ℝ) : fischer 0 Q = 0 := by
  simp [fischer]

lemma fischer_add_left (P P' Q : MvPolynomial (Fin d) ℝ) :
    fischer (P + P') Q = fischer P Q + fischer P' Q := by
  classical
  set S := P.support ∪ P'.support ∪ (P + P').support
  rw [fischer_eq_sum (S := S) (by intro m; simp +contextual [S]),
    fischer_eq_sum (S := S) (by intro m; simp +contextual [S]),
    fischer_eq_sum (S := S) (by intro m; simp +contextual [S]), ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun m _ => ?_
  simp only [AddMonoidAlgebra.coeff_add, Finsupp.coe_add, Pi.add_apply]
  ring

lemma fischer_sum_left {ι : Type*} (s : Finset ι) (f : ι → MvPolynomial (Fin d) ℝ)
    (Q : MvPolynomial (Fin d) ℝ) : fischer (∑ i ∈ s, f i) Q = ∑ i ∈ s, fischer (f i) Q := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [fischer_zero_left]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, fischer_add_left, ih]

lemma fischer_sum_right {ι : Type*} (s : Finset ι) (P : MvPolynomial (Fin d) ℝ)
    (f : ι → MvPolynomial (Fin d) ℝ) : fischer P (∑ i ∈ s, f i) = ∑ i ∈ s, fischer P (f i) := by
  simp only [fischer, coeff_sum, Finset.mul_sum]
  exact Finset.sum_comm

lemma fischer_zero_right (P : MvPolynomial (Fin d) ℝ) : fischer P 0 = 0 := by
  simp [fischer]

/-- Multiplication by `Xᵢ` is adjoint to `∂ᵢ` for the Fischer inner product. -/
lemma fischer_mul_X (P Q : MvPolynomial (Fin d) ℝ) (i : Fin d) :
    fischer (P * X i) Q = fischer P (pderiv i Q) := by
  unfold fischer
  rw [support_mul_X, Finset.sum_map]
  refine Finset.sum_congr rfl fun m _ => ?_
  simp only [addRightEmbedding_apply, coeff_mul_X, coeff_pderiv, fischerWeight_add_single]
  ring

/-- The Fischer inner product is positive definite. -/
lemma fischer_self_pos {P : MvPolynomial (Fin d) ℝ} (hP : P ≠ 0) : 0 < fischer P P := by
  refine Finset.sum_pos (fun m hm => ?_) (support_nonempty.mpr hP)
  rw [mul_assoc]
  exact mul_pos (fischerWeight_pos m) (mul_self_pos.mpr (mem_support_iff.mp hm))

/-- `r² = Σᵢ Xᵢ²`. -/
def rSq (d : ℕ) : MvPolynomial (Fin d) ℝ := ∑ i, X i * X i

lemma rSq_isHomogeneous (d : ℕ) : (rSq d).IsHomogeneous 2 :=
  IsHomogeneous.sum _ _ _ fun i _ => (isHomogeneous_X ℝ i).mul (isHomogeneous_X ℝ i)

lemma rSq_ne_zero {d : ℕ} (hd : 1 ≤ d) : rSq d ≠ 0 := by
  intro h
  have := congrArg (eval fun _ => (1 : ℝ)) h
  simp [rSq] at this
  omega

/-- A harmonic polynomial divisible by `r²` vanishes: `⟨r² P, r² P⟩ = ⟨P, Δ(r² P)⟩ = 0`. -/
lemma eq_zero_of_polyLaplacian_eq_zero_of_eq_rSq_mul {d : ℕ} {P Q : MvPolynomial (Fin d) ℝ}
    (hQ : polyLaplacian d Q = 0) (hQP : Q = rSq d * P) : Q = 0 := by
  by_contra hne
  have hpos := fischer_self_pos hne
  have hsum : rSq d * P = ∑ i, P * X i * X i := by
    simp only [rSq, Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => by ring
  have h0 : fischer Q Q = 0 := by
    calc fischer Q Q = fischer (∑ i, P * X i * X i) Q := by rw [← hsum, ← hQP]
      _ = ∑ i, fischer P (pderiv i (pderiv i Q)) := by
        rw [fischer_sum_left]
        exact Finset.sum_congr rfl fun i _ => by rw [fischer_mul_X, fischer_mul_X]
      _ = fischer P (polyLaplacian d Q) := by rw [polyLaplacian_apply, fischer_sum_right]
      _ = 0 := by rw [hQ, fischer_zero_right]
  linarith

/-- `dim Harm_{l+2} + dim Hom_l = dim Hom_{l+2}`: the Laplacian `Hom_{l+2} → Hom_l` is onto. -/
lemma finrank_harmonicSubmodule_add_finrank {d : ℕ} (hd : 1 ≤ d) (l : ℕ) :
    Module.finrank ℝ (harmonicSubmodule d (l + 2)) +
        Module.finrank ℝ (homogeneousSubmodule (Fin d) ℝ l) =
      Module.finrank ℝ (homogeneousSubmodule (Fin d) ℝ (l + 2)) := by
  set K := harmonicSubmodule d (l + 2)
  set Hl := homogeneousSubmodule (Fin d) ℝ l
  set H2 := homogeneousSubmodule (Fin d) ℝ (l + 2)
  have : FiniteDimensional ℝ Hl :=
    Module.Finite.iff_fg.mpr (homogeneousSubmodule_fg (σ := Fin d) (R := ℝ) l)
  have : FiniteDimensional ℝ H2 :=
    Module.Finite.iff_fg.mpr (homogeneousSubmodule_fg (σ := Fin d) (R := ℝ) (l + 2))
  apply le_antisymm
  · -- `K` and `r² Hl` are independent subspaces of `H2`
    set M := LinearMap.mulLeft ℝ (rSq d)
    have hinj : Function.Injective M := mul_right_injective₀ (rSq_ne_zero hd)
    set R := Hl.map M
    have : FiniteDimensional ℝ R := Module.Finite.map Hl M
    have hRH2 : R ≤ H2 := by
      rintro _ ⟨P, hP, rfl⟩
      rw [mem_homogeneousSubmodule, add_comm l 2]
      exact (rSq_isHomogeneous d).mul ((mem_homogeneousSubmodule l P).mp hP)
    have hKR : K ⊓ R = ⊥ := by
      rw [eq_bot_iff]
      rintro Q ⟨hQK, P, -, hQP⟩
      exact (Submodule.mem_bot ℝ).mpr
        (eq_zero_of_polyLaplacian_eq_zero_of_eq_rSq_mul (LinearMap.mem_ker.mp hQK.2) hQP.symm)
    have hR : Module.finrank ℝ R = Module.finrank ℝ Hl :=
      (Submodule.equivMapOfInjective M hinj Hl).finrank_eq.symm
    have h := Submodule.finrank_sup_add_finrank_inf_eq K R
    rw [hKR, finrank_bot, add_zero, hR] at h
    rw [← h]
    exact Submodule.finrank_mono (sup_le inf_le_left hRH2)
  · -- rank-nullity for `Δ : H2 → MvPolynomial`, whose range lies in `Hl`
    set g := (polyLaplacian d).domRestrict H2
    have hrange : LinearMap.range g ≤ Hl := by
      rintro _ ⟨P, rfl⟩
      exact (mem_homogeneousSubmodule l _).mpr
        (polyLaplacian_isHomogeneous ((mem_homogeneousSubmodule _ _).mp P.2))
    have hker : Module.finrank ℝ (LinearMap.ker g) = Module.finrank ℝ K := by
      rw [LinearMap.ker_domRestrict]
      have : (LinearMap.ker (polyLaplacian d)).comap H2.subtype = K.comap H2.subtype := by
        simp [K, harmonicSubmodule, H2, Submodule.comap_inf]
      rw [this]
      exact (Submodule.comapSubtypeEquivOfLe (inf_le_left : K ≤ H2)).finrank_eq
    have h := LinearMap.finrank_range_add_finrank_ker g
    rw [hker] at h
    rw [← h, add_comm]
    exact Nat.add_le_add_left (Submodule.finrank_mono hrange) _

/-- The homogeneous harmonic polynomials of degree `l` in `d ≥ 2` variables form a space of
dimension `C(l + d - 1, d - 1) - C(l + d - 3, d - 1)`. -/
lemma finrank_harmonicSubmodule {d : ℕ} (hd : 2 ≤ d) (l : ℕ) :
    Module.finrank ℝ (harmonicSubmodule d l) =
      (l + d - 1).choose (d - 1) - (l + d - 3).choose (d - 1) := by
  rcases Nat.lt_or_ge l 2 with hl | hl
  · -- in degrees `0` and `1` every homogeneous polynomial is harmonic
    have : harmonicSubmodule d l = homogeneousSubmodule (Fin d) ℝ l := by
      refine inf_eq_left.mpr fun P hP => LinearMap.mem_ker.mpr ?_
      exact polyLaplacian_eq_zero_of_lt_two ((mem_homogeneousSubmodule l P).mp hP) hl
    rw [this, finrank_homogeneousSubmodule (by omega),
      Nat.choose_eq_zero_of_lt (by omega : l + d - 3 < d - 1), Nat.sub_zero]
  · obtain ⟨l, rfl⟩ : ∃ k, l = k + 2 := ⟨l - 2, by omega⟩
    have h := finrank_harmonicSubmodule_add_finrank (by omega : 1 ≤ d) l
    rw [finrank_homogeneousSubmodule (by omega), finrank_homogeneousSubmodule (by omega)] at h
    rw [show l + 2 + d - 3 = l + d - 1 by omega]
    omega

/-- In three variables the homogeneous harmonic polynomials of degree `l` form a space of
dimension `2l + 1`. -/
lemma finrank_harmonicSubmodule_three (l : ℕ) :
    Module.finrank ℝ (harmonicSubmodule 3 l) = 2 * l + 1 := by
  rw [finrank_harmonicSubmodule (by norm_num)]
  rcases l with _ | _ | l
  · simp
  · simp
  · simp only [show l + 2 + 3 - 1 = l + 4 by omega, show l + 2 + 3 - 3 = l + 2 by omega,
      show 3 - 1 = 2 by rfl, Nat.choose_two_right]
    rw [show (l + 4) * (l + 4 - 1) = (l + 2) * (l + 2 - 1) + 2 * (2 * (l + 2) + 1) by
      rw [show l + 4 - 1 = l + 3 by omega, show l + 2 - 1 = l + 1 by omega]; ring]
    omega

/-- `Σ_{l ≤ n} (2l + 1) = (n + 1)²`. -/
lemma sum_two_mul_add_one (n : ℕ) : ∑ l ∈ Finset.range (n + 1), (2 * l + 1) = (n + 1) ^ 2 := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ, ih]; ring

/-!

## B. Polynomials as functions on space

-/

/-- A polynomial in `d` variables as a function on `Space d`. -/
def toFun {d : ℕ} (P : MvPolynomial (Fin d) ℝ) (y : Space d) : ℝ := eval (fun i => y i) P

@[simp]
lemma toFun_C {d : ℕ} (a : ℝ) : toFun (C a : MvPolynomial (Fin d) ℝ) = fun _ => a := by
  funext y
  simp [toFun]

@[simp]
lemma toFun_add {d : ℕ} (P Q : MvPolynomial (Fin d) ℝ) : toFun (P + Q) = toFun P + toFun Q := by
  funext y
  simp [toFun]

lemma toFun_mul_X {d : ℕ} (P : MvPolynomial (Fin d) ℝ) (j : Fin d) :
    toFun (P * X j) = fun y => toFun P y * y j := by
  funext y
  simp [toFun]

/-- Polynomials are smooth. -/
lemma contDiff_toFun_infty {d : ℕ} (P : MvPolynomial (Fin d) ℝ) : ContDiff ℝ ∞ (toFun P) := by
  induction P using MvPolynomial.induction_on with
  | C a => rw [toFun_C]; exact contDiff_const
  | add P Q hP hQ => rw [toFun_add]; exact hP.add hQ
  | mul_X P j hP =>
    rw [toFun_mul_X]
    exact hP.mul (by simpa [Space.coord_apply] using Space.coord_contDiff (i := j))

/-- Polynomials are twice continuously differentiable. -/
lemma contDiff_toFun {d : ℕ} (P : MvPolynomial (Fin d) ℝ) : ContDiff ℝ 2 (toFun P) :=
  contDiff_infty.mp (contDiff_toFun_infty P) 2

lemma differentiable_toFun {d : ℕ} (P : MvPolynomial (Fin d) ℝ) : Differentiable ℝ (toFun P) :=
  (contDiff_infty.mp (contDiff_toFun_infty P) 1).differentiable one_ne_zero

/-- The partial derivative of a polynomial function is the polynomial partial derivative. -/
lemma deriv_toFun {d : ℕ} (i : Fin d) (P : MvPolynomial (Fin d) ℝ) :
    ∂[i] (toFun P) = toFun (pderiv i P) := by
  induction P using MvPolynomial.induction_on with
  | C a =>
    funext y
    rw [toFun_C, pderiv_C, show (0 : MvPolynomial (Fin d) ℝ) = C 0 by simp, toFun_C]
    exact deriv_const a i
  | add P Q hP hQ =>
    rw [toFun_add, deriv_add _ _ (differentiable_toFun P) (differentiable_toFun Q), hP, hQ,
      map_add, toFun_add]
  | mul_X P j hP =>
    funext y
    have hc : DifferentiableAt ℝ (fun y : Space d => y j) y := Space.eval_differentiable j y
    rw [toFun_mul_X, Space.deriv_eq, fderiv_fun_mul (differentiable_toFun P y) hc]
    simp only [_root_.add_apply, _root_.smul_apply, smul_eq_mul,
      ← Space.deriv_eq, hP, deriv_component]
    simp [toFun, pderiv_X, Pi.single_apply, eq_comm]
    split_ifs <;> simp

/-- Euler's relation `Σᵢ yᵢ ∂ᵢP = l P` for a homogeneous polynomial of degree `l`. -/
lemma euler_toFun {d l : ℕ} {P : MvPolynomial (Fin d) ℝ} (hP : P.IsHomogeneous l)
    (y : Space d) : ∑ i, y i * ∂[i] (toFun P) y = l * toFun P y := by
  have h := congrArg (eval (fun i => y i)) hP.sum_X_mul_pderiv
  simp only [map_sum, map_mul, eval_X, nsmul_eq_mul] at h
  simpa [deriv_toFun, toFun] using h

/-- The Laplacian of a polynomial function is the polynomial Laplacian. -/
lemma laplacian_toFun {d : ℕ} (P : MvPolynomial (Fin d) ℝ) (y : Space d) :
    Δ (toFun P) y = toFun (polyLaplacian d P) y := by
  rw [laplacian_eq_sum_snd_deriv]
  simp [deriv_toFun, polyLaplacian, toFun, map_sum]

/-- A homogeneous harmonic polynomial of degree `l` gives the bound state
`boundState H N l P` of energy `E_{N+l}`, away from the nucleus. -/
lemma boundState_eigen_of_mem_harmonicSubmodule (H : QuantumMechanics.HydrogenAtom d)
    (hd : 2 ≤ d) (hk : 0 < H.k) (N l : ℕ) {P : MvPolynomial (Fin d) ℝ}
    (hP : P ∈ harmonicSubmodule d l) {x : Space d} (hx : x ≠ 0) :
    -((Constants.ℏ : ℝ) ^ 2 / (2 * H.m)) * Δ (boundState H N l (toFun P)) x +
        H.potential x * boundState H N l (toFun P) x =
      H.energyLevel (N + l) * boundState H N l (toFun P) x := by
  obtain ⟨hhom, hker⟩ := Submodule.mem_inf.mp hP
  refine boundState_eigen H hd hk N l (contDiff_toFun P)
    (euler_toFun ((mem_homogeneousSubmodule l P).mp hhom)) (fun y => ?_) hx
  rw [laplacian_toFun, LinearMap.mem_ker.mp hker]
  simp [toFun]

/-!

## C. Linear independence of the bound states

-/

/-- A homogeneous polynomial of degree `l` scales as `P(t y) = t^l P(y)`. -/
lemma toFun_smul_of_isHomogeneous {d l : ℕ} {P : MvPolynomial (Fin d) ℝ}
    (hP : P.IsHomogeneous l) (t : ℝ) (y : Space d) : toFun P (t • y) = t ^ l * toFun P y := by
  simp only [toFun, Space.smul_apply]
  rw [eval_eq, eval_eq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hdeg : ∑ i ∈ m.support, m i = l := by
    have := hP (mem_support_iff.mp hm)
    simpa [Finsupp.weight_apply, Finsupp.sum] using this
  simp_rw [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hdeg]
  ring

/-- If `Σ_l c_l t^l f_l(t) = 0` for all `t > 0`, with continuous `f_l` and `f_l(0) ≠ 0`, then
all `c_l` vanish: compare the lowest powers of `t` as `t → 0⁺`. -/
lemma eq_zero_of_sum_pow_mul {n : ℕ} (c : Fin (n + 1) → ℝ) (f : Fin (n + 1) → ℝ → ℝ)
    (hf : ∀ l, Continuous (f l)) (hf0 : ∀ l, f l 0 ≠ 0)
    (h : ∀ t, 0 < t → ∑ l, c l * t ^ (l : ℕ) * f l t = 0) : c = 0 := by
  have key : ∀ k : ℕ, ∀ l : Fin (n + 1), (l : ℕ) < k → c l = 0 := by
    intro k
    induction k with
    | zero => intro l hl; omega
    | succ k ih =>
      intro l hl
      rcases Nat.lt_succ_iff_lt_or_eq.mp hl with hl | hl
      · exact ih l hl
      subst hl
      let g : ℝ → ℝ := fun t => ∑ m : Fin (n + 1),
        if (l : ℕ) ≤ m then c m * t ^ ((m : ℕ) - l) * f m t else 0
      have hg : Continuous g := by
        refine continuous_finsetSum _ fun m _ => ?_
        split_ifs
        · exact (continuous_const.mul (continuous_pow _)).mul (hf m)
        · exact continuous_const
      have hgt : ∀ t, 0 < t → g t = 0 := by
        intro t ht
        have hsum : t ^ (l : ℕ) * g t = ∑ m, c m * t ^ (m : ℕ) * f m t := by
          simp only [g, Finset.mul_sum]
          refine Finset.sum_congr rfl fun m _ => ?_
          split_ifs with hm
          · have hm' : (m : ℕ) = l + ((m : ℕ) - l) := by omega
            conv_rhs => rw [hm', pow_add]
            ring
          · rw [ih m (by omega)]
            simp
        rw [h t ht] at hsum
        exact (mul_eq_zero.mp hsum).resolve_left (pow_ne_zero _ ht.ne')
      have hg0 : g 0 = 0 := by
        have h1 : Filter.Tendsto g (nhdsWithin 0 (Set.Ioi 0)) (nhds (g 0)) :=
          hg.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
        have h2 : Filter.Tendsto g (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) :=
          tendsto_const_nhds.congr'
            (eventually_nhdsWithin_of_forall fun t ht => (hgt t ht).symm)
        exact tendsto_nhds_unique h1 h2
      have hg0' : g 0 = c l * f l 0 := by
        simp only [g]
        rw [Finset.sum_eq_single l]
        · simp
        · intro m _ hm
          split_ifs with hml
          · have : (m : ℕ) - l ≠ 0 := by
              have : (m : ℕ) ≠ l := fun h => hm (Fin.ext h)
              omega
            simp [zero_pow this]
          · rfl
        · intro hl
          exact absurd (Finset.mem_univ l) hl
      rw [hg0'] at hg0
      exact (mul_eq_zero.mp hg0).resolve_right (hf0 l)
  funext l
  exact key (n + 1) l l.isLt

/-- The bound states of the level `n`: a family `(P_l)_{l ≤ n}` of homogeneous harmonic
polynomials gives `Σ_l boundState H (n - l) l P_l`. -/
def boundStateMap (H : QuantumMechanics.HydrogenAtom d) (n : ℕ) :
    ((l : Fin (n + 1)) → harmonicSubmodule d l) →ₗ[ℝ] (Space d → ℝ) where
  toFun Ps := ∑ l : Fin (n + 1),
    boundState H (n - l) l (toFun (Ps l : MvPolynomial (Fin d) ℝ))
  map_add' Ps Qs := by
    funext y
    simp [boundState, toFun, Finset.sum_add_distrib, mul_add]
  map_smul' c Ps := by
    funext y
    simp [boundState, toFun, Finset.mul_sum, mul_left_comm]

/-- The bound states of one level, for different `l` and linearly independent polynomials, are
linearly independent. Along a ray `y = t ω` the summand of degree `l` is `e^(-κ t ‖ω‖)` times
`t^l P_l(ω)` times a Laguerre polynomial in `t` that does not vanish at `t = 0`. -/
lemma boundStateMap_injective (H : QuantumMechanics.HydrogenAtom d) (n : ℕ) :
    Function.Injective (boundStateMap H n) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro Ps hPs
  set κ := boundKappa H n
  -- every `P_l` vanishes at every point `w`
  have hw : ∀ w : Space d, ∀ l, toFun (Ps l : MvPolynomial (Fin d) ℝ) w = 0 := by
    intro w
    let f : Fin (n + 1) → ℝ → ℝ := fun l t =>
      (laguerreScaled κ (n - l) (2 * l + d - 2)).eval (t * ‖w‖)
    have hc := eq_zero_of_sum_pow_mul (fun l => toFun (Ps l : MvPolynomial (Fin d) ℝ) w) f
      (fun l => (Polynomial.continuous _).comp (continuous_id.mul continuous_const))
      (fun l => by
        simp only [f, laguerreScaled, zero_mul, Polynomial.eval_comp, Polynomial.eval_mul,
          Polynomial.eval_C, Polynomial.eval_X, mul_zero, eval_laguerre_zero]
        exact_mod_cast (Nat.choose_pos (Nat.le_add_right _ _)).ne')
      (fun t ht => by
        have h := congr_fun hPs (t • w)
        simp only [boundStateMap, LinearMap.coe_mk, AddHom.coe_mk, Finset.sum_apply,
          Pi.zero_apply] at h
        have hterm : ∀ l : Fin (n + 1),
            boundState H (n - l) l (toFun (Ps l : MvPolynomial (Fin d) ℝ)) (t • w) =
              Real.exp (-(κ * (t * ‖w‖))) *
                (toFun (Ps l : MvPolynomial (Fin d) ℝ) w * t ^ (l : ℕ) * f l t) := by
          intro l
          have hl : n - (l : ℕ) + l = n := Nat.sub_add_cancel (Nat.lt_succ_iff.mp l.isLt)
          have hhom := (mem_homogeneousSubmodule _ _).mp (Submodule.mem_inf.mp (Ps l).2).1
          rw [boundState, hl, toFun_smul_of_isHomogeneous hhom, norm_smul,
            Real.norm_of_nonneg ht.le, radialFactor]
          simp only [f]
          ring
        simp only [hterm, ← Finset.mul_sum] at h
        exact (mul_eq_zero.mp h).resolve_left (Real.exp_pos _).ne')
    exact fun l => congr_fun hc l
  funext l
  apply Subtype.ext
  apply MvPolynomial.funext
  intro x
  simpa [toFun] using hw ⟨x⟩ l

/-- The bound states of the level `n` span a space of dimension `Σ_{l ≤ n} dim Harm_l`. -/
lemma finrank_range_boundStateMap (H : QuantumMechanics.HydrogenAtom d) (n : ℕ) :
    Module.finrank ℝ (LinearMap.range (boundStateMap H n)) =
      ∑ l : Fin (n + 1), Module.finrank ℝ (harmonicSubmodule d l) := by
  rw [LinearMap.finrank_range_of_inj (boundStateMap_injective H n), Module.finrank_pi_fintype]

/-- In three dimensions the level `n` carries `(n + 1)²` linearly independent bound states. -/
lemma finrank_range_boundStateMap_three (H : QuantumMechanics.HydrogenAtom 3)
    (n : ℕ) : Module.finrank ℝ (LinearMap.range (boundStateMap H n)) = (n + 1) ^ 2 := by
  rw [finrank_range_boundStateMap]
  simp only [finrank_harmonicSubmodule_three]
  rw [Fin.sum_univ_eq_sum_range (fun l => 2 * l + 1), sum_two_mul_add_one]

end PhyslibAlpha.Hydrogen
