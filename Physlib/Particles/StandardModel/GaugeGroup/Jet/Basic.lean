/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Particles.StandardModel.Basic
public import Physlib.Relativity.DerivAlgebra
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.SymmetricAlgebra.Basic
public import Mathlib.LinearAlgebra.SymmetricAlgebra.Basis
public import Mathlib.RepresentationTheory.Basic
public import Mathlib.RingTheory.TensorProduct.Basic
public import Physlib.Relativity.Tensors.ComplexTensor.Vector.Pre.Basic
/-!

# The jet gauge group

## i. Overview

For the Standard Model on Minkowski spacetime,
gauge transforms are maps from spacetime to the gauge group `G := SU(3) × SU(2) × U(1)`.

If one is considering a gauge transformation `g` at a point `x`, its action
on all the fields and their derivatives at `x` is determined by the
value of `g` and all its derivatives at `x`.  The collection of all
possible values of `g` and their derivatives at `x` is called the *jet* of `g` at `x`.
These form a group, which we call `JetGaugeGroupI`.

The group `JetGaugeGroupI` acts on all the fields and their derivatives at `x`,
every gauge transformation `g` has a corresponding element of `JetGaugeGroupI`,
and the action of `g` on the fields and their derivatives at `x` is determined by this element.

Thus locally it is enough to consider the action of `JetGaugeGroupI` on the fields and
their derivatives at a point, instead of the full set of gauge transformations on spacetime,
which is large and unwieldy.

## Start at a better overview

A Lagrangian at a point x is a polynomial in the fields and
 finitely many of their derivatives at x — that is the whole of
 its input. Symmetries of such an expression can therefore only
 ever see fields through that same finite window, and so a
 symmetry given by a function g : M → G can only act through the
 data g(x), ∂g(x), ∂²g(x), …. Two gauge transformations with the
 same Taylor expansion at x are indistinguishable to every
 Lagrangian at x: the honest symmetry group is not C^∞(M, G) but
 its quotient by that equivalence, the group of jets at x.


So we want to work with Taylor expansions rather than functions.
The key observation is that Taylor expansions can be added and
multiplied just like numbers: the coefficients of a product are
given by the familiar sums of binomial coefficients times pairs
of derivatives, which is just the Leibniz rule. This makes them a
ring, which we call JetRing — it plays the same role that ℂ does
for ordinary numbers, only its elements record a value together
with all of its derivatives.

Now, a group like SU(3), SU(2), or U(1) is defined by equations
 in matrix entries — U*U = 1, det U = 1 — and nothing in those
 equations demands that the entries be complex numbers. They make
 sense whenever the entries can be added, multiplied, and
 conjugated. In particular, they make sense for matrices whose
 entries are Taylor expansions. Writing down the Standard Model
 gauge group with entries in JetRing instead of ℂ gives
 JetGaugeGroupI, and unwinding the definitions shows this is
 precisely the group of Taylor expansions of gauge
 transformations: an element is a g(x) together with all its
 derivatives, constrained to be unitary order by order.

The payoff is that the derivative bookkeeping disappears into th
 ring multiplication. Products, inverses, and the adjoint action
  of jets are just the group operations of JetGaugeGroupI, so
  facts like "the jet of the inverse is the inverse of the jet"
  hold for free instead of needing a separate check at each
  order. We use infinite Taylor expansions rather than truncating
  at some order k, so that a single group acts on Lagrangians of
  every derivative order at once. The resulting group is blind to
  everything global — topology, winding, large gauge
  transformations — which is exactly right, since so is a
  Lagrangian at a point.


-/

@[expose] public section

namespace StandardModel

open Matrix MvPowerSeries JetRing
open scoped Nat

/-!

## B. The jet gauge group

The ring `JetRing` of formal power series in the spacetime coordinates, in which
jets of fields and of gauge transformations are valued, is defined in
`Physlib.Relativity.DerivAlgebra`, together with the algebra of derivative
symbols `DerivAlgebraComplex` and the action `DerivAlgebraComplex.jetRingAction`
of the jet ring on it.

-/

/-- The group of formal infinite-order jets, at a spacetime point, of local gauge
  transformations of the Standard Model: the `R`-points of the gauge group for `R`
  the ring `JetRing` of formal power series in the spacetime coordinates.

  Since gauge transformations multiply pointwise, jets multiply as power series and
  the group structure is that of the matrix groups over `JetRing`. The unitarity and
  determinant constraints hold as power-series identities, i.e. at every jet order.

  Evaluation at the base point recovers `GaugeGroupI`; see `JetGaugeGroupI.eval`. -/
abbrev JetGaugeGroupI : Type :=
  specialUnitaryGroup (Fin 3) JetRing × specialUnitaryGroup (Fin 2) JetRing ×
  unitary JetRing

namespace JetGaugeGroupI


/-- The underlying matrix value of an element of `JetGaugeGroupI`. -/
def toVal (U : JetGaugeGroupI) : Matrix (Fin 3) (Fin 3) JetRing × Matrix (Fin 2) (Fin 2) JetRing × JetRing :=
  (U.1.1, U.2.1.1, U.2.2.1)

/-!

## C. Evaluation at the base point

The constant coefficient of a power series is its value at the base point of the
jet. Applied entrywise it sends jets of gauge transformations to their zeroth-order
parts, giving a group homomorphism `JetGaugeGroupI →* GaugeGroupI`.

-/

/-- Entrywise evaluation at the base point commutes with the conjugate transpose. -/
lemma mapMatrix_constantCoeff_star {n : Type} [Fintype n] [DecidableEq n]
    (A : Matrix n n JetRing) :
    (constantCoeff : JetRing →+* ℂ).mapMatrix (star A) =
      star ((constantCoeff : JetRing →+* ℂ).mapMatrix A) := by
  ext i j
  simp [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.star_apply]

/-- Evaluation of a jet of a special-unitary gauge transformation at the base point:
  the entrywise constant coefficient. -/
noncomputable def evalSU (n : Type) [Fintype n] [DecidableEq n] :
    specialUnitaryGroup n JetRing →* specialUnitaryGroup n ℂ where
  toFun U := ⟨(constantCoeff : JetRing →+* ℂ).mapMatrix U.1, by
    obtain ⟨h1, h2⟩ := mem_specialUnitaryGroup_iff.mp U.2
    rw [mem_specialUnitaryGroup_iff]
    constructor
    · rw [mem_unitaryGroup_iff] at h1 ⊢
      rw [show star ((constantCoeff : JetRing →+* ℂ).mapMatrix U.1) =
          (constantCoeff : JetRing →+* ℂ).mapMatrix (star U.1) from
          (mapMatrix_constantCoeff_star U.1).symm, ← map_mul, h1, map_one]
    · rw [← RingHom.map_det, h2, map_one]⟩
  map_one' := Subtype.ext (map_one ((constantCoeff : JetRing →+* ℂ).mapMatrix))
  map_mul' U V := Subtype.ext (map_mul ((constantCoeff : JetRing →+* ℂ).mapMatrix) U.1 V.1)

/-- Evaluation of a jet of a `U(1)` gauge transformation at the base point: the
  constant coefficient. -/
noncomputable def evalU1 : unitary JetRing →* unitary ℂ where
  toFun u := ⟨constantCoeff u.1, by
    obtain ⟨h1, h2⟩ := Unitary.mem_iff.mp u.2
    exact Unitary.mem_iff.mpr
      ⟨by rw [← constantCoeff_star, ← map_mul, h1, map_one],
        by rw [← constantCoeff_star, ← map_mul, h2, map_one]⟩⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' u v := Subtype.ext (map_mul _ u.1 v.1)

/-- Evaluation of a jet of a gauge transformation at the base point, projecting the
  jet gauge group onto the gauge group `GaugeGroupI` by taking zeroth-order parts on
  each factor. -/
noncomputable def eval : JetGaugeGroupI →* GaugeGroupI :=
  (evalSU (Fin 3)).prodMap ((evalSU (Fin 2)).prodMap evalU1)


/-!

## The derivative

We define the derivative of an element of `JetGaugeGroupI` as a product of matrices,
and give some properties of it related to the Maurer–Cartan form.

-/

/-- The derivative of an element of `JetGaugeGroupI` returning
  a product of matrices. -/
noncomputable def deriv (μ : Fin 1 ⊕ Fin 3) (U : JetGaugeGroupI) :
    Matrix (Fin 3) (Fin 3) JetRing × Matrix (Fin 2) (Fin 2) JetRing × JetRing :=
  (U.1.1.map (pderiv ℂ μ), U.2.1.1.map (pderiv ℂ μ), pderiv ℂ μ U.2.2.1)


lemma deriv_mul (μ : Fin 1 ⊕ Fin 3) (U V : JetGaugeGroupI) :
    deriv μ (U * V) = deriv μ U * V.toVal + U.toVal * deriv μ V := by
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · show (U.1.1 * V.1.1).map (pderiv ℂ μ) =
      U.1.1.map (pderiv ℂ μ) * V.1.1 + U.1.1 * V.1.1.map (pderiv ℂ μ)
    ext i j : 1
    simp only [Matrix.map_apply, Matrix.mul_apply, Matrix.add_apply, map_sum,
      Derivation.leibniz, smul_eq_mul]
    exact (Finset.sum_congr rfl fun k _ => by ring).trans Finset.sum_add_distrib
  · show (U.2.1.1 * V.2.1.1).map (pderiv ℂ μ) =
      U.2.1.1.map (pderiv ℂ μ) * V.2.1.1 + U.2.1.1 * V.2.1.1.map (pderiv ℂ μ)
    ext i j : 1
    simp only [Matrix.map_apply, Matrix.mul_apply, Matrix.add_apply, map_sum,
      Derivation.leibniz, smul_eq_mul]
    exact (Finset.sum_congr rfl fun k _ => by ring).trans Finset.sum_add_distrib
  · show pderiv ℂ μ (U.2.2.1 * V.2.2.1) =
      pderiv ℂ μ U.2.2.1 * V.2.2.1 + U.2.2.1 * pderiv ℂ μ V.2.2.1
    rw [Derivation.leibniz]
    simp only [smul_eq_mul]
    ring

@[simp]
lemma deriv_one (μ : Fin 1 ⊕ Fin 3) : deriv μ (1 : JetGaugeGroupI) = 0 := by
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · show (1 : Matrix (Fin 3) (Fin 3) JetRing).map (pderiv ℂ μ) = 0
    ext i j : 1
    simp [Matrix.map_apply, Matrix.one_apply, apply_ite (pderiv ℂ μ)]
  · show (1 : Matrix (Fin 2) (Fin 2) JetRing).map (pderiv ℂ μ) = 0
    ext i j : 1
    simp [Matrix.map_apply, Matrix.one_apply, apply_ite (pderiv ℂ μ)]
  · show pderiv ℂ μ (1 : JetRing) = 0
    exact pderiv_one

lemma star_deriv (μ : Fin 1 ⊕ Fin 3) (U : JetGaugeGroupI) :
    star (deriv μ U) = deriv μ (star U) := by
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · show star (U.1.1.map (pderiv ℂ μ)) = (star U.1.1).map (pderiv ℂ μ)
    ext i j : 1
    simp only [Matrix.star_apply, Matrix.map_apply]
    exact (JetRing.pderiv_star μ (U.1.1 j i)).symm
  · show star (U.2.1.1.map (pderiv ℂ μ)) = (star U.2.1.1).map (pderiv ℂ μ)
    ext i j : 1
    simp only [Matrix.star_apply, Matrix.map_apply]
    exact (JetRing.pderiv_star μ (U.2.1.1 j i)).symm
  · show star (pderiv ℂ μ U.2.2.1) = pderiv ℂ μ (star U.2.2.1)
    exact (JetRing.pderiv_star μ U.2.2.1).symm

lemma deriv_mul_inv_toVal_SU3_traceless (μ : Fin 1 ⊕ Fin 3) (U : JetGaugeGroupI) :
    (Complex.I • (deriv μ U * (U⁻¹).toVal)).1.trace = 0 := by
  set A : Matrix (Fin 3) (Fin 3) JetRing := U.1.1 with hA
  have hU : A * star A = 1 := by
    have h := (mem_specialUnitaryGroup_iff.mp U.1.2).1
    rwa [mem_unitaryGroup_iff] at h
  have hdet : A.det = 1 := (mem_specialUnitaryGroup_iff.mp U.1.2).2
  have hadj : star A = A.adjugate := by
    have h1 : star A * A = 1 := mul_eq_one_comm.mp hU
    calc star A = star A * (A * A.adjugate) := by
          rw [Matrix.mul_adjugate, hdet, one_smul, mul_one]
      _ = star A * A * A.adjugate := by rw [mul_assoc]
      _ = A.adjugate := by rw [h1, one_mul]
  have jacobi : (A.map (pderiv ℂ μ) * A.adjugate).trace = pderiv ℂ μ A.det := by
    rw [Matrix.det_fin_three]
    simp only [Matrix.trace_fin_three, Matrix.mul_apply, Fin.sum_univ_three,
      Matrix.map_apply, Matrix.adjugate_fin_three, Matrix.of_apply, Matrix.cons_val',
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons, Matrix.head_fin_const, Matrix.empty_val', Matrix.cons_val_fin_one,
      map_sub, map_add, Derivation.leibniz, smul_eq_mul]
    ring
  rw [show (Complex.I • (deriv μ U * (U⁻¹).toVal)).1 =
      Complex.I • (A.map (pderiv ℂ μ) * star A) from rfl,
    Matrix.trace_smul, hadj, jacobi, hdet, pderiv_one, smul_zero]

lemma deriv_mul_inv_toVal_SU2_traceless (μ : Fin 1 ⊕ Fin 3) (U : JetGaugeGroupI) :
    (Complex.I • (deriv μ U * (U⁻¹).toVal)).2.1.trace = 0 := by
  set A : Matrix (Fin 2) (Fin 2) JetRing := U.2.1.1 with hA
  have hU : A * star A = 1 := by
    have h := (mem_specialUnitaryGroup_iff.mp U.2.1.2).1
    rwa [mem_unitaryGroup_iff] at h
  have hdet : A.det = 1 := (mem_specialUnitaryGroup_iff.mp U.2.1.2).2
  have hadj : star A = A.adjugate := by
    have h1 : star A * A = 1 := mul_eq_one_comm.mp hU
    calc star A = star A * (A * A.adjugate) := by
          rw [Matrix.mul_adjugate, hdet, one_smul, mul_one]
      _ = star A * A * A.adjugate := by rw [mul_assoc]
      _ = A.adjugate := by rw [h1, one_mul]
  have jacobi : (A.map (pderiv ℂ μ) * A.adjugate).trace = pderiv ℂ μ A.det := by
    rw [Matrix.det_fin_two]
    simp only [adjugate_fin_two, trace_fin_two, Matrix.mul_apply, map_apply, of_apply, cons_val',
      cons_val_zero, empty_val', cons_val_fin_one, Fin.sum_univ_two, cons_val_one, map_sub,
      Derivation.leibniz, smul_eq_mul]
    ring
  rw [show (Complex.I • (deriv μ U * (U⁻¹).toVal)).2.1 =
      Complex.I • (A.map (pderiv ℂ μ) * star A) from rfl,
    Matrix.trace_smul, hadj, jacobi, hdet, pderiv_one, smul_zero]

lemma star_deriv_mul_inv_toVal_SU3 (μ : Fin 1 ⊕ Fin 3) (U : JetGaugeGroupI) :
    star ((Complex.I • (deriv μ U * (U⁻¹).toVal)).1) =
    (Complex.I • (deriv μ U * (U⁻¹).toVal)).1 := by
  set A : Matrix (Fin 3) (Fin 3) JetRing := U.1.1 with hA
  -- differentiate the unitarity relation `U U⁻¹ = 1` with the Leibniz rule `deriv_mul`
  have h := deriv_mul μ U U⁻¹
  rw [mul_inv_cancel, deriv_one] at h
  have hq : A * ((star A).map (pderiv ℂ μ)) = -(A.map (pderiv ℂ μ) * star A) :=
    congrArg (fun p => p.1) (eq_neg_of_add_eq_zero_right h.symm)
  have hstarmap : star (A.map (pderiv ℂ μ)) = (star A).map (pderiv ℂ μ) :=
    congrArg (fun p => p.1) (star_deriv μ U)
  -- rewrite the `ℂ`-scalar `i` as the constant series `C i`, acting through `JetRing`
  have hCs : (Complex.I • (deriv μ U * (U⁻¹).toVal)).1 =
      (MvPowerSeries.C Complex.I : JetRing) • (A.map (pderiv ℂ μ) * star A) := by
    rw [show (Complex.I • (deriv μ U * (U⁻¹).toVal)).1 =
        Complex.I • (A.map (pderiv ℂ μ) * star A) from rfl]
    ext i j
    simp only [Matrix.smul_apply, smul_eq_mul, Algebra.smul_def,
      MvPowerSeries.algebraMap_apply]
    simp
  -- the star flips `i` to `-i` and the differentiated unitarity flips the product back
  rw [hCs, star_smul, star_mul, star_star, hstarmap, hq, JetRing.star_C,
    show (star Complex.I) = -Complex.I by simp, map_neg, neg_smul, smul_neg, neg_neg]

lemma star_deriv_mul_inv_toVal_SU2 (μ : Fin 1 ⊕ Fin 3) (U : JetGaugeGroupI) :
    star ((Complex.I • (deriv μ U * (U⁻¹).toVal)).2.1) =
    (Complex.I • (deriv μ U * (U⁻¹).toVal)).2.1 := by
  set A : Matrix (Fin 2) (Fin 2) JetRing := U.2.1.1 with hA
  -- differentiate the unitarity relation `U U⁻¹ = 1` with the Leibniz rule `deriv_mul`
  have h := deriv_mul μ U U⁻¹
  rw [mul_inv_cancel, deriv_one] at h
  have hq : A * ((star A).map (pderiv ℂ μ)) = -(A.map (pderiv ℂ μ) * star A) :=
    congrArg (fun p => p.2.1) (eq_neg_of_add_eq_zero_right h.symm)
  have hstarmap : star (A.map (pderiv ℂ μ)) = (star A).map (pderiv ℂ μ) :=
    congrArg (fun p => p.2.1) (star_deriv μ U)
  -- rewrite the `ℂ`-scalar `i` as the constant series `C i`, acting through `JetRing`
  have hCs : (Complex.I • (deriv μ U * (U⁻¹).toVal)).2.1 =
      (MvPowerSeries.C Complex.I : JetRing) • (A.map (pderiv ℂ μ) * star A) := by
    rw [show (Complex.I • (deriv μ U * (U⁻¹).toVal)).2.1 =
        Complex.I • (A.map (pderiv ℂ μ) * star A) from rfl]
    ext i j
    simp only [Matrix.smul_apply, smul_eq_mul, Algebra.smul_def,
      MvPowerSeries.algebraMap_apply]
    simp
  -- the star flips `i` to `-i` and the differentiated unitarity flips the product back
  rw [hCs, star_smul, star_mul, star_star, hstarmap, hq, JetRing.star_C,
    show (star Complex.I) = -Complex.I by simp, map_neg, neg_smul, smul_neg, neg_neg]

lemma star_deriv_mul_inv_toVal_U1 (μ : Fin 1 ⊕ Fin 3) (U : JetGaugeGroupI) :
    star ((Complex.I • (deriv μ U * (U⁻¹).toVal)).2.2) =
    (Complex.I • (deriv μ U * (U⁻¹).toVal)).2.2 := by
  set u : JetRing := U.2.2.1 with hu'
  -- differentiate the unitarity relation `U U⁻¹ = 1` with the Leibniz rule `deriv_mul`
  have h := deriv_mul μ U U⁻¹
  rw [mul_inv_cancel, deriv_one] at h
  have hq : pderiv ℂ μ (star u) * u = -(pderiv ℂ μ u * star u) :=
    (mul_comm _ _).trans (congrArg (fun p => p.2.2) (eq_neg_of_add_eq_zero_right h.symm))
  -- rewrite the `ℂ`-scalar `i` as the constant series `C i`, acting through `JetRing`
  have hCs : (Complex.I • (deriv μ U * (U⁻¹).toVal)).2.2 =
      (MvPowerSeries.C Complex.I : JetRing) * (pderiv ℂ μ u * star u) := by
    rw [show (Complex.I • (deriv μ U * (U⁻¹).toVal)).2.2 =
        Complex.I • (pderiv ℂ μ u * star u) from rfl,
      Algebra.smul_def, MvPowerSeries.algebraMap_apply]
    simp
  -- the star flips `i` to `-i` and the differentiated unitarity flips the product back
  rw [hCs, star_mul', JetRing.star_C, star_mul', star_star, ← JetRing.pderiv_star, hq,
    show (star Complex.I) = -Complex.I by simp, map_neg, neg_mul, mul_neg, neg_neg]


/-- The iterated formal derivative, in the (unordered) directions given by the
  multiset `s`, of the value of a jet gauge transformation, taken entrywise on each
  factor. This is the derivative-normalized Taylor coefficient of `U` at `s`, as a jet:
  its value at the base point is `∏ (s.count μ)!` times the power-series coefficient
  of `U` at the monomial `s`. -/
noncomputable def iteratedDeriv (s : Multiset (Fin 1 ⊕ Fin 3)) (U : JetGaugeGroupI) :
    Matrix (Fin 3) (Fin 3) JetRing × Matrix (Fin 2) (Fin 2) JetRing × JetRing :=
  (U.1.1.map fun f => s.foldl (fun f μ => pderiv ℂ μ f) f,
    U.2.1.1.map fun f => s.foldl (fun f μ => pderiv ℂ μ f) f,
    s.foldl (fun f μ => pderiv ℂ μ f) U.2.2.1)

/-!

## D. Constant jets

The constant power series embed the gauge group `GaugeGroupI` into the jet gauge
group, as the jets of constant (global) gauge transformations. This is a section of
the evaluation `eval`.

-/

/-- Entrywise inclusion of constants commutes with the conjugate transpose. -/
lemma mapMatrix_C_star {n : Type} [Fintype n] [DecidableEq n] (A : Matrix n n ℂ) :
    (C : ℂ →+* JetRing).mapMatrix (star A) = star ((C : ℂ →+* JetRing).mapMatrix A) := by
  ext i j
  simp [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.star_apply]

/-- The jet of a constant special-unitary gauge transformation: the entrywise
  inclusion of constants. -/
noncomputable def ofConstantSU (n : Type) [Fintype n] [DecidableEq n] :
    specialUnitaryGroup n ℂ →* specialUnitaryGroup n JetRing where
  toFun u := ⟨(C : ℂ →+* JetRing).mapMatrix u.1, by
    obtain ⟨h1, h2⟩ := mem_specialUnitaryGroup_iff.mp u.2
    rw [mem_specialUnitaryGroup_iff]
    constructor
    · rw [mem_unitaryGroup_iff] at h1 ⊢
      rw [show star ((C : ℂ →+* JetRing).mapMatrix u.1) =
          (C : ℂ →+* JetRing).mapMatrix (star u.1) from (mapMatrix_C_star u.1).symm,
        ← map_mul, h1, map_one]
    · rw [← RingHom.map_det, h2, map_one]⟩
  map_one' := Subtype.ext (map_one ((C : ℂ →+* JetRing).mapMatrix))
  map_mul' u v := Subtype.ext (map_mul ((C : ℂ →+* JetRing).mapMatrix) u.1 v.1)

/-- The jet of a constant `U(1)` gauge transformation: the inclusion of constants. -/
noncomputable def ofConstantU1 : unitary ℂ →* unitary JetRing where
  toFun u := ⟨C u.1, by
    obtain ⟨h1, h2⟩ := Unitary.mem_iff.mp u.2
    exact Unitary.mem_iff.mpr
      ⟨by rw [star_C, ← map_mul, h1, map_one],
        by rw [star_C, ← map_mul, h2, map_one]⟩⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' u v := Subtype.ext (map_mul _ u.1 v.1)

/-- The embedding of the gauge group into the jet gauge group as the jets of
  constant (global) gauge transformations. -/
noncomputable def ofConstant : GaugeGroupI →* JetGaugeGroupI :=
  (ofConstantSU (Fin 3)).prodMap ((ofConstantSU (Fin 2)).prodMap ofConstantU1)

/-- Evaluating the jet of a constant gauge transformation at the base point recovers
  the gauge transformation: `ofConstant` is a section of `eval`. -/
@[simp]
lemma eval_ofConstant (g : GaugeGroupI) : eval (ofConstant g) = g := by
  refine Prod.ext (Subtype.ext ?_) (Prod.ext (Subtype.ext ?_) (Subtype.ext ?_))
  · ext i j
    simp [eval, ofConstant, evalSU, ofConstantSU,
      RingHom.mapMatrix_apply, Matrix.map_apply]
  · ext i j
    simp [eval, ofConstant, evalSU, ofConstantSU,
      RingHom.mapMatrix_apply, Matrix.map_apply]
  · simp [eval, ofConstant, evalU1, ofConstantU1]

@[simp]
lemma deriv_ofConstant (μ : Fin 1 ⊕ Fin 3) (U₀ : GaugeGroupI) :
    deriv μ (JetGaugeGroupI.ofConstant U₀) = 0 := by
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · show ((C : ℂ →+* JetRing).mapMatrix U₀.1.1).map (pderiv ℂ μ) = 0
    ext i j : 1
    simp [RingHom.mapMatrix_apply, Matrix.map_apply, pderiv_C]
  · show ((C : ℂ →+* JetRing).mapMatrix U₀.2.1.1).map (pderiv ℂ μ) = 0
    ext i j : 1
    simp [RingHom.mapMatrix_apply, Matrix.map_apply, pderiv_C]
  · show pderiv ℂ μ (C U₀.2.2.1 : JetRing) = 0
    simp [pderiv_C]

end JetGaugeGroupI

end StandardModel
