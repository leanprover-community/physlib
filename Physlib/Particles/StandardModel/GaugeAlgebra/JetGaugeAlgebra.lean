/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Particles.StandardModel.Basic
public import Physlib.Particles.StandardModel.GaugeAlgebra.Basic
public import Physlib.Particles.StandardModel.GaugeGroup.Jet.Basic
public import Physlib.Relativity.Tensors.ComplexTensor.Basic
public import Physlib.Relativity.Tensors.RealTensor.Vector.Basic
public import Physlib.Relativity.Tensors.RealTensor.Vector.Representation
public import Physlib.Relativity.SL2C.Basic
public import Physlib.Mathematics.ConjModule
public import Mathlib.LinearAlgebra.ExteriorAlgebra.Basis
public import Physlib.Particles.LagrangianTheory.Basic
public import Mathlib.RingTheory.MvPowerSeries.Derivative
public import Physlib.Mathematics.MvPolynomialTranslation
public import Mathlib.Algebra.MvPolynomial.Derivation
public import Mathlib.Analysis.Normed.Algebra.Exponential
public import Mathlib.RingTheory.MvPowerSeries.PiTopology
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.RingTheory.PowerSeries.Derivative
public import Mathlib.RingTheory.PowerSeries.Basic
/-!
# The jet gauge algebra

We define `JetGaugeAlgebra` as the Lie algebra of `JetGaugeGroupI`,
defined explicitly as traceless self-adjoint matrices, and giving it an instance `LieAlgebra`.
This is a matrix Lie algebra, so the bracket is given by the commutator of matrices.

Note here that `JetGaugeAlgebra` is a module over `ℝ` not `ℂ` or `JetRing`.

On this Lie algebra define a prefered basis, `basis`, indexed by
`basisIndex × Multiset (Fin 1 ⊕ Fin 3)`.
Here `basisIndex` is the sum `Fin 8 ⊕ Fin 3 ⊕ Fin 1`. The first factor
corresponds to the Gell-Mann matrices which form a basis of `su(3)`,
the second factor corresponds to the Pauli matrices which form a basis of `su(2)`,
and the third factor corresponds to the identity matrix which forms a basis of `u(1)`.

We let `structuralConstant` (typically called `f`) be the structure constants of the Lie algebra
with respect to this prefered basis, so that
```
  [basis i, basis j] = i * ∑ k, structuralConstant i j k • basis k
```

On `JetGaugeAlgebra` we define the adjoint representation of `JetGaugeGroupI`,
`adjointRep`, which acts via `x ↦ g * x * g⁻¹`.

There is also a derivative `deriv : Fin 1 ⊕ Fin 3 → JetLieAlgebra →ₗ[ℝ] JetLieAlgebra`
whose action can be defined componentwise in terms of the basis.

The derivative acts on brackets via the Leibniz rule:
```
  deriv μ [x, y] = [deriv μ x, y] + [x, deriv μ y]
```

-/

@[expose] public section

namespace StandardModel
open MvPowerSeries Matrix

/-- The jet gauge algebra: the Lie-algebra analogue of `JetGaugeGroupI`, with one factor per
  gauge group factor — traceless self-adjoint `3 × 3` and `2 × 2` matrices and a self-adjoint
  scalar, all with coefficients in the ring `JetRing` of formal power series in the spacetime
  coordinates. The Maurer–Cartan forms of the jet gauge group are valued here, hermiticity
  being `star_maurerCartanSU3` and its companions. -/
abbrev JetGaugeAlgebra :=
  ↥(selfAdjoint.submodule ℝ (Matrix (Fin 3) (Fin 3) JetRing) ⊓
    LinearMap.ker (Matrix.traceLinearMap (Fin 3) ℝ JetRing)) ×
  ↥(selfAdjoint.submodule ℝ (Matrix (Fin 2) (Fin 2) JetRing) ⊓
    LinearMap.ker (Matrix.traceLinearMap (Fin 2) ℝ JetRing)) ×
  selfAdjoint JetRing

namespace JetGaugeAlgebra

/-!

## Basic projections

-/

/-- The `su(3)`-factor component of an element of the jet gauge algebra. -/
def toSU3Matrix (a : JetGaugeAlgebra) : Matrix (Fin 3) (Fin 3) JetRing := a.1

/-- The `su(2)`-factor component of an element of the jet gauge algebra. -/
def toSU2Matrix (a : JetGaugeAlgebra) : Matrix (Fin 2) (Fin 2) JetRing  := a.2.1

/-- The `u(1)`-factor component of an element of the jet gauge algebra. -/
def toU1Value (a : JetGaugeAlgebra) :  JetRing := a.2.2

/-- The underlying matrix value of an element of the jet gauge algebra, as a
  product of matrices. -/
def toVal (a : JetGaugeAlgebra) :
    Matrix (Fin 3) (Fin 3) JetRing × Matrix (Fin 2) (Fin 2) JetRing × JetRing :=
  (a.toSU3Matrix, a.toSU2Matrix, a.toU1Value)

@[simp]
lemma toVal_fst (a : JetGaugeAlgebra) : a.toVal.1 = a.toSU3Matrix := rfl

@[simp]
lemma toVal_snd_fst (a : JetGaugeAlgebra) : a.toVal.2.1 = a.toSU2Matrix := rfl

@[simp]
lemma toVal_snd_snd (a : JetGaugeAlgebra) : a.toVal.2.2 = a.toU1Value := rfl

@[ext]
lemma ext_of_matrix {a b : JetGaugeAlgebra} (h1 : a.toSU3Matrix = b.toSU3Matrix)
    (h2 : a.toSU2Matrix = b.toSU2Matrix) (h3 : a.toU1Value = b.toU1Value) : a = b := by
  cases a; cases b
  simp only [toSU3Matrix, toSU2Matrix, toU1Value] at h1 h2 h3
  grind

/-!

## Constructor from a product of matrices

-/

def ofMatrixProd (A : Matrix (Fin 3) (Fin 3) JetRing ×
    Matrix (Fin 2) (Fin 2) JetRing × JetRing) (hA : star A.1 = A.1 ∧ A.1.trace = 0)
    (hB : star A.2.1 = A.2.1 ∧ A.2.1.trace = 0) (hC : star A.2.2 = A.2.2) : JetGaugeAlgebra :=
  ⟨⟨A.1, hA⟩, ⟨A.2.1, hB⟩, ⟨A.2.2, hC⟩⟩

@[simp]
lemma ofMatrixProd_toSU3Matrix (A : Matrix (Fin 3) (Fin 3) JetRing ×
    Matrix (Fin 2) (Fin 2) JetRing × JetRing) (hA : star A.1 = A.1 ∧ A.1.trace = 0)
    (hB : star A.2.1 = A.2.1 ∧ A.2.1.trace = 0) (hC : star A.2.2 = A.2.2) :
    (ofMatrixProd A hA hB hC).toSU3Matrix = A.1 := by rfl

@[simp]
lemma ofMatrixProd_toSU2Matrix (A : Matrix (Fin 3) (Fin 3) JetRing ×
    Matrix (Fin 2) (Fin 2) JetRing × JetRing) (hA : star A.1 = A.1 ∧ A.1.trace = 0)
    (hB : star A.2.1 = A.2.1 ∧ A.2.1.trace = 0) (hC : star A.2.2 = A.2.2) :
    (ofMatrixProd A hA hB hC).toSU2Matrix = A.2.1 := by rfl

@[simp]
lemma ofMatrixProd_toU1Value (A : Matrix (Fin 3) (Fin 3) JetRing ×
    Matrix (Fin 2) (Fin 2) JetRing × JetRing) (hA : star A.1 = A.1 ∧ A.1.trace = 0)
    (hB : star A.2.1 = A.2.1 ∧ A.2.1.trace = 0) (hC : star A.2.2 = A.2.2) :
    (ofMatrixProd A hA hB hC).toU1Value = A.2.2 := by rfl

/-!

## The Lie algebra instance

-/

@[simp]
lemma add_toSU3Matrix (a b : JetGaugeAlgebra) :
    (a + b).toSU3Matrix = a.toSU3Matrix + b.toSU3Matrix := by rfl

@[simp]
lemma add_toSU2Matrix (a b : JetGaugeAlgebra) :
    (a + b).toSU2Matrix = a.toSU2Matrix + b.toSU2Matrix := by rfl

@[simp]
lemma add_toU1Value (a b : JetGaugeAlgebra) :
    (a + b).toU1Value = a.toU1Value + b.toU1Value := by rfl

@[simp]
lemma zero_toSU3Matrix : (0 : JetGaugeAlgebra).toSU3Matrix = 0 := by rfl

@[simp]
lemma zero_toSU2Matrix : (0 : JetGaugeAlgebra).toSU2Matrix = 0 := by rfl

@[simp]
lemma zero_toU1Value : (0 : JetGaugeAlgebra).toU1Value = 0 := by rfl

@[simp]
lemma smul_toSU3Matrix (r : ℝ) (a : JetGaugeAlgebra) :
    (r • a).toSU3Matrix = r • a.toSU3Matrix := by rfl

@[simp]
lemma smul_toSU2Matrix (r : ℝ) (a : JetGaugeAlgebra) :
    (r • a).toSU2Matrix = r • a.toSU2Matrix := by rfl

@[simp]
lemma smul_toU1Value (r : ℝ) (a : JetGaugeAlgebra) :
    (r • a).toU1Value = r • a.toU1Value := by rfl

@[simp]
lemma sub_toSU3Matrix (a b : JetGaugeAlgebra) :
    (a - b).toSU3Matrix = a.toSU3Matrix - b.toSU3Matrix := by rfl

@[simp]
lemma sub_toSU2Matrix (a b : JetGaugeAlgebra) :
    (a - b).toSU2Matrix = a.toSU2Matrix - b.toSU2Matrix := by rfl

@[simp]
lemma sub_toU1Value (a b : JetGaugeAlgebra) :
    (a - b).toU1Value = a.toU1Value - b.toU1Value := by rfl

/-- The bracket on the jet gauge algebra: `I` times the matrix commutator on the
  `su(3)` and `su(2)` factors, and zero on the (commutative) `u(1)` factor. The
  factor of `I` is what makes the bracket of two hermitian matrices hermitian
  again; it is also why the bracket is only `ℝ`-bilinear, not `ℂ`-bilinear. -/
noncomputable instance : Bracket JetGaugeAlgebra JetGaugeAlgebra where
  bracket a b := ofMatrixProd
      (Complex.I • (a.toSU3Matrix * b.toSU3Matrix - b.toSU3Matrix * a.toSU3Matrix),
        Complex.I • (a.toSU2Matrix * b.toSU2Matrix - b.toSU2Matrix * a.toSU2Matrix),
        0)
      ⟨by
        rw [star_smul, star_sub, star_mul, star_mul,
          show star a.toSU3Matrix = a.toSU3Matrix from a.1.2.1,
          show star b.toSU3Matrix = b.toSU3Matrix from b.1.2.1,
          Complex.star_def, Complex.conj_I, neg_smul, ← smul_neg, neg_sub],
        by rw [Matrix.trace_smul, Matrix.trace_sub, Matrix.trace_mul_comm, sub_self, smul_zero]⟩
      ⟨by
        rw [star_smul, star_sub, star_mul, star_mul,
          show star a.toSU2Matrix = a.toSU2Matrix from a.2.1.2.1,
          show star b.toSU2Matrix = b.toSU2Matrix from b.2.1.2.1,
          Complex.star_def, Complex.conj_I, neg_smul, ← smul_neg, neg_sub],
        by rw [Matrix.trace_smul, Matrix.trace_sub, Matrix.trace_mul_comm, sub_self, smul_zero]⟩
      (star_zero _)

@[simp]
lemma bracket_toSU3Matrix (a b : JetGaugeAlgebra) :
    ⁅a, b⁆.toSU3Matrix =
      Complex.I • (a.toSU3Matrix * b.toSU3Matrix - b.toSU3Matrix * a.toSU3Matrix) := rfl

@[simp]
lemma bracket_toSU2Matrix (a b : JetGaugeAlgebra) :
    ⁅a, b⁆.toSU2Matrix =
      Complex.I • (a.toSU2Matrix * b.toSU2Matrix - b.toSU2Matrix * a.toSU2Matrix) := rfl

@[simp]
lemma bracket_toU1Value (a b : JetGaugeAlgebra) :
    ⁅a, b⁆.toU1Value = 0 := rfl

noncomputable instance : LieRing JetGaugeAlgebra where
  add_lie a b c := by
    ext <;> simp [add_mul, mul_add, smul_add, smul_sub] <;> abel
  lie_add a b c := by
    ext <;> simp [add_mul, mul_add, smul_add, smul_sub] <;> abel
  lie_self a := by
    ext <;> simp
  leibniz_lie a b c := by
    refine ext_of_matrix ?_ ?_ ?_ <;>
      simp only [bracket_toSU3Matrix, bracket_toSU2Matrix, bracket_toU1Value,
        add_toSU3Matrix, add_toSU2Matrix, add_toU1Value, mul_smul_comm, smul_mul_assoc,
        smul_smul, Complex.I_mul_I, smul_sub, mul_sub, sub_mul, mul_assoc, add_zero] <;>
      module

noncomputable instance : LieAlgebra ℝ JetGaugeAlgebra where
  lie_smul r a b := by refine ext_of_matrix ?_ ?_ ?_ <;> simp <;> module

/-!

## The derivative on the jet gauge algebra

-/

/-- The formal derivative in the direction `μ` on the jet gauge algebra, acting
  entrywise on each factor. It preserves hermiticity since `star` commutes with
  `pderiv`, and tracelessness since the trace of the entrywise derivative is the
  derivative of the trace. -/
noncomputable def deriv (μ : Fin 1 ⊕ Fin 3) : JetGaugeAlgebra →ₗ[ℝ] JetGaugeAlgebra where
  toFun a := ofMatrixProd
      (a.toSU3Matrix.map (pderiv ℂ μ), a.toSU2Matrix.map (pderiv ℂ μ),
        pderiv ℂ μ a.toU1Value)
      ⟨by
        ext i j : 1
        simpa [Matrix.star_apply, Matrix.map_apply, ← JetRing.pderiv_star] using
          congrArg (fun M => pderiv ℂ μ (M i j))
            (show star a.toSU3Matrix = a.toSU3Matrix from a.1.2.1),
        by rw [← AddMonoidHom.map_trace, show a.toSU3Matrix.trace = 0 from a.1.2.2, map_zero]⟩
      ⟨by
        ext i j : 1
        simpa [Matrix.star_apply, Matrix.map_apply, ← JetRing.pderiv_star] using
          congrArg (fun M => pderiv ℂ μ (M i j))
            (show star a.toSU2Matrix = a.toSU2Matrix from a.2.1.2.1),
        by rw [← AddMonoidHom.map_trace, show a.toSU2Matrix.trace = 0 from a.2.1.2.2, map_zero]⟩
      (by rw [← JetRing.pderiv_star, show star a.toU1Value = a.toU1Value from a.2.2.2])
  map_add' a b := by
    ext <;> simp [Matrix.map_apply]
  map_smul' r a := by
    refine ext_of_matrix ?_ ?_ ?_ <;>
      simp only [ofMatrixProd_toSU3Matrix, ofMatrixProd_toSU2Matrix, ofMatrixProd_toU1Value,
        smul_toSU3Matrix, smul_toSU2Matrix, smul_toU1Value, RingHom.id_apply]
    · ext i j : 1
      simp only [Matrix.map_apply, Matrix.smul_apply]
      rw [← algebraMap_smul ℂ r, Derivation.map_smul, algebraMap_smul]
    · ext i j : 1
      simp only [Matrix.map_apply, Matrix.smul_apply]
      rw [← algebraMap_smul ℂ r, Derivation.map_smul, algebraMap_smul]
    · rw [← algebraMap_smul ℂ r, Derivation.map_smul, algebraMap_smul]

@[simp]
lemma deriv_toSU3Matrix (μ : Fin 1 ⊕ Fin 3) (a : JetGaugeAlgebra) :
    (deriv μ a).toSU3Matrix = a.toSU3Matrix.map (pderiv ℂ μ) := rfl

@[simp]
lemma deriv_toSU2Matrix (μ : Fin 1 ⊕ Fin 3) (a : JetGaugeAlgebra) :
    (deriv μ a).toSU2Matrix = a.toSU2Matrix.map (pderiv ℂ μ) := rfl

@[simp]
lemma deriv_toU1Value (μ : Fin 1 ⊕ Fin 3) (a : JetGaugeAlgebra) :
    (deriv μ a).toU1Value = pderiv ℂ μ a.toU1Value := rfl

/-- Formal derivatives on the jet gauge algebra commute. -/
lemma deriv_comm (μ ν : Fin 1 ⊕ Fin 3) (a : JetGaugeAlgebra) :
    deriv μ (deriv ν a) = deriv ν (deriv μ a) := by
  refine ext_of_matrix ?_ ?_ ?_
  · ext i j : 1
    simp [Matrix.map_apply, JetRing.pderiv_comm μ ν]
  · ext i j : 1
    simp [Matrix.map_apply, JetRing.pderiv_comm μ ν]
  · exact JetRing.pderiv_comm μ ν _

/-- The derivative is a derivation of the bracket: the Leibniz rule
  `deriv μ ⁅x, y⁆ = ⁅deriv μ x, y⁆ + ⁅x, deriv μ y⁆`. -/
lemma deriv_bracket (μ : Fin 1 ⊕ Fin 3) (x y : JetGaugeAlgebra) :
    deriv μ ⁅x, y⁆ = ⁅deriv μ x, y⁆ + ⁅x, deriv μ y⁆ := by
  have hleib : ∀ (κ : Type) [Fintype κ] [DecidableEq κ] (M N : Matrix κ κ JetRing),
      (M * N).map (pderiv ℂ μ) = M.map (pderiv ℂ μ) * N + M * N.map (pderiv ℂ μ) := by
    intro κ _ _ M N
    ext i j : 1
    simp only [Matrix.map_apply, Matrix.mul_apply, Matrix.add_apply, map_sum,
      Derivation.leibniz, smul_eq_mul]
    exact (Finset.sum_congr rfl fun k _ => by ring).trans Finset.sum_add_distrib
  have hsmul : ∀ (κ : Type) [Fintype κ] [DecidableEq κ] (c : ℂ) (M : Matrix κ κ JetRing),
      (c • M).map (pderiv ℂ μ) = c • M.map (pderiv ℂ μ) :=
    fun _ _ _ _ _ => Matrix.ext fun _ _ => Derivation.map_smul _ _ _
  have hsub : ∀ (κ : Type) [Fintype κ] [DecidableEq κ] (M N : Matrix κ κ JetRing),
      (M - N).map (pderiv ℂ μ) = M.map (pderiv ℂ μ) - N.map (pderiv ℂ μ) := by
    intro κ _ _ M N
    ext i j : 1
    simp only [Matrix.map_apply, Matrix.sub_apply, map_sub]
  refine ext_of_matrix ?_ ?_ ?_ <;>
    simp only [deriv_toSU3Matrix, deriv_toSU2Matrix, deriv_toU1Value, bracket_toSU3Matrix,
      bracket_toSU2Matrix, bracket_toU1Value, add_toSU3Matrix, add_toSU2Matrix,
      add_toU1Value, hsmul, hsub, hleib, map_zero, add_zero]
  · rw [← smul_add]
    congr 1
    abel
  · rw [← smul_add]
    congr 1
    abel

/-!

## The iterated derivative

-/
/-- Post-composition with `deriv` is right-commutative, since formal derivatives
  commute (`deriv_comm`). This is what allows iterated derivatives to be indexed by a
  `Multiset` of directions. -/
instance : RightCommutative
    (fun (D : JetGaugeAlgebra →ₗ[ℝ] JetGaugeAlgebra) (μ : Fin 1 ⊕ Fin 3) => D.comp (deriv μ)) where
  right_comm D μ ν := by
    refine LinearMap.ext fun a => ?_
    exact congrArg D (deriv_comm μ ν a)

/-- The iterated formal derivative on the jet gauge algebra, in the (unordered, since
  derivatives commute) directions given by the multiset `μs`. -/
noncomputable def iteratedDeriv (μs : Multiset (Fin 1 ⊕ Fin 3)) :
    JetGaugeAlgebra →ₗ[ℝ] JetGaugeAlgebra :=
  μs.foldl (fun D μ => D.comp (deriv μ)) LinearMap.id

@[simp]
lemma iteratedDeriv_zero : iteratedDeriv 0 = LinearMap.id := by
  simp [iteratedDeriv]

lemma iteratedDeriv_cons (μ : Fin 1 ⊕ Fin 3) (μs : Multiset (Fin 1 ⊕ Fin 3)) :
    iteratedDeriv (μ ::ₘ μs) = (deriv μ).comp (iteratedDeriv μs) := by
  have h : ∀ (s : Multiset (Fin 1 ⊕ Fin 3)) (D : JetGaugeAlgebra →ₗ[ℝ] JetGaugeAlgebra),
      s.foldl (fun D μ => D.comp (deriv μ)) D = D.comp (iteratedDeriv s) := by
    intro s
    induction s using Multiset.induction_on with
    | empty => intro D; simp [iteratedDeriv]
    | cons κ t ih =>
        intro D
        rw [iteratedDeriv, Multiset.foldl_cons, Multiset.foldl_cons, ih, ih]
        simp [LinearMap.comp_assoc]
  rw [iteratedDeriv, Multiset.foldl_cons, h]
  simp

/-- The iterated derivative is additive in the multiset of directions: deriving
  along `s + t` is deriving along `t` and then along `s`. -/
lemma iteratedDeriv_add (s t : Multiset (Fin 1 ⊕ Fin 3)) :
    iteratedDeriv (s + t) = (iteratedDeriv s).comp (iteratedDeriv t) := by
  induction s using Multiset.induction_on with
  | empty => simp [iteratedDeriv_zero]
  | cons μ s ih =>
      rw [Multiset.cons_add, iteratedDeriv_cons, iteratedDeriv_cons, ih,
        LinearMap.comp_assoc]

@[simp]
lemma iteratedDeriv_singleton (μ : Fin 1 ⊕ Fin 3) :
    iteratedDeriv ({μ} : Multiset (Fin 1 ⊕ Fin 3)) = deriv μ := by
  rw [show ({μ} : Multiset (Fin 1 ⊕ Fin 3)) = μ ::ₘ 0 from rfl, iteratedDeriv_cons,
    iteratedDeriv_zero, LinearMap.comp_id]

/-- The iterated Leibniz rule for the bracket: the iterated derivative of a bracket
  is the antidiagonal convolution of iterated derivatives of the two arguments. -/
lemma iteratedDeriv_bracket (s : Multiset (Fin 1 ⊕ Fin 3)) (a b : JetGaugeAlgebra) :
    iteratedDeriv s ⁅a, b⁆ =
      (s.antidiagonal.map fun p => ⁅iteratedDeriv p.1 a, iteratedDeriv p.2 b⁆).sum := by
  induction s using Multiset.induction_on with
  | empty => simp [Multiset.antidiagonal_zero]
  | cons κ s ih =>
      rw [iteratedDeriv_cons, LinearMap.comp_apply, ih, map_multiset_sum,
        Multiset.map_map,
        Multiset.map_congr rfl (fun p hp => by
          rw [Function.comp_apply, deriv_bracket,
            show deriv κ (iteratedDeriv p.1 a) = iteratedDeriv (κ ::ₘ p.1) a from by
              rw [iteratedDeriv_cons]; rfl,
            show deriv κ (iteratedDeriv p.2 b) = iteratedDeriv (κ ::ₘ p.2) b from by
              rw [iteratedDeriv_cons]; rfl]),
        Multiset.sum_map_add]
      simp only [Multiset.antidiagonal_cons, Multiset.map_add, Multiset.sum_add,
        Multiset.map_map, Function.comp_apply, Prod.map_fst, Prod.map_snd, id_eq]
      abel




lemma iteratedDeriv_toSU3Matrix (s : Multiset (Fin 1 ⊕ Fin 3)) (a : JetGaugeAlgebra) :
    (iteratedDeriv s a).toSU3Matrix =
      a.toSU3Matrix.map fun f => s.foldl (fun f ρ => pderiv ℂ ρ f) f := by
  induction s using Multiset.induction_on with
  | empty => simp [iteratedDeriv_zero]
  | cons μ t ih =>
      rw [iteratedDeriv_cons, LinearMap.comp_apply, deriv_toSU3Matrix, ih]
      ext i j : 1
      simp only [Matrix.map_apply, Multiset.foldl_cons]
      exact (JetRing.foldl_pderiv_pderiv t μ _).symm

lemma iteratedDeriv_toSU2Matrix (s : Multiset (Fin 1 ⊕ Fin 3)) (a : JetGaugeAlgebra) :
    (iteratedDeriv s a).toSU2Matrix =
      a.toSU2Matrix.map fun f => s.foldl (fun f ρ => pderiv ℂ ρ f) f := by
  induction s using Multiset.induction_on with
  | empty => simp [iteratedDeriv_zero]
  | cons μ t ih =>
      rw [iteratedDeriv_cons, LinearMap.comp_apply, deriv_toSU2Matrix, ih]
      ext i j : 1
      simp only [Matrix.map_apply, Multiset.foldl_cons]
      exact (JetRing.foldl_pderiv_pderiv t μ _).symm

lemma iteratedDeriv_toU1Value (s : Multiset (Fin 1 ⊕ Fin 3)) (a : JetGaugeAlgebra) :
    (iteratedDeriv s a).toU1Value = s.foldl (fun f ρ => pderiv ℂ ρ f) a.toU1Value := by
  induction s using Multiset.induction_on with
  | empty => simp [iteratedDeriv_zero]
  | cons μ t ih =>
      rw [iteratedDeriv_cons, LinearMap.comp_apply, deriv_toU1Value, ih,
        Multiset.foldl_cons, JetRing.foldl_pderiv_pderiv]


/-!

## Taylor coefficients and evaluation at the base point

-/

/-- The Taylor coefficient of an element of the jet gauge algebra at the monomial
  given by the multiset `r` of spacetime directions, taken entrywise, as an
  `ℝ`-linear map to the constant gauge algebra `GaugeAlgebra`.

  For `r ≠ 0` this is only linear: the coefficient of a product is a convolution of
  coefficients, so it does not respect the bracket. The zeroth coefficient does; see
  `eval` for that morphism of Lie algebras. -/
noncomputable def taylorCoeff (r : Multiset (Fin 1 ⊕ Fin 3)) :
    JetGaugeAlgebra →ₗ[ℝ] GaugeAlgebra where
  toFun a := GaugeAlgebra.ofMatrixProd
      (a.toSU3Matrix.map (coeff r.toFinsupp), a.toSU2Matrix.map (coeff r.toFinsupp),
        coeff r.toFinsupp a.toU1Value)
      ⟨by
        ext i j : 1
        simpa [Matrix.star_apply, Matrix.map_apply] using
          congrArg (fun M => coeff r.toFinsupp (M i j))
            (show star a.toSU3Matrix = a.toSU3Matrix from a.1.2.1),
        by rw [← AddMonoidHom.map_trace, show a.toSU3Matrix.trace = 0 from a.1.2.2, map_zero]⟩
      ⟨by
        ext i j : 1
        simpa [Matrix.star_apply, Matrix.map_apply] using
          congrArg (fun M => coeff r.toFinsupp (M i j))
            (show star a.toSU2Matrix = a.toSU2Matrix from a.2.1.2.1),
        by rw [← AddMonoidHom.map_trace, show a.toSU2Matrix.trace = 0 from a.2.1.2.2, map_zero]⟩
      (by rw [← JetRing.coeff_star, show star a.toU1Value = a.toU1Value from a.2.2.2])
  map_add' a b := by
    ext <;> simp [Matrix.map_apply]
  map_smul' t a := by
    refine GaugeAlgebra.ext_of_matrix ?_ ?_ ?_ <;>
      simp only [GaugeAlgebra.ofMatrixProd_toSU3Matrix, GaugeAlgebra.ofMatrixProd_toSU2Matrix,
        GaugeAlgebra.ofMatrixProd_toU1Value, smul_toSU3Matrix, smul_toSU2Matrix, smul_toU1Value,
        GaugeAlgebra.smul_toSU3Matrix, GaugeAlgebra.smul_toSU2Matrix, GaugeAlgebra.smul_toU1Value,
        RingHom.id_apply]
    · ext i j : 1
      simp only [Matrix.map_apply, Matrix.smul_apply]
      rw [← algebraMap_smul ℂ t, map_smul, algebraMap_smul]
    · ext i j : 1
      simp only [Matrix.map_apply, Matrix.smul_apply]
      rw [← algebraMap_smul ℂ t, map_smul, algebraMap_smul]
    · rw [← algebraMap_smul ℂ t, map_smul, algebraMap_smul]

@[simp]
lemma taylorCoeff_toSU3Matrix (r : Multiset (Fin 1 ⊕ Fin 3)) (a : JetGaugeAlgebra) :
    (taylorCoeff r a).toSU3Matrix = a.toSU3Matrix.map (coeff r.toFinsupp) := rfl

@[simp]
lemma taylorCoeff_toSU2Matrix (r : Multiset (Fin 1 ⊕ Fin 3)) (a : JetGaugeAlgebra) :
    (taylorCoeff r a).toSU2Matrix = a.toSU2Matrix.map (coeff r.toFinsupp) := rfl

@[simp]
lemma taylorCoeff_toU1Value (r : Multiset (Fin 1 ⊕ Fin 3)) (a : JetGaugeAlgebra) :
    (taylorCoeff r a).toU1Value = coeff r.toFinsupp a.toU1Value := rfl

/-- The zeroth Taylor coefficient respects the bracket, since the constant coefficient
  of a product of jets is the product of the constant coefficients. -/
lemma taylorCoeff_zero_bracket (a b : JetGaugeAlgebra) :
    taylorCoeff 0 ⁅a, b⁆ = ⁅taylorCoeff 0 a, taylorCoeff 0 b⁆ := by
  refine GaugeAlgebra.ext_of_matrix ?_ ?_ ?_
  · ext i j : 1
    simp [Matrix.map_apply, Matrix.mul_apply, smul_eq_mul,
      coeff_zero_eq_constantCoeff, map_sum, Finset.mul_sum, mul_sub]
  · ext i j : 1
    simp [Matrix.map_apply, Matrix.mul_apply, smul_eq_mul,
      coeff_zero_eq_constantCoeff, mul_sub]
  · simp

/-- Evaluation of the jet gauge algebra at the base point: the zeroth Taylor
  coefficient, as a morphism of Lie algebras. -/
noncomputable def eval : JetGaugeAlgebra →ₗ⁅ℝ⁆ GaugeAlgebra :=
  { taylorCoeff 0 with map_lie' := taylorCoeff_zero_bracket _ _ }

/-- The inclusion of the constant gauge algebra into the jet gauge algebra: the jets
  with no spacetime dependence, given entrywise by the constant power series. This is
  a section of `eval`. -/
noncomputable def ofConstant : GaugeAlgebra →ₗ[ℝ] JetGaugeAlgebra where
  toFun a := ofMatrixProd
      (a.toSU3Matrix.map (C : ℂ → JetRing), a.toSU2Matrix.map (C : ℂ → JetRing),
        C a.toU1Value)
      ⟨by
        ext i j : 1
        simpa [Matrix.star_apply, Matrix.map_apply] using
          congrArg (fun M => (C (M i j) : JetRing))
            (show star a.toSU3Matrix = a.toSU3Matrix from a.1.2.1),
        by rw [← AddMonoidHom.map_trace, show a.toSU3Matrix.trace = 0 from a.1.2.2, map_zero]⟩
      ⟨by
        ext i j : 1
        simpa [Matrix.star_apply, Matrix.map_apply] using
          congrArg (fun M => (C (M i j) : JetRing))
            (show star a.toSU2Matrix = a.toSU2Matrix from a.2.1.2.1),
        by rw [← AddMonoidHom.map_trace, show a.toSU2Matrix.trace = 0 from a.2.1.2.2, map_zero]⟩
      (by rw [JetRing.star_C, show star a.toU1Value = a.toU1Value from a.2.2.2])
  map_add' a b := by
    ext <;> simp [Matrix.map_apply]
  map_smul' t a := by
    have hC : ∀ x : ℂ, (C (t • x) : JetRing) = t • C x := fun x => by
      rw [Algebra.smul_def, Algebra.smul_def, map_mul, MvPowerSeries.algebraMap_apply]
    refine ext_of_matrix ?_ ?_ ?_ <;>
      simp only [ofMatrixProd_toSU3Matrix, ofMatrixProd_toSU2Matrix, ofMatrixProd_toU1Value,
        GaugeAlgebra.smul_toSU3Matrix, GaugeAlgebra.smul_toSU2Matrix,
        GaugeAlgebra.smul_toU1Value, smul_toSU3Matrix, smul_toSU2Matrix, smul_toU1Value,
        RingHom.id_apply]
    · ext i j : 1
      simp only [Matrix.map_apply, Matrix.smul_apply]
      exact hC _
    · ext i j : 1
      simp only [Matrix.map_apply, Matrix.smul_apply]
      exact hC _
    · exact hC _

@[simp]
lemma ofConstant_toSU3Matrix (a : GaugeAlgebra) :
    (ofConstant a).toSU3Matrix = a.toSU3Matrix.map (C : ℂ → JetRing) := rfl

@[simp]
lemma ofConstant_toSU2Matrix (a : GaugeAlgebra) :
    (ofConstant a).toSU2Matrix = a.toSU2Matrix.map (C : ℂ → JetRing) := rfl

@[simp]
lemma ofConstant_toU1Value (a : GaugeAlgebra) :
    (ofConstant a).toU1Value = C a.toU1Value := rfl

lemma eval_apply (a : JetGaugeAlgebra) : eval a = taylorCoeff 0 a := rfl

@[simp]
lemma eval_ofConstant (a : GaugeAlgebra) : eval (ofConstant a) = a := by
  refine GaugeAlgebra.ext_of_matrix ?_ ?_ ?_
  · ext i j : 1
    simp [Matrix.map_apply, eval_apply, coeff_zero_eq_constantCoeff, constantCoeff_C]
  · ext i j : 1
    simp [Matrix.map_apply,  eval_apply, coeff_zero_eq_constantCoeff, constantCoeff_C]
  · simp [coeff_zero_eq_constantCoeff, eval_apply, constantCoeff_C]


lemma eval_toSU3Matrix_apply (a : JetGaugeAlgebra) (i j : Fin 3) :
    (eval a).toSU3Matrix i j = constantCoeff (a.toSU3Matrix i j) := by
  rw [show eval a = taylorCoeff 0 a from rfl, taylorCoeff_toSU3Matrix, Matrix.map_apply,
    show Multiset.toFinsupp (0 : Multiset (Fin 1 ⊕ Fin 3)) = 0 from map_zero _,
    coeff_zero_eq_constantCoeff]

lemma eval_toSU2Matrix_apply (a : JetGaugeAlgebra) (i j : Fin 2) :
    (eval a).toSU2Matrix i j = constantCoeff (a.toSU2Matrix i j) := by
  rw [show eval a = taylorCoeff 0 a from rfl, taylorCoeff_toSU2Matrix, Matrix.map_apply,
    show Multiset.toFinsupp (0 : Multiset (Fin 1 ⊕ Fin 3)) = 0 from map_zero _,
    coeff_zero_eq_constantCoeff]

lemma eval_toU1Value_eq (a : JetGaugeAlgebra) :
    (eval a).toU1Value = constantCoeff a.toU1Value := by
  rw [show eval a = taylorCoeff 0 a from rfl, taylorCoeff_toU1Value,
    show Multiset.toFinsupp (0 : Multiset (Fin 1 ⊕ Fin 3)) = 0 from map_zero _,
    coeff_zero_eq_constantCoeff]


/-- Taylor determinacy: a jet gauge algebra element is determined by the base-point
  values of its iterated derivatives. -/
theorem ext_of_eval_iteratedDeriv {x y : JetGaugeAlgebra}
    (h : ∀ s, eval (iteratedDeriv s x) = eval (iteratedDeriv s y)) : x = y := by
  have key : ∀ (n : ℕ) (x y : JetGaugeAlgebra),
      (∀ s, eval (iteratedDeriv s x) = eval (iteratedDeriv s y)) →
      ∀ m : (Fin 1 ⊕ Fin 3) →₀ ℕ, Finsupp.degree m = n →
        (∀ i j, coeff m (x.toSU3Matrix i j) = coeff m (y.toSU3Matrix i j)) ∧
        (∀ i j, coeff m (x.toSU2Matrix i j) = coeff m (y.toSU2Matrix i j)) ∧
        coeff m x.toU1Value = coeff m y.toU1Value := by
    intro n
    induction n with
    | zero =>
        intro x y hxy m hm
        have hm0 : m = 0 := (Finsupp.degree_eq_zero_iff m).mp hm
        subst hm0
        have h0 := hxy 0
        rw [iteratedDeriv_zero] at h0
        simp only [LinearMap.id_coe, id_eq] at h0
        have h0' : taylorCoeff 0 x = taylorCoeff 0 y := h0
        refine ⟨fun i j => ?_, fun i j => ?_, ?_⟩
        · simpa [Matrix.map_apply] using
            congrArg (fun g => GaugeAlgebra.toSU3Matrix g i j) h0'
        · simpa [Matrix.map_apply] using
            congrArg (fun g => GaugeAlgebra.toSU2Matrix g i j) h0'
        · simpa using congrArg GaugeAlgebra.toU1Value h0'
    | succ n ih =>
        intro x y hxy m hm
        -- pick a direction occurring in `m` and peel one derivative off
        have hm0 : m ≠ 0 := fun h0 => by simp [h0] at hm
        obtain ⟨μ, hμ⟩ := Finsupp.ne_iff.mp hm0
        simp only [Finsupp.coe_zero, Pi.zero_apply] at hμ
        have hle : Finsupp.single μ 1 ≤ m := by
          rw [Finsupp.single_le_iff]
          omega
        have hm'' : m - Finsupp.single μ 1 + Finsupp.single μ 1 = m :=
          tsub_add_cancel_of_le hle
        have hdeg' : Finsupp.degree (m - Finsupp.single μ 1) = n := by
          have h1 := congrArg Finsupp.degree hm''
          rw [map_add, Finsupp.degree_single, hm] at h1
          omega
        -- the derivative pair inherits the hypothesis, by additivity of `iteratedDeriv`
        have hd : ∀ s, eval (iteratedDeriv s (deriv μ x)) =
            eval (iteratedDeriv s (deriv μ y)) := by
          intro s
          have h1 := hxy (s + {μ})
          rwa [iteratedDeriv_add, LinearMap.comp_apply, iteratedDeriv_singleton] at h1
        obtain ⟨k3, k2, k1⟩ := ih (deriv μ x) (deriv μ y) hd (m - Finsupp.single μ 1) hdeg'
        refine ⟨fun i j => ?_, fun i j => ?_, ?_⟩
        · have hk := k3 i j
          simp only [deriv_toSU3Matrix, Matrix.map_apply] at hk
          rw [coeff_pderiv, coeff_pderiv, hm''] at hk
          exact mul_right_cancel₀ (Nat.cast_add_one_ne_zero _) hk
        · have hk := k2 i j
          simp only [deriv_toSU2Matrix, Matrix.map_apply] at hk
          rw [coeff_pderiv, coeff_pderiv, hm''] at hk
          exact mul_right_cancel₀ (Nat.cast_add_one_ne_zero _) hk
        · have hk := k1
          simp only [deriv_toU1Value] at hk
          rw [coeff_pderiv, coeff_pderiv, hm''] at hk
          exact mul_right_cancel₀ (Nat.cast_add_one_ne_zero _) hk
  refine ext_of_matrix ?_ ?_ ?_
  · ext i j : 1
    ext m
    exact (key (Finsupp.degree m) x y h m rfl).1 i j
  · ext i j : 1
    ext m
    exact (key (Finsupp.degree m) x y h m rfl).2.1 i j
  · ext m
    exact (key (Finsupp.degree m) x y h m rfl).2.2

/-- Bracket congruence: the base-point Taylor data of an iterated derivative of a
  bracket depends only on the corresponding Taylor data of the two arguments. -/
lemma eval_iteratedDeriv_bracket_congr (w : Multiset (Fin 1 ⊕ Fin 3))
    (a b a' b' : JetGaugeAlgebra)
    (ha : ∀ p ≤ w, eval (iteratedDeriv p a) = eval (iteratedDeriv p a'))
    (hb : ∀ p ≤ w, eval (iteratedDeriv p b) = eval (iteratedDeriv p b')) :
    eval (iteratedDeriv w ⁅a, b⁆) = eval (iteratedDeriv w ⁅a', b'⁆) := by
  induction w using Multiset.induction_on generalizing a b a' b' with
  | empty =>
      have ha0 := ha 0 le_rfl
      have hb0 := hb 0 le_rfl
      rw [iteratedDeriv_zero] at ha0 hb0 ⊢
      simp only [LinearMap.id_coe, id_eq] at ha0 hb0 ⊢
      rw [LieHom.map_lie, LieHom.map_lie, ha0, hb0]
  | cons ρ w ihw =>
      have hcons : ∀ c : JetGaugeAlgebra,
          iteratedDeriv (ρ ::ₘ w) c = iteratedDeriv w (deriv ρ c) := by
        intro c
        rw [show (ρ ::ₘ w : Multiset (Fin 1 ⊕ Fin 3)) = w + {ρ} from by
            rw [add_comm, Multiset.singleton_add],
          iteratedDeriv_add, LinearMap.comp_apply, iteratedDeriv_singleton]
      have htrans : ∀ (c c' : JetGaugeAlgebra),
          (∀ p ≤ ρ ::ₘ w, eval (iteratedDeriv p c) = eval (iteratedDeriv p c')) →
          ∀ p ≤ w, eval (iteratedDeriv p (deriv ρ c)) = eval (iteratedDeriv p (deriv ρ c')) := by
        intro c c' hc p hp
        have h1 := hc (p + {ρ}) (by
          rw [show (ρ ::ₘ w : Multiset (Fin 1 ⊕ Fin 3)) = w + {ρ} from by
            rw [add_comm, Multiset.singleton_add]]
          exact add_le_add hp le_rfl)
        rwa [iteratedDeriv_add, LinearMap.comp_apply, iteratedDeriv_singleton] at h1
      have hrest : ∀ (c c' : JetGaugeAlgebra),
          (∀ p ≤ ρ ::ₘ w, eval (iteratedDeriv p c) = eval (iteratedDeriv p c')) →
          ∀ p ≤ w, eval (iteratedDeriv p c) = eval (iteratedDeriv p c') :=
        fun c c' hc p hp => hc p (hp.trans (Multiset.le_cons_self w ρ))
      rw [hcons, hcons, deriv_bracket, deriv_bracket, map_add, map_add, map_add, map_add]
      rw [ihw _ _ _ _ (htrans a a' ha) (hrest b b' hb),
        ihw _ _ _ _ (hrest a a' ha) (htrans b b' hb)]

/-!

## The basis

-/


/-!

## The adjoint representation of Jet Gauge group

-/

/-- The adjoint action of an element `U` of the jet gauge group on the jet gauge algebra,
  acting on the `su(3)` and `su(2)` factors by `a ↦ U a U⁻¹`, with `U⁻¹ = star U` by
  unitarity, and trivially on the `u(1)` factor since `JetRing` is commutative.
  Hermiticity is preserved since `star (U a (star U)) = U (star a) (star U)`, and
  tracelessness since the trace is invariant under conjugation. -/
noncomputable def adjointMap (U : JetGaugeGroupI) : JetGaugeAlgebra →ₗ[ℝ] JetGaugeAlgebra where
  toFun a := ofMatrixProd
      (U.1.1 * a.toSU3Matrix * star U.1.1,
        U.2.1.1 * a.toSU2Matrix * star U.2.1.1,
        a.toU1Value)
      ⟨by
        rw [star_mul, star_mul, star_star,
          show star a.toSU3Matrix = a.toSU3Matrix from a.1.2.1, mul_assoc],
        by
        rw [Matrix.trace_mul_comm, ← mul_assoc,
          show star U.1.1 * U.1.1 = 1 from mem_unitaryGroup_iff'.mp
            (mem_specialUnitaryGroup_iff.mp U.1.2).1,
          one_mul, show a.toSU3Matrix.trace = 0 from a.1.2.2]⟩
      ⟨by
        rw [star_mul, star_mul, star_star,
          show star a.toSU2Matrix = a.toSU2Matrix from a.2.1.2.1]
        exact (mul_assoc _ _ _).symm,
        by
        rw [Matrix.trace_mul_comm, ← mul_assoc,
          show star U.2.1.1 * U.2.1.1 = 1 from mem_unitaryGroup_iff'.mp
            (mem_specialUnitaryGroup_iff.mp U.2.1.2).1,
          one_mul, show a.toSU2Matrix.trace = 0 from a.2.1.2.2]⟩
      (show star a.toU1Value = a.toU1Value from a.2.2.2)
  map_add' a b := by
    ext <;> simp [mul_add, add_mul]
  map_smul' r a := by
    ext <;> simp

@[simp]
lemma adjointMap_toSU3Matrix (U : JetGaugeGroupI) (a : JetGaugeAlgebra) :
    (adjointMap U a).toSU3Matrix = U.1.1 * a.toSU3Matrix * star U.1.1 := rfl

@[simp]
lemma adjointMap_toSU2Matrix (U : JetGaugeGroupI) (a : JetGaugeAlgebra) :
    (adjointMap U a).toSU2Matrix = U.2.1.1 * a.toSU2Matrix * star U.2.1.1 := rfl

@[simp]
lemma adjointMap_toU1Value (U : JetGaugeGroupI) (a : JetGaugeAlgebra) :
    (adjointMap U a).toU1Value = a.toU1Value := rfl

/-- The adjoint representation of the jet gauge group on the jet gauge algebra,
  `U ↦ (a ↦ U a U⁻¹)` factorwise. -/
noncomputable def adjoint : Representation ℝ JetGaugeGroupI JetGaugeAlgebra where
  toFun := adjointMap
  map_one' := by
    refine LinearMap.ext fun a => ?_
    ext <;> simp
  map_mul' U V := by
    refine LinearMap.ext fun a => ?_
    ext <;> simp [star_mul, mul_assoc]

/-- Evaluating the adjoint action of a gauge jet on a constant at the base point is
  the adjoint action of the base-point value of the jet. -/
lemma eval_adjointMap_ofConstant (U : JetGaugeGroupI) (a : GaugeAlgebra) :
    eval (adjointMap U (ofConstant a)) = GaugeAlgebra.adjoint U.eval a := by
  have hmap : ∀ {n : Type} [Fintype n] [DecidableEq n] (M : Matrix n n JetRing),
      M.map (coeff (Multiset.toFinsupp (0 : Multiset (Fin 1 ⊕ Fin 3)))) =
        (constantCoeff : JetRing →+* ℂ).mapMatrix M := by
    intro n _ _ M
    ext i j
    simp [Matrix.map_apply, RingHom.mapMatrix_apply, coeff_zero_eq_constantCoeff]
  have hC3 : (constantCoeff : JetRing →+* ℂ).mapMatrix (a.toSU3Matrix.map C)
      = a.toSU3Matrix := by
    ext i j
    simp [RingHom.mapMatrix_apply, Matrix.map_apply, constantCoeff_C]
  have hC2 : (constantCoeff : JetRing →+* ℂ).mapMatrix (a.toSU2Matrix.map C)
      = a.toSU2Matrix := by
    ext i j
    simp [RingHom.mapMatrix_apply, Matrix.map_apply, constantCoeff_C]
  refine GaugeAlgebra.ext_of_matrix ?_ ?_ ?_
  · simp only [eval_apply, taylorCoeff_toSU3Matrix, adjointMap_toSU3Matrix,
      ofConstant_toSU3Matrix, GaugeAlgebra.adjoint_toSU3Matrix]
    rw [hmap, map_mul, map_mul, JetRing.mapMatrix_constantCoeff_star, hC3]
    rfl
  · simp only [eval_apply, taylorCoeff_toSU2Matrix, adjointMap_toSU2Matrix,
      ofConstant_toSU2Matrix, GaugeAlgebra.adjoint_toSU2Matrix]
    rw [hmap, map_mul, map_mul, JetRing.mapMatrix_constantCoeff_star, hC2]
    rfl
  · simp [eval_apply, taylorCoeff_toU1Value, adjointMap_toU1Value, ofConstant_toU1Value,
      coeff_zero_eq_constantCoeff, constantCoeff_C, GaugeAlgebra.adjoint_toU1Value]

/-- The constant inclusion is a morphism of Lie algebras: constants bracket to
  constants. -/
lemma ofConstant_lie (a b : GaugeAlgebra) :
    ofConstant ⁅a, b⁆ = ⁅ofConstant a, ofConstant b⁆ := by
  refine ext_of_matrix ?_ ?_ ?_
  · ext i j : 1
    simp [Matrix.map_apply, Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul,
      MvPowerSeries.smul_eq_C_mul, map_sum, Finset.mul_sum, mul_sub]
  · ext i j : 1
    simp [Matrix.map_apply, Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul,
      MvPowerSeries.smul_eq_C_mul, mul_sub]
  · simp

/-- The adjoint action preserves the bracket: conjugation is an automorphism of the
  Lie algebra, using unitarity to cancel the inner `U† U` factors. -/
lemma adjointMap_lie (U : JetGaugeGroupI) (x y : JetGaugeAlgebra) :
    adjointMap U ⁅x, y⁆ = ⁅adjointMap U x, adjointMap U y⁆ := by
  refine ext_of_matrix ?_ ?_ ?_
  · have hU : star U.1.1 * U.1.1 = 1 := by
      have h := (Matrix.mem_specialUnitaryGroup_iff.mp U.1.2).1
      rwa [Matrix.mem_unitaryGroup_iff'] at h
    have key : ∀ X Y : Matrix (Fin 3) (Fin 3) JetRing,
        (U.1.1 * X * star U.1.1) * (U.1.1 * Y * star U.1.1) =
          U.1.1 * (X * Y) * star U.1.1 := by
      intro X Y
      simp only [mul_assoc]
      rw [show star U.1.1 * (U.1.1 * (Y * star U.1.1)) = Y * star U.1.1 from by
        rw [← mul_assoc, hU, one_mul]]
    simp only [adjointMap_toSU3Matrix, bracket_toSU3Matrix, mul_smul_comm, smul_mul_assoc]
    rw [key, key, mul_sub, sub_mul]
  · have hU : star U.2.1.1 * U.2.1.1 = 1 := by
      have h := (Matrix.mem_specialUnitaryGroup_iff.mp U.2.1.2).1
      rwa [Matrix.mem_unitaryGroup_iff'] at h
    have key : ∀ X Y : Matrix (Fin 2) (Fin 2) JetRing,
        (U.2.1.1 * X * star U.2.1.1) * (U.2.1.1 * Y * star U.2.1.1) =
          U.2.1.1 * (X * Y) * star U.2.1.1 := by
      intro X Y
      simp only [mul_assoc]
      rw [show star U.2.1.1 * (U.2.1.1 * (Y * star U.2.1.1)) = Y * star U.2.1.1 from by
        rw [← mul_assoc, hU, one_mul]]
    simp only [adjointMap_toSU2Matrix, bracket_toSU2Matrix, mul_smul_comm, smul_mul_assoc]
    rw [key, key, mul_sub, sub_mul]
  · simp

end JetGaugeAlgebra

end StandardModel
