/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.AlgebraicFramework.JordanOrderUnit.StructureAlgebra
public import Mathlib.Algebra.Ring.IsFormallyReal

/-!
# Finite-rank Jordan trace and determinant data

This is the algebraic finite-dimensional companion to the order-unit state space.  It records the
generic trace and determinant of a formally real real Jordan algebra, and obtains density
observables by cutting the canonical sum-of-squares cone at trace one.  It does not assert that
these are all order-unit states or normal JBW states: those are distinct analytic assertions.
-/

@[expose] public section

namespace JordanAlgebra

variable {E : Type*} [NonAssocCommRing E] [Module ℝ E] [SMulCommClass ℝ E E]
  [IsScalarTower ℝ E E] [IsCommJordan E] [IsFormallyReal E]

/-- Generic finite-rank trace and determinant data for a formally real real Jordan algebra.

The intermediate coefficients of the generic minimal polynomial are deliberately not postulated:
they should be added together with an actual Cayley--Hamilton theorem, rather than as unused
structure fields. -/
structure TraceDeterminant (E : Type*) [NonAssocCommRing E] [Module ℝ E] where
  /-- Jordan rank, i.e. determinant degree and trace of the unit. -/
  rank : ℕ
  /-- The generic trace. -/
  trace : E →ₗ[ℝ] ℝ
  /-- The generic determinant. -/
  determinant : E → ℝ
  determinant_smul : ∀ (r : ℝ) (x : E), determinant (r • x) = r ^ rank * determinant x
  trace_one : trace 1 = rank
  determinant_one : determinant 1 = 1

namespace TraceDeterminant

/-- The finite-rank density-observable base: sums of Jordan squares with trace one. -/
def states (τ : TraceDeterminant E) : Set E :=
  {ρ | IsSumSq ρ ∧ τ.trace ρ = 1}

/-- A pure finite-rank density observable is an idempotent density observable. -/
def pureStates (τ : TraceDeterminant E) : Set E :=
  {ρ | ρ ∈ τ.states ∧ ρ * ρ = ρ}

/-- Expectation in a finite-rank density observable. -/
def expectation (τ : TraceDeterminant E) (ρ : τ.states) : E →ₗ[ℝ] ℝ where
  toFun a := τ.trace ((ρ : E) * a)
  map_add' a b := by rw [mul_add, map_add]
  map_smul' r a := by simp [mul_smul_comm]

omit [IsScalarTower ℝ E E] [IsCommJordan E] [IsFormallyReal E] in
@[simp] theorem expectation_apply (τ : TraceDeterminant E) (ρ : τ.states) (a : E) :
    τ.expectation ρ a = τ.trace ((ρ : E) * a) := rfl

omit [IsCommJordan E] [IsFormallyReal E] in
/-- Square scalar weights preserve the sum-of-squares cone. -/
theorem sq_smul_isSumSq {x : E} (hx : IsSumSq x) (r : ℝ) : IsSumSq ((r * r) • x) := by
  induction hx with
  | zero => simp
  | sq_add a hs ih =>
    rw [smul_add]
    have hsq : (r * r) • (a * a) = (r • a) * (r • a) := by
      rw [smul_mul_assoc, mul_smul_comm, smul_smul]
    rw [hsq]
    exact IsSumSq.sq_add _ ih

omit [IsCommJordan E] [IsFormallyReal E] in
/-- Square-weighted mixtures remain finite-rank density observables. -/
theorem sq_smul_add_sq_smul_mem_states (τ : TraceDeterminant E)
    {ρ σ : E} (hρ : ρ ∈ τ.states) (hσ : σ ∈ τ.states)
    {r s : ℝ} (hrs : r * r + s * s = 1) :
    (r * r) • ρ + (s * s) • σ ∈ τ.states := by
  refine ⟨IsSumSq.add (sq_smul_isSumSq hρ.1 r) (sq_smul_isSumSq hσ.1 s), ?_⟩
  rw [map_add, map_smul, map_smul, hρ.2, hσ.2]
  simpa using hrs

omit [IsCommJordan E] [IsFormallyReal E] in
/-- Expectations respect square-weighted finite-rank mixtures. -/
theorem expectation_sq_smul_add_sq_smul (τ : TraceDeterminant E)
    {ρ σ : E} (hρ : ρ ∈ τ.states) (hσ : σ ∈ τ.states)
    {r s : ℝ} (hrs : r * r + s * s = 1) (a : E) :
    τ.expectation ⟨(r * r) • ρ + (s * s) • σ,
      τ.sq_smul_add_sq_smul_mem_states hρ hσ hrs⟩ a =
      (r * r) * τ.expectation ⟨ρ, hρ⟩ a + (s * s) * τ.expectation ⟨σ, hσ⟩ a := by
  simp only [expectation_apply, add_mul, smul_mul_assoc, map_add, map_smul, smul_eq_mul]

end TraceDeterminant

end JordanAlgebra
