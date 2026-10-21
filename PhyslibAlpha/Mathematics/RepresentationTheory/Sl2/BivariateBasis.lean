/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.Mathematics.RepresentationTheory.Sl2.Classification

/-!
# A basis for two commuting sl₂ actions

Builds a joint primitive vector and bivariate ladder basis for commuting triples.

## i. Overview

Two commuting `sl₂` triples have a joint primitive vector: a primitive-weight space for
the first triple is invariant under the second. Iterating the two lowering operators from
that vector produces a grid of weight vectors. For a jointly irreducible action, these form
a basis with explicit raising, lowering, and weight formulas.

## ii. Key results

- `exists_joint_primitive` finds a common highest-weight vector.
- `IsBivariateGrid` records the standard `V(n1) ⊗ V(n2)` action formulas on a grid family.
- `exists_bivariate_basis` constructs a grid basis satisfying `IsBivariateGrid`.

## iii. Table of contents

- A. Joint primitive vectors and strings

## iv. References

- Mathlib, `Mathlib.Algebra.Lie.Sl2`.

## A. Joint primitive vectors and strings
-/

@[expose] public section

noncomputable section

namespace PhyslibAlpha.Sl2

open scoped TensorProduct

attribute [local instance 100] LieRing.ofAssociativeRing

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- Under the tautological action, `LieModule.toEnd` is the original endomorphism. -/
lemma toEnd_ambient_eq (x : Module.End K V) :
    LieModule.toEnd K (Module.End K V) V x = x := by
  ext v
  rw [LieModule.toEnd_apply_apply, Module.End.lie_apply]

/-- Powers of the tautological action are powers of the endomorphism. -/
lemma toEnd_ambient_pow (x : Module.End K V) (k : ℕ) :
    LieModule.toEnd K (Module.End K V) V x ^ k = x ^ k := by
  rw [toEnd_ambient_eq]

/-- Commuting endomorphisms have vanishing associative-ring bracket, and conversely. -/
lemma commute_of_lie_eq_zero {a b : Module.End K V} (h : ⁅a, b⁆ = 0) : Commute a b := by
  rw [commute_iff_eq]
  rwa [LieRing.of_associative_ring_bracket, sub_eq_zero] at h

/-- A power of `f` commutes past an endomorphism commuting with `f`. -/
lemma apply_pow_comm {f y : Module.End K V} (hy : Commute f y) (a : ℕ) (v : V) :
    y ((f ^ a) v) = (f ^ a) (y v) :=
  (LinearMap.congr_fun (hy.pow_left a).eq v).symm

/-- Powers of an endomorphism vanish beyond the first vanishing power. -/
lemma pow_apply_eq_zero {f : Module.End K V} {v : V} {k : ℕ} (h : (f ^ k) v = 0) {a : ℕ}
    (ha : k ≤ a) : (f ^ a) v = 0 := by
  obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le ha
  rw [add_comm, pow_add, Module.End.mul_apply, h, map_zero]

/-- A linear map sending a spanning family into its span preserves the span. -/
lemma map_mem_span_of_range {ι : Type*} (g : ι → V) (y : Module.End K V)
    (hy : ∀ i, y (g i) ∈ Submodule.span K (Set.range g)) :
    ∀ v ∈ Submodule.span K (Set.range g), y v ∈ Submodule.span K (Set.range g) :=
  fun _ hv => (Submodule.span_le (p := (Submodule.span K (Set.range g)).comap y)).mpr
    (Set.range_subset_iff.mpr hy) hv

section Plain

variable {h e f : Module.End K V} {t : IsSl2Triple h e f} {m : V} {n : ℕ}

/-- A primitive vector is a `h`-eigenvector, in plain-operator form. -/
lemma prim_h (P : t.HasPrimitiveVectorWith m (n : K)) : h m = (n : K) • m := by
  simpa [Module.End.lie_apply] using P.lie_h

/-- A primitive vector is killed by `e`, in plain-operator form. -/
lemma prim_e (P : t.HasPrimitiveVectorWith m (n : K)) : e m = 0 := by
  simpa [Module.End.lie_apply] using P.lie_e

/-- The `h`-weights along a lowering string, in plain-operator form. -/
lemma prim_h_pow (P : t.HasPrimitiveVectorWith m (n : K)) (k : ℕ) :
    h ((f ^ k) m) = ((n : K) - 2 * k) • (f ^ k) m := by
  simpa [Module.End.lie_apply, toEnd_ambient_pow] using P.lie_h_pow_toEnd_f k

/-- The raising operator along a lowering string, in plain-operator form. -/
lemma prim_e_pow_succ (P : t.HasPrimitiveVectorWith m (n : K)) (k : ℕ) :
    e ((f ^ (k + 1)) m) = (((k : K) + 1) * ((n : K) - k)) • (f ^ k) m := by
  simpa [Module.End.lie_apply, toEnd_ambient_pow] using P.lie_e_pow_succ_toEnd_f k

/-- A lowering string closes after `n + 1` steps, in plain-operator form. -/
lemma prim_f_pow_zero [CharZero K] [FiniteDimensional K V]
    (P : t.HasPrimitiveVectorWith m (n : K)) : (f ^ (n + 1)) m = 0 := by
  simpa [toEnd_ambient_pow] using P.pow_toEnd_f_eq_zero_of_eq_nat rfl

/-- The first `n + 1` lowering steps of a primitive vector are nonzero. -/
lemma prim_f_pow_ne_zero [CharZero K] (P : t.HasPrimitiveVectorWith m (n : K)) {k : ℕ}
    (hk : k ≤ n) : (f ^ k) m ≠ 0 := by
  simpa [toEnd_ambient_pow] using P.pow_toEnd_f_ne_zero_of_eq_nat rfl hk

end Plain

/-- A difference of two numbers in `[0, n]` that is a multiple of `n + 1` vanishes. -/
lemma eq_zero_of_sub_eq_mul {n a a' d : ℤ} (ha : 0 ≤ a ∧ a ≤ n) (ha' : 0 ≤ a' ∧ a' ≤ n)
    (h : a' - a = (n + 1) * d) : d = 0 := by
  rcases lt_trichotomy d 0 with hd | hd | hd
  · have : d ≤ -1 := by omega
    nlinarith
  · exact hd
  · have : 1 ≤ d := by omega
    nlinarith

/-- The integer weights `(n1 - 2a) + (n1 + 1)(n2 - 2b)` separate grid points. -/
lemma int_weight_inj {n1 n2 a a' b b' : ℕ} (ha : a ≤ n1) (ha' : a' ≤ n1)
    (h : (n1 : ℤ) - 2 * a + ((n1 : ℤ) + 1) * ((n2 : ℤ) - 2 * b) =
      (n1 : ℤ) - 2 * a' + ((n1 : ℤ) + 1) * ((n2 : ℤ) - 2 * b')) : a = a' ∧ b = b' := by
  have hd := eq_zero_of_sub_eq_mul (n := (n1 : ℤ)) (a := a) (a' := a') (d := (b : ℤ) - b')
    (by omega) (by omega) (by linarith)
  obtain rfl : b = b' := by omega
  exact ⟨by omega, rfl⟩

/-- The combined weights `h1 + (n1 + 1) h2` separate the points of the grid. -/
lemma weight_pair_injective [CharZero K] {n1 n2 : ℕ} :
    Function.Injective (fun p : Fin (n1 + 1) × Fin (n2 + 1) =>
      ((n1 : K) - 2 * (p.1 : ℕ)) + ((n1 : K) + 1) * ((n2 : K) - 2 * (p.2 : ℕ))) := by
  rintro ⟨a, b⟩ ⟨a', b'⟩ heq
  simp only at heq
  obtain ⟨h1, h2⟩ := int_weight_inj (Nat.lt_succ_iff.mp a.isLt) (Nat.lt_succ_iff.mp a'.isLt)
    (by exact_mod_cast heq : (n1 : ℤ) - 2 * (a : ℕ) + ((n1 : ℤ) + 1) * ((n2 : ℤ) - 2 * (b : ℕ)) =
      (n1 : ℤ) - 2 * (a' : ℕ) + ((n1 : ℤ) + 1) * ((n2 : ℤ) - 2 * (b' : ℕ)))
  exact Prod.ext (Fin.ext h1) (Fin.ext h2)

/-- A family `g` indexed by the grid `Fin (n1 + 1) × Fin (n2 + 1)` realises the standard
`V(n1) ⊗ V(n2)` action of two commuting `sl₂`-triples: `g (a, b)` has weights
`(n1 - 2a, n2 - 2b)`, the lowering operators shift one index, and the raising operators
shift it back with the standard coefficients. -/
structure IsBivariateGrid (h1 e1 f1 h2 e2 f2 : Module.End K V) (n1 n2 : ℕ)
    (g : Fin (n1 + 1) × Fin (n2 + 1) → V) : Prop where
  /-- The first Cartan operator acts diagonally. -/
  h1_apply (a : Fin (n1 + 1)) (b : Fin (n2 + 1)) :
    h1 (g (a, b)) = ((n1 : K) - 2 * (a : ℕ)) • g (a, b)
  /-- The second Cartan operator acts diagonally. -/
  h2_apply (a : Fin (n1 + 1)) (b : Fin (n2 + 1)) :
    h2 (g (a, b)) = ((n2 : K) - 2 * (b : ℕ)) • g (a, b)
  /-- The first raising operator kills the first row. -/
  e1_zero (b : Fin (n2 + 1)) : e1 (g (0, b)) = 0
  /-- The first raising operator lowers the first index. -/
  e1_pos (a : Fin (n1 + 1)) (_ : 0 < (a : ℕ)) (b : Fin (n2 + 1)) : e1 (g (a, b)) =
    (((a : ℕ) : K) * ((n1 : K) - ((a : ℕ) : K) + 1)) • g (⟨(a : ℕ) - 1, by omega⟩, b)
  /-- The first lowering operator raises the first index. -/
  f1_lt (a : Fin (n1 + 1)) (_ : (a : ℕ) < n1) (b : Fin (n2 + 1)) :
    f1 (g (a, b)) = g (⟨(a : ℕ) + 1, by omega⟩, b)
  /-- The first lowering operator kills the last row. -/
  f1_last (b : Fin (n2 + 1)) : f1 (g (Fin.last n1, b)) = 0
  /-- The second raising operator kills the first column. -/
  e2_zero (a : Fin (n1 + 1)) : e2 (g (a, 0)) = 0
  /-- The second raising operator lowers the second index. -/
  e2_pos (a : Fin (n1 + 1)) (b : Fin (n2 + 1)) (_ : 0 < (b : ℕ)) : e2 (g (a, b)) =
    (((b : ℕ) : K) * ((n2 : K) - ((b : ℕ) : K) + 1)) • g (a, ⟨(b : ℕ) - 1, by omega⟩)
  /-- The second lowering operator raises the second index. -/
  f2_lt (a : Fin (n1 + 1)) (b : Fin (n2 + 1)) (_ : (b : ℕ) < n2) :
    f2 (g (a, b)) = g (a, ⟨(b : ℕ) + 1, by omega⟩)
  /-- The second lowering operator kills the last column. -/
  f2_last (a : Fin (n1 + 1)) : f2 (g (a, Fin.last n2)) = 0

/-- No proper nonzero subspace is invariant under all six operators of two `sl₂`-triples. -/
def JointlyIrreducible (h1 e1 f1 h2 e2 f2 : Module.End K V) : Prop :=
  ∀ W : Submodule K V,
    (∀ x ∈ ({h1, e1, f1, h2, e2, f2} : Set (Module.End K V)), ∀ v ∈ W, x v ∈ W) →
    W = ⊥ ∨ W = ⊤

/-- The vector `f1 ^ a (f2 ^ b m)` of the bivariate lowering grid. -/
def gridVec (f1 f2 : Module.End K V) (m : V) (a b : ℕ) : V := (f1 ^ a) ((f2 ^ b) m)

/-- The bivariate lowering grid, indexed by `Fin (n1 + 1) × Fin (n2 + 1)`. -/
def gridFun (f1 f2 : Module.End K V) (m : V) (n1 n2 : ℕ) :
    Fin (n1 + 1) × Fin (n2 + 1) → V := fun p => gridVec f1 f2 m p.1 p.2

/-- The span of the bivariate lowering grid. -/
def gridSpan (f1 f2 : Module.End K V) (m : V) (n1 n2 : ℕ) : Submodule K V :=
  Submodule.span K (Set.range (gridFun f1 f2 m n1 n2))

section Grid

variable [CharZero K] {h1 e1 f1 h2 e2 f2 : Module.End K V}
    {t1 : IsSl2Triple h1 e1 f1} {t2 : IsSl2Triple h2 e2 f2} {n1 n2 : ℕ} {m0 : V}
    (P1 : t1.HasPrimitiveVectorWith m0 (n1 : K)) (P2 : t2.HasPrimitiveVectorWith m0 (n2 : K))
    (hc : ∀ x ∈ ({h1, e1, f1} : Set (Module.End K V)),
      ∀ y ∈ ({h2, e2, f2} : Set (Module.End K V)), Commute x y)

include P1 P2 hc

/-- Each lowering of the second triple is still primitive for the first triple. -/
lemma grid_primitive1 {b : ℕ} (hb : b ≤ n2) :
    t1.HasPrimitiveVectorWith ((f2 ^ b) m0) (n1 : K) := by
  refine ⟨prim_f_pow_ne_zero P2 hb, ?_, ?_⟩
  · rw [Module.End.lie_apply, apply_pow_comm (hc h1 (by simp) f2 (by simp)).symm, prim_h P1,
      map_smul]
  · rw [Module.End.lie_apply, apply_pow_comm (hc e1 (by simp) f2 (by simp)).symm, prim_e P1,
      map_zero]

/-- The grid vectors inside the rectangle are nonzero. -/
lemma grid_ne {a b : ℕ} (ha : a ≤ n1) (hb : b ≤ n2) : gridVec f1 f2 m0 a b ≠ 0 :=
  prim_f_pow_ne_zero (grid_primitive1 P1 P2 hc hb) ha

/-- The first Cartan weight of a grid vector. -/
lemma grid_h1 {b : ℕ} (a : ℕ) (hb : b ≤ n2) :
    h1 (gridVec f1 f2 m0 a b) = ((n1 : K) - 2 * a) • gridVec f1 f2 m0 a b :=
  prim_h_pow (grid_primitive1 P1 P2 hc hb) a

omit [CharZero K] P1 in
/-- The second Cartan weight of a grid vector. -/
lemma grid_h2 (a b : ℕ) :
    h2 (gridVec f1 f2 m0 a b) = ((n2 : K) - 2 * b) • gridVec f1 f2 m0 a b := by
  rw [gridVec, apply_pow_comm (hc f1 (by simp) h2 (by simp)), prim_h_pow P2, map_smul]

/-- The first raising operator kills the top of each column. -/
lemma grid_e1_zero {b : ℕ} (hb : b ≤ n2) : e1 (gridVec f1 f2 m0 0 b) = 0 := by
  simpa [gridVec] using prim_e (grid_primitive1 P1 P2 hc hb)

/-- The first raising operator on a grid vector. -/
lemma grid_e1_succ {b : ℕ} (a : ℕ) (hb : b ≤ n2) :
    e1 (gridVec f1 f2 m0 (a + 1) b) =
      (((a : K) + 1) * ((n1 : K) - a)) • gridVec f1 f2 m0 a b :=
  prim_e_pow_succ (grid_primitive1 P1 P2 hc hb) a

omit [CharZero K] P1 P2 hc in
/-- The first lowering operator shifts the first index. -/
lemma grid_f1 (a b : ℕ) : f1 (gridVec f1 f2 m0 a b) = gridVec f1 f2 m0 (a + 1) b :=
  (LinearMap.congr_fun (pow_succ' f1 a) ((f2 ^ b) m0)).symm

/-- The first lowering operator kills the end of each column. -/
lemma grid_f1_last [FiniteDimensional K V] {b : ℕ} (hb : b ≤ n2) :
    f1 (gridVec f1 f2 m0 n1 b) = 0 := by
  rw [grid_f1]
  exact prim_f_pow_zero (grid_primitive1 P1 P2 hc hb)

omit [CharZero K] P1 in
/-- The second raising operator kills the top of each row. -/
lemma grid_e2_zero (a : ℕ) : e2 (gridVec f1 f2 m0 a 0) = 0 := by
  rw [gridVec, apply_pow_comm (hc f1 (by simp) e2 (by simp))]
  simp [prim_e P2]

omit [CharZero K] P1 in
/-- The second raising operator on a grid vector. -/
lemma grid_e2_succ (a b : ℕ) :
    e2 (gridVec f1 f2 m0 a (b + 1)) =
      (((b : K) + 1) * ((n2 : K) - b)) • gridVec f1 f2 m0 a b := by
  rw [gridVec, apply_pow_comm (hc f1 (by simp) e2 (by simp)), prim_e_pow_succ P2, map_smul]
  rfl

omit [CharZero K] P1 P2 in
/-- The second lowering operator shifts the second index. -/
lemma grid_f2 (a b : ℕ) : f2 (gridVec f1 f2 m0 a b) = gridVec f1 f2 m0 a (b + 1) := by
  rw [gridVec, apply_pow_comm (hc f1 (by simp) f2 (by simp))]
  exact congrArg _ (LinearMap.congr_fun (pow_succ' f2 b) m0).symm

omit P1 in
/-- The second lowering operator kills the end of each row. -/
lemma grid_f2_last [FiniteDimensional K V] (a : ℕ) : f2 (gridVec f1 f2 m0 a n2) = 0 := by
  rw [grid_f2 hc, gridVec, prim_f_pow_zero P2, map_zero]

/-- Grid vectors outside the rectangle vanish. -/
lemma grid_eq_zero [FiniteDimensional K V] {a b : ℕ} (h : n1 < a ∨ n2 < b) :
    gridVec f1 f2 m0 a b = 0 := by
  by_cases hb : b ≤ n2
  · exact pow_apply_eq_zero (prim_f_pow_zero (grid_primitive1 P1 P2 hc hb))
      (h.resolve_right (not_lt.mpr hb))
  · have : (f2 ^ b) m0 = 0 := pow_apply_eq_zero (prim_f_pow_zero P2) (by omega)
    simp [gridVec, this]

/-- Every grid vector lies in the span of the finite grid. -/
lemma grid_mem_gridSpan [FiniteDimensional K V] (a b : ℕ) :
    gridVec f1 f2 m0 a b ∈ gridSpan f1 f2 m0 n1 n2 := by
  by_cases h : a ≤ n1 ∧ b ≤ n2
  · exact Submodule.subset_span ⟨(⟨a, by omega⟩, ⟨b, by omega⟩), rfl⟩
  · rw [grid_eq_zero P1 P2 hc (by omega)]
    exact Submodule.zero_mem _


variable [FiniteDimensional K V]

/-- The span of the grid is stable under `h1`. -/
lemma gridSpan_stable_h1 : ∀ v ∈ gridSpan f1 f2 m0 n1 n2, h1 v ∈ gridSpan f1 f2 m0 n1 n2 := by
  refine map_mem_span_of_range (gridFun f1 f2 m0 n1 n2) h1 fun p => ?_
  show h1 (gridVec f1 f2 m0 p.1 p.2) ∈ _
  rw [grid_h1 P1 P2 hc _ (Nat.lt_succ_iff.mp p.2.isLt)]
  exact Submodule.smul_mem _ _ (grid_mem_gridSpan P1 P2 hc _ _)

/-- The span of the grid is stable under `h2`. -/
lemma gridSpan_stable_h2 : ∀ v ∈ gridSpan f1 f2 m0 n1 n2, h2 v ∈ gridSpan f1 f2 m0 n1 n2 := by
  refine map_mem_span_of_range (gridFun f1 f2 m0 n1 n2) h2 fun p => ?_
  show h2 (gridVec f1 f2 m0 p.1 p.2) ∈ _
  rw [grid_h2 P2 hc]
  exact Submodule.smul_mem _ _ (grid_mem_gridSpan P1 P2 hc _ _)

/-- The span of the grid is stable under `f1`. -/
lemma gridSpan_stable_f1 : ∀ v ∈ gridSpan f1 f2 m0 n1 n2, f1 v ∈ gridSpan f1 f2 m0 n1 n2 := by
  refine map_mem_span_of_range (gridFun f1 f2 m0 n1 n2) f1 fun p => ?_
  show f1 (gridVec f1 f2 m0 p.1 p.2) ∈ _
  rw [grid_f1]
  exact grid_mem_gridSpan P1 P2 hc _ _

/-- The span of the grid is stable under `f2`. -/
lemma gridSpan_stable_f2 : ∀ v ∈ gridSpan f1 f2 m0 n1 n2, f2 v ∈ gridSpan f1 f2 m0 n1 n2 := by
  refine map_mem_span_of_range (gridFun f1 f2 m0 n1 n2) f2 fun p => ?_
  show f2 (gridVec f1 f2 m0 p.1 p.2) ∈ _
  rw [grid_f2 hc]
  exact grid_mem_gridSpan P1 P2 hc _ _

/-- The span of the grid is stable under `e1`. -/
lemma gridSpan_stable_e1 : ∀ v ∈ gridSpan f1 f2 m0 n1 n2, e1 v ∈ gridSpan f1 f2 m0 n1 n2 := by
  refine map_mem_span_of_range (gridFun f1 f2 m0 n1 n2) e1 fun p => ?_
  show e1 (gridVec f1 f2 m0 p.1 p.2) ∈ _
  have hb := Nat.lt_succ_iff.mp p.2.isLt
  rcases Nat.eq_zero_or_pos (p.1 : ℕ) with ha | ha
  · rw [ha, grid_e1_zero P1 P2 hc hb]
    exact Submodule.zero_mem _
  · obtain ⟨j, hj⟩ := Nat.exists_eq_add_one_of_ne_zero ha.ne'
    rw [hj, grid_e1_succ P1 P2 hc j hb]
    exact Submodule.smul_mem _ _ (grid_mem_gridSpan P1 P2 hc _ _)

/-- The span of the grid is stable under `e2`. -/
lemma gridSpan_stable_e2 : ∀ v ∈ gridSpan f1 f2 m0 n1 n2, e2 v ∈ gridSpan f1 f2 m0 n1 n2 := by
  refine map_mem_span_of_range (gridFun f1 f2 m0 n1 n2) e2 fun p => ?_
  show e2 (gridVec f1 f2 m0 p.1 p.2) ∈ _
  rcases Nat.eq_zero_or_pos (p.2 : ℕ) with hb | hb
  · rw [hb, grid_e2_zero P2 hc]
    exact Submodule.zero_mem _
  · obtain ⟨j, hj⟩ := Nat.exists_eq_add_one_of_ne_zero hb.ne'
    rw [hj, grid_e2_succ P2 hc]
    exact Submodule.smul_mem _ _ (grid_mem_gridSpan P1 P2 hc _ _)

/-- The span of the grid is stable under all six generators. -/
lemma gridSpan_stable {x : Module.End K V} (hx : x ∈ ({h1, e1, f1, h2, e2, f2} : Set _)) :
    ∀ v ∈ gridSpan f1 f2 m0 n1 n2, x v ∈ gridSpan f1 f2 m0 n1 n2 := by
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
  exacts [gridSpan_stable_h1 P1 P2 hc, gridSpan_stable_e1 P1 P2 hc, gridSpan_stable_f1 P1 P2 hc,
    gridSpan_stable_h2 P1 P2 hc, gridSpan_stable_e2 P1 P2 hc, gridSpan_stable_f2 P1 P2 hc]

/-- Joint irreducibility forces the grid to span. -/
lemma gridSpan_eq_top (hirr : JointlyIrreducible h1 e1 f1 h2 e2 f2) :
    gridSpan f1 f2 m0 n1 n2 = ⊤ := by
  rcases hirr _ fun x hx => gridSpan_stable P1 P2 hc hx with hbot | htop
  · have hmem := grid_mem_gridSpan P1 P2 hc 0 0
    rw [hbot] at hmem
    exact absurd ((Submodule.mem_bot K).mp hmem) (grid_ne P1 P2 hc (Nat.zero_le _) (Nat.zero_le _))
  · exact htop

/-- The grid spans, in the form needed to build a basis. -/
lemma top_le_span_gridFun (hirr : JointlyIrreducible h1 e1 f1 h2 e2 f2) :
    ⊤ ≤ Submodule.span K (Set.range (gridFun f1 f2 m0 n1 n2)) :=
  (gridSpan_eq_top P1 P2 hc hirr).ge


omit [FiniteDimensional K V] in
/-- The combined Cartan operator has the grid vectors as eigenvectors. -/
lemma grid_hasEigenvector (p : Fin (n1 + 1) × Fin (n2 + 1)) :
    (h1 + ((n1 : K) + 1) • h2).HasEigenvector
      (((n1 : K) - 2 * (p.1 : ℕ)) + ((n1 : K) + 1) * ((n2 : K) - 2 * (p.2 : ℕ)))
      (gridFun f1 f2 m0 n1 n2 p) := by
  have hb := Nat.lt_succ_iff.mp p.2.isLt
  refine ⟨?_, grid_ne P1 P2 hc (Nat.lt_succ_iff.mp p.1.isLt) hb⟩
  rw [Module.End.mem_eigenspace_iff]
  show h1 (gridVec f1 f2 m0 p.1 p.2) + ((n1 : K) + 1) • h2 (gridVec f1 f2 m0 p.1 p.2) = _
  rw [grid_h1 P1 P2 hc _ hb, grid_h2 P2 hc, smul_smul, ← add_smul]
  rfl

omit [FiniteDimensional K V] in
/-- The bivariate grid is linearly independent. -/
lemma grid_linearIndependent : LinearIndependent K (gridFun f1 f2 m0 n1 n2) :=
  (h1 + ((n1 : K) + 1) • h2).eigenvectors_linearIndependent' _ weight_pair_injective _
    (grid_hasEigenvector P1 P2 hc)

omit [FiniteDimensional K V] in
/-- The first raising operator on a grid vector, for a positive index. -/
lemma grid_e1_pos (a : Fin (n1 + 1)) (ha : 0 < (a : ℕ)) {b : ℕ} (hb : b ≤ n2) :
    e1 (gridVec f1 f2 m0 a b) = (((a : ℕ) : K) * ((n1 : K) - ((a : ℕ) : K) + 1)) •
      gridVec f1 f2 m0 ((a : ℕ) - 1) b := by
  obtain ⟨j, hj⟩ := Nat.exists_eq_add_one_of_ne_zero ha.ne'
  rw [hj, Nat.add_sub_cancel, grid_e1_succ P1 P2 hc j hb]
  congr 1
  push_cast
  ring

omit [CharZero K] [FiniteDimensional K V] P1 in
/-- The second raising operator on a grid vector, for a positive index. -/
lemma grid_e2_pos (a : ℕ) (b : Fin (n2 + 1)) (hb : 0 < (b : ℕ)) :
    e2 (gridVec f1 f2 m0 a b) = (((b : ℕ) : K) * ((n2 : K) - ((b : ℕ) : K) + 1)) •
      gridVec f1 f2 m0 a ((b : ℕ) - 1) := by
  obtain ⟨j, hj⟩ := Nat.exists_eq_add_one_of_ne_zero hb.ne'
  rw [hj, Nat.add_sub_cancel, grid_e2_succ P2 hc]
  congr 1
  push_cast
  ring

/-- The grid realises the standard bivariate action. -/
lemma gridFun_isBivariateGrid :
    IsBivariateGrid h1 e1 f1 h2 e2 f2 n1 n2 (gridFun f1 f2 m0 n1 n2) where
  h1_apply _ b := grid_h1 P1 P2 hc _ (Nat.lt_succ_iff.mp b.isLt)
  h2_apply _ _ := grid_h2 P2 hc _ _
  e1_zero b := grid_e1_zero P1 P2 hc (Nat.lt_succ_iff.mp b.isLt)
  e1_pos a ha b := grid_e1_pos P1 P2 hc a ha (Nat.lt_succ_iff.mp b.isLt)
  f1_lt _ _ _ := grid_f1 _ _
  f1_last b := grid_f1_last P1 P2 hc (Nat.lt_succ_iff.mp b.isLt)
  e2_zero _ := grid_e2_zero P2 hc _
  e2_pos _ b hb := grid_e2_pos P2 hc _ b hb
  f2_lt _ _ _ := grid_f2 hc _ _
  f2_last _ := grid_f2_last P2 hc _

end Grid


/-- The first-triple primitive vectors of weight `n`: vectors killed by `e` with `h`-weight `n`. -/
def primSpace (h e : Module.End K V) (n : K) : Submodule K V :=
  LinearMap.ker e ⊓ LinearMap.ker (h - n • (1 : Module.End K V))

/-- Membership in `primSpace`, in plain-operator form. -/
lemma mem_primSpace {h e : Module.End K V} {n : K} {v : V} :
    v ∈ primSpace h e n ↔ e v = 0 ∧ h v = n • v := by
  simp [primSpace, sub_eq_zero]

/-- An endomorphism commuting with `e` and `h` preserves `primSpace`. -/
lemma primSpace_map_mem {h e y : Module.End K V} {n : K} {v : V} (hey : Commute e y)
    (hhy : Commute h y) (hv : v ∈ primSpace h e n) : y v ∈ primSpace h e n := by
  rw [mem_primSpace] at hv ⊢
  have he : e (y v) = y (e v) := LinearMap.congr_fun hey.eq v
  have hh : h (y v) = y (h v) := LinearMap.congr_fun hhy.eq v
  rw [he, hh, hv.1, hv.2, map_zero, map_smul]
  exact ⟨rfl, rfl⟩

/-- A vector of `primSpace` that is nonzero is primitive. -/
lemma hasPrimitiveVectorWith_of_mem_primSpace {h e f : Module.End K V} {t : IsSl2Triple h e f}
    {n : K} {w : V} (hw : w ∈ primSpace h e n) (hne : w ≠ 0) : t.HasPrimitiveVectorWith w n :=
  ⟨hne, (mem_primSpace.mp hw).2, (mem_primSpace.mp hw).1⟩

/-- Commuting triples give commuting operators. -/
lemma commute_of_hcomm {h1 e1 f1 h2 e2 f2 : Module.End K V}
    (hcomm : ∀ x ∈ ({h1, e1, f1} : Set (Module.End K V)),
      ∀ y ∈ ({h2, e2, f2} : Set (Module.End K V)), ⁅x, y⁆ = 0) :
    ∀ x ∈ ({h1, e1, f1} : Set (Module.End K V)),
      ∀ y ∈ ({h2, e2, f2} : Set (Module.End K V)), Commute x y :=
  fun x hx y hy => commute_of_lie_eq_zero (hcomm x hx y hy)

/-- The representation space of a nonzero `sl₂`-triple is nontrivial. -/
lemma nontrivial_of_isSl2Triple {h e f : Module.End K V} (t : IsSl2Triple h e f) :
    Nontrivial V := by
  rcases subsingleton_or_nontrivial V with hsub | hnt
  · exact absurd (LinearMap.ext fun v => @Subsingleton.elim V hsub _ _ : h = 0) t.h_ne_zero
  · exact hnt

/-- A subspace stable under the generators is stable under the generated subalgebra. -/
lemma lie_mem_of_generators {h e f : Module.End K V} (t : IsSl2Triple h e f) (W : Submodule K V)
    (hh : ∀ v ∈ W, h v ∈ W) (he : ∀ v ∈ W, e v ∈ W) (hf : ∀ v ∈ W, f v ∈ W)
    (x : ↥(t.toLieSubalgebra (R := K))) {v : V} (hv : v ∈ W) : ⁅(x : Module.End K V), v⁆ ∈ W := by
  obtain ⟨c1, c2, c3, hc⟩ := IsSl2Triple.mem_toLieSubalgebra_iff.mp x.property
  rw [hc, t.lie_e_f]
  simp only [add_lie, smul_lie]
  exact W.add_mem (W.add_mem (W.smul_mem c1 (he v hv)) (W.smul_mem c2 (hf v hv)))
    (W.smul_mem c3 (hh v hv))

/-- A primitive vector of the induced triple on a Lie submodule is primitive in `V`. -/
lemma hasPrimitiveVectorWith_of_sub {h e f : Module.End K V} {t : IsSl2Triple h e f}
    {N : LieSubmodule K ↥(t.toLieSubalgebra (R := K)) V} {w : N} {n : K}
    (P : (isSl2Triple_sub (K := K) t).HasPrimitiveVectorWith w n) :
    t.HasPrimitiveVectorWith (w : V) n := by
  refine ⟨fun hz => P.ne_zero (Subtype.ext hz), ?_, ?_⟩
  · have hh : (↑(⁅hSub (K := K) t, w⁆) : V) = (↑((n : K) • w) : V) := by rw [P.lie_h]
    rwa [LieSubmodule.coe_bracket, LieSubalgebra.coe_bracket_of_module, Module.End.lie_apply,
      LieSubmodule.coe_smul] at hh
  · have hh : (↑(⁅eSub (K := K) t, w⁆) : V) = (↑(0 : ↥N) : V) := by rw [P.lie_e]
    rwa [LieSubmodule.coe_bracket, LieSubalgebra.coe_bracket_of_module, Module.End.lie_apply,
      ZeroMemClass.coe_zero] at hh

section Exists

variable [IsAlgClosed K] [CharZero K] [FiniteDimensional K V]

/-- A nonzero subspace stable under the generators contains a primitive vector. -/
lemma exists_primitive_in_invariant {h e f : Module.End K V} (t : IsSl2Triple h e f)
    (W : Submodule K V) (hW : W ≠ ⊥) (hh : ∀ v ∈ W, h v ∈ W) (he : ∀ v ∈ W, e v ∈ W)
    (hf : ∀ v ∈ W, f v ∈ W) : ∃ (n : ℕ) (w : V), w ∈ W ∧ t.HasPrimitiveVectorWith w (n : K) := by
  let N : LieSubmodule K ↥(t.toLieSubalgebra (R := K)) V :=
    { __ := W, lie_mem := fun {x v} hv => lie_mem_of_generators t W hh he hf x hv }
  have : Nontrivial ↥N := by
    rw [LieSubmodule.nontrivial_iff_ne_bot]
    exact fun hbot => hW ((congrArg LieSubmodule.toSubmodule hbot).trans
      LieSubmodule.bot_toSubmodule)
  have : FiniteDimensional K ↥N :=
    FiniteDimensional.finiteDimensional_submodule (N : Submodule K V)
  obtain ⟨ν, w, -, P⟩ :=
    (isSl2Triple_sub (K := K) t).exists_hasPrimitiveVectorWith (R := K) (M := ↥N)
  obtain ⟨n, rfl⟩ := P.exists_nat
  exact ⟨n, w, w.property, hasPrimitiveVectorWith_of_sub P⟩

variable {h1 e1 f1 h2 e2 f2 : Module.End K V}
    (t1 : IsSl2Triple h1 e1 f1) (t2 : IsSl2Triple h2 e2 f2)
    (hcomm : ∀ x ∈ ({h1, e1, f1} : Set (Module.End K V)),
      ∀ y ∈ ({h2, e2, f2} : Set (Module.End K V)), ⁅x, y⁆ = 0)
    (hirr : JointlyIrreducible h1 e1 f1 h2 e2 f2)

omit [IsAlgClosed K] [CharZero K] [FiniteDimensional K V] in
/-- The primitive space of the first triple is stable under every operator of the second. -/
lemma primSpace_stable {n : K} {y : Module.End K V} {v : V}
    (hc : ∀ x ∈ ({h1, e1, f1} : Set (Module.End K V)),
      ∀ y ∈ ({h2, e2, f2} : Set (Module.End K V)), Commute x y)
    (hy : y ∈ ({h2, e2, f2} : Set (Module.End K V))) (hv : v ∈ primSpace h1 e1 n) :
    y v ∈ primSpace h1 e1 n :=
  primSpace_map_mem (hc e1 (by simp) y hy) (hc h1 (by simp) y hy) hv

include t1 t2 hcomm in
/-- Two commuting triples have a common primitive vector. The primitive-weight space for
the first triple is invariant under the second, so a primitive vector for the second can be
chosen inside it. -/
lemma exists_joint_primitive : ∃ (n1 n2 : ℕ) (m0 : V), m0 ≠ 0 ∧
    t1.HasPrimitiveVectorWith m0 (n1 : K) ∧ t2.HasPrimitiveVectorWith m0 (n2 : K) := by
  have := nontrivial_of_isSl2Triple t1
  obtain ⟨μ1, m1, hm1ne, P1⟩ := t1.exists_hasPrimitiveVectorWith (R := K) (M := V)
  obtain ⟨n1, rfl⟩ := P1.exists_nat
  have hc := commute_of_hcomm hcomm
  obtain ⟨n2, w, hw, P2⟩ := exists_primitive_in_invariant t2 _
    ((Submodule.ne_bot_iff _).mpr ⟨m1, mem_primSpace.mpr ⟨prim_e P1, prim_h P1⟩, hm1ne⟩)
    (fun _ hv => primSpace_stable hc (by simp) hv) (fun _ hv => primSpace_stable hc (by simp) hv)
    (fun _ hv => primSpace_stable hc (by simp) hv)
  exact ⟨n1, n2, w, P2.ne_zero, hasPrimitiveVectorWith_of_mem_primSpace hw P2.ne_zero, P2⟩

include t1 t2 hcomm hirr in
/-- For a jointly irreducible pair of commuting triples, the vectors `f1 ^ a (f2 ^ b m0)`
form a basis. The basis realises the standard bivariate action, including the endpoints of
each string. -/
lemma exists_bivariate_basis :
    ∃ (n1 n2 : ℕ) (B : Module.Basis (Fin (n1 + 1) × Fin (n2 + 1)) K V),
      IsBivariateGrid h1 e1 f1 h2 e2 f2 n1 n2 B := by
  obtain ⟨n1, n2, m0, -, P1, P2⟩ := exists_joint_primitive t1 t2 hcomm
  have hc := commute_of_hcomm hcomm
  refine ⟨n1, n2, Module.Basis.mk (grid_linearIndependent P1 P2 hc)
    (top_le_span_gridFun P1 P2 hc hirr), ?_⟩
  rw [Module.Basis.coe_mk]
  exact gridFun_isBivariateGrid P1 P2 hc

end Exists

end PhyslibAlpha.Sl2
