/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.CondensedMatter.Crystal.Geometry
public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.Topology.Algebra.PontryaginDual

/-!

# Reciprocal lattice

## i. Overview

A Bravais lattice with primitive translations `a₁, …, a_d` in Euclidean space acts on
functions of position by translation. A plane wave `r ↦ exp(i k · r)` of wave vector `k`
restricts to the lattice as the character `n ↦ exp(i Σ_j n_j ⟨a_j, k⟩)` of the translation
group `ℤ^d`. Two wave vectors give the same character exactly when they differ by an element of
the reciprocal lattice, the set of `k` with `⟨a_j, k⟩ ∈ 2π ℤ` for every `j`. The Brillouin zone
is the quotient of wave-vector space by this lattice, and it is the Pontryagin dual of the
translation group.

`dualCharacter a k` is the character of `ℤ^d` determined by the wave vector `k`.
`reciprocalLattice a` is its kernel in wave-vector space. For `d` independent vectors in
`ℝ^d`, `reciprocalBasis` is the basis `b_i` with `⟨a_j, b_i⟩ = 2π δ_ij`, and
`dualCharacter_surjective` states that every character of `ℤ^d` arises from a wave vector, so
that wave-vector space modulo the reciprocal lattice is the full dual.

## ii. Key results

- `dualCharacter` : the character of the translation group given by a wave vector.
- `reciprocalLattice` : the wave vectors whose plane wave is trivial on the lattice.
- `dualCharacter_eq_one_iff` : the kernel of `dualCharacter` is the reciprocal lattice.
- `reciprocalBasis` : the basis `b_i` with `⟨a_j, b_i⟩ = 2π δ_ij`.
- `dualCharacter_surjective` : every character of the translation group is a plane wave.

## iii. Table of contents

- A. Characters from wave vectors
- B. The reciprocal basis

## iv. References

* N. Ashcroft & N. D. Mermin, Solid State Physics, Chapter 5.

-/

@[expose] public section

namespace CondensedMatter.Crystal

open scoped RealInnerProductSpace

/-! ## A. Characters from wave vectors -/

section Characters

variable {d D : ℕ} (a : Fin d → EuclideanSpace ℝ (Fin D))

/-- The phase accumulated by a plane wave of wave vector `k` under the lattice translation
`n`. -/
noncomputable def phase (k : EuclideanSpace ℝ (Fin D)) (n : Multiplicative (Fin d → ℤ)) : ℝ :=
  ∑ j, (n.toAdd j : ℝ) * ⟪a j, k⟫

/-- The character of the translation group `ℤ^d` given by the plane wave of wave vector `k`. -/
noncomputable def dualCharacter (k : EuclideanSpace ℝ (Fin D)) :
    PontryaginDual (Multiplicative (Fin d → ℤ)) where
  toFun n := Circle.exp (phase a k n)
  map_one' := by simp [phase]
  map_mul' n m := by
    rw [← Circle.exp_add]
    congr 1
    simp [phase, add_mul, Finset.sum_add_distrib]
  continuous_toFun := continuous_of_discreteTopology

/-- The reciprocal lattice: wave vectors whose plane wave is trivial on every lattice
translation. -/
def reciprocalLattice : AddSubgroup (EuclideanSpace ℝ (Fin D)) where
  carrier := {k | ∀ j, ∃ m : ℤ, ⟪a j, k⟫ = 2 * Real.pi * m}
  zero_mem' j := ⟨0, by simp⟩
  add_mem' {k l} hk hl j := by
    obtain ⟨m, hm⟩ := hk j
    obtain ⟨m', hm'⟩ := hl j
    exact ⟨m + m', by rw [inner_add_right, hm, hm']; push_cast; ring⟩
  neg_mem' {k} hk j := by
    obtain ⟨m, hm⟩ := hk j
    exact ⟨-m, by rw [inner_neg_right, hm]; push_cast; ring⟩

/-- Evaluating the character of a wave vector gives the exponential of the phase. -/
lemma dualCharacter_apply (k : EuclideanSpace ℝ (Fin D)) (n : Multiplicative (Fin d → ℤ)) :
    dualCharacter a k n = Circle.exp (phase a k n) := rfl

/-- The phase of a lattice translation is additive in the wave vector. -/
lemma phase_add (k l : EuclideanSpace ℝ (Fin D)) (n : Multiplicative (Fin d → ℤ)) :
    phase a (k + l) n = phase a k n + phase a l n := by
  simp [phase, inner_add_right, mul_add, Finset.sum_add_distrib]

/-- A wave vector gives the trivial character exactly when it lies in the reciprocal lattice. -/
lemma dualCharacter_eq_one_iff (k : EuclideanSpace ℝ (Fin D)) :
    dualCharacter a k = 1 ↔ k ∈ reciprocalLattice a := by
  constructor
  · intro h j
    have h1 : Circle.exp (phase a k (Multiplicative.ofAdd (Pi.single j 1))) = 1 := by
      rw [← dualCharacter_apply, h]; rfl
    rw [Circle.exp_eq_one] at h1
    obtain ⟨m, hm⟩ := h1
    refine ⟨m, ?_⟩
    simpa [phase, Pi.single_apply, mul_comm] using hm
  · intro hk
    refine ContinuousMonoidHom.ext fun n => ?_
    change Circle.exp _ = 1
    rw [Circle.exp_eq_one]
    choose m hm using hk
    refine ⟨∑ j, n.toAdd j * m j, ?_⟩
    simp_rw [phase, hm]
    push_cast
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun j _ => by ring

/-- Wave vectors differing by a reciprocal lattice vector give the same character. -/
lemma dualCharacter_add_of_mem {k l : EuclideanSpace ℝ (Fin D)}
    (hl : l ∈ reciprocalLattice a) : dualCharacter a (k + l) = dualCharacter a k := by
  have h1 : ∀ n, Circle.exp (phase a l n) = 1 := fun n => by
    have := congrArg (fun χ : PontryaginDual (Multiplicative (Fin d → ℤ)) => χ n)
      ((dualCharacter_eq_one_iff a l).2 hl)
    exact this
  refine ContinuousMonoidHom.ext fun n => ?_
  change Circle.exp (phase a (k + l) n) = Circle.exp (phase a k n)
  rw [phase_add, Circle.exp_add, h1, mul_one]

end Characters

/-! ## B. The reciprocal basis -/

section Basis

variable {d : ℕ} [NeZero d] {a : Fin d → EuclideanSpace ℝ (Fin d)}

/-- The basis of space formed by independent primitive translations. -/
noncomputable def latticeBasis (ha : LinearIndependent ℝ a) :
    Module.Basis (Fin d) ℝ (EuclideanSpace ℝ (Fin d)) :=
  basisOfLinearIndependentOfCardEqFinrank ha (by simp)

/-- The reciprocal basis `b_i`, characterized by `⟨a_j, b_i⟩ = 2π δ_ij`. -/
noncomputable def reciprocalBasis (ha : LinearIndependent ℝ a) (i : Fin d) :
    EuclideanSpace ℝ (Fin d) :=
  (2 * Real.pi) •
    (InnerProductSpace.toDual ℝ _).symm (((latticeBasis ha).coord i).toContinuousLinearMap)

/-- The reciprocal basis is dual to the primitive translations up to the factor `2π`. -/
lemma inner_reciprocalBasis (ha : LinearIndependent ℝ a) (i j : Fin d) :
    ⟪a j, reciprocalBasis ha i⟫ = if i = j then 2 * Real.pi else 0 := by
  rw [reciprocalBasis, inner_smul_right, real_inner_comm, InnerProductSpace.toDual_symm_apply]
  have : latticeBasis ha j = a j := by simp [latticeBasis]
  simp [← this, Module.Basis.coord_apply, Finsupp.single_apply, eq_comm]

/-- Every character of the translation group is the plane wave of some wave vector. -/
lemma dualCharacter_surjective (ha : LinearIndependent ℝ a) :
    Function.Surjective (dualCharacter a) := by
  intro χ
  let θ : Fin d → ℝ := fun j => Complex.arg (χ (Multiplicative.ofAdd (Pi.single j 1)))
  refine ⟨∑ i, (θ i / (2 * Real.pi)) • reciprocalBasis ha i, ?_⟩
  have hk : ∀ j, ⟪a j, ∑ i, (θ i / (2 * Real.pi)) • reciprocalBasis ha i⟫ = θ j := by
    intro j
    simp only [inner_sum, inner_smul_right, inner_reciprocalBasis]
    simp [Real.pi_ne_zero]
  refine ContinuousMonoidHom.ext fun n => ?_
  have hn : n = ∏ j, Multiplicative.ofAdd (Pi.single j 1 : Fin d → ℤ) ^ (n.toAdd j) := by
    apply Multiplicative.toAdd.injective
    funext j
    simp [toAdd_prod, Finset.sum_apply, Pi.single_apply]
  have e : ∀ j, χ (Multiplicative.ofAdd (Pi.single j 1)) = Circle.exp (θ j) := fun j =>
    (Circle.exp_arg _).symm
  symm
  change χ n = Circle.exp (phase a _ n)
  have hsum : ∀ f : Fin d → ℝ, ∏ j, Circle.exp (f j) = Circle.exp (∑ j, f j) := by
    intro f
    induction (Finset.univ : Finset (Fin d)) using Finset.induction_on with
    | empty => simp
    | insert j t hj ih => rw [Finset.prod_insert hj, Finset.sum_insert hj, Circle.exp_add, ih]
  conv_lhs => rw [hn, map_prod]
  simp_rw [map_zpow, e, phase, hk, ← Circle.exp_intCast_mul]
  exact hsum _

end Basis

end CondensedMatter.Crystal
