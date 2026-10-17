/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.CondensedMatter.Crystal.Brillouin
public import Mathlib.Analysis.Complex.Circle

/-!

# Coordinates on the Brillouin zone and the action of the symmetries

The Brillouin zone of `ℤ^d` is the torus of coordinates modulo `1`, and a symmetry acts on the
coordinates by an explicit integer matrix.

## i. Overview

A crystal momentum of the lattice `ℤ^d` is a character `r ↦ exp (2πi k · r)`, determined by the
coordinates `k ∈ ℝ^d` modulo `ℤ^d`: the Brillouin zone is the torus `ℝ^d / ℤ^d`, in coordinates
along the reciprocal basis. A symmetry with linear part `A` sends the momentum of coordinates `k`
to the momentum of coordinates `k'`, with `k'_j = ∑_i k_i (A⁻¹ e_j)_i`: the transpose of the
inverse of the matrix of `A`. Momenta with coordinates in `(1/n) ℤ`, which include the high-symmetry
points of the standard lattices, are the points of finite order. Their equality and the action of a
symmetry on them reduce to divisibility of integers, which can be decided by computation.

Together with `littleGroup` and `IrreducibleZone`, this lets one prove which momenta are equivalent
and what the little group of a momentum is for a given lattice, by integer arithmetic.

## ii. Key results

- `brillouinPoint` : the momentum with given coordinates.
- `brillouinPoint_eq_iff` : two sets of coordinates give the same momentum exactly when they
  differ by integers.
- `brillouinPoint_surjective` : every momentum has coordinates.
- `smul_brillouinPoint` : the action of a symmetry on coordinates.
- `torsionPoint`, `smul_torsionPoint`, `torsionPoint_eq_iff` : momenta of finite order.
- `mem_littleGroup_torsionPoint_iff` : the little group of a momentum of finite order.

## iii. Table of contents

- A. Momenta from coordinates
- B. The action of a symmetry on coordinates
- C. Momenta of finite order

## iv. References

* N. Ashcroft & N. D. Mermin, Solid State Physics, Chapters 5 and 7.

-/

@[expose] public section

namespace CondensedMatter.Crystal

variable {d : ℕ}

/-! ## A. Momenta from coordinates -/

/-- The momentum with coordinates `k` along the reciprocal basis: the character
`r ↦ exp (2πi k · r)` of `ℤ^d`. -/
noncomputable def brillouinPoint (k : Fin d → ℝ) : BrillouinZone (Fin d → ℤ) where
  toFun r := Circle.exp (2 * Real.pi * ∑ j, k j * (Multiplicative.toAdd r j : ℝ))
  map_one' := by simp
  map_mul' r r' := by
    rw [← Circle.exp_add]
    congr 1
    simp only [toAdd_mul, Pi.add_apply, Int.cast_add, mul_add, Finset.sum_add_distrib]
  continuous_toFun := continuous_of_discreteTopology

lemma brillouinPoint_apply (k : Fin d → ℝ) (r : Fin d → ℤ) :
    brillouinPoint k (Multiplicative.ofAdd r) =
      Circle.exp (2 * Real.pi * ∑ j, k j * (r j : ℝ)) := rfl

lemma brillouinPoint_single (k : Fin d → ℝ) (j : Fin d) :
    brillouinPoint k (Multiplicative.ofAdd (Pi.single j 1)) = Circle.exp (2 * Real.pi * k j) := by
  rw [brillouinPoint_apply]
  congr 2
  rw [Finset.sum_eq_single j]
  · simp
  · intro i _ hij; simp [hij]
  · exact fun h => absurd (Finset.mem_univ _) h

/-- **Two sets of coordinates give the same momentum exactly when they differ by integers.** -/
lemma brillouinPoint_eq_iff (k k' : Fin d → ℝ) :
    brillouinPoint k = brillouinPoint k' ↔ ∀ j, ∃ z : ℤ, k j - k' j = z := by
  constructor
  · intro h j
    have h1 := congrArg (fun χ : BrillouinZone (Fin d → ℤ) =>
      χ (Multiplicative.ofAdd (Pi.single j 1))) h
    simp only [brillouinPoint_single] at h1
    have h2 : Circle.exp (2 * Real.pi * (k j - k' j)) = 1 := by
      rw [mul_sub, Circle.exp_sub, h1, div_self']
    obtain ⟨m, hm⟩ := Circle.exp_eq_one.1 h2
    refine ⟨m, ?_⟩
    have hpi : (2 * Real.pi) ≠ 0 := by positivity
    apply mul_left_cancel₀ hpi
    rw [hm]; ring
  · intro h
    refine ContinuousMonoidHom.ext fun r => ?_
    change Circle.exp _ = Circle.exp _
    choose z hz using h
    have h3 : ∑ j, k j * ((Multiplicative.toAdd r j : ℤ) : ℝ) =
        ∑ j, k' j * ((Multiplicative.toAdd r j : ℤ) : ℝ) +
          ∑ j, (z j : ℝ) * ((Multiplicative.toAdd r j : ℤ) : ℝ) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [show k j = k' j + z j by linarith [hz j]]
      ring
    have h4 : 2 * Real.pi * ∑ j, (z j : ℝ) * ((Multiplicative.toAdd r j : ℤ) : ℝ) =
        ((∑ j, z j * Multiplicative.toAdd r j : ℤ) : ℝ) * (2 * Real.pi) := by
      push_cast; ring
    rw [h3, mul_add, Circle.exp_add, h4, Circle.exp_int_mul_two_pi, mul_one]

/-- A character of `ℤ^d` is determined by its values on the basis vectors. -/
lemma brillouinZone_ext {χ ψ : BrillouinZone (Fin d → ℤ)}
    (h : ∀ j, χ (Multiplicative.ofAdd (Pi.single j 1)) = ψ (Multiplicative.ofAdd (Pi.single j 1))) :
    χ = ψ := by
  have key : ∀ (φ : BrillouinZone (Fin d → ℤ)) (r : Fin d → ℤ),
      φ (Multiplicative.ofAdd r) = ∏ j, φ (Multiplicative.ofAdd (Pi.single j 1)) ^ r j := by
    intro φ r
    have hn : Multiplicative.ofAdd r =
        ∏ j, Multiplicative.ofAdd (Pi.single j 1 : Fin d → ℤ) ^ (r j) := by
      apply Multiplicative.toAdd.injective
      funext j
      simp [toAdd_prod, Finset.sum_apply, Pi.single_apply]
    conv_lhs => rw [hn, map_prod]
    simp_rw [map_zpow]
  refine ContinuousMonoidHom.ext fun r => ?_
  have := key χ (Multiplicative.toAdd r)
  have h2 := key ψ (Multiplicative.toAdd r)
  have e : Multiplicative.ofAdd (Multiplicative.toAdd r) = r := rfl
  rw [e] at this h2
  exact this.trans ((Finset.prod_congr rfl fun j _ => by rw [h j]).trans h2.symm)

/-- **Every momentum has coordinates.** -/
lemma brillouinPoint_surjective : Function.Surjective (brillouinPoint (d := d)) := by
  intro χ
  refine ⟨fun j => Complex.arg (χ (Multiplicative.ofAdd (Pi.single j 1))) / (2 * Real.pi), ?_⟩
  refine brillouinZone_ext fun j => ?_
  rw [brillouinPoint_single]
  have hpi : (2 * Real.pi) ≠ 0 := by positivity
  rw [mul_div_cancel₀ _ hpi]
  exact (Circle.exp_arg _)

/-! ## B. The action of a symmetry on coordinates -/

/-- A lattice automorphism is determined by its values on the basis vectors. -/
lemma apply_eq_sum_single (A : (Fin d → ℤ) ≃+ (Fin d → ℤ)) (r : Fin d → ℤ) (i : Fin d) :
    A r i = ∑ j, r j * A (Pi.single j 1) i := by
  conv_lhs => rw [← Finset.univ_sum_single r]
  rw [map_sum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  have : (Pi.single j (r j) : Fin d → ℤ) = r j • Pi.single j 1 := by
    ext k; simp [Pi.single_apply]
  rw [this, map_zsmul]
  simp

/-- **A symmetry acts on the coordinates of a momentum** by the transpose of the inverse of the
matrix of its linear part. -/
lemma smul_brillouinPoint {F : Type*} (s : CellSymmetry (Fin d → ℤ) F) (k : Fin d → ℝ) :
    s • brillouinPoint k =
      brillouinPoint (fun j => ∑ i, k i * (s.linear.symm (Pi.single j 1) i : ℝ)) := by
  refine brillouinZone_ext fun j => ?_
  rw [brillouinPoint_single, smul_apply, brillouinPoint_apply]

/-! ## C. Momenta of finite order -/

/-- The momentum with coordinates `m / n`: a point of finite order of the Brillouin zone. -/
noncomputable def torsionPoint (n : ℕ) (m : Fin d → ℤ) : BrillouinZone (Fin d → ℤ) :=
  brillouinPoint fun j => (m j : ℝ) / n

/-- **Momenta of finite order are equal exactly when the numerators agree modulo `n`.** -/
lemma torsionPoint_eq_iff {n : ℕ} (hn : 0 < n) (m m' : Fin d → ℤ) :
    torsionPoint n m = torsionPoint n m' ↔ ∀ j, (n : ℤ) ∣ m j - m' j := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [torsionPoint, torsionPoint, brillouinPoint_eq_iff]
  refine forall_congr' fun j => ?_
  constructor
  · rintro ⟨z, hz⟩
    refine ⟨z, ?_⟩
    have : ((m j - m' j : ℤ) : ℝ) = ((n * z : ℤ) : ℝ) := by
      push_cast
      field_simp at hz ⊢
      linarith
    exact_mod_cast this
  · rintro ⟨z, hz⟩
    refine ⟨z, ?_⟩
    have : ((m j - m' j : ℤ) : ℝ) = ((n * z : ℤ) : ℝ) := by exact_mod_cast hz
    push_cast at this
    field_simp
    linarith

/-- A symmetry acts on a momentum of finite order by an integer matrix on the numerators. -/
lemma smul_torsionPoint {F : Type*} (n : ℕ) (s : CellSymmetry (Fin d → ℤ) F) (m : Fin d → ℤ) :
    s • torsionPoint n m =
      torsionPoint n (fun j => ∑ i, m i * s.linear.symm (Pi.single j 1) i) := by
  unfold torsionPoint
  rw [smul_brillouinPoint]
  congr 1
  funext j
  push_cast
  rw [div_eq_mul_inv, Finset.sum_mul]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- **The little group of a momentum of finite order**, as integer arithmetic: a bond-preserving
symmetry fixes the momentum with numerators `m` modulo `n` exactly when the integer vector
obtained from the matrix of its linear part is congruent to `m` modulo `n`. -/
lemma mem_littleGroup_torsionPoint_iff {F : Type*} [Finite F]
    (g : PeriodicGraph (Crystal.ofUnitCell (Fin d → ℤ) F)) {n : ℕ} (hn : 0 < n)
    (m : Fin d → ℤ) (s : g.symmetries) :
    s ∈ g.littleGroup (torsionPoint n m) ↔
      ∀ j, (n : ℤ) ∣ (∑ i, m i * (s : CellSymmetry (Fin d → ℤ) F).linear.symm (Pi.single j 1) i) -
        m j := by
  rw [g.mem_littleGroup]
  change (s : CellSymmetry (Fin d → ℤ) F) • torsionPoint n m = torsionPoint n m ↔ _
  rw [smul_torsionPoint, torsionPoint_eq_iff hn]

end CondensedMatter.Crystal
