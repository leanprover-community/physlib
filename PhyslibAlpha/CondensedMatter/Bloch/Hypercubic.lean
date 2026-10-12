/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.CondensedMatter.Bloch.PointSymmetry
public import PhyslibAlpha.CondensedMatter.Crystal.PointGroup.Hypercubic
public import Mathlib.Data.Fin.Tuple.Sort
public import Mathlib.Algebra.Order.Round

/-!

# Nearest-neighbour hopping on the hypercubic lattice

The band of nearest-neighbour hopping on the hypercubic lattice, and the irreducible zone modulo
the hyperoctahedral group.

## i. Overview

Nearest-neighbour hopping with amplitude `t` on `ℤ^d` has the Bloch matrix, a `1 × 1` matrix,
`2 t ∑_j cos (2π k_j)` at the momentum with coordinates `k`. Every signed permutation of the
axes is a symmetry of the lattice, and acts on the coordinates by permuting them and changing
their signs, so the band is invariant. Every momentum is carried by a signed permutation into the
set `0 ≤ k_{d-1} ≤ … ≤ k_1 ≤ k_0 ≤ 1/2`, a simplex which is a fraction `1 / (2^d d!)` of the
Brillouin zone. This is the irreducible zone: the Brillouin zone modulo the point group. The
spectrum of the hopping is therefore the set of values of the band on this simplex.

## ii. Key results

- `hypercubicZone` : the simplex `0 ≤ k_{d-1} ≤ … ≤ k_0 ≤ 1/2`.
- `coversOrbits_hypercubic` : every momentum is equivalent to a momentum in the simplex.
- `exists_signedPerm_to_cone` : an explicit signed permutation carrying a momentum into the
  simplex.
- `hypercubicBand`, `hoppingSymbol_hypercubic` : the Bloch matrix of nearest-neighbour hopping.
- `iUnion_spectrum_hypercubic` : the spectrum is the set of values of the band on the simplex.
- `littleGroup_gamma`, `littleGroup_corner` : the centre and the corner of the zone are fixed by
  every symmetry.
- `iUnion_spectrum_hypercubic_eq_Icc` : the spectrum is the interval `[-2 d |t|, 2 d |t|]`.

## iii. Table of contents

- A. The irreducible zone
- B. The nearest-neighbour band
- C. The spectrum is an interval
- D. The fully symmetric momenta

## iv. References

* N. Ashcroft & N. D. Mermin, Solid State Physics, Chapter 8.

-/

@[expose] public section

namespace CondensedMatter.Bloch

open CondensedMatter.Crystal

variable {d : ℕ}

/-! ## A. The irreducible zone -/

/-- The cone `0 ≤ k_{d-1} ≤ … ≤ k_0 ≤ 1/2` of coordinates. -/
def hypercubicCone (d : ℕ) : Set (Fin d → ℝ) :=
  {k | (∀ i, 0 ≤ k i ∧ k i ≤ 1 / 2) ∧ Antitone k}

/-- The irreducible zone of the hypercubic lattice: the momenta with coordinates in the cone. -/
def hypercubicZone (d : ℕ) : Set (BrillouinZone (Fin d → ℤ)) :=
  {χ | ∃ k ∈ hypercubicCone d, χ = brillouinPoint k}

/-- **A signed permutation is a bond-preserving symmetry of the hypercubic lattice.** -/
lemma signedPerm_mem_symmetries (π : Equiv.Perm (Fin d)) (ε : Fin d → Bool) :
    (⟨signedPerm π ε, 1, 0⟩ : CellSymmetry (Fin d → ℤ) Unit) ∈
      (hypercubicGraph d).symmetries := by
  rw [PeriodicGraph.mem_symmetries_iff]
  rintro ⟨⟩ ⟨⟩ r
  have := signedPerm_mem_pointStabilizer π ε r
  simpa using this.symm

/-- The coordinates of the image of a momentum under a symmetry whose linear part is a signed
permutation. -/
lemma smul_brillouinPoint_of_linear {F : Type*} (s : CellSymmetry (Fin d → ℤ) F)
    (π : Equiv.Perm (Fin d)) (ε : Fin d → Bool) (h : s.linear = signedPerm π ε)
    (k : Fin d → ℝ) :
    s • brillouinPoint k = brillouinPoint (fun j => (signOf (ε j) : ℝ) * k (π.symm j)) := by
  rw [smul_brillouinPoint, h]
  congr 1
  funext j
  have : ∀ i, ((signedPerm π ε).symm (Pi.single j 1) i : ℝ) =
      if π i = j then (signOf (ε j) : ℝ) else 0 := by
    intro i
    change ((signOf (ε (π i)) * (Pi.single j 1 : Fin d → ℤ) (π i) : ℤ) : ℝ) = _
    by_cases h : π i = j
    · subst h; simp
    · simp [h]
  simp only [this]
  rw [Finset.sum_eq_single (π.symm j)]
  · simp [mul_comm]
  · intro i _ hi
    have : π i ≠ j := fun h => hi (by rw [← h]; simp)
    simp [this]
  · exact fun h => absurd (Finset.mem_univ _) h

/-- The coordinates of the image of a momentum under a signed permutation. -/
lemma smul_brillouinPoint_signedPerm (π : Equiv.Perm (Fin d)) (ε : Fin d → Bool) (k : Fin d → ℝ) :
    (⟨signedPerm π ε, 1, 0⟩ : CellSymmetry (Fin d → ℤ) Unit) • brillouinPoint k =
      brillouinPoint (fun j => (signOf (ε j) : ℝ) * k (π.symm j)) :=
  smul_brillouinPoint_of_linear _ π ε rfl k

/-- **Every momentum is carried into the irreducible zone by a signed permutation.** -/
lemma exists_signedPerm_to_cone (k : Fin d → ℝ) :
    ∃ (π : Equiv.Perm (Fin d)) (ε : Fin d → Bool) (k' : Fin d → ℝ), k' ∈ hypercubicCone d ∧
      (⟨signedPerm π ε, 1, 0⟩ : CellSymmetry (Fin d → ℤ) Unit) • brillouinPoint k =
        brillouinPoint k' := by
  set u : Fin d → ℝ := fun i => k i - round (k i) with hu
  set a : Fin d → ℝ := fun i => |u i| with ha
  set σ : Equiv.Perm (Fin d) := Tuple.sort (fun i => -a i) with hσ
  have hmono : Monotone ((fun i => -a i) ∘ σ) := Tuple.monotone_sort _
  refine ⟨σ.symm, fun j => decide (0 ≤ u (σ j)), fun j => a (σ j), ⟨⟨fun i => ⟨abs_nonneg _, ?_⟩,
    ?_⟩, ?_⟩⟩
  · exact abs_sub_round (k (σ i))
  · intro i j hij
    have := hmono hij
    simp only [Function.comp_apply] at this
    linarith
  · rw [smul_brillouinPoint_signedPerm, eq_comm, brillouinPoint_eq_iff]
    intro j
    simp only [Equiv.symm_symm]
    by_cases h : 0 ≤ u (σ j)
    · have e1 : a (σ j) = k (σ j) - round (k (σ j)) := abs_of_nonneg h
      have e2 : (signOf (decide (0 ≤ u (σ j))) : ℝ) = 1 := by simp [signOf, h]
      refine ⟨-round (k (σ j)), ?_⟩
      show a (σ j) - (signOf (decide (0 ≤ u (σ j))) : ℝ) * k (σ j) = _
      rw [e1, e2]
      push_cast
      ring
    · have h' : u (σ j) < 0 := not_le.1 h
      have e1 : a (σ j) = -(k (σ j) - round (k (σ j))) := abs_of_neg h'
      have e2 : (signOf (decide (0 ≤ u (σ j))) : ℝ) = -1 := by simp [signOf, h]
      refine ⟨round (k (σ j)), ?_⟩
      show a (σ j) - (signOf (decide (0 ≤ u (σ j))) : ℝ) * k (σ j) = _
      rw [e1, e2]
      ring

/-- **The hypercubic zone covers the orbits of the point group.** -/
lemma coversOrbits_hypercubic :
    CoversOrbits (hypercubicGraph d) (hypercubicZone d) := by
  intro χ
  obtain ⟨k, rfl⟩ := brillouinPoint_surjective χ
  obtain ⟨π, ε, k', hk', h⟩ := exists_signedPerm_to_cone k
  refine ⟨QuotientGroup.mk ⟨_, signedPerm_mem_symmetries π ε⟩, k', hk', ?_⟩
  exact h

/-! ## B. The nearest-neighbour band -/

/-- The band of nearest-neighbour hopping with amplitude `t` on the hypercubic lattice, at the
momentum with coordinates `k`: `2 t ∑_j cos (2π k_j)`. -/
noncomputable def hypercubicBand (t : ℝ) (k : Fin d → ℝ) : ℝ :=
  2 * t * ∑ j, Real.cos (2 * Real.pi * k j)

private lemma brillouinPoint_single_sign (k : Fin d → ℝ) (j : Fin d) (b : ℤ) :
    brillouinPoint k (Multiplicative.ofAdd (Pi.single j b : Fin d → ℤ)) =
      Circle.exp (2 * Real.pi * (k j * b)) := by
  rw [brillouinPoint_apply]
  congr 2
  rw [Finset.sum_eq_single j]
  · simp
  · intro i _ hij; simp [hij]
  · exact fun h => absurd (Finset.mem_univ _) h

private lemma circle_exp_add_neg (x : ℝ) :
    ((Circle.exp x : Circle) : ℂ) + ((Circle.exp (-x) : Circle) : ℂ) =
      ((2 * Real.cos x : ℝ) : ℂ) := by
  rw [Circle.coe_exp, Circle.coe_exp, Complex.exp_mul_I, Complex.exp_mul_I]
  push_cast
  simp [Complex.cos_neg, Complex.sin_neg]
  ring

/-- **The Bloch matrix of nearest-neighbour hopping on the hypercubic lattice** is the `1 × 1`
matrix with the entry `2 t ∑_j cos (2π k_j)`. -/
lemma hoppingSymbol_hypercubic (t : ℝ) (k : Fin d → ℝ) :
    hoppingSymbol (uniformHopping (hypercubicGraph d) (t : ℂ)) (brillouinPoint k) =
      Matrix.of fun _ _ => ((hypercubicBand t k : ℝ) : ℂ) := by
  classical
  ext i j
  obtain rfl : i = () := Subsingleton.elim _ _
  obtain rfl : j = () := Subsingleton.elim _ _
  let f : Fin d × Bool → (Fin d → ℤ) := fun p => Pi.single p.1 (signOf p.2)
  have hf : Function.Injective f := by
    rintro ⟨j, b⟩ ⟨j', b'⟩ h
    have h1 := congrFun h j
    have hj : j = j' := by
      by_contra hne
      simp [f, hne, signOf_ne_zero] at h1
    subst hj
    simp only [f, Pi.single_eq_same] at h1
    exact Prod.ext rfl (signOf_injective h1)
  have hentry : ∀ r, entry (uniformHopping (hypercubicGraph d) (t : ℂ)) () () r =
      if (hypercubicGraph d).Bonded () () r then (t : ℂ) else 0 := fun r => rfl
  have hsub : (entry (uniformHopping (hypercubicGraph d) (t : ℂ)) () ()).support ⊆
      Finset.univ.image f := by
    intro r hr
    rw [Finsupp.mem_support_iff, hentry] at hr
    have hb : (hypercubicGraph d).Bonded () () r := by
      by_contra hnb; exact hr (ite_eq_right hnb)
    obtain ⟨j, h | h⟩ := (hypercubic_bonded_iff_exists r).1 hb
    · exact Finset.mem_image.2 ⟨(j, true), Finset.mem_univ _, by simp [f, h, signOf]⟩
    · exact Finset.mem_image.2 ⟨(j, false), Finset.mem_univ _, by
        simp only [f, signOf, h]; ext i; by_cases hi : i = j <;> simp [hi]⟩
  rw [hoppingSymbol_apply, Finsupp.sum_of_support_subset _ hsub _ (fun r _ => by simp),
    Finset.sum_image (fun p _ q _ h => hf h)]
  have hb0 : ∀ (j : Fin d) (b : Bool),
      (hypercubicGraph d).Bonded () () (Pi.single j (signOf b)) := by
    intro j b
    cases b
    · exact (hypercubic_bonded_iff_exists _).2 ⟨j, Or.inr (by
        ext i; by_cases hi : i = j <;> simp [signOf, hi])⟩
    · exact (hypercubic_bonded_iff_exists _).2 ⟨j, Or.inl (by simp [signOf])⟩
  have hb : ∀ p : Fin d × Bool, (hypercubicGraph d).Bonded () () (f p) := fun p => hb0 p.1 p.2
  simp only [hentry, hb, ite_true]
  rw [Fintype.sum_prod_type]
  simp only [Fintype.sum_bool, f]
  rw [Matrix.of_apply, hypercubicBand]
  push_cast
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  have e1 : signOf true = 1 := by simp [signOf]
  have e2 : signOf false = -1 := by simp [signOf]
  rw [brillouinPoint_single_sign, brillouinPoint_single_sign, e1, e2]
  have h1 : 2 * Real.pi * (k j * ((1 : ℤ) : ℝ)) = 2 * Real.pi * k j := by push_cast; ring
  have h2 : 2 * Real.pi * (k j * ((-1 : ℤ) : ℝ)) = -(2 * Real.pi * k j) := by push_cast; ring
  rw [h1, h2, ← add_mul, circle_exp_add_neg]
  push_cast
  ring

private lemma spectrum_const (c : ℂ) :
    spectrum ℂ (Matrix.of fun (_ : Unit) (_ : Unit) => c) = {c} := by
  have : (Matrix.of fun (_ : Unit) (_ : Unit) => c) = algebraMap ℂ (Matrix Unit Unit ℂ) c := by
    ext i j
    obtain rfl : i = () := Subsingleton.elim _ _
    obtain rfl : j = () := Subsingleton.elim _ _
    simp [Matrix.algebraMap_eq_diagonal]
  rw [this]
  exact spectrum.scalar_eq c

/-- **The spectrum of nearest-neighbour hopping on the hypercubic lattice** is the set of values
of the band `2 t ∑_j cos (2π k_j)` on the irreducible zone `0 ≤ k_{d-1} ≤ … ≤ k_0 ≤ 1/2`, which is
`1 / (2^d d!)` of the Brillouin zone. -/
lemma iUnion_spectrum_hypercubic (t : ℝ) :
    (⋃ χ : BrillouinZone (Fin d → ℤ),
        spectrum ℂ (hoppingSymbol (uniformHopping (hypercubicGraph d) (t : ℂ)) χ)) =
      {z : ℂ | ∃ k ∈ hypercubicCone d, z = ((hypercubicBand t k : ℝ) : ℂ)} := by
  rw [iUnion_spectrum_eq_of_covers (isHermitian_hoppingSymbol_uniform _ t)
    (isCovariant_uniformHopping _ (t : ℂ)) (coversOrbits_hypercubic (d := d))]
  ext z
  simp only [Set.mem_iUnion, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨χ, ⟨k, hk, rfl⟩, hz⟩
    rw [hoppingSymbol_hypercubic, spectrum_const] at hz
    exact ⟨k, hk, hz⟩
  · rintro ⟨k, hk, rfl⟩
    refine ⟨brillouinPoint k, ⟨k, hk, rfl⟩, ?_⟩
    rw [hoppingSymbol_hypercubic, spectrum_const]
    rfl

/-! ## C. The spectrum is an interval -/

lemma convex_hypercubicCone : Convex ℝ (hypercubicCone d) := by
  intro k hk k' hk' a b ha hb hab
  refine ⟨fun i => ⟨?_, ?_⟩, fun i j hij => ?_⟩
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    nlinarith [(hk.1 i).1, (hk'.1 i).1]
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    nlinarith [(hk.1 i).2, (hk'.1 i).2]
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    nlinarith [hk.2 hij, hk'.2 hij]

lemma continuous_hypercubicBand (t : ℝ) : Continuous (hypercubicBand (d := d) t) := by
  unfold hypercubicBand
  fun_prop

lemma abs_hypercubicBand_le (t : ℝ) (k : Fin d → ℝ) :
    |hypercubicBand t k| ≤ 2 * d * |t| := by
  unfold hypercubicBand
  rw [abs_mul, abs_mul, abs_two]
  have : |∑ j, Real.cos (2 * Real.pi * k j)| ≤ d := by
    calc _ ≤ ∑ j, |Real.cos (2 * Real.pi * k j)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _j : Fin d, (1 : ℝ) := Finset.sum_le_sum fun j _ => Real.abs_cos_le_one _
      _ = d := by simp
  calc 2 * |t| * |∑ j, Real.cos (2 * Real.pi * k j)| ≤ 2 * |t| * d :=
        mul_le_mul_of_nonneg_left this (by positivity)
    _ = 2 * d * |t| := by ring

/-- **The band of nearest-neighbour hopping takes exactly the values in `[-2 d |t|, 2 d |t|]` on
the irreducible zone.** -/
lemma hypercubicBand_image (t : ℝ) :
    hypercubicBand t '' hypercubicCone d = Set.Icc (-(2 * d * |t|)) (2 * d * |t|) := by
  refine Set.Subset.antisymm ?_ ?_
  · rintro _ ⟨k, -, rfl⟩
    exact abs_le.1 (abs_hypercubicBand_le t k)
  · have hc : IsPreconnected (hypercubicBand t '' hypercubicCone d) :=
      (convex_hypercubicCone.isPreconnected).image _ (continuous_hypercubicBand t).continuousOn
    have h0 : (0 : Fin d → ℝ) ∈ hypercubicCone d :=
      ⟨fun i => ⟨le_rfl, by norm_num⟩, fun i j _ => le_rfl⟩
    have h1 : (fun _ => (1 / 2 : ℝ) : Fin d → ℝ) ∈ hypercubicCone d :=
      ⟨fun i => ⟨by norm_num, le_rfl⟩, fun i j _ => le_rfl⟩
    have e0 : hypercubicBand (d := d) t 0 = 2 * d * t := by simp [hypercubicBand]; ring
    have e1 : hypercubicBand (d := d) t (fun _ => 1 / 2) = -(2 * d * t) := by
      have hcos : Real.cos (2 * Real.pi * 2⁻¹) = -1 := by
        rw [show 2 * Real.pi * 2⁻¹ = Real.pi by ring, Real.cos_pi]
      simp [hypercubicBand, hcos]
      ring
    rcases le_total 0 t with ht | ht
    · rw [abs_of_nonneg ht]
      have := hc.Icc_subset (a := hypercubicBand (d := d) t (fun _ => 1 / 2)) (b := hypercubicBand
        (d := d) t 0)
        ⟨_, h1, rfl⟩ ⟨_, h0, rfl⟩
      rwa [e0, e1] at this
    · rw [abs_of_nonpos ht]
      have := hc.Icc_subset (a := hypercubicBand (d := d) t 0) (b := hypercubicBand (d := d) t
        (fun _ => 1 / 2))
        ⟨_, h0, rfl⟩ ⟨_, h1, rfl⟩
      rw [e0, e1] at this
      convert this using 2 <;> ring

/-- **The spectrum of nearest-neighbour hopping on the hypercubic lattice is the interval
`[-2 d |t|, 2 d |t|]`.** -/
lemma iUnion_spectrum_hypercubic_eq_Icc (t : ℝ) :
    (⋃ χ : BrillouinZone (Fin d → ℤ),
        spectrum ℂ (hoppingSymbol (uniformHopping (hypercubicGraph d) (t : ℂ)) χ)) =
      ((↑) : ℝ → ℂ) '' Set.Icc (-(2 * d * |t|)) (2 * d * |t|) := by
  rw [iUnion_spectrum_hypercubic, ← hypercubicBand_image]
  ext z
  simp only [Set.mem_ofPred_eq, Set.mem_image]
  constructor
  · rintro ⟨k, hk, rfl⟩; exact ⟨_, ⟨k, hk, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨k, hk, rfl⟩, rfl⟩; exact ⟨k, hk, rfl⟩

/-! ## D. The fully symmetric momenta -/

/-- **The centre `Γ` of the Brillouin zone is fixed by every symmetry.** -/
lemma littleGroup_gamma (d : ℕ) :
    (hypercubicGraph d).littleGroup (brillouinPoint (0 : Fin d → ℝ)) = ⊤ := by
  refine (Subgroup.eq_top_iff' _).2 fun s => ?_
  rw [PeriodicGraph.mem_littleGroup]
  change (s : CellSymmetry (Fin d → ℤ) Unit) • brillouinPoint (0 : Fin d → ℝ) = _
  rw [smul_brillouinPoint]
  congr 1
  funext j
  simp

/-- **The corner `R = (1/2, …, 1/2)` of the Brillouin zone is fixed by every symmetry**: its
little group is the whole group. -/
lemma littleGroup_corner (d : ℕ) :
    (hypercubicGraph d).littleGroup (brillouinPoint (fun _ : Fin d => (1 / 2 : ℝ))) = ⊤ := by
  refine (Subgroup.eq_top_iff' _).2 fun s => ?_
  rw [PeriodicGraph.mem_littleGroup]
  obtain ⟨π, ε, h⟩ := (mem_pointStabilizer_hypercubic_iff
    (Multiplicative.ofAdd (s : CellSymmetry (Fin d → ℤ) Unit).linear)).1
    (PeriodicGraph.linear_mem_pointStabilizer _ s.2)
  change (s : CellSymmetry (Fin d → ℤ) Unit) • brillouinPoint (fun _ : Fin d => (1 / 2 : ℝ)) = _
  rw [smul_brillouinPoint_of_linear _ π ε h, eq_comm, brillouinPoint_eq_iff]
  intro j
  cases hε : ε j
  · exact ⟨1, by simp [signOf]; norm_num⟩
  · exact ⟨0, by simp [signOf]⟩

end CondensedMatter.Bloch
