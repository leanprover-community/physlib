/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.CondensedMatter.Crystal.PointGroup.Basic
public import Mathlib.RingTheory.Noetherian.Orzech
public import Mathlib.RingTheory.Noetherian.Basic
public import Mathlib.RingTheory.PrincipalIdealDomain
public import Mathlib.Algebra.EuclideanDomain.Int
public import Mathlib.LinearAlgebra.LinearIndependent.Defs

/-!

# Counting the point group of a Bravais lattice

The point group of an `n`-dimensional lattice with a finite set `N` of neighbour displacements
is counted by the possible images of the `n` basis vectors.

## i. Overview

An automorphism of `ℤⁿ` that preserves the set `N` of bonded displacements is determined by the
images of the basis vectors, which are neighbour displacements when the basis vectors are
themselves bonded. A tuple of neighbour displacements, one for each basis vector, defines such
an automorphism exactly when the linear map it determines maps `N` into itself, and is injective
on `N`. Injectivity on the finite set `N` makes the map a bijection of `N`, so its image contains
the basis, and a surjective endomorphism of `ℤⁿ` is an automorphism. The point group is therefore
in bijection with the set of such tuples, a finite set that is counted by a direct computation.

## ii. Key results

- `PeriodicGraph.pointStabilizerEquiv` : the point group is in bijection with the admissible
  tuples of neighbour displacements.
- `PeriodicGraph.card_pointGroup` : its cardinality is the number of admissible tuples.

## iii. Table of contents

- A. Linear maps determined by the images of the basis
- B. Admissible tuples
- C. The count

## iv. References

* N. Ashcroft & N. D. Mermin, Solid State Physics, Chapter 7.

-/

@[expose] public section

namespace CondensedMatter.Crystal

namespace PeriodicGraph

variable {n : ℕ}

/-! ## A. Linear maps determined by the images of the basis -/

/-- The linear map of `ℤⁿ` taking the basis vectors to the given vectors. -/
def act (v : Fin n → Fin n → ℤ) : (Fin n → ℤ) →ₗ[ℤ] (Fin n → ℤ) :=
  Fintype.linearCombination ℤ v

lemma act_apply (v : Fin n → Fin n → ℤ) (d : Fin n → ℤ) : act v d = ∑ j, d j • v j := by
  simp [act, Fintype.linearCombination_apply]

lemma act_single (v : Fin n → Fin n → ℤ) (j : Fin n) : act v (Pi.single j 1) = v j := by
  simp [act_apply, Pi.single_apply]

/-- A lattice automorphism is determined by the images of the basis vectors. -/
lemma apply_eq_act (A : AddAut (Fin n → ℤ)) (d : Fin n → ℤ) :
    A d = act (fun j => A (Pi.single j 1)) d := by
  rw [act_apply]
  conv_lhs => rw [← Finset.univ_sum_single d]
  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← map_zsmul]
  congr 1
  ext k
  simp [Pi.single_apply]

/-! ## B. Admissible tuples -/

/-- A tuple of neighbour displacements is admissible when its linear map takes the set of
neighbour displacements into itself, injectively. -/
structure Admissible (N : Finset (Fin n → ℤ)) (v : Fin n → Fin n → ℤ) : Prop where
  mem : ∀ j, v j ∈ N
  mapsTo : ∀ d ∈ N, act v d ∈ N
  injOn : Set.InjOn (act v) N

variable {N : Finset (Fin n → ℤ)} (hN : ∀ j, (Pi.single j 1 : Fin n → ℤ) ∈ N)
include hN

omit hN in
/-- An admissible tuple maps the set of neighbour displacements onto itself. -/
lemma Admissible.image_eq {v : Fin n → Fin n → ℤ} (hv : Admissible N v) :
    N.image (act v) = N := by
  classical
  refine Finset.eq_of_subset_of_card_le ?_ ?_
  · intro y hy
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hy
    exact hv.mapsTo d hd
  · rw [Finset.card_image_of_injOn hv.injOn]

/-- An admissible tuple gives a surjective linear map. -/
lemma Admissible.surjective {v : Fin n → Fin n → ℤ} (hv : Admissible N v) :
    Function.Surjective (act v) := by
  classical
  intro y
  have hrange : ∀ j, (Pi.single j 1 : Fin n → ℤ) ∈ LinearMap.range (act v) := fun j => by
    have : (Pi.single j 1 : Fin n → ℤ) ∈ N.image (act v) := by rw [hv.image_eq]; exact hN j
    obtain ⟨d, _, hd⟩ := Finset.mem_image.mp this
    exact ⟨d, hd⟩
  have : y ∈ LinearMap.range (act v) := by
    rw [← Finset.univ_sum_single y]
    refine Submodule.sum_mem _ fun j _ => ?_
    have h1 : (Pi.single j (y j) : Fin n → ℤ) = y j • Pi.single j 1 := by
      ext k; simp [Pi.single_apply]
    rw [h1]
    exact Submodule.smul_mem _ _ (hrange j)
  exact this

/-- An admissible tuple gives an injective linear map. -/
lemma Admissible.injective {v : Fin n → Fin n → ℤ} (hv : Admissible N v) :
    Function.Injective (act v) := by
  have : IsNoetherian ℤ (Fin n → ℤ) := isNoetherian_of_isNoetherianRing_of_finite ℤ _
  exact IsNoetherian.injective_of_surjective_endomorphism (act v) (hv.surjective hN)

/-- A displacement is a neighbour exactly when its image under an admissible tuple is. -/
lemma Admissible.act_mem_iff {v : Fin n → Fin n → ℤ} (hv : Admissible N v) (d : Fin n → ℤ) :
    act v d ∈ N ↔ d ∈ N := by
  classical
  refine ⟨fun h => ?_, hv.mapsTo d⟩
  rw [← hv.image_eq] at h
  obtain ⟨d', hd', hdd⟩ := Finset.mem_image.mp h
  rw [← hv.injective hN hdd]
  exact hd'

/-- The lattice automorphism of an admissible tuple. -/
noncomputable def Admissible.equiv {v : Fin n → Fin n → ℤ} (hv : Admissible N v) :
    AddAut (Fin n → ℤ) :=
  AddEquiv.ofBijective (act v).toAddMonoidHom ⟨hv.injective hN, hv.surjective hN⟩

lemma Admissible.equiv_apply {v : Fin n → Fin n → ℤ} (hv : Admissible N v) (d : Fin n → ℤ) :
    hv.equiv hN d = act v d := rfl

/-! ## C. The count -/

variable {g : PeriodicGraph (Crystal.ofUnitCell (Fin n → ℤ) Unit)}
  (hg : ∀ d, g.Bonded () () d ↔ d ∈ N)
include hg

/-- **The point group of a Bravais lattice is in bijection with the admissible tuples of
neighbour displacements.** -/
noncomputable def pointStabilizerEquiv : g.pointStabilizer ≃ {v // Admissible N v} where
  toFun A := ⟨fun j => (Multiplicative.toAdd A.1 : AddAut (Fin n → ℤ)) (Pi.single j 1), by
    have hA : ∀ d, (Multiplicative.toAdd A.1 : AddAut (Fin n → ℤ)) d ∈ N ↔ d ∈ N := fun d => by
      rw [← hg, ← hg]; exact A.2 d
    refine ⟨fun j => (hA _).2 (hN j), fun d hd => ?_, ?_⟩
    · rw [← apply_eq_act]; exact (hA d).2 hd
    · intro d _ d' _ h
      rw [← apply_eq_act, ← apply_eq_act] at h
      exact (Multiplicative.toAdd A.1 : AddAut (Fin n → ℤ)).injective h⟩
  invFun v := ⟨Multiplicative.ofAdd (v.2.equiv hN), fun d => by
    rw [hg, hg]
    exact v.2.act_mem_iff hN d⟩
  left_inv A := by
    refine Subtype.ext ?_
    refine Multiplicative.toAdd.injective (AddEquiv.ext fun d => ?_)
    exact (apply_eq_act (Multiplicative.toAdd A.1 : AddAut (Fin n → ℤ)) d).symm
  right_inv v := by
    refine Subtype.ext (funext fun j => ?_)
    exact act_single v.1 j

/-- **The order of the point group** is the number of admissible tuples of neighbour
displacements. -/
lemma card_pointGroup : Nat.card g.pointGroup = Nat.card {v // Admissible N v} :=
  (Nat.card_congr (pointGroupEquiv g).toEquiv).trans
    (Nat.card_congr (pointStabilizerEquiv hN hg))


end PeriodicGraph

end CondensedMatter.Crystal
