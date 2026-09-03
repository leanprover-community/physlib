/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.Dimension.Finite
public import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# The dimension of an internal direct sum

A vector space that is the internal direct sum of a finite family of finite-dimensional subspaces
has the sum of their dimensions, `TauCeti.finrank_eq_sum_finrank_of_isInternal`. Finiteness is
asked of the summands rather than of the ambient space: the two are equivalent here, and the
former is the form available at a call site that only knows its summands.

`TauCeti.finsum_finrank_eq_finrank_of_isInternal` is the same count for a decomposition indexed by
an arbitrary type in which all but finitely many summands vanish, written with `finsum`. A graded
decomposition is usually indexed by `ℤ` even when only finitely many degrees occur, so this is the
form such a decomposition meets.

Mathlib has `Module.finrank_directSum` for the *external* direct sum `⨁ i, M i` and
`DirectSum.IsInternal` for an internal decomposition, but not the dimension count that combining
them gives; the bridge is the canonical isomorphism
`LinearEquiv.ofBijective (DirectSum.coeLinearMap V)` an internal decomposition provides.
-/

public section

namespace TauCeti

open scoped DirectSum

/-- **The dimensions of the summands of an internal direct sum add up.** -/
theorem finrank_eq_sum_finrank_of_isInternal {K M ι : Type*} [DivisionRing K] [AddCommGroup M]
    [Module K M] [Fintype ι] [DecidableEq ι] {V : ι → Submodule K M}
    [∀ i, Module.Finite K (V i)] (h : DirectSum.IsInternal V) :
    Module.finrank K M = ∑ i, Module.finrank K (V i) := by
  rw [← (LinearEquiv.ofBijective (DirectSum.coeLinearMap V) h).finrank_eq,
    Module.finrank_directSum]

/-- **The dimension of an independent finite sum of subspaces is the sum of their dimensions.**
Unlike `TauCeti.finrank_eq_sum_finrank_of_isInternal`, the ambient module here is the supremum of
the given family rather than an independently supplied module. -/
theorem finrank_iSup_eq_sum_finrank_of_iSupIndep {K M ι : Type*} [DivisionRing K]
    [AddCommGroup M] [Module K M] [Fintype ι] {V : ι → Submodule K M}
    [∀ i, Module.Finite K (V i)] (h : iSupIndep V) :
    Module.finrank K ((⨆ i, V i) : Submodule K M) = ∑ i, Module.finrank K (V i) := by
  classical
  let S : Submodule K M := ⨆ i, V i
  have hV : ∀ i, V i ≤ S := fun i ↦ le_iSup V i
  let e : Submodule K S ≃o Set.Iic S := S.mapIic
  have he : (e ∘ fun i ↦ (V i).comap S.subtype) = fun i ↦ ⟨V i, hV i⟩ := by
    funext i
    apply Subtype.ext
    simp only [Function.comp_apply, e, Submodule.coe_mapIic_apply]
    rw [Submodule.map_comap_subtype, inf_of_le_right (hV i)]
  have hindep : iSupIndep fun i ↦ (V i).comap S.subtype := by
    rw [← iSupIndep_map_orderIso_iff e, he]
    exact iSupIndep.of_coe_Iic_comp h
  have hint : DirectSum.IsInternal fun i ↦ (V i).comap S.subtype := by
    refine DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top hindep ?_
    apply e.injective
    calc
      e (⨆ i, (V i).comap S.subtype) = ⨆ i, e ((V i).comap S.subtype) := e.map_iSup _
      _ = ⨆ i, ⟨V i, hV i⟩ := congrArg iSup he
      _ = ⟨S, Set.mem_Iic.mpr le_rfl⟩ := Subtype.ext (by simp [S])
      _ = e ⊤ := e.map_top.symm
  rw [finrank_eq_sum_finrank_of_isInternal hint]
  exact Finset.sum_congr rfl fun i _ ↦
    (Submodule.comapSubtypeEquivOfLe (hV i)).finrank_eq

/-- **The dimensions of the summands of an internal direct sum add up**, for a decomposition
indexed by an arbitrary type in which only finitely many summands are nonzero. -/
theorem finsum_finrank_eq_finrank_of_isInternal {K M ι : Type*} [DivisionRing K] [AddCommGroup M]
    [Module K M] [DecidableEq ι] {V : ι → Submodule K M} [∀ i, Module.Finite K (V i)]
    (h : DirectSum.IsInternal V) (hV : {i | V i ≠ ⊥}.Finite) :
    ∑ᶠ i, Module.finrank K (V i) = Module.finrank K M := by
  obtain ⟨hindep, htop⟩ := (DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top V).1 h
  have hbot : ∀ i ∉ hV.toFinset, V i = ⊥ := by
    intro i hi
    simpa using hV.mem_toFinset.not.1 hi
  have hsub : DirectSum.IsInternal fun i : (hV.toFinset : Finset ι) ↦ V i := by
    refine (DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top _).2
      ⟨hindep.comp Subtype.val_injective, top_unique ?_⟩
    rw [← htop]
    refine iSup_le fun i ↦ ?_
    by_cases hi : i ∈ hV.toFinset
    · exact le_iSup (fun j : (hV.toFinset : Finset ι) ↦ V j) ⟨i, hi⟩
    · simp [hbot i hi]
  have hsupport : (Function.support fun i ↦ Module.finrank K (V i)) ⊆ hV.toFinset :=
    fun i hi ↦ hV.mem_toFinset.2 fun hb ↦ hi (by simp [hb])
  rw [finsum_eq_sum_of_support_subset _ hsupport, finrank_eq_sum_finrank_of_isInternal hsub]
  exact (Finset.sum_coe_sort _ _).symm

end TauCeti
