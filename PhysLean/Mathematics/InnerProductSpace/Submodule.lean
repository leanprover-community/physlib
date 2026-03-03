/-
Copyright (c) 2026 Gregory J. Loges. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregory J. Loges
-/
import Mathlib.Analysis.InnerProductSpace.LinearPMap
/-!

# Submodules of `E × E`

In this module we define `submoduleToLp` which reinterprets a submodule of `E × E`,
where `E` is an inner product space, as a submodule of `WithLp 2 (E × E)`.
This allows us to take advantage of the inner product structure, since otherwise
by default `E × E` is given the sup norm.

-/

namespace InnerProductSpaceSubmodule

open LinearPMap Submodule

variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  (M : Submodule ℂ (E × E))

/-- The submodule of `WithLp 2 (E × E)` defined by `M`. -/
def submoduleToLp : Submodule ℂ (WithLp 2 (E × E)) where
  carrier := {x | x.ofLp ∈ M}
  add_mem' := by
    intro a b ha hb
    exact Submodule.add_mem M ha hb
  zero_mem' := Submodule.zero_mem M
  smul_mem' := by
    intro c x hx
    exact Submodule.smul_mem M c hx

lemma mem_submodule_iff_mem_submoduleToLp (f : E × E) :
    f ∈ M ↔ (WithLp.toLp 2 f) ∈ submoduleToLp M := Eq.to_iff rfl

lemma submoduleToLp_closure :
    (submoduleToLp M.topologicalClosure) = (submoduleToLp M).topologicalClosure := by
  rw [Submodule.ext_iff]
  intro x
  rw [← mem_submodule_iff_mem_submoduleToLp]
  change x.ofLp ∈ _root_.closure M ↔ x ∈ _root_.closure (submoduleToLp M)
  repeat rw [mem_closure_iff_nhds]
  constructor
  · intro h t ht
    apply mem_nhds_iff.mp at ht
    rcases ht with ⟨t1, ht1, ht1', hx⟩
    have : ∃ t' ∈ nhds x.ofLp, (∀ y ∈ t', WithLp.toLp 2 y ∈ t1) := by
      refine Filter.eventually_iff_exists_mem.mp ?_
      apply ContinuousAt.eventually_mem (by fun_prop) (IsOpen.mem_nhds ht1' hx)
    rcases this with ⟨t2, ht2, ht2'⟩
    rcases h t2 ht2 with ⟨w, hw⟩
    use WithLp.toLp 2 w
    exact ⟨Set.mem_preimage.mp (ht1 (ht2' w hw.1)),
      (mem_submodule_iff_mem_submoduleToLp M w).mpr hw.2⟩
  · intro h t ht
    apply mem_nhds_iff.mp at ht
    rcases ht with ⟨t1, ht1, ht1', hx⟩
    have : ∃ t' ∈ nhds x, (∀ y ∈ t', y.ofLp ∈ t1) := by
      refine Filter.eventually_iff_exists_mem.mp ?_
      exact ContinuousAt.eventually_mem (by fun_prop) (IsOpen.mem_nhds ht1' hx)
    rcases this with ⟨t2, ht2, ht2'⟩
    rcases h t2 ht2 with ⟨w, hw⟩
    use w.ofLp
    exact ⟨Set.mem_preimage.mp (ht1 (ht2' w hw.1)), (mem_toAddSubgroup (submoduleToLp M)).mp hw.2⟩

lemma mem_submodule_closure_iff_mem_submoduleToLp_closure (f : E × E) :
    f ∈ M.topologicalClosure ↔ (WithLp.toLp 2 f) ∈ (submoduleToLp M).topologicalClosure := by
  rw [← submoduleToLp_closure]
  rfl

lemma mem_submodule_adjoint_iff_mem_submoduleToLp_orthogonal (f : E × E) :
    f ∈ M.adjoint ↔ WithLp.toLp 2 (f.2, -f.1) ∈ (submoduleToLp M)ᗮ := by
  constructor <;> intro h
  · rw [mem_orthogonal]
    intro u hu
    rw [mem_adjoint_iff] at h
    have h' : inner ℂ u.snd f.1 = inner ℂ u.fst f.2 := by
      rw [← sub_eq_zero]
      exact h u.fst u.snd hu
    simp [h']
  · rw [mem_adjoint_iff]
    intro a b hab
    rw [mem_orthogonal] at h
    have hab' := (mem_submodule_iff_mem_submoduleToLp M (a, b)).mp hab
    have h' : inner ℂ a f.2 = inner ℂ b f.1 := by
      rw [← sub_eq_zero, sub_eq_add_neg, ← inner_neg_right]
      exact h (WithLp.toLp 2 (a, b)) hab'
    simp [h']

lemma mem_submodule_adjoint_adjoint_iff_mem_submoduleToLp_orthogonal_orthogonal (f : E × E) :
    f ∈ M.adjoint.adjoint ↔ WithLp.toLp 2 f ∈ (submoduleToLp M)ᗮᗮ := by
  simp only [mem_adjoint_iff]
  trans ∀ v, (∀ w ∈ submoduleToLp M, inner ℂ w v = 0) → inner ℂ v (WithLp.toLp 2 f) = 0
  · constructor <;> intro h
    · intro v hw
      have h' := h (-v.snd) v.fst
      rw [inner_neg_left, sub_neg_eq_add] at h'
      apply h'
      intro a b hab
      rw [inner_neg_right, neg_sub_left, neg_eq_zero]
      exact hw (WithLp.toLp 2 (a, b)) ((mem_submodule_iff_mem_submoduleToLp M (a, b)).mp hab)
    · intro a b h'
      rw [sub_eq_add_neg, ← inner_neg_left]
      apply h (WithLp.toLp 2 (b, -a))
      intro w hw
      have hw' := h' w.fst w.snd hw
      rw [sub_eq_zero] at hw'
      simp [hw']
  simp only [← mem_orthogonal]

lemma mem_submodule_closure_adjoint_iff_mem_submoduleToLp_closure_orthogonal (f : E × E) :
    f ∈ M.topologicalClosure.adjoint ↔
    WithLp.toLp 2 (f.2, -f.1) ∈ (submoduleToLp M).topologicalClosureᗮ := by
  rw [mem_submodule_adjoint_iff_mem_submoduleToLp_orthogonal, submoduleToLp_closure]

end InnerProductSpaceSubmodule
