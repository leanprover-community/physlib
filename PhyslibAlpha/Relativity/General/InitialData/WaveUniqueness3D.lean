/-
Copyright (c) 2026 The Gravitation formalisation contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Vergara Gil
-/

module

public import PhyslibAlpha.Relativity.General.InitialData.WaveEnergy3D

/-!

# Uniqueness for the 3D linear wave equation

## i. Overview

This file bundles the regularity used by the 3D energy method and proves
uniqueness by applying energy conservation to the difference of two solutions.
The difference has zero Cauchy data, so its conserved energy is zero; the
zero-energy lemma then forces `u_t` and `∇u` to vanish, and time integration
forces the difference itself to vanish.


## ii. Key results

- `WaveSolution3D`
- `wave_unique3D_of_same_data`

## iii. Table of contents

- A. Uniqueness for the three-dimensional problem

## iv. References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., AMS, 2010, §2.4. [ref: Evans2010PDE]
-/
@[expose] public section

/-! ## A. Uniqueness for the three-dimensional problem -/

open MeasureTheory BoxIntegral
open scoped Topology

namespace GeneralRelativity

/-- A regular solution of the 3D linear wave equation on a spatial box, with the
derivative fields and boundary conditions used by the energy method.  `M` bounds
the differentiated energy density. -/
structure WaveSolution3D
    (u ut : ℝ → Space3 → ℝ) (grad : ℝ → Space3 → Space3)
    (utt : ℝ → Space3 → ℝ) (gradt : ℝ → Space3 → Space3)
    (Dut : ℝ → Space3 → Space3 →L[ℝ] ℝ)
    (Dgrad : ℝ → Space3 → Space3 →L[ℝ] Space3)
    (lap : ℝ → Space3 → ℝ) (I : Box (Fin 3)) (M : ℝ) : Prop where
  hu_t : ∀ s x, HasDerivAt (fun s : ℝ => u s x) (ut s x) s
  hu_face_upper : ∀ (s : ℝ) (i : Fin 3) (y : Fin 2 → ℝ),
    u s (i.insertNth (I.upper i) y) = 0
  hu_face_lower : ∀ (s : ℝ) (i : Fin 3) (y : Fin 2 → ℝ),
    u s (i.insertNth (I.lower i) y) = 0
  hut : ∀ s x, HasDerivAt (fun s : ℝ => ut s x) (utt s x) s
  hgrad : ∀ s x, HasDerivAt (fun s : ℝ => grad s x) (gradt s x) s
  hut_cont : Continuous (Function.uncurry ut)
  hgrad_cont : Continuous (Function.uncurry grad)
  hutt_cont : Continuous (Function.uncurry utt)
  hgradt_cont : Continuous (Function.uncurry gradt)
  hbound : ∀ s x, ‖waveEnergy3DDerivIntegrand ut utt grad gradt s x‖ ≤ M
  hut_spatial : ∀ t x, HasFDerivAt (ut t) (Dut t x) x
  hgrad_spatial : ∀ t x, HasFDerivAt (grad t) (Dgrad t x) x
  hlap : ∀ t x, (∑ i : Fin 3, Dgrad t x (Pi.single i 1) i) = lap t x
  hgradut : ∀ (t : ℝ) (x : Space3) (i : Fin 3),
    Dut t x (Pi.single i 1) = gradt t x i
  hwave : ∀ t x, utt t x = lap t x
  hdiv_int : ∀ s, IntegrableOn
    (fun x => ∑ i, waveFlux3DDeriv ut grad Dut Dgrad s x (Pi.single i 1) i)
    (Box.Icc I)
  hut_face_upper : ∀ (s : ℝ) (i : Fin 3) (y : Fin 2 → ℝ),
    ut s (i.insertNth (I.upper i) y) = 0
  hut_face_lower : ∀ (s : ℝ) (i : Fin 3) (y : Fin 2 → ℝ),
    ut s (i.insertNth (I.lower i) y) = 0

/-- If the time derivative vanishes at every time, the field is constant in
time at that spatial point. -/
lemma u_eq_initial_of_ut_zero3D (u ut : ℝ → Space3 → ℝ) (x : Space3)
    (hu_t : ∀ s, HasDerivAt (fun s : ℝ => u s x) (ut s x) s)
    (hut0 : ∀ s, ut s x = 0) :
    ∀ t, u t x = u 0 x := by
  have hderiv : ∀ s, deriv (fun s : ℝ => u s x) s = 0 := by
    intro s
    rw [(hu_t s).deriv, hut0 s]
  exact fun t => is_const_of_deriv_eq_zero
    (fun s => (hu_t s).differentiableAt) hderiv t 0

/-- A point of the closed box that is not interior lies on a face. -/
lemma exists_coord_eq_bound_of_mem_Icc_not_mem_Ioo
    {I : Box (Fin 3)} {x : Space3}
    (hx : x ∈ Box.Icc I) (hxnot : x ∉ Box.Ioo I) :
    ∃ i : Fin 3, x i = I.lower i ∨ x i = I.upper i := by
  by_contra h
  apply hxnot
  change x ∈ Set.pi Set.univ
    (fun i : Fin 3 => Set.Ioo (I.lower i) (I.upper i))
  intro i _
  have hx' : x ∈ Box.Icc I := hx
  rw [Box.Icc_eq_pi] at hx'
  have hxi : I.lower i ≤ x i ∧ x i ≤ I.upper i :=
    hx' i (Set.mem_univ i)
  constructor
  · exact lt_of_le_of_ne hxi.1 (fun heq => h ⟨i, Or.inl heq.symm⟩)
  · exact lt_of_le_of_ne hxi.2 (fun heq => h ⟨i, Or.inr heq⟩)

/-- **Zero-data uniqueness in 3D.**  A regular wave solution with zero initial
position, velocity and gradient, and homogeneous Dirichlet data for the field,
vanishes on the closed box. -/
lemma wave_zero_of_zero_data3D
    (u ut : ℝ → Space3 → ℝ) (grad : ℝ → Space3 → Space3)
    (utt : ℝ → Space3 → ℝ) (gradt : ℝ → Space3 → Space3)
    (Dut : ℝ → Space3 → Space3 →L[ℝ] ℝ)
    (Dgrad : ℝ → Space3 → Space3 →L[ℝ] Space3)
    (lap : ℝ → Space3 → ℝ) (I : Box (Fin 3)) (M : ℝ)
    (S : WaveSolution3D u ut grad utt gradt Dut Dgrad lap I M)
    (hinit : ∀ x, u 0 x = 0)
    (hvel : ∀ x, ut 0 x = 0)
    (hgrad0 : ∀ x i, grad 0 x i = 0) :
    ∀ t x, x ∈ Box.Icc I → u t x = 0 := by
  have hEconst : ∀ t, waveEnergy3D ut grad I t = waveEnergy3D ut grad I 0 :=
    waveEnergy3D_eq_initial_of_wave ut utt grad gradt Dut Dgrad lap I M
      S.hut S.hgrad S.hut_cont S.hgrad_cont S.hutt_cont S.hgradt_cont S.hbound
      S.hut_spatial S.hgrad_spatial S.hlap S.hgradut S.hwave S.hdiv_int
      S.hut_face_upper S.hut_face_lower
  have hE0 : waveEnergy3D ut grad I 0 = 0 :=
    waveEnergy3D_eq_zero_initial ut grad I hvel hgrad0
  have hzero_ut : ∀ t x, x ∈ Box.Ioo I → ut t x = 0 := by
    intro t x hx
    have hEt : waveEnergy3D ut grad I t = 0 := by
      rw [hEconst t, hE0]
    exact (eq_zero_of_waveEnergy3D_eq_zero ut grad
      S.hut_cont S.hgrad_cont hEt x hx).1
  intro t x hx
  by_cases hxIoo : x ∈ Box.Ioo I
  · have hconst := u_eq_initial_of_ut_zero3D u ut x
      (fun s => S.hu_t s x) (fun s => hzero_ut s x hxIoo) t
    rw [hconst, hinit x]
  · obtain ⟨i, hi | hi⟩ :=
      exists_coord_eq_bound_of_mem_Icc_not_mem_Ioo hx hxIoo
    · have hrepr : i.insertNth (I.lower i) (i.removeNth x) = x := by
        rw [← hi]
        exact Fin.insertNth_self_removeNth i x
      rw [← hrepr]
      exact S.hu_face_lower t i (i.removeNth x)
    · have hrepr : i.insertNth (I.upper i) (i.removeNth x) = x := by
        rw [← hi]
        exact Fin.insertNth_self_removeNth i x
      rw [← hrepr]
      exact S.hu_face_upper t i (i.removeNth x)

/-- **General-data uniqueness in 3D.**  Two regular wave solutions with the same
initial position, velocity and spatial gradient, and the same homogeneous
Dirichlet data, agree on the closed box.  The proof applies the zero-data theorem
to their difference. -/
lemma wave_unique3D_of_same_data
    (u v : ℝ → Space3 → ℝ) (ut vt : ℝ → Space3 → ℝ)
    (grad vgrad : ℝ → Space3 → Space3)
    (utt vtt : ℝ → Space3 → ℝ) (gradt vgradt : ℝ → Space3 → Space3)
    (Dut vDut : ℝ → Space3 → Space3 →L[ℝ] ℝ)
    (Dgrad vDgrad : ℝ → Space3 → Space3 →L[ℝ] Space3)
    (lap vlap : ℝ → Space3 → ℝ) (I : Box (Fin 3)) (M N Mw : ℝ)
    (S : WaveSolution3D u ut grad utt gradt Dut Dgrad lap I M)
    (T : WaveSolution3D v vt vgrad vtt vgradt vDut vDgrad vlap I N)
    (hboundw : ∀ s x,
      ‖waveEnergy3DDerivIntegrand
        (fun s x => ut s x - vt s x)
        (fun s x => utt s x - vtt s x)
        (fun s x => grad s x - vgrad s x)
        (fun s x => gradt s x - vgradt s x) s x‖ ≤ Mw)
    (hdivw : ∀ s, IntegrableOn
      (fun x => ∑ i : Fin 3,
        waveFlux3DDeriv
          (fun s x => ut s x - vt s x)
          (fun s x => grad s x - vgrad s x)
          (fun s x => Dut s x - vDut s x)
          (fun s x => Dgrad s x - vDgrad s x)
          s x (Pi.single i 1) i) (Box.Icc I))
    (hinit : ∀ x, u 0 x = v 0 x)
    (hvel : ∀ x, ut 0 x = vt 0 x)
    (hgrad0 : ∀ x i, grad 0 x i = vgrad 0 x i) :
    ∀ t x, x ∈ Box.Icc I → u t x = v t x := by
  let w : ℝ → Space3 → ℝ := fun s x => u s x - v s x
  let wt : ℝ → Space3 → ℝ := fun s x => ut s x - vt s x
  let wgrad : ℝ → Space3 → Space3 := fun s x => grad s x - vgrad s x
  let wtt : ℝ → Space3 → ℝ := fun s x => utt s x - vtt s x
  let wgradt : ℝ → Space3 → Space3 := fun s x => gradt s x - vgradt s x
  let wDut : ℝ → Space3 → Space3 →L[ℝ] ℝ := fun s x => Dut s x - vDut s x
  let wDgrad : ℝ → Space3 → Space3 →L[ℝ] Space3 := fun s x => Dgrad s x - vDgrad s x
  let wlap : ℝ → Space3 → ℝ := fun s x => lap s x - vlap s x

  have hW : WaveSolution3D w wt wgrad wtt wgradt wDut wDgrad wlap I Mw := by
    refine {
      hu_t := ?_
      hu_face_upper := ?_
      hu_face_lower := ?_
      hut := ?_
      hgrad := ?_
      hut_cont := ?_
      hgrad_cont := ?_
      hutt_cont := ?_
      hgradt_cont := ?_
      hbound := ?_
      hut_spatial := ?_
      hgrad_spatial := ?_
      hlap := ?_
      hgradut := ?_
      hwave := ?_
      hdiv_int := ?_
      hut_face_upper := ?_
      hut_face_lower := ?_ }
    · intro s x
      convert (S.hu_t s x).sub (T.hu_t s x) using 1
    · intro s i y
      simp [w, S.hu_face_upper s i y, T.hu_face_upper s i y]
    · intro s i y
      simp [w, S.hu_face_lower s i y, T.hu_face_lower s i y]
    · intro s x
      convert (S.hut s x).sub (T.hut s x) using 1
    · intro s x
      convert (S.hgrad s x).sub (T.hgrad s x) using 1
    · convert S.hut_cont.sub T.hut_cont using 1
      funext p
      simp [wt, Function.uncurry, Pi.sub_apply]
    · convert S.hgrad_cont.sub T.hgrad_cont using 1
      funext p
      simp [wgrad, Function.uncurry, Pi.sub_apply]
    · convert S.hutt_cont.sub T.hutt_cont using 1
      funext p
      simp [wtt, Function.uncurry, Pi.sub_apply]
    · convert S.hgradt_cont.sub T.hgradt_cont using 1
      funext p
      simp [wgradt, Function.uncurry, Pi.sub_apply]
    · simpa [wt, wtt, wgrad, wgradt] using hboundw
    · intro t x
      convert (S.hut_spatial t x).sub (T.hut_spatial t x) using 1
    · intro t x
      convert (S.hgrad_spatial t x).sub (T.hgrad_spatial t x) using 1
    · intro t x
      have h1 := S.hlap t x
      have h2 := T.hlap t x
      change (∑ i : Fin 3,
        (Dgrad t x (Pi.single i 1) i - vDgrad t x (Pi.single i 1) i)) =
          lap t x - vlap t x
      rw [Finset.sum_sub_distrib, h1, h2]
    · intro t x i
      have h1 := S.hgradut t x i
      have h2 := T.hgradut t x i
      change Dut t x (Pi.single i 1) - vDut t x (Pi.single i 1) =
        gradt t x i - vgradt t x i
      rw [h1, h2]
    · intro t x
      simp [wtt, wlap, S.hwave t x, T.hwave t x]
    · simpa [wt, wgrad, wDut, wDgrad] using hdivw
    · intro s i y
      simp [wt, S.hut_face_upper s i y, T.hut_face_upper s i y]
    · intro s i y
      simp [wt, S.hut_face_lower s i y, T.hut_face_lower s i y]

  have hzero := wave_zero_of_zero_data3D w wt wgrad wtt wgradt wDut wDgrad wlap I Mw hW
    (by intro x; simp [w, hinit x])
    (by intro x; simp [wt, hvel x])
    (by intro x i; simp [wgrad, hgrad0 x i])
  intro t x hx
  have h := hzero t x hx
  simpa [w] using sub_eq_zero.mp h

end GeneralRelativity
