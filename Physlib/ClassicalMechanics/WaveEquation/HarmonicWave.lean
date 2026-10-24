/-
Copyright (c) 2025 Zhi Kai Pong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Philippe Kevorkian, Zhi Kai Pong
-/
module

public import Physlib.ClassicalMechanics.WaveEquation.Basic
/-!

# Harmonic Wave

Time-harmonic waves.

The wave equation is invariant under linear isometries of space, and a single plane wave can be
rotated so that it travels along `basis 2`.

Note TODO `EGU3E` may require considerable effort to be made rigorous and may heavily depend on
the status of Fourier theory in Mathlib.

-/

@[expose] public section

namespace ClassicalMechanics
open Space

/-- The wavevector which indicates a direction and has magnitude `2π/λ`. -/
abbrev WaveVector (d : ℕ := 3) := EuclideanSpace ℝ (Fin d)

/-- Direction of a wavevector. -/
noncomputable def WaveVector.toDirection {d : ℕ} (k : WaveVector d) (h : k ≠ 0) :
    Direction d where
  unit := (‖k‖⁻¹) • basis.repr.symm (k)
  norm := by
    simp [norm_smul]
    field_simp

/-- General form of time-harmonic wave in terms of angular frequency `ω` and wave vector `k`. -/
noncomputable def harmonicWave (a g : ℝ → Space d → ℝ) (ω : WaveVector d → ℝ) (k : WaveVector d) :
    Time → Space d → ℝ :=
    fun t r => a (ω k) r * Real.cos (ω k * t - g (ω k) r)

/-!

## Rotations and the direction of propagation

-/

/-- At `(t, x)`, `f` composed with a linear isometry `R` satisfies the wave equation if and only
  if `f` satisfies it at `(t, R x)`. -/
lemma waveEquation_comp_linearIsometryEquiv_iff {d : ℕ}
    (f : Time → Space d → EuclideanSpace ℝ (Fin d)) (R : Space d ≃ₗᵢ[ℝ] Space d) (t : Time)
    (x : Space d) (c : ℝ) (hf : ∀ i, DifferentiableAt ℝ (fderiv ℝ (fun y => f t y i)) (R x)) :
    WaveEquation (fun t y => f t (R y)) t x c ↔ WaveEquation f t (R x) c := by
  rw [WaveEquation, WaveEquation, laplacianVec_comp_linearIsometryEquiv (f t) R x hf]

/-- For `f` twice continuously differentiable in space, `f` composed with a linear isometry `R`
  satisfies the wave equation everywhere if and only if `f` does. -/
lemma forall_waveEquation_comp_linearIsometryEquiv_iff {d : ℕ}
    (f : Time → Space d → EuclideanSpace ℝ (Fin d)) (R : Space d ≃ₗᵢ[ℝ] Space d) (c : ℝ)
    (hf : ∀ t, ContDiff ℝ 2 (f t)) :
    (∀ t x, WaveEquation (fun t y => f t (R y)) t x c) ↔ ∀ t x, WaveEquation f t x c := by
  have hd (t : Time) (i : Fin d) (z : Space d) :
      DifferentiableAt ℝ (fderiv ℝ (fun y => f t y i)) z :=
    ((contDiff_euclidean.mp (hf t) i).fderiv_right (m := 1) le_rfl).differentiable one_ne_zero z
  refine ⟨fun h t z => ?_, fun h t x =>
    (waveEquation_comp_linearIsometryEquiv_iff f R t x c (hd t · _)).mpr (h t (R x))⟩
  simpa using (waveEquation_comp_linearIsometryEquiv_iff f R t (R.symm z) c (hd t · _)).mp
    (h t (R.symm z))

/-- If `R` sends the direction `s` to `e`, the plane wave in direction `s` is the plane wave in
  direction `e` composed with `R`. -/
lemma planeWave_eq_comp_linearIsometryEquiv {d : ℕ} (f₀ : ℝ → EuclideanSpace ℝ (Fin d)) (c : ℝ)
    {s e : Direction d} (R : Space d ≃ₗᵢ[ℝ] Space d) (h : R s.unit = e.unit) :
    planeWave f₀ c s = fun t x => planeWave f₀ c e t (R x) := by
  funext t x
  rw [planeWave_eq, planeWave_eq, ← h, LinearIsometryEquiv.inner_map_map]

/-- Every direction in three-dimensional space is sent to `basis 2` by a rotation. -/
lemma exists_rotation_apply_unit_eq_basis_two (s : Direction) :
    ∃ R : Space ≃ₗᵢ[ℝ] Space, LinearMap.det R.toLinearMap = 1 ∧ R s.unit = basis 2 := by
  by_cases hs : s.unit = basis 2
  · exact ⟨LinearIsometryEquiv.refl ℝ Space, by simp, by simp [hs]⟩
  -- Two reflections: one exchanging `s.unit` and `basis 2`, one fixing `basis 2`.
  have hv : s.unit - basis 2 ≠ 0 := sub_ne_zero.mpr hs
  have h0 : basis (d := 3) 0 ≠ 0 := (basis (d := 3)).orthonormal.ne_zero 0
  refine ⟨(ℝ ∙ (s.unit - basis 2))ᗮ.reflection.trans (ℝ ∙ basis (d := 3) 0)ᗮ.reflection, ?_, ?_⟩
  · rw [LinearIsometryEquiv.toLinearEquiv_trans, LinearEquiv.coe_trans, LinearMap.det_comp,
      Submodule.det_reflection, Submodule.det_reflection, Submodule.orthogonal_orthogonal,
      Submodule.orthogonal_orthogonal, finrank_span_singleton hv, finrank_span_singleton h0]
    norm_num
  · rw [LinearIsometryEquiv.trans_apply,
      Submodule.reflection_sub (s.norm.trans ((basis (d := 3)).norm_eq_one 2).symm)]
    apply Submodule.reflection_mem_subspace_eq_self
    rw [Submodule.mem_orthogonal_singleton_iff_inner_right]
    exact basis.orthonormal.2 (show (0 : Fin 3) ≠ 2 by decide)

open InnerProductSpace
set_option linter.unusedVariables false in
/-- Transverse monochromatic time-harmonic plane wave where the direction of propagation
  is taken to be `EuclideanSpace.single 2 1`. `f₀x` and `f₀y` are the respective amplitudes,
  `ω` is the angular frequency, `δx` and `δy` are the respective phases for `fx` and `fy`. -/
@[nolint unusedArguments]
noncomputable def transverseHarmonicPlaneWave (k : WaveVector) (f₀x f₀y ω δx δy : ℝ)
    (hk : k = EuclideanSpace.single 2 (ω/c)) :
    Time → Space → EuclideanSpace ℝ (Fin 3) :=
    let fx := harmonicWave (fun _ _ => f₀x) (fun _ r => ⟪k, basis.repr r⟫_ℝ - δx) (fun _ => ω) k
    let fy := harmonicWave (fun _ _ => f₀y) (fun _ r => ⟪k, basis.repr r⟫_ℝ - δy) (fun _ => ω) k
    fun t r => fx t r • EuclideanSpace.single 0 1 + fy t r • EuclideanSpace.single 1 1

/-- The transverse harmonic planewave representation is equivalent to the general planewave
  expression with `‖k‖ = ω/c`. -/
lemma transverseHarmonicPlaneWave_eq_planeWave {c : ℝ} {k : WaveVector} {f₀x f₀y ω δx δy : ℝ}
    (hc_ge_zero : 0 < c) (hω_ge_zero : 0 < ω) (hk : k = EuclideanSpace.single 2 (ω/c)) :
    (transverseHarmonicPlaneWave k f₀x f₀y ω δx δy hk) = planeWave
    (fun p => (f₀x * Real.cos (-(ω/c)*p + δx)) • (EuclideanSpace.single 0 1) +
    (f₀y * Real.cos (-(ω/c)*p + δy)) • (EuclideanSpace.single 1 1)) c
    (WaveVector.toDirection k (by rw [hk]; simp [ne_of_gt, hc_ge_zero, hω_ge_zero])) := by
  unfold transverseHarmonicPlaneWave planeWave
  ext1 t
  ext1 r
  rw [harmonicWave, harmonicWave, WaveVector.toDirection]
  simp only [Fin.isValue, neg_mul]
  have normk: ‖k‖ = ω/c := by
    rw [hk]
    simp [← abs_div, hc_ge_zero, hω_ge_zero, le_of_lt]
  rw [normk]
  rw [mul_sub, inner_smul_right, real_inner_comm, ← mul_assoc]
  ring_nf
  simp [ne_of_gt, hc_ge_zero, hω_ge_zero, mul_comm ω, mul_assoc, basis_repr_inner_eq]

TODO "Show that any disturbance (subject to certain conditions) can be expressed
    as a superposition of harmonic plane waves via Fourier integral."

end ClassicalMechanics
