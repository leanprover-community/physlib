/-
Copyright (c) 2026 Alex Vergara Gil.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Vergara Gil
-/

module

public import PhyslibAlpha.Relativity.General.InitialData.ReducedWave3D
public import PhyslibAlpha.Relativity.General.Linearized.LinearizedWaveGauge
public import PhyslibAlpha.Relativity.General.InitialData.CauchyInterfaces
public import PhyslibAlpha.Cosmology.FLRW.Basic
public import PhyslibAlpha.Relativity.Metrics.CoordinateMetric
public import Mathlib.Analysis.ODE.ExistUnique
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring

/-!

# Reduced Cauchy problem in wave gauge and symmetry-reduced Einstein evolution

## i. Overview

This module instantiates `ReducedLocalExistenceCertificate` in two concrete
settings, together with directional 3D wave existence and the nonlinear harmonic
gauge condition:

1. **Directional 3D plane waves and superposition**: `directionalWave3D k f g`
   solves the 3D wave equation `∂ₜ² u = Δu` for every unit wavevector
   `∑ i, (k i)² = 1` with arbitrary `C²` Cauchy data `(f, g)` along `k · x`,
   and the coordinate Laplacian is linear (`spatialLaplacian3D_add`).
2. **Nonlinear harmonic (wave) gauge condition**: `harmonicGaugeCond g ginv x μ`
   (`g^{αβ} Γ^μ_{αβ} = 0`), with `minkowski_harmonicGauge` for Minkowski.
3. **Linearized 3D wave-gauge reduced Cauchy problem on a box**:
   `linearizedBox_reducedLocalExistence` inhabits
   `ReducedLocalExistenceCertificate (linearizedBoxReducedProblem I)` using
   `WaveUniqueness3D.wave_zero_of_zero_data3D` and `Linearized.ttWave_waveGauge`,
   accompanied by the nontrivial `ttWave_reduced_solution`.
4. **Nonlinear 4D flat FLRW reduced Einstein Cauchy problem**:
   `flrw_reducedLocalExistence` inhabits
   `ReducedLocalExistenceCertificate (flrwReducedProblem Λ a₀ v₀ ha₀)` for the
   second-order Einstein–Friedmann evolution equation `2 a a'' + (a')² = Λ a²`
   via Mathlib's Picard–Lindelöf local existence (`ContDiffAt`) and
   uniqueness (`ODE_solution_unique_of_mem_Ioo`).

Scope boundary: this proves reduced local existence and uniqueness for the 3D
linear wave-gauge system on a box and for the nonlinear 4D FLRW reduced
Einstein ODE, not Choquet–Bruhat's full 1952 `H^s(ℝ³)` quasilinear symmetric
hyperbolic theorem without symmetry.

## ii. Key results

- `directionalWave3D_wave_equation`, `directionalWave3D_cauchy_data` : a
  directional 3D plane wave solves the wave equation and attains its Cauchy data.
- `spatialLaplacian3D_add` : the coordinate Laplacian is linear on sums.
- `harmonicGaugeCond`, `minkowski_harmonicGauge` : the nonlinear harmonic gauge
  condition and its Minkowski instance.
- `linearizedBox_reducedLocalExistence`, `ttWave_reduced_solution` : the
  certificate for the linearized 3D wave-gauge system, with a nontrivial
  transverse-traceless solution.
- `flrw_reducedLocalExistence` : the certificate for the nonlinear 4D flat
  FLRW reduced Einstein ODE.

## iii. Table of contents

- A. Directional 3D plane waves and superposition
- B. Nonlinear harmonic (wave) gauge condition
- C. Linearized 3D wave-gauge reduced Cauchy problem on a box
- D. Nonlinear 4D flat FLRW reduced Einstein Cauchy problem

## iv. References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., AMS, 2010, §2.4.
  [ref: Evans2010PDE]
* R. M. Wald, *General Relativity*, University of Chicago Press, 1984, Ch. 7.
  [ref: wald_1984_general_relativity]

-/

@[expose] public section

open MeasureTheory BoxIntegral Metric Set
open scoped Topology ContDiff NNReal

namespace GeneralRelativity

/-! ## A. Directional 3D plane waves and superposition -/

/-- The 3D Euclidean inner product `k · x = ∑ i, k i * x i`. -/
noncomputable def dot3 (k x : SpaceChart) : ℝ :=
  ∑ i : Fin 3, k i * x i

/-- A 3D d'Alembert plane wave propagating along an arbitrary wavevector `k`:
`u(t, x) = dAlembert f g t (k · x)`. -/
noncomputable def directionalWave3D (k : SpaceChart) (f g : ℝ → ℝ) (t : ℝ) (x : SpaceChart) : ℝ :=
  dAlembert f g t (dot3 k x)

private lemma hasDerivAt_dot3_update (k x : SpaceChart) (i : Fin 3) (s : ℝ) :
    HasDerivAt (fun u : ℝ => dot3 k (Function.update x i u)) (k i) s := by
  fin_cases i
  · change HasDerivAt (fun u : ℝ => dot3 k (Function.update x 0 u)) (k 0) s
    have hfun : (fun u : ℝ => dot3 k (Function.update x 0 u)) =
        fun u : ℝ => k 0 * u + (k 1 * x 1 + k 2 * x 2) := by
      funext u; simp [dot3, Fin.sum_univ_three]; ring
    rw [hfun]
    simpa using ((hasDerivAt_id s).const_mul (k 0)).add_const (k 1 * x 1 + k 2 * x 2)
  · change HasDerivAt (fun u : ℝ => dot3 k (Function.update x 1 u)) (k 1) s
    have hfun : (fun u : ℝ => dot3 k (Function.update x 1 u)) =
        fun u : ℝ => k 1 * u + (k 0 * x 0 + k 2 * x 2) := by
      funext u; simp [dot3, Fin.sum_univ_three]; ring
    rw [hfun]
    simpa using ((hasDerivAt_id s).const_mul (k 1)).add_const (k 0 * x 0 + k 2 * x 2)
  · change HasDerivAt (fun u : ℝ => dot3 k (Function.update x 2 u)) (k 2) s
    have hfun : (fun u : ℝ => dot3 k (Function.update x 2 u)) =
        fun u : ℝ => k 2 * u + (k 0 * x 0 + k 1 * x 1) := by
      funext u; simp [dot3, Fin.sum_univ_three]; ring
    rw [hfun]
    simpa using ((hasDerivAt_id s).const_mul (k 2)).add_const (k 0 * x 0 + k 1 * x 1)

private lemma coordDeriv_directionalWave3D
    (k : SpaceChart) (f g f' : ℝ → ℝ) (hf : ∀ y, HasDerivAt f (f' y) y)
    (hg : Continuous g) (t : ℝ) (x : SpaceChart) (i : Fin 3) :
    coordDeriv (directionalWave3D k f g t) i x =
      k i * ((f' (dot3 k x + t) + f' (dot3 k x - t)) / 2 +
        (g (dot3 k x + t) - g (dot3 k x - t)) / 2) := by
  unfold coordDeriv directionalWave3D
  have h1 := hasDerivAt_dAlembert_x f g f' hf hg t (dot3 k x)
  have h1' : HasDerivAt (dAlembert f g t)
      ((f' (dot3 k x + t) + f' (dot3 k x - t)) / 2 +
        (g (dot3 k x + t) - g (dot3 k x - t)) / 2)
      (dot3 k (Function.update x i (x i))) := by
    simpa [Function.update_eq_self] using h1
  have h2 := hasDerivAt_dot3_update k x i (x i)
  have hcomp := h1'.comp (x i) h2
  have heq : (fun s : ℝ => dAlembert f g t (dot3 k (Function.update x i s))) =
      (dAlembert f g t ∘ fun u : ℝ => dot3 k (Function.update x i u)) := rfl
  rw [heq, hcomp.deriv]
  ring

private lemma coordDeriv2_directionalWave3D
    (k : SpaceChart) (f g f' f'' g' : ℝ → ℝ)
    (hf : ∀ y, HasDerivAt f (f' y) y)
    (hf' : ∀ y, HasDerivAt f' (f'' y) y)
    (hg : ∀ y, HasDerivAt g (g' y) y)
    (hgc : Continuous g) (t : ℝ) (x : SpaceChart) (i : Fin 3) :
    coordDeriv2 (directionalWave3D k f g t) i x =
      k i ^ 2 * ((f'' (dot3 k x + t) + f'' (dot3 k x - t)) / 2 +
        (g' (dot3 k x + t) - g' (dot3 k x - t)) / 2) := by
  unfold coordDeriv2
  have hfun : (fun y : SpaceChart => coordDeriv (directionalWave3D k f g t) i y) =
      fun y : SpaceChart =>
        k i * ((f' (dot3 k y + t) + f' (dot3 k y - t)) / 2 +
          (g (dot3 k y + t) - g (dot3 k y - t)) / 2) := by
    funext y
    exact coordDeriv_directionalWave3D k f g f' hf hgc t y i
  rw [hfun]
  unfold coordDeriv
  have h1 := hasDerivAt_waveX f' g f'' g' hf' hg t (dot3 k x)
  have h1' : HasDerivAt
      (fun u : ℝ => (f' (u + t) + f' (u - t)) / 2 + (g (u + t) - g (u - t)) / 2)
      ((f'' (dot3 k x + t) + f'' (dot3 k x - t)) / 2 +
        (g' (dot3 k x + t) - g' (dot3 k x - t)) / 2)
      (dot3 k (Function.update x i (x i))) := by
    simpa [Function.update_eq_self] using h1
  have h2 := hasDerivAt_dot3_update k x i (x i)
  have hcomp := (h1'.comp (x i) h2).const_mul (k i)
  have heq : (fun s : ℝ =>
      k i * ((f' (dot3 k (Function.update x i s) + t) +
          f' (dot3 k (Function.update x i s) - t)) / 2 +
        (g (dot3 k (Function.update x i s) + t) -
          g (dot3 k (Function.update x i s) - t)) / 2)) =
      (fun y : ℝ => k i * ((fun u : ℝ => (f' (u + t) + f' (u - t)) / 2 +
        (g (u + t) - g (u - t)) / 2) ∘ fun u => dot3 k (Function.update x i u)) y) := rfl
  rw [heq, hcomp.deriv]
  ring

/-- For any unit wavevector `∑ i, (k i)² = 1`, `directionalWave3D k f g` solves
the 3D coordinate wave equation `∂ₜ² u = Δ u`. -/
lemma directionalWave3D_wave_equation
    (k : SpaceChart) (hk : (∑ i : Fin 3, k i ^ 2) = 1)
    (f g f' f'' g' : ℝ → ℝ)
    (hf : ∀ y, HasDerivAt f (f' y) y)
    (hf' : ∀ y, HasDerivAt f' (f'' y) y)
    (hg : ∀ y, HasDerivAt g (g' y) y)
    (hgc : Continuous g) (t : ℝ) (x : SpaceChart) :
    deriv (fun s : ℝ => deriv (fun s : ℝ => directionalWave3D k f g s x) s) t =
      spatialLaplacian3D (directionalWave3D k f g t) x := by
  have hlap : spatialLaplacian3D (directionalWave3D k f g t) x =
      (f'' (dot3 k x + t) + f'' (dot3 k x - t)) / 2 +
        (g' (dot3 k x + t) - g' (dot3 k x - t)) / 2 := by
    unfold spatialLaplacian3D
    have hsum :
        (∑ i : Fin 3, coordDeriv2 (directionalWave3D k f g t) i x) =
          (∑ i : Fin 3, k i ^ 2) *
            ((f'' (dot3 k x + t) + f'' (dot3 k x - t)) / 2 +
              (g' (dot3 k x + t) - g' (dot3 k x - t)) / 2) := by
      simp_rw [coordDeriv2_directionalWave3D k f g f' f'' g' hf hf' hg hgc t x,
        ← Finset.sum_mul]
    rw [hsum, hk, one_mul]
  rw [hlap]
  unfold directionalWave3D
  have htime : (fun s : ℝ => deriv (fun s : ℝ => dAlembert f g s (dot3 k x)) s) =
      fun s : ℝ =>
        (f' (dot3 k x + s) - f' (dot3 k x - s)) / 2 +
          (g (dot3 k x + s) + g (dot3 k x - s)) / 2 := by
    funext s
    exact (hasDerivAt_dAlembert_t f g f' hf hgc s (dot3 k x)).deriv
  rw [htime, (hasDerivAt_waveT f' g f'' g' hf' hg t (dot3 k x)).deriv]

/-- `directionalWave3D` attains the prescribed Cauchy data `(f (k · x), g (k · x))`. -/
lemma directionalWave3D_cauchy_data
    (k : SpaceChart) (f g f' : ℝ → ℝ) (hf : ∀ y, HasDerivAt f (f' y) y)
    (hg : Continuous g) (x : SpaceChart) :
    directionalWave3D k f g 0 x = f (dot3 k x) ∧
      HasDerivAt (fun t : ℝ => directionalWave3D k f g t x) (g (dot3 k x)) 0 :=
  ⟨by simp [directionalWave3D, dAlembert_zero],
    hasDerivAt_dAlembert_zero f g f' hf hg (dot3 k x)⟩

/-- Superposition of coordinate derivatives along axis `i`. -/
lemma coordDeriv_add (u v : SpaceChart → ℝ) (i : Fin 3) (x : SpaceChart)
    (hu : DifferentiableAt ℝ (fun s => u (Function.update x i s)) (x i))
    (hv : DifferentiableAt ℝ (fun s => v (Function.update x i s)) (x i)) :
    coordDeriv (fun y => u y + v y) i x = coordDeriv u i x + coordDeriv v i x :=
  deriv_add hu hv

/-- Superposition of the 3D coordinate Laplacian on sums of solutions. -/
lemma spatialLaplacian3D_add (u v : SpaceChart → ℝ) (x : SpaceChart)
    (hu : ∀ i : Fin 3, DifferentiableAt ℝ
      (fun s => coordDeriv u i (Function.update x i s)) (x i))
    (hv : ∀ i : Fin 3, DifferentiableAt ℝ
      (fun s => coordDeriv v i (Function.update x i s)) (x i))
    (h1u : ∀ i : Fin 3, ∀ᶠ y in 𝓝 x,
      DifferentiableAt ℝ (fun s => u (Function.update y i s)) (y i))
    (h1v : ∀ i : Fin 3, ∀ᶠ y in 𝓝 x,
      DifferentiableAt ℝ (fun s => v (Function.update y i s)) (y i)) :
    spatialLaplacian3D (fun y => u y + v y) x =
      spatialLaplacian3D u x + spatialLaplacian3D v x := by
  unfold spatialLaplacian3D
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  unfold coordDeriv2
  have hcont : Continuous (fun s : ℝ => Function.update x i s) := by
    rw [continuous_pi_iff]
    intro j
    by_cases hj : j = i
    · subst hj; simp only [Function.update_self]; exact continuous_id
    · simp only [Function.update, hj, ↓reduceDIte]; exact continuous_const
  have htend : Filter.Tendsto (fun s : ℝ => Function.update x i s) (𝓝 (x i)) (𝓝 x) := by
    convert hcont.continuousAt.tendsto using 1
    simp [Function.update_eq_self]
  have hev : (fun s : ℝ => coordDeriv (fun y => u y + v y) i (Function.update x i s))
      =ᶠ[𝓝 (x i)] fun s : ℝ =>
        coordDeriv u i (Function.update x i s) +
          coordDeriv v i (Function.update x i s) := by
    filter_upwards [(h1u i).filter_mono htend, (h1v i).filter_mono htend] with s hsu hsv
    exact coordDeriv_add u v i (Function.update x i s) hsu hsv
  rw [coordDeriv, hev.deriv_eq, ((hu i).hasDerivAt.fun_add (hv i).hasDerivAt).deriv]
  rfl

/-! ## B. Nonlinear harmonic (wave) gauge condition -/

/-- Nonlinear harmonic (wave) gauge condition `Γ^μ := g^{αβ} Γ^μ_{αβ} = 0` at a
spacetime chart point `x`. -/
noncomputable def harmonicGaugeCond (g ginv : (Fin 4 → ℝ) → Tensor2 4)
    (x : Fin 4 → ℝ) (μ : Fin 4) : Prop :=
  (∑ α : Fin 4, ∑ β : Fin 4,
    ginv x α β * CoordinateCurvature.christoffel g ginv x μ α β) = 0

/-- Minkowski spacetime satisfies the nonlinear harmonic gauge condition
identically. -/
lemma minkowski_harmonicGauge (x : Fin 4 → ℝ) (μ : Fin 4) :
    harmonicGaugeCond (fun _ => minkowski.g) (fun _ => minkowski.ginv) x μ := by
  unfold harmonicGaugeCond
  have hG : ∀ α β, CoordinateCurvature.christoffel (fun _ => minkowski.g) (fun _ => minkowski.ginv)
      x μ α β = 0 := by
    intro α β
    simp [CoordinateCurvature.christoffel, CoordinateCurvature.coordDeriv_const]
  simp [hG]

/-! ## C. Linearized 3D wave-gauge reduced Cauchy problem on a box -/

/-- A scalar wave-gauge field restricted to `ℝ × Box.Icc I`, paired with its
initial velocity and spatial gradient so Cauchy data uniqueness determines the
entire value uniquely via `WaveUniqueness3D`. -/
@[ext]
structure LinearizedBoxField (I : BoxIntegral.Box (Fin 3)) where
  /-- The spacetime field value at a time and a spatial point in `I`. -/
  val : ℝ → {x : SpaceChart // x ∈ BoxIntegral.Box.Icc I} → ℝ
  /-- The initial velocity of the field. -/
  vel0 : SpaceChart → ℝ
  /-- The initial spatial gradient of the field. -/
  grad0 : SpaceChart → SpaceChart

/-- The canonical zero wave-gauge field on `I`. -/
def LinearizedBoxField.zero (I : BoxIntegral.Box (Fin 3)) : LinearizedBoxField I where
  val := fun _ _ => 0
  vel0 := fun _ => 0
  grad0 := fun _ => fun _ => 0

/-- Reduced Cauchy problem for a linearized wave-gauge scalar mode on the closed
box `I` with homogeneous Dirichlet boundary data and initial data `(0, 0, 0)`. -/
noncomputable def linearizedBoxReducedProblem (I : BoxIntegral.Box (Fin 3)) :
    ReducedCauchyProblem minkowskiChart where
  data := minkowskiChartInitialData
  Solution := LinearizedBoxField I
  IsSolution := fun F =>
    ∃ (u ut : ℝ → SpaceChart → ℝ) (grad : ℝ → SpaceChart → SpaceChart)
      (utt : ℝ → SpaceChart → ℝ) (gradt : ℝ → SpaceChart → SpaceChart)
      (Dut : ℝ → SpaceChart → SpaceChart →L[ℝ] ℝ)
      (Dgrad : ℝ → SpaceChart → SpaceChart →L[ℝ] SpaceChart)
      (lap : ℝ → SpaceChart → ℝ) (M : ℝ),
      WaveSolution3D u ut grad utt gradt Dut Dgrad lap I M ∧
      (∀ t (x : SpaceChart) (hx : x ∈ BoxIntegral.Box.Icc I), F.val t ⟨x, hx⟩ = u t x) ∧
      (∀ x, x ∉ BoxIntegral.Box.Icc I → u 0 x = 0) ∧
      ut 0 = F.vel0 ∧
      grad 0 = F.grad0
  HasCauchyData := fun F =>
    (∀ (x : SpaceChart) (hx : x ∈ BoxIntegral.Box.Icc I), F.val 0 ⟨x, hx⟩ = 0) ∧
    F.vel0 = 0 ∧
    F.grad0 = 0
  IsWaveGauge := fun F =>
    ∃ P : Linearized.MetricPerturbation,
      (∀ y, Linearized.WaveGaugePerturbation P y) ∧
      (∀ t (x : SpaceChart) (hx : x ∈ BoxIntegral.Box.Icc I),
        F.val t ⟨x, hx⟩ = P.h ![t, x 0, x 1, x 2] 1 1)

private lemma zero_waveSolution3D (I : BoxIntegral.Box (Fin 3)) :
    WaveSolution3D (fun _ _ => 0) (fun _ _ => 0) (fun _ _ => 0)
      (fun _ _ => 0) (fun _ _ => 0) (fun _ _ => 0) (fun _ _ => 0)
      (fun _ _ => 0) I 0 := by
  refine {
    hu_t := fun s x => hasDerivAt_const s (0 : ℝ)
    hu_face_upper := fun _ _ _ => rfl
    hu_face_lower := fun _ _ _ => rfl
    hut := fun s x => hasDerivAt_const s (0 : ℝ)
    hgrad := fun s x => hasDerivAt_const s (0 : SpaceChart)
    hut_cont := continuous_const
    hgrad_cont := continuous_const
    hutt_cont := continuous_const
    hgradt_cont := continuous_const
    hbound := fun s x => by
      simp [waveEnergy3DDerivIntegrand]
    hut_spatial := fun t x => hasFDerivAt_const (0 : ℝ) x
    hgrad_spatial := fun t x => hasFDerivAt_const (0 : SpaceChart) x
    hlap := fun _ _ => by simp
    hgradut := fun _ _ _ => by simp
    hwave := fun _ _ => rfl
    hdiv_int := fun s => by
      have hfn : (fun x => ∑ i : Fin 3,
          waveFlux3DDeriv (fun _ _ => 0) (fun _ _ => 0)
            (fun _ _ => 0) (fun _ _ => 0) s x (Pi.single i 1) i) = fun _ => (0 : ℝ) := by
        funext x; simp [waveFlux3DDeriv]
      rw [hfn]
      exact integrableOn_zero
    hut_face_upper := fun _ _ _ => rfl
    hut_face_lower := fun _ _ _ => rfl }

private lemma eq_zero_of_linearizedBoxSol (I : BoxIntegral.Box (Fin 3))
    (F : LinearizedBoxField I)
    (hsol : (linearizedBoxReducedProblem I).IsSolution F)
    (hdata : (linearizedBoxReducedProblem I).HasCauchyData F) :
    F = LinearizedBoxField.zero I := by
  rcases hsol with ⟨u, ut, grad, utt, gradt, Dut, Dgrad, lap, M, hS, hval, hout, hvel, hgrad⟩
  rcases hdata with ⟨hv0, hvel0, hgrad0⟩
  have hinit_all : ∀ x : SpaceChart, u 0 x = 0 := by
    intro x
    by_cases hx : x ∈ BoxIntegral.Box.Icc I
    · rw [← hval 0 x hx, hv0 x hx]
    · exact hout x hx
  have hvel_all : ∀ x : SpaceChart, ut 0 x = 0 := by
    intro x
    have h := congrFun hvel x
    rw [h, hvel0]
    rfl
  have hgrad_all : ∀ (x : SpaceChart) (i : Fin 3), grad 0 x i = 0 := by
    intro x i
    have h := congrFun (congrFun hgrad x) i
    rw [h, hgrad0]
    rfl
  have hzero := wave_zero_of_zero_data3D u ut grad utt gradt Dut Dgrad lap I M hS
    hinit_all hvel_all hgrad_all
  ext t x
  · exact (hval t x.1 x.2).trans (hzero t x.1 x.2)
  · simp [hvel0, LinearizedBoxField.zero]
  · simp [hgrad0, LinearizedBoxField.zero]

/-- **Certificate for the linearized 3D wave-gauge system**: inhabits
`ReducedLocalExistenceCertificate` on any closed 3D spatial box `I`, using
`Linearized.ttWave_waveGauge` and `WaveUniqueness3D.wave_zero_of_zero_data3D`. -/
lemma linearizedBox_reducedLocalExistence (I : BoxIntegral.Box (Fin 3)) :
    ReducedLocalExistenceCertificate (linearizedBoxReducedProblem I) where
  local_existence := by
    refine ⟨LinearizedBoxField.zero I, ?_, ?_, ?_⟩
    · refine ⟨_, _, _, _, _, _, _, _, 0, zero_waveSolution3D I,
        (fun _ _ _ => rfl), (fun _ _ => rfl), rfl, rfl⟩
    · exact ⟨fun _ _ => rfl, rfl, rfl⟩
    · refine ⟨Linearized.ttWave 0 0 (fun _ => 0), ?_, ?_⟩
      · intro y
        exact Linearized.ttWave_waveGauge 0 0 (fun _ => 0) contDiff_const y
      · intro t x hx
        simp [LinearizedBoxField.zero, Linearized.ttWave]
  local_uniqueness := fun u v hu hv hu0 hv0 => by
    rw [eq_zero_of_linearizedBoxSol I u hu hu0, eq_zero_of_linearizedBoxSol I v hv hv0]

/-- Nontrivial gravitational-wave reduced solution: the transverse-traceless plane
wave `ttWave hPlus hCross f` (for any `C²` waveform `f`) solves both the 4D
wave-gauge linearized vacuum equations (`G^{(1)} = 0`, Lorenz gauge) and the 3D
directional wave equation along `e₃`. -/
lemma ttWave_reduced_solution (hPlus hCross : ℝ) (f f' f'' : ℝ → ℝ)
    (hf : ContDiff ℝ 2 f) (hf1 : ∀ z, HasDerivAt f (f' z) z)
    (hf2 : ∀ z, HasDerivAt f' (f'' z) z) :
    (∀ y, Linearized.WaveGaugePerturbation (Linearized.ttWave hPlus hCross f) y) ∧
      (∀ y i j, Linearized.linearizedEinstein (Linearized.ttWave hPlus hCross f) y i j = 0) ∧
      (∀ t (x : SpaceChart),
        let f0 : ℝ → ℝ := fun z => hPlus * f (-z)
        let g0 : ℝ → ℝ := fun z => hPlus * f' (-z)
        deriv (fun s : ℝ => deriv (fun s : ℝ =>
            directionalWave3D ![0, 0, 1] f0 g0 s x) s) t =
          spatialLaplacian3D
            (directionalWave3D ![0, 0, 1] f0 g0 t) x ∧
          directionalWave3D ![0, 0, 1] f0 g0 t x =
            (Linearized.ttWave hPlus hCross f).h ![t, x 0, x 1, x 2] 1 1) := by
  refine ⟨fun y => Linearized.ttWave_waveGauge hPlus hCross f hf y,
    fun y i j => Linearized.ttWave_linearizedEinstein_zero hPlus hCross f hf y i j,
    fun t x => ?_⟩
  let f0 : ℝ → ℝ := fun z => hPlus * f (-z)
  let f0' : ℝ → ℝ := fun z => -(hPlus * f' (-z))
  let f0'' : ℝ → ℝ := fun z => hPlus * f'' (-z)
  let g0 : ℝ → ℝ := fun z => hPlus * f' (-z)
  let g0' : ℝ → ℝ := fun z => -(hPlus * f'' (-z))
  have hf0 : ∀ z, HasDerivAt f0 (f0' z) z := fun z => by
    have h := (hf1 (-z)).comp z (hasDerivAt_neg z)
    simpa [f0, f0'] using h.const_mul hPlus
  have hf0' : ∀ z, HasDerivAt f0' (f0'' z) z := fun z => by
    have h := (hf2 (-z)).comp z (hasDerivAt_neg z)
    have hmul : HasDerivAt (fun y : ℝ => -(hPlus * f' (-y))) (-(hPlus * (f'' (-z) * (-1)))) z :=
      (h.const_mul hPlus).fun_neg
    convert hmul using 1
    ring
  have hg0 : ∀ z, HasDerivAt g0 (g0' z) z := fun z => by
    have h := (hf2 (-z)).comp z (hasDerivAt_neg z)
    simpa [g0, g0'] using h.const_mul hPlus
  have hg0c : Continuous g0 := continuous_iff_continuousAt.mpr fun z => (hg0 z).continuousAt
  have hk : (∑ i : Fin 3, (![(0 : ℝ), 0, 1] i) ^ 2) = 1 := by
    simp [Fin.sum_univ_three]
  constructor
  · exact directionalWave3D_wave_equation ![0, 0, 1] hk f0 g0 f0' f0'' g0' hf0 hf0' hg0 hg0c t x
  · unfold directionalWave3D dAlembert
    have hdot : dot3 ![0, 0, 1] x = x 2 := by
      simp [dot3, Fin.sum_univ_three]
    rw [hdot]
    have hftc : (∫ s in (x 2 - t)..(x 2 + t), g0 s) =
        f0 (x 2 - t) - f0 (x 2 + t) := by
      have hderiv : ∀ s ∈ uIcc (x 2 - t) (x 2 + t), HasDerivAt (fun r => -f0 r) (g0 s) s := by
        intro s _
        have hneg : HasDerivAt (fun r => -f0 r) (-f0' s) s := (hf0 s).fun_neg
        convert hneg using 1
        simp [f0', g0]
      have hint : IntervalIntegrable g0 volume (x 2 - t) (x 2 + t) :=
        hg0c.intervalIntegrable _ _
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
      ring
    rw [hftc]
    have hsub : -(x 2 - t) = ![t, x 0, x 1, x 2] 0 - ![t, x 0, x 1, x 2] 3 := by
      simp [Matrix.cons_val_zero, Matrix.cons_val]
    have hlhs : ((fun z : ℝ => hPlus * f (-z)) (x 2 + t) +
          (fun z : ℝ => hPlus * f (-z)) (x 2 - t)) / 2 +
        1 / 2 * (f0 (x 2 - t) - f0 (x 2 + t)) = hPlus * f (-(x 2 - t)) := by
      simp only [f0]
      ring
    rw [hlhs, hsub]
    simp [Linearized.ttWave]

/-! ## D. Nonlinear 4D flat FLRW reduced Einstein Cauchy problem -/

/-- Autonomous first-order ODE vector field on `ℝ × ℝ` equivalent to the
reduced 4D flat FLRW Einstein evolution equation
`2 a a'' + (a')² = Λ a²` (`G_{11} + Λ g_{11} = 0`):
`(a, v) ↦ (v, (Λ a² - v²) / (2 a))`. -/
noncomputable def flrwField (Λ : ℝ) (p : ℝ × ℝ) : ℝ × ℝ :=
  (p.2, (Λ * p.1 ^ 2 - p.2 ^ 2) / (2 * p.1))

lemma contDiffAt_flrwField (Λ a₀ v₀ : ℝ) (ha₀ : a₀ ≠ 0) :
    ContDiffAt ℝ 1 (flrwField Λ) (a₀, v₀) := by
  have h1 : ContDiffAt ℝ 1 (fun p : ℝ × ℝ => p.2) (a₀, v₀) := contDiffAt_snd
  have hnum : ContDiffAt ℝ 1 (fun p : ℝ × ℝ => Λ * p.1 ^ 2 - p.2 ^ 2) (a₀, v₀) :=
    (contDiffAt_const.mul (contDiffAt_fst.pow 2)).sub (contDiffAt_snd.pow 2)
  have hden : ContDiffAt ℝ 1 (fun p : ℝ × ℝ => 2 * p.1) (a₀, v₀) :=
    contDiffAt_const.mul contDiffAt_fst
  have hdiv : ContDiffAt ℝ 1
      (fun p : ℝ × ℝ => (Λ * p.1 ^ 2 - p.2 ^ 2) / (2 * p.1)) (a₀, v₀) :=
    hnum.div hden (mul_ne_zero two_ne_zero ha₀)
  exact h1.prodMk hdiv

/-- Elementary explicit Lipschitz constant for `flrwField Λ` on
`closedBall (a₀, v₀) (|a₀| / 2)`. -/
lemma flrwField_lipschitzOn (Λ a₀ v₀ : ℝ) (ha₀ : a₀ ≠ 0) :
    ∃ K : ℝ≥0, LipschitzOnWith K (flrwField Λ) (closedBall (a₀, v₀) (|a₀| / 2)) := by
  let L0 : ℝ := 1 +
    (|Λ| * (3 * |a₀| / 2) ^ 2 + (|v₀| + |a₀| / 2) ^ 2 +
      2 * (3 * |a₀| / 2) * (|v₀| + |a₀| / 2)) / (|a₀| ^ 2 / 2)
  have hL0_nn : 0 ≤ L0 := by
    dsimp [L0]
    positivity
  let K : ℝ≥0 := ⟨L0, hL0_nn⟩
  refine ⟨K, ?_⟩
  rw [lipschitzOnWith_iff_dist_le_mul]
  intro p hp q hq
  rw [mem_closedBall, dist_eq_norm, Prod.norm_def] at hp hq
  have hp1_sub : |p.1 - a₀| ≤ |a₀| / 2 := le_trans (le_max_left _ _) hp
  have hp2_sub : |p.2 - v₀| ≤ |a₀| / 2 := le_trans (le_max_right _ _) hp
  have hq1_sub : |q.1 - a₀| ≤ |a₀| / 2 := le_trans (le_max_left _ _) hq
  have hq2_sub : |q.2 - v₀| ≤ |a₀| / 2 := le_trans (le_max_right _ _) hq
  have ha_pos : 0 < |a₀| := abs_pos.mpr ha₀
  have hp1_lb : |a₀| / 2 ≤ |p.1| := by
    have := abs_sub_abs_le_abs_sub a₀ p.1
    rw [abs_sub_comm a₀ p.1] at this
    linarith
  have hq1_lb : |a₀| / 2 ≤ |q.1| := by
    have := abs_sub_abs_le_abs_sub a₀ q.1
    rw [abs_sub_comm a₀ q.1] at this
    linarith
  have hp1_ne : p.1 ≠ 0 := abs_pos.mp (by linarith)
  have hq1_ne : q.1 ≠ 0 := abs_pos.mp (by linarith)
  have hp1_ub : |p.1| ≤ 3 * |a₀| / 2 := by
    have := abs_add_le (p.1 - a₀) a₀
    simpa using le_trans this (by linarith)
  have hq1_ub : |q.1| ≤ 3 * |a₀| / 2 := by
    have := abs_add_le (q.1 - a₀) a₀
    simpa using le_trans this (by linarith)
  have hp2_ub : |p.2| ≤ |v₀| + |a₀| / 2 := by
    have := abs_add_le (p.2 - v₀) v₀
    simpa using le_trans this (by linarith)
  have hq2_ub : |q.2| ≤ |v₀| + |a₀| / 2 := by
    have := abs_add_le (q.2 - v₀) v₀
    simpa using le_trans this (by linarith)
  have hden_lb : |a₀| ^ 2 / 2 ≤ |2 * p.1 * q.1| := by
    rw [abs_mul, abs_mul, abs_of_pos (zero_lt_two (α := ℝ))]
    nlinarith [abs_nonneg p.1, abs_nonneg q.1]
  have hden_pos : 0 < |a₀| ^ 2 / 2 := by positivity
  have hd_pos : 0 < |2 * p.1 * q.1| := lt_of_lt_of_le hden_pos hden_lb
  have hdiff2 : (Λ * p.1 ^ 2 - p.2 ^ 2) / (2 * p.1) - (Λ * q.1 ^ 2 - q.2 ^ 2) / (2 * q.1) =
      (Λ * p.1 * q.1 * (p.1 - q.1) + p.2 ^ 2 * (p.1 - q.1) -
        p.1 * (p.2 + q.2) * (p.2 - q.2)) / (2 * p.1 * q.1) := by
    field_simp [hp1_ne, hq1_ne]
    ring
  let d : ℝ := dist p q
  have hd1 : |p.1 - q.1| ≤ d := by
    simp [d, dist_eq_norm, Prod.norm_def, Real.norm_eq_abs]
  have hd2 : |p.2 - q.2| ≤ d := by
    simp [d, dist_eq_norm, Prod.norm_def, Real.norm_eq_abs]
  have hnum_le : |Λ * p.1 * q.1 * (p.1 - q.1) + p.2 ^ 2 * (p.1 - q.1) -
      p.1 * (p.2 + q.2) * (p.2 - q.2)| ≤
      (|Λ| * (3 * |a₀| / 2) ^ 2 + (|v₀| + |a₀| / 2) ^ 2 +
        2 * (3 * |a₀| / 2) * (|v₀| + |a₀| / 2)) * d := by
    have htri1 : |Λ * p.1 * q.1 * (p.1 - q.1) + p.2 ^ 2 * (p.1 - q.1) -
        p.1 * (p.2 + q.2) * (p.2 - q.2)| ≤
        |Λ * p.1 * q.1 * (p.1 - q.1)| + |p.2 ^ 2 * (p.1 - q.1)| +
          |p.1 * (p.2 + q.2) * (p.2 - q.2)| := by
      calc |Λ * p.1 * q.1 * (p.1 - q.1) + p.2 ^ 2 * (p.1 - q.1) -
            p.1 * (p.2 + q.2) * (p.2 - q.2)|
          ≤ |Λ * p.1 * q.1 * (p.1 - q.1) + p.2 ^ 2 * (p.1 - q.1)| +
            |p.1 * (p.2 + q.2) * (p.2 - q.2)| := abs_sub _ _
        _ ≤ _ := add_le_add (abs_add_le _ _) le_rfl
    have ht1 : |Λ * p.1 * q.1 * (p.1 - q.1)| ≤ |Λ| * (3 * |a₀| / 2) ^ 2 * d := by
      rw [abs_mul, abs_mul, abs_mul]
      have hpq : |p.1| * |q.1| ≤ (3 * |a₀| / 2) ^ 2 := by
        nlinarith [abs_nonneg p.1, abs_nonneg q.1]
      have h3 : |Λ| * |p.1| * |q.1| ≤ |Λ| * (3 * |a₀| / 2) ^ 2 := by
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_left hpq (abs_nonneg Λ)
      exact mul_le_mul h3 hd1 (abs_nonneg _) (by positivity)
    have ht2 : |p.2 ^ 2 * (p.1 - q.1)| ≤ (|v₀| + |a₀| / 2) ^ 2 * d := by
      rw [abs_mul, abs_pow]
      have hpq : |p.2| ^ 2 ≤ (|v₀| + |a₀| / 2) ^ 2 := by
        nlinarith [abs_nonneg p.2]
      exact mul_le_mul hpq hd1 (abs_nonneg _) (by positivity)
    have ht3 : |p.1 * (p.2 + q.2) * (p.2 - q.2)| ≤
        2 * (3 * |a₀| / 2) * (|v₀| + |a₀| / 2) * d := by
      rw [abs_mul, abs_mul]
      have hsum : |p.2 + q.2| ≤ 2 * (|v₀| + |a₀| / 2) :=
        le_trans (abs_add_le p.2 q.2) (by linarith)
      have hprod : |p.1| * |p.2 + q.2| ≤ 2 * (3 * |a₀| / 2) * (|v₀| + |a₀| / 2) := by
        have := mul_le_mul hp1_ub hsum (abs_nonneg _) (by positivity)
        linarith
      exact mul_le_mul hprod hd2 (abs_nonneg _) (by positivity)
    linarith
  have hcomp2 : |(flrwField Λ p).2 - (flrwField Λ q).2| ≤ L0 * d := by
    simp only [flrwField]
    rw [hdiff2, abs_div]
    have hstep1 : |Λ * p.1 * q.1 * (p.1 - q.1) + p.2 ^ 2 * (p.1 - q.1) -
          p.1 * (p.2 + q.2) * (p.2 - q.2)| / |2 * p.1 * q.1| ≤
        (|Λ| * (3 * |a₀| / 2) ^ 2 + (|v₀| + |a₀| / 2) ^ 2 +
          2 * (3 * |a₀| / 2) * (|v₀| + |a₀| / 2)) * d / (|a₀| ^ 2 / 2) :=
      div_le_div₀ (by positivity) hnum_le hden_pos hden_lb
    have hstep2 : (|Λ| * (3 * |a₀| / 2) ^ 2 + (|v₀| + |a₀| / 2) ^ 2 +
          2 * (3 * |a₀| / 2) * (|v₀| + |a₀| / 2)) * d / (|a₀| ^ 2 / 2) ≤ L0 * d := by
      have heq : L0 * d = d + ((|Λ| * (3 * |a₀| / 2) ^ 2 + (|v₀| + |a₀| / 2) ^ 2 +
          2 * (3 * |a₀| / 2) * (|v₀| + |a₀| / 2)) * d / (|a₀| ^ 2 / 2)) := by
        dsimp [L0]; ring
      rw [heq]
      linarith [dist_nonneg (x := p) (y := q)]
    exact le_trans hstep1 hstep2
  have hcomp1 : |(flrwField Λ p).1 - (flrwField Λ q).1| ≤ L0 * d := by
    simp only [flrwField]
    have hadd_nn : 0 ≤ (|Λ| * (3 * |a₀| / 2) ^ 2 + (|v₀| + |a₀| / 2) ^ 2 +
        2 * (3 * |a₀| / 2) * (|v₀| + |a₀| / 2)) / (|a₀| ^ 2 / 2) := by
      positivity
    have h1 : 1 ≤ L0 := by
      dsimp [L0]
      linarith
    exact le_trans hd2 (by nlinarith [dist_nonneg (x := p) (y := q)])
  rw [dist_eq_norm, Prod.norm_def]
  simp only [Real.norm_eq_abs]
  exact max_le hcomp1 hcomp2

/-- Local existence for the nonlinear 4D flat FLRW reduced ODE inside a safe
non-degenerate ball around `(a₀, v₀)`. -/
lemma flrw_ivp_exists_in_ball (Λ a₀ v₀ : ℝ) (ha₀ : a₀ ≠ 0) :
    ∃ δ > 0, ∃ z : ℝ → ℝ × ℝ, z 0 = (a₀, v₀) ∧
      ∀ t ∈ Ioo (-δ) δ,
        HasDerivAt z (flrwField Λ (z t)) t ∧
        z t ∈ closedBall (a₀, v₀) (|a₀| / 2) := by
  have hf := contDiffAt_flrwField Λ a₀ v₀ ha₀
  obtain ⟨z, hz0, ε, hε, hz⟩ :=
    hf.exists_forall_mem_closedBall_exists_eq_forall_mem_Ioo_hasDerivAt₀ 0
  have hz' : ∀ t ∈ Ioo (-ε) ε, HasDerivAt z (flrwField Λ (z t)) t := by
    intro t ht
    exact hz t (by simpa using ht)
  have hcont : ContinuousAt z 0 :=
    (hz' 0 ⟨neg_lt_zero.mpr hε, hε⟩).continuousAt
  have hR : 0 < |a₀| / 2 := half_pos (abs_pos.mpr ha₀)
  have hnhds : ∀ᶠ t in 𝓝 (0 : ℝ), z t ∈ closedBall (a₀, v₀) (|a₀| / 2) := by
    have hmem : closedBall (a₀, v₀) (|a₀| / 2) ∈ 𝓝 (z 0) := by
      rw [hz0]
      exact closedBall_mem_nhds (a₀, v₀) hR
    exact hcont.eventually hmem
  obtain ⟨δ₁, hδ₁, hball⟩ := Metric.mem_nhds_iff.mp hnhds
  refine ⟨min ε δ₁, lt_min hε hδ₁, z, hz0, fun t ht => ?_⟩
  have htε : t ∈ Ioo (-ε) ε :=
    ⟨lt_of_le_of_lt (neg_le_neg (min_le_left _ _)) ht.1,
      lt_of_lt_of_le ht.2 (min_le_left _ _)⟩
  have htd1 : t ∈ Metric.ball (0 : ℝ) δ₁ := by
    rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs, abs_lt]
    exact ⟨lt_of_le_of_lt (neg_le_neg (min_le_right _ _)) ht.1,
      lt_of_lt_of_le ht.2 (min_le_right _ _)⟩
  exact ⟨hz' t htε, hball htd1⟩

/-- Chosen local existence radius for the flat FLRW reduced Cauchy problem. -/
noncomputable def flrwLocalRadius (Λ a₀ v₀ : ℝ) (ha₀ : a₀ ≠ 0) : ℝ :=
  Classical.choose (flrw_ivp_exists_in_ball Λ a₀ v₀ ha₀)

lemma flrwLocalRadius_pos (Λ a₀ v₀ : ℝ) (ha₀ : a₀ ≠ 0) :
    0 < flrwLocalRadius Λ a₀ v₀ ha₀ :=
  (Classical.choose_spec (flrw_ivp_exists_in_ball Λ a₀ v₀ ha₀)).1

/-- A curve `(a, a')` on `Ioo (-δ) δ` solving the nonlinear flat FLRW reduced
Einstein ODE `2 a a'' + (a')² = Λ a²`. -/
@[ext]
structure FLRWReducedSol (δ : ℝ) where
  /-- The scale factor and its derivative along the interval `Ioo (-δ) δ`. -/
  val : {t : ℝ // t ∈ Ioo (-δ) δ} → ℝ × ℝ

/-- The nonlinear 4D flat FLRW reduced Einstein Cauchy problem packaged as a
`ReducedCauchyProblem`. -/
noncomputable def flrwReducedProblem (Λ a₀ v₀ : ℝ) (ha₀ : a₀ ≠ 0) :
    ReducedCauchyProblem minkowskiChart where
  data := minkowskiChartInitialData
  Solution := FLRWReducedSol (flrwLocalRadius Λ a₀ v₀ ha₀)
  IsSolution := fun u =>
    ∃ z : ℝ → ℝ × ℝ,
      (∀ t (ht : t ∈ Ioo (-flrwLocalRadius Λ a₀ v₀ ha₀) (flrwLocalRadius Λ a₀ v₀ ha₀)),
        u.val ⟨t, ht⟩ = z t ∧
        HasDerivAt z (flrwField Λ (z t)) t ∧
        z t ∈ closedBall (a₀, v₀) (|a₀| / 2))
  HasCauchyData := fun u =>
    u.val ⟨0, ⟨neg_lt_zero.mpr (flrwLocalRadius_pos Λ a₀ v₀ ha₀),
      flrwLocalRadius_pos Λ a₀ v₀ ha₀⟩⟩ = (a₀, v₀)
  IsWaveGauge := fun u =>
    ∀ t (ht : t ∈ Ioo (-flrwLocalRadius Λ a₀ v₀ ha₀) (flrwLocalRadius Λ a₀ v₀ ha₀)),
      (u.val ⟨t, ht⟩).1 ≠ 0

/-- **Certificate for the nonlinear 4D flat FLRW reduced Einstein system**:
inhabits `ReducedLocalExistenceCertificate` via Mathlib's Picard–Lindelöf
existence (`ContDiffAt.exists_forall_mem_closedBall_exists_eq_forall_mem_Ioo_hasDerivAt₀`)
and uniqueness (`ODE_solution_unique_of_mem_Ioo`) with an explicit Lipschitz
bound on the FLRW phase-space vector field. -/
lemma flrw_reducedLocalExistence (Λ a₀ v₀ : ℝ) (ha₀ : a₀ ≠ 0) :
    ReducedLocalExistenceCertificate (flrwReducedProblem Λ a₀ v₀ ha₀) where
  local_existence := by
    have hspec := (Classical.choose_spec (flrw_ivp_exists_in_ball Λ a₀ v₀ ha₀)).2
    rcases hspec with ⟨z, hz0, hz⟩
    let δ := flrwLocalRadius Λ a₀ v₀ ha₀
    refine ⟨⟨fun t => z t.1⟩, ⟨z, fun t ht => ⟨rfl, hz t ht⟩⟩, hz0, fun t ht => ?_⟩
    have hball := (hz t ht).2
    rw [mem_closedBall, dist_eq_norm, Prod.norm_def] at hball
    have hsub : |(z t).1 - a₀| ≤ |a₀| / 2 := le_trans (le_max_left _ _) hball
    have ha_pos : 0 < |a₀| := abs_pos.mpr ha₀
    have hlb : |a₀| / 2 ≤ |(z t).1| := by
      have := abs_sub_abs_le_abs_sub a₀ (z t).1
      rw [abs_sub_comm a₀ (z t).1] at this
      linarith
    exact abs_pos.mp (by linarith)
  local_uniqueness := fun u v ⟨z₁, hz₁⟩ ⟨z₂, hz₂⟩ hu₀ hv₀ => by
    obtain ⟨K, hK⟩ := flrwField_lipschitzOn Λ a₀ v₀ ha₀
    let δ := flrwLocalRadius Λ a₀ v₀ ha₀
    have hδ : 0 < δ := flrwLocalRadius_pos Λ a₀ v₀ ha₀
    have ht0 : (0 : ℝ) ∈ Ioo (-δ) δ := ⟨neg_lt_zero.mpr hδ, hδ⟩
    have heq0 : z₁ 0 = z₂ 0 := by
      have h1 := (hz₁ 0 ht0).1
      have h2 := (hz₂ 0 ht0).1
      rw [← h1, ← h2]
      exact hu₀.trans hv₀.symm
    have heq : EqOn z₁ z₂ (Ioo (-δ) δ) :=
      ODE_solution_unique_of_mem_Ioo
        (fun _ _ => hK) ht0
        (fun t ht => ⟨(hz₁ t ht).2.1, (hz₁ t ht).2.2⟩)
        (fun t ht => ⟨(hz₂ t ht).2.1, (hz₂ t ht).2.2⟩)
        heq0
    apply FLRWReducedSol.ext
    funext t
    rw [(hz₁ t.1 t.2).1, (hz₂ t.1 t.2).1, heq t.2]

end GeneralRelativity
