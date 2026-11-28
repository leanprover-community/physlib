/-
Copyright (c) 2026 The Gravitation formalisation contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Vergara Gil
-/

module

public import PhyslibAlpha.Relativity.General.InitialData.WaveCauchy
public import PhyslibAlpha.Relativity.General.InitialData.Divergence3D

/-!

# A 3D linear reduced-wave existence model

## i. Overview

This file is a scoped M3 stepping stone, not a quasilinear Einstein existence
theorem.  It embeds the one-dimensional d'Alembert solution into three spatial
dimensions by making it depend only on the first coordinate.  The resulting
field solves the linear constant-coefficient 3D wave equation

  ∂ₜ² u = ∑ᵢ ∂ᵢ² u

with Cauchy data constant in the transverse directions.  The spatial operator
is the explicit sum of coordinate second derivatives.

No gauge, quasilinearity, constraint propagation, or manifold statement is
claimed here.


## ii. Key results

- `planeWave3D`
- `spatialLaplacian3D_planeWave3D`
- `planeWave3D_wave_equation`

## iii. Table of contents

- A. Plane waves and the three-dimensional Laplacian

## iv. References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., AMS, 2010, §2.4. [ref: Evans2010PDE]
-/
@[expose] public section

/-! ## A. Plane waves and the three-dimensional Laplacian -/

namespace GeneralRelativity

/-- The derivative along one coordinate direction at a point. -/
noncomputable def coordDeriv (u : Space3 → ℝ) (i : Fin 3) (x : Space3) : ℝ :=
  deriv (fun s : ℝ => u (Function.update x i s)) (x i)

/-- The second derivative along one coordinate direction. -/
noncomputable def coordDeriv2 (u : Space3 → ℝ) (i : Fin 3) (x : Space3) : ℝ :=
  coordDeriv (fun y => coordDeriv u i y) i x

/-- The coordinate Laplacian on `Space3`, as the sum of second coordinate
derivatives. -/
noncomputable def spatialLaplacian3D (u : Space3 → ℝ) (x : Space3) : ℝ :=
  ∑ i : Fin 3, coordDeriv2 u i x

/-- The d'Alembert solution embedded in three dimensions, depending only on
`x 0`. -/
noncomputable def planeWave3D (f g : ℝ → ℝ) (t : ℝ) (x : Space3) : ℝ :=
  dAlembert f g t (x 0)

/-- The first coordinate derivative of the embedded d'Alembert field. -/
lemma coordDeriv_planeWave3D_zero
    (f g f' : ℝ → ℝ) (hf : ∀ y, HasDerivAt f (f' y) y)
    (hg : Continuous g) (t : ℝ) (x : Space3) :
    coordDeriv (planeWave3D f g t) 0 x =
      (f' (x 0 + t) + f' (x 0 - t)) / 2 +
        (g (x 0 + t) - g (x 0 - t)) / 2 := by
  unfold coordDeriv planeWave3D
  have h := hasDerivAt_dAlembert_x f g f' hf hg t (x 0)
  have hfun : (fun s : ℝ => dAlembert f g t (Function.update x 0 s 0)) =
      fun s : ℝ => dAlembert f g t s := by
    funext s
    simp
  rw [hfun]
  exact h.deriv

/-- A transverse coordinate derivative of the embedded d'Alembert field
vanishes. -/
lemma coordDeriv_planeWave3D_succ
    (f g : ℝ → ℝ) (t : ℝ) (x : Space3) (j : Fin 2) :
    coordDeriv (planeWave3D f g t) (Fin.succ j) x = 0 := by
  unfold coordDeriv planeWave3D
  have h0 : (0 : Fin 3) ≠ Fin.succ j := by
    exact fun h => Fin.succ_ne_zero j h.symm
  simp [Function.update_of_ne h0]

/-- The second coordinate derivative in the distinguished direction. -/
lemma coordDeriv2_planeWave3D_zero
    (f g f' f'' g' : ℝ → ℝ)
    (hf : ∀ y, HasDerivAt f (f' y) y)
    (hf' : ∀ y, HasDerivAt f' (f'' y) y)
    (hg : ∀ y, HasDerivAt g (g' y) y)
    (hgc : Continuous g) (t : ℝ) (x : Space3) :
    coordDeriv2 (planeWave3D f g t) 0 x =
      (f'' (x 0 + t) + f'' (x 0 - t)) / 2 +
        (g' (x 0 + t) - g' (x 0 - t)) / 2 := by
  unfold coordDeriv2
  have hfun : (fun y : Space3 => coordDeriv (planeWave3D f g t) 0 y) =
      fun y : Space3 =>
        (f' (y 0 + t) + f' (y 0 - t)) / 2 +
          (g (y 0 + t) - g (y 0 - t)) / 2 := by
    funext y
    exact coordDeriv_planeWave3D_zero f g f' hf hgc t y
  rw [hfun]
  unfold coordDeriv
  have h := hasDerivAt_waveX f' g f'' g' hf' hg t (x 0)
  have hfun2 :
      (fun s : ℝ =>
        (f' (Function.update x 0 s 0 + t) + f' (Function.update x 0 s 0 - t)) / 2 +
          (g (Function.update x 0 s 0 + t) - g (Function.update x 0 s 0 - t)) / 2) =
        fun s : ℝ =>
          (f' (s + t) + f' (s - t)) / 2 + (g (s + t) - g (s - t)) / 2 := by
    funext s
    simp
  rw [hfun2]
  exact h.deriv

/-- A transverse second coordinate derivative of the embedded d'Alembert field
vanishes. -/
lemma coordDeriv2_planeWave3D_succ
    (f g : ℝ → ℝ) (t : ℝ) (x : Space3) (j : Fin 2) :
    coordDeriv2 (planeWave3D f g t) (Fin.succ j) x = 0 := by
  unfold coordDeriv2
  have hfun : (fun y : Space3 => coordDeriv (planeWave3D f g t) (Fin.succ j) y) =
      fun _ : Space3 => 0 := by
    funext y
    exact coordDeriv_planeWave3D_succ f g t y j
  rw [hfun]
  unfold coordDeriv
  simp

/-- The coordinate Laplacian of the embedded d'Alembert field. -/
lemma spatialLaplacian3D_planeWave3D
    (f g f' f'' g' : ℝ → ℝ)
    (hf : ∀ y, HasDerivAt f (f' y) y)
    (hf' : ∀ y, HasDerivAt f' (f'' y) y)
    (hg : ∀ y, HasDerivAt g (g' y) y)
    (hgc : Continuous g) (t : ℝ) (x : Space3) :
    spatialLaplacian3D (planeWave3D f g t) x =
      (f'' (x 0 + t) + f'' (x 0 - t)) / 2 +
        (g' (x 0 + t) - g' (x 0 - t)) / 2 := by
  unfold spatialLaplacian3D
  rw [Fin.sum_univ_three]
  rw [coordDeriv2_planeWave3D_zero f g f' f'' g' hf hf' hg hgc t x]
  have h1 : coordDeriv2 (planeWave3D f g t) 1 x = 0 := by
    simpa using coordDeriv2_planeWave3D_succ f g t x 0
  have h2 : coordDeriv2 (planeWave3D f g t) 2 x = 0 := by
    simpa using coordDeriv2_planeWave3D_succ f g t x 1
  rw [h1, h2]
  ring

/-- **Scoped 3D linear wave existence.**  The embedded d'Alembert field solves
the coordinate wave equation `u_tt = Δu` in three spatial dimensions. -/
lemma planeWave3D_wave_equation
    (f g f' f'' g' : ℝ → ℝ)
    (hf : ∀ y, HasDerivAt f (f' y) y)
    (hf' : ∀ y, HasDerivAt f' (f'' y) y)
    (hg : ∀ y, HasDerivAt g (g' y) y)
    (hgc : Continuous g) (t : ℝ) (x : Space3) :
    deriv (fun t : ℝ => deriv (fun t : ℝ => planeWave3D f g t x) t) t =
      spatialLaplacian3D (planeWave3D f g t) x := by
  rw [spatialLaplacian3D_planeWave3D f g f' f'' g' hf hf' hg hgc t x]
  unfold planeWave3D
  have htime : (fun s : ℝ => deriv (fun s : ℝ => dAlembert f g s (x 0)) s) =
      fun s : ℝ =>
        (f' (x 0 + s) - f' (x 0 - s)) / 2 +
          (g (x 0 + s) + g (x 0 - s)) / 2 := by
    funext s
    exact (hasDerivAt_dAlembert_t f g f' hf hgc s (x 0)).deriv
  rw [htime]
  rw [(hasDerivAt_waveT f' g f'' g' hf' hg t (x 0)).deriv]

/-- The embedded field has the prescribed initial position. -/
lemma planeWave3D_zero (f g : ℝ → ℝ) (x : Space3) :
    planeWave3D f g 0 x = f (x 0) := by
  simp [planeWave3D, dAlembert_zero]

/-- The embedded field has the prescribed initial velocity. -/
lemma hasDerivAt_planeWave3D_zero
    (f g f' : ℝ → ℝ) (hf : ∀ y, HasDerivAt f (f' y) y)
    (hg : Continuous g) (x : Space3) :
    HasDerivAt (fun t : ℝ => planeWave3D f g t x) (g (x 0)) 0 := by
  unfold planeWave3D
  exact hasDerivAt_dAlembert_zero f g f' hf hg (x 0)

/-- The scoped 3D model satisfies both prescribed Cauchy data. -/
lemma planeWave3D_cauchy_data
    (f g f' : ℝ → ℝ) (hf : ∀ y, HasDerivAt f (f' y) y)
    (hg : Continuous g) (x : Space3) :
    planeWave3D f g 0 x = f (x 0) ∧
      HasDerivAt (fun t : ℝ => planeWave3D f g t x) (g (x 0)) 0 :=
  ⟨planeWave3D_zero f g x, hasDerivAt_planeWave3D_zero f g f' hf hg x⟩

end GeneralRelativity
