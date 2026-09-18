/-
Copyright (c) 2026 Eduardo Nava-Hernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eduardo Nava-Hernández, José Arturo Nava-Hernández, Gerardo Gabriel Nava Gómez
-/
module

public import PhyslibAlpha.AlgebraicFramework.CStarAlgebra.DimUncertainty.D10_Certificado

/-!
# D11 — Elementary quantum of area

This module brings to Lean the strictly mathematical reading of the
elementary quantum:

* `deltaGeom 4` is the first positive linear defect of the `d ≥ 4` tail.
* `deltaGeom 4 ^ 2` is the first elementary quantum of area.
* By monotonicity, no area resolution realized in `H_d`, `d ≥ 4`,
  falls below that quantum.

No physical units, baryons, or Planck scale are introduced. To attach
an external unit later, it suffices to multiply by a nonnegative scale:
the bound survives by order.

The mathematical dependency is the package chain:
Cauchy--Gram → Robertson--Schrödinger → `T_d/P_d` instance →
Niven/Szegő/monotonicity. It does not modify Robertson 1929; it uses
it as an anchor and derives the area floor from its discrete realization.
-/

@[expose] public section

noncomputable section

namespace CuantoMinimoArea

open Gnomon

/-- Elementary quantum of area of the `H_d` tail, `d ≥ 4`. -/
def cuantoCuanticoElemental : ℝ :=
  deltaGeom 4 ^ 2

/-- Operational alias: the minimum "small square" is the elementary quantum. -/
def cuadritoMinimo : ℝ :=
  cuantoCuanticoElemental

/-- Resolution area induced by the geometric defect in `H_d`. -/
def areaResolucionHd (d : ℕ) : ℝ :=
  deltaGeom d ^ 2

/-- The citable name and the operational alias are the same quantity. -/
theorem cuadritoMinimo_eq_cuantoCuanticoElemental :
    cuadritoMinimo = cuantoCuanticoElemental := by
  rfl

/-- The "small square" is exactly the area resolution in `H_4`. -/
theorem cuadritoMinimo_eq_areaResolucionH4 :
    cuadritoMinimo = areaResolucionHd 4 := by
  rfl

/-- The elementary quantum is exactly the area resolution in `H_4`. -/
theorem cuantoCuanticoElemental_eq_areaResolucionH4 :
    cuantoCuanticoElemental = areaResolucionHd 4 := by
  rfl

/-- The elementary quantum of area is strictly positive. -/
theorem cuantoCuanticoElemental_pos : 0 < cuantoCuanticoElemental := by
  unfold cuantoCuanticoElemental
  have hδ : 0 < deltaGeom 4 :=
    deltaGeom_pos_of_four_le 4 (by omega)
  positivity

/-- Positivity alias for the operational name. -/
theorem cuadritoMinimo_pos : 0 < cuadritoMinimo := by
  simpa [cuadritoMinimo] using cuantoCuanticoElemental_pos

/-- Every resolution area in `H_d`, `d ≥ 4`, lies above the quantum. -/
theorem cuantoCuanticoElemental_le_areaResolucionHd (d : ℕ) (hd : 4 ≤ d) :
    cuantoCuanticoElemental ≤ areaResolucionHd d := by
  unfold cuantoCuanticoElemental areaResolucionHd
  exact deltaGeom_sq_four_le d hd

/-- Every resolution area in `H_d`, `d ≥ 4`, lies above the small square. -/
theorem cuadritoMinimo_le_areaResolucionHd (d : ℕ) (hd : 4 ≤ d) :
    cuadritoMinimo ≤ areaResolucionHd d := by
  simpa [cuadritoMinimo] using cuantoCuanticoElemental_le_areaResolucionHd d hd

/-- No realized resolution in `H_d`, `d ≥ 4`, is strictly less than the
elementary quantum. -/
theorem no_hay_resolucion_menor_que_cuanto_cuantico
    (d : ℕ) (hd : 4 ≤ d) :
    ¬ areaResolucionHd d < cuantoCuanticoElemental := by
  exact not_lt.mpr (cuantoCuanticoElemental_le_areaResolucionHd d hd)

/-- Operational alias: no resolution is less than the minimum small square. -/
theorem no_hay_resolucion_menor_que_cuadrito
    (d : ℕ) (hd : 4 ≤ d) :
    ¬ areaResolucionHd d < cuadritoMinimo := by
  simpa [cuadritoMinimo] using no_hay_resolucion_menor_que_cuanto_cuantico d hd

/-- Any threshold below the small square falls below every realized
resolution in the `d ≥ 4` tail. -/
theorem umbral_bajo_cuadrito_no_alcanza_Hd
    (d : ℕ) (hd : 4 ≤ d) (ε : ℝ) (hε : ε < cuadritoMinimo) :
    ε < areaResolucionHd d :=
  lt_of_lt_of_le hε (cuadritoMinimo_le_areaResolucionHd d hd)

/-- Applying a nonnegative external scale preserves the minimum bound. -/
theorem escala_no_negativa_conserva_cuanto_cuantico
    (escala : ℝ) (hesc : 0 ≤ escala) (d : ℕ) (hd : 4 ≤ d) :
    escala * cuantoCuanticoElemental ≤ escala * areaResolucionHd d :=
  mul_le_mul_of_nonneg_left (cuantoCuanticoElemental_le_areaResolucionHd d hd) hesc

/-- Operational alias for the nonnegative external scale. -/
theorem escala_no_negativa_conserva_cuadrito
    (escala : ℝ) (hesc : 0 ≤ escala) (d : ℕ) (hd : 4 ≤ d) :
    escala * cuadritoMinimo ≤ escala * areaResolucionHd d := by
  simpa [cuadritoMinimo] using escala_no_negativa_conserva_cuanto_cuantico escala hesc d hd

/-- With a positive external scale, the scaled quantum remains strictly
positive. -/
theorem cuanto_cuantico_escalado_pos
    (escala : ℝ) (hesc : 0 < escala) :
    0 < escala * cuantoCuanticoElemental :=
  mul_pos hesc cuantoCuanticoElemental_pos

/-- Operational alias: with a positive scale, the scaled small square
remains strictly positive. -/
theorem cuadrito_escalado_pos
    (escala : ℝ) (hesc : 0 < escala) :
    0 < escala * cuadritoMinimo := by
  simpa [cuadritoMinimo] using cuanto_cuantico_escalado_pos escala hesc

/-- Citable certificate for the elementary quantum of area. -/
structure CertificadoCuantoMinimoArea where
  cuanto_pos : 0 < cuantoCuanticoElemental
  area_minima : ∀ d : ℕ, 4 ≤ d → cuantoCuanticoElemental ≤ areaResolucionHd d
  no_menor : ∀ d : ℕ, 4 ≤ d → ¬ areaResolucionHd d < cuantoCuanticoElemental
  escala_conserva :
    ∀ escala : ℝ, 0 ≤ escala →
      ∀ d : ℕ, 4 ≤ d →
        escala * cuantoCuanticoElemental ≤ escala * areaResolucionHd d

theorem certificadoCuantoMinimoArea_OK :
    Nonempty CertificadoCuantoMinimoArea :=
  ⟨{ cuanto_pos := cuantoCuanticoElemental_pos
     area_minima := cuantoCuanticoElemental_le_areaResolucionHd
     no_menor := no_hay_resolucion_menor_que_cuanto_cuantico
     escala_conserva := escala_no_negativa_conserva_cuanto_cuantico }⟩

end CuantoMinimoArea
