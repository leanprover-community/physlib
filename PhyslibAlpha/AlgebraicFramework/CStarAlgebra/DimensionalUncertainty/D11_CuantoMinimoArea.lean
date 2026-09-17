/-
Copyright (c) 2026 Eduardo Nava-Hernández, José Arturo Nava-Hernández, Gerardo Gabriel Nava Gómez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eduardo Nava-Hernández, José Arturo Nava-Hernández, Gerardo Gabriel Nava Gómez
-/
module

public import PhyslibAlpha.AlgebraicFramework.CStarAlgebra.DimensionalUncertainty.D10_Certificado

@[expose] public section

/-!
# D11 — Cuanto cuántico elemental de área

Este módulo baja a Lean la lectura estrictamente matemática del cuanto
cuántico elemental:

* `deltaGeom 4` es el primer defecto lineal positivo de la cola `d ≥ 4`.
* `deltaGeom 4 ^ 2` es el primer cuanto cuántico elemental de área.
* Por monotonía, ninguna resolución de área realizada en `H_d`, `d ≥ 4`,
  queda por debajo de ese cuanto.

No introduce unidades físicas, bariones ni escala de Planck. Si luego se
quiere poner una unidad externa, basta multiplicar por una escala no negativa:
la cota sobrevive por orden.

La dependencia matemática es la cadena del paquete:
Cauchy--Gram → Robertson--Schrödinger → instancia `T_d/P_d` →
Niven/Szegő/monotonía. No modifica Robertson 1929; lo usa como ancla y
deriva el piso de área de su realización discreta.
-/

noncomputable section

namespace CuantoMinimoArea

open Gnomon

/-- Cuanto cuántico elemental de área de la cola `H_d`, `d ≥ 4`. -/
def cuantoCuanticoElemental : ℝ :=
  deltaGeom 4 ^ 2

/-- Alias operativo: el "cuadrito" mínimo es el cuanto cuántico elemental. -/
def cuadritoMinimo : ℝ :=
  cuantoCuanticoElemental

/-- Área de resolución inducida por el defecto geométrico en `H_d`. -/
def areaResolucionHd (d : ℕ) : ℝ :=
  deltaGeom d ^ 2

/-- El nombre citable y el alias operativo son la misma cantidad. -/
theorem cuadritoMinimo_eq_cuantoCuanticoElemental :
    cuadritoMinimo = cuantoCuanticoElemental := by
  rfl

/-- El "cuadrito" es exactamente la resolución de área en `H_4`. -/
theorem cuadritoMinimo_eq_areaResolucionH4 :
    cuadritoMinimo = areaResolucionHd 4 := by
  rfl

/-- El cuanto cuántico elemental es exactamente la resolución de área en `H_4`. -/
theorem cuantoCuanticoElemental_eq_areaResolucionH4 :
    cuantoCuanticoElemental = areaResolucionHd 4 := by
  rfl

/-- El cuanto cuántico elemental de área es estrictamente positivo. -/
theorem cuantoCuanticoElemental_pos : 0 < cuantoCuanticoElemental := by
  unfold cuantoCuanticoElemental
  have hδ : 0 < deltaGeom 4 :=
    deltaGeom_pos_of_four_le 4 (by omega)
  positivity

/-- Alias de positividad para el nombre operativo. -/
theorem cuadritoMinimo_pos : 0 < cuadritoMinimo := by
  simpa [cuadritoMinimo] using cuantoCuanticoElemental_pos

/-- Toda área de resolución en `H_d`, `d ≥ 4`, está por encima del cuanto. -/
theorem cuantoCuanticoElemental_le_areaResolucionHd (d : ℕ) (hd : 4 ≤ d) :
    cuantoCuanticoElemental ≤ areaResolucionHd d := by
  unfold cuantoCuanticoElemental areaResolucionHd
  exact deltaGeom_sq_four_le d hd

/-- Toda área de resolución en `H_d`, `d ≥ 4`, está por encima del cuadrito. -/
theorem cuadritoMinimo_le_areaResolucionHd (d : ℕ) (hd : 4 ≤ d) :
    cuadritoMinimo ≤ areaResolucionHd d := by
  simpa [cuadritoMinimo] using cuantoCuanticoElemental_le_areaResolucionHd d hd

/-- No existe una resolución realizada en `H_d`, `d ≥ 4`, estrictamente menor
que el cuanto cuántico elemental. -/
theorem no_hay_resolucion_menor_que_cuanto_cuantico
    (d : ℕ) (hd : 4 ≤ d) :
    ¬ areaResolucionHd d < cuantoCuanticoElemental := by
  exact not_lt.mpr (cuantoCuanticoElemental_le_areaResolucionHd d hd)

/-- Alias operativo: no hay resolución menor que el cuadrito mínimo. -/
theorem no_hay_resolucion_menor_que_cuadrito
    (d : ℕ) (hd : 4 ≤ d) :
    ¬ areaResolucionHd d < cuadritoMinimo := by
  simpa [cuadritoMinimo] using no_hay_resolucion_menor_que_cuanto_cuantico d hd

/-- Cualquier umbral por debajo del cuadrito queda por debajo de toda
resolución realizada en la cola `d ≥ 4`. -/
theorem umbral_bajo_cuadrito_no_alcanza_Hd
    (d : ℕ) (hd : 4 ≤ d) (ε : ℝ) (hε : ε < cuadritoMinimo) :
    ε < areaResolucionHd d :=
  lt_of_lt_of_le hε (cuadritoMinimo_le_areaResolucionHd d hd)

/-- Poner una escala externa no negativa conserva la cota mínima. -/
theorem escala_no_negativa_conserva_cuanto_cuantico
    (escala : ℝ) (hesc : 0 ≤ escala) (d : ℕ) (hd : 4 ≤ d) :
    escala * cuantoCuanticoElemental ≤ escala * areaResolucionHd d :=
  mul_le_mul_of_nonneg_left (cuantoCuanticoElemental_le_areaResolucionHd d hd) hesc

/-- Alias operativo para la escala externa no negativa. -/
theorem escala_no_negativa_conserva_cuadrito
    (escala : ℝ) (hesc : 0 ≤ escala) (d : ℕ) (hd : 4 ≤ d) :
    escala * cuadritoMinimo ≤ escala * areaResolucionHd d :=
by
  simpa [cuadritoMinimo] using escala_no_negativa_conserva_cuanto_cuantico escala hesc d hd

/-- Con una escala externa positiva, el cuanto escalado sigue siendo
estrictamente positivo. -/
theorem cuanto_cuantico_escalado_pos
    (escala : ℝ) (hesc : 0 < escala) :
    0 < escala * cuantoCuanticoElemental :=
  mul_pos hesc cuantoCuanticoElemental_pos

/-- Alias operativo: con escala positiva, el cuadrito escalado sigue siendo
estrictamente positivo. -/
theorem cuadrito_escalado_pos
    (escala : ℝ) (hesc : 0 < escala) :
    0 < escala * cuadritoMinimo :=
by
  simpa [cuadritoMinimo] using cuanto_cuantico_escalado_pos escala hesc

/-- Certificado citable del cuanto cuántico elemental de área. -/
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
