/-
Copyright (c) 2026 Eduardo Nava-Hernández, José Arturo Nava-Hernández, Gerardo Gabriel Nava Gómez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eduardo Nava-Hernández, José Arturo Nava-Hernández, Gerardo Gabriel Nava Gómez
-/
module

public import PhyslibAlpha.AlgebraicFramework.HilbertSpace.PathSpectralGap.D0_Habitat
public import Mathlib.Combinatorics.SimpleGraph.Hasse

@[expose] public section

/-!
# D3 — Operadores de transporte y posición sobre el grafo camino

El soporte discreto no introduce un grafo ad hoc: es literalmente
`SimpleGraph.pathGraph d` de Mathlib, el camino con `d` vértices
`0,1,…,d−1` y aristas sólo entre vecinos consecutivos. Sobre esa base se
definen dos matrices hermitianas: `T_d` (transporte, soportado en las
aristas del camino) y `P_d` (posición, diagonal, con coordenadas
centradas en `[-1,1]`).

La segunda mitad del archivo (`CanalPreFuerza`) prueba, sin apelar a
ninguna elección de diseño, que el grafo camino es la **única** opción
compatible con dos condiciones puramente combinatorias: localidad
(ninguna arista salta vecinos) y completitud (no falta ningún paso
elemental). Cualquier grafo local en `Fin d` que no omita un paso mínimo
**es** `pathGraph d`; no hay otro candidato.
-/

namespace TransportePosicion

open SimpleGraph

/-- Grafo de fase del canal transporte–posición: el camino `pathGraph d`
de Mathlib. -/
abbrev GrafoTP (d : ℕ) : SimpleGraph (Fin d) :=
  SimpleGraph.pathGraph d

/-- Adyacencia elemental del camino: sólo hay desplazamiento mínimo de un
paso. -/
theorem grafoTP_adj {d : ℕ} {i j : Fin d} :
    (GrafoTP d).Adj i j ↔ i.val + 1 = j.val ∨ j.val + 1 = i.val := by
  simpa [GrafoTP] using
    (SimpleGraph.pathGraph_adj (n := d) (u := i) (v := j))

/-- Predicado decidible del desplazamiento mínimo en la línea discreta. -/
def PasoMinimo {d : ℕ} (i j : Fin d) : Prop :=
  i.val + 1 = j.val ∨ j.val + 1 = i.val

instance pasoMinimo_decidable {d : ℕ} (i j : Fin d) :
    Decidable (PasoMinimo i j) := by
  unfold PasoMinimo
  infer_instance

/-- El paso mínimo decidible es exactamente la adyacencia de `pathGraph`. -/
theorem pasoMinimo_iff_adj {d : ℕ} {i j : Fin d} :
    PasoMinimo i j ↔ (GrafoTP d).Adj i j := by
  rw [grafoTP_adj]
  rfl

/-- El soporte discreto `T_d/P_d` es isomorfo a `pathGraph d` por definición
canónica. -/
theorem grafoTP_es_pathGraph (d : ℕ) :
    Nonempty (GrafoTP d ≃g SimpleGraph.pathGraph d) := by
  change Nonempty (SimpleGraph.pathGraph d ≃g SimpleGraph.pathGraph d)
  exact ⟨SimpleGraph.Iso.refl⟩

/-- Matriz de adyacencia compleja del canal de transporte. -/
noncomputable def Ad (d : ℕ) : Matrix (Fin d) (Fin d) ℂ :=
  fun i j => if PasoMinimo i j then 1 else 0

/-- Radio espectral usado para normalizar el transporte de la cadena
finita: `ρ_d = 2 cos(π/(d+1))`. -/
noncomputable def rho (d : ℕ) : ℝ :=
  2 * Real.cos (Real.pi / ((d : ℝ) + 1))

/-- Operador de transporte normalizado `T_d = A_d / ρ_d`. -/
noncomputable def Td (d : ℕ) : Matrix (Fin d) (Fin d) ℂ :=
  fun i j => Ad d i j / (rho d : ℂ)

/-- Coordenada centrada de posición sobre la base discreta, en `[-1,1]`. -/
noncomputable def posicionCoord (d : ℕ) (j : Fin d) : ℝ :=
  (2 * ((j.val : ℝ) + 1) - ((d : ℝ) + 1)) / ((d : ℝ) - 1)

/-- Operador de posición diagonal `P_d`. -/
noncomputable def Pd (d : ℕ) : Matrix (Fin d) (Fin d) ℂ :=
  fun i j => if i = j then (posicionCoord d i : ℂ) else 0

theorem Ad_eq_one_iff {d : ℕ} {i j : Fin d} :
    Ad d i j = 1 ↔ (GrafoTP d).Adj i j := by
  unfold Ad
  rw [← pasoMinimo_iff_adj]
  by_cases h : PasoMinimo i j
  · simp [h]
  · simp [h]

theorem Td_eq_zero_of_not_adj {d : ℕ} {i j : Fin d}
    (h : ¬ (GrafoTP d).Adj i j) :
    Td d i j = 0 := by
  have hpaso : ¬ PasoMinimo i j := by
    intro hp
    exact h (pasoMinimo_iff_adj.mp hp)
  simp [Td, Ad, hpaso]

/-- `P_d` es diagonal en la base discreta. -/
theorem Pd_eq_zero_offdiag {d : ℕ} {i j : Fin d} (hij : i ≠ j) :
    Pd d i j = 0 := by
  simp [Pd, hij]

/-- En la diagonal, `P_d` devuelve la coordenada discreta centrada. -/
theorem Pd_diag {d : ℕ} (i : Fin d) :
    Pd d i i = (posicionCoord d i : ℂ) := by
  simp [Pd]

end TransportePosicion

/-!
## Por qué `pathGraph d` y no otro grafo

Un canal local (toda arista es un paso mínimo entre vecinos) y completo
(no falta ningún paso mínimo posible) sobre `Fin d` es, por extensionalidad
de la relación de adyacencia, exactamente `pathGraph d`. No hay una
"simplificación" que conserve ambas propiedades: quitar una arista rompe
la completitud.
-/

namespace CanalPreFuerza

open SimpleGraph

/-- Localidad estricta: toda arista del canal es un paso entre vecinos
consecutivos. No se permiten saltos ni atajos. -/
def LocalidadOrdenada {d : ℕ} (G : SimpleGraph (Fin d)) : Prop :=
  ∀ {i j : Fin d}, G.Adj i j → TransportePosicion.PasoMinimo i j

/-- Completitud: todo paso entre vecinos consecutivos debe estar presente.
Quitar uno rompe el movimiento local completo entre los extremos de la
celda. -/
def PasosElementalesCompletos {d : ℕ} (G : SimpleGraph (Fin d)) : Prop :=
  ∀ {i j : Fin d}, TransportePosicion.PasoMinimo i j → G.Adj i j

/-- Defecto por intentar simplificar más que `pathGraph d`: se omite al
menos un paso elemental consecutivo. -/
def OmitePasoElemental {d : ℕ} (G : SimpleGraph (Fin d)) : Prop :=
  ∃ i j : Fin d, TransportePosicion.PasoMinimo i j ∧ ¬ G.Adj i j

/-- Canal ordenado, local y completo en la celda discreta. -/
structure CanalLocalNoRamificadoOrdenado (d : ℕ) where
  grafo : SimpleGraph (Fin d)
  localidad_ordenada : LocalidadOrdenada grafo
  pasos_elementales : PasosElementalesCompletos grafo

/-- En un canal local ordenado completo, la adyacencia es exactamente el
paso mínimo de la celda. -/
theorem CanalLocalNoRamificadoOrdenado.adj_iff_paso
    {d : ℕ} (C : CanalLocalNoRamificadoOrdenado d) {i j : Fin d} :
    C.grafo.Adj i j ↔ TransportePosicion.PasoMinimo i j := by
  exact ⟨fun h => C.localidad_ordenada h,
    fun h => C.pasos_elementales h⟩

/-- Teorema de minimalidad: localidad ordenada y pasos elementales
completos fuerzan que el soporte sea exactamente `pathGraph d`. -/
theorem canal_local_no_ramificado_es_pathGraph
    {d : ℕ} (C : CanalLocalNoRamificadoOrdenado d) :
    C.grafo = SimpleGraph.pathGraph d := by
  ext i j
  rw [C.adj_iff_paso]
  simpa [TransportePosicion.GrafoTP] using
    (TransportePosicion.pasoMinimo_iff_adj (d := d) (i := i) (j := j))

/-- Versión isomórfica del mismo cierre. -/
theorem canal_local_no_ramificado_iso_pathGraph
    {d : ℕ} (C : CanalLocalNoRamificadoOrdenado d) :
    Nonempty (C.grafo ≃g SimpleGraph.pathGraph d) := by
  rw [canal_local_no_ramificado_es_pathGraph C]
  exact ⟨SimpleGraph.Iso.refl⟩

/-- El canal canónico `T_d/P_d` satisface directamente el certificado local
ordenado: no tiene saltos y no omite pasos elementales. -/
def canal_TP_local_no_ramificado (d : ℕ) :
    CanalLocalNoRamificadoOrdenado d where
  grafo := TransportePosicion.GrafoTP d
  localidad_ordenada := by
    intro i j h
    exact (TransportePosicion.pasoMinimo_iff_adj
      (d := d) (i := i) (j := j)).mpr h
  pasos_elementales := by
    intro i j h
    exact (TransportePosicion.pasoMinimo_iff_adj
      (d := d) (i := i) (j := j)).mp h

/-- Ningún canal que ya satisface el certificado local ordenado puede omitir
un paso elemental: "no hay una simplificación local más simple que
`pathGraph d`". -/
theorem no_hay_canal_local_mas_simple_que_Pd
    {d : ℕ} (C : CanalLocalNoRamificadoOrdenado d) :
    ¬ OmitePasoElemental C.grafo := by
  rintro ⟨i, j, hpaso, hno⟩
  exact hno (C.pasos_elementales hpaso)

/-- Cierre: el soporte canónico `T_d/P_d` es `pathGraph d`, y cualquier
intento local de hacerlo "más simple" pierde un paso elemental. -/
theorem cierre_minimalidad_local_TP (d : ℕ) :
    (canal_TP_local_no_ramificado d).grafo = SimpleGraph.pathGraph d ∧
      ¬ OmitePasoElemental (canal_TP_local_no_ramificado d).grafo := by
  exact ⟨canal_local_no_ramificado_es_pathGraph
      (canal_TP_local_no_ramificado d),
    no_hay_canal_local_mas_simple_que_Pd
      (canal_TP_local_no_ramificado d)⟩

end CanalPreFuerza
