/-
Copyright (c) 2026 Eduardo Nava-Hernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eduardo Nava-Hernández, José Arturo Nava-Hernández, Gerardo Gabriel Nava Gómez
-/
module

public import PhyslibAlpha.AlgebraicFramework.HilbertSpace.PathGap.D0_Habitat
public import Mathlib.Combinatorics.SimpleGraph.Hasse

/-!
# D3 — Transport and position operators on the path graph

The discrete support is not an ad-hoc graph: it is literally
`SimpleGraph.pathGraph d` from Mathlib, the path on `d` vertices
`0,1,…,d−1` with edges only between consecutive neighbours. Two
Hermitian matrices are built on it: `T_d` (transport, supported on
path edges) and `P_d` (position, diagonal, centered in `[-1,1]`).

The second half (`CanalPreFuerza`) proves, without any design choice,
that the path graph is the **only** option compatible with two purely
combinatorial conditions: locality (no edge skips a neighbour) and
completeness (no elementary step is missing). Any local graph on
`Fin d` that omits no minimal step **is** `pathGraph d`.
-/

@[expose] public section

namespace TransportePosicion

open SimpleGraph

/-- Phase graph of the transport–position channel: Mathlib's
`pathGraph d`. -/
abbrev GrafoTP (d : ℕ) : SimpleGraph (Fin d) :=
  SimpleGraph.pathGraph d

/-- Elementary path adjacency: only single minimal-step displacement. -/
theorem grafoTP_adj {d : ℕ} {i j : Fin d} :
    (GrafoTP d).Adj i j ↔ i.val + 1 = j.val ∨ j.val + 1 = i.val := by
  simpa [GrafoTP] using
    (SimpleGraph.pathGraph_adj (n := d) (u := i) (v := j))

/-- Decidable minimal-displacement predicate on the discrete line. -/
def PasoMinimo {d : ℕ} (i j : Fin d) : Prop :=
  i.val + 1 = j.val ∨ j.val + 1 = i.val

instance instDecidablePasoMinimo {d : ℕ} (i j : Fin d) :
    Decidable (PasoMinimo i j) := by
  unfold PasoMinimo
  infer_instance

/-- The decidable minimal step is exactly `pathGraph` adjacency. -/
theorem pasoMinimo_iff_adj {d : ℕ} {i j : Fin d} :
    PasoMinimo i j ↔ (GrafoTP d).Adj i j := by
  rw [grafoTP_adj]
  rfl

/-- The discrete support `T_d/P_d` is isomorphic to `pathGraph d` by
canonical definition. -/
theorem grafoTP_es_pathGraph (d : ℕ) :
    Nonempty (GrafoTP d ≃g SimpleGraph.pathGraph d) := by
  change Nonempty (SimpleGraph.pathGraph d ≃g SimpleGraph.pathGraph d)
  exact ⟨SimpleGraph.Iso.refl⟩

/-- Complex adjacency matrix of the transport channel. -/
noncomputable def Ad (d : ℕ) : Matrix (Fin d) (Fin d) ℂ :=
  fun i j => if PasoMinimo i j then 1 else 0

/-- Spectral radius for normalizing the finite-chain transport:
`ρ_d = 2 cos(π/(d+1))`. -/
noncomputable def rho (d : ℕ) : ℝ :=
  2 * Real.cos (Real.pi / ((d : ℝ) + 1))

/-- Normalized transport operator `T_d = A_d / ρ_d`. -/
noncomputable def Td (d : ℕ) : Matrix (Fin d) (Fin d) ℂ :=
  fun i j => Ad d i j / (rho d : ℂ)

/-- Centered position coordinate on the discrete basis, in `[-1,1]`. -/
noncomputable def posicionCoord (d : ℕ) (j : Fin d) : ℝ :=
  (2 * ((j.val : ℝ) + 1) - ((d : ℝ) + 1)) / ((d : ℝ) - 1)

/-- Diagonal position operator `P_d`. -/
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

/-- `P_d` is diagonal in the discrete basis. -/
theorem Pd_eq_zero_offdiag {d : ℕ} {i j : Fin d} (hij : i ≠ j) :
    Pd d i j = 0 := by
  simp [Pd, hij]

/-- On the diagonal, `P_d` returns the centered discrete coordinate. -/
theorem Pd_diag {d : ℕ} (i : Fin d) :
    Pd d i i = (posicionCoord d i : ℂ) := by
  simp [Pd]

end TransportePosicion

/-!
## Why `pathGraph d` and not another graph

A local channel (every edge is a minimal step between neighbours) and
complete (no possible minimal step is missing) on `Fin d` is, by
extensionality of the adjacency relation, exactly `pathGraph d`. There
is no "simplification" preserving both properties: removing an edge
breaks completeness.
-/

namespace CanalPreFuerza

open SimpleGraph

/-- Strict locality: every channel edge is a step between consecutive
neighbours. No jumps or shortcuts allowed. -/
def LocalidadOrdenada {d : ℕ} (G : SimpleGraph (Fin d)) : Prop :=
  ∀ {i j : Fin d}, G.Adj i j → TransportePosicion.PasoMinimo i j

/-- Completeness: every step between consecutive neighbours must be
present. Removing one breaks full local movement between the cell
endpoints. -/
def PasosElementalesCompletos {d : ℕ} (G : SimpleGraph (Fin d)) : Prop :=
  ∀ {i j : Fin d}, TransportePosicion.PasoMinimo i j → G.Adj i j

/-- Defect from trying to simplify beyond `pathGraph d`: at least one
consecutive elementary step is omitted. -/
def OmitePasoElemental {d : ℕ} (G : SimpleGraph (Fin d)) : Prop :=
  ∃ i j : Fin d, TransportePosicion.PasoMinimo i j ∧ ¬ G.Adj i j

/-- Ordered, local and complete channel on the discrete cell. -/
structure CanalLocalNoRamificadoOrdenado (d : ℕ) where
  /-- The graph supporting the ordered local channel. -/
  grafo : SimpleGraph (Fin d)
  localidad_ordenada : LocalidadOrdenada grafo
  pasos_elementales : PasosElementalesCompletos grafo

/-- In a complete ordered local channel, adjacency is exactly the
minimal step of the cell. -/
theorem CanalLocalNoRamificadoOrdenado.adj_iff_paso
    {d : ℕ} (C : CanalLocalNoRamificadoOrdenado d) {i j : Fin d} :
    C.grafo.Adj i j ↔ TransportePosicion.PasoMinimo i j := by
  exact ⟨fun h => C.localidad_ordenada h,
    fun h => C.pasos_elementales h⟩

/-- Minimality theorem: ordered locality and complete elementary steps
force the support to be exactly `pathGraph d`. -/
theorem canal_local_no_ramificado_es_pathGraph
    {d : ℕ} (C : CanalLocalNoRamificadoOrdenado d) :
    C.grafo = SimpleGraph.pathGraph d := by
  ext i j
  rw [C.adj_iff_paso]
  simpa [TransportePosicion.GrafoTP] using
    (TransportePosicion.pasoMinimo_iff_adj (d := d) (i := i) (j := j))

/-- Isomorphic version of the same closure. -/
theorem canal_local_no_ramificado_iso_pathGraph
    {d : ℕ} (C : CanalLocalNoRamificadoOrdenado d) :
    Nonempty (C.grafo ≃g SimpleGraph.pathGraph d) := by
  rw [canal_local_no_ramificado_es_pathGraph C]
  exact ⟨SimpleGraph.Iso.refl⟩

/-- The canonical channel `T_d/P_d` directly satisfies the ordered local
certificate: it has no jumps and omits no elementary steps. -/
def canalTPLocalNoRamificado (d : ℕ) :
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

/-- No channel that already satisfies the ordered local certificate can
omit an elementary step: "there is no local simplification simpler than
`pathGraph d`". -/
theorem no_hay_canal_local_mas_simple_que_Pd
    {d : ℕ} (C : CanalLocalNoRamificadoOrdenado d) :
    ¬ OmitePasoElemental C.grafo := by
  rintro ⟨i, j, hpaso, hno⟩
  exact hno (C.pasos_elementales hpaso)

/-- Closure: the canonical support `T_d/P_d` is `pathGraph d`, and any
local attempt to make it "simpler" loses an elementary step. -/
theorem cierre_minimalidad_local_TP (d : ℕ) :
    (canalTPLocalNoRamificado d).grafo = SimpleGraph.pathGraph d ∧
      ¬ OmitePasoElemental (canalTPLocalNoRamificado d).grafo := by
  exact ⟨canal_local_no_ramificado_es_pathGraph
      (canalTPLocalNoRamificado d),
    no_hay_canal_local_mas_simple_que_Pd
      (canalTPLocalNoRamificado d)⟩

end CanalPreFuerza
