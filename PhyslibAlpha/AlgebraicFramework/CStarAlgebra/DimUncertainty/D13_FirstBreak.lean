/-
Copyright (c) 2026 Eduardo Nava-Hernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eduardo Nava-Hernández, José Arturo Nava-Hernández, Gerardo Gabriel Nava Gómez
-/
module

public import PhyslibAlpha.AlgebraicFramework.HilbertSpace.PathGap.D3_GrafoCamino
public import PhyslibAlpha.AlgebraicFramework.HilbertSpace.PathGap.D7_Niven

/-!
# The first combinatorial break is `d = 4`

Combinatorial complement to the Niven theorem (`D7_Niven.lean`):
Robertson–Schrödinger spectral saturation on `P_d` fails exactly when
`P_d` acquires its first *interior* edge (an edge between two vertices
that are not endpoints of the path), and that coincidence occurs
exactly at `d = 4`.

Two independent routes to the same dimension:

* **spectral** (`D7_Niven.lean`): `cos²(π/(d+1)) = (d-1)/4 ↔ d ∈ {2,3}`;
* **combinatorial** (here): `P_d` has an edge between two interior
  vertices if and only if `4 ≤ d`.

`primera_ruptura_iff_dimension_cuatro` certifies that both routes point
to the same dimension `d = 4`, without using any spectral equation in
the combinatorial half.
-/

@[expose] public section

namespace PrimeraRuptura

open SimpleGraph

/-- Arithmetic-spectral equation representing path saturation
(the same as `Gnomon.saturacion_iff`, written as a predicate). -/
def SaturacionCamino (d : ℕ) : Prop :=
  Real.cos (Real.pi / (d + 1)) ^ 2 = ((d : ℝ) - 1) / 4

/-- Break: negation of the path saturation equality. -/
def RupturaCamino (d : ℕ) : Prop := ¬ SaturacionCamino d

/-- From the minimum dimension `2`, the break occurs exactly from `4`. -/
theorem ruptura_camino_iff_cuatro_le (d : ℕ) (hd : 2 ≤ d) :
    RupturaCamino d ↔ 4 ≤ d := by
  unfold RupturaCamino SaturacionCamino
  rw [Gnomon.saturacion_iff d hd]
  omega

/-- Dimension four is already in break. -/
theorem ruptura_camino_cuatro : RupturaCamino 4 := by
  exact (ruptura_camino_iff_cuatro_le 4 (by norm_num)).2 (by norm_num)

/-- Purely combinatorial predicate for non-terminal path vertices. -/
def VerticeInterior {d : ℕ} (i : Fin d) : Prop :=
  0 < i.val ∧ i.val + 1 < d

/-- A genuinely interior edge exists when two non-terminal
vertices of the path are adjacent. -/
def TieneAristaInterior (d : ℕ) : Prop :=
  ∃ i j : Fin d,
    VerticeInterior i ∧ VerticeInterior j ∧
      (SimpleGraph.pathGraph d).Adj i j

/-- The path has an interior edge iff it has at least four
vertices. This equivalence uses neither Robertson nor the saturation
equation: it is pure path combinatorics. -/
theorem tiene_arista_interior_iff_cuatro_le (d : ℕ) :
    TieneAristaInterior d ↔ 4 ≤ d := by
  constructor
  · rintro ⟨i, j, hi, hj, hadj⟩
    rcases hi with ⟨hi0, hiend⟩
    rcases hj with ⟨hj0, hjend⟩
    rw [SimpleGraph.pathGraph_adj] at hadj
    rcases hadj with hij | hji <;> omega
  · intro hd
    let i : Fin d := ⟨1, by omega⟩
    let j : Fin d := ⟨2, by omega⟩
    refine ⟨i, j, ?_, ?_, ?_⟩
    · simp [VerticeInterior, i]
      omega
    · simp [VerticeInterior, j]
      omega
    · rw [SimpleGraph.pathGraph_adj]
      exact Or.inl rfl

/-- Central coincidence: within the `d ≥ 2` regime, having an edge between
two interior vertices is exactly equivalent to breaking saturation. The two
faces are proved by independent routes: combinatorial and spectral. -/
theorem transporte_interior_iff_ruptura (d : ℕ) (hd : 2 ≤ d) :
    TieneAristaInterior d ↔ RupturaCamino d := by
  exact (tiene_arista_interior_iff_cuatro_le d).trans
    (ruptura_camino_iff_cuatro_le d hd).symm

/-- The first break is an order property: there is a break at `d`, and `d`
is less than or equal to every other admissible dimension that also breaks. -/
def EsPrimeraRuptura (d : ℕ) : Prop :=
  2 ≤ d ∧ RupturaCamino d ∧
    ∀ n : ℕ, 2 ≤ n → RupturaCamino n → d ≤ n

/-- Dimensional characterization: the first break is exactly `d = 4`. -/
theorem primera_ruptura_iff_dimension_cuatro (d : ℕ) :
    EsPrimeraRuptura d ↔ d = 4 := by
  constructor
  · rintro ⟨hd2, hdR, hmin⟩
    have h4d : 4 ≤ d := (ruptura_camino_iff_cuatro_le d hd2).1 hdR
    have hd4 : d ≤ 4 := hmin 4 (by norm_num) ruptura_camino_cuatro
    omega
  · rintro rfl
    refine ⟨by norm_num, ruptura_camino_cuatro, ?_⟩
    intro n hn2 hnR
    exact (ruptura_camino_iff_cuatro_le n hn2).1 hnR

end PrimeraRuptura
