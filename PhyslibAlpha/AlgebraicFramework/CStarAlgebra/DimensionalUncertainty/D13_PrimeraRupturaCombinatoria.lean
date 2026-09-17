/-
Copyright (c) 2026 Eduardo Nava-Hernández, José Arturo Nava-Hernández, Gerardo Gabriel Nava Gómez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eduardo Nava-Hernández, José Arturo Nava-Hernández, Gerardo Gabriel Nava Gómez
-/
module

public import PhyslibAlpha.AlgebraicFramework.HilbertSpace.PathSpectralGap.D3_GrafoCamino
public import PhyslibAlpha.AlgebraicFramework.HilbertSpace.PathSpectralGap.D7_Niven

@[expose] public section

/-!
# La primera ruptura combinatoria es `d = 4`

Complemento combinatorio al teorema de Niven (`D7_Niven.lean`): la
saturación espectral de Robertson–Schrödinger sobre `P_d` deja de
cumplirse exactamente cuando `P_d` adquiere su primera arista *interior*
(una arista entre dos vértices que no son extremos del camino), y esa
coincidencia ocurre exactamente en `d = 4`.

Dos rutas independientes hacia la misma dimensión:

* **espectral** (`D7_Niven.lean`): `cos²(π/(d+1)) = (d-1)/4 ↔ d ∈ {2,3}`;
* **combinatoria** (aquí): `P_d` tiene una arista entre dos vértices
  interiores si y sólo si `4 ≤ d`.

`primera_ruptura_iff_dimension_cuatro` certifica que ambas rutas señalan
la misma dimensión `d = 4`, sin usar ninguna ecuación espectral en la
mitad combinatoria.
-/

namespace PrimeraRuptura

open SimpleGraph

/-- Ecuación aritmético-espectral que representa la saturación del camino
(la misma de `Gnomon.saturacion_iff`, escrita como predicado). -/
def SaturacionCamino (d : ℕ) : Prop :=
  Real.cos (Real.pi / (d + 1)) ^ 2 = ((d : ℝ) - 1) / 4

/-- Ruptura: negación de la igualdad de saturación del camino. -/
def RupturaCamino (d : ℕ) : Prop := ¬ SaturacionCamino d

/-- Desde la dimensión mínima `2`, la ruptura ocurre exactamente desde `4`. -/
theorem ruptura_camino_iff_cuatro_le (d : ℕ) (hd : 2 ≤ d) :
    RupturaCamino d ↔ 4 ≤ d := by
  unfold RupturaCamino SaturacionCamino
  rw [Gnomon.saturacion_iff d hd]
  omega

/-- La dimensión cuatro ya está en ruptura. -/
theorem ruptura_camino_cuatro : RupturaCamino 4 := by
  exact (ruptura_camino_iff_cuatro_le 4 (by norm_num)).2 (by norm_num)

/-- Predicado puramente combinatorio de vértice no terminal del camino. -/
def VerticeInterior {d : ℕ} (i : Fin d) : Prop :=
  0 < i.val ∧ i.val + 1 < d

/-- Existe una arista genuinamente interior cuando dos vértices no
terminales del camino son adyacentes. -/
def TieneAristaInterior (d : ℕ) : Prop :=
  ∃ i j : Fin d,
    VerticeInterior i ∧ VerticeInterior j ∧
      (SimpleGraph.pathGraph d).Adj i j

/-- El camino tiene una arista interior si y sólo si posee al menos cuatro
vértices. Esta equivalencia no usa Robertson ni la ecuación de saturación:
es pura combinatoria del camino. -/
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

/-- Coincidencia central: dentro del régimen `d ≥ 2`, tener una arista entre
dos vértices interiores equivale exactamente a romper la saturación. Las dos
caras se demuestran por rutas independientes: combinatoria y espectral. -/
theorem transporte_interior_iff_ruptura (d : ℕ) (hd : 2 ≤ d) :
    TieneAristaInterior d ↔ RupturaCamino d := by
  exact (tiene_arista_interior_iff_cuatro_le d).trans
    (ruptura_camino_iff_cuatro_le d hd).symm

/-- La primera ruptura es una propiedad de orden: hay ruptura en `d`, y `d`
es menor o igual que cualquier otra dimensión admisible que también rompa. -/
def EsPrimeraRuptura (d : ℕ) : Prop :=
  2 ≤ d ∧ RupturaCamino d ∧
    ∀ n : ℕ, 2 ≤ n → RupturaCamino n → d ≤ n

/-- Caracterización dimensional: la primera ruptura es exactamente `d = 4`. -/
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
