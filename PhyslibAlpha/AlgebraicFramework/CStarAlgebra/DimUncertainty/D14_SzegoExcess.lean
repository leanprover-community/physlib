/-
Copyright (c) 2026 Eduardo Nava-Hernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eduardo Nava-Hernández, José Arturo Nava-Hernández, Gerardo Gabriel Nava Gómez
-/
module

public import PhyslibAlpha.AlgebraicFramework.CStarAlgebra.DimUncertainty.D9_Monotonia

/-!
# El exceso sobre el límite de Szegő

Corolario aritmético directo de la monotonía (`D9_Monotonia.lean`) y el
límite de Szegő (`D8_Szego.lean`): el "exceso" `Cinf - CNava(d)` —cuánto
le falta a `CNava(d)` para alcanzar el límite `C∞`— es positivo, máximo
exactamente en `d = 4`, estrictamente decreciente en `d`, y se disuelve a
`0`. No es un pilar nuevo: es la misma cadena de `D9_Monotonia.lean` leída
desde el lado del remanente en vez del valor mismo.
-/

@[expose] public section

open Filter
open scoped Topology

namespace Gnomon

/-- El exceso de coherencia: cuánto le falta a `CNava(d)` para alcanzar el
límite de Szegő `C∞`. -/
noncomputable def excesoBrecha (d : ℕ) : ℝ := Cinf - CNava d

/-- El exceso es siempre positivo: `CNava(d)` nunca alcanza `C∞` a `d`
finito. -/
theorem excesoBrecha_pos (d : ℕ) (hd : 4 ≤ d) : 0 < excesoBrecha d := by
  unfold excesoBrecha
  linarith [CNava_lt_Cinf d hd]

/-- El exceso es estrictamente decreciente en `d`, heredado de la
monotonía de `CNava`. -/
theorem excesoBrecha_strictAnti {a b : ℕ} (ha : 4 ≤ a) (hb : 4 ≤ b) (hab : a < b) :
    excesoBrecha b < excesoBrecha a := by
  unfold excesoBrecha
  linarith [CNava_strictMonoOn_ge_four ha hb hab]

/-- El exceso máximo de toda la cola `d ≥ 4` se alcanza exactamente en
`d = 4`: el mínimo global de `CNava` es el techo del exceso. -/
theorem excesoBrecha_le_four (d : ℕ) (hd : 4 ≤ d) :
    excesoBrecha d ≤ excesoBrecha 4 := by
  unfold excesoBrecha
  linarith [CNava_four_le d hd]

/-- El exceso se apaga por completo: `Cinf − CNava(d) → 0`, acotado arriba
por `excesoBrecha 4` y llevado a `0` por el límite de Szegő. -/
theorem excesoBrecha_tendsto_zero :
    Tendsto (fun d : ℕ => excesoBrecha d) atTop (𝓝 0) := by
  unfold excesoBrecha
  have h : Tendsto (fun d : ℕ => Cinf - CNava d) atTop (𝓝 (Cinf - Cinf)) :=
    limite_szego_CNava.const_sub Cinf
  simpa using h

end Gnomon
