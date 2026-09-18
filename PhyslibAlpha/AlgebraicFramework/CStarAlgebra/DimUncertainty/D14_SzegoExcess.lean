/-
Copyright (c) 2026 Eduardo Nava-Hernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eduardo Nava-Hernández, José Arturo Nava-Hernández, Gerardo Gabriel Nava Gómez
-/
module

public import PhyslibAlpha.AlgebraicFramework.CStarAlgebra.DimUncertainty.D9_Monotonia

/-!
# The excess over the Szegő limit

Direct arithmetic corollary of monotonicity (`D9_Monotonia.lean`) and
the Szegő limit (`D8_Szego.lean`): the "excess" `Cinf - CNava(d)` — how
far `CNava(d)` is from reaching the limit `C∞` — is positive, maximal
exactly at `d = 4`, strictly decreasing in `d`, and dissolves to `0`.
Not a new pillar: it is the same chain from `D9_Monotonia.lean` read
from the remainder side instead of the value itself.
-/

@[expose] public section

open Filter
open scoped Topology

namespace Gnomon

/-- The coherence excess: how far `CNava(d)` is from reaching the
Szegő limit `C∞`. -/
noncomputable def excesoBrecha (d : ℕ) : ℝ := Cinf - CNava d

/-- The excess is always positive: `CNava(d)` never reaches `C∞` at
finite `d`. -/
theorem excesoBrecha_pos (d : ℕ) (hd : 4 ≤ d) : 0 < excesoBrecha d := by
  unfold excesoBrecha
  linarith [CNava_lt_Cinf d hd]

/-- The excess is strictly decreasing in `d`, inherited from the
monotonicity of `CNava`. -/
theorem excesoBrecha_strictAnti {a b : ℕ} (ha : 4 ≤ a) (hb : 4 ≤ b) (hab : a < b) :
    excesoBrecha b < excesoBrecha a := by
  unfold excesoBrecha
  linarith [CNava_strictMonoOn_ge_four ha hb hab]

/-- The maximum excess over the entire `d ≥ 4` tail is attained exactly at
`d = 4`: the global minimum of `CNava` is the ceiling of the excess. -/
theorem excesoBrecha_le_four (d : ℕ) (hd : 4 ≤ d) :
    excesoBrecha d ≤ excesoBrecha 4 := by
  unfold excesoBrecha
  linarith [CNava_four_le d hd]

/-- The excess vanishes completely: `Cinf − CNava(d) → 0`, bounded above
by `excesoBrecha 4` and driven to `0` by the Szegő limit. -/
theorem excesoBrecha_tendsto_zero :
    Tendsto (fun d : ℕ => excesoBrecha d) atTop (𝓝 0) := by
  unfold excesoBrecha
  have h : Tendsto (fun d : ℕ => Cinf - CNava d) atTop (𝓝 (Cinf - Cinf)) :=
    limite_szego_CNava.const_sub Cinf
  simpa using h

end Gnomon
