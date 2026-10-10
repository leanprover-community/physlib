/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.QFT.QED.AnomalyCancellation.Basic
/-!
# The Pure U(1) case with 1 fermion

We show that in this case the charge must be zero.
-/

@[expose] public section

open Nat
open Finset

namespace PureU1

variable {n : ℕ}

namespace One

lemma solEqZero (S : (PureU1 1).LinSols) : S = 0 := by
  apply ACCSystemLinear.LinSols.ext
  funext i
  rw [Fin.fin_one_eq_zero i, ← Fin.sum_univ_one S.val]
  exact pureU1_linear S

end One

end PureU1
