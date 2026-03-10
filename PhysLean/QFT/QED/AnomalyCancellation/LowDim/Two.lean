/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import PhysLean.QFT.QED.AnomalyCancellation.Basic
/-!
# The Pure U(1) case with 2 fermions

We define an equivalence between `LinSols` and `Sols`.
-/

@[expose] public section

open Nat
open Finset

namespace PureU1

variable {n : ℕ}

namespace Two

/-- An equivalence between `LinSols` and `Sols`. -/
def equiv : (PureU1 2).LinSols ≃ (PureU1 2).Sols where
  toFun S := ⟨⟨S, fun i => Fin.elim0 i⟩, by
    have hLin := pureU1_linear S
    simp only [Fin.sum_univ_two, Fin.isValue] at hLin
    erw [accCube_explicit]
    simp only [Fin.sum_univ_two, Fin.isValue]
    rw [show S.val (0 : Fin 2) = - S.val (1 : Fin 2) from eq_neg_of_add_eq_zero_left hLin]
    ring⟩
  invFun S := S.1.1
  left_inv S := rfl
  right_inv S := rfl

end Two

end PureU1
