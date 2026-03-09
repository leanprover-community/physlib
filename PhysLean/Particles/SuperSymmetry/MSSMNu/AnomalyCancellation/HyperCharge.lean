/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import PhysLean.Particles.SuperSymmetry.MSSMNu.AnomalyCancellation.Basic
/-!
# Hypercharge in MSSM.

Relevant definitions for the MSSM hypercharge.

-/

@[expose] public section

namespace MSSMACC
open MSSMCharges
open MSSMACCs
open BigOperators

/-- The hypercharge as an element of `MSSMACC.charges`. -/
def YAsCharge : MSSMACC.Charges := toSpecies.invFun
  ⟨fun s => fun i =>
    match s, i with
    | 0, 0 => 1
    | 0, 1 => 1
    | 0, 2 => 1
    | 1, 0 => -4
    | 1, 1 => -4
    | 1, 2 => -4
    | 2, 0 => 2
    | 2, 1 => 2
    | 2, 2 => 2
    | 3, 0 => -3
    | 3, 1 => -3
    | 3, 2 => -3
    | 4, 0 => 6
    | 4, 1 => 6
    | 4, 2 => 6
    | 5, 0 => 0
    | 5, 1 => 0
    | 5, 2 => 0,
  fun s =>
    match s with
    | 0 => -3
    | 1 => 3⟩

/-- The hypercharge as an element of `MSSMACC.Sols`. -/
def Y : MSSMACC.Sols :=
  MSSMACC.AnomalyFreeMk YAsCharge
    (by with_unfolding_all rfl) (by with_unfolding_all rfl)
    (by with_unfolding_all rfl) (by with_unfolding_all rfl) (by with_unfolding_all rfl)
    (by with_unfolding_all rfl)

end MSSMACC
