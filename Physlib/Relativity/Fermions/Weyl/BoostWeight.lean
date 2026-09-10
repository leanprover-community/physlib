/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Relativity.Fermions.Weyl.LeftHanded
public import Physlib.Relativity.Fermions.Weyl.RightHanded
public import Physlib.Relativity.LorentzGroup.Boosts.WeightGrading
/-!
# The boost weights of a Weyl spinor

Along the `z`-axis the `SL(2,ℂ)` boost is the diagonal matrix `diag (t, t⁻¹)`, so both
Weyl bases are bases of boost eigenvectors: the first component carries weight `+1` and
the second weight `-1`.  A Weyl spinor is a half-vector.

-/

@[expose] public section

namespace Lorentz

open Matrix MatrixGroups

/-- **The boost weight of a Weyl-spinor index.**  Along the `z`-axis the `SL(2,ℂ)` boost is
  the diagonal matrix `diag (t, t⁻¹)`, so the first spinor component carries weight `+1` and
  the second weight `-1`; a Weyl spinor is a half-vector. -/
def weylWeight (k : Fin 2) : ℤ := if k = 0 then 1 else -1

/-- The negated Weyl weight, which is what a dual spinor index carries, is `±1`. -/
lemma neg_weylWeight_mem (k : Fin 2) : -(weylWeight k) ∈ ({-1, 1} : Finset ℤ) := by
  fin_cases k <;> simp [weylWeight]

/-- The right-handed Weyl basis diagonalises the `z`-boost, with weights `±1`. -/
lemma rightHandedWeyl_rep_boostAxis_two_basis (t : ℝ) (ht : t ≠ 0) (k : Fin 2) :
    Fermion.RightHandedWeyl.rep (SL2C.boostAxis 2 t ht) (Fermion.RightHandedWeyl.basis k)
      = ((t : ℝ) : ℂ) ^ (weylWeight k) • Fermion.RightHandedWeyl.basis k := by
  rw [Fermion.RightHandedWeyl.rep_apply_basis]
  fin_cases k <;>
    simp [weylWeight, Fin.sum_univ_two]

/-- The left-handed Weyl basis diagonalises the `z`-boost, with weights `±1`. -/
lemma leftHandedWeyl_rep_boostAxis_two_basis (t : ℝ) (ht : t ≠ 0) (k : Fin 2) :
    Fermion.LeftHandedWeyl.rep (SL2C.boostAxis 2 t ht) (Fermion.LeftHandedWeyl.basis k)
      = ((t : ℝ) : ℂ) ^ (weylWeight k) • Fermion.LeftHandedWeyl.basis k := by
  rw [Fermion.LeftHandedWeyl.rep_apply_basis]
  fin_cases k <;>
    simp [weylWeight, Fin.sum_univ_two]

end Lorentz
