/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Relativity.Fermions.Weyl.LeftHanded
public import Physlib.Relativity.Fermions.Weyl.RightHanded
public import Physlib.Relativity.LorentzGroup.Boosts.Axis
/-!
# The boost weights of a Weyl spinor

Along the `z`-axis the `SL(2,ℂ)` boost is the diagonal matrix `diag (t, t⁻¹)`, so both
Weyl bases are bases of boost eigenvectors: the first component carries weight `+1` and
the second weight `-1`.  A Weyl spinor is a half-vector (A).

Along a general axis the boost is the `z`-boost conjugated by `SL2C.rotationZToAxis`, so the
columns of that rotation are boost eigenvectors of the same weights. Section B records them as
explicit coefficient vectors on the standard Weyl basis, for a left-handed index and, through
the conjugate boost, for a right-handed one, with the matrices writing the standard basis back.
Their normalisation is not uniform across the axes and is kept as it is. Section C is the weight
of a pair of Weyl indices.

-/

@[expose] public section

namespace Lorentz

open Matrix MatrixGroups

/-!

## A. The boost weight along the `z`-axis

-/

/-- The boost weight of a Weyl-spinor index. Along the `z`-axis the `SL(2,ℂ)` boost is
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

/-!

## B. The Weyl weight bases along a spatial axis

-/

/-- The axis-`i` Weyl weight basis of a left-handed index, written as coefficient
  vectors on the standard Weyl basis. -/
def weylCoeff (i : Fin 3) (κ α : Fin 2) : ℂ :=
  if i = 0 then (if κ = 0 then 1 else if α = 0 then -1 else 1)
  else if i = 1 then (if κ = α then 1 else Complex.I)
  else (if κ = α then 1 else 0)

/-- The axis-`i` Weyl weight basis of a right-handed index: the entrywise conjugate of
  the left-handed one. -/
def weylCoeffC (i : Fin 3) (κ α : Fin 2) : ℂ :=
  if i = 0 then (if κ = 0 then 1 else if α = 0 then -1 else 1)
  else if i = 1 then (if κ = α then 1 else -Complex.I)
  else (if κ = α then 1 else 0)

/-- The standard Weyl basis of a left-handed index written back in the axis-`i` weight
  basis. -/
noncomputable def weylCoeffInv (i : Fin 3) (α κ : Fin 2) : ℂ :=
  if i = 0 then (if κ = 0 then 2⁻¹ else if α = 0 then -2⁻¹ else 2⁻¹)
  else if i = 1 then (if κ = α then 2⁻¹ else -(2⁻¹ * Complex.I))
  else (if κ = α then 1 else 0)

/-- The standard Weyl basis of a right-handed index written back in the axis-`i` weight
  basis. -/
noncomputable def weylCoeffInvC (i : Fin 3) (α κ : Fin 2) : ℂ :=
  if i = 0 then (if κ = 0 then 2⁻¹ else if α = 0 then -2⁻¹ else 2⁻¹)
  else if i = 1 then (if κ = α then 2⁻¹ else 2⁻¹ * Complex.I)
  else (if κ = α then 1 else 0)

/-- The left-handed weight basis is a basis: the two coefficient matrices are inverse. -/
lemma sum_weylCoeffInv_mul (i : Fin 3) (α β : Fin 2) :
    ∑ κ, weylCoeffInv i α κ * weylCoeff i κ β = if α = β then 1 else 0 := by
  fin_cases i <;> fin_cases α <;> fin_cases β <;>
    simp [weylCoeff, weylCoeffInv, Fin.sum_univ_two] <;>
    norm_num [Complex.ext_iff]

/-- The right-handed weight basis is a basis: the two coefficient matrices are inverse. -/
lemma sum_weylCoeffInvC_mul (i : Fin 3) (α β : Fin 2) :
    ∑ κ, weylCoeffInvC i α κ * weylCoeffC i κ β = if α = β then 1 else 0 := by
  fin_cases i <;> fin_cases α <;> fin_cases β <;>
    simp [weylCoeffC, weylCoeffInvC, Fin.sum_univ_two] <;>
    norm_num [Complex.ext_iff]

/-- The left-handed weight basis diagonalises the axis-`i` boost, with the weights
  `weylWeight`. -/
lemma sum_boostAxis_weylCoeff (i : Fin 3) (κ β : Fin 2) {t : ℝ} (ht : t ≠ 0) :
    ∑ α, (SL2C.boostAxis i t ht).1 β α * weylCoeff i κ α
      = ((t : ℝ) : ℂ) ^ (weylWeight κ) * weylCoeff i κ β := by
  have htc : ((t : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  fin_cases i <;> fin_cases κ <;> fin_cases β
  all_goals simp [SL2C.boostAxis, weylCoeff, weylWeight, Fin.sum_univ_two]
  all_goals try field_simp
  all_goals try simp only [Complex.I_sq]
  all_goals try ring

/-- The right-handed weight basis diagonalises the conjugate of the axis-`i` boost,
  with the weights `weylWeight`. -/
lemma sum_boostAxis_weylCoeffC (i : Fin 3) (κ β : Fin 2) {t : ℝ} (ht : t ≠ 0) :
    ∑ α, star ((SL2C.boostAxis i t ht).1 β α) * weylCoeffC i κ α
      = ((t : ℝ) : ℂ) ^ (weylWeight κ) * weylCoeffC i κ β := by
  have htc : ((t : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  simp only [SL2C.star_boostAxis_apply]
  fin_cases i <;> fin_cases κ <;> fin_cases β
  all_goals simp [SL2C.boostAxis, weylCoeffC, weylWeight, Fin.sum_univ_two]
  all_goals try field_simp
  all_goals try simp only [Complex.I_sq]
  all_goals try ring

/-!

## C. The weight of a pair of Weyl indices

-/

/-- The boost weight of a pair of Weyl weight indices: the sum of the two. -/
def pairWeight (κ : Fin 2 × Fin 2) : ℤ := weylWeight κ.1 + weylWeight κ.2

/-- The weight-zero pairs are the two mixed pairs. -/
lemma sum_weightZeroFilter {M : Type*} [AddCommMonoid M] (f : Fin 2 × Fin 2 → M) :
    ∑ κ ∈ Finset.univ.filter (fun κ : Fin 2 × Fin 2 => pairWeight κ = 0), f κ
      = f (0, 1) + f (1, 0) := by
  rw [show (Finset.univ.filter (fun κ : Fin 2 × Fin 2 => pairWeight κ = 0))
      = {(0, 1), (1, 0)} from by decide, Finset.sum_insert (by decide),
    Finset.sum_singleton]

end Lorentz
