/-
Copyright (c) 2026 Daniel Leonforte. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Leonforte
-/
module

public import PhyslibAlpha.QuantumMechanics.AngularMomentum.WignerEckart

/-!

# Selection rules for multipole transitions

The triangle rule for tensor operators in the usual inequality form, and the angular momentum
and parity selection rules for electromagnetic multipole transitions.

## i. Overview

By the Wigner–Eckart theorem a nonzero tensor operator of rank `k` from `V(m)` to `V(p)` requires
`p = k + m - 2j` for some `j ≤ min k m`. In doubled units (`k = 2λ`, `m = 2Iᵢ`, `p = 2I_f`) this is
the triangle rule `|Iᵢ - I_f| ≤ λ ≤ Iᵢ + I_f` together with `Iᵢ + I_f + λ ∈ ℕ`, written here as
`TriangleRule k m p`.

For an electromagnetic multipole transition of order `λ` the photon carries angular momentum
`λ ≥ 1`, and the transition operator has parity `(-1)^λ` (electric, `Eλ`) or `(-1)^(λ+1)`
(magnetic, `Mλ`). These two facts are standard input and are not derived here; the parity
condition is the elementary statement `parity_eq_of_ne_zero`. `IsAllowedMultipole` collects the
three conditions. As an example, the file checks the three branches that depopulate the
`16⁺` isomer of `¹⁷⁸Hf` (`E3` to `13⁻`, `M4` to `12⁻`, `E5` to `11⁻`) and the `E1` decay of the
`8⁻` isomer, and shows that each is the lowest allowed multipole. The hindrance of these
transitions by the `K` quantum number is a separate effect and not a selection rule.

## ii. Key results

- `TriangleRule` and `exists_eq_iff_triangleRule` translate the Clebsch–Gordan condition.
- `IsTensorOperator.triangleRule` is the triangle rule for nonzero tensor operators.
- `parity_eq_of_ne_zero` is the parity rule.
- `IsAllowedMultipole` combines the rules; `hf178_primary_branches_allowed` and the lemmas after
  it are worked examples.

## iii. Table of contents

- A. The triangle rule
- B. Parity and multipole transitions
- C. Example: the decay of the ¹⁷⁸ᵐ²Hf isomer

## iv. References

- J. M. Blatt and V. F. Weisskopf, *Theoretical Nuclear Physics*, Wiley (1952), chapter XII.
- ENSDF, ¹⁷⁸Hf adopted levels and gammas, E. Achterberg, O. A. Capurro, G. V. Marti,
  Nucl. Data Sheets 110, 1473 (2009).

## A. The triangle rule

-/

@[expose] public section

noncomputable section

namespace PhyslibAlpha.Sl2

open StandardSl2Module

/-- The triangle rule in doubled units: `p ≤ k + m`, `k ≤ m + p`, `m ≤ k + p` and `k + m + p`
even. For `k = 2λ`, `m = 2Iᵢ`, `p = 2I_f` this is `|Iᵢ - I_f| ≤ λ ≤ Iᵢ + I_f` with
`Iᵢ + I_f + λ` an integer. -/
def TriangleRule (k m p : ℕ) : Prop :=
  p ≤ k + m ∧ k ≤ m + p ∧ m ≤ k + p ∧ (k + m + p) % 2 = 0

instance (k m p : ℕ) : Decidable (TriangleRule k m p) := by
  unfold TriangleRule
  infer_instance

/-- `p` occurs in the Clebsch–Gordan decomposition of `V(k) ⊗ V(m)` exactly when the triangle
rule holds. -/
lemma exists_eq_iff_triangleRule {k m p : ℕ} :
    (∃ j : Fin (min k m + 1), k + m - 2 * (j : ℕ) = p) ↔ TriangleRule k m p := by
  constructor
  · rintro ⟨j, hj⟩
    have := j.isLt
    unfold TriangleRule
    omega
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨⟨(k + m - p) / 2, by omega⟩, by simp only; omega⟩

/-- **Triangle rule.** A nonzero tensor operator of rank `k` from `V(m)` to `V(p)` satisfies
`TriangleRule k m p`. -/
lemma IsTensorOperator.triangleRule {K : Type*} [Field K] [CharZero K] {k m p : ℕ}
    (hkm : 0 < k + m)
    {T : StandardSl2Module K k →ₗ[K] StandardSl2Module K m →ₗ[K] StandardSl2Module K p}
    (hT : IsTensorOperator T) (hT0 : T ≠ 0) : TriangleRule k m p := by
  by_contra h
  exact hT0 (hT.eq_zero_of_forall_ne hkm fun j hj => h (exists_eq_iff_triangleRule.mp ⟨j, hj⟩))

/-!

## B. Parity and multipole transitions

-/

/-- **Parity rule.** If a linear map between states of definite parities `πᵢ` and `π_f` has
parity `π_T`, in the sense `π_f • T = π_T • πᵢ • T`, and is nonzero, then `π_f = π_T * πᵢ`. -/
lemma parity_eq_of_ne_zero {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] {T : V →ₗ[K] W} {πi πf πT : K}
    (h : πf • T = πT • πi • T) (hT : T ≠ 0) : πf = πT * πi := by
  rw [smul_smul, ← sub_eq_zero, ← sub_smul] at h
  exact sub_eq_zero.mp ((smul_eq_zero.mp h).resolve_right hT)

/-- Electric and magnetic multipoles. -/
inductive MultipoleType
  /-- Electric multipole `Eλ`. -/
  | electric
  /-- Magnetic multipole `Mλ`. -/
  | magnetic
  deriving DecidableEq

/-- The parity of a multipole operator of order `λ`: `(-1)^λ` for `Eλ`, `(-1)^(λ+1)` for `Mλ`. -/
def MultipoleType.parity : MultipoleType → ℕ → ℤ
  | .electric, l => (-1) ^ l
  | .magnetic, l => (-1) ^ (l + 1)

/-- A multipole transition of type `t` and order `l` between a state of spin `Iᵢ` and parity
`πᵢ` and a state of spin `I_f` and parity `π_f` (spins in doubled units `twoIi = 2Iᵢ`,
`twoIf = 2I_f`) is allowed if `l ≥ 1`, the triangle rule holds and the parities match. -/
def IsAllowedMultipole (twoIi twoIf : ℕ) (πi πf : ℤ) (t : MultipoleType) (l : ℕ) : Prop :=
  1 ≤ l ∧ TriangleRule (2 * l) twoIi twoIf ∧ πf = t.parity l * πi

instance (twoIi twoIf : ℕ) (πi πf : ℤ) (t : MultipoleType) (l : ℕ) :
    Decidable (IsAllowedMultipole twoIi twoIf πi πf t l) := by
  unfold IsAllowedMultipole
  infer_instance

/-!

## C. Example: the decay of the ¹⁷⁸ᵐ²Hf isomer

Spins in doubled units: `16⁺` is `(32, 1)`, `13⁻` is `(26, -1)`, `12⁻` is `(24, -1)`, `11⁻` is
`(22, -1)`, and the `8⁻` and `8⁺` levels of the `4 s` isomer decay are `(16, -1)` and `(16, 1)`.

-/

/-- The three branches depopulating the `16⁺` isomer are allowed: `E3` to `13⁻`, `M4` to `12⁻`,
`E5` to `11⁻`. -/
lemma hf178_primary_branches_allowed :
    IsAllowedMultipole 32 26 1 (-1) .electric 3 ∧ IsAllowedMultipole 32 24 1 (-1) .magnetic 4 ∧
      IsAllowedMultipole 32 22 1 (-1) .electric 5 := by
  decide

/-- `E3` is the lowest allowed multipole for `16⁺ → 13⁻`. -/
lemma hf178_E3_lowest : ∀ l < 3, ¬ IsAllowedMultipole 32 26 1 (-1) .electric l ∧
    ¬ IsAllowedMultipole 32 26 1 (-1) .magnetic l := by
  decide

/-- `M4` is the lowest allowed multipole for `16⁺ → 12⁻`; `E4` is forbidden by parity. -/
lemma hf178_M4_lowest : (∀ l < 4, ¬ IsAllowedMultipole 32 24 1 (-1) .electric l ∧
    ¬ IsAllowedMultipole 32 24 1 (-1) .magnetic l) ∧
    ¬ IsAllowedMultipole 32 24 1 (-1) .electric 4 := by
  decide

/-- `E5` is the lowest allowed multipole for `16⁺ → 11⁻`. -/
lemma hf178_E5_lowest : (∀ l < 5, ¬ IsAllowedMultipole 32 22 1 (-1) .electric l ∧
    ¬ IsAllowedMultipole 32 22 1 (-1) .magnetic l) ∧
    ¬ IsAllowedMultipole 32 22 1 (-1) .magnetic 5 := by
  decide

/-- The `8⁻ → 8⁺` decay of the `4 s` isomer is `E1`, and `M1` is forbidden by parity. -/
lemma hf178_E1_8minus : IsAllowedMultipole 16 16 (-1) 1 .electric 1 ∧
    ¬ IsAllowedMultipole 16 16 (-1) 1 .magnetic 1 := by
  decide

end PhyslibAlpha.Sl2
