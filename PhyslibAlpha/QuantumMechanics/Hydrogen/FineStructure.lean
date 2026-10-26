/-
Copyright (c) 2026 Daniel Leonforte. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Leonforte
-/
module

public import PhyslibAlpha.QuantumMechanics.Hydrogen.RadialFunctions
public import PhyslibAlpha.QuantumMechanics.AngularMomentum.SpinOrbit

/-!

# The fine structure of hydrogen

The first-order fine structure of hydrogen: relativistic kinetic, spin–orbit and Darwin
corrections, evaluated with the radial expectation values of `RadialFunctions.lean` and the
spin–orbit eigenvalues of `SpinOrbit.lean`, add up to a shift that depends on `j` only.

## i. Overview

For the level `(ν, l, j)` with Bohr energy `E_ν = -Ry/ν²` and `α = k/(ℏc)` the three standard
first-order corrections are

- `E_rel = -⟨(E_ν - V)²⟩/(2mc²)` with `V = -k/r`,
- `E_SO = k/(2m²c²) ⟨1/r³⟩ ⟨L · S⟩`,
- `E_D = π k ℏ²/(2m²c²) |ψ(0)|²`, non-zero only for `l = 0`.

Inserting the proved values of `⟨1/r⟩`, `⟨1/r²⟩`, `⟨1/r³⟩`, `|R(0)|²` and of `L · S` on the
`j = l ± 1/2` states gives

`E_rel + E_SO + E_D = E_ν α²/ν² (ν/(j + 1/2) - 3/4)`

in both cases (`fineStructureShift_upper`, `fineStructureShift_lower`), so `2s_{1/2}` and
`2p_{1/2}` stay degenerate (`fineStructureShift_upper_eq_lower`).

What is taken as physical input: the three perturbation operators and the first-order formula
`ΔE = ⟨H'⟩`, the identity `⟨p⁴⟩ = 4m²⟨(E - V)²⟩`, and `|ψ(0)|² = |R(0)|²/(4π)`. What is proved:
the radial equation, the radial integrals, the `L · S` eigenvalues and the algebra that combines
them.

## ii. Key results

- `relativisticShift`, `spinOrbitShift`, `darwinShift`, `fineStructureShift`: the corrections.
- `fineStructureShift_upper`: the formula for `j = l + 1/2`, including `l = 0`.
- `fineStructureShift_lower`: the formula for `j = l - 1/2`, `l ≥ 1`.
- `fineStructureShift_upper_eq_lower`: the shift depends on `j` only.

## iii. Table of contents

- A. The three first-order corrections
- B. The fine-structure formula

## iv. References

- H. A. Bethe and E. E. Salpeter, *Quantum Mechanics of One- and Two-Electron Atoms*, Springer
  (1957).
- J. J. Sakurai and J. Napolitano, *Modern Quantum Mechanics*, 3rd ed., Cambridge University
  Press (2020), section 5.3.

## A. The three first-order corrections

-/

@[expose] public section

noncomputable section

namespace PhyslibAlpha.Hydrogen

open QuantumMechanics Constants

variable (H : HydrogenAtom 3) (c : SpeedOfLight)

/-- The fine-structure constant `α = k/(ℏ c)` of the atom. -/
def fineStructureConstant : ℝ := H.k / ((ℏ : ℝ) * c)

/-- The relativistic kinetic correction `-⟨p⁴⟩/(8 m³ c²) = -⟨(E - V)²⟩/(2 m c²)` in the state
`(ν, l)`, written with `p² = 2m(E - V)`, `V = -k/r` and the radial expectation values
`⟨1/r⟩ = ⟨1/ρ⟩/a`, `⟨1/r²⟩ = ⟨1/ρ²⟩/a²`. -/
def relativisticShift (ν l : ℕ) : ℝ :=
  -(1 / (2 * H.m * (c : ℝ) ^ 2)) * (H.energyLevel (ν - 1) ^ 2 +
    2 * H.energyLevel (ν - 1) * H.k * (radialMean ν l 1 / bohrRadius H) +
      H.k ^ 2 * (radialMean ν l 2 / bohrRadius H ^ 2))

/-- The spin–orbit correction `k/(2 m² c²) ⟨1/r³⟩ ⟨L · S⟩`, where `⟨L · S⟩ = ℏ² ls`. -/
def spinOrbitShift (ν l : ℕ) (ls : ℝ) : ℝ :=
  H.k * (ℏ : ℝ) ^ 2 * ls / (2 * H.m ^ 2 * (c : ℝ) ^ 2) * (radialMean ν l 3 / bohrRadius H ^ 3)

/-- The Darwin correction `π k ℏ²/(2 m² c²) |ψ(0)|²`, which is non-zero only for `s` states;
there `|ψ(0)|² = |R(0)|²/(4π)` with `R` normalised in physical units. -/
def darwinShift (ν l : ℕ) : ℝ :=
  if l = 0 then
    H.k * (ℏ : ℝ) ^ 2 / (8 * H.m ^ 2 * (c : ℝ) ^ 2) *
      (radialR ν 0 0 ^ 2 / radialMoment ν 0 0 / bohrRadius H ^ 3)
  else 0

/-- The total first-order fine-structure shift of the level `(ν, l)` with `⟨L · S⟩ = ℏ² ls`. -/
def fineStructureShift (ν l : ℕ) (ls : ℝ) : ℝ :=
  relativisticShift H c ν l + spinOrbitShift H c ν l ls + darwinShift H c ν l

/-!

## B. The fine-structure formula

-/

variable {H c} {ν l : ℕ}

lemma levelIndex_sub_one (hν : 1 ≤ ν) : HydrogenAtom.levelIndex 3 (ν - 1) = ν := by
  rw [HydrogenAtom.levelIndex_eq, Nat.cast_sub hν]
  push_cast
  ring

lemma ls_upper {ls : ℝ} (hls : (ls : ℂ) = Sl2.spinOrbitValue (2 * l) 1 0) : ls = l / 2 := by
  have h : (ls : ℂ) = ((l / 2 : ℝ) : ℂ) := by
    rw [hls, Sl2.spinOrbitValue, show 2 * l + 1 - 2 * 0 = 2 * l + 1 by omega]
    push_cast
    ring
  exact_mod_cast h

lemma ls_lower (hl1 : 1 ≤ l) {ls : ℝ} (hls : (ls : ℂ) = Sl2.spinOrbitValue (2 * l) 1 1) :
    ls = -((l : ℝ) + 1) / 2 := by
  have h : (ls : ℂ) = ((-((l : ℝ) + 1) / 2 : ℝ) : ℂ) := by
    rw [hls, Sl2.spinOrbitValue, show 2 * l + 1 - 2 * 1 = 2 * l - 1 by omega,
      Nat.cast_sub (show 1 ≤ 2 * l by omega)]
    push_cast
    ring
  exact_mod_cast h

/-- **Fine structure, `j = l + 1/2`.** With `⟨L · S⟩/ℏ²` the eigenvalue of `L · S` on the
`j = l + 1/2` string (`Sl2.dot_coupled_stringVec`), the three corrections add up to
`E_ν α²/ν² (ν/(j + 1/2) - 3/4)`. For `l = 0` the spin–orbit term vanishes and the Darwin term
takes its place. -/
lemma fineStructureShift_upper (hk : 0 < H.k) (hl : l < ν) {ls : ℝ}
    (hls : (ls : ℂ) = Sl2.spinOrbitValue (2 * l) 1 0) :
    fineStructureShift H c ν l ls = H.energyLevel (ν - 1) * fineStructureConstant H c ^ 2 /
      (ν : ℝ) ^ 2 * ((ν : ℝ) / ((l + 1 / 2 : ℝ) + 1 / 2) - 3 / 4) := by
  rw [ls_upper hls]
  have hm := H.m_pos.ne'
  have hk0 := hk.ne'
  have hℏ := ℏ_ne_zero
  have hc := c.val_ne_zero
  have hν : (ν : ℝ) ≠ 0 := by exact_mod_cast (show ν ≠ 0 by omega)
  rcases Nat.eq_zero_or_pos l with rfl | hl1
  · simp only [fineStructureShift, relativisticShift, spinOrbitShift, darwinShift, ↓reduceIte,
      radialMean_one hl, radialMean_two hl, radialR_zero_sq_div hl, Nat.cast_zero, zero_div,
      mul_zero, zero_mul, add_zero]
    rw [HydrogenAtom.energyLevel_eq, levelIndex_sub_one (by omega),
      HydrogenAtom.rydbergEnergy_eq, fineStructureConstant, bohrRadius]
    field_simp
    ring
  · have hl0 : (l : ℝ) ≠ 0 := by exact_mod_cast hl1.ne'
    simp only [fineStructureShift, relativisticShift, spinOrbitShift, darwinShift,
      hl1.ne', ↓reduceIte, radialMean_one hl, radialMean_two hl, radialMean_three hl hl1, add_zero]
    rw [HydrogenAtom.energyLevel_eq, levelIndex_sub_one (by omega),
      HydrogenAtom.rydbergEnergy_eq, fineStructureConstant, bohrRadius]
    field_simp
    ring

/-- **Fine structure, `j = l - 1/2`.** For `l ≥ 1` the three corrections add up to
`E_ν α²/ν² (ν/(j + 1/2) - 3/4)` with `j = l - 1/2`. -/
lemma fineStructureShift_lower (hk : 0 < H.k) (hl : l < ν) (hl1 : 1 ≤ l)
    {ls : ℝ} (hls : (ls : ℂ) = Sl2.spinOrbitValue (2 * l) 1 1) :
    fineStructureShift H c ν l ls = H.energyLevel (ν - 1) * fineStructureConstant H c ^ 2 /
      (ν : ℝ) ^ 2 * ((ν : ℝ) / ((l - 1 / 2 : ℝ) + 1 / 2) - 3 / 4) := by
  rw [ls_lower hl1 hls]
  have hm := H.m_pos.ne'
  have hk0 := hk.ne'
  have hℏ := ℏ_ne_zero
  have hc := c.val_ne_zero
  have hν : (ν : ℝ) ≠ 0 := by exact_mod_cast (show ν ≠ 0 by omega)
  have hl0 : (l : ℝ) ≠ 0 := by exact_mod_cast (show l ≠ 0 by omega)
  simp only [fineStructureShift, relativisticShift, spinOrbitShift, darwinShift,
    show l ≠ 0 by omega, ↓reduceIte, radialMean_one hl, radialMean_two hl, radialMean_three hl hl1,
    add_zero]
  rw [HydrogenAtom.energyLevel_eq, levelIndex_sub_one (by omega),
    HydrogenAtom.rydbergEnergy_eq, fineStructureConstant, bohrRadius]
  field_simp
  ring

/-- **The fine-structure shift depends on `j` only.** The levels `(ν, l, j = l + 1/2)` and
`(ν, l + 1, j = l + 1/2)` are shifted by the same amount; for `ν = 2`, `l = 0` this is the
degeneracy of `2s_{1/2}` and `2p_{1/2}` that the Lamb shift lifts. -/
lemma fineStructureShift_upper_eq_lower (hk : 0 < H.k) (hl : l + 1 < ν)
    {ls ls' : ℝ} (hls : (ls : ℂ) = Sl2.spinOrbitValue (2 * l) 1 0)
    (hls' : (ls' : ℂ) = Sl2.spinOrbitValue (2 * (l + 1)) 1 1) :
    fineStructureShift H c ν l ls = fineStructureShift H c ν (l + 1) ls' := by
  rw [fineStructureShift_upper hk (by omega) hls,
    fineStructureShift_lower hk hl (by omega) hls']
  push_cast
  ring_nf

end PhyslibAlpha.Hydrogen
