/-
Copyright (c) 2026 Daniel Leonforte. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Leonforte
-/
module

public import PhyslibAlpha.Mathematics.RepresentationTheory.Sl2.TensorDecomposition
public import PhyslibAlpha.QuantumMechanics.AngularMomentum.Basic

/-!
# Addition of angular momenta

Couples two angular momenta and identifies the total angular momentum on the
Clebsch–Gordan decomposition.

## i. Overview

Two angular momentum representations on `V` and `W` give one on `V ⊗ W`, with total angular
momentum `J = J₁ ⊗ 1 + 1 ⊗ J₂`. The standard module `V(n)` carries the spin-`n/2`
representation with `Jz = H/2`, `J+ = E` and `J- = F`. For spins `j₁ = m/2` and `j₂ = n/2` the
total `J²` acts on the `k`-th lowering string of `V(m) ⊗ V(n)` by `J(J + 1)` with
`J = j₁ + j₂ - k`, and `Jz` acts on its `l`-th vector by `J - l`. As `k` runs from `0` to
`min m n`, `J` runs from `j₁ + j₂` down to `|j₁ - j₂|`. The Clebsch–Gordan equivalence
`cgEquiv` intertwines `Jz`, `J+` and `J-` of the coupled system with those of the spin-`J`
representations on the summands.

## ii. Key results

- `AngularMomentumRepresentation.tensor` is the coupled representation on `V ⊗ W`.
- `AngularMomentumRepresentation.standard` is the spin-`n/2` representation on `V(n)`.
- `Jsq_coupled_stringVec` and `Jz_coupled_stringVec` give the total `J²` and `Jz` on the
  lowering strings.
- `cgEquiv_Jz_coupled`, `cgEquiv_Jp_coupled` and `cgEquiv_Jm_coupled` give the intertwining
  with the summands.

## iii. Table of contents

- A. Coupled angular momentum
- B. The spin-`n/2` representation on `V(n)`
- C. Total angular momentum on `V(m) ⊗ V(n)`
  - C.1. Eigenvalues on the lowering strings
  - C.2. Intertwining with the summands

## iv. References

- Mathlib, `Mathlib.Algebra.Lie.Sl2`.

## A. Coupled angular momentum
-/

@[expose] public section

noncomputable section

namespace PhyslibAlpha.Sl2

open scoped TensorProduct DirectSum

open StandardSl2Module

attribute [local instance 100] LieRing.ofAssociativeRing

namespace AngularMomentumRepresentation

variable {V W : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

/-- The coupled angular momentum `J = J₁ ⊗ 1 + 1 ⊗ J₂` on `V ⊗ W`. -/
def tensor (ρ₁ : AngularMomentumRepresentation V) (ρ₂ : AngularMomentumRepresentation W) :
    AngularMomentumRepresentation (V ⊗[ℂ] W) where
  Jx := diagEnd ρ₁.Jx ρ₂.Jx
  Jy := diagEnd ρ₁.Jy ρ₂.Jy
  Jz := diagEnd ρ₁.Jz ρ₂.Jz
  comm_xy := by rw [lie_diagEnd, ρ₁.comm_xy, ρ₂.comm_xy, diagEnd_smul]
  comm_yz := by rw [lie_diagEnd, ρ₁.comm_yz, ρ₂.comm_yz, diagEnd_smul]
  comm_zx := by rw [lie_diagEnd, ρ₁.comm_zx, ρ₂.comm_zx, diagEnd_smul]

lemma tensor_Jp (ρ₁ : AngularMomentumRepresentation V) (ρ₂ : AngularMomentumRepresentation W) :
    (tensor ρ₁ ρ₂).Jp = diagEnd ρ₁.Jp ρ₂.Jp := by
  simp only [Jp, tensor, diagEnd_add, diagEnd_smul]

lemma tensor_Jm (ρ₁ : AngularMomentumRepresentation V) (ρ₂ : AngularMomentumRepresentation W) :
    (tensor ρ₁ ρ₂).Jm = diagEnd ρ₁.Jm ρ₂.Jm := by
  simp only [Jm, tensor, diagEnd_sub, diagEnd_smul]

/-! ## B. The spin-`n/2` representation on `V(n)` -/

variable (n : ℕ)

/-- `EF = FE + H` on `V(n)`, the associative form of `⁅E, F⁆ = H`. -/
lemma ρE_mul_ρF :
    (ρE : Module.End ℂ (StandardSl2Module ℂ n)) * ρF = ρF * ρE + ρH := by
  have h := rel_ef (K := ℂ) (n := n)
  rw [LieRing.of_associative_ring_bracket] at h
  rw [← h]
  abel

/-- `HE = EH + 2E` on `V(n)`, the associative form of `⁅H, E⁆ = 2E`. -/
lemma ρH_mul_ρE :
    (ρH : Module.End ℂ (StandardSl2Module ℂ n)) * ρE = ρE * ρH + (2 : ℂ) • ρE := by
  have h := rel_he (K := ℂ) (n := n)
  rw [LieRing.of_associative_ring_bracket] at h
  rw [← h]
  abel

/-- `HF = FH - 2F` on `V(n)`, the associative form of `⁅H, F⁆ = -2F`. -/
lemma ρH_mul_ρF :
    (ρH : Module.End ℂ (StandardSl2Module ℂ n)) * ρF = ρF * ρH + (-2 : ℂ) • ρF := by
  have h := rel_hf (K := ℂ) (n := n)
  rw [LieRing.of_associative_ring_bracket] at h
  rw [← h]
  abel

/-- `Jx = (E + F)/2` on `V(n)`. -/
def stdJx : Module.End ℂ (StandardSl2Module ℂ n) := (1 / 2 : ℂ) • (ρE + ρF)

/-- `Jy = -i(E - F)/2` on `V(n)`. -/
def stdJy : Module.End ℂ (StandardSl2Module ℂ n) := (-Complex.I / 2) • (ρE - ρF)

/-- `Jz = H/2` on `V(n)`. -/
def stdJz : Module.End ℂ (StandardSl2Module ℂ n) := (1 / 2 : ℂ) • ρH

lemma stdJx_stdJy : ⁅stdJx n, stdJy n⁆ = Complex.I • stdJz n := by
  simp only [stdJx, stdJy, stdJz, LieRing.of_associative_ring_bracket, smul_mul_assoc,
    mul_smul_comm, smul_smul, add_mul, mul_add, sub_mul, mul_sub, ρE_mul_ρF]
  match_scalars <;> ring_nf

lemma stdJy_stdJz : ⁅stdJy n, stdJz n⁆ = Complex.I • stdJx n := by
  simp only [stdJx, stdJy, stdJz, LieRing.of_associative_ring_bracket, smul_mul_assoc,
    mul_smul_comm, smul_smul, sub_mul, mul_sub, ρH_mul_ρE, ρH_mul_ρF, smul_add]
  match_scalars <;> ring_nf

lemma stdJz_stdJx : ⁅stdJz n, stdJx n⁆ = Complex.I • stdJy n := by
  simp only [stdJx, stdJy, stdJz, LieRing.of_associative_ring_bracket, smul_mul_assoc,
    mul_smul_comm, smul_smul, add_mul, mul_add, ρH_mul_ρE, ρH_mul_ρF, smul_add, smul_sub]
  match_scalars <;> ring_nf <;> simp only [Complex.I_sq] <;> ring_nf

/-- The spin-`n/2` representation on `V(n)`: `Jz = H/2`, `Jx = (E + F)/2`,
`Jy = -i(E - F)/2`, so that `J+ = E` and `J- = F`. -/
def standard : AngularMomentumRepresentation (StandardSl2Module ℂ n) where
  Jx := stdJx n
  Jy := stdJy n
  Jz := stdJz n
  comm_xy := stdJx_stdJy n
  comm_yz := stdJy_stdJz n
  comm_zx := stdJz_stdJx n

lemma standard_Jp : (standard n).Jp = ρE := by
  simp only [Jp, standard, stdJx, stdJy, smul_smul, smul_add, smul_sub]
  match_scalars <;> ring_nf <;> simp only [Complex.I_sq] <;> ring_nf

lemma standard_Jm : (standard n).Jm = ρF := by
  simp only [Jm, standard, stdJx, stdJy, smul_smul, smul_add, smul_sub]
  match_scalars <;> ring_nf <;> simp only [Complex.I_sq] <;> ring_nf

lemma standard_Jz : (standard n).Jz = (1 / 2 : ℂ) • ρH := rfl

end AngularMomentumRepresentation

/-! ## C. Total angular momentum on `V(m) ⊗ V(n)`

### C.1. Eigenvalues on the lowering strings -/

open AngularMomentumRepresentation

variable {m n : ℕ}

/-- The coupled representation of spins `m/2` and `n/2` on `V(m) ⊗ V(n)`. -/
abbrev coupled (m n : ℕ) :
    AngularMomentumRepresentation (StandardSl2Module ℂ m ⊗[ℂ] StandardSl2Module ℂ n) :=
  tensor (standard m) (standard n)

lemma coupled_Jz : (coupled m n).Jz = (1 / 2 : ℂ) • tensorH m n := by
  simp only [coupled, tensor, standard, stdJz, diagEnd_smul, tensorH]

lemma coupled_Jp : (coupled m n).Jp = tensorE m n := by
  rw [coupled, tensor_Jp, standard_Jp, standard_Jp, tensorE]

lemma coupled_Jm : (coupled m n).Jm = tensorF m n := by
  rw [coupled, tensor_Jm, standard_Jm, standard_Jm, tensorF]

section String

variable {k : ℕ} (hmn : 0 < m + n) (hkm : k ≤ m) (hkn : k ≤ n)

include hmn hkm hkn

/-- `Jz` acts on the `l`-th vector of the `k`-th string by `J - l`, `J = (m + n - 2k)/2`. -/
lemma Jz_coupled_stringVec (l : ℕ) :
    (coupled m n).Jz (stringVec m n k l) =
      (((m + n - 2 * k : ℕ) : ℂ) / 2 - l) • stringVec m n k l := by
  rw [coupled_Jz, LinearMap.smul_apply, tensorH_stringVec hmn hkm hkn, smul_smul]
  congr 1
  ring

/-- The total `J²` acts on the `k`-th string by `J(J + 1)`, `J = (m + n - 2k)/2`. -/
lemma Jsq_coupled_stringVec (l : ℕ) :
    (coupled m n).Jsq (stringVec m n k l) =
      (((m + n - 2 * k : ℕ) : ℂ) / 2 * (((m + n - 2 * k : ℕ) : ℂ) / 2 + 1)) •
        stringVec m n k l := by
  rw [Jsq, Jsq_eq_Jp_mul_Jm, coupled_Jp, coupled_Jm]
  simp only [LinearMap.sub_apply, LinearMap.add_apply, Module.End.mul_apply,
    tensorF_stringVec, tensorE_stringVec_succ hmn hkm hkn, Jz_coupled_stringVec hmn hkm hkn,
    map_smul]
  module

end String

/-! ### C.2. Intertwining with the summands -/

lemma sumEnd_smul (c : ℂ) (A : ∀ k, Module.End ℂ (CGSummand ℂ m n k)) (y : CGSum ℂ m n) :
    sumEnd (fun k => c • A k) y = c • sumEnd A y := by
  have h : sumEnd (fun k => c • A k) = c • sumEnd A :=
    DirectSum.linearMap_ext ℂ fun k => LinearMap.ext fun x => by
      simp [sumEnd_lof]
  rw [h, LinearMap.smul_apply]

/-- `cgEquiv` intertwines the total `Jz` with `Jz` of the spin-`J` summands. -/
lemma cgEquiv_Jz_coupled (hmn : 0 < m + n)
    (x : StandardSl2Module ℂ m ⊗[ℂ] StandardSl2Module ℂ n) :
    cgEquiv hmn ((coupled m n).Jz x) = sumEnd (fun _ => (standard _).Jz) (cgEquiv hmn x) := by
  rw [coupled_Jz, LinearMap.smul_apply, map_smul, cgEquiv_tensorH, ← sumEnd_smul]
  simp only [standard_Jz]

/-- `cgEquiv` intertwines the total `J+` with `J+` of the spin-`J` summands. -/
lemma cgEquiv_Jp_coupled (hmn : 0 < m + n)
    (x : StandardSl2Module ℂ m ⊗[ℂ] StandardSl2Module ℂ n) :
    cgEquiv hmn ((coupled m n).Jp x) = sumEnd (fun _ => (standard _).Jp) (cgEquiv hmn x) := by
  simp only [coupled_Jp, standard_Jp, cgEquiv_tensorE]

/-- `cgEquiv` intertwines the total `J-` with `J-` of the spin-`J` summands. -/
lemma cgEquiv_Jm_coupled (hmn : 0 < m + n)
    (x : StandardSl2Module ℂ m ⊗[ℂ] StandardSl2Module ℂ n) :
    cgEquiv hmn ((coupled m n).Jm x) = sumEnd (fun _ => (standard _).Jm) (cgEquiv hmn x) := by
  simp only [coupled_Jm, standard_Jm, cgEquiv_tensorF]

end PhyslibAlpha.Sl2
