/-
Copyright (c) 2026 Daniel Leonforte. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Leonforte
-/
module

public import PhyslibAlpha.Mathematics.RepresentationTheory.Sl2.Schur
public import PhyslibAlpha.QuantumMechanics.AngularMomentum.Addition

/-!

# Spin–orbit coupling

The operator `L · S` on coupled angular momenta, its eigenvalues on the states of total angular
momentum `J`, the fine-structure doublet and Landé's interval rule.

## i. Overview

For two angular momenta `L` on `V` and `S` on `W` the scalar product
`L · S = Lx ⊗ Sx + Ly ⊗ Sy + Lz ⊗ Sz` satisfies, for the total angular momentum
`J = L ⊗ 1 + 1 ⊗ S`,

`J² = L² ⊗ 1 + 1 ⊗ S² + 2 L · S`.

This is pure algebra on pure tensors (`Jsq_tensor`). On `V(m) ⊗ V(n)` with `l = m/2`,
`s = n/2`, the operators `L²` and `S²` are the scalars `l(l + 1)` and `s(s + 1)`
(`Jsq_standard`), and `J²` acts on the `k`-th lowering string by `J(J + 1)`,
`J = l + s - k` (`Jsq_coupled_stringVec`). Hence every state of total angular momentum `J` is an
eigenvector of `L · S`:

`L · S = (J(J + 1) - l(l + 1) - s(s + 1)) / 2`.

With a spin-orbit Hamiltonian `ζ L · S` this gives

- the fine-structure doublet for `s = 1/2`: `L · S = l/2` for `J = l + 1/2` and
  `L · S = -(l + 1)/2` for `J = l - 1/2`, a splitting of `(2l + 1)/2` in units of `ζ`;
- Landé's interval rule: neighbouring levels `J` and `J - 1` of a multiplet are `J` apart in
  units of `ζ`.

## ii. Key results

- `dot`, `Jsq_tensor`: the operator `L · S` and the identity `J² = L² + S² + 2 L · S`.
- `Jsq_standard`: `J² = j(j + 1)` on the spin-`j` representation.
- `dot_coupled_stringVec`: the eigenvalues of `L · S`.
- `dot_coupled_stringVec_doublet_upper`, `dot_coupled_stringVec_doublet_lower`: the doublet.
- `spinOrbitValue_sub_succ`: the interval rule.

## iii. Table of contents

- A. The scalar product of two angular momenta
- B. The Casimir operator of `V(n)`
- C. Eigenvalues of `L · S`
- D. Fine structure and the interval rule

## iv. References

- J. J. Sakurai and J. Napolitano, *Modern Quantum Mechanics*, 3rd ed., Cambridge University
  Press (2020), sections 3.8 and 5.3.
- A. Landé, *Termstruktur und Zeemaneffekt der Multipletts*, Z. Phys. 15, 189 (1923).

## A. The scalar product of two angular momenta

-/

@[expose] public section

noncomputable section

namespace PhyslibAlpha.Sl2

open scoped TensorProduct

open StandardSl2Module

attribute [local instance 100] LieRing.ofAssociativeRing

namespace AngularMomentumRepresentation

variable {V W : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

/-- The scalar product `L · S = Lx ⊗ Sx + Ly ⊗ Sy + Lz ⊗ Sz` on `V ⊗ W`. -/
def dot (ρ₁ : AngularMomentumRepresentation V) (ρ₂ : AngularMomentumRepresentation W) :
    Module.End ℂ (V ⊗[ℂ] W) :=
  TensorProduct.map ρ₁.Jx ρ₂.Jx + TensorProduct.map ρ₁.Jy ρ₂.Jy + TensorProduct.map ρ₁.Jz ρ₂.Jz

/-- **`J² = L² + S² + 2 L · S`.** -/
lemma Jsq_tensor (ρ₁ : AngularMomentumRepresentation V) (ρ₂ : AngularMomentumRepresentation W) :
    (tensor ρ₁ ρ₂).Jsq = ρ₁.Jsq.rTensor W + ρ₂.Jsq.lTensor V + (2 : ℂ) • dot ρ₁ ρ₂ := by
  refine TensorProduct.ext' fun x y => ?_
  simp only [Jsq, tensor, LinearMap.add_apply, Module.End.mul_apply, diagEnd_tmul, map_add,
    LinearMap.rTensor_tmul, LinearMap.lTensor_tmul, LinearMap.smul_apply, dot,
    TensorProduct.map_tmul, TensorProduct.add_tmul, TensorProduct.tmul_add]
  module

/-!

## B. The Casimir operator of `V(n)`

-/

/-- `J² = j(j + 1)` on the spin-`j` representation `V(2j)`. -/
lemma Jsq_standard (n : ℕ) :
    (standard n).Jsq =
      ((n : ℂ) / 2 * ((n : ℂ) / 2 + 1)) • (1 : Module.End ℂ (StandardSl2Module ℂ n)) := by
  refine StandardSl2Module.linearMap_ext_vNat fun a => ?_
  rw [Jsq, Jsq_eq_Jp_mul_Jm, standard_Jp, standard_Jm, standard_Jz]
  simp only [LinearMap.sub_apply, LinearMap.add_apply, Module.End.mul_apply, LinearMap.smul_apply,
    ρF_vNat, ρE_vNat_succ, ρH_vNat, map_smul, Module.End.one_apply]
  module

end AngularMomentumRepresentation

/-!

## C. Eigenvalues of `L · S`

-/

open AngularMomentumRepresentation

variable {m n : ℕ}

/-- The eigenvalue `(J(J + 1) - l(l + 1) - s(s + 1)) / 2` of `L · S` for `l = m/2`, `s = n/2`
and `J = (m + n)/2 - k`. -/
def spinOrbitValue (m n k : ℕ) : ℂ :=
  (((m + n - 2 * k : ℕ) : ℂ) / 2 * (((m + n - 2 * k : ℕ) : ℂ) / 2 + 1) -
    (m : ℂ) / 2 * ((m : ℂ) / 2 + 1) - (n : ℂ) / 2 * ((n : ℂ) / 2 + 1)) / 2

/-- **Spin–orbit eigenvalues.** Every vector of the `k`-th lowering string of `V(m) ⊗ V(n)`, a
state of total angular momentum `J = (m + n)/2 - k`, is an eigenvector of `L · S` with eigenvalue
`(J(J + 1) - l(l + 1) - s(s + 1)) / 2`. -/
lemma dot_coupled_stringVec {k : ℕ} (hmn : 0 < m + n) (hkm : k ≤ m) (hkn : k ≤ n) (l : ℕ) :
    dot (standard m) (standard n) (stringVec m n k l) =
      spinOrbitValue m n k • stringVec m n k l := by
  have hT := LinearMap.congr_fun (Jsq_tensor (standard m) (standard n))
    (stringVec (K := ℂ) m n k l)
  rw [show tensor (standard m) (standard n) = coupled m n from rfl,
    Jsq_coupled_stringVec hmn hkm hkn, Jsq_standard, Jsq_standard] at hT
  simp only [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.rTensor_smul,
    LinearMap.lTensor_smul, Module.End.one_eq_id, LinearMap.rTensor_id, LinearMap.lTensor_id,
    LinearMap.id_apply] at hT
  rw [spinOrbitValue]
  linear_combination (norm := module) (-1 / 2 : ℂ) • hT

/-!

## D. Fine structure and the interval rule

-/

/-- **Fine-structure doublet, upper level.** For spin `1/2` and `J = l + 1/2`,
`L · S = l/2` (`l = m/2`). -/
lemma dot_coupled_stringVec_doublet_upper (l' : ℕ) :
    dot (standard m) (standard 1) (stringVec m 1 0 l') =
      ((m : ℂ) / 4) • stringVec m 1 0 l' := by
  rw [dot_coupled_stringVec (by omega) (Nat.zero_le m) (Nat.zero_le 1), spinOrbitValue]
  congr 1
  push_cast
  ring

/-- **Fine-structure doublet, lower level.** For spin `1/2` and `J = l - 1/2`,
`L · S = -(l + 1)/2` (`l = m/2`, `m ≥ 1`). -/
lemma dot_coupled_stringVec_doublet_lower (hm : 1 ≤ m) (l' : ℕ) :
    dot (standard m) (standard 1) (stringVec m 1 1 l') =
      (-((m : ℂ) + 2) / 4) • stringVec m 1 1 l' := by
  rw [dot_coupled_stringVec (by omega) hm le_rfl, spinOrbitValue,
    show m + 1 - 2 * 1 = m - 1 by omega, Nat.cast_sub hm]
  congr 1
  push_cast
  ring

/-- The doublet splitting `l/2 + (l + 1)/2 = (2l + 1)/2`. -/
lemma spinOrbitValue_doublet_sub (hm : 1 ≤ m) :
    spinOrbitValue m 1 0 - spinOrbitValue m 1 1 = ((m : ℂ) + 1) / 2 := by
  rw [spinOrbitValue, spinOrbitValue, show m + 1 - 2 * 1 = m - 1 by omega, Nat.cast_sub hm]
  push_cast
  ring

/-- **Landé's interval rule.** The levels `J` and `J - 1` of a multiplet differ in `L · S` by `J`,
`J = (m + n)/2 - k`. -/
lemma spinOrbitValue_sub_succ {k : ℕ} (hkm : k + 1 ≤ m) (hkn : k + 1 ≤ n) :
    spinOrbitValue m n k - spinOrbitValue m n (k + 1) = ((m + n - 2 * k : ℕ) : ℂ) / 2 := by
  rw [spinOrbitValue, spinOrbitValue,
    show m + n - 2 * k = m + n - 2 * (k + 1) + 2 by omega]
  push_cast
  ring

end PhyslibAlpha.Sl2
