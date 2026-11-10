/-
Copyright (c) 2026 Andrea Pari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrea Pari
-/
module

public import Physlib.Mathematics.Tensors.ElabTactics

/-!

# Examples of index notation

Examples and tests of the index notation `{…}ᵀ` and of the tactics `tensor_components`,
`tensor_regroup` and `tensor_slots`.

## i. Overview

Each example states an equation in index notation and proves it by `rfl` or by one of the tactics.
The `#guard_msgs` tests fix the elaborated terms and the error messages of false goals.

## ii. Key results

There are no declarations, only examples.

## iii. Table of contents

- A. Products, sums and contractions
- B. Lowering and raising
- C. Tensorial types
- D. Regrouping contractions
- E. Regrouping with forms
- F. Chains of lowerings and raisings

## iv. References

-/

namespace Tensors.Notation

open Species

variable {k : Type} [CommRing k] {K : Type} {G : Type} [Group G] {basisIdx : K → Type}
    [∀ κ, Fintype (basisIdx κ)] [∀ κ, DecidableEq (basisIdx κ)] {S : Species k G K basisIdx}
    (a c : Color K) (T U W : S.Tensor ![a, a.dual]) (T' : S.Tensor ![a.dual, a])
    (κ : K) (v : S.Tensor ![⟨κ, .up⟩]) (r : k) (Λ : G)

/-!

## A. Products, sums and contractions

-/

/-- info: T : S.Tensor ![a, a.dual] -/
#guard_msgs in
#check {T | μ ν}ᵀ

/-- The matrix product `T^μ_ν U^ν_ρ`. -/
noncomputable example : S.Tensor ![a, a.dual] := {T | μ ν ⊗ U | ν ρ}ᵀ

/-- A product given as one term, with the colors `prodColors ![a, a.dual] ![a, a.dual]`, is the
product in the notation. -/
example : {S.tmulEquiv _ _ (T ⊗ₜ U) | μ ν ν ρ = T | μ ν ⊗ U | ν ρ}ᵀ := rfl

/-- An equation with a tensor `s` with no slots, `T^μ_μ = s`. The space after the bar keeps
Mathlib's absolute value `|x|` from reading it. -/
example (s : S.Tensor (![] : Fin 0 → Color K)) : {T | μ μ = s | }ᵀ ↔ {T | μ μ}ᵀ = s := Iff.rfl

/-- An equation in parentheses is the same equation. -/
example : {(T | μ ν = U | μ ν)}ᵀ ↔ {T | μ ν = U | μ ν}ᵀ := Iff.rfl

/-- An equation whose right side lists its indices in the other order, `T^μ_ν = T'_ν^μ`. -/
example : Prop := {T | μ ν = T' | ν μ}ᵀ

/-- The trace of a product of four matrices, `T^μ_ν U^ν_ρ T^ρ_σ U^σ_μ`. -/
noncomputable example : S.Tensor (![] : Fin 0 → Color K) :=
  {T | μ ν ⊗ U | ν ρ ⊗ T | ρ σ ⊗ U | σ μ}ᵀ

/-- The trace of a product of five matrices, `T^μ_ν U^ν_ρ W^ρ_σ T^σ_τ U^τ_μ`. -/
noncomputable example : S.Tensor (![] : Fin 0 → Color K) :=
  {T | μ ν ⊗ U | ν ρ ⊗ W | ρ σ ⊗ T | σ τ ⊗ U | τ μ}ᵀ

/-- Sums, negatives and scalar multiples, `-T^μ_ν + r U^μ_ν`. -/
example : {-T | μ ν + r • U | μ ν}ᵀ = -T + r • U := rfl

/-- A scalar multiple of a contraction, `r T^μ_ν U^ν_ρ`. -/
example : {r • {T | μ ν ⊗ U | ν ρ}ᵀ | μ ρ}ᵀ = r • {T | μ ν ⊗ U | ν ρ}ᵀ := rfl

/-- Each side of a sum is contracted first, so `μ` is free again in the product,
`(T^λ_λ + U^λ_λ) T^μ_ν`. -/
example : {(T | μ μ + U | μ μ) ⊗ T | μ ν}ᵀ = {({T | μ μ}ᵀ + {U | μ μ}ᵀ) | ⊗ T | μ ν}ᵀ := rfl

-- The two sides of a sum or an equation must agree in the colors of each name.
/-- error: index notation: ν has the color a.dual on the left and a on the right -/
#guard_msgs in
#check {T | μ ν = T | ν μ}ᵀ

-- A term that is neither a tensor nor tensorial is rejected, with the error of the instance search.
/-- error: index notation: r is not a tensor and has no `Tensorial` instance:
failed to synthesize instance of type class
  Tensorial -/
#guard_msgs (substring := true) in
#check {r | μ}ᵀ

-- A term whose type is not known, such as a bare numeral, is rejected.
/-- error: index notation: the type of 0 is not known; give it, as `(0 : S.Tensor ![…])` -/
#guard_msgs in
#check {0 | μ ν}ᵀ

/-- An expression in parentheses is contracted first, so `μ` is free again in the product,
`(T^λ_λ) U^μ_ρ`. -/
example : {(T | μ μ) ⊗ U | μ ρ}ᵀ = {{T | μ μ}ᵀ | ⊗ U | μ ρ}ᵀ := rfl

-- A name appearing three times in one product chain is rejected.
/-- error: index notation: μ appears more than twice -/
#guard_msgs in
#check {T | μ μ ⊗ U | μ ρ}ᵀ

-- A tensor whose colors are not a literal list is rejected.
/-- error: index notation: the colors of t must be a literal list -/
#guard_msgs in
example (f : Fin 2 → Color K) (t : S.Tensor f) : S.Tensor f := {t | μ ν}ᵀ

-- A pair of slots whose colors are not dual is rejected.
/-- error: index notation: μ joins the colors a and a, which are not dual -/
#guard_msgs in
#check {T | μ ν ⊗ T | μ ρ}ᵀ

/-- Contracting `ν` and then `ρ` is contracting both at once, `(T U)^μ_ρ W^ρ_τ = T^μ_ν U^ν_ρ W^ρ_τ`,
by `tmulEquiv_contr_left` and `contr_contr`. -/
example : {{T | μ ν ⊗ U | ν ρ}ᵀ | μ ρ ⊗ W | ρ τ = T | μ ν ⊗ U | ν ρ ⊗ W | ρ τ}ᵀ := by
  rw [Tensor.tmulEquiv_contr_left, Tensor.contr_contr]
  congr 2
  ext x
  fin_cases x <;> rfl

/-!

## B. Lowering and raising

-/

section Metric

variable [S.HasForm κ] [S.HasForm c.kind]

/-- Lowering and then raising an index gives the vector back, `(v_μ)^μ = v^μ`. -/
example : {{v | ↓μ}ᵀ | ↑μ}ᵀ = v := toDualAt_toDualAt _ _ _ _ _ _

-- An arrow that does not match the variance of the slot is rejected.
/-- error: index notation: ↑μ needs a visibly lower index -/
#guard_msgs in
#check {v | ↑μ}ᵀ

/-- `τ` lowers an upper index, as `↓` does. -/
example : {v | τ(μ)}ᵀ = {v | ↓μ}ᵀ := rfl

/-- `τ` needs no visible variance, so it flips an index of any color, `(w_μ)^μ = w^μ`. -/
example (w : S.Tensor ![c]) : {{w | τ(μ)}ᵀ | τ(μ)}ᵀ = w := by
  tensor_slots

/-- Lowering commutes with the group action, `(Λ v)_μ = Λ (v_μ)`, by `rw [equiv_smul]`. -/
example : {(Λ • v) | ↓μ}ᵀ = Λ • {v | ↓μ}ᵀ := by rw [equiv_smul]

/-- Lowering both indices commutes with the group action, `(Λ M)_μν = Λ (M_μν)`. -/
example (M : S.Tensor ![⟨κ, .up⟩, ⟨κ, .up⟩]) : {(Λ • M) | ↓μ ↓ν}ᵀ = Λ • {M | ↓μ ↓ν}ᵀ := by
  simp only [equiv_smul]

/-- A trace commutes with the group action, `(Λ T)^μ_μ = Λ (T^μ_μ)`, by
`rw [intertwiningMap_smul]`. -/
example : {(Λ • T) | μ μ}ᵀ = Λ • {T | μ μ}ᵀ := by rw [intertwiningMap_smul]

/-- `g^μν g_νρ = δ^μ_ρ`, by `contr_formTensor_formTensor`. The relabeling the notation generates
is `ColorEquiv.matMul`, checked slot by slot. -/
example : {S.formTensor c | μ ν ⊗ S.formTensor c.dual | ν ρ = S.deltaTensor c.dual | μ ρ}ᵀ := by
  rw [← contr_formTensor_formTensor]
  congr 2
  ext x
  fin_cases x <;> rfl

end Metric

/-!

## C. Tensorial types

-/

section Tensorial

variable {M : Type} [AddCommGroup M] [Module k M] [Tensorial S ![a, a.dual] M] (m : M)

/-- info: Tensorial.toTensor m : S.Tensor ![a, a.dual] -/
#guard_msgs in
#check {m | μ ν}ᵀ

/-- The contraction `m^μ_ν T^ν_ρ` of an element of a tensorial type with a tensor. -/
noncomputable example : S.Tensor ![a, a.dual] := {m | μ ν ⊗ T | ν ρ}ᵀ

/-- The contraction `m^μ_ν m^ν_ρ` inside `M ⊗ M`, through `Tensorial.prod`. -/
noncomputable example : S.Tensor ![a, a.dual] := {(m ⊗ₜ[k] m) | μ ν ν ρ}ᵀ

/-- The contraction `m^μ_ν T^ν_ρ` read back as an element of `M`. -/
noncomputable example : M := {m | μ ν ⊗ T | ν ρ}ᵀ

open TensorProduct in
/-- A product with no contraction is read back as `m ⊗ₜ m`, with no relabeling. -/
example : ({m | μ ν ⊗ m | ρ σ}ᵀ : M ⊗[k] M) = m ⊗ₜ m := by
  rw [← Tensorial.toTensor_tmul, Representation.Equiv.symm_apply_apply]

/-- A tensor on `Fin 2` relabeled onto the slots `Fin 1 ⊕ Fin 1` of a product. -/
noncomputable example : S.Tensor (prodColors ![a] ![a.dual]) := {T | μ ν}ᵀ

/-- error: index notation: the free index μ has the color a, but its slot is expected to have the
color a.dual -/
#guard_msgs in
example : S.Tensor (prodColors ![a.dual] ![a]) := {T | μ ν}ᵀ

end Tensorial

/-!

## D. Regrouping contractions

-/

/-- By `tensor_regroup`, with the other grouping on the right,
`(T U)^μ_ρ W^ρ_τ = T^μ_ν (U W)^ν_τ`. -/
example : {{T | μ ν ⊗ U | ν ρ}ᵀ | μ ρ ⊗ W | ρ τ = T | μ ν ⊗ {U | ν ρ ⊗ W | ρ τ}ᵀ | ν τ}ᵀ := by
  tensor_regroup

/-- `tensor_regroup` reorders the factors, `T^μ_ν U^ν_ρ = U^ν_ρ T^μ_ν`. -/
example : {T | μ ν ⊗ U | ν ρ = U | ν ρ ⊗ T | μ ν}ᵀ := by
  tensor_regroup

/-- A factor that appears twice, `T^μ_ν T^ν_ρ = T^ν_ρ T^μ_ν`. -/
example : {T | μ ν ⊗ T | ν ρ = T | ν ρ ⊗ T | μ ν}ᵀ := by
  tensor_regroup

/-- The trace is cyclic, `tr(T U T U) = tr(U T U T)`. -/
example : {T | μ ν ⊗ U | ν ρ ⊗ T | ρ σ ⊗ U | σ μ = U | ν ρ ⊗ T | ρ σ ⊗ U | σ μ ⊗ T | μ ν}ᵀ := by
  tensor_regroup

/-- `tensor_regroup` moves scalars out of the products, `(r T^μ_ν) U^ν_ρ = r (U^ν_ρ T^μ_ν)`. -/
example : {(r • T) | μ ν ⊗ U | ν ρ = r • {U | ν ρ ⊗ T | μ ν}ᵀ | ρ μ}ᵀ := by
  tensor_regroup

/-- Negatives, `(-T^μ_ν) U^ν_ρ = -(U^ν_ρ T^μ_ν)`. -/
example : {-T | μ ν ⊗ U | ν ρ = -{U | ν ρ ⊗ T | μ ν}ᵀ | ρ μ}ᵀ := by
  tensor_regroup

/-- Sums, matched summand by summand in any order, `T^μ_ν U^ν_ρ - W^μ_ρ = -W^μ_ρ + U^ν_ρ T^μ_ν`. -/
example : {T | μ ν ⊗ U | ν ρ + -W | μ ρ = -W | μ ρ + U | ν ρ ⊗ T | μ ν}ᵀ := by
  tensor_regroup

/-- A sum inside a product is distributed, `T^μ_ν (U + W)^ν_ρ = U^ν_ρ T^μ_ν + W^ν_ρ T^μ_ν`. -/
example : {T | μ ν ⊗ (U | ν ρ + W | ν ρ) = U | ν ρ ⊗ T | μ ν + W | ν ρ ⊗ T | μ ν}ᵀ := by
  tensor_regroup

/-- A delta on one side is inserted on the other, `T^μ_ν = T^μ_ρ δ^ρ_ν`. The left side is a single
tensor, read as a contraction with no pairs. -/
example : {T | μ ν = T | μ ρ ⊗ S.deltaTensor a.dual | ρ ν}ᵀ := by
  tensor_regroup

/-- A delta contracted at its second slot must be inserted at a slot of the dual color. -/
example : {T | μ ν = T | μ ρ ⊗ S.deltaTensor a | ν ρ}ᵀ := by
  tensor_regroup

/-- Matching a delta at its second slot also works when the delta is on the left. -/
example : {T | μ ρ ⊗ S.deltaTensor a | ν ρ = T | μ ν}ᵀ := by
  tensor_regroup

/-- A delta inside a sum, `T^μ_ν + U^μ_ρ δ^ρ_ν = U^μ_ν + T^μ_ν`. -/
example : {T | μ ν + U | μ ρ ⊗ S.deltaTensor a.dual | ρ ν = U | μ ν + T | μ ν}ᵀ := by
  tensor_regroup

/-- A delta on the left side is inserted on the right, `T^μ_ρ δ^ρ_ν = T^μ_ν`. -/
example : {T | μ ρ ⊗ S.deltaTensor a.dual | ρ ν = T | μ ν}ᵀ := by
  tensor_regroup

/-- Three equal factors, matched in one of the `3!` ways,
`T^μ_ν T^ν_ρ T^ρ_σ = T^ρ_σ T^ν_ρ T^μ_ν`. -/
example : {T | μ ν ⊗ T | ν ρ ⊗ T | ρ σ = T | ρ σ ⊗ T | ν ρ ⊗ T | μ ν}ᵀ := by
  tensor_regroup

-- A factor with no counterpart on the other side is named.
/-- error: tensor_regroup: the factor
  U
has no equal factor on the right -/
#guard_msgs in
example : {T | μ ν ⊗ U | ν ρ = W | ν ρ ⊗ T | μ ν}ᵀ := by
  tensor_regroup

-- The same factors contracted along other pairs of slots, `T U W ≠ T W U`, are rejected.
/-- error: tensor_regroup: the two sides contract different pairs of slots, for each way of
matching their equal factors -/
#guard_msgs in
example : {T | μ ν ⊗ U | ν ρ ⊗ W | ρ σ = T | μ ν ⊗ W | ν ρ ⊗ U | ρ σ}ᵀ := by
  tensor_regroup

-- A summand with no counterpart on the other side is named.
/-- error: tensor_regroup: the summand
  W
has no matching summand on the right -/
#guard_msgs in
example : {T | μ ν + W | μ ν = U | μ ν + T | μ ν}ᵀ := by
  tensor_regroup

/-- `tensor_regroup using h` finds `T^μ_ν U^ν_ρ` among the factors, rewrites it by `h` and
regroups, `U^ν_ρ W^ρ_σ T^μ_ν = W^μ_ρ W^ρ_σ`. -/
example (h : {T | μ ν ⊗ U | ν ρ = W | μ ρ}ᵀ) :
    {U | ν ρ ⊗ W | ρ σ ⊗ T | μ ν = W | μ ρ ⊗ W | ρ σ}ᵀ := by
  tensor_regroup using h

/-- The identity is found on the right side, `W^μ_ρ W^ρ_σ = U^ν_ρ W^ρ_σ T^μ_ν`. -/
example (h : {T | μ ν ⊗ U | ν ρ = W | μ ρ}ᵀ) :
    {W | μ ρ ⊗ W | ρ σ = U | ν ρ ⊗ W | ρ σ ⊗ T | μ ν}ᵀ := by
  tensor_regroup using h

/-- Two identities in turn, `U^ν_ρ W^ρ_σ T^μ_ν = (T U) W = W W = T`. -/
example (h₁ : {T | μ ν ⊗ U | ν ρ = W | μ ρ}ᵀ) (h₂ : {W | μ ν ⊗ W | ν ρ = T | μ ρ}ᵀ) :
    {U | ν ρ ⊗ W | ρ σ ⊗ T | μ ν = T | μ σ}ᵀ := by
  tensor_regroup using h₁, h₂

/-- The free indices of the identity may be contracted with each other, `T^μ_ν U^ν_μ = W^μ_μ`. -/
example (h : {T | μ ν ⊗ U | ν ρ = W | μ ρ}ᵀ) : {U | ν μ ⊗ T | μ ν = W | μ μ}ᵀ := by
  tensor_regroup using h

-- The factors `T` and `U` are contracted as `U^ν_ρ T^ρ_μ`, not as `T^μ_ν U^ν_ρ`.
/-- error: tensor_regroup: no factors of either side are contracted as in the left side of h -/
#guard_msgs in
example (h : {T | μ ν ⊗ U | ν ρ = W | μ ρ}ᵀ) : {U | ν ρ ⊗ T | ρ μ = W | ν μ}ᵀ := by
  tensor_regroup using h

-- After the rewrite the two sides still differ, `W ≠ U`.
/-- error: tensor_regroup: the factor
  W
has no equal factor on the right -/
#guard_msgs in
example (h : {T | μ ν ⊗ U | ν ρ = W | μ ρ}ᵀ) : {T | μ ν ⊗ U | ν ρ = U | μ ρ}ᵀ := by
  tensor_regroup using h

/-!

## E. Regrouping with forms

-/

section Metric

variable [S.HasForm κ] [S.HasForm c.kind]

/-- A lowering is a contraction with the form, `v_μ = g_μν v^ν`. -/
example : {v | ↓μ = S.formTensor ⟨κ, .down⟩ | μ ν ⊗ v | ν}ᵀ := by
  tensor_regroup

/-- A form and its inverse are matched by inserting a delta, `v^μ = v^ν g_νρ g^ρμ`. -/
example : {v | μ = v | ν ⊗ S.formTensor ⟨κ, .down⟩ | ν ρ ⊗ S.formTensor ⟨κ, .up⟩ | ρ μ}ᵀ := by
  tensor_regroup

/-- A lowering cancels against the inverse form, `g^ρν M^μ_ν = M^μρ`. -/
example (M : S.Tensor ![⟨κ, .up⟩, ⟨κ, .up⟩]) :
    {M | μ ↓ν ⊗ S.formTensor ⟨κ, .up⟩ | ρ ν = M | μ ρ}ᵀ := by
  tensor_regroup

/-- Two lowerings cancel against two inverse forms, one pair at a time,
`g^ρμ g^σν M_μν = M^ρσ`. -/
example (M : S.Tensor ![⟨κ, .up⟩, ⟨κ, .up⟩]) :
    {M | ↓μ ↓ν ⊗ S.formTensor ⟨κ, .up⟩ | ρ μ ⊗ S.formTensor ⟨κ, .up⟩ | σ ν = M | ρ σ}ᵀ := by
  tensor_regroup

/-- The same with the pairs on the right side and on two kinds, `N^ρσ = g^ρμ g'^σν N_μν`. -/
example (κ' : K) [S.HasForm κ'] (N : S.Tensor ![⟨κ, .up⟩, ⟨κ', .up⟩]) :
    {N | ρ σ = N | ↓μ ↓ν ⊗ S.formTensor ⟨κ, .up⟩ | ρ μ ⊗ S.formTensor ⟨κ', .up⟩ | σ ν}ᵀ := by
  tensor_regroup

/-- A lowering contracted with the first index of a symmetric form, `g^νρ M^μ_ν = M^μρ`. -/
example [S.IsSymmetricForm κ] (M : S.Tensor ![⟨κ, .up⟩, ⟨κ, .up⟩]) :
    {M | μ ↓ν ⊗ S.formTensor ⟨κ, .up⟩ | ν ρ = M | μ ρ}ᵀ := by
  tensor_regroup

/-- With an antisymmetric form the second index cancels with no sign, `ε^ρν M^μ_ν = M^μρ`. -/
example [S.IsAntisymmetricForm κ] (M : S.Tensor ![⟨κ, .up⟩, ⟨κ, .up⟩]) :
    {M | μ ↓ν ⊗ S.formTensor ⟨κ, .up⟩ | ρ ν = M | μ ρ}ᵀ := by
  tensor_regroup

/-- With an antisymmetric form the first index cancels with a sign, `ε^νρ M^μ_ν = -M^μρ`. -/
example [S.IsAntisymmetricForm κ] (M : S.Tensor ![⟨κ, .up⟩, ⟨κ, .up⟩]) :
    {M | μ ↓ν ⊗ S.formTensor ⟨κ, .up⟩ | ν ρ = -M | μ ρ}ᵀ := by
  tensor_regroup

-- The sign of an antisymmetric form is not dropped, `ε^νρ M^μ_ν ≠ M^μρ`.
/-- error: tensor_regroup: the forms left over on one side do not cancel in inverse pairs against
the other side
  S.formTensor { kind := κ, variance := Variance.up }.dual
  S.formTensor { kind := κ, variance := Variance.up } -/
#guard_msgs in
example [S.IsAntisymmetricForm κ] (M : S.Tensor ![⟨κ, .up⟩, ⟨κ, .up⟩]) :
    {M | μ ↓ν ⊗ S.formTensor ⟨κ, .up⟩ | ν ρ = M | μ ρ}ᵀ := by
  tensor_regroup

-- Cancelling the pairs does not swap the free indices, `M_μν g^μρ g^νσ ≠ M^σρ`.
/-- error: tensor_regroup: the forms left over on one side do not cancel in inverse pairs against
the other side
  S.formTensor { kind := κ, variance := Variance.up }.dual
  S.formTensor { kind := κ, variance := Variance.up }.dual
  S.formTensor { kind := κ, variance := Variance.up }
  S.formTensor { kind := κ, variance := Variance.up } -/
#guard_msgs in
example (M : S.Tensor ![⟨κ, .up⟩, ⟨κ, .up⟩]) :
    {M | ↓μ ↓ν ⊗ S.formTensor ⟨κ, .up⟩ | μ ρ ⊗ S.formTensor ⟨κ, .up⟩ | ν σ = M | σ ρ}ᵀ := by
  tensor_regroup

-- A false goal with lowerings reports the summand as written, not with the lowerings expanded.
/-- error: tensor_regroup: the summand
  (S.toDualAt 0 { kind := κ, variance := Variance.up } ⋯ ⋯ ⋯) w
has no matching summand on the right -/
#guard_msgs in
example (w : S.Tensor ![⟨κ, .up⟩]) : {v | ↓μ + w | ↓μ = v | ↓μ + v | ↓μ}ᵀ := by
  tensor_regroup

/-- Summands of opposite signs are matched by swapping an antisymmetric form,
`M^μν g_νρ = -(g_ρν M^μν)`. -/
example [S.IsAntisymmetricForm κ] (M : S.Tensor ![⟨κ, .up⟩, ⟨κ, .up⟩]) :
    {M | μ ν ⊗ S.formTensor ⟨κ, .down⟩ | ν ρ =
      -{S.formTensor ⟨κ, .down⟩ | ρ ν ⊗ M | μ ν}ᵀ | ρ μ}ᵀ := by
  tensor_regroup

/-- A symmetric form is swapped when the regrouping fails, `M^μν g_νρ = M^μν g_ρν`. -/
example [S.IsSymmetricForm κ] (M : S.Tensor ![⟨κ, .up⟩, ⟨κ, .up⟩]) :
    {M | μ ν ⊗ S.formTensor ⟨κ, .down⟩ | ν ρ = M | μ ν ⊗ S.formTensor ⟨κ, .down⟩ | ρ ν}ᵀ := by
  tensor_regroup

/-- `g^μν g_νρ = δ^μ_ρ` by `tensor_regroup`, which writes the delta as the contraction of the two
forms. -/
example : {S.formTensor c | μ ν ⊗ S.formTensor c.dual | ν ρ = S.deltaTensor c.dual | μ ρ}ᵀ := by
  tensor_regroup

/-- The delta on the left side, `δ^μ_ρ = g^μν g_νρ`. -/
example : {S.deltaTensor c.dual | μ ρ = S.formTensor c | μ ν ⊗ S.formTensor c.dual | ν ρ}ᵀ := by
  tensor_regroup

end Metric

/-!

## F. Chains of lowerings and raisings

-/

section Metric

variable [S.HasForm κ] [S.HasForm c.kind]

/-- Lowering and then raising by `tensor_slots`, `(v_μ)^μ = v^μ`. -/
example : {{v | ↓μ}ᵀ | ↑μ}ᵀ = v := by
  tensor_slots

/-- `tensor_slots` with the chain on the right side, `v^μ = (v_μ)^μ`. -/
example : v = {{v | ↓μ}ᵀ | ↑μ}ᵀ := by
  tensor_slots

-- An equation with no lowering or raising is rejected.
/-- error: tensor_slots: neither side lowers or raises an index -/
#guard_msgs in
example (w : S.Tensor ![⟨κ, .up⟩]) : v = w := by
  tensor_slots

/-- Lowering both indices and raising them again, `(M_μν)^μν = M^μν`. -/
example (M : S.Tensor ![⟨κ, .up⟩, ⟨κ, .up⟩]) : {{M | ↓μ ↓ν}ᵀ | ↑μ ↑ν}ᵀ = M := by
  tensor_slots

/-- Lowerings at two slots commute, `(M_μ^ν)_ν = (M^μ_ν)_μ`. -/
example (M : S.Tensor ![⟨κ, .up⟩, ⟨κ, .up⟩]) : {{M | ↓μ ν}ᵀ | μ ↓ν = {M | μ ↓ν}ᵀ | ↓μ ν}ᵀ := by
  tensor_slots

end Metric

end Tensors.Notation
