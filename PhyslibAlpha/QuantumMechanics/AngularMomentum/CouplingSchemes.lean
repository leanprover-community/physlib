/-
Copyright (c) 2026 Daniel Leonforte. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Leonforte
-/
module

public import PhyslibAlpha.QuantumMechanics.AngularMomentum.ClebschGordanFormula

/-!

# The two coupling schemes of three angular momenta

The irreducible components of `V(m) ⊗ V(n)` as isometric embeddings, the triple tensor product
`V(a) ⊗ V(b) ⊗ V(c)` with its Casimir operator, and the two ways of coupling three angular
momenta.

## i. Overview

Three angular momenta `j₁ = a/2`, `j₂ = b/2`, `j₃ = c/2` live on
`V(a) ⊗ V(b) ⊗ V(c)`. A state of total angular momentum `J` and projection `M` can be built in
two ways:

- `|(j₁ j₂) j₁₂, j₃; J M⟩`: first couple `j₁` and `j₂` to `j₁₂`, then `j₁₂` and `j₃` to `J`;
- `|j₁, (j₂ j₃) j₂₃; J M⟩`: first couple `j₂` and `j₃` to `j₂₃`, then `j₁` and `j₂₃` to `J`.

Both are built from the Clebsch–Gordan states `coupledVec` of `ClebschGordanCoefficients`. The
`k`-th irreducible component of `V(m) ⊗ V(n)` is the image of the isometric embedding
`embed : V(m + n - 2k) → V(m) ⊗ V(n)`, `u_l ↦ |J, J - l⟩`, which intertwines `E`, `F` and `H`
(it is a rescaled inverse of `cgEquiv`). The first scheme is `embed ⊗ 1` applied to the coupled
states of `V(a + b - 2k₁) ⊗ V(c)`, the second is `1 ⊗ embed` followed by the associator.

The recoupling coefficients between the two schemes and the 6j symbols are in `SixJ`.

## ii. Key results

- `embed`, `tensorForm_embed`, `tensorF_embed`: the isometric intertwining embeddings.
- `Triple`, `tripleForm`, `tripleE`, `tripleF`, `tripleH`: the triple tensor product with its
  contravariant form and the total `E`, `F`, `H`.
- `tensorCas`, `tripleCas`: the Casimir operators.
- `stateA`, `stateB`: the two coupling schemes.

## iii. Table of contents

- A. The irreducible components as isometric embeddings
- B. The triple tensor product
- C. The Casimir operator
- D. The two coupling schemes

## iv. References

- A. R. Edmonds, *Angular Momentum in Quantum Mechanics*, Princeton University Press (1957),
  chapter 6.

## A. The irreducible components as isometric embeddings

-/

@[expose] public section

noncomputable section

namespace PhyslibAlpha.Sl2

open StandardSl2Module

open scoped TensorProduct

section Embed

variable {m n : ℕ} (hmn : 0 < m + n) (k : Fin (min m n + 1))

/-- The isometric embedding `V(m + n - 2k) → V(m) ⊗ V(n)` onto the `k`-th irreducible component,
`u_l ↦ |J, J - l⟩`. -/
def embed : StandardSl2Module ℝ (m + n - 2 * (k : ℕ)) →ₗ[ℝ]
    StandardSl2Module ℝ m ⊗[ℝ] StandardSl2Module ℝ n :=
  (Real.sqrt (hwNormSq m n k))⁻¹ •
    ((cgEquiv (K := ℝ) hmn).symm.toLinearMap ∘ₗ DirectSum.lof ℝ _ (CGSummand ℝ m n) k)

lemma cgEquiv_symm_sumVec (l : ℕ) :
    (cgEquiv (K := ℝ) hmn).symm (DirectSum.lof ℝ _ (CGSummand ℝ m n) k (vNat _ l)) =
      stringVec m n k l := by
  rw [LinearEquiv.symm_apply_eq, cgEquiv_stringVec, sumVec]

lemma embed_vNat (l : ℕ) :
    embed hmn k (vNat _ l) = (Real.sqrt (hwNormSq m n k))⁻¹ • stringVec m n k l := by
  rw [embed, LinearMap.smul_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
    cgEquiv_symm_sumVec]

lemma embed_normVec (l : ℕ) : embed hmn k (normVec _ l) = coupledVec m n k l := by
  rw [normVec, map_smul, embed_vNat, smul_smul, coupledVec, Real.sqrt_mul (Nat.cast_nonneg _),
    mul_inv]

lemma tensorF_embed (x : StandardSl2Module ℝ (m + n - 2 * (k : ℕ))) :
    tensorF m n (embed hmn k x) = embed hmn k (ρF x) := by
  simp only [embed, LinearMap.smul_apply, LinearMap.comp_apply, LinearEquiv.coe_coe, map_smul]
  congr 1
  apply (cgEquiv (K := ℝ) hmn).injective
  rw [cgEquiv_tensorF, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply, sumEnd_lof]

lemma tensorE_embed (x : StandardSl2Module ℝ (m + n - 2 * (k : ℕ))) :
    tensorE m n (embed hmn k x) = embed hmn k (ρE x) := by
  simp only [embed, LinearMap.smul_apply, LinearMap.comp_apply, LinearEquiv.coe_coe, map_smul]
  congr 1
  apply (cgEquiv (K := ℝ) hmn).injective
  rw [cgEquiv_tensorE, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply, sumEnd_lof]

lemma tensorH_embed (x : StandardSl2Module ℝ (m + n - 2 * (k : ℕ))) :
    tensorH m n (embed hmn k x) = embed hmn k (ρH x) := by
  simp only [embed, LinearMap.smul_apply, LinearMap.comp_apply, LinearEquiv.coe_coe, map_smul]
  congr 1
  apply (cgEquiv (K := ℝ) hmn).injective
  rw [cgEquiv_tensorH, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply, sumEnd_lof]

/-- The embedding is an isometry. -/
lemma tensorForm_embed (x y : StandardSl2Module ℝ (m + n - 2 * (k : ℕ))) :
    tensorForm m n (embed hmn k x) (embed hmn k y) = invForm ℝ _ x y := by
  have hkm : (k : ℕ) ≤ m := by have := k.isLt; omega
  have hkn : (k : ℕ) ≤ n := by have := k.isLt; omega
  have hw := hwNormSq_pos hkm hkn
  have hs := Real.mul_self_sqrt hw.le
  have h : (tensorForm m n).compl₁₂ (embed hmn k) (embed hmn k) = invForm ℝ _ :=
    bilin_ext_vNat fun a b => by
      simp only [LinearMap.compl₁₂_apply, embed_vNat, map_smul, LinearMap.smul_apply,
        smul_eq_mul]
      rw [tensorForm_stringVec hmn hkm hkn hkm hkn, invForm_vNat, ← hwNormSq]
      by_cases hab : a = b
      · subst hab
        rw [ite_eq_left ⟨rfl, rfl⟩]
        by_cases ha : a ≤ m + n - 2 * (k : ℕ)
        · rw [ite_eq_left ⟨rfl, ha⟩]
          calc (Real.sqrt (hwNormSq m n k))⁻¹ * ((Real.sqrt (hwNormSq m n k))⁻¹ *
                ((normSq (m + n - 2 * (k : ℕ)) a : ℝ) * hwNormSq m n k)) =
              (normSq (m + n - 2 * (k : ℕ)) a : ℝ) *
                (hwNormSq m n k / (Real.sqrt (hwNormSq m n k) * Real.sqrt (hwNormSq m n k))) := by
                ring
            _ = _ := by rw [hs, div_self hw.ne', mul_one]
        · have h0 : (normSq (m + n - 2 * (k : ℕ)) a : ℝ) = 0 := by
            rw [normSq, Nat.descFactorial_eq_zero_iff_lt.mpr (by omega), mul_zero, Nat.cast_zero]
          rw [ite_eq_right (fun h => ha h.2), h0]
          ring
      · rw [ite_eq_right (fun h => hab h.2), ite_eq_right (fun h => hab h.1), mul_zero, mul_zero]
  exact LinearMap.congr_fun (LinearMap.congr_fun h x) y

/-- Different components are orthogonal. -/
lemma tensorForm_embed_of_ne {k' : Fin (min m n + 1)} (hkk : k ≠ k')
    (x : StandardSl2Module ℝ (m + n - 2 * (k : ℕ)))
    (y : StandardSl2Module ℝ (m + n - 2 * (k' : ℕ))) :
    tensorForm m n (embed hmn k x) (embed hmn k' y) = 0 := by
  have hkm : (k : ℕ) ≤ m := by have := k.isLt; omega
  have hkn : (k : ℕ) ≤ n := by have := k.isLt; omega
  have hk'm : (k' : ℕ) ≤ m := by have := k'.isLt; omega
  have hk'n : (k' : ℕ) ≤ n := by have := k'.isLt; omega
  have h : (tensorForm m n).compl₁₂ (embed hmn k) (embed hmn k') = 0 :=
    linearMap_ext_vNat fun a => linearMap_ext_vNat fun b => by
      simp only [LinearMap.compl₁₂_apply, LinearMap.zero_apply, embed_vNat, map_smul,
        LinearMap.smul_apply, smul_eq_mul]
      rw [tensorForm_stringVec hmn hkm hkn hk'm hk'n, ite_eq_right (fun h => hkk (Fin.ext h.1)),
        mul_zero, mul_zero]
  exact LinearMap.congr_fun (LinearMap.congr_fun h x) y

end Embed

/-!

## B. The triple tensor product

-/

section Triple

variable (a b c : ℕ)

/-- `V(a) ⊗ V(b) ⊗ V(c)`, bracketed as `(V(a) ⊗ V(b)) ⊗ V(c)`. -/
abbrev Triple : Type :=
  (StandardSl2Module ℝ a ⊗[ℝ] StandardSl2Module ℝ b) ⊗[ℝ] StandardSl2Module ℝ c

/-- The contravariant form on the triple product. -/
def tripleForm : LinearMap.BilinForm ℝ (Triple a b c) :=
  LinearMap.BilinForm.tmul (tensorForm a b) (invForm ℝ c)

/-- The total raising operator on the triple product. -/
def tripleE : Module.End ℝ (Triple a b c) := diagEnd (tensorE a b) ρE

/-- The total lowering operator on the triple product. -/
def tripleF : Module.End ℝ (Triple a b c) := diagEnd (tensorF a b) ρF

/-- The total weight operator on the triple product. -/
def tripleH : Module.End ℝ (Triple a b c) := diagEnd (tensorH a b) ρH

variable {a b c}

lemma tripleForm_tmul (x x' : StandardSl2Module ℝ a ⊗[ℝ] StandardSl2Module ℝ b)
    (y y' : StandardSl2Module ℝ c) :
    tripleForm a b c (x ⊗ₜ y) (x' ⊗ₜ y') = tensorForm a b x x' * invForm ℝ c y y' := by
  rw [tripleForm, LinearMap.BilinForm.tensorDistrib_tmul, smul_eq_mul, mul_comm]

lemma tripleBilin_ext {B B' : LinearMap.BilinForm ℝ (Triple a b c)}
    (h : ∀ x y z x' y' z', B ((x ⊗ₜ y) ⊗ₜ z) ((x' ⊗ₜ y') ⊗ₜ z') =
      B' ((x ⊗ₜ y) ⊗ₜ z) ((x' ⊗ₜ y') ⊗ₜ z')) : B = B' :=
  TensorProduct.ext_threefold fun x y z =>
    TensorProduct.ext_threefold fun x' y' z' => h x y z x' y' z'

lemma invForm_ρF_apply {n : ℕ} (x y : StandardSl2Module ℝ n) :
    invForm ℝ n (ρF x) y = invForm ℝ n x (ρE y) := by
  rw [invForm_comm, ← invForm_ρE_apply, invForm_comm]

lemma tripleForm_tripleF (u v : Triple a b c) :
    tripleForm a b c (tripleF a b c u) v = tripleForm a b c u (tripleE a b c v) := by
  have h : LinearMap.comp (tripleForm a b c) (tripleF a b c) =
      LinearMap.compl₂ (tripleForm a b c) (tripleE a b c) :=
    tripleBilin_ext fun x y z x' y' z' => by
      simp only [LinearMap.comp_apply, LinearMap.compl₂_apply, tripleF, tripleE, diagEnd_tmul,
        map_add, LinearMap.add_apply, tripleForm_tmul, tensorForm_tensorF, invForm_ρF_apply]
  exact LinearMap.congr_fun (LinearMap.congr_fun h u) v

lemma tripleForm_tripleE (u v : Triple a b c) :
    tripleForm a b c (tripleE a b c u) v = tripleForm a b c u (tripleF a b c v) := by
  have h : LinearMap.comp (tripleForm a b c) (tripleE a b c) =
      LinearMap.compl₂ (tripleForm a b c) (tripleF a b c) :=
    tripleBilin_ext fun x y z x' y' z' => by
      simp only [LinearMap.comp_apply, LinearMap.compl₂_apply, tripleF, tripleE, diagEnd_tmul,
        map_add, LinearMap.add_apply, tripleForm_tmul, tensorForm_tensorE, invForm_ρE_apply]
  exact LinearMap.congr_fun (LinearMap.congr_fun h u) v

lemma tripleForm_tripleH (u v : Triple a b c) :
    tripleForm a b c (tripleH a b c u) v = tripleForm a b c u (tripleH a b c v) := by
  have h : LinearMap.comp (tripleForm a b c) (tripleH a b c) =
      LinearMap.compl₂ (tripleForm a b c) (tripleH a b c) :=
    tripleBilin_ext fun x y z x' y' z' => by
      simp only [LinearMap.comp_apply, LinearMap.compl₂_apply, tripleH, diagEnd_tmul,
        map_add, LinearMap.add_apply, tripleForm_tmul, tensorForm_tensorH, invForm_ρH_apply]
  exact LinearMap.congr_fun (LinearMap.congr_fun h u) v

lemma tripleForm_assoc_symm (x x' : StandardSl2Module ℝ a)
    (w w' : StandardSl2Module ℝ b ⊗[ℝ] StandardSl2Module ℝ c) :
    tripleForm a b c ((TensorProduct.assoc ℝ _ _ _).symm (x ⊗ₜ w))
      ((TensorProduct.assoc ℝ _ _ _).symm (x' ⊗ₜ w')) = invForm ℝ a x x' * tensorForm b c w w' := by
  induction w using TensorProduct.inductionOn with
  | tmul y z =>
    induction w' using TensorProduct.inductionOn with
    | tmul y' z' =>
      rw [TensorProduct.assoc_symm_tmul, TensorProduct.assoc_symm_tmul, tripleForm_tmul,
        tensorForm_tmul, tensorForm_tmul]
      ring
    | add w₁ w₂ h₁ h₂ =>
      simp only [TensorProduct.tmul_add, map_add, h₁, h₂]
      ring
  | add w₁ w₂ h₁ h₂ =>
    simp only [TensorProduct.tmul_add, map_add, LinearMap.add_apply, h₁, h₂]
    ring

lemma tripleF_assoc_symm (x : StandardSl2Module ℝ a)
    (w : StandardSl2Module ℝ b ⊗[ℝ] StandardSl2Module ℝ c) :
    tripleF a b c ((TensorProduct.assoc ℝ _ _ _).symm (x ⊗ₜ w)) =
      (TensorProduct.assoc ℝ _ _ _).symm (ρF x ⊗ₜ w + x ⊗ₜ tensorF b c w) := by
  induction w using TensorProduct.inductionOn with
  | tmul y z =>
    simp only [TensorProduct.assoc_symm_tmul, tripleF, tensorF, diagEnd_tmul, map_add,
      TensorProduct.add_tmul, TensorProduct.tmul_add]
    abel
  | add w₁ w₂ h₁ h₂ =>
    simp only [TensorProduct.tmul_add, map_add, h₁, h₂]
    abel

lemma tripleE_assoc_symm (x : StandardSl2Module ℝ a)
    (w : StandardSl2Module ℝ b ⊗[ℝ] StandardSl2Module ℝ c) :
    tripleE a b c ((TensorProduct.assoc ℝ _ _ _).symm (x ⊗ₜ w)) =
      (TensorProduct.assoc ℝ _ _ _).symm (ρE x ⊗ₜ w + x ⊗ₜ tensorE b c w) := by
  induction w using TensorProduct.inductionOn with
  | tmul y z =>
    simp only [TensorProduct.assoc_symm_tmul, tripleE, tensorE, diagEnd_tmul, map_add,
      TensorProduct.add_tmul, TensorProduct.tmul_add]
    abel
  | add w₁ w₂ h₁ h₂ =>
    simp only [TensorProduct.tmul_add, map_add, h₁, h₂]
    abel

lemma tripleH_assoc_symm (x : StandardSl2Module ℝ a)
    (w : StandardSl2Module ℝ b ⊗[ℝ] StandardSl2Module ℝ c) :
    tripleH a b c ((TensorProduct.assoc ℝ _ _ _).symm (x ⊗ₜ w)) =
      (TensorProduct.assoc ℝ _ _ _).symm (ρH x ⊗ₜ w + x ⊗ₜ tensorH b c w) := by
  induction w using TensorProduct.inductionOn with
  | tmul y z =>
    simp only [TensorProduct.assoc_symm_tmul, tripleH, tensorH, diagEnd_tmul, map_add,
      TensorProduct.add_tmul, TensorProduct.tmul_add]
    abel
  | add w₁ w₂ h₁ h₂ =>
    simp only [TensorProduct.tmul_add, map_add, h₁, h₂]
    abel

lemma tripleForm_comm (u v : Triple a b c) : tripleForm a b c u v = tripleForm a b c v u := by
  have h : tripleForm a b c = LinearMap.flip (tripleForm a b c) :=
    tripleBilin_ext fun x y z x' y' z' => by
      rw [LinearMap.flip_apply, tripleForm_tmul, tripleForm_tmul, tensorForm_comm, invForm_comm]
  rw [h, LinearMap.flip_apply, ← h]

end Triple

/-!

## C. The Casimir operator

-/

section Casimir

variable {m n : ℕ}

variable (m n) in
/-- `2 J² = E F + F E + H²/2` on `V(m) ⊗ V(n)`. -/
def tensorCas : Module.End ℝ (StandardSl2Module ℝ m ⊗[ℝ] StandardSl2Module ℝ n) :=
  tensorE m n * tensorF m n + tensorF m n * tensorE m n + (1 / 2 : ℝ) • (tensorH m n * tensorH m n)

/-- `2 J² = N(N + 2)/2 = 2 J(J + 1)` on the `k`-th string, `N = m + n - 2k`. -/
lemma tensorCas_stringVec {k : ℕ} (hmn : 0 < m + n) (hkm : k ≤ m) (hkn : k ≤ n) (l : ℕ) :
    tensorCas m n (stringVec m n k l) =
      (((m + n - 2 * k : ℕ) : ℝ) * (((m + n - 2 * k : ℕ) : ℝ) + 2) / 2) • stringVec m n k l := by
  rcases l with _ | l
  · simp only [tensorCas, LinearMap.add_apply, Module.End.mul_apply, LinearMap.smul_apply,
      tensorF_stringVec, tensorE_stringVec_succ hmn hkm hkn, tensorE_stringVec_zero hkm hkn,
      map_zero, tensorH_stringVec hmn hkm hkn, map_smul, Nat.cast_zero]
    module
  · simp only [tensorCas, LinearMap.add_apply, Module.End.mul_apply, LinearMap.smul_apply,
      tensorF_stringVec, tensorE_stringVec_succ hmn hkm hkn, tensorH_stringVec hmn hkm hkn,
      map_smul, Nat.cast_add, Nat.cast_one]
    module

lemma tensorCas_coupledVec {k : ℕ} (hmn : 0 < m + n) (hkm : k ≤ m) (hkn : k ≤ n) (l : ℕ) :
    tensorCas m n (coupledVec m n k l) =
      (((m + n - 2 * k : ℕ) : ℝ) * (((m + n - 2 * k : ℕ) : ℝ) + 2) / 2) • coupledVec m n k l := by
  rw [coupledVec, map_smul, tensorCas_stringVec hmn hkm hkn, smul_comm]

variable (a b c : ℕ) in
/-- `2 J²` on the triple product. -/
def tripleCas : Module.End ℝ (Triple a b c) :=
  tripleE a b c * tripleF a b c + tripleF a b c * tripleE a b c +
    (1 / 2 : ℝ) • (tripleH a b c * tripleH a b c)

lemma tripleForm_tripleCas {a b c : ℕ} (u v : Triple a b c) :
    tripleForm a b c (tripleCas a b c u) v = tripleForm a b c u (tripleCas a b c v) := by
  simp only [tripleCas, LinearMap.add_apply, Module.End.mul_apply, LinearMap.smul_apply, map_add,
    map_smul, LinearMap.add_apply, LinearMap.smul_apply]
  rw [tripleForm_tripleE, tripleForm_tripleF, tripleForm_tripleF, tripleForm_tripleE,
    tripleForm_tripleH, tripleForm_tripleH]

end Casimir

/-!

## D. The two coupling schemes

-/

section States

variable {a b c : ℕ}

/-- `|(j₁ j₂) j₁₂, j₃; J, M⟩`: `j₁ = a/2`, `j₂ = b/2`, `j₃ = c/2`, `j₁₂ = (a + b)/2 - k₁`,
`J = j₁₂ + j₃ - k₂`, `M = J - l`. -/
def stateA (hab : 0 < a + b) (k₁ : Fin (min a b + 1)) (k₂ l : ℕ) : Triple a b c :=
  (embed hab k₁).rTensor _ (coupledVec (a + b - 2 * (k₁ : ℕ)) c k₂ l)

/-- `V(a) ⊗ V(b + c - 2k₃) → V(a) ⊗ V(b) ⊗ V(c)`, through the `k₃`-th component of
`V(b) ⊗ V(c)`. -/
def assocEmbed (hbc : 0 < b + c) (k₃ : Fin (min b c + 1)) :
    StandardSl2Module ℝ a ⊗[ℝ] StandardSl2Module ℝ (b + c - 2 * (k₃ : ℕ)) →ₗ[ℝ] Triple a b c :=
  (TensorProduct.assoc ℝ _ _ _).symm.toLinearMap ∘ₗ (embed hbc k₃).lTensor _

/-- `|j₁, (j₂ j₃) j₂₃; J, M⟩`: `j₂₃ = (b + c)/2 - k₃`, `J = j₁ + j₂₃ - k₄`, `M = J - l`. -/
def stateB (hbc : 0 < b + c) (k₃ : Fin (min b c + 1)) (k₄ l : ℕ) : Triple a b c :=
  assocEmbed hbc k₃ (coupledVec a (b + c - 2 * (k₃ : ℕ)) k₄ l)

section A

variable (hab : 0 < a + b) (k₁ : Fin (min a b + 1))

lemma tripleF_rTensor_embed
    (u : StandardSl2Module ℝ (a + b - 2 * (k₁ : ℕ)) ⊗[ℝ] StandardSl2Module ℝ c) :
    tripleF a b c ((embed hab k₁).rTensor _ u) = (embed hab k₁).rTensor _ (tensorF _ c u) := by
  have h : tripleF a b c ∘ₗ (embed hab k₁).rTensor _ = (embed hab k₁).rTensor _ ∘ₗ tensorF _ c :=
    TensorProduct.ext' fun x z => by
      rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.rTensor_tmul, tripleF,
        diagEnd_tmul, tensorF_embed, tensorF, diagEnd_tmul, map_add, LinearMap.rTensor_tmul,
        LinearMap.rTensor_tmul]
  exact LinearMap.congr_fun h u

lemma tripleE_rTensor_embed
    (u : StandardSl2Module ℝ (a + b - 2 * (k₁ : ℕ)) ⊗[ℝ] StandardSl2Module ℝ c) :
    tripleE a b c ((embed hab k₁).rTensor _ u) = (embed hab k₁).rTensor _ (tensorE _ c u) := by
  have h : tripleE a b c ∘ₗ (embed hab k₁).rTensor _ = (embed hab k₁).rTensor _ ∘ₗ tensorE _ c :=
    TensorProduct.ext' fun x z => by
      rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.rTensor_tmul, tripleE,
        diagEnd_tmul, tensorE_embed, tensorE, diagEnd_tmul, map_add, LinearMap.rTensor_tmul,
        LinearMap.rTensor_tmul]
  exact LinearMap.congr_fun h u

lemma tripleH_rTensor_embed
    (u : StandardSl2Module ℝ (a + b - 2 * (k₁ : ℕ)) ⊗[ℝ] StandardSl2Module ℝ c) :
    tripleH a b c ((embed hab k₁).rTensor _ u) = (embed hab k₁).rTensor _ (tensorH _ c u) := by
  have h : tripleH a b c ∘ₗ (embed hab k₁).rTensor _ = (embed hab k₁).rTensor _ ∘ₗ tensorH _ c :=
    TensorProduct.ext' fun x z => by
      rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.rTensor_tmul, tripleH,
        diagEnd_tmul, tensorH_embed, tensorH, diagEnd_tmul, map_add, LinearMap.rTensor_tmul,
        LinearMap.rTensor_tmul]
  exact LinearMap.congr_fun h u

lemma tripleCas_rTensor_embed
    (u : StandardSl2Module ℝ (a + b - 2 * (k₁ : ℕ)) ⊗[ℝ] StandardSl2Module ℝ c) :
    tripleCas a b c ((embed hab k₁).rTensor _ u) = (embed hab k₁).rTensor _ (tensorCas _ c u) := by
  simp only [tripleCas, tensorCas, LinearMap.add_apply, Module.End.mul_apply, LinearMap.smul_apply,
    tripleF_rTensor_embed, tripleE_rTensor_embed, tripleH_rTensor_embed, map_add, map_smul]

lemma tripleForm_rTensor_embed
    (u u' : StandardSl2Module ℝ (a + b - 2 * (k₁ : ℕ)) ⊗[ℝ] StandardSl2Module ℝ c) :
    tripleForm a b c ((embed hab k₁).rTensor _ u) ((embed hab k₁).rTensor _ u') =
      tensorForm _ c u u' := by
  have h : LinearMap.compl₁₂ (tripleForm a b c) ((embed hab k₁).rTensor _)
      ((embed hab k₁).rTensor _) = tensorForm _ c :=
    tensorBilin_ext fun x z x' z' => by
      rw [LinearMap.compl₁₂_apply, LinearMap.rTensor_tmul, LinearMap.rTensor_tmul, tripleForm_tmul,
        tensorForm_embed, tensorForm_tmul]
  exact LinearMap.congr_fun (LinearMap.congr_fun h u) u'

lemma tripleForm_rTensor_embed_of_ne {k₁' : Fin (min a b + 1)} (hk : k₁ ≠ k₁')
    (u : StandardSl2Module ℝ (a + b - 2 * (k₁ : ℕ)) ⊗[ℝ] StandardSl2Module ℝ c)
    (u' : StandardSl2Module ℝ (a + b - 2 * (k₁' : ℕ)) ⊗[ℝ] StandardSl2Module ℝ c) :
    tripleForm a b c ((embed hab k₁).rTensor _ u) ((embed hab k₁').rTensor _ u') = 0 := by
  have h : LinearMap.compl₁₂ (tripleForm a b c) ((embed hab k₁).rTensor _)
      ((embed hab k₁').rTensor _) = 0 :=
    TensorProduct.ext' fun x z => TensorProduct.ext' fun x' z' => by
      rw [LinearMap.compl₁₂_apply, LinearMap.rTensor_tmul, LinearMap.rTensor_tmul, tripleForm_tmul,
        tensorForm_embed_of_ne hab k₁ hk, zero_mul, LinearMap.zero_apply, LinearMap.zero_apply]
  exact LinearMap.congr_fun (LinearMap.congr_fun h u) u'

end A

section B

variable (hbc : 0 < b + c) (k₃ : Fin (min b c + 1))

lemma tripleF_assocEmbed
    (w : StandardSl2Module ℝ a ⊗[ℝ] StandardSl2Module ℝ (b + c - 2 * (k₃ : ℕ))) :
    tripleF a b c (assocEmbed hbc k₃ w) = assocEmbed hbc k₃ (tensorF a _ w) := by
  have h : tripleF a b c ∘ₗ assocEmbed hbc k₃ = assocEmbed hbc k₃ ∘ₗ tensorF a _ :=
    TensorProduct.ext' fun x y => by
      simp only [assocEmbed, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearMap.lTensor_tmul,
        tripleF_assoc_symm, tensorF_embed]
      rw [tensorF, diagEnd_tmul]
      simp only [map_add, LinearMap.lTensor_tmul]
  exact LinearMap.congr_fun h w

lemma tripleE_assocEmbed
    (w : StandardSl2Module ℝ a ⊗[ℝ] StandardSl2Module ℝ (b + c - 2 * (k₃ : ℕ))) :
    tripleE a b c (assocEmbed hbc k₃ w) = assocEmbed hbc k₃ (tensorE a _ w) := by
  have h : tripleE a b c ∘ₗ assocEmbed hbc k₃ = assocEmbed hbc k₃ ∘ₗ tensorE a _ :=
    TensorProduct.ext' fun x y => by
      simp only [assocEmbed, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearMap.lTensor_tmul,
        tripleE_assoc_symm, tensorE_embed]
      rw [tensorE, diagEnd_tmul]
      simp only [map_add, LinearMap.lTensor_tmul]
  exact LinearMap.congr_fun h w

lemma tripleH_assocEmbed
    (w : StandardSl2Module ℝ a ⊗[ℝ] StandardSl2Module ℝ (b + c - 2 * (k₃ : ℕ))) :
    tripleH a b c (assocEmbed hbc k₃ w) = assocEmbed hbc k₃ (tensorH a _ w) := by
  have h : tripleH a b c ∘ₗ assocEmbed hbc k₃ = assocEmbed hbc k₃ ∘ₗ tensorH a _ :=
    TensorProduct.ext' fun x y => by
      simp only [assocEmbed, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearMap.lTensor_tmul,
        tripleH_assoc_symm, tensorH_embed]
      rw [tensorH, diagEnd_tmul]
      simp only [map_add, LinearMap.lTensor_tmul]
  exact LinearMap.congr_fun h w

lemma tripleCas_assocEmbed
    (w : StandardSl2Module ℝ a ⊗[ℝ] StandardSl2Module ℝ (b + c - 2 * (k₃ : ℕ))) :
    tripleCas a b c (assocEmbed hbc k₃ w) = assocEmbed hbc k₃ (tensorCas a _ w) := by
  simp only [tripleCas, tensorCas, LinearMap.add_apply, Module.End.mul_apply, LinearMap.smul_apply,
    tripleF_assocEmbed, tripleE_assocEmbed, tripleH_assocEmbed, map_add, map_smul]

lemma tripleForm_assocEmbed
    (w w' : StandardSl2Module ℝ a ⊗[ℝ] StandardSl2Module ℝ (b + c - 2 * (k₃ : ℕ))) :
    tripleForm a b c (assocEmbed hbc k₃ w) (assocEmbed hbc k₃ w') = tensorForm a _ w w' := by
  have h : LinearMap.compl₁₂ (tripleForm a b c) (assocEmbed hbc k₃) (assocEmbed hbc k₃) =
      tensorForm a _ :=
    tensorBilin_ext fun x y x' y' => by
      simp only [assocEmbed, LinearMap.compl₁₂_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
        LinearMap.lTensor_tmul]
      rw [tripleForm_assoc_symm, tensorForm_embed, tensorForm_tmul]
  exact LinearMap.congr_fun (LinearMap.congr_fun h w) w'

lemma tripleForm_assocEmbed_of_ne {k₃' : Fin (min b c + 1)} (hk : k₃ ≠ k₃')
    (w : StandardSl2Module ℝ a ⊗[ℝ] StandardSl2Module ℝ (b + c - 2 * (k₃ : ℕ)))
    (w' : StandardSl2Module ℝ a ⊗[ℝ] StandardSl2Module ℝ (b + c - 2 * (k₃' : ℕ))) :
    tripleForm a b c (assocEmbed hbc k₃ w) (assocEmbed hbc k₃' w') = 0 := by
  have h : LinearMap.compl₁₂ (tripleForm a b c) (assocEmbed hbc k₃) (assocEmbed hbc k₃') = 0 :=
    TensorProduct.ext' fun x y => TensorProduct.ext' fun x' y' => by
      simp only [assocEmbed, LinearMap.compl₁₂_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
        LinearMap.lTensor_tmul, LinearMap.zero_apply]
      rw [tripleForm_assoc_symm, tensorForm_embed_of_ne hbc k₃ hk, mul_zero]
  exact LinearMap.congr_fun (LinearMap.congr_fun h w) w'

end B

end States

end PhyslibAlpha.Sl2
