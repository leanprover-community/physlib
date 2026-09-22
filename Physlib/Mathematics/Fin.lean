/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Mathlib.Algebra.Order.Group.Nat
public import Mathlib.Algebra.Order.Monoid.NatCast
public import Mathlib.Logic.Equiv.Fin.Basic
/-!
# Fin lemmas

The purpose of this file is to define some results Fin currently
in Mathlib.

At some point these should either be up-streamed to Mathlib or replaced with definitions already
in Mathlib.

-/

@[expose] public section
namespace Physlib.Fin

open _root_.Physlib.Fin
variable {n : Nat}

/-- Given a `i` and `x` in `Fin n.succ.succ` returns an element of `Fin n.succ`
  subtracting 1 if `i.val ≤ x.val` else casting x. -/
def predAboveI (i x : Fin n.succ.succ) : Fin n.succ :=
  if h : x.val < i.val then
    ⟨x.val, by omega⟩
  else
    ⟨x.val - 1, by omega⟩

lemma predAboveI_self (i : Fin n.succ.succ) : predAboveI i i = ⟨i.val - 1, by omega⟩ := by
  simp [predAboveI]

@[simp]
lemma predAboveI_succAbove (i : Fin n.succ.succ) (x : Fin n.succ) :
    predAboveI i (Fin.succAbove i x) = x := by
  simp only [predAboveI, Fin.succAbove, Fin.ext_iff, apply_dite Fin.val, apply_ite Fin.val,
    Fin.lt_def, Fin.val_castSucc, Fin.val_succ]
  split_ifs <;> omega

lemma succsAbove_predAboveI {i x : Fin n.succ.succ} (h : i ≠ x) :
    Fin.succAbove i (predAboveI i x) = x := by
  replace h := Fin.val_ne_of_ne h
  simp only [Fin.succAbove, predAboveI, Fin.ext_iff, apply_dite Fin.val, apply_ite Fin.val,
    Fin.lt_def, Fin.val_castSucc, Fin.val_succ]
  split_ifs <;> omega

lemma predAboveI_eq_iff {i x : Fin n.succ.succ} (h : i ≠ x) (y : Fin n.succ) :
    y = predAboveI i x ↔ i.succAbove y = x := by
  apply Iff.intro <;> intro h
  · subst h
    rw [succsAbove_predAboveI h]
  · simp [← h]

lemma predAboveI_lt {i x : Fin n.succ.succ} (h : x.val < i.val) :
    predAboveI i x = ⟨x.val, by omega⟩ := by
  simp [predAboveI, h]

lemma predAboveI_ge {i x : Fin n.succ.succ} (h : i.val < x.val) :
    predAboveI i x = ⟨x.val - 1, by omega⟩ := by
  simp only [Nat.succ_eq_add_one, predAboveI, Fin.val_fin_lt, dite_eq_right_iff, Fin.mk.injEq]
  omega

lemma succAbove_succAbove_predAboveI (i : Fin n.succ.succ) (j : Fin n.succ) (x : Fin n) :
    i.succAbove (j.succAbove x) =
    (i.succAbove j).succAbove ((predAboveI (i.succAbove j) i).succAbove x) := by
  rw [← (predAboveI_eq_iff (Fin.succAbove_ne i j) (j.predAbove i)).mpr
      (Fin.succAbove_succAbove_predAbove i j),
    Fin.succAbove_succAbove_succAbove_predAbove]

/-- The equivalence between `Fin n.succ` and `Fin 1 ⊕ Fin n` extracting the
  `i`th component. -/
def finExtractOne {n : ℕ} (i : Fin (n + 1)) : Fin (n + 1) ≃ Fin 1 ⊕ Fin n :=
  (finCongr (by omega : n.succ = i + 1 + (n - i))).trans <|
  finSumFinEquiv.symm.trans <|
  (Equiv.sumCongr (finSumFinEquiv.symm.trans (Equiv.sumComm (Fin i) (Fin 1)))
    (Equiv.refl (Fin (n-i)))).trans <|
  (Equiv.sumAssoc (Fin 1) (Fin i) (Fin (n - i))).trans <|
  Equiv.sumCongr (Equiv.refl (Fin 1)) (finSumFinEquiv.trans (finCongr (by omega)))

@[simp]
lemma finExtractOne_apply_eq {n : ℕ} (i : Fin n.succ) :
    finExtractOne i i = Sum.inl 0 := by
  rw [← Equiv.eq_symm_apply]
  rfl

lemma finExtractOne_symm_inr {n : ℕ} (i : Fin n.succ) :
    (finExtractOne i).symm ∘ Sum.inr = i.succAbove := by
  ext x
  simp only [Nat.succ_eq_add_one, finExtractOne, Function.comp_apply, Equiv.symm_trans_apply,
    finCongr_symm, Equiv.symm_symm, Equiv.sumCongr_symm, Equiv.refl_symm, Equiv.sumCongr_apply,
    Equiv.coe_refl, Sum.map_inr, finCongr_apply, Fin.val_cast]
  change (finSumFinEquiv
    (Sum.map (⇑(finSumFinEquiv.symm.trans (Equiv.sumComm (Fin ↑i) (Fin 1))).symm) id
    ((Equiv.sumAssoc (Fin 1) (Fin ↑i) (Fin (n - i))).symm
    (Sum.inr (finSumFinEquiv.symm (Fin.cast _ x)))))).val = _
  by_cases hi : x.1 < i.1
  · generalize_proofs hp
    have h1 : (finSumFinEquiv.symm (Fin.cast hp x)) =
        Sum.inl ⟨x, hi⟩ := by
      rw [← finSumFinEquiv_symm_apply_castAdd]
      rfl
    rw [h1]
    simp only [Nat.succ_eq_add_one, Equiv.sumAssoc_symm_apply_inr_inl, Sum.map_inl,
      Equiv.symm_trans_apply, Equiv.symm_symm, Equiv.sumComm_symm, Equiv.sumComm_apply,
      Sum.swap_inr, finSumFinEquiv_apply_left, Fin.castAdd_mk]
    rw [Fin.succAbove]
    split
    · rfl
    rename_i hn
    simp_all only [Nat.succ_eq_add_one, not_lt, Fin.le_def, Fin.val_castSucc, Fin.val_succ,
      left_eq_add]
    omega
  · generalize_proofs hp
    have h1 : (finSumFinEquiv.symm (Fin.cast hp x)) =
        Sum.inr ⟨x - i, by omega⟩ := by
      rw [← finSumFinEquiv_symm_apply_natAdd]
      apply congrArg
      ext
      simp only [Nat.succ_eq_add_one, Fin.val_cast, Fin.natAdd_mk]
      omega
    rw [h1, Fin.succAbove]
    split
    · rename_i hn
      simp_all [Fin.lt_def]
    simp only [Nat.succ_eq_add_one, Equiv.sumAssoc_symm_apply_inr_inr, Sum.map_inr, id_eq,
      finSumFinEquiv_apply_right, Fin.natAdd_mk, Fin.val_succ]
    omega

@[simp]
lemma finExtractOne_symm_inr_apply {n : ℕ} (i : Fin n.succ) (x : Fin n) :
    (finExtractOne i).symm (Sum.inr x) = i.succAbove x := calc
  _ = ((finExtractOne i).symm ∘ Sum.inr) x := rfl
  _ = i.succAbove x := by rw [finExtractOne_symm_inr]

@[simp]
lemma finExtractOne_symm_inl_apply {n : ℕ} (i : Fin n.succ) :
    (finExtractOne i).symm (Sum.inl 0) = i := by
  rfl

lemma finExtractOne_apply_neq {n : ℕ} (i j : Fin (n + 1 + 1)) (hij : i ≠ j) :
    finExtractOne i j = Sum.inr (predAboveI i j) := by
  symm
  apply (Equiv.symm_apply_eq _).mp ?_
  simp only [Nat.succ_eq_add_one, finExtractOne_symm_inr_apply]
  exact succsAbove_predAboveI hij

/-- Given an equivalence `Fin n.succ.succ ≃ Fin n.succ.succ`, and an `i : Fin n.succ.succ`,
  the map `Fin n.succ → Fin n.succ` obtained by dropping `i` and it's image. -/
def finExtractOnPermHom {m : ℕ} (i : Fin n.succ.succ) (σ : Fin n.succ.succ ≃ Fin m.succ.succ) :
    Fin n.succ → Fin m.succ := fun x => predAboveI (σ i) (σ ((finExtractOne i).symm (Sum.inr x)))

lemma finExtractOnPermHom_inv {m : ℕ} (i : Fin n.succ.succ)
    (σ : Fin n.succ.succ ≃ Fin m.succ.succ) :
    (finExtractOnPermHom (σ i) σ.symm) ∘ (finExtractOnPermHom i σ) = id := by
  funext x
  have hσ : σ i ≠ σ (i.succAbove x) := by simp
  simp only [Function.comp_apply, finExtractOnPermHom, finExtractOne_symm_inr_apply,
    Equiv.symm_apply_apply, succsAbove_predAboveI hσ, predAboveI_succAbove, id_eq]

/-- Given an equivalence `Fin n.succ.succ ≃ Fin n.succ.succ`, and an `i : Fin n.succ.succ`,
  the equivalence `Fin n.succ ≃ Fin n.succ` obtained by dropping `i` and it's image. -/
def finExtractOnePerm {m : ℕ} (i : Fin n.succ.succ) (σ : Fin n.succ.succ ≃ Fin m.succ.succ) :
    Fin n.succ ≃ Fin m.succ where
  toFun x := finExtractOnPermHom i σ x
  invFun x := finExtractOnPermHom (σ i) σ.symm x
  left_inv x := by simpa using congrFun (finExtractOnPermHom_inv i σ) x
  right_inv x := by simpa using congrFun (finExtractOnPermHom_inv (σ i) σ.symm) x

lemma finExtractOnePerm_equiv {n m : ℕ} (e : Fin n.succ.succ ≃ Fin m.succ.succ)
    (i : Fin n.succ.succ) :
    e ∘ i.succAbove = (e i).succAbove ∘ finExtractOnePerm i e := by
  funext x
  have hσ : e i ≠ e (i.succAbove x) := by simp
  simp only [Function.comp_apply, finExtractOnePerm, finExtractOnPermHom, Equiv.coe_fn_mk,
    finExtractOne_symm_inr_apply, succsAbove_predAboveI hσ]

@[simp]
lemma finExtractOnePerm_apply (i : Fin n.succ.succ) (σ : Fin n.succ.succ ≃ Fin n.succ.succ)
    (x : Fin n.succ) : finExtractOnePerm i σ x = predAboveI (σ i)
    (σ ((finExtractOne i).symm (Sum.inr x))) := rfl

@[simp]
lemma finExtractOnePerm_symm_apply (i : Fin n.succ.succ) (σ : Fin n.succ.succ ≃ Fin n.succ.succ)
    (x : Fin n.succ) : (finExtractOnePerm i σ).symm x = predAboveI (σ.symm (σ i))
    (σ.symm ((finExtractOne (σ i)).symm (Sum.inr x))) := rfl

/-- The equivalence of types `Fin n.succ.succ ≃ (Fin 1 ⊕ Fin 1) ⊕ Fin n` extracting
  the `i` and `(i.succAbove j)`. -/
def finExtractTwo {n : ℕ} (i : Fin n.succ.succ) (j : Fin n.succ) :
    Fin n.succ.succ ≃ (Fin 1 ⊕ Fin 1) ⊕ Fin n :=
  (finExtractOne i).trans <|
  (Equiv.sumCongr (Equiv.refl (Fin 1)) (finExtractOne j)).trans <|
  (Equiv.sumAssoc (Fin 1) (Fin 1) (Fin n)).symm

@[simp]
lemma finExtractTwo_apply_fst {n : ℕ} (i : Fin n.succ.succ) (j : Fin n.succ) :
    finExtractTwo i j i = Sum.inl (Sum.inl 0) := by
  simp [finExtractTwo]

lemma finExtractTwo_symm_inr {n : ℕ} (i : Fin n.succ.succ) (j : Fin n.succ) :
    (finExtractTwo i j).symm ∘ Sum.inr = i.succAbove ∘ j.succAbove := by
  ext1 x
  simp [finExtractTwo]

@[simp]
lemma finExtractTwo_symm_inr_apply {n : ℕ} (i : Fin n.succ.succ) (j : Fin n.succ) (x : Fin n) :
    (finExtractTwo i j).symm (Sum.inr x) = i.succAbove (j.succAbove x) := by
  simp [finExtractTwo]

@[simp]
lemma finExtractTwo_symm_inl_inr_apply {n : ℕ} (i : Fin n.succ.succ) (j : Fin n.succ) :
    (finExtractTwo i j).symm (Sum.inl (Sum.inr 0)) = i.succAbove j := by
  simp [finExtractTwo]

@[simp]
lemma finExtractTwo_symm_inl_inl_apply {n : ℕ} (i : Fin n.succ.succ) (j : Fin n.succ) :
    (finExtractTwo i j).symm (Sum.inl (Sum.inl 0)) = i := by rfl

@[simp]
lemma finExtractTwo_apply_snd {n : ℕ} (i : Fin n.succ.succ) (j : Fin n.succ) :
    finExtractTwo i j (i.succAbove j) = Sum.inl (Sum.inr 0) := by
  simp [← Equiv.eq_symm_apply]

/-- Takes two maps `Fin n → Fin n` and returns the equivalence they form. -/
def finMapToEquiv (f1 : Fin n → Fin m) (f2 : Fin m → Fin n)
    (h : ∀ x, f1 (f2 x) = x := by decide)
    (h' : ∀ x, f2 (f1 x) = x := by decide) : Fin n ≃ Fin m where
  toFun := f1
  invFun := f2
  left_inv := h'
  right_inv := h

@[simp]
lemma finMapToEquiv_apply {f1 : Fin n → Fin m} {f2 : Fin m → Fin n}
    {h : ∀ x, f1 (f2 x) = x} {h' : ∀ x, f2 (f1 x) = x} (x : Fin n) :
    finMapToEquiv f1 f2 h h' x = f1 x := rfl

@[simp]
lemma finMapToEquiv_symm_apply {f1 : Fin n → Fin m} {f2 : Fin m → Fin n}
    {h : ∀ x, f1 (f2 x) = x} {h' : ∀ x, f2 (f1 x) = x} (x : Fin m) :
    (finMapToEquiv f1 f2 h h').symm x = f2 x := rfl

lemma finMapToEquiv_symm_eq {f1 : Fin n → Fin m} {f2 : Fin m → Fin n}
    {h : ∀ x, f1 (f2 x) = x} {h' : ∀ x, f2 (f1 x) = x} :
    (finMapToEquiv f1 f2 h h').symm = finMapToEquiv f2 f1 h' h := rfl

/-- Given an equivalence between `Fin n` and `Fin m`, the induced equivalence between
  `Fin n.succ` and `Fin m.succ` derived by `Fin.cons`. -/
def equivCons {n m : ℕ} (e : Fin n ≃ Fin m) : Fin n.succ ≃ Fin m.succ where
  toFun := Fin.cons 0 (Fin.succ ∘ e.toFun)
  invFun := Fin.cons 0 (Fin.succ ∘ e.invFun)
  left_inv i := by induction i using Fin.cases <;> simp
  right_inv i := by induction i using Fin.cases <;> simp

@[simp]
lemma equivCons_zero {n m : ℕ} (e : Fin n ≃ Fin m) :
    equivCons e 0 = 0 := rfl

@[simp]
lemma equivCons_trans {n m k : ℕ} (e : Fin n ≃ Fin m) (f : Fin m ≃ Fin k) :
    Fin.equivCons (e.trans f) = (Fin.equivCons e).trans (Fin.equivCons f) := by
  ext x
  induction x using Fin.cases <;> rfl

@[simp]
lemma equivCons_castOrderIso {n m : ℕ} (h : n = m) :
    (Fin.equivCons (Fin.castOrderIso h).toEquiv) = (Fin.castOrderIso (by simp [h])).toEquiv := by
  ext x
  induction x using Fin.cases <;> rfl

@[simp]
lemma equivCons_symm_succ {n m : ℕ} (e : Fin n ≃ Fin m) (i : ℕ) (hi : i + 1 < m.succ) :
    (Fin.equivCons e).symm ⟨i + 1, hi⟩ = (e.symm ⟨i, Nat.succ_lt_succ_iff.mp hi⟩).succ := rfl

@[simp]
lemma equivCons_succ {n m : ℕ} (e : Fin n ≃ Fin m) (i : ℕ) (hi : i + 1 < n.succ) :
    (Fin.equivCons e) ⟨i + 1, hi⟩ = (e ⟨i, Nat.succ_lt_succ_iff.mp hi⟩).succ := rfl

end Physlib.Fin
