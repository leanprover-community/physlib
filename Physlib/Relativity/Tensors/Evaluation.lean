/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Relativity.Tensors.Product
public import Physlib.Relativity.Tensors.Contraction.Basis
public import Physlib.Meta.Sorry
/-!

# Evaluation of tensor indices

-/

@[expose] public section

namespace TensorSpecies

variable {k : Type} [CommRing k] {C : Type} {G : Type} [Group G]
    {V : C → Type} [∀ c, AddCommGroup (V c)] [∀ c, Module k (V c)]
    {basisIdx : C → Type} [∀ c, Fintype (basisIdx c)] [∀ c, DecidableEq (basisIdx c)]
    {rep : (c : C) → Representation k G (V c)} {b : (c : C) → Module.Basis (basisIdx c) k (V c)}
    {S : TensorSpecies k C G V basisIdx rep b}

namespace Tensor

namespace Pure

variable {n : ℕ} {c : Fin (n + 1) → C}

/-!

## The evaluation coefficient.

-/

/-- Given a `i : Fin (n + 1)`, a `b : basisIdx (c i)` and a pure tensor
  `p : Pure S c`, `evalPCoeff i b p` is the `b`th component of `p i`. -/
noncomputable def evalPCoeff (i : Fin (n + 1)) (φ : basisIdx (c i)) (p : Pure S c) : k :=
  (b (c i)).repr (p i) φ

@[simp]
lemma evalPCoeff_update_self (i : Fin (n + 1)) [inst : DecidableEq (Fin (n + 1))]
    (φ : basisIdx (c i)) (p : Pure S c)
    (x : V (c i)) :
    evalPCoeff i φ (p.update i x) = (b (c i)).repr x φ := by
  simp [evalPCoeff]

@[simp]
lemma evalPCoeff_update_succAbove (i : Fin (n + 1)) [inst : DecidableEq (Fin (n + 1))]
    (j : Fin n)
    (φ : basisIdx (c i)) (p : Pure S c)
    (x : V (c (i.succAbove j))) :
    evalPCoeff i φ (p.update (i.succAbove j) x) = evalPCoeff i φ p := by
  simp [evalPCoeff]

lemma evalPCoeff_basisVector (i : Fin (n + 1)) (φ : basisIdx (c i)) (b' : ComponentIdx (S := S) c) :
    evalPCoeff i φ (Pure.basisVector c b') = if b' i = φ then (1 : k) else 0 := by
  simp [evalPCoeff, basisVector, Finsupp.single_apply]

/-!

## Evaluation for a pure tensor.

-/

/-- Given a `i : Fin (n + 1)`, a `φ : basisIdx (c i)` and a pure tensor
  `p : Pure S c`, `evalP i φ p` is the tensor formed by evaluating the `i`th index
  of `p` at `φ`. -/
noncomputable def evalP (i : Fin (n + 1)) (φ : basisIdx (c i)) (p : Pure S c) :
  Tensor S (c ∘ i.succAbove) := evalPCoeff i φ p • (drop p i).toTensor

@[simp]
lemma evalP_update_add [inst : DecidableEq (Fin (n + 1))] (i j : Fin (n + 1))
    (φ : basisIdx (c i)) (p : Pure S c)
    (x y: V (c j)) :
    evalP i φ (p.update j (x + y)) =
    evalP i φ (p.update j x) + evalP i φ (p.update j y) := by
  simp only [evalP]
  rcases Fin.eq_self_or_eq_succAbove i j with rfl | ⟨j, rfl⟩
  · simp [add_smul]
  · simp

@[simp]
lemma evalP_update_smul [inst : DecidableEq (Fin (n + 1))] (i j : Fin (n + 1))
    (φ : basisIdx (c i)) (p : Pure S c)
    (r : k)
    (x : V (c j)) :
    evalP i φ (p.update j (r • x)) =
    r • evalP i φ (p.update j x) := by
  simp only [evalP]
  rcases Fin.eq_self_or_eq_succAbove i j with rfl | ⟨j, rfl⟩
  · simp [smul_smul]
  · simp [smul_smul, mul_comm]

/-!

## Evaluation for a pure tensor as multilinear map.

-/

/-- The multi-linear map formed by evaluation of an index of pure tensors. -/
noncomputable def evalPMultilinear {n : ℕ} {c : Fin (n + 1)→ C}
    (i : Fin (n + 1)) (φ : basisIdx (c i)) :
    MultilinearMap k (fun i => V (c i))
      (S.Tensor (c ∘ i.succAbove)) where
  toFun p := evalP i φ p
  map_update_add' p m x y := by
    change (update p m (x + y)).evalP i φ = _
    simp only [evalP_update_add]
    rfl
  map_update_smul' p k r y := by
    change (update p k (r • y)).evalP i φ = _
    rw [Pure.evalP_update_smul]
    rfl

end Pure

TODO "Choose a more descriptive name for `evalT` and `evalP`, taking into consideration
  the namespaces they live in."

/-- Evaluation of a tensor at a given index and basis element. -/
noncomputable def evalT {n : ℕ} {c : Fin (n + 1) → C} (i : Fin (n + 1))
      (φ : basisIdx (c i)) :
    Tensor S c →ₗ[k] Tensor S (c ∘ i.succAbove) :=
  PiTensorProduct.lift (Pure.evalPMultilinear i φ)

@[simp]
lemma evalT_pure {n : ℕ} {c : Fin (n + 1) → C} (i : Fin (n + 1))
    (φ : basisIdx (c i)) (p : Pure S c) :
    evalT i φ p.toTensor = Pure.evalP i φ p := by
  simp only [evalT, Pure.toTensor]
  change _ = Pure.evalPMultilinear i φ p
  conv_rhs => rw [← PiTensorProduct.lift.tprod]

lemma evalT_basis {n : ℕ} {c : Fin (n + 1) → C} (i : Fin (n + 1))
    (b : ComponentIdx c) (x : basisIdx (c i)) :
    evalT i x (basis (S := S) c b) = if b i = x then basis (c ∘ i.succAbove)
      (fun j => b (i.succAbove j)) else 0 := by
  simp only [basis_apply, evalT_pure, Pure.evalP, Pure.evalPCoeff_basisVector, ite_smul, one_smul,
    zero_smul]
  rfl

attribute [-simp] Matrix.cons_val_zero Matrix.cons_val Fin.succAbove_zero

TODO "Add lemmas related to the interaction of evalT and permT, prodT and contrT."

/-!

## The commutation of evaluation with permutations.

-/

/-- Commuting evaluation with permutations.-/
lemma evalT_permT {n m : ℕ} {c : Fin (n + 1) → C} {c' : Fin (m + 1) → C}
    {σ : Fin (n + 1) → Fin (m + 1)}
    (h : IsReindexing c' c  σ) (i : Fin (n + 1)) (x : basisIdx (c i)) (t : Tensor S c') :
    evalT i x (permT _ h t) = permT _ (h.succAbove i)
      (evalT (σ i) (basisIdxCongr (by simp [h.2]) x) t) := by
  induction' t using Tensor.induction_on_basis with b a t h t1 t2 h1 h2
  · simp only [evalT_basis, permT_basis]
    by_cases h1 : (basisIdxCongr (by simp [h.2])) (b (σ i)) = x
    · have h1' : basisIdxCongr (by simp [h.2]) x = b (σ i) := by subst h1; simp
      simp only [h1, ↓reduceIte, h1', permT_basis]
      congr
      funext j
      refine (Equiv.eq_symm_apply (basisIdxCongr _)).mp ?_
      simp only [basisIdxCongr_symm]
      erw [basisIdxCongr_apply_apply]
      apply ComponentIdx.congr_right
      split_ifs with h2
      · simp [h2]
      · have hne : σ (i.succAbove j) ≠ ((σ i).pred h2).succ := by
          rw [Fin.succ_pred]; exact fun heq => Fin.succAbove_ne i j (h.1.injective heq)
        rw [show (σ i).succAbove = (((σ i).pred h2).succ).succAbove from by rw [Fin.succ_pred]]
        exact (Fin.succ_succAbove_predAbove hne).symm
    · have h1' : b (σ i) ≠ basisIdxCongr (by simp [h.2]) x := by by_contra h2; simp [h2] at h1
      simp [h1, h1']
  · simp
  · simp only [map_smul, h]
  · simp only [map_add, h1, h2]

/-!

## The commutation of evaluation with evaluation.

-/

/-- Commutation of two evaluations on a tensor basis vector. -/
lemma evalT_evalT_basis {n : ℕ} {c : Fin (n + 1 + 1) → C}
    (k1 : Fin (n + 1 + 1)) (k2 : Fin (n + 1)) (φ1 : basisIdx (c k1))
    (φ2 : basisIdx ((c ∘ k1.succAbove) k2)) (ψ : ComponentIdx (S := S) c) :
    evalT k2 φ2 (evalT k1 φ1 (basis (S := S) c ψ)) =
      permT id (IsReindexing.succAbove_succAbove_comm k1 k2)
        (evalT (k2.predAbove k1)
          (basisIdxCongr
            (congrArg c (Fin.succAbove_succAbove_predAbove k1 k2).symm) φ1)
          (evalT (k1.succAbove k2) φ2 (basis (S := S) c ψ))) := by
  simp only [evalT_basis, apply_ite, map_zero]
  have hk1 : (k1.succAbove k2).succAbove (k2.predAbove k1) = k1 :=
    Fin.succAbove_succAbove_predAbove k1 k2
  have hcond :
      (ψ ((k1.succAbove k2).succAbove (k2.predAbove k1)) =
          basisIdxCongr (congrArg c hk1.symm) φ1) ↔ ψ k1 = φ1 := by
    rw [ComponentIdx.congr_right ψ _ k1 hk1]
    exact (basisIdxCongr _).apply_eq_iff_eq
  by_cases h2 : ψ (k1.succAbove k2) = φ2
  · by_cases h1 : ψ k1 = φ1
    · have htr :
          ψ ((k1.succAbove k2).succAbove (k2.predAbove k1)) =
            basisIdxCongr (congrArg c hk1.symm) φ1 := hcond.mpr h1
      simp only [h2, h1, htr, ↓reduceIte]
      rw [permT_basis]
      congr 1
      funext i
      exact ComponentIdx.congr_right ψ _ _
        (Fin.succAbove_succAbove_succAbove_predAbove k1 k2 i).symm
    · have hntr :
          ¬ ψ ((k1.succAbove k2).succAbove (k2.predAbove k1)) =
              basisIdxCongr (congrArg c hk1.symm) φ1 := by
        intro htr
        exact h1 (hcond.mp htr)
      simp only [h2, h1, hntr, ↓reduceIte]
  · simp only [h2, ↓reduceIte, ite_self]

/-- Evaluating two tensor indices commutes, up to the canonical reindexing
identifying the two possible orders in which the indices are removed. -/
lemma evalT_evalT {n : ℕ} {c : Fin (n + 1 + 1) → C}
    (k1 : Fin (n + 1 + 1)) (k2 : Fin (n + 1)) (φ1 : basisIdx (c k1))
    (φ2 : basisIdx ((c ∘ k1.succAbove) k2)) (t : Tensor S c) :
    evalT k2 φ2 (evalT k1 φ1 t) =
      permT id (IsReindexing.succAbove_succAbove_comm k1 k2)
        (evalT (k2.predAbove k1)
          (basisIdxCongr
            (congrArg c (Fin.succAbove_succAbove_predAbove k1 k2).symm) φ1)
          (evalT (k1.succAbove k2) φ2 t)) := by
  induction' t using Tensor.induction_on_basis with ψ a t ht t1 t2 ht1 ht2
  · exact evalT_evalT_basis (S := S) k1 k2 φ1 φ2 ψ
  · simp
  · simp only [map_smul, ht]
  · simp only [map_add, ht1, ht2]

/-!

## The commutation of evaluation with contraction.

-/

/-- Commuting evaluation with contraction. Evaluating index `k` and then contracting the
  pair `i j` equals contracting the corresponding pair `k.succAbove i`, `k.succAbove j` and
  then evaluating the residual index, up to the identity reindexing
  `IsReindexing.succAbove_succSuccAbove_comm`. -/
lemma contrT_evalT {n : ℕ} {c : Fin (n + 1 + 1 + 1) → C}
    (k : Fin (n + 1 + 1 + 1)) (i j : Fin (n + 1 + 1)) (φ : basisIdx (c k))
    (hij : i ≠ j ∧ S.τ ((c ∘ k.succAbove) i) = (c ∘ k.succAbove) j) (t : Tensor S c) :
    contrT n i j hij (evalT k φ t) =
    permT id (.succAbove_succSuccAbove_comm k i j hij.1)
      (evalT (Fin.predPredAbove (k.succAbove i) (k.succAbove j) (by simp [hij.1]) k (by simp))
        (basisIdxCongr (by simp) φ)
        (contrT (n + 1) (k.succAbove i) (k.succAbove j) ⟨by simp [hij.1], hij.2⟩ t)) := by
  induction' t using Tensor.induction_on_basis with b a t hb t1 t2 hb1 hb2
  · have hs : Pure.contrPCoeff i j hij
          (Pure.basisVector (c ∘ k.succAbove) (fun m => b (k.succAbove m))) =
        Pure.contrPCoeff (k.succAbove i) (k.succAbove j) ⟨by simp [hij.1], hij.2⟩
          (Pure.basisVector c b) := rfl
    conv_lhs => rw [evalT_basis]
    conv_rhs => rw [contrT_basis, map_smul, evalT_basis]
    rw [apply_ite (contrT n i j hij), map_zero, contrT_basis, hs, map_smul,
      apply_ite (permT id (IsReindexing.succAbove_succSuccAbove_comm k i j hij.1)), map_zero,
      permT_basis, smul_ite, smul_zero]
    have hidx : ∀ m, (k.succAbove i).succSuccAbove (k.succAbove j)
        (((k.succAbove i).predPredAbove (k.succAbove j) (by simp [hij.1]) k (by simp)).succAbove m)
        = k.succAbove (i.succSuccAbove j m) := by
      intro m
      apply Fin.val_injective
      simp only [Fin.succSuccAbove, Fin.succAbove, Fin.predPredAbove, Fin.lt_def,
        Fin.val_castSucc, Fin.val_succ, apply_ite Fin.val, apply_dite Fin.val]
      grind (splits := 60)
    have hk : (k.succAbove i).succSuccAbove (k.succAbove j)
        ((k.succAbove i).predPredAbove (k.succAbove j) (by simp [hij.1]) k (by simp)) = k := by simp
    have hcond : (ComponentIdx.dropPair (k.succAbove i) (k.succAbove j) b
          ((k.succAbove i).predPredAbove (k.succAbove j) (by simp [hij.1]) k (by simp)) =
          basisIdxCongr (by simp) φ) = (b k = φ) := by
      simp only [ComponentIdx.dropPair]
      rw [ComponentIdx.congr_right b _ k hk, eq_iff_iff]
      exact (basisIdxCongr _).apply_eq_iff_eq
    simp only [hcond]
    split_ifs with hbk
    · congr 1
      congr 1
      funext m
      simp only [ComponentIdx.dropPair, id_eq]
      exact ComponentIdx.congr_right b _ _ (hidx m).symm
    · rfl
  · simp
  · simp only [map_smul, hb]
  · simp only [map_add, hb1, hb2]

TODO "Add a lemma similar to `contrT_evalT` except with the contraction and
  evaluation the other way around."

/-!

## The commutation of evaluation with products.

-/

/-- Evaluating an index in the right factor of a tensor product commutes with forming the
  product, up to the identity reindexing which identifies the two ways of removing that
  index from the appended color list. -/
lemma evalT_prodT_right {n n1 : ℕ} {c : Fin n → C} {c1 : Fin (n1 + 1) → C}
    (i : Fin (n1 + 1)) (x : basisIdx (c1 i)) (t : Tensor S c) (t1 : Tensor S c1) :
    prodT t (evalT i x t1) =
    permT id (IsReindexing.append_succAbove_natAdd (n := n) (n1 := n1) i)
      (evalT (Fin.natAdd (m := n1 + 1) n i) (basisIdxCongr (by simp) x) (prodT t t1)) := by
  symm
  induction' t using Tensor.induction_on_basis with b a t ht t2 t3 ht2 ht3
  · induction' t1 using Tensor.induction_on_basis with b1 a t ht t2 t3 ht2 ht3
    · by_cases hi : b1 i = x
      · have hprod : ComponentIdx.prod.symm (b, b1) (Fin.natAdd (m := n1 + 1) n i) =
            basisIdxCongr (by simp) x := by
          simp [hi]
        rw [prodT_basis', evalT_basis, ite_eq_left hprod, permT_basis]
        rw [evalT_basis, ite_eq_left hi, prodT_basis']
        congr
        ext j
        refine Fin.addCases (fun a => ?_) (fun a => ?_) j
        · have hidx : (Fin.natAdd (m := n1 + 1) n i).succAbove (Fin.castAdd n1 a) =
              Fin.castAdd (n1 + 1) a := by
            rw [Fin.succAbove_of_castSucc_lt]
            · ext
              simp
            · simp only [Fin.lt_def, Fin.val_castSucc, Fin.val_castAdd, Fin.val_natAdd]
              omega
          simp only [id_eq]
          erw [ComponentIdx.congr_right (ComponentIdx.prod.symm (b, b1)) _ _ hidx]
          simp only [ComponentIdx.prod_symm_castAdd]
          exact basisIdxCongr_heq_arg _ _ (by
            simp only [basisIdxCongr, Equiv.cast_apply]
            exact (cast_heq _ _).trans (cast_heq _ _))
        · have hidx : (Fin.natAdd (m := n1 + 1) n i).succAbove
              (Fin.natAdd (m := n1) n a) =
              Fin.natAdd (m := n1 + 1) n (i.succAbove a) := by
            have hcond : ((Fin.natAdd (m := n1) n a).castSucc <
                Fin.natAdd (m := n1 + 1) n i) ↔
                (a.castSucc < i) := by
              simp only [Fin.lt_def, Fin.val_castSucc, Fin.val_natAdd]
              omega
            simp only [Fin.succAbove, hcond]
            split_ifs <;> ext <;> simp [Nat.add_assoc]
          simp only [id_eq]
          erw [ComponentIdx.congr_right (ComponentIdx.prod.symm (b, b1)) _ _ hidx]
          simp only [ComponentIdx.prod_symm_natAdd]
          exact basisIdxCongr_heq_arg _ _ (by
            simp only [basisIdxCongr, Equiv.cast_apply]
            exact (cast_heq _ _).trans (cast_heq _ _))
      · have hprod : ComponentIdx.prod.symm (b, b1) (Fin.natAdd (m := n1 + 1) n i) ≠
            basisIdxCongr (by simp) x := by
          intro hprod
          exact hi (by simpa [ComponentIdx.prod] using hprod)
        rw [prodT_basis', evalT_basis, ite_eq_right hprod]
        rw [evalT_basis, ite_eq_right hi]
        simp
    · simp
    · simp [ht]
    · simp [map_add, ht2, ht3]
  · simp
  · simp [ht]
  · simp [map_add, ht2, ht3]

TODO "Add a lemmas related to the commutation of evaluation with contraction."

/-!

## Other properties of evaluation

-/
set_option backward.isDefEq.respectTransparency false in
/-- Evaluating the single-index basis tensor `basis ![c] (single.symm b)` at the index `x`
  yields the field element `1` if `b = x` (transported across `![c] 0 = c`) and `0` otherwise:
  evaluation of a one-index basis tensor is the Kronecker delta. -/
lemma evalT_basis_single {c : C} (b : basisIdx c) (x : basisIdx (![c] 0)) :
    (evalT 0 x (basis (S := S) ![c] (ComponentIdx.single.symm b))).toScalar =
    if basisIdxCongr (by simp) b =  x then 1 else 0 := by
  rw [evalT_basis]
  simp only [ComponentIdx.single_symm_apply]
  split_ifs
  · exact toScalar_basis _
  · simp

/-- Basis expansion of a one-index tensor: every `t : Tensor S ![c]` is the sum over basis
  indices `i` of its evaluation coefficient `toScalar (evalT 0 i t)` times the corresponding
  basis tensor. -/
lemma eq_sum_evalT_of_single_tensor_basis {c : C} (t : Tensor S ![c]) :
    t = ∑ i, toScalar (evalT 0 i t) • basis ![c] (ComponentIdx.single.symm
      (basisIdxCongr (by simp) i)) := by
  induction' t using Tensor.induction_on_basis with b a t h t1 t2 h1 h2
  · obtain ⟨i, rfl⟩ := ComponentIdx.single.symm.surjective b
    conv_rhs => enter [2, i]; rw [evalT_basis_single]
    simp
  · simp
  · conv_lhs => rw [h]
    simp [Finset.smul_sum, smul_smul]
  · simp [add_smul, Finset.sum_add_distrib]
    grind

/-- Reconstruction of a tensor from the evaluations of its last index: every `t : Tensor S c`
  is the sum over basis indices `i` of the evaluation `evalT (Fin.last n) i t` tensored with
  the basis covector `basis ![c (Fin.last n)] (single.symm i)`, with the appended index
  permuted back into the last slot. -/
lemma eq_sum_evalT {n : ℕ} {c : Fin (n + 1) → C} (t : Tensor S c) :
    t = ∑ i, permT id (IsReindexing.append_succ_last c) (prodT (evalT (Fin.last n) i t)
      (basis ![c (Fin.last n)] (ComponentIdx.single.symm i)))   := by
  induction' t using Tensor.induction_on_basis with b a t h t1 t2 h1 h2
  · conv_rhs => enter [2, i]; rw [evalT_basis]
    generalize_proofs h1 h2 h3
    rw [Finset.sum_eq_single (b (Fin.last n))]
    · simp only [Nat.succ_eq_add_one, Nat.reduceAdd, ↓reduceIte]
      rw [prodT_basis, basis_apply, permT_pure]
      congr
      funext i
      simp only [Pure.basisVector, Pure.permP_basisVector]
      congr
      refine Fin.addCases (fun j => ?_) (fun j => ?_) i
      · simp only [id_eq, ComponentIdx.prod_symm_castAdd, Function.comp_apply]
        erw [basisIdxCongr_apply_apply]
        exact ComponentIdx.congr_right b _ _ (by rw [Fin.succAbove_last]; rfl)
      · simp only [id_eq, ComponentIdx.prod_symm_natAdd, ComponentIdx.single_symm_apply,
          basisIdxCongr_apply_apply]
        exact ComponentIdx.congr_right _ _ _ (by fin_cases j; rfl)
    · intro j h1 h1
      rw [ite_eq_right (by grind)]
      simp
    · simp
  · simp
  · conv_lhs => rw [h]
    simp [Finset.smul_sum]
  · simp [Finset.sum_add_distrib]
    grind

/-- Reconstruction of a tensor from the evaluations of its first index: every `t : Tensor S c`
  is the sum over basis indices `i` of the basis covector `basis ![c 0] (single.symm i)` tensored
  with the evaluation `evalT 0 i t`, with the prepended index permuted back into the first slot.
  This is the first-index analogue of `eq_sum_evalT`. -/
lemma eq_sum_evalT_zero {n : ℕ} {c : Fin (n + 1) → C} (t : Tensor S c) :
    t = ∑ i, permT _ (IsReindexing.append_of_first c)
    (prodT (basis ![c 0] (ComponentIdx.single.symm i)) (evalT 0 i t))  := by
  induction' t using Tensor.induction_on_basis with b a t h t1 t2 h1 h2
  · conv_rhs => enter [2, i]; rw [evalT_basis]
    generalize_proofs h1 h2 h3
    rw [Finset.sum_eq_single (b 0)]
    · simp only [↓reduceIte]
      rw [prodT_basis, basis_apply, permT_pure]
      congr
      funext i
      simp only [Pure.basisVector, Pure.permP_basisVector]
      congr
      refine Fin.cases ?_ (fun j => ?_) i
      · simp only [ComponentIdx.prod, Equiv.coe_fn_symm_mk, Fin.cast_zero, Fin.addCases,
          ComponentIdx.single_symm_apply, basisIdxCongr_apply_apply]
        exact ComponentIdx.congr_right b 0 0 rfl
      · simp only [ComponentIdx.prod, Equiv.coe_fn_symm_mk, Fin.addCases]
        rw [dite_eq_right (by simp)]
        simp only [eqRec_eq_cast, basisIdxCongr, Equiv.cast_apply, cast_cast]
        symm
        rw [cast_eq_iff_heq]
        congr 1
    · intro j h1 h1
      rw [ite_eq_right (by grind)]
      simp
    · simp
  · simp
  · conv_lhs => rw [h]
    simp [Finset.smul_sum]
  · simp [Finset.sum_add_distrib]
    grind

lemma ext_of_evalT {n : ℕ} {c : Fin (n + 1) → C} (t1 t2 : Tensor S c)
    (h : ∀ i φ, evalT i φ t1 = evalT i φ t2) :
    t1 = t2 := by
  rw [eq_sum_evalT t1, eq_sum_evalT t2]
  congr
  funext i
  rw [h]

lemma ext_of_evalT_index {n : ℕ} {c : Fin (n + 1) → C} {t1 t2 : Tensor S c}
    (i : Fin (n + 1)) (h : ∀ φ, evalT i φ t1 = evalT i φ t2) :
    t1 = t2 := by
  have evalT_eq : ∀ (j : Fin (n + 1)), j = i →
      ∀ (ψ : basisIdx (c j)), evalT j ψ t1 = evalT j ψ t2 := by
    rintro j rfl ψ; exact h ψ
  let e : Fin (n + 1) ≃ Fin (n + 1) := Equiv.swap i (Fin.last n)
  have h0 : IsReindexing c (c ∘ e) e := ⟨e.bijective, fun _ => rfl⟩
  have hlast : e (Fin.last n) = i := Equiv.swap_apply_right i (Fin.last n)
  have hperm : permT e h0 t1 = permT e h0 t2 := by
    rw [eq_sum_evalT (permT e h0 t1), eq_sum_evalT (permT e h0 t2)]
    congr 1
    funext φ
    rw [evalT_permT h0 (Fin.last n) φ t1, evalT_permT h0 (Fin.last n) φ t2,
      evalT_eq (e (Fin.last n)) hlast]
  rw [← sub_eq_zero, ← permT_eq_zero_iff h0, map_sub, hperm, sub_self]

end Tensor
end TensorSpecies
