/-
Copyright (c) 2026 Andrea Pari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrea Pari
-/
module

public import Physlib.Relativity.Tensors.Contraction.CrossToSlot
public import Physlib.Relativity.Tensors.UnitTensor
public import Physlib.Relativity.Tensors.Evaluation
/-!

# Contraction against the unit tensor

## i. Overview

The unit tensor is the identity for slot contraction: contracting any slot of `t` against
`unitTensor` for that slot's color returns `t`, the slot relabelled to the survivor tail. That is
what collapses "raise then lower" to the identity, a metric contracted against its dual becoming
the unit tensor and then contracting away.

`crossToEnd_unitTensor` is proved by decomposing `t` along its last slot (`eq_sum_evalT`) and
transporting to an arbitrary slot with the transposition `swap i (last)`. On it the round trip
against a matched pair is assembled in both conventions, and a pair collapsing in *both* orders
makes the two contractions mutually inverse, which `crossToSlotEquiv` bundles as a linear
equivalence between the two color assignments.

Since `unitTensor` is `RCLike`-valued, this material sits over an `[RCLike k]` variable block, apart
from the `CommRing` `crossToEnd`/`crossToSlot` algebra.

## ii. Key results

- `TensorSpecies.Tensor.crossToEnd_unitTensor` : the unit tensor is an identity for `crossToEnd`
    at any named slot.
- `TensorSpecies.Tensor.crossToEnd_round_trip_of_unit_slot` : two contractions against a pair that
    collapses to the unit tensor return the original tensor, in result-to-end form.
- `TensorSpecies.Tensor.crossToSlot_raise_lower_round_trip` : the round trip in result-to-slot
    form, every color propositional.
- `TensorSpecies.Tensor.crossToSlotEquiv` : raising and lowering a named index against a pair that
    collapses in both orders, as a linear equivalence.

## iii. Table of contents

- A. The unit tensor as a slot-contraction identity
- B. Round trips against a matched pair
- C. Raising and lowering as an equivalence

## iv. References

* None.
-/

@[expose] public section

namespace TensorSpecies

variable {k : Type} [RCLike k] {C : Type} {G : Type} [Group G]
    {V : C → Type} [∀ c, AddCommGroup (V c)] [∀ c, Module k (V c)]
    {basisIdx : C → Type} [∀ c, Fintype (basisIdx c)] [∀ c, DecidableEq (basisIdx c)]
    {rep : (c : C) → Representation k G (V c)} {b : (c : C) → Module.Basis (basisIdx c) k (V c)}
    {S : TensorSpecies k C G V basisIdx rep b}
attribute [-simp] LinearEquiv.cast_apply

namespace Tensor

/-!

## A. The unit tensor as a slot-contraction identity

Contracting a named slot against `unitTensor` returns the tensor unchanged, the slot carried to the
survivor tail by `move_last`.

-/

set_option backward.isDefEq.respectTransparency false in
/-- Cross-contracting the last slot of the product `E ⊗ B` (with `B` rank one) against the unit
  tensor for that slot's color returns `E ⊗ B` unchanged, the contracted slot carried to the end.
  The rank-one spectator case that seeds `crossToEnd_unitTensor_slot`. -/
private lemma crossToEnd_prodT_unitTensor {nV : ℕ} {cE : Fin nV → C} {cB : C}
    (E : Tensor S cE) (B : Tensor S ![cB]) :
    crossToEnd (Fin.last nV) (0 : Fin 2)
        (by rw [show (Fin.last nV : Fin (nV + 1)) = Fin.natAdd nV 0 from Fin.ext (by simp)]; simp :
          S.τ ((Fin.append cE ![cB]) (Fin.last nV)) = ![S.τ cB, cB] 0)
        (prodT E B) (unitTensor cB) =
      permT id (IsReindexing.on_id.mpr (fun i => by
        refine Fin.addCases (fun j => ?_) (fun j => ?_) i
        · simp only [Fin.append_left, Function.comp_apply, Fin.succAbove_last]
          exact (Fin.append_left cE ![cB] j).symm
        · simp only [Fin.append_right, Function.comp_apply, Fin.succAbove_zero]
          fin_cases j
          rfl)) (prodT E B) := by
  simp only [crossToEnd, LinearMap.compr₂_apply, LinearMap.comp_apply]
  rw [contrT_congr (n := nV + 1) (⟨nV, by omega⟩ : Fin (nV + 1 + 1 + 1))
      (⟨nV + 1, by omega⟩ : Fin (nV + 1 + 1 + 1)) _ (Fin.ext (by simp)) (Fin.ext (by simp))]
  rw [prodT_assoc E B (unitTensor cB)]
  simp only [permT_permT]
  rw [contrT_permT]
  simp only [Fin.cast_eq_self, Function.comp_apply]
  have hij : (0 : Fin 3) ≠ (1 : Fin 3) ∧
      S.τ (Fin.append ![cB] ![S.τ cB, cB] 0) = Fin.append ![cB] ![S.τ cB, cB] 1 :=
    ⟨by decide, by rfl⟩
  have key : (contrT (nV + 1) (⟨nV, by omega⟩ : Fin (nV + 1 + 1 + 1)) ⟨nV + 1, by omega⟩
        (by refine ⟨by simp [Fin.ext_iff], ?_⟩
            rw [show (⟨nV, by omega⟩ : Fin (nV + 1 + 1 + 1))
                    = Fin.natAdd nV (0 : Fin 3) from Fin.ext (by simp),
                show (⟨nV + 1, by omega⟩ : Fin (nV + 1 + 1 + 1))
                    = Fin.natAdd nV (1 : Fin 3) from Fin.ext (by simp)]
            rw [Fin.append_right, Fin.append_right]; exact hij.2)
        (prodT E (prodT B (unitTensor cB)))) =
      (permT id (IsReindexing.on_id_symm (IsReindexing.append_succSuccAbove_natAdd (0:Fin 3) 1)))
        (prodT E (contrT 1 0 1 hij (prodT B (unitTensor cB)))) :=
    contrT_prodT_snd (0 : Fin 3) 1 hij (prodT B (unitTensor cB)) E
  rw [contrT_single_unitTensor] at key
  -- The `contrT_congr` pinning leaves slot proofs that match `key`'s only at `instances`
  -- transparency; the trailing `permT_permT` needs the full `erw`.
  rw (transparency := .instances) [key, permT_permT]
  rw [prodT_permT_right, permT_permT]
  erw [permT_permT]
  apply permT_congr
  · funext i
    simp only [Function.comp_apply, id_eq, Fin.funPredPredAbove]
    apply Fin.ext
    simp only [Nat.succ_eq_add_one, Nat.reduceAdd, CompTriple.comp_eq,
      Fin.cast_eq_self, Fin.predPredAbove_succSuccAbove]
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp [Fin.append_left, Fin.append_right]
  · rfl

set_option backward.isDefEq.respectTransparency false in
/-- The boundary case of `crossToEnd_unitTensor`, proved by spectator decomposition along the last
  slot (`eq_sum_evalT`). The last slot is threaded as a variable `i` with `hilast : i = last nA` so
  that `crossToEnd_unitTensor` can apply it at the image of `i` under its transposition without a
  dependent rewrite of the slot index. -/
private lemma crossToEnd_unitTensor_slot {nA : ℕ} {cA : Fin (nA + 1) → C} {c : C}
    {i : Fin (nA + 1)} (hilast : i = Fin.last nA) (hc : cA i = c) (t1 : Tensor S cA) :
    crossToEnd i (0 : Fin 2) (by simp [hc] : S.τ (cA i) = ![S.τ c, c] 0) t1 (unitTensor c) =
      permT (Fin.append i.succAbove (fun _ : Fin 1 => i)) (IsReindexing.move_last i hc) t1 := by
  subst hilast
  subst hc
  rw [eq_sum_evalT t1, map_sum, LinearMap.sum_apply, map_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  change crossToEnd (Fin.last nA) 0 _
    (permT (fun x => x) _
      (prodT (evalT (Fin.last nA) i t1)
        (basis ![cA (Fin.last nA)] (ComponentIdx.single.symm i))))
    (unitTensor (S := S) (cA (Fin.last nA))) = _
  rw [crossToEnd_permT_left (Fin.last nA) 0 (fun x => x) (fun x => x)
    (IsReindexing.append_succ_last cA) (by rfl)]
  rw [crossToEnd_prodT_unitTensor]
  simp only [permT_permT]
  refine permT_congr (funext fun x => ?_) rfl
  refine Fin.addCases (fun j => ?_) (fun j => ?_) x
  · simp only [Fin.append_left, Function.comp_apply, id_eq, Fin.succAbove_last]
    rfl
  · simp only [Fin.append_right, Function.comp_apply]
    exact Fin.ext (by simp)

/-- Contracting slot `i` of `t1` against the unit tensor for that slot's color returns `t1`, the
  contracted slot relabelled by `move_last i`. The unit tensor acts as an identity for `crossToEnd`
  at any named slot. -/
lemma crossToEnd_unitTensor {nA : ℕ} {cA : Fin (nA + 1) → C} {c : C}
    (i : Fin (nA + 1)) (hc : cA i = c) (t1 : Tensor S cA) :
    crossToEnd i (0 : Fin 2) (by simp [hc] : S.τ (cA i) = ![S.τ c, c] 0) t1 (unitTensor c) =
      permT (Fin.append i.succAbove (fun _ : Fin 1 => i)) (IsReindexing.move_last i hc) t1 := by
  set τ : Fin (nA + 1) → Fin (nA + 1) := ⇑(Equiv.swap i (Fin.last nA)) with hτdef
  have hτbij : Function.Bijective τ := (Equiv.swap i (Fin.last nA)).bijective
  have hτi : τ i = Fin.last nA := Equiv.swap_apply_left i (Fin.last nA)
  have hself : ∀ x, τ (τ x) = x := fun x => Equiv.swap_apply_self i (Fin.last nA) x
  -- `τ` is injective, so it restricts to the survivors of `i`: some `τ'` fills the square
  -- `(τ i).succAbove ∘ τ' = τ ∘ i.succAbove`.
  obtain ⟨τ', hτ'⟩ : ∃ τ' : Fin nA → Fin nA, (τ i).succAbove ∘ τ' = τ ∘ i.succAbove :=
    ⟨fun a => (Fin.exists_succAbove_eq (hτbij.1.ne (Fin.succAbove_ne i a))).choose,
      funext fun a => (Fin.exists_succAbove_eq (hτbij.1.ne (Fin.succAbove_ne i a))).choose_spec⟩
  have hre2 : IsReindexing cA (cA ∘ τ) τ := Tensor.IsReindexing.swap i (Fin.last nA)
  have hre : IsReindexing (cA ∘ τ) cA τ :=
    ⟨hτbij, fun x => by simp only [Function.comp_apply, hself]⟩
  have ht1 : permT τ hre (permT τ hre2 t1) = t1 := by
    rw [permT_permT]; exact permT_congr_eq_id _ _ _ (funext hself)
  conv_lhs => rw [← ht1]
  rw [crossToEnd_permT_left i (0 : Fin 2) τ τ' hre hτ' _
      (permT τ hre2 t1) (unitTensor c),
    crossToEnd_unitTensor_slot hτi (by simp only [Function.comp_apply, hself]; exact hc)
      (permT τ hre2 t1), permT_permT, permT_permT]
  refine permT_congr (funext fun x => ?_) rfl
  refine Fin.addCases (fun a => ?_) (fun a => ?_) x
  · simp only [Function.comp_apply, Fin.append_left]
    rw [show (τ i).succAbove (τ' a) = τ (i.succAbove a) from congrFun hτ' a, hself]
  · simp only [Function.comp_apply, Fin.append_right, hself]

/-!

## B. Round trips against a matched pair

When two rank-2 tensors collapse to the unit tensor after their shared index is contracted,
contracting a slot first against one and then against the other returns the original tensor.

-/

/-- The color list `crossToEnd` produces from a matched rank-2 pair `M : ![a, d]`, `M' : ![b, e]` is
  the color list `![S.τ e, e]` of `unitTensor e`, via the identity slot map: the reindexing carried
  by the collapse hypothesis `M · M' = δ` of the round trips below. Only the surviving colors `a`
  and `e` enter, and `a` equals `S.τ e` only propositionally, so a pair whose colors match
  propositionally enters with no transport. -/
lemma IsReindexing.unitTensor_pair {a b d e : C} (h : S.τ e = a) :
    IsReindexing (![S.τ e, e] : Fin 2 → C)
      (Fin.append ((![a, d] : Fin 2 → C) ∘ (Fin.last 1).succAbove)
        ((![b, e] : Fin 2 → C) ∘ (0 : Fin 2).succAbove))
      (id : Fin 2 → Fin 2) :=
  IsReindexing.on_id.mpr (fun j => by fin_cases j <;> first | exact h | rfl)

/-- Round trip of two contractions against a matched pair, in result-to-end form. Contracting slot
  `i` of `t` against `M₁`, then contracting the surviving `M₁`-index (deposited at slot `j`) against
  `M₂`, returns `t` up to the cycle that moves the round-tripped slot from the end back to `i`,
  whenever `M₁` and `M₂` collapse to the unit tensor. The last slot is threaded as a variable `j`
  with `hj : j = last nA` so that a caller can apply it at a propositionally-last slot without a
  dependent rewrite of the slot index. -/
lemma crossToEnd_round_trip_of_unit_slot {nA : ℕ} {c : Fin (nA + 1) → C} {d : C}
    (i j : Fin (nA + 1)) (hj : j = Fin.last nA)
    (M₁ : Tensor S ![S.τ (c i), d]) (M₂ : Tensor S ![S.τ d, c i])
    (hM : crossToEnd (Fin.last 1) (0 : Fin 2) rfl M₁ M₂ =
      permT (id : Fin 2 → Fin 2) (IsReindexing.unitTensor_pair rfl)
        (unitTensor (S := S) (c i)))
    (t : Tensor S c) :
    crossToEnd j (0 : Fin 2)
        (by subst hj
            rw [show (Fin.last nA : Fin (nA + 1)) = Fin.natAdd nA (0 : Fin 1) from
                  Fin.ext (by simp), Fin.append_right]; rfl)
        (crossToEnd i (0 : Fin 2) rfl t M₁) M₂ =
      permT (Fin.append i.succAbove (fun _ : Fin 1 => i))
        (by
          subst hj
          exact ⟨by
            rw [Fin.append_succAbove_const_eq_cycleIcc i]
            exact (Fin.cycleIcc i (Fin.last nA)).bijective,
          fun x => by
            refine Fin.addCases (fun a => ?_) (fun a => ?_) x
            · simp only [Function.comp_apply, Fin.append_left, Fin.succAbove_last,
                show (Fin.castSucc a : Fin (nA + 1)) = Fin.castAdd 1 a from rfl]
            · fin_cases a
              simp [Fin.append_right, Fin.succAbove_zero]⟩)
        t := by
  subst hj
  rw [crossToEnd_assoc_rankTwo i rfl rfl t M₁ M₂]
  rw [hM]
  rw [crossToEnd_permT_right i (0 : Fin 2)
    (id : Fin 2 → Fin 2) (fun x : Fin 1 => x)
    (IsReindexing.on_id.mpr (fun i => by fin_cases i <;> rfl)) rfl]
  -- The `id`-spelled map leaves the contracted slot spelled `id 0`; reduce it so that `rw` can
  -- key on `crossToEnd_unitTensor`.
  dsimp only [id_eq]
  rw [crossToEnd_unitTensor (nA := nA) (cA := c) (c := c i) i rfl, permT_permT, permT_permT]
  apply permT_congr
  · funext x
    refine Fin.addCases (fun a => ?_) (fun a => ?_) x
    · simp [Fin.append_left]
    · fin_cases a
      simp [Fin.append_right, Function.comp_apply]
  · rfl

set_option backward.isDefEq.respectTransparency false in
/-- Round trip for `crossToSlot` at an arbitrary slot, with the colors in their composite form.
  The general-color statement `crossToSlot_raise_lower_round_trip` is obtained from this by
  substituting its three color equalities. -/
private lemma crossToSlot_round_trip_of_unit {nA : ℕ} {c : Fin (nA + 1) → C} {d : C}
    (i : Fin (nA + 1))
    (M₁ : Tensor S ![S.τ (c i), d]) (M₂ : Tensor S ![S.τ d, c i])
    (hM : crossToEnd (Fin.last 1) (0 : Fin 2) rfl M₁ M₂ =
      permT (id : Fin 2 → Fin 2) (IsReindexing.unitTensor_pair rfl)
        (unitTensor (S := S) (c i)))
    (t : Tensor S c) :
    crossToSlot (S := S) i (0 : Fin 2)
        (by rw [Function.update_self] : S.τ (Function.update c i d i) = S.τ d) M₂
        (crossToSlot (S := S) i (0 : Fin 2) rfl M₁ t) =
      permT (id : Fin (nA + 1) → Fin (nA + 1)) (IsReindexing.update_update_of_eq i rfl) t := by
  have hcycle : (⇑(Fin.cycleIcc i (Fin.last nA)).symm) i = Fin.last nA :=
    (Equiv.symm_apply_eq _).2 (Fin.cycleIcc_of_last (Fin.le_last i)).symm
  -- The inverse cycle carries a reinserted survivor `i.succAbove a` back to its position `a` in
  -- the survivor block.
  have hcycle_succAbove : ∀ a : Fin nA,
      (Fin.cycleIcc i (Fin.last nA)).symm (i.succAbove a) = Fin.castAdd 1 a := fun a =>
    (Equiv.symm_apply_eq _).2
      (by rw [← Fin.append_succAbove_const_eq_cycleIcc i, Fin.append_left])
  rw [crossToSlot_eq_crossToEnd, crossToSlot_eq_crossToEnd]
  -- `crossToSlot`'s output color reduces to the clean one only at default transparency, so `rw`
  -- cannot key on the composite. Precompute the left commutator and `erw` it instead.
  have hpl := crossToEnd_permT_left i (0 : Fin 2)
    ⇑(Fin.cycleIcc i (Fin.last nA)).symm id (IsReindexing.crossToSlot_cycle i (0 : Fin 2))
    (by
      funext a
      simp only [Function.comp_apply, id_eq]
      rw [hcycle, hcycle_succAbove, Fin.succAbove_last]
      rfl)
    (show S.τ (Function.update c i d i) = ![S.τ d, c i] 0 by
      rw [Function.update_self, Matrix.cons_val_zero])
    (crossToEnd i (0 : Fin 2) rfl t M₁) M₂
  erw [hpl]
  erw [permT_permT]
  rw [crossToEnd_round_trip_of_unit_slot i ((⇑(Fin.cycleIcc i (Fin.last nA)).symm) i)
    hcycle M₁ M₂ hM t, permT_permT]
  apply permT_congr
  · funext x
    simp only [Function.comp_id]
    rw [Fin.append_castAdd_natAdd_eq_id]
    simp [Function.comp_apply, Fin.append_succAbove_const_eq_cycleIcc]
  · rfl

/-- Raising then lowering a named index, with every color threaded propositionally. For a rank-2
  metric `M : ![a, d]` and an inverse `M' : ![b, e]` collapsing to the unit tensor (`M · M' = δ`),
  at any rank and any slot `i`: contracting slot `i` with `M`, then contracting the result with
  `M'`, is the identity up to the `Function.update` color reindex.

  No color is pinned to a composite. `ha : τ (c i) = a` places the metric's contracted slot,
  `hb : τ d = b` the inverse's, and `he : c i = e` the surviving one, so a caller whose metric and
  inverse sit at literal colors supplies them directly, with no transporting `permT` on either
  factor. Lowering then raising is this same statement with `M` and `M'` exchanged and the reversed
  collapse `M' · M = δ`; neither collapse follows from the other here. -/
lemma crossToSlot_raise_lower_round_trip {nA : ℕ} {c : Fin (nA + 1) → C} {a b d e : C}
    (i : Fin (nA + 1)) (he : c i = e) (ha : S.τ (c i) = a) (hb : S.τ d = b)
    (M : Tensor S ![a, d]) (M' : Tensor S ![b, e])
    (hM : crossToEnd (Fin.last 1) (0 : Fin 2) hb M M' =
      permT (id : Fin 2 → Fin 2)
        (IsReindexing.unitTensor_pair ((congrArg S.τ he.symm).trans ha))
        (unitTensor (S := S) e))
    (t : Tensor S c) :
    crossToSlot (S := S) i (0 : Fin 2)
        (by rw [Function.update_self]; exact hb : S.τ (Function.update c i d i) = b) M'
        (crossToSlot (S := S) i (0 : Fin 2) ha M t) =
      permT (id : Fin (nA + 1) → Fin (nA + 1)) (IsReindexing.update_update_of_eq i he) t := by
  subst ha
  subst hb
  subst he
  exact crossToSlot_round_trip_of_unit i M M' hM t

/-!

## C. Raising and lowering as an equivalence

Both collapse orders are hypotheses here and each is used once: `M · M' = δ` gives one round trip
by section B, `M' · M = δ` the other through injectivity of the lowering half.

-/

section RoundTripEquiv

variable {nA : ℕ} {c : Fin (nA + 1) → C} {a b d e : C} (i : Fin (nA + 1))
    (he : c i = e) (ha : S.τ (c i) = a) (hb : S.τ d = b)
    (M : Tensor S ![a, d]) (M' : Tensor S ![b, e])
    (hMM' : crossToEnd (Fin.last 1) (0 : Fin 2) hb M M' =
      permT (id : Fin 2 → Fin 2)
        (IsReindexing.unitTensor_pair ((congrArg S.τ he.symm).trans ha))
        (unitTensor (S := S) e))
    (hM'M : crossToEnd (Fin.last 1) (0 : Fin 2) ((congrArg S.τ he.symm).trans ha) M' M =
      permT (id : Fin 2 → Fin 2) (IsReindexing.unitTensor_pair hb) (unitTensor (S := S) d))

set_option backward.isDefEq.respectTransparency false in
include hMM' in
/-- Lowering undoes raising: `crossToSlot_raise_lower_round_trip` with the color cast absorbed into
  `crossToSlotInv`. -/
lemma crossToSlotInv_crossToSlot (t : Tensor S c) :
    crossToSlotInv i he hb M' (crossToSlot i (0 : Fin 2) ha M t) = t := by
  simp only [crossToSlotInv, LinearMap.coe_comp, Function.comp_apply]
  -- Unfolding `crossToSlotInv` leaves the inner slot proof at the clean color `b` where the goal
  -- wants the composite `![b, e] 0`, so `rw` cannot key on the round trip; `erw` matches.
  erw [crossToSlot_raise_lower_round_trip i he ha hb M M' hMM' t, permT_permT]
  exact permT_congr_eq_id _ _ _ rfl

include hMM' hM'M in
/-- Raising undoes lowering. The reversed collapse `M' · M = δ` is the round trip at the color
  list `Function.update c i d` with the pair exchanged, which gives the lowering half a left
  inverse and hence injectivity; that upgrades `crossToSlotInv_crossToSlot` to a two-sided
  inverse. -/
lemma crossToSlot_crossToSlotInv (t : Tensor S (Function.update c i d)) :
    crossToSlot i (0 : Fin 2) ha M (crossToSlotInv i he hb M' t) = t := by
  have hswap := crossToSlot_raise_lower_round_trip (S := S) (c := Function.update c i d) i
    (by simp : Function.update c i d i = d)
    (by rw [Function.update_self]; exact hb : S.τ (Function.update c i d i) = b)
    ((congrArg S.τ he.symm).trans ha) M' M hM'M
  have hgi : Function.Injective (crossToSlot (S := S) i (0 : Fin 2)
      (show S.τ (Function.update c i d i) = b by rw [Function.update_self]; exact hb) M') := by
    intro x y hxy
    exact permT_injective _ (by rw [← hswap x, ← hswap y, hxy])
  have hinj : Function.Injective (crossToSlotInv (S := S) i he hb M') := by
    simp only [crossToSlotInv]
    exact (permT_injective _).comp hgi
  exact Function.LeftInverse.rightInverse_of_injective
    (crossToSlotInv_crossToSlot i he ha hb M M' hMM') hinj t

/-- Raising and lowering a named index against a mutually inverse pair, as a linear equivalence: the
  two color assignments `c` and `Function.update c i d` carry the same tensors. `M` and `M'` are
  matched only propositionally and `d` is unrelated to `c i`, so this covers a metric pairing two
  unrelated colors as well as a metric and its inverse at `S.τ (c i)`. -/
noncomputable def crossToSlotEquiv : Tensor S c ≃ₗ[k] Tensor S (Function.update c i d) :=
  LinearEquiv.mk (crossToSlot i (0 : Fin 2) ha M) (crossToSlotInv i he hb M').toFun
    (crossToSlotInv_crossToSlot i he ha hb M M' hMM')
    (crossToSlot_crossToSlotInv i he ha hb M M' hMM' hM'M)

end RoundTripEquiv

end Tensor

end TensorSpecies
