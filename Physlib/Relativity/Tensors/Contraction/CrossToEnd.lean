/-
Copyright (c) 2026 Andrea Pari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrea Pari
-/
module

public import Physlib.Relativity.Tensors.ComponentIdx.Insert
public import Physlib.Relativity.Tensors.Contraction.Basis
public import Physlib.Relativity.Tensors.Constructors
/-!

# Cross contraction at named slots

## i. Overview

`contrT` contracts two slots of a single tensor. Contracting a slot of one tensor against a slot of
another (`T^{μν} u_ν`, `g_{μν} v^ν`) is `prodT` then `contrT`, which leaves every call site to
locate the two post-product slots and discharge the distinctness and `τ`-duality goals.

`crossToEnd i j hc` performs that contraction at named slots `i` and `j`, with
`hc : S.τ (cA i) = cB j` recording their `τ`-duality. The output color is
`Fin.append (cA ∘ i.succAbove) (cB ∘ j.succAbove)`: every slot of `cA` except `i`, in order, then
every slot of `cB` except `j`. These are the survivors. Any slot is reachable:
`crossToEnd 2 0 _ R u` reads as `R_{μνρσ} u^ρ`. The survivors are appended rather than interleaved,
and appending is associative, so both bracketings of a chain produce the same survivor list in the
same order.

The complementary convention keeps the replacement index in place. Contracting slot `1` of
`![c₀, c₁, c₂, c₃]` against a rank-two `![S.τ c₁, d]` gives `![c₀, c₂, c₃, d]` here and
`![c₀, d, c₂, c₃]` there; that operation is `crossToSlot`, built on this substrate in
`Physlib.Relativity.Tensors.Contraction.CrossToSlot`.

## ii. Key results

- `TensorSpecies.Tensor.crossToEnd` : the slot-addressed cross contraction.
- `TensorSpecies.Tensor.crossToEnd_two` : at rank two on each factor, a plain `contrT` of the
    product on slots `1, 2`.
- `TensorSpecies.Tensor.crossToEnd_basis` : the contraction of two basis tensors, which
    characterises `crossToEnd`.
- `TensorSpecies.Tensor.crossToEnd_basis_repr_eq_sum_fin` : the component formula at arbitrary
    slots and ranks for any species, the contraction of the two contracted basis vectors left as an
    opaque coefficient.
- `TensorSpecies.Tensor.crossToEnd_basis_repr_eq_sum_dual` : the same formula for a species with
    contraction-dual bases, the δ collapsing the two sums into one.
- `TensorSpecies.Tensor.crossToEnd_pair_basis_repr` : the component formula at rank two on each
    factor.
- `TensorSpecies.Tensor.matrixOfCs_crossToEnd_pair` : the same as a matrix equation, cross
    contraction being the product of the component matrices.
- `TensorSpecies.Tensor.crossToEnd_equivariant` : the contraction commutes with the `G`-action.
- `TensorSpecies.Tensor.crossToEnd_assoc_rankTwo` : rebracket the chain
    `A —(iA·0)— B —(last·0)— C` at rank-two `B` and `C`, up to `permT id`. Not full associativity.
- `TensorSpecies.Tensor.crossToEnd_permT_left` / `crossToEnd_permT_right` : move a relabelling of
    the left or right factor through the contraction, the contracted slot moving with it.

## iii. Table of contents

- A. Slot-addressed cross contraction
- B. Component formulas and equivariance
- C. Rebracketing the metric chain
- D. Permutation commutators

## iv. References

* None.
-/

@[expose] public section

namespace TensorSpecies

variable {k : Type} [CommRing k] {C : Type} {G : Type} [Group G]
    {V : C → Type} [∀ c, AddCommGroup (V c)] [∀ c, Module k (V c)]
    {basisIdx : C → Type} [∀ c, Fintype (basisIdx c)] [∀ c, DecidableEq (basisIdx c)]
    {rep : (c : C) → Representation k G (V c)} {b : (c : C) → Module.Basis (basisIdx c) k (V c)}
    {S : TensorSpecies k C G V basisIdx rep b}

namespace Tensor

open Fin

/-!

## A. Slot-addressed cross contraction

-/

/-- Slot-addressed cross contraction: contract slot `i` of `t1` against slot `j` of `t2`. The
  survivors are `t1`'s slots except `i` followed by `t2`'s slots except `j`, so the output color is
  a clean `Fin (nA + nB) → C` and a chain composes without recasts. -/
noncomputable def crossToEnd {nA nB : ℕ} {cA : Fin (nA + 1) → C} {cB : Fin (nB + 1) → C}
    (i : Fin (nA + 1)) (j : Fin (nB + 1)) (hc : S.τ (cA i) = cB j) :
    Tensor S cA →ₗ[k] Tensor S cB →ₗ[k]
      Tensor S (Fin.append (cA ∘ i.succAbove) (cB ∘ j.succAbove)) :=
  LinearMap.compr₂ prodT <|
    permT id
      (by
        refine ⟨Function.bijective_id, fun m => ?_⟩
        simp only [id_eq, Function.comp_apply]
        refine Fin.addCases (fun a => ?_) (fun a => ?_) m
        · rw [Fin.succSuccAbove_castAdd_natAdd_apply_castAdd i j a]
          simp only [Fin.append_left, Function.comp_apply]
        · rw [Fin.succSuccAbove_castAdd_natAdd_apply_natAdd i j a]
          simp only [Fin.append_right, Function.comp_apply]) ∘ₗ
    contrT (nA + nB)
      (Fin.cast (show (nA + 1) + (nB + 1) = (nA + nB) + 1 + 1 by omega) (Fin.castAdd (nB + 1) i))
      (Fin.cast (show (nA + 1) + (nB + 1) = (nA + nB) + 1 + 1 by omega) (Fin.natAdd (nA + 1) j))
      (by
        refine ⟨Fin.ne_of_val_ne ?_, ?_⟩
        · simp only [Fin.val_cast, Fin.val_castAdd, Fin.val_natAdd]; omega
        · simp only [Function.comp_apply, Fin.cast_cast, Fin.cast_eq_self,
            Fin.append_left, Fin.append_right]
          exact hc) ∘ₗ
    permT (Fin.cast (show (nA + nB) + 1 + 1 = (nA + 1) + (nB + 1) by omega))
      (IsReindexing.fin_cast_isReindexing _ _ (by omega))

set_option backward.isDefEq.respectTransparency false in
/-- Cross-contracting the last slot of a rank-2 tensor `A` with the `0`-slot of a rank-2 tensor `B`
  is a plain `contrT` of their product on the middle slots `1, 2`, up to a color recast. Discharging
  the slot arithmetic once lets a `contrT`-level identity lift to `crossToEnd` by one rewrite. -/
lemma crossToEnd_two {cA cB : Fin 2 → C} (h : S.τ (cA (Fin.last 1)) = cB 0)
    (A : Tensor S cA) (B : Tensor S cB) :
    crossToEnd (Fin.last 1) (0 : Fin 2) h A B
      = permT (id : Fin 2 → Fin 2) (IsReindexing.on_id.mpr (fun i => by fin_cases i <;> rfl))
          (contrT 2 (1 : Fin 4) (2 : Fin 4)
            (by
              refine ⟨by decide, ?_⟩
              rw [show (1 : Fin 4) = Fin.castAdd 2 (1 : Fin 2) from rfl,
                  show (2 : Fin 4) = Fin.natAdd 2 (0 : Fin 2) from rfl,
                  Fin.append_left, Fin.append_right]
              exact h)
            (prodT A B)) := by
  simp only [crossToEnd, LinearMap.compr₂_apply, LinearMap.comp_apply]
  rw [contrT_permT, contrT_congr (n := 2) 1 2 _ (by rfl) (by rfl)]
  simp only [permT_permT, CompTriple.comp_eq]
  refine permT_congr ?_ rfl
  ext i
  fin_cases i <;> rfl

/-!

## B. Component formulas and equivariance

`crossToEnd i j hc` is the curried bilinear map `LinearMap.compr₂ prodT` post-composed with the
linear `permT`/`contrT` factors, so additivity, scalar multiplication, and finite sums in either
argument are already the generic `map_add`/`map_smul`/`map_sum` and need no lemmas of their own.

-/

/-- Cross contraction of two basis tensors: the contraction of the two contracted basis vectors
times the basis tensor of the surviving labels. These values determine `crossToEnd i j hc`, a
bilinear map in the two tensors. -/
lemma crossToEnd_basis {nA nB : ℕ} {cA : Fin (nA + 1) → C} {cB : Fin (nB + 1) → C}
    (i : Fin (nA + 1)) (j : Fin (nB + 1)) (hc : S.τ (cA i) = cB j)
    (φA : ComponentIdx (S := S) cA) (φB : ComponentIdx (S := S) cB) :
    crossToEnd i j hc (basis cA φA) (basis cB φB) =
      S.contr (cA i) (b (cA i) (φA i) ⊗ₜ[k] b (S.τ (cA i)) (basisIdxCongr hc.symm (φB j))) •
        basis (Fin.append (cA ∘ i.succAbove) (cB ∘ j.succAbove))
          (ComponentIdx.prod.symm (fun m => φA (i.succAbove m), fun m => φB (j.succAbove m))) := by
  simp only [crossToEnd, LinearMap.compr₂_apply, LinearMap.comp_apply]
  rw [prodT_basis', permT_basis, contrT_basis, map_smul, permT_basis]
  congr 1
  · simp only [Pure.contrPCoeff, Pure.basisVector]
    rw [map_basis_eq, S.contr_basis_congr (a' := cA i) (by simp)]
    congr 3
    · exact eq_of_heq ((basisIdxCongr_heq _ _).trans ((basisIdxCongr_heq _ _).trans
        (ComponentIdx.prod_symm_heq_castAdd _ _ (Fin.ext (by simp)))))
    · exact eq_of_heq ((basisIdxCongr_heq _ _).trans ((basisIdxCongr_heq _ _).trans
        ((basisIdxCongr_heq _ _).trans ((ComponentIdx.prod_symm_heq_natAdd _ _
          (Fin.ext (by simp))).trans (basisIdxCongr_heq _ _).symm))))
  · congr 1
    funext m
    refine eq_of_heq ((basisIdxCongr_heq _ _).trans ?_)
    refine Fin.addCases (fun a => ?_) (fun a => ?_) m
    · refine ((basisIdxCongr_heq _ _).trans
        (ComponentIdx.prod_symm_heq_castAdd φA φB (a := i.succAbove a) ?_)).trans
        (ComponentIdx.prod_symm_heq_castAdd (fun m => φA (i.succAbove m))
          (fun m => φB (j.succAbove m)) (a := a) rfl).symm
      simpa using Fin.succSuccAbove_castAdd_natAdd_apply_castAdd i j a
    · refine ((basisIdxCongr_heq _ _).trans
        (ComponentIdx.prod_symm_heq_natAdd φA φB (a := j.succAbove a) ?_)).trans
        (ComponentIdx.prod_symm_heq_natAdd (fun m => φA (i.succAbove m))
          (fun m => φB (j.succAbove m)) (a := a) rfl).symm
      simpa using Fin.succSuccAbove_castAdd_natAdd_apply_natAdd i j a

/-- The component formula for a cross contraction at arbitrary slots and ranks, for any species:
each contracted label is summed over its own slot, with the contraction of the two basis vectors as
coefficient. The counterpart of `contrT_basis_repr_apply_eq_sum_fin` for two tensors. -/
lemma crossToEnd_basis_repr_eq_sum_fin {nA nB : ℕ} {cA : Fin (nA + 1) → C}
    {cB : Fin (nB + 1) → C} (i : Fin (nA + 1)) (j : Fin (nB + 1)) (hc : S.τ (cA i) = cB j)
    (t1 : Tensor S cA) (t2 : Tensor S cB)
    (φ : ComponentIdx (S := S) (Fin.append (cA ∘ i.succAbove) (cB ∘ j.succAbove))) :
    (basis (Fin.append (cA ∘ i.succAbove) (cB ∘ j.succAbove))).repr
        (crossToEnd i j hc t1 t2) φ =
      ∑ x₁ : basisIdx (cA i), ∑ x₂ : basisIdx (cB j),
        ((basis cA).repr t1 (ComponentIdx.insert i (x₁, φ.prod.1)) *
          (basis cB).repr t2 (ComponentIdx.insert j (x₂, φ.prod.2))) *
        S.contr (cA i) (b (cA i) x₁ ⊗ₜ[k]
          b (S.τ (cA i)) (basisIdxCongr (by rw [hc]) x₂)) := by
  -- Expand both tensors in their bases and evaluate each term by `crossToEnd_basis`.
  conv_lhs => rw [← (basis cA).sum_repr t1, ← (basis cB).sum_repr t2]
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, crossToEnd_basis,
    Finsupp.coe_finsetSum, Finsupp.coe_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    Module.Basis.repr_self, Finsupp.single_apply, Equiv.symm_apply_eq, Prod.ext_iff, Finset.mul_sum]
  -- Split each summed index at its contracted slot and keep the term matching `φ`.
  rw [Finset.sum_comm, ← (ComponentIdx.insert i).sum_comp, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun x₁ _ => ?_
  simp only [ComponentIdx.insert_apply_succAbove, ComponentIdx.insert_apply_self, mul_ite, mul_one,
    mul_zero, ite_and]
  rw [Finset.sum_eq_single φ.prod.1
    (fun p _ hp => Finset.sum_eq_zero fun x _ => by simp [hp]) (by simp)]
  rw [← (ComponentIdx.insert j).sum_comp, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun x₂ _ => ?_
  simp only [ComponentIdx.insert_apply_succAbove, ComponentIdx.insert_apply_self, ite_true]
  rw [Finset.sum_eq_single φ.prod.2 (fun p _ hp => by simp [hp]) (by simp)]
  simp only [ite_true]
  ring

/-- The component formula for a cross contraction at arbitrary slots and ranks, for a species with
contraction-dual bases: the contraction coefficient is `δ` and one sum remains, the contracted label
of `t2` matched to that of `t1` by `contrDualIdxEquiv`. -/
lemma crossToEnd_basis_repr_eq_sum_dual [HasContrDualBases S] {nA nB : ℕ} {cA : Fin (nA + 1) → C}
    {cB : Fin (nB + 1) → C} (i : Fin (nA + 1)) (j : Fin (nB + 1)) (hc : S.τ (cA i) = cB j)
    (t1 : Tensor S cA) (t2 : Tensor S cB)
    (φ : ComponentIdx (S := S) (Fin.append (cA ∘ i.succAbove) (cB ∘ j.succAbove))) :
    (basis (Fin.append (cA ∘ i.succAbove) (cB ∘ j.succAbove))).repr
        (crossToEnd i j hc t1 t2) φ =
      ∑ x : basisIdx (cA i),
        (basis cA).repr t1 (ComponentIdx.insert i (x, φ.prod.1)) *
        (basis cB).repr t2 (ComponentIdx.insert j
          (basisIdxCongr hc ((HasContrDualBases.contrDualIdxEquiv S (cA i)).symm x),
            φ.prod.2)) := by
  rw [crossToEnd_basis_repr_eq_sum_fin]
  simp [HasContrDualBases.contr_basis_eq_ite, mul_ite, ← Equiv.symm_apply_eq,
    ← basisIdxCongr_symm hc]

/-- The component formula for cross-contracting the last slot of a rank-two tensor with the first
slot of another. The surviving labels are supplied as a dependent pair, so the formula applies when
the species has colour-dependent basis-index types. -/
lemma crossToEnd_pair_basis_repr [HasContrDualBases S] {c0 c1 c2 c3 : C} (h : S.τ c1 = c2)
    (t1 : Tensor S ![c0, c1]) (t2 : Tensor S ![c2, c3])
    (y0 : basisIdx c0) (y3 : basisIdx c3) :
    (basis (Fin.append (![c0, c1] ∘ (Fin.last 1).succAbove)
        (![c2, c3] ∘ (0 : Fin 2).succAbove))).repr
      (crossToEnd (Fin.last 1) (0 : Fin 2) h t1 t2)
      (ComponentIdx.pair.symm (y0, y3)) =
      ∑ x : basisIdx c1,
        (basis ![c0, c1]).repr t1 (ComponentIdx.pair.symm (y0, x)) *
        (basis ![c2, c3]).repr t2
          (ComponentIdx.pair.symm
            (basisIdxCongr h ((HasContrDualBases.contrDualIdxEquiv S c1).symm x), y3)) := by
  refine (crossToEnd_basis_repr_eq_sum_dual (Fin.last 1) (0 : Fin 2) h t1 t2
    (ComponentIdx.pair.symm (y0, y3))).trans ?_
  refine Finset.sum_congr rfl fun x _ => ?_
  congr 1 <;> apply congrArg <;> funext i <;> fin_cases i <;> rfl

/-- Cross contraction of two rank-two tensors is the product of their component matrices, the
  middle labels matched by `HasContrDualBases.contrIdx`. -/
lemma matrixOfCs_crossToEnd_pair [HasContrDualBases S] {c0 c1 c2 c3 : C} (h : S.τ c1 = c2)
    (t1 : S.Tensor ![c0, c1]) (t2 : S.Tensor ![c2, c3]) :
    matrixOfCs (crossToEnd (Fin.last 1) (0 : Fin 2) h t1 t2) =
      matrixOf t1 * (matrixOf t2).submatrix ⇑(HasContrDualBases.contrIdx h) id := by
  ext y0 y3
  exact (crossToEnd_pair_basis_repr h t1 t2 y0 y3).trans rfl

/-- Cross contraction is `G`-equivariant, each of `prodT`, `contrT` and `permT` being so. -/
@[simp]
lemma crossToEnd_equivariant {nA nB : ℕ} {cA : Fin (nA + 1) → C} {cB : Fin (nB + 1) → C}
    (i : Fin (nA + 1)) (j : Fin (nB + 1)) (hc : S.τ (cA i) = cB j) (g : G)
    (t1 : Tensor S cA) (t2 : Tensor S cB) :
    crossToEnd i j hc (g • t1) (g • t2) = g • crossToEnd i j hc t1 t2 := by
  simp only [crossToEnd, LinearMap.compr₂_apply, LinearMap.comp_apply, prodT_equivariant,
    contrT_equivariant, permT_equivariant]

/-!

## C. Rebracketing the metric chain

Both bracketings reduce to one product contracted at its two seams in opposite order, then drop to
the pure-tensor level, so the seam permutation never crosses a contraction under `whnf`;
`Pure.permP_dropPair_dropPair_congr` closes the step.

-/

/-- Rebracket the chain `A —(iA·0)— B —(last·0)— C` for rank-two `B` and `C`: contracting `A·B`
  first and then `·C` equals contracting `B·C` first and then `A·`, up to the color recast
  `permT id`.

  Not full associativity: only `A`'s attachment slot `iA` is free. `B`'s rank two is what makes the
  statement possible, the second contraction being addressed at `Fin.last nA`, the slot `B`'s unique
  survivor occupies in `A·B`. Other slots are reached by conjugating with the `permT` commutators.

  With `A := T`, `B := g`, `C := g⁻¹` this reassociates `(T·g)·g⁻¹` to `T·(g·g⁻¹)`, after which
  `g·g⁻¹` collapses to the unit tensor: the step behind raising then lowering a named index. -/
lemma crossToEnd_assoc_rankTwo {nA : ℕ}
    {cA : Fin (nA + 1) → C} {cB cC : Fin 2 → C}
    (iA : Fin (nA + 1))
    (hc1 : S.τ (cA iA) = cB 0)
    (hc2 : S.τ (cB (Fin.last 1)) = cC 0)
    (tA : Tensor S cA) (tB : Tensor S cB) (tC : Tensor S cC) :
    crossToEnd (Fin.last nA) 0
        (by
          rw [show (Fin.last nA : Fin (nA + 1)) = Fin.natAdd nA (Fin.last 0) from
              Fin.ext (by simp), Fin.append_right, Function.comp_apply, Fin.succAbove_zero,
            Fin.succ_last]
          exact hc2)
        (crossToEnd iA 0 hc1 tA tB) tC =
      permT id
        (IsReindexing.on_id.mpr fun i => by
          refine Fin.addCases (fun a => ?_) (fun a => ?_) i
          · simp only [Fin.append_left, Function.comp_apply, Fin.succAbove_last,
              show a.castSucc = Fin.castAdd 1 a from rfl, Fin.append_left]
          · simp only [Fin.append_right, Function.comp_apply, Fin.succAbove_zero]
            fin_cases a
            rfl)
        (crossToEnd iA 0
          (by
            rw [show (0 : Fin (1 + 1)) = Fin.castAdd 1 (0 : Fin 1) from rfl, Fin.append_left,
              Function.comp_apply, Fin.succAbove_last, Fin.castSucc_zero]
            exact hc1)
          tA
          (crossToEnd (Fin.last 1) 0 hc2 tB tC)) := by
  simp only [crossToEnd, LinearMap.compr₂_apply, LinearMap.comp_apply, permT_permT]
  conv_rhs => rw [prodT_permT_right, prodT_contrT_snd]
  conv_lhs => rw [prodT_permT_left, prodT_contrT_fst]
  rw [prodT_swap tC, prodT_permT_left]
  conv_rhs => rw [prodT_permT_right, prodT_assoc' tA tB tC]
  simp only [permT_permT]
  generalize (prodT (prodT tA tB) tC) = X
  conv_lhs => rw [contrT_permT]
  conv_rhs => rw [contrT_permT]
  simp only [permT_permT]
  conv_lhs => rw [contrT_permT]
  conv_rhs => rw [contrT_permT]
  simp only [permT_permT]
  conv_rhs => rw [contrT_permT]
  simp only [permT_permT]
  apply induction_on_pure (t := X)
  · intro p
    simp only [contrT_pure, permT_pure, Pure.contrP, map_smul]
    rw [smul_smul, smul_smul]
    -- Index-map facts used only by this proof, kept local rather than exported. They are `clear`ed
    -- before the closing `grind`, which would otherwise ingest them as candidate facts.
    have happend_swap_val : ∀ (n n2 : ℕ) (x : Fin (n2 + n)),
        (Fin.append (Fin.natAdd n) (Fin.castAdd n2) x).val =
          if x.val < n2 then n + x.val else x.val - n2 := by
      intro n n2 x
      refine Fin.addCases (fun i => ?_) (fun i => ?_) x
      · simp [Fin.append_left]
      · simp [Fin.append_right]
    have happend_castAdd_cast : ∀ (na nb n2 : ℕ) (heq : na = nb),
        Fin.append (Fin.castAdd n2 ∘ Fin.cast heq) (Fin.natAdd nb) =
          Fin.cast (show na + n2 = nb + n2 by omega) := by
      intro na nb n2 heq
      subst heq
      simpa using Fin.append_castAdd_natAdd_eq_id
    have happend_natAdd_cast : ∀ (na nb n2 : ℕ) (heq : na = nb),
        Fin.append (Fin.castAdd nb) (Fin.natAdd n2 ∘ Fin.cast heq) =
          Fin.cast (show n2 + na = n2 + nb by omega) := by
      intro na nb n2 heq
      subst heq
      simpa using Fin.append_castAdd_natAdd_eq_id
    apply congrArg₂ (fun r t => r • t)
    · -- Coefficients.
      simp only [Pure.contrPCoeff_dropPair]
      rw [mul_comm]
      apply congrArg₂ (fun x y : k => x * y)
      all_goals apply Pure.contrPCoeff_congr p
      all_goals apply Fin.ext
      all_goals
        simp only [Nat.add_eq, Function.id_comp, Function.comp_id, Function.comp_apply,
          Fin.cast_castAdd_left, Fin.cast_natAdd_left,
          Fin.funPredPredAbove, Fin.succSuccAbove_predPredAbove,
          Fin.append_right, happend_swap_val,
          Fin.append_castAdd_natAdd_eq_id, id_eq, happend_castAdd_cast,
          happend_natAdd_cast, Fin.succSuccAbove_val, Fin.val_castAdd,
          Fin.val_natAdd, Fin.val_last, Fin.val_cast, Fin.val_zero]
        split_ifs <;> omega
    · -- Slot maps.
      apply congrArg Pure.toTensor
      apply Pure.permP_dropPair_dropPair_congr p
      intro m
      -- The `funPredPredAbove` layers are nested, so they must be peeled one at a time; one
      -- combined `simp` set thrashes `whnf` instead.
      iterate 3
        try simp only [Function.comp_apply, id_eq]
        try simp only [Fin.funPredPredAbove]
        try simp only [Fin.succSuccAbove_predPredAbove]
      apply Fin.ext
      -- Pinning a block injection to a literal slot `⟨v, _⟩` is stated at `Fin` level, not at
      -- `.val` level, so that a rewrite replaces the composite before `Fin.succSuccAbove_val`
      -- builds its `ite` conditions on it, keeping the generated `Decidable` instances in sync.
      have hcast_castAdd : ∀ {n m N : ℕ} (h : n + m = N) {i : Fin n} {v : ℕ} (hv : i.val = v),
          Fin.cast h (Fin.castAdd m i) = ⟨v, by have := i.isLt; omega⟩ := by
        intro n m N h i v hv
        exact Fin.ext (by simp [hv])
      have hcast_natAdd : ∀ {n m N : ℕ} (h : n + m = N) {i : Fin m} {v : ℕ} (hv : n + i.val = v),
          Fin.cast h (Fin.natAdd n i) = ⟨v, by have := i.isLt; omega⟩ := by
        intro n m N h i v hv
        exact Fin.ext (by simp [hv])
      -- Pin each slot to a literal `⟨v, _⟩`, innermost first, so that `succSuccAbove_val` fires.
      rw [hcast_castAdd (i := Fin.last nA) (v := nA) _ rfl,
        hcast_natAdd (n := nA + 1) (i := (0 : Fin (1 + 1))) (v := nA + 1) _
          (by simp only [Fin.val_zero, Nat.add_zero]),
        hcast_castAdd (i := iA) (v := (iA : ℕ)) _ rfl,
        Fin.natAdd_mk (1 + 1) (iA : ℕ),
        Fin.natAdd_mk (1 + 1) (nA + 1),
        hcast_castAdd (i := Fin.last 1) (v := 1) _ rfl,
        hcast_natAdd (n := 1 + 1) (i := (0 : Fin (1 + 1))) (v := 1 + 1) _
          (by simp only [Fin.val_zero, Nat.add_zero]),
        Fin.natAdd_mk (nA + 1) 1,
        Fin.natAdd_mk (nA + 1) (1 + 1)]
      simp only [Function.comp_id]
      rw [Fin.append_castAdd_natAdd_eq_id]
      simp only [Nat.add_eq, id_eq, happend_swap_val, happend_castAdd_cast,
        happend_natAdd_cast, Fin.succSuccAbove_val, Fin.val_cast]
      -- Four nested reinsertion conditionals; the split budget is `SuccSuccAbove`'s. The spent
      -- index-map hypotheses are dropped first: `grind` ingests the local context, and leaving
      -- them in costs it more than twice the elaboration time.
      clear happend_swap_val happend_castAdd_cast happend_natAdd_cast hcast_castAdd hcast_natAdd
      grind (splits := 20)
  · intro r t ht; simp only [map_smul, ht]
  · intro t1 t2 h1 h2; simp only [map_add, h1, h2]

/-!

## D. Permutation commutators

Moving a relabelling of one factor through the slot-addressed contraction. The relabelling `σ` need
not fix the contracted slot, so it carries the contraction from slot `i` to slot `σ i` and restricts
to the survivors as a map `σ'` filling the square `(σ i).succAbove ∘ σ' = σ ∘ i.succAbove`. Taking
`σ'` as an argument rather than deriving it lets a caller supply the survivor map it wants (`id`, a
swap-induced map) instead of an opaque composite.

-/

/-- Left commutator: contracting slot `i` of `permT σ t1` equals contracting slot `σ i` of `t1`,
  then relabelling the survivors by `σ'`. The square `hσ'` records how `σ'` carries the complement
  of `i` to the complement of `σ i`, and implies its bijectivity. -/
lemma crossToEnd_permT_left {nA nB : ℕ} {cA cA' : Fin (nA + 1) → C}
    {cB : Fin (nB + 1) → C}
    (i : Fin (nA + 1)) (j : Fin (nB + 1))
    (σ : Fin (nA + 1) → Fin (nA + 1)) (σ' : Fin nA → Fin nA)
    (hσ : IsReindexing cA cA' σ)
    (hσ' : (σ i).succAbove ∘ σ' = σ ∘ i.succAbove)
    (hc : S.τ (cA' i) = cB j)
    (t1 : Tensor S cA) (t2 : Tensor S cB) :
    crossToEnd i j hc (permT σ hσ t1) t2 =
      permT (Fin.append (Fin.castAdd nB ∘ σ') (Fin.natAdd nA))
        (IsReindexing.append_congr_left (cB ∘ j.succAbove)
          (IsReindexing.succAbove_of_succAbove_eq i hσ hσ'))
        (crossToEnd (σ i) j (by rw [hσ.2 i]; exact hc) t1 t2) := by
  simp only [crossToEnd, LinearMap.compr₂_apply, LinearMap.comp_apply]
  rw [prodT_permT_left]
  simp only [permT_permT]
  generalize prodT t1 t2 = X
  apply induction_on_pure (t := X)
  · intro p
    simp only [contrT_pure, permT_pure, Pure.contrP, map_smul]
    congr 1
    · simp only [Pure.contrPCoeff_permP]
      apply Pure.contrPCoeff_congr <;> (apply Fin.ext; simp)
    · apply congrArg Pure.toTensor
      apply Pure.permP_dropPair_permP_congr p
      intro m
      simp only [Function.comp_apply, id_eq]
      refine Fin.addCases (fun a => ?_) (fun b => ?_) m
      · rw [Fin.succSuccAbove_castAdd_natAdd_apply_castAdd i j a, Fin.append_left,
          Function.comp_apply, Fin.append_left, Function.comp_apply,
          Fin.succSuccAbove_castAdd_natAdd_apply_castAdd (σ i) j _,
          show (σ i).succAbove (σ' a) = σ (i.succAbove a) from congrFun hσ' a]
      · rw [Fin.succSuccAbove_castAdd_natAdd_apply_natAdd i j b, Fin.append_right,
          Fin.append_right, Fin.succSuccAbove_castAdd_natAdd_apply_natAdd (σ i) j b]
  · intro r t ht; simp only [map_smul, ht]
  · intro t1 t2 h1 h2; simp only [map_add, h1, h2]

/-- Right commutator, the mirror of `crossToEnd_permT_left`: contracting slot `j` of `permT σ t2`
  equals contracting slot `σ j` of `t2`, then relabelling the survivors by `σ'`. -/
lemma crossToEnd_permT_right {nA nB : ℕ} {cA : Fin (nA + 1) → C}
    {cB cB' : Fin (nB + 1) → C}
    (i : Fin (nA + 1)) (j : Fin (nB + 1))
    (σ : Fin (nB + 1) → Fin (nB + 1)) (σ' : Fin nB → Fin nB)
    (hσ : IsReindexing cB cB' σ)
    (hσ' : (σ j).succAbove ∘ σ' = σ ∘ j.succAbove)
    (hc : S.τ (cA i) = cB' j)
    (t1 : Tensor S cA) (t2 : Tensor S cB) :
    crossToEnd i j hc t1 (permT σ hσ t2) =
      permT (Fin.append (Fin.castAdd nB) (Fin.natAdd nA ∘ σ'))
        (IsReindexing.append_congr_right (cA ∘ i.succAbove)
          (IsReindexing.succAbove_of_succAbove_eq j hσ hσ'))
        (crossToEnd i (σ j) (by rw [hσ.2 j]; exact hc) t1 t2) := by
  simp only [crossToEnd, LinearMap.compr₂_apply, LinearMap.comp_apply]
  rw [prodT_permT_right]
  simp only [permT_permT]
  generalize prodT t1 t2 = X
  apply induction_on_pure (t := X)
  · intro p
    simp only [contrT_pure, permT_pure, Pure.contrP, map_smul]
    congr 1
    · simp only [Pure.contrPCoeff_permP]
      apply Pure.contrPCoeff_congr <;> (apply Fin.ext; simp)
    · apply congrArg Pure.toTensor
      apply Pure.permP_dropPair_permP_congr p
      intro m
      simp only [Function.comp_apply, id_eq]
      refine Fin.addCases (fun a => ?_) (fun b => ?_) m
      · rw [Fin.succSuccAbove_castAdd_natAdd_apply_castAdd i j a, Fin.append_left,
          Fin.append_left, Fin.succSuccAbove_castAdd_natAdd_apply_castAdd i (σ j) a]
      · rw [Fin.succSuccAbove_castAdd_natAdd_apply_natAdd i j b, Fin.append_right,
          Function.comp_apply, Fin.append_right, Function.comp_apply,
          Fin.succSuccAbove_castAdd_natAdd_apply_natAdd i (σ j) _,
          show (σ j).succAbove (σ' b) = σ (j.succAbove b) from congrFun hσ' b]
  · intro r t ht; simp only [map_smul, ht]
  · intro t1 t2 h1 h2; simp only [map_add, h1, h2]

end Tensor

end TensorSpecies
