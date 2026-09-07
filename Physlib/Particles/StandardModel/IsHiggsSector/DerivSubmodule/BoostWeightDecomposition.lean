/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Particles.StandardModel.IsHiggsSector.DerivSubmodule.Basic
/-!
# The boost weight decomposition of the Higgs sector

The boost-weight analogue of `GaugeWeightDecomposition.lean`.  There the Higgs symbols were
split by their *gauge* weight, the value index doing all the work; here they are split by
their *boost* weight along a spatial axis, the derivative slots doing all the work and the
value index sitting inert.

This is the simplest of the three sectors.  The Higgs symbols `H n l φ` and `barH n l φ`
carry only the `n` covariant-derivative slots — there is no extra covector index to pack
alongside them, as there is for the field strength of the gauge sector — so
`IsLorentzCovDerivTransforms` is literally `RotatesIndices` for each of the two families.
And the value space is *Lorentz trivial*: `IsHiggsSector.repLorentz_H` runs through
`Representation.trivial ℂ SL(2,ℂ) HiggsVec` and `repLorentz_barH` through its conjugate,
so the dual value index carries boost weight `0` and contributes nothing — unlike the
Weyl-spinor value index of the fermion sector.

So the whole weight is carried by the derivative slots.  Reading the `n` slots in the
light-cone basis of the `i`-th axis produces the symbols `lightConeHiggs i c φ` and
`lightConeBarHiggs i c φ`, and these are boost eigenvectors: a slot of type `c j`
contributes `lightConeWeight (c j)` — `+2` for `D₀ - Dᵢ`, `-2` for `D₀ + Dᵢ` and `0` for
the two transverse directions — so the total weight is `∑ j, lightConeWeight (c j)`.
Joining the Higgs and conjugate-Higgs decompositions gives `derivSubmoduleBoostWeight`, a
`Lorentz.BoostWeight.WeightDecomposition` of `h.derivSubmodule n` along every axis.  The
weights that occur are the achievable slot sums: even integers of absolute value at most
`2 * n`.

-/

@[expose] public section

namespace Lorentz.BoostWeight.WeightDecomposition

open MatrixGroups

variable {K : Type*} [Field K] [Algebra ℝ K] {M : Type*} [AddCommGroup M] [Module K M]

/-- **The weight decomposition of a space the Lorentz group acts trivially on**: everything
  sits in weight zero.  `IsHiggsSector.trivialWeightDecomposition` is the case `M = K`; the
  Higgs value spaces need the same statement for the (conjugate) dual of `HiggsVec`. -/
noncomputable def ofTrivialAction (rep : Representation K SL(2,ℂ) M)
    (htriv : ∀ (g : SL(2,ℂ)) (x : M), rep g x = x) (i : Fin 3) :
    WeightDecomposition rep i ⊤ where
  piece k := if k = 0 then ⊤ else ⊥
  supp := {0}
  piece_le k := by
    by_cases hk : k = 0
    · subst hk
      rw [if_pos rfl]
      intro x _ t ht
      rw [htriv, zpow_zero, one_smul]
    · rw [if_neg hk]
      exact bot_le
  piece_eq_bot k hk := if_neg (by simpa using hk)
  iSup_piece := le_antisymm le_top (le_iSup_of_le 0 (by rw [if_pos rfl]))

/-- The pieces of a trivial action: everything in weight zero, nothing elsewhere. -/
@[simp]
lemma ofTrivialAction_piece (rep : Representation K SL(2,ℂ) M)
    (htriv : ∀ (g : SL(2,ℂ)) (x : M), rep g x = x) (i : Fin 3) (k : ℤ) :
    (ofTrivialAction rep htriv i).piece k = if k = 0 then ⊤ else ⊥ := rfl

/-- The support of a trivial action is `{0}`. -/
@[simp]
lemma ofTrivialAction_supp (rep : Representation K SL(2,ℂ) M)
    (htriv : ∀ (g : SL(2,ℂ)) (x : M), rep g x = x) (i : Fin 3) :
    (ofTrivialAction rep htriv i).supp = {0} := rfl

end Lorentz.BoostWeight.WeightDecomposition

namespace StandardModel

open TensorProduct Matrix MatrixGroups Lorentz Lorentz.BoostWeight

namespace IsHiggsSector

set_option linter.unusedVariables false

variable {B : Type} [Ring B] [Algebra ℂ B]
  {rep : Representation ℂ GaugeGroupI B}
  {hrep_mul : ∀ (g : GaugeGroupI) (b₁ b₂ : B), rep g (b₁ * b₂) = rep g b₁ * rep g b₂}
  {repLorentz : Representation ℂ SL(2,ℂ) B}
  {hrepLorentz_mul : ∀ (Λ : SL(2,ℂ)) (b₁ b₂ : B),
    repLorentz Λ (b₁ * b₂) = repLorentz Λ b₁ * repLorentz Λ b₂}
  {H : (n : ℕ) → (Fin n → (Fin 1 ⊕ Fin 3)) → Module.Dual ℂ HiggsVec →ₗ[ℂ] B}
  {barH : (n : ℕ) → (Fin n → (Fin 1 ⊕ Fin 3)) →
    Module.Dual ℂ (ConjModule HiggsVec) →ₗ[ℂ] B}
  {massWeightPoly : B →ₐ[ℂ] Polynomial B}
  (h : IsHiggsSector B rep hrep_mul repLorentz hrepLorentz_mul H barH
      massWeightPoly)

/-!

## A. The Higgs symbols rotate their derivative indices

-/

include h in
/-- **Every derivative slot of a Higgs symbol is a Lorentz vector index.**  This is the
  structure field `repLorentz_H`, read as the hypothesis the light-cone machinery runs
  on; the value index transforms by the dual of the *trivial* representation, i.e. not at
  all. -/
lemma rotatesIndices_H (n : ℕ) :
    RotatesIndices (Representation.trivial ℂ SL(2,ℂ) HiggsVec).dual repLorentz (H n) :=
  fun g l φ => h.repLorentz_H g n l φ

include h in
/-- **Every derivative slot of a conjugate-Higgs symbol is a Lorentz vector index.**  The
  value index transforms by the dual of the conjugate of the trivial representation, which
  again is the identity. -/
lemma rotatesIndices_barH (n : ℕ) :
    RotatesIndices (Representation.trivial ℂ SL(2,ℂ) HiggsVec).conj.dual repLorentz (barH n) :=
  fun g l φ => h.repLorentz_barH g n l φ

/-!

## B. The value spaces are Lorentz trivial

-/

/-- **The Higgs value space carries boost weight zero.**  The dual of the trivial
  representation on `HiggsVec` acts as the identity, so the whole of
  `Module.Dual ℂ HiggsVec` sits in weight `0`. -/
noncomputable def higgsValueWeight (i : Fin 3) :
    WeightDecomposition (Representation.trivial ℂ SL(2,ℂ) HiggsVec).dual i ⊤ :=
  WeightDecomposition.ofTrivialAction _ Representation.trivial_dual_apply i

/-- **The conjugate-Higgs value space carries boost weight zero.** -/
noncomputable def barHiggsValueWeight (i : Fin 3) :
    WeightDecomposition (Representation.trivial ℂ SL(2,ℂ) HiggsVec).conj.dual i ⊤ :=
  WeightDecomposition.ofTrivialAction _ Representation.conj_trivial_dual_apply i

/-- Every value index of the Higgs has boost weight zero. -/
lemma mem_boostWeightSubmodule_higgsValue (i : Fin 3) (φ : Module.Dual ℂ HiggsVec) :
    φ ∈ boostWeightSubmodule (Representation.trivial ℂ SL(2,ℂ) HiggsVec).dual i 0 :=
  fun t ht => by rw [Representation.trivial_dual_apply, zpow_zero, one_smul]

/-- Every value index of the conjugate Higgs has boost weight zero. -/
lemma mem_boostWeightSubmodule_barHiggsValue (i : Fin 3)
    (φ : Module.Dual ℂ (ConjModule HiggsVec)) :
    φ ∈ boostWeightSubmodule (Representation.trivial ℂ SL(2,ℂ) HiggsVec).conj.dual i 0 :=
  fun t ht => by rw [Representation.conj_trivial_dual_apply, zpow_zero, one_smul]

/-!

## C. The light-cone Higgs symbols and their boost weights

-/

/-- **The light-cone Higgs symbols.**  The `n` covariant-derivative slots of `H n` are read
  in the light-cone basis of the `i`-th spatial axis, `c j` naming the light-cone direction
  of the `j`-th slot. -/
noncomputable def lightConeHiggs (h : IsHiggsSector B rep hrep_mul repLorentz hrepLorentz_mul
      H barH massWeightPoly) {n : ℕ} (i : Fin 3) (c : Fin n → Fin 4)
    (φ : Module.Dual ℂ HiggsVec) : B :=
  lightConeDeriv (H n) i c φ

/-- **The light-cone conjugate-Higgs symbols.** -/
noncomputable def lightConeBarHiggs (h : IsHiggsSector B rep hrep_mul repLorentz
      hrepLorentz_mul H barH massWeightPoly) {n : ℕ} (i : Fin 3) (c : Fin n → Fin 4)
    (φ : Module.Dual ℂ (ConjModule HiggsVec)) : B :=
  lightConeDeriv (barH n) i c φ

/-- **The light-cone Higgs symbols have definite boost weight.**  Each of the `n` slots
  contributes the weight of its light-cone direction: `+2` for `D₀ - Dᵢ`, `-2` for
  `D₀ + Dᵢ` and `0` for the two transverse directions.  The value index is inert, so no
  further contribution appears. -/
lemma lightConeHiggs_mem {n : ℕ} (i : Fin 3) (c : Fin n → Fin 4)
    (φ : Module.Dual ℂ HiggsVec) :
    h.lightConeHiggs i c φ ∈
      boostWeightSubmodule repLorentz i (∑ j, lightConeWeight (c j)) := by
  rw [lightConeHiggs]
  simpa using lightConeDeriv_mem (H n) (h.rotatesIndices_H n) i c
    (mem_boostWeightSubmodule_higgsValue i φ)

/-- **The light-cone conjugate-Higgs symbols have definite boost weight**, carried entirely
  by the derivative slots. -/
lemma lightConeBarHiggs_mem {n : ℕ} (i : Fin 3) (c : Fin n → Fin 4)
    (φ : Module.Dual ℂ (ConjModule HiggsVec)) :
    h.lightConeBarHiggs i c φ ∈
      boostWeightSubmodule repLorentz i (∑ j, lightConeWeight (c j)) := by
  rw [lightConeBarHiggs]
  simpa using lightConeDeriv_mem (barH n) (h.rotatesIndices_barH n) i c
    (mem_boostWeightSubmodule_barHiggsValue i φ)

include h in
/-- The range of a light-cone Higgs symbol map lies in one boost weight space. -/
lemma range_lightConeDeriv_H_le {n : ℕ} (i : Fin 3) (c : Fin n → Fin 4) :
    LinearMap.range (lightConeDeriv (H n) i c)
      ≤ boostWeightSubmodule repLorentz i (∑ j, lightConeWeight (c j)) := by
  rintro _ ⟨φ, rfl⟩
  exact h.lightConeHiggs_mem i c φ

include h in
/-- The range of a light-cone conjugate-Higgs symbol map lies in one boost weight space. -/
lemma range_lightConeDeriv_barH_le {n : ℕ} (i : Fin 3) (c : Fin n → Fin 4) :
    LinearMap.range (lightConeDeriv (barH n) i c)
      ≤ boostWeightSubmodule repLorentz i (∑ j, lightConeWeight (c j)) := by
  rintro _ ⟨φ, rfl⟩
  exact h.lightConeBarHiggs_mem i c φ

/-!

## D. The boost weight decomposition of the two submodules

-/

/-- The ranges of the Higgs symbol maps, joined over the derivative indices, are the Higgs
  submodule. -/
lemma iSup_range_H (n : ℕ) :
    (⨆ d : Fin n → (Fin 1 ⊕ Fin 3), LinearMap.range (H n d)) = h.higgsSubmodule n := by
  rw [higgsSubmodule]

/-- The ranges of the conjugate-Higgs symbol maps, joined over the derivative indices, are
  the conjugate-Higgs submodule. -/
lemma iSup_range_barH (n : ℕ) :
    (⨆ d : Fin n → (Fin 1 ⊕ Fin 3), LinearMap.range (barH n d)) = h.barHiggsSubmodule n := by
  rw [barHiggsSubmodule]

/-- **The boost weight decomposition of the Higgs submodules**, along any spatial axis and
  for any number of covariant derivatives: the derivative slots carry all the weight. -/
noncomputable def higgsSubmoduleBoostWeight (h : IsHiggsSector B rep hrep_mul repLorentz
      hrepLorentz_mul H barH massWeightPoly) (n : ℕ) (i : Fin 3) :
    WeightDecomposition repLorentz i (h.higgsSubmodule n) :=
  (IsDerivativeCollection.boostDecomp (H n) (h.rotatesIndices_H n) i
    (higgsValueWeight i)).copy (h.iSup_range_H n)

/-- **The boost weight decomposition of the conjugate-Higgs submodules.** -/
noncomputable def barHiggsSubmoduleBoostWeight (h : IsHiggsSector B rep hrep_mul repLorentz
      hrepLorentz_mul H barH massWeightPoly) (n : ℕ) (i : Fin 3) :
    WeightDecomposition repLorentz i (h.barHiggsSubmodule n) :=
  (IsDerivativeCollection.boostDecomp (barH n) (h.rotatesIndices_barH n) i
    (barHiggsValueWeight i)).copy (h.iSup_range_barH n)

/-- The weight-`k` piece of the Higgs submodule is the join of the light-cone symbol ranges
  whose slots have total weight `k`. -/
lemma higgsSubmoduleBoostWeight_piece (n : ℕ) (i : Fin 3) (k : ℤ) :
    (h.higgsSubmoduleBoostWeight n i).piece k
      = ⨆ (c : Fin n → Fin 4) (_ : (∑ j, lightConeWeight (c j)) = k),
        LinearMap.range (lightConeDeriv (H n) i c) := by
  show (⨆ c : Fin n → Fin 4,
    ((higgsValueWeight i).piece (k - ∑ j, lightConeWeight (c j))).map
      (lightConeDeriv (H n) i c)) = _
  refine iSup_congr fun c => ?_
  by_cases hc : (∑ j, lightConeWeight (c j)) = k
  · rw [show k - (∑ j, lightConeWeight (c j)) = 0 from by omega, higgsValueWeight,
      WeightDecomposition.ofTrivialAction_piece, if_pos rfl, Submodule.map_top, iSup_pos hc]
  · rw [higgsValueWeight, WeightDecomposition.ofTrivialAction_piece, if_neg (by omega),
      Submodule.map_bot, iSup_neg hc]

/-- The weight-`k` piece of the conjugate-Higgs submodule is the join of the light-cone
  symbol ranges whose slots have total weight `k`. -/
lemma barHiggsSubmoduleBoostWeight_piece (n : ℕ) (i : Fin 3) (k : ℤ) :
    (h.barHiggsSubmoduleBoostWeight n i).piece k
      = ⨆ (c : Fin n → Fin 4) (_ : (∑ j, lightConeWeight (c j)) = k),
        LinearMap.range (lightConeDeriv (barH n) i c) := by
  show (⨆ c : Fin n → Fin 4,
    ((barHiggsValueWeight i).piece (k - ∑ j, lightConeWeight (c j))).map
      (lightConeDeriv (barH n) i c)) = _
  refine iSup_congr fun c => ?_
  by_cases hc : (∑ j, lightConeWeight (c j)) = k
  · rw [show k - (∑ j, lightConeWeight (c j)) = 0 from by omega, barHiggsValueWeight,
      WeightDecomposition.ofTrivialAction_piece, if_pos rfl, Submodule.map_top, iSup_pos hc]
  · rw [barHiggsValueWeight, WeightDecomposition.ofTrivialAction_piece, if_neg (by omega),
      Submodule.map_bot, iSup_neg hc]

/-!

## E. The boost weight decomposition of the Higgs derivative submodules

-/

/-- **The boost weight decomposition of the Higgs derivative submodules**, along any spatial
  axis and for any number of covariant derivatives: the join of the Higgs and
  conjugate-Higgs decompositions. -/
noncomputable def derivSubmoduleBoostWeight (h : IsHiggsSector B rep hrep_mul repLorentz
      hrepLorentz_mul H barH massWeightPoly) (n : ℕ) (i : Fin 3) :
    WeightDecomposition repLorentz i (h.derivSubmodule n) :=
  ((h.higgsSubmoduleBoostWeight n i).sup
    (h.barHiggsSubmoduleBoostWeight n i)).copy (by rw [derivSubmodule])

/-- **The weight-`k` piece of the Higgs derivative submodule** is spanned by the light-cone
  Higgs and conjugate-Higgs symbols whose `n` slots have total weight `k`. -/
lemma derivSubmoduleBoostWeight_piece (n : ℕ) (i : Fin 3) (k : ℤ) :
    (h.derivSubmoduleBoostWeight n i).piece k
      = (⨆ (c : Fin n → Fin 4) (_ : (∑ j, lightConeWeight (c j)) = k),
          LinearMap.range (lightConeDeriv (H n) i c))
        ⊔ ⨆ (c : Fin n → Fin 4) (_ : (∑ j, lightConeWeight (c j)) = k),
          LinearMap.range (lightConeDeriv (barH n) i c) := by
  show (h.higgsSubmoduleBoostWeight n i).piece k
      ⊔ (h.barHiggsSubmoduleBoostWeight n i).piece k = _
  rw [h.higgsSubmoduleBoostWeight_piece n i k, h.barHiggsSubmoduleBoostWeight_piece n i k]

/-- The Higgs boost weights are the totals of the light-cone weights of the `n` derivative
  slots. -/
lemma higgsSubmoduleBoostWeight_supp (n : ℕ) (i : Fin 3) :
    (h.higgsSubmoduleBoostWeight n i).supp
      = (Finset.univ ×ˢ ({0} : Finset ℤ)).image
        fun p : (Fin n → Fin 4) × ℤ => (∑ j, lightConeWeight (p.1 j)) + p.2 := rfl

/-- The conjugate-Higgs boost weights are the same totals. -/
lemma barHiggsSubmoduleBoostWeight_supp (n : ℕ) (i : Fin 3) :
    (h.barHiggsSubmoduleBoostWeight n i).supp
      = (Finset.univ ×ˢ ({0} : Finset ℤ)).image
        fun p : (Fin n → Fin 4) × ℤ => (∑ j, lightConeWeight (p.1 j)) + p.2 := rfl

/-- **The boost weights occurring in the Higgs derivative submodules**: the totals of the
  light-cone weights of the `n` derivative slots.  They do not depend on the axis. -/
lemma derivSubmoduleBoostWeight_supp (n : ℕ) (i : Fin 3) :
    (h.derivSubmoduleBoostWeight n i).supp
      = (Finset.univ : Finset (Fin n → Fin 4)).image
        fun c => ∑ j, lightConeWeight (c j) := by
  have hsup : (h.derivSubmoduleBoostWeight n i).supp
      = (h.higgsSubmoduleBoostWeight n i).supp
        ∪ (h.barHiggsSubmoduleBoostWeight n i).supp := rfl
  rw [hsup, h.higgsSubmoduleBoostWeight_supp n i, h.barHiggsSubmoduleBoostWeight_supp n i]
  ext k
  simp [Finset.mem_image]

/-- Every boost weight occurring in a Higgs derivative submodule is even: each slot
  contributes `+2`, `-2` or `0`. -/
lemma two_dvd_of_mem_derivSubmoduleBoostWeight_supp (n : ℕ) (i : Fin 3) {k : ℤ}
    (hk : k ∈ (h.derivSubmoduleBoostWeight n i).supp) : (2 : ℤ) ∣ k := by
  have hw : ∀ κ : Fin 4,
      lightConeWeight κ = 2 ∨ lightConeWeight κ = -2 ∨ lightConeWeight κ = 0 := by
    intro κ
    simp only [lightConeWeight]
    split_ifs <;> simp
  rw [h.derivSubmoduleBoostWeight_supp n i, Finset.mem_image] at hk
  obtain ⟨c, -, rfl⟩ := hk
  refine Finset.dvd_sum fun j _ => ?_
  rcases hw (c j) with hj | hj | hj <;> rw [hj] <;> norm_num

/-- Every boost weight occurring in a Higgs derivative submodule has absolute value at most
  `2 * n`: the `n` slots contribute at most `2` each. -/
lemma abs_le_of_mem_derivSubmoduleBoostWeight_supp (n : ℕ) (i : Fin 3) {k : ℤ}
    (hk : k ∈ (h.derivSubmoduleBoostWeight n i).supp) : |k| ≤ 2 * n := by
  have hw : ∀ κ : Fin 4,
      lightConeWeight κ = 2 ∨ lightConeWeight κ = -2 ∨ lightConeWeight κ = 0 := by
    intro κ
    simp only [lightConeWeight]
    split_ifs <;> simp
  rw [h.derivSubmoduleBoostWeight_supp n i, Finset.mem_image] at hk
  obtain ⟨c, -, rfl⟩ := hk
  calc |∑ j, lightConeWeight (c j)|
      ≤ ∑ j, |lightConeWeight (c j)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j : Fin n, (2 : ℤ) := Finset.sum_le_sum fun j _ => by
        rcases hw (c j) with hj | hj | hj <;> rw [hj] <;> norm_num
    _ = 2 * n := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

/-!

## F. The occurring weights in low order

-/

/-- The boost weights of the underived Higgs: no slots, so only `0`. -/
lemma derivSubmoduleBoostWeight_supp_zero (i : Fin 3) :
    (h.derivSubmoduleBoostWeight 0 i).supp = {0} := by
  rw [h.derivSubmoduleBoostWeight_supp 0 i]
  decide

/-- The boost weights of the once-derived Higgs: one slot, so `-2`, `0` or `2`. -/
lemma derivSubmoduleBoostWeight_supp_one (i : Fin 3) :
    (h.derivSubmoduleBoostWeight 1 i).supp = {-2, 0, 2} := by
  rw [h.derivSubmoduleBoostWeight_supp 1 i]
  decide

/-- The boost weights of the twice-derived Higgs: two slots, so `-4` to `4`. -/
lemma derivSubmoduleBoostWeight_supp_two (i : Fin 3) :
    (h.derivSubmoduleBoostWeight 2 i).supp = {-4, -2, 0, 2, 4} := by
  rw [h.derivSubmoduleBoostWeight_supp 2 i]
  decide

end IsHiggsSector

end StandardModel

end
