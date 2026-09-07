/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Particles.StandardModel.IsGaugeSector.Basic
public import Physlib.Particles.StandardModel.IsHiggsSector.Basic
/-!
# The boost weight decomposition of the gauge sector

The boost-weight analogue of `GaugeWeightDecomposition.lean`.  There the field-strength
symbols were split by their *gauge* weight, the value index doing all the work; here they
are split by their *boost* weight along a spatial axis, the Lorentz indices doing all the
work and the value index sitting inert.

The field strength `F l μ ν φ` carries two covector indices `μ`, `ν` beyond the tuple `l`
of covariant-derivative directions, and `IsGaugeSector.repLorentz_F` mixes all of them by
the same Lorentz matrix.  So the symbols are repackaged, by `fieldStrengthSymbol`, as a
family indexed by `Fin (n + 2) → Fin 1 ⊕ Fin 3`: the first `n` slots are the derivative
directions and the last two are `μ` and `ν`.  The value index is a *real* dual vector, so
the repackaged family is presented as a `ℂ`-linear map out of `ℂ` — one for each `φ` —
which is exactly the shape `IsHiggsSector.RotatesIndices` asks for,
with the trivial representation on `ℂ` recording that the value index carries no Lorentz
weight.

Everything then follows from the light-cone machinery of the Higgs sector.  Reading the
`n + 2` slots in the light-cone basis of the `i`-th axis produces the symbols
`lightConeFieldStrength i c φ`, and these are boost eigenvectors: the slot type `c j`
contributes `lightConeWeight (c j)` — `+2` for `D₀ - Dᵢ`, `-2` for `D₀ + Dᵢ` and `0` for
the two transverse directions — so the total weight is `∑ j, lightConeWeight (c j)`.
Joining over the light-cone multi-indices and over the value index gives
`derivSubmoduleBoostWeight`, a `Lorentz.BoostWeight.WeightDecomposition` of
`h.derivSubmodule n` along every axis.  The weights that occur are the achievable slot
sums: even integers of absolute value at most `2 * (n + 2)`.

-/

@[expose] public section

namespace Lorentz.BoostWeight.WeightDecomposition

open MatrixGroups

variable {K : Type*} [Field K] [Algebra ℝ K] {M : Type*} [AddCommGroup M] [Module K M]

/-- **The join of an arbitrary family of weight decompositions sharing one support.**  The
  weight-`k` piece of the join is the join of the weight-`k` pieces; a common finite set of
  weights containing every member's support is supplied, so the index type need not be
  finite. -/
noncomputable def iSupOfSupp {ι : Type*} {rep : Representation K SL(2,ℂ) M} {i : Fin 3}
    {V : ι → Submodule K M} (d : (a : ι) → WeightDecomposition rep i (V a)) (s : Finset ℤ)
    (hs : ∀ a, (d a).supp ⊆ s) : WeightDecomposition rep i (⨆ a, V a) where
  piece k := ⨆ a, (d a).piece k
  supp := s
  piece_le k := iSup_le fun a => (d a).piece_le k
  piece_eq_bot k hk := iSup_eq_bot.mpr fun a => (d a).piece_eq_bot k fun hm => hk (hs a hm)
  iSup_piece := by
    rw [iSup_comm]
    exact iSup_congr fun a => (d a).iSup_piece

/-- The pieces of an indexed join are the joins of the pieces. -/
@[simp]
lemma iSupOfSupp_piece {ι : Type*} {rep : Representation K SL(2,ℂ) M} {i : Fin 3}
    {V : ι → Submodule K M} (d : (a : ι) → WeightDecomposition rep i (V a)) (s : Finset ℤ)
    (hs : ∀ a, (d a).supp ⊆ s) (k : ℤ) :
    (iSupOfSupp d s hs).piece k = ⨆ a, (d a).piece k := rfl

end Lorentz.BoostWeight.WeightDecomposition

namespace StandardModel

open Matrix MatrixGroups Lorentz Lorentz.BoostWeight
open IsHiggsSector.IsDerivativeCollection

/-- Each light-cone direction carries weight `+2`, `-2` or `0`. -/
lemma lightConeWeight_eq_two_or_neg_two_or_zero (κ : Fin 4) :
    lightConeWeight κ = 2 ∨ lightConeWeight κ = -2 ∨ lightConeWeight κ = 0 := by
  simp only [lightConeWeight]
  split_ifs <;> simp

namespace IsGaugeSector

variable {B : Type} [Ring B] [Algebra ℂ B]
  {repGauge : Representation ℂ GaugeGroupI B}
  {hrepGauge_mul : ∀ (g : GaugeGroupI) (b₁ b₂ : B),
    repGauge g (b₁ * b₂) = repGauge g b₁ * repGauge g b₂}
  {repLorentz : Representation ℂ SL(2,ℂ) B}
  {hrepLorentz_mul : ∀ (Λ : SL(2,ℂ)) (b₁ b₂ : B),
    repLorentz Λ (b₁ * b₂) = repLorentz Λ b₁ * repLorentz Λ b₂}
  {F : {n : ℕ} → (Fin n → Fin 1 ⊕ Fin 3) → (Fin 1 ⊕ Fin 3) → (Fin 1 ⊕ Fin 3) →
    Module.Dual ℝ GaugeAlgebra →ₗ[ℝ] B}
  {massWeightPoly : B →ₐ[ℂ] Polynomial B}
  (h : IsGaugeSector B repGauge hrepGauge_mul repLorentz hrepLorentz_mul
      F massWeightPoly)

/-!

## A. The field strength as a symbol family with `n + 2` covector slots

-/

set_option linter.unusedVariables false in
/-- **The field strength repackaged as a derivative symbol family.**  The `n` covariant
  derivative directions and the two covector indices `μ`, `ν` are collected into a single
  tuple of `n + 2` spacetime directions — the first `n` slots by `Fin.castAdd`, the last two
  by `Fin.natAdd` — and the value index `φ` is frozen.  The result is presented as a
  `ℂ`-linear map out of `ℂ`, scaling the symbol, so that the light-cone machinery of the
  Higgs sector applies verbatim. -/
noncomputable def fieldStrengthSymbol
    (h : IsGaugeSector B repGauge hrepGauge_mul repLorentz hrepLorentz_mul F massWeightPoly)
    {n : ℕ} (φ : Module.Dual ℝ GaugeAlgebra) (d : Fin (n + 2) → Fin 1 ⊕ Fin 3) :
    ℂ →ₗ[ℂ] B :=
  LinearMap.toSpanSingleton ℂ B
    (F (fun j : Fin n => d (Fin.castAdd 2 j)) (d (Fin.natAdd n 0)) (d (Fin.natAdd n 1)) φ)

/-- The packed symbol map scales the field strength. -/
lemma fieldStrengthSymbol_apply {n : ℕ} (φ : Module.Dual ℝ GaugeAlgebra)
    (d : Fin (n + 2) → Fin 1 ⊕ Fin 3) (z : ℂ) :
    h.fieldStrengthSymbol φ d z =
      z • F (fun j : Fin n => d (Fin.castAdd 2 j)) (d (Fin.natAdd n 0))
        (d (Fin.natAdd n 1)) φ := rfl

/-- The range of a packed symbol map is the line through the field-strength symbol. -/
lemma range_fieldStrengthSymbol {n : ℕ} (φ : Module.Dual ℝ GaugeAlgebra)
    (d : Fin (n + 2) → Fin 1 ⊕ Fin 3) :
    LinearMap.range (h.fieldStrengthSymbol φ d) =
      Submodule.span ℂ {F (fun j : Fin n => d (Fin.castAdd 2 j)) (d (Fin.natAdd n 0))
        (d (Fin.natAdd n 1)) φ} :=
  (LinearMap.span_singleton_eq_range ℂ B _).symm

include h in
/-- **All `n + 2` slots of the packed family are Lorentz vector indices.**  The single
  Lorentz matrix of `repLorentz_F` mixes the derivative directions and the two covector
  indices alike, so after packing the law is one sum over one product; the value index is a
  real dual vector and carries no Lorentz weight, recorded by the trivial representation
  on `ℂ`. -/
lemma rotatesIndices_fieldStrengthSymbol {n : ℕ} (φ : Module.Dual ℝ GaugeAlgebra) :
    RotatesIndices (1 : Representation ℂ SL(2,ℂ) ℂ) repLorentz
      (h.fieldStrengthSymbol (n := n) φ) := by
  intro g d w
  calc repLorentz g (h.fieldStrengthSymbol φ d w)
      = ∑ q : (Fin n → Fin 1 ⊕ Fin 3) × (Fin 1 ⊕ Fin 3) × (Fin 1 ⊕ Fin 3),
          (w * ((∏ j, (((SL2C.toLorentzGroup g).1 (q.1 j)
                (d (Fin.castAdd 2 j)) : ℝ) : ℂ)) *
            ((((SL2C.toLorentzGroup g).1 q.2.1 (d (Fin.natAdd n 0)) : ℝ) : ℂ) *
              (((SL2C.toLorentzGroup g).1 q.2.2 (d (Fin.natAdd n 1)) : ℝ) : ℂ)))) •
            F q.1 q.2.1 q.2.2 φ := by
        simp only [Fintype.sum_prod_type, fieldStrengthSymbol,
          LinearMap.toSpanSingleton_apply, map_smul, h.repLorentz_F, Finset.smul_sum,
          smul_smul]
    _ = ∑ A : Fin (n + 2) → Fin 1 ⊕ Fin 3,
          (∏ j, (((SL2C.toLorentzGroup g).1 (A j) (d j) : ℝ) : ℂ)) •
            h.fieldStrengthSymbol φ A ((1 : Representation ℂ SL(2,ℂ) ℂ) g w) := by
        refine Fintype.sum_equiv (((Equiv.refl (Fin n → Fin 1 ⊕ Fin 3)).prodCongr
          (piFinTwoEquiv (fun _ => Fin 1 ⊕ Fin 3)).symm).trans (Fin.appendEquiv n 2)) _ _ ?_
        rintro ⟨p, a, b⟩
        show _ = (∏ j, (((SL2C.toLorentzGroup g).1 (Fin.append p ![a, b] j)
            (d j) : ℝ) : ℂ)) • h.fieldStrengthSymbol φ (Fin.append p ![a, b])
              ((1 : Representation ℂ SL(2,ℂ) ℂ) g w)
        rw [Fin.prod_univ_add, Fin.prod_univ_two]
        simp only [fieldStrengthSymbol, LinearMap.toSpanSingleton_apply, Fin.append_left,
          Fin.append_right, Matrix.cons_val_zero, Matrix.cons_val_one, smul_smul]
        congr 1
        rw [show ((1 : Representation ℂ SL(2,ℂ) ℂ) g) w = w from rfl]
        ring

/-!

## B. The light-cone field strengths and their boost weights

-/

set_option linter.unusedVariables false in
/-- **The light-cone field strengths.**  The `n + 2` slots of the packed symbol — the
  covariant derivative directions together with the two covector indices — are read in the
  light-cone basis of the `i`-th spatial axis, `c j` naming the light-cone direction of the
  `j`-th slot. -/
noncomputable def lightConeFieldStrength
    (h : IsGaugeSector B repGauge hrepGauge_mul repLorentz hrepLorentz_mul F massWeightPoly)
    {n : ℕ} (i : Fin 3) (c : Fin (n + 2) → Fin 4) (φ : Module.Dual ℝ GaugeAlgebra) : B :=
  lightConeDeriv (h.fieldStrengthSymbol (n := n) φ) i c 1

/-- The light-cone symbol map scales the light-cone field strength. -/
lemma lightConeDeriv_fieldStrengthSymbol_apply {n : ℕ} (i : Fin 3) (c : Fin (n + 2) → Fin 4)
    (φ : Module.Dual ℝ GaugeAlgebra) (z : ℂ) :
    lightConeDeriv (h.fieldStrengthSymbol (n := n) φ) i c z =
      z • h.lightConeFieldStrength i c φ := by
  conv_lhs => rw [← mul_one z, ← smul_eq_mul]
  rw [map_smul]
  rfl

/-- The range of a light-cone symbol map is the line through the light-cone field
  strength. -/
lemma range_lightConeDeriv_fieldStrengthSymbol {n : ℕ} (i : Fin 3) (c : Fin (n + 2) → Fin 4)
    (φ : Module.Dual ℝ GaugeAlgebra) :
    LinearMap.range (lightConeDeriv (h.fieldStrengthSymbol (n := n) φ) i c) =
      Submodule.span ℂ {h.lightConeFieldStrength i c φ} := by
  refine le_antisymm ?_ ((Submodule.span_singleton_le_iff_mem _ _).mpr ⟨1, rfl⟩)
  rintro _ ⟨z, rfl⟩
  rw [h.lightConeDeriv_fieldStrengthSymbol_apply i c φ z]
  exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)

/-- **The light-cone field strengths have definite boost weight.**  Each of the `n + 2`
  slots contributes the weight of its light-cone direction: `+2` for `D₀ - Dᵢ`, `-2` for
  `D₀ + Dᵢ` and `0` for the two transverse directions.  The value index is inert, so no
  further contribution appears. -/
lemma lightConeFieldStrength_mem {n : ℕ} (i : Fin 3) (c : Fin (n + 2) → Fin 4)
    (φ : Module.Dual ℝ GaugeAlgebra) :
    h.lightConeFieldStrength i c φ ∈
      boostWeightSubmodule repLorentz i (∑ j, lightConeWeight (c j)) :=
  range_lightConeDeriv_le (h.fieldStrengthSymbol (n := n) φ)
    (h.rotatesIndices_fieldStrengthSymbol φ) i c ⟨1, rfl⟩

/-!

## C. The boost weight decomposition

-/

set_option linter.unusedVariables false in
/-- The boost weight decomposition of the span of the field-strength symbols at one fixed
  value index. -/
noncomputable def symbolBoostWeight
    (h : IsGaugeSector B repGauge hrepGauge_mul repLorentz hrepLorentz_mul F massWeightPoly)
    {n : ℕ} (i : Fin 3) (φ : Module.Dual ℝ GaugeAlgebra) :
    WeightDecomposition repLorentz i
      (⨆ d : Fin (n + 2) → Fin 1 ⊕ Fin 3, LinearMap.range (h.fieldStrengthSymbol φ d)) :=
  boostDecomp (h.fieldStrengthSymbol (n := n) φ) (h.rotatesIndices_fieldStrengthSymbol φ) i
    (IsHiggsSector.trivialWeightDecomposition i)

/-- The weight-`k` piece at one value index is spanned by the light-cone field strengths
  whose slots have total weight `k`. -/
lemma symbolBoostWeight_piece {n : ℕ} (i : Fin 3) (φ : Module.Dual ℝ GaugeAlgebra) (k : ℤ) :
    (h.symbolBoostWeight (n := n) i φ).piece k
      = ⨆ (c : Fin (n + 2) → Fin 4) (_ : (∑ j, lightConeWeight (c j)) = k),
        Submodule.span ℂ {h.lightConeFieldStrength i c φ} := by
  show (⨆ c : Fin (n + 2) → Fin 4,
    ((IsHiggsSector.trivialWeightDecomposition i).piece
      (k - ∑ j, lightConeWeight (c j))).map
        (lightConeDeriv (h.fieldStrengthSymbol (n := n) φ) i c)) = _
  refine iSup_congr fun c => ?_
  by_cases hc : (∑ j, lightConeWeight (c j)) = k
  · rw [show k - (∑ j, lightConeWeight (c j)) = 0 from by omega,
      IsHiggsSector.trivialWeightDecomposition_piece, if_pos rfl, Submodule.map_top,
      iSup_pos hc, h.range_lightConeDeriv_fieldStrengthSymbol i c φ]
  · rw [IsHiggsSector.trivialWeightDecomposition_piece, if_neg (by omega),
      Submodule.map_bot, iSup_neg hc]

/-- The packed symbol ranges, joined over the value index and the `n + 2` slots, recover the
  gauge derivative submodule: packing and unpacking a tuple of directions is a bijection. -/
lemma iSup_range_fieldStrengthSymbol (n : ℕ) :
    (⨆ (φ : Module.Dual ℝ GaugeAlgebra) (d : Fin (n + 2) → Fin 1 ⊕ Fin 3),
      LinearMap.range (h.fieldStrengthSymbol φ d)) = h.derivSubmodule n := by
  rw [derivSubmodule]
  refine le_antisymm (iSup_le fun φ => iSup_le fun d => ?_) ?_
  · rw [h.range_fieldStrengthSymbol φ d, Submodule.span_singleton_le_iff_mem]
    exact Submodule.mem_iSup_of_mem _ (Submodule.mem_iSup_of_mem _
      (Submodule.mem_iSup_of_mem _ (Submodule.subset_span ⟨φ, rfl⟩)))
  · refine iSup_le fun l => iSup_le fun μ => iSup_le fun ν => Submodule.span_le.mpr ?_
    rintro _ ⟨φ, rfl⟩
    refine Submodule.mem_iSup_of_mem φ
      (Submodule.mem_iSup_of_mem (Fin.append l ![μ, ν]) ?_)
    rw [h.range_fieldStrengthSymbol φ (Fin.append l ![μ, ν])]
    simp only [Fin.append_left, Fin.append_right, Matrix.cons_val_zero, Matrix.cons_val_one]
    exact Submodule.mem_span_singleton_self _

set_option linter.unusedVariables false in
/-- **The boost weight decomposition of the gauge derivative submodules**, along any spatial
  axis and for any number of covariant derivatives. -/
noncomputable def derivSubmoduleBoostWeight
    (h : IsGaugeSector B repGauge hrepGauge_mul repLorentz hrepLorentz_mul F massWeightPoly)
    (n : ℕ) (i : Fin 3) : WeightDecomposition repLorentz i (h.derivSubmodule n) :=
  (WeightDecomposition.iSupOfSupp (fun φ => h.symbolBoostWeight (n := n) i φ)
    ((Finset.univ ×ˢ ({0} : Finset ℤ)).image
      fun p : (Fin (n + 2) → Fin 4) × ℤ => (∑ j, lightConeWeight (p.1 j)) + p.2)
    fun _ => subset_rfl).copy (h.iSup_range_fieldStrengthSymbol n)

/-- **The weight-`k` piece of the gauge derivative submodule** is spanned by the light-cone
  field strengths whose `n + 2` slots have total weight `k`, over all value indices. -/
lemma derivSubmoduleBoostWeight_piece (n : ℕ) (i : Fin 3) (k : ℤ) :
    (h.derivSubmoduleBoostWeight n i).piece k
      = ⨆ (φ : Module.Dual ℝ GaugeAlgebra) (c : Fin (n + 2) → Fin 4)
          (_ : (∑ j, lightConeWeight (c j)) = k),
        Submodule.span ℂ {h.lightConeFieldStrength i c φ} := by
  show (⨆ φ, (h.symbolBoostWeight (n := n) i φ).piece k) = _
  exact iSup_congr fun φ => h.symbolBoostWeight_piece i φ k

/-- **The boost weights occurring in the gauge derivative submodules**: the totals of the
  light-cone weights of the `n + 2` slots.  They do not depend on the axis. -/
lemma derivSubmoduleBoostWeight_supp (n : ℕ) (i : Fin 3) :
    (h.derivSubmoduleBoostWeight n i).supp
      = (Finset.univ : Finset (Fin (n + 2) → Fin 4)).image
        fun c => ∑ j, lightConeWeight (c j) := by
  show ((Finset.univ ×ˢ ({0} : Finset ℤ)).image
      fun p : (Fin (n + 2) → Fin 4) × ℤ => (∑ j, lightConeWeight (p.1 j)) + p.2) = _
  ext k
  simp [Finset.mem_image]

/-- Every boost weight occurring in a gauge derivative submodule is even: each slot
  contributes `+2`, `-2` or `0`. -/
lemma two_dvd_of_mem_derivSubmoduleBoostWeight_supp (n : ℕ) (i : Fin 3) {k : ℤ}
    (hk : k ∈ (h.derivSubmoduleBoostWeight n i).supp) : (2 : ℤ) ∣ k := by
  rw [h.derivSubmoduleBoostWeight_supp n i, Finset.mem_image] at hk
  obtain ⟨c, -, rfl⟩ := hk
  refine Finset.dvd_sum fun j _ => ?_
  rcases lightConeWeight_eq_two_or_neg_two_or_zero (c j) with hj | hj | hj <;>
    rw [hj] <;> norm_num

/-- Every boost weight occurring in a gauge derivative submodule has absolute value at most
  `2 * (n + 2)`: the `n + 2` slots contribute at most `2` each. -/
lemma abs_le_of_mem_derivSubmoduleBoostWeight_supp (n : ℕ) (i : Fin 3) {k : ℤ}
    (hk : k ∈ (h.derivSubmoduleBoostWeight n i).supp) : |k| ≤ 2 * (n + 2) := by
  rw [h.derivSubmoduleBoostWeight_supp n i, Finset.mem_image] at hk
  obtain ⟨c, -, rfl⟩ := hk
  calc |∑ j, lightConeWeight (c j)|
      ≤ ∑ j, |lightConeWeight (c j)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j : Fin (n + 2), (2 : ℤ) := Finset.sum_le_sum fun j _ => by
        rcases lightConeWeight_eq_two_or_neg_two_or_zero (c j) with hj | hj | hj <;>
          rw [hj] <;> norm_num
    _ = 2 * (n + 2) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        push_cast
        ring

/-!

## The occurring weights in low order

-/

/-- The light-cone weight totals of two slots. -/
lemma image_lightConeWeight_sum_two :
    (Finset.univ : Finset (Fin 2 → Fin 4)).image (fun c => ∑ j, lightConeWeight (c j))
      = {-4, -2, 0, 2, 4} := by decide

/-- The light-cone weight totals of three slots. -/
lemma image_lightConeWeight_sum_three :
    (Finset.univ : Finset (Fin 3 → Fin 4)).image (fun c => ∑ j, lightConeWeight (c j))
      = {-6, -4, -2, 0, 2, 4, 6} := by decide

set_option maxRecDepth 4000 in
/-- The light-cone weight totals of four slots. -/
lemma image_lightConeWeight_sum_four :
    (Finset.univ : Finset (Fin 4 → Fin 4)).image (fun c => ∑ j, lightConeWeight (c j))
      = {-8, -6, -4, -2, 0, 2, 4, 6, 8} := by decide

/-- The boost weights of the underived field strength: two slots, so `-4` to `4`. -/
lemma derivSubmoduleBoostWeight_supp_zero (i : Fin 3) :
    (h.derivSubmoduleBoostWeight 0 i).supp = {-4, -2, 0, 2, 4} := by
  rw [h.derivSubmoduleBoostWeight_supp 0 i]
  exact image_lightConeWeight_sum_two

/-- The boost weights of the once-derived field strength: three slots, so `-6` to `6`. -/
lemma derivSubmoduleBoostWeight_supp_one (i : Fin 3) :
    (h.derivSubmoduleBoostWeight 1 i).supp = {-6, -4, -2, 0, 2, 4, 6} := by
  rw [h.derivSubmoduleBoostWeight_supp 1 i]
  exact image_lightConeWeight_sum_three

/-- The boost weights of the twice-derived field strength: four slots, so `-8` to `8`. -/
lemma derivSubmoduleBoostWeight_supp_two (i : Fin 3) :
    (h.derivSubmoduleBoostWeight 2 i).supp = {-8, -6, -4, -2, 0, 2, 4, 6, 8} := by
  rw [h.derivSubmoduleBoostWeight_supp 2 i]
  exact image_lightConeWeight_sum_four

end IsGaugeSector

end StandardModel

end
