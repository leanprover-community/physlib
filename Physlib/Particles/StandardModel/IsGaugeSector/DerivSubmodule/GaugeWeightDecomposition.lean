/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Particles.StandardModel.IsGaugeSector.Basic
public import Physlib.Particles.StandardModel.GaugeAlgebra.RootDecomposition
public import Physlib.Particles.StandardModel.GaugeAlgebra.Basis
public import Physlib.Particles.StandardModel.GaugeGroup.GaugeWeightDecomposition
/-!
# The gauge weight decomposition of the gauge sector

The field strength takes values in the *adjoint* representation, where — unlike the
fundamental representations carrying the fermions — the standard (Gell-Mann and Pauli)
basis is not a basis of torus eigenvectors.  The eigenvectors appear only after
complexification: the torus scales the matrix entry `(j, k)` of the `su(3)` and `su(2)`
blocks by `d j * star (d k)`, so the combinations `φ ± i ψ` of the real and imaginary
parts of an entry functional are eigenvectors, while the Cartan and `u(1)` directions
are fixed.

This file collects that computation: the torus elements act by conjugation with the
diagonal matrices `torusSU3Diag` and `torusSU2Diag`, `dualMap_pair_of_entry` turns an
entrywise scaling into the rotation of a real pair of coordinate functionals, and
`repGauge_pair_add` / `repGauge_pair_sub` / `repGauge_fixed` convert those into
eigenvector statements for the field-strength symbols in the algebra `B`.

-/

@[expose] public section

namespace StandardModel

open Matrix MatrixGroups

/-- A join over a nonempty index of a constant family of supports is that support. -/
lemma biUnion_univ_const {ι : Type*} [Fintype ι] [Nonempty ι] (t : Finset GaugeWeight) :
    (Finset.univ : Finset ι).biUnion (fun _ => t) = t := by
  ext w
  simp

/-!

## E. Eigenvectors of the gauge action among the field-strength symbols

-/

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

lemma real_smul_eq (r : ℝ) (b : B) : r • b = ((r : ℂ)) • b := by
  rw [← Complex.coe_algebraMap, algebraMap_smul]

include h in
lemma repGauge_pair_add (g : GaugeGroupI) {n : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
    (μ ν : Fin 1 ⊕ Fin 3) (φ₁ φ₂ : Module.Dual ℝ GaugeAlgebra) (z : ℂ)
    (h1 : (GaugeAlgebra.adjointMap g⁻¹).dualMap φ₁ = z.re • φ₁ - z.im • φ₂)
    (h2 : (GaugeAlgebra.adjointMap g⁻¹).dualMap φ₂ = z.im • φ₁ + z.re • φ₂) :
    repGauge g (F l μ ν φ₁ + Complex.I • F l μ ν φ₂)
      = z • (F l μ ν φ₁ + Complex.I • F l μ ν φ₂) := by
  rw [map_add, map_smul, h.repGauge_F, h.repGauge_F, h1, h2, map_sub, map_add,
    map_smul, map_smul, map_smul, map_smul, real_smul_eq z.re, real_smul_eq z.im,
    real_smul_eq z.im, real_smul_eq z.re]
  conv_rhs => rw [← Complex.re_add_im z]
  match_scalars <;> · ring_nf; try rw [Complex.I_sq]; try ring

include h in
lemma repGauge_pair_sub (g : GaugeGroupI) {n : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
    (μ ν : Fin 1 ⊕ Fin 3) (φ₁ φ₂ : Module.Dual ℝ GaugeAlgebra) (z : ℂ)
    (h1 : (GaugeAlgebra.adjointMap g⁻¹).dualMap φ₁ = z.re • φ₁ - z.im • φ₂)
    (h2 : (GaugeAlgebra.adjointMap g⁻¹).dualMap φ₂ = z.im • φ₁ + z.re • φ₂) :
    repGauge g (F l μ ν φ₁ - Complex.I • F l μ ν φ₂)
      = (starRingEnd ℂ z) • (F l μ ν φ₁ - Complex.I • F l μ ν φ₂) := by
  rw [map_sub, map_smul, h.repGauge_F, h.repGauge_F, h1, h2, map_sub, map_add,
    map_smul, map_smul, map_smul, map_smul, real_smul_eq z.re, real_smul_eq z.im,
    real_smul_eq z.im, real_smul_eq z.re]
  rw [show (starRingEnd ℂ) z = (z.re : ℂ) - (z.im : ℂ) * Complex.I by
    rw [Complex.ext_iff]; simp]
  match_scalars <;> · ring_nf; try rw [Complex.I_sq]; try ring

include h in
lemma repGauge_fixed (g : GaugeGroupI) {n : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
    (μ ν : Fin 1 ⊕ Fin 3) (φ : Module.Dual ℝ GaugeAlgebra)
    (h1 : (GaugeAlgebra.adjointMap g⁻¹).dualMap φ = φ) :
    repGauge g (F l μ ν φ) = F l μ ν φ := by
  rw [h.repGauge_F, h1]

/-!

## F. The gauge weight decomposition

-/

set_option linter.unusedVariables false in
open GaugeAlgebra in
/-- The weight vectors of the adjoint: for each root the two complex combinations of
  the paired coordinate symbols, and for each Cartan direction the symbol itself. -/
noncomputable def adjVec (h : IsGaugeSector B repGauge hrepGauge_mul repLorentz
      hrepLorentz_mul F massWeightPoly) {n : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
    (μ ν : Fin 1 ⊕ Fin 3) : Fin 4 ⊕ Fin 4 ⊕ Fin 4 → B
  | Sum.inl r => F l μ ν (stdBasis.coord (rootIdx r).1)
      + Complex.I • F l μ ν (stdBasis.coord (rootIdx r).2)
  | Sum.inr (Sum.inl r) => F l μ ν (stdBasis.coord (rootIdx r).1)
      - Complex.I • F l μ ν (stdBasis.coord (rootIdx r).2)
  | Sum.inr (Sum.inr c) => F l μ ν (stdBasis.coord (cartanIdx c))

/-- The gauge weight of each adjoint weight vector. -/
def adjWeight : Fin 4 ⊕ Fin 4 ⊕ Fin 4 → GaugeWeight
  | Sum.inl r => GaugeAlgebra.rootWeight r
  | Sum.inr (Sum.inl r) => -(GaugeAlgebra.rootWeight r)
  | Sum.inr (Sum.inr _) => 0

open GaugeAlgebra in
/-- Each adjoint weight vector is a simultaneous eigenvector of the gauge torus. -/
lemma repGauge_adjVec {n : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3) (μ ν : Fin 1 ⊕ Fin 3)
    (k : Fin 4 ⊕ Fin 4 ⊕ Fin 4) (i : Fin 4) :
    repGauge (gaugeTorusGen i) (h.adjVec l μ ν k)
      = ((expI : ℂ) ^ GaugeWeight.coord (adjWeight k) i) • h.adjVec l μ ν k := by
  match k with
  | Sum.inl r =>
    show repGauge (gaugeTorusGen i) (F l μ ν (stdBasis.coord (rootIdx r).1)
        + Complex.I • F l μ ν (stdBasis.coord (rootIdx r).2)) = _
    obtain ⟨p1, p2⟩ := dualMap_pair_of_entry (coord_rootIdx_fst r) (coord_rootIdx_snd r)
      (rootEntry_adjointMap r i)
    exact h.repGauge_pair_add _ l μ ν _ _ _ p1 p2
  | Sum.inr (Sum.inl r) =>
    show repGauge (gaugeTorusGen i) (F l μ ν (stdBasis.coord (rootIdx r).1)
        - Complex.I • F l μ ν (stdBasis.coord (rootIdx r).2)) = _
    obtain ⟨p1, p2⟩ := dualMap_pair_of_entry (coord_rootIdx_fst r) (coord_rootIdx_snd r)
      (rootEntry_adjointMap r i)
    rw [h.repGauge_pair_sub _ l μ ν _ _ _ p1 p2]
    congr 1
    rw [show GaugeWeight.coord (adjWeight (Sum.inr (Sum.inl r) :
        Fin 4 ⊕ Fin 4 ⊕ Fin 4)) i = -(GaugeWeight.coord (rootWeight r) i) from by
      simp [adjWeight, GaugeWeight.coord_neg]]
    rw [← Complex.star_def, star_expI_zpow]
  | Sum.inr (Sum.inr c) =>
    show repGauge (gaugeTorusGen i) (F l μ ν (stdBasis.coord (cartanIdx c))) = _
    rw [h.repGauge_fixed _ l μ ν _ (dualMap_coord_cartanIdx c i)]
    show _ = ((expI : ℂ) ^ GaugeWeight.coord (0 : GaugeWeight) i) • _
    simp [adjVec]

open GaugeAlgebra in
/-- The first symbol of a root pair, recovered from the two weight vectors. -/
lemma F_coord_rootIdx_fst {n : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3) (μ ν : Fin 1 ⊕ Fin 3)
    (r : Fin 4) :
    F l μ ν (stdBasis.coord (rootIdx r).1)
      = (2 : ℂ)⁻¹ • (h.adjVec l μ ν (Sum.inl r)
        + h.adjVec l μ ν (Sum.inr (Sum.inl r))) := by
  show _ = (2 : ℂ)⁻¹ • ((F l μ ν (stdBasis.coord (rootIdx r).1)
      + Complex.I • F l μ ν (stdBasis.coord (rootIdx r).2))
    + (F l μ ν (stdBasis.coord (rootIdx r).1)
      - Complex.I • F l μ ν (stdBasis.coord (rootIdx r).2)))
  match_scalars <;> · field_simp; try ring

open GaugeAlgebra in
/-- The second symbol of a root pair, recovered from the two weight vectors. -/
lemma F_coord_rootIdx_snd {n : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3) (μ ν : Fin 1 ⊕ Fin 3)
    (r : Fin 4) :
    F l μ ν (stdBasis.coord (rootIdx r).2)
      = (-(Complex.I / 2)) • (h.adjVec l μ ν (Sum.inl r)
        - h.adjVec l μ ν (Sum.inr (Sum.inl r))) := by
  show _ = (-(Complex.I / 2)) • ((F l μ ν (stdBasis.coord (rootIdx r).1)
      + Complex.I • F l μ ν (stdBasis.coord (rootIdx r).2))
    - (F l μ ν (stdBasis.coord (rootIdx r).1)
      - Complex.I • F l μ ν (stdBasis.coord (rootIdx r).2)))
  match_scalars <;> · ring_nf; try rw [Complex.I_sq]; try ring

open GaugeAlgebra in
/-- Every standard coordinate symbol lies in the join of the weight-vector lines. -/
lemma F_coord_mem_iSup {n : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3) (μ ν : Fin 1 ⊕ Fin 3)
    (a : Fin 8 ⊕ Fin 3 ⊕ Fin 1) :
    F l μ ν (stdBasis.coord a)
      ∈ ⨆ k, Submodule.span ℂ {h.adjVec l μ ν k} := by
  have hmem : ∀ k, h.adjVec l μ ν k ∈ ⨆ k, Submodule.span ℂ {h.adjVec l μ ν k} :=
    fun k => Submodule.mem_iSup_of_mem k (Submodule.mem_span_singleton_self _)
  have hfst : ∀ r : Fin 4, F l μ ν (stdBasis.coord (rootIdx r).1)
      ∈ ⨆ k, Submodule.span ℂ {h.adjVec l μ ν k} := fun r => by
    rw [h.F_coord_rootIdx_fst l μ ν r]
    exact Submodule.smul_mem _ _ (Submodule.add_mem _ (hmem _) (hmem _))
  have hsnd : ∀ r : Fin 4, F l μ ν (stdBasis.coord (rootIdx r).2)
      ∈ ⨆ k, Submodule.span ℂ {h.adjVec l μ ν k} := fun r => by
    rw [h.F_coord_rootIdx_snd l μ ν r]
    exact Submodule.smul_mem _ _ (Submodule.sub_mem _ (hmem _) (hmem _))
  have hcar : ∀ c : Fin 4, F l μ ν (stdBasis.coord (cartanIdx c))
      ∈ ⨆ k, Submodule.span ℂ {h.adjVec l μ ν k} := fun c => hmem (Sum.inr (Sum.inr c))
  match a with
  | Sum.inl k =>
    fin_cases k
    · exact hfst 0
    · exact hsnd 0
    · exact hcar 0
    · exact hfst 1
    · exact hsnd 1
    · exact hfst 2
    · exact hsnd 2
    · exact hcar 1
  | Sum.inr (Sum.inl j) =>
    fin_cases j
    · exact hfst 3
    · exact hsnd 3
    · exact hcar 2
  | Sum.inr (Sum.inr u) =>
    fin_cases u
    · exact hcar 3

open GaugeAlgebra in
/-- The span of the field-strength symbols is the join of the twelve weight lines. -/
lemma span_range_eq_iSup {n : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3) (μ ν : Fin 1 ⊕ Fin 3) :
    Submodule.span ℂ (Set.range (F l μ ν))
      = ⨆ k, Submodule.span ℂ {h.adjVec l μ ν k} := by
  refine le_antisymm (Submodule.span_le.mpr ?_) (iSup_le fun k => ?_)
  · rintro x ⟨φ, rfl⟩
    rw [← stdBasis.sum_dual_apply_smul_coord φ, map_sum]
    refine Submodule.sum_mem _ fun a _ => ?_
    rw [map_smul, real_smul_eq]
    exact Submodule.smul_mem _ _ (h.F_coord_mem_iSup l μ ν a)
  · refine (Submodule.span_singleton_le_iff_mem _ _).mpr ?_
    have hF : ∀ φ, F l μ ν φ ∈ Submodule.span ℂ (Set.range (F l μ ν)) :=
      fun φ => Submodule.subset_span ⟨φ, rfl⟩
    match k with
    | Sum.inl r =>
      exact Submodule.add_mem _ (hF _) (Submodule.smul_mem _ _ (hF _))
    | Sum.inr (Sum.inl r) =>
      exact Submodule.sub_mem _ (hF _) (Submodule.smul_mem _ _ (hF _))
    | Sum.inr (Sum.inr c) => exact hF _

/-- The gauge weight decomposition of the span of one field-strength symbol map. -/
@[implicit_reducible]
noncomputable def rangeGaugeWeight {n : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
    (μ ν : Fin 1 ⊕ Fin 3) :
    GaugeWeightDecomposition repGauge (Submodule.span ℂ (Set.range (F l μ ν))) :=
  GaugeWeightDecomposition.copy
    (GaugeWeightDecomposition.iSup hrepGauge_mul fun k =>
      GaugeWeightDecomposition.spanSingleton hrepGauge_mul (h.adjVec l μ ν k) (adjWeight k)
        (fun i => h.repGauge_adjVec l μ ν k i))
    _ (h.span_range_eq_iSup l μ ν)

/-- **The gauge weight decomposition of the gauge derivative submodules**, for any
  number of covariant derivatives. -/
@[implicit_reducible]
noncomputable instance derivSubmoduleGaugeWeight (n : ℕ) :
    GaugeWeightDecomposition repGauge (h.derivSubmodule n) :=
  GaugeWeightDecomposition.copy
    (GaugeWeightDecomposition.iSup hrepGauge_mul fun l : Fin n → Fin 1 ⊕ Fin 3 =>
      GaugeWeightDecomposition.iSup hrepGauge_mul fun μ : Fin 1 ⊕ Fin 3 =>
      GaugeWeightDecomposition.iSup hrepGauge_mul fun ν : Fin 1 ⊕ Fin 3 =>
        h.rangeGaugeWeight l μ ν)
    _ (by rw [derivSubmodule])


/-- The support of the decomposition of one symbol map: the image of `adjWeight`. -/
lemma rangeGaugeWeight_supp {n : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3) (μ ν : Fin 1 ⊕ Fin 3) :
    (h.rangeGaugeWeight l μ ν).supp
      = Finset.univ.biUnion fun k : Fin 4 ⊕ Fin 4 ⊕ Fin 4 =>
        ({adjWeight k} : Finset GaugeWeight) :=
  rfl

/-- **The gauge weights occurring in the gauge derivative submodules**: the six `su(3)`
  roots, the two `su(2)` roots and the zero weight carried by the Cartan and `u(1)`
  directions.  The weights do not depend on the number of covariant derivatives, and
  every one of them has vanishing hypercharge. -/
lemma derivSubmoduleGaugeWeight_supp (n : ℕ) :
    (h.derivSubmoduleGaugeWeight n).supp
      = {((2, -1, 0, 0) : GaugeWeight), (1, 1, 0, 0), (-1, 2, 0, 0), (0, 0, 2, 0),
        (-2, 1, 0, 0), (-1, -1, 0, 0), (1, -2, 0, 0), (0, 0, -2, 0), (0, 0, 0, 0)} := by
  have hstep : (h.derivSubmoduleGaugeWeight n).supp
      = Finset.univ.biUnion fun k : Fin 4 ⊕ Fin 4 ⊕ Fin 4 =>
        ({adjWeight k} : Finset GaugeWeight) := by
    show Finset.univ.biUnion (fun l : Fin n → Fin 1 ⊕ Fin 3 =>
      Finset.univ.biUnion fun μ : Fin 1 ⊕ Fin 3 =>
      Finset.univ.biUnion fun ν : Fin 1 ⊕ Fin 3 =>
        (h.rangeGaugeWeight l μ ν).supp) = _
    simp only [rangeGaugeWeight_supp, biUnion_univ_const]
  rw [hstep]
  decide

/-!

## G. The pieces of the decomposition

-/

/-- **The pieces of the gauge weight decomposition.**  The weight-`w` piece is the join,
  over the derivative slots and the two covector indices, of the lines spanned by those
  weight vectors whose weight is `w`. -/
lemma derivSubmoduleGaugeWeight_piece (n : ℕ) (w : GaugeWeight) :
    (h.derivSubmoduleGaugeWeight n).piece w
      = ⨆ (l : Fin n → Fin 1 ⊕ Fin 3) (μ : Fin 1 ⊕ Fin 3) (ν : Fin 1 ⊕ Fin 3)
        (k : Fin 4 ⊕ Fin 4 ⊕ Fin 4),
        (if w = adjWeight k then ℂ ∙ h.adjVec l μ ν k else ⊥) := rfl

/-- The piece at a root weight: the `+` combination for that root alone. -/
lemma derivSubmoduleGaugeWeight_piece_rootWeight (n : ℕ) (r : Fin 4) :
    (h.derivSubmoduleGaugeWeight n).piece (GaugeAlgebra.rootWeight r)
      = ⨆ (l : Fin n → Fin 1 ⊕ Fin 3) (μ : Fin 1 ⊕ Fin 3) (ν : Fin 1 ⊕ Fin 3),
        ℂ ∙ h.adjVec l μ ν (Sum.inl r) := by
  rw [h.derivSubmoduleGaugeWeight_piece]
  refine iSup_congr fun l => iSup_congr fun μ => iSup_congr fun ν => ?_
  rw [iSup_sum, iSup_sum]
  have h1 : ∀ a b : Fin 4,
      (GaugeAlgebra.rootWeight a = adjWeight (Sum.inl b)) ↔ b = a := by decide
  have h2 : ∀ a b : Fin 4,
      ¬ (GaugeAlgebra.rootWeight a = adjWeight (Sum.inr (Sum.inl b))) := by decide
  have h3 : ∀ a c : Fin 4,
      ¬ (GaugeAlgebra.rootWeight a = adjWeight (Sum.inr (Sum.inr c))) := by decide
  simp only [h1, h2, h3, if_false, iSup_bot, sup_bot_eq]
  refine le_antisymm (iSup_le fun i => ?_) (le_iSup_of_le r (by simp))
  split_ifs with hi
  · subst hi
    exact le_rfl
  · exact bot_le

/-- The piece at the opposite of a root weight: the `-` combination for that root. -/
lemma derivSubmoduleGaugeWeight_piece_neg_rootWeight (n : ℕ) (r : Fin 4) :
    (h.derivSubmoduleGaugeWeight n).piece (-(GaugeAlgebra.rootWeight r))
      = ⨆ (l : Fin n → Fin 1 ⊕ Fin 3) (μ : Fin 1 ⊕ Fin 3) (ν : Fin 1 ⊕ Fin 3),
        ℂ ∙ h.adjVec l μ ν (Sum.inr (Sum.inl r)) := by
  rw [h.derivSubmoduleGaugeWeight_piece]
  refine iSup_congr fun l => iSup_congr fun μ => iSup_congr fun ν => ?_
  rw [iSup_sum, iSup_sum]
  have h1 : ∀ a b : Fin 4, ¬ (-(GaugeAlgebra.rootWeight a) = adjWeight (Sum.inl b)) := by decide
  have h2 : ∀ a b : Fin 4,
      (-(GaugeAlgebra.rootWeight a) = adjWeight (Sum.inr (Sum.inl b))) ↔ b = a := by
    decide
  have h3 : ∀ a c : Fin 4,
      ¬ (-(GaugeAlgebra.rootWeight a) = adjWeight (Sum.inr (Sum.inr c))) := by decide
  simp only [h1, h2, h3, if_false, iSup_bot, bot_sup_eq, sup_bot_eq]
  refine le_antisymm (iSup_le fun i => ?_) (le_iSup_of_le r (by simp))
  split_ifs with hi
  · subst hi
    exact le_rfl
  · exact bot_le

/-- The weight-zero piece: the two `su(3)` Cartan generators, the `su(2)` Cartan
  generator and the `u(1)` generator, the only directions the torus fixes. -/
lemma derivSubmoduleGaugeWeight_piece_zero' (n : ℕ) :
    (h.derivSubmoduleGaugeWeight n).piece 0
      = ⨆ (l : Fin n → Fin 1 ⊕ Fin 3) (μ : Fin 1 ⊕ Fin 3) (ν : Fin 1 ⊕ Fin 3)
          (c : Fin 4),
        ℂ ∙ h.adjVec l μ ν (Sum.inr (Sum.inr c)) := by
  rw [h.derivSubmoduleGaugeWeight_piece]
  refine iSup_congr fun l => iSup_congr fun μ => iSup_congr fun ν => ?_
  rw [iSup_sum, iSup_sum]
  have h1 : ∀ b : Fin 4, ¬ ((0 : GaugeWeight) = adjWeight (Sum.inl b)) := by decide
  have h2 : ∀ b : Fin 4, ¬ ((0 : GaugeWeight) = adjWeight (Sum.inr (Sum.inl b))) := by decide
  have h3 : ∀ c : Fin 4, ((0 : GaugeWeight) = adjWeight (Sum.inr (Sum.inr c))) := by decide
  simp only [h1, h2, if_false, iSup_bot, bot_sup_eq]
  exact iSup_congr fun c => if_pos (h3 c)

/-- Every other weight has a trivial piece. -/
lemma derivSubmoduleGaugeWeight_piece_eq_bot (n : ℕ) {w : GaugeWeight}
    (hw : w ∉ (h.derivSubmoduleGaugeWeight n).supp) :
    (h.derivSubmoduleGaugeWeight n).piece w = ⊥ :=
  (h.derivSubmoduleGaugeWeight n).piece_eq_bot w hw

end IsGaugeSector


end StandardModel
