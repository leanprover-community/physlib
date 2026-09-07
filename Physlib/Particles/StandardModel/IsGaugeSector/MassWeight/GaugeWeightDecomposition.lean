/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Particles.StandardModel.IsGaugeSector.MassWeight.Basic
public import Physlib.Particles.StandardModel.IsGaugeSector.DerivSubmodule.GaugeWeightDecomposition
/-!
# The gauge weight decomposition of the gauge mass-weight submodules

Each mass-weight submodule of the gauge sector up to weight eight has an explicit
description in terms of the derivative submodules, and the derivative submodules carry
a gauge weight decomposition.  Transporting the latter along the former decomposes
every mass-weight submodule up to weight eight: the odd weights and weights two are
trivial, weight four is the underived field strength, weight six the once-derived one,
and weight eight the twice-derived one together with the products of two underived
ones.

-/

@[expose] public section

namespace StandardModel

open Matrix MatrixGroups GaugeAlgebra

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

/-- Weight one is trivial. -/
@[implicit_reducible]
noncomputable def massWeightSubmoduleGaugeWeightOne :
    GaugeWeightDecomposition repGauge (h.massWeightSubmodule 1) :=
  GaugeWeightDecomposition.copy (GaugeWeightDecomposition.bot hrepGauge_mul) _
    h.massWeightSubmodule_one_eq

/-- Weight two is trivial. -/
@[implicit_reducible]
noncomputable def massWeightSubmoduleGaugeWeightTwo :
    GaugeWeightDecomposition repGauge (h.massWeightSubmodule 2) :=
  GaugeWeightDecomposition.copy (GaugeWeightDecomposition.bot hrepGauge_mul) _
    h.massWeightSubmodule_two_eq

/-- Weight three is trivial. -/
@[implicit_reducible]
noncomputable def massWeightSubmoduleGaugeWeightThree :
    GaugeWeightDecomposition repGauge (h.massWeightSubmodule 3) :=
  GaugeWeightDecomposition.copy (GaugeWeightDecomposition.bot hrepGauge_mul) _
    h.massWeightSubmodule_three_eq

/-- Weight four is the underived field strength. -/
@[implicit_reducible]
noncomputable def massWeightSubmoduleGaugeWeightFour :
    GaugeWeightDecomposition repGauge (h.massWeightSubmodule 4) :=
  GaugeWeightDecomposition.copy (h.derivSubmoduleGaugeWeight 0) _
    h.massWeightSubmodule_four_eq

/-- Weight five is trivial. -/
@[implicit_reducible]
noncomputable def massWeightSubmoduleGaugeWeightFive :
    GaugeWeightDecomposition repGauge (h.massWeightSubmodule 5) :=
  GaugeWeightDecomposition.copy (GaugeWeightDecomposition.bot hrepGauge_mul) _
    h.massWeightSubmodule_five_eq

/-- Weight six is the once-derived field strength. -/
@[implicit_reducible]
noncomputable def massWeightSubmoduleGaugeWeightSix :
    GaugeWeightDecomposition repGauge (h.massWeightSubmodule 6) :=
  GaugeWeightDecomposition.copy (h.derivSubmoduleGaugeWeight 1) _
    h.massWeightSubmodule_six_eq

/-- Weight seven is trivial. -/
@[implicit_reducible]
noncomputable def massWeightSubmoduleGaugeWeightSeven :
    GaugeWeightDecomposition repGauge (h.massWeightSubmodule 7) :=
  GaugeWeightDecomposition.copy (GaugeWeightDecomposition.bot hrepGauge_mul) _
    h.massWeightSubmodule_seven_eq

/-- Weight eight is the twice-derived field strength together with the products of two
  underived ones. -/
@[implicit_reducible]
noncomputable def massWeightSubmoduleGaugeWeightEight :
    GaugeWeightDecomposition repGauge (h.massWeightSubmodule 8) :=
  GaugeWeightDecomposition.copy
    (GaugeWeightDecomposition.sup (d := h.derivSubmoduleGaugeWeight 2)
      (d' := GaugeWeightDecomposition.mul (d := h.derivSubmoduleGaugeWeight 0)
        (d' := h.derivSubmoduleGaugeWeight 0))) _
    h.massWeightSubmodule_eight_eq


/-!

## The weight-zero pieces

-/

/-- The weight-zero piece of one symbol map's decomposition: the Cartan and `u(1)`
  directions, the only ones the torus fixes. -/
lemma rangeGaugeWeight_piece_zero {n : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
    (μ ν : Fin 1 ⊕ Fin 3) :
    (h.rangeGaugeWeight l μ ν).piece 0
      = ⨆ c : Fin 4, ℂ ∙ F l μ ν (stdBasis.coord (cartanIdx c)) := by
  show (⨆ k : Fin 4 ⊕ Fin 4 ⊕ Fin 4,
    (if (0 : GaugeWeight) = adjWeight k then ℂ ∙ h.adjVec l μ ν k else ⊥)) = _
  rw [iSup_sum, iSup_sum]
  have hr : ∀ r : Fin 4, ¬ ((0 : GaugeWeight) = adjWeight (Sum.inl r)) := by decide
  have hs : ∀ r : Fin 4, ¬ ((0 : GaugeWeight) = adjWeight (Sum.inr (Sum.inl r))) := by decide
  have hc : ∀ c : Fin 4, ((0 : GaugeWeight) = adjWeight (Sum.inr (Sum.inr c))) := by decide
  simp only [hr, if_false, hs, ciSup_const, bot_sup_eq]
  rfl

/-- **The weight-zero piece of the gauge derivative submodules**: the spans of the
  field-strength symbols evaluated on the four weight-zero directions of the adjoint —
  the two `su(3)` Cartan generators, the `su(2)` Cartan generator and the `u(1)`
  generator.  The four are distinct, so the join carries no duplicates. -/
lemma derivSubmoduleGaugeWeight_piece_zero (n : ℕ) :
    (h.derivSubmoduleGaugeWeight n).piece 0
      = ⨆ (l : Fin n → Fin 1 ⊕ Fin 3) (μ : Fin 1 ⊕ Fin 3) (ν : Fin 1 ⊕ Fin 3)
          (c : Fin 4),
        ℂ ∙ F l μ ν (stdBasis.coord (cartanIdx c)) := by
  show (⨆ (l : Fin n → Fin 1 ⊕ Fin 3) (μ : Fin 1 ⊕ Fin 3) (ν : Fin 1 ⊕ Fin 3),
    (h.rangeGaugeWeight l μ ν).piece 0) = _
  exact iSup_congr fun l => iSup_congr fun μ => iSup_congr fun ν =>
    h.rangeGaugeWeight_piece_zero l μ ν

/-- The weight-zero piece at mass weight 1: the submodule itself is trivial. -/
lemma massWeightSubmoduleGaugeWeightOne_piece_zero :
    (h.massWeightSubmoduleGaugeWeightOne).piece 0 = ⊥ := rfl

/-- The weight-zero piece at mass weight 2: the submodule itself is trivial. -/
lemma massWeightSubmoduleGaugeWeightTwo_piece_zero :
    (h.massWeightSubmoduleGaugeWeightTwo).piece 0 = ⊥ := rfl

/-- The weight-zero piece at mass weight 3: the submodule itself is trivial. -/
lemma massWeightSubmoduleGaugeWeightThree_piece_zero :
    (h.massWeightSubmoduleGaugeWeightThree).piece 0 = ⊥ := rfl

/-- The weight-zero piece at mass weight 5: the submodule itself is trivial. -/
lemma massWeightSubmoduleGaugeWeightFive_piece_zero :
    (h.massWeightSubmoduleGaugeWeightFive).piece 0 = ⊥ := rfl

/-- The weight-zero piece at mass weight 7: the submodule itself is trivial. -/
lemma massWeightSubmoduleGaugeWeightSeven_piece_zero :
    (h.massWeightSubmoduleGaugeWeightSeven).piece 0 = ⊥ := rfl

/-- The weight-zero piece at mass weight four: the undifferentiated field strength on
  the four fixed directions of the adjoint. -/
lemma massWeightSubmoduleGaugeWeightFour_piece_zero :
    (h.massWeightSubmoduleGaugeWeightFour).piece 0
      = ⨆ (μ : Fin 1 ⊕ Fin 3) (ν : Fin 1 ⊕ Fin 3) (c : Fin 4),
        ℂ ∙ F ![] μ ν (stdBasis.coord (cartanIdx c)) := by
  show (h.derivSubmoduleGaugeWeight 0).piece 0 = _
  rw [h.derivSubmoduleGaugeWeight_piece_zero 0]
  exact le_antisymm (iSup_le fun l => by rw [Subsingleton.elim l ![]])
    (le_iSup (fun l : Fin 0 → Fin 1 ⊕ Fin 3 => ⨆ (μ : Fin 1 ⊕ Fin 3) (ν : Fin 1 ⊕ Fin 3)
      (c : Fin 4), ℂ ∙ F l μ ν (stdBasis.coord (cartanIdx c))) ![])

/-- The weight-zero piece at mass weight six: the once-differentiated field strength on
  the four fixed directions of the adjoint. -/
lemma massWeightSubmoduleGaugeWeightSix_piece_zero :
    (h.massWeightSubmoduleGaugeWeightSix).piece 0
      = ⨆ (l : Fin 1 → Fin 1 ⊕ Fin 3) (μ : Fin 1 ⊕ Fin 3) (ν : Fin 1 ⊕ Fin 3)
          (c : Fin 4),
        ℂ ∙ F l μ ν (stdBasis.coord (cartanIdx c)) :=
  h.derivSubmoduleGaugeWeight_piece_zero 1

/-- Any two weight pieces of a gauge derivative submodule commute: the gauge sector is
  bosonic, and every piece sits inside the derivative submodule. -/
lemma piece_mul_comm (n : ℕ) (w w' : GaugeWeight) :
    (h.derivSubmoduleGaugeWeight n).piece w * (h.derivSubmoduleGaugeWeight n).piece w'
      = (h.derivSubmoduleGaugeWeight n).piece w' * (h.derivSubmoduleGaugeWeight n).piece w := by
  have hle : ∀ v : GaugeWeight,
      (h.derivSubmoduleGaugeWeight n).piece v ≤ h.derivSubmodule n := fun v => by
    conv_rhs => rw [← (h.derivSubmoduleGaugeWeight n).iSup_piece]
    exact le_iSup _ v
  refine le_antisymm (Submodule.mul_le.mpr fun x hx y hy => ?_)
    (Submodule.mul_le.mpr fun x hx y hy => ?_) <;>
  · rw [(h.commute_of_mem_derivSubmodule (hle _ hx) (hle _ hy)).eq]
    exact Submodule.mul_mem_mul hy hx

/-!

## The gauge-component pieces

At mass weight eight the weight-zero content splits by gauge group factor.  A product
of two underived symbols has weight zero exactly when the two weights are opposite, so
the contributions are indexed by the root directions: the roots `0`, `1` and `2` are the
`su(3)` roots and give the gluon contribution, the root `3` is the `su(2)` root and
gives the isospin contribution, and the weight-zero directions pair with themselves to
give the neutral contribution of the two `su(3)` Cartan directions, the `su(2)` Cartan
direction and hypercharge.

-/

/-- The span of the underived raising vectors along the `r`-th root direction. -/
noncomputable def rootRaisingSpan (r : Fin 4) : Submodule ℂ B :=
  ⨆ (l : Fin 0 → Fin 1 ⊕ Fin 3) (μ : Fin 1 ⊕ Fin 3) (ν : Fin 1 ⊕ Fin 3),
    ℂ ∙ h.adjVec l μ ν (Sum.inl r)

/-- The span of the underived lowering vectors along the `r`-th root direction. -/
noncomputable def rootLoweringSpan (r : Fin 4) : Submodule ℂ B :=
  ⨆ (l : Fin 0 → Fin 1 ⊕ Fin 3) (μ : Fin 1 ⊕ Fin 3) (ν : Fin 1 ⊕ Fin 3),
    ℂ ∙ h.adjVec l μ ν (Sum.inr (Sum.inl r))

/-- The span of the underived weight-zero vectors: the two `su(3)` Cartan directions,
  the `su(2)` Cartan direction and the `u(1)` direction. -/
noncomputable def cartanSpan : Submodule ℂ B :=
  ⨆ (l : Fin 0 → Fin 1 ⊕ Fin 3) (μ : Fin 1 ⊕ Fin 3) (ν : Fin 1 ⊕ Fin 3) (c : Fin 4),
    ℂ ∙ h.adjVec l μ ν (Sum.inr (Sum.inr c))

/-- The gluon contribution to the weight-zero piece: the three products pairing an
  `su(3)` raising vector against the matching lowering vector. -/
noncomputable def gluonRootPart : Submodule ℂ B :=
  h.rootRaisingSpan 0 * h.rootLoweringSpan 0
    ⊔ (h.rootRaisingSpan 1 * h.rootLoweringSpan 1
      ⊔ h.rootRaisingSpan 2 * h.rootLoweringSpan 2)

/-- The isospin contribution to the weight-zero piece: the single product pairing the
  `su(2)` raising vector against the matching lowering vector. -/
noncomputable def isospinRootPart : Submodule ℂ B :=
  h.rootRaisingSpan 3 * h.rootLoweringSpan 3

/-- The neutral contribution to the weight-zero piece: the products of the weight-zero
  directions with themselves, namely the two `su(3)` Cartan directions, the `su(2)`
  Cartan direction and hypercharge. -/
noncomputable def neutralCartanPart : Submodule ℂ B := h.cartanSpan * h.cartanSpan

/-- The weight-zero piece at mass weight eight, split into the contributions of the
  three gauge group factors: the twice-differentiated field strength on the four fixed
  directions of the adjoint, joined with the gluon, isospin and neutral parts. -/
lemma massWeightSubmoduleGaugeWeightEight_piece_zero :
    (h.massWeightSubmoduleGaugeWeightEight).piece 0
      = (⨆ (l : Fin 2 → Fin 1 ⊕ Fin 3) (μ : Fin 1 ⊕ Fin 3) (ν : Fin 1 ⊕ Fin 3)
          (c : Fin 4),
          ℂ ∙ F l μ ν (stdBasis.coord (cartanIdx c)))
        ⊔ (h.gluonRootPart ⊔ (h.isospinRootPart ⊔ h.neutralCartanPart)) := by
  have h5 : (h.massWeightSubmoduleGaugeWeightEight).piece 0
      = (⨆ (l : Fin 2 → Fin 1 ⊕ Fin 3) (μ : Fin 1 ⊕ Fin 3) (ν : Fin 1 ⊕ Fin 3)
          (c : Fin 4),
          ℂ ∙ F l μ ν (stdBasis.coord (cartanIdx c)))
        ⊔ ((h.derivSubmoduleGaugeWeight 0).piece (2, -1, 0, 0)
              * (h.derivSubmoduleGaugeWeight 0).piece (-2, 1, 0, 0)
          ⊔ ((h.derivSubmoduleGaugeWeight 0).piece (1, 1, 0, 0)
              * (h.derivSubmoduleGaugeWeight 0).piece (-1, -1, 0, 0)
          ⊔ ((h.derivSubmoduleGaugeWeight 0).piece (-1, 2, 0, 0)
              * (h.derivSubmoduleGaugeWeight 0).piece (1, -2, 0, 0)
          ⊔ ((h.derivSubmoduleGaugeWeight 0).piece (0, 0, 2, 0)
              * (h.derivSubmoduleGaugeWeight 0).piece (0, 0, -2, 0)
          ⊔ ((h.derivSubmoduleGaugeWeight 0).piece (0, 0, 0, 0)
              * (h.derivSubmoduleGaugeWeight 0).piece (0, 0, 0, 0)))))) := by
    show (h.derivSubmoduleGaugeWeight 2).piece 0
        ⊔ GaugeWeightDecomposition.piece repGauge
          (h.derivSubmodule 0 * h.derivSubmodule 0) 0 = _
    rw [h.derivSubmoduleGaugeWeight_piece_zero 2,
      GaugeWeightDecomposition.mul_piece_eq_sub 0, h.derivSubmoduleGaugeWeight_supp 0]
    simp only [Finset.iSup_insert, Finset.iSup_singleton,
      show (0 : GaugeWeight) - (2, -1, 0, 0) = (-2, 1, 0, 0) from by decide,
      show (0 : GaugeWeight) - (1, 1, 0, 0) = (-1, -1, 0, 0) from by decide,
      show (0 : GaugeWeight) - (-1, 2, 0, 0) = (1, -2, 0, 0) from by decide,
      show (0 : GaugeWeight) - (0, 0, 2, 0) = (0, 0, -2, 0) from by decide,
      show (0 : GaugeWeight) - (-2, 1, 0, 0) = (2, -1, 0, 0) from by decide,
      show (0 : GaugeWeight) - (-1, -1, 0, 0) = (1, 1, 0, 0) from by decide,
      show (0 : GaugeWeight) - (1, -2, 0, 0) = (-1, 2, 0, 0) from by decide,
      show (0 : GaugeWeight) - (0, 0, -2, 0) = (0, 0, 2, 0) from by decide,
      show (0 : GaugeWeight) - (0, 0, 0, 0) = (0, 0, 0, 0) from by decide]
    rw [h.piece_mul_comm 0 (-2, 1, 0, 0) (2, -1, 0, 0),
      h.piece_mul_comm 0 (-1, -1, 0, 0) (1, 1, 0, 0),
      h.piece_mul_comm 0 (1, -2, 0, 0) (-1, 2, 0, 0),
      h.piece_mul_comm 0 (0, 0, -2, 0) (0, 0, 2, 0)]
    congr 1
    have key : ∀ a b c d e : Submodule ℂ B,
        a ⊔ (b ⊔ (c ⊔ (d ⊔ (a ⊔ (b ⊔ (c ⊔ (d ⊔ e)))))))
          = a ⊔ (b ⊔ (c ⊔ (d ⊔ e))) := by
      intro a b c d e
      simp [sup_left_comm]
    exact key _ _ _ _ _
  have e0 : ((2, -1, 0, 0) : GaugeWeight) = GaugeAlgebra.rootWeight 0 := rfl
  have e1 : ((1, 1, 0, 0) : GaugeWeight) = GaugeAlgebra.rootWeight 1 := rfl
  have e2 : ((-1, 2, 0, 0) : GaugeWeight) = GaugeAlgebra.rootWeight 2 := rfl
  have e3 : ((0, 0, 2, 0) : GaugeWeight) = GaugeAlgebra.rootWeight 3 := rfl
  have f0 : ((-2, 1, 0, 0) : GaugeWeight) = -(GaugeAlgebra.rootWeight 0) := by decide
  have f1 : ((-1, -1, 0, 0) : GaugeWeight) = -(GaugeAlgebra.rootWeight 1) := by decide
  have f2 : ((1, -2, 0, 0) : GaugeWeight) = -(GaugeAlgebra.rootWeight 2) := by decide
  have f3 : ((0, 0, -2, 0) : GaugeWeight) = -(GaugeAlgebra.rootWeight 3) := by decide
  have z0 : ((0, 0, 0, 0) : GaugeWeight) = 0 := rfl
  rw [h5, e0, e1, e2, e3, f0, f1, f2, f3, z0,
    h.derivSubmoduleGaugeWeight_piece_rootWeight,
    h.derivSubmoduleGaugeWeight_piece_rootWeight,
    h.derivSubmoduleGaugeWeight_piece_rootWeight,
    h.derivSubmoduleGaugeWeight_piece_rootWeight,
    h.derivSubmoduleGaugeWeight_piece_neg_rootWeight,
    h.derivSubmoduleGaugeWeight_piece_neg_rootWeight,
    h.derivSubmoduleGaugeWeight_piece_neg_rootWeight,
    h.derivSubmoduleGaugeWeight_piece_neg_rootWeight,
    h.derivSubmoduleGaugeWeight_piece_zero']
  simp only [gluonRootPart, isospinRootPart, neutralCartanPart, rootRaisingSpan,
    rootLoweringSpan, cartanSpan, sup_assoc]

end IsGaugeSector

end StandardModel
