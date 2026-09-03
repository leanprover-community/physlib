/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.GroupAction.ConjAct
public import Mathlib.MeasureTheory.Function.LpSpace.Complete
public import Mathlib.MeasureTheory.Function.LpSpace.DomAct.Basic
public import Mathlib.MeasureTheory.Group.Measure
public import PhyslibAlpha.QuantumMechanics.RepresentationTheory.TauCetiPort.MeasureTheory.Function.Lp.CompMeasurePreservingEquiv

/-!
# Conjugation-invariance in `Lp`, and the class functions

Conjugation `g ↦ h * g * h⁻¹` on a group is left translation followed by right translation, so a
measure that is invariant under both is invariant under conjugation.  Normalized Haar measure on a
compact group is such a measure, which is what makes "class function" a meaningful condition on an
almost-everywhere equivalence class.

This file records that invariance as the two typeclasses Mathlib's machinery consumes: the
conjugation action of `ConjAct G` on `G` is measurable and measure-preserving, so
Mathlib's `DomMulAct` action supplies an isometric action of `(ConjAct G)ᵈᵐᵃ` on `Lp E p μ` by
precomposition, `(c • f) g = f (h * g * h⁻¹)`.  The **class functions** `classFunctionLp` are the
vectors that action fixes: a closed submodule, since each conjugation acts by an isometry.

Only conjugation-invariance, `SMulInvariantMeasure (ConjAct G) G μ`, is asked of `μ` for that
theory; two-sided translation invariance appears just once, as the hypothesis under which
`TauCeti.instSMulInvariantMeasureConjAct` supplies it.

The condition is on the *class*, not on a representative, and that is the point of packaging it
this way rather than as a pointwise slogan: pointwise conjugation-invariance of a function is not
stable under changing it on a null set, so it does not descend to `Lp` at all.  What descends is
`TauCeti.mem_classFunctionLp_iff_ae`, invariance up to a null set.

## Main definitions

* `TauCeti.classFunctionLp`: the class functions in `Lp E p μ`, a submodule.
* `TauCeti.conjLpₗᵢ`: conjugation by a fixed element, as a linear isometric equivalence of
  `Lp E p μ`. This is the same operation as the `(ConjAct G)ᵈᵐᵃ`-action; for `p = 2`, the bundled
  linear isometry gives inner-product preservation through `LinearIsometry.inner_map_map`.

## Main statements

* `TauCeti.instMeasurableConstSMulConjAct` and `TauCeti.instSMulInvariantMeasureConjAct`: the two
  instances that unlock `DomMulAct`'s action on `Lp`, the second deriving conjugation-invariance
  from two-sided translation invariance.
* `TauCeti.measurePreserving_conj`: conjugation preserves a conjugation-invariant measure, stated
  through the group operation.
* `TauCeti.conjAct_smul_Lp_ae_eq`: the induced action on `Lp` is precomposition with conjugation.
* `TauCeti.compMeasurePreserving_conj_eq_smul`: precomposition with conjugation is that action.
* `TauCeti.mem_classFunctionLp_iff_ae`: membership read on representatives, as invariance almost
  everywhere.
* `TauCeti.isClosed_classFunctionLp`: the class functions are a closed subspace, hence
  (`TauCeti.instCompleteSpaceClassFunctionLp`) complete.
* `TauCeti.mem_classFunctionLp_of_ae_eq_of_conj_invariant`: a pointwise invariant representative
  makes a class function.
* `TauCeti.conjLpₗᵢ_apply_of_mem_classFunctionLp`: a class function is fixed by every conjugation
  isometry.

The compact-group specialization -- that the character of a continuous representation is a class
function in `L²(G)` -- is in `TauCeti/RepresentationTheory/Compact/ClassFunctionLp.lean`.
-/

public section

open MeasureTheory
open scoped ENNReal

namespace TauCeti

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul G]

/-- Conjugation by a fixed element is measurable, so the conjugation action of `ConjAct G` on `G`
has measurable orbit maps. -/
instance instMeasurableConstSMulConjAct : MeasurableConstSMul (ConjAct G) G where
  measurable_const_smul c := by
    simp only [ConjAct.smul_def]
    exact (measurable_id.const_mul _).mul_const _

/-- **A two-sided invariant measure is invariant under conjugation.**  Conjugation by `h` is left
translation by `h` followed by right translation by `h⁻¹`. -/
instance instSMulInvariantMeasureConjAct {μ : Measure G} [μ.IsMulLeftInvariant]
    [μ.IsMulRightInvariant] : SMulInvariantMeasure (ConjAct G) G μ where
  measure_preimage_smul c s hs := by
    simp only [ConjAct.smul_def]
    exact ((measurePreserving_mul_right μ (ConjAct.ofConjAct c)⁻¹).comp
      (measurePreserving_mul_left μ (ConjAct.ofConjAct c))).measure_preimage hs.nullMeasurableSet

/-- **Conjugation preserves a conjugation-invariant measure**, stated in terms of the group
operation rather than the action of `ConjAct G`.  Bi-invariant measures are the intended source of
the hypothesis (`TauCeti.instSMulInvariantMeasureConjAct`). -/
theorem measurePreserving_conj (μ : Measure G) [SMulInvariantMeasure (ConjAct G) G μ] (h : G) :
    MeasurePreserving (fun g ↦ h * g * h⁻¹) μ μ :=
  measurePreserving_smul (ConjAct.toConjAct h) μ

variable {E : Type*} [NormedAddCommGroup E] {p : ℝ≥0∞} {μ : Measure G}
  [SMulInvariantMeasure (ConjAct G) G μ]

/-- The action of `(ConjAct G)ᵈᵐᵃ` on `Lp E p μ` is precomposition with conjugation: the class of
`f` is sent to the class of `g ↦ f (h * g * h⁻¹)`. -/
theorem conjAct_smul_Lp_ae_eq (h : G) (f : Lp E p μ) :
    DomMulAct.mk (ConjAct.toConjAct h) • f =ᵐ[μ] fun g ↦ f (h * g * h⁻¹) := by
  simpa only [Equiv.symm_apply_apply, ConjAct.smul_def, ConjAct.ofConjAct_toConjAct] using
    DomMulAct.smul_Lp_ae_eq (DomMulAct.mk (ConjAct.toConjAct h)) f

/-- **The class functions in `Lp`.**  The submodule of `Lp E p μ` fixed by every conjugation,
for a conjugation-invariant measure `μ` on a group `G`.

Invariance is a condition on the *class*, not on a representative: an element of `Lp` is a class
function exactly when each of its conjugates agrees with it almost everywhere
(`TauCeti.mem_classFunctionLp_iff_ae`).  Asking instead for a pointwise identity would not define a
submodule of `Lp` at all, since it is not stable under changing a representative on a null set. -/
def classFunctionLp (𝕜 E : Type*) [NormedRing 𝕜] [NormedAddCommGroup E] [Module 𝕜 E]
    [IsBoundedSMul 𝕜 E] (p : ℝ≥0∞) (μ : Measure G) [SMulInvariantMeasure (ConjAct G) G μ] :
    Submodule 𝕜 (Lp E p μ) where
  carrier := {f | ∀ c : (ConjAct G)ᵈᵐᵃ, c • f = f}
  add_mem' hf hg c := by rw [DomMulAct.smul_Lp_add, hf c, hg c]
  zero_mem' c := DomMulAct.smul_Lp_zero c
  smul_mem' a _ hf c := by rw [smul_comm, hf c]

variable (𝕜 : Type*) [NormedRing 𝕜] [Module 𝕜 E] [IsBoundedSMul 𝕜 E]

@[simp]
theorem mem_classFunctionLp_iff {f : Lp E p μ} :
    f ∈ classFunctionLp 𝕜 E p μ ↔ ∀ c : (ConjAct G)ᵈᵐᵃ, c • f = f :=
  Iff.rfl

/-- **Membership of `classFunctionLp`, read on representatives.**  A class lies in
`classFunctionLp` exactly when each of its conjugates agrees with it almost everywhere. -/
theorem mem_classFunctionLp_iff_ae {f : Lp E p μ} :
    f ∈ classFunctionLp 𝕜 E p μ ↔ ∀ h : G, (fun g ↦ f (h * g * h⁻¹)) =ᵐ[μ] f := by
  constructor
  · intro hf h
    refine ((conjAct_smul_Lp_ae_eq h f).symm.trans ?_)
    rw [hf (DomMulAct.mk (ConjAct.toConjAct h))]
  · intro hf c
    obtain ⟨a, rfl⟩ := DomMulAct.mk.surjective c
    obtain ⟨h, rfl⟩ := ConjAct.toConjAct.surjective a
    exact Lp.ext ((conjAct_smul_Lp_ae_eq h f).trans (hf h))

section Topology

-- Only the statements in this section need `1 ≤ p`, for the norm topology on `Lp E p μ`;
-- membership of `classFunctionLp` is an algebraic condition, meaningful for every exponent.
variable [Fact (1 ≤ p)]

/-- **The class functions form a closed subspace.**  Each conjugation acts on `Lp` by an isometry,
so the set where it agrees with the identity is closed, and `classFunctionLp` is their
intersection. -/
theorem isClosed_classFunctionLp : IsClosed (classFunctionLp 𝕜 E p μ : Set (Lp E p μ)) := by
  have : (classFunctionLp 𝕜 E p μ : Set (Lp E p μ)) =
      ⋂ c : (ConjAct G)ᵈᵐᵃ, {f : Lp E p μ | c • f = f} := by
    ext f
    simp [classFunctionLp]
  rw [this]
  exact isClosed_iInter fun c ↦ isClosed_eq (continuous_const_smul c) continuous_id

/-- **The class functions are complete.**  A closed subspace of the complete space `Lp E p μ`.
Completeness is what makes the intended specialization `classFunctionLp ℂ ℂ 2 μ` a Hilbert space,
which is the setting in which the characters of a compact group are expected to form an
orthonormal basis. -/
instance instCompleteSpaceClassFunctionLp [CompleteSpace E] :
    CompleteSpace (classFunctionLp 𝕜 E p μ) :=
  (isClosed_classFunctionLp 𝕜).completeSpace_coe

end Topology

/-- **A genuinely invariant representative makes a class function.**  If some representative `F` of
`f` is constant on conjugacy classes on the nose, then `f` is a class function.  Only the
representative is
asked to be invariant pointwise: the null set on which `f` and `F` disagree pulls back along
conjugation to a null set, because conjugation preserves `μ`. -/
theorem mem_classFunctionLp_of_ae_eq_of_conj_invariant {f : Lp E p μ} {F : G → E} (hF : ⇑f =ᵐ[μ] F)
    (hFconj : ∀ g h : G, F (h * g * h⁻¹) = F g) : f ∈ classFunctionLp 𝕜 E p μ := by
  rw [mem_classFunctionLp_iff_ae]
  intro h
  have hconj := (measurePreserving_conj μ h).quasiMeasurePreserving.ae_eq_comp hF
  refine hconj.trans (Filter.EventuallyEq.trans ?_ hF.symm)
  exact Filter.Eventually.of_forall fun g ↦ hFconj g h

/-- A constant is a class function. -/
theorem const_mem_classFunctionLp [IsFiniteMeasure μ] (a : E) :
    Lp.const p μ a ∈ classFunctionLp 𝕜 E p μ :=
  fun c ↦ DomMulAct.smul_Lp_const c a

section Isometry

variable [Fact (1 ≤ p)]

/-- **Conjugation by a fixed element, as a linear isometric equivalence of `Lp E p μ`.**  It
agrees with the action of `(ConjAct G)ᵈᵐᵃ` (`TauCeti.compMeasurePreserving_conj_eq_smul`), is
represented by precomposition with conjugation (`TauCeti.coeFn_conjLpₗᵢ`), and its inverse is
conjugation by `h⁻¹`. For `p = 2`, the underlying linear isometry records inner-product
preservation through `LinearIsometry.inner_map_map`. -/
noncomputable def conjLpₗᵢ (h : G) : Lp E p μ ≃ₗᵢ[𝕜] Lp E p μ :=
  Lp.compMeasurePreservingₗᵢEquiv 𝕜 (measurePreserving_conj μ h)
    (measurePreserving_conj μ h⁻¹)
    (.of_eq (funext fun g ↦ by simp [mul_assoc]))

variable {𝕜}

/-- Conjugation as an isometric equivalence applies by `Lp.compMeasurePreserving`. -/
@[simp]
theorem conjLpₗᵢ_apply (h : G) (f : Lp E p μ) :
    conjLpₗᵢ 𝕜 h f = Lp.compMeasurePreserving (fun g ↦ h * g * h⁻¹)
      (measurePreserving_conj μ h) f :=
  Lp.compMeasurePreservingₗᵢEquiv_apply 𝕜 _ _ _ f

/-- The conjugation isometry is represented by `g ↦ f (h * g * h⁻¹)`. -/
theorem coeFn_conjLpₗᵢ (h : G) (f : Lp E p μ) : conjLpₗᵢ 𝕜 h f =ᵐ[μ] fun g ↦ f (h * g * h⁻¹) :=
  Lp.coeFn_compMeasurePreservingₗᵢEquiv 𝕜 (measurePreserving_conj μ h)
    (measurePreserving_conj μ h⁻¹) _ f

/-- The inverse of conjugation by `h` is conjugation by `h⁻¹`. -/
@[simp]
theorem conjLpₗᵢ_symm (h : G) :
    (conjLpₗᵢ (E := E) (p := p) (μ := μ) 𝕜 h).symm =
      conjLpₗᵢ (E := E) (p := p) (μ := μ) 𝕜 h⁻¹ := by
  refine LinearIsometryEquiv.ext fun f ↦ ?_
  rw [LinearIsometryEquiv.symm_apply_eq, conjLpₗᵢ_apply, conjLpₗᵢ_apply]
  exact (Lp.compMeasurePreserving_comp_apply_of_ae_id (E := E) (p := p)
    (measurePreserving_conj μ h⁻¹) (measurePreserving_conj μ h)
    (.of_eq (funext fun g ↦ by simp [mul_assoc])) f).symm

omit [Fact (1 ≤ p)] in
/-- **Precomposition by conjugation is the `(ConjAct G)ᵈᵐᵃ`-action.**  The two are the same
operation, so a statement proved for either transfers to the other; `classFunctionLp` is phrased
with the action, while `TauCeti.conjLpₗᵢ_apply` connects this statement to the bundled linear
isometry that gives inner-product preservation on `L²`. -/
@[simp]
theorem compMeasurePreserving_conj_eq_smul (h : G) (f : Lp E p μ) :
    Lp.compMeasurePreserving (fun g ↦ h * g * h⁻¹) (measurePreserving_conj μ h) f =
      DomMulAct.mk (ConjAct.toConjAct h) • f :=
  Lp.ext ((Lp.coeFn_compMeasurePreserving f (measurePreserving_conj μ h)).trans
    (conjAct_smul_Lp_ae_eq h f).symm)

/-- **A class function is fixed by every conjugation isometry.**  This is the definition of
`TauCeti.classFunctionLp`, read on the bundled operation. -/
theorem conjLpₗᵢ_apply_of_mem_classFunctionLp {f : Lp E p μ} (hf : f ∈ classFunctionLp 𝕜 E p μ)
    (h : G) : conjLpₗᵢ 𝕜 h f = f :=
  Lp.ext ((coeFn_conjLpₗᵢ h f).trans (mem_classFunctionLp_iff_ae 𝕜 |>.1 hf h))

end Isometry

/-- On a commutative group every element of `Lp` is a class function: conjugation is trivial. -/
theorem classFunctionLp_eq_top_of_commGroup {G : Type*} [CommGroup G] [MeasurableSpace G]
    [MeasurableMul G] {μ : Measure G} [SMulInvariantMeasure (ConjAct G) G μ] :
    classFunctionLp 𝕜 E p μ = ⊤ := by
  refine eq_top_iff.2 fun f _ ↦ ?_
  rw [mem_classFunctionLp_iff_ae]
  intro h
  refine Filter.Eventually.of_forall fun g ↦ ?_
  simp [mul_comm h g, mul_assoc]

end TauCeti
