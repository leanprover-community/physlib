/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jinzheng Li, Nathaneal Sajan, Joseph Tooby-Smith
-/
module

public import PhyslibAlpha.ClassicalFieldTheory.GaugeTheory.MatterField.Prod
/-!
# The direct sum of a finite family of matter fields

A finite family of matter fields of one mass weight and statistics as a single matter field.

## i. Overview

`prod` sums two matter fields of the same mass weight and statistics. This file
does the same for a finite family `M : ι → G.MatterField`, producing a single matter
field valued in `∀ i, (M i).V`. It is the operation that turns the several species of a
theory into one field. The fifteen fermionic multiplets of the Standard Model become one
fermion field, carried by `GaugeFieldData.fermionMatterField`.

The binary and indexed versions are the same construction with `LinearMap.prodMap`
replaced by `LinearMap.piMap` and `jetProdEquiv` by `jetPiEquiv`, so the proofs run in
parallel. The representation of the global gauge group is the componentwise one, built as
a continuous homomorphism into the units of the continuous linear maps of the product, and
the infinitesimal and jet gauge actions are derived from it. As in the binary case, the
direct sum is represented by one `MatterField`, which has one mass weight and one
statistic, so the summands must share both. The caller supplies the common values `w` and
`σ`, together with proofs that every summand has them, so the direct sum of an empty family
also has a definite weight and statistics.

Finiteness of `ι` is essential and not merely convenient. `jetPiEquiv`, the
identification of the jets of the product with the product of the jets through which the
jet gauge action is defined, exists only for a finite index type, and finite dimensionality
of the value space would fail for an infinite family in any case.

## ii. Key results

- `repPiUnits` : the componentwise representation of the global gauge group.
- `pi` : the direct sum of a finite family of matter fields of one mass weight and one
  statistic.
- `lieAlgebraRep_pi` : the Lie algebra acts on the direct sum index by index.
- `pi_repAlgebra` and `pi_repJet` : the derived infinitesimal and jet gauge actions are the
  index-by-index ones, `repAlgebraPi` and `repJetPi`.
- `repJetPi_smul` : the jet action is fibrewise, as each summand is.
- `lTensor_proj_repJetPi` : the projection onto a summand intertwines it with that summand's
  own action.
- `repCoeff_repJetPi` : its base-point Taylor coefficients are the family of those of the
  summands.
- `fieldDerivSpacePiEquiv` : the component space of the direct sum is the family of the
  component spaces of the summands.
- `fieldDerivSpacePiEquiv_symm_single` : a summand sits inside it as the pullback along
  the projection onto that summand.

## iii. Table of contents

- A. The direct sum of a finite family of matter fields
- B. Diagonal maps of an indexed product
- C. The index-by-index gauge actions
- D. The derived actions of the direct sum
- E. The component space of the direct sum

## iv. References

* None.

-/

@[expose] public section

open Matrix MatrixGroups TensorProduct

namespace GlobalGaugeGroup.MatterField

variable {κ : Type} [Fintype κ] [DecidableEq κ] {G : GlobalGaugeGroup κ}

/-!

## A. The direct sum of a finite family of matter fields

The direct sum acts index by index, so its representation of the global gauge group is the
componentwise one, built as a continuous homomorphism into the units of the continuous linear
maps of the product.

-/

section Pi

variable {ι : Type} [Fintype ι] [DecidableEq ι] (M : ι → G.MatterField)

/-- The product of a family of representations, acting index by index. This is the
  indexed analogue of `Representation.prod`, which Mathlib provides only in the binary
  case. -/
noncomputable def repPi {W : ι → Type} [∀ i, AddCommGroup (W i)]
    [∀ i, Module ℂ (W i)] {H : Type} [Group H] (ρ : ∀ i, Representation ℂ H (W i)) :
    Representation ℂ H (∀ i, W i) where
  toFun U := LinearMap.piMap fun i => ρ i U
  map_one' := by
    refine LinearMap.ext fun x => funext fun i => ?_
    rw [show LinearMap.piMap (fun i => ρ i 1) x i = ρ i 1 (x i) from rfl, map_one]
    rfl
  map_mul' U W := by
    refine LinearMap.ext fun x => funext fun i => ?_
    rw [show LinearMap.piMap (fun i => ρ i (U * W)) x i = ρ i (U * W) (x i) from rfl,
      map_mul]
    rfl

/-- The family of continuous linear maps `f i` as the continuous linear map of the product acting
  index by index, a ring homomorphism. -/
noncomputable def piMapRingHom :
    (∀ i, (M i).V →L[ℂ] (M i).V) →+* ((∀ i, (M i).V) →L[ℂ] (∀ i, (M i).V)) where
  toFun f := ContinuousLinearMap.pi fun i => (f i).comp (ContinuousLinearMap.proj i)
  map_one' := ContinuousLinearMap.ext fun _ => rfl
  map_mul' _ _ := ContinuousLinearMap.ext fun _ => rfl
  map_zero' := ContinuousLinearMap.ext fun _ => rfl
  map_add' _ _ := ContinuousLinearMap.ext fun _ => rfl

omit [Fintype ι] [DecidableEq ι] in
@[simp]
lemma piMapRingHom_apply (f : ∀ i, (M i).V →L[ℂ] (M i).V) (v : ∀ i, (M i).V) (i : ι) :
    piMapRingHom M f v i = f i (v i) := rfl

omit [DecidableEq ι] in
lemma continuous_piMapRingHom : Continuous (piMapRingHom M) := by
  let L : (∀ i, (M i).V →L[ℂ] (M i).V) →ₗ[ℂ]
      ((∀ i, (M i).V) →L[ℂ] (∀ i, (M i).V)) :=
    { toFun := piMapRingHom M
      map_add' := map_add _
      map_smul' := fun _ _ => ContinuousLinearMap.ext fun _ => rfl }
  have : ∀ i, FiniteDimensional ℂ ((M i).V →L[ℂ] (M i).V) := fun i =>
    LinearEquiv.finiteDimensional
      (LinearMap.toContinuousLinearMap (𝕜 := ℂ) (E := (M i).V) (F' := (M i).V))
  exact LinearMap.continuous_of_finiteDimensional L

/-- The direct sum `g ↦ (ρ_{M i}(g))ᵢ` of the representations of a family of matrix matter
  fields. -/
noncomputable def repPiUnits : G.group →ₜ* ((∀ i, (M i).V) →L[ℂ] (∀ i, (M i).V))ˣ where
  toMonoidHom := (Units.map (piMapRingHom M).toMonoidHom).comp
    (MulEquiv.piUnits.symm.toMonoidHom.comp (MonoidHom.pi fun i => (M i).rep.toMonoidHom))
  continuous_toFun := Units.continuous_iff.2
    ⟨(continuous_piMapRingHom M).comp
        (continuous_pi fun i => Units.continuous_val.comp (M i).rep.continuous),
      (continuous_piMapRingHom M).comp
        (continuous_pi fun i => Units.continuous_coe_inv.comp (M i).rep.continuous)⟩

omit [DecidableEq ι] in
@[simp]
lemma repPiUnits_apply (g : G.group) :
    ((repPiUnits M g : ((∀ i, (M i).V) →L[ℂ] (∀ i, (M i).V))ˣ) :
        (∀ i, (M i).V) →L[ℂ] (∀ i, (M i).V)) =
      piMapRingHom M fun i => ((M i).rep g : (M i).V →L[ℂ] (M i).V) := rfl

/-- The direct sum of a finite family of matter fields with common mass weight `w` and
  common statistics `σ`, given with proofs that every summand has them. It is one field
  valued in `∀ i, (M i).V`, of weight `w` and statistics `σ`, with every action acting index
  by index. -/
noncomputable def pi (w : ℕ) (_h : ∀ i, (M i).massWeight = w) (σ : FieldStatistic)
    (_hσ : ∀ i, (M i).statistic = σ) : G.MatterField where
  V := ∀ i, (M i).V
  rep := repPiUnits M
  repLorentz := repPi fun i => (M i).repLorentz
  massWeight := w
  statistic := σ

variable (w : ℕ) (h : ∀ i, (M i).massWeight = w) (σ : FieldStatistic)
  (hσ : ∀ i, (M i).statistic = σ)

omit [DecidableEq ι] in
@[simp]
lemma pi_repLorentz : (pi M w h σ hσ).repLorentz = repPi fun i => (M i).repLorentz := rfl

omit [DecidableEq ι] in
@[simp]
lemma pi_massWeight : (pi M w h σ hσ).massWeight = w := rfl

omit [DecidableEq ι] in
@[simp]
lemma pi_statistic : (pi M w h σ hσ).statistic = σ := rfl

end Pi

/-!

## B. Diagonal maps of an indexed product

Every piece of data of the direct sum acts index by index, that is through
`LinearMap.piMap`. The four facts about that construction used below — that it is
additive, negative-preserving and multiset-sum-preserving in the family, and that it
composes index by index — all hold because `piMap` is evaluated pointwise, so each is a
single `LinearMap.ext`.

-/

section Diagonal

variable {ι : Type} {W : ι → Type} [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]

private lemma piMap_add_piMap (f g : ∀ i, W i →ₗ[ℂ] W i) :
    LinearMap.piMap (fun i => f i + g i) = LinearMap.piMap f + LinearMap.piMap g :=
  LinearMap.ext fun _ => rfl

private lemma piMap_neg (f : ∀ i, W i →ₗ[ℂ] W i) :
    LinearMap.piMap (fun i => -f i) = -LinearMap.piMap f :=
  LinearMap.ext fun _ => rfl

private lemma piMap_comp (f g : ∀ i, W i →ₗ[ℂ] W i) :
    (LinearMap.piMap f).comp (LinearMap.piMap g)
      = LinearMap.piMap fun i => (f i).comp (g i) :=
  LinearMap.ext fun _ => rfl

private lemma piMap_multiset_sum {κ : Type} (S : Multiset κ)
    (f : κ → ∀ i, W i →ₗ[ℂ] W i) :
    LinearMap.piMap (fun i => (S.map fun k => f k i).sum)
      = (S.map fun k => LinearMap.piMap (f k)).sum := by
  induction S using Multiset.induction_on with
  | empty => exact LinearMap.ext fun _ => rfl
  | cons k S ih =>
      rw [show (fun i => ((k ::ₘ S).map fun k => f k i).sum)
          = fun i => f k i + (S.map fun k => f k i).sum from
        funext fun i => by rw [Multiset.map_cons, Multiset.sum_cons],
        piMap_add_piMap, ih, Multiset.map_cons, Multiset.sum_cons]

end Diagonal


/-!

## C. The index-by-index gauge actions

The jet gauge action and the infinitesimal gauge action of the direct sum are the families of
those of the summands, and the second generates the first.

-/

section Pi

variable {ι : Type} [Fintype ι] [DecidableEq ι] (M : ι → G.MatterField)

/-- The jet gauge action of an indexed direct sum, the family of actions read
  through the identification of the jets of `∀ i, (M i).V` with the family of jets. -/
noncomputable def repJetPi :
    Representation ℂ G.gaugeJetGroup (SpaceTimeAlgebra ⊗[ℂ] (∀ i, (M i).V)) where
  toFun U := LinearEquiv.conjRingEquiv (jetPiEquiv fun i => (M i).V).symm
    (repPi (fun i => (M i).repJet) U)
  map_one' := by rw [map_one, map_one]
  map_mul' U W := by rw [map_mul, map_mul]

lemma repJetPi_apply (U : G.gaugeJetGroup) (z : SpaceTimeAlgebra ⊗[ℂ] (∀ i, (M i).V)) :
    repJetPi M U z = (jetPiEquiv fun i => (M i).V).symm
      (fun i => (M i).repJet U (jetPiEquiv (fun i => (M i).V) z i)) := rfl

/-- The jet gauge action of an indexed direct sum is fibrewise. It acts index by
  index, and each summand is fibrewise, so multiplication by a scalar jet passes through
  the splitting untouched. This is the statement `repJet_smul` for `pi`, stated
  separately so that it can be used without fixing a common mass weight. -/
lemma repJetPi_smul (U : G.gaugeJetGroup) (χ : SpaceTimeAlgebra)
    (z : SpaceTimeAlgebra ⊗[ℂ] (∀ i, (M i).V)) :
    repJetPi M U (χ • z) = χ • repJetPi M U z := by
  rw [repJetPi_apply, repJetPi_apply,
    show (fun i => (M i).repJet U (jetPiEquiv (fun i => (M i).V) (χ • z) i))
        = fun i => χ • (M i).repJet U (jetPiEquiv (fun i => (M i).V) z i) from
      funext fun i => by rw [jetPiEquiv_smul, (M i).repJet_smul],
    jetPiEquiv_symm_smul]

/-- A summand is a subrepresentation of the jet gauge action of the direct sum. The
  projection onto the value space of one summand, applied to the jets, intertwines the
  summed action with that summand's own, since the summed action is the family of the actions,
  and reading off a summand of the jets is the projection on the value factor. -/
lemma lTensor_proj_repJetPi (i : ι) (U : G.gaugeJetGroup) :
    (LinearMap.lTensor SpaceTimeAlgebra (LinearMap.proj i)).comp (repJetPi M U)
      = ((M i).repJet U).comp (LinearMap.lTensor SpaceTimeAlgebra (LinearMap.proj i)) := by
  refine LinearMap.ext fun z => ?_
  rw [LinearMap.comp_apply, LinearMap.comp_apply, ← jetPiEquiv_eq_lTensor_proj,
    ← jetPiEquiv_eq_lTensor_proj, repJetPi_apply, LinearEquiv.apply_symm_apply]

/-- The infinitesimal action of an indexed direct sum, the family of actions, one on
  each summand. -/
noncomputable def repAlgebraPi :
    G.lieSubalgebra →ₗ[ℝ] (∀ i, (M i).V) →ₗ[ℂ] (∀ i, (M i).V) where
  toFun c := LinearMap.piMap fun i => (M i).repAlgebra c
  map_add' c₁ c₂ := by
    rw [show (fun i => (M i).repAlgebra (c₁ + c₂))
        = fun i => (M i).repAlgebra c₁ + (M i).repAlgebra c₂ from
      funext fun i => map_add _ _ _, piMap_add_piMap]
  map_smul' r c := by
    rw [show (fun i => (M i).repAlgebra (r • c)) = fun i => r • (M i).repAlgebra c from
      funext fun i => map_smul _ _ _, RingHom.id_apply]
    exact LinearMap.ext fun _ => rfl

omit [Fintype ι] [DecidableEq ι] in
@[simp]
lemma repAlgebraPi_apply (c : G.lieSubalgebra) :
    repAlgebraPi M c = LinearMap.piMap fun i => (M i).repAlgebra c := rfl

/-- The base-point Taylor coefficients of the summed jet action are the family of the
  coefficients of the summands, since `jetOfConstant`, `jetIteratedDeriv` and `jetEval` all act
  index by index through `jetPiEquiv`. -/
lemma repCoeff_repJetPi (U : G.gaugeJetGroup) (x : Multiset (Fin 1 ⊕ Fin 3)) :
    GlobalGaugeGroup.repCoeff (repJetPi M) U x =
      LinearMap.piMap fun i => GlobalGaugeGroup.repCoeff (M i).repJet U x := by
  refine LinearMap.ext fun p => funext fun i => ?_
  show jetEval (jetIteratedDeriv x (repJetPi M U (jetOfConstant p))) i = _
  rw [jetEval_pi, jetPiEquiv_jetIteratedDeriv,
    show jetPiEquiv (fun i => (M i).V) (repJetPi M U (jetOfConstant p)) i
        = (M i).repJet U (jetOfConstant (p i)) from by
      rw [repJetPi_apply, LinearEquiv.apply_symm_apply]
      rfl]
  rfl

/-- The index-by-index algebra action generates the index-by-index jet action. Both
  laws of `IsInfinitesimalActionOf` are the corresponding laws of the summands, read
  through `repCoeff_repJetPi`, since `piMap` is additive in the family and composes index
  by index. -/
lemma isInfinitesimalActionOf_repAlgebraPi :
    G.IsInfinitesimalActionOf (repAlgebraPi M) (repJetPi M) where
  repCoeff_cons U μ x := by
    rw [repCoeff_repJetPi,
      show (fun i => GlobalGaugeGroup.repCoeff (M i).repJet U (μ ::ₘ x))
          = fun i => -((x.antidiagonal.map fun p =>
            (M i).repAlgebra (G.evalLie (G.iteratedDerivJ p.1
                (-G.maurerCartan U μ))) ∘ₗ
              GlobalGaugeGroup.repCoeff (M i).repJet U p.2).sum) from
        funext fun i => (M i).isInfinitesimalActionOf.repCoeff_cons U μ x,
      piMap_neg, piMap_multiset_sum]
    refine congrArg Neg.neg (congrArg Multiset.sum (Multiset.map_congr rfl fun p _ => ?_))
    rw [repCoeff_repJetPi, repAlgebraPi_apply, piMap_comp]
  repCoeff_act U x c := by
    rw [repCoeff_repJetPi, repAlgebraPi_apply, piMap_comp,
      show (fun i => (GlobalGaugeGroup.repCoeff (M i).repJet U x).comp
            ((M i).repAlgebra c))
          = fun i => ((x.antidiagonal.map fun p =>
            (M i).repAlgebra (G.adjointCoeff U p.1 c) ∘ₗ
              GlobalGaugeGroup.repCoeff (M i).repJet U p.2).sum) from
        funext fun i => (M i).isInfinitesimalActionOf.repCoeff_act U x c,
      piMap_multiset_sum]
    refine congrArg Multiset.sum (Multiset.map_congr rfl fun p _ => ?_)
    rw [repCoeff_repJetPi, repAlgebraPi_apply, piMap_comp]

/-!

## D. The derived actions of the direct sum

The infinitesimal and jet gauge actions that the direct sum inherits from its representation
are the index-by-index ones.

-/

variable (w : ℕ) (h : ∀ i, (M i).massWeight = w) (σ : FieldStatistic)
  (hσ : ∀ i, (M i).statistic = σ)

omit [DecidableEq ι] in
/-- The Lie algebra acts on a direct sum index by index. -/
lemma lieAlgebraRep_pi (X : G.lieSubalgebra) :
    lieAlgebraRep (pi M w h σ hσ) X = piMapRingHom M fun i => lieAlgebraRep (M i) X := by
  let _ : ∀ i, NormedAlgebra ℚ ((M i).V →L[ℂ] (M i).V) := fun i =>
    .restrictScalars ℚ ℝ _
  let _ : NormedAlgebra ℚ ((∀ i, (M i).V) →L[ℂ] (∀ i, (M i).V)) :=
    .restrictScalars ℚ ℝ _
  refine lieAlgebraRep_eq_of _ fun t g hg => ?_
  change piMapRingHom M (fun i => (((M i).rep g : ((M i).V →L[ℂ] (M i).V)ˣ) :
    (M i).V →L[ℂ] (M i).V)) = _
  have hexp : (fun i => NormedSpace.exp (t • lieAlgebraRep (M i) X)) =
      NormedSpace.exp (fun i => t • lieAlgebraRep (M i) X) := by
    rw [Pi.exp_def]
  rw [show (fun i => (((M i).rep g : ((M i).V →L[ℂ] (M i).V)ˣ) : (M i).V →L[ℂ] (M i).V)) =
      fun i => NormedSpace.exp (t • lieAlgebraRep (M i) X) from
    funext fun i => rep_eq_exp_lieAlgebraRep (M i) hg, hexp,
    NormedSpace.map_exp (piMapRingHom M) (continuous_piMapRingHom M)]
  rfl

omit [DecidableEq ι] in
/-- The Lie algebra of a direct sum acts index by index. -/
@[simp]
lemma pi_repAlgebra : (pi M w h σ hσ).repAlgebra = repAlgebraPi M :=
  LinearMap.ext fun c => by
    rw [repAlgebra_apply, lieAlgebraRep_pi]
    rfl

/-- The gauge jets act on a direct sum index by index. -/
@[simp]
lemma pi_repJet : (pi M w h σ hσ).repJet = repJetPi M := by
  have hI := (pi M w h σ hσ).isInfinitesimalActionOf
  rw [pi_repAlgebra] at hI
  refine hI.eq_of_repCoeff_zero (isInfinitesimalActionOf_repAlgebraPi M)
    (pi M w h σ hσ).repJet_smul (repJetPi_smul M) fun U => ?_
  refine Eq.trans ?_ (repCoeff_repJetPi M U 0).symm
  rw [repCoeff_repJet, repCoeff_zero]
  refine LinearMap.ext fun p => funext fun i => ?_
  show _ = GlobalGaugeGroup.repCoeff (M i).repJet U 0 (p i)
  rw [repCoeff_repJet, repCoeff_zero]
  rfl

/-!

## E. The component space of the direct sum

The direct sum was built so that the several species of a theory can be treated as one
field. Nothing is lost in doing so at the level of component functions either: the
symbols `∂_s ψ_α` and `∂_s ψ̄_α` of the summed field are exactly the families, over the
index, of the symbols of the summands. This is the component-space image of the
identification `jetPiEquiv` that defines the summed jet action, and it is the finite
direct sum case of `FieldDerivSpace.piEquiv`.

-/

/-- The component space of a direct sum of matter fields splits. A component function
  of `pi M w h σ hσ` is exactly a family, one component function per summand. Both
  halves split by `FieldDerivSpace.fstPiEquiv` and `FieldDerivSpace.sndPiEquiv`, and
  the pair of families is reassembled into a family of pairs index by index. -/
noncomputable def fieldDerivSpacePiEquiv :
    FieldDerivSpace (pi M w h σ hσ) ≃ₗ[ℂ] ∀ i, FieldDerivSpace (M i) :=
  (LinearEquiv.prodCongr (FieldDerivSpace.fstPiEquiv fun i => (M i).V)
      (FieldDerivSpace.sndPiEquiv fun i => (M i).V)).trans prodPiEquiv

/-- The summand of one species is the pullback along the projection onto it. A
  component function of the summand `i`, placed in the family and read back as a component
  function of the direct sum, is that function precomposed with the projection onto the
  summand. This is what identifies the splitting with the species inclusions of a direct
  sum of component spaces. -/
lemma fieldDerivSpacePiEquiv_symm_single (i : ι) (x : FieldDerivSpace (M i)) :
    (fieldDerivSpacePiEquiv M w h σ hσ).symm (Pi.single i x)
      = FieldDerivSpace.comap
        (LinearMap.proj (φ := fun i => (M i).V) i :
          (pi M w h σ hσ).V →ₗ[ℂ] (M i).V) x := by
  have hfst : (fun j => ((Pi.single i x : ∀ j, FieldDerivSpace (M j)) j).1)
      = Pi.single i x.1 :=
    funext fun j =>
      Pi.apply_single (fun j (p : FieldDerivSpace (M j)) => p.1) (fun _ => rfl) i x j
  have hsnd : (fun j => ((Pi.single i x : ∀ j, FieldDerivSpace (M j)) j).2)
      = Pi.single i x.2 :=
    funext fun j =>
      Pi.apply_single (fun j (p : FieldDerivSpace (M j)) => p.2) (fun _ => rfl) i x j
  show ((FieldDerivSpace.fstPiEquiv (fun i => (M i).V)).symm
        (fun j => ((Pi.single i x : ∀ j, FieldDerivSpace (M j)) j).1),
      (FieldDerivSpace.sndPiEquiv (fun i => (M i).V)).symm
        (fun j => ((Pi.single i x : ∀ j, FieldDerivSpace (M j)) j).2)) = _
  rw [hfst, hsnd, FieldDerivSpace.fstPiEquiv_symm_single,
    FieldDerivSpace.sndPiEquiv_symm_single]
  rfl

end Pi

end GlobalGaugeGroup.MatterField
