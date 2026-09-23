/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.ClassicalFieldTheory.GaugeTheory.MatterField.Prod
/-!
# The direct sum of a finite family of matter fields

## i. Overview

`MatterField.prod` sums two matter fields of the same mass weight. This file does the same
for a finite family `M : ι → MatterField jets`, producing a single matter field valued in
`∀ i, (M i).V`. It is the operation that turns the several species of a theory into one
field: the fifteen fermionic multiplets of the Standard Model become one fermion field,
carried by `GaugeFieldData.fermionMatterField`.

The binary and indexed versions are the same construction with `LinearMap.prodMap`
replaced by `LinearMap.piMap` and `jetProdEquiv` by `jetPiEquiv`, so the proofs run in
parallel; only the diagonal-map algebra used along the way differs. As in the binary case
the mass weight has to be shared, and is taken as a hypothesis: a `MatterField` carries
one weight, which is what makes the mass-weight grading of its field algebra well defined.

Finiteness of `ι` is essential and not merely convenient. `jetPiEquiv` — the
identification of the jets of the product with the product of the jets, through which the
jet gauge action is defined — exists only for a finite index type, and finiteness of the
value space, a field of `MatterField`, would fail for an infinite family in any case.

## ii. Key results

- `MatterField.repJetPi` : the jet gauge action of an indexed direct sum.
- `MatterField.repJetPi_smul` : it is fibrewise, as each summand is.
- `MatterField.lTensor_proj_repJetPi` : the projection onto a summand intertwines it with
  that summand's own action.
- `MatterField.repAlgebraPi` : the infinitesimal gauge action of an indexed direct sum.
- `MatterField.repCoeff_repJetPi` : its base-point Taylor coefficients are the family of
  those of the summands.
- `MatterField.pi` : the direct sum of a finite family of matter fields of one mass
  weight.
- `MatterField.jetComponentSpacePiEquiv` : the component space of the direct sum is the
  family of the component spaces of the summands.
- `MatterField.jetComponentSpacePiEquiv_symm_single` : a summand sits inside it as the
  pullback along the projection onto that summand.

## iii. Table of contents

- A. Diagonal maps of an indexed product
- B. The direct sum of a finite family of matter fields
- C. The component space of the direct sum

-/

@[expose] public section

open Matrix MatrixGroups TensorProduct

namespace MatterField

variable {G₀ : Type} [Group G₀] {𝔤 : Type} [LieRing 𝔤] [LieAlgebra ℝ 𝔤]
  {GJ : Type} [Group GJ] {𝔤J : Type} [LieRing 𝔤J] [LieAlgebra ℝ 𝔤J]
  {jets : LocalGaugeData G₀ 𝔤 GJ 𝔤J}

/-!

## A. Diagonal maps of an indexed product

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

## B. The direct sum of a finite family of matter fields

-/

section Pi

variable {ι : Type} [Fintype ι] [DecidableEq ι] (M : ι → MatterField jets)

/-- The product of a family of representations, acting index by index. This is the
  indexed analogue of `Representation.prod`, which Mathlib provides only in the binary
  case. -/
noncomputable def repPi {W : ι → Type} [∀ i, AddCommGroup (W i)]
    [∀ i, Module ℂ (W i)] (ρ : ∀ i, Representation ℂ GJ (W i)) :
    Representation ℂ GJ (∀ i, W i) where
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

/-- **The jet gauge action of an indexed direct sum**: the family of actions, read
  through the identification of the jets of `∀ i, (M i).V` with the family of jets. -/
noncomputable def repJetPi : Representation ℂ GJ (JetRing ⊗[ℂ] (∀ i, (M i).V)) where
  toFun U := LinearEquiv.conjRingEquiv (jetPiEquiv fun i => (M i).V).symm
    (repPi (fun i => (M i).repJet) U)
  map_one' := by rw [map_one, map_one]
  map_mul' U W := by rw [map_mul, map_mul]

lemma repJetPi_apply (U : GJ) (z : JetRing ⊗[ℂ] (∀ i, (M i).V)) :
    repJetPi M U z = (jetPiEquiv fun i => (M i).V).symm
      (fun i => (M i).repJet U (jetPiEquiv (fun i => (M i).V) z i)) := rfl

/-- The jet gauge action of an indexed direct sum is fibrewise. It acts index by
  index, and each summand is fibrewise, so multiplication by a scalar jet passes through
  the splitting untouched. This is the field `repJet_smul` of `MatterField.pi`, stated
  separately so that it can be used without fixing a common mass weight. -/
lemma repJetPi_smul (U : GJ) (χ : JetRing) (z : JetRing ⊗[ℂ] (∀ i, (M i).V)) :
    repJetPi M U (χ • z) = χ • repJetPi M U z := by
  rw [repJetPi_apply, repJetPi_apply,
    show (fun i => (M i).repJet U (jetPiEquiv (fun i => (M i).V) (χ • z) i))
        = fun i => χ • (M i).repJet U (jetPiEquiv (fun i => (M i).V) z i) from
      funext fun i => by rw [jetPiEquiv_smul, (M i).repJet_smul],
    jetPiEquiv_symm_smul]

/-- A summand is a subrepresentation of the jet gauge action of the direct sum. The
  projection onto the value space of one summand, applied to the jets, intertwines the
  summed action with that summand's own: the summed action is the family of the actions,
  and reading off a summand of the jets is the projection on the value factor. -/
lemma lTensor_proj_repJetPi (i : ι) (U : GJ) :
    (LinearMap.lTensor JetRing (LinearMap.proj i)).comp (repJetPi M U)
      = ((M i).repJet U).comp (LinearMap.lTensor JetRing (LinearMap.proj i)) := by
  refine LinearMap.ext fun z => ?_
  rw [LinearMap.comp_apply, LinearMap.comp_apply, ← jetPiEquiv_eq_lTensor_proj,
    ← jetPiEquiv_eq_lTensor_proj, repJetPi_apply, LinearEquiv.apply_symm_apply]

/-- **The infinitesimal action of an indexed direct sum**: the family of actions, one on
  each summand. -/
noncomputable def repAlgebraPi : 𝔤 →ₗ[ℝ] (∀ i, (M i).V) →ₗ[ℂ] (∀ i, (M i).V) where
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
lemma repAlgebraPi_apply (c : 𝔤) :
    repAlgebraPi M c = LinearMap.piMap fun i => (M i).repAlgebra c := rfl

/-- The base-point Taylor coefficients of the summed jet action are the family of the
  coefficients of the summands: `jetOfConstant`, `jetIteratedDeriv` and `jetEval` all act
  index by index through `jetPiEquiv`. -/
lemma repCoeff_repJetPi (U : GJ) (x : Multiset (Fin 1 ⊕ Fin 3)) :
    GaugeAlgebraRealization.repCoeff (repJetPi M) U x =
      LinearMap.piMap fun i => GaugeAlgebraRealization.repCoeff (M i).repJet U x := by
  refine LinearMap.ext fun p => funext fun i => ?_
  show jetEval (jetIteratedDeriv x (repJetPi M U (jetOfConstant p))) i = _
  rw [jetEval_pi, jetPiEquiv_jetIteratedDeriv,
    show jetPiEquiv (fun i => (M i).V) (repJetPi M U (jetOfConstant p)) i
        = (M i).repJet U (jetOfConstant (p i)) from by
      rw [repJetPi_apply, LinearEquiv.apply_symm_apply]
      rfl]
  rfl

/-- **The index-by-index algebra action generates the index-by-index jet action**: both
  laws of `IsInfinitesimalActionOf` are the corresponding laws of the summands, read
  through `repCoeff_repJetPi`, since `piMap` is additive in the family and composes index
  by index. -/
lemma isInfinitesimalActionOf_repAlgebraPi :
    jets.IsInfinitesimalActionOf (repAlgebraPi M) (repJetPi M) where
  repCoeff_cons U μ x := by
    rw [repCoeff_repJetPi,
      show (fun i => GaugeAlgebraRealization.repCoeff (M i).repJet U (μ ::ₘ x))
          = fun i => -((x.antidiagonal.map fun p =>
            (M i).repAlgebra (jets.evalLie (jets.iteratedDeriv p.1
                (jets.maurerCartan U μ))) ∘ₗ
              GaugeAlgebraRealization.repCoeff (M i).repJet U p.2).sum) from
        funext fun i => (M i).repAlgebra_isInfinitesimalAction.repCoeff_cons U μ x,
      piMap_neg, piMap_multiset_sum]
    refine congrArg Neg.neg (congrArg Multiset.sum (Multiset.map_congr rfl fun p _ => ?_))
    rw [repCoeff_repJetPi, repAlgebraPi_apply, piMap_comp]
  repCoeff_act U x c := by
    rw [repCoeff_repJetPi, repAlgebraPi_apply, piMap_comp,
      show (fun i => (GaugeAlgebraRealization.repCoeff (M i).repJet U x).comp
            ((M i).repAlgebra c))
          = fun i => ((x.antidiagonal.map fun p =>
            (M i).repAlgebra (jets.adjointCoeff U p.1 c) ∘ₗ
              GaugeAlgebraRealization.repCoeff (M i).repJet U p.2).sum) from
        funext fun i => (M i).repAlgebra_isInfinitesimalAction.repCoeff_act U x c,
      piMap_multiset_sum]
    refine congrArg Multiset.sum (Multiset.map_congr rfl fun p _ => ?_)
    rw [repCoeff_repJetPi, repAlgebraPi_apply, piMap_comp]

/-- **The direct sum of a finite family of matter fields** sharing one mass weight `w`:
  one field valued in `∀ i, (M i).V`, with every action acting index by index. The shared
  weight is a hypothesis for the same reason as in the binary case — a `MatterField`
  carries a single weight — and here it says that the whole family is degenerate in mass
  dimension, as the fermions of a gauge theory are. -/
noncomputable def pi (w : ℕ) (_h : ∀ i, (M i).massWeight = w) : MatterField jets where
  V := ∀ i, (M i).V
  repLorentz := repPi fun i => (M i).repLorentz
  repJet := repJetPi M
  repAlgebra := repAlgebraPi M
  repJet_smul := repJetPi_smul M
  repAlgebra_isInfinitesimalAction := isInfinitesimalActionOf_repAlgebraPi M
  massWeight := w

lemma pi_V (w : ℕ) (h : ∀ i, (M i).massWeight = w) : (pi M w h).V = ∀ i, (M i).V := rfl

@[simp]
lemma pi_repJet (w : ℕ) (h : ∀ i, (M i).massWeight = w) :
    (pi M w h).repJet = repJetPi M := rfl

@[simp]
lemma pi_repAlgebra (w : ℕ) (h : ∀ i, (M i).massWeight = w) :
    (pi M w h).repAlgebra = repAlgebraPi M := rfl

@[simp]
lemma pi_massWeight (w : ℕ) (h : ∀ i, (M i).massWeight = w) :
    (pi M w h).massWeight = w := rfl

/-- The Lorentz action of the direct sum is the family of Lorentz actions, acting index by
  index. -/
lemma pi_repLorentz_apply (w : ℕ) (h : ∀ i, (M i).massWeight = w) (Λ : SL(2,ℂ))
    (v : ∀ i, (M i).V) (i : ι) :
    (pi M w h).repLorentz Λ v i = (M i).repLorentz Λ (v i) := rfl

/-!

## C. The component space of the direct sum

The direct sum was built so that the several species of a theory can be treated as one
field. Nothing is lost in doing so at the level of component functions either: the
symbols `∂_s ψ_α` and `∂_s ψ̄_α` of the summed field are exactly the families, over the
index, of the symbols of the summands. This is the component-space image of the
identification `jetPiEquiv` that defines the summed jet action, and it is the finite
direct sum case of `JetComponentSpace.piEquiv`.

-/

/-- **The component space of a direct sum of matter fields splits.** A component function
  of `MatterField.pi M w h` is exactly a family, one component function per summand. Both
  halves split by `JetComponentSpace.fstPiEquiv` and `JetComponentSpace.sndPiEquiv`, and
  the pair of families is reassembled into a family of pairs index by index. -/
noncomputable def jetComponentSpacePiEquiv (w : ℕ) (h : ∀ i, (M i).massWeight = w) :
    JetComponentSpace (pi M w h) ≃ₗ[ℂ] ∀ i, JetComponentSpace (M i) :=
  (LinearEquiv.prodCongr (JetComponentSpace.fstPiEquiv fun i => (M i).V)
      (JetComponentSpace.sndPiEquiv fun i => (M i).V)).trans prodPiEquiv

lemma jetComponentSpacePiEquiv_apply (w : ℕ) (h : ∀ i, (M i).massWeight = w)
    (x : JetComponentSpace (pi M w h)) (i : ι) :
    jetComponentSpacePiEquiv M w h x i =
      (JetComponentSpace.fstPiEquiv (fun i => (M i).V) x.1 i,
        JetComponentSpace.sndPiEquiv (fun i => (M i).V) x.2 i) := rfl

/-- **The summand of one species is the pullback along the projection onto it.** A
  component function of the summand `i`, placed in the family and read back as a component
  function of the direct sum, is that function precomposed with the projection onto the
  summand. This is what identifies the splitting with the species inclusions of a direct
  sum of component spaces. -/
lemma jetComponentSpacePiEquiv_symm_single (w : ℕ) (h : ∀ i, (M i).massWeight = w)
    (i : ι) (x : JetComponentSpace (M i)) :
    (jetComponentSpacePiEquiv M w h).symm (Pi.single i x)
      = JetComponentSpace.comap
        (LinearMap.proj (φ := fun i => (M i).V) i : (pi M w h).V →ₗ[ℂ] (M i).V) x := by
  have hfst : (fun j => ((Pi.single i x : ∀ j, JetComponentSpace (M j)) j).1)
      = Pi.single i x.1 :=
    funext fun j =>
      Pi.apply_single (fun j (p : JetComponentSpace (M j)) => p.1) (fun _ => rfl) i x j
  have hsnd : (fun j => ((Pi.single i x : ∀ j, JetComponentSpace (M j)) j).2)
      = Pi.single i x.2 :=
    funext fun j =>
      Pi.apply_single (fun j (p : JetComponentSpace (M j)) => p.2) (fun _ => rfl) i x j
  show ((JetComponentSpace.fstPiEquiv (fun i => (M i).V)).symm
        (fun j => ((Pi.single i x : ∀ j, JetComponentSpace (M j)) j).1),
      (JetComponentSpace.sndPiEquiv (fun i => (M i).V)).symm
        (fun j => ((Pi.single i x : ∀ j, JetComponentSpace (M j)) j).2)) = _
  rw [hfst, hsnd, JetComponentSpace.fstPiEquiv_symm_single,
    JetComponentSpace.sndPiEquiv_symm_single]
  rfl

end Pi

end MatterField
