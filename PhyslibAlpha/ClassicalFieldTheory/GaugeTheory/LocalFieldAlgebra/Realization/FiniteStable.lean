/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import PhyslibAlpha.ClassicalFieldTheory.GaugeTheory.LocalFieldAlgebra.LocalCovFieldAlgebra.Basic
public import PhyslibAlpha.Mathematics.RepresentationTheory.Reynolds.ContinuousFamily
public import PhyslibAlpha.ClassicalFieldTheory.GaugeTheory.LocalFieldAlgebra.Realization.Conditions
/-!

# Finite-dimensional stable subspaces of the covariant field algebra

Every covariant expression lies in a finite-dimensional subspace stable under the gauge and
Lorentz groups, on which both act continuously.

## i. Overview

The Haar average over the gauge group and the Casimir projection for the Lorentz group act on
finite-dimensional spaces with continuous actions. To use them on the covariant field algebra,
every covariant expression must lie in such a space. This file constructs one, stable under the
joint action of the ordinary gauge group and the Lorentz group.

Two conditions are needed. The Lorentz representation of every species must be continuous,
`GaugeFieldData.LorentzContinuous`, and the gauge and Lorentz representations of every species
must commute, `GaugeFieldData.GaugeLorentzCommute`. The second makes the two actions on the
covariant field algebra commute, so that together they form one representation
`repGaugeLorentz` of `G × SL(2,ℂ)`.

The construction is by generation, through the continuous families of
`PhyslibAlpha.Mathematics.RepresentationTheory.Reynolds.ContinuousFamily`. A finite family of
vectors is a continuous family when each group element maps every vector of the family to a
combination of the family with coefficients depending continuously on the group element. The
span of a continuous family for both groups is a finite-dimensional subrepresentation on which
both groups act continuously. Each covariant generator lies in such a span.

- The field strength `∇_l F_μν^φ` with `l` of fixed length, over a basis of the adjoint index
  `φ`. The gauge group acts on `φ` through the adjoint representation, and the Lorentz group
  mixes the directions and the two indices by the Lorentz matrix.
- The covariant tower `∇_l ψ^φ` of a species with `l` of fixed length, over a basis of the value
  index `φ`. The gauge group acts on `φ` through the gauge representation, and the Lorentz group
  mixes the directions by the Lorentz matrix and acts on `φ` through the Lorentz representation.
  The same holds for the conjugate towers.

The scalars span a continuous family, sums of elements lie in the span of the union of their
families, and products in the span of the products of their families, since both groups act by
algebra maps. So every element of the covariant field algebra lies in the span of a continuous
family.

## ii. Key results

- `GaugeFieldData.LocalCovFieldAlgebra.commute_repValue_repLorentzGroup` : the gauge and Lorentz
  actions on the covariant field algebra commute.
- `GaugeFieldData.LocalCovFieldAlgebra.repGaugeLorentz` : the joint action of `G × SL(2,ℂ)`.
- `GaugeFieldData.LocalCovFieldAlgebra.exists_subrepresentation` : every covariant expression
  lies in a finite-dimensional subrepresentation of the joint action on which both groups act
  with continuous matrix coefficients.
- `GaugeFieldData.LocalCovFieldAlgebra.finiteSubrep` : a chosen such subrepresentation.

## iii. Table of contents

- A. The actions on the value space of a matter field
  - A.1. Continuity
  - A.2. Commutation
- B. The joint action of the gauge and Lorentz groups
- C. Continuity on the covariant towers
  - C.1. The Lorentz matrix
  - C.2. The field-strength tower
  - C.3. The matter towers
- D. Finite-dimensional stable subspaces

## iv. References

* None.

-/

@[expose] public section

open Matrix MatrixGroups Lorentz
open GlobalGaugeGroup (repDualCoeff)


open Representation (ContinuousCoeff IsContinuousFamily HasContinuousSpan)

/-!

## A. The actions on the value space of a matter field

### A.1. Continuity

-/

namespace GlobalGaugeGroup.MatterField

variable {κ : Type} [Fintype κ] [DecidableEq κ] {G : GlobalGaugeGroup κ} (M : G.MatterField)

/-- A constant gauge jet acts on the dual of the value space through the gauge representation of
the inverse of its value. -/
lemma repDualCoeff_gaugeJetOfConstant_inv (g : G.group) :
    repDualCoeff M.repJet (G.gaugeJetOfConstant g)⁻¹ 0 =
      ((M.rep g⁻¹ : M.V →L[ℂ] M.V) : M.V →ₗ[ℂ] M.V).dualMap := by
  show (repCoeff M _ 0).dualMap = _
  rw [repCoeff_zero, G.evalGaugeJet.map_inv, G.evalGaugeJet_gaugeJetOfConstant]

/-- A constant gauge jet acts on the dual of the conjugate value space through the conjugate of
the gauge representation of the inverse of its value. -/
lemma repDualCoeff_repConj_gaugeJetOfConstant_inv (g : G.group) :
    repDualCoeff (FieldDerivSpace.repConj M.repJet) (G.gaugeJetOfConstant g)⁻¹ 0 =
      (ConjModule.endConj ((M.rep g⁻¹ : M.V →L[ℂ] M.V) : M.V →ₗ[ℂ] M.V)).dualMap := by
  show (GlobalGaugeGroup.repCoeff _ _ 0).dualMap = _
  rw [GlobalGaugeGroup.repCoeff_repConj]
  show (ConjModule.endConj (repCoeff M _ 0)).dualMap = _
  rw [repCoeff_zero, G.evalGaugeJet.map_inv, G.evalGaugeJet_gaugeJetOfConstant]

lemma continuousCoeff_rep :
    ContinuousCoeff fun g : G.group => ((M.rep g : M.V →L[ℂ] M.V) : Module.End ℂ M.V) :=
  fun v φ => M.continuous_rep_apply v φ

/-- The gauge group acts on the dual of the value space with continuous coefficients. -/
lemma continuousCoeff_repDualCoeff :
    ContinuousCoeff fun g : G.group => repDualCoeff M.repJet (G.gaugeJetOfConstant g)⁻¹ 0 := by
  simp only [repDualCoeff_gaugeJetOfConstant_inv]
  exact ((continuousCoeff_rep M).comp continuous_inv).dualMap

/-- The gauge group acts on the dual of the conjugate value space with continuous
coefficients. -/
lemma continuousCoeff_repDualCoeff_repConj : ContinuousCoeff fun g : G.group =>
    repDualCoeff (FieldDerivSpace.repConj M.repJet) (G.gaugeJetOfConstant g)⁻¹ 0 := by
  simp only [repDualCoeff_repConj_gaugeJetOfConstant_inv]
  exact ((continuousCoeff_rep M).comp continuous_inv).endConj.dualMap

/-- For a continuous Lorentz representation, the Lorentz group acts on the dual of the value
space with continuous coefficients. -/
lemma LorentzContinuous.continuousCoeff_dual {M : G.MatterField} (hM : M.LorentzContinuous) :
    ContinuousCoeff fun Λ : SL(2,ℂ) => M.repLorentz.dual Λ := by
  simp only [Representation.dual_apply, ← LinearMap.dualMap_def]
  exact (ContinuousCoeff.comp (σ := fun Λ => M.repLorentz Λ) hM continuous_inv).dualMap

/-- For a continuous Lorentz representation, the Lorentz group acts on the dual of the
conjugate value space with continuous coefficients. -/
lemma LorentzContinuous.continuousCoeff_conj_dual {M : G.MatterField}
    (hM : M.LorentzContinuous) : ContinuousCoeff fun Λ : SL(2,ℂ) => M.repLorentz.conj.dual Λ := by
  have h (Λ : SL(2,ℂ)) : M.repLorentz.conj Λ = ConjModule.endConj (M.repLorentz Λ) := rfl
  simp only [Representation.dual_apply, ← LinearMap.dualMap_def, h]
  exact (ContinuousCoeff.comp (σ := fun Λ => M.repLorentz Λ) hM continuous_inv).endConj.dualMap

/-!

### A.2. Commutation

-/

/-- When the gauge and Lorentz representations commute, so do their actions on the dual of the
value space. -/
lemma GaugeLorentzCommute.repDualCoeff_dual {M : G.MatterField} (hM : M.GaugeLorentzCommute)
    (g : G.group) (Λ : SL(2,ℂ)) (φ : Module.Dual ℂ M.V) :
    repDualCoeff M.repJet (G.gaugeJetOfConstant g)⁻¹ 0 (M.repLorentz.dual Λ φ) =
      M.repLorentz.dual Λ (repDualCoeff M.repJet (G.gaugeJetOfConstant g)⁻¹ 0 φ) := by
  rw [repDualCoeff_gaugeJetOfConstant_inv]
  ext v
  simp only [Representation.dual_apply, Module.Dual.transpose_apply, LinearMap.dualMap_apply,
    LinearMap.comp_apply, ContinuousLinearMap.coe_coe]
  rw [hM]

/-- When the gauge and Lorentz representations commute, so do their actions on the dual of the
conjugate value space. -/
lemma GaugeLorentzCommute.repDualCoeff_conj_dual {M : G.MatterField}
    (hM : M.GaugeLorentzCommute) (g : G.group) (Λ : SL(2,ℂ))
    (φ : Module.Dual ℂ (ConjModule M.V)) :
    repDualCoeff (FieldDerivSpace.repConj M.repJet) (G.gaugeJetOfConstant g)⁻¹ 0
        (M.repLorentz.conj.dual Λ φ) =
      M.repLorentz.conj.dual Λ
        (repDualCoeff (FieldDerivSpace.repConj M.repJet) (G.gaugeJetOfConstant g)⁻¹ 0 φ) := by
  rw [repDualCoeff_repConj_gaugeJetOfConstant_inv]
  ext v
  simp only [Representation.dual_apply, Module.Dual.transpose_apply, LinearMap.dualMap_apply,
    LinearMap.comp_apply, ContinuousLinearMap.coe_coe, Representation.conj_apply,
    ConjModule.endConj_apply, LinearEquiv.symm_apply_apply]
  rw [hM]

end GlobalGaugeGroup.MatterField

namespace GaugeFieldData.LocalCovFieldAlgebra

variable {κ : Type} [Fintype κ] [DecidableEq κ] {G : GlobalGaugeGroup κ} {T : GaugeFieldData G}

-- The entry `Λ_{b a}` of the Lorentz matrix of `Λ : SL(2,ℂ)`, as a complex scalar.
set_option quotPrecheck false in
local notation:max "L[" Λ "]" b:max a:max => (((SL2C.toLorentzGroup Λ).1 b a : ℝ) : ℂ)

/-!

## B. The joint action of the gauge and Lorentz groups

-/

/-- A constant gauge jet commutes with the Lorentz group on the field-strength tower. -/
lemma repJet_repLorentzGroup_covDerivFieldStrength (g : G.group) (Λ : SL(2,ℂ))
    (l : List (Fin 1 ⊕ Fin 3)) (μ ν : Fin 1 ⊕ Fin 3) (φ : Module.Dual ℝ G.lieSubalgebra) :
    T.repJet (G.gaugeJetOfConstant g) (T.repLorentzGroup Λ (T.covDerivFieldStrength l μ ν φ)) =
      T.repLorentzGroup Λ
        (T.repJet (G.gaugeJetOfConstant g) (T.covDerivFieldStrength l μ ν φ)) := by
  obtain ⟨n, l, rfl⟩ : ∃ n, ∃ l' : Fin n → Fin 1 ⊕ Fin 3, l = List.ofFn l' :=
    ⟨_, l.get, (List.ofFn_get l).symm⟩
  simp only [repLorentzGroup_covDerivFieldStrength, repJet_covDerivFieldStrength, map_sum,
    map_smul]

/-- A constant gauge jet commutes with the Lorentz group on the tower of a fermionic species. -/
lemma repJet_repLorentzGroup_covDerivFermion (hC : T.GaugeLorentzCommute) (g : G.group)
    (Λ : SL(2,ℂ)) (i : T.FermionSpecies) {n : ℕ}
    (l : Fin n → Fin 1 ⊕ Fin 3) (φ : Module.Dual ℂ (T.FermionValue i)) :
    T.repJet (G.gaugeJetOfConstant g) (T.repLorentzGroup Λ (T.covDerivFermion i l φ)) =
      T.repLorentzGroup Λ (T.repJet (G.gaugeJetOfConstant g) (T.covDerivFermion i l φ)) := by
  simp only [repLorentzGroup_covDerivFermion Λ i (hC.1 i).gaugeLorentzCompatible,
    repJet_covDerivFermion, map_sum,
    map_smul, (hC.1 i).repDualCoeff_dual]

lemma repJet_repLorentzGroup_covDerivConjFermion (hC : T.GaugeLorentzCommute) (g : G.group)
    (Λ : SL(2,ℂ)) (i : T.FermionSpecies) {n : ℕ}
    (l : Fin n → Fin 1 ⊕ Fin 3) (φ : Module.Dual ℂ (ConjModule (T.FermionValue i))) :
    T.repJet (G.gaugeJetOfConstant g) (T.repLorentzGroup Λ (T.covDerivConjFermion i l φ)) =
      T.repLorentzGroup Λ (T.repJet (G.gaugeJetOfConstant g) (T.covDerivConjFermion i l φ)) := by
  simp only [repLorentzGroup_covDerivConjFermion Λ i (hC.1 i).gaugeLorentzCompatible,
    repJet_covDerivConjFermion,
    map_sum, map_smul, (hC.1 i).repDualCoeff_conj_dual]

lemma repJet_repLorentzGroup_covDerivBoson (hC : T.GaugeLorentzCommute) (g : G.group)
    (Λ : SL(2,ℂ)) (j : T.BosonSpecies) {n : ℕ}
    (l : Fin n → Fin 1 ⊕ Fin 3) (φ : Module.Dual ℂ (T.BosonValue j)) :
    T.repJet (G.gaugeJetOfConstant g) (T.repLorentzGroup Λ (T.covDerivBoson j l φ)) =
      T.repLorentzGroup Λ (T.repJet (G.gaugeJetOfConstant g) (T.covDerivBoson j l φ)) := by
  simp only [repLorentzGroup_covDerivBoson Λ j (hC.2 j).gaugeLorentzCompatible,
    repJet_covDerivBoson, map_sum,
    map_smul, (hC.2 j).repDualCoeff_dual]

lemma repJet_repLorentzGroup_covDerivConjBoson (hC : T.GaugeLorentzCommute) (g : G.group)
    (Λ : SL(2,ℂ)) (j : T.BosonSpecies) {n : ℕ}
    (l : Fin n → Fin 1 ⊕ Fin 3) (φ : Module.Dual ℂ (ConjModule (T.BosonValue j))) :
    T.repJet (G.gaugeJetOfConstant g) (T.repLorentzGroup Λ (T.covDerivConjBoson j l φ)) =
      T.repLorentzGroup Λ (T.repJet (G.gaugeJetOfConstant g) (T.covDerivConjBoson j l φ)) := by
  simp only [repLorentzGroup_covDerivConjBoson Λ j (hC.2 j).gaugeLorentzCompatible,
    repJet_covDerivConjBoson,
    map_sum, map_smul, (hC.2 j).repDualCoeff_conj_dual]

/-- On the covariant field algebra, a constant gauge jet commutes with the Lorentz group when
the gauge and Lorentz representations of every species commute. -/
lemma repJet_repLorentzGroup_comm (hC : T.GaugeLorentzCommute) (g : G.group) (Λ : SL(2,ℂ))
    {x : T.LocalFieldAlgebra} (hx : x ∈ T.LocalCovFieldAlgebra) :
    T.repJet (G.gaugeJetOfConstant g) (T.repLorentzGroup Λ x) =
      T.repLorentzGroup Λ (T.repJet (G.gaugeJetOfConstant g) x) := by
  refine induction (P := fun x => T.repJet (G.gaugeJetOfConstant g) (T.repLorentzGroup Λ x) =
    T.repLorentzGroup Λ (T.repJet (G.gaugeJetOfConstant g) x)) hx
    (repJet_repLorentzGroup_covDerivFieldStrength g Λ)
    (repJet_repLorentzGroup_covDerivFermion hC g Λ)
    (repJet_repLorentzGroup_covDerivConjFermion hC g Λ)
    (repJet_repLorentzGroup_covDerivBoson hC g Λ)
    (repJet_repLorentzGroup_covDerivConjBoson hC g Λ) (fun z => ?_) (fun x y hx hy => ?_)
    (fun x y hx hy => ?_)
  · simp only [map_smul, GaugeFieldData.repJet_apply_one, GaugeFieldData.repLorentzGroup_apply_one]
  · simp only [map_add, hx, hy]
  · exact ((congrArg (T.repJet _) (GaugeFieldData.repLorentzGroup_apply_mul Λ x y)).trans
      (GaugeFieldData.repJet_apply_mul _ _ _)).trans ((congrArg₂ (· * ·) hx hy).trans
        ((GaugeFieldData.repLorentzGroup_apply_mul Λ _ _).symm.trans
          (congrArg (T.repLorentzGroup Λ) (GaugeFieldData.repJet_apply_mul _ x y).symm)))

lemma repValue_apply_one (g : G.group) : repValue T g 1 = 1 :=
  Subtype.ext (GaugeFieldData.repJet_apply_one _)

lemma repLorentzGroup_apply_one (hGL : T.GaugeLorentzCompatible) (Λ : SL(2,ℂ)) :
    repLorentzGroup T hGL Λ 1 = 1 :=
  Subtype.ext (GaugeFieldData.repLorentzGroup_apply_one Λ)

/-- The ordinary gauge group and the Lorentz group act on the covariant field algebra by
commuting operators, when the gauge and Lorentz representations of every species commute. -/
lemma commute_repValue_repLorentzGroup (hC : T.GaugeLorentzCommute) (g : G.group) (Λ : SL(2,ℂ)) :
    Commute (repValue T g) (repLorentzGroup T hC.gaugeLorentzCompatible Λ) :=
  LinearMap.ext fun x => Subtype.ext (repJet_repLorentzGroup_comm hC g Λ x.2)

variable (T) in
/-- The action of `G × SL(2,ℂ)` on the covariant field algebra, built from the commuting actions
of the ordinary gauge group and of the Lorentz group. -/
noncomputable def repGaugeLorentz (hC : T.GaugeLorentzCommute) :
    Representation ℂ (G.group × SL(2,ℂ)) T.LocalCovFieldAlgebra :=
  Representation.prodOfCommute (repValue T) (repLorentzGroup T hC.gaugeLorentzCompatible)
    (commute_repValue_repLorentzGroup hC)

lemma repGaugeLorentz_comp_inl (hC : T.GaugeLorentzCommute) :
    (repGaugeLorentz T hC).comp (MonoidHom.inl G.group SL(2,ℂ)) = repValue T :=
  Representation.prodOfCommute_comp_inl _ _ _

lemma repGaugeLorentz_comp_inr (hC : T.GaugeLorentzCommute) :
    (repGaugeLorentz T hC).comp (MonoidHom.inr G.group SL(2,ℂ)) =
      repLorentzGroup T hC.gaugeLorentzCompatible :=
  Representation.prodOfCommute_comp_inr _ _ _

/-!

## C. Continuity on the covariant towers

### C.1. The Lorentz matrix

-/

/-- The entries of the Lorentz matrix of `Λ : SL(2,ℂ)` depend continuously on `Λ`. -/
lemma continuous_toLorentzGroup_apply (b a : Fin 1 ⊕ Fin 3) :
    Continuous fun Λ : SL(2,ℂ) => L[Λ] b a := by
  simp only [SL2C.toLorentzGroup_eq_trace]
  have hΛ : Continuous fun Λ : SL(2,ℂ) => (Λ : Matrix (Fin 2) (Fin 2) ℂ) := continuous_subtype_val
  exact ((continuous_const.matrix_mul ((hΛ.matrix_mul continuous_const).matrix_mul
    hΛ.matrix_conjTranspose)).matrix_trace).div_const 2

/-!

### C.2. The field-strength tower

-/

/-- The adjoint representation of the gauge group has continuous coefficients. -/
lemma continuousCoeff_adjointRep : ContinuousCoeff fun g : G.group => G.adjointRep g := by
  intro a ψ
  obtain ⟨F, hF⟩ := LinearMap.exists_extend (p := G.lieAlgebra) ψ
  have h (g : G.group) : ψ (G.adjointRep g a) =
      F ((g : GeneralLinearGroup κ ℂ) * (a : Matrix κ κ ℂ) * ((g : GeneralLinearGroup κ ℂ)⁻¹ :
        GeneralLinearGroup κ ℂ)) := by
    rw [← hF]
    rfl
  simp only [h]
  have hv : Continuous fun g : G.group => ((g : GeneralLinearGroup κ ℂ) : Matrix κ κ ℂ) :=
    Units.continuous_val.comp continuous_subtype_val
  have hi : Continuous fun g : G.group =>
      (((g : GeneralLinearGroup κ ℂ)⁻¹ : GeneralLinearGroup κ ℂ) : Matrix κ κ ℂ) :=
    Units.continuous_coe_inv.comp continuous_subtype_val
  exact F.continuous_of_finiteDimensional.comp ((hv.matrix_mul continuous_const).matrix_mul hi)

/-- The field-strength tower is real-linear in its adjoint index. -/
lemma covFieldStrength_eq_sum (l : List (Fin 1 ⊕ Fin 3)) (μ ν : Fin 1 ⊕ Fin 3)
    (φ : Module.Dual ℝ G.lieSubalgebra) :
    covFieldStrength T l μ ν φ = ∑ j, ((Module.finBasis ℝ _ |>.repr φ j : ℝ) : ℂ) •
      covFieldStrength T l μ ν (Module.finBasis ℝ (Module.Dual ℝ G.lieSubalgebra) j) := by
  refine Subtype.ext ?_
  simp only [coe_covFieldStrength, AddSubmonoidClass.coe_finsetSum, Subalgebra.coe_smul]
  conv_lhs => rw [← (Module.finBasis ℝ (Module.Dual ℝ G.lieSubalgebra)).sum_repr φ]
  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_smul, ← algebraMap_smul ℂ]
  rfl

/-- The field-strength tower has a continuous span. -/
lemma hasContinuousSpan_covFieldStrength (hGL : T.GaugeLorentzCompatible) {n : ℕ}
    (l : Fin n → Fin 1 ⊕ Fin 3) (μ ν : Fin 1 ⊕ Fin 3) (φ : Module.Dual ℝ G.lieSubalgebra) :
    HasContinuousSpan (repValue T) (repLorentzGroup T hGL)
      (covFieldStrength T (List.ofFn l) μ ν φ) := by
  let t (q : (Fin n → Fin 1 ⊕ Fin 3) × (Fin 1 ⊕ Fin 3) × (Fin 1 ⊕ Fin 3))
      (x : Module.Dual ℝ G.lieSubalgebra) : T.LocalCovFieldAlgebra :=
    covFieldStrength T (List.ofFn q.1) q.2.1 q.2.2 x
  have ht (q : (Fin n → Fin 1 ⊕ Fin 3) × (Fin 1 ⊕ Fin 3) × (Fin 1 ⊕ Fin 3)) x :=
    covFieldStrength_eq_sum (T := T) (List.ofFn q.1) q.2.1 q.2.2 x
  refine .of_mem_span (Representation.isContinuousFamily_tower _ Complex.continuous_ofReal t ht
      _ (continuousCoeff_adjointRep.comp continuous_inv).dualMap
      (fun q q' _ => if q = q' then 1 else 0) (fun _ _ => continuous_const) ?_)
    (Representation.isContinuousFamily_tower _ Complex.continuous_ofReal t ht
      (fun _ => 1) (fun _ _ => continuous_const)
      (fun q q' Λ => (∏ k, L[Λ] (q'.1 k) (q.1 k)) * (L[Λ] q'.2.1 q.2.1 * L[Λ] q'.2.2 q.2.2))
      (fun _ _ => (continuous_finsetProd _ fun _ _ => continuous_toLorentzGroup_apply _ _).mul
        ((continuous_toLorentzGroup_apply _ _).mul (continuous_toLorentzGroup_apply _ _))) ?_) ?_
  · intro g q x
    simp [t, repValue_covFieldStrength]
  · intro Λ q x
    simp only [t, repLorentzGroup_covFieldStrength, Fintype.sum_prod_type, Finset.smul_sum,
      smul_smul, one_apply_eq_self]
  · have h := ht (l, μ, ν) φ
    dsimp only at h
    rw [h]
    exact Submodule.sum_mem _ fun j _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨((l, μ, ν), j), rfl⟩)

/-!

### C.3. The matter towers

-/

/-- A tower `t p x`, linear in `x`, on which the gauge group acts through an operator family with
continuous coefficients on `x`, and the Lorentz group through the Lorentz matrix on the
directions `p` and an operator family with continuous coefficients on `x`, has a continuous
span. -/
lemma hasContinuousSpan_tower (hGL : T.GaugeLorentzCompatible) {D : Type} [AddCommGroup D]
    [Module ℂ D] [FiniteDimensional ℂ D] {n : ℕ}
    (t : (Fin n → Fin 1 ⊕ Fin 3) → D →ₗ[ℂ] T.LocalCovFieldAlgebra)
    {σ₁ : G.group → Module.End ℂ D} (hσ₁ : ContinuousCoeff σ₁)
    (h₁ : ∀ g p x, repValue T g (t p x) = t p (σ₁ g x))
    {σ₂ : SL(2,ℂ) → Module.End ℂ D} (hσ₂ : ContinuousCoeff σ₂)
    (h₂ : ∀ Λ p x, repLorentzGroup T hGL Λ (t p x) =
      ∑ p', (∏ k, L[Λ] (p' k) (p k)) • t p' (σ₂ Λ x))
    (l : Fin n → Fin 1 ⊕ Fin 3) (x : D) :
    HasContinuousSpan (repValue T) (repLorentzGroup T hGL) (t l x) := by
  have ht (p : Fin n → Fin 1 ⊕ Fin 3) (x : D) :
      t p x = ∑ j, (fun z : ℂ => z) ((Module.finBasis ℂ D).repr x j) •
        t p (Module.finBasis ℂ D j) := by
    conv_lhs => rw [← (Module.finBasis ℂ D).sum_repr x]
    simp only [map_sum, map_smul]
  refine .of_mem_span (Representation.isContinuousFamily_tower _ continuous_id (fun p => t p) ht
      _ hσ₁ (fun p p' _ => if p = p' then 1 else 0) (fun _ _ => continuous_const) ?_)
    (Representation.isContinuousFamily_tower _ continuous_id (fun p => t p) ht _ hσ₂
      (fun p p' Λ => ∏ k, L[Λ] (p' k) (p k))
      (fun _ _ => continuous_finsetProd _ fun _ _ => continuous_toLorentzGroup_apply _ _) h₂) ?_
  · intro g p x
    simp [h₁]
  · rw [ht]
    exact Submodule.sum_mem _ fun j _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨(l, j), rfl⟩)

/-!

## D. Finite-dimensional stable subspaces

-/

/-- Every element of the covariant field algebra lies in the span of a finite family on which
the ordinary gauge group and the Lorentz group act with continuous coefficients. -/
lemma hasContinuousSpan (hGL : T.GaugeLorentzCompatible) (hL : T.LorentzContinuous)
    (a : T.LocalCovFieldAlgebra) : HasContinuousSpan (repValue T) (repLorentzGroup T hGL) a := by
  obtain ⟨a, ha⟩ := a
  change a ∈ Algebra.adjoin ℂ T.covGenerators at ha
  induction ha using Algebra.adjoin_induction with
  | mem x hx =>
    refine covGenerators_cases (P := fun b => ∀ hb : b ∈ T.LocalCovFieldAlgebra,
      HasContinuousSpan (repValue T) (repLorentzGroup T hGL) ⟨b, hb⟩) hx ?_ ?_ ?_ ?_ ?_ _
    · intro l μ ν φ _
      have h := hasContinuousSpan_covFieldStrength hGL l.get μ ν φ
      rw [List.ofFn_get] at h
      exact h
    · intro i n l φ _
      exact hasContinuousSpan_tower hGL (covFermion T i) (T.fermion i).continuousCoeff_repDualCoeff
        (fun g p x => repJet_covFermion _ i p x) (hL.1 i).continuousCoeff_dual
        (fun Λ p x => repLorentzGroup_covFermion hGL Λ i p x) l φ
    · intro i n l φ _
      exact hasContinuousSpan_tower hGL (covConjFermion T i)
        (T.fermion i).continuousCoeff_repDualCoeff_repConj
        (fun g p x => repJet_covConjFermion _ i p x) (hL.1 i).continuousCoeff_conj_dual
        (fun Λ p x => repLorentzGroup_covConjFermion hGL Λ i p x) l φ
    · intro j n l φ _
      exact hasContinuousSpan_tower hGL (covBoson T j) (T.boson j).continuousCoeff_repDualCoeff
        (fun g p x => repJet_covBoson _ j p x) (hL.2 j).continuousCoeff_dual
        (fun Λ p x => repLorentzGroup_covBoson hGL Λ j p x) l φ
    · intro j n l φ _
      exact hasContinuousSpan_tower hGL (covConjBoson T j)
        (T.boson j).continuousCoeff_repDualCoeff_repConj
        (fun g p x => repJet_covConjBoson _ j p x) (hL.2 j).continuousCoeff_conj_dual
        (fun Λ p x => repLorentzGroup_covConjBoson hGL Λ j p x) l φ
  | algebraMap z =>
    rw [show (⟨algebraMap ℂ T.LocalFieldAlgebra z, Subalgebra.algebraMap_mem _ z⟩ :
      T.LocalCovFieldAlgebra) = z • 1 from Subtype.ext (Algebra.algebraMap_eq_smul_one z)]
    exact Representation.hasContinuousSpan_smul_one repValue_apply_one
      (repLorentzGroup_apply_one hGL) z
  | add x y _ _ hx hy => exact hx.add hy
  | mul x y _ _ hx hy => exact hx.mul repValue_apply_mul (repLorentzGroup_apply_mul hGL) hy

/-- Every element of the covariant field algebra lies in a finite-dimensional subrepresentation
for the joint action of the gauge and Lorentz groups, on which both groups act with continuous
matrix coefficients. -/
lemma exists_subrepresentation (hL : T.LorentzContinuous) (hC : T.GaugeLorentzCommute)
    (a : T.LocalCovFieldAlgebra) :
    ∃ W : Subrepresentation (repGaugeLorentz T hC), a ∈ W.toSubmodule ∧
      FiniteDimensional ℂ W.toSubmodule ∧
      Representation.ContinuousMatrixCoeff (W.comp (MonoidHom.inl G.group SL(2,ℂ))) ∧
      Representation.ContinuousMatrixCoeff (W.comp (MonoidHom.inr G.group SL(2,ℂ))) := by
  have h := hasContinuousSpan hC.gaugeLorentzCompatible hL a
  unfold Representation.HasContinuousSpan at h
  obtain ⟨ι, _, v, ha_v, h₁, h₂⟩ := h
  exact Representation.exists_subrepresentation_of_isContinuousFamily _ h₁ h₂ ha_v

/-- A chosen finite-dimensional subrepresentation for the joint action of the gauge and Lorentz
groups containing `a`, on which both groups act with continuous matrix coefficients. -/
noncomputable def finiteSubrep (hL : T.LorentzContinuous) (hC : T.GaugeLorentzCommute)
    (a : T.LocalCovFieldAlgebra) :
    Subrepresentation (repGaugeLorentz T hC) :=
  (exists_subrepresentation hL hC a).choose

variable (hL : T.LorentzContinuous) (hC : T.GaugeLorentzCommute) (a : T.LocalCovFieldAlgebra)

lemma mem_finiteSubrep : a ∈ (finiteSubrep hL hC a).toSubmodule :=
  (exists_subrepresentation hL hC a).choose_spec.1

instance finiteDimensional_finiteSubrep :
    FiniteDimensional ℂ (finiteSubrep hL hC a).toSubmodule :=
  (exists_subrepresentation hL hC a).choose_spec.2.1

lemma continuousMatrixCoeff_finiteSubrep_inl : Representation.ContinuousMatrixCoeff
    ((finiteSubrep hL hC a).comp (MonoidHom.inl G.group SL(2,ℂ))) :=
  (exists_subrepresentation hL hC a).choose_spec.2.2.1

lemma continuousMatrixCoeff_finiteSubrep_inr : Representation.ContinuousMatrixCoeff
    ((finiteSubrep hL hC a).comp (MonoidHom.inr G.group SL(2,ℂ))) :=
  (exists_subrepresentation hL hC a).choose_spec.2.2.2

end GaugeFieldData.LocalCovFieldAlgebra
