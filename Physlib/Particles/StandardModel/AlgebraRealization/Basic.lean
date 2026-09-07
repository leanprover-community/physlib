/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module
public import Physlib.Particles.StandardModel.Fermions.DownSinglet.GaugeAlgebraAction
public import Physlib.Particles.StandardModel.Fermions.LeptonDoublet.GaugeAlgebraAction
public import Physlib.Particles.StandardModel.Fermions.LeptonSinglet.GaugeAlgebraAction
public import Physlib.Particles.StandardModel.Fermions.QuarkDoublet.GaugeAlgebraAction
public import Physlib.Particles.StandardModel.Fermions.UpSinglet.GaugeAlgebraAction
public import Physlib.Particles.StandardModel.GaugeBosons.AlgebraValued.Symmeterized
public import Physlib.Particles.StandardModel.HiggsBoson.GaugeAlgebraAction
public import Physlib.Particles.StandardModel.JetAlgebra.TransformsIn
/-!
# The algebra valued Standard model

## i. Overview

An algebra `B` carries a Standard Model when the fields of the Standard Model, and every
polynomial expression in them, sit inside it compatibly with the gauge action, the Lorentz
action and the mass-weight grading. The jet algebra `StandardModel.JetAlgebra` is the
universal object with those fields, so the statement is a single one: an algebra map
`JetAlgebra →ₐ[ℂ] B`, equivariant for the jet gauge group and the Lorentz group and
compatible with `massWeightPoly`. That is the structure `AlgebraRealization`, together with
the two demands that the group actions be multiplicative on the whole of `B` and not
merely on the image of the map — the covariant derivative of a matter field needs them
there.

The thirteen families of derivative symbols are then derived: `h.A`, `h.H`, `h.barH` and
the ten fermion families are the jet algebra's own families pushed along the map. Every
transformation law, mass weight and commutation rule they satisfy is likewise the jet
algebra's own fact pushed along the map. Section B does that transport once for each shape
a law takes, and sections C to E prove the gauge laws, the Lorentz laws and the mass
weights, one section per shape. They carry the names they carried when they were axioms,
so they are used exactly as before.

The statistics of the fields — the commutation and anticommutation laws of the thirteen
families — are proved the same way in [`Commutations.lean`](Commutations.lean). The
covariant reduction, which rests on both, is [`CovariantDeriv.lean`](CovariantDeriv.lean):
the Lorentz mixing of derivative slots, the field algebra, the covariant derivative towers,
their gauge covariance and the classification of jet-gauge invariants.

## ii. Key results

- `StandardModel.AlgebraRealization` : an algebra is a Standard Model when it receives an
  equivariant algebra map from the jet algebra.
- `AlgebraRealization.A`, `AlgebraRealization.H` and their companions : the thirteen families of
  derivative symbols of a Standard Model.
- `AlgebraRealization.repJet_A`, `AlgebraRealization.repLorentz_H`,
  `AlgebraRealization.massWeight_d` and their companions : the transformation laws and mass
  weights of those families.

## iii. Table of contents

- A. The fields of a Standard Model
- B. Transporting a fact along the defining map
- C. The gauge transformation of the fields
- D. The Lorentz transformation of the fields
- E. The mass weights of the fields

-/

@[expose] public section

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 1000000
set_option synthInstance.maxSize 2048
set_option maxRecDepth 8000

namespace StandardModel

open TensorProduct Matrix MatrixGroups Lorentz

/-- The algebra `B`, with a jet gauge action, a Lorentz action and a mass-weight grading,
  is a Standard Model when it receives an algebra map from the jet algebra of the Standard
  Model which is equivariant for both actions and compatible with the grading. The fields
  of the Standard Model then sit inside `B` as the images of the jet algebra's own, and
  every law they satisfy there is the jet algebra's own law pushed along the map.

  The last two fields are not consequences of the first four: an equivariant map forces the
  two actions to be multiplicative only on its image, whereas the covariant derivative of a
  matter field needs them multiplicative on the whole of `B`. -/
structure AlgebraRealization (B : Type) [Ring B] [Algebra ℂ B]
    (repJet : Representation ℂ JetGaugeGroupI B)
    (repLorentz : Representation ℂ SL(2,ℂ) B)
    (massWeightPoly : B →ₐ[ℂ] Polynomial B) where
  /-- The algebra map out of the jet algebra of the Standard Model: it is what places the
    fields of the Standard Model, and every polynomial expression in them, inside `B`. -/
  toAlgHom : JetAlgebra →ₐ[ℂ] B
  /-- The map is equivariant for the jet gauge group: the gauge action on `B` restricts
    along it to the jet algebra's own. -/
  map_repJet : ∀ (U : JetGaugeGroupI) (x : JetAlgebra),
    toAlgHom (JetAlgebra.repJetGaugeGroupI U x) = repJet U (toAlgHom x)
  /-- The map is equivariant for the Lorentz group: the Lorentz action on `B` restricts
    along it to the jet algebra's own. -/
  map_repLorentz : ∀ (Λ : SL(2,ℂ)) (x : JetAlgebra),
    toAlgHom (JetAlgebra.repLorentzGroup Λ x) = repLorentz Λ (toAlgHom x)
  /-- The map carries the mass-weight grading of the jet algebra to that of `B`: the
    mass-weight polynomial of an image is the image of the mass-weight polynomial. -/
  map_massWeight : ∀ x : JetAlgebra, massWeightPoly (toAlgHom x)
    = Polynomial.mapAlgHom toAlgHom (JetAlgebra.massWeightPoly x)
  /-- The jet gauge action preserves products on the whole of `B`, not merely on the image
    of the jet algebra: gauge transformations act by algebra endomorphisms. -/
  repJet_mul : ∀ (U : JetGaugeGroupI) (b₁ b₂ : B),
    repJet U (b₁ * b₂) = repJet U b₁ * repJet U b₂
  /-- Lorentz transformations act on `B` by algebra maps: the action preserves products, so
    each `repLorentz Λ` is an algebra endomorphism of `B`. -/
  repLorentz_mul : ∀ (Λ : SL(2,ℂ)) (b₁ b₂ : B),
    repLorentz Λ (b₁ * b₂) = repLorentz Λ b₁ * repLorentz Λ b₂

namespace AlgebraRealization

variable {B : Type} [Ring B] [Algebra ℂ B]
  {repJet : Representation ℂ JetGaugeGroupI B}
  {repLorentz : Representation ℂ SL(2,ℂ) B}
  {massWeightPoly : B →ₐ[ℂ] Polynomial B}
  (h : AlgebraRealization B repJet repLorentz massWeightPoly)

/-!

## A. The fields of a Standard Model

The thirteen families of derivative symbols the theory is written in — the gauge field,
the Higgs field and its conjugate, and the five fermion species in three generations with
their conjugates — are no longer data of the structure. They are the corresponding
families of the jet algebra, carried into `B` along the defining algebra map. The gauge
family is real-linear in its value index, so the map is restricted to `ℝ` there.

-/

/-- The derivative symbols `∂_s A_μ^ψ` of the gauge field inside `B`. -/
noncomputable def A (s : Multiset (Fin 1 ⊕ Fin 3)) (μ : Fin 1 ⊕ Fin 3) :
    Module.Dual ℝ GaugeAlgebra →ₗ[ℝ] B :=
  h.toAlgHom.toLinearMap.restrictScalars ℝ ∘ₗ JetAlgebra.gaugeField s μ

/-- The derivative symbols `∂_s H_φ` of the Higgs field inside `B`. -/
noncomputable def H (s : Multiset (Fin 1 ⊕ Fin 3)) :
    Module.Dual ℂ HiggsVec →ₗ[ℂ] B :=
  h.toAlgHom.toLinearMap ∘ₗ JetAlgebra.higgsField s

/-- The derivative symbols `∂_s H̄_φ` of the conjugate Higgs field inside `B`. -/
noncomputable def barH (s : Multiset (Fin 1 ⊕ Fin 3)) :
    Module.Dual ℂ (ConjModule HiggsVec) →ₗ[ℂ] B :=
  h.toAlgHom.toLinearMap ∘ₗ JetAlgebra.conjHiggsField s

/-- The derivative symbols of the `i`-th generation down-type quark singlet inside `B`. -/
noncomputable def d (i : Fin 3) (s : Multiset (Fin 1 ⊕ Fin 3)) :
    Module.Dual ℂ DownSinglet →ₗ[ℂ] B :=
  h.toAlgHom.toLinearMap ∘ₗ JetAlgebra.downSingletField i s

/-- The derivative symbols of the `i`-th generation conjugate down-type quark singlet
  inside `B`. -/
noncomputable def bard (i : Fin 3) (s : Multiset (Fin 1 ⊕ Fin 3)) :
    Module.Dual ℂ (ConjModule DownSinglet) →ₗ[ℂ] B :=
  h.toAlgHom.toLinearMap ∘ₗ JetAlgebra.conjDownSingletField i s

/-- The derivative symbols of the `i`-th generation up-type quark singlet inside `B`. -/
noncomputable def u (i : Fin 3) (s : Multiset (Fin 1 ⊕ Fin 3)) :
    Module.Dual ℂ UpSinglet →ₗ[ℂ] B :=
  h.toAlgHom.toLinearMap ∘ₗ JetAlgebra.upSingletField i s

/-- The derivative symbols of the `i`-th generation conjugate up-type quark singlet
  inside `B`. -/
noncomputable def baru (i : Fin 3) (s : Multiset (Fin 1 ⊕ Fin 3)) :
    Module.Dual ℂ (ConjModule UpSinglet) →ₗ[ℂ] B :=
  h.toAlgHom.toLinearMap ∘ₗ JetAlgebra.conjUpSingletField i s

/-- The derivative symbols of the `i`-th generation quark doublet inside `B`. -/
noncomputable def Q (i : Fin 3) (s : Multiset (Fin 1 ⊕ Fin 3)) :
    Module.Dual ℂ QuarkDoublet →ₗ[ℂ] B :=
  h.toAlgHom.toLinearMap ∘ₗ JetAlgebra.quarkDoubletField i s

/-- The derivative symbols of the `i`-th generation conjugate quark doublet inside `B`. -/
noncomputable def barQ (i : Fin 3) (s : Multiset (Fin 1 ⊕ Fin 3)) :
    Module.Dual ℂ (ConjModule QuarkDoublet) →ₗ[ℂ] B :=
  h.toAlgHom.toLinearMap ∘ₗ JetAlgebra.conjQuarkDoubletField i s

/-- The derivative symbols of the `i`-th generation lepton doublet inside `B`. -/
noncomputable def L (i : Fin 3) (s : Multiset (Fin 1 ⊕ Fin 3)) :
    Module.Dual ℂ LeptonDoublet →ₗ[ℂ] B :=
  h.toAlgHom.toLinearMap ∘ₗ JetAlgebra.leptonDoubletField i s

/-- The derivative symbols of the `i`-th generation conjugate lepton doublet inside `B`. -/
noncomputable def barL (i : Fin 3) (s : Multiset (Fin 1 ⊕ Fin 3)) :
    Module.Dual ℂ (ConjModule LeptonDoublet) →ₗ[ℂ] B :=
  h.toAlgHom.toLinearMap ∘ₗ JetAlgebra.conjLeptonDoubletField i s

/-- The derivative symbols of the `i`-th generation charged-lepton singlet inside `B`. -/
noncomputable def e (i : Fin 3) (s : Multiset (Fin 1 ⊕ Fin 3)) :
    Module.Dual ℂ LeptonSinglet →ₗ[ℂ] B :=
  h.toAlgHom.toLinearMap ∘ₗ JetAlgebra.leptonSingletField i s

/-- The derivative symbols of the `i`-th generation conjugate charged-lepton singlet
  inside `B`. -/
noncomputable def bare (i : Fin 3) (s : Multiset (Fin 1 ⊕ Fin 3)) :
    Module.Dual ℂ (ConjModule LeptonSinglet) →ₗ[ℂ] B :=
  h.toAlgHom.toLinearMap ∘ₗ JetAlgebra.conjLeptonSingletField i s

/-!

## B. Transporting a fact along the defining map

Every law the old structure demanded as an axiom is now a theorem, proved once for the jet
algebra and transported along `toAlgHom`. The transport is the same in each of the shapes
the laws take, so each shape is done once. The three shapes used here are a Leibniz
convolution for the gauge action, a slot-mixing sum for the Lorentz action and a monomial
eigenvalue equation for the mass weights; the anticommutation shape is transported in
[`Commutations.lean`](Commutations.lean), beside the laws that use it.

-/

/-- A jet gauge transformation law transports along the defining map: the convolution is a
  multiset sum, and the map is additive and equivariant. -/
private lemma map_family_repJet {V : Type} [AddCommGroup V] [Module ℂ V]
    {rep : Representation ℂ JetGaugeGroupI (JetRing ⊗[ℂ] V)}
    {G : Multiset (Fin 1 ⊕ Fin 3) → Module.Dual ℂ V →ₗ[ℂ] JetAlgebra}
    (hG : TransformsIn (B := JetAlgebra) JetAlgebra.repJetGaugeGroupI rep G) :
    TransformsIn repJet rep fun s => h.toAlgHom.toLinearMap ∘ₗ G s := by
  intro U φ s
  show repJet U (h.toAlgHom _) = _
  rw [← h.map_repJet, hG U φ s, map_multiset_sum, Multiset.map_map]
  rfl

/-- A Lorentz transformation law transports along the defining map: the slot mixing is a
  finite sum of scalar multiples, and the map is linear and equivariant. -/
private lemma map_family_repLorentz {V : Type} [AddCommGroup V] [Module ℂ V]
    {rep : Representation ℂ SL(2,ℂ) V}
    {G : Multiset (Fin 1 ⊕ Fin 3) → Module.Dual ℂ V →ₗ[ℂ] JetAlgebra}
    (hG : IsLorentzDerivTransforms (A := JetAlgebra) JetAlgebra.repLorentzGroup rep G) :
    IsLorentzDerivTransforms repLorentz rep fun s => h.toAlgHom.toLinearMap ∘ₗ G s := by
  intro Λ n l φ
  show repLorentz Λ (h.toAlgHom _) = _
  rw [← h.map_repLorentz, hG Λ n l φ, map_sum]
  exact Finset.sum_congr rfl fun p _ => map_smul h.toAlgHom _ _

/-!

## C. The gauge transformation of the fields

The gauge field is a gauge field — Lorentz covector symbols, the all-orders adjoint
Leibniz convolution with the Maurer–Cartan shift, and a multiplicative gauge action — and
each of the twelve matter families transforms in its own jet gauge representation, the
barred families in the conjugate of it.

-/

/-- The law `repJet_A` of a Standard Model, obtained from the corresponding law of the
  jet algebra by pushing it along the defining algebra map. -/
lemma repJet_A : IsGaugeField repLorentz repJet h.A where
  lorentz_apply := by
    intro Λ n l μ φ
    have key := congrArg h.toAlgHom (JetAlgebra.isGaugeField.lorentz_apply Λ n l μ φ)
    rw [h.map_repLorentz] at key
    refine key.trans ?_
    rw [map_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [map_smul, map_sum]
    congr 1
    exact Finset.sum_congr rfl fun a _ => map_smul h.toAlgHom _ _
  gauge_apply_deriv := by
    intro U s μ φ
    have key := congrArg h.toAlgHom (JetAlgebra.isGaugeField.gauge_apply_deriv U s μ φ)
    rw [h.map_repJet] at key
    refine key.trans ?_
    rw [map_add, map_multiset_sum, Multiset.map_map, AlgHom.commutes]
    rfl
  gauge_mul := h.repJet_mul

/-- The law `repJet_H` of a Standard Model, obtained from the corresponding law of the
  jet algebra by pushing it along the defining algebra map. -/
lemma repJet_H : TransformsIn repJet HiggsVec.repJetGaugeGroupI h.H :=
  h.map_family_repJet JetAlgebra.transformsIn_higgsField

/-- The law `repJet_barH` of a Standard Model, obtained from the corresponding law of the
  jet algebra by pushing it along the defining algebra map. -/
lemma repJet_barH : TransformsIn repJet (repConj HiggsVec.repJetGaugeGroupI) h.barH :=
  h.map_family_repJet JetAlgebra.transformsIn_conjHiggsField

/-- The law `repJet_d` of a Standard Model, obtained from the corresponding law of the
  jet algebra by pushing it along the defining algebra map. -/
lemma repJet_d : ∀ i, TransformsIn repJet DownSinglet.repJetGaugeGroupI (h.d i) :=
  fun i => h.map_family_repJet (JetAlgebra.transformsIn_downSingletField i)

/-- The law `repJet_bard` of a Standard Model, obtained from the corresponding law of the
  jet algebra by pushing it along the defining algebra map. -/
lemma repJet_bard : ∀ i, TransformsIn repJet (repConj DownSinglet.repJetGaugeGroupI) (h.bard i) :=
  fun i => h.map_family_repJet (JetAlgebra.transformsIn_conjDownSingletField i)

/-- The law `repJet_u` of a Standard Model, obtained from the corresponding law of the
  jet algebra by pushing it along the defining algebra map. -/
lemma repJet_u : ∀ i, TransformsIn repJet UpSinglet.repJetGaugeGroupI (h.u i) :=
  fun i => h.map_family_repJet (JetAlgebra.transformsIn_upSingletField i)

/-- The law `repJet_baru` of a Standard Model, obtained from the corresponding law of the
  jet algebra by pushing it along the defining algebra map. -/
lemma repJet_baru : ∀ i, TransformsIn repJet (repConj UpSinglet.repJetGaugeGroupI) (h.baru i) :=
  fun i => h.map_family_repJet (JetAlgebra.transformsIn_conjUpSingletField i)

/-- The law `repJet_Q` of a Standard Model, obtained from the corresponding law of the
  jet algebra by pushing it along the defining algebra map. -/
lemma repJet_Q : ∀ i, TransformsIn repJet QuarkDoublet.repJetGaugeGroupI (h.Q i) :=
  fun i => h.map_family_repJet (JetAlgebra.transformsIn_quarkDoubletField i)

/-- The law `repJet_barQ` of a Standard Model, obtained from the corresponding law of the
  jet algebra by pushing it along the defining algebra map. -/
lemma repJet_barQ : ∀ i, TransformsIn repJet (repConj QuarkDoublet.repJetGaugeGroupI) (h.barQ i) :=
  fun i => h.map_family_repJet (JetAlgebra.transformsIn_conjQuarkDoubletField i)

/-- The law `repJet_L` of a Standard Model, obtained from the corresponding law of the
  jet algebra by pushing it along the defining algebra map. -/
lemma repJet_L : ∀ i, TransformsIn repJet LeptonDoublet.repJetGaugeGroupI (h.L i) :=
  fun i => h.map_family_repJet (JetAlgebra.transformsIn_leptonDoubletField i)

/-- The law `repJet_barL` of a Standard Model, obtained from the corresponding law of the
  jet algebra by pushing it along the defining algebra map. -/
lemma repJet_barL : ∀ i, TransformsIn repJet (repConj LeptonDoublet.repJetGaugeGroupI) (h.barL i) :=
  fun i => h.map_family_repJet (JetAlgebra.transformsIn_conjLeptonDoubletField i)

/-- The law `repJet_e` of a Standard Model, obtained from the corresponding law of the
  jet algebra by pushing it along the defining algebra map. -/
lemma repJet_e : ∀ i, TransformsIn repJet LeptonSinglet.repJetGaugeGroupI (h.e i) :=
  fun i => h.map_family_repJet (JetAlgebra.transformsIn_leptonSingletField i)

/-- The law `repJet_bare` of a Standard Model, obtained from the corresponding law of the
  jet algebra by pushing it along the defining algebra map. -/
lemma repJet_bare : ∀ i, TransformsIn repJet (repConj LeptonSinglet.repJetGaugeGroupI) (h.bare i) :=
  fun i => h.map_family_repJet (JetAlgebra.transformsIn_conjLeptonSingletField i)

/-!

## D. The Lorentz transformation of the fields

The derivative slots of every field mix by per-slot Lorentz matrices, and the value index
by the contragredient of the species' Lorentz representation: the Higgs is a scalar, the
fermions are Weyl spinors, and the barred fields carry the conjugate representations.

-/

/-- The law `repLorentz_H` of a Standard Model, obtained from the corresponding law of the
  jet algebra by pushing it along the defining algebra map. -/
lemma repLorentz_H : IsLorentzDerivTransforms repLorentz
    (Representation.trivial ℂ SL(2,ℂ) HiggsVec) h.H :=
  h.map_family_repLorentz JetAlgebra.isLorentzDerivTransforms_higgsField

/-- The law `repLorentz_barH` of a Standard Model, obtained from the corresponding law of the
  jet algebra by pushing it along the defining algebra map. -/
lemma repLorentz_barH : IsLorentzDerivTransforms repLorentz
    (Representation.trivial ℂ SL(2,ℂ) HiggsVec).conj h.barH :=
  h.map_family_repLorentz JetAlgebra.isLorentzDerivTransforms_conjHiggsField

/-- The law `repLorentz_d` of a Standard Model, obtained from the corresponding law of the
  jet algebra by pushing it along the defining algebra map. -/
lemma repLorentz_d : ∀ i, IsLorentzDerivTransforms repLorentz
    DownSinglet.repLorentzGroup (h.d i) :=
  fun i => h.map_family_repLorentz (JetAlgebra.isLorentzDerivTransforms_downSingletField i)

/-- The law `repLorentz_bard` of a Standard Model, obtained from the corresponding law of the
  jet algebra by pushing it along the defining algebra map. -/
lemma repLorentz_bard : ∀ i, IsLorentzDerivTransforms repLorentz
    DownSinglet.repLorentzGroup.conj (h.bard i) :=
  fun i => h.map_family_repLorentz (JetAlgebra.isLorentzDerivTransforms_conjDownSingletField i)

/-- The law `repLorentz_u` of a Standard Model, obtained from the corresponding law of the
  jet algebra by pushing it along the defining algebra map. -/
lemma repLorentz_u : ∀ i, IsLorentzDerivTransforms repLorentz
    UpSinglet.repLorentzGroup (h.u i) :=
  fun i => h.map_family_repLorentz (JetAlgebra.isLorentzDerivTransforms_upSingletField i)

/-- The law `repLorentz_baru` of a Standard Model, obtained from the corresponding law of the
  jet algebra by pushing it along the defining algebra map. -/
lemma repLorentz_baru : ∀ i, IsLorentzDerivTransforms repLorentz
    UpSinglet.repLorentzGroup.conj (h.baru i) :=
  fun i => h.map_family_repLorentz (JetAlgebra.isLorentzDerivTransforms_conjUpSingletField i)

/-- The law `repLorentz_Q` of a Standard Model, obtained from the corresponding law of the
  jet algebra by pushing it along the defining algebra map. -/
lemma repLorentz_Q : ∀ i, IsLorentzDerivTransforms repLorentz
    QuarkDoublet.repLorentzGroup (h.Q i) :=
  fun i => h.map_family_repLorentz (JetAlgebra.isLorentzDerivTransforms_quarkDoubletField i)

/-- The law `repLorentz_barQ` of a Standard Model, obtained from the corresponding law of the
  jet algebra by pushing it along the defining algebra map. -/
lemma repLorentz_barQ : ∀ i, IsLorentzDerivTransforms repLorentz
    QuarkDoublet.repLorentzGroup.conj (h.barQ i) :=
  fun i => h.map_family_repLorentz (JetAlgebra.isLorentzDerivTransforms_conjQuarkDoubletField i)

/-- The law `repLorentz_L` of a Standard Model, obtained from the corresponding law of the
  jet algebra by pushing it along the defining algebra map. -/
lemma repLorentz_L : ∀ i, IsLorentzDerivTransforms repLorentz
    LeptonDoublet.repLorentzGroup (h.L i) :=
  fun i => h.map_family_repLorentz (JetAlgebra.isLorentzDerivTransforms_leptonDoubletField i)

/-- The law `repLorentz_barL` of a Standard Model, obtained from the corresponding law of the
  jet algebra by pushing it along the defining algebra map. -/
lemma repLorentz_barL : ∀ i, IsLorentzDerivTransforms repLorentz
    LeptonDoublet.repLorentzGroup.conj (h.barL i) :=
  fun i => h.map_family_repLorentz (JetAlgebra.isLorentzDerivTransforms_conjLeptonDoubletField i)

/-- The law `repLorentz_e` of a Standard Model, obtained from the corresponding law of the
  jet algebra by pushing it along the defining algebra map. -/
lemma repLorentz_e : ∀ i, IsLorentzDerivTransforms repLorentz
    LeptonSinglet.repLorentzGroup (h.e i) :=
  fun i => h.map_family_repLorentz (JetAlgebra.isLorentzDerivTransforms_leptonSingletField i)

/-- The law `repLorentz_bare` of a Standard Model, obtained from the corresponding law of the
  jet algebra by pushing it along the defining algebra map. -/
lemma repLorentz_bare : ∀ i, IsLorentzDerivTransforms repLorentz
    LeptonSinglet.repLorentzGroup.conj (h.bare i) :=
  fun i => h.map_family_repLorentz (JetAlgebra.isLorentzDerivTransforms_conjLeptonSingletField i)


end AlgebraRealization

end StandardModel
