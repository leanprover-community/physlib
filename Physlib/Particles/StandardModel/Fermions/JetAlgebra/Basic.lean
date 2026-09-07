/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Particles.StandardModel.Matter.FermionicAlgebra.Prod
public import Physlib.Particles.StandardModel.Matter.FermionicAlgebra.LorentzAction
public import Physlib.Particles.StandardModel.Matter.FermionicAlgebra.GaugeAction
public import Physlib.Particles.StandardModel.Matter.FermionicAlgebra.MassDim
public import Physlib.Particles.StandardModel.Fermions.LeptonDoublet
public import Physlib.Particles.StandardModel.Fermions.LeptonSinglet.Basic
public import Physlib.Particles.StandardModel.Fermions.QuarkDoublet
public import Physlib.Particles.StandardModel.Fermions.UpSinglet
public import Physlib.Particles.StandardModel.Fermions.DownSinglet
/-!
# The fermionic jet algebra of the Standard Model

## i. Overview

The jet algebra of the Standard Model is the algebra in which a Lagrangian lives: the free
algebra on the component functions of every field and all their spacetime derivatives,
subject only to the statistics of the fields.

This file builds its fermionic factor, `FermionJetAlgebra`; the bosonic factors — the gauge
fields and the Higgs — commute with everything and will enter as separate tensor factors.

The Standard Model carries five fermion species — the lepton doublet, the charged-lepton
singlet, the quark doublet, and the up- and down-type quark singlets — each in three
generations, and the fermionic jet algebra is the *exterior product* of their individual
fermionic algebras: generators anticommute, and they do so **across species and generations
as well as within a species**, since all of them are fermionic.

That exterior product is *realized* here as a single exterior algebra on the direct sum of
the fifteen target spaces, and then *identified* with the graded tensor product of the
species algebras by `FermionicAlgebra.prodEquiv`, applied once per species
(`FermionJetAlgebra.exteriorProductLeptonDoublet` and its siblings below). The
identification is genuine, not a convention: the exterior algebra of a direct sum is the
graded (super) tensor product of the exterior algebras of the summands. An ordinary tensor
product `⊗[ℂ]` would instead make generators of different species *commute*, which is wrong
for fermions.

The direct sum is taken as the definition rather than the graded tensor product because
Mathlib's `GradedTensorProduct` carries no `GradedAlgebra` instance, so a graded tensor
product of three or more factors cannot currently be written down as a type; the peeled
form, one species at a time, is as far as the type-level statement goes. Working inside a
single `ExteriorAlgebra` also keeps every algebraic class projecting from one root, and lets
the whole `FermionicAlgebra` API — the Lorentz action, the jet gauge action, the total
derivative and its iterates — apply to `FermionJetAlgebra` unchanged.

## ii. Key results

- `FermionSpace` : the total target space of the Standard Model fermions.
- `FermionSpace.leptonDoubletProj`, … : the projections onto a species and generation.
- `FermionSpace.leptonDoubletIncl`, … : the inclusions of a species and generation.
- `FermionJetAlgebra` : the jet algebra of the Standard Model fermions.
- `FermionJetAlgebra.ofLeptonDoublet`, … : the component functions of each species and
  generation.
- `FermionJetAlgebra.exteriorProductLeptonDoublet`, … : the jet algebra as the exterior
  product of the species algebras.

## iii. Table of contents

- A. The target space of the Standard Model fermions
  - A.1. The projections onto the species
  - A.2. The inclusions onto the species
  - A.3. The action of the Lorentz group
  - A.4. The action of the global gauge group
  - A.5. The action of the jet gauge group
- B. The fermionic jet algebra
  - B.1. The component functions of each species
  - B.2. The exterior product decomposition

-/

@[expose] public section

namespace StandardModel

open TensorProduct

/-!

## A. The target space of the Standard Model fermions

-/

/-- The total target space of the Standard Model fermions: the direct sum of three
  generations each of the lepton doublet, the charged-lepton singlet, the quark doublet, and
  the up- and down-type quark singlets. The three generations of a species sit together, so
  that a species can be split off the jet algebra as a single exterior factor. -/
abbrev FermionSpace : Type :=
  (Fin 3 → LeptonDoublet) × (Fin 3 → LeptonSinglet) × (Fin 3 → QuarkDoublet) ×
    (Fin 3 → UpSinglet) × (Fin 3 → DownSinglet)

namespace FermionSpace

/-!

### A.1. The projections onto the species

The component functions of a field are *covectors* on its target space, so it is the
projections — not the inclusions — that carry the individual species into the jet algebra.
Each projection takes a generation index `i : Fin 3`.

-/

/-- The projection onto the `i`-th generation of the lepton doublet. -/
def leptonDoubletProj (i : Fin 3) : FermionSpace →ₗ[ℂ] LeptonDoublet :=
  (LinearMap.proj i).comp (LinearMap.fst ℂ _ _)

/-- The projection onto the `i`-th generation of the charged-lepton singlet. -/
def leptonSingletProj (i : Fin 3) : FermionSpace →ₗ[ℂ] LeptonSinglet :=
  (LinearMap.proj i).comp ((LinearMap.fst ℂ _ _).comp (LinearMap.snd ℂ _ _))

/-- The projection onto the `i`-th generation of the quark doublet. -/
def quarkDoubletProj (i : Fin 3) : FermionSpace →ₗ[ℂ] QuarkDoublet :=
  (LinearMap.proj i).comp
    ((LinearMap.fst ℂ _ _).comp ((LinearMap.snd ℂ _ _).comp (LinearMap.snd ℂ _ _)))

/-- The projection onto the `i`-th generation of the up-type quark singlet. -/
def upSingletProj (i : Fin 3) : FermionSpace →ₗ[ℂ] UpSinglet :=
  (LinearMap.proj i).comp ((LinearMap.fst ℂ _ _).comp
    ((LinearMap.snd ℂ _ _).comp ((LinearMap.snd ℂ _ _).comp (LinearMap.snd ℂ _ _))))

/-- The projection onto the `i`-th generation of the down-type quark singlet. -/
def downSingletProj (i : Fin 3) : FermionSpace →ₗ[ℂ] DownSinglet :=
  (LinearMap.proj i).comp ((LinearMap.snd ℂ _ _).comp
    ((LinearMap.snd ℂ _ _).comp ((LinearMap.snd ℂ _ _).comp (LinearMap.snd ℂ _ _))))

/-!

### A.2. The inclusions onto the species

The one-sided inverses of the projections: the inclusion of a single species and generation
as a summand of the total target space, zero in every other slot. `…Proj i ∘ …Incl i` is the
identity, and every other composite of a projection with an inclusion vanishes.

-/

/-- The inclusion of the `i`-th generation lepton doublet as a summand. -/
def leptonDoubletIncl (i : Fin 3) : LeptonDoublet →ₗ[ℂ] FermionSpace :=
  (LinearMap.inl ℂ _ _).comp (LinearMap.single ℂ (fun _ : Fin 3 => LeptonDoublet) i)

/-- The inclusion of the `i`-th generation charged-lepton singlet as a summand. -/
def leptonSingletIncl (i : Fin 3) : LeptonSinglet →ₗ[ℂ] FermionSpace :=
  (LinearMap.inr ℂ _ _).comp ((LinearMap.inl ℂ _ _).comp
    (LinearMap.single ℂ (fun _ : Fin 3 => LeptonSinglet) i))

/-- The inclusion of the `i`-th generation quark doublet as a summand. -/
def quarkDoubletIncl (i : Fin 3) : QuarkDoublet →ₗ[ℂ] FermionSpace :=
  (LinearMap.inr ℂ _ _).comp ((LinearMap.inr ℂ _ _).comp
    ((LinearMap.inl ℂ _ _).comp
      (LinearMap.single ℂ (fun _ : Fin 3 => QuarkDoublet) i)))

/-- The inclusion of the `i`-th generation up-type quark singlet as a summand. -/
def upSingletIncl (i : Fin 3) : UpSinglet →ₗ[ℂ] FermionSpace :=
  (LinearMap.inr ℂ _ _).comp ((LinearMap.inr ℂ _ _).comp ((LinearMap.inr ℂ _ _).comp
    ((LinearMap.inl ℂ _ _).comp
      (LinearMap.single ℂ (fun _ : Fin 3 => UpSinglet) i))))

/-- The inclusion of the `i`-th generation down-type quark singlet as a summand. -/
def downSingletIncl (i : Fin 3) : DownSinglet →ₗ[ℂ] FermionSpace :=
  (LinearMap.inr ℂ _ _).comp ((LinearMap.inr ℂ _ _).comp ((LinearMap.inr ℂ _ _).comp
    ((LinearMap.inr ℂ _ _).comp
      (LinearMap.single ℂ (fun _ : Fin 3 => DownSinglet) i))))

@[simp]
lemma leptonDoubletProj_comp_leptonDoubletIncl (i : Fin 3) :
    (leptonDoubletProj i).comp (leptonDoubletIncl i) = LinearMap.id :=
  LinearMap.ext fun _ => by simp [leptonDoubletProj, leptonDoubletIncl]

@[simp]
lemma leptonSingletProj_comp_leptonSingletIncl (i : Fin 3) :
    (leptonSingletProj i).comp (leptonSingletIncl i) = LinearMap.id :=
  LinearMap.ext fun _ => by simp [leptonSingletProj, leptonSingletIncl]

@[simp]
lemma quarkDoubletProj_comp_quarkDoubletIncl (i : Fin 3) :
    (quarkDoubletProj i).comp (quarkDoubletIncl i) = LinearMap.id :=
  LinearMap.ext fun _ => by simp [quarkDoubletProj, quarkDoubletIncl]

@[simp]
lemma upSingletProj_comp_upSingletIncl (i : Fin 3) :
    (upSingletProj i).comp (upSingletIncl i) = LinearMap.id :=
  LinearMap.ext fun _ => by simp [upSingletProj, upSingletIncl]

@[simp]
lemma downSingletProj_comp_downSingletIncl (i : Fin 3) :
    (downSingletProj i).comp (downSingletIncl i) = LinearMap.id :=
  LinearMap.ext fun _ => by simp [downSingletProj, downSingletIncl]

/-!

### A.3. The action of the Lorentz group

-/

/-- The pointwise representation on a finite power of the representation space. -/
noncomputable def _root_.Representation.pi {k G V : Type*} (ι : Type*) [CommSemiring k]
    [Monoid G] [AddCommMonoid V] [Module k V] (ρ : Representation k G V) :
    Representation k G (ι → V) where
  toFun g := LinearMap.piMap fun _ => ρ g
  map_one' := by
    refine LinearMap.ext fun v => funext fun i => ?_
    simp
  map_mul' g₁ g₂ := by
    refine LinearMap.ext fun v => funext fun i => ?_
    simp [Module.End.mul_apply]

open Matrix MatrixGroups in
/-- The Lorentz action on the total fermionic target space: each species and generation
  transforms in its own Lorentz representation. -/
noncomputable def repLorentzGroup : Representation ℂ SL(2,ℂ) FermionSpace :=
  ((LeptonDoublet.repLorentzGroup.pi (Fin 3)).prod
    ((LeptonSinglet.repLorentzGroup.pi (Fin 3)).prod
      ((QuarkDoublet.repLorentzGroup.pi (Fin 3)).prod
        ((UpSinglet.repLorentzGroup.pi (Fin 3)).prod
          (DownSinglet.repLorentzGroup.pi (Fin 3))))))

/-!

### A.4. The action of the global gauge group

-/

/-- The global gauge action on the total fermionic target space: each species and
  generation transforms in its own representation of the gauge group. -/
noncomputable def repGaugeGroupI : Representation ℂ GaugeGroupI FermionSpace :=
  ((LeptonDoublet.repGaugeGroupI.pi (Fin 3)).prod
    ((LeptonSinglet.repGaugeGroupI.pi (Fin 3)).prod
      ((QuarkDoublet.repGaugeGroupI.pi (Fin 3)).prod
        ((UpSinglet.repGaugeGroupI.pi (Fin 3)).prod
          (DownSinglet.repGaugeGroupI.pi (Fin 3))))))

/-!

### A.5. The action of the jet gauge group

The jets of the total fermionic field split as the product of the jets of the species,
generation by generation; a jet of gauge transformations acts on each factor through the
species' own jet action. The identification is `JetRing`-linear, so the fibrewise
linearity of the species actions is inherited by the product.

-/

open TensorProduct in
/-- The jets of the total fermionic field as the product of the jets of the species and
  generations. The identification is `JetRing`-linear. -/
noncomputable def jetEquiv :
    JetRing ⊗[ℂ] FermionSpace ≃ₗ[JetRing]
      (Fin 3 → JetRing ⊗[ℂ] LeptonDoublet) ×
        ((Fin 3 → JetRing ⊗[ℂ] LeptonSinglet) ×
          ((Fin 3 → JetRing ⊗[ℂ] QuarkDoublet) ×
            ((Fin 3 → JetRing ⊗[ℂ] UpSinglet) ×
              (Fin 3 → JetRing ⊗[ℂ] DownSinglet)))) :=
  (TensorProduct.prodRight ℂ JetRing JetRing _ _).trans <|
    LinearEquiv.prodCongr (TensorProduct.piRight ℂ JetRing JetRing _) <|
      (TensorProduct.prodRight ℂ JetRing JetRing _ _).trans <|
        LinearEquiv.prodCongr (TensorProduct.piRight ℂ JetRing JetRing _) <|
          (TensorProduct.prodRight ℂ JetRing JetRing _ _).trans <|
            LinearEquiv.prodCongr (TensorProduct.piRight ℂ JetRing JetRing _) <|
              (TensorProduct.prodRight ℂ JetRing JetRing _ _).trans <|
                LinearEquiv.prodCongr (TensorProduct.piRight ℂ JetRing JetRing _)
                  (TensorProduct.piRight ℂ JetRing JetRing _)

open TensorProduct in
/-- The map through which a jet of gauge transformations acts on the jets of the total
  fermionic field: the species actions, factor by factor. -/
noncomputable def jetActionMap (U : JetGaugeGroupI) :
    ((Fin 3 → JetRing ⊗[ℂ] LeptonDoublet) ×
      ((Fin 3 → JetRing ⊗[ℂ] LeptonSinglet) ×
        ((Fin 3 → JetRing ⊗[ℂ] QuarkDoublet) ×
          ((Fin 3 → JetRing ⊗[ℂ] UpSinglet) ×
            (Fin 3 → JetRing ⊗[ℂ] DownSinglet))))) →ₗ[ℂ]
    ((Fin 3 → JetRing ⊗[ℂ] LeptonDoublet) ×
      ((Fin 3 → JetRing ⊗[ℂ] LeptonSinglet) ×
        ((Fin 3 → JetRing ⊗[ℂ] QuarkDoublet) ×
          ((Fin 3 → JetRing ⊗[ℂ] UpSinglet) ×
            (Fin 3 → JetRing ⊗[ℂ] DownSinglet))))) :=
  LinearMap.prodMap (LinearMap.piMap fun _ => LeptonDoublet.repJetGaugeGroupI U)
    (LinearMap.prodMap (LinearMap.piMap fun _ => LeptonSinglet.repJetGaugeGroupI U)
      (LinearMap.prodMap (LinearMap.piMap fun _ => QuarkDoublet.repJetGaugeGroupI U)
        (LinearMap.prodMap (LinearMap.piMap fun _ => UpSinglet.repJetGaugeGroupI U)
          (LinearMap.piMap fun _ => DownSinglet.repJetGaugeGroupI U))))

/-- The pointwise lift of the identity maps is the identity. -/
lemma _root_.LinearMap.piMap_id {R ι : Type*} {φ : ι → Type*} [Semiring R]
    [∀ i, AddCommMonoid (φ i)] [∀ i, Module R (φ i)] :
    LinearMap.piMap (fun i => (LinearMap.id : φ i →ₗ[R] φ i)) = LinearMap.id :=
  LinearMap.ext fun _ => funext fun _ => rfl

/-- The pointwise lift of compositions is the composition of the pointwise lifts. -/
lemma _root_.LinearMap.piMap_comp_piMap {R ι : Type*} {φ ψ ω : ι → Type*} [Semiring R]
    [∀ i, AddCommMonoid (φ i)] [∀ i, Module R (φ i)]
    [∀ i, AddCommMonoid (ψ i)] [∀ i, Module R (ψ i)]
    [∀ i, AddCommMonoid (ω i)] [∀ i, Module R (ω i)]
    (f : ∀ i, ψ i →ₗ[R] ω i) (g : ∀ i, φ i →ₗ[R] ψ i) :
    (LinearMap.piMap f).comp (LinearMap.piMap g)
      = LinearMap.piMap fun i => (f i).comp (g i) :=
  LinearMap.ext fun _ => funext fun _ => rfl

open TensorProduct in
/-- The map of jets of the identity is the identity. -/
lemma jetActionMap_one : jetActionMap 1 = LinearMap.id := by
  rw [jetActionMap]
  simp only [map_one, Module.End.one_eq_id, LinearMap.piMap_id, LinearMap.prodMap_id]

open TensorProduct in
/-- The map of jets of a product is the composition of the maps of jets. -/
lemma jetActionMap_mul (U V : JetGaugeGroupI) :
    jetActionMap (U * V) = (jetActionMap U).comp (jetActionMap V) := by
  rw [jetActionMap, jetActionMap, jetActionMap, LinearMap.prodMap_comp,
    LinearMap.prodMap_comp, LinearMap.prodMap_comp, LinearMap.prodMap_comp,
    LinearMap.piMap_comp_piMap, LinearMap.piMap_comp_piMap, LinearMap.piMap_comp_piMap,
    LinearMap.piMap_comp_piMap, LinearMap.piMap_comp_piMap]
  simp only [map_mul, Module.End.mul_eq_comp]

open TensorProduct in
set_option maxRecDepth 4000 in
/-- **The jet gauge action on the jets of the total fermionic field**: the species
  actions, transported through the splitting of the jets. -/
noncomputable def repJetGaugeGroupI :
    Representation ℂ JetGaugeGroupI (JetRing ⊗[ℂ] FermionSpace) where
  toFun U := (jetEquiv.restrictScalars ℂ).symm.toLinearMap ∘ₗ jetActionMap U ∘ₗ
    (jetEquiv.restrictScalars ℂ).toLinearMap
  map_one' := by
    refine LinearMap.ext fun z => ?_
    show (jetEquiv.restrictScalars ℂ).symm (jetActionMap 1
      ((jetEquiv.restrictScalars ℂ) z)) = z
    rw [jetActionMap_one, LinearMap.id_apply]
    exact (jetEquiv.restrictScalars ℂ).symm_apply_apply z
  map_mul' U V := by
    refine LinearMap.ext fun z => ?_
    show (jetEquiv.restrictScalars ℂ).symm (jetActionMap (U * V)
        ((jetEquiv.restrictScalars ℂ) z))
      = (jetEquiv.restrictScalars ℂ).symm (jetActionMap U ((jetEquiv.restrictScalars ℂ)
          ((jetEquiv.restrictScalars ℂ).symm (jetActionMap V
            ((jetEquiv.restrictScalars ℂ) z)))))
    rw [(jetEquiv.restrictScalars ℂ).apply_symm_apply, jetActionMap_mul,
      LinearMap.comp_apply]

open TensorProduct in
set_option maxRecDepth 4000 in
/-- **The jet gauge action on the jets of the total fermionic field is fibrewise**: it
  commutes with multiplication by scalar jets, because the splitting of the jets is
  `JetRing`-linear and each species action is fibrewise. -/
lemma repJetGaugeGroupI_smul (U : JetGaugeGroupI) (χ : JetRing)
    (z : JetRing ⊗[ℂ] FermionSpace) :
    repJetGaugeGroupI U (χ • z) = χ • repJetGaugeGroupI U z := by
  have hact : ∀ w, jetActionMap U (χ • w) = χ • jetActionMap U w := by
    intro w
    refine Prod.ext (funext fun i => ?_) (Prod.ext (funext fun i => ?_)
      (Prod.ext (funext fun i => ?_) (Prod.ext (funext fun i => ?_)
        (funext fun i => ?_))))
    · exact LeptonDoublet.repJetGaugeGroupI_smul U χ _
    · exact LeptonSinglet.repJetGaugeGroupI_smul U χ _
    · exact QuarkDoublet.repJetGaugeGroupI_smul U χ _
    · exact UpSinglet.repJetGaugeGroupI_smul U χ _
    · exact DownSinglet.repJetGaugeGroupI_smul U χ _
  show (jetEquiv.restrictScalars ℂ).symm (jetActionMap U
      ((jetEquiv.restrictScalars ℂ) (χ • z)))
    = χ • (jetEquiv.restrictScalars ℂ).symm (jetActionMap U
        ((jetEquiv.restrictScalars ℂ) z))
  rw [show (jetEquiv.restrictScalars ℂ) (χ • z) = χ • (jetEquiv.restrictScalars ℂ) z from
      map_smul jetEquiv χ z,
    hact,
    show (jetEquiv.restrictScalars ℂ).symm (χ • jetActionMap U
        ((jetEquiv.restrictScalars ℂ) z))
      = χ • (jetEquiv.restrictScalars ℂ).symm (jetActionMap U
          ((jetEquiv.restrictScalars ℂ) z)) from
      map_smul jetEquiv.symm χ _]

end FermionSpace

/-!

## B. The fermionic jet algebra

-/

/-- **The jet algebra of the Standard Model fermions**: the exterior product of the fermionic
  algebras of the five species, realized as the fermionic algebra of their direct sum. Its
  generators are the component functions `∂_s ψ_φ` and `∂_s ψ̄_φ` of every species and
  generation, and any two of them anticommute — within a species and across species alike.

  This is the fermionic factor of the full Standard Model jet algebra; the gauge and Higgs
  factors are bosonic and commute with it. -/
abbrev FermionJetAlgebra : Type := FermionicAlgebra FermionSpace

namespace FermionJetAlgebra

/-!

### B.1. The component functions of each species

Each species and generation enters through its projection out of `FermionSpace`: a covector
on the species pulls back to a covector on the total target space, and thence to a generator
of the jet algebra. Their iterated derivatives `FermionicAlgebra.iteratedJetDeriv` are the
higher generators.

-/

/-- The component functions of the `i`-th generation lepton doublet inside the Standard
  Model jet algebra. -/
noncomputable def ofLeptonDoublet (i : Fin 3) :
    Module.Dual ℂ LeptonDoublet →ₗ[ℂ] FermionJetAlgebra :=
  FermionicAlgebra.ofField.comp (Module.Dual.transpose (FermionSpace.leptonDoubletProj i))

/-- The component functions of the `i`-th generation charged-lepton singlet. -/
noncomputable def ofLeptonSinglet (i : Fin 3) :
    Module.Dual ℂ LeptonSinglet →ₗ[ℂ] FermionJetAlgebra :=
  FermionicAlgebra.ofField.comp (Module.Dual.transpose (FermionSpace.leptonSingletProj i))

/-- The component functions of the `i`-th generation quark doublet. -/
noncomputable def ofQuarkDoublet (i : Fin 3) :
    Module.Dual ℂ QuarkDoublet →ₗ[ℂ] FermionJetAlgebra :=
  FermionicAlgebra.ofField.comp (Module.Dual.transpose (FermionSpace.quarkDoubletProj i))

/-- The component functions of the `i`-th generation up-type quark singlet. -/
noncomputable def ofUpSinglet (i : Fin 3) :
    Module.Dual ℂ UpSinglet →ₗ[ℂ] FermionJetAlgebra :=
  FermionicAlgebra.ofField.comp (Module.Dual.transpose (FermionSpace.upSingletProj i))

/-- The component functions of the `i`-th generation down-type quark singlet. -/
noncomputable def ofDownSinglet (i : Fin 3) :
    Module.Dual ℂ DownSinglet →ₗ[ℂ] FermionJetAlgebra :=
  FermionicAlgebra.ofField.comp (Module.Dual.transpose (FermionSpace.downSingletProj i))

/-- The conjugate component functions of the `i`-th generation lepton doublet. -/
noncomputable def ofConjLeptonDoublet (i : Fin 3) :
    Module.Dual ℂ (ConjModule LeptonDoublet) →ₗ[ℂ] FermionJetAlgebra :=
  FermionicAlgebra.ofConjField.comp
    (Module.Dual.transpose (ConjModule.map (FermionSpace.leptonDoubletProj i)))

/-- The conjugate component functions of the `i`-th generation charged-lepton singlet. -/
noncomputable def ofConjLeptonSinglet (i : Fin 3) :
    Module.Dual ℂ (ConjModule LeptonSinglet) →ₗ[ℂ] FermionJetAlgebra :=
  FermionicAlgebra.ofConjField.comp
    (Module.Dual.transpose (ConjModule.map (FermionSpace.leptonSingletProj i)))

/-- The conjugate component functions of the `i`-th generation quark doublet. -/
noncomputable def ofConjQuarkDoublet (i : Fin 3) :
    Module.Dual ℂ (ConjModule QuarkDoublet) →ₗ[ℂ] FermionJetAlgebra :=
  FermionicAlgebra.ofConjField.comp
    (Module.Dual.transpose (ConjModule.map (FermionSpace.quarkDoubletProj i)))

/-- The conjugate component functions of the `i`-th generation up-type quark singlet. -/
noncomputable def ofConjUpSinglet (i : Fin 3) :
    Module.Dual ℂ (ConjModule UpSinglet) →ₗ[ℂ] FermionJetAlgebra :=
  FermionicAlgebra.ofConjField.comp
    (Module.Dual.transpose (ConjModule.map (FermionSpace.upSingletProj i)))

/-- The conjugate component functions of the `i`-th generation down-type quark singlet. -/
noncomputable def ofConjDownSinglet (i : Fin 3) :
    Module.Dual ℂ (ConjModule DownSinglet) →ₗ[ℂ] FermionJetAlgebra :=
  FermionicAlgebra.ofConjField.comp
    (Module.Dual.transpose (ConjModule.map (FermionSpace.downSingletProj i)))

/-!

### B.2. The exterior product decomposition

`FermionicAlgebra.prodEquiv` identifies the fermionic algebra of a direct sum with the
graded tensor product of the two fermionic algebras. Applied repeatedly it exhibits the jet
algebra as the exterior product of the five species algebras, peeling off one species — all
three of its generations at once — at a time. It has to be stated one species at a time:
`GradedTensorProduct` carries no `GradedAlgebra` instance in Mathlib, so the fully nested
five-fold graded tensor product is not expressible as a type.

-/

open scoped TensorProduct

/-- The fermionic jet algebra as the exterior product of the three-generation
  lepton-doublet algebra with the algebra of the remaining four species. -/
noncomputable def exteriorProductLeptonDoublet :
    FermionJetAlgebra ≃ₐ[ℂ] (FermionicAlgebra.evenOdd (Fin 3 → LeptonDoublet) ᵍ⊗[ℂ]
      FermionicAlgebra.evenOdd ((Fin 3 → LeptonSinglet) × (Fin 3 → QuarkDoublet) ×
        (Fin 3 → UpSinglet) × (Fin 3 → DownSinglet))) :=
  FermionicAlgebra.prodEquiv _ _

/-- The charged-lepton singlets split off the remaining three species. -/
noncomputable def exteriorProductLeptonSinglet :
    FermionicAlgebra ((Fin 3 → LeptonSinglet) × (Fin 3 → QuarkDoublet) ×
        (Fin 3 → UpSinglet) × (Fin 3 → DownSinglet)) ≃ₐ[ℂ]
      (FermionicAlgebra.evenOdd (Fin 3 → LeptonSinglet) ᵍ⊗[ℂ]
        FermionicAlgebra.evenOdd ((Fin 3 → QuarkDoublet) × (Fin 3 → UpSinglet) ×
          (Fin 3 → DownSinglet))) :=
  FermionicAlgebra.prodEquiv _ _

/-- The quark doublets split off the two quark singlets. -/
noncomputable def exteriorProductQuarkDoublet :
    FermionicAlgebra ((Fin 3 → QuarkDoublet) × (Fin 3 → UpSinglet) ×
        (Fin 3 → DownSinglet)) ≃ₐ[ℂ]
      (FermionicAlgebra.evenOdd (Fin 3 → QuarkDoublet) ᵍ⊗[ℂ]
        FermionicAlgebra.evenOdd ((Fin 3 → UpSinglet) × (Fin 3 → DownSinglet))) :=
  FermionicAlgebra.prodEquiv _ _

/-- The two quark singlets as an exterior product. -/
noncomputable def exteriorProductUpSinglet :
    FermionicAlgebra ((Fin 3 → UpSinglet) × (Fin 3 → DownSinglet)) ≃ₐ[ℂ]
      (FermionicAlgebra.evenOdd (Fin 3 → UpSinglet) ᵍ⊗[ℂ]
        FermionicAlgebra.evenOdd (Fin 3 → DownSinglet)) :=
  FermionicAlgebra.prodEquiv _ _

/-!

### B.3. The actions on the fermionic jet algebra

-/

open Matrix MatrixGroups in
/-- The Lorentz action on the fermionic jet algebra of the Standard Model. -/
noncomputable def repLorentzGroup : Representation ℂ SL(2,ℂ) FermionJetAlgebra :=
  FermionicAlgebra.repLorentzGroup FermionSpace.repLorentzGroup

/-- The jet gauge action on the fermionic jet algebra of the Standard Model. -/
noncomputable def repJetGaugeGroupI : Representation ℂ JetGaugeGroupI FermionJetAlgebra :=
  FermionicAlgebra.repJetGaugeGroupI FermionSpace.repJetGaugeGroupI
    FermionSpace.repJetGaugeGroupI_smul

/-- The global gauge action on the fermionic jet algebra of the Standard Model. -/
noncomputable def repGaugeGroupI : Representation ℂ GaugeGroupI FermionJetAlgebra :=
  FermionicAlgebra.repGaugeGroupI FermionSpace.repJetGaugeGroupI
    FermionSpace.repJetGaugeGroupI_smul

/-!

### B.4. The mass-dimension scaling

-/

/-- The mass-dimension scaling on the fermionic jet algebra: every Standard Model fermion
  has mass dimension `3/2`, that is mass weight three, and each derivative adds mass
  weight two. -/
noncomputable def massWeightScale (c : ℂ) : FermionJetAlgebra →ₐ[ℂ] FermionJetAlgebra :=
  FermionicAlgebra.massWeightScale 3 c

end FermionJetAlgebra

end StandardModel
