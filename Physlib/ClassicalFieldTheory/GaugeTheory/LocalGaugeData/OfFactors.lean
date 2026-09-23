/-
Copyright (c) 2026 Jinzheng Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jinzheng Li
-/
module

public import Physlib.ClassicalFieldTheory.GaugeTheory.LocalGaugeData.SU.Basic
public import Physlib.ClassicalFieldTheory.GaugeTheory.LocalGaugeData.U1
public import Physlib.ClassicalFieldTheory.GaugeTheory.LocalGaugeData.Prod
public import Physlib.ClassicalFieldTheory.GaugeTheory.MatterField.MatrixRep.Table
/-!
# Local gauge data from a list of factors

## i. Overview

A gauge group is named, as in a model-building table, by a list of symbols `U1` and
`SU n`. This file builds the local gauge data of such a list: the product, in the order of
the list, of the local gauge data `LocalGaugeData.u1` and `LocalGaugeData.su n` of the
factors. The carriers are the corresponding products of `JetU1` and `JetSU n`, and of
their Lie algebras, so that a model's gauge group is a concrete product of matrix groups.
The list of factors of the product, in the sense of the table layer, is assembled from
the canonical factors of the pieces (`Factors.factors`), and the product of faithful
packages is faithful.

With this, a model on any gauge group built from `U(1)` and `SU(n)` factors is a table
alone: `LocalGaugeData.ofFactors Γ` is its gauge data and `Factors.factors Γ` is what its
rows are charged under.

## ii. Key results

- `LocalGaugeData.FactorSpec` : the symbols `U1` and `SU n`.
- `LocalGaugeData.ofFactors` : the local gauge data of a list of factors.
- `LocalGaugeData.Factors.factors` : the canonical factors of that gauge data.

## iii. Table of contents

- A. Factor symbols and their gauge data
- B. The carriers of a list of factors
- C. The gauge data of a list of factors
- D. The canonical factors

-/

@[expose] public section

namespace LocalGaugeData

/-!

## A. Factor symbols and their gauge data

-/

/-- **A factor symbol**: `U(1)` or `SU(n)`. -/
inductive FactorSpec
  /-- The factor `U(1)`. -/
  | U1
  /-- The factor `SU(n)`. -/
  | SU (n : ℕ)
  deriving DecidableEq, Repr

namespace FactorSpec

/-- The group of jets of a factor. -/
def G : FactorSpec → Type
  | .U1 => JetU1
  | .SU n => JetSU n

/-- The Lie algebra of a factor. -/
def 𝔤 : FactorSpec → Type
  | .U1 => U1Algebra
  | .SU n => SUAlgebra n

/-- The group of a factor. -/
def G₀ : FactorSpec → Type
  | .U1 => _root_.U1
  | .SU n => _root_.SU n

/-- The jets of the Lie algebra of a factor. -/
def 𝔤J : FactorSpec → Type
  | .U1 => JetU1Algebra
  | .SU n => JetSUAlgebra n

noncomputable instance instGroupG : (f : FactorSpec) → Group f.G
  | .U1 => inferInstanceAs (Group JetU1)
  | .SU n => inferInstanceAs (Group (JetSU n))

noncomputable instance instGroupG₀ : (f : FactorSpec) → Group f.G₀
  | .U1 => inferInstanceAs (Group _root_.U1)
  | .SU n => inferInstanceAs (Group (_root_.SU n))

noncomputable instance instLieRing𝔤 : (f : FactorSpec) → LieRing f.𝔤
  | .U1 => inferInstanceAs (LieRing U1Algebra)
  | .SU n => inferInstanceAs (LieRing (SUAlgebra n))

noncomputable instance instLieAlgebra𝔤 : (f : FactorSpec) → LieAlgebra ℝ f.𝔤
  | .U1 => inferInstanceAs (LieAlgebra ℝ U1Algebra)
  | .SU n => inferInstanceAs (LieAlgebra ℝ (SUAlgebra n))

noncomputable instance instLieRing𝔤J : (f : FactorSpec) → LieRing f.𝔤J
  | .U1 => inferInstanceAs (LieRing JetU1Algebra)
  | .SU n => inferInstanceAs (LieRing (JetSUAlgebra n))

noncomputable instance instLieAlgebra𝔤J : (f : FactorSpec) → LieAlgebra ℝ f.𝔤J
  | .U1 => inferInstanceAs (LieAlgebra ℝ JetU1Algebra)
  | .SU n => inferInstanceAs (LieAlgebra ℝ (JetSUAlgebra n))

noncomputable instance instFinite𝔤 : (f : FactorSpec) → Module.Finite ℝ f.𝔤
  | .U1 => inferInstanceAs (Module.Finite ℝ U1Algebra)
  | .SU n => inferInstanceAs (Module.Finite ℝ (SUAlgebra n))

/-- The local gauge data of a factor. -/
noncomputable abbrev data : (f : FactorSpec) → LocalGaugeData f.G₀ f.𝔤 f.G f.𝔤J
  | .U1 => u1
  | .SU n => su n

/-- The canonical factor of the local gauge data of a factor symbol. -/
noncomputable abbrev factor : (f : FactorSpec) → Factor f.data
  | .U1 => .U1 u1Factor
  | .SU n => .SU (suFactor n)

noncomputable instance instFaithfulData : (f : FactorSpec) → f.data.Faithful
  | .U1 => inferInstanceAs u1.Faithful
  | .SU n => inferInstanceAs (su n).Faithful

end FactorSpec

/-!

## B. The carriers of a list of factors

The carriers of a list of factors are the products, in the order of the list, of the
carriers of the factors; a one-element list has the carriers of its factor. The carriers
are definitions rather than abbreviations, so that instance search on them goes through
the instances below rather than through the unfolded products: this keeps the instances
found at every use site identical to those inside the gauge data.

-/

namespace Factors

/-- The group of jets of a list of factors. -/
def G : List FactorSpec → Type
  | [] => Unit
  | [f] => f.G
  | f :: g :: gs => f.G × G (g :: gs)

/-- The Lie algebra of a list of factors. -/
def 𝔤 : List FactorSpec → Type
  | [] => Unit
  | [f] => f.𝔤
  | f :: g :: gs => f.𝔤 × 𝔤 (g :: gs)

/-- The group of a list of factors. -/
def G₀ : List FactorSpec → Type
  | [] => Unit
  | [f] => f.G₀
  | f :: g :: gs => f.G₀ × G₀ (g :: gs)

/-- The jets of the Lie algebra of a list of factors. -/
def 𝔤J : List FactorSpec → Type
  | [] => Unit
  | [f] => f.𝔤J
  | f :: g :: gs => f.𝔤J × 𝔤J (g :: gs)

TODO (lines := 142-166) (date := 2026-09-11) "These could all
  likely be defined with the typical List.foldr construction, or List.prod of similar."

instance : Bracket Unit Unit := ⟨fun _ _ => ()⟩

instance : LieRing Unit where
  add_lie _ _ _ := rfl
  lie_add _ _ _ := rfl
  lie_self _ := rfl
  leibniz_lie _ _ _ := rfl

instance : LieAlgebra ℝ Unit where
  lie_smul _ _ _ := rfl

@[instance_reducible]
noncomputable def instGroupG : (Γ : List FactorSpec) → Group (G Γ)
  | [] => inferInstanceAs (Group Unit)
  | [f] => inferInstanceAs (Group f.G)
  | f :: g :: gs =>
    letI := instGroupG (g :: gs)
    inferInstanceAs (Group (f.G × G (g :: gs)))

noncomputable instance (Γ : List FactorSpec) : Group (G Γ) := instGroupG Γ

@[instance_reducible]
noncomputable def instGroupG₀ : (Γ : List FactorSpec) → Group (G₀ Γ)
  | [] => inferInstanceAs (Group Unit)
  | [f] => inferInstanceAs (Group f.G₀)
  | f :: g :: gs =>
    letI := instGroupG₀ (g :: gs)
    inferInstanceAs (Group (f.G₀ × G₀ (g :: gs)))

noncomputable instance (Γ : List FactorSpec) : Group (G₀ Γ) := instGroupG₀ Γ

@[instance_reducible]
noncomputable def instLieRing𝔤 : (Γ : List FactorSpec) → LieRing (𝔤 Γ)
  | [] => inferInstanceAs (LieRing Unit)
  | [f] => inferInstanceAs (LieRing f.𝔤)
  | f :: g :: gs =>
    letI := instLieRing𝔤 (g :: gs)
    inferInstanceAs (LieRing (f.𝔤 × 𝔤 (g :: gs)))

noncomputable instance (Γ : List FactorSpec) : LieRing (𝔤 Γ) := instLieRing𝔤 Γ

@[instance_reducible]
noncomputable def instLieAlgebra𝔤 : (Γ : List FactorSpec) → LieAlgebra ℝ (𝔤 Γ)
  | [] => inferInstanceAs (LieAlgebra ℝ Unit)
  | [f] => inferInstanceAs (LieAlgebra ℝ f.𝔤)
  | f :: g :: gs =>
    letI := instLieRing𝔤 (g :: gs)
    letI := instLieAlgebra𝔤 (g :: gs)
    inferInstanceAs (LieAlgebra ℝ (f.𝔤 × 𝔤 (g :: gs)))

noncomputable instance (Γ : List FactorSpec) : LieAlgebra ℝ (𝔤 Γ) := instLieAlgebra𝔤 Γ

@[instance_reducible]
noncomputable def instLieRing𝔤J : (Γ : List FactorSpec) → LieRing (𝔤J Γ)
  | [] => inferInstanceAs (LieRing Unit)
  | [f] => inferInstanceAs (LieRing f.𝔤J)
  | f :: g :: gs =>
    letI := instLieRing𝔤J (g :: gs)
    inferInstanceAs (LieRing (f.𝔤J × 𝔤J (g :: gs)))

noncomputable instance (Γ : List FactorSpec) : LieRing (𝔤J Γ) := instLieRing𝔤J Γ

@[instance_reducible]
noncomputable def instLieAlgebra𝔤J : (Γ : List FactorSpec) → LieAlgebra ℝ (𝔤J Γ)
  | [] => inferInstanceAs (LieAlgebra ℝ Unit)
  | [f] => inferInstanceAs (LieAlgebra ℝ f.𝔤J)
  | f :: g :: gs =>
    letI := instLieRing𝔤J (g :: gs)
    letI := instLieAlgebra𝔤J (g :: gs)
    inferInstanceAs (LieAlgebra ℝ (f.𝔤J × 𝔤J (g :: gs)))

noncomputable instance (Γ : List FactorSpec) : LieAlgebra ℝ (𝔤J Γ) := instLieAlgebra𝔤J Γ

instance instFinite𝔤 : (Γ : List FactorSpec) → Module.Finite ℝ (𝔤 Γ)
  | [] => inferInstanceAs (Module.Finite ℝ Unit)
  | [f] => inferInstanceAs (Module.Finite ℝ f.𝔤)
  | f :: g :: gs =>
    letI := instLieRing𝔤 (g :: gs)
    letI := instLieAlgebra𝔤 (g :: gs)
    letI := instFinite𝔤 (g :: gs)
    inferInstanceAs (Module.Finite ℝ (f.𝔤 × 𝔤 (g :: gs)))

end Factors

/-!

## C. The gauge data of a list of factors

-/

/-- The trivial local gauge data, of the empty list of factors. -/
noncomputable def trivial : LocalGaugeData Unit Unit Unit Unit where
  eval := 1
  ofConstant := 1
  eval_ofConstant _ := rfl
  evalLie := 0
  ofConstantLie := 0
  ofConstantLie_lie _ _ := rfl
  evalLie_ofConstantLie _ := rfl
  deriv _ := 0
  deriv_comm _ _ _ := rfl
  deriv_bracket _ _ _ := rfl
  deriv_ofConstantLie _ _ := rfl
  coord _ := 0
  deriv_coord _ _ _ := rfl
  evalLie_coord _ _ := rfl
  coord_lie _ _ _ := rfl
  adjoint := 1
  adjoint_lie _ _ _ := rfl
  adjointValue := 1
  evalLie_adjoint _ _ := rfl
  maurerCartan _ _ := ()
  maurerCartan_ofConstant _ _ := rfl
  maurerCartan_cocycle _ _ _ := rfl
  maurerCartan_structure _ _ _ := rfl
  deriv_adjoint _ _ _ := rfl

instance instFaithfulTrivial : trivial.Faithful where
  ext_of_evalLie_iteratedDeriv _ := rfl
  eq_ofConstant_of_maurerCartan_eq_zero _ := rfl

open Factors in
/-- **The local gauge data of a list of factors**: the product, in the order of the list,
  of the local gauge data of the factors. -/
noncomputable def ofFactors : (Γ : List FactorSpec) → LocalGaugeData (G₀ Γ) (𝔤 Γ) (G Γ) (𝔤J Γ)
  | [] => trivial
  | [f] => f.data
  | f :: g :: gs => f.data.prod (ofFactors (g :: gs))

@[simp]
lemma ofFactors_nil : ofFactors [] = trivial := rfl

@[simp]
lemma ofFactors_singleton (f : FactorSpec) : ofFactors [f] = f.data := rfl

@[simp]
lemma ofFactors_cons_cons (f g : FactorSpec) (gs : List FactorSpec) :
    ofFactors (f :: g :: gs) = f.data.prod (ofFactors (g :: gs)) := rfl

/-- The local gauge data of a list of factors is faithful. -/
noncomputable instance instFaithfulOfFactors : (Γ : List FactorSpec) → (ofFactors Γ).Faithful
  | [] => inferInstanceAs trivial.Faithful
  | [f] => inferInstanceAs f.data.Faithful
  | f :: g :: gs =>
    letI := instFaithfulOfFactors (g :: gs)
    inferInstanceAs (f.data.prod (ofFactors (g :: gs))).Faithful

/-!

## D. The canonical factors

-/

variable {G₁ : Type} [Group G₁] {𝔤₁ : Type} [LieRing 𝔤₁] [LieAlgebra ℝ 𝔤₁]
  {G₀₁ : Type} [Group G₀₁] {𝔤J₁ : Type} [LieRing 𝔤J₁] [LieAlgebra ℝ 𝔤J₁]
  {G₂ : Type} [Group G₂] {𝔤₂ : Type} [LieRing 𝔤₂] [LieAlgebra ℝ 𝔤₂]
  {G₀₂ : Type} [Group G₀₂] {𝔤J₂ : Type} [LieRing 𝔤J₂] [LieAlgebra ℝ 𝔤J₂]
  {j₁ : LocalGaugeData G₀₁ 𝔤₁ G₁ 𝔤J₁} {j₂ : LocalGaugeData G₀₂ 𝔤₂ G₂ 𝔤J₂}

/-- A factor of the first gauge data, as a factor of the product. -/
noncomputable abbrev Factor.inl : Factor j₁ → Factor (j₁.prod j₂)
  | .U1 F => .U1 F.inl
  | .SU F => .SU F.inl

/-- A factor of the second gauge data, as a factor of the product. -/
noncomputable abbrev Factor.inr : Factor j₂ → Factor (j₁.prod j₂)
  | .U1 F => .U1 F.inr
  | .SU F => .SU F.inr

/-- The factors of the second gauge data, as factors of the product. -/
noncomputable abbrev Factors.inr : Factors j₂ → Factors (j₁.prod j₂)
  | [] => []
  | F :: Fs => F.inr :: Factors.inr Fs

/-- **The canonical factors** of the local gauge data of a list of factors. -/
noncomputable abbrev Factors.factors : (Γ : List FactorSpec) → Factors (ofFactors Γ)
  | [] => []
  | [f] => [f.factor]
  | f :: g :: gs => f.factor.inl :: Factors.inr (Factors.factors (g :: gs))

end LocalGaugeData
