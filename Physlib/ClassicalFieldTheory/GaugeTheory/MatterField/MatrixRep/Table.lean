/-
Copyright (c) 2026 Jinzheng Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jinzheng Li
-/
module

public import Physlib.ClassicalFieldTheory.GaugeTheory.MatterField.MatrixRep.Factors
public import Physlib.ClassicalFieldTheory.GaugeTheory.GaugeFieldData.Basic
public import Physlib.Relativity.Fermions.Weyl.LeftHanded
public import Physlib.Relativity.Fermions.Weyl.RightHanded
/-!
# Model tables

## i. Overview

A gauge-theory model is written down, as in a model-building tool, as a *table*: the gauge
group as a list of factors, and for each field its number of generations, its Lorentz
label and one charge per factor — an integer charge under a `U(1)` factor, a
representation label under an `SU(n)` factor.

This file defines the tables over any local gauge data and compiles them into the general
theory. A gauge group is a list of `Factor`s, each a `U1Factor` or an `SUFactor` of the
local gauge data; the charges of a field form the tuple `Charges Γ` over the list; the
charges name a matrix representation `Charges.rep`, assembled from the factors by the
hypercharge twist and the Kronecker product; a field is its Lorentz label and its charges,
`MatterFieldData Γ`, so that it reads `(.L, .singlet, .fund, -3)`, and compiles to a
`MatterField`; the field data of a model, `FieldData Γ Fields`, assigns each field its
number of generations and its data, and compiles to a `GaugeFieldData`.

## ii. Key results

- `LocalGaugeData.Factor`, `Factors` : a gauge group presented as a list of factors.
- `SURep`, `Charges` : the charge labels of a row and the charge tuple.
- `Charges.rep` : the matrix representation named by a charge tuple.
- `LorentzLabel`, `MatterFieldData` : the Lorentz label and the data of a field.
- `MatterFieldData.toMatterField`, `toMatterFieldOn` : the matter field of a datum, on the
  tensor-product target space or on any target space presented as one.
- `FieldData`, `FieldData.toGaugeFieldData` : the field data of a model and its compilation.
- `FieldData.toGaugeFieldData_gaugeLorentzCompatible` : the field content of a model
  satisfies `GaugeFieldData.GaugeLorentzCompatible`.

## iii. Table of contents

- A. Factors and charge labels
- B. Charge tuples and their internal index
- C. The representation named by a charge tuple
- D. Matter field data and its matter field
- E. The field data of a model and its field content

-/

@[expose] public section

open Matrix MatrixGroups TensorProduct

namespace LocalGaugeData

variable {G₀ : Type} [Group G₀] {𝔤 : Type} [LieRing 𝔤] [LieAlgebra ℝ 𝔤]
  {GJ : Type} [Group GJ] {𝔤J : Type} [LieRing 𝔤J] [LieAlgebra ℝ 𝔤J]

/-!

## A. Factors and charge labels

-/

/-- **A factor of the gauge group**, presented in the local gauge data: a `U(1)` factor or
  an `SU(n)` factor. -/
inductive Factor (jets : LocalGaugeData G₀ 𝔤 GJ 𝔤J)
  /-- A `U(1)` factor. -/
  | U1 (F : U1Factor jets)
  /-- An `SU(n)` factor. -/
  | SU {n : ℕ} (F : SUFactor jets (Fin n))

/-- **A gauge group presented by its factors.** -/
abbrev Factors (jets : LocalGaugeData G₀ 𝔤 GJ 𝔤J) : Type := List (Factor jets)

/-- **A representation label under `SU(n)`.** -/
inductive SURep
  /-- The singlet `1`. -/
  | singlet
  /-- The fundamental `n`. -/
  | fund
  /-- The antifundamental `n̄`. -/
  | antifund
  deriving DecidableEq, Repr

/-- The dimension of the representation of `SU(n)` a label names. -/
abbrev SURep.dim (n : ℕ) : SURep → ℕ
  | .singlet => 1
  | .fund => n
  | .antifund => n

variable {jets : LocalGaugeData G₀ 𝔤 GJ 𝔤J}

/-- The matrix representation of an `SU(n)` factor named by a label. -/
noncomputable def SURep.rep {n : ℕ} (F : SUFactor jets (Fin n)) :
    (r : SURep) → MatrixRep jets (Fin (r.dim n))
  | .singlet => MatrixRep.trivial
  | .fund => F.fund
  | .antifund => F.fund.conj

/-- The charge a field carries under a factor: an integer under `U(1)`, a representation
  label under `SU(n)`. -/
abbrev Factor.Charge : Factor jets → Type
  | .U1 _ => ℤ
  | .SU _ => SURep

/-!

## B. Charge tuples and their internal index

-/

/-- **The charge tuple** of a row: one charge per factor, as a nested pair so that a row
  reads `(1, .fund, .fund)`. -/
abbrev Charges : Factors jets → Type
  | [] => Unit
  | [f] => f.Charge
  | f :: g :: gs => f.Charge × Charges (g :: gs)

/-- **The internal index of a list of dimensions**: the product of the `Fin n` over the
  list, with `Fin 1` for the empty list and no trailing factor for a one-element list. -/
abbrev IdxOfDims : List ℕ → Type
  | [] => Fin 1
  | [n] => Fin n
  | n :: m :: ms => Fin n × IdxOfDims (m :: ms)

/-- The index of a list of dimensions is finite. -/
@[instance_reducible]
def IdxOfDims.fintype : (ds : List ℕ) → Fintype (IdxOfDims ds)
  | [] => inferInstanceAs (Fintype (Fin 1))
  | [n] => inferInstanceAs (Fintype (Fin n))
  | n :: m :: ms =>
    letI := IdxOfDims.fintype (m :: ms)
    inferInstanceAs (Fintype (Fin n × IdxOfDims (m :: ms)))

/-- The index of a list of dimensions has decidable equality. -/
@[instance_reducible]
def IdxOfDims.decidableEq : (ds : List ℕ) → DecidableEq (IdxOfDims ds)
  | [] => inferInstanceAs (DecidableEq (Fin 1))
  | [n] => inferInstanceAs (DecidableEq (Fin n))
  | n :: m :: ms =>
    letI := IdxOfDims.decidableEq (m :: ms)
    inferInstanceAs (DecidableEq (Fin n × IdxOfDims (m :: ms)))

instance (ds : List ℕ) : Fintype (IdxOfDims ds) := IdxOfDims.fintype ds

instance (ds : List ℕ) : DecidableEq (IdxOfDims ds) := IdxOfDims.decidableEq ds

/-- The dimensions an `SU(n)` label contributes to the internal index: none for the
  singlet, `n` for the fundamental and the antifundamental. -/
abbrev SURep.dims (n : ℕ) : SURep → List ℕ
  | .singlet => []
  | .fund => [n]
  | .antifund => [n]

/-- **The dimensions of the internal index** of a charge tuple: the sizes of the
  nontrivial `SU(n)` representations it names, in the order of the factors. `U(1)` factors
  and singlets contribute nothing, so that a field charged under a single `SU(n)` factor is
  indexed by `Fin n` alone. -/
abbrev Charges.dims : (Γ : Factors jets) → Charges Γ → List ℕ
  | [], _ => []
  | [.U1 _], _ => []
  | [.SU (n := n) _], r => SURep.dims n r
  | .U1 _ :: g :: gs, c => Charges.dims (g :: gs) c.2
  | .SU (n := n) _ :: g :: gs, c => SURep.dims n c.1 ++ Charges.dims (g :: gs) c.2

/-- **The internal index** of a field with the given charges: the product of the
  nontrivial `SU(n)`-representation indices. -/
abbrev Idx (Γ : Factors jets) (c : Charges Γ) : Type := IdxOfDims (Charges.dims Γ c)

/-!

## C. The representation named by a charge tuple

The representation is assembled in two steps. The `SU(n)` labels give a Kronecker product
of fundamental and antifundamental representations over the nontrivial dimensions,
`Charges.suRep`, in which a singlet contributes no factor and the trivial representation is
dropped rather than tensored in; the `U(1)` charges then twist the result, `Charges.twist`.

-/

/-- The Kronecker product with the representation on the remaining dimensions, with the
  trivial representation dropped when there are none. -/
noncomputable def MatrixRep.kronDims {n : ℕ} (R₁ : MatrixRep jets (Fin n)) :
    (ds : List ℕ) → MatrixRep jets (IdxOfDims ds) → MatrixRep jets (IdxOfDims (n :: ds))
  | [], _ => R₁
  | _ :: _, R₂ => R₁.kron R₂

/-- The matrix representation of an `SU(n)` factor named by a label, on the index of the
  dimensions the label contributes. -/
noncomputable def SURep.repDims {n : ℕ} (F : SUFactor jets (Fin n)) :
    (r : SURep) → MatrixRep jets (IdxOfDims (r.dims n))
  | .singlet => MatrixRep.trivial
  | .fund => F.fund
  | .antifund => F.fund.conj

/-- The `SU(n)` part of the representation named by a charge tuple: the Kronecker product
  of the nontrivial representations the labels name. -/
noncomputable def Charges.suRep :
    (Γ : Factors jets) → (c : Charges Γ) → MatrixRep jets (IdxOfDims (Charges.dims Γ c))
  | [], _ => MatrixRep.trivial
  | [.U1 _], _ => MatrixRep.trivial
  | [.SU F], r => SURep.repDims F r
  | .U1 _ :: g :: gs, c => Charges.suRep (g :: gs) c.2
  | .SU _ :: g :: gs, (.singlet, c) => Charges.suRep (g :: gs) c
  | .SU F :: g :: gs, (.fund, c) => F.fund.kronDims _ (Charges.suRep (g :: gs) c)
  | .SU F :: g :: gs, (.antifund, c) => F.fund.conj.kronDims _ (Charges.suRep (g :: gs) c)

/-- The `U(1)` part of the representation named by a charge tuple: the charge twists of
  all the `U(1)` factors, applied to a given representation. -/
noncomputable def Charges.twist {ι : Type} [Fintype ι] [DecidableEq ι] :
    (Γ : Factors jets) → Charges Γ → MatrixRep jets ι → MatrixRep jets ι
  | [], _, R => R
  | [.U1 F], q, R => F.charge q R
  | [.SU _], _, R => R
  | .U1 F :: g :: gs, c, R => F.charge c.1 (Charges.twist (g :: gs) c.2 R)
  | .SU _ :: g :: gs, c, R => Charges.twist (g :: gs) c.2 R

/-- **The matrix representation named by a charge tuple**: the Kronecker product of the
  nontrivial `SU(n)` representations the labels name, twisted by the charge powers of the
  `U(1)` jets. -/
noncomputable def Charges.rep (Γ : Factors jets) (c : Charges Γ) : MatrixRep jets (Idx Γ c) :=
  Charges.twist Γ c (Charges.suRep Γ c)

/-!

## D. Matter field data and its matter field

A field of a model is written down as its Lorentz label and its charge tuple, so that
`(.L, .singlet, .fund, -3)` is a left-handed doublet of hypercharge `-3`. The datum
compiles to a `MatterField` on the target space `S ⊗ (Idx → ℂ)` of the label's Lorentz
factor and the internal index of the charges, or, through an identification `e`, on any
target space presented as such a tensor product.

-/

/-- **The Lorentz label of a field**: a left- or right-handed Weyl spinor or a scalar. -/
inductive LorentzLabel
  /-- A left-handed Weyl spinor. -/
  | L
  /-- A right-handed Weyl spinor. -/
  | R
  /-- A Lorentz scalar. -/
  | scalar
  deriving DecidableEq, Repr

namespace LorentzLabel

/-- Whether the label is fermionic. -/
def isFermion : LorentzLabel → Bool
  | .L => true
  | .R => true
  | .scalar => false

/-- The Lorentz factor of the target space of a field with the given label. -/
abbrev Space : LorentzLabel → Type
  | .L => Fermion.LeftHandedWeyl
  | .R => Fermion.RightHandedWeyl
  | .scalar => ℂ

instance : Module.Finite ℂ Fermion.LeftHandedWeyl :=
  Module.Finite.of_basis Fermion.LeftHandedWeyl.basis

instance : Module.Finite ℂ Fermion.RightHandedWeyl :=
  Module.Finite.of_basis Fermion.RightHandedWeyl.basis

instance instAddCommGroupSpace : (l : LorentzLabel) → AddCommGroup l.Space
  | .L => inferInstanceAs (AddCommGroup Fermion.LeftHandedWeyl)
  | .R => inferInstanceAs (AddCommGroup Fermion.RightHandedWeyl)
  | .scalar => inferInstanceAs (AddCommGroup ℂ)

instance instModuleSpace : (l : LorentzLabel) → Module ℂ l.Space
  | .L => inferInstanceAs (Module ℂ Fermion.LeftHandedWeyl)
  | .R => inferInstanceAs (Module ℂ Fermion.RightHandedWeyl)
  | .scalar => inferInstanceAs (Module ℂ ℂ)

instance instFreeSpace : (l : LorentzLabel) → Module.Free ℂ l.Space
  | .L => inferInstanceAs (Module.Free ℂ Fermion.LeftHandedWeyl)
  | .R => inferInstanceAs (Module.Free ℂ Fermion.RightHandedWeyl)
  | .scalar => inferInstanceAs (Module.Free ℂ ℂ)

instance instFiniteSpace : (l : LorentzLabel) → Module.Finite ℂ l.Space
  | .L => inferInstanceAs (Module.Finite ℂ Fermion.LeftHandedWeyl)
  | .R => inferInstanceAs (Module.Finite ℂ Fermion.RightHandedWeyl)
  | .scalar => inferInstanceAs (Module.Finite ℂ ℂ)

/-- The representation of the Lorentz group on the Lorentz factor of a label. -/
noncomputable def rep : (l : LorentzLabel) → Representation ℂ SL(2,ℂ) l.Space
  | .L => Fermion.LeftHandedWeyl.rep
  | .R => Fermion.RightHandedWeyl.rep
  | .scalar => Representation.trivial ℂ SL(2,ℂ) ℂ

/-- The mass weight of a field with the given label, in the units in which a derivative
  has weight `2`: `3` for a Weyl spinor, `2` for a scalar. -/
def massWeight : LorentzLabel → ℕ
  | .L => 3
  | .R => 3
  | .scalar => 2

/-- The index of the basis of the Lorentz factor of a label: the two spinor components of
  a Weyl spinor, one component for a scalar. -/
abbrev basisIndex : LorentzLabel → Type
  | .L => Fin 2
  | .R => Fin 2
  | .scalar => Unit

instance instFintypeBasisIndex : (l : LorentzLabel) → Fintype l.basisIndex
  | .L => inferInstanceAs (Fintype (Fin 2))
  | .R => inferInstanceAs (Fintype (Fin 2))
  | .scalar => inferInstanceAs (Fintype Unit)

instance instDecidableEqBasisIndex : (l : LorentzLabel) → DecidableEq l.basisIndex
  | .L => inferInstanceAs (DecidableEq (Fin 2))
  | .R => inferInstanceAs (DecidableEq (Fin 2))
  | .scalar => inferInstanceAs (DecidableEq Unit)

/-- The basis of the Lorentz factor of a label: the Weyl basis, or `1` for a scalar. -/
noncomputable def basis : (l : LorentzLabel) → Module.Basis l.basisIndex ℂ l.Space
  | .L => Fermion.LeftHandedWeyl.basis
  | .R => Fermion.RightHandedWeyl.basis
  | .scalar => Module.Basis.singleton Unit ℂ

end LorentzLabel

/-- **The data of a matter field**: its Lorentz label and its charge tuple, so that a
  field reads `(.L, .singlet, .fund, -3)`. -/
abbrev MatterFieldData (Γ : Factors jets) : Type := LorentzLabel × Charges Γ

namespace MatterFieldData

variable {Γ : Factors jets} (M : MatterFieldData Γ)

/-- The Lorentz label of the field. -/
abbrev lorentz : LorentzLabel := M.1

/-- The charges of the field. -/
abbrev charges : Charges Γ := M.2

/-- The internal index of the field. -/
abbrev Idx : Type := LocalGaugeData.Idx Γ M.charges

/-- The matrix representation named by the charges of the field. -/
noncomputable abbrev rep : MatrixRep jets M.Idx := Charges.rep Γ M.charges

/-- The mass weight of the field. -/
abbrev massWeight : ℕ := M.lorentz.massWeight

/-- **The target space of the field**: the Lorentz factor of its label tensored with the
  functions on its internal index. -/
abbrev V : Type := M.lorentz.Space ⊗[ℂ] (M.Idx → ℂ)

/-- **The basis of the target space**: the basis of the Lorentz factor tensored with the
  coordinate basis of the internal index. -/
noncomputable def basis : Module.Basis (M.lorentz.basisIndex × M.Idx) ℂ M.V :=
  M.lorentz.basis.tensorProduct (Pi.basisFun ℂ M.Idx)

/-- A basis vector of the target space is a basis vector of the Lorentz factor tensored with
  a coordinate vector of the internal index. -/
@[simp]
lemma basis_apply (a : M.lorentz.basisIndex) (i : M.Idx) :
    M.basis (a, i) = M.lorentz.basis a ⊗ₜ Pi.single i 1 := by
  rw [basis, Module.Basis.tensorProduct_apply, Pi.basisFun_apply]

/-- **The matter field of a datum on a presented target space**: a target space `V`
  identified with the Lorentz factor of the label tensored with the internal index of the
  charges, transforming in the representation the charges name. -/
noncomputable def toMatterFieldOn {V : Type} [AddCommGroup V] [Module ℂ V]
    [Module.Free ℂ V] [Module.Finite ℂ V]
    (e : V ≃ₗ[ℂ] M.lorentz.Space ⊗[ℂ] (M.Idx → ℂ)) : MatterField jets :=
  M.rep.matterField e M.lorentz.rep M.massWeight

/-- **The matter field of a datum**: the target space is the Lorentz factor of the label
  tensored with the internal index of the charges. -/
noncomputable def toMatterField : MatterField jets :=
  M.toMatterFieldOn (LinearEquiv.refl ℂ _)

variable {V : Type} [AddCommGroup V] [Module ℂ V] [Module.Free ℂ V] [Module.Finite ℂ V]
  (e : V ≃ₗ[ℂ] M.lorentz.Space ⊗[ℂ] (M.Idx → ℂ))

@[simp]
lemma toMatterFieldOn_V : (M.toMatterFieldOn e).V = V := rfl

@[simp]
lemma toMatterFieldOn_repJet : (M.toMatterFieldOn e).repJet = M.rep.repJet e := rfl

@[simp]
lemma toMatterFieldOn_repAlgebra : (M.toMatterFieldOn e).repAlgebra = M.rep.repAlgebra e :=
  rfl

@[simp]
lemma toMatterFieldOn_repLorentz :
    (M.toMatterFieldOn e).repLorentz = MatrixRep.repLorentz e M.lorentz.rep := rfl

@[simp]
lemma toMatterFieldOn_massWeight : (M.toMatterFieldOn e).massWeight = M.massWeight := rfl

@[simp]
lemma toMatterField_massWeight : M.toMatterField.massWeight = M.massWeight := rfl

/-- The target space of the matter field of a datum is the target space of the datum. -/
@[simp]
lemma toMatterField_V : M.toMatterField.V = M.V := rfl

/-- The gauge and Lorentz actions of the matter field of a datum commute. -/
lemma toMatterFieldOn_gaugeLorentzCompatible :
    (M.toMatterFieldOn e).GaugeLorentzCompatible :=
  MatrixRep.matterField_gaugeLorentzCompatible _ _ _ _

/-- The gauge and Lorentz actions of the matter field of a datum commute. -/
lemma toMatterField_gaugeLorentzCompatible : M.toMatterField.GaugeLorentzCompatible :=
  M.toMatterFieldOn_gaugeLorentzCompatible _

end MatterFieldData

/-!

## E. The field data of a model and its field content

-/

/-- **The field data of a model**: for each field of the model, its number of generations
  and its matter field data. -/
abbrev FieldData (Γ : Factors jets) (Fields : Type) : Type := Fields → ℕ × MatterFieldData Γ

namespace FieldData

variable [Module.Finite ℝ 𝔤] {Γ : Factors jets} {Fields : Type} [Fintype Fields]
  [DecidableEq Fields] (D : FieldData Γ Fields)

/-- The number of generations of a field. -/
abbrev generations (f : Fields) : ℕ := (D f).1

/-- The matter field data of a field. -/
abbrev data (f : Fields) : MatterFieldData Γ := (D f).2

/-- The fermionic fields of the model. -/
abbrev Fermions : Type := {f : Fields // (D.data f).lorentz.isFermion = true}

/-- The bosonic fields of the model. -/
abbrev Bosons : Type := {f : Fields // (D.data f).lorentz.isFermion = false}

/-- The fermionic species of the model: a fermionic field together with a generation. -/
abbrev FermionSpecies : Type := Σ f : D.Fermions, Fin (D.generations f.1)

/-- The bosonic species of the model: a bosonic field together with a generation. -/
abbrev BosonSpecies : Type := Σ f : D.Bosons, Fin (D.generations f.1)

/-- **The field content of a model**: one matter field per species, the matter field of the
  species' data. -/
noncomputable def toGaugeFieldData : GaugeFieldData jets where
  FermionSpecies := D.FermionSpecies
  fermion s := (D.data s.1.1).toMatterField
  BosonSpecies := D.BosonSpecies
  boson s := (D.data s.1.1).toMatterField

@[simp]
lemma toGaugeFieldData_FermionSpecies :
    D.toGaugeFieldData.FermionSpecies = D.FermionSpecies := rfl

@[simp]
lemma toGaugeFieldData_fermion (s : D.FermionSpecies) :
    D.toGaugeFieldData.fermion s = (D.data s.1.1).toMatterField := rfl

@[simp]
lemma toGaugeFieldData_BosonSpecies : D.toGaugeFieldData.BosonSpecies = D.BosonSpecies := rfl

@[simp]
lemma toGaugeFieldData_boson (s : D.BosonSpecies) :
    D.toGaugeFieldData.boson s = (D.data s.1.1).toMatterField := rfl

/-- The field content of a model satisfies `GaugeFieldData.GaugeLorentzCompatible`: every
  species is a matrix representation on the internal index tensored with a Lorentz
  factor. -/
lemma toGaugeFieldData_gaugeLorentzCompatible : D.toGaugeFieldData.GaugeLorentzCompatible :=
  ⟨fun _ => MatterFieldData.toMatterField_gaugeLorentzCompatible _,
    fun _ => MatterFieldData.toMatterField_gaugeLorentzCompatible _⟩

end FieldData

end LocalGaugeData
