/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license.
Authors: Joseph Tooby-Smith
-/
import Physlib.Meta.Basic
import Physlib.Meta.Remark.Properties
import Physlib.Meta.Notes.ToHTML
import Mathlib.Lean.CoreM
import Physlib
/-!

# Extracting notes from Lean files

-/

open Lean System Meta Physlib

inductive NameStatus
  | complete : NameStatus
  | incomplete : NameStatus

instance : ToString NameStatus where
  toString
    | NameStatus.complete => "complete"
    | NameStatus.incomplete => "incomplete"

inductive NotePart
  | h1 : String → NotePart
  | h2 : String → NotePart
  | p : String → NotePart
  | name : Name → NameStatus → NotePart
  | warning : String → NotePart

structure DeclInfo where
  line : Nat
  fileName : Name
  name : Name
  status : NameStatus
  declString : String
  docString : String
  isDef : Bool
  isThm : Bool

def DeclInfo.ofName (n : Name) (ns : NameStatus): MetaM DeclInfo := do
  let line ← Name.lineNumber n
  let fileName ← Name.fileName n
  let declString ← Name.getDeclStringNoDoc n
  let docString ← Name.getDocString n
  let constInfo ← getConstInfo n
  let isDef := constInfo.isDef ∨ Lean.isStructure (← getEnv) n ∨ constInfo.isInductive
  let isThm := declString.startsWith "theorem" ∨ declString.startsWith "noncomputable theorem"
  pure {
    line := line,
    fileName := fileName,
    name := n,
    status := ns,
    declString := declString,
    docString := docString,
    isDef := isDef
    isThm := isThm}

def DeclInfo.toYML (d : DeclInfo) : MetaM String := do
  let declStringIndent := d.declString.replace "\n" "\n      "
  let docStringIndent := d.docString.replace "\n" "\n      "
  let link := Name.toGitHubLink d.fileName d.line
  return s!"
  - type: name
    name: {d.name}
    line: {d.line}
    fileName: {d.fileName}
    status: \"{d.status}\"
    link: \"{link}\"
    isDef: {d.isDef}
    isThm: {d.isThm}
    docString: |
      {docStringIndent}
    declString: |
      {declStringIndent}"

/-- In `(List String) × Nat × Nat` the first `Nat` is section number, the second `Nat`
  is subsection number, and the third `Nat` is defn. or lemma number.
  Definitions and lemmas etc are done by section not subsection. -/
def NotePart.toYMLM : ((List String) × Nat × Nat × Nat) →  NotePart →
    MetaM ((List String) × Nat × Nat × Nat)
  | x, NotePart.h1 s =>
    let newString := s!"
  - type: h1
    sectionNo: {x.2.1.succ}
    content: \"{s}\""
    return ⟨x.1 ++ [newString], ⟨Nat.succ x.2.1, 0, 0⟩⟩
  | x, NotePart.h2 s =>
    let newString := s!"
  - type: h2
    sectionNo: \"{x.2.1}.{x.2.2.1.succ}\"
    content: \"{s}\""
    return ⟨x.1 ++ [newString], ⟨x.2.1, Nat.succ x.2.2.1, x.2.2.2⟩⟩
  | x, NotePart.p s =>
    let newString := s!"
  - type: p
    content: \"{s}\""
    return ⟨x.1 ++ [newString], x.2⟩
  | x, NotePart.warning s =>
    let newString := s!"
  - type: warning
    content: \"{s}\""
    return ⟨x.1 ++ [newString], x.2⟩
  | x, NotePart.name n s => do
  match (← RemarkInfo.IsRemark n) with
  | true =>
    let remarkInfo ← RemarkInfo.getRemarkInfo n
    let content := remarkInfo.content
    let contentIndent := content.replace "\n" "\n      "
    let shortName := remarkInfo.name.toString
    let newString := s!"
  - type: remark
    name: \"{shortName}\"
    status : \"{s}\"
    link: \"{Name.toGitHubLink remarkInfo.fileName remarkInfo.line}\"
    content: |
      {contentIndent}"
    return ⟨x.1 ++ [newString], x.2⟩
  | false =>
  let newString ← (← DeclInfo.ofName n s).toYML
  let newString := newString ++ s!"\n    declNo: \"{x.2.1}.{x.2.2.2.succ}\""
  return ⟨x.1 ++ [newString], ⟨x.2.1, x.2.2.1, Nat.succ x.2.2.2⟩⟩

structure Note where
  title : String
  /-- The curators of the note are the people who put the note together.
    This may not conicide with the original authors of the material. -/
  curators : List String
  parts : List NotePart

def Note.toYML : Note → MetaM String
  | ⟨title, curators, parts⟩ => do
  let parts ← parts.foldlM NotePart.toYMLM ([], ⟨0, 0⟩)
  return s!"
title: \"{title}\"
curators: {String.intercalate "," curators}
parts:
  {String.intercalate "\n" parts.1}"

def perturbationTheory : Note where
  title := "Proof of Wick's theorem"
  curators := ["Joseph Tooby-Smith"]
  parts := [
    .h1 "Introduction",
    .name `FieldSpecification.wicks_theorem_context .incomplete,
    .p "In this note we walk through the important parts of the proof of the three versions of
      Wick's theorem for field operators containing carrying both fermionic and bosonic statistics,
      as it appears in Physlib. Not every lemma or definition is covered here.
      The aim is to give just enough that the story can be understood.",
    .p "
     Before proceeding with the steps in the proof, we review some basic terminology
     related to Lean and type theory. The most important notion is that of a type.
     We don't give any formal definition here, except to say that a type `T`, like a set, has
     elements `x` which we say are of type `T` and write `x : T`. Examples of types include,
     the type of natural numbers `ℕ`, the type of real numbers `ℝ`, the type of numbers
     `0, …, n-1` denoted `Fin n`. Given two types `T` and `S`, we can form the product type `T × S`,
     and the function type `T → S`.

     Types form the foundation of Lean and the theory behind them will be used both explicitly and
      implicitly throughout this note.",
    .h1 "Field operators",
    .h2 "Field statistics",
    .name ``FieldStatistic .complete,
    .name ``FieldStatistic.instCommGroup .complete,
    .name ``FieldStatistic.exchangeSign .complete,
    .h2 "Field specifications",
    .name ``FieldSpecification .complete,
    .h2 "Field operators",
    .name ``FieldSpecification.FieldOp .complete,
    .name ``FieldSpecification.fieldOpStatistic .complete,
    .name ``CreateAnnihilate .complete,
    .name ``FieldSpecification.CrAnFieldOp .complete,
    .name ``FieldSpecification.crAnFieldOpToCreateAnnihilate .complete,
    .name ``FieldSpecification.crAnStatistics .complete,
    .name `FieldSpecification.notation_remark .complete,
    .h2 "Field-operator free algebra",
    .name ``FieldSpecification.FieldOpFreeAlgebra .complete,
    .name `FieldSpecification.FieldOpFreeAlgebra.naming_convention .complete,
    .name ``FieldSpecification.FieldOpFreeAlgebra.ofCrAnOpF .complete,
    .name ``FieldSpecification.FieldOpFreeAlgebra.universality .complete,
    .name ``FieldSpecification.FieldOpFreeAlgebra.ofCrAnListF .complete,
    .name ``FieldSpecification.FieldOpFreeAlgebra.ofFieldOpF .complete,
    .name ``FieldSpecification.FieldOpFreeAlgebra.ofFieldOpListF .complete,
    .name `FieldSpecification.FieldOpFreeAlgebra.notation_drop .complete,
    .name ``FieldSpecification.FieldOpFreeAlgebra.fieldOpFreeAlgebraGrade .complete,
    .name ``FieldSpecification.FieldOpFreeAlgebra.superCommuteF .complete,
    .name ``FieldSpecification.FieldOpFreeAlgebra.superCommuteF_ofCrAnListF_ofCrAnListF_eq_sum .complete,
    .h2 "Field-operator algebra",
    .name ``FieldSpecification.WickAlgebra .complete,
    .name ``FieldSpecification.WickAlgebra.ι .complete,
    .name ``FieldSpecification.WickAlgebra.universality .complete,
    .name ``FieldSpecification.WickAlgebra.ofCrAnOp .complete,
    .name ``FieldSpecification.WickAlgebra.ofCrAnList .complete,
    .name ``FieldSpecification.WickAlgebra.ofFieldOp .complete,
    .name ``FieldSpecification.WickAlgebra.ofCrAnList .complete,
    .name `FieldSpecification.WickAlgebra.notation_drop .complete,
    .name ``FieldSpecification.WickAlgebra.anPart .complete,
    .name ``FieldSpecification.WickAlgebra.crPart .complete,
    .name ``FieldSpecification.WickAlgebra.ofFieldOp_eq_crPart_add_anPart .complete,
    .name ``FieldSpecification.WickAlgebra.WickAlgebraGrade .complete,
    .name ``FieldSpecification.WickAlgebra.superCommute .complete,
    .h1 "Time ordering",
    .name ``FieldSpecification.crAnTimeOrderRel .complete,
    .name ``FieldSpecification.crAnTimeOrderList .complete,
    .name ``FieldSpecification.crAnTimeOrderSign .complete,
    .name ``FieldSpecification.FieldOpFreeAlgebra.timeOrderF .complete,
    .name ``FieldSpecification.WickAlgebra.timeOrder .complete,
    .name ``FieldSpecification.WickAlgebra.timeOrder_eq_maxTimeField_mul_finset .complete,
    .name ``FieldSpecification.WickAlgebra.timeOrder_timeOrder_mid .complete,
    .h1 "Normal ordering",
    .name ``FieldSpecification.normalOrderRel .complete,
    .name ``FieldSpecification.normalOrderList .complete,
    .name ``FieldSpecification.normalOrderSign .complete,
    .name ``FieldSpecification.normalOrderSign_eraseIdx .complete,
    .name ``FieldSpecification.FieldOpFreeAlgebra.normalOrderF .complete,
    .name ``FieldSpecification.WickAlgebra.normalOrder .complete,
    .name ``FieldSpecification.WickAlgebra.normalOrder_superCommute_eq_zero .complete,
    .name ``FieldSpecification.WickAlgebra.ofCrAnOp_superCommute_normalOrder_ofCrAnList_sum .complete,
    .name ``FieldSpecification.WickAlgebra.ofFieldOp_mul_normalOrder_ofFieldOpList_eq_sum .complete,
    .h1 "Wick Contractions",
    .h2 "Definition",
    .name ``WickContraction .complete,
    .name ``WickContraction.mem_three .complete,
    .name ``WickContraction.mem_four .complete,
    .name `WickContraction.contraction_notation .complete,
    .name ``WickContraction.GradingCompliant .complete,
    .h2 "Aside: Cardinality",
    .name ``WickContraction.card_eq_cardFun .complete,
    .h2 "Uncontracted elements",
    .name ``WickContraction.uncontracted .complete,
    .name ``WickContraction.uncontractedListGet .complete,
    .h2 "Constructors",
    .name ``WickContraction.insertAndContract .complete,
    .name ``WickContraction.insertLift_sum .complete,
    .name ``WickContraction.join .complete,
    .h2 "Sign",
    .name ``WickContraction.sign .complete,
    .name ``WickContraction.join_sign .complete,
    .name ``WickContraction.sign_insert_none .complete,
    .name ``WickContraction.sign_insert_none_zero .complete,
    .name ``WickContraction.sign_insert_some_of_not_lt .complete,
    .name ``WickContraction.sign_insert_some_of_lt .complete,
    .name ``WickContraction.sign_insert_some_zero .complete,
    .h2 "Normal order",
    .name ``FieldSpecification.WickAlgebra.normalOrder_uncontracted_none .complete,
    .name ``FieldSpecification.WickAlgebra.normalOrder_uncontracted_some .complete,
    .h1 "Static Wick's theorem",
    .h2 "Static contractions",
    .name ``WickContraction.staticContract .complete,
    .name ``WickContraction.staticContract_insert_none .complete,
    .name ``WickContraction.staticContract_insert_some .complete,
    .h2 "Static Wick terms",
    .name ``WickContraction.staticWickTerm .complete,
    .name ``WickContraction.staticWickTerm_empty_nil .complete,
    .name ``WickContraction.staticWickTerm_insert_zero_none .complete,
    .name ``WickContraction.staticWickTerm_insert_zero_some .complete,
    .name ``WickContraction.mul_staticWickTerm_eq_sum .complete,
    .h2 "The Static Wick's theorem",
    .name ``FieldSpecification.WickAlgebra.static_wick_theorem .complete,
    .h1 "Wick's theorem",
    .h2 "Time contractions",
    .name ``FieldSpecification.WickAlgebra.timeContract .complete,
    .name ``FieldSpecification.WickAlgebra.timeContract_of_timeOrderRel .complete,
    .name ``FieldSpecification.WickAlgebra.timeContract_of_not_timeOrderRel_expand .complete,
    .name ``FieldSpecification.WickAlgebra.timeContract_mem_center .complete,
    .name ``WickContraction.timeContract .complete,
    .name ``WickContraction.timeContract_insert_none .complete,
    .name ``WickContraction.timeContract_insert_some_of_not_lt .complete,
    .name ``WickContraction.timeContract_insert_some_of_lt .complete,
    .name ``WickContraction.join_sign_timeContract .complete,
    .h2 "Wick terms",
    .name ``WickContraction.wickTerm .complete,
    .name ``WickContraction.wickTerm_empty_nil .complete,
    .name ``WickContraction.wickTerm_insert_none .complete,
    .name ``WickContraction.wickTerm_insert_some .complete,
    .name ``WickContraction.mul_wickTerm_eq_sum .complete,
    .h2 "Wick's theorem",
    .name ``FieldSpecification.wicks_theorem .complete,
    .h1 "Normal-ordered Wick's theorem",
    .name ``WickContraction.EqTimeOnly.timeOrder_staticContract_of_not_mem .complete,
    .name ``WickContraction.EqTimeOnly.staticContract_eq_timeContract_of_eqTimeOnly .complete,
    .name ``WickContraction.EqTimeOnly.timeOrder_timeContract_mul_of_eqTimeOnly_left .complete,
    .name ``FieldSpecification.WickAlgebra.timeOrder_ofFieldOpList_eqTimeOnly .complete,
    .name ``FieldSpecification.WickAlgebra.normalOrder_timeOrder_ofFieldOpList_eq_eqTimeOnly_empty .complete,
    .name ``FieldSpecification.WickAlgebra.timeOrder_haveEqTime_split .complete,
    .name ``FieldSpecification.WickAlgebra.wicks_theorem_normal_order .complete
    ]

def harmonicOscillator : Note where
  title := "The Quantum Harmonic Oscillator"
  curators := ["Joseph Tooby-Smith"]
  parts := [
    .h1 "Introduction",
    .p "The quantum harmonic oscillator is a fundamental example of a one-dimensional
      quantum mechanical system. It is often one of the first models encountered by undergraduate
      students studying quantum mechanics.",
    .p " This note presents the formalization of the quantum harmonic oscillator in the theorem prover
     Lean 4, as part of the larger project Physlib.
     What this means is that every definition and theorem in this note has been formally checked
     for mathematical correctness for by a computer. There are a number of
     motivations for doing this which are discussed <a href = 'https://physlib.io'>here</a>.",
    .p "Note that we do not give every definition and theorem which is part of
      the formalization.
     Our goal is give key aspects, in such a way that we hope this note will be useful
     to newcomers to Lean or those simply interested in learning about the
     quantum harmonic oscillator.",
    .h1 "Hilbert Space",
    .name ``QuantumMechanics.OneDimension.HilbertSpace .complete,
    .name ``QuantumMechanics.OneDimension.HilbertSpace.MemHS .complete,
    .name ``QuantumMechanics.OneDimension.HilbertSpace.memHS_iff .complete,
    .name ``QuantumMechanics.OneDimension.HilbertSpace.mk .complete,
    .name ``QuantumMechanics.OneDimension.HilbertSpace.Operators .complete,
    .name ``QuantumMechanics.OneDimension.HilbertSpace.memHS_of_parity .complete,
    .h1 "The Schrodinger Operator",
    .name ``QuantumMechanics.OneDimension.HarmonicOscillator .complete,
    .name ``QuantumMechanics.OneDimension.HarmonicOscillator.ξ .complete,
    .name ``QuantumMechanics.OneDimension.HarmonicOscillator.schrodingerOperator .complete,
    .name ``QuantumMechanics.OneDimension.HarmonicOscillator.schrodingerOperator_parity .complete,
    .h1 "The eigenfunctions of the Schrodinger Operator",
    .name ``Physlib.physHermite .complete,
    .name ``QuantumMechanics.OneDimension.HarmonicOscillator.eigenfunction .complete,
    .h2 "Properties of the eigenfunctions",
    .name ``QuantumMechanics.OneDimension.HarmonicOscillator.eigenfunction_integrable .complete,
    .name ``QuantumMechanics.OneDimension.HarmonicOscillator.eigenfunction_conj .complete,
    .name ``QuantumMechanics.OneDimension.HarmonicOscillator.eigenfunction_aeStronglyMeasurable .complete,
    .name ``QuantumMechanics.OneDimension.HarmonicOscillator.eigenfunction_square_integrable .complete,
    .name ``QuantumMechanics.OneDimension.HarmonicOscillator.eigenfunction_memHS .complete,
    .name ``QuantumMechanics.OneDimension.HarmonicOscillator.eigenfunction_differentiableAt .complete,
    .name ``QuantumMechanics.OneDimension.HarmonicOscillator.eigenfunction_orthonormal .complete,
    .name ``QuantumMechanics.OneDimension.HarmonicOscillator.eigenfunction_parity .complete,
    .h1 "The time-independent Schrodinger Equation",
    .name ``QuantumMechanics.OneDimension.HarmonicOscillator.eigenValue .complete,
    .name ``QuantumMechanics.OneDimension.HarmonicOscillator.schrodingerOperator_eigenfunction
      .complete,
    .h1 "Completeness",
    .name ``QuantumMechanics.OneDimension.HarmonicOscillator.orthogonal_power_of_mem_orthogonal .complete,
    .name ``QuantumMechanics.OneDimension.HarmonicOscillator.orthogonal_exp_of_mem_orthogonal .complete,
    .name ``QuantumMechanics.OneDimension.HarmonicOscillator.fourierIntegral_zero_of_mem_orthogonal .complete,
    .name ``QuantumMechanics.OneDimension.HarmonicOscillator.eigenfunction_completeness .complete,
    ]

def higgsPotential : Note where
  title := "The Higgs potential"
  curators := ["Joseph Tooby-Smith"]
  parts := [
    .h1 "Introduction",
    .p "The Higgs potential is a key part of the Standard Model of particle physics.
      It is a scalar potential which is used to give mass to the elementary particles.
      The Higgs potential is a polynomial of degree four in the Higgs field.",
    .h1 "The Higgs field",
    .name ``StandardModel.HiggsVec .complete,
    .name ``StandardModel.HiggsBundle .complete,
    .name ``StandardModel.HiggsField .complete,
    .h1 "The Higgs potential",
    .name ``StandardModel.HiggsField.Potential .complete,
    .name ``StandardModel.HiggsField.normSq .complete,
    .name ``StandardModel.HiggsField.Potential.toFun .complete,
    .h2 "Properties of the Higgs potential",
    .name ``StandardModel.HiggsField.Potential.neg_𝓵_quadDiscrim_zero_bound .complete,
    .name ``StandardModel.HiggsField.Potential.pos_𝓵_quadDiscrim_zero_bound .complete,
    .name ``StandardModel.HiggsField.Potential.neg_𝓵_sol_exists_iff .complete,
    .name ``StandardModel.HiggsField.Potential.pos_𝓵_sol_exists_iff .complete,
    .h2 "Boundedness of the Higgs potential",
    .name ``StandardModel.HiggsField.Potential.IsBounded .complete,
    .name ``StandardModel.HiggsField.Potential.isBounded_𝓵_nonneg .complete,
    .name ``StandardModel.HiggsField.Potential.isBounded_of_𝓵_pos .complete,
    .h2 "Maximum and minimum of the Higgs potential",
    .name ``StandardModel.HiggsField.Potential.isMaxOn_iff_field_of_𝓵_neg .complete,
    .name ``StandardModel.HiggsField.Potential.isMinOn_iff_field_of_𝓵_pos .complete,
  ]

def tensors : Note where
  title := "Tensors and index notation 🚧"
  curators := ["Joseph Tooby-Smith"]
  parts := [
    .warning "This note is a work in progress. (5th March 2025)",
    .h1 "Introduction",
    .p "This note is related to: https://arxiv.org/pdf/2411.07667, and concerns the
      implementation of tensors and index notation into Physlib, and
      its mathematical structure.",
    .p  "This note is not intended to be a first-introduction to tensors and index notation.",
    .h1 "Tensor Species",
    .name ``TensorSpecies .incomplete,
    .h2 "Example: Complex Lorentz tensors",
    .h1 "Tensor trees",
    .name ``TensorTree .incomplete,
    .name ``TensorTree.tensor .incomplete,
    .h2 "Node identities",
    .h1 "Elaboration",
    .h1 "Example use: Pauli matrices"
  ]

def notesToMake : List (Note × String) := [
    (perturbationTheory, "perturbationTheory"),
    (harmonicOscillator, "harmonicOscillator"),
    (higgsPotential, "higgsPotential"),
    (tensors, "tensors")]

def makeYML (nt : Note × String) : IO UInt32 := do
  let n := nt.1
  let s := nt.2
  let ymlString ← CoreM.withImportModules #[`Physlib] (n.toYML).run'
  let fileOut : System.FilePath := {toString := s!"./docs/_data/{s}.yml"}
  IO.FS.writeFile fileOut ymlString
  IO.println (s!"YML file made for {n.title}.")
  pure 0

unsafe def main (_ : List String) : IO UInt32 := do
  initSearchPath (← findSysroot)
  Lean.enableInitializersExecution
  let _ ← notesToMake.mapM makeYML
  pure 0
