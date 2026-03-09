/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import PhysLean.Relativity.PauliMatrices.ToTensor
/-!

## Bispinors

-/

@[expose] public section
open IndexNotation
open CategoryTheory
open MonoidalCategory
open Matrix
open MatrixGroups
open Complex
open TensorProduct
open IndexNotation
open CategoryTheory
open OverColor.Discrete
open Fermion
noncomputable section
namespace complexLorentzTensor
open Lorentz
open PauliMatrix
/-!

## Definitions

-/
open TensorSpecies
open Tensor

/-- A bispinor `pᵃᵃ` created from a lorentz vector `p^μ`. -/
def contrBispinorUp (p : ℂT[.up]) : ℂT[.upL, .upR] := permT id (PermCond.auto)
  {pauliCo | μ α β ⊗ p | μ}ᵀ

/-- A bispinor `pₐₐ` created from a lorentz vector `p^μ`. -/
def contrBispinorDown (p : ℂT[.up]) : ℂT[.downL, .downR] := permT id (PermCond.auto)
  {εL' | α α' ⊗ εR' | β β' ⊗ contrBispinorUp p | α β}ᵀ

/-- A bispinor `pᵃᵃ` created from a lorentz vector `p_μ`. -/
def coBispinorUp (p : ℂT[.down]) : ℂT[.upL, .upR] := permT id (PermCond.auto)
  {σ^^^ | μ α β ⊗ p | μ}ᵀ

/-- A bispinor `pₐₐ` created from a lorentz vector `p_μ`. -/
def coBispinorDown (p : ℂT[.down]) : ℂT[.downL, .downR] := permT id (PermCond.auto)
  {εL' | α α' ⊗ εR' | β β' ⊗ coBispinorUp p | α β}ᵀ

/-!

## Basic equalities.

-/

/-- `{contrBispinorUp p | α β = εL | α α' ⊗ εR | β β'⊗ contrBispinorDown p | α' β' }ᵀ`.

Proof: expand `contrBispinorDown` and use fact that metrics contract to the identity.
-/
informal_lemma contrBispinorUp_eq_metric_contr_contrBispinorDown where
  deps := [``contrBispinorUp, ``contrBispinorDown, ``leftMetric, ``rightMetric]
  tag := "6V2PV"

/-- `{coBispinorUp p | α β = εL | α α' ⊗ εR | β β'⊗ coBispinorDown p | α' β' }ᵀ`.

proof: expand `coBispinorDown` and use fact that metrics contract to the identity.
-/
informal_lemma coBispinorUp_eq_metric_contr_coBispinorDown where
  deps := [``coBispinorUp, ``coBispinorDown, ``leftMetric, ``rightMetric]
  tag := "6V2P6"

end complexLorentzTensor
end
