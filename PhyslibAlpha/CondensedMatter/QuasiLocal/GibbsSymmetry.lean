/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.CondensedMatter.QuasiLocal.Interaction
public import PhyslibAlpha.CondensedMatter.QuasiLocal.Symmetry

/-!

# Covariance of the finite-volume ensembles under site symmetries

A symmetry of an interaction carries the Hamiltonian and the ensembles of a box to those of the
moved box.

## i. Overview

Let a group `Γ` act on the sites, all of which carry the same finite configuration space. An
interaction is *invariant* if moving a term moves the term of the moved region:
`quantumIso γ X (Φ X) = Φ (γ • X)`. Then the Hamiltonian of a box `Λ` is carried to the Hamiltonian
of `γ • Λ`, because moving commutes with lifting and with the sum over the regions inside the box.
Moving is a `*`-isomorphism preserving the trace, so it commutes with the exponential and carries
the Gibbs weight to the Gibbs weight and the Gibbs state to the Gibbs state: the expectation of the
moved observable in the ensemble of the moved box equals the expectation in the ensemble of the box.

## ii. Key results

- `quantumIso_exp` : moving commutes with the exponential.
- `Interaction.hamiltonian_smul` : the Hamiltonian of a moved box.
- `Interaction.canonicalState_smul`, `Interaction.grandCanonicalState_smul` : covariance of the
  canonical and grand canonical ensembles.

## iii. Table of contents

- A. Moving the Gibbs weight
- B. Moving the Hamiltonian
- C. Moving the ensembles

## iv. References

* None.

-/

@[expose] public section

noncomputable section

namespace CondensedMatter

namespace QuasiLocal

open ProbabilisticTheory
open scoped Matrix Pointwise

variable {S : Type*} [DecidableEq S] {Γ : Type*} [Group Γ] [MulAction Γ S]
variable {Ω₀ : Type*} [Fintype Ω₀] [DecidableEq Ω₀]

/-! ## A. Moving the Gibbs weight -/

open scoped Matrix.Norms.Operator in
/-- Moving commutes with the exponential. -/
lemma quantumIso_exp (γ : Γ) (X : Finset S) (a : Alg (fun _ : S => Ω₀) X) :
    quantumIso γ X (NormedSpace.exp a) = NormedSpace.exp (quantumIso γ X a) :=
  NormedSpace.map_exp (quantumIso γ X)
    (LinearMap.continuous_of_finiteDimensional (quantumIso γ X).toAlgHom.toLinearMap) a

/-- Moving preserves the trace. -/
lemma quantumIso_trace (γ : Γ) (X : Finset S) (a : Alg (fun _ : S => Ω₀) X) :
    (quantumIso γ X a).trace = a.trace := by
  simp only [Matrix.trace, Matrix.diag, quantumIso, StarAlgHom.coe_mk,
    Matrix.of_apply]
  exact Fintype.sum_equiv (cfgEquiv Γ Ω₀ γ X) _ _ (fun _ => rfl)

lemma quantumIso_gibbsWeight (γ : Γ) (X : Finset S) (a : Alg (fun _ : S => Ω₀) X) :
    quantumIso γ X (gibbsWeight a) = gibbsWeight (quantumIso γ X a) := by
  rw [gibbsWeight, gibbsWeight, quantumIso_exp, map_neg]

lemma quantumIso_partition (γ : Γ) (X : Finset S) (a : Alg (fun _ : S => Ω₀) X) :
    partition (quantumIso γ X a) = partition a := by
  rw [partition, partition, ← quantumIso_gibbsWeight, quantumIso_trace]

/-- **The Gibbs functional is covariant.** -/
lemma gibbsFunctional_quantumIso (γ : Γ) (X : Finset S) (h b : Alg (fun _ : S => Ω₀) X) :
    gibbsFunctional (quantumIso γ X h) (quantumIso γ X b) = gibbsFunctional h b := by
  rw [gibbsFunctional_apply, gibbsFunctional_apply, quantumIso_partition,
    ← quantumIso_gibbsWeight, ← map_mul, quantumIso_trace]

/-! ## B. Moving the Hamiltonian -/

/-- An interaction is *invariant* under `γ` if moving a term gives the term of the moved region. -/
def Interaction.IsInvariant (I : Interaction (fun _ : S => Ω₀)) (γ : Γ) : Prop :=
  ∀ X : Finset S, quantumIso γ X (I.Φ X) = I.Φ (γ • X)

/-- The bijection between the regions of a box and the regions of the moved box. -/
def powersetSmul (γ : Γ) (Λ : Finset S) : Λ.powerset ≃ (γ • Λ).powerset where
  toFun X := ⟨γ • X.1, Finset.mem_powerset.2 (smul_mono γ (Finset.mem_powerset.1 X.2))⟩
  invFun Y := ⟨γ⁻¹ • Y.1, Finset.mem_powerset.2 (by
    have := smul_mono γ⁻¹ (Finset.mem_powerset.1 Y.2)
    rwa [inv_smul_smul] at this)⟩
  left_inv X := Subtype.ext (inv_smul_smul γ X.1)
  right_inv Y := Subtype.ext (smul_inv_smul γ Y.1)

/-- **The Hamiltonian of a moved box**: for an invariant interaction, moving the Hamiltonian of a
box gives the Hamiltonian of the moved box. -/
lemma Interaction.hamiltonian_smul (I : Interaction (fun _ : S => Ω₀)) {γ : Γ}
    (hI : I.IsInvariant γ) (Λ : Finset S) :
    quantumIso γ Λ (I.hamiltonian Λ) = I.hamiltonian (γ • Λ) := by
  rw [Interaction.hamiltonian, Interaction.hamiltonian, map_sum]
  refine Fintype.sum_equiv (powersetSmul γ Λ) _ _ (fun X => ?_)
  rw [quantumIso_incl, hI X.1]
  rfl

/-! ## C. Moving the ensembles -/

variable [Nonempty Ω₀]

/-- **The canonical ensemble is covariant**: the expectation of a moved observable in the
ensemble of the moved box is the expectation of the observable in the ensemble of the box. -/
lemma Interaction.canonicalState_smul (I : Interaction (fun _ : S => Ω₀)) {γ : Γ}
    (hI : I.IsInvariant γ) (β : ℝ) (Λ : Finset S) (a : Alg (fun _ : S => Ω₀) Λ) :
    I.canonicalState β (γ • Λ) (quantumIso γ Λ a) = I.canonicalState β Λ a := by
  have hH := I.hamiltonian_smul hI Λ
  change gibbsFunctional ((β : ℂ) • I.hamiltonian (γ • Λ)) (quantumIso γ Λ a) =
    gibbsFunctional ((β : ℂ) • I.hamiltonian Λ) a
  rw [← hH, ← map_smul]
  exact gibbsFunctional_quantumIso γ Λ _ a

/-- The bijection between the sites of a box and the sites of the moved box. -/
def siteSmul (γ : Γ) (Λ : Finset S) : ↥Λ ≃ ↥(γ • Λ) where
  toFun x := ⟨γ • x.1, Finset.smul_mem_smul_finset x.2⟩
  invFun y := ⟨γ⁻¹ • y.1, Finset.inv_smul_mem_iff.2 y.2⟩
  left_inv x := Subtype.ext (inv_smul_smul γ x.1)
  right_inv y := Subtype.ext (smul_inv_smul γ y.1)

omit [Nonempty Ω₀] in
/-- **A uniform charge is moved to the uniform charge of the moved box.** -/
lemma chargeOp_smul (q₀ : Ω₀ → ℝ) (γ : Γ) (Λ : Finset S) :
    quantumIso γ Λ (chargeOp (fun _ : S => q₀) Λ) = chargeOp (fun _ : S => q₀) (γ • Λ) := by
  ext c c'
  simp only [chargeOp, quantumIso, StarAlgHom.coe_mk,
    Matrix.of_apply, Matrix.diagonal_apply]
  by_cases h : c = c'
  · subst h
    simp only [ite_true]
    congr 1
    refine Fintype.sum_equiv (siteSmul γ Λ) _ _ (fun x => rfl)
  · have : cfgEquiv Γ Ω₀ γ Λ c ≠ cfgEquiv Γ Ω₀ γ Λ c' :=
      fun e => h ((cfgEquiv Γ Ω₀ γ Λ).injective e)
    simp [h, this]

omit [Nonempty Ω₀] in
/-- The charge of a moved box, as a statement about the operator whose weight is the grand
canonical one. -/
lemma grandCanonicalOp_quantumIso (γ : Γ) (Λ : Finset S) (β μ : ℝ) (H N : Alg (fun _ : S => Ω₀) Λ) :
    quantumIso γ Λ (grandCanonicalOp β μ H N) =
      grandCanonicalOp β μ (quantumIso γ Λ H) (quantumIso γ Λ N) := by
  simp only [grandCanonicalOp, map_smul, map_sub]

/-- **The grand canonical ensemble is covariant**, for an invariant interaction and a uniform
charge. -/
lemma Interaction.grandCanonicalState_smul (I : Interaction (fun _ : S => Ω₀)) {γ : Γ}
    (hI : I.IsInvariant γ) (q₀ : Ω₀ → ℝ) (β μ : ℝ) (Λ : Finset S)
    (a : Alg (fun _ : S => Ω₀) Λ) :
    I.grandCanonicalState (fun _ : S => q₀) β μ (γ • Λ) (quantumIso γ Λ a) =
      I.grandCanonicalState (fun _ : S => q₀) β μ Λ a := by
  have hH := I.hamiltonian_smul hI Λ
  have hN := chargeOp_smul q₀ γ Λ
  change gibbsFunctional (grandCanonicalOp β μ (I.hamiltonian (γ • Λ))
      (chargeOp (fun _ : S => q₀) (γ • Λ))) (quantumIso γ Λ a) =
    gibbsFunctional (grandCanonicalOp β μ (I.hamiltonian Λ) (chargeOp (fun _ : S => q₀) Λ)) a
  rw [← hH, ← hN, ← grandCanonicalOp_quantumIso]
  exact gibbsFunctional_quantumIso γ Λ _ a

end QuasiLocal

end CondensedMatter

end
