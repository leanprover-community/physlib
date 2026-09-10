/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith, Jinzheng Li, Nathaneal Sajan
-/
module

public import Physlib.Relativity.Fermions.Weyl.Metric
public import Physlib.Relativity.DerivAlgebra
public import Physlib.Particles.StandardModel.HiggsBoson.Basic
public import Mathlib.LinearAlgebra.CliffordAlgebra.Conjugation
public import Mathlib.LinearAlgebra.ExteriorAlgebra.Basis
public import Physlib.Mathematics.ConjModule
public import Mathlib.RingTheory.GradedAlgebra.Basic
public import Mathlib.LinearAlgebra.SymmetricAlgebra.Basic
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.LinearAlgebra.CliffordAlgebra.Contraction
public import Mathlib.LinearAlgebra.SymmetricAlgebra.Basis
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.Data.Finsupp.Multiset
public import Mathlib.LinearAlgebra.TensorAlgebra.Basis
public import Physlib.Relativity.Tensors.ComplexTensor.Vector.Pre.Basic
public import Physlib.Relativity.Tensors.RealTensor.CoVector.Representation
public import Physlib.Relativity.SL2C.Basic
/-!

# The basis of the dual real jet-slot algebra

## i. Overview

`LagrangianTheory.dualRealJetAlgebraBasis` is the basis of the symmetric algebra of dual real
jet slots `SymmetricAlgebra ℝ (Module.Dual ℝ Lorentz.CoVector)`, indexed by multisets of
spacetime indices. It is the multiset-indexed basis used throughout the gauge-boson jet
algebra (`GaugeBosons/GaugeJetAlgebra`) to name a monomial in the derivative slots by the
multiset of spacetime indices it carries.

-/

@[expose] public section

open Matrix MatrixGroups Module TensorProduct

namespace LagrangianTheory

/-- The basis of the symmetric algebra of dual real jet slots, indexed by multisets of
  spacetime indices. -/
noncomputable def dualRealJetAlgebraBasis :
    Basis (Multiset (Fin 1 ⊕ Fin 3)) ℝ (SymmetricAlgebra ℝ (Module.Dual ℝ Lorentz.CoVector)) :=
  Lorentz.CoVector.basis.dualBasis.symmetricAlgebra.reindex Multiset.toFinsupp.toEquiv.symm

/-- The multiset basis of the dual derivative symbols, as a basis vector of the
  symmetric algebra at the corresponding multi-index. -/
lemma dualRealJetAlgebraBasis_apply (s : Multiset (Fin 1 ⊕ Fin 3)) :
    dualRealJetAlgebraBasis s =
      Lorentz.CoVector.basis.dualBasis.symmetricAlgebra (Multiset.toFinsupp s) := by
  rw [dualRealJetAlgebraBasis, Basis.reindex_apply, Equiv.symm_symm]
  rfl

/-- The multiset basis vectors of the real dual derivative slots multiply by adding the
  multisets. -/
lemma dualRealJetAlgebraBasis_mul (s t : Multiset (Fin 1 ⊕ Fin 3)) :
    dualRealJetAlgebraBasis s * dualRealJetAlgebraBasis t =
      dualRealJetAlgebraBasis (s + t) := by
  rw [dualRealJetAlgebraBasis_apply, dualRealJetAlgebraBasis_apply,
    dualRealJetAlgebraBasis_apply, map_add]
  simp only [Basis.symmetricAlgebra, Basis.map_apply,
    show ∀ p, (SymmetricAlgebra.equivMvPolynomial
        Lorentz.CoVector.basis.dualBasis).symm.toLinearEquiv p =
      (SymmetricAlgebra.equivMvPolynomial Lorentz.CoVector.basis.dualBasis).symm p
      from fun _ => rfl,
    ← map_mul, MvPolynomial.coe_basisMonomials]
  simp only [MvPolynomial.monomial_mul, mul_one]

/-- The multiset basis of the real dual derivative slots at the empty multiset is the
  unit. -/
lemma dualRealJetAlgebraBasis_nil :
    dualRealJetAlgebraBasis (0 : Multiset (Fin 1 ⊕ Fin 3)) = 1 := by
  rw [dualRealJetAlgebraBasis_apply,
    show Multiset.toFinsupp (0 : Multiset (Fin 1 ⊕ Fin 3)) = 0 by simp,
    Basis.symmetricAlgebra, Basis.map_apply,
    show (SymmetricAlgebra.equivMvPolynomial
        Lorentz.CoVector.basis.dualBasis).symm.toLinearEquiv
        ((MvPolynomial.basisMonomials (Fin 1 ⊕ Fin 3) ℝ) 0) =
      (SymmetricAlgebra.equivMvPolynomial Lorentz.CoVector.basis.dualBasis).symm
        ((MvPolynomial.basisMonomials (Fin 1 ⊕ Fin 3) ℝ) 0) from rfl,
    show (MvPolynomial.basisMonomials (Fin 1 ⊕ Fin 3) ℝ) (0 : (Fin 1 ⊕ Fin 3) →₀ ℕ)
        = 1 from by
      rw [MvPolynomial.coe_basisMonomials]
      show MvPolynomial.monomial 0 1 = 1
      rw [MvPolynomial.monomial_zero', MvPolynomial.C_1],
    map_one]

/-- The multiset basis of the real dual derivative slots at a singleton index. -/
lemma dualRealJetAlgebraBasis_singleton (μ : Fin 1 ⊕ Fin 3) :
    dualRealJetAlgebraBasis ({μ} : Multiset (Fin 1 ⊕ Fin 3)) =
      SymmetricAlgebra.ι ℝ (Module.Dual ℝ Lorentz.CoVector)
        (Lorentz.CoVector.basis.dualBasis μ) := by
  have h : (MvPolynomial.basisMonomials (Fin 1 ⊕ Fin 3) ℝ) (Finsupp.single μ 1) =
      MvPolynomial.X μ := rfl
  rw [dualRealJetAlgebraBasis, Basis.reindex_apply, Equiv.symm_symm,
    show Multiset.toFinsupp.toEquiv ({μ} : Multiset (Fin 1 ⊕ Fin 3)) =
      Finsupp.single μ 1 by simp,
    Basis.symmetricAlgebra, Basis.map_apply, h]
  simp

end LagrangianTheory
