/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import Physlib.CondensedMatter.TightBindingChain.Basic
public import PhyslibAlpha.CondensedMatter.Bloch.FiniteBloch

/-!

# The tight binding chain as a finite periodic crystal

## i. Overview

The tight binding chain of `N` sites with periodic boundary conditions is a finite periodic
crystal with translation group `Fin N` and one orbital per cell. In the coordinates `⟪|x⟩, ψ⟫`
its Hamiltonian is the hopping operator with the matrix `E0` on the site itself and `-t` to each
of its two neighbours.

## ii. Key results

- `hoppingMatrix` : the hopping matrices of the tight binding chain.
- `hopping_hoppingMatrix` : the Hamiltonian of the tight binding chain is the hopping operator of
  these matrices.

## iii. Table of contents

- A. The Hamiltonian as a hopping operator

## iv. References

None.

-/

@[expose] public section

namespace CondensedMatter
namespace TightBindingChain

open InnerProductSpace FiniteBloch

variable (T : TightBindingChain)

/-!

## A. The Hamiltonian as a hopping operator

-/

/-- The hopping matrices of the tight binding chain as a finite periodic crystal with one orbital
  per cell: `E0` on the site itself and `-t` to each of its two neighbours. -/
noncomputable def hoppingMatrix (r : Fin T.N) : Matrix (Fin 1) (Fin 1) ℂ :=
  ((if r = 0 then (T.E0 : ℂ) else 0) - (if r = 1 then (T.t : ℂ) else 0) -
    (if r = -1 then (T.t : ℂ) else 0)) • 1

/-- The Hamiltonian of the tight binding chain, in the coordinates `⟪|x⟩, ψ⟫`, is the hopping
  operator of the finite periodic crystal with the matrices `hoppingMatrix`. -/
lemma hopping_hoppingMatrix (ψ : T.HilbertSpace) :
    hopping T.hoppingMatrix (fun x _ => ⟪|x⟩, ψ⟫_ℂ) = fun x _ => ⟪|x⟩, T.hamiltonian ψ⟫_ℂ := by
  ext x i
  rw [hopping_apply, ← hamiltonian_hermitian, hamiltonian_apply_localizedState]
  simp only [hoppingMatrix, Matrix.smul_mulVec, Matrix.one_mulVec, Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul, sub_mul, ite_mul, zero_mul, Finset.sum_sub_distrib,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true, sub_zero, sub_neg_eq_add, inner_sub_left,
    inner_add_left, inner_smul_left, Complex.conj_ofReal]
  ring

end TightBindingChain
end CondensedMatter
