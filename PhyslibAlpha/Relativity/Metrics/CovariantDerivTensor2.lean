/-
Copyright (c) 2026 Alex Vergara Gil. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Vergara Gil
-/
module

public import PhyslibAlpha.Relativity.Tensors.Tensor2

/-!

# Levi-Civita covariant derivative of a rank-2 tensor

Three-dimensional covariant derivative of a rank-2 tensor from Christoffel symbols.

## i. Overview

For a rank-2 tensor `K` with coordinate partial derivatives `dK`, the Levi-Civita covariant
derivative is `∇_μ K_{ij} = ∂_μ K_{ij} - Γ^l_{μi} K_{lj} - Γ^l_{μj} K_{il}`.

## ii. Key results

- `InitialData.covariantDerivTensor2` : covariant derivative of a rank-2 tensor.
- `InitialData.covariantDerivTensor2_eq_of_zero` : reduction to partial derivatives when the
  connection vanishes.

## iii. Table of contents

- A. Covariant derivative of a rank-2 tensor

## iv. References

* R. M. Wald, *General Relativity* (1984), Ch. 3 (Sec. 3.1). [ref: wald_1984_general_relativity]
-/

@[expose] public section

namespace GeneralRelativity

namespace InitialData

/-!

## A. Covariant derivative of a rank-2 tensor

The connection acts on each tensor index with the corresponding Christoffel symbol.

-/

/-- Three-dimensional Levi-Civita covariant derivative of a rank-2 tensor `K`:
`∇_μ K_{ij} = ∂_μ K_{ij} - Γ^l_{μi} K_{lj} - Γ^l_{μj} K_{il}`. -/
def covariantDerivTensor2 (Γ : Fin 3 → Fin 3 → Fin 3 → ℝ) (dK : Fin 3 → Tensor2 3)
    (K : Tensor2 3) : Fin 3 → Tensor2 3 :=
  fun μ i j => dK μ i j - (∑ l, Γ l μ i * K l j) - (∑ l, Γ l μ j * K i l)

/-- In locally flat / normal coordinates where the 3D Christoffel symbols vanish (`Γ = 0`),
the covariant derivative `covariantDerivTensor2` reduces to the partial derivative table `dK`. -/
lemma covariantDerivTensor2_eq_of_zero (dK : Fin 3 → Tensor2 3) (K : Tensor2 3) :
    covariantDerivTensor2 0 dK K = dK := by
  ext μ i j
  simp [covariantDerivTensor2]

end InitialData

end GeneralRelativity
