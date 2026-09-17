/-
Copyright (c) 2026 Eduardo Nava-Hernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eduardo Nava-Hernández, José Arturo Nava-Hernández, Gerardo Gabriel Nava Gómez
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# Obstrucción de traza al conmutador escalar en dimensión finita

Complemento algebraico a la construcción de `T_d`, `P_d` en
`D3_GrafoCamino.lean`: en dimensión finita ningún conmutador matricial
puede ser un múltiplo escalar no nulo de la identidad, mientras que sí
existen pares de matrices unitarias que anticonmutan exactamente.

Dos afirmaciones, independientes entre sí:

1. Todo conmutador matricial `[Q,P] = QP - PQ` tiene traza cero
   (`Matrix.trace_mul_comm`), así que nunca puede igualar `c • 1` para
   `c ≠ 0` (`no_nonzero_scalar_exact_commutator`).
2. Esa obstrucción es sobre el conmutador aditivo; no impide la
   no-conmutatividad multiplicativa: el par de matrices `2×2`
   `W₁ = !![0,1;1,0]`, `W₂ = !![1,0;0,-1]` satisface exactamente
   `W₂ W₁ = -(W₁ W₂)` (`parWeyl_anticonmuta`).
-/

@[expose] public section

noncomputable section

namespace ConmutadorEscalarFinito

/-- Conmutador matricial. -/
def commutator {d : ℕ}
    (Q P : Matrix (Fin d) (Fin d) ℂ) : Matrix (Fin d) (Fin d) ℂ :=
  Q * P - P * Q

/-- La traza de todo conmutador matricial finito es cero. -/
theorem trace_commutator_zero {d : ℕ}
    (Q P : Matrix (Fin d) (Fin d) ℂ) :
    Matrix.trace (commutator Q P) = 0 := by
  rw [commutator, Matrix.trace_sub, Matrix.trace_mul_comm Q P, sub_self]

/-- En dimensión finita positiva, un conmutador no puede ser un múltiplo
escalar no nulo de la identidad. -/
theorem no_nonzero_scalar_exact_commutator {d : ℕ} (hd : 0 < d)
    (Q P : Matrix (Fin d) (Fin d) ℂ) (c : ℂ) (hc : c ≠ 0) :
    commutator Q P ≠ c • (1 : Matrix (Fin d) (Fin d) ℂ) := by
  intro h
  have ht := congrArg Matrix.trace h
  have hleft : Matrix.trace (commutator Q P) = 0 :=
    trace_commutator_zero Q P
  have hright : Matrix.trace (c • (1 : Matrix (Fin d) (Fin d) ℂ)) = c * d := by
    simp
  rw [hleft, hright] at ht
  have hd0 : (d : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hd)
  exact (mul_ne_zero hc hd0) ht.symm

/-- Corolario: en particular, el conmutador tampoco puede igualar un
múltiplo imaginario `i·c` de la identidad para ningún real `c ≠ 0`. -/
theorem commutador_ne_escalar_imaginario {d : ℕ} (hd : 0 < d)
    (Q P : Matrix (Fin d) (Fin d) ℂ) (c : ℝ) (hc : c ≠ 0) :
    commutator Q P ≠ (Complex.I * (c : ℂ)) • (1 : Matrix (Fin d) (Fin d) ℂ) := by
  apply no_nonzero_scalar_exact_commutator hd Q P
  exact mul_ne_zero Complex.I_ne_zero (Complex.ofReal_ne_zero.mpr hc)

/-! ## Un par de Weyl exacto en dimensión dos -/

/-- Primera matriz del par de Weyl `2×2`. -/
def W1 : Matrix (Fin 2) (Fin 2) ℂ :=
  !![0, 1; 1, 0]

/-- Segunda matriz del par de Weyl `2×2`. -/
def W2 : Matrix (Fin 2) (Fin 2) ℂ :=
  !![1, 0; 0, -1]

/-- Relación de Weyl exacta: `W₂ W₁ = -(W₁ W₂)`. La obstrucción de traza de
arriba es sobre el conmutador *aditivo*; no impide esta anticonmutación
*multiplicativa* exacta en dimensión finita. -/
theorem parWeyl_anticonmuta : W2 * W1 = -(W1 * W2) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [W1, W2, Matrix.mul_apply, Fin.sum_univ_two]

/-- En particular, `W₁` y `W₂` no conmutan. -/
theorem parWeyl_no_conmuta : W2 * W1 ≠ W1 * W2 := by
  intro h
  have hij := congrFun (congrFun h (0 : Fin 2)) (1 : Fin 2)
  norm_num [W1, W2, Matrix.mul_apply, Fin.sum_univ_two] at hij

end ConmutadorEscalarFinito
