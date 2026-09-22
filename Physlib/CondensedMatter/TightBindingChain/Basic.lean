/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.QuantumMechanics.HilbertSpaces.FiniteTarget.Basic
/-!

# The tight binding chain

## i. Overview

The tight binding chain corresponds to an electron in motion
in a 1d solid with the assumption the electron can sit only on the atoms of the solid.

The solid is assumed to consist of `N` sites with a separation of `a` between them

Mathematically, the tight binding chain corresponds to a
QM problem located on a lattice with only self and nearest neighbour interactions,
with periodic boundary conditions.

## ii. Key results

- `TightBindingChain` : The physical parameters making up the tight binding chain.
- `localizedState` : The orthonormal basis of localized states.
- `hamiltonian` : The Hamiltonian of the tight binding chain.
- `BrillouinZone` : The Brillouin zone of the tight binding chain.
- `QuantaWaveNumber` : The quantized wavenumbers of the energy eigenstates.
- `energyEigenstate` : The energy eigenstates of the tight binding chain.
- `energyEigenvalue` : The energy eigenvalues of the tight binding chain.
- `hamiltonian_energyEigenstate` : The Hamiltonian acting on an energy eigenstate
  gives the corresponding energy eigenvalue times the energy eigenstate.

## iii. Table of contents

- A. The setup
  - A.1. The input data for the tight binding chain
  - A.2. The Hilbert space
- B. The localized states
  - B.1. The orthonormal basis of localized states
  - B.2. Notation for localized states
  - B.3. Orthonormality of the localized states
- C. The operator `|m⟩⟨n|`
  - C.1. Definition of the operator `|m⟩⟨n|`
  - C.2. Notation for the operator `|m⟩⟨n|`
  - C.3. The operator `|m⟩⟨n|` applied to a localized state
- D. The Hamiltonian of the tight binding chain
  - D.1. Hermiticity of the Hamiltonian
  - D.2. Hamiltonian applied to a localized state
  - D.3. Mean energy of a localized state
- E. The Brillouin zone and quantized wavenumbers
  - E.1. The Brillouin zone
  - E.2. The quantized wavenumbers of the energy eigenstates
  - E.3. Wavenumbers lie in the Brillouin zone
  - E.4. Expotentials related to the quantized wavenumbers
- F. The energy eigenstates and eigenvalues
  - F.1. The energy eigenstates
  - F.2. Orthonormality of the energy eigenstates
  - F.3. The energy eigenvalues
  - F.4. The time-independent Schrodinger equation

## iv. References

* https://www.damtp.cam.ac.uk/user/tong/aqm/aqmtwo.pdf. [ref: tong_statistical_physics]
-/

@[expose] public section

namespace CondensedMatter

/-!

## A. The setup

-/

/-!

### A.1. The input data for the tight binding chain

-/

/-- The physical parameters making up the tight binding chain. -/
structure TightBindingChain where
  /-- The number of sites, or atoms, in the chain -/
  N : Nat
  [N_ne_zero : NeZero N]
  /-- The distance between the sites -/
  a : ℝ
  a_pos : 0 < a
  /-- The energy associate with a particle sitting at a fixed site. -/
  E0 : ℝ
  /-- The hopping parameter. -/
  t : ℝ

namespace TightBindingChain
open InnerProductSpace
variable (T : TightBindingChain)

instance : NeZero T.N := T.N_ne_zero

/-!

### A.2. The Hilbert space

-/

/-- The Hilbert space of a `TightBindingchain` is the `N`-dimensional finite dimensional
Hilbert space. -/
abbrev HilbertSpace := QuantumMechanics.FiniteHilbertSpace (Fin T.N)

/-!

## B. The localized states

Localized states correspond to the electron being located on a specific site in the chain.

-/

/-!

### B.1. The orthonormal basis of localized states

-/

/-- The eigenstate corresponding to the particle been located on the `n`th site. -/
noncomputable def localizedState {T : TightBindingChain} :
    OrthonormalBasis (Fin T.N) ℂ (HilbertSpace T) :=
  QuantumMechanics.FiniteHilbertSpace.basisFun (Fin T.N)

/-!

### B.2. Notation for localized states

-/

@[inherit_doc localizedState]
scoped notation "|" n "⟩" => localizedState n

/-- The inner product of two localized states. -/
scoped notation "⟨" m "|" n "⟩" => ⟪localizedState m, localizedState n⟫_ℂ

/-!

### B.3. Orthonormality of the localized states

-/

/-- The localized states are normalized. -/
lemma localizedState_orthonormal : Orthonormal ℂ (localizedState (T := T)) :=
  (localizedState (T := T)).orthonormal

lemma localizedState_orthonormal_eq_ite (m n : Fin T.N) :
    ⟨m|n⟩ = if m = n then 1 else 0 := orthonormal_iff_ite.mp T.localizedState_orthonormal _ _

/-!

## C. The operator `|m⟩⟨n|`

-/

/-!

### C.1. Definition of the operator `|m⟩⟨n|`

-/

/-- The linear map `|m⟩⟨n|` for `⟨n|` localized states. -/
noncomputable def localizedComp {T : TightBindingChain} (m n : Fin T.N) :
    T.HilbertSpace →ₗ[ℂ] T.HilbertSpace where
  toFun ψ := ⟪|n⟩, ψ⟫_ℂ • |m⟩
  map_add' ψ1 ψ2 := by rw [inner_add_right, add_smul]
  map_smul' _ _ := by rw [inner_smul_right, RingHom.id_apply, smul_smul]

/-!

### C.2. Notation for the operator `|m⟩⟨n|`

-/

@[inherit_doc localizedComp]
scoped notation "|" n "⟩⟨" m "|" => localizedComp n m

/-!

### C.3. The operator `|m⟩⟨n|` applied to a localized state

-/
lemma localizedComp_apply_localizedState (m n p : Fin T.N) :
    |m⟩⟨n| |p⟩ = if n = p then |m⟩ else 0 := by
  rw [localizedComp, LinearMap.coe_mk, AddHom.coe_mk,
    T.localizedState_orthonormal_eq_ite n p, ite_smul, one_smul, zero_smul]

/-- The adjoint of localizedComp |m⟩⟨n| is |n⟩⟨m|. -/
lemma localizedComp_adjoint (m n : Fin T.N) (ψ φ : T.HilbertSpace) :
    ⟪|m⟩⟨n| ψ, φ⟫_ℂ = ⟪ψ, |n⟩⟨m| φ⟫_ℂ := by
  simp only [localizedComp, LinearMap.coe_mk, AddHom.coe_mk, inner_smul_left, inner_smul_right,
    inner_conj_symm]
  ring

/-!

## D. The Hamiltonian of the tight binding chain

-/

/-- The Hamiltonian of the tight binding chain with periodic
  boundary conditions is given by `E₀ ∑ n, |n⟩⟨n| - t ∑ n, (|n⟩⟨n + 1| + |n + 1⟩⟨n|)`.
  The periodic boundary conditions is manifested by the `+` in `n + 1` being
  within `Fin T.N` (that is modulo `T.N`). -/
noncomputable def hamiltonian : T.HilbertSpace →ₗ[ℂ] T.HilbertSpace :=
  T.E0 • ∑ n : Fin T.N, |n⟩⟨n| - T.t • ∑ n : Fin T.N, (|n⟩⟨n + 1| + |n + 1⟩⟨n|)

/-!

### D.1. Hermiticity of the Hamiltonian

-/

/-- The hamiltonian of the tight binding chain is hermitian. -/
lemma hamiltonian_hermitian (ψ φ : T.HilbertSpace) :
    ⟪T.hamiltonian ψ, φ⟫_ℂ = ⟪ψ, T.hamiltonian φ⟫_ℂ := by
  simp only [hamiltonian, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.coe_sum,
    Finset.sum_apply, LinearMap.add_apply, inner_sub_left, inner_sub_right]
  congr 1
  · -- E0 term
    simp only [Finset.smul_sum, sum_inner, inner_sum, inner_smul_left_eq_smul,
      inner_smul_right_eq_smul, localizedComp_adjoint]
  · -- t term
    simp only [Finset.smul_sum, smul_add, sum_inner, inner_sum, inner_add_left, inner_add_right,
      inner_smul_left_eq_smul, inner_smul_right_eq_smul, localizedComp_adjoint]
    exact Finset.sum_congr rfl fun n _ => by ring

/-!

### D.2. Hamiltonian applied to a localized state

-/

/-- The Hamiltonian applied to the localized state `|n⟩` gives
  `T.E0 • |n⟩ - T.t • (|n + 1⟩ + |n - 1⟩)`. -/
lemma hamiltonian_apply_localizedState (n : Fin T.N) :
    T.hamiltonian |n⟩ = (T.E0 : ℂ) • |n⟩ - (T.t : ℂ) • (|n + 1⟩ + |n - 1⟩) := by
  simp only [hamiltonian, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.coe_sum,
    Finset.sum_apply, LinearMap.add_apply, smul_add, Finset.sum_add_distrib,
    localizedComp_apply_localizedState, ← eq_sub_iff_add_eq, Finset.sum_ite_eq', Finset.mem_univ,
    ite_true]
  module

/-!

### D.3. Mean energy of a localized state

-/

/-- The energy of a localized state in the tight binding chain is `E0`.
  This lemma assumes that there is more then one site in the chain otherwise the
  result is not true. -/
lemma energy_localizedState (n : Fin T.N) (htn : 1 < T.N) : ⟪|n⟩, T.hamiltonian |n⟩⟫_ℂ = T.E0 := by
  rw [hamiltonian_apply_localizedState]
  simp only [smul_add, inner_sub_right, inner_add_right, inner_smul_right,
    localizedState_orthonormal_eq_ite, ↓reduceIte, mul_one, left_eq_add, eq_sub_iff_add_eq,
    add_eq_left, Fin.one_eq_zero_iff, mul_ite, mul_zero, sub_eq_self]
  simp [show T.N ≠ 1 from by omega]

/-!

## E. The Brillouin zone and quantized wavenumbers

-/

/-!

### E.1. The Brillouin zone

-/

/-- The Brillouin zone of the tight binding model is `[-π/a, π/a)`.
  This is the set in which wave functions are uniquely defined. -/
def BrillouinZone : Set ℝ := Set.Ico (- Real.pi / T.a) (Real.pi / T.a)

/-!

### E.2. The quantized wavenumbers of the energy eigenstates

-/

/-- The wavenumbers associated with the energy eigenstates.
  This corresponds to the set `2 π / (a N) * (n - ⌊N/2⌋)` for `n : Fin T.N`.
  It is defined as such so it sits in the Brillouin zone. -/
def QuantaWaveNumber : Set ℝ := {x | (∃ n : Fin T.N,
    2 * Real.pi / (T.a * T.N) * ((n : ℝ) - (T.N / 2 : ℕ)) = x)}

/-!

### E.3. Wavenumbers lie in the Brillouin zone

-/

/-- The quantized wavenumbers form a subset of the `BrillouinZone`. -/
lemma quantaWaveNumber_subset_brillouinZone : T.QuantaWaveNumber ⊆ T.BrillouinZone := by
  rintro _ ⟨n, rfl⟩
  have hT := T.a_pos
  have hNpos : 0 < T.N := lt_of_le_of_lt (Nat.zero_le _) n.isLt
  simp only [BrillouinZone, Set.mem_Ico]
  generalize T.N = x at *
  generalize T.a = a at *
  have hx : (0 : ℝ) < x := by exact_mod_cast hNpos
  have hn : (n : ℝ) + 1 ≤ x := by exact_mod_cast n.isLt
  have hn0 : (0 : ℝ) ≤ n := by positivity
  have hx2 : 2 * ((x / 2 : ℕ) : ℝ) ≤ x := by exact_mod_cast (by omega : 2 * (x / 2) ≤ x)
  have hx2' : (x : ℝ) ≤ 2 * ((x / 2 : ℕ) : ℝ) + 1 := by
    exact_mod_cast (by omega : x ≤ 2 * (x / 2) + 1)
  refine ⟨?_, ?_⟩
  · rw [div_mul_eq_mul_div, div_le_div_iff₀ hT (mul_pos hT hx)]
    nlinarith [hx2, hn0, mul_pos Real.pi_pos hT]
  · rw [div_mul_eq_mul_div, div_lt_div_iff₀ (mul_pos hT hx) hT]
    nlinarith [hn, hx2', mul_pos Real.pi_pos hT]

/-!

### E.4. Expotentials related to the quantized wavenumbers

-/

lemma quantaWaveNumber_exp_N (n : ℕ) (k : T.QuantaWaveNumber) :
    Complex.exp (Complex.I * k * n * T.N * T.a) = 1 := by
  refine Complex.exp_eq_one_iff.mpr ?_
  obtain ⟨_, m, rfl⟩ := k
  use ((m : Int) - (T.N / 2 : ℕ)) * (n : ℤ)
  have hpp : (T.N : ℂ) ≠ 0 := by simp [Ne.symm (NeZero.ne' T.N)]
  have hT' : (T.a : ℂ) ≠ 0 := Complex.ne_zero_of_re_pos T.a_pos
  simp only [Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_ofNat, Complex.ofReal_natCast,
    Complex.ofReal_sub, Int.cast_mul, Int.cast_sub, Int.cast_natCast]
  field_simp

lemma quantaWaveNumber_exp_sub_one (n : Fin T.N) (k : T.QuantaWaveNumber) :
    Complex.exp (Complex.I * k * (n - 1).val * T.a) =
    Complex.exp (Complex.I * k * n * T.a) * Complex.exp (- Complex.I * k * T.a) := by
  rw [Fin.val_sub]
  trans Complex.exp (Complex.I * ↑↑k * ↑(((T.N - 1 + n)/T.N) * T.N + (n - 1).val) * ↑T.a)
  · simp only [Nat.cast_add, Nat.cast_mul]
    have h0 : (Complex.I * ↑↑k * (↑((T.N - 1 + ↑n) / T.N) * ↑T.N + (n - 1).val) * ↑T.a)
        = Complex.I * ↑↑k * ↑((T.N - 1 + ↑n) / T.N) * ↑T.N * ↑T.a +
        Complex.I * ↑↑k * ((n - 1).val* ↑T.a) := by ring
    rw [h0, Complex.exp_add, quantaWaveNumber_exp_N]
    simp only [Fin.val_one', one_mul]
    congr 1
    simp only [mul_assoc, mul_eq_mul_left_iff, mul_eq_mul_right_iff, Nat.cast_inj,
      Complex.ofReal_eq_zero, Complex.I_ne_zero, or_false]
    aesop
  · have hx : (((T.N - 1 + n)/T.N) * T.N + (n - 1).val) =
        (T.N - 1 + n) := by
      conv_rhs => rw [← Nat.div_add_mod' (a := T.N - 1 + n) (b := T.N)]
      congr
      by_cases hn : T.N = 1
      · simp only [hn, tsub_self, zero_add]
        have h0 : n = 0 := by omega
        subst h0
        simpa using hn
      · rw [@Fin.val_sub]
        congr
        simp [Nat.one_mod_eq_one.mpr hn]
    rw [hx]
    have hl : (Complex.I * ↑↑k * ↑(T.N - 1 + ↑n) * ↑T.a) =
        Complex.I * ↑↑k * n * ↑T.a + Complex.I * ↑↑k * ↑(T.N - 1) * ↑T.a := by
      simp only [Nat.cast_add]
      ring
    rw [hl, Complex.exp_add]
    congr 1
    rw [Nat.cast_pred (Nat.pos_of_neZero T.N)]
    have hl : (Complex.I * ↑↑k * (↑T.N - 1) * ↑T.a) =
      Complex.I * ↑↑k * (1 : ℕ) * ↑T.N * ↑T.a + (- Complex.I * ↑↑k * ↑T.a) := by ring
    rw [hl, Complex.exp_add, quantaWaveNumber_exp_N, neg_mul, one_mul]

lemma quantaWaveNumber_exp_add_one (n : Fin T.N) (k : T.QuantaWaveNumber) :
    Complex.exp (Complex.I * k * (n + 1).val * T.a) =
    Complex.exp (Complex.I * k * n * T.a) * Complex.exp (Complex.I * k * T.a) := by
  conv_rhs =>
    rw [show n = (n + 1) - 1 from (add_sub_cancel_right n 1).symm,
      quantaWaveNumber_exp_sub_one, mul_assoc, ← Complex.exp_add]
    simp

/-!

## F. The energy eigenstates and eigenvalues

-/

/-!

### F.1. The energy eigenstates

-/

/-- The energy eigenstates of the tight binding chain They are given by
  `∑ n, exp (I * k * n * T.a) • |n⟩`. -/
noncomputable def energyEigenstate (k : T.QuantaWaveNumber) : T.HilbertSpace :=
  ∑ n : Fin T.N, Complex.exp (Complex.I * k * n * T.a) • |n⟩

/-!

### F.2. Orthonormality of the energy eigenstates

-/

/-- The energy eigenstates of the tight binding chain are orthogonal.

This is a fundamental quantum mechanical result: eigenstates of a Hermitian operator
(the Hamiltonian) with distinct eigenvalues are orthogonal. Here we prove it directly
using the periodic boundary conditions which quantize the wavenumbers.

The key physical insight is that different wavenumbers k₁ ≠ k₂ give rise to different
N-th roots of unity exp(i(k₂-k₁)a), and the sum of all N-th roots of unity equals zero. -/
lemma energyEigenstate_orthogonal :
    Pairwise fun k1 k2 => ⟪T.energyEigenstate k1, T.energyEigenstate k2⟫_ℂ = 0 := by
  intro k1 k2 hne
  set ω := Complex.exp (Complex.I * (k2 - k1) * T.a) with hω_def
  -- Each term of the overlap is a power of the `N`-th root of unity `ω`.
  have hterm (n : ℕ) : (starRingEnd ℂ) (Complex.exp (Complex.I * k1 * n * T.a)) *
      Complex.exp (Complex.I * k2 * n * T.a) = ω ^ n := by
    rw [← Complex.exp_conj, ← Complex.exp_add, hω_def, ← Complex.exp_nat_mul]
    simp only [map_mul, Complex.conj_I, Complex.conj_ofReal, Complex.conj_natCast]
    ring_nf
  have hω_pow : ω ^ T.N = 1 := by
    rw [hω_def, ← Complex.exp_nat_mul, show (T.N : ℂ) * (Complex.I * (k2 - k1) * T.a) =
      Complex.I * k2 * (1 : ℕ) * T.N * T.a - Complex.I * k1 * (1 : ℕ) * T.N * T.a by
        push_cast; ring,
      Complex.exp_sub, T.quantaWaveNumber_exp_N 1 k2, T.quantaWaveNumber_exp_N 1 k1, div_one]
  -- Distinct quantized wavenumbers differ by a non-multiple of `2π / a`, so `ω ≠ 1`.
  have hω_ne_one : ω ≠ 1 := fun hω_eq_one => hne <| by
    obtain ⟨_, ⟨n1, rfl⟩⟩ := k1
    obtain ⟨_, ⟨n2, rfl⟩⟩ := k2
    obtain ⟨m, hm⟩ := Complex.exp_eq_one_iff.mp (hω_def ▸ hω_eq_one)
    have ha : (T.a : ℂ) ≠ 0 := Complex.ne_zero_of_re_pos T.a_pos
    have hN : (T.N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne T.N)
    push_cast at hm
    field_simp at hm
    have hm_int : (T.N : ℤ) ∣ (n2 : ℤ) - n1 := ⟨m, by
      have : (n2 : ℂ) - n1 = (T.N : ℂ) * m := by ring_nf at hm ⊢; exact hm
      exact_mod_cast this⟩
    have := Int.eq_zero_of_abs_lt_dvd hm_int
      (abs_lt.mpr ⟨by have := n1.isLt; omega, by have := n2.isLt; omega⟩)
    simp only [show n1.val = n2.val by omega]
  -- The sum of all `N`-th roots of unity vanishes, since `ω ^ N = 1` and `ω ≠ 1`.
  simp only [energyEigenstate, sum_inner]
  simp_rw [inner_sum, inner_smul_left, inner_smul_right, localizedState_orthonormal_eq_ite]
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte, hterm]
  rw [Fin.sum_univ_eq_sum_range (ω ^ ·), geom_sum_eq hω_ne_one, hω_pow, sub_self, zero_div]

/-!

### F.3. The energy eigenvalues

-/

/-- The energy eigenvalue of the tight binding chain for a `k` in `QuantaWaveNumber` is
  `E0 - 2 * t * Real.cos (k * T.a)`. -/
noncomputable def energyEigenvalue (k : T.QuantaWaveNumber) : ℝ :=
  T.E0 - 2 * T.t * Real.cos (k * T.a)

/-!

### F.4. The time-independent Schrodinger equation

-/

/-- The energy eigenstates satisfy the time-independent Schrodinger equation. -/
lemma hamiltonian_energyEigenstate (k : T.QuantaWaveNumber) :
    T.hamiltonian (T.energyEigenstate k) = T.energyEigenvalue k• T.energyEigenstate k := by
  trans (T.energyEigenvalue k : ℂ) • T.energyEigenstate k
  swap
  · rfl
  rw [energyEigenstate]
  have hp1 : (∑ n : Fin T.N, Complex.exp (Complex.I * k * n * T.a) • |n + 1⟩)
    = ∑ n : Fin T.N, Complex.exp (Complex.I * k * (n - 1).val * T.a) • |n⟩ := by
    conv_rhs => rw [← Equiv.sum_comp (Equiv.addRight (1 : Fin T.N))]
    simp [Equiv.coe_addRight, add_sub_cancel_right]
  have hm1 : (∑ n : Fin T.N, Complex.exp (Complex.I * k * n * T.a) • |n - 1⟩)
    = ∑ n : Fin T.N, Complex.exp (Complex.I * k * (n + 1).val * T.a) • |n⟩ := by
    conv_rhs => rw [← Equiv.sum_comp (Equiv.subRight (1 : Fin T.N))]
    simp [Equiv.subRight_apply, sub_add_cancel]
  calc
      _ = ∑ n : Fin T.N, Complex.exp (Complex.I * k * n * T.a) • T.hamiltonian |n⟩ := by simp
      _ = ∑ n : Fin T.N, Complex.exp (Complex.I * k * n * T.a) • (T.E0 • |n⟩
          - T.t • (|n + 1⟩ + |n - 1⟩)) := by
          simp [hamiltonian_apply_localizedState, Complex.coe_smul, smul_add]
      _ = T.E0 • (∑ n : Fin T.N, Complex.exp (Complex.I * k * n * T.a) • |n⟩)
        - T.t • ((∑ n : Fin T.N, Complex.exp (Complex.I * k * n * T.a) • |n + 1⟩) +
          (∑ n : Fin T.N, Complex.exp (Complex.I * k * n * T.a) • |n - 1⟩)) := by
        simp only [smul_add, Finset.smul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun n _ => ?_
        module
      _ = T.E0 • (∑ n : Fin T.N, Complex.exp (Complex.I * k * n * T.a) • |n⟩)
        - T.t • ((∑ n : Fin T.N, Complex.exp (Complex.I * k * (n - 1).val * T.a) • |n⟩) +
          (∑ n : Fin T.N, Complex.exp (Complex.I * k * (n + 1).val * T.a) • |n⟩)) := by
          rw [hp1, hm1]
      _ = ∑ n : Fin T.N, (T.E0 * Complex.exp (Complex.I * k * n * T.a) - T.t *
          (Complex.exp (Complex.I * k * (n - 1).val * T.a) +
          Complex.exp (Complex.I * k * (n + 1).val * T.a))) • |n⟩ := by
        simp [Finset.smul_sum, ← Finset.sum_add_distrib,
          ← add_smul, sub_smul, ← smul_smul, Finset.sum_sub_distrib]
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [smul_smul]
  simp only [quantaWaveNumber_exp_sub_one, quantaWaveNumber_exp_add_one, energyEigenvalue,
    Complex.ofReal_sub, Complex.ofReal_mul, Complex.ofReal_ofNat, Complex.ofReal_cos,
      Complex.cos.eq_1]
  ring_nf

end TightBindingChain
end CondensedMatter
