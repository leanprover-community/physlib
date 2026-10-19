/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.Basic.Complex.Basic
public import PhyslibAlpha.Mathematics.RepresentationTheory.Sl2.Classification

/-!
# Abstract angular momentum representations

Packages three endomorphisms obeying the angular momentum commutation relations and
connects them to `sl₂`.

## i. Overview

The commutation relations for three complex-linear angular momentum operators determine an
`sl₂` triple with Cartan operator `2Jz` and raising and lowering operators `Jp` and `Jm`.
This lets Mathlib’s primitive-vector theory classify finite-dimensional irreducible
representations. The square `Jx² + Jy² + Jz²` commutes with the three operators and acts as
`j(j+1)` on an irreducible representation of highest weight `2j`.

## ii. Key results

- `AngularMomentumRepresentation` records the angular momentum commutators.
- `isSl2Triple` identifies `2Jz`, `Jp`, and `Jm` with an `sl₂` triple.
- `Jsq_eq_smul` gives the Casimir eigenvalue on an irreducible representation.
- `magneticBasisVec` defines the lowering-string vectors; no basis theorem is asserted here.

## iii. Table of contents

- A. Angular momentum and its `sl₂` triple
  - A.1. Spin classification

## iv. References

- Mathlib, `Mathlib.Algebra.Lie.Sl2`.

## A. Angular momentum and its `sl₂` triple
-/

@[expose] public section

noncomputable section

namespace PhyslibAlpha.Sl2

attribute [local instance 100] LieRing.ofAssociativeRing

variable (V : Type*) [AddCommGroup V] [Module ℂ V]

/-- Angular momentum representation. Three operators
`Jx, Jy, Jz` on a state space `V`, satisfying the `so(3)` commutation relations
`[Jx,Jy] = iJz` and cyclic permutations. (The physical requirement that they be
self-adjoint on a Hilbert space is out of scope for this algebraic model.) -/
structure AngularMomentumRepresentation where
  /-- The first Cartesian component of angular momentum. -/
  Jx : Module.End ℂ V
  /-- The second Cartesian component of angular momentum. -/
  Jy : Module.End ℂ V
  /-- The third Cartesian component of angular momentum. -/
  Jz : Module.End ℂ V
  comm_xy : ⁅Jx, Jy⁆ = Complex.I • Jz
  comm_yz : ⁅Jy, Jz⁆ = Complex.I • Jx
  comm_zx : ⁅Jz, Jx⁆ = Complex.I • Jy

namespace AngularMomentumRepresentation

variable {V}

/-- Ladder operators. `J± := Jx ± iJy`. -/
def Jp (ρ : AngularMomentumRepresentation V) : Module.End ℂ V := ρ.Jx + Complex.I • ρ.Jy

@[inherit_doc Jp]
def Jm (ρ : AngularMomentumRepresentation V) : Module.End ℂ V := ρ.Jx - Complex.I • ρ.Jy

/-- Commutation relations for the ladder operators:
`[Jz, J±] = ±J±` and `[J+, J-] = 2Jz`. -/
lemma comm_z_p (ρ : AngularMomentumRepresentation V) : ⁅ρ.Jz, ρ.Jp⁆ = ρ.Jp := by
  have hzy : ⁅ρ.Jz, ρ.Jy⁆ = -(Complex.I • ρ.Jx) := by rw [← lie_skew, ρ.comm_yz]
  simp only [Jp, lie_add, lie_smul, ρ.comm_zx, hzy, smul_neg, smul_smul,
    Complex.I_mul_I, neg_smul, neg_neg, one_smul]
  abel

lemma comm_z_m (ρ : AngularMomentumRepresentation V) : ⁅ρ.Jz, ρ.Jm⁆ = -ρ.Jm := by
  have hzy : ⁅ρ.Jz, ρ.Jy⁆ = -(Complex.I • ρ.Jx) := by rw [← lie_skew, ρ.comm_yz]
  simp only [Jm, lie_sub, lie_smul, ρ.comm_zx, hzy, smul_neg, smul_smul,
    Complex.I_mul_I, neg_smul, neg_neg, one_smul]
  abel

lemma comm_p_m (ρ : AngularMomentumRepresentation V) :
    ⁅ρ.Jp, ρ.Jm⁆ = (2 : ℂ) • ρ.Jz := by
  have h1 : ⁅ρ.Jx, ρ.Jm⁆ = ρ.Jz := by
    simp only [Jm, lie_sub, lie_self, lie_smul, ρ.comm_xy, smul_smul, Complex.I_mul_I,
      zero_sub, neg_smul, one_smul, neg_neg]
  have hyx : ⁅ρ.Jy, ρ.Jx⁆ = -(Complex.I • ρ.Jz) := by rw [← lie_skew, ρ.comm_xy]
  have h2 : ⁅ρ.Jy, ρ.Jm⁆ = -(Complex.I • ρ.Jz) := by
    simp only [Jm, lie_sub, lie_self, lie_smul, hyx, smul_zero, sub_zero]
  have hsmul : ⁅Complex.I • ρ.Jy, ρ.Jm⁆ = Complex.I • ⁅ρ.Jy, ρ.Jm⁆ := by
    rw [← lie_skew, lie_smul, ← lie_skew ρ.Jy ρ.Jm, smul_neg]
  have h3 : ⁅ρ.Jp, ρ.Jm⁆ = ⁅ρ.Jx, ρ.Jm⁆ + Complex.I • ⁅ρ.Jy, ρ.Jm⁆ := by
    rw [Jp, add_lie, hsmul]
  rw [h3, h1, h2, smul_neg, smul_smul, Complex.I_mul_I, neg_smul, one_smul, neg_neg,
    two_smul]

/-- Angular momentum generates an `sl₂`-triple, via
`h := 2 • Jz`, `e := J+`, `f := J-` (the doubling of `Jz` reconciles the physicists'
normalization `[Jz,J±]=±J±` with the `sl₂`-triple normalization `[h,e]=2e`).

The hypothesis `ρ.Jz ≠ 0` is necessary: the all-zero representation
(`Jx = Jy = Jz = 0`) satisfies every field of `AngularMomentumRepresentation`
but gives `h = 2 • Jz = 0`, which `IsSl2Triple` explicitly excludes
(`h_ne_zero`) — the trivial, spin-`0` representation does not generate an
honest copy of `sl₂` inside `End(V)`. -/
lemma isSl2Triple (ρ : AngularMomentumRepresentation V) (hz : ρ.Jz ≠ 0) :
    IsSl2Triple ((2 : ℂ) • ρ.Jz) ρ.Jp ρ.Jm where
  h_ne_zero := smul_ne_zero (by norm_num) hz
  lie_e_f := comm_p_m ρ
  lie_h_e_nsmul := by
    have hcast : (2 : ℕ) • ρ.Jz = (2 : ℂ) • ρ.Jz := by
      rw [← Nat.cast_smul_eq_nsmul ℂ]; norm_num
    rw [← hcast, nsmul_lie, comm_z_p]
  lie_h_f_nsmul := by
    have hcast : (2 : ℕ) • ρ.Jz = (2 : ℂ) • ρ.Jz := by
      rw [← Nat.cast_smul_eq_nsmul ℂ]; norm_num
    rw [← hcast, nsmul_lie, comm_z_m, smul_neg]

/-! ### A.1. Spin classification -/

/-- Irreducibility of an angular momentum representation: no proper subspace is
invariant under `Jx`, `Jy`, and `Jz` simultaneously. -/
def IsIrreducible (ρ : AngularMomentumRepresentation V) : Prop :=
  ∀ W : Submodule ℂ V,
    (∀ v ∈ W, ρ.Jx v ∈ W) → (∀ v ∈ W, ρ.Jy v ∈ W) → (∀ v ∈ W, ρ.Jz v ∈ W) →
    W = ⊥ ∨ W = ⊤

/-- Irreducibility transfers along the bridge:
`ρ.IsIrreducible` agrees with irreducibility of the induced module for the `sl₂`-subalgebra
generated by `(2Jz, J+, J-)` (via the automatic `LieSubalgebra.lieRingModule`/`lieModule`
instances restricting the tautological `Module.End ℂ V`-action on `V`). -/
lemma Jx_mem_sl2 (ρ : AngularMomentumRepresentation V) (hz : ρ.Jz ≠ 0) :
    ρ.Jx ∈ (ρ.isSl2Triple hz).toLieSubalgebra ℂ := by
  exact IsSl2Triple.mem_toLieSubalgebra_iff.mpr
    ⟨(1 / 2 : ℂ), (1 / 2 : ℂ), 0, by simp [Jp, Jm]; module⟩

lemma Jy_mem_sl2 (ρ : AngularMomentumRepresentation V) (hz : ρ.Jz ≠ 0) :
    ρ.Jy ∈ (ρ.isSl2Triple hz).toLieSubalgebra ℂ := by
  refine IsSl2Triple.mem_toLieSubalgebra_iff.mpr
    ⟨(-Complex.I / 2 : ℂ), (Complex.I / 2 : ℂ), 0, ?_⟩
  simp only [Jp, Jm, zero_smul, add_zero]
  rw [smul_add, smul_sub, smul_smul, smul_smul]
  have h₁ : (-Complex.I / 2 * Complex.I : ℂ) = 1 / 2 := by
    rw [div_mul_eq_mul_div, neg_mul, Complex.I_mul_I]; ring
  have h₂ : (Complex.I / 2 * Complex.I : ℂ) = -(1 / 2) := by
    rw [div_mul_eq_mul_div, Complex.I_mul_I]; ring
  rw [h₁, h₂]
  module

lemma Jz_mem_sl2 (ρ : AngularMomentumRepresentation V) (hz : ρ.Jz ≠ 0) :
    ρ.Jz ∈ (ρ.isSl2Triple hz).toLieSubalgebra ℂ := by
  refine IsSl2Triple.mem_toLieSubalgebra_iff.mpr ⟨0, 0, (1 / 2 : ℂ), ?_⟩
  rw [comm_p_m]
  module

lemma Jp_mem_of_invariant (ρ : AngularMomentumRepresentation V)
    (W : Submodule ℂ V) (hx : ∀ v ∈ W, ρ.Jx v ∈ W)
    (hy : ∀ v ∈ W, ρ.Jy v ∈ W) {v : V} (hv : v ∈ W) : ρ.Jp v ∈ W := by
  change ρ.Jx v + Complex.I • ρ.Jy v ∈ W
  exact W.add_mem (hx v hv) (W.smul_mem _ (hy v hv))

lemma Jm_mem_of_invariant (ρ : AngularMomentumRepresentation V)
    (W : Submodule ℂ V) (hx : ∀ v ∈ W, ρ.Jx v ∈ W)
    (hy : ∀ v ∈ W, ρ.Jy v ∈ W) {v : V} (hv : v ∈ W) : ρ.Jm v ∈ W := by
  change ρ.Jx v - Complex.I • ρ.Jy v ∈ W
  exact W.sub_mem (hx v hv) (W.smul_mem _ (hy v hv))

lemma sl2_invariant_of_angular_invariant (ρ : AngularMomentumRepresentation V)
    (hz : ρ.Jz ≠ 0) (W : Submodule ℂ V)
    (hx : ∀ v ∈ W, ρ.Jx v ∈ W) (hy : ∀ v ∈ W, ρ.Jy v ∈ W)
    (hzW : ∀ v ∈ W, ρ.Jz v ∈ W) {x : ↥((ρ.isSl2Triple hz).toLieSubalgebra ℂ)}
    {v : V} (hv : v ∈ W) : ⁅x, v⁆ ∈ W := by
  obtain ⟨c₁, c₂, c₃, hc⟩ := IsSl2Triple.mem_toLieSubalgebra_iff.mp x.property
  change (x : Module.End ℂ V) v ∈ W
  rw [hc]
  simp only [LinearMap.add_apply, LinearMap.smul_apply]
  refine W.add_mem (W.add_mem (W.smul_mem _ (Jp_mem_of_invariant ρ W hx hy hv))
    (W.smul_mem _ (Jm_mem_of_invariant ρ W hx hy hv))) (W.smul_mem _ ?_)
  rw [comm_p_m]
  exact W.smul_mem _ (hzW v hv)

/-- A nonzero `Jz` forces the representation space to be nontrivial. -/
lemma nontrivial_of_Jz_ne_zero (ρ : AngularMomentumRepresentation V) (hz : ρ.Jz ≠ 0) :
    Nontrivial V := by
  rcases subsingleton_or_nontrivial V with hsub | hnt
  · exact absurd (LinearMap.ext fun v => @Subsingleton.elim V hsub _ _ : ρ.Jz = 0) hz
  · exact hnt

/-- Lie submodules are stable under every operator in the generated subalgebra. -/
lemma lieSubmodule_stable (ρ : AngularMomentumRepresentation V) (hz : ρ.Jz ≠ 0)
    (N : LieSubmodule ℂ ↥((ρ.isSl2Triple hz).toLieSubalgebra ℂ) V) {x : Module.End ℂ V}
    (hx : x ∈ (ρ.isSl2Triple hz).toLieSubalgebra ℂ) : ∀ v ∈ (N : Submodule ℂ V), x v ∈ N := by
  intro v hv
  have := N.lie_mem (x := ⟨x, hx⟩) hv
  simpa [LieSubalgebra.coe_bracket_of_module, Module.End.lie_apply] using this

lemma angular_irreducible_implies_sl2 (ρ : AngularMomentumRepresentation V)
    (hz : ρ.Jz ≠ 0) (hirr : ρ.IsIrreducible) :
    LieModule.IsIrreducible ℂ ↥((ρ.isSl2Triple hz).toLieSubalgebra ℂ) V := by
  have := nontrivial_of_Jz_ne_zero ρ hz
  refine LieModule.IsIrreducible.mk (fun N hN => ?_)
  rcases hirr N (lieSubmodule_stable ρ hz N (Jx_mem_sl2 ρ hz))
      (lieSubmodule_stable ρ hz N (Jy_mem_sl2 ρ hz))
      (lieSubmodule_stable ρ hz N (Jz_mem_sl2 ρ hz)) with hbot | htop
  · exact absurd ((LieSubmodule.toSubmodule_eq_bot N).mp hbot) hN
  · exact (LieSubmodule.toSubmodule_eq_top N).mp htop

lemma sl2_irreducible_implies_angular (ρ : AngularMomentumRepresentation V)
    (hz : ρ.Jz ≠ 0)
    (hirr : LieModule.IsIrreducible ℂ ↥((ρ.isSl2Triple hz).toLieSubalgebra ℂ) V) :
    ρ.IsIrreducible := by
  intro W hWx hWy hWz
  let N : LieSubmodule ℂ ↥((ρ.isSl2Triple hz).toLieSubalgebra ℂ) V :=
    { __ := W, lie_mem := fun {x v} hv =>
        sl2_invariant_of_angular_invariant ρ hz W hWx hWy hWz hv }
  have hNW : (N : Submodule ℂ V) = W := rfl
  rcases eq_bot_or_eq_top N with hbot | htop
  · exact Or.inl (hNW ▸ congrArg LieSubmodule.toSubmodule hbot ▸ LieSubmodule.bot_toSubmodule)
  · exact Or.inr (hNW ▸ congrArg LieSubmodule.toSubmodule htop ▸ LieSubmodule.top_toSubmodule)

/-- Invariance under `Jx`, `Jy`, `Jz` is equivalent to irreducibility for the generated
`sl₂` Lie subalgebra. -/
lemma isIrreducible_iff (ρ : AngularMomentumRepresentation V) (hz : ρ.Jz ≠ 0) :
    ρ.IsIrreducible ↔ LieModule.IsIrreducible ℂ (↥((ρ.isSl2Triple hz).toLieSubalgebra ℂ)) V := by
  constructor
  · exact angular_irreducible_implies_sl2 ρ hz
  · exact sl2_irreducible_implies_angular ρ hz

/-- A finite-dimensional irreducible angular momentum representation is isomorphic to a
standard `sl₂` module for the subalgebra generated by `(2Jz, Jp, Jm)`. -/
lemma spin_classification [FiniteDimensional ℂ V] (ρ : AngularMomentumRepresentation V)
    (hz : ρ.Jz ≠ 0) (hirr : ρ.IsIrreducible) :
    ∃ n : ℕ, letI := standardSl2ModuleLieRingModule (K := ℂ) (n := n) (ρ.isSl2Triple hz)
      Nonempty (V ≃ₗ⁅ℂ, ↥((ρ.isSl2Triple hz).toLieSubalgebra ℂ)⁆ StandardSl2Module ℂ n) := by
  have : LieModule.IsIrreducible ℂ ↥((ρ.isSl2Triple hz).toLieSubalgebra ℂ) V :=
    (isIrreducible_iff ρ hz).mp hirr
  exact classification (ρ.isSl2Triple hz)

/-- `J+J- = Jx²+Jy²+Jz`: the standard ladder-operator identity, a purely algebraic
consequence of the commutation relations (no representation theory needed). Used to
reduce `Jsq_eq_smul` to a statement about `Jp * Jm`, via
`J² = Jp*Jm + Jz*Jz - Jz` (equivalently `Jm*Jp + Jz*Jz + Jz`). -/
lemma Jp_mul_Jm (ρ : AngularMomentumRepresentation V) :
    ρ.Jp * ρ.Jm = ρ.Jx * ρ.Jx + ρ.Jy * ρ.Jy + ρ.Jz := by
  have hexpand : ρ.Jp * ρ.Jm = ρ.Jx * ρ.Jx + ρ.Jy * ρ.Jy -
      Complex.I • (ρ.Jx * ρ.Jy - ρ.Jy * ρ.Jx) := by
    simp only [Jp, Jm, add_mul, mul_sub, smul_mul_assoc, mul_smul_comm, smul_add, smul_smul,
      Complex.I_mul_I, neg_one_smul, smul_sub]
    abel
  have hcomm : ρ.Jx * ρ.Jy - ρ.Jy * ρ.Jx = Complex.I • ρ.Jz := by
    have := ρ.comm_xy
    rwa [LieRing.of_associative_ring_bracket] at this
  rw [hexpand, hcomm, smul_smul, Complex.I_mul_I, neg_one_smul]
  abel

/-- `J² = J+J- + Jz² - Jz`: a purely algebraic consequence of the commutation
relations (no representation theory needed), used to reduce `Jsq_eq_smul` to a
statement about the ladder operators. -/
lemma Jsq_eq_Jp_mul_Jm (ρ : AngularMomentumRepresentation V) :
    ρ.Jx * ρ.Jx + ρ.Jy * ρ.Jy + ρ.Jz * ρ.Jz =
      ρ.Jp * ρ.Jm + ρ.Jz * ρ.Jz - ρ.Jz := by
  rw [Jp_mul_Jm]; abel

/-- Product Leibniz rule for the associative-ring bracket on `Module.End ℂ V`:
`⁅a*x, z⁆ = a*⁅x,z⁆ + ⁅a,z⁆*x`. -/
lemma leibniz_end (a x z : Module.End ℂ V) :
    (⁅a * x, z⁆ : Module.End ℂ V) = a * ⁅x, z⁆ + ⁅a, z⁆ * x := by
  simp only [LieRing.of_associative_ring_bracket]
  noncomm_ring

/-- Unfolds the associative-ring bracket relation `⁅a, b⁆ = c` into `a * b = b * a + c`. -/
lemma mul_eq_of_lie_eq {a b c : Module.End ℂ V} (h : (⁅a, b⁆ : Module.End ℂ V) = c) :
    a * b = b * a + c := by
  rw [← h, LieRing.of_associative_ring_bracket]
  abel

/-- `J²` commutes with `J+`: a step towards showing `J²` is central, hence (on an
irreducible module) acts as a scalar. -/
lemma Jsq_comm_p (ρ : AngularMomentumRepresentation V) :
    (⁅ρ.Jx * ρ.Jx + ρ.Jy * ρ.Jy + ρ.Jz * ρ.Jz, ρ.Jp⁆ : Module.End ℂ V) = 0 := by
  rw [Jsq_eq_Jp_mul_Jm, sub_lie, add_lie, leibniz_end, leibniz_end]
  have hmp : (⁅ρ.Jm, ρ.Jp⁆ : Module.End ℂ V) = -((2 : ℂ) • ρ.Jz) := by
    rw [← lie_skew, comm_p_m]
  have hpp : (⁅ρ.Jp, ρ.Jp⁆ : Module.End ℂ V) = 0 := lie_self ρ.Jp
  have hzp : (⁅ρ.Jz, ρ.Jp⁆ : Module.End ℂ V) = ρ.Jp := comm_z_p ρ
  rw [hmp, hpp, hzp, zero_mul, add_zero, mul_neg, mul_smul_comm, mul_eq_of_lie_eq hzp]
  module

/-- `J²` commutes with `J-`: a step towards showing `J²` is central, hence (on an
irreducible module) acts as a scalar. -/
lemma Jsq_comm_m (ρ : AngularMomentumRepresentation V) :
    (⁅ρ.Jx * ρ.Jx + ρ.Jy * ρ.Jy + ρ.Jz * ρ.Jz, ρ.Jm⁆ : Module.End ℂ V) = 0 := by
  rw [Jsq_eq_Jp_mul_Jm, sub_lie, add_lie, leibniz_end, leibniz_end]
  have hmm : (⁅ρ.Jm, ρ.Jm⁆ : Module.End ℂ V) = 0 := lie_self ρ.Jm
  have hpm : (⁅ρ.Jp, ρ.Jm⁆ : Module.End ℂ V) = (2 : ℂ) • ρ.Jz := comm_p_m ρ
  have hzm : (⁅ρ.Jz, ρ.Jm⁆ : Module.End ℂ V) = -ρ.Jm := comm_z_m ρ
  rw [hmm, hpm, hzm, mul_zero, zero_add, smul_mul_assoc, mul_neg, neg_mul,
    mul_eq_of_lie_eq hzm]
  module

/-- `J²` commutes with `Jz`: derived from `Jsq_comm_p`/`Jsq_comm_m` via the Jacobi
identity, since `2•Jz = ⁅Jp,Jm⁆`. -/
lemma Jsq_comm_z (ρ : AngularMomentumRepresentation V) :
    (⁅ρ.Jx * ρ.Jx + ρ.Jy * ρ.Jy + ρ.Jz * ρ.Jz, ρ.Jz⁆ : Module.End ℂ V) = 0 := by
  have h2z : (2 : ℂ) • (⁅ρ.Jx * ρ.Jx + ρ.Jy * ρ.Jy + ρ.Jz * ρ.Jz, ρ.Jz⁆ : Module.End ℂ V) = 0 := by
    rw [← lie_smul, show ((2 : ℂ) • ρ.Jz : Module.End ℂ V) = ⁅ρ.Jp, ρ.Jm⁆ from (comm_p_m ρ).symm,
      leibniz_lie, Jsq_comm_p, Jsq_comm_m, zero_lie, lie_zero, add_zero]
  exact (smul_right_inj (two_ne_zero (α := ℂ))).mp (by simpa using h2z)

/-- The quadratic angular momentum operator `Jx² + Jy² + Jz²`. -/
def Jsq (ρ : AngularMomentumRepresentation V) : Module.End ℂ V :=
  ρ.Jx * ρ.Jx + ρ.Jy * ρ.Jy + ρ.Jz * ρ.Jz

/-- On a primitive vector of weight `n`, `Jp Jm` acts by `n`. -/
lemma JpJm_on_primitive (ρ : AngularMomentumRepresentation V) (hz : ρ.Jz ≠ 0)
    {n : ℕ} {v : V} (P : (ρ.isSl2Triple hz).HasPrimitiveVectorWith v (n : ℂ)) :
    ρ.Jp (ρ.Jm v) = (n : ℂ) • v := by
  have hp : ρ.Jp v = 0 := by simpa [Module.End.lie_apply] using P.lie_e
  have hh : (2 : ℂ) • ρ.Jz v = (n : ℂ) • v := by
    simpa [Module.End.lie_apply, LinearMap.smul_apply] using P.lie_h
  have hc : ρ.Jp * ρ.Jm - ρ.Jm * ρ.Jp = (2 : ℂ) • ρ.Jz := by
    simpa only [LieRing.of_associative_ring_bracket] using comm_p_m ρ
  have hv := congrArg (fun T : Module.End ℂ V => T v) hc
  simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.mul_apply] at hv
  rw [hp, map_zero, sub_zero] at hv
  rw [hv, hh]

/-- The Cartan operator acts by half the highest weight on a primitive vector. -/
lemma Jz_on_primitive (ρ : AngularMomentumRepresentation V) (hz : ρ.Jz ≠ 0)
    {n : ℕ} {v : V} (P : (ρ.isSl2Triple hz).HasPrimitiveVectorWith v (n : ℂ)) :
    ρ.Jz v = ((n : ℂ) / 2) • v := by
  have hh : (2 : ℂ) • ρ.Jz v = (n : ℂ) • v := by
    simpa [Module.End.lie_apply, LinearMap.smul_apply] using P.lie_h
  apply (smul_right_inj (two_ne_zero (α := ℂ))).mp
  rw [hh, smul_smul]
  rw [show (2 : ℂ) * ((n : ℂ) / 2) = (n : ℂ) from by ring]

/-- The quadratic operator has the expected eigenvalue on a primitive vector. -/
lemma Jsq_on_primitive (ρ : AngularMomentumRepresentation V) (hz : ρ.Jz ≠ 0)
    {n : ℕ} {v : V} (P : (ρ.isSl2Triple hz).HasPrimitiveVectorWith v (n : ℂ)) :
    ρ.Jsq v = ((n : ℂ) / 2 * ((n : ℂ) / 2 + 1)) • v := by
  have hp := JpJm_on_primitive ρ hz P
  have hzv := Jz_on_primitive ρ hz P
  have heq := congrArg (fun T : Module.End ℂ V => T v) (Jsq_eq_Jp_mul_Jm ρ)
  simp only [LinearMap.add_apply, LinearMap.sub_apply, Module.End.mul_apply] at heq
  change (ρ.Jx * ρ.Jx + ρ.Jy * ρ.Jy + ρ.Jz * ρ.Jz) v = _
  simp only [LinearMap.add_apply, Module.End.mul_apply]
  rw [heq, hp, hzv, map_smul, hzv, smul_smul]
  module

/-- An eigenspace of an endomorphism is stable under commuting endomorphisms. -/
lemma ker_scalar_stable (C A : Module.End ℂ V) (c : ℂ)
    (hCA : (⁅C, A⁆ : Module.End ℂ V) = 0)
    {v : V} (hv : v ∈ LinearMap.ker (C - c • (1 : Module.End ℂ V))) :
    A v ∈ LinearMap.ker (C - c • (1 : Module.End ℂ V)) := by
  have h0 : C * A = A * C := by
    rwa [LieRing.of_associative_ring_bracket, sub_eq_zero] at hCA
  have hCv : C v = c • v := by
    simpa [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
      Module.End.one_apply, sub_eq_zero] using hv
  have heq := congrArg (fun T : Module.End ℂ V => T v) h0
  simp only [Module.End.mul_apply] at heq
  simp only [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
    Module.End.one_apply, sub_eq_zero]
  rw [heq, hCv, map_smul]

/-- `Jx` is half the sum of the ladder operators. -/
lemma Jx_apply_eq (ρ : AngularMomentumRepresentation V) (v : V) :
    ρ.Jx v = ((1 : ℂ) / 2) • (ρ.Jp v + ρ.Jm v) := by
  simp only [Jp, Jm, LinearMap.add_apply, LinearMap.sub_apply, LinearMap.smul_apply]
  module

/-- `Jy` is `-i/2` times the difference of the ladder operators. -/
lemma Jy_apply_eq (ρ : AngularMomentumRepresentation V) (v : V) :
    ρ.Jy v = (-(Complex.I / 2)) • (ρ.Jp v - ρ.Jm v) := by
  simp only [Jp, Jm, LinearMap.add_apply, LinearMap.sub_apply, LinearMap.smul_apply]
  rw [show ρ.Jx v + Complex.I • ρ.Jy v - (ρ.Jx v - Complex.I • ρ.Jy v)
    = (2 : ℂ) • (Complex.I • ρ.Jy v) from by module, smul_smul, smul_smul]
  have hI : (-(Complex.I / 2) * 2 * Complex.I : ℂ) = 1 := by
    rw [show (-(Complex.I / 2) * 2 * Complex.I : ℂ) = -(Complex.I * Complex.I) from by ring,
      Complex.I_mul_I]
    ring
  rw [hI, one_smul]

/-- The `J²` eigenspace is stable under `Jx`. -/
lemma Jsq_ker_stable_x (ρ : AngularMomentumRepresentation V) (c : ℂ)
    {v : V} (hv : v ∈ LinearMap.ker (ρ.Jsq - c • (1 : Module.End ℂ V))) :
    ρ.Jx v ∈ LinearMap.ker (ρ.Jsq - c • (1 : Module.End ℂ V)) := by
  have hp := ker_scalar_stable ρ.Jsq ρ.Jp c (Jsq_comm_p ρ) hv
  have hm := ker_scalar_stable ρ.Jsq ρ.Jm c (Jsq_comm_m ρ) hv
  rw [Jx_apply_eq]
  exact Submodule.smul_mem _ _ (Submodule.add_mem _ hp hm)

/-- The `J²` eigenspace is stable under `Jy`. -/
lemma Jsq_ker_stable_y (ρ : AngularMomentumRepresentation V) (c : ℂ)
    {v : V} (hv : v ∈ LinearMap.ker (ρ.Jsq - c • (1 : Module.End ℂ V))) :
    ρ.Jy v ∈ LinearMap.ker (ρ.Jsq - c • (1 : Module.End ℂ V)) := by
  have hp := ker_scalar_stable ρ.Jsq ρ.Jp c (Jsq_comm_p ρ) hv
  have hm := ker_scalar_stable ρ.Jsq ρ.Jm c (Jsq_comm_m ρ) hv
  rw [Jy_apply_eq]
  exact Submodule.smul_mem _ _ (Submodule.sub_mem _ hp hm)

/-- A nonzero vector in a `J²` eigenspace forces that eigenspace to be everything. -/
lemma Jsq_ker_eq_top (ρ : AngularMomentumRepresentation V)
    (hirr : ρ.IsIrreducible) (c : ℂ) {v : V} (hv : v ≠ 0)
    (hmem : v ∈ LinearMap.ker (ρ.Jsq - c • (1 : Module.End ℂ V))) :
    LinearMap.ker (ρ.Jsq - c • (1 : Module.End ℂ V)) = ⊤ := by
  rcases hirr _ (fun w hw => Jsq_ker_stable_x ρ c hw) (fun w hw => Jsq_ker_stable_y ρ c hw)
      (fun w hw => ker_scalar_stable ρ.Jsq ρ.Jz c (Jsq_comm_z ρ) hw) with hbot | htop
  · exact absurd (Submodule.mem_bot ℂ |>.mp (hbot ▸ hmem)) hv
  · exact htop

/-- A nonzero `J²` eigenvector forces `J²` to be that scalar on an irreducible module. -/
lemma Jsq_eq_scalar_of_eigenvector (ρ : AngularMomentumRepresentation V)
    (hirr : ρ.IsIrreducible) (c : ℂ) {v : V} (hv : v ≠ 0)
    (hCv : ρ.Jsq v = c • v) : ρ.Jsq = c • (1 : Module.End ℂ V) := by
  have hmem : v ∈ LinearMap.ker (ρ.Jsq - c • (1 : Module.End ℂ V)) := by
    simpa [LinearMap.mem_ker, sub_eq_zero] using hCv
  exact sub_eq_zero.mp (LinearMap.ker_eq_top.mp (Jsq_ker_eq_top ρ hirr c hv hmem))

/-- If `Jz = 0`, the commutation relations force all three angular momentum operators
to vanish. -/
lemma Jsq_eq_zero_of_Jz_eq_zero (ρ : AngularMomentumRepresentation V)
    (hz : ρ.Jz = 0) : ρ.Jsq = 0 := by
  have hy : ρ.Jy = 0 := by
    have h := ρ.comm_zx
    rw [hz, zero_lie] at h
    exact (smul_eq_zero.mp h.symm).resolve_left Complex.I_ne_zero
  have hx : ρ.Jx = 0 := by
    have h := ρ.comm_yz
    rw [hz, lie_zero] at h
    exact (smul_eq_zero.mp h.symm).resolve_left Complex.I_ne_zero
  simp [Jsq, hx, hy, hz]

/-- On an irreducible finite-dimensional representation, `J²` acts by `j(j+1)` for
some `j = n/2`. -/
lemma Jsq_eq_smul [FiniteDimensional ℂ V] (ρ : AngularMomentumRepresentation V)
    (hirr : ρ.IsIrreducible) :
    ∃ n : ℕ, ρ.Jsq = ((n : ℂ) / 2 * ((n : ℂ) / 2 + 1)) • (1 : Module.End ℂ V) := by
  by_cases hz : ρ.Jz = 0
  · exact ⟨0, by simp [Jsq_eq_zero_of_Jz_eq_zero ρ hz]⟩
  · have := nontrivial_of_Jz_ne_zero ρ hz
    obtain ⟨μ, v, hv, P⟩ := (ρ.isSl2Triple hz).exists_hasPrimitiveVectorWith (R := ℂ) (M := V)
    obtain ⟨n, hn⟩ := P.exists_nat
    subst hn
    exact ⟨n, Jsq_eq_scalar_of_eigenvector ρ hirr _ hv (Jsq_on_primitive ρ hz P)⟩

/-- Magnetic-weight ladder vectors: given a primitive vector
`v₀` of weight `n` for the triple `(2Jz, J+, J-)`, this defines `(J-)ᵏ v₀` for
`k = 0,…,n`. A basis theorem and reindexing by `m = n/2 - k` remain to be added. -/
def magneticBasisVec (ρ : AngularMomentumRepresentation V) (hz : ρ.Jz ≠ 0) {n : ℕ} {v₀ : V}
    (_ : (ρ.isSl2Triple hz).HasPrimitiveVectorWith v₀ (n : ℂ)) (k : Fin (n + 1)) : V :=
  (ρ.Jm ^ (k : ℕ)) v₀

end AngularMomentumRepresentation

end PhyslibAlpha.Sl2
