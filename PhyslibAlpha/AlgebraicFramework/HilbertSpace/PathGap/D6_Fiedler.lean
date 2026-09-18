/-
Copyright (c) 2026 Eduardo Nava-Hernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eduardo Nava-Hernández, José Arturo Nava-Hernández, Gerardo Gabriel Nava Gómez
-/
module

public import PhyslibAlpha.AlgebraicFramework.HilbertSpace.PathGap.D5_MaximaTension

/-!
# D6 — Fiedler spectral decomposition on the discrete path

Explicit diagonalization, in the sine/phase mode basis, of the adjacency
operator `A_d` and the observable `i[T_d,P_d]` on `pathGraph d`. The
complete spectrum is obtained in closed form and the fundamental mode
(the Fiedler vector) is identified as the extremal eigenvector of the
observable `i[T_d,P_d]`. Full, unmodified content from the original
corpus spectral decomposition — pure linear algebra and spectral graph
theory, with no interpretive layer.
-/

@[expose] public section

noncomputable section

open scoped ComplexConjugate

namespace TransportePosicion

theorem sum_cond_succ {d : ℕ} (i : Fin d) (f : Fin d → ℂ) :
    (∑ j : Fin d, if i.val + 1 = j.val then f j else 0) =
      if h : i.val + 1 < d then f ⟨i.val + 1, h⟩ else 0 := by
  classical
  by_cases h : i.val + 1 < d
  · let s : Fin d := ⟨i.val + 1, h⟩
    have hs (j : Fin d) : i.val + 1 = j.val ↔ s = j := by
      simp only [s]
      exact ⟨fun e => Fin.ext e, fun e => by
        have := congrArg Fin.val e
        simpa [s] using this⟩
    simp_rw [hs]
    simp [h, s]
  · have hs (j : Fin d) : i.val + 1 ≠ j.val := by omega
    simp [h, hs]

theorem sum_cond_pred {d : ℕ} (i : Fin d) (f : Fin d → ℂ) :
    (∑ j : Fin d, if j.val + 1 = i.val then f j else 0) =
      if h : 0 < i.val then f ⟨i.val - 1, by omega⟩ else 0 := by
  classical
  by_cases h : 0 < i.val
  · let p : Fin d := ⟨i.val - 1, by omega⟩
    have hp (j : Fin d) : j.val + 1 = i.val ↔ p = j := by
      simp only [p]
      constructor
      · intro e
        apply Fin.ext
        change i.val - 1 = j.val
        omega
      · intro e
        have he := congrArg Fin.val e
        change i.val - 1 = j.val at he
        omega
    simp_rw [hp]
    simp [h, p]
  · have hp (j : Fin d) : j.val + 1 ≠ i.val := by omega
    simp [h, hp]

theorem sum_pasoMinimo
    {d : ℕ} (i : Fin d) (f : Fin d → ℂ) :
    (∑ j : Fin d, if PasoMinimo i j then f j else 0) =
      (if h : i.val + 1 < d then f ⟨i.val + 1, h⟩ else 0) +
      (if h : 0 < i.val then f ⟨i.val - 1, by omega⟩ else 0) := by
  classical
  rw [show (∑ j : Fin d, if PasoMinimo i j then f j else 0) =
      (∑ j : Fin d, if i.val + 1 = j.val then f j else 0) +
      (∑ j : Fin d, if j.val + 1 = i.val then f j else 0) by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    unfold PasoMinimo
    by_cases h₁ : i.val + 1 = j.val
    · have h₂ : j.val + 1 ≠ i.val := by omega
      simp [h₁, h₂]
    · by_cases h₂ : j.val + 1 = i.val <;> simp [h₁, h₂]]
  rw [sum_cond_succ, sum_cond_pred]

theorem Ad_mulVec_apply
    {d : ℕ} (i : Fin d) (f : Fin d → ℂ) :
    (Ad d).mulVec f i =
      (if h : i.val + 1 < d then f ⟨i.val + 1, h⟩ else 0) +
      (if h : 0 < i.val then f ⟨i.val - 1, by omega⟩ else 0) := by
  classical
  simp only [Matrix.mulVec, dotProduct, Ad]
  simp_rw [ite_mul, one_mul, zero_mul]
  exact sum_pasoMinimo i f

/-- Spectral angle of the `k`th sine mode on the path with `d` vertices. -/
noncomputable def anguloModo (d : ℕ) (k : Fin d) : ℝ :=
  ((k.val : ℝ) + 1) * Real.pi / ((d : ℝ) + 1)

/-- The unnormalized sine eigenmode of the path adjacency matrix. -/
noncomputable def modoSeno (d : ℕ) (k : Fin d) : Fin d → ℂ :=
  fun j => (Real.sin (((j.val : ℝ) + 1) * anguloModo d k) : ℂ)

theorem recurrencia_seno (a : ℝ) (n : ℕ) :
    Real.sin (((n : ℝ) + 2) * a) + Real.sin ((n : ℝ) * a) =
      2 * Real.cos a * Real.sin (((n : ℝ) + 1) * a) := by
  rw [show ((n : ℝ) + 2) * a = ((n : ℝ) + 1) * a + a by ring,
    Real.sin_add,
    show (n : ℝ) * a = ((n : ℝ) + 1) * a - a by ring,
    Real.sin_sub]
  ring

theorem seno_frontera_superior
    {d : ℕ} (k : Fin d) :
    Real.sin (((d : ℝ) + 1) * anguloModo d k) = 0 := by
  unfold anguloModo
  have hd : (d : ℝ) + 1 ≠ 0 := by positivity
  rw [show ((d : ℝ) + 1) *
      (((k.val : ℝ) + 1) * Real.pi / ((d : ℝ) + 1)) =
      (k.val + 1 : ℕ) * Real.pi by
        push_cast
        field_simp]
  exact Real.sin_nat_mul_pi (k.val + 1)

theorem Ad_modoSeno
    {d : ℕ} (hd : 1 ≤ d) (k : Fin d) :
    (Ad d).mulVec (modoSeno d k) =
      fun i => (2 * Real.cos (anguloModo d k) : ℂ) * modoSeno d k i := by
  funext i
  rw [Ad_mulVec_apply]
  by_cases hs : i.val + 1 < d
  · by_cases hp : 0 < i.val
    · simp only [hs, hp, dite_true, modoSeno]
      have hpred : i.val - 1 + 1 = i.val := by omega
      have hsucc : i.val + 1 + 1 = i.val + 2 := by omega
      have hpredR : ((i.val - 1 : ℕ) : ℝ) + 1 = (i.val : ℝ) := by
        exact_mod_cast hpred
      have hsuccR : ((i.val + 1 : ℕ) : ℝ) + 1 = (i.val : ℝ) + 2 := by
        exact_mod_cast hsucc
      rw [hpredR, hsuccR]
      exact_mod_cast recurrencia_seno (anguloModo d k) i.val
    · have hi0 : i.val = 0 := by omega
      simp only [hs, hp, dite_true, dite_false, add_zero, modoSeno]
      simp only [hi0, Nat.cast_zero, zero_add, Nat.cast_one]
      exact_mod_cast (by
        simpa using recurrencia_seno (anguloModo d k) 0)
  · have hilast : i.val + 1 = d := by omega
    by_cases hp : 0 < i.val
    · simp only [hs, hp, dite_false, dite_true, zero_add, modoSeno]
      have hrec := recurrencia_seno (anguloModo d k) i.val
      have hzero :
          Real.sin (((i.val : ℝ) + 2) * anguloModo d k) = 0 := by
        rw [show ((i.val : ℝ) + 2) = (d : ℝ) + 1 by
          exact_mod_cast (show i.val + 2 = d + 1 by omega)]
        exact seno_frontera_superior k
      rw [hzero, zero_add] at hrec
      have hpred : i.val - 1 + 1 = i.val := by omega
      have hpredR : ((i.val - 1 : ℕ) : ℝ) + 1 = (i.val : ℝ) := by
        exact_mod_cast hpred
      rw [hpredR]
      exact_mod_cast hrec
    · have hd1 : d = 1 := by omega
      subst d
      have hk0 : k = 0 := Subsingleton.elim _ _
      have hi0 : i = 0 := Subsingleton.elim _ _
      subst k
      subst i
      norm_num [modoSeno, anguloModo]

/-- Adjacency eigenvalue associated with `modoSeno d k`. -/
noncomputable def autovalorAd (d : ℕ) (k : Fin d) : ℂ :=
  (2 * Real.cos (anguloModo d k) : ℝ)

theorem anguloModo_mem_Icc {d : ℕ} (k : Fin d) :
    anguloModo d k ∈ Set.Icc (0 : ℝ) Real.pi := by
  constructor
  · unfold anguloModo
    positivity
  · unfold anguloModo
    have hk : (k.val : ℝ) + 1 ≤ (d : ℝ) + 1 := by
      exact_mod_cast (show k.val + 1 ≤ d + 1 by omega)
    have hd : 0 < (d : ℝ) + 1 := by positivity
    calc
      ((k.val : ℝ) + 1) * Real.pi / ((d : ℝ) + 1) ≤
          ((d : ℝ) + 1) * Real.pi / ((d : ℝ) + 1) := by
            gcongr
      _ = Real.pi := by field_simp

theorem autovalorAd_injective {d : ℕ} :
    Function.Injective (autovalorAd d) := by
  intro k l hkl
  have hcos :
      Real.cos (anguloModo d k) = Real.cos (anguloModo d l) := by
    apply mul_left_cancel₀ (a := (2 : ℝ)) (by norm_num)
    apply Complex.ofReal_injective
    simpa [autovalorAd] using hkl
  have hang : anguloModo d k = anguloModo d l :=
    Real.strictAntiOn_cos.injOn
      (anguloModo_mem_Icc k) (anguloModo_mem_Icc l) hcos
  apply Fin.ext
  unfold anguloModo at hang
  have hp : Real.pi ≠ 0 := Real.pi_ne_zero
  have hd : (d : ℝ) + 1 ≠ 0 := by positivity
  have : (k.val : ℝ) = (l.val : ℝ) := by
    field_simp at hang
    nlinarith
  exact_mod_cast this

theorem modoSeno_ne_zero {d : ℕ} (hd : 1 ≤ d) (k : Fin d) :
    modoSeno d k ≠ 0 := by
  intro h
  have h0 := congrFun h ⟨0, hd⟩
  have ha0 : 0 < anguloModo d k := by
    unfold anguloModo
    positivity
  have hapi : anguloModo d k < Real.pi := by
    unfold anguloModo
    have hk : (k.val : ℝ) + 1 < (d : ℝ) + 1 := by
      exact_mod_cast Nat.add_lt_add_right k.isLt 1
    have hdR : 0 < (d : ℝ) + 1 := by positivity
    calc
      ((k.val : ℝ) + 1) * Real.pi / ((d : ℝ) + 1) <
          ((d : ℝ) + 1) * Real.pi / ((d : ℝ) + 1) := by
            gcongr
      _ = Real.pi := by field_simp
  have hs := (Real.sin_pos_of_pos_of_lt_pi ha0 hapi).ne'
  apply Complex.ofReal_ne_zero.mpr hs
  simpa [modoSeno] using h0

theorem modoSeno_hasEigenvector
    {d : ℕ} (hd : 1 ≤ d) (k : Fin d) :
    Module.End.HasEigenvector (Matrix.toLin' (Ad d))
      (autovalorAd d k) (modoSeno d k) := by
  constructor
  · rw [Module.End.mem_eigenspace_iff, Matrix.toLin'_apply]
    ext i
    simpa [autovalorAd] using congrFun (Ad_modoSeno hd k) i
  · exact modoSeno_ne_zero hd k

theorem modosSeno_linearIndependent
    {d : ℕ} (hd : 1 ≤ d) :
    LinearIndependent ℂ (modoSeno d) :=
  Module.End.eigenvectors_linearIndependent' (Matrix.toLin' (Ad d))
    (autovalorAd d) autovalorAd_injective (modoSeno d)
    (modoSeno_hasEigenvector hd)

/-- Basis of sine eigenmodes for the finite path adjacency operator. -/
noncomputable def baseModosSeno
    {d : ℕ} (hd : 1 ≤ d) : Module.Basis (Fin d) ℂ (Fin d → ℂ) := by
  classical
  exact basisOfPiSpaceOfLinearIndependent (modosSeno_linearIndependent hd)

theorem baseModosSeno_apply
    {d : ℕ} (hd : 1 ≤ d) (k : Fin d) :
    baseModosSeno hd k = modoSeno d k := by
  classical
  exact congrFun (coe_basisOfPiSpaceOfLinearIndependent
    (modosSeno_linearIndependent hd)) k

theorem Ad_eq_suma_modos
    {d : ℕ} (hd : 1 ≤ d) (v : Fin d → ℂ) :
    Matrix.toLin' (Ad d) v =
      ∑ k : Fin d,
        (baseModosSeno hd).repr v k •
          (autovalorAd d k • modoSeno d k) := by
  calc
    Matrix.toLin' (Ad d) v =
        Matrix.toLin' (Ad d)
          (∑ k, (baseModosSeno hd).repr v k • baseModosSeno hd k) := by
            rw [(baseModosSeno hd).sum_repr v]
    _ = ∑ k, (baseModosSeno hd).repr v k •
          Matrix.toLin' (Ad d) (baseModosSeno hd k) := by
            simp only [map_sum, map_smul]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro k _
      rw [baseModosSeno_apply]
      congr 1
      rw [Matrix.toLin'_apply]
      ext i
      simpa [autovalorAd] using congrFun (Ad_modoSeno hd k) i

theorem repr_Ad
    {d : ℕ} (hd : 1 ≤ d) (v : Fin d → ℂ) (k : Fin d) :
    (baseModosSeno hd).repr (Matrix.toLin' (Ad d) v) k =
      autovalorAd d k * (baseModosSeno hd).repr v k := by
  rw [Ad_eq_suma_modos hd v, map_sum]
  classical
  simp [← baseModosSeno_apply hd, Finsupp.single_apply, mul_comm]

theorem autovalorAd_agota_espectro
    {d : ℕ} (hd : 1 ≤ d) {μ : ℂ}
    (hμ : Module.End.HasEigenvalue (Matrix.toLin' (Ad d)) μ) :
    ∃ k : Fin d, μ = autovalorAd d k := by
  obtain ⟨v, hv⟩ := hμ.exists_hasEigenvector
  have hrepr : (baseModosSeno hd).repr v ≠ 0 := by
    simpa using (baseModosSeno hd).repr.injective.ne hv.2
  have hk : ∃ k : Fin d, (baseModosSeno hd).repr v k ≠ 0 := by
    by_contra h
    push Not at h
    apply hrepr
    apply Finsupp.ext
    intro k
    exact h k
  obtain ⟨k, hk⟩ := hk
  have heig := Module.End.mem_eigenspace_iff.mp hv.1
  have hc := congrArg (fun w => (baseModosSeno hd).repr w k) heig
  rw [repr_Ad] at hc
  simp only [map_smul] at hc
  exact ⟨k, (mul_right_cancel₀ hk hc).symm⟩

theorem anguloFiedler_le_anguloModo
    {d : ℕ} (k : Fin d) :
    anguloFiedler d ≤ anguloModo d k := by
  unfold anguloFiedler anguloModo
  have hd : 0 < (d : ℝ) + 1 := by positivity
  have hk : (1 : ℝ) ≤ (k.val : ℝ) + 1 := by
    exact_mod_cast (show 1 ≤ k.val + 1 by omega)
  calc
    Real.pi / ((d : ℝ) + 1) =
        1 * Real.pi / ((d : ℝ) + 1) := by ring
    _ ≤ ((k.val : ℝ) + 1) * Real.pi / ((d : ℝ) + 1) := by
      gcongr

theorem anguloModo_le_pi_sub_fiedler
    {d : ℕ} (k : Fin d) :
    anguloModo d k ≤ Real.pi - anguloFiedler d := by
  unfold anguloFiedler anguloModo
  have hd : 0 < (d : ℝ) + 1 := by positivity
  have hk : (k.val : ℝ) + 1 ≤ d := by
    exact_mod_cast (show k.val + 1 ≤ d by omega)
  calc
    ((k.val : ℝ) + 1) * Real.pi / ((d : ℝ) + 1) ≤
        (d : ℝ) * Real.pi / ((d : ℝ) + 1) := by
          gcongr
    _ = Real.pi - Real.pi / ((d : ℝ) + 1) := by
      field_simp
      ring

theorem abs_cos_anguloModo_le_cos_fiedler
    {d : ℕ} (hd : 2 ≤ d) (k : Fin d) :
    |Real.cos (anguloModo d k)| ≤ Real.cos (anguloFiedler d) := by
  apply abs_le.mpr
  constructor
  · rw [← Real.cos_pi_sub]
    apply Real.cos_le_cos_of_nonneg_of_le_pi
    · exact (anguloModo_mem_Icc k).1
    · have hθ : 0 ≤ anguloFiedler d := by
        unfold anguloFiedler
        positivity
      linarith [Real.pi_pos]
    · exact anguloModo_le_pi_sub_fiedler k
  · apply Real.cos_le_cos_of_nonneg_of_le_pi
    · unfold anguloFiedler
      positivity
    · exact (anguloModo_mem_Icc k).2
    · exact anguloFiedler_le_anguloModo k

theorem norma_autovalorAd_le_rho
    {d : ℕ} (hd : 2 ≤ d) (k : Fin d) :
    ‖autovalorAd d k‖ ≤ rho d := by
  rw [autovalorAd, Complex.norm_real, Real.norm_eq_abs,
    abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  rw [rho]
  exact mul_le_mul_of_nonneg_left
    (by simpa [anguloFiedler] using
      abs_cos_anguloModo_le_cos_fiedler hd k)
    (by norm_num)

/-- Matrix of the Hermitian commutator observable `i[T_d,P_d]`. -/
noncomputable def Kmat (d : ℕ) : Matrix (Fin d) (Fin d) ℂ :=
  Complex.I • ((Td d * Pd d) - (Pd d * Td d))

/-- Phase factor converting sine modes into commutator eigenmodes. -/
noncomputable def fase (j : ℕ) : ℂ := (-Complex.I) ^ j

/-- Phase-twisted sine mode for the commutator matrix. -/
noncomputable def modoFase (d : ℕ) (k : Fin d) : Fin d → ℂ :=
  fun j => fase j.val * modoSeno d k j

theorem Kmat_apply
    (d : ℕ) (i j : Fin d) :
    Kmat d i j =
      Complex.I * Td d i j *
        ((posicionCoord d j : ℂ) - posicionCoord d i) := by
  rw [Kmat]
  change Complex.I * (((Td d * Pd d) - (Pd d * Td d)) i j) = _
  rw [Matrix.sub_apply,
    Td_mul_Pd_apply, Pd_mul_Td_apply]
  ring

theorem termino_vecino_fase
    {d : ℕ} (hd : 2 ≤ d) {i j : Fin d}
    (hpaso : PasoMinimo i j) (z : ℂ) :
    Kmat d i j * (fase j.val * z) =
      ((2 / ((d : ℝ) - 1) / rho d : ℝ) : ℂ) *
        (fase i.val * z) := by
  have hrhoR : rho d ≠ 0 := (rho_pos d hd).ne'
  have hrhoC : (rho d : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hrhoR
  have hdsubR : (d : ℝ) - 1 ≠ 0 := by
    have : (1 : ℝ) < d := by exact_mod_cast (show 1 < d by omega)
    linarith
  rw [Kmat_apply]
  have hTd : Td d i j = 1 / (rho d : ℂ) := by
    simp [Td, Ad, hpaso]
  rw [hTd]
  rcases hpaso with hij | hji
  · have hpos := posicionCoord_succ_sub d hd i j hij
    have hposC :
        (posicionCoord d j : ℂ) - posicionCoord d i =
          ((2 / ((d : ℝ) - 1) : ℝ) : ℂ) := by
      exact_mod_cast hpos
    have hpow : fase j.val = fase i.val * (-Complex.I) := by
      unfold fase
      rw [← hij, pow_succ]
    rw [hpow, hposC]
    push_cast
    field_simp [hrhoR, hdsubR]
    ring_nf
    simp [Complex.I_sq]
  · have hpos := posicionCoord_succ_sub d hd j i hji
    have hposC :
        (posicionCoord d j : ℂ) - posicionCoord d i =
          -((2 / ((d : ℝ) - 1) : ℝ) : ℂ) := by
      exact_mod_cast (show posicionCoord d j - posicionCoord d i =
        -(2 / ((d : ℝ) - 1)) by linarith)
    have hpow : fase i.val = fase j.val * (-Complex.I) := by
      unfold fase
      rw [← hji, pow_succ]
    have hI : fase j.val = fase i.val * Complex.I := by
      calc
        fase j.val = fase j.val * ((-Complex.I) * Complex.I) := by
          rw [show (-Complex.I) * Complex.I = 1 by
            apply Complex.ext <;> norm_num]
          ring
        _ = fase i.val * Complex.I := by rw [hpow]; ring
    rw [hI, hposC]
    push_cast
    field_simp [hrhoR, hdsubR]
    ring_nf
    simp [Complex.I_sq]

theorem Kmat_mulVec_modoFase
    {d : ℕ} (hd : 2 ≤ d) (k : Fin d) :
    (Kmat d).mulVec (modoFase d k) =
      fun i =>
        (((2 / ((d : ℝ) - 1)) *
          (2 * Real.cos (anguloModo d k) / rho d) : ℝ) : ℂ) *
          modoFase d k i := by
  funext i
  simp only [Matrix.mulVec, dotProduct]
  rw [show (∑ j : Fin d, Kmat d i j * modoFase d k j) =
      ∑ j : Fin d,
        if PasoMinimo i j then
          (((2 / ((d : ℝ) - 1) / rho d : ℝ) : ℂ) *
            (fase i.val * modoSeno d k j))
        else 0 by
      apply Finset.sum_congr rfl
      intro j _
      by_cases hp : PasoMinimo i j
      · simp only [hp, if_pos, modoFase]
        exact termino_vecino_fase hd hp (modoSeno d k j)
      · have hz : Kmat d i j = 0 := by
          rw [Kmat_apply]
          simp [Td, Ad, hp]
        simp [hp, hz]]
  rw [show (∑ x : Fin d,
      if PasoMinimo i x then
        (((2 / ((d : ℝ) - 1) / rho d : ℝ) : ℂ) *
          (fase i.val * modoSeno d k x))
      else 0) =
      (((2 / ((d : ℝ) - 1) / rho d : ℝ) : ℂ) * fase i.val) *
        ∑ x : Fin d, if PasoMinimo i x then modoSeno d k x else 0 by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    by_cases hp : PasoMinimo i x <;> simp [hp]
    ring]
  rw [show (∑ j : Fin d, if PasoMinimo i j then modoSeno d k j else 0) =
      (Ad d).mulVec (modoSeno d k) i by
        simp only [Matrix.mulVec, dotProduct, Ad]
        simp_rw [ite_mul, one_mul, zero_mul]]
  rw [congrFun (Ad_modoSeno (by omega) k) i]
  simp only [modoFase]
  push_cast
  ring

/-- Eigenvalue of `Kmat d` associated with `modoFase d k`. -/
noncomputable def autovalorK (d : ℕ) (k : Fin d) : ℂ :=
  ((((2 / ((d : ℝ) - 1)) / rho d : ℝ) : ℂ) * autovalorAd d k)

theorem Kmat_modoFase
    {d : ℕ} (hd : 2 ≤ d) (k : Fin d) :
    Matrix.toLin' (Kmat d) (modoFase d k) =
      autovalorK d k • modoFase d k := by
  rw [Matrix.toLin'_apply]
  ext i
  change (Kmat d).mulVec (modoFase d k) i =
    autovalorK d k * modoFase d k i
  rw [congrFun (Kmat_mulVec_modoFase hd k) i]
  simp only [autovalorK, autovalorAd]
  push_cast
  ring

theorem modoFase_ne_zero
    {d : ℕ} (hd : 2 ≤ d) (k : Fin d) :
    modoFase d k ≠ 0 := by
  intro h
  have h0 := congrFun h ⟨0, by omega⟩
  have hs := modoSeno_ne_zero (by omega : 1 ≤ d) k
  apply hs
  funext j
  have hf : fase j.val ≠ 0 := by
    exact pow_ne_zero _ (neg_ne_zero.mpr Complex.I_ne_zero)
  have hj := congrFun h j
  simp only [modoFase] at hj
  exact (mul_eq_zero.mp hj).resolve_left hf

theorem autovalorK_injective
    {d : ℕ} (hd : 2 ≤ d) :
    Function.Injective (autovalorK d) := by
  intro k l hkl
  apply autovalorAd_injective
  unfold autovalorK at hkl
  have hcR : (2 / ((d : ℝ) - 1)) / rho d ≠ 0 := by
    have hdR : (d : ℝ) - 1 ≠ 0 := by
      have : (1 : ℝ) < d := by exact_mod_cast (show 1 < d by omega)
      linarith
    exact div_ne_zero (div_ne_zero (by norm_num) hdR) (rho_pos d hd).ne'
  exact mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr hcR) hkl

theorem modoFase_hasEigenvector
    {d : ℕ} (hd : 2 ≤ d) (k : Fin d) :
    Module.End.HasEigenvector (Matrix.toLin' (Kmat d))
      (autovalorK d k) (modoFase d k) := by
  constructor
  · rw [Module.End.mem_eigenspace_iff]
    exact Kmat_modoFase hd k
  · exact modoFase_ne_zero hd k

theorem modosFase_linearIndependent
    {d : ℕ} (hd : 2 ≤ d) :
    LinearIndependent ℂ (modoFase d) :=
  Module.End.eigenvectors_linearIndependent' (Matrix.toLin' (Kmat d))
    (autovalorK d) (autovalorK_injective hd) (modoFase d)
    (modoFase_hasEigenvector hd)

/-- Basis of phase-twisted eigenmodes for `Kmat`. -/
noncomputable def baseModosFase
    {d : ℕ} (hd : 2 ≤ d) : Module.Basis (Fin d) ℂ (Fin d → ℂ) := by
  classical
  exact basisOfPiSpaceOfLinearIndependent (modosFase_linearIndependent hd)

theorem baseModosFase_apply
    {d : ℕ} (hd : 2 ≤ d) (k : Fin d) :
    baseModosFase hd k = modoFase d k := by
  classical
  exact congrFun (coe_basisOfPiSpaceOfLinearIndependent
    (modosFase_linearIndependent hd)) k

theorem Kmat_eq_suma_modos
    {d : ℕ} (hd : 2 ≤ d) (v : Fin d → ℂ) :
    Matrix.toLin' (Kmat d) v =
      ∑ k : Fin d,
        (baseModosFase hd).repr v k •
          (autovalorK d k • modoFase d k) := by
  calc
    Matrix.toLin' (Kmat d) v =
        Matrix.toLin' (Kmat d)
          (∑ k, (baseModosFase hd).repr v k • baseModosFase hd k) := by
            rw [(baseModosFase hd).sum_repr v]
    _ = ∑ k, (baseModosFase hd).repr v k •
          Matrix.toLin' (Kmat d) (baseModosFase hd k) := by
            simp only [map_sum, map_smul]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro k _
      rw [baseModosFase_apply]
      congr 1
      exact Kmat_modoFase hd k

theorem repr_Kmat
    {d : ℕ} (hd : 2 ≤ d) (v : Fin d → ℂ) (k : Fin d) :
    (baseModosFase hd).repr (Matrix.toLin' (Kmat d) v) k =
      autovalorK d k * (baseModosFase hd).repr v k := by
  rw [Kmat_eq_suma_modos hd v, map_sum]
  classical
  simp [← baseModosFase_apply hd, Finsupp.single_apply, mul_comm]

theorem Kmat_autovalor_agota_espectro
    {d : ℕ} (hd : 2 ≤ d) {μ : ℂ}
    (hμ : Module.End.HasEigenvalue (Matrix.toLin' (Kmat d)) μ) :
    ∃ k : Fin d, μ = autovalorK d k := by
  obtain ⟨v, hv⟩ := hμ.exists_hasEigenvector
  have hrepr : (baseModosFase hd).repr v ≠ 0 := by
    simpa using (baseModosFase hd).repr.injective.ne hv.2
  obtain ⟨k, hk⟩ :
      ∃ k : Fin d, (baseModosFase hd).repr v k ≠ 0 := by
    by_contra h
    push Not at h
    apply hrepr
    apply Finsupp.ext
    intro k
    exact h k
  have heig := Module.End.mem_eigenspace_iff.mp hv.1
  have hcoord := congrArg (fun w => (baseModosFase hd).repr w k) heig
  rw [repr_Kmat] at hcoord
  simp only [map_smul] at hcoord
  exact ⟨k, (mul_right_cancel₀ hk hcoord).symm⟩

theorem norma_autovalorK_le_paso
    {d : ℕ} (hd : 2 ≤ d) (k : Fin d) :
    ‖autovalorK d k‖ ≤ 2 / ((d : ℝ) - 1) := by
  have hδ : 0 ≤ 2 / ((d : ℝ) - 1) := by
    have hdsub : 0 < (d : ℝ) - 1 := by
      have : (1 : ℝ) < d := by exact_mod_cast (show 1 < d by omega)
      linarith
    exact div_nonneg (by norm_num) hdsub.le
  have hρ := rho_pos d hd
  rw [autovalorK, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (div_nonneg hδ hρ.le)]
  calc
    (2 / ((d : ℝ) - 1) / rho d) * ‖autovalorAd d k‖ ≤
        (2 / ((d : ℝ) - 1) / rho d) * rho d := by
          gcongr
          exact norma_autovalorAd_le_rho hd k
    _ = 2 / ((d : ℝ) - 1) := by
      field_simp [(rho_pos d hd).ne']

theorem KdOp_eq_Kmat (d : ℕ) :
    KdOp d = Matrix.toEuclideanLin (Kmat d) := by
  unfold KdOp ConstructorEspectralTP.observableTension Kmat
  rw [conmutador_TdOp_PdOp_eq_matriz]
  exact (Matrix.toEuclideanLin :
    Matrix (Fin d) (Fin d) ℂ ≃ₗ[ℂ] (Hd d →ₗ[ℂ] Hd d)).map_smul
      Complex.I ((Td d * Pd d) - (Pd d * Td d)) |>.symm

/-- The phase-twisted commutator eigenmode represented in `Hd d`. -/
noncomputable def modoFaseHd (d : ℕ) (k : Fin d) : Hd d :=
  WithLp.toLp 2 (modoFase d k)

theorem KdOp_modoFaseHd
    {d : ℕ} (hd : 2 ≤ d) (k : Fin d) :
    KdOp d (modoFaseHd d k) =
      autovalorK d k • modoFaseHd d k := by
  rw [KdOp_eq_Kmat]
  change WithLp.toLp 2 ((Kmat d).mulVec (modoFase d k)) =
    WithLp.toLp 2 (fun i => autovalorK d k * modoFase d k i)
  congr 1
  funext i
  simpa [smul_eq_mul] using congrFun (Kmat_modoFase hd k) i

theorem modoFaseHd_ne_zero
    {d : ℕ} (hd : 2 ≤ d) (k : Fin d) :
    modoFaseHd d k ≠ 0 := by
  exact (WithLp.linearEquiv 2 ℂ (Fin d → ℂ)).symm.injective.ne
    (modoFase_ne_zero hd k)

theorem modoFaseHd_hasEigenvector
    {d : ℕ} (hd : 2 ≤ d) (k : Fin d) :
    Module.End.HasEigenvector (KdOp d)
      (autovalorK d k) (modoFaseHd d k) := by
  constructor
  · rw [Module.End.mem_eigenspace_iff]
    exact KdOp_modoFaseHd hd k
  · exact modoFaseHd_ne_zero hd k

theorem modosFaseHd_linearIndependent
    {d : ℕ} (hd : 2 ≤ d) :
    LinearIndependent ℂ (modoFaseHd d) :=
  Module.End.eigenvectors_linearIndependent' (KdOp d)
    (autovalorK d) (autovalorK_injective hd) (modoFaseHd d)
    (modoFaseHd_hasEigenvector hd)

/-- Basis of commutator eigenmodes in the finite Hilbert space `Hd d`. -/
noncomputable def baseModosFaseHd
    {d : ℕ} (hd : 2 ≤ d) : Module.Basis (Fin d) ℂ (Hd d) :=
  (baseModosFase hd).map (WithLp.linearEquiv 2 ℂ (Fin d → ℂ)).symm

theorem baseModosFaseHd_apply
    {d : ℕ} (hd : 2 ≤ d) (k : Fin d) :
    baseModosFaseHd hd k = modoFaseHd d k := by
  simp [baseModosFaseHd, modoFaseHd, baseModosFase_apply]

theorem KdOp_eq_suma_modos
    {d : ℕ} (hd : 2 ≤ d) (v : Hd d) :
    KdOp d v =
      ∑ k : Fin d,
        (baseModosFaseHd hd).repr v k •
          (autovalorK d k • modoFaseHd d k) := by
  calc
    KdOp d v =
        KdOp d
          (∑ k, (baseModosFaseHd hd).repr v k •
            baseModosFaseHd hd k) := by
              rw [(baseModosFaseHd hd).sum_repr v]
    _ = ∑ k, (baseModosFaseHd hd).repr v k •
          KdOp d (baseModosFaseHd hd k) := by
            simp only [map_sum, map_smul]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro k _
      rw [baseModosFaseHd_apply]
      congr 1
      exact KdOp_modoFaseHd hd k

theorem repr_KdOp
    {d : ℕ} (hd : 2 ≤ d) (v : Hd d) (k : Fin d) :
    (baseModosFaseHd hd).repr (KdOp d v) k =
      autovalorK d k * (baseModosFaseHd hd).repr v k := by
  rw [KdOp_eq_suma_modos hd v, map_sum]
  classical
  simp [← baseModosFaseHd_apply hd, Finsupp.single_apply, mul_comm]

theorem KdOp_autovalor_agota_espectro
    {d : ℕ} (hd : 2 ≤ d) {μ : ℂ}
    (hμ : Module.End.HasEigenvalue (KdOp d) μ) :
    ∃ k : Fin d, μ = autovalorK d k := by
  obtain ⟨v, hv⟩ := hμ.exists_hasEigenvector
  have hrepr : (baseModosFaseHd hd).repr v ≠ 0 := by
    simpa using (baseModosFaseHd hd).repr.injective.ne hv.2
  obtain ⟨k, hk⟩ :
      ∃ k : Fin d, (baseModosFaseHd hd).repr v k ≠ 0 := by
    by_contra h
    push Not at h
    apply hrepr
    apply Finsupp.ext
    intro k
    exact h k
  have heig := Module.End.mem_eigenspace_iff.mp hv.1
  have hcoord := congrArg (fun w => (baseModosFaseHd hd).repr w k) heig
  rw [repr_KdOp] at hcoord
  simp only [map_smul] at hcoord
  exact ⟨k, (mul_right_cancel₀ hk hcoord).symm⟩

theorem todo_autovalor_KdOp_acotado
    {d : ℕ} (hd : 2 ≤ d) {μ : ℂ}
    (hμ : Module.End.HasEigenvalue (KdOp d) μ) :
    ‖μ‖ ≤ 2 / ((d : ℝ) - 1) := by
  obtain ⟨k, rfl⟩ := KdOp_autovalor_agota_espectro hd hμ
  exact norma_autovalorK_le_paso hd k

theorem autovalorK_fundamental
    (d : ℕ) (hd : 2 ≤ d) :
    autovalorK d ⟨0, by omega⟩ =
      ((2 / ((d : ℝ) - 1) : ℝ) : ℂ) := by
  have hρ : rho d ≠ 0 := (rho_pos d hd).ne'
  have hdsub : (d : ℝ) - 1 ≠ 0 := by
    have : (1 : ℝ) < d := by exact_mod_cast (show 1 < d by omega)
    linarith
  simp only [autovalorK, autovalorAd, anguloModo,
    Nat.cast_zero, zero_add]
  rw [show (1 : ℝ) * Real.pi / ((d : ℝ) + 1) =
    Real.pi / ((d : ℝ) + 1) by ring]
  rw [show (2 * Real.cos (Real.pi / ((d : ℝ) + 1)) : ℝ) = rho d by
    rfl]
  push_cast
  field_simp [hρ, hdsub]

theorem modoFaseHd_fundamental_eq_vectorFiedlerCrudo
    (d : ℕ) (hd : 2 ≤ d) :
    modoFaseHd d ⟨0, by omega⟩ = vectorFiedlerCrudo d := by
  change WithLp.toLp 2 (fun j : Fin d =>
      (-Complex.I) ^ j.val *
        (Real.sin (((j.val : ℝ) + 1) *
          ((((⟨0, by omega⟩ : Fin d).val : ℝ) + 1) * Real.pi /
            ((d : ℝ) + 1))) : ℂ)) =
    WithLp.toLp 2 (fun j : Fin d =>
      (-Complex.I) ^ j.val *
        (Real.sin (((j.val : ℝ) + 1) *
          (Real.pi / ((d : ℝ) + 1))) : ℂ))
  congr 1
  funext j
  congr 3
  norm_num

theorem KdOp_vectorFiedlerCrudo
    (d : ℕ) (hd : 2 ≤ d) :
    KdOp d (vectorFiedlerCrudo d) =
      ((2 / ((d : ℝ) - 1) : ℝ) : ℂ) • vectorFiedlerCrudo d := by
  rw [← modoFaseHd_fundamental_eq_vectorFiedlerCrudo d hd,
    KdOp_modoFaseHd hd, autovalorK_fundamental d hd]

theorem KdOp_vectorFiedlerExplicito
    (d : ℕ) (hd : 2 ≤ d) :
    KdOp d (vectorFiedlerExplicito d) =
      ((2 / ((d : ℝ) - 1) : ℝ) : ℂ) • vectorFiedlerExplicito d := by
  rw [vectorFiedlerExplicito, map_smul, KdOp_vectorFiedlerCrudo d hd]
  module

theorem radioEspectral_KdOp_eq_paso
    (d : ℕ) (hd : 2 ≤ d) :
    letI : Nonempty (Fin d) := ⟨⟨0, by omega⟩⟩
    letI : Nontrivial (Hd d) := inferInstance
    ConstructorEspectralTP.radioEspectral (KdOp d) (KdOp_simetrico d) =
      2 / ((d : ℝ) - 1) := by
  letI : Nonempty (Fin d) := ⟨⟨0, by omega⟩⟩
  letI : Nontrivial (Hd d) := inferInstance
  have hdsub : 0 < (d : ℝ) - 1 := by
    have : (1 : ℝ) < d := by exact_mod_cast (show 1 < d by omega)
    linarith
  have hδ : 0 ≤ 2 / ((d : ℝ) - 1) := by
    exact div_nonneg (by norm_num) hdsub.le
  apply le_antisymm
  · have heig :=
      (KdOp_simetrico d).hasEigenvalue_eigenvalues rfl
        (ConstructorEspectralTP.indiceExtremal (KdOp d) (KdOp_simetrico d))
    have hb := todo_autovalor_KdOp_acotado hd heig
    simpa [ConstructorEspectralTP.radioEspectral,
      ConstructorEspectralTP.autovalorExtremal,
      Complex.norm_real, Real.norm_eq_abs] using hb
  · have hb :=
      ConstructorEspectralTP.norma_aplicacion_le_radio_mul_norma
        (KdOp d) (KdOp_simetrico d) (vectorFiedlerExplicito d)
    rw [KdOp_vectorFiedlerExplicito d hd, norm_smul,
      vectorFiedlerExplicito_normalizado d (by omega)] at hb
    have hb' :
        2 / ‖(((d : ℝ) : ℂ) - 1)‖ ≤
          ConstructorEspectralTP.radioEspectral (KdOp d) (KdOp_simetrico d) := by
      simpa [Complex.norm_real, abs_of_nonneg hδ] using hb
    rw [show (((d : ℝ) : ℂ) - 1) = (((d : ℝ) - 1 : ℝ) : ℂ) by
      push_cast
      ring, Complex.norm_real, Real.norm_of_nonneg hdsub.le] at hb'
    exact hb'

end TransportePosicion
