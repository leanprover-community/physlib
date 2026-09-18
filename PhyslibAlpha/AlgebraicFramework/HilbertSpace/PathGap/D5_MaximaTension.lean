/-
Copyright (c) 2026 Eduardo Nava-Hernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eduardo Nava-Hernández, José Arturo Nava-Hernández, Gerardo Gabriel Nava Gómez
-/
module

public import PhyslibAlpha.AlgebraicFramework.HilbertSpace.PathGap.D3_GrafoCamino
public import Mathlib.Analysis.CStarAlgebra.Module.Constructions
public import Mathlib.Analysis.InnerProductSpace.Spectrum
public import Mathlib.Analysis.Matrix.Hermitian
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.PicardGroup
public import Mathlib.RingTheory.SimpleRing.Principal

/-!
# D5 — Maximal-tension state and the observable `i[T_d,P_d]`

In finite dimension, `i[T,P]` is symmetric (Hermitian) whenever `T`
and `P` are; by the finite spectral theorem it has an orthonormal
eigenbasis. This file picks the eigenvector whose eigenvalue has
maximal absolute value and proves the envelope over all normalised
states: that state realises, among all unit states of the same
channel, the greatest possible commutator tension. The same extremal
state is then exhibited in explicit coordinates (sine-phase mode)
for the concrete pair `(T_d,P_d)` of the discrete path: it is the
"Fiedler mode" of the chain.

Closes with a concrete non-commutativity certificate:
`[T_d,P_d] ≠ 0` for `d ≥ 2`, witnessed by a single matrix entry.
-/

@[expose] public section

noncomputable section

namespace ConstructorEspectralTP

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [FiniteDimensional ℂ H] [Nontrivial H]

/-- In positive dimension there exists an index whose eigenvalue
has maximal absolute value. -/
theorem existe_indice_extremal (K : H →ₗ[ℂ] H) (hK : K.IsSymmetric) :
    ∃ i : Fin (Module.finrank ℂ H),
      ∀ j : Fin (Module.finrank ℂ H),
        |hK.eigenvalues rfl j| ≤ |hK.eigenvalues rfl i| := by
  have hne : (Finset.univ : Finset (Fin (Module.finrank ℂ H))).Nonempty := by
    exact ⟨⟨0, Module.finrank_pos⟩, Finset.mem_univ _⟩
  obtain ⟨i, _, hi⟩ :=
    Finset.exists_max_image
      (Finset.univ : Finset (Fin (Module.finrank ℂ H)))
      (fun j => |hK.eigenvalues rfl j|) hne
  exact ⟨i, fun j => hi j (Finset.mem_univ j)⟩

/-- An index at which the absolute eigenvalue of `K` is maximal. -/
def indiceExtremal (K : H →ₗ[ℂ] H) (hK : K.IsSymmetric) :
    Fin (Module.finrank ℂ H) :=
  (existe_indice_extremal K hK).choose

/-- The eigenvalue selected by `indiceExtremal`. -/
def autovalorExtremal (K : H →ₗ[ℂ] H) (hK : K.IsSymmetric) : ℝ :=
  hK.eigenvalues rfl (indiceExtremal K hK)

/-- Spectral radius realised by the chosen state. -/
def radioEspectral (K : H →ₗ[ℂ] H) (hK : K.IsSymmetric) : ℝ :=
  |autovalorExtremal K hK|

/-- Unit state of maximal tension. -/
def estadoExtremal (K : H →ₗ[ℂ] H) (hK : K.IsSymmetric) : H :=
  hK.eigenvectorBasis rfl (indiceExtremal K hK)

theorem modulo_autovalor_le_radio
    (K : H →ₗ[ℂ] H) (hK : K.IsSymmetric)
    (j : Fin (Module.finrank ℂ H)) :
    |hK.eigenvalues rfl j| ≤ radioEspectral K hK := by
  exact (existe_indice_extremal K hK).choose_spec j

theorem radioEspectral_nonneg (K : H →ₗ[ℂ] H) (hK : K.IsSymmetric) :
    0 ≤ radioEspectral K hK :=
  abs_nonneg _

theorem estadoExtremal_normalizado (K : H →ₗ[ℂ] H) (hK : K.IsSymmetric) :
    ‖estadoExtremal K hK‖ = 1 := by
  exact (hK.eigenvectorBasis rfl).orthonormal.norm_eq_one (indiceExtremal K hK)

theorem aplica_estadoExtremal (K : H →ₗ[ℂ] H) (hK : K.IsSymmetric) :
    K (estadoExtremal K hK) =
      (autovalorExtremal K hK : ℂ) • estadoExtremal K hK := by
  exact hK.apply_eigenvectorBasis rfl (indiceExtremal K hK)

/-- The action of a symmetric operator is bounded by the chosen
spectral radius. -/
theorem norma_aplicacion_le_radio_mul_norma
    (K : H →ₗ[ℂ] H) (hK : K.IsSymmetric) (v : H) :
    ‖K v‖ ≤ radioEspectral K hK * ‖v‖ := by
  let hn : Module.finrank ℂ H = Module.finrank ℂ H := rfl
  have hKv_sq :
      ‖K v‖ ^ 2 =
        ∑ i : Fin (Module.finrank ℂ H),
          ‖(hK.eigenvalues hn i : ℂ) *
            ((hK.eigenvectorBasis hn).repr v i)‖ ^ 2 := by
    calc
      ‖K v‖ ^ 2 = ‖(hK.eigenvectorBasis hn).repr (K v)‖ ^ 2 := by
        rw [(hK.eigenvectorBasis hn).repr.norm_map]
      _ = ∑ i : Fin (Module.finrank ℂ H),
          ‖(hK.eigenvectorBasis hn).repr (K v) i‖ ^ 2 :=
        EuclideanSpace.norm_sq_eq _
      _ = ∑ i : Fin (Module.finrank ℂ H),
          ‖(hK.eigenvalues hn i : ℂ) *
            ((hK.eigenvectorBasis hn).repr v i)‖ ^ 2 := by
        apply Finset.sum_congr rfl
        intro i _
        exact congrArg (fun z : ℂ => ‖z‖ ^ 2)
          (hK.eigenvectorBasis_apply_self_apply hn v i)
  have hsum_le :
      (∑ i : Fin (Module.finrank ℂ H),
          ‖(hK.eigenvalues hn i : ℂ) *
            ((hK.eigenvectorBasis hn).repr v i)‖ ^ 2) ≤
        ∑ i : Fin (Module.finrank ℂ H),
          radioEspectral K hK ^ 2 *
            ‖(hK.eigenvectorBasis hn).repr v i‖ ^ 2 := by
    apply Finset.sum_le_sum
    intro i _
    have hi := modulo_autovalor_le_radio K hK i
    have hi' :
        |hK.eigenvalues hn i| ≤ radioEspectral K hK := by
      simpa only using hi
    have hi_nonneg : 0 ≤ |hK.eigenvalues hn i| := abs_nonneg _
    have hR_nonneg := radioEspectral_nonneg K hK
    have hi_sq :
        |hK.eigenvalues hn i| ^ 2 ≤ radioEspectral K hK ^ 2 := by
      nlinarith [hi']
    simpa only [norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow] using
      mul_le_mul_of_nonneg_right hi_sq
        (sq_nonneg ‖(hK.eigenvectorBasis hn).repr v i‖)
  have hv_sq :
      (∑ i : Fin (Module.finrank ℂ H),
          radioEspectral K hK ^ 2 *
            ‖(hK.eigenvectorBasis hn).repr v i‖ ^ 2) =
        radioEspectral K hK ^ 2 * ‖v‖ ^ 2 := by
    rw [← Finset.mul_sum, ← EuclideanSpace.norm_sq_eq]
    rw [(hK.eigenvectorBasis hn).repr.norm_map]
  have hsq :
      ‖K v‖ ^ 2 ≤ (radioEspectral K hK * ‖v‖) ^ 2 := by
    rw [hKv_sq, mul_pow]
    exact hsum_le.trans_eq hv_sq
  have hleft : 0 ≤ ‖K v‖ := norm_nonneg _
  have hright : 0 ≤ radioEspectral K hK * ‖v‖ :=
    mul_nonneg (radioEspectral_nonneg K hK) (norm_nonneg _)
  nlinarith

/-- Envelope of the quadratic form on the unit sphere. -/
theorem expectativa_le_radio
    (K : H →ₗ[ℂ] H) (hK : K.IsSymmetric)
    (v : H) (hv : ‖v‖ = 1) :
    ‖@inner ℂ H _ v (K v)‖ ≤ radioEspectral K hK := by
  calc
    ‖@inner ℂ H _ v (K v)‖ ≤ ‖v‖ * ‖K v‖ :=
      norm_inner_le_norm v (K v)
    _ ≤ ‖v‖ * (radioEspectral K hK * ‖v‖) :=
      mul_le_mul_of_nonneg_left
        (norma_aplicacion_le_radio_mul_norma K hK v) (norm_nonneg _)
    _ = radioEspectral K hK := by rw [hv]; ring

/-- The chosen state realises exactly the spectral radius. -/
theorem estadoExtremal_realiza_radio
    (K : H →ₗ[ℂ] H) (hK : K.IsSymmetric) :
    ‖@inner ℂ H _ (estadoExtremal K hK) (K (estadoExtremal K hK))‖ =
      radioEspectral K hK := by
  rw [aplica_estadoExtremal K hK, inner_smul_right]
  rw [inner_self_eq_norm_sq_to_K, estadoExtremal_normalizado K hK]
  simp [radioEspectral, autovalorExtremal]

/-- Raw commutator `[T,P]`. -/
def conmutador (T P : H →ₗ[ℂ] H) : H →ₗ[ℂ] H :=
  T.comp P - P.comp T

/-- Hermitian tension observable `i[T,P]`. -/
def observableTension (T P : H →ₗ[ℂ] H) : H →ₗ[ℂ] H :=
  Complex.I • conmutador T P

/-- For symmetric operators, `i[T,P]` is symmetric. -/
theorem observableTension_simetrico
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (T P : E →ₗ[ℂ] E) (hT : T.IsSymmetric) (hP : P.IsSymmetric) :
    (observableTension T P).IsSymmetric := by
  intro x y
  change
    @inner ℂ E _ (Complex.I • (T (P x) - P (T x))) y =
      @inner ℂ E _ x (Complex.I • (T (P y) - P (T y)))
  rw [inner_smul_left, inner_smul_right, inner_sub_left, inner_sub_right]
  rw [hT (P x) y, hP x (T y), hP (T x) y, hT x (P y)]
  simp only [Complex.conj_I]
  ring

theorem radioEspectral_pos_of_ne_zero
    (K : H →ₗ[ℂ] H) (hK : K.IsSymmetric) (hK0 : K ≠ 0) :
    0 < radioEspectral K hK := by
  have hR0 : radioEspectral K hK ≠ 0 := by
    intro hR
    apply hK0
    ext v
    have hv := norma_aplicacion_le_radio_mul_norma K hK v
    rw [hR, zero_mul] at hv
    exact norm_eq_zero.mp (le_antisymm hv (norm_nonneg _))
  exact lt_of_le_of_ne (radioEspectral_nonneg K hK) (Ne.symm hR0)

theorem observableTension_ne_zero
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (T P : E →ₗ[ℂ] E) (hC : conmutador T P ≠ 0) :
    observableTension T P ≠ 0 := by
  intro hK
  apply hC
  ext v
  have hv := LinearMap.congr_fun hK v
  change Complex.I • conmutador T P v = 0 at hv
  exact (smul_eq_zero.mp hv).resolve_left Complex.I_ne_zero

end ConstructorEspectralTP

namespace TransportePosicion

open ConstructorEspectralTP

/-- Full linear realisation of the canonical transport matrix. -/
noncomputable def TdOp (d : ℕ) : Hd d →ₗ[ℂ] Hd d :=
  Matrix.toEuclideanLin (Td d)

/-- Full linear realisation of the canonical position matrix. -/
noncomputable def PdOp (d : ℕ) : Hd d →ₗ[ℂ] Hd d :=
  Matrix.toEuclideanLin (Pd d)

theorem pasoMinimo_simetrico {d : ℕ} {i j : Fin d} :
    PasoMinimo i j ↔ PasoMinimo j i := by
  constructor <;> rintro (h | h)
  · exact Or.inr h
  · exact Or.inl h
  · exact Or.inr h
  · exact Or.inl h

/-- The transport matrix is Hermitian. -/
theorem Td_isHermitian (d : ℕ) : Matrix.IsHermitian (Td d) := by
  rw [Matrix.IsHermitian.ext_iff]
  intro i j
  have hrho : star (rho d : ℂ) = (rho d : ℂ) := by
    exact Complex.conj_ofReal _
  by_cases h : PasoMinimo i j
  · have h' : PasoMinimo j i := pasoMinimo_simetrico.mp h
    simp only [Td, Ad, h, h', if_pos]
    rw [one_div, star_inv₀, hrho]
  · have h' : ¬PasoMinimo j i := by
      intro hji
      exact h (pasoMinimo_simetrico.mpr hji)
    simp [Td, Ad, h, h']

/-- The diagonal position matrix is Hermitian. -/
theorem Pd_isHermitian (d : ℕ) : Matrix.IsHermitian (Pd d) := by
  rw [Matrix.IsHermitian.ext_iff]
  intro i j
  by_cases hij : i = j
  · subst j
    simp [Pd, posicionCoord]
  · have hji : j ≠ i := Ne.symm hij
    simp [Pd, hij, hji]

theorem TdOp_simetrico (d : ℕ) : (TdOp d).IsSymmetric := by
  exact Matrix.isSymmetric_toEuclideanLin_iff.mpr (Td_isHermitian d)

theorem PdOp_simetrico (d : ℕ) : (PdOp d).IsSymmetric := by
  exact Matrix.isSymmetric_toEuclideanLin_iff.mpr (Pd_isHermitian d)

/-- Concrete Hermitian observable `i[T_d,P_d]`. -/
noncomputable def KdOp (d : ℕ) : Hd d →ₗ[ℂ] Hd d :=
  observableTension (TdOp d) (PdOp d)

theorem KdOp_simetrico (d : ℕ) : (KdOp d).IsSymmetric :=
  observableTension_simetrico (TdOp d) (PdOp d)
    (TdOp_simetrico d) (PdOp_simetrico d)

/-- Canonical state `ψ_d`: unit eigenvector of `i[T_d,P_d]` whose
eigenvalue has maximal absolute value. -/
noncomputable def psiD (d : ℕ) (hd : 1 ≤ d) : Hd d := by
  letI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  exact estadoExtremal (KdOp d) (KdOp_simetrico d)

theorem psiD_normalizado (d : ℕ) (hd : 1 ≤ d) :
    ‖psiD d hd‖ = 1 := by
  letI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  exact estadoExtremal_normalizado (KdOp d) (KdOp_simetrico d)

/-! ## Explicit Fiedler vector

The spectral choice above realises the maximal tension but does not
expose its coordinates. The following mode pins the sine-phase
realisation on `Fin d`. Positivity of `sin` on `(0, π)`
constructively proves that no coordinate vanishes. -/

/-- Fundamental angle of the finite path. -/
noncomputable def anguloFiedler (d : ℕ) : ℝ :=
  Real.pi / ((d : ℝ) + 1)

/-- Sine mode with the complex phase of `i[T_d,P_d]`, not yet
normalized. -/
noncomputable def vectorFiedlerCrudo (d : ℕ) : Hd d :=
  WithLp.toLp 2 fun j : Fin d =>
    (-Complex.I) ^ j.val *
      (Real.sin (((j.val : ℝ) + 1) * anguloFiedler d) : ℂ)

/-- All sine amplitudes of the fundamental mode are strictly
positive. -/
theorem seno_fiedler_pos
    (d : ℕ) (hd : 1 ≤ d) (j : Fin d) :
    0 < Real.sin (((j.val : ℝ) + 1) * anguloFiedler d) := by
  apply Real.sin_pos_of_pos_of_lt_pi
  · unfold anguloFiedler
    positivity
  · unfold anguloFiedler
    have hj : (j.val : ℝ) + 1 < (d : ℝ) + 1 := by
      exact_mod_cast Nat.add_lt_add_right j.isLt 1
    have hden : 0 < (d : ℝ) + 1 := by positivity
    calc
      ((j.val : ℝ) + 1) * (Real.pi / ((d : ℝ) + 1)) =
          (((j.val : ℝ) + 1) / ((d : ℝ) + 1)) * Real.pi := by ring
      _ < 1 * Real.pi :=
        mul_lt_mul_of_pos_right ((div_lt_one hden).2 hj) Real.pi_pos
      _ = Real.pi := one_mul _

theorem vectorFiedlerCrudo_coordenada_ne_zero
    (d : ℕ) (hd : 1 ≤ d) (j : Fin d) :
    vectorFiedlerCrudo d j ≠ 0 := by
  unfold vectorFiedlerCrudo
  apply mul_ne_zero
  · exact pow_ne_zero _ (neg_ne_zero.mpr Complex.I_ne_zero)
  · exact Complex.ofReal_ne_zero.mpr
      (ne_of_gt (seno_fiedler_pos d hd j))

theorem vectorFiedlerCrudo_ne_zero
    (d : ℕ) (hd : 1 ≤ d) :
    vectorFiedlerCrudo d ≠ 0 := by
  let j : Fin d := ⟨0, hd⟩
  intro h
  have hj := congrArg (fun v : Hd d => v j) h
  exact vectorFiedlerCrudo_coordenada_ne_zero d hd j hj

/-- Explicit normalized Fiedler vector, no eigenvector choice. -/
noncomputable def vectorFiedlerExplicito (d : ℕ) : Hd d :=
  ((‖vectorFiedlerCrudo d‖ : ℂ)⁻¹) • vectorFiedlerCrudo d

theorem vectorFiedlerExplicito_normalizado
    (d : ℕ) (hd : 1 ≤ d) :
    ‖vectorFiedlerExplicito d‖ = 1 := by
  rw [vectorFiedlerExplicito, norm_smul]
  have hn : ‖vectorFiedlerCrudo d‖ ≠ 0 :=
    norm_ne_zero_iff.mpr (vectorFiedlerCrudo_ne_zero d hd)
  simp [hn]

theorem vectorFiedlerExplicito_coordenada_ne_zero
    (d : ℕ) (hd : 1 ≤ d) (j : Fin d) :
    vectorFiedlerExplicito d j ≠ 0 := by
  rw [vectorFiedlerExplicito]
  change (↑‖vectorFiedlerCrudo d‖ : ℂ)⁻¹ * vectorFiedlerCrudo d j ≠ 0
  apply mul_ne_zero
  · exact inv_ne_zero (Complex.ofReal_ne_zero.mpr
      (norm_ne_zero_iff.mpr (vectorFiedlerCrudo_ne_zero d hd)))
  · exact vectorFiedlerCrudo_coordenada_ne_zero d hd j

theorem Td_mul_Pd_apply (d : ℕ) (i j : Fin d) :
    (Td d * Pd d) i j = Td d i j * (posicionCoord d j : ℂ) := by
  rw [Matrix.mul_apply, Finset.sum_eq_single j]
  · simp [Pd]
  · intro k _ hkj
    simp [Pd, hkj]
  · simp

theorem Pd_mul_Td_apply (d : ℕ) (i j : Fin d) :
    (Pd d * Td d) i j = (posicionCoord d i : ℂ) * Td d i j := by
  rw [Matrix.mul_apply, Finset.sum_eq_single i]
  · simp [Pd]
  · intro k _ hki
    simp [Pd, Ne.symm hki]
  · simp

theorem rho_pos (d : ℕ) (hd : 2 ≤ d) : 0 < rho d := by
  have hden : 0 < (d : ℝ) + 1 := by positivity
  have hden3 : (3 : ℝ) ≤ (d : ℝ) + 1 := by
    exact_mod_cast (show 3 ≤ d + 1 by omega)
  have hfrac : 1 / ((d : ℝ) + 1) < (1 : ℝ) / 2 := by
    rw [div_lt_div_iff₀ hden (by norm_num : (0 : ℝ) < 2)]
    linarith
  have hangle_pos : 0 < Real.pi / ((d : ℝ) + 1) :=
    div_pos Real.pi_pos hden
  have hangle_lt :
      Real.pi / ((d : ℝ) + 1) < Real.pi / 2 := by
    have hmul := mul_lt_mul_of_pos_left hfrac Real.pi_pos
    simpa [div_eq_mul_inv] using hmul
  have hcos :
      0 < Real.cos (Real.pi / ((d : ℝ) + 1)) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hangle_lt⟩
  unfold rho
  positivity

theorem posicionCoord_succ_sub
    (d : ℕ) (hd : 2 ≤ d)
    (i j : Fin d) (hij : i.val + 1 = j.val) :
    posicionCoord d j - posicionCoord d i = 2 / ((d : ℝ) - 1) := by
  unfold posicionCoord
  have hdsub : (d : ℝ) - 1 ≠ 0 := by
    have : (1 : ℝ) < d := by exact_mod_cast (show 1 < d by omega)
    linarith
  have hijr : (j.val : ℝ) = (i.val : ℝ) + 1 := by exact_mod_cast hij.symm
  rw [hijr]
  field_simp
  ring

/-- Concrete non-commutativity certificate: one neighbour entry suffices. -/
theorem conmutador_matriz_entrada_vecina_no_cero
    (d : ℕ) (hd : 2 ≤ d) :
    let i : Fin d := ⟨0, by omega⟩
    let j : Fin d := ⟨1, by omega⟩
    ((Td d * Pd d) - (Pd d * Td d)) i j ≠ 0 := by
  dsimp only
  let i : Fin d := ⟨0, by omega⟩
  let j : Fin d := ⟨1, by omega⟩
  have hij : i.val + 1 = j.val := rfl
  have hpaso : PasoMinimo i j := Or.inl hij
  have hrho : (rho d : ℂ) ≠ 0 := by
    exact_mod_cast (rho_pos d hd).ne'
  have hdelta :
      (posicionCoord d j : ℂ) - (posicionCoord d i : ℂ) ≠ 0 := by
    have hdpos : 0 < (2 : ℝ) / ((d : ℝ) - 1) := by
      have : (1 : ℝ) < d := by exact_mod_cast (show 1 < d by omega)
      positivity
    exact_mod_cast
      ((posicionCoord_succ_sub d hd i j hij).trans_ne hdpos.ne')
  rw [Matrix.sub_apply, Td_mul_Pd_apply, Pd_mul_Td_apply]
  have hTd : Td d i j = 1 / (rho d : ℂ) := by
    simp [Td, Ad, hpaso]
  rw [hTd]
  intro hz
  have hz0 :
      (rho d : ℂ)⁻¹ * (posicionCoord d j : ℂ) -
        (posicionCoord d i : ℂ) * (rho d : ℂ)⁻¹ = 0 := by
    simpa [i, j, one_div] using hz
  have hz' :
      (rho d : ℂ)⁻¹ *
        ((posicionCoord d j : ℂ) - (posicionCoord d i : ℂ)) = 0 := by
    calc
      (rho d : ℂ)⁻¹ *
          ((posicionCoord d j : ℂ) - (posicionCoord d i : ℂ)) =
        (rho d : ℂ)⁻¹ * (posicionCoord d j : ℂ) -
          (posicionCoord d i : ℂ) * (rho d : ℂ)⁻¹ := by ring
      _ = 0 := hz0
  exact hdelta ((mul_eq_zero.mp hz').resolve_left (inv_ne_zero hrho))

theorem conmutador_matriz_no_cero (d : ℕ) (hd : 2 ≤ d) :
    (Td d * Pd d) - (Pd d * Td d) ≠ 0 := by
  intro hz
  have hentry := congrFun (congrFun hz ⟨0, by omega⟩) ⟨1, by omega⟩
  exact conmutador_matriz_entrada_vecina_no_cero d hd hentry

theorem conmutador_TdOp_PdOp_eq_matriz (d : ℕ) :
    conmutador (TdOp d) (PdOp d) =
      Matrix.toEuclideanLin ((Td d * Pd d) - (Pd d * Td d)) := by
  simp [conmutador, TdOp, PdOp, Matrix.toEuclideanLin, Matrix.toLpLin_mul_same]

/-- `[T_d,P_d] ≠ 0` for `d ≥ 2`. -/
theorem conmutador_TdOp_PdOp_no_cero (d : ℕ) (hd : 2 ≤ d) :
    conmutador (TdOp d) (PdOp d) ≠ 0 := by
  rw [conmutador_TdOp_PdOp_eq_matriz]
  intro hz
  apply conmutador_matriz_no_cero d hd
  apply Matrix.toEuclideanLin.injective
  simpa using hz

theorem KdOp_no_cero (d : ℕ) (hd : 2 ≤ d) : KdOp d ≠ 0 :=
  observableTension_ne_zero (TdOp d) (PdOp d)
    (conmutador_TdOp_PdOp_no_cero d hd)

end TransportePosicion
