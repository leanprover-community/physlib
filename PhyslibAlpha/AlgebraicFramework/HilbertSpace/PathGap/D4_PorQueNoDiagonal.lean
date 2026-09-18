/-
Copyright (c) 2026 Eduardo Nava-Hernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eduardo Nava-Hernández, José Arturo Nava-Hernández, Gerardo Gabriel Nava Gómez
-/
module

public import PhyslibAlpha.AlgebraicFramework.HilbertSpace.PathGap.D3_GrafoCamino

/-!
# D4 — Why not a diagonal step

`D3_GrafoCamino.lean` pins the support of `T_d` on the minimal
(nearest-neighbour) steps of `pathGraph d`. This file closes, with
two independent arguments, the question of why a "diagonal" step
(changing more than one coordinate at once) is never an alternative:

1. **If there were ≥ 2 genuine axes** (generalising to a cubic lattice
   `Fin dx × Fin dy × Fin dz`), Pythagoras decides: the orthogonal
   step (one axis) has Euclidean distance exactly `1`; the double
   diagonal, exactly `√2`; the triple, exactly `√3`. Since
   `1 < √2` and `1 < √3`, the orthogonal step is always strictly
   shorter. This is not a design choice: it is the minimal
   adjacency that Pythagoras forces.
2. **In the case actually used by `T_d/P_d`** (a single axis,
   `dy = dz = 1`), the question does not even arise: with one
   genuine axis the "diagonal step" relation is the **empty**
   relation — no pair of sites satisfies it, because a trivial
   axis (`Fin 1`) has no minimal step at all. The diagonal
   presupposes, in order to be non-vacuously stated, two axes
   already distinguished from each other.
-/

@[expose] public section

noncomputable section

namespace PathGraph3D

/-- Site of a cubic lattice: product of three 1D lattices. -/
abbrev Sitio3D (dx dy dz : ℕ) := Fin dx × Fin dy × Fin dz

/-- Orthogonal adjacency of the cube: changes exactly one coordinate
at a time by a minimal step along that axis. -/
def Adj3D {dx dy dz : ℕ} (p q : Sitio3D dx dy dz) : Prop :=
  (TransportePosicion.PasoMinimo p.1 q.1 ∧ p.2 = q.2) ∨
    (p.1 = q.1 ∧ TransportePosicion.PasoMinimo p.2.1 q.2.1 ∧ p.2.2 = q.2.2) ∨
    (p.1 = q.1 ∧ p.2.1 = q.2.1 ∧ TransportePosicion.PasoMinimo p.2.2 q.2.2)

end PathGraph3D

/-! ## 1. Pythagoras: the orthogonal step is always strictly shorter -/

namespace OrtogonalidadMinimalPitagoras

open PathGraph3D
open TransportePosicion

/-- Euclidean distance between two cube sites, viewing each `Fin`
coordinate as a real via the natural cast. -/
noncomputable def dist3D {dx dy dz : ℕ} (p q : Sitio3D dx dy dz) : ℝ :=
  Real.sqrt (
    ((p.1 : ℝ) - (q.1 : ℝ)) ^ 2 +
    ((p.2.1 : ℝ) - (q.2.1 : ℝ)) ^ 2 +
    ((p.2.2 : ℝ) - (q.2.2 : ℝ)) ^ 2)

/-- Two coordinates at a `PasoMinimo` differ, as reals, by exactly
`±1`; their squared difference is `1`. -/
theorem pasoMinimo_sq_diff_eq_one {d : ℕ} {i j : Fin d} (h : PasoMinimo i j) :
    ((i.val : ℝ) - (j.val : ℝ)) ^ 2 = 1 := by
  rcases h with h | h
  · have hij : (j.val : ℝ) = (i.val : ℝ) + 1 := by exact_mod_cast h.symm
    rw [hij]; ring
  · have hji : (i.val : ℝ) = (j.val : ℝ) + 1 := by exact_mod_cast h.symm
    rw [hji]; ring

theorem eq_sq_diff_eq_zero {d : ℕ} {i j : Fin d} (h : i = j) :
    ((i.val : ℝ) - (j.val : ℝ)) ^ 2 = 0 := by
  rw [h]; ring

/-! ### Orthogonal step: distance exactly `1` -/

theorem dist3D_eq_one_of_Adj3D
    {dx dy dz : ℕ} {p q : Sitio3D dx dy dz} (h : Adj3D p q) :
    dist3D p q = 1 := by
  unfold dist3D
  rcases h with ⟨hx, hyz⟩ | ⟨hx, hy, hz⟩ | ⟨hx, hy, hz⟩
  · have hy0 : ((p.2.1 : ℝ) - (q.2.1 : ℝ)) ^ 2 = 0 :=
      eq_sq_diff_eq_zero (congrArg Prod.fst hyz)
    have hz0 : ((p.2.2 : ℝ) - (q.2.2 : ℝ)) ^ 2 = 0 :=
      eq_sq_diff_eq_zero (congrArg Prod.snd hyz)
    have hsum :
        ((p.1 : ℝ) - (q.1 : ℝ)) ^ 2 + ((p.2.1 : ℝ) - (q.2.1 : ℝ)) ^ 2 +
            ((p.2.2 : ℝ) - (q.2.2 : ℝ)) ^ 2 = 1 := by
      rw [pasoMinimo_sq_diff_eq_one hx, hy0, hz0]; ring
    rw [hsum, Real.sqrt_one]
  · have hx0 : ((p.1 : ℝ) - (q.1 : ℝ)) ^ 2 = 0 := eq_sq_diff_eq_zero hx
    have hz0 : ((p.2.2 : ℝ) - (q.2.2 : ℝ)) ^ 2 = 0 := eq_sq_diff_eq_zero hz
    have hsum :
        ((p.1 : ℝ) - (q.1 : ℝ)) ^ 2 + ((p.2.1 : ℝ) - (q.2.1 : ℝ)) ^ 2 +
            ((p.2.2 : ℝ) - (q.2.2 : ℝ)) ^ 2 = 1 := by
      rw [hx0, pasoMinimo_sq_diff_eq_one hy, hz0]; ring
    rw [hsum, Real.sqrt_one]
  · have hx0 : ((p.1 : ℝ) - (q.1 : ℝ)) ^ 2 = 0 := eq_sq_diff_eq_zero hx
    have hy0 : ((p.2.1 : ℝ) - (q.2.1 : ℝ)) ^ 2 = 0 := eq_sq_diff_eq_zero hy
    have hsum :
        ((p.1 : ℝ) - (q.1 : ℝ)) ^ 2 + ((p.2.1 : ℝ) - (q.2.1 : ℝ)) ^ 2 +
            ((p.2.2 : ℝ) - (q.2.2 : ℝ)) ^ 2 = 1 := by
      rw [hx0, hy0, pasoMinimo_sq_diff_eq_one hz]; ring
    rw [hsum, Real.sqrt_one]

/-! ### Double diagonal step: distance exactly `√2` -/

/-- Diagonal neighbour in two axes: two coordinates change by
`PasoMinimo` simultaneously, the third stays fixed. `Adj3D`
never produces this case. -/
def PasoDiagonalDoble {dx dy dz : ℕ} (p q : Sitio3D dx dy dz) : Prop :=
  (PasoMinimo p.1 q.1 ∧ PasoMinimo p.2.1 q.2.1 ∧ p.2.2 = q.2.2) ∨
  (PasoMinimo p.1 q.1 ∧ p.2.1 = q.2.1 ∧ PasoMinimo p.2.2 q.2.2) ∨
  (p.1 = q.1 ∧ PasoMinimo p.2.1 q.2.1 ∧ PasoMinimo p.2.2 q.2.2)

theorem dist3D_eq_sqrt_two_of_PasoDiagonalDoble
    {dx dy dz : ℕ} {p q : Sitio3D dx dy dz} (h : PasoDiagonalDoble p q) :
    dist3D p q = Real.sqrt 2 := by
  unfold dist3D
  rcases h with ⟨hx, hy, hz⟩ | ⟨hx, hy, hz⟩ | ⟨hx, hy, hz⟩
  · have hz0 : ((p.2.2 : ℝ) - (q.2.2 : ℝ)) ^ 2 = 0 := eq_sq_diff_eq_zero hz
    have hsum :
        ((p.1 : ℝ) - (q.1 : ℝ)) ^ 2 + ((p.2.1 : ℝ) - (q.2.1 : ℝ)) ^ 2 +
            ((p.2.2 : ℝ) - (q.2.2 : ℝ)) ^ 2 = 2 := by
      rw [pasoMinimo_sq_diff_eq_one hx, pasoMinimo_sq_diff_eq_one hy, hz0]; ring
    rw [hsum]
  · have hy0 : ((p.2.1 : ℝ) - (q.2.1 : ℝ)) ^ 2 = 0 := eq_sq_diff_eq_zero hy
    have hsum :
        ((p.1 : ℝ) - (q.1 : ℝ)) ^ 2 + ((p.2.1 : ℝ) - (q.2.1 : ℝ)) ^ 2 +
            ((p.2.2 : ℝ) - (q.2.2 : ℝ)) ^ 2 = 2 := by
      rw [pasoMinimo_sq_diff_eq_one hx, hy0, pasoMinimo_sq_diff_eq_one hz]; ring
    rw [hsum]
  · have hx0 : ((p.1 : ℝ) - (q.1 : ℝ)) ^ 2 = 0 := eq_sq_diff_eq_zero hx
    have hsum :
        ((p.1 : ℝ) - (q.1 : ℝ)) ^ 2 + ((p.2.1 : ℝ) - (q.2.1 : ℝ)) ^ 2 +
            ((p.2.2 : ℝ) - (q.2.2 : ℝ)) ^ 2 = 2 := by
      rw [hx0, pasoMinimo_sq_diff_eq_one hy, pasoMinimo_sq_diff_eq_one hz]; ring
    rw [hsum]

/-! ### Triple diagonal step: distance exactly `√3` -/

/-- Diagonal neighbour in all three axes (the unit cube corner). -/
def PasoDiagonalTriple {dx dy dz : ℕ} (p q : Sitio3D dx dy dz) : Prop :=
  PasoMinimo p.1 q.1 ∧ PasoMinimo p.2.1 q.2.1 ∧ PasoMinimo p.2.2 q.2.2

theorem dist3D_eq_sqrt_three_of_PasoDiagonalTriple
    {dx dy dz : ℕ} {p q : Sitio3D dx dy dz} (h : PasoDiagonalTriple p q) :
    dist3D p q = Real.sqrt 3 := by
  obtain ⟨hx, hy, hz⟩ := h
  unfold dist3D
  have hsum :
      ((p.1 : ℝ) - (q.1 : ℝ)) ^ 2 + ((p.2.1 : ℝ) - (q.2.1 : ℝ)) ^ 2 +
          ((p.2.2 : ℝ) - (q.2.2 : ℝ)) ^ 2 = 3 := by
    rw [pasoMinimo_sq_diff_eq_one hx, pasoMinimo_sq_diff_eq_one hy,
      pasoMinimo_sq_diff_eq_one hz]; ring
  rw [hsum]

/-! ### Pythagoras closure: the orthogonal step always wins -/

theorem uno_lt_sqrt_two : (1 : ℝ) < Real.sqrt 2 := by
  have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  nlinarith [Real.sqrt_nonneg (2 : ℝ), h2]

theorem uno_lt_sqrt_three : (1 : ℝ) < Real.sqrt 3 := by
  have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  nlinarith [Real.sqrt_nonneg (3 : ℝ), h3]

/-- The orthogonal step (the only one admitted by `Adj3D`) is
strictly shorter than any double diagonal step. -/
theorem ortogonal_mas_corto_que_diagonal_doble
    {dx dy dz : ℕ} {p q p' q' : Sitio3D dx dy dz}
    (hOrt : Adj3D p q) (hDiag : PasoDiagonalDoble p' q') :
    dist3D p q < dist3D p' q' := by
  rw [dist3D_eq_one_of_Adj3D hOrt, dist3D_eq_sqrt_two_of_PasoDiagonalDoble hDiag]
  exact uno_lt_sqrt_two

/-- The orthogonal step is strictly shorter than any triple
diagonal step (the cube corner). -/
theorem ortogonal_mas_corto_que_diagonal_triple
    {dx dy dz : ℕ} {p q p' q' : Sitio3D dx dy dz}
    (hOrt : Adj3D p q) (hDiag : PasoDiagonalTriple p' q') :
    dist3D p q < dist3D p' q' := by
  rw [dist3D_eq_one_of_Adj3D hOrt, dist3D_eq_sqrt_three_of_PasoDiagonalTriple hDiag]
  exact uno_lt_sqrt_three

/-- CLOSURE. No diagonal (double or triple) can tie or beat the
orthogonal step in distance: the minimal adjacency of the cube
(`Adj3D`) is the only one compatible with Euclidean distance
minimality. This is not an arbitrary choice: it is the one
Pythagoras forces. -/
theorem adyacencia_minima_es_ortogonal
    {dx dy dz : ℕ} {p q p' q' : Sitio3D dx dy dz}
    (hOrt : Adj3D p q)
    (hDiag : PasoDiagonalDoble p' q' ∨ PasoDiagonalTriple p' q') :
    dist3D p q < dist3D p' q' := by
  rcases hDiag with hD | hD
  · exact ortogonal_mas_corto_que_diagonal_doble hOrt hD
  · exact ortogonal_mas_corto_que_diagonal_triple hOrt hD

end OrtogonalidadMinimalPitagoras

/-! ## 2. With a single axis, the diagonal is the empty relation -/

namespace DiagonalPresuponeDosPd

open PathGraph3D
open OrtogonalidadMinimalPitagoras

/-- On a trivial axis (`Fin 1`, a single point) there is no
minimal step: `PasoMinimo` is the empty relation. -/
theorem pasoMinimo_vacio_en_eje_trivial (i j : Fin 1) :
    ¬ TransportePosicion.PasoMinimo i j := by
  unfold TransportePosicion.PasoMinimo
  have hi := i.isLt
  have hj := j.isLt
  omega

/-- With a single genuine axis (`dy = dz = 1`),
`PasoDiagonalDoble` is the empty relation: no pair of sites
satisfies it. -/
theorem diagonalDoble_vacia_con_un_solo_eje
    {dx : ℕ} (p q : Sitio3D dx 1 1) : ¬ PasoDiagonalDoble p q := by
  unfold PasoDiagonalDoble
  rintro (⟨_, hy, _⟩ | ⟨_, _, hz⟩ | ⟨_, hy, _⟩)
  · exact pasoMinimo_vacio_en_eje_trivial p.2.1 q.2.1 hy
  · exact pasoMinimo_vacio_en_eje_trivial p.2.2 q.2.2 hz
  · exact pasoMinimo_vacio_en_eje_trivial p.2.1 q.2.1 hy

/-- With a single genuine axis, `PasoDiagonalTriple` (the cube
corner) does not exist either: it is also the empty relation. -/
theorem diagonalTriple_vacia_con_un_solo_eje
    {dx : ℕ} (p q : Sitio3D dx 1 1) : ¬ PasoDiagonalTriple p q := by
  unfold PasoDiagonalTriple
  rintro ⟨_, hy, _⟩
  exact pasoMinimo_vacio_en_eje_trivial p.2.1 q.2.1 hy

/-- CLOSURE. With a single axis, no diagonal — double or triple —
exists. The diagonal is, in the literal set-theoretic sense,
posterior to the existence of two distinguished axes: not prior,
not simultaneous, not elementary. The model `T_d/P_d` (a single
axis) never needs to exclude it by decree: there is nothing to
exclude. -/
theorem diagonal_no_existe_con_un_solo_eje
    {dx : ℕ} (p q : Sitio3D dx 1 1) :
    ¬ (PasoDiagonalDoble p q ∨ PasoDiagonalTriple p q) := by
  rintro (h | h)
  · exact diagonalDoble_vacia_con_un_solo_eje p q h
  · exact diagonalTriple_vacia_con_un_solo_eje p q h

end DiagonalPresuponeDosPd

end
