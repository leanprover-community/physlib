/-
Copyright (c) 2026 Rob Sneiderman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rob Sneiderman
-/
module

public import Physlib.SpaceAndTime.Space.EuclideanGroup.Basic
public import Physlib.SpaceAndTime.Space.Origin
public import Physlib.SpaceAndTime.Time.InnerProductSpace

/-!
# The Galilean group

This file defines Galilean transformations in `d` spatial dimensions, together with their group
law and their action on `Time × Space d`.

An element consists of a spatial orthogonal transformation `R`, a boost velocity `v`, a spatial
translation `a`, and a time translation `b`. We use the active convention
`(t, x) ↦ (t + b, R x + v t + a)`.
-/

@[expose] public section

variable {d : ℕ}

/-- A Galilean transformation in `d` spatial dimensions. The fields are, in order, the spatial
orthogonal part, boost velocity, spatial translation, and time translation. -/
@[ext]
structure GalileanGroup (d : ℕ := 3) where
  /-- The spatial orthogonal part. -/
  rotation : Matrix.orthogonalGroup (Fin d) ℝ
  /-- The boost velocity. -/
  velocity : EuclideanSpace ℝ (Fin d)
  /-- The spatial translation. -/
  spaceTranslation : EuclideanSpace ℝ (Fin d)
  /-- The time translation. -/
  timeTranslation : Time

namespace GalileanGroup

/-! ## A. Basic support lemmas -/

lemma orthogonal_smul_smul (R : Matrix.orthogonalGroup (Fin d) ℝ) (c : ℝ)
    (v : EuclideanSpace ℝ (Fin d)) :
    R • (c • v) = c • (R • v) := by
  change (DistribMulAction.toLinearEquiv ℝ (EuclideanSpace ℝ (Fin d)) R) (c • v) =
    c • ((DistribMulAction.toLinearEquiv ℝ (EuclideanSpace ℝ (Fin d)) R) v)
  rw [map_smul]

/-! ## B. Group operations -/

/-- The identity Galilean transformation. -/
instance : One (GalileanGroup d) where
  one := ⟨1, 0, 0, 0⟩

@[simp]
lemma one_rotation : (1 : GalileanGroup d).rotation = 1 := rfl

@[simp]
lemma one_velocity : (1 : GalileanGroup d).velocity = 0 := rfl

@[simp]
lemma one_spaceTranslation : (1 : GalileanGroup d).spaceTranslation = 0 := rfl

@[simp]
lemma one_timeTranslation : (1 : GalileanGroup d).timeTranslation = 0 := rfl

/-- The product whose action is composition: `(g * h) • tx = g • h • tx`. -/
instance : Mul (GalileanGroup d) where
  mul g h :=
    ⟨g.rotation * h.rotation,
      g.rotation • h.velocity + g.velocity,
      g.spaceTranslation + g.rotation • h.spaceTranslation + h.timeTranslation.val • g.velocity,
      g.timeTranslation + h.timeTranslation⟩

@[simp]
lemma mul_rotation (g h : GalileanGroup d) :
    (g * h).rotation = g.rotation * h.rotation := rfl

@[simp]
lemma mul_velocity (g h : GalileanGroup d) :
    (g * h).velocity = g.rotation • h.velocity + g.velocity := rfl

@[simp]
lemma mul_spaceTranslation (g h : GalileanGroup d) :
    (g * h).spaceTranslation =
      g.spaceTranslation + g.rotation • h.spaceTranslation + h.timeTranslation.val • g.velocity :=
  rfl

@[simp]
lemma mul_timeTranslation (g h : GalileanGroup d) :
    (g * h).timeTranslation = g.timeTranslation + h.timeTranslation := rfl

/-- The inverse Galilean transformation. -/
instance : Inv (GalileanGroup d) where
  inv g :=
    ⟨g.rotation⁻¹,
      -(g.rotation⁻¹ • g.velocity),
      -(g.rotation⁻¹ • g.spaceTranslation) + g.timeTranslation.val • (g.rotation⁻¹ • g.velocity),
      -g.timeTranslation⟩

@[simp]
lemma inv_rotation (g : GalileanGroup d) :
    g⁻¹.rotation = g.rotation⁻¹ := rfl

/-- The inverse boost velocity formula. -/
@[simp]
lemma inv_velocity (g : GalileanGroup d) :
    g⁻¹.velocity = -(g.rotation⁻¹ • g.velocity) := rfl

@[simp]
lemma inv_spaceTranslation (g : GalileanGroup d) :
    g⁻¹.spaceTranslation =
      -(g.rotation⁻¹ • g.spaceTranslation) +
        g.timeTranslation.val • (g.rotation⁻¹ • g.velocity) := rfl

@[simp]
lemma inv_timeTranslation (g : GalileanGroup d) :
    g⁻¹.timeTranslation = -g.timeTranslation := rfl

/-- The Galilean transformations form a group under composition. -/
instance : Group (GalileanGroup d) where
  mul_assoc g h k := by
    refine GalileanGroup.ext ?_ ?_ ?_ ?_
    · simpa using (mul_assoc g.rotation h.rotation k.rotation)
    · simp [mul_smul, smul_add, add_assoc]
    · simp only [mul_spaceTranslation, mul_rotation, mul_velocity, mul_timeTranslation,
        Time.add_val]
      rw [mul_smul, smul_add, smul_add, add_smul, smul_add, orthogonal_smul_smul]
      abel
    · ext
      simp [Time.add_val, add_assoc]
  one_mul g := by
    refine GalileanGroup.ext ?_ ?_ ?_ ?_
    · simp
    · simp
    · simp
    · ext
      simp
  mul_one g := by
    refine GalileanGroup.ext ?_ ?_ ?_ ?_
    · simp
    · simp
    · simp
    · ext
      simp
  inv_mul_cancel g := by
    refine GalileanGroup.ext ?_ ?_ ?_ ?_
    · simp
    · simp
    · simp [smul_neg, add_comm, add_left_comm]
    · ext
      simp

instance : Inhabited (GalileanGroup d) where
  default := 1

/-! ## C. Action on time and space -/

/-- The Galilean action on space at the time `t`, `x ↦ R x + v t + a`. -/
noncomputable def actSpace (g : GalileanGroup d) (t : Time) (x : Space d) : Space d :=
  Space.vectorToSpace
    (g.rotation • (x -ᵥ (0 : Space d)) + t.val • g.velocity + g.spaceTranslation)

/-- The Galilean action on `Time × Space d`. -/
noncomputable def act (g : GalileanGroup d) (tx : Time × Space d) : Time × Space d :=
  (tx.1 + g.timeTranslation, g.actSpace tx.1 tx.2)

noncomputable instance : MulAction (GalileanGroup d) (Time × Space d) where
  smul := act
  one_smul tx := by
    rcases tx with ⟨t, x⟩
    change act (1 : GalileanGroup d) (t, x) = (t, x)
    ext i <;> simp [act, actSpace]
  mul_smul g h tx := by
    rcases tx with ⟨t, x⟩
    change act (g * h) (t, x) = act g (act h (t, x))
    ext i
    · simp [act, Time.add_val, add_comm, add_left_comm]
    · simp only [act, actSpace, Space.vectorToSpace_apply, Space.vectorToSpace_vsub_zero,
        mul_rotation, mul_velocity, mul_spaceTranslation, mul_timeTranslation, Time.add_val]
      rw [mul_smul, smul_add, smul_add, smul_add, orthogonal_smul_smul]
      simp only [PiLp.add_apply, PiLp.smul_apply]
      ring_nf

@[simp]
lemma smul_fst (g : GalileanGroup d) (tx : Time × Space d) :
    (g • tx).1 = tx.1 + g.timeTranslation := rfl

@[simp]
lemma smul_snd (g : GalileanGroup d) (tx : Time × Space d) :
    (g • tx).2 = g.actSpace tx.1 tx.2 := rfl

@[simp]
lemma smul_mk (g : GalileanGroup d) (t : Time) (x : Space d) :
    g • ((t, x) : Time × Space d) = (t + g.timeTranslation, g.actSpace t x) := rfl

@[simp]
lemma actSpace_apply (g : GalileanGroup d) (t : Time) (x : Space d) (i : Fin d) :
    g.actSpace t x i =
      (g.rotation • (x -ᵥ (0 : Space d))) i + t.val * g.velocity i + g.spaceTranslation i := by
  simp [actSpace, Space.vectorToSpace, add_assoc]

/-! ## D. Subgroup inclusions -/

/-- A Euclidean spatial transformation as a Galilean transformation with zero boost and no time
translation. -/
def ofEuclidean (g : EuclideanGroup d) : GalileanGroup d :=
  ⟨g.linear, 0, g.translation, 0⟩

@[simp]
lemma ofEuclidean_rotation (g : EuclideanGroup d) :
    (ofEuclidean g).rotation = g.linear := rfl

@[simp]
lemma ofEuclidean_velocity (g : EuclideanGroup d) :
    (ofEuclidean g).velocity = 0 := rfl

@[simp]
lemma ofEuclidean_spaceTranslation (g : EuclideanGroup d) :
    (ofEuclidean g).spaceTranslation = g.translation := rfl

@[simp]
lemma ofEuclidean_timeTranslation (g : EuclideanGroup d) :
    (ofEuclidean g).timeTranslation = 0 := rfl

/-- Inclusion of the Euclidean group into the Galilean group. -/
def euclidean.incl : EuclideanGroup d →* GalileanGroup d where
  toFun := ofEuclidean
  map_one' := rfl
  map_mul' g h := by
    ext i <;> simp [ofEuclidean]

/-- A pure orthogonal spatial transformation as a Galilean transformation. -/
def ofOrthogonal (R : Matrix.orthogonalGroup (Fin d) ℝ) : GalileanGroup d :=
  ⟨R, 0, 0, 0⟩

@[simp]
lemma ofOrthogonal_rotation (R : Matrix.orthogonalGroup (Fin d) ℝ) :
    (ofOrthogonal R).rotation = R := rfl

@[simp]
lemma ofOrthogonal_velocity (R : Matrix.orthogonalGroup (Fin d) ℝ) :
    (ofOrthogonal R).velocity = 0 := rfl

@[simp]
lemma ofOrthogonal_spaceTranslation (R : Matrix.orthogonalGroup (Fin d) ℝ) :
    (ofOrthogonal R).spaceTranslation = 0 := rfl

@[simp]
lemma ofOrthogonal_timeTranslation (R : Matrix.orthogonalGroup (Fin d) ℝ) :
    (ofOrthogonal R).timeTranslation = 0 := rfl

/-- Inclusion of the orthogonal group into the Galilean group. -/
def orthogonal.incl : Matrix.orthogonalGroup (Fin d) ℝ →* GalileanGroup d where
  toFun := ofOrthogonal
  map_one' := rfl
  map_mul' R S := by
    ext i <;> simp [ofOrthogonal]

/-- Inclusion of the existing spatial rotation subgroup into the Galilean group. -/
noncomputable def rotation.incl : EuclideanGroup.RotationGroup d →* GalileanGroup d where
  toFun r := ofOrthogonal (r : EuclideanGroup d).linear
  map_one' := rfl
  map_mul' r s := by
    ext i <;> simp [ofOrthogonal]

/-- A pure spatial translation as a Galilean transformation. -/
def ofSpaceTranslation (a : EuclideanSpace ℝ (Fin d)) : GalileanGroup d :=
  ⟨1, 0, a, 0⟩

@[simp]
lemma ofSpaceTranslation_rotation (a : EuclideanSpace ℝ (Fin d)) :
    (ofSpaceTranslation a).rotation = 1 := rfl

@[simp]
lemma ofSpaceTranslation_velocity (a : EuclideanSpace ℝ (Fin d)) :
    (ofSpaceTranslation a).velocity = 0 := rfl

@[simp]
lemma ofSpaceTranslation_spaceTranslation (a : EuclideanSpace ℝ (Fin d)) :
    (ofSpaceTranslation a).spaceTranslation = a := rfl

@[simp]
lemma ofSpaceTranslation_timeTranslation (a : EuclideanSpace ℝ (Fin d)) :
    (ofSpaceTranslation a).timeTranslation = 0 := rfl

/-- Inclusion of spatial translations into the Galilean group. -/
def spaceTranslation.incl :
    Multiplicative (EuclideanSpace ℝ (Fin d)) →* GalileanGroup d where
  toFun a := ofSpaceTranslation a.toAdd
  map_one' := rfl
  map_mul' a b := by
    ext i <;> simp [ofSpaceTranslation]

/-- Inclusion of the existing spatial translation subgroup into the Galilean group. -/
noncomputable def spaceTranslationGroup.incl :
    EuclideanGroup.TranslationGroup d →* GalileanGroup d :=
  euclidean.incl.comp (EuclideanGroup.TranslationGroup.incl d)

/-- A pure time translation as a Galilean transformation. -/
def ofTimeTranslation (b : Time) : GalileanGroup d :=
  ⟨1, 0, 0, b⟩

@[simp]
lemma ofTimeTranslation_rotation (b : Time) :
    (ofTimeTranslation (d := d) b).rotation = 1 := rfl

@[simp]
lemma ofTimeTranslation_velocity (b : Time) :
    (ofTimeTranslation (d := d) b).velocity = 0 := rfl

@[simp]
lemma ofTimeTranslation_spaceTranslation (b : Time) :
    (ofTimeTranslation (d := d) b).spaceTranslation = 0 := rfl

@[simp]
lemma ofTimeTranslation_timeTranslation (b : Time) :
    (ofTimeTranslation (d := d) b).timeTranslation = b := rfl

/-- Inclusion of time translations into the Galilean group. -/
def timeTranslation.incl : Multiplicative Time →* GalileanGroup d where
  toFun b := ofTimeTranslation b.toAdd
  map_one' := rfl
  map_mul' a b := by
    ext i <;> simp [ofTimeTranslation]

end GalileanGroup
