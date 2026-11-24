/-
Copyright (c) 2026 Christian Thierfelder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Thierfelder
-/
module

public import Physlib.SpaceAndTime.Time.Basic
/-!

# The Present Time

The present cosmic time `t₀`, the instant at which present-day values of cosmological quantities,
such as the Hubble constant `H₀`, are taken.

## i. Overview

`Time` is a torsor over `ℝ`: it carries a unit and an orientation but no distinguished instant. The
present is therefore not a feature of `Time` but a datum of the cosmological model, in the way the
speed of light `SpeedOfLight` is a datum of the system of units rather than a fixed number.

`TimeNow` records a chosen instant as the present. A present-day quantity such as the Hubble
constant `H₀ = H(t₀)` then takes a `TimeNow` rather than a free `Time`, so that its type says it is
the value today and not the value at an arbitrary instant.

## ii. Key results

- `TimeNow` : A chosen instant of `Time` taken to be the present.

## iii. Table of contents

- A. The type
- B. Instances

## iv. References

* None.

-/

@[expose] public section

namespace Cosmology

/-!

## A. The type

-/

/-- A chosen instant of `Time` taken to be the present, `t₀`. -/
structure TimeNow where
  /-- The instant of the present. -/
  val : Time

namespace TimeNow

/-!

## B. Instances

-/

instance : Coe TimeNow Time := ⟨TimeNow.val⟩

instance : Nonempty TimeNow := ⟨⟨⟨0⟩⟩⟩

end TimeNow

end Cosmology
