/-
Copyright (c) 2026 Nikolai Kashcheev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nikolai Kashcheev
-/
module

public import Mathlib.Topology.Instances.Matrix

/-!
# Countable bases for matrix spaces

Second countability of matrices with their coordinate topology.

## i. Overview

A matrix space with countably many entries inherits second countability
from its scalar space. This supplies the ambient topological instance for
matrix groups and their coordinate subspaces.

## ii. Key results

* `Matrix.instSecondCountableTopology`: second countability of matrix spaces.

## iii. Table of contents

- A. The coordinate topology

## iv. References

* None.
-/

public section

namespace Matrix

/-!
## A. The coordinate topology
-/

/-- Matrices with countably many entries over a second-countable space are second-countable. -/
instance instSecondCountableTopology {m n R : Type*} [Countable m] [Countable n]
    [TopologicalSpace R] [SecondCountableTopology R] :
    SecondCountableTopology (Matrix m n R) :=
  inferInstanceAs (SecondCountableTopology (m → n → R))

end Matrix
