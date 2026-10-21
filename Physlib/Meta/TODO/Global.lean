/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Meta.TODO.Basic
/-!

# Global TODO items

This module contains global TODO items, which are not specific to any particular module,
but are still important for the development of Physlib.

-/

@[expose] public section

TODO "Ensure that all the lines in QuantumInfo are below 100 characters long."

TODO "Remove all instances of `erw` within Physlib. This usually
  indicates the need for better API."

TODO "Refactor: Refactor the code in the QuantumInfo module to mirror the API structure
  of the rest of Physlib. For example, different key data structures should have their own files
  or directories. Results should be organized in a general way such that they can be applied more
  generally."
