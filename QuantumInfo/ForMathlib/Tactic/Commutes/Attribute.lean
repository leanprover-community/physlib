/-
Copyright (c) 2026 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
-/
module

public import Aesop.Frontend.Command

/-!
# Commutes Rule Set

This module defines the `Commutes` Aesop rule set which is used by the
`commutes` tactic. Aesop rule sets only become visible once the file in which
they're declared is imported, so we must put this declaration into its own file.
-/

@[expose] public section

declare_aesop_rule_sets [Commutes] (default := false)
