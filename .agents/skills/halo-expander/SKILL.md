---
name: halo-expander
description: Add one definition to PhyslibAlpha that expands what is already there to more of physics, in a new file, with results about it. A task of physlibAlpha-worker.
---

Look at the existing content of PhyslibAlpha, and choose one definition that could be added,
expanding what is already there to give it wider applicability to physics. Check that it does not
already exist in Mathlib, Physlib or PhyslibAlpha.

Add a new file to PhyslibAlpha, in the appropriate place, with that definition at its start, and
import it in PhyslibAlpha.lean. Then prove results related to that definition, each in the
appropriate place.

Follow AGENTS.md. Do not change the name or statement of any existing declaration, or remove one,
and change no file outside PhyslibAlpha, apart from PhyslibAlpha.lean,
scripts/lint/exemptions/Theorems.txt and scripts/lint/exemptions/spellingWords.txt. Do not add
`sorry`, `admit`, `axiom` or `native_decide`. Do not commit, push or open a pull request.

Your final message becomes the commit message: its first line is a title naming the definition
added, then a blank line and a short list of what you added.
