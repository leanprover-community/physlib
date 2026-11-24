# Write your first API map

[Issue #1891](https://github.com/leanprover-community/physlib/issues/1891) invites
physicists to write or improve API maps. A map explains a topic and links each
formalized claim to the corresponding Lean declarations. You can draft and check
the map locally before signing in to GitHub.

1. **Pick one topic you know.** Use the [API tracker](https://physlib.io/api-tracker)
   to find an existing map to improve or a small API without a map.
   Look for related maps and open pull requests before starting.
   For example, you could document how the rectangular barrier API defines
   [probability current](../../PhyslibAlpha/QuantumMechanics/RectangularBarrier/ProbabilityCurrent.lean)
   and the assumptions under which it is constant.
2. **Draft the map in a checkout.** Clone the public repository and open that
   directory in your editor or coding agent.

   ```sh
   git clone https://github.com/leanprover-community/physlib.git
   cd physlib
   git switch -c first-api-map
   ```

   Read the [API-map guide](../API_MAP_GUIDE.md) for the file format, including
   the Alpha headings for a map that has not undergone full review. Put a
   new `API-map.md` in the directory for the API it describes. The
   [canonical ensemble map](../../Physlib/StatisticalMechanics/CanonicalEnsemble/API-map.md)
   shows how the prose and references fit together.

   If you are using a coding agent, give it this request and substitute a
   topic you know:

   > Read `.agents/skills/physlib-alpha-api-map/SKILL.md`. I know classical
   > mechanics and am new to Lean. Help me make one focused API-map
   > contribution for #1891. Inspect the cited Lean statements, edit the
   > map, run the checks, and show me the diff for review.

3. **Check locally.** Install Lean using the [getting-started guide](https://physlib.io/getting-started),
   then run the map linter from the repository root:

   ```sh
   lake exe api_map_lint --verbose
   ```

   Check that the prose matches the assumptions and conclusions of the Lean
   statements. Verify the bibliography yourself and read the [AI policy](../../AI-POLICY.md)
   if you used AI assistance.
4. **Review and send it to your fork.** From the repository root, replace
   `path/to/API-map.md` with your map's actual path. Review the staged diff
   before committing. It shows new files as well as edits to existing maps.

   ```sh
   git status --short
   git add -- path/to/API-map.md
   git diff --cached
   git commit -m "docs: add API map for <topic>"
   ```

   If you use the GitHub CLI with HTTPS, this sequence signs you in, connects
   Git to those credentials, and adds a remote named `fork`. The
   original public clone remains your `origin`.

   ```sh
   gh auth login --hostname github.com --git-protocol https --web
   gh auth status --hostname github.com
   gh auth setup-git --hostname github.com
   gh repo fork --remote --remote-name fork
   git remote get-url fork
   ```

   If the CLI does not add a remote for your existing fork, add it with
   `git remote add fork https://github.com/<your-username>/physlib.git`.
   Check that `git remote get-url fork` points to your account, then push.

   ```sh
   git push -u fork first-api-map
   ```

   Open a pull request against PhysLib and describe the change in your own
   words. See GitHub's [authentication guide](https://docs.github.com/en/authentication/keeping-your-account-and-data-secure/about-authentication-to-github)
   if sign-in fails. Your draft and commit are already on your machine.
