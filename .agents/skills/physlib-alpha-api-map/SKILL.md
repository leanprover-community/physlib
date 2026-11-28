---
name: physlib-alpha-api-map
description: Help a newcomer with expertise in an area of physics write a new API map for that area, or improve an existing one, through a conversation that ends in a reviewable diff and a short summary of what changed. Use it only when someone says they want to write or improve an API map.
---

# Write or improve an API map

Help a newcomer who has expertise in an area of physics write an API map for that area, or improve the map that already exists. They start by naming an area of physics. At the end they get a complete diff to review and a short summary of what has been done.

## Ground rules

- Work as a conversation. As you go through each step, show the newcomer what has changed and ask whether it looks good or whether there is anything they would change.
- Keep everything on the newcomer's machine. Do not push, open a PR or post anything. The newcomer writes the PR description.
- Do not build Physlib or download the full cache.
- Do not change dependency versions to get around an error.

## Step 1: Choose the topic

Find a topic that corresponds to something coherent within the project and suits an API map.

A topic suits a map if it has a key data structure: you could imagine writing a structure and then writing definitions and lemmas about it.

If the area is broad, look for those key data structures and suggest a few topics for the newcomer to choose from. If there is already code for the area, in Physlib or in PhyslibAlpha, the file directories should indicate this structure, and topics tend to be data structures rather than definitions. If there is no code yet, think carefully about possible options, and give the newcomer examples from areas already in Physlib, such as the electromagnetic potential for electromagnetism.

Then search the repository for an existing map on the topic. You do not need to check open PRs. If a map exists, improve it. If not, write a new one.

## Step 2: Frame the map

Settle the key data structure and the important results the map should include.

The data structure should already be determined by this point. If there is Lean code in the area, tell the newcomer what is there and what would fit this map. If the area is completely new, ask the newcomer which results are important, then suggest more, along the lines of "if we have this, we may also want this".

## Step 3: Write the abstract

Write an abstract that gives a reader an overview of the area.

Ask the newcomer for a two-sentence summary of the area in purely physics terms: what the core definition is, where it leads, and why it is important. Turn that into something more like an abstract. Check that it makes sense, is easy to read and gives an overview of the area.

## Step 4: Lay out the structure

Agree the sections of the map with the newcomer.

Follow `docs/API_MAP_GUIDE.md`. Start with the definition of the key data structure, then cover what you can do with it, the questions you can ask, and the definitions built from it. Be guided by what the newcomer thinks is important in this area: suggest directions and a structure that might work, and let the newcomer confirm it or say no.

## Step 5: Check completeness and readability

Make sure the map has everything you want in it, and that it is readable and coherent.

Check it against the important results agreed in Step 2. Ask the newcomer whether it makes sense, and get them to confirm that it works.

## Step 6: Add references

Include the important references for this area.

Ask the newcomer whether there are important references in this area that should be mentioned and cited. The newcomer must supply them. Format them and put them in the right place in the map.

## Step 7: Match to the Lean declarations

Check that the map matches the Lean code.

For each result in the map, do a quick check and say yes or no: does it match its declaration? Mark any result not yet in the Lean code with the square-bracket `[TODO]` marker from `docs/API_MAP_GUIDE.md`, as existing maps do.

## Step 8: Run the final checks

Make sure the map is within the style. Run the API map linter:

```bash
lake exe api_map_lint --verbose
```

Fix any problems it reports.

## Step 9: Hand back the diff

Show the newcomer the complete diff and a very short summary of what has been done, something quick to read. The newcomer reviews it and writes the PR description.
