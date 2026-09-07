# How to write and work through TODO items

A `TODO "…"` command records a note about the module it appears in. It can carry the
range of lines the note is about, written `TODO (lines := 379-430) "…"`, which is what
makes a note point at a block of code rather than at wherever the note happens to sit.

The command itself is documented in `Physlib/Meta/TODO/Basic.lean`. This file is about
the editor and command-line side: how to write one without typing it out, how to list
what is outstanding, and how to hand the outstanding items to Claude.

## Writing one from VS Code

Select the lines the note is about and run the task **`Physlib: TODO about selection`**
from the command palette (`cmd + shift + p`, then "Tasks: Run Task").

## Listing what is outstanding

```
python3 scripts/todos.py                    # to the terminal
python3 scripts/todos.py --md todos.md      # regenerate the committed list
python3 scripts/todos.py --head some-branch # read a ref instead of the working tree
```

This lists the TODO items **this branch introduces**, by scanning the working tree and
the merge-base with the same matcher and subtracting the sets, so a note that was
already on `master` is not reported and moving one around is not churn. Each entry shows
the range of code it is about, and where the note itself sits when that differs:

```
IsSU3BiAdjoint.lean:379-430 (at 431)     Fix the errors within these lemmas.
```

Regenerate `todos.md` and commit it in the same commit that adds or resolves a TODO.

## Handing the outstanding items to Claude

Set it as a session goal with `/goal`, so Claude keeps working until they are all done
and keeps checking back for ones added in the meantime:

```
/goal There are a number of TODO items added in this branch. The outstanding ones can
be found from: python3.12 ./scripts/todos.py — run this script to find the TODO items.
Here we only care about those with explicit line ranges, for example 66-164.

These TODO items correspond to tasks. Do these tasks.
- Where possible do them in parallel with different runners.
- Use the fastest model possible which will do the tasks effectively.
- Once done, delete the corresponding TODO item from the code.
I will add more TODO items, so you should periodically check for new tasks to do.
```

Two things make this work in practice. Restricting it to items with explicit line ranges
picks out the ones that name a concrete block of code, which are the ones specific enough
to act on. And because the notes are attached to line ranges rather than to positions in
a list, you can keep adding them while Claude works: new ones are picked up on the next
run of the script.

One caveat: parallel runners must not be given the same file. Two agents editing one file
will clobber each other, so the work is split one runner per file, and tasks that touch a
shared destination are done in sequence afterwards.
