#!/usr/bin/env python3
"""Insert a `TODO` command below a line or a range of lines of a Lean file.

The `TODO` command is a top-level Lean command, so it cannot be dropped just anywhere:
placing it inside a term, a tactic block, a docstring or a `/- -/` comment is a parse
error.  This script finds the nearest safe top-level position below the target and puts
the command there, so an editor can offer "add a TODO about this block" on a selection.

The command goes below the target rather than above it so that the lines it names stay
where they are: the `(lines := ...)` clause counts lines of the file the command is
written into, and inserting above the target would push the target down.

Usage:

    python scripts/insert_todo.py FILE START [END] [--text "..."]

`START` and `END` are 1-indexed line numbers of the code the note is about; `END`
defaults to `START`.  A blank line, or a pair of them, is a place in the file rather than
a piece of code, so a note taken there is written without a `(lines := ...)` clause and
refers to where it sits.  With no `--text` an empty string is inserted, ready to type
into.  The point between the quotes of the note is printed on stdout as `LINE:COLUMN`,
and with `--goto` the cursor of the running editor is put there.
"""

from __future__ import annotations

import argparse
import os
import re
import sys

# A top-level command starts in column zero with one of these.  Attributes and
# docstrings are top-level too: they begin the declaration they attach to, so a command
# may be inserted above them but not below them.
DECL_START = re.compile(
    r"^(@\[|/--|/-!|private\b|protected\b|noncomputable\b|partial\b|unsafe\b|meta\b"
    r"|public\b|def\b|abbrev\b|lemma\b|theorem\b|example\b|instance\b|structure\b"
    r"|class\b|inductive\b|namespace\b|section\b|end\b|open\b|variable\b|universe\b"
    r"|set_option\b|attribute\b|macro\b|syntax\b|notation\b|scoped\b|TODO\b)"
)

# The header of a Lean file.  Imports come before every command, so a `TODO` may not be
# inserted among them however close to the target they are.
HEADER = re.compile(r"^(module\b|prelude\b|((public|meta)\s+)*import\b)")


def block_comments(lines: list[str]) -> tuple[set[int], set[int]]:
    """The 0-indexed lines that sit inside a `/- ... -/` block, and the lines on which a
    `/-- ... -/` docstring closes.  A docstring attaches to the declaration below it,
    whereas a `/- -/` comment or a `/-! -/` module docstring stands on its own."""
    inside: set[int] = set()
    doc_ends: set[int] = set()
    depth = 0
    doc = False
    for i, line in enumerate(lines):
        if depth > 0:
            inside.add(i)
        else:
            opener = line.find("/-")
            doc = opener != -1 and line.startswith("/--", opener)
        closes = line.count("-/")
        was, depth = depth, max(0, depth + line.count("/-") - closes)
        if doc and depth == 0 and (was > 0 or closes):
            doc_ends.add(i)
    return inside, doc_ends


def attaches_below(line: str, is_doc_end: bool) -> bool:
    """Whether a line belongs to the declaration beneath it, so that nothing may be
    inserted between the two: a docstring, an attribute, or a `... in` prefix."""
    stripped = line.strip()
    return is_doc_end or stripped.startswith("@[") or stripped.endswith(" in")


def first_command_line(lines: list[str], inside: set[int]) -> int:
    """The 0-indexed line before which no command may go, that is, the line after the
    last `import` of the file."""
    last = -1
    for i, line in enumerate(lines):
        if i in inside or not line.strip() or line.lstrip().startswith(("--", "/-")):
            continue
        if not HEADER.match(line):
            break
        last = i
    return last + 1


def safe_insertion_line(lines: list[str], target: int) -> int:
    """A 0-indexed line below `target` (0-indexed) at which a command may be inserted.

    Walks down from the target to the first line that begins a top-level command,
    refusing to stop among the imports, inside a block comment, or below an attribute or
    docstring that attaches to the command found.  The end of the file is always safe.
    """
    inside, doc_ends = block_comments(lines)
    for i in range(max(target + 1, first_command_line(lines, inside)), len(lines)):
        if i in inside or not DECL_START.match(lines[i]):
            continue
        j = i - 1
        while j >= 0 and not lines[j].strip():
            j -= 1
        if j < 0 or not attaches_below(lines[j], j in doc_ends):
            return i
    return len(lines)


def names_lines(lines: list[str], start: int, end: int) -> bool:
    """Whether a note about lines `start` to `end` (1-indexed) should say so.

    One or two blank lines are a gap between declarations rather than any code, so a
    note taken there is about the place and not about what is written on it.  Naming
    those lines would only pin the note to nothing; without a `(lines := ...)` clause it
    refers to the line the command is on, which is exactly that place.
    """
    if end - start > 1:
        return True
    return any(lines[i - 1].strip() for i in range(start, end + 1))


def render(start: int | None, end: int, text: str) -> str:
    """The `TODO` command for a line or a range of lines, or, when `start` is `None`,
    one that names no lines at all."""
    escaped = text.replace("\\", "\\\\").replace('"', '\\"')
    if start is None:
        return f'TODO "{escaped}"\n'
    if end > start:
        return f'TODO (lines := {start}-{end}) "{escaped}"\n'
    return f'TODO (lines := {start}) "{escaped}"\n'


def goto(path: str, line: int, column: int, settle: float) -> None:
    """Put the cursor at `line`, `column` of `path` in the running editor.

    The `vscode://` URL is handed straight to the window that is already open, which
    costs a few tens of milliseconds.  The `code` command would do the same thing by
    starting a second copy of VS Code's command line interface, which on this machine
    takes the better part of a second, most of the time this script spends.

    The pause first is not politeness: VS Code has to notice that the file changed on
    disk and reload it, and a cursor placed before that lands in the old text and is
    then dragged along by the insertion.  `--settle-ms` tunes it.
    """
    import subprocess
    import time
    from urllib.parse import quote

    time.sleep(settle)
    url = f"vscode://file{quote(os.path.abspath(path))}:{line}:{column}"
    opener = ["open", "-g", url] if sys.platform == "darwin" else ["xdg-open", url]
    try:
        failed = subprocess.run(opener, check=False).returncode != 0
    except OSError:
        failed = True
    if failed:
        print(f"could not open {url}, cursor not moved", file=sys.stderr)


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("file")
    ap.add_argument("start", type=int, help="first line the note is about (1-indexed)")
    ap.add_argument("end", type=int, nargs="?", help="last line (defaults to start)")
    ap.add_argument("--text", default="", help="the note itself")
    ap.add_argument(
        "--from-selection",
        action="store_true",
        help="read the editor selection from PHYSLIB_TODO_SELECTION and treat `start` "
        "as the line the cursor is on, so that the range covers the whole selection",
    )
    ap.add_argument(
        "--goto",
        action="store_true",
        help="put the cursor of the running editor between the quotes of the note",
    )
    ap.add_argument(
        "--settle-ms",
        type=int,
        default=120,
        help="with `--goto`, how long to let VS Code reload the file before the cursor "
        "is moved into it (default 120)",
    )
    ap.add_argument(
        "--dry-run", action="store_true", help="print the result instead of writing"
    )
    args = ap.parse_args()

    start = args.start
    end = args.end if args.end is not None else start

    if args.from_selection:
        # An editor gives the cursor line, which sits at one end of the selection, and
        # the selected text, whose line count gives the other end.
        selection = os.environ.get("PHYSLIB_TODO_SELECTION", "")
        span = selection.count("\n") if selection else 0
        end = args.start
        start = max(1, args.start - span)
    if end < start:
        start, end = end, start

    with open(args.file, encoding="utf-8") as fh:
        lines = fh.readlines()
    if not 1 <= start <= len(lines):
        print(f"{args.file}: line {start} is out of range", file=sys.stderr)
        return 1
    end = min(end, len(lines))
    if lines and not lines[-1].endswith("\n"):
        lines[-1] += "\n"

    at = safe_insertion_line(lines, end - 1)
    command = render(start if names_lines(lines, start, end) else None, end, args.text)
    # Keep the note a paragraph of its own, without doubling a blank line already there.
    before = ["\n"] if at > 0 and lines[at - 1].strip() else []
    after = ["\n"] if at < len(lines) and lines[at].strip() else []

    new = lines[:at] + before + [command] + after + lines[at:]
    if args.dry_run:
        sys.stdout.writelines(new)
        return 0

    with open(args.file, "w", encoding="utf-8") as fh:
        fh.writelines(new)

    # The cursor belongs between the quotes, after any text already written there.
    line = at + len(before) + 1
    column = command.rindex('"') + 1
    print(f"{line}:{column}")
    if args.goto:
        goto(args.file, line, column, args.settle_ms / 1000)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
