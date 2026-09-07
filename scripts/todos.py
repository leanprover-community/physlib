#!/usr/bin/env python3
"""
todos.py -- list the TODOs this branch introduces, relative to its merge-base.

Scans the working tree and the merge-base with the same matcher and subtracts
the sets, so the output is "what this PR adds", not "every TODO in Physlib".
The default scans the working tree, so uncommitted edits are visible and the
file can be regenerated in the same commit that changes a TODO.

Pass --head to read another ref instead, straight out of the object store: no
checkout, no branch switching, working tree untouched.

  python scripts/todos.py                          # to the terminal
  python scripts/todos.py --md todos.md
  python scripts/todos.py --head joseph/AddPotentialAlgebra
"""

import argparse
import os
import re
import subprocess
import sys
import textwrap
from typing import NamedTuple

DEFAULT_MASTER = "upstream/master"
DEFAULT_ROOT = "Physlib"

# Physlib/Meta/TODO/ implements the TODO command; it is *about* todos and would
# otherwise dominate the output. scripts/ likewise. QuantumInfo/ is a separate
# subproject with its own `--TODO` convention and is out of scope.
EXCLUDE = re.compile(r"(^|/)(Meta|scripts)/")

# TODO "..." and TODO (lines := 82) "..." / TODO (lines := 201-223) "..."  (Lean command)
CMD_START = re.compile(
    r'^\s*TODO\s*(?:\(\s*lines\s*:=\s*(\d+)\s*(?:-\s*(\d+)\s*)?\)\s*)?"'
)
DOC_LINE = re.compile(r"^\s*/-!\s*TODO:\s*")     # /-! TODO: ... -/
LOOSE = re.compile(r"todo", re.I)

# Matches `todo` but is not a work item: section headings, and identifiers that
# merely contain the word.
NOISE = re.compile(
    r"(^\s*#{1,6}\s*TODO\b)"          # '## TODO' section heading
    r"|(Physlib\.Meta\.TODO)"
    r"|(TODO_to_yml|FullTODO|todoExtension|todoInfo|allTODO)"
    # Prose *about* todos, mostly in module docstrings, not work items.
    r"|(collecting TODO items)|(contains only TODO items)"
    r"|(is a TODO to)|(Open TODO items)|(see the `TODO`)",
    re.I,
)


class Todo(NamedTuple):
    """One TODO item: the code it is about, and where the note itself is written.

    `line` and `endline` are the range given by a `(lines := ...)` clause, or the
    line the note is written on when it carries no clause. `at` is always the line
    the note itself is on: since `scripts/insert_todo.py` writes a note *below* the
    code it is about, the two are usually different.
    """

    path: str
    line: int
    endline: int
    kind: str
    content: str
    at: int

    def lines(self):
        """The range of code, as it is written in a `(lines := ...)` clause."""
        return f"{self.line}-{self.endline}" if self.endline > self.line else f"{self.line}"

    def label(self, name):
        """`name` and the code range, saying where the note is when that differs."""
        return f"{name}:{self.lines()}" + (f" (at {self.at})" if self.at != self.line else "")


def git(repo, *args):
    out = subprocess.run(["git", "-C", repo, *args], capture_output=True, check=True)
    return out.stdout.decode("utf-8", "replace")


def list_files(repo, ref, root):
    paths = git(repo, "ls-tree", "-r", "--name-only", ref, "--", root).splitlines()
    return [p for p in paths if p.endswith(".lean") and not EXCLUDE.search(p)]


def read_blobs(repo, ref, paths):
    """Bulk-read many blobs in one subprocess. Returns {path: text}."""
    proc = subprocess.Popen(
        ["git", "-C", repo, "cat-file", "--batch"],
        stdin=subprocess.PIPE, stdout=subprocess.PIPE,
    )
    out, _ = proc.communicate("".join(f"{ref}:{p}\n" for p in paths).encode())

    blobs, pos = {}, 0
    for path in paths:
        nl = out.find(b"\n", pos)
        if nl == -1:
            break
        header = out[pos:nl].decode("utf-8", "replace")
        pos = nl + 1
        if header.endswith(("missing", "ambiguous")):
            continue
        size = int(header.rsplit(" ", 1)[1])
        blobs[path] = out[pos:pos + size].decode("utf-8", "replace")
        pos += size + 1  # trailing newline after the blob
    return blobs


def parse_file(path, text):
    """Yield (path, line, endline, kind, content) items, coalescing wrapped ones.

    `line`/`endline` are the lines of code the item is about: the range given by a
    `(lines := ...)` clause, or the line the item is written on when it has none.
    """
    lines = text.splitlines()
    items, unclassified = [], []
    i = 0
    while i < len(lines):
        line = lines[i]

        # --- TODO "..." command; the string may span several lines -----------
        cmd = CMD_START.match(line)
        if cmd:
            start = i
            first = int(cmd.group(1)) if cmd.group(1) else start + 1
            last = int(cmd.group(2)) if cmd.group(2) else first
            body = line[line.index('"') + 1:]
            while '"' not in body.replace('\\"', ""):
                i += 1
                if i >= len(lines):
                    break
                body += " " + lines[i].strip()
            if '"' in body:
                body = body[:body.rindex('"')]
            items.append(Todo(path, first, last, "cmd",
                               " ".join(body.split()), start + 1))
            i += 1
            continue

        # --- /-! TODO: ... -/ runs; capitalised first word starts a new item --
        if DOC_LINE.match(line):
            start = i
            body = DOC_LINE.sub("", line).replace("-/", "").strip()
            while i + 1 < len(lines) and DOC_LINE.match(lines[i + 1]):
                nxt = DOC_LINE.sub("", lines[i + 1]).replace("-/", "").strip()
                first = nxt.split(" ", 1)[0] if nxt else ""
                if first[:1].isupper():   # heuristic: new sentence, new item
                    break
                body += " " + nxt
                i += 1
            items.append(Todo(path, start + 1, start + 1, "doc",
                               " ".join(body.split()), start + 1))
            i += 1
            continue

        if LOOSE.search(line) and not NOISE.search(line):
            unclassified.append(Todo(path, i + 1, i + 1, "?", line.strip(), i + 1))
        i += 1

    return items, unclassified


def list_files_worktree(repo, root):
    """Tracked files, plus new ones not yet added to the index.

    A file that has just been written is exactly where a fresh TODO is most likely to
    be, and `git ls-files` alone lists only what is tracked, so a note in a new file
    would be reported by no run of this script until someone remembered to `git add` it.
    """
    tracked = git(repo, "ls-files", "--", root).splitlines()
    new = git(repo, "ls-files", "--others", "--exclude-standard", "--", root).splitlines()
    paths = sorted(set(tracked) | set(new))
    return [p for p in paths if p.endswith(".lean") and not EXCLUDE.search(p)]


def read_worktree(repo, paths):
    blobs = {}
    for path in paths:
        try:
            with open(os.path.join(repo, path), encoding="utf-8") as fh:
                blobs[path] = fh.read()
        except OSError:
            continue
    return blobs


def scan(repo, ref, root):
    """ref=None scans the working tree, so uncommitted edits are visible."""
    if ref is None:
        paths = list_files_worktree(repo, root)
        blobs = read_worktree(repo, paths)
    else:
        paths = list_files(repo, ref, root)
        blobs = read_blobs(repo, ref, paths)

    items, unknown = [], []
    for path, text in blobs.items():
        a, b = parse_file(path, text)
        items += a
        unknown += b
    return items, unknown, len(paths)


def key(content):
    """Identity of a TODO: its text, path-independent so moves aren't churn."""
    return " ".join(content.lower().split()).rstrip(".")


def group_by_dir(items):
    by_dir = {}
    for todo in sorted(items):
        by_dir.setdefault(todo.path.rsplit("/", 1)[0], []).append(todo)
    return by_dir


def emit_terminal(items, unknown, meta, plain):
    print("# TODOs introduced by this branch")
    print(f"# base {meta['base'][:8]} -> head {meta['head'][:8]}  ({meta['date']})")
    print(f"# {meta['files']} files - {len(items)} new\n")

    for directory, group in sorted(group_by_dir(items).items()):
        if plain:
            for todo in group:
                print(f"{todo.path} | {todo.content}")
            continue
        print(directory.replace("Physlib/", ""))
        for todo in group:
            label = todo.label(todo.path.rsplit("/", 1)[1])
            head, *rest = textwrap.wrap(todo.content, 56) or [""]
            print(f"  {label:<40} {head}")
            for cont in rest:
                print(f"  {'':<40} {cont}")
        print()

    if unknown:
        print(f"UNCLASSIFIED ({len(unknown)}) - new here, matched /todo/i, no known form:")
        for todo in sorted(unknown):
            print(f"  {todo.path}:{todo.line}  {todo.content[:70]}")


def md_escape(text):
    """Brackets would terminate the link text early."""
    return text.replace("[", "\\[").replace("]", "\\]")


def emit_md(items, meta, repo_url, link_ref):
    out = [
        "# TODOs introduced by this branch",
        "",
        f"{len(items)} open &middot; as of {meta['date']}",
        "",
        "> Regenerate with `python scripts/todos.py --md todos.md` after adding or",
        "> resolving a TODO, and commit it in the same commit.",
        "",
        '**Format.** Use the `TODO "…"` command',
        "",
    ]
    for directory, group in sorted(group_by_dir(items).items()):
        out += [f"### `{directory.replace('Physlib/', '')}`", ""]
        for todo in group:
            name = todo.path.rsplit("/", 1)[1]
            anchor = f"L{todo.line}-L{todo.endline}" if todo.endline > todo.line \
                else f"L{todo.line}"
            link = f"{repo_url}/blob/{link_ref}/{todo.path}"
            row = (f"- {md_escape(todo.content)} "
                   f"&nbsp;[`{name}:{todo.lines()}`]({link}#{anchor})")
            if todo.at != todo.line:   # where to go to edit the note itself
                row += f" &nbsp;[`@{todo.at}`]({link}#L{todo.at})"
            out.append(row)
        out.append("")

    return "\n".join(out)


def main():
    # Lean sources are full of ℂ, ℝ, ψ; the Windows console defaults to cp1252.
    sys.stdout.reconfigure(encoding="utf-8", errors="replace")

    ap = argparse.ArgumentParser()
    ap.add_argument("--repo", default=".")
    ap.add_argument("--head", default=None, help="defaults to the working tree")
    ap.add_argument("--base", default=None, help="defaults to merge-base with master")
    ap.add_argument("--master", default=DEFAULT_MASTER)
    ap.add_argument("--root", default=DEFAULT_ROOT)
    ap.add_argument("--plain", action="store_true", help="no line numbers; diff-friendly")
    ap.add_argument("--md")
    ap.add_argument("--repo-url", default="https://github.com/jstoobysmith/JTSphyslib")
    # Link against the branch, not the head SHA: a SHA in every URL would rewrite
    # every line of todos.md on each push, even when no TODO changed.
    ap.add_argument("--link-ref", default="AddPotentialAlgebra")
    args = ap.parse_args()

    head_sha = git(args.repo, "rev-parse", args.head or "HEAD").strip()
    date = git(args.repo, "log", "-1", "--format=%ad", "--date=short",
               args.head or "HEAD").strip()
    base = args.base or git(args.repo, "merge-base", args.master,
                            args.head or "HEAD").strip()

    items, unknown, nfiles = scan(args.repo, args.head, args.root)
    base_items, base_unknown, _ = scan(args.repo, base, args.root)

    base_keys = {key(todo.content) for todo in base_items}
    items = [todo for todo in items if key(todo.content) not in base_keys]

    # The unclassified lines are subtracted too, so that section only ever reports a
    # loose TODO this branch itself introduced. A loose line counts as pre-existing if
    # its wording is anywhere at the merge-base, in either form: a stray `-- todo:`
    # rewritten as a `TODO` command is not new work. Only this list is widened that
    # way; the items above stay keyed against the items at the base alone.
    loose_keys = base_keys | {key(todo.content) for todo in base_unknown}
    unknown = [todo for todo in unknown if key(todo.content) not in loose_keys]

    meta = {"base": base, "head": head_sha, "date": date, "files": nfiles}

    emit_terminal(items, unknown, meta, args.plain)
    if args.md:
        with open(args.md, "w", encoding="utf-8") as fh:
            fh.write(emit_md(items, meta, args.repo_url, args.link_ref))


if __name__ == "__main__":
    main()
