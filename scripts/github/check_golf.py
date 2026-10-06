#!/usr/bin/env python3
"""check_golf.py -- verify that a pull request only golfs proofs.

A "golf" changes the *proofs* of lemmas/theorems (and the *bodies* of
definitions) without touching their *statements* (the signature: the name,
the binders and the type). This script compares two git revisions of the
repository and, for every declaration in the changed Lean files, decides
whether its statement was preserved and only the proof/body changed. For a
definition it further distinguishes changes confined to its ``by`` proof
blocks (data unchanged) from changes to the defining term itself (where the
data *may* have changed -- textually we cannot always tell). It also
counts the trivial reshapes among the golfs: proofs where only a newline was
removed (same tokens, fewer lines), and proofs where tactics were joined onto
one line with a ``;`` (excluding the ``<;>`` combinator).

It is meant to be driven from a GitHub workflow that reacts to a
``/check-golf`` comment on a pull request: it produces a Markdown report and,
when asked, upserts that report as a single PR comment (posting it the first
time, editing it on subsequent runs).

The Lean side is parsed textually -- no build is required, which keeps the
check fast. The parser strips comments and string literals, tracks bracket
depth, and splits each declaration at the top-level ``:=`` (or ``where``) that
separates its statement from its body. That top-level split is what lets it
ignore ``:=`` inside default-valued binders and ``by`` tactic blocks that live
*inside* a type (e.g. ``⟨x, by omega⟩``).

With ``--measure`` it additionally reports the compile cost of the golf: for
every changed file it compiles the base and head versions and diffs their
heartbeats (via Mathlib's ``#count_heartbeats``) and wall-clock time. This
requires a built project, so it is only used from CI after a ``lake build``.

Usage (analysis / dry-run, prints Markdown to stdout):

    scripts/github/check_golf.py --base <ref> --head <ref>

Usage (from CI, upserts the PR comment):

    scripts/github/check_golf.py --base <sha> --head <sha> \
        --repo owner/name --pr 1234 --post

The GitHub token is read from ``$GITHUB_TOKEN`` (override with ``--token-env``).
"""

from __future__ import annotations

import argparse
import json
import os
import re
import subprocess
import sys
import tempfile
import time
import urllib.request
from dataclasses import dataclass, field
from typing import Dict, List, Optional, Tuple

# The hidden marker lets the workflow find the comment it previously posted so
# it can edit it in place instead of piling up duplicates.
COMMENT_MARKER = "<!-- check-golf-report -->"

# Keywords that introduce a named declaration whose statement we want to track.
DECL_KEYWORDS = (
    "theorem",
    "lemma",
    "def",
    "abbrev",
    "instance",
    "example",
    "structure",
    "inductive",
    "class",
    "opaque",
)

# A declaration is a "proof" (statement + proof) versus a "definition"
# (statement + defining term). Golfing either preserves the statement.
PROOF_KEYWORDS = {"theorem", "lemma", "example"}

# Modifiers that may sit between the start of a line and the declaration keyword
# (attributes ``@[...]`` and ``set_option ... in`` / ``open ... in`` prefixes are
# handled structurally, not through this set).
MODIFIERS = {
    "private",
    "protected",
    "noncomputable",
    "unsafe",
    "partial",
    "nonrec",
    "scoped",
    "local",
    "mutual",
}

# Keywords that open/close a namespacing scope.
SCOPE_KEYWORDS = {"namespace", "section", "end"}

OPEN_BRACKETS = "([{⟨⦃"
CLOSE_BRACKETS = ")]}⟩⦄"

# Characters that terminate the name token following a declaration keyword.
NAME_STOP = set(" \t\r\n({[⦃⟨:=")


# --------------------------------------------------------------------------- #
# Lean lexical pre-processing
# --------------------------------------------------------------------------- #
def code_view(text: str) -> str:
    """Return ``text`` with comments and string literals blanked to spaces.

    Length and newline positions are preserved so indices computed on the
    result line up with the original source. Block comments (``/- -/``) nest,
    which also covers doc comments (``/-- -/``) and module docs (``/-! -/``).
    """
    out: List[str] = []
    i, n = 0, len(text)
    NORMAL, LINE, BLOCK, STR = 0, 1, 2, 3
    state = NORMAL
    block_depth = 0
    while i < n:
        c = text[i]
        two = text[i:i + 2]
        if state == NORMAL:
            if two == "--":
                out.append("  ")
                i += 2
                state = LINE
                continue
            if two == "/-":
                out.append("  ")
                i += 2
                state = BLOCK
                block_depth = 1
                continue
            if c == '"':
                out.append(" ")
                i += 1
                state = STR
                continue
            out.append(c)
            i += 1
        elif state == LINE:
            if c == "\n":
                out.append("\n")
                state = NORMAL
            else:
                out.append(" ")
            i += 1
        elif state == BLOCK:
            if two == "/-":
                out.append("  ")
                i += 2
                block_depth += 1
                continue
            if two == "-/":
                out.append("  ")
                i += 2
                block_depth -= 1
                if block_depth == 0:
                    state = NORMAL
                continue
            out.append("\n" if c == "\n" else " ")
            i += 1
        else:  # STR
            if c == "\\":
                out.append("  " if i + 1 < n else " ")
                i += 2
                continue
            if c == '"':
                out.append(" ")
                state = NORMAL
                i += 1
                continue
            out.append("\n" if c == "\n" else " ")
            i += 1
    return "".join(out)


def normalize(fragment: str) -> str:
    """Collapse whitespace so pure reformatting is not seen as a change."""
    return " ".join(fragment.split())


# A standalone `;` tactic separator, i.e. not part of the `<;>` combinator.
_SEMI_RE = re.compile(r"(?<!<);(?!>)")


def code_lines(fragment: str) -> List[str]:
    """Non-blank lines of a (comment-stripped) fragment, each stripped."""
    return [line.strip() for line in fragment.split("\n") if line.strip()]


def semi_count(fragment: str) -> int:
    """Number of standalone `;` tactic separators (ignoring `<;>`)."""
    return len(_SEMI_RE.findall(fragment))


_BY_RE = re.compile(r"(?<![\w'.])by(?![\w'])")


def mask_by_indent(body: str) -> str:
    """Collapse indentation-delimited ``by`` tactic blocks to a placeholder.

    In a definition, proof *obligations* are usually discharged by ``by``
    blocks (delimited by indentation), while the data lives outside them.
    Masking every ``by`` block therefore leaves the data: if two versions of a
    definition agree once their ``by`` blocks are masked, only proofs changed
    and the definition's data is unchanged. This is a heuristic -- a proof
    written as a term rather than ``by`` is not recognised as a proof.
    """
    lines = body.split("\n")
    out: List[str] = []
    i, n = 0, len(lines)
    while i < n:
        line = lines[i]
        indent = len(line) - len(line.lstrip())
        m = _BY_RE.search(line)
        if m:
            out.append(line[:m.start()] + "<by>")
            i += 1
            while i < n:
                nxt = lines[i]
                stripped = nxt.lstrip()
                if stripped == "" or len(nxt) - len(stripped) > indent:
                    i += 1
                else:
                    break
        else:
            out.append(line)
            i += 1
    return normalize("\n".join(out))


def _ident_char(c: str) -> bool:
    return c.isalnum() or c in "_.'" or ord(c) > 127


def mask_by_blocks(sig_code: str) -> str:
    """Blank the contents of ``by`` tactic blocks embedded inside a statement.

    A statement's *type* can embed proof terms -- ``⟨x, by omega⟩`` or an
    argument such as ``(by decide)``. By proof irrelevance those tactic blocks
    do not affect the elaborated type, so golfing them keeps the statement.
    Each embedded ``by`` block runs to the end of its enclosing bracket group;
    we replace it with a placeholder so signatures that differ only inside such
    blocks compare equal.
    """
    out: List[str] = []
    i, n = 0, len(sig_code)
    depth = 0
    while i < n:
        if (sig_code[i:i + 2] == "by"
                and (i == 0 or not _ident_char(sig_code[i - 1]))
                and (i + 2 >= n or not _ident_char(sig_code[i + 2]))):
            d0 = depth
            out.append("by<>")
            i += 2
            while i < n:
                c = sig_code[i]
                if c in OPEN_BRACKETS:
                    depth += 1
                elif c in CLOSE_BRACKETS:
                    if depth == d0:
                        break  # close bracket of the enclosing group
                    depth -= 1
                i += 1
            continue
        c = sig_code[i]
        if c in OPEN_BRACKETS:
            depth += 1
        elif c in CLOSE_BRACKETS:
            depth = max(0, depth - 1)
        out.append(c)
        i += 1
    return normalize("".join(out))


# --------------------------------------------------------------------------- #
# Declaration extraction
# --------------------------------------------------------------------------- #
@dataclass
class Decl:
    name: str
    keyword: str
    signature: str         # normalized statement (keyword .. up to `:=`/`where`)
    signature_masked: str  # same, with embedded `by` proof blocks blanked
    body: str              # normalized defining term / proof
    body_raw: str          # defining term / proof, comments stripped, layout kept

    @property
    def is_proof(self) -> bool:
        return self.keyword in PROOF_KEYWORDS


def _line_prefix(code: str, pos: int) -> str:
    """The text on ``pos``'s line, up to ``pos`` (from the previous newline)."""
    start = code.rfind("\n", 0, pos) + 1
    return code[start:pos]


_WHERE_RE = re.compile(r"(?<![\w.'])where(?![\w'])")


def _block_starts(code: str) -> List[int]:
    """Indices of top-level command starts: non-blank characters in column 0.

    In Mathlib-style Lean, top-level commands (``lemma``, ``def``,
    ``namespace``, ...) begin in column 0, while everything that belongs to a
    command -- multi-line signatures, tactic blocks, term proofs -- is
    indented. Segmenting on column-0 lines is therefore robust even when a
    proof body contains brackets we cannot balance textually (e.g. a ``by``
    block closed by indentation rather than a ``)``).
    """
    starts = [0] if code and not code[0].isspace() else []
    for i in range(1, len(code)):
        if code[i - 1] == "\n" and not code[i].isspace() and code[i] != "\n":
            starts.append(i)
    return starts


def _read_token(code: str, pos: int, end: int) -> str:
    j = pos
    while j < end and code[j] not in NAME_STOP and code[j] != "@":
        j += 1
    return code[pos:j]


def _strip_prefixes(code: str, start: int, end: int) -> int:
    """Skip attributes / modifiers / ``... in`` prefixes; return keyword index."""
    pos = start
    while pos < end:
        while pos < end and code[pos] in " \t\r\n":
            pos += 1
        if pos >= end:
            break
        if code[pos] == "@" and pos + 1 < end and code[pos + 1] == "[":
            depth = 0
            while pos < end:
                if code[pos] == "[":
                    depth += 1
                elif code[pos] == "]":
                    depth -= 1
                    if depth == 0:
                        pos += 1
                        break
                pos += 1
            continue
        tok = _read_token(code, pos, end)
        if tok in MODIFIERS:
            pos += len(tok)
            continue
        if tok in ("set_option", "open"):
            m = re.compile(r"(?<![\w.'])in(?![\w'])").search(code, pos, end)
            if m:
                pos = m.end()
                continue
        break
    return pos


def _find_boundary(code: str, start: int, end: int) -> int:
    """Index in ``[start, end)`` where the statement ends and the body begins.

    Bracket depth is tracked *locally* to this declaration. The body begins at
    the first top-level ``:=`` or ``where``, or -- for equation-compiler
    declarations that have neither -- at the first line-leading ``|`` arm
    (recognised by a following top-level ``=>``, which distinguishes a real arm
    from an absolute value ``|x|`` in a type). Returns ``end`` if none found.
    """
    b_assign = b_where = b_bar = None
    seen_bars: List[int] = []
    depth = 0
    i = start
    while i < end:
        c = code[i]
        if depth == 0:
            if b_assign is None and code[i:i + 2] == ":=":
                b_assign = i
            elif code[i:i + 2] == "=>" and seen_bars and b_bar is None:
                b_bar = seen_bars[0]
            elif b_where is None and _WHERE_RE.match(code, i):
                b_where = i
            if c == "|" and _line_prefix(code, i).strip() == "":
                seen_bars.append(i)
        if c in OPEN_BRACKETS:
            depth += 1
        elif c in CLOSE_BRACKETS:
            depth = max(0, depth - 1)
        i += 1
    candidates = [b for b in (b_assign, b_where, b_bar) if b is not None]
    return min(candidates) if candidates else end


def _apply_scope(stack: List[Tuple[str, str]], keyword: str, name: str) -> None:
    if keyword == "namespace":
        stack.append(("namespace", name))
    elif keyword == "section":
        stack.append(("section", name))
    else:  # end
        if name:
            for k in range(len(stack) - 1, -1, -1):
                if stack[k][1] == name:
                    del stack[k:]
                    return
            if stack:
                stack.pop()
        elif stack:
            stack.pop()


def parse_decls(text: str) -> "Dict[str, Decl]":
    """Parse ``text`` into a map from qualified name to :class:`Decl`."""
    code = code_view(text)
    starts = _block_starts(code)
    ns_stack: List[Tuple[str, str]] = []
    result: "Dict[str, Decl]" = {}
    seen: Dict[str, int] = {}

    for idx, start in enumerate(starts):
        end = starts[idx + 1] if idx + 1 < len(starts) else len(code)
        kw_pos = _strip_prefixes(code, start, end)
        keyword = _read_token(code, kw_pos, end)

        if keyword in SCOPE_KEYWORDS:
            rest = code[kw_pos + len(keyword):end].split("\n", 1)[0].strip()
            name = rest.split()[0] if rest else ""
            _apply_scope(ns_stack, keyword, name)
            continue
        if keyword not in DECL_KEYWORDS:
            continue

        # Parse the declaration name.
        j = kw_pos + len(keyword)
        while j < end and code[j] in " \t\r\n":
            j += 1
        k = j
        while k < end and code[k] not in NAME_STOP:
            k += 1
        local = code[j:k]
        if not local:
            continue  # anonymous instance / example -- cannot track by name

        boundary = _find_boundary(code, k, end)
        sig_code = code[kw_pos:boundary]
        signature = normalize(sig_code)
        signature_masked = mask_by_blocks(sig_code)
        body_start = boundary + (2 if code[boundary:boundary + 2] == ":=" else 0)
        body_raw = code[body_start:end]
        body = normalize(body_raw)

        prefix = ".".join(nm for kind, nm in ns_stack
                          if kind == "namespace" and nm)
        qualified = (prefix + "." + local) if prefix else local
        if qualified in seen:
            seen[qualified] += 1
            qualified = "{}#{}".format(qualified, seen[qualified])
        else:
            seen[qualified] = 0
        result[qualified] = Decl(qualified, keyword, signature,
                                 signature_masked, body, body_raw)
    return result


# --------------------------------------------------------------------------- #
# Comparison
# --------------------------------------------------------------------------- #
@dataclass
class FileReport:
    path: str
    statement_changed: List[str] = field(default_factory=list)
    proof_golfed: List[str] = field(default_factory=list)
    embedded_proof_changed: List[str] = field(default_factory=list)
    def_proof_golfed: List[str] = field(default_factory=list)
    def_value_changed: List[str] = field(default_factory=list)
    added: List[str] = field(default_factory=list)
    removed: List[str] = field(default_factory=list)
    # Trivial golf shapes (subsets / refinements of the above).
    newline_removed: List[str] = field(default_factory=list)
    semicolon_crammed: List[Tuple[str, int]] = field(default_factory=list)

    @property
    def touched(self) -> bool:
        return bool(self.statement_changed or self.proof_golfed
                    or self.embedded_proof_changed or self.def_proof_golfed
                    or self.def_value_changed or self.added or self.removed
                    or self.newline_removed)


def compare_file(path: str, base_src: Optional[str],
                 head_src: Optional[str]) -> FileReport:
    rep = FileReport(path)
    base = parse_decls(base_src) if base_src is not None else {}
    head = parse_decls(head_src) if head_src is not None else {}
    for name, d in head.items():
        if name not in base:
            rep.added.append(name)
            continue
        b = base[name]
        if b.signature != d.signature:
            if b.signature_masked == d.signature_masked:
                # Only embedded proof terms differ: the type is unchanged.
                rep.embedded_proof_changed.append(name)
            else:
                rep.statement_changed.append(name)
            continue
        # Statement preserved; classify how the proof/body changed.
        if b.body != d.body:
            # A real token-level change to the proof / defining term.
            if d.is_proof:
                rep.proof_golfed.append(name)
            else:
                mb, mh = mask_by_indent(b.body_raw), mask_by_indent(d.body_raw)
                # "Data unchanged" only if the term outside `by` proof blocks is
                # identical AND the whole body is not itself one `by` block: a
                # `def foo := by ...` builds its *value* with tactics, so any
                # change there may change the definition, not just a proof.
                if mb == mh and mh != "<by>":
                    rep.def_proof_golfed.append(name)
                else:
                    rep.def_value_changed.append(name)
            crammed = semi_count(d.body_raw) - semi_count(b.body_raw)
            if crammed > 0:
                rep.semicolon_crammed.append((name, crammed))
        elif len(code_lines(b.body_raw)) > len(code_lines(d.body_raw)):
            # Same tokens, fewer lines: the proof was only reflowed (a newline
            # was deleted) without joining tactics with `;`.
            rep.newline_removed.append(name)
    for name in base:
        if name not in head:
            rep.removed.append(name)
    return rep


# --------------------------------------------------------------------------- #
# Git helpers
# --------------------------------------------------------------------------- #
def git(*args: str) -> str:
    return subprocess.run(["git", *args], check=True, capture_output=True,
                          text=True).stdout


def git_maybe(*args: str) -> Optional[str]:
    p = subprocess.run(["git", *args], capture_output=True, text=True)
    return p.stdout if p.returncode == 0 else None


def changed_lean_files(base: str, head: str) -> List[str]:
    out = git("diff", "--name-only", "--diff-filter=ACMRD", base, head)
    return [f for f in out.splitlines() if f.endswith(".lean")]


def file_at(ref: str, path: str) -> Optional[str]:
    return git_maybe("show", "{}:{}".format(ref, path))


# --------------------------------------------------------------------------- #
# Compile-cost measurement (heartbeats + time)
# --------------------------------------------------------------------------- #
IMPORT_RE = re.compile(r"^\s*(?:public\s+|private\s+|meta\s+)*import\s")
HEARTBEAT_RE = re.compile(r"[Uu]sed (?:approximately )?(\d+) heartbeats")


@dataclass
class Measurement:
    path: str
    base_hb: Optional[int] = None
    head_hb: Optional[int] = None
    base_ms: Optional[float] = None
    head_ms: Optional[float] = None
    note: str = ""

    @property
    def ok(self) -> bool:
        return self.base_hb is not None and self.head_hb is not None

    @property
    def dhb(self) -> int:
        return (self.head_hb or 0) - (self.base_hb or 0)


def _comment_mask(src: str) -> bytearray:
    """``mask[i] == 1`` if character ``i`` is inside a comment."""
    n = len(src)
    mask = bytearray(n)
    i, state, depth = 0, 0, 0  # state: 0 normal, 1 line, 2 block, 3 string
    while i < n:
        c = src[i]
        two = src[i:i + 2]
        if state == 0:
            if two == "--":
                mask[i] = 1
                if i + 1 < n:
                    mask[i + 1] = 1
                i += 2
                state = 1
            elif two == "/-":
                mask[i] = 1
                if i + 1 < n:
                    mask[i + 1] = 1
                i += 2
                state, depth = 2, 1
            elif c == '"':
                i += 1
                state = 3
            else:
                i += 1
        elif state == 1:
            if c == "\n":
                state = 0
            else:
                mask[i] = 1
            i += 1
        elif state == 2:
            if two == "/-":
                mask[i] = 1
                mask[i + 1] = 1
                i += 2
                depth += 1
            elif two == "-/":
                mask[i] = 1
                mask[i + 1] = 1
                i += 2
                depth -= 1
                if depth == 0:
                    state = 0
            else:
                mask[i] = 1
                i += 1
        else:  # string
            if c == "\\":
                i += 2
            elif c == '"':
                state = 0
                i += 1
            else:
                i += 1
    return mask


def _attach_point(src: str, mask: bytearray, start: int) -> int:
    """Move an insertion point above a doc comment attached to a declaration."""
    j = start
    while j > 0 and src[j - 1].isspace():
        j -= 1
    if j > 0 and mask[j - 1]:
        while j > 0 and mask[j - 1]:
            j -= 1
        return src.rfind("\n", 0, j) + 1
    return start


def _instrument(src: str) -> Optional[str]:
    """Wrap every top-level declaration with a heartbeat counter; None if no imports.

    Mathlib's ``#count_heartbeats in <cmd>`` reports the heartbeats a command
    uses, but only under ``Elab.async false`` -- otherwise the proof elaborates
    in a background task the counter cannot see. So we import the counter, force
    synchronous elaboration once, and prefix ``#count_heartbeats in`` before
    each declaration (above any attached doc comment, so it stays attached).
    """
    code = code_view(src)
    starts = _block_starts(code)
    lines = src.split("\n")
    imports = [i for i, line in enumerate(lines) if IMPORT_RE.match(line)]
    if not imports:
        return None

    # Character offset of the start of each source line.
    line_off = [0]
    for line in lines:
        line_off.append(line_off[-1] + len(line) + 1)
    import_at = line_off[max(imports) + 1]

    mask = _comment_mask(src)
    inserts = [(import_at, "import Mathlib.Util.CountHeartbeats\n"
                           "set_option Elab.async false\n\n")]
    # Attributes/modifiers can sit on their own column-0 line, forming a block
    # of their own; such a prefix block belongs to the declaration that follows,
    # so the counter must go before the prefix, not between it and the keyword.
    prefix_start = None
    for idx, start in enumerate(starts):
        end = starts[idx + 1] if idx + 1 < len(starts) else len(code)
        kw_pos = _strip_prefixes(code, start, end)
        keyword = _read_token(code, kw_pos, end)
        logical_start = prefix_start if prefix_start is not None else start
        if keyword == "":
            # Attribute-/modifier-only line: hold it for the next declaration.
            prefix_start = logical_start
            continue
        if keyword in DECL_KEYWORDS:
            inserts.append((_attach_point(src, mask, logical_start),
                            "#count_heartbeats in\n"))
        prefix_start = None

    out = src
    for offset, text in sorted(inserts, reverse=True):
        out = out[:offset] + text + out[offset:]
    return out


def _run_lean(source: str) -> Tuple[bool, int, float]:
    """Compile ``source`` with ``lake env lean``; return (ok, heartbeats, ms).

    Heartbeats are deterministic; wall-clock time includes constant import
    loading, so only the base-vs-head *delta* is meaningful.
    """
    with tempfile.NamedTemporaryFile("w", suffix=".lean", delete=False) as f:
        f.write(source)
        tmp = f.name
    try:
        t0 = time.monotonic()
        p = subprocess.run(["lake", "env", "lean", tmp],
                           capture_output=True, text=True)
        ms = (time.monotonic() - t0) * 1000.0
    finally:
        os.unlink(tmp)
    out = p.stdout + p.stderr
    total = sum(int(m.group(1)) for m in HEARTBEAT_RE.finditer(out))
    return p.returncode == 0, total, ms


def measure_revision(ref: str, path: str) -> Tuple[Optional[int], Optional[float], str]:
    """Measure heartbeats/time for ``path`` at ``ref`` against the built env."""
    src = file_at(ref, path)
    if src is None:
        return None, None, "file absent at {}".format(ref[:9])
    injected = _instrument(src)
    if injected is None:
        return None, None, "no import block"
    ok, hb, ms = _run_lean(injected)
    if not ok:
        return None, None, "did not compile in isolation"
    return hb, ms, ""


def measure_files(base: str, head: str, reports: List[FileReport],
                  limit: Optional[int] = None,
                  jobs: int = 1) -> List[Measurement]:
    """Measure each file that had a proof/body change, base and head.

    The base source is compiled against the (head) built environment; this is
    sound exactly when statements are preserved -- which is what the check
    itself verifies -- because only proof/body text then differs.

    With ``jobs > 1`` measurements run concurrently. Heartbeats are
    deterministic and unaffected; wall-clock times are measured under load,
    so only large time deltas remain meaningful.
    """
    paths = [r.path for r in reports
             if r.proof_golfed or r.embedded_proof_changed or r.def_value_changed]
    if limit is not None:
        paths = paths[:limit]

    def one(path: str) -> Measurement:
        bhb, bms, bnote = measure_revision(base, path)
        hhb, hms, hnote = measure_revision(head, path)
        return Measurement(path, bhb, hhb, bms, hms, bnote or hnote)

    out: List[Measurement] = []
    if jobs <= 1:
        for i, path in enumerate(paths):
            m = one(path)
            out.append(m)
            print("[{}/{}] measured {} ({})".format(
                i + 1, len(paths), path, m.note or "ok"), file=sys.stderr)
        return out
    from concurrent.futures import ThreadPoolExecutor
    with ThreadPoolExecutor(max_workers=jobs) as ex:
        for i, m in enumerate(ex.map(one, paths)):
            out.append(m)
            print("[{}/{}] measured {} ({})".format(
                i + 1, len(paths), m.path, m.note or "ok"), file=sys.stderr)
    return out


# --------------------------------------------------------------------------- #
# Report rendering
# --------------------------------------------------------------------------- #
def _bullets(names: List[str], path: str) -> str:
    return "\n".join("- `{}` — `{}`".format(n, path) for n in sorted(names))


def _fmt_signed(n: int) -> str:
    return "+{:,}".format(n) if n > 0 else "{:,}".format(n)


def _render_measurements(lines: List[str],
                         measurements: List[Measurement]) -> None:
    ok = [m for m in measurements if m.ok]
    failed = [m for m in measurements if not m.ok]
    lines.append("### ⏱️ Compile cost (base → head)")
    lines.append("")
    if not ok:
        lines.append("_No changed files could be measured in isolation "
                     "({} attempted)._".format(len(measurements)))
        lines.append("")
        return
    tb = sum(m.base_hb for m in ok)
    th = sum(m.head_hb for m in ok)
    tbm = sum(m.base_ms or 0.0 for m in ok)
    thm = sum(m.head_ms or 0.0 for m in ok)
    pct = (100.0 * (th - tb) / tb) if tb else 0.0
    extra = (" ({} could not be measured in isolation)".format(len(failed))
             if failed else "")
    lines.append("Measured **{}** file(s) with body changes{}.".format(
        len(ok), extra))
    lines.append("")
    lines.append("- **Heartbeats:** {:,} → {:,} (**{}**, {:+.1f}%)".format(
        tb, th, _fmt_signed(th - tb), pct))
    lines.append("- **Elapsed** (wall-clock, includes constant import loading): "
                 "{:.1f}s → {:.1f}s".format(tbm / 1000.0, thm / 1000.0))
    lines.append("")
    movers = [m for m in ok if m.dhb != 0]
    top = sorted(movers, key=lambda m: abs(m.dhb), reverse=True)[:20]
    top.sort(key=lambda m: m.dhb)
    if top:
        lines.append("<details open><summary>Largest heartbeat changes "
                     "({} of {} files differ)</summary>\n".format(
                         len(movers), len(ok)))
        lines.append("| File | Δ heartbeats | base → head |")
        lines.append("|---|---:|---|")
        for m in top:
            lines.append("| `{}` | {} | {:,} → {:,} |".format(
                m.path, _fmt_signed(m.dhb), m.base_hb, m.head_hb))
        lines.append("\n</details>")
        lines.append("")


def render_report(base: str, head: str, reports: List[FileReport],
                  measurements: "Optional[List[Measurement]]" = None) -> str:
    stmt = [(r.path, n) for r in reports for n in r.statement_changed]
    golfed = [(r.path, n) for r in reports for n in r.proof_golfed]
    embedded = [(r.path, n) for r in reports for n in r.embedded_proof_changed]
    defproof = [(r.path, n) for r in reports for n in r.def_proof_golfed]
    defval = [(r.path, n) for r in reports for n in r.def_value_changed]
    added = [(r.path, n) for r in reports for n in r.added]
    removed = [(r.path, n) for r in reports for n in r.removed]
    newline = [(r.path, n) for r in reports for n in r.newline_removed]
    crammed = [(r.path, n, c) for r in reports for n, c in r.semicolon_crammed]
    cram_total = sum(c for _, _, c in crammed)
    n_files = sum(1 for r in reports if r.touched)

    lines: List[str] = [COMMENT_MARKER, "## 🏌️ check-golf report", ""]
    lines.append("Comparing base `{}` → head `{}` across **{}** changed Lean "
                 "file(s).".format(base[:9], head[:9], n_files))
    lines.append("")
    if stmt:
        lines.append("**Result: ❌ Statements changed.** {} declaration(s) "
                     "changed their statement — this is more than a golf. See "
                     "below.".format(len(stmt)))
    elif golfed or embedded or defproof or defval or newline:
        lines.append("**Result: ✅ Statements preserved.** Every changed "
                     "declaration kept its statement; only proofs / bodies "
                     "changed.")
    else:
        lines.append("**Result: ✅ No declaration statements changed.**")
    lines.append("")

    lines.append("| Category | Count |")
    lines.append("|---|---:|")
    lines.append("| Proofs golfed (statement unchanged) | {} |".format(len(golfed)))
    lines.append("| Embedded proofs golfed (type unchanged) | {} |".format(len(embedded)))
    lines.append("| Definition proofs golfed (data unchanged) | {} |".format(len(defproof)))
    lines.append("| **Definition bodies changed** (data *may* have changed, type unchanged) | {} |".format(len(defval)))
    lines.append("| **Statements changed** | {} |".format(len(stmt)))
    lines.append("| Declarations added | {} |".format(len(added)))
    lines.append("| Declarations removed | {} |".format(len(removed)))
    lines.append("")
    lines.append("Of the golfed proofs/bodies above, the trivial reshapes were:")
    lines.append("")
    lines.append("| Golf shape | Count |")
    lines.append("|---|---:|")
    lines.append("| Only a newline removed (proof reflowed, tokens unchanged) | {} |"
                 .format(len(newline)))
    lines.append("| Declarations with tactics joined by `;` | {} |".format(len(crammed)))
    lines.append("| — total `;` tactic-joins introduced | {} |".format(cram_total))
    lines.append("")

    def section(title: str, items: List[Tuple[str, str]], open_: bool,
                note: str = "") -> None:
        if not items:
            return
        lines.append("<details{}><summary>{} ({})</summary>\n".format(
            " open" if open_ else "", title, len(items)))
        if note:
            lines.append(note + "\n")
        for path, name in sorted(items):
            lines.append("- `{}` — `{}`".format(name, path))
        lines.append("\n</details>")
        lines.append("")

    section("❌ Statements changed", stmt, open_=True)
    section("🔧 Definition bodies changed (data may have changed, type unchanged)",
            defval, open_=bool(defval and not stmt),
            note=("_The defining term outside `by` proof blocks changed, or the "
                  "whole body is one `by` block. The data may or may not have "
                  "actually changed — flagged for a human glance._"))
    section("✅ Proofs golfed", golfed, open_=False)
    section("✅ Embedded proofs golfed (type unchanged)", embedded, open_=False)
    section("✅ Definition proofs golfed (data unchanged)", defproof, open_=False)
    section("↩️ Only a newline removed (tokens unchanged)", newline, open_=False)
    section("➕ Declarations added", added, open_=False)
    section("➖ Declarations removed", removed, open_=False)

    if crammed:
        lines.append("<details><summary>➡️ Tactics joined by `;` ({})</summary>\n"
                     .format(len(crammed)))
        for path, name, count in sorted(crammed):
            suffix = "" if count == 1 else " (×{})".format(count)
            lines.append("- `{}` — `{}`{}".format(name, path, suffix))
        lines.append("\n</details>")
        lines.append("")

    if measurements is not None:
        _render_measurements(lines, measurements)

    lines.append(
        "<sub>Generated by <code>scripts/github/check_golf.py</code> · triggered by "
        "<code>/check-golf</code>. Statements are compared textually: comments "
        "and whitespace are ignored, and <code>by</code> proof terms embedded "
        "in a type are treated as proofs (proof-irrelevant). Anonymous "
        "instances and <code>example</code>s are not tracked (no stable name). "
        "For a <code>def</code>/<code>instance</code>/<code>abbrev</code> we mask "
        "its <code>by</code> proof blocks: if only those changed it is a "
        "“definition proofs golfed” (the data is unchanged); if something "
        "outside them changed — or the whole body is one <code>by</code> block "
        "— it is a “definition body changed” (the data may have changed; "
        "textually we cannot always tell). <code>;</code> "
        "counts exclude the <code>&lt;;&gt;</code> combinator. Heartbeats are "
        "measured with Mathlib's <code>#count_heartbeats</code> and are "
        "deterministic; elapsed time is wall-clock.</sub>")
    return "\n".join(lines)


# --------------------------------------------------------------------------- #
# GitHub comment upsert
# --------------------------------------------------------------------------- #
def _api(method: str, url: str, token: str,
         payload: Optional[dict] = None) -> dict:
    data = json.dumps(payload).encode() if payload is not None else None
    req = urllib.request.Request(url, data=data, method=method)
    req.add_header("Authorization", "Bearer " + token)
    req.add_header("Accept", "application/vnd.github+json")
    req.add_header("X-GitHub-Api-Version", "2022-11-28")
    if data is not None:
        req.add_header("Content-Type", "application/json")
    with urllib.request.urlopen(req) as resp:
        raw = resp.read().decode()
    return json.loads(raw) if raw else {}


def find_existing_comment(repo: str, pr: int, token: str) -> Optional[int]:
    page = 1
    while True:
        url = ("https://api.github.com/repos/{}/issues/{}/comments"
               "?per_page=100&page={}".format(repo, pr, page))
        req = urllib.request.Request(url)
        req.add_header("Authorization", "Bearer " + token)
        req.add_header("Accept", "application/vnd.github+json")
        with urllib.request.urlopen(req) as resp:
            batch = json.loads(resp.read().decode())
        if not batch:
            return None
        for comment in batch:
            if COMMENT_MARKER in (comment.get("body") or ""):
                return comment["id"]
        if len(batch) < 100:
            return None
        page += 1


def upsert_comment(repo: str, pr: int, token: str, body: str) -> str:
    existing = find_existing_comment(repo, pr, token)
    if existing is not None:
        _api("PATCH",
             "https://api.github.com/repos/{}/issues/comments/{}".format(
                 repo, existing), token, {"body": body})
        return "edited comment {}".format(existing)
    created = _api("POST",
                   "https://api.github.com/repos/{}/issues/{}/comments".format(
                       repo, pr), token, {"body": body})
    return "created comment {}".format(created.get("id"))


# --------------------------------------------------------------------------- #
# CLI
# --------------------------------------------------------------------------- #
def build_reports(base: str, head: str) -> List[FileReport]:
    reports = []
    for path in changed_lean_files(base, head):
        rep = compare_file(path, file_at(base, path), file_at(head, path))
        if rep.touched:
            reports.append(rep)
    return reports


def main(argv: Optional[List[str]] = None) -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--base", required=True, help="base git ref (merge-base)")
    ap.add_argument("--head", required=True, help="head git ref")
    ap.add_argument("--repo", help="owner/name, required with --post")
    ap.add_argument("--pr", type=int, help="PR number, required with --post")
    ap.add_argument("--post", action="store_true",
                    help="upsert the report as a PR comment")
    ap.add_argument("--token-env", default="GITHUB_TOKEN",
                    help="env var holding the GitHub token (default GITHUB_TOKEN)")
    ap.add_argument("--measure", action="store_true",
                    help="also measure compile time and heartbeats "
                         "(requires a built project)")
    ap.add_argument("--measure-jobs", type=int,
                    default=max(1, os.cpu_count() or 1),
                    help="concurrent measurement compiles (default: nproc)")
    ap.add_argument("--measure-limit", type=int, default=None,
                    help="measure at most this many files (for a quick sample)")
    args = ap.parse_args(argv)

    reports = build_reports(args.base, args.head)
    measurements = None
    if args.measure:
        measurements = measure_files(args.base, args.head, reports,
                                     args.measure_limit,
                                     args.measure_jobs)
    body = render_report(args.base, args.head, reports, measurements)

    if args.post:
        if not (args.repo and args.pr):
            ap.error("--post requires --repo and --pr")
        token = os.environ.get(args.token_env, "")
        if not token:
            ap.error("no token in ${}".format(args.token_env))
        status = upsert_comment(args.repo, args.pr, token, body)
        print(status, file=sys.stderr)
    else:
        print(body)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
