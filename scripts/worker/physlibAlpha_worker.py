#!/usr/bin/env -S uv run --script
# /// script
# requires-python = ">=3.11"
# dependencies = []
# ///
r"""
# physlibAlpha-worker

This script allows the automation of tasks in PhyslibAlpha, making it easy for people
to donate tokens in a useful and responsible way. This script can be used independently,
or as the backend of a more sophisticated engine.

## The tasks

-- Each task is a skill in Physlib, `.agents/skills/<task>/SKILL.md`: the text after its
   frontmatter is the prompt given to the agent. Only the skills listed in
   `scripts/worker/physlibAlpha_worker.toml` are tasks of the worker. That file also gives each
   task's PR title, and which task is the default, for example:

       default = "alpha-next-step"

       [tasks.alpha-next-step]
       title = "feat(PhyslibAlpha): add a definition expanding PhyslibAlpha"

       [tasks.alpha-align-with-handbook]
       title = "refactor(PhyslibAlpha): tidy a PhyslibAlpha file"

   The tasks are read from upstream master (step 7), or, with `--tasks-from <path>`, from the
   Physlib checkout at <path>, to test changes to them.
-- custom "<input>": This runs the a custom task on PhyslibAlpha.

## How it works

The file is in numbered sections, which the worker runs one after the other (section 5 only
defines the agents that the later steps use):

1. Determine the save location.
2. Determine if a fork exists and if not create one.
3. Determine if a clone already exists, and if not make one.
4. Create a new branch based on upstream/master.
5. Infrastructure for Agents.
6. Finding the model to run the code on.
7. Determine the task.
8. Running the task.
9. Creating the PR.
10. Clean up.

## Locally testing

From the root of a Physlib checkout, run the file directly with Python (3.11 or later; the script
uses only Python's standard library):

    python3 scripts/worker/physlibAlpha_worker.py alpha-align-with-handbook

To test changes to the tasks or the config before they reach master, read them from your
checkout instead:

    python3 scripts/worker/physlibAlpha_worker.py alpha-align-with-handbook --tasks-from .

A local run does everything a real one does, including opening a PR on
`leanprover-community/physlib`.

"""

from __future__ import annotations

import argparse
import json
import os
import re
import subprocess
import sys
import time
import tomllib
from dataclasses import dataclass
from datetime import datetime, timezone
from pathlib import Path

UPSTREAM = "leanprover-community/physlib"
BASE_BRANCH = "master"
LIBRARY = "PhyslibAlpha"
NAME = "physlibAlpha-worker"
CONFIG = "scripts/worker/physlibAlpha_worker.toml"


###################
# 0. Running commands, and reporting progress
###################
# Each step below is a section of this file. It opens with the step's specification, as
# comments, followed by the code that carries it out.


class WorkerError(Exception):
    """A failure the worker reports and stops on."""


# Whether to color the output: only on a terminal, and not when NO_COLOR is set.
_COLOR = sys.stdout.isatty() and not os.environ.get("NO_COLOR")


def _paint(code: str, text: str) -> str:
    """`text` in the terminal style `code` (e.g. "2" for dim), when coloring is on."""
    return f"\033[{code}m{text}\033[0m" if _COLOR else text


def step(title: str) -> None:
    """Print the heading of a step of the run, e.g. `==> 1. Determine the save location`."""
    print("\n" + _paint("1;36", f"==> {title}"), flush=True)


def info(text: str) -> None:
    """Print `text` under the current step, each line indented."""
    for line in text.splitlines() or [""]:
        print(f"    {line}", flush=True)

def run(
    cmd: list[str],
    cwd: Path | None = None,
    capture: bool = False,
    check: bool = True,
    stdin_text: str | None = None,
    quiet: bool = False,
) -> subprocess.CompletedProcess[str]:
    """Run `cmd`, echoing it; raise WorkerError when it fails and `check` is set."""
    if not quiet:
        print(_paint("2", "    $ " + " ".join(cmd)), flush=True)
    try:
        result = subprocess.run(cmd, cwd=cwd, text=True, input=stdin_text, capture_output=capture)
    except FileNotFoundError:
        raise WorkerError(f"`{cmd[0]}` is not installed") from None
    if check and result.returncode != 0:
        detail = (result.stderr or result.stdout or "").strip() if capture else ""
        raise WorkerError(f"`{' '.join(cmd)}` failed (exit {result.returncode})" + (f":\n{detail}" if detail else ""))
    return result


def output(cmd: list[str], cwd: Path | None = None) -> str:
    """Run `cmd` and return its standard output."""
    return run(cmd, cwd=cwd, capture=True).stdout.strip()

###################
# 1. Determine the save location
###################
# First we need the location where we will save the clone of Physlib,
# and where the task will end up running. In the below we call this
# <save-location>.
def save_location() -> Path:
    # - If the environment variable `PHYSLIBALPHA_WORKER_HOME` is set, we use that.
    if home := os.environ.get("PHYSLIBALPHA_WORKER_HOME"):
        return Path(home).expanduser()
    # - If working on windows, `%LOCALAPPDATA%\physlibAlpha-worker`
    if os.name == "nt":
        local = os.environ.get("LOCALAPPDATA") or str(Path.home() / "AppData" / "Local")
        return Path(local) / NAME
    # - If working on mac or Linux, `$XDG_STATE_HOME/physlibAlpha-worker`, defaulting to
    #   `~/.local/state/physlibAlpha-worker`
    state = os.environ.get("XDG_STATE_HOME") or str(Path.home() / ".local" / "state")
    return Path(state) / NAME

###################
# 2. Determine if a fork exists and if not create one
###################
# Determine the user's GitHub login, and if there exists a fork of Physlib for that login.
# If there is not create such a fork.
# This outputs `<login>/<name>`.
def ensure_fork() -> str:
    """The user's fork of Physlib, `<login>/<name>`, made if there is none."""
    login = output(["gh", "api", "user", "--jq", ".login"])
    # Look for the fork among the user's forks by its parent, so a renamed fork is found too.
    repos = output(["gh", "repo", "list", login, "--fork", "--limit", "1000", "--json", "nameWithOwner,parent"])
    for repo in json.loads(repos):
        parent = repo.get("parent") or {}
        if f"{parent.get('owner', {}).get('login')}/{parent.get('name')}" == UPSTREAM:
            info(f"fork: {repo['nameWithOwner']}")
            return repo["nameWithOwner"]
    # There is none: ask GitHub for one, then wait until GitHub has built it.
    info(f"no fork of {UPSTREAM} found; creating one")
    fork = output(
        ["gh", "api", "-X", "POST", f"repos/{UPSTREAM}/forks", "-F", "default_branch_only=true", "--jq", ".full_name"]
    )
    info(f"waiting for GitHub to build {fork}")
    for _ in range(60):
        if run(["gh", "api", f"repos/{fork}", "--jq", ".full_name"], capture=True, check=False, quiet=True).returncode == 0:
            info(f"fork: {fork}")
            return fork
        time.sleep(5)
    raise WorkerError(f"GitHub did not finish building the fork {fork} within 5 minutes; try again later")

###################
# 3. Determine if a clone already exists, and if not make one
###################
# Determines if a clone of the fork exists at `<save-location>/physlib`.
# If it does not it creates one.
def ensure_clone(save: Path, fork: str) -> Path:
    """The clone of the fork in <save-location>, made if there is none."""
    clone = save / "physlib"
    if clone.exists():
        result = run(["git", "-C", str(clone), "remote", "get-url", "origin"], capture=True, check=False)
        if result.returncode != 0 or result.stdout.strip() not in (
            f"https://github.com/{fork}.git", f"git@github.com:{fork}.git"
        ):
            raise WorkerError(f"{clone} exists but is not a clone of {fork}; it has been left alone")
    else:
        save.mkdir(parents=True, exist_ok=True)
        run(["gh", "repo", "clone", fork, str(clone)])
    return clone


###################
# 4. Create a new branch based on upstream/master
###################
# This creates a branch based on upstream/master called `physlibAlpha-worker/<time>`.
# It also deletes other local branches of that name, to prevent unused works building up.
def create_branch(save: Path, started: str) -> str:
    """Update the clone to upstream master, delete earlier runs' branches, and create <branch>."""
    clone = save / "physlib"
    run(["git", "-C", str(clone), "fetch", "upstream", BASE_BRANCH])
    run(["git", "-C", str(clone), "reset", "--hard"])
    run(["git", "-C", str(clone), "clean", "-fd"])
    run(["git", "-C", str(clone), "switch", "--detach", f"upstream/{BASE_BRANCH}"])
    old = output(["git", "-C", str(clone), "branch", "--list", f"{NAME}/*", "--format", "%(refname:short)"])
    for old_branch in old.splitlines():
        run(["git", "-C", str(clone), "branch", "-D", old_branch])
    branch = f"{NAME}/{started}"
    run(["git", "-C", str(clone), "switch", "--create", branch, f"upstream/{BASE_BRANCH}"])
    return branch

###################
# 5. Infrastructure for Agents
###################
# We define the general data class for agents, which are agent agnostic.

@dataclass
class AgentRun:
    """How the agent's run ended: whether it succeeded, its final message, and its cost."""

    ok: bool
    message: str  # the agent's final message
    cost_usd: float | None


@dataclass
class Agent:
    """The agent that runs the task: everything later steps need to know about it."""

    name: str  # `claude` or `codex`
    model: str
    effort: str
    command: list[str]  # <agent-command>, with the task's permissions
    co_author: str  # <co-author>

    def narrate(self, event: dict) -> None:
        """Show one event of the agent's output as a line of progress."""
        if self.name == "claude" and event.get("type") == "assistant":
            for block in event.get("message", {}).get("content", []):
                if block.get("type") == "text" and block.get("text", "").strip():
                    info(block["text"].strip())
                elif block.get("type") == "tool_use":
                    arg = block.get("input", {})
                    detail = str(arg.get("command") or arg.get("file_path") or arg.get("pattern") or "")
                    info(_paint("2", f"-> {block.get('name')} {detail.splitlines()[0][:100] if detail else ''}"))
        elif self.name == "codex" and event.get("type") == "item.completed":
            item = event.get("item", {})
            if item.get("type") == "agent_message":
                info(item.get("text", "").strip())
            elif item.get("type") == "command_execution":
                info(_paint("2", f"-> {str(item.get('command', ''))[:100]}"))

    def outcome(self, events: list[dict]) -> tuple[bool, str, float | None]:
        """Whether the last event reports success, the final message, and the cost if reported."""
        last = events[-1] if events else {}
        if self.name == "claude":
            ok = last.get("type") == "result" and last.get("is_error") is False
            return ok, (last.get("result") or "").strip(), last.get("total_cost_usd")
        messages = [
            e["item"].get("text", "") for e in events
            if e.get("type") == "item.completed" and e.get("item", {}).get("type") == "agent_message"
        ]
        return last.get("type") == "turn.completed", (messages[-1] if messages else "").strip(), None

    def run(self, clone: Path, prompt: str, log: Path) -> AgentRun:
        """Run the agent in `clone`, prompt on standard input, showing progress and saving every
        line it prints to `log`."""
        print(_paint("2", "    $ " + " ".join(self.command) + " < prompt"), flush=True)
        info(f"log: {log}")
        log.parent.mkdir(parents=True, exist_ok=True)
        events: list[dict] = []
        with log.open("w") as saved, subprocess.Popen(
            self.command, cwd=clone, text=True, stdin=subprocess.PIPE, stdout=subprocess.PIPE
        ) as proc:
            assert proc.stdin and proc.stdout
            proc.stdin.write(prompt)
            proc.stdin.close()
            for line in proc.stdout:
                saved.write(line)
                try:
                    event = json.loads(line)
                except json.JSONDecodeError:
                    continue
                events.append(event)
                self.narrate(event)
        ok, message, cost = self.outcome(events)
        return AgentRun(proc.returncode == 0 and ok, message, cost)



###################
# 6. Finding the model to run the code on
###################
# Input data and models
AGENTS = ("claude", "codex")
DEFAULT_MODELS = {"claude": "claude-opus-5-5", "codex": "gpt-6.1-sol"}
EFFORTS = ("low", "medium", "high", "xhigh", "max")
DEFAULT_EFFORT = "high"
# Claude

CLAUDE_PERMISSIONS = [
    "--permission-mode", "acceptEdits",
    "--allowedTools", "Read", "Edit", "Write", "Glob", "Grep",
    "Bash(lake build:*)",
    "Bash(lake env lean:*)",
    # The checks AGENTS.md lists under "Before you finish".
    "Bash(lake exe cache get:*)",
    "Bash(lake exe lint_all:*)",
    "Bash(lake exe theorem_lint:*)",
    "Bash(lake exe forMathlib_lint:*)",
    "Bash(./scripts/lint/required/lint-style.sh:*)",
    "Bash(lake exe module_doc_lint:*)",
    "Bash(lake exe auxillary_script_test:*)",
    "Bash(lake exe runPhyslibAlphaLinters:*)",
    "Bash(lake exe noAlphaImports:*)",
    "Bash(lake exe alphaFileImports:*)",
    "Bash(./scripts/lint/required/alpha/alphaPythonLinters.sh:*)",
    # Read-only git, and committing.
    "Bash(git diff:*)",
    "Bash(git status:*)",
    "Bash(git log:*)",
    "Bash(git show:*)",
    "Bash(git add:*)",
    "Bash(git commit:*)",
]
def claude_agent(model: str | None, effort: str) -> Agent:
    """Claude Code as the agent, once it is checked to be installed and logged in."""
    run(["claude", "--version"], capture=True)
    result = run(["claude", "auth", "status"], capture=True, check=False)
    try:
        status = json.loads(result.stdout)
    except json.JSONDecodeError:
        status = {}
    if not status.get("loggedIn"):
        raise WorkerError("Claude Code is not logged in; run `claude auth login`")
    pays = "a subscription" if status.get("authMethod") == "claude.ai" else "an API key"
    info(f"tokens will be spent by {status.get('email') or 'this account'}, through {pays}")

    model = model or DEFAULT_MODELS["claude"]
    command = [
        "claude", "-p", "--model", model, "--effort", effort, "--output-format", "stream-json", "--verbose",
        *CLAUDE_PERMISSIONS,
    ]
    # <co-author>: `claude-opus-5-5` gives
    # `Co-authored-by: Claude Opus 5.5 <no-reply+claude-opus-5-5@anthropic.com>`.
    match = re.fullmatch(r"claude-([a-z]+)-(\d+)(?:-(\d+))?", model)
    if match:
        version = match[2] + (f".{match[3]}" if match[3] else "")
        co_author = f"Co-authored-by: Claude {match[1].title()} {version} <no-reply+{model}@anthropic.com>"
    else:
        co_author = f"Co-authored-by: {model}"
    return Agent("claude", model, effort, command, co_author)

# Codex

CODEX_PERMISSIONS = ["--sandbox", "workspace-write"]

def codex_agent(model: str | None, effort: str) -> Agent:
    """Codex as the agent, once it is checked to be installed and logged in."""
    run(["codex", "--version"], capture=True)
    info(output(["codex", "login", "status"]))

    model = model or DEFAULT_MODELS["codex"]
    command = ["codex", "exec", "--json", "--model", model, "-c", f'model_reasoning_effort="{effort}"', *CODEX_PERMISSIONS, "-"]
    # <co-author>: the email address for models other than Claude is still to be decided.
    return Agent("codex", model, effort, command, f"Co-authored-by: {model}")

# Choosing the model
def choose_agent(requested: str | None, model: str | None, effort: str) -> Agent:
    """The first agent, of the one requested or of claude then codex, whose checks pass."""
    makers = {"claude": claude_agent, "codex": codex_agent}
    failures = []
    for name in [requested] if requested else list(AGENTS):
        try:
            agent = makers[name](model, effort)
        except WorkerError as error:
            failures.append(f"{name}: {error}")
            continue
        info(f"agent: {agent.name}, model: {agent.model}, effort: {agent.effort}")
        return agent
    raise WorkerError("no agent passed its checks:\n" + "\n".join(failures))


###################
# 7. Determine the task
###################
# - Read the config, and the skill of each task it lists, from upstream master, or from
#   <path> with `--tasks-from <path>`:
#   `git -C <save-location>/physlib show upstream/master:scripts/worker/physlibAlpha_worker.toml`
#   `git -C <save-location>/physlib show upstream/master:.agents/skills/<task>/SKILL.md`
# - The task, <task>, is the one the user names, otherwise the config's `default`. It must be
#   `custom`, or be listed in the config and have a skill; otherwise stop, and tell the user
#   which tasks there are.


@dataclass
class Task:
    """The task to run: its name, <prompt>, and the PR's <title>."""

    name: str
    prompt: str  # <prompt>
    title: str  # <title>


def read_task_file(clone: Path, tasks_from: Path | None, path: str) -> str | None:
    """`path` from upstream master, or from the checkout `tasks_from`; None if it does not exist."""
    if tasks_from is not None:
        local = tasks_from / path
        return local.read_text() if local.is_file() else None
    result = run(["git", "-C", str(clone), "show", f"upstream/{BASE_BRANCH}:{path}"], capture=True, check=False)
    return result.stdout if result.returncode == 0 else None


def skill_path(name: str) -> str:
    """Where the skill of the task `name` is."""
    return f".agents/skills/{name}/SKILL.md"


def skill_prompt(skill: str) -> str:
    """The text of a SKILL.md after its frontmatter (the lines between the first two `---`)."""
    lines = skill.splitlines()
    if lines and lines[0].strip() == "---":
        end = next((i for i, line in enumerate(lines[1:], 1) if line.strip() == "---"), 0)
        lines = lines[end + 1 :]
    return "\n".join(lines).strip()


def custom_title(user_input: str) -> str:
    """The PR title of a custom task: `PhyslibAlpha: ` and the input's first line, cut to 72."""
    first_line = user_input.strip().splitlines()[0] if user_input.strip() else ""
    return f"{LIBRARY}: {first_line[:72]}"


def determine_task(clone: Path, tasks_from: Path | None, requested: str | None, user_input: str | None) -> Task:
    """The task the user names, or the config's default; `custom`, or one listed with a skill."""
    config_text = read_task_file(clone, tasks_from, CONFIG)
    if config_text is None:
        raise WorkerError(f"there is no {CONFIG} in {tasks_from or 'upstream master'}")
    try:
        config = tomllib.loads(config_text)
    except tomllib.TOMLDecodeError as error:
        raise WorkerError(f"{CONFIG} is not valid TOML: {error}") from None
    listed = config.get("tasks", {})
    skills = {name: read_task_file(clone, tasks_from, skill_path(name)) for name in listed}
    name = requested or str(config.get("default", ""))
    if name == "custom":
        if not user_input:
            raise WorkerError('the custom task needs its input: custom "<input>"')
        return Task("custom", user_input, custom_title(user_input))
    if user_input:
        raise WorkerError(f"only the custom task takes an input, not {name}")
    skill = skills.get(name)
    if skill is None or "title" not in listed[name]:
        available = ["custom", *sorted(n for n in listed if skills[n] is not None and "title" in listed[n])]
        raise WorkerError(f"there is no task {name!r}; the tasks are: {', '.join(available)}")
    return Task(name, skill_prompt(skill), listed[name]["title"])


###################
# 8. Running the task
###################
# - Get the build cache, so that the agent's builds and the checks below only compile what
#   changed. This fetches Mathlib's prebuilt files and Physlib's own, PhyslibAlpha's included:
#   `lake exe get_cache`
#   (run in `<save-location>/physlib`, as are all commands below.)
# - Write the prompt, <prompt>: the text of the task's skill after its frontmatter; for
#   `custom`, the user's input, word for word.
# - Run <agent-command>, sending the prompt on its standard input. Show the user its progress,
#   and save every line it prints to
#   `<save-location>/logs/<time>-<task>.jsonl`.
# - Check the agent finished: it must exit with 0, and its last event must report success (as
#   step 5 describes for each agent). If it failed, stop; the clone is left as it is, for the
#   user to look at.
# - Check the change, without relying on what the agent reports. The change is everything
#   that differs from upstream/master, whether the agent committed it or not:
#   - The agent stayed on <branch>, and only added commits to it. The first prints <branch>;
#     the second fails if upstream/master is not an ancestor of what is checked out:
#     `git branch --show-current`
#     `git merge-base --is-ancestor upstream/master HEAD`
#   - Which files changed. The first lists the files changed since upstream/master, in commits
#     or not, with a rename listed as a deletion and an addition; the second lists the new
#     files not yet added. If none changed, tell the user the agent's final message and go to
#     step 10:
#     `git diff --name-status --no-renames upstream/master`
#     `git ls-files --others --exclude-standard`
#   - Only files in `PhyslibAlpha/` and `PhyslibAlpha.lean` changed, and none was deleted.
#   - No `sorry`, `admit`, `axiom` or `native_decide` was added.
#   - PhyslibAlpha builds:
#     `lake build PhyslibAlpha`
#   - The PhyslibAlpha linters that AGENTS.md lists pass (`alphaFileImports` also checks that
#     `PhyslibAlpha.lean` imports any new file):
#     `lake exe module_doc_lint`
#     `./scripts/lint/required/alpha/alphaPythonLinters.sh`
#     `lake exe runPhyslibAlphaLinters`
#     `lake exe alphaFileImports`
#     `lake exe noAlphaImports`
#   If any check fails, stop and say which; the clone is left as it is.

ALSO_ALLOWED = (f"{LIBRARY}.lean",)  # the files a task may change, besides those in PhyslibAlpha/
ESCAPE_HATCHES = re.compile(r"\b(sorry|admit|axiom|native_decide)\b")
LINTERS = [
    ["lake", "exe", "module_doc_lint"],
    ["./scripts/lint/required/alpha/alphaPythonLinters.sh"],
    ["lake", "exe", "runPhyslibAlphaLinters"],
    ["lake", "exe", "alphaFileImports"],
    ["lake", "exe", "noAlphaImports"],
]


def run_task(save: Path, task: Task, agent: Agent, branch: str, started: str) -> tuple[AgentRun, Path, bool]:
    """Run the agent on the task, and check its change; the bool says whether anything changed."""
    clone = save / "physlib"
    run(["lake", "exe", "get_cache"], cwd=clone)
    log = save / "logs" / f"{started}-{task.name}.jsonl"
    result = agent.run(clone, task.prompt, log)
    if not result.ok:
        raise WorkerError(f"the agent did not finish successfully; see {log}. The clone {clone} is left as it is")
    changed = check_change(clone, branch)
    if not changed:
        info("nothing changed; the agent's final message was:")
        info(result.message)
    return result, log, changed


def check_branch(clone: Path, branch: str) -> list[str]:
    """Problems if the agent left <branch>, or rewrote it rather than adding commits."""
    problems = []
    current = output(["git", "branch", "--show-current"], cwd=clone)
    if current != branch:
        problems.append(f"the agent left the branch {branch} (now on {current or 'a detached HEAD'})")
    ancestor = run(["git", "merge-base", "--is-ancestor", f"upstream/{BASE_BRANCH}", "HEAD"], cwd=clone, check=False)
    if ancestor.returncode != 0:
        problems.append(f"upstream/{BASE_BRANCH} is no longer an ancestor of the branch")
    return problems


def changed_files(clone: Path) -> list[tuple[str, str]]:
    """Each file changed since upstream/master, committed or not, as (status, path).

    The status is git's letter: `A` added, `M` modified, `D` deleted; a rename is a `D` and an `A`.
    """
    diff = run(["git", "diff", "--name-status", "--no-renames", f"upstream/{BASE_BRANCH}"], cwd=clone, capture=True).stdout
    new = run(["git", "ls-files", "--others", "--exclude-standard"], cwd=clone, capture=True).stdout
    # Each line of the diff is the status letter, a tab and the path.
    entries = [tuple(line.split("\t", 1)) for line in diff.splitlines()]
    return [(status, path) for status, path in entries] + [("A", path) for path in new.splitlines()]


def at_upstream(clone: Path, path: str) -> str:
    """`path` as it is on upstream/master; empty if it is new."""
    result = run(["git", "show", f"upstream/{BASE_BRANCH}:{path}"], cwd=clone, capture=True, check=False, quiet=True)
    return result.stdout if result.returncode == 0 else ""


def escape_hatch_problems(clone: Path, changed: list[str]) -> list[str]:
    """The changed Lean files with more uses of sorry, admit, axiom or native_decide than before."""
    problems = []
    for path in changed:
        if path.endswith(".lean") and (clone / path).is_file():
            added = len(ESCAPE_HATCHES.findall((clone / path).read_text())) - len(
                ESCAPE_HATCHES.findall(at_upstream(clone, path))
            )
            if added > 0:
                problems.append(f"{path}: {added} new use(s) of sorry, admit, axiom or native_decide")
    return problems


def check_change(clone: Path, branch: str) -> bool:
    """Check the change without relying on what the agent reports. False when nothing changed."""
    problems = check_branch(clone, branch)
    if problems:
        raise WorkerError("the change failed its checks:\n" + "\n".join(problems))
    entries = changed_files(clone)
    if not entries:
        return False
    changed = [path for _, path in entries]
    info("changed: " + ", ".join(changed))
    for status, path in entries:
        if status == "D":
            problems.append(f"deleted or renamed: {path}")
        elif not (path.startswith(f"{LIBRARY}/") or path in ALSO_ALLOWED):
            problems.append(f"changed a file outside {LIBRARY}: {path}")
    problems += escape_hatch_problems(clone, changed)
    if problems:
        raise WorkerError("the change failed its checks:\n" + "\n".join(problems))
    run(["lake", "build", LIBRARY], cwd=clone)
    for linter in LINTERS:
        run(linter, cwd=clone)
    return True


###################
# 9. Creating the PR
###################
# Nothing in the PR is written by the AI: its title comes from a fixed template, and its
# description holds only the model and the prompt.
# - Commit what the agent left uncommitted, if anything (the first prints nothing if there is
#   none), with <title> (below) followed by a blank line and <co-author>:
#   `git status --porcelain`
#   `git add --all`
#   `git commit --file -`
# - Push the branch to the fork:
#   `git push origin <branch>`
# - Make the title, <title>:
#   - a task from the config: its `title` there;
#   - `custom`: `PhyslibAlpha: ` followed by the first line of the user's input, cut to 72
#     characters.
# - Make the description, <body>: the model, then the prompt exactly as sent, in a code block:
#
#       Made by physlibAlpha-worker.
#
#       Model: <model> (<agent>, effort <effort>)
#
#       Prompt:
#
#       ```
#       <prompt>
#       ```
#
# - Open the PR from the fork's branch into Physlib's master, with <body> sent on standard
#   input. This prints the PR's address, <pr-url>:
#   `gh pr create --repo leanprover-community/physlib --base master --head <login>:<branch> --title <title> --body-file -`


def open_pr(save: Path, fork: str, branch: str, task: Task, agent: Agent) -> str:
    """Commit what is left, push <branch>, and open the PR; return <pr-url>."""
    clone = save / "physlib"
    login = fork.split("/")[0]  # the fork is <login>/<name>
    if output(["git", "status", "--porcelain"], cwd=clone):
        run(["git", "add", "--all"], cwd=clone)
        run(["git", "commit", "--file", "-"], cwd=clone, stdin_text=f"{task.title}\n\n{agent.co_author}\n")
    run(["git", "push", "origin", branch], cwd=clone)
    body = (
        f"Made by {NAME}.\n\n"
        f"Model: {agent.model} ({agent.name}, effort {agent.effort})\n\n"
        f"Prompt:\n\n```\n{task.prompt}\n```\n"
    )
    result = run(
        ["gh", "pr", "create", "--repo", UPSTREAM, "--base", BASE_BRANCH, "--head", f"{login}:{branch}",
         "--title", task.title, "--body-file", "-"],
        cwd=clone, capture=True, stdin_text=body,
    )
    return result.stdout.strip().splitlines()[-1]


###################
# 10. Clean up
###################
# - After a successful run, leave the branch and delete it from the clone. It lives on in the
#   fork, which the PR is made from:
#   `git switch --detach upstream/master`
#   `git branch -D <branch>`
# - After a failed or interrupted run (including Ctrl-C), leave the clone as it is, so the
#   user can look at what the agent did; step 4 of the next run throws it away, branch included.
# - Keep the `.lake` build cache and the logs. Do not delete the branch on the fork: the PR
#   needs it.
# - Tell the user what happened: the task, the agent and model, the cost if the
#   agent reports one (for `claude`, `total_cost_usd` in its last event), the log file, and
#   <pr-url> from step 9.


def clean_up(
    save: Path, branch: str, task: Task, agent: Agent, result: AgentRun, log: Path, pr_url: str | None
) -> None:
    """Delete <branch> from the clone, and tell the user what happened."""
    clone = save / "physlib"
    run(["git", "switch", "--detach", f"upstream/{BASE_BRANCH}"], cwd=clone)
    run(["git", "branch", "-D", branch], cwd=clone)
    info(f"task: {task.name}")
    info(f"agent: {agent.name}, model: {agent.model}")
    if result.cost_usd is not None:
        info(f"cost: ${result.cost_usd:.2f}")
    info(f"log: {log}")
    info(f"PR: {pr_url}" if pr_url else "PR: none, as nothing changed")


###################
# 11. The whole run, and the command line
###################


def work(args: argparse.Namespace) -> int:
    """Run the steps, one after the other."""
    started = datetime.now(timezone.utc).strftime("%Y%m%d-%H%M%S")
    tasks_from = Path(args.tasks_from).expanduser().resolve() if args.tasks_from else None

    step("1. Determine the save location")
    save = save_location()
    info(str(save))

    step("2. Determine if a fork exists and if not create one")
    fork = ensure_fork()

    step("3. Determine if a clone already exists, and if not make one")
    ensure_clone(save, fork)

    step("4. Create a new branch based on upstream/master")
    branch = create_branch(save, started)

    step("6. Finding the model to run the code on")
    agent = choose_agent(args.agent, args.model, args.effort)

    step("7. Determine the task")
    task = determine_task(save / "physlib", tasks_from, args.task, args.input)
    info(f"task: {task.name}" + (f" (from {tasks_from})" if tasks_from else ""))

    step("8. Running the task")
    result, log, changed = run_task(save, task, agent, branch, started)

    pr_url = None
    if changed:
        step("9. Creating the PR")
        pr_url = open_pr(save, fork, branch, task, agent)

    step("10. Clean up")
    clean_up(save, branch, task, agent, result, log, pr_url)
    return 0


def parser() -> argparse.ArgumentParser:
    """The command line: the task, its input for `custom`, and the options."""
    top = argparse.ArgumentParser(prog=NAME, description="Run one task on PhyslibAlpha with an AI agent, and open a PR.")
    top.add_argument(
        "task", nargs="?",
        help=f"a task listed in {CONFIG}, or `custom` (default: the default task listed there)",
    )
    top.add_argument("input", nargs="?", help="for `custom` only: the task, given to the agent word for word")
    top.add_argument("--agent", choices=AGENTS, help="claude or codex (default: claude, then codex if it fails)")
    top.add_argument("--model", help="a full model ID; needs --agent (default: claude-opus-5-5 / gpt-6.1-sol)")
    top.add_argument("--effort", choices=EFFORTS, default=DEFAULT_EFFORT, help="default: high")
    top.add_argument(
        "--tasks-from", metavar="PATH",
        help="read the tasks from the Physlib checkout at PATH instead of upstream master, to test them",
    )
    return top


def main(argv: list[str] | None = None) -> int:
    """Parse the command line and run the worker, reporting a failure rather than raising it."""
    top = parser()
    args = top.parse_args(argv)
    if args.model and not args.agent:
        top.error("--model needs --agent, since a model belongs to one agent")
    try:
        return work(args)
    except WorkerError as error:
        print(_paint("31", f"\nerror: {error}"), file=sys.stderr)
        return 1
    except KeyboardInterrupt:
        print("\ninterrupted; the clone is left as it is", file=sys.stderr)
        return 130


if __name__ == "__main__":
    raise SystemExit(main())
