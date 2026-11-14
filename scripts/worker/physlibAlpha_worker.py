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

       default = "physlibalpha-next-step"

       [tasks.physlibalpha-next-step]
       title = "feat(PhyslibAlpha): add a definition expanding PhyslibAlpha"

       [tasks.physlibalpha-align-with-handbook]
       title = "refactor(PhyslibAlpha): tidy a PhyslibAlpha file"

       [tasks.physlibalpha-add]
       title = "feat(PhyslibAlpha): add a given result to PhyslibAlpha"
       input = true

   A task with `input = true` must be given an input, `<task> "<input>"`, which is put before
   the skill's text in the prompt, as the input `X`; other tasks take none. The tasks are read
   from upstream master (step 8), or, with `--tasks-from <path>`, from the Physlib checkout at
   <path>, to test changes to them.
-- custom "<input>": This runs the a custom task on PhyslibAlpha.

## How it works

The file is in numbered sections, which the worker runs one after the other (sections 5 and 7
only define the agents and tasks that the later steps use):

1. Determine the save location.
2. Determine if a fork exists and if not create one.
3. Determine if a clone already exists, and if not make one.
4. Create a new branch based on upstream/master.
5. Infrastructure for Agents.
6. Finding the model to run the code on.
7. Infrastructure for Tasks.
8. Reading the task.
9. Running the task.
10. Safety checks.
11. Creating the PR.
12. Handbook alignment report.
13. Clean up.

## Locally testing

From the root of a Physlib checkout, run the file directly with Python (3.11 or later; the script
uses only Python's standard library):

    python3 scripts/worker/physlibAlpha_worker.py physlibalpha-align-with-handbook

To test changes to the tasks or the config before they reach master, read them from your
checkout instead:

    python3 scripts/worker/physlibAlpha_worker.py physlibalpha-align-with-handbook --tasks-from .

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
from collections.abc import Callable
from dataclasses import dataclass, replace
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


def fenced(text: str) -> str:
    """`text` in a Markdown code block, fenced with more backticks than any run of them inside it."""
    fence = "```"
    while fence in text:
        fence += "`"
    return f"{fence}\n{text}\n{fence}"

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
    review_command: Callable[[Path], list[str]]  # <agent-command> for a review, writing only in a folder
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


def claude_review_permissions(work: Path) -> list[str]:
    """For running the skill handbook-alignment: reading, subagents, writing only in `work`, and
    the commands the skill uses, none of which builds or posts."""
    # A rule's absolute path starts `//`, and is in POSIX form: on Windows, `C:\x` is `/c/x`. An
    # `Edit` rule covers every tool that writes files, and redirecting a command's output.
    path = work.as_posix()
    if re.match(r"[A-Za-z]:/", path):
        path = f"/{path[0].lower()}{path[2:]}"
    return [
        "--allowedTools", "Read", "Glob", "Grep", "Agent", f"Edit(/{path}/**)",
        "Bash(mkdir:*)",
        "Bash(git fetch:*)",
        "Bash(git worktree:*)",
        "Bash(git diff:*)",
        "Bash(git log:*)",
        "Bash(git show:*)",
        "Bash(git ls-files:*)",
        "Bash(git merge-base:*)",
        "Bash(gh pr view:*)",
        "Bash(gh pr diff:*)",
        "Bash(python3 .agents/skills/handbook-alignment/report.py:*)",
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
    base = ["claude", "-p", "--model", model, "--effort", effort, "--output-format", "stream-json", "--verbose"]
    # <co-author>: `claude-opus-5-5` gives
    # `Co-authored-by: Claude Opus 5.5 <no-reply+claude-opus-5-5@anthropic.com>`.
    match = re.fullmatch(r"claude-([a-z]+)-(\d+)(?:-(\d+))?", model)
    if match:
        version = match[2] + (f".{match[3]}" if match[3] else "")
        co_author = f"Co-authored-by: Claude {match[1].title()} {version} <no-reply+{model}@anthropic.com>"
    else:
        co_author = f"Co-authored-by: {model}"
    return Agent(
        "claude", model, effort, [*base, *CLAUDE_PERMISSIONS],
        lambda work: [*base, *claude_review_permissions(work)], co_author,
    )

# Codex

CODEX_PERMISSIONS = ["--sandbox", "workspace-write"]


def codex_review_permissions(work: Path) -> list[str]:
    """For running the skill handbook-alignment: writing in the clone and in `work`, with the
    network, which the skill's `git fetch` and `gh` need."""
    return ["--sandbox", "workspace-write", "--add-dir", str(work), "-c", "sandbox_workspace_write.network_access=true"]


def codex_agent(model: str | None, effort: str) -> Agent:
    """Codex as the agent, once it is checked to be installed and logged in."""
    run(["codex", "--version"], capture=True)
    info(output(["codex", "login", "status"]))

    model = model or DEFAULT_MODELS["codex"]
    base = ["codex", "exec", "--json", "--model", model, "-c", f'model_reasoning_effort="{effort}"']
    # <co-author>: the email address for models other than Claude is still to be decided.
    return Agent(
        "codex", model, effort, [*base, *CODEX_PERMISSIONS, "-"],
        lambda work: [*base, *codex_review_permissions(work), "-"],
        f"Co-authored-by: {model}",
    )

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
# 7. Infrastructure for Tasks
###################
# We give the underlying infrastructure for tasks

@dataclass
class Task:
    """The task to run: its name, <prompt>, and the PR's <title>."""
    name: str
    prompt: str  # <prompt>
    title: str  # <title>


###################
# 8. Reading the task
###################
# Returns `Task` using physlibAlpha_worker.toml within the clone, in the
# upstream/master branch, unless otherwise specified.

def determine_task(clone: Path, tasks_from: Path | None, requested: str | None, user_input: str | None) -> Task:
    """The task the user names, or the config's default; `custom`, or one listed with a skill."""
    def read(path: str) -> str | None:
        """`path` from upstream master, or from the checkout `tasks_from`; None if it does not exist."""
        if tasks_from is not None:
            local = tasks_from / path
            return local.read_text() if local.is_file() else None
        result = run(["git", "-C", str(clone), "show", f"upstream/{BASE_BRANCH}:{path}"], capture=True, check=False)
        return result.stdout if result.returncode == 0 else None
    # A custom task: the prompt is the input, the title `PhyslibAlpha: ` and its first line, cut to 72.
    if requested == "custom":
        if not user_input:
            raise WorkerError('the custom task needs its input: custom "<input>"')
        first_line = (user_input.strip().splitlines() or [""])[0]
        return Task("custom", user_input, f"{LIBRARY}: {first_line[:72]}")
    # A listed task: the config gives the default task and the PR title of each task.
    config_text = read(CONFIG)
    if config_text is None:
        raise WorkerError(f"there is no {CONFIG} in {tasks_from or 'upstream master'}")
    try:
        config = tomllib.loads(config_text)
    except tomllib.TOMLDecodeError as error:
        raise WorkerError(f"{CONFIG} is not valid TOML: {error}") from None
    name = requested or str(config.get("default", ""))
    listed = config.get("tasks", {})
    titles = {n: task["title"] for n, task in listed.items() if "title" in task}
    skills = {n: read(f".agents/skills/{n}/SKILL.md") for n in titles}
    skill = skills.get(name)
    if skill is None:
        available = ["custom", *sorted(n for n, s in skills.items() if s is not None)]
        raise WorkerError(f"there is no task {name!r}; the tasks are: {', '.join(available)}")
    # A task takes an input exactly when the config says `input = true` for it.
    takes_input = listed[name].get("input") is True
    if takes_input and not user_input:
        raise WorkerError(f'the task {name} needs its input: {name} "<input>"')
    if user_input and not takes_input:
        raise WorkerError(f"the task {name} takes no input")
    # The prompt is the input, if any, then the skill after its frontmatter, which sits between
    # the first two `---`.
    if skill.startswith("---"):
        skill = skill.split("---", 2)[-1]
    prompt = skill.strip()
    if user_input:
        prompt = f"The input `X`:\n\n{fenced(user_input)}\n\n{prompt}"
    return Task(name, prompt, titles[name])


###################
# 9. Running the task
###################
# Running the task

def run_task(save: Path, task: Task, agent: Agent, started: str) -> tuple[AgentRun, Path, bool]:
    """Run the agent on the task; the bool says whether anything changed."""
    clone = save / "physlib"
    run(["lake", "exe", "get_cache"], cwd=clone)
    log = save / "logs" / f"{started}-{task.name}.jsonl"
    result = agent.run(clone, task.prompt, log)
    if not result.ok:
        raise WorkerError(f"the agent did not finish successfully; see {log}. The clone {clone} is left as it is")
    changed = bool(
        output(["git", "rev-list", f"upstream/{BASE_BRANCH}..HEAD"], cwd=clone)
        or output(["git", "status", "--porcelain"], cwd=clone)
    )
    if not changed:
        info("nothing changed; the agent's final message was:")
        info(result.message)
    return result, log, changed


###################
# 10. Safety checks
###################
# This does safety checks on a PR to make sure it is valid.

def safety_checks(clone: Path, branch: str) -> None:
    """Check the agent's change without relying on what it reports; raise WorkerError if it fails.

    The change is everything that differs from upstream/master, whether committed or not.
    """
    upstream = f"upstream/{BASE_BRANCH}"
    problems = []
    # The agent stayed on <branch>, and only added commits to it.
    current = output(["git", "branch", "--show-current"], cwd=clone)
    if current != branch:
        problems.append(f"the agent left the branch {branch} (now on {current or 'a detached HEAD'})")
    if run(["git", "merge-base", "--is-ancestor", upstream, "HEAD"], cwd=clone, check=False).returncode != 0:
        problems.append(f"{upstream} is no longer an ancestor of the branch")
    # The changed files, as (status, path). Each line of the diff is git's status letter (`A`
    # added, `M` modified, `D` deleted; a rename is a `D` and an `A`), a tab and the path; the
    # files not yet added are new.
    diff = output(["git", "diff", "--name-status", "--no-renames", upstream], cwd=clone)
    new = output(["git", "ls-files", "--others", "--exclude-standard"], cwd=clone)
    changed = [line.split("\t", 1) for line in diff.splitlines()] + [["A", path] for path in new.splitlines()]
    escape_hatches = re.compile(r"\b(sorry|admit|axiom|native_decide)\b")
    for status, path in changed:
        # Only files in PhyslibAlpha/ and PhyslibAlpha.lean changed, and none was deleted.
        if status == "D":
            problems.append(f"deleted or renamed: {path}")
            continue
        if not (path.startswith(f"{LIBRARY}/") or path == f"{LIBRARY}.lean"):
            problems.append(f"changed a file outside {LIBRARY}: {path}")
        # No sorry, admit, axiom or native_decide was added.
        if path.endswith(".lean") and (clone / path).is_file():
            before = run(["git", "show", f"{upstream}:{path}"], cwd=clone, capture=True, check=False, quiet=True)
            added = len(escape_hatches.findall((clone / path).read_text())) - len(
                escape_hatches.findall(before.stdout if before.returncode == 0 else "")
            )
            if added > 0:
                problems.append(f"{path}: {added} new use(s) of sorry, admit, axiom or native_decide")
    if problems:
        raise WorkerError("the change failed its checks:\n" + "\n".join(problems))
    # PhyslibAlpha builds, and the PhyslibAlpha linters that AGENTS.md lists pass
    # (`alphaFileImports` also checks that PhyslibAlpha.lean imports any new file).
    run(["lake", "build", LIBRARY], cwd=clone)
    for linter in [
        ["lake", "exe", "module_doc_lint"],
        ["./scripts/lint/required/alpha/alphaPythonLinters.sh"],
        ["lake", "exe", "runPhyslibAlphaLinters"],
        ["lake", "exe", "alphaFileImports"],
        ["lake", "exe", "noAlphaImports"],
    ]:
        run(linter, cwd=clone)


###################
# 11. Creating the PR
###################
# Opens the PR

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
        f"Prompt:\n\n{fenced(task.prompt)}\n"
    )
    result = run(
        ["gh", "pr", "create", "--repo", UPSTREAM, "--base", BASE_BRANCH, "--head", f"{login}:{branch}",
         "--title", task.title, "--body-file", "-"],
        cwd=clone, capture=True, stdin_text=body,
    )
    return result.stdout.strip().splitlines()[-1]


###################
# 12. Handbook alignment report
###################
# Runs the skill `.agents/skills/handbook-alignment` on the PR, in its non-interactive mode, and
# posts the report it makes as a comment on the PR.
def handbook_alignment(save: Path, tasks_from: Path | None, pr_url: str, agent: Agent, started: str) -> str | None:
    """Run the skill handbook-alignment on the PR, and post its report there; return the
    comment's URL, or None if no report was posted."""
    clone = save / "physlib"
    folder = save / "reviews" / started
    try:
        skill = ((tasks_from or clone) / ".agents/skills/handbook-alignment/SKILL.md").read_text()
        if skill.startswith("---"):
            skill = skill.split("---", 2)[-1]  # the text after the frontmatter
        folder.mkdir(parents=True)
        request = f"#{pr_url.rstrip('/').split('/')[-1]} non-interactive {folder}"
        reviewer = replace(agent, command=agent.review_command(folder))
        result = reviewer.run(clone, f"{skill.strip()}\n\nThe request: {request}\n", folder / "review.jsonl")
        report_file = folder / "report.md"
        if not (result.ok and report_file.is_file()):
            raise WorkerError(f"the skill made no report; its final message was:\n{result.message}")
        report = report_file.read_text().rstrip()
        report += f"\n\n<sub>Made by {NAME}, with {agent.model} ({agent.name}, effort {agent.effort}).</sub>\n"
        posted = run(["gh", "pr", "comment", pr_url, "--body-file", "-"], capture=True, stdin_text=report)
    except (WorkerError, OSError) as error:
        info(f"no handbook alignment report was posted: {error}")
        return None
    url = posted.stdout.strip().splitlines()[-1]
    info(f"report: {url}" + (f" (cost: ${result.cost_usd:.2f})" if result.cost_usd is not None else ""))
    return url


###################
# 13. Clean up
###################
# Cleaning up the code

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
# 14. The whole run, and the command line
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

    step("8. Reading the task")
    task = determine_task(save / "physlib", tasks_from, args.task, args.input)
    info(f"task: {task.name}" + (f" (from {tasks_from})" if tasks_from else ""))

    step("9. Running the task")
    result, log, changed = run_task(save, task, agent, started)

    pr_url = None
    if changed:
        step("10. Safety checks")
        safety_checks(save / "physlib", branch)

        step("11. Creating the PR")
        pr_url = open_pr(save, fork, branch, task, agent)

        step("12. Handbook alignment report")
        handbook_alignment(save, tasks_from, pr_url, agent, started)

    step("13. Clean up")
    clean_up(save, branch, task, agent, result, log, pr_url)
    return 0


def parser() -> argparse.ArgumentParser:
    """The command line: the task, its input for `custom`, and the options."""
    top = argparse.ArgumentParser(prog=NAME, description="Run one task on PhyslibAlpha with an AI agent, and open a PR.")
    top.add_argument(
        "task", nargs="?",
        help=f"a task listed in {CONFIG}, or `custom` (default: the default task listed there)",
    )
    top.add_argument(
        "input", nargs="?",
        help="for `custom`, the task itself, word for word; for a task with `input = true` in "
        f"{CONFIG}, the input `X` it works on",
    )
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
