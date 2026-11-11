#!/usr/bin/env -S uv run --script
# /// script
# requires-python = ">=3.11"
# dependencies = []
# ///
r"""
# physlibAlpha-worker

This script allows the automation of tasks in PhyslibAlpha, making it easy for people
to donate tokens in a useful and responsable way. This script can be used independently,
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

   The tasks are read from upstream master (step 4), or, with `--tasks-from <path>`, from the
   Physlib checkout at <path>, to test changes to them.
-- custom "<input>": This runs the a custom task on PhyslibAlpha.

## How it works

1. Determine the save location. In order of preference:
   - `$PHYSLIBALPHA_WORKER_HOME`, if set;
   - Linux and macOS: `$XDG_STATE_HOME/physlibAlpha-worker`, defaulting to
     `~/.local/state/physlibAlpha-worker`;
   - Windows: `%LOCALAPPDATA%\physlibAlpha-worker`.
   The clone of Physlib goes in `physlib/` inside it, and logs in `logs/`.
   In the below we call this <save-location>.
2. Determine if a fork exists and if not make one:
   - Find the user's GitHub login:
     `gh api user --jq .login`
   - List the forks the user owns, with the repository each was forked from:
     `gh repo list <login> --fork --limit 1000 --json nameWithOwner,parent`
   - The fork is the one whose parent is `leanprover-community/physlib`.
   - If there is no fork, create one in two steps:
     - Ask GitHub to create the fork. GitHub answers at once with the fork's name, but builds
       the fork in the background, so it may not exist yet. The name is normally
       `<login>/physlib`; if the user already has a repository called `physlib`, GitHub picks
       another (such as `<login>/physlib-1`), so use the name GitHub returns:
       `gh api -X POST repos/leanprover-community/physlib/forks -F default_branch_only=true --jq .full_name`
     - Wait until the fork exists. This command looks the repository up, and fails while GitHub
       is still building it; run it every 5 seconds, for up to 5 minutes, until it succeeds:
       `gh api repos/<fork> --jq .full_name`
3. Determine if a clone already exists, and if not make one. The clone lives in
   `<save-location>/physlib`.
   - If that folder exists, check it is a clone of the fork: this prints the address the clone
     was made from, which must be the fork's, `https://github.com/<fork>.git` (or
     `git@github.com:<fork>.git` if the user has set gh to use SSH):
     `git -C <save-location>/physlib remote get-url origin`
     If it prints anything else, or fails, stop with an error and leave the folder alone.
   - If that folder does not exist, clone the fork into it. Because the fork's parent is
     Physlib, gh names the fork `origin` and adds Physlib as a second remote, `upstream`, which
     the next step branches from:
     `gh repo clone <fork> <save-location>/physlib`
4. Determine the task, and create a branch for it based on upstream/master.
   - Fetch the latest master from Physlib:
     `git -C <save-location>/physlib fetch upstream master`
   - Throw away anything an earlier run left in the clone. `clean` without `-x` keeps the files
     git ignores, so the `.lake` build cache survives:
     `git -C <save-location>/physlib reset --hard`
     `git -C <save-location>/physlib clean -fd`
   - Read the config, and the skill of each task it lists, from upstream master, or from
     <path> with `--tasks-from <path>`:
     `git -C <save-location>/physlib show upstream/master:scripts/worker/physlibAlpha_worker.toml`
     `git -C <save-location>/physlib show upstream/master:.agents/skills/<task>/SKILL.md`
   - The task, <task>, is the one the user names, otherwise the config's `default`. It must be
     `custom`, or be listed in the config and have a skill; otherwise stop, and tell the user
     which tasks there are.
   - The branch is called `physlibAlpha-worker/<task>-<time>`, where `<time>` is when the run
     started, in UTC, as `YYYYMMDD-HHMMSS`; for example
     `physlibAlpha-worker/alpha-align-with-handbook-20261110-143005`. The prefix marks the
     branches the worker made on the fork, and the time makes every name new, so a run never
     collides with an earlier one. Below we call this <branch>.
   - Create the branch from upstream/master and switch to it. The worker later pushes it with
     `git push origin <branch>`, naming the fork explicitly, so it never goes to Physlib:
     `git -C <save-location>/physlib switch --create <branch> upstream/master`
5. Finding the model to run the code on.
   Input, from the user:
   - `--agent`: the program that runs the model: `claude` (Claude Code) or `codex` (OpenAI's
     Codex). If the user gives it, only that agent is tried. If not, `claude` is tried first,
     and `codex` if any of Claude Code's checks below fails.
   - `--model`: a full model ID, which needs `--agent` too, since a model belongs to one agent.
     Not an alias such as `opus`: an alias means whichever model the installed program maps it
     to, which can lag behind (Claude Code 2.1.269 maps `opus` to `claude-opus-5`). Default
     `claude-opus-5-5` for `claude`, `gpt-6.1-sol` for `codex`.
   - `--effort`: `low`, `medium`, `high`, `xhigh` or `max`, default `high`.
   Output, used by the later steps:
   - <agent-command>: the command that starts the agent on a task, without the prompt (sent on
     its standard input) or the task's permissions (added by the step that runs the task).
   - <co-author>: the name credited in the commit the worker makes (step 7), as AGENTS.md asks,
     made from the model ID;
     for `claude-opus-5-5`:
     `Co-authored-by: Claude Opus 5.5 <no-reply+claude-opus-5-5@anthropic.com>`
     For `codex` it names the model ID; the email address is still to be decided.
   Steps, for `--agent claude`:
   - Check Claude Code is installed. This fails if it is not:
     `claude --version`
   - Check Claude Code is logged in. This prints JSON, in which `loggedIn` must be `true`. Tell
     the user whose tokens will be spent: the `email` field gives the account, and `authMethod`
     says how it pays (`claude.ai` for a subscription; otherwise an API key):
     `claude auth status`
   - <agent-command>:
     `claude -p --model <model> --effort <effort> --output-format stream-json --verbose`
   Steps, for `--agent codex`:
   - Check Codex is installed:
     `codex --version`
   - Check Codex is logged in. This prints how it is logged in, and fails if it is not:
     `codex login status`
   - <agent-command>. `--json` prints one JSON event per line, and the final `-` makes Codex
     read the prompt from its standard input:
     `codex exec --json --model <model> -c model_reasoning_effort="<effort>" -`
   If no agent passes its checks, stop and tell the user what failed for each.
6. Running the task.
   - Get the build cache, so that the agent's builds and the checks below only compile what
     changed. This fetches Mathlib's prebuilt files and Physlib's own, PhyslibAlpha's included:
     `lake exe get_cache`
     (run in `<save-location>/physlib`, as are all commands below.)
   - Write the prompt, <prompt>: the text of the task's skill after its frontmatter; for
     `custom`, the user's input, word for word.
   - Add the task's permissions to <agent-command>. Edits are allowed inside the clone, and
     the only commands allowed are builds, the checks that AGENTS.md lists under "Before you
     finish", read-only git, and committing on <branch>:
     - `claude`:
       `--permission-mode acceptEdits --allowedTools Read Edit Write Glob Grep "Bash(lake build:*)" "Bash(lake env lean:*)" "Bash(lake exe cache get:*)" "Bash(lake exe lint_all:*)" "Bash(lake exe theorem_lint:*)" "Bash(lake exe forMathlib_lint:*)" "Bash(./scripts/lint/required/lint-style.sh:*)" "Bash(lake exe module_doc_lint:*)" "Bash(lake exe auxillary_script_test:*)" "Bash(lake exe runPhyslibAlphaLinters:*)" "Bash(lake exe noAlphaImports:*)" "Bash(lake exe alphaFileImports:*)" "Bash(./scripts/lint/required/alpha/alphaPythonLinters.sh:*)" "Bash(git diff:*)" "Bash(git status:*)" "Bash(git log:*)" "Bash(git show:*)" "Bash(git add:*)" "Bash(git commit:*)"`
     - `codex` has no list of allowed commands; its sandbox lets it edit and run commands in
       the clone only. It may keep `.git` read-only, so that Codex cannot commit; step 7 then
       commits its change:
       `--sandbox workspace-write`
   - Run <agent-command> with the permissions, sending the prompt on its standard input. Show
     the user its progress, and save every line it prints to
     `<save-location>/logs/<time>-<task>.jsonl`.
   - Check the agent finished: it must exit with 0, and its last event must report success
     (for `claude`, `"type": "result"` with `"is_error": false`). If it failed, stop; the clone
     is left as it is, for the user to look at.
   - Check the change, without relying on what the agent reports. The change is everything
     that differs from upstream/master, whether the agent committed it or not:
     - The agent stayed on <branch>, and only added commits to it. The first prints <branch>;
       the second fails if upstream/master is not an ancestor of what is checked out:
       `git branch --show-current`
       `git merge-base --is-ancestor upstream/master HEAD`
     - Which files changed. The first lists the files changed since upstream/master, in commits
       or not, with a rename listed as a deletion and an addition; the second lists the new
       files not yet added. If none changed, tell the user the agent's final message and go to
       step 8:
       `git diff --name-status --no-renames upstream/master`
       `git ls-files --others --exclude-standard`
     - Only files in `PhyslibAlpha/` and `PhyslibAlpha.lean` changed, and none was deleted.
     - No `sorry`, `admit`, `axiom` or `native_decide` was added.
     - PhyslibAlpha builds:
       `lake build PhyslibAlpha`
     - The PhyslibAlpha linters that AGENTS.md lists pass (`alphaFileImports` also checks that
       `PhyslibAlpha.lean` imports any new file):
       `lake exe module_doc_lint`
       `./scripts/lint/required/alpha/alphaPythonLinters.sh`
       `lake exe runPhyslibAlphaLinters`
       `lake exe alphaFileImports`
       `lake exe noAlphaImports`
     If any check fails, stop and say which; the clone is left as it is.
7. Creating the PR. Nothing in the PR is written by the AI: its title comes from a fixed
   template, and its description holds only the model and the prompt.
   - Commit what the agent left uncommitted, if anything (the first prints nothing if there is
     none), with <title> (below) followed by a blank line and <co-author>:
     `git status --porcelain`
     `git add --all`
     `git commit --file -`
   - Push the branch to the fork:
     `git push origin <branch>`
   - Make the title, <title>:
     - a task from the config: its `title` there;
     - `custom`: `PhyslibAlpha: ` followed by the first line of the user's input, cut to 72
       characters.
   - Make the description, <body>: the model, then the prompt exactly as sent, in a code block:

         Made by physlibAlpha-worker.

         Model: <model> (<agent>, effort <effort>)

         Prompt:

         ```
         <prompt>
         ```

   - Open the PR from the fork's branch into Physlib's master, with <body> sent on standard
     input. This prints the PR's address, <pr-url>:
     `gh pr create --repo leanprover-community/physlib --base master --head <login>:<branch> --title <title> --body-file -`
8. Clean up.
   - After a successful run, leave the branch and delete it from the clone. It lives on in the
     fork, which the PR is made from:
     `git switch --detach upstream/master`
     `git branch -D <branch>`
   - After a failed or interrupted run (including Ctrl-C), leave the clone as it is, so the
     user can look at what the agent did; step 4 of the next run throws it away.
   - Keep the `.lake` build cache and the logs. Do not delete the branch on the fork: the PR
     needs it.
   - Tell the user what happened: the task, the agent and model, the cost if the
     agent reports one (for `claude`, `total_cost_usd` in its last event), the log file, and
     <pr-url> from step 7.

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


# =============================================================================
# 0. Running commands and reporting progress
# =============================================================================


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


def git(clone: Path, *args: str) -> None:
    """Run `git <args>` in `clone`, echoing it; raise WorkerError when it fails."""
    run(["git", "-C", str(clone), *args])


# =============================================================================
# 1. Determine the save location
# =============================================================================


def save_location() -> Path:
    if home := os.environ.get("PHYSLIBALPHA_WORKER_HOME"):
        return Path(home).expanduser()
    if os.name == "nt":
        local = os.environ.get("LOCALAPPDATA") or str(Path.home() / "AppData" / "Local")
        return Path(local) / NAME
    state = os.environ.get("XDG_STATE_HOME") or str(Path.home() / ".local" / "state")
    return Path(state) / NAME


# =============================================================================
# 2. Determine if a fork exists and if not make one
# =============================================================================


def github_login() -> str:
    return output(["gh", "api", "user", "--jq", ".login"])


def find_fork(login: str) -> str | None:
    """The user's fork of Physlib, found by its parent, so a renamed fork is found too."""
    repos = json.loads(
        output(["gh", "repo", "list", login, "--fork", "--limit", "1000", "--json", "nameWithOwner,parent"])
    )
    for repo in repos:
        parent = repo.get("parent") or {}
        if f"{parent.get('owner', {}).get('login')}/{parent.get('name')}" == UPSTREAM:
            return repo["nameWithOwner"]
    return None


def create_fork() -> str:
    """Ask GitHub for a fork, then wait until GitHub has built it."""
    fork = output(
        ["gh", "api", "-X", "POST", f"repos/{UPSTREAM}/forks", "-F", "default_branch_only=true", "--jq", ".full_name"]
    )
    info(f"waiting for GitHub to build {fork}")
    for _ in range(60):
        if run(["gh", "api", f"repos/{fork}", "--jq", ".full_name"], capture=True, check=False, quiet=True).returncode == 0:
            return fork
        time.sleep(5)
    raise WorkerError(f"GitHub did not finish building the fork {fork} within 5 minutes; try again later")


def ensure_fork() -> tuple[str, str]:
    """The user's login and fork."""
    login = github_login()
    fork = find_fork(login)
    if fork is None:
        info(f"no fork of {UPSTREAM} found; creating one")
        fork = create_fork()
    info(f"fork: {fork}")
    return login, fork


# =============================================================================
# 3. Determine if a clone already exists, and if not make one
# =============================================================================


def ensure_clone(save: Path, fork: str) -> Path:
    clone = save / "physlib"
    if clone.exists():
        result = run(["git", "-C", str(clone), "remote", "get-url", "origin"], capture=True, check=False)
        url = result.stdout.strip()
        if result.returncode != 0 or url not in (f"https://github.com/{fork}.git", f"git@github.com:{fork}.git"):
            raise WorkerError(f"{clone} exists but is not a clone of {fork}; it has been left alone")
    else:
        clone.parent.mkdir(parents=True, exist_ok=True)
        run(["gh", "repo", "clone", fork, str(clone)])
    return clone


# =============================================================================
# 4. Determine the task, and create a branch for it based on upstream/master
# =============================================================================


@dataclass
class Task:
    name: str
    prompt: str  # <prompt>
    title: str  # <title>


def update_clone(clone: Path) -> None:
    git(clone, "fetch", "upstream", BASE_BRANCH)
    git(clone, "reset", "--hard")
    git(clone, "clean", "-fd")


def read_task_file(clone: Path, tasks_from: Path | None, path: str) -> str | None:
    """`path` from upstream master, or from the checkout `tasks_from`; None if it does not exist."""
    if tasks_from is not None:
        local = tasks_from / path
        return local.read_text() if local.is_file() else None
    result = run(["git", "-C", str(clone), "show", f"upstream/{BASE_BRANCH}:{path}"], capture=True, check=False)
    return result.stdout if result.returncode == 0 else None


def skill_path(name: str) -> str:
    return f".agents/skills/{name}/SKILL.md"


def skill_prompt(skill: str) -> str:
    """The text of a SKILL.md after its frontmatter (the lines between the first two `---`)."""
    lines = skill.splitlines()
    if lines and lines[0].strip() == "---":
        end = next((i for i, line in enumerate(lines[1:], 1) if line.strip() == "---"), 0)
        lines = lines[end + 1 :]
    return "\n".join(lines).strip()


def custom_title(user_input: str) -> str:
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


def create_branch(clone: Path, task: str, started: str) -> str:
    branch = f"{NAME}/{task}-{started}"
    git(clone, "switch", "--create", branch, f"upstream/{BASE_BRANCH}")
    return branch


# =============================================================================
# 5. Finding the model to run the code on
# =============================================================================

AGENTS = ("claude", "codex")
DEFAULT_MODELS = {"claude": "claude-opus-5-5", "codex": "gpt-6.1-sol"}
EFFORTS = ("low", "medium", "high", "xhigh", "max")
DEFAULT_EFFORT = "high"


@dataclass
class Agent:
    name: str
    model: str
    effort: str
    command: list[str]  # <agent-command>
    co_author: str  # <co-author>


def check_claude() -> None:
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


def check_codex() -> None:
    run(["codex", "--version"], capture=True)
    info(output(["codex", "login", "status"]))


def agent_command(name: str, model: str, effort: str) -> list[str]:
    if name == "claude":
        return ["claude", "-p", "--model", model, "--effort", effort, "--output-format", "stream-json", "--verbose"]
    return ["codex", "exec", "--json", "--model", model, "-c", f'model_reasoning_effort="{effort}"', "-"]


def co_author(name: str, model: str) -> str:
    """`claude-opus-5-5` gives `Co-authored-by: Claude Opus 5.5 <no-reply+claude-opus-5-5@anthropic.com>`."""
    match = re.fullmatch(r"claude-([a-z]+)-(\d+)(?:-(\d+))?", model)
    if name == "claude" and match:
        version = match[2] + (f".{match[3]}" if match[3] else "")
        return f"Co-authored-by: Claude {match[1].title()} {version} <no-reply+{model}@anthropic.com>"
    # The email address for other models is still to be decided.
    return f"Co-authored-by: {model}"


def choose_agent(requested: str | None, model: str | None, effort: str) -> Agent:
    """The first agent, of the one requested or of claude then codex, whose checks pass."""
    failures = []
    for name in [requested] if requested else list(AGENTS):
        try:
            check_claude() if name == "claude" else check_codex()
        except WorkerError as error:
            failures.append(f"{name}: {error}")
            continue
        model = model or DEFAULT_MODELS[name]
        info(f"agent: {name}, model: {model}, effort: {effort}")
        return Agent(name, model, effort, agent_command(name, model, effort), co_author(name, model))
    raise WorkerError("no agent passed its checks:\n" + "\n".join(failures))


# =============================================================================
# 6. Running the task
# =============================================================================

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
    "Bash(git diff:*)",
    "Bash(git status:*)",
    "Bash(git log:*)",
    "Bash(git show:*)",
    "Bash(git add:*)",
    "Bash(git commit:*)",
]
CODEX_PERMISSIONS = ["--sandbox", "workspace-write"]

# The files a task may change, besides those in PhyslibAlpha/.
ALSO_ALLOWED = (f"{LIBRARY}.lean",)
ESCAPE_HATCHES = re.compile(r"\b(sorry|admit|axiom|native_decide)\b")
LINTERS = [
    ["lake", "exe", "module_doc_lint"],
    ["./scripts/lint/required/alpha/alphaPythonLinters.sh"],
    ["lake", "exe", "runPhyslibAlphaLinters"],
    ["lake", "exe", "alphaFileImports"],
    ["lake", "exe", "noAlphaImports"],
]


def with_permissions(agent: Agent) -> list[str]:
    """<agent-command> with the task's permissions; Codex's final `-` must stay last."""
    if agent.name == "claude":
        return agent.command + CLAUDE_PERMISSIONS
    return agent.command[:-1] + CODEX_PERMISSIONS + agent.command[-1:]


@dataclass
class AgentRun:
    ok: bool
    message: str  # the agent's final message
    cost_usd: float | None


def _narrate(event: dict) -> None:
    """Show one event of the agent's output as a line of progress."""
    if event.get("type") == "assistant":  # claude
        for block in event.get("message", {}).get("content", []):
            if block.get("type") == "text" and block.get("text", "").strip():
                info(block["text"].strip())
            elif block.get("type") == "tool_use":
                arg = block.get("input", {})
                detail = str(arg.get("command") or arg.get("file_path") or arg.get("pattern") or "")
                info(_paint("2", f"-> {block.get('name')} {detail.splitlines()[0][:100] if detail else ''}"))
    elif event.get("type") == "item.completed":  # codex
        item = event.get("item", {})
        if item.get("type") == "agent_message":
            info(item.get("text", "").strip())
        elif item.get("type") == "command_execution":
            info(_paint("2", f"-> {str(item.get('command', ''))[:100]}"))


def _outcome(agent: Agent, events: list[dict]) -> tuple[bool, str, float | None]:
    """Whether the last event reports success, the final message, and the cost if reported."""
    last = events[-1] if events else {}
    if agent.name == "claude":
        ok = last.get("type") == "result" and last.get("is_error") is False
        return ok, (last.get("result") or "").strip(), last.get("total_cost_usd")
    messages = [
        e["item"].get("text", "") for e in events
        if e.get("type") == "item.completed" and e.get("item", {}).get("type") == "agent_message"
    ]
    return last.get("type") == "turn.completed", (messages[-1] if messages else "").strip(), None


def run_agent(clone: Path, agent: Agent, prompt: str, log: Path) -> AgentRun:
    """Run the agent, prompt on standard input, showing progress and saving every line to `log`."""
    cmd = with_permissions(agent)
    print(_paint("2", "    $ " + " ".join(cmd) + " < prompt"), flush=True)
    info(f"log: {log}")
    log.parent.mkdir(parents=True, exist_ok=True)
    events: list[dict] = []
    with log.open("w") as saved, subprocess.Popen(
        cmd, cwd=clone, text=True, stdin=subprocess.PIPE, stdout=subprocess.PIPE
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
            _narrate(event)
    ok, message, cost = _outcome(agent, events)
    return AgentRun(proc.returncode == 0 and ok, message, cost)


def check_branch(clone: Path, branch: str) -> list[str]:
    """Problems if the agent left <branch>, or rewrote it rather than adding commits."""
    problems = []
    current = run(["git", "branch", "--show-current"], cwd=clone, capture=True).stdout.strip()
    if current != branch:
        problems.append(f"the agent left the branch {branch} (now on {current or 'a detached HEAD'})")
    ancestor = run(
        ["git", "merge-base", "--is-ancestor", f"upstream/{BASE_BRANCH}", "HEAD"], cwd=clone, check=False
    )
    if ancestor.returncode != 0:
        problems.append(f"upstream/{BASE_BRANCH} is no longer an ancestor of the branch")
    return problems


def changed_files(clone: Path) -> list[tuple[str, str]]:
    """Each file changed since upstream/master, committed or not, as (status, path).

    The status is git's letter: `A` added, `M` modified, `D` deleted; a rename is a `D` and an `A`.
    """
    diff = run(
        ["git", "diff", "--name-status", "--no-renames", f"upstream/{BASE_BRANCH}"], cwd=clone, capture=True
    ).stdout
    new = run(["git", "ls-files", "--others", "--exclude-standard"], cwd=clone, capture=True).stdout
    # Each line of the diff is the status letter, a tab and the path.
    entries = [tuple(line.split("\t", 1)) for line in diff.splitlines()]
    return [(status, path) for status, path in entries] + [("A", path) for path in new.splitlines()]


def at_upstream(clone: Path, path: str) -> str:
    """`path` as it is on upstream/master; empty if it is new."""
    result = run(["git", "show", f"upstream/{BASE_BRANCH}:{path}"], cwd=clone, capture=True, check=False, quiet=True)
    return result.stdout if result.returncode == 0 else ""


def escape_hatch_problems(clone: Path, changed: list[str]) -> list[str]:
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


# =============================================================================
# 7. Creating the PR
# =============================================================================


def commit_leftovers(clone: Path, title: str, co_author_line: str) -> None:
    """Commit what the agent left uncommitted, if anything, with <title> and <co-author>."""
    if not run(["git", "status", "--porcelain"], cwd=clone, capture=True).stdout.strip():
        return
    git(clone, "add", "--all")
    run(["git", "-C", str(clone), "commit", "--file", "-"], stdin_text=f"{title}\n\n{co_author_line}\n")


def push(clone: Path, branch: str) -> None:
    git(clone, "push", "origin", branch)


def pr_body(agent: Agent, prompt: str) -> str:
    return (
        f"Made by {NAME}.\n\n"
        f"Model: {agent.model} ({agent.name}, effort {agent.effort})\n\n"
        f"Prompt:\n\n```\n{prompt}\n```\n"
    )


def open_pr(clone: Path, login: str, branch: str, title: str, body: str) -> str:
    """Open the PR and return its address."""
    result = run(
        ["gh", "pr", "create", "--repo", UPSTREAM, "--base", BASE_BRANCH, "--head", f"{login}:{branch}",
         "--title", title, "--body-file", "-"],
        cwd=clone, capture=True, stdin_text=body,
    )
    return result.stdout.strip().splitlines()[-1]


# =============================================================================
# 8. Clean up
# =============================================================================


def clean_up(clone: Path, branch: str) -> None:
    git(clone, "switch", "--detach", f"upstream/{BASE_BRANCH}")
    git(clone, "branch", "-D", branch)


def report(task: str, agent: Agent, cost: float | None, log: Path, pr_url: str | None) -> None:
    info(f"task: {task}")
    info(f"agent: {agent.name}, model: {agent.model}")
    if cost is not None:
        info(f"cost: ${cost:.2f}")
    info(f"log: {log}")
    info(f"PR: {pr_url}" if pr_url else "PR: none, as nothing changed")


# =============================================================================
# The whole run, and the command line
# =============================================================================


def work(args: argparse.Namespace) -> int:
    started = datetime.now(timezone.utc).strftime("%Y%m%d-%H%M%S")

    step("1. Determine the save location")
    save = save_location()
    info(str(save))

    step("2. Determine if a fork exists and if not make one")
    login, fork = ensure_fork()

    step("3. Determine if a clone already exists, and if not make one")
    clone = ensure_clone(save, fork)

    step("4. Determine the task, and create a branch for it based on upstream/master")
    update_clone(clone)
    tasks_from = Path(args.tasks_from).expanduser().resolve() if args.tasks_from else None
    task = determine_task(clone, tasks_from, args.task, args.input)
    info(f"task: {task.name}" + (f" (from {tasks_from})" if tasks_from else ""))
    branch = create_branch(clone, task.name, started)

    step("5. Finding the model to run the code on")
    agent = choose_agent(args.agent, args.model, args.effort)

    step("6. Running the task")
    run(["lake", "exe", "get_cache"], cwd=clone)
    log = save / "logs" / f"{started}-{task.name}.jsonl"
    result = run_agent(clone, agent, task.prompt, log)
    if not result.ok:
        raise WorkerError(f"the agent did not finish successfully; see {log}. The clone {clone} is left as it is")
    changed = check_change(clone, branch)

    pr_url = None
    if changed:
        step("7. Creating the PR")
        commit_leftovers(clone, task.title, agent.co_author)
        push(clone, branch)
        pr_url = open_pr(clone, login, branch, task.title, pr_body(agent, task.prompt))
    else:
        info("nothing changed; the agent's final message was:")
        info(result.message)

    step("8. Clean up")
    clean_up(clone, branch)
    report(task.name, agent, result.cost_usd, log, pr_url)
    return 0


def parser() -> argparse.ArgumentParser:
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
