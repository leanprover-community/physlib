# /// script
# requires-python = ">=3.11"
# dependencies = [
#     "requests",
# ]
# ///

# This script requires the following tools:
# - uv: https://docs.astral.sh/uv/
# - gource: https://gource.io/
# - ffmpeg: https://ffmpeg.org/
#
# Run it from the root of the git repo using:
#
# $ uv run scripts/website/gource.py
#
# It will produce a file called `gource.mp4` in the root of the git repo. You
# will also see the progress live while the script is running.

import shlex
import subprocess
import tempfile
from dataclasses import dataclass, field
from pathlib import Path

import requests


@dataclass
class Author:
    name: str
    github: str
    aliases: set[str] = field(default_factory=set)


AUTHORS: list[Author] = [
#    Author(
#        name="FirstName1 LastName1",
#        github="githubusername1",
#        aliases={"githubusername1'"},
#    ),
#    Author(
#        name="FirstName2 LastName2",
#        github="githubusername2",
#    ),
]


def run(*cmd: str | Path) -> None:
    args = [str(arg) for arg in cmd]
    print(f"$ {shlex.join(args)}")
    subprocess.check_call(args)


def patch_log_file(input: Path, output: Path) -> None:
    renamings = {}
    for author in AUTHORS:
        for alias in author.aliases:
            renamings[alias] = author.name

    names = set()
    with open(input) as f_in, open(output, "w") as f_out:
        for line in f_in:
            time, name, rest = line.split("|", maxsplit=2)
            name = renamings.get(name, name)
            names.add(name)
            f_out.write(f"{time}|{name}|{rest}")

    print()
    print("Unique names (after renaming):")
    authors_by_name = {author.name: author for author in AUTHORS}
    for name in sorted(names):
        author = authors_by_name.get(name)
        if author is None:
            print(f"- {name}")
        else:
            print(f"- {name} [GitHub: {author.github}]")


def fetch_github_avatars(path: Path) -> None:
    print()
    print("Fetching GitHub avatars...")
    path.mkdir(parents=True, exist_ok=True)
    for author in AUTHORS:
        print(f"- {author.name}")
        try:
            r = requests.get(f"https://github.com/{author.github}.png")
            r.raise_for_status()
            with open(path / f"{author.name}.png", "wb") as f:
                f.write(r.content)
        except Exception as e:
            print(f"Failed to get profile picture for {author.name}: {e}")


# https://docs.python.org/3/library/subprocess.html#replacing-shell-pipeline
# https://github.com/acaudwell/Gource/wiki/Videos
# https://gist.github.com/Gnzlt/a2bd6551f0044a673e455b269646d487
def render_video(log: Path, avatars: Path, output: Path) -> None:
    print()
    print("Rendering video")
    framerate = "60"

    p_gource = subprocess.Popen(
        [
            "gource",
            log,
            *("--user-image-dir", avatars),
            *("--auto-skip-seconds", "0.1"),
            *("--seconds-per-day", "1"),
            "-1920x1080",  # Resolution
            *("--output-ppm-stream", "-"),
            *("--output-framerate", framerate),
        ],
        stdout=subprocess.PIPE,
    )

    p_ffmpeg = subprocess.Popen(
        [
            "ffmpeg",
            "-y",
            *("-r", framerate),
            *("-f", "image2pipe"),
            *("-vcodec", "ppm"),
            *("-i", "-"),
            output,
        ],
        stdin=p_gource.stdout,
    )

    p_gource.stdout.close()
    p_ffmpeg.communicate()


def main() -> None:
    with tempfile.TemporaryDirectory(prefix="gource-") as tmpdirname:
        tmpdir: Path = Path(tmpdirname)
        log_file = tmpdir / "log.txt"
        patched_log_file = tmpdir / "log_patched.txt"
        avatar_dir = tmpdir / "avatars"

        print(f"{tmpdir = !s}")
        run("gource", "--output-custom-log", log_file)
        patch_log_file(log_file, patched_log_file)
        fetch_github_avatars(avatar_dir)
        render_video(patched_log_file, avatar_dir, Path("gource.mp4"))


if __name__ == "__main__":
    main()
