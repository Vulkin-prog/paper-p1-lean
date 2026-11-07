#!/usr/bin/env python3
"""Check the source-file requirements before the complete Palomar workflow.

This is a local source scan, not Palomar's complete mechanical preflight.
Requirements reviewed at PalomarPolicy 28bd48b9b71bbb2a82c718ce761d5a4220ef8e60
and PalomarSubmission 14aa8d6b3c2f14a8540605e37144560b9a00e7e7.
"""

from pathlib import Path
import subprocess

ROOT = Path(__file__).resolve().parents[1]


def has_module_header(text):
    index = 0
    while index < len(text):
        if text[index] in " \r\n":
            index += 1
        elif text.startswith("--", index):
            end = text.find("\n", index)
            index = len(text) if end == -1 else end + 1
        elif text.startswith("/-", index) and not text.startswith(("/-!", "/--"), index):
            index += 2
            depth = 1
            while index < len(text) and depth:
                if text.startswith("/-", index):
                    depth += 1
                    index += 2
                elif text.startswith("-/", index):
                    depth -= 1
                    index += 2
                else:
                    index += 1
            if depth:
                return False
        else:
            rest = text[index:]
            return rest == "module" or rest.startswith(("module\n", "module\r", "module "))
    return False


def main():
    paths = subprocess.check_output(
        ["git", "ls-files", "--cached", "--others", "--exclude-standard", "-z", "*.lean"],
        cwd=ROOT,
    ).decode().split("\0")
    paths = sorted(set(path for path in paths if path))
    errors = []
    maximum = (0, "")
    for name in paths:
        path = ROOT / name
        if path.is_symlink() or not path.is_file():
            errors.append(f"{name}: not a regular source file")
            continue
        text = path.read_text()
        lines = text.count("\n") + int(bool(text) and not text.endswith("\n"))
        maximum = max(maximum, (lines, name))
        if lines > 10_000:
            errors.append(f"{name}: {lines} lines exceeds the 10,000-line limit")
        if path.name != "lakefile.lean" and not has_module_header(text):
            errors.append(f"{name}: module header must precede imports and documentation")
    if errors:
        raise SystemExit("\n".join(errors))
    if not paths:
        raise SystemExit("No Lean source files found")
    print(f"Local Palomar source scan passed for {len(paths)} Lean files.")
    print(f"Longest source: {maximum[1]} ({maximum[0]} lines).")
    print("Scope: source regularity, module headers and line limits; full Palomar preflight remains separate.")


if __name__ == "__main__":
    main()
