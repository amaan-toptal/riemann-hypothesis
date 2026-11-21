#!/usr/bin/env python3
"""Regenerate verification/static-scan.txt: a text search of the submission for risky constructs.

    python3 scripts/static-scan.py > verification/static-scan.txt
    python3 scripts/static-scan.py --check verification/static-scan.txt

Counts are matching lines. `src/Challenge.lean` is excluded: it is ours, not the submission's,
and deliberately contains `sorry`. A text search is not a proof; Comparator's checks are.
"""
import argparse
from collections import Counter
import difflib
import os
from pathlib import Path
import re
import sys

ROOT = Path(__file__).resolve().parent.parent / "src"
EXCLUDED = {"Challenge.lean"}
DECL = r"^\s*(@\[[^\]]*\]\s*)?"
NOTATION = r"(notation3?|infix[lr]?|prefix|postfix)\b"
NEEDLES = ["notation", "infix", "prefix", "postfix"]

# (label, literal needles, pattern). A file is searched with the pattern only if it contains
# a needle, which keeps a full scan to about a minute. Patterns apply per line, case-sensitive.
ROWS = [
    ("axiom (anywhere)", ["axiom"], r"\baxiom\b"),
    ("sorry / sorryAx", ["sorry"], r"\bsorry(Ax)?\b"),
    ("admit", ["admit"], r"\badmit\b"),
    ("native_decide/ofReduceBool/trustCompiler", ["native_decide", "ofReduceBool", "trustCompiler"],
     r"native_decide|ofReduceBool|trustCompiler"),
    ("implemented_by/extern", ["implemented_by", "extern"], r"implemented_by|\bextern\b"),
    ("unsafe", ["unsafe"], r"\bunsafe\b"),
    ("opaque", ["opaque"], r"\bopaque\b"),
    ("set_option debug.*", ["debug."], r"set_option\s+debug\."),
    ("skipKernelTC", ["skipKernelTC"], r"skipKernelTC"),
    ("addDecl/addAndCompile", ["addDecl", "addAndCompile"], r"addDecl|addAndCompile"),
    ("modifyEnv/setEnv", ["modifyEnv", "setEnv"], r"modifyEnv|setEnv"),
    ("run_cmd/run_elab/run_meta/#eval", ["run_cmd", "run_elab", "run_meta", "#eval"],
     r"run_cmd|run_elab|run_meta|#eval"),
    ("run_tac", ["run_tac"], r"\brun_tac\b"),
    ("MVarId.assign / .assign", [".assign"], r"\.assign\b"),
    ("partial def", ["partial"], r"\bpartial\s+def\b"),
    ("kexactB", ["kexactB"], r"\bkexactB\b"),
    ("kcopy", ["kcopy"], r"\bkcopy\b"),
    ("@[positivity] extension", ["@[positivity"], r"@\[positivity"),
    ("initialize", ["initialize"], r"^\s*(builtin_)?initialize\b"),
    ("elab/macro/syntax defs", ["elab", "macro", "syntax"],
     r"^\s*(local\s+|scoped\s+)?(elab|macro|syntax|macro_rules|elab_rules)\b"),
    ("notation-family declarations", NEEDLES, DECL + r"((local|scoped)\s+)?" + NOTATION),
    ("notation-family (non-local)", NEEDLES, DECL + NOTATION),
    ("import Lean", ["import Lean"], r"^import Lean\b"),
    ("IO/filesystem/process API", ["IO.", "System.FilePath"],
     r"(^|[^A-Za-z0-9_.])(IO\.(FS|Process|getEnv|println|print|eprint|eprintln|appendFile|readFile|writeFile)"
     r"|System\.FilePath)\b"),
    ("allowUnsafeReducibility", ["allowUnsafeReducibility"], r"allowUnsafeReducibility"),
    ("comments -- or /-", ["--", "/-"], r"--|/-"),
]
LISTED = [
    ("addDecl / modifyEnv / run_cmd", ["addDecl", "addAndCompile", "modifyEnv", "setEnv", "run_cmd", "run_elab",
                                       "run_meta", "#eval"],
     r"addDecl|addAndCompile|modifyEnv|setEnv|run_cmd|run_elab|run_meta|#eval"),
    ("MVarId.assign or partial def", [".assign", "partial"], r"\.assign\b|\bpartial\s+def\b"),
    ("kexactB / kcopy definitions", ["kexactB", "kcopy"], r"^\s*(elab|macro|syntax)\b.*\b(kexactB|kcopy)\b"),
    ("run_tac", ["run_tac"], r"\brun_tac\b"),
]
CENSUS = re.compile(r"^\s*set_option\s+([A-Za-z0-9_.]+)", re.M)


def sources(root):
    for directory, subdirectories, files in os.walk(root):
        subdirectories.sort()
        for name in sorted(files):
            path = Path(directory, name)
            if name.endswith(".lean") and path.relative_to(root).as_posix() not in EXCLUDED:
                yield path


def scan(root):
    rows = [(label, needles, re.compile(pattern, re.M)) for label, needles, pattern in ROWS]
    listed = [(label, needles, re.compile(pattern, re.M)) for label, needles, pattern in LISTED]
    counts, census, files = Counter(), Counter(), {label: [] for label, _, _ in listed}
    total = 0
    for path in sources(root):
        total += 1
        text = path.read_text(encoding="utf-8")
        lines = None
        for label, needles, pattern in rows:
            if any(needle in text for needle in needles) and pattern.search(text):
                lines = lines if lines is not None else text.splitlines()
                counts[label] += sum(1 for line in lines if pattern.search(line))
        for label, needles, pattern in listed:
            if any(needle in text for needle in needles) and pattern.search(text):
                files[label].append("./" + path.relative_to(root).as_posix())
        if "set_option" in text:
            census.update(CENSUS.findall(text))
    return total, counts, census, files


def render(root):
    total, counts, census, files = scan(root)
    width = max(len(label) for label, _, _ in ROWS) + 2
    out = [f"# Risky-construct scan over all {total:,} .lean files in src/ except Challenge.lean (line counts)",
           "# Regenerate: python3 scripts/static-scan.py > verification/static-scan.txt"]
    out += [f"{label:<{width}} {counts[label]}" for label, _, _ in ROWS]
    for label, paths in files.items():
        out += ["", f"## Files with {label} ({len(paths)})"] + paths
    out += ["", "## set_option census (leading indentation ignored)"]
    out += [f"{count:6d} set_option {name}" for name, count in sorted(census.items(), key=lambda i: (-i[1], i[0]))]
    return "\n".join(out) + "\n"


def main():
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--root", type=Path, default=ROOT)
    parser.add_argument("--check", type=Path, help="fail if this committed scan differs from a fresh one")
    args = parser.parse_args()
    report = render(args.root)
    if not args.check:
        sys.stdout.write(report)
        return 0
    committed = args.check.read_text(encoding="utf-8")
    if committed == report:
        print(f"{args.check} is up to date")
        return 0
    sys.stdout.writelines(difflib.unified_diff(committed.splitlines(True), report.splitlines(True),
                                               str(args.check), "fresh scan"))
    return 1


if __name__ == "__main__":
    sys.exit(main())
