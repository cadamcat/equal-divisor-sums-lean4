#!/usr/bin/env python3
"""Check that Erdos824.erdos_824 in Erdos824.Theorem has the statement of Challenge.lean.

Elaborates Challenge.lean and, in a separate Lean run, Erdos824.Theorem. Each run prints with
`set_option pp.all true` the type of Erdos824.erdos_824 and the definition Erdos824.h. The two
outputs must be identical. Exit 0 when they are, 1 otherwise. Run after the library build.
"""
import os
import re
import subprocess
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
QUERIES = ["set_option pp.all true", "#check @Erdos824.erdos_824", "#print Erdos824.h"]


def printed(header):
    fd, p = tempfile.mkstemp(prefix=".check_statement_", suffix=".lean", dir=ROOT)
    with os.fdopen(fd, "w") as f:
        f.write("\n".join(header + QUERIES) + "\n")
    try:
        r = subprocess.run(["lake", "env", "lean", p], cwd=ROOT, capture_output=True, text=True)
    finally:
        os.unlink(p)
    lines = re.sub(r"^.*?:\d+:\d+: ", "", r.stdout, flags=re.M).splitlines()
    keep = [l for l in lines if not l.startswith("warning") and "declaration uses 'sorry'" not in l]
    return r.returncode, "\n".join(keep).strip()


def main() -> int:
    challenge = (ROOT / "Challenge.lean").read_text(encoding="utf-8").splitlines()
    rc1, a = printed(challenge)
    rc2, b = printed(["import Erdos824.Theorem"])
    same = rc1 == 0 and rc2 == 0 and a == b and "Erdos824.erdos_824" in a
    print(f"challenge exit {rc1}, Erdos824.Theorem exit {rc2}, pp.all outputs identical: {a == b}")
    if not same:
        print("--- Challenge.lean\n" + a[-3000:] + "\n--- Erdos824.Theorem\n" + b[-3000:])
        return 1
    print("PASS: Erdos824.erdos_824 and Erdos824.h agree with Challenge.lean.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
