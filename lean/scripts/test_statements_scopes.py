# Copyright 2026 Anthropic PBC
# SPDX-License-Identifier: Apache-2.0
"""A small test of one rule of make_statements_html.py's scanner: 'namespace A.B.C' opens three scopes, and 'end C'
closes the innermost alone, as in Lean.

Usage, from the repository's lean/ folder:
    python3 scripts/test_statements_scopes.py

It writes four small Lean texts into a temporary folder of its own, which the system removes with it, scans each with
the generator's own scanner, and prints one line for each. Exit code 0 if all four come out as due. It reads no file of
the library but the generator, and it runs no Lean. Needs Python 3.7 or later and only the standard library."""
import importlib.util
import os
import sys
import tempfile

sys.dont_write_bytecode = True  # leave no __pycache__ beside the generator
HERE = os.path.dirname(os.path.abspath(__file__))
GENERATOR = sys.argv[1] if len(sys.argv) > 1 else os.path.join(HERE, "make_statements_html.py")
spec = importlib.util.spec_from_file_location("make_statements_html", GENERATOR)
gen = importlib.util.module_from_spec(spec)
spec.loader.exec_module(gen)

CASES = [
    (
        "one scope at a time",
        "namespace A.B.C\ndef x : Nat := 0\nend C\ndef y : Nat := 0\nend B\ndef z : Nat := 0\nend A\n",
        ["A.B.C.x", "A.B.y", "A.z"],
    ),
    ("all three at once", "namespace A.B.C\ndef x : Nat := 0\nend A.B.C\ndef w : Nat := 0\n", ["A.B.C.x", "w"]),
    ("a name that is no end of the namespace's", "namespace A.B.C\ndef x : Nat := 0\nend D\n", None),
    ("the namespace's beginning, not its end", "namespace A.B.C\ndef x : Nat := 0\nend A\n", None),
]


def names(text, folder, number):
    path = "Case%d.lean" % number
    with open(os.path.join(folder, path), "w", encoding="utf-8") as f:
        f.write(text)
    return [".".join(d.namespaces + [d.written]) for d in gen.scan(gen.Source(folder, path), shown=False)]


def main():
    failed = 0
    with tempfile.TemporaryDirectory() as folder:
        for number, (title, text, due) in enumerate(CASES, 1):
            try:
                got = names(text, folder, number)
            except gen.Stop as stop:
                got, why = None, str(stop)
            good = got == due
            failed += not good
            print("%s: %s: %s" % ("as due" if good else "NOT AS DUE", title, "the scanner stops" if got is None else got))
    print("RESULT: %s" % ("all four as due" if not failed else "%d of four not as due" % failed))
    return 1 if failed else 0


if __name__ == "__main__":
    sys.exit(main())
