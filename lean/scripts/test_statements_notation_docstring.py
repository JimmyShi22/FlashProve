# Copyright 2026 Anthropic PBC
# SPDX-License-Identifier: Apache-2.0
"""A small test of one rule of make_statements_html.py's scanner: a docstring that stands before 'notation' or 'local
notation' is that notation's comment, as in Lean, and the scanner reads on; a docstring before any other command that is
no declaration, or before nothing, still stops it.

Usage, from the repository's lean/ folder:
    python3 scripts/test_statements_notation_docstring.py

It writes small Lean texts into a temporary folder of its own, which the system removes with it, scans each with the
generator's own scanner as a file that a page shows whole, and prints one line for each. Exit code 0 if all come out as
due. It reads no file of the library but the generator, and it runs no Lean. Needs Python 3.7 or later and only the
standard library."""
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

DEF = "/-- a number -/\ndef x : Nat := 0\n"
# (title, text, the names due and how many lines are in force above the last of them; or the words of the stop due)
CASES = [
    ("before 'notation'", '/-- zero -/\nnotation "Z" => (0 : Nat)\n' + DEF, (["x"], 1)),
    ("before 'local notation'", '/-- zero -/\nlocal notation "Z" => (0 : Nat)\n' + DEF, (["x"], 1)),
    (
        "before each of two, as in the library",
        '/-- zero -/\nlocal notation "Z" => (0 : Nat)\n/-- one -/\nlocal notation "I" => (1 : Nat)\n\n' + DEF,
        (["x"], 2),
    ),
    ("before the declaration alone; the notation has none", 'local notation "Z" => (0 : Nat)\n' + DEF, (["x"], 1)),
    (
        "before 'scoped notation'",
        'namespace A\n/-- zero -/\nscoped notation "Z" => (0 : Nat)\n' + DEF + "end A\n",
        "a docstring before 'notation'",
    ),
    (
        "before 'scoped[A] notation'",
        '/-- zero -/\nscoped[A] notation "Z" => (0 : Nat)\n' + DEF,
        "a docstring before 'notation'",
    ),
    (
        "before an attribute and 'notation'",
        '/-- zero -/\n@[inherit_doc] notation "Z" => (0 : Nat)\n' + DEF,
        "a docstring before 'notation'",
    ),
    ("before 'notation3'", '/-- zero -/\nnotation3 "Z" => (0 : Nat)\n' + DEF, "a docstring before 'notation3'"),
    ("before 'variable'", "/-- a number -/\nvariable (n : Nat)\n" + DEF, "a docstring before 'variable'"),
    ("before 'infixl'", '/-- plus -/\ninfixl:65 " +++ " => Nat.add\n' + DEF, "a docstring before 'infixl'"),
    ("before 'macro'", '/-- zero -/\nmacro "zz" : term => `(0)\n' + DEF, "a docstring before 'macro'"),
    ("before 'open'", "/-- open it -/\nopen Nat\n" + DEF, "a docstring before 'open'"),
    ("before 'section'", "/-- a part -/\nsection\n" + DEF + "end\n", "a docstring before 'section'"),
    ("before 'end'", "namespace A\n" + DEF + "/-- the end -/\nend A\n", "a docstring before 'end'"),
    ("before nothing", DEF + "/-- words that belong to nothing -/\n", "a docstring that belongs to no declaration"),
    (
        "behind the word 'local', not before it",
        'local /-- zero -/ notation "Z" => (0 : Nat)\n' + DEF,
        "a docstring after an attribute or modifier",
    ),
]


def scanned(text, folder, number):
    path = "Case%d.lean" % number
    with open(os.path.join(folder, path), "w", encoding="utf-8") as f:
        f.write(text)
    found = gen.scan(gen.Source(folder, path), shown=True)
    return [".".join(d.namespaces + [d.written]) for d in found], len(found[-1].in_force)


def main():
    failed = 0
    with tempfile.TemporaryDirectory() as folder:
        for number, (title, text, due) in enumerate(CASES, 1):
            try:
                got = scanned(text, folder, number)
            except gen.Stop as stop:
                got = str(stop)
            good = (due in got) if isinstance(due, str) and isinstance(got, str) else got == due
            failed += not good
            print("%s: a docstring %s: %s" % ("as due" if good else "NOT AS DUE", title, got))
    print("RESULT: %s" % ("all %d as due" % len(CASES) if not failed else "%d of %d not as due" % (failed, len(CASES))))
    return 1 if failed else 0


if __name__ == "__main__":
    sys.exit(main())
