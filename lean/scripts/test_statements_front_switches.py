# Copyright 2026 Anthropic PBC
# SPDX-License-Identifier: Apache-2.0
"""A small test of two optional lines of front/labels.txt. 'group-TOP | words' gives a group in the front page's list of
definitions a title of its own; a line whose TOP is no group stops both programs. 'contents-depth | sections' leaves the
sub-sections out of the contents. Without these lines both rules give what the page had before.
make_statements_html.py and check_statements_html.py each have code of their own for these rules, and must agree.

Usage, from the repository's lean/ folder:
    python3 scripts/test_statements_front_switches.py [GENERATOR [CHECKER]]

It loads the two programs, calls their three small functions on the same made-up labels, and prints one line for each
case. Exit code 0 if all come out as due. It also looks in each program's text for the one place where each function is
used. It reads the two programs and nothing else, writes nothing, and runs no Lean. It does not make or check a page.
Needs Python 3.7 or later and only the standard library."""
import importlib.util
import os
import sys

sys.dont_write_bytecode = True  # leave no __pycache__ beside the programs
HERE = os.path.dirname(os.path.abspath(__file__))
GENERATOR = sys.argv[1] if len(sys.argv) > 1 else os.path.join(HERE, "make_statements_html.py")
CHECKER = sys.argv[2] if len(sys.argv) > 2 else os.path.join(HERE, "check_statements_html.py")


def load(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


REFUSED = "refused"
PLAIN = {"title": "A page"}
TITLED = {"group-Cm": "Commitments", "group-Ladder.lean": "The top file", "group-Ladder": "The goals", "group-Run": ""}
# (title, which rule, the labels, the argument, what is due)
CASES = [
    ("no such line: the folder's name", "group", PLAIN, "Cm", "Cm"),
    ("no such line: a file's name", "group", PLAIN, "Ladder.lean", "Ladder.lean"),
    ("a line for this folder", "group", TITLED, "Cm", "Commitments"),
    ("a line for a file in no folder", "group", TITLED, "Ladder.lean", "The top file"),
    ("a line for the folder of the like name", "group", TITLED, "Ladder", "The goals"),
    ("lines for other folders alone", "group", TITLED, "Fmt", "Fmt"),
    ("a line without words", "group", TITLED, "Run", "Run"),
    ("a folder whose name begins like a titled one", "group", TITLED, "CmX", "CmX"),
    ("no such line: none is idle", "idle", PLAIN, ("Cm", "Fmt"), []),
    ("every line has its group", "idle", TITLED, ("Cm", "Fmt", "Ladder", "Ladder.lean", "Run"), []),
    ("two lines without a group", "idle", TITLED, ("Cm", "Ladder"), ["group-Ladder.lean", "group-Run"]),
    ("a group whose name begins like the line's", "idle", {"group-Cm": "x"}, ("CmX",), ["group-Cm"]),
    ("no group at all", "idle", {"group-Cm": "x"}, (), ["group-Cm"]),
    ("no such line: a section", "contents", PLAIN, 2, True),
    ("no such line: a sub-section", "contents", PLAIN, 3, True),
    ("'sections': a section", "contents", {"contents-depth": "sections"}, 2, True),
    ("'sections': a sub-section", "contents", {"contents-depth": "sections"}, 3, False),
    ("another word", "contents", {"contents-depth": "all"}, 3, REFUSED),
    ("another word, at a section", "contents", {"contents-depth": "none"}, 2, REFUSED),
    ("no word", "contents", {"contents-depth": ""}, 3, REFUSED),
]
# how often each call's text must stand in its program: at its place of use, and in the function's own first line
USES = [
    (GENERATOR, "group_title(label, top)", 2),
    (GENERATOR, "idle_group_lines(label, by_top)", 2),
    (GENERATOR, 'in_contents(label, sec["level"])', 1),
    (CHECKER, "f_group_title(label, top)", 2),
    (CHECKER, "f_idle_group_lines(label, tops)", 2),
    (CHECKER, 'f_in_contents(label, sec["level"])', 1),
]


def main():
    gen, chk = load("make_statements_html", GENERATOR), load("check_statements_html", CHECKER)
    failed = 0
    for title, rule, labels, argument, due in CASES:
        got = []
        name = {"group": "group_title", "idle": "idle_group_lines", "contents": "in_contents"}[rule]
        for module, name, stop in ((gen, name, "Stop"), (chk, "f_" + name, "GiveUp")):
            if not hasattr(module, name):
                got.append("no function " + name)
                continue
            try:
                got.append(getattr(module, name)(dict(labels), argument))
            except getattr(module, stop):
                got.append(REFUSED)
        good = got[0] == due and got[1] == due and type(got[0]) is type(due) and type(got[1]) is type(due)
        failed += not good
        mark = "as due" if good else "NOT AS DUE"
        print("%s: %s: %s: the generator: %r | the checker: %r" % (mark, rule, title, got[0], got[1]))
    for path, text, due in USES:
        n = open(path, encoding="utf-8").read().count(text)
        failed += n != due
        mark = "as due" if n == due else "NOT AS DUE"
        print("%s: %s stands %d times in %s (due: %d)" % (mark, text, n, os.path.basename(path), due))
    total = len(CASES) + len(USES)
    print("RESULT: %s" % ("all %d as due" % total if not failed else "%d of %d not as due" % (failed, total)))
    return 1 if failed else 0


if __name__ == "__main__":
    sys.exit(main())
