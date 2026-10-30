# Copyright 2026 Anthropic PBC
# SPDX-License-Identifier: Apache-2.0
"""A small test of one rule of the front page: a status to which front/labels.txt gives no chip words, on a card that has
none of its own, gets no chip at all; every chip with words is written as before; and make_statements_html.py and
check_statements_html.py, which each write the chip by code of their own, give the same text.

Usage, from the repository's lean/ folder:
    python3 scripts/test_statements_empty_chip.py [GENERATOR [CHECKER]]

It cuts the one function out of each program's text (chip_html; chip), runs both on the same small labels, and prints one
line for each case. Exit code 0 if all come out as due. It reads the two programs and nothing else, writes nothing, and
runs no Lean. Needs Python 3.7 or later and only the standard library."""
import html
import os
import re
import sys
import textwrap

HERE = os.path.dirname(os.path.abspath(__file__))
GENERATOR = sys.argv[1] if len(sys.argv) > 1 else os.path.join(HERE, "make_statements_html.py")
CHECKER = sys.argv[2] if len(sys.argv) > 2 else os.path.join(HERE, "check_statements_html.py")

LABEL = {}
for key, kind, words, tip in (
    ("definition", "definition", "", "a definition"),
    ("proved", "theorem", "", "a theorem"),
    ("target", "statement", "", "a statement"),
    ("hypothesis-open", "hypothesis", "hypothesis · not proved", "open"),
    ("hypothesis-proved", "hypothesis", "hypothesis · proved", "p"),
):
    LABEL["type-" + key], LABEL["chip-" + key], LABEL["tip-" + key] = kind, words, tip


class Refused(Exception):
    pass


def cut(path, name, others):
    """The nested function 'name' of the program at path, as a function of this test's own, over LABEL."""
    text = open(path, encoding="utf-8").read()
    found = re.findall(r"(?m)^    def %s\(.*?(?=^    def |^    [a-z_]+ = )" % name, text, re.S)
    if len(found) != 1:
        raise SystemExit("%s: %d functions named %s, and one is due" % (path, len(found), name))
    space = dict(others, label=LABEL)
    exec(textwrap.dedent(found[0]), space)
    return space[name]


SPAN = '<span class="chip chip-%s" title="%s">%s</span>'
# (title, the arguments: status, word, own words, theorems, the card it is borrowed from; what is due)
CASES = [
    ("no words in labels.txt, none of its own: a definition", ("definition", "", "", (), ""), ""),
    ("no words in labels.txt, none of its own: a theorem", ("proved", "", "", (), ""), ""),
    ("no words, borrowed by a row from another card", ("definition", "", "", (), "A.b"), ""),
    ("no words, though theorems are named for it", ("target", "", "", ("A.t",), ""), ""),
    ("words in labels.txt", ("hypothesis", "open", "", (), ""), SPAN % ("other", "open", "hypothesis · not proved")),
    ("words, of the bright kind", ("hypothesis", "proved", "", (), ""), SPAN % ("std", "p", "hypothesis · proved")),
    (
        "no words in labels.txt, words of the card's own",
        ("target", "", "stated", ("A.t",), ""),
        SPAN % ("other", "a statement; theorems named for it: A.t", "stated"),
    ),
    (
        "words, borrowed from another card",
        ("hypothesis", "open", "", (), "A.b"),
        SPAN % ("other", "open; the chip of the card A.b", "hypothesis · not proved"),
    ),
    ("a status that labels.txt lacks", ("hypothesis", "unheard-of", "", (), ""), Refused),
]


def main():
    esc = lambda s: html.escape(s, quote=True)
    bright = ("proved", "by-definition", "by-construction")
    makes = cut(GENERATOR, "chip_html", {"esc": esc, "BRIGHT": bright, "Stop": Refused})
    checks = cut(CHECKER, "chip", {"f_esc": esc, "F_BRIGHT": bright, "GiveUp": Refused})
    failed = 0
    for title, arguments, due in CASES:
        got = []
        for f in (makes, checks):
            try:
                got.append(f(*arguments))
            except Refused:
                got.append(Refused)
        good = got[0] == due and got[1] == due
        failed += not good
        said = ["refused" if g is Refused else "no chip" if g == "" else g for g in got]
        mark = "as due" if good else "NOT AS DUE"
        print("%s: %s: the generator: %s | the checker: %s" % (mark, title, said[0], said[1]))
    print("RESULT: %s" % ("all %d as due" % len(CASES) if not failed else "%d of %d not as due" % (failed, len(CASES))))
    return 1 if failed else 0


if __name__ == "__main__":
    sys.exit(main())
