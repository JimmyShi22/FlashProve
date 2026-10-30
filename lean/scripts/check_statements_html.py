#!/usr/bin/env python3
# Copyright 2026 Anthropic PBC
# SPDX-License-Identifier: Apache-2.0
"""Compare lean/STATEMENTS-ALL.html (the long page) and lean/STATEMENTS.html (the front page) with the Lean files.

Usage, from the repository's lean/ folder:
    python3 scripts/check_statements_html.py . STATEMENTS-ALL.html --front=STATEMENTS.html

In general:
    check_statements_html.py LEAN_FOLDER LONG_HTML [--short=SHORT_HTML] [--front=FRONT_HTML] [--heads=FOLDER]
                             [--generator=FILE | --skip-check-8] [--uses-table=FILE]

Without --short and --front the long page is checked alone, and it must not have the line that leads to another page.
With --short both are checked, under the same eight numbers; a message on the short page begins with 'short page:'. With
--front the front page is checked too ('front page:'); the line at the long page's top must then lead to it, or to the
front page beside the long page that the line 'back-to | NAME.html' of front/labels.txt names.

--heads: the folder with the four head texts, perhaps also.txt, which names the folders that the long page
shows in full besides the two, the folder short/ with the short page's words, the folder front/ with the front page's
and the folder shell/ with that page's frame, style sheet and script; by default statements-html/ next to this program.
--generator: make_statements_html.py; by default the one next to this program. Check 8 runs it, with the page going to a
pipe. Without the generator nothing is checked, unless --skip-check-8 is given. Apart from running the generator this
program only reads: it writes, makes and removes no file. Needs Python 3.7 or later and the standard library; if
html5lib is installed, the page is also parsed with it in strict mode. Exit code 0 if no check that ran has failed.
Where the checks cannot go on, the program prints what they have found so far and a line 'CANNOT CHECK: ...', and the
exit code is 1. The program sets no limit on its own time or memory, only on the size of each file that it reads and on
the time of each run of the generator (half an hour; a run takes well under a minute). Ctrl-C ends it and leaves nothing
behind. A file that it reads may not itself be a link (links among the folders above it are not looked at). Where the
system can open a file without following such a link, it does so. Where it cannot (Windows), it looks first, refuses a
link, and then opens: two acts.

THE CHECKS
 1. Every block of Lean source on the page is the file's text, character for character, from the first
    word of the command to its end, at the lines that the page gives; and the lines shown above a
    declaration are the ones in force there.
 2. Every text on the left is the docstring of the declaration beside it, and every comment of a file
    is that comment: block for block the same kind (paragraph, list item, title, indented block), the
    same words, code and bold in the same places. White space is compared only in indented blocks.
 3. Every declaration of VerifiableInference/ and IntegerModel/ has exactly one entry; files, entries
    and comments are in the stated order; the two last parts hold what they should and nothing else.
 4. A theorem, lemma or example is shown up to the sign that opens its proof, and no further.
 5. Every link goes where the written rule says (the rule is in make_statements_html.py's docstring),
    every marked name is declared where its tooltip says, and the lists at the top are right.
 6. The page loads nothing and leads nowhere outside; it uses only the known elements and attributes;
    its style and script are the ones whose sha256 is written below in this program.
 7. The page has no words of its own beyond the head texts and a fixed list of titles: every piece of
    text and every attribute must have been covered by one of the comparisons, or the check fails.
 8. Running the generator twice gives the page's bytes.

OF THE SHORT PAGE, under the same numbers: (1, 4) the pieces of Lean on each card, joined, are the declaration's text in
the file, character for character, from its start to its end by this program's own reading of the file, a theorem up to
the sign that opens its proof (on a card that goes by field, the fields' doc comments stand at the left: 2); the lines
in force stand above it, folded only where an earlier card of the same section shows these very lines; (2) a field's
comment, a first sentence of a doc comment, and a bullet that remarks.txt marks '(doc)' are the file's; (3) the
sections, the cards, their order and each card's status are claims.txt's; 'proved' and 'proved-under' stand only on a
theorem or lemma that has a line in scripts/top-theorems.txt, the list of the library's audit (which of the two fits is
not tested), and 'definition', 'only-defined' and the three words for hypotheses on no theorem, lemma or example; a
hypothesis is called proved only if the theorem that claims.txt names for it states that hypothesis and nothing else, or
that hypothesis under one that is called assumed, with no binder, no line in force, no 'sorry' written in its proof, and
a line in that list; a section's cards are folded only if claims.txt says so; the index holds what the cards' Lean texts
name and what claims.txt adds; the counts on the page are counted again; (5) what is linked, marked or dressed in a
piece is what the long page's entry has at the same place, and every link leads where its kind says; (6) as for the long
page, with tables of its own; (7) every word is a data file's, in its place, and nothing else has words. The entries
kept at the page's end, which the hover card and the side panel show, are the long page's entries. What is not held:
whether a phrase, a title, a tile or a remark says what its Lean text says, and whether a status word is true beyond
what (3) says: these are words of people or programs outside, and this program only holds that the page has them as the
data files do.

THE FRONT PAGE. Its frame, style sheet and script are three files in the folder shell/
(shell/ORIGIN.txt says what they are). They are used unchanged, except for the lines listed in shell/turns.txt.
This program builds the whole page again, from those files, from the data files in front/ and from its own reading of
the Lean files, and compares the result with the page byte for byte. So the page has no element, attribute, word or
character that this program does not expect, line ends among them: the generator keeps the page's lines short by line
ends at fixed places and by writing a long stretch of Lean in pieces (f_block, f_in_lines, F_PIECE), and this program
expects the same. A difference is reported under the number of the check that covers the part where it lies: (1, 4) the
pieces of Lean in a card's rows, which joined together are the declaration's text from start to end as this program
reads the file, a theorem only up to the sign that opens its proof; the lines in force above the declaration, which are
the card's first row, and which the block of data lists for every embedded declaration, so that the hover card and the
side panel show them with it; the lines of Lean in the block of data that the script uses to draw rows, hover cards and
the side panel; (3) the cards, their kinds, chips and order; which declarations are embedded; the statuses 'proved' and
'proved-under' stand only on the card of a theorem or lemma that has a line in scripts/top-theorems.txt, the list of the
library's audit, and no 'sorry', 'sorryAx' or 'admit' written in its proof, or as that card's chip in a row or a table;
a hypothesis has one of the three statuses with the bright chip, and a target's own chip words speak of a proof, only if
the data name theorems for it that pass the same test (not: that these theorems prove it); the words that labels.txt
gives to the other statuses do not hold a handful of words such as 'proved' without 'not'; (5) the table of links, by
the written rule; the table of contents; the target of every link; every limit is linked from some card; a card whose
declaration also has a card on the short page links to it, and that card exists; (6) frame, policy, style sheet, script,
and the four files of shell/ are the ones whose sha256 is written below in this program; (7) every word comes from a
data file and stands in its place (but for two phrases in a chip's tooltip: 'the chip of the card', 'theorems named for
it'); words that the data mark as a quotation of a page under the Lean folder stand in that page, as a run of whole
words. Seven things are also checked on the page itself, without the rebuilt copy (f_by_itself): every embedded line is
a line of its file, or the start of one and marked as cut short; none lies inside a proof; every piece in a row is the
part of its line that its numbers name; no id and no declaration's key stands twice; the lines listed as in force above
a declaration are the ones in force there (by the same reading of the Lean file as the rebuilt copy's); no embedded line
stands at or below a command that this program does not know; no line of the page is longer than 10,000 characters, and
no line end parts a number's comma from the next number. NOT CHECKED: whether a row's words, a title, a tile, a pill, a
box, the legend, a remark or a limit says what its Lean text says; whether a status, or the words that labels.txt prints
for it (its tooltip among them), is true beyond what (3) says; whether a quotation leaves out a word before or behind it
that turns its sense; what the script does, its colours among that. Those are the work of people or programs outside
this one, which only checks that the page has them as the files do.

What the two halves are worth. Checks 1 to 7 read the page with a reader of their own and compare it with
the Lean files. They are meant to catch a fault of the generator, or a page that is out of date. They
also fail on many changes made to the page by hand, but they are not a defence against a page that
somebody has edited on purpose. Check 8 is: it makes the page again and compares the bytes. It trusts
the generator, whose text, with the long and the short page's styles and scripts, is next to this program.

HOW FAR CHECKS 1 TO 7 CAN BE TRUSTED. This program imports nothing from the generator and finds the end of each text in
another way (it splits the file into tokens; the generator blanks comments and strings and counts characters). But one
author wrote nearly all of both, and both rest on the same picture of Lean: commands begin in the first column, a proof
opens with ':=', 'where' or a bar, and names are looked up by the same written rule, which this program states again in
its own code. Likewise its reading of a comment's blocks (blocks_of) follows the generator's (comment_html) branch for
branch, its reading of the short page's data files (s_cuts, check_short) follows the generator's (cuts, short_page), and
its making of the front page (check_front) follows the generator's (front_page) step by step. A mistake in that picture
or in those rules passes both. Both take a command that begins with '#' to change nothing that a page shows, and neither
sees what a macro or an elaborator of the Lean files' own adds, changes or leaves out. A command in the first column
whose first word neither program knows is passed over; since it may do anything to what stands below it, no declaration
from its line to the end of its file can be shown on a page, and in the folders that the long page shows whole it ends
the check. Both fit Lean files written in this library's plain style; a file written to deceive them may still pass. The
pages show Lean text: what that text means to Lean, with the notations and macros declared anywhere in the library, is
Lean's to say, not these programs'. The one witness from outside is --uses-table: a table that a small Lean program
makes from a build of the library (tab-separated: module, full name, kind, the constants in the type, the constants in
the body). Neither that program nor the table is in this repository. With the table, check 5 also compares every link in
the Lean source of the first two folders with Lean's own resolution of names.
"""

import sys

if __name__ == "__main__" and not sys.flags.isolated and not getattr(sys.flags, "safe_path", False):
    del sys.path[0]  # this program's own folder: a file there with the name of a library module must not be imported

import base64
import errno
import hashlib
import json
import os
import re
import stat
import subprocess
import unicodedata
from html.parser import HTMLParser

STYLE_SHA256 = "ff579fa518883d6bce751a9b251768f3d00aef6088115a250ecc1e915b6f30d0"
SCRIPT_SHA256 = "3cb93fa637cf71cc55d5149aadcb8a382075e6e09182517bc6a06145333d575c"

FOLDERS = ("VerifiableInference", "IntegerModel")
FIRST_FILES = [
    "VerifiableInference/" + x + ".lean" if "/" not in x else x + ".lean"
    for x in (
        "Johnson/Goal/Skeleton/SoundOfVerifyAt",
        "Johnson/PVR/SoundOfTheForm",
        "Statements",
        "RandomOracleModel",
        "MoreStatements",
        "Steps",
        "ModelWeights",
        "IntegerModel/Model",
        "RequestOfTokens",
        "CanServe",
        "IntegerModel/TrueRequest",
        "IntegerModel/ModelOutput",
        "IntegerModel/Arrays/SameModel",
        "Checks",
        "ProbabilityGuards",
        "ModelGuards",
        "ModelGuardsAtReference",
    )
]
MAIN = ["VerifierAndGoals.AtTheName.sound_of_verify_at", "PV.Ride.sound_of_the_form_at"]
MAX_LINES, MAX_CHARACTERS = 60, 6000
KINDS = (
    "theorem",
    "lemma",
    "def",
    "abbrev",
    "structure",
    "class",
    "inductive",
    "instance",
    "opaque",
    "axiom",
    "example",
)
NO_PROOF = ("theorem", "lemma", "example")
MODIFIERS = ("private", "protected", "noncomputable", "partial", "unsafe", "nonrec", "local", "scoped")
IN_FORCE = (
    "variable",
    "include",
    "omit",
    "universe",
    "notation",
    "infix",
    "infixl",
    "infixr",
    "prefix",
    "postfix",
    "macro",
    "syntax",
    "macro_rules",
    "elab",
    "declare_syntax_cat",
)
CONTINUES = ("termination_by", "decreasing_by", "where", "with")
UNREADABLE = ("have", "show", "from", "by", "do", "match", "suffices", "letI", "haveI", "let_fun", "calc")
INTERPOLATING = ("s!", "m!", "f!")  # right before a string: Lean reads what stands between { and } in it as code
# Words with which Lean begins a new command wherever they stand, in the first column or not.
BEGINS_A_COMMAND = frozenset(
    KINDS
    + IN_FORCE
    + ("namespace", "section", "end", "mutual", "open", "export", "import", "attribute", "set_option", "initialize")
    + ("builtin_initialize", "elab_rules", "run_cmd", "run_elab", "run_meta", "alias", "add_decl_doc")
    + ("suppress_compilation", "assert_not_exists", "library_note", "compile_inductive", "irreducible_def")
    + ("notation3", "variable?", "binder_predicate", "unif_hint", "proof_wanted", "simproc", "dsimproc", "simproc_decl")
)
# The first words of the commands that this program knows. So is every word that begins with '#', but '#exit'.
KNOWN_COMMANDS = frozenset(
    KINDS
    + IN_FORCE
    + ("namespace", "section", "end", "open", "export", "mutual", "import", "set_option", "attribute", "deriving")
    + ("initialize", "run_cmd", "assert_not_exists", "library_note", "add_decl_doc", "compile_inductive")
    + ("suppress_compilation", "unseal", "seal")
)
TITLE = "FlashProve: Lean statements"
T_MAIN, T_CONTENTS, T_LINKED = "The main theorem", "Contents", "Linked declarations"
T_NAMED = ["Linked from the two statements above", "Linked from the Lean texts of those"]
T_HOW, T_SKIP = "How to read the entries", "Skip to the statements"
FIXED_IDS = (
    "main-theorem",
    "contents",
    "filter",
    "nomatch",
    "other",
    "onbytes",
    "panel",
    "panel-back",
    "panel-go",
    "panel-close",
    "panel-body",
)
T_PART = {
    "other": "Declared in the library's other folders",
    "onbytes": "OnBytes/: the theorems that OnBytes/THEOREMS.md lists",
}
LICENCE = "\nCopyright 2026 Anthropic PBC\nSPDX-License-Identifier: Apache-2.0\n"
HEAD_LINK = r"(?:[A-Za-z]+/)*[A-Z][A-Z-]*\.md"
BACKTICK = chr(96)
OPEN, CLOSE = "([{⟨⦃⟦⌈⌊", ")]}⟩⦄⟧⌉⌋"

# Rule 4: last parts that Lean's core, Std or Mathlib have or are likely to have.
# fmt: off
LIKELY_ELSEWHERE = {
    "map", "bind", "pure", "run", "val", "get", "set", "fst", "snd", "toFun", "comp", "symm", "trans", "mp", "mpr",
    "elim", "left", "right", "some", "none", "toList", "toArray", "toNat", "toInt", "toFinset", "card", "length",
    "size", "sum", "prod", "filter", "foldl", "foldr", "head", "tail", "take", "drop", "append", "reverse", "zip",
    "range", "mem", "subset", "union", "inter", "image", "preimage", "support", "coe", "cast", "congr", "ext", "inj",
    "injective", "surjective", "bijective", "le", "lt", "ne", "eq", "not", "and", "or", "imp", "intro", "rec",
    "casesOn", "property", "choose", "exists", "forall", "isSome", "isNone", "getD", "orElse", "default", "apply",
    "inv", "one", "zero", "add", "mul", "sub", "div", "pow", "neg", "dvd", "succ", "pred", "min", "max", "abs",
    "norm", "dist", "measure", "prob", "toReal", "toNNReal", "toOuterMeasure", "toMeasure", "toPMF", "uniform",
    "IsZero", "mapM", "forM", "foldlM", "filterMap", "flatMap", "join", "seq", "quotient", "evaluate", "eval", "index",
}
# fmt: on

# The only elements, attributes and classes that the page may use.
# fmt: off
ELEMENTS = {
    "html": {"lang"}, "head": set(), "meta": {"charset", "name", "content", "http-equiv"}, "title": set(),
    "style": set(), "body": set(), "h1": set(), "h2": {"class", "id"}, "h3": set(), "a": {"class", "href", "id"},
    "div": {"class", "id", "data-file", "data-from", "data-to"}, "p": {"class", "id", "hidden", "data-from"},
    "aside": {"id", "aria-label", "hidden"}, "button": {"type", "id"},
    "code": set(), "b": set(), "wbr": set(), "pre": set(), "ul": set(), "li": {"class"}, "nav": {"aria-label"},
    "input": {"id", "type", "placeholder", "aria-label", "hidden"}, "details": {"class", "id"}, "summary": set(),
    "main": set(), "section": set(), "article": {"class", "id", "data-file", "data-kind"},
    "span": {"class", "title"}, "script": set(),
}
CLASSES = {
    "a": {"r", "skip", "top"}, "h2": {"part"}, "div": {"head", "mod", "two", "words", "lean", "force", "text"},
    "p": {"p", "n", "i", "h1", "h2", "h3", "h4", "none", "moved", "path", "bar"}, "li": {"s1", "s2", "d1", "d2", "c1"},
    "details": {"how", "file"}, "span": {"k", "w", "ln", "c", "s", "u"}, "article": {"e"},
}
# fmt: on
VOID = {"meta", "input", "wbr"}
# Which elements may be the children of which ('tag' or 'tag.class'). An element that is not listed has none.
IN_A_COMMENT = {"p.p", "p.n", "p.i", "p.h1", "p.h2", "p.h3", "p.h4", "ul"}
CHILDREN = {
    "#root": {"html"},
    "html": {"head", "body"},
    "head": {"meta", "title", "style"},
    "body": {"a.skip", "h1", "div.head", "details.how", "main", "a.top", "aside", "script"},
    "details.how": {"summary", "div.head"},
    "div.head": {"p"},
    "p": {"a", "code"},
    "main": {"section", "nav"},
    "section": {"h2", "h2.part", "div.head", "div.mod", "article.e", "p.moved", "details.file", "p.path"},
    "nav": {"h2", "ul", "details"},
    "details": {"summary", "input", "p.none", "details", "ul"},
    "summary": {"a"},
    "ul": {"li", "li.s1", "li.s2", "li.d1", "li.d2", "li.c1"},
    "li": {"a.r", "span.k"},
    "code": {"a.r"},
    "b": {"code"},
    "article.e": {"h3", "div.two"},
    "h3": {"a", "span.k", "span.w"},
    "a": {"wbr"},
    "div.two": {"div.words", "div.lean"},
    "div.words": IN_A_COMMENT | {"p.none"},
    "div.mod": IN_A_COMMENT,
    "div.lean": {"div.force", "div.text"},
    "div.force": {"span.ln", "pre"},
    "div.text": {"span.ln", "pre", "p.none"},
    "pre": {"a.r", "span.u", "span.c", "span.s", "b"},
    "details.file": {"summary", "div.mod"},
    "p.moved": {"a.r"},
    "aside": {"p.bar", "div"},
    "p.bar": {"button", "a"},
}
for _block in ("p.p", "p.n", "p.i", "p.h1", "p.h2", "p.h3", "p.h4", "li.s1", "li.s2", "li.d1", "li.d2", "li.c1"):
    CHILDREN[_block] = {"code", "b"}

problems = {k: [] for k in range(1, 9)}
counts = {}


class GiveUp(Exception):
    """The check cannot be made at all. The message says why."""


def plainly(s):
    """For messages: a character that cannot be seen (a control character, a change of direction, a line end) is written
    as its escape, so that a name from the page or from a file cannot steer the reader's terminal or forge a line."""
    return "".join(c if c.isprintable() else c.encode("unicode_escape").decode("ascii") for c in s)


def show(line):
    """One line of the report."""
    sys.stdout.write(plainly(line) + "\n")


PREFIX = [""]  # 'short page: ' while that page is read: it then stands in front of every message and count


def bad(check, text):
    problems[check].append(PREFIX[0] + text)


def show_problems(check):
    for p in problems[check][:40]:
        show("    " + p)
    if len(problems[check]) > 40:
        show("    ... and %d more" % (len(problems[check]) - 40))


def count(key, by=1):
    counts[PREFIX[0] + key] = counts.get(PREFIX[0] + key, 0) + by


def fold(s):
    return " ".join(s.split())


def read(path, what, most):
    """The text of a plain file of at most 'most' bytes. It is opened without following a link and without waiting (a
    pipe would make the program hang); what was opened is then looked at, and no more than the bound is read. Where os
    has no O_NOFOLLOW, a look by path stands in front of the open and refuses a link: two acts, not one."""
    if not hasattr(os, "O_NOFOLLOW") and os.path.islink(path):
        raise GiveUp("%s is a link or a special file, not a plain file: %s" % (what, path))
    try:
        handle = os.open(path, os.O_RDONLY | sum(getattr(os, x, 0) for x in ("O_NOFOLLOW", "O_NONBLOCK", "O_BINARY")))
    except OSError as e:
        if e.errno == errno.ELOOP:
            raise GiveUp("%s is a link or a special file, not a plain file: %s" % (what, path))
        raise GiveUp("cannot read %s: %s" % (what, path))
    if not stat.S_ISREG(os.fstat(handle).st_mode):
        os.close(handle)
        raise GiveUp("%s is a link or a special file, not a plain file: %s" % (what, path))
    with os.fdopen(handle, "rb") as f:
        try:
            data = f.read(most + 1)
        except OSError:
            raise GiveUp("cannot read %s: %s" % (what, path))
    if len(data) > most:
        raise GiveUp("%s has more than %d bytes: %s" % (what, most, path))
    try:
        return data.decode("utf-8")
    except UnicodeDecodeError:
        raise GiveUp("%s is not UTF-8: %s" % (what, path))


# ------------------------------------------------------------------------------------------ the page


class Text(str):
    """A piece of text of the page. 'used' is set once a comparison has covered it."""

    used = False


class Node:
    def __init__(self, tag, attrs, parent):
        self.tag, self.attrs, self.parent, self.kids = tag, dict(attrs), parent, []
        self.used = set()  # the attributes that a comparison has covered

    def spend_text(self):
        """Call this only where the WHOLE text under this element, as text() gives it, has been compared."""
        for n in self.walk():
            for k in n.kids:
                if isinstance(k, Text):
                    k.used = True

    def spend_attrs(self, *names):
        """Call this where these attributes (or all) of this element have been compared with something."""
        self.used.update(names or self.attrs)

    def cls(self):
        return self.attrs.get("class", "")

    def walk(self):
        yield self
        for k in self.kids:
            if isinstance(k, Node):
                yield from k.walk()

    def text(self):
        return "".join(k if isinstance(k, str) else k.text() for k in self.kids)

    def find(self, tag, cls=None):
        return [n for n in self.walk() if n is not self and n.tag == tag and (cls is None or n.cls() == cls)]

    def children(self, tag=None, cls=None):
        return [
            n
            for n in self.kids
            if isinstance(n, Node) and (tag is None or n.tag == tag) and (cls is None or n.cls() == cls)
        ]

    def shape(self):
        """The element children as 'tag.class', for comparing with what is expected."""
        return [n.tag + ("." + n.cls() if n.cls() else "") for n in self.children()]

    def own_text(self):
        return fold("".join(k for k in self.kids if isinstance(k, str)))


class Reader(HTMLParser):
    def __init__(self):
        super().__init__(convert_charrefs=True)
        self.root = Node("#root", [], None)
        self.at, self.doctype, self.comments = self.root, None, []

    def handle_decl(self, decl):
        self.doctype = decl

    def handle_starttag(self, tag, attrs):
        if len({a for a, _ in attrs}) != len(attrs):
            bad(6, "an attribute is given twice in <%s>, line %d" % (tag, self.getpos()[0]))
        n = Node(tag, attrs, self.at)
        self.at.kids.append(n)
        if tag not in VOID:
            self.at = n

    def handle_startendtag(self, tag, attrs):
        bad(6, "<%s/> closes itself, line %d" % (tag, self.getpos()[0]))

    def handle_endtag(self, tag):
        if self.at.tag != tag:
            bad(6, "</%s> closes <%s>, line %d" % (tag, self.at.tag, self.getpos()[0]))
        else:
            self.at = self.at.parent

    def handle_data(self, data):
        self.at.kids.append(Text(data))

    def handle_comment(self, data):
        self.comments.append(data)

    def handle_pi(self, data):
        bad(6, "a processing instruction, line %d" % self.getpos()[0])

    def unknown_decl(self, data):
        bad(6, "a '<![ ... ]>' section, line %d" % self.getpos()[0])


def check_raw_text(page):
    """Check 6, before any parsing. A parser and a browser can read odd HTML differently, and what this program's
    parser drops it cannot compare. So the page's text must be of the plainest form, which all of them read alike."""
    begins = "<!DOCTYPE html>\n<!--" + LICENCE + "-->\n<html"
    if not page.startswith(begins) or not page.endswith("</script>\n</body>\n</html>\n"):
        bad(
            6,
            "the page must begin with the doctype and the two licence lines, and end with </script>, </body>, </html>",
        )
    rest = page[len(begins) - len("<html") :] if page.startswith(begins) else page
    for name in ("style", "script"):  # their text is compared by its sha256; here it is set aside
        opened, closed = "<%s>" % name, "</%s>" % name
        if rest.count(opened) != 1 or rest.lower().count(closed) != 1 or rest.find(opened) > rest.find(closed):
            bad(6, "the page must have one <%s> ... </%s>" % (name, name))
            return
        rest = rest[: rest.find(opened) + len(opened)] + rest[rest.find(closed) :]
    tag = re.compile(r'</[a-z][a-z0-9]*>|<[a-z][a-z0-9]*(?: [a-z][a-z-]*(?:="[^"<>]*")?)*>')
    left = tag.sub("", rest)
    for sign in re.finditer("[<>]", left):
        bad(
            6,
            "a '%s' that is not part of a plainly written tag: %r"
            % (sign.group(), left[max(0, sign.start() - 30) : sign.end() + 30]),
        )
    for sign in re.finditer(r"&(?!(?:lt|gt|amp|quot|#x27);)", rest):
        bad(
            6,
            "an '&' that does not begin one of the five escapes that the page uses: %r"
            % rest[sign.start() : sign.end() + 20],
        )


# ------------------------------------------------------------------------------------ the Lean files

IDC = r"\w'!?₀-₉ₐ-ₜᵢ-ᵪ"
ONE = r"(?:(?![λΠΣ])[^\W\d][%s]*|«[^»\n]*»)" % IDC
NAME = re.compile(r"%s(?:\.%s)*" % (ONE, ONE))
TOKEN = re.compile(
    r"\s+|--[^\n]*|/-|\"|'(?:\\(?:x..|u....|.)|[^\\'\n])'|%s(?:\.%s)*|:=|=>|::|\|\|\|?|." % (ONE, ONE), re.S
)


def within(path, folder):
    """Is the file at 'path' somewhere under 'folder'?"""
    return path.startswith(folder + "/")


def lean_paths(root):
    """The Lean files of the folder. A folder whose name begins with '.' is not part of the library."""
    out = []
    for folder, subfolders, names in os.walk(root):
        subfolders[:] = [x for x in subfolders if not x.startswith(".")]
        for x in names:
            if x.endswith(".lean"):
                path = os.path.relpath(os.path.join(folder, x), root).replace(os.sep, "/")
                if not stat.S_ISREG(os.lstat(os.path.join(folder, x)).st_mode):
                    raise GiveUp("%s is a link or a special file, not a plain file" % path)
                out.append(path)
    return sorted(out)


def plain_type(s):
    """The first name of a type that is a plain application 'T a b'; otherwise None."""
    out, depth = [], 0
    for ch in s:
        if ch in OPEN:
            depth += 1
        elif ch in CLOSE:
            depth -= 1
        elif depth == 0:
            out.append(ch)
    s = "".join(out).strip()
    m = NAME.match(s)
    return m.group() if m and re.fullmatch(r"[%s\s.«»]*" % IDC, s) else None


COMMAND_WORD = re.compile(
    r"(?<![%s.])(?:#exit|%s)(?![%s])" % (IDC, "|".join(sorted(BEGINS_A_COMMAND, key=len, reverse=True)), IDC)
)


class Command:
    """A command of a Lean file, from its first token in the first column to its last token."""

    def __init__(self):
        self.word = self.kind = self.name = self.full = self.doc = None
        self.start = self.end = self.shown_end = self.line = self.name_start = 0
        self.modifiers, self.namespaces, self.opens, self.lines_above = [], [], [], []
        self.trouble = None
        self.binders, self.members, self.parents, self.binder_groups, self.result_type = set(), [], [], [], None


class Lean:
    """One Lean file. tokens: (kind, start, end), kind one of c (comment), s (string or character),
    w (name or word), p (any other sign)."""

    def __init__(self, root, path):
        self.path, self.text = path, unnumbered(path, read(os.path.join(root, path), "the Lean file", 20000000))
        self.offsets = [0] + [m.end() for m in re.finditer("\n", self.text)]
        self._tokens = self._commands = self._plain = self._comments = None
        self.unknown = None  # (line, why): the first command that this program does not know; set by commands()

    def line_of(self, pos):
        lo, hi = 0, len(self.offsets) - 1
        while lo < hi:
            mid = (lo + hi + 1) // 2
            if self.offsets[mid] <= pos:
                lo = mid
            else:
                hi = mid - 1
        return lo + 1

    def tokens(self):
        if self._tokens is not None:
            return self._tokens
        t, n, pos, out = self.text, len(self.text), 0, []
        while pos < n:
            m = TOKEN.match(t, pos)
            g, end = m.group(), m.end()
            if g.isspace():
                pos = end
                continue
            if g.startswith("--"):
                kind = "c"
            elif g == "/-":
                kind, depth = "c", 1
                while depth:
                    a, b = t.find("/-", end), t.find("-/", end)
                    if b < 0:
                        raise GiveUp("%s:%d: a comment is not closed" % (self.path, self.line_of(pos)))
                    if 0 <= a < b:
                        depth, end = depth + 1, a + 2
                    else:
                        depth, end = depth - 1, b + 2
            elif g == '"':
                kind, end = "s", self._string_end(pos, out)
            elif g[0] == "'" and len(g) > 1:
                kind = "s"
            elif NAME.fullmatch(g):
                kind = "w"
            else:
                kind = "p"
            out.append((kind, pos, end))
            pos = end
        self._tokens = out
        return out

    def _string_end(self, pos, before):
        """The end of the string that opens at pos. What stands right before it tells its sort. Where this program
        cannot be sure that it ends the string where Lean does, it gives up: one quote out of step, and it would take
        the inside of Lean's next string for commands and Lean's commands for a string."""
        t, k, hashes = self.text, len(before) - 1, 0
        while k >= 0 and t[before[k][1] : before[k][2]] == "#" and before[k][2] == pos - hashes:
            hashes, k = hashes + 1, k - 1
        word = t[before[k][1] : before[k][2]] if k >= 0 and before[k][2] == pos - hashes else ""
        if word == "r":
            end = t.find('"' + "#" * hashes, pos + 1)
            if end < 0:
                raise GiveUp("%s:%d: a raw string is not closed" % (self.path, self.line_of(pos)))
            return end + 1 + hashes
        if word in INTERPOLATING:
            return self._quote_end(pos, True)
        if word.endswith("!") and word != "!":  # '!' alone is the sign for 'not'
            raise GiveUp(
                "%s:%d: a string right after '%s'. This program cannot tell whether Lean reads { } in that string as "
                "code. Put a blank between the two" % (self.path, self.line_of(pos), word)
            )
        return self._unmarked_end(pos)

    def _unmarked_end(self, pos):
        """The end of a string with nothing right before it. The word before it may still be a macro that reads { } as
        code, as in 'throwError "{f "x"}"', and this program cannot know. It takes the reading with code, which ends
        later or at the same place, and gives up if a command could begin between the two ends: then, whichever way
        Lean reads the string, this program misses no command and sees none that Lean does not see."""
        end = self._quote_end(pos, False)
        if "{" not in self.text[pos:end]:
            return end
        try:
            later = self._quote_end(pos, True)
        except GiveUp:
            later = None
        if later is None or COMMAND_WORD.search(self.text, end, later):
            raise GiveUp(
                "%s:%d: this string has a '{'. If Lean reads it as it stands, it ends in line %d. If Lean reads { } in "
                "it as code, %s. This program cannot tell which reading is Lean's. Write the brace as \\x7b"
                % (
                    self.path,
                    self.line_of(pos),
                    self.line_of(end - 1),
                    (
                        "this program cannot find its end"
                        if later is None
                        else "it ends in line %d, and between the two ends stands a word that begins a command"
                        % self.line_of(later - 1)
                    ),
                )
            )
        return later

    def _quote_end(self, pos, braces_hold_code):
        """The place after the quote that closes the string opened at pos, which is not a raw string."""
        t, j = self.text, pos + 1
        while j < len(t):
            if t[j] == "\\":
                j += 2
            elif t[j] == '"':
                return j + 1
            elif t[j] == "{" and braces_hold_code:
                depth = 0
                while j < len(t):
                    free = not re.match("[%s]" % IDC, t[j - 1])  # no name ends right before this character
                    if t.startswith(("--", "/-"), j) or t[j] == "«" or (t[j] == "'" and free):
                        raise GiveUp(
                            "%s:%d: a comment, a character in quotes or a name in « » between { and } in a string: "
                            "this program does not read these there" % (self.path, self.line_of(j))
                        )
                    if t[j] == '"':
                        if not free or t[j - 1] == "#":
                            raise GiveUp(
                                "%s:%d: between { and } in a string, a second string with a word or '#' right before "
                                "it: this program does not read these there" % (self.path, self.line_of(j))
                            )
                        j = self._unmarked_end(j)
                        continue
                    depth += (t[j] == "{") - (t[j] == "}")
                    j += 1
                    if depth == 0:
                        break
            else:
                j += 1
        raise GiveUp("%s:%d: a string is not closed" % (self.path, self.line_of(pos)))

    def comments(self):
        if self._comments is None:
            self._comments = [(a, b) for k, a, b in self.tokens() if k == "c"]
        return self._comments

    def anchor(self, first, since, behind, end):
        """(where the characters of an anchor of rows.txt stand next, from 'behind' on and before 'end'; where its row
        begins), or None. The anchor before it stands from 'since' to 'behind'. An anchor that begins like a comment
        ('/-', '--') is sought where a comment opens, and its row begins with it. Of any other anchor no character may
        stand in a comment, and it does not begin in the midst of a name. Its row takes along the comments right before
        it: each the first thing on its line, nothing but blanks and line ends up to the anchor; but none of them if the
        first of them is the comment that the anchor before opens: then they belong to that anchor's row."""
        t, at = self.text, self.text.find(first, behind, end)
        comments = [(a, b) for a, b in self.comments() if b > since and a < end]
        if first.startswith(("/-", "--")):
            while at >= 0 and not any(a == at for a, _ in comments):
                at = t.find(first, at + 1, end)
            return None if at < 0 else (at, at)
        name = "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789_'"  # plain letters alone
        while at >= 0 and (
            any(a < at + len(first) and at < b for a, b in comments) or (at and t[at - 1] in name and t[at] in name)
        ):
            at = t.find(first, at + 1, end)
        if at < 0:
            return None
        begins = at
        for a, b in reversed(comments):
            if b > begins:
                continue
            if t[b:begins].strip() or t[t.rfind("\n", 0, a) + 1 : a].strip():
                break
            if a < behind:
                return at, at
            begins = a
        return at, begins

    def plain(self):
        """The text with comments and strings replaced by blanks, for looking at names only."""
        if self._plain is None:
            out, i = [], 0
            for k, a, b in self.tokens():
                if k in "cs":
                    out += [self.text[i:a], re.sub(r"[^\n]", " ", self.text[a:b])]
                    i = b
            self._plain = "".join(out) + self.text[i:]
        return self._plain

    def commands(self):
        """The commands of the file, with everything that the checks need to know about each."""
        if self._commands is not None:
            return self._commands
        t, toks = self.text, [x for x in self.tokens()]
        word = lambda i: t[toks[i][1] : toks[i][2]]
        at_margin = set(self.offsets)
        code = [i for i, x in enumerate(toks) if x[0] != "c"]
        firsts, depth = [], 0  # depth: how many brackets of the command that is being read are still open
        body = False  # has the command that is being read come to a ':=' outside brackets?
        for n, i in enumerate(code):
            w = word(i)
            if toks[i][1] in at_margin:
                continues = (
                    depth > 0  # as for Lean: a list in brackets may go on in the first column
                    or w in CONTINUES
                    or w in ("|", ")", "]", "}", "⟩")
                    or (w in ("(", "[", "{", "⟨", "⦃") and not body)  # a binder that is not indented: before ':=' alone
                    or (w == "deriving" and n + 1 < len(code) and word(code[n + 1]) != "instance")
                )
                if not continues:
                    firsts.append(n)
                    depth, body = 0, False
            if toks[i][0] == "p" and len(w) == 1:
                depth += (w in OPEN) - (w in CLOSE)
            body = body or (w == ":=" and depth == 0)
        out, merged = [], []
        for a, n in enumerate(firsts):  # an attribute or modifier on a line of its own belongs to the next line
            if merged and merged[-1][1]:
                merged[-1] = (merged[-1][0], False)
            else:
                merged.append((n, False))
            stop_at = firsts[a + 1] if a + 1 < len(firsts) else len(code)
            k = merged[-1][0]
            k = self._skip_head(code, word, k, stop_at)[0]
            if k >= stop_at:
                merged[-1] = (merged[-1][0], True)
        starts = [n for n, _ in merged]
        scopes, pending_opens, pending_lines = [[None, [], [], []]], [], []  # [name, namespace parts, opens, lines]
        for a, n in enumerate(starts):
            stop_at = starts[a + 1] if a + 1 < len(starts) else len(code)
            c = Command()
            c.start, c.end = toks[code[n]][1], toks[code[stop_at - 1]][2]
            c.line = self.line_of(c.start)
            k, c.modifiers = self._skip_head(code, word, n, stop_at)
            c.word = word(code[k]) if k < stop_at else ""
            if c.word == "#" and k + 1 < stop_at:
                c.word += word(code[k + 1])  # '#exit', '#check' ...
            words = [word(code[j]) for j in range(k, stop_at)]
            self._refuse_second_command(c, words, [toks[code[j]] for j in range(k, stop_at)])
            signs = [word(code[j]) for j in range(n, stop_at) if toks[code[j]][0] == "p"]
            if any(signs.count(a) != signs.count(b) for a, b in zip(OPEN, CLOSE)):
                raise GiveUp(
                    "%s:%d: the brackets of the command that begins here do not pair. This program cannot tell where "
                    "the command ends" % (self.path, c.line)
                )
            if self.unknown is None:
                why = self._why_unknown(c, words)
                self.unknown = (c.line, why) if why else None
            c.namespaces = [p for s in scopes for p in s[1]]
            if c.word in KINDS:
                self._read_declaration(c, toks, code, word, k, stop_at)
                if self.unknown and not c.trouble:
                    c.trouble = (
                        "line %d of its file has %s. What that command does to the text below it this program cannot "
                        "know, so nothing from there on can be shown" % self.unknown
                    )
                c.opens = [o for s in scopes for o in s[2]] + pending_opens
                c.lines_above = [l for s in scopes for l in s[3]] + pending_lines
                before = [x for x in toks[: code[n]][-1:] if x[0] == "c" and t.startswith("/--", x[1])]
                c.doc = before[0][1:] if before else None
                pending_opens, pending_lines = [], []
            elif any(x == "in" and (y in MODIFIERS or y in KINDS or y == "@") for x, y in zip(words, words[1:])):
                c.trouble = "a declaration on the same line as '%s ... in'" % c.word
            elif words and words[-1] == "in" and c.word not in ("namespace", "section", "end", "mutual"):
                pending_lines.append(c)
                if c.word == "open":
                    pending_opens.append((list(c.namespaces), words[1:-1]))
            else:
                pending_opens, pending_lines = [], []
                if c.word == "namespace":
                    scopes.append([words[1], words[1].split("."), [], []])
                elif c.word in ("section", "mutual"):
                    scopes.append([words[1] if len(words) > 1 else "", [], [], []])
                elif c.word == "end":
                    rest = words[1] if len(words) > 1 else ""
                    while len(scopes) > 1:
                        name = scopes.pop()[0]
                        if rest == name or not rest.endswith("." + name):
                            break
                        rest = rest[: -len(name) - 1]
                elif c.word == "open":
                    scopes[-1][2].append((list(c.namespaces), words[1:]))
                elif c.word in IN_FORCE:
                    scopes[-1][3].append(c)
            out.append(c)
        self._commands = out
        return out

    @staticmethod
    def _why_unknown(c, words):
        """None if this program knows the command c, else what is the matter with it, in words. An unknown command is
        passed over: it declares nothing, opens nothing, puts nothing in force. But it may be a macro of the library's
        own that does any of these: so no declaration from its line on can be shown on a page (see 'trouble')."""
        if not (c.word in KNOWN_COMMANDS or (c.word.startswith("#") and c.word not in ("#", "#exit"))):
            return "a command that this program does not know, '%s'" % c.word
        if c.word == "open":
            rest = words[1:-1] if words[-1] == "in" else words[1:]
            text = " ".join(rest)
            if not (
                rest[:1] == ["scoped"]
                or "renaming" in rest
                or re.fullmatch(r"\S+ \( .*\)", text)
                or re.fullmatch(r"\S+ hiding .*", text)
                or all(NAME.fullmatch(w) for w in rest)
            ):
                return "an 'open' command in a form that this program does not read"
        return None

    def _refuse_second_command(self, c, words, tokens):
        """Give up if a word that begins a command stands behind the first word of c. This program takes a command to
        run from one first column to the next. Lean does not: it begins a new command at such a word wherever it
        stands, so a 'variable' line that is indented under a proof would be in force below and be shown nowhere.
        Not seen: a command that the library declares for itself (macro, elab, syntax); 'seal', 'unseal'; and of the
        commands that begin with '#' all but '#exit' ('#s' is also how Mathlib writes the size of a finite set)."""
        for j in range(1, len(words)):
            w, before = words[j], words[j - 1]
            touches = tokens[j - 1][2] == tokens[j][1]  # no blank between this word and the sign before it
            if before == "#" and touches and w == "exit" and j > 1:
                w = "#exit"
            elif tokens[j][0] == "s" or w not in BEGINS_A_COMMAND:
                continue
            elif before in (".", BACKTICK) and touches:
                continue  # a name: '.abbrev', or the word quoted by a backtick
            elif before == "(" and j >= 2 and words[j - 2] == BACKTICK:
                continue  # a command that a macro quotes: it is not run here
            elif j == 1 and (c.word, w) in (("class", "inductive"), ("class", "abbrev"), ("deriving", "instance")):
                continue
            elif w == "instance":  # the attribute of that name, as in: attribute [local instance]
                i = j - 1
                while i > 0 and words[i] in ("local", "scoped", "-"):
                    i -= 1
                if words[i] in ("[", ","):
                    continue
            elif w == "open" and "in" in words[j + 1 : -1]:
                # 'open A B in' before a term or a tactic. As the command's last words it would reach the next command
                between = words[j + 1 : j + 1 + words[j + 1 :].index("in")]
                signs, other = ("(", ")", ",", "→", "-", ">"), BEGINS_A_COMMAND.union(("seal", "unseal"))
                if all(x in signs or (NAME.fullmatch(x) and x not in other) for x in between):
                    continue
            elif w == "set_option":  # 'set_option NAME VALUE in' before a term or a tactic, likewise
                q = j + 3
                while q < len(words) and words[q - 1].isdigit() and words[q].isdigit():
                    q += 1
                if q < len(words) - 1 and words[q] == "in":
                    continue
            raise GiveUp(
                "%s:%d: '%s' stands inside the command that begins in line %d. Lean begins a new command at that word; "
                "this program reads a command only from the first column of a line. Put the word there"
                % (self.path, self.line_of(tokens[j][1]), w, c.line)
            )

    def _members(self, c, toks, code, word, k, stop_at):
        """The fields of a structure or class (the first names on the lines that are indented like the first
        line after 'where'), the constructors of an inductive type (the name after each bar)."""
        if c.kind not in ("structure", "class", "inductive"):
            return []
        column = lambda j: toks[code[j]][1] - self.offsets[self.line_of(toks[code[j]][1]) - 1]
        first = lambda j: self.text[self.offsets[self.line_of(toks[code[j]][1]) - 1] : toks[code[j]][1]].strip() == ""
        depth, opened, bars, fields, indent = 0, None, [], [], None
        for j in range(k, stop_at):
            w = word(code[j])
            if toks[code[j]][0] == "p" and w in OPEN:
                depth += 1
            elif toks[code[j]][0] == "p" and w in CLOSE:
                depth -= 1
                continue
            if depth == 0 and w == "|" and j + 1 < stop_at and toks[code[j + 1]][0] == "w":
                bars.append(word(code[j + 1]))
            if opened is None:
                if depth == 0 and w in ("where", ":="):
                    opened = j
                continue
            if depth <= 1 and first(j) and w != "deriving" and (depth == 0 or w in ("(", "{", "[", "⦃")):
                if indent is None:
                    indent = column(j)
                if column(j) == indent:
                    i = j + (depth == 1)
                    while i < stop_at and word(code[i]) in ("private", "protected"):
                        i += 1
                    run = []
                    while (
                        i < stop_at and (toks[code[i]][0] == "w" or word(code[i]) == "_") and "." not in word(code[i])
                    ):
                        run.append(word(code[i]))
                        i += 1
                    if i < stop_at and word(code[i]) == "::":
                        continue
                    fields += [x for x in run if x != "_"]
        if c.kind == "inductive" or (bars and not fields):
            return bars
        return fields + ["mk"]

    @staticmethod
    def _skip_head(code, word, k, stop_at):
        """Skip attributes and modifiers. Returns (index of the command's own word, the modifiers)."""
        modifiers = []
        while k < stop_at:
            w = word(code[k])
            if w == "@" or (w == "scoped" and k + 1 < stop_at and word(code[k + 1]) == "["):
                depth, k = 0, k + 1
                while k < stop_at:
                    depth += (word(code[k]) in OPEN) - (word(code[k]) in CLOSE)
                    k += 1
                    if depth == 0:
                        break
            elif w in MODIFIERS:
                modifiers.append(w)
                k += 1
            else:
                break
        return k, modifiers

    def _read_declaration(self, c, toks, code, word, k, stop_at):
        """Name, full name, own binders, and where the shown text ends."""
        c.kind = c.word
        k += 1
        if c.kind == "class" and k < stop_at and word(code[k]) in ("inductive", "abbrev"):
            k += 1
        if c.kind == "instance" and k + 1 < stop_at and word(code[k]) == "(" and word(code[k + 1]) == "priority":
            while word(code[k]) != ")":
                k += 1
            k += 1
        if c.kind != "example" and k < stop_at and toks[code[k]][0] == "w":
            c.name, c.name_start = word(code[k]), toks[code[k]][1]
            k += 1
            parts = c.name.split(".")
            c.full = ".".join(parts[1:] if parts[0] == "_root_" else c.namespaces + parts)
        elif c.kind not in ("example", "instance"):
            c.trouble = "no name after '%s'" % c.kind
        j = k
        while j < stop_at and word(code[j]) in ("(", "[", "{", "⦃"):  # the declaration's own binders
            depth, names, colon, mentioned = 0, [], False, set()
            while j < stop_at:
                w = word(code[j])
                depth += (w in OPEN) - (w in CLOSE)
                if depth == 1 and w == ":":
                    colon = True
                elif depth == 1 and not colon and toks[code[j]][0] == "w":
                    names.append(w)
                elif depth == 1 and not colon and w not in ("(", "[", "{", "⦃", "_"):
                    names.append(None)
                elif colon and toks[code[j]][0] == "w":
                    mentioned.add(w.split(".")[0])
                j += 1
                if depth == 0:
                    break
            if colon and None not in names:
                c.binders.update(names)
                c.binder_groups.append((set(names), mentioned))
            else:
                c.binder_groups.append((set(), mentioned | {x.split(".")[0] for x in names if x}))
        depth, colon = 0, None  # the result type that the source writes: what follows the last ':' outside brackets
        for i in range(k, stop_at):
            w = word(code[i])
            if toks[code[i]][0] == "p" and (w in OPEN or w in CLOSE):
                depth += (w in OPEN) - (w in CLOSE)
            elif depth == 0 and w in (":=", "where", "|"):
                break
            elif depth == 0 and w == ":":
                colon = i
        else:
            i = stop_at
        if colon is not None:
            c.result_type = plain_type(
                " ".join(word(code[x]) if toks[code[x]][0] != "s" else '"' for x in range(colon + 1, i))
            )
        c.members = self._members(c, toks, code, word, k, stop_at)
        depth, after_extends = 0, False
        for i in range(k, stop_at if c.kind in ("structure", "class") else k):  # 'extends A, B'
            w = word(code[i])
            depth += (w in OPEN) - (w in CLOSE)
            if depth == 0 and w in ("where", ":="):
                break
            if depth == 0 and after_extends and toks[code[i]][0] == "w":
                c.parents.append(w)
            after_extends = after_extends or (depth == 0 and w == "extends")
        c.shown_end = c.end
        if c.kind not in NO_PROOF:
            after = [x for x in toks if x[1] >= c.end][:1]  # a line comment on the last line is part of the text
            if (
                after
                and after[0][0] == "c"
                and self.text.startswith("--", after[0][1])
                and self.text[c.end : after[0][1]].strip(" ") == ""
            ):
                c.shown_end = after[0][2]
            return
        depth, lets, funs = 0, 0, 0
        for j in range(k, stop_at):
            w, (kind, a, _) = word(code[j]), toks[code[j]]
            if kind == "p" and w in OPEN:
                depth += 1
            elif kind == "p" and w in CLOSE:
                depth -= 1
            elif depth == 0:
                first_on_line = self.text[self.offsets[self.line_of(a) - 1] : a].strip() == ""
                if w == ":=" and lets:
                    lets -= 1
                elif w == "|" and word(code[j - 1]) in ("fun", "λ", "with"):
                    c.trouble = "a bar after '%s' in the statement" % word(code[j - 1])
                    return
                elif w == "|":
                    level, first_sign, bars = 0, None, 0  # an arm has its '=>' before any ':=', outside brackets
                    for i in range(j + 1, stop_at):
                        x = word(code[i])
                        if toks[code[i]][0] == "p" and (x in OPEN or x in CLOSE):
                            level += (x in OPEN) - (x in CLOSE)
                        elif level == 0 and x in ("=>", ":=", "fun", "λ"):  # a pattern cannot hold a 'fun'
                            first_sign = x
                            break
                        elif level == 0 and x == "|":
                            bars += 1  # two bars before the '=>': perhaps an absolute value above a proof in arms
                    if first_sign in (":=", "fun", "λ"):
                        continue  # it opens no proof: an absolute value, say; the statement goes on
                    if first_sign != "=>" or not first_on_line or bars:
                        c.trouble = "a bar of which this program cannot tell whether it opens the proof"
                        return
                    c.shown_end = toks[code[j - 1]][2]
                    return
                elif w == ":=" or w == "where":
                    c.shown_end = toks[code[j - 1]][2]
                    return
                elif w == "let":
                    lets += 1
                elif w in ("fun", "λ"):
                    funs += 1
                elif w in ("=>", "↦") and funs:
                    funs -= 1
                elif w in UNREADABLE or w == "=>":
                    c.trouble = "'%s' outside brackets in the statement" % w
                    return
        c.trouble = "nothing opens a proof"


class Table:
    """What all the Lean files declare, read by this program."""

    def __init__(self, root, keep):
        self.decl, self.member, self.by_last, self.spaces, self.imports = {}, {}, {}, set(), {}
        self.name_at, self._visible, self.files, self.types, self.result_at, self.lines = {}, {}, {}, {}, {}, {}
        for path in lean_paths(root):
            L = Lean(root, path)
            self.imports[path], self.lines[path] = [], L.text.count("\n")
            if L.commands() and L.unknown and any(within(path, f) for f in FOLDERS):
                raise GiveUp("%s:%d: %s, in a folder that the long page shows whole" % ((path,) + L.unknown))
            for c in L.commands():
                if c.word == "#exit":
                    raise GiveUp("%s:%d: '#exit': Lean reads nothing below it, and this program would" % (path, c.line))
                if c.word == "import":
                    self.imports[path] += [x.replace(".", "/") + ".lean" for x in L.text[c.start : c.end].split()[1:]]
                for q in range(1, len(c.namespaces) + 1):
                    self.spaces.add(".".join(c.namespaces[:q]))
                if not c.full:
                    continue
                place = (path, c.line)
                record = place + (c.kind, "protected" in c.modifiers, "private" in c.modifiers)
                self.decl.setdefault(c.full, []).append(record)
                self.name_at[place] = c.full
                parts = c.full.split(".")
                self.by_last.setdefault(parts[-1], set()).add((tuple(parts), place))
                for q in range(1, len(parts) + (c.kind in ("structure", "class", "inductive"))):
                    self.spaces.add(".".join(parts[:q]))
                if c.kind in ("structure", "class"):
                    self.types[place] = c
                elif c.kind != "inductive" and c.result_type:
                    self.result_at[place] = c
                for x in c.members:
                    self.member.setdefault(c.full + "." + x, []).append(record)
                    self.by_last.setdefault(x, set()).add((tuple(parts) + (x,), place))
            if path in keep:
                self.files[path] = L
            else:
                L._tokens = L._plain = None  # the tokens of 5,000 files would not fit in memory

    def visible_from(self, path):
        """The file and all that it imports, directly or through other files."""
        if path not in self._visible:
            reached, frontier = {path}, {path}
            while frontier:
                frontier = {q for p in frontier for q in self.imports.get(p, ())} - reached
                reached |= frontier
            self._visible[path] = reached
        return self._visible[path]

    def look(self, full, path, one_part, everywhere):
        for table in (self.decl, self.member):
            out = [
                r[:2]
                for r in table.get(full, ())
                if not (r[4] and r[0] != path)
                and not (one_part and r[3] and table is self.decl)
                and (everywhere or r[0] in self.visible_from(path))
            ]
            if out:
                return out
        return []

    def opened(self, opens):
        out = []
        for here, words in opens:
            if words and (words[0] == "scoped" or "renaming" in words):  # the new names are not followed: no link
                continue
            text = " ".join(words)
            only = re.fullmatch(r"(\S+) \( (.*) \)", text) or re.fullmatch(r"(\S+) \( \)", text)
            hiding = re.fullmatch(r"(\S+) hiding (.*)", text)
            for name in ([only.group(1)] if only else [hiding.group(1)] if hiding else words):
                if name.startswith("_root_."):
                    candidates = [name[7:]]
                else:
                    candidates = [".".join(here[:q] + [name]) for q in range(len(here), -1, -1)]
                    candidates += [o[0] + "." + name for o in out]
                for cand in candidates:
                    item = (
                        cand,
                        tuple(only.group(2).split()) if only and only.lastindex == 2 else () if only else None,
                        tuple(hiding.group(2).split()) if hiding else (),
                    )
                    if cand in self.spaces and item not in out:
                        out.append(item)
        return out

    def lookup(self, name, c, path, everywhere=False):
        """Rule 2. Returns (the places that fit, how many parts of the name they take)."""
        parts = name.split(".")
        if parts[0] == "_root_":
            return self.look(".".join(parts[1:]), path, False, everywhere), len(parts)
        own = c.name.split(".")[:-1] if c.name and not c.name.startswith("_root_") else []
        here, opened = c.namespaces + own, self.opened(c.opens)
        for length in range(len(parts), 0, -1):
            begin, fit = parts[:length], []
            for q in range(len(here), 0, -1):
                fit += self.look(".".join(here[:q] + begin), path, length == 1, everywhere)
            if not fit:
                fit += self.look(".".join(begin), path, length == 1, everywhere)
                for o, only, hidden in opened:
                    if only is not None and not (length == 1 and begin[0] in only):
                        continue
                    if length == 1 and begin[0] in hidden:
                        continue
                    fit += self.look(o + "." + ".".join(begin), path, length == 1, everywhere)
            if fit:
                return sorted(set(fit)), length
        return [], 0


ID1 = ONE
ONE_PART = re.compile(r"(?<![%s.»])%s(?![%s.«])" % (IDC, ID1, IDC))
BINDER = re.compile(r"(?<![%s.])(?:∀|∃!|∃|λ|Σ|Π|∑|∏|⨆|⨅|⋃|⋂|(?:fun|let|have|obtain|suffices)(?![%s]))" % (IDC, IDC))
# '_' is a name by ID1; a second arm for it made the search double with every '_'
NAMES_THEN_COLON = re.compile(r"[(\[{⦃]\s*((?:%s\s+)*%s)\s*:" % (ID1, ID1))
TACTIC = re.compile(
    r"(?m)(?:^|(?<![%s.])by|;|·|<;>)[ \t]*(?:intro|intros|rintro|rcases|cases|induction|ext|funext|set|"
    r"generalize|rename_i|next|case|choose)(?![%s])([^\n]*)" % (IDC, IDC)
)


def group_end(text, k):
    depth = 0
    for j in range(k, len(text)):
        depth += (text[j] in OPEN) - (text[j] in CLOSE)
        if depth == 0:
            return j + 1
    return -1


def flat(text):
    """The text with blanks for the brackets and for what is inside them."""
    out, depth = [], 0
    for ch in text:
        if ch in OPEN:
            depth += 1
            out.append(" ")
        elif ch in CLOSE:
            depth -= 1
            out.append(" ")
        else:
            out.append(ch if depth == 0 or ch == "\n" else " ")
    return "".join(out)


def bound_in(text, after_where):
    """Rule 1: (the names that this Lean text binds somewhere, name -> the types written for it; None stands
    for a binding without a plain written type)."""
    types = {}

    def bind(names, type_name=None):
        for x in names:
            if x != "_":
                types.setdefault(x, set()).add(type_name)

    def plain_type(s):
        s = flat(s).strip()
        m = NAME.match(s)
        return m.group() if m and re.fullmatch(r"[%s\s.«»]*" % IDC, s) else None

    for m in NAMES_THEN_COLON.finditer(text):
        e = group_end(text, m.start())
        with_value = text.startswith(":=", m.end() - 1)
        bind(m.group(1).split(), None if e < 0 or with_value else plain_type(text[m.end() : e - 1].split(":=")[0]))
    one = re.compile(r"(?:%s|_)(?!\.)" % ID1)
    for m in BINDER.finditer(text):
        k, run = m.end(), []
        while True:
            while k < len(text) and text[k].isspace():
                k += 1
            w = one.match(text, k)
            if w:
                run.append(w.group())
                k = w.end()
            elif k < len(text) and text[k] in "([{⦃⟨":
                e = group_end(text, k)
                if e < 0:
                    break
                if ":" not in flat(text[k + 1 : e - 1]):
                    bind(ONE_PART.findall(text[k + 1 : e - 1]))
                k = e
            else:
                break
        if text.startswith(":", k) and not text.startswith(":=", k):
            depth, e = 0, k + 1  # the type runs to a comma, ':=' or '=>' outside brackets, or to a closing bracket
            while e < len(text) and not (
                depth == 0 and (text[e] in CLOSE or text[e] == "," or text.startswith((":=", "=>"), e))
            ):
                depth += (text[e] in OPEN) - (text[e] in CLOSE)
                e += 1
            bind(run, plain_type(text[k + 1 : e]))
        else:
            bind(run)
    level = flat(text)
    for m in re.finditer(r"(?<![%s.])(%s)\s*:=" % (IDC, ID1), text):
        if level[m.start()] == " ":
            bind([m.group(1)])
    for pattern in (
        TACTIC,
        re.compile(r"(?<![%s.])for\s+([^\n]*?)\s+in(?![%s])" % (IDC, IDC)),
        re.compile(r"\|([^|\n]*?)=>"),
    ):
        for m in pattern.finditer(text):
            bind(ONE_PART.findall(m.group(1)))
    for m in re.finditer(r"(?<![%s.])(?:if|match)\s+(%s)\s*:" % (IDC, ID1), text):
        bind([m.group(1)])
    for m in re.finditer(r"\{([^{}|\n]*?)\|", text):
        bind(ONE_PART.findall(re.split("[:∈]", m.group(1))[0]))
    if after_where is not None:
        rest = text[after_where:].split("\n")
        lines = [
            l for l in (rest[1:] if not rest[0].strip() else rest) if l.strip() and not l.strip().startswith("deriving")
        ]
        if lines:  # fields: the lines indented like the first one
            indent = len(lines[0]) - len(lines[0].lstrip())
            for l in lines:
                if len(l) - len(l.lstrip()) == indent and not re.match(r"\s*%s\s*::" % ID1, l):
                    m = re.match(
                        r"\s*(?:private\s+|protected\s+)?((?:%s\s+)*%s)\s*(?::|\(|\{|\[|$)" % (ID1, ID1), l
                    ) or NAMES_THEN_COLON.match(l.strip())
                    if m:
                        bind(m.group(1).split())
    return types


CODE_OPENS, CODE_CLOSES, BOLD_OPENS, BOLD_CLOSES = "\ue000", "\ue001", "\ue002", "\ue003"


def blocks_of(source, as_lines=False):
    """The blocks of a comment, read from the file: [(kind, text)]. Kinds: p a paragraph; s1, s2, d1, d2 a list item
    ('*' or '-', outer or inner); c1 text that goes on at the outer item's level after inner items; n a numbered
    paragraph; h1 to h4 a title; i an indented block, whose lines are kept. In the text, code and bold are shown by
    private signs, so that their exact places can be compared."""
    blocks, open_kind, text_column = [], None, 0
    if as_lines:  # a folded opening comment: one block, line for line
        kept = [l.rstrip() for l in source.split("\n")]
        kept[0] = kept[0].lstrip()
        while kept and not kept[0]:
            kept.pop(0)
        while kept and not kept[-1]:
            kept.pop()
        if kept:
            blocks.append(["i", kept])
        source = ""
    for number, line in enumerate(source.split("\n")):
        if number == 0:
            line = line.lstrip()  # it follows the opening sign
        words = line.strip()
        indent = len(line) - len(line.lstrip())
        item = re.match(r" *([*-]) +(?=\S)", line)
        title = re.match(r" {0,3}(#{1,4}) +(?=\S)", line)
        if not words:
            open_kind = None
        elif item:
            open_kind, text_column = ("s" if item.group(1) == "*" else "d") + ("2" if indent >= 2 else "1"), item.end()
            blocks.append([open_kind, [line[item.end() :].strip()]])
        elif open_kind in ("s2", "d2") and 0 < indent < text_column:
            open_kind = "c1"
            blocks.append([open_kind, [words]])
        elif title:
            open_kind = None
            blocks.append(["h%d" % len(title.group(1)), [line[title.end() :].strip()]])
        elif re.match(r" {0,3}(?:\((?:\d{1,2}|[a-z]|[ivx]{1,4})\)|\d{1,2}\.) ", line):
            open_kind = "n"
            blocks.append([open_kind, [words]])
        elif open_kind == "i" and indent:
            blocks[-1][1].append(line.rstrip())
        elif open_kind not in (None, "i") and bool(indent) == (open_kind != "p"):
            blocks[-1][1].append(words)
        else:
            open_kind = "i" if indent else "p"
            blocks.append([open_kind, [line.rstrip() if indent else words]])
    out = []
    for kind, lines in blocks:
        if kind == "i":
            margin = min(len(l) - len(l.lstrip()) for l in lines if l)
            lines = [l[margin:] for l in lines]
        text, pieces = "\n".join(lines), "\n".join(lines).split(BACKTICK)
        if len(pieces) % 2:  # the backticks pair up
            stars_pair_up = not as_lines and sum(p.count("**") for p in pieces[::2]) % 2 == 0
            sign = BACKTICK if as_lines else ""  # there the file's own signs are printed too
            made, bold = [], False
            for k, piece in enumerate(pieces):
                if k % 2:
                    made.append(sign + CODE_OPENS + piece + CODE_CLOSES + sign)
                elif not stars_pair_up:
                    made.append(piece)
                else:
                    for j, part in enumerate(piece.split("**")):
                        if j:
                            made.append(BOLD_CLOSES if bold else BOLD_OPENS)
                            bold = not bold
                        made.append(part)
            text = "".join(made)
        out.append((kind, text if kind == "i" else fold(text)))
    return out


def shown_block(node):
    """The text of one block of a comment on the page, with the same private signs."""
    out = []
    for k in node.kids:
        if isinstance(k, str):
            out.append(k)
        elif k.tag == "code":
            out.append(CODE_OPENS + k.text() + CODE_CLOSES)
        elif k.tag == "b":
            out.append(BOLD_OPENS + shown_block(k) + BOLD_CLOSES)
    return "".join(out)


def compare_comment(node, L, start, end, opener, what, as_lines=False):
    """Check 2 for one comment: block for block, its kind, its words, and where code and bold begin and end."""
    want = blocks_of(L.text[start + opener : end - 2], as_lines)
    got, compared = [], []
    for k in node.children():
        for b in k.children("li") if k.tag == "ul" else [k]:
            got.append((b.cls(), shown_block(b) if b.cls() == "i" else fold(shown_block(b))))
            compared.append(b)
    if got != want:
        k = next((k for k, (x, y) in enumerate(zip(got, want)) if x != y), min(len(got), len(want)))
        plain = lambda b: "%s %r" % (b[0], re.sub("[\ue000-\ue003]", "|", b[1])[:60])
        bad(
            2,
            "%s: block %d of the comment should be %s and is %s"
            % (what, k + 1, plain(want[k]) if k < len(want) else "absent", plain(got[k]) if k < len(got) else "absent"),
        )
        return
    if (node.attrs.get("data-from"), node.attrs.get("data-to")) != (str(L.line_of(start)), str(L.line_of(end - 1))):
        bad(2, "%s: the comment's line numbers are wrong" % what)
    if node.attrs.get("data-file", L.path) != L.path:
        bad(2, "%s: the comment is said to be another file's" % what)
    for b in compared:  # only the blocks that were compared: text between them is left for the last sweep to find
        b.spend_text()
    node.spend_attrs("data-from", "data-to", "data-file")
    count("blocks of comments compared", len(want))
    count("indented blocks among them, compared line by line", sum(1 for b in want if b[0] == "i"))


# ---------------------------------------------------------------------------------------- the checks


class Entry:
    """An <article> of the page, with what the page says of it and the command that this program found."""


def label(first, last):
    return "line %d" % first if first == last else "lines %d–%d" % (first, last)


def check_grammar(top, page, reader, g=None):
    """Check 6: only known elements, attributes and classes, each in its place; nothing from outside. 'g' holds the
    tables of the page at hand; without it, the long page's."""
    g = g or {
        "elements": ELEMENTS,
        "classes": CLASSES,
        "children": CHILDREN,
        "hidden": ("filter", "nomatch", "panel"),
        "style": STYLE_SHA256,
        "script": SCRIPT_SHA256,
        "links": r"#\S+|%s" % HEAD_LINK,
    }
    check_raw_text(page)
    if (reader.doctype or "").lower() != "doctype html":
        bad(6, "the page does not begin with <!DOCTYPE html>")
    if reader.comments != [LICENCE] or not page.startswith("<!DOCTYPE html>\n<!--" + LICENCE + "-->\n<html"):
        bad(6, "the only HTML comment allowed is the two licence lines, right after the doctype")
    for n in top.walk():
        if n.tag == "#root":
            continue
        if n.tag not in g["elements"]:
            bad(6, "element <%s>" % n.tag)
            continue
        here = n.tag + ("." + n.cls() if n.cls() else "")
        above = n.parent.tag + ("." + n.parent.cls() if n.parent.cls() else "")
        if here not in g["children"].get(above, ()):
            bad(6, "<%s> inside <%s>: it cannot be there" % (here, above))
        for k, v in n.attrs.items():
            if k not in g["elements"][n.tag]:
                bad(6, "attribute %s on <%s>" % (k, n.tag))
            elif k == "class" and v not in g["classes"].get(n.tag, ()):
                bad(6, "class '%s' on <%s>" % (v, n.tag))
            elif k == "hidden" and n.attrs.get("id") not in g["hidden"]:
                bad(6, "'hidden' on <%s>: part of the page could not be seen" % n.tag)
            elif k == "title" and n.cls() != "u":
                bad(6, "a tooltip on something that is not a marked name")
            elif k in ("data-from", "data-to") and not (v or "").isdigit():
                bad(6, "%s is not a number" % k)
    metas = [sorted(m.attrs.items()) for m in top.find("meta")]
    styles, scripts = top.find("style"), top.find("script")
    if len(styles) != 1 or len(scripts) != 1:
        raise GiveUp("the page must have one <style> and one <script>; it has %d and %d" % (len(styles), len(scripts)))
    style, script = styles[0].text(), scripts[0].text()
    b64 = lambda s: base64.b64encode(hashlib.sha256(s.encode()).digest()).decode()
    policy = (
        "default-src 'none'; style-src 'sha256-%s'; script-src 'sha256-%s'; base-uri 'none'; form-action 'none'"
        % (b64(style), b64(script))
    )
    if metas != [
        [("charset", "utf-8")],
        [("content", "width=device-width, initial-scale=1"), ("name", "viewport")],
        [("content", policy), ("http-equiv", "Content-Security-Policy")],
    ]:
        bad(6, "the <meta> elements must be: charset, viewport, and the policy that allows only this style and script")
    for what, text, want in (("style", style, g["style"]), ("script", script, g["script"])):
        if hashlib.sha256(text.encode()).hexdigest() != want:
            bad(6, "the %s is not the expected one: its sha256 differs from the one written in this program" % what)
    if top.find("html")[0].attrs != {"lang": "en"}:
        bad(6, '<html> must have lang="en" and nothing else')
    for n in top.find("meta") + top.find("html"):
        n.spend_attrs()
    for n in styles + scripts:
        n.spend_text()
    # An address can only act from an attribute, the style or the script. In a comment copied from a Lean file
    # it is plain text (a credit may give one).
    active = [style, script] + [v or "" for n in top.walk() for v in n.attrs.values()]
    for pattern in (r"https?:", r"\bwww\.", r"\bftp:", r"\bdata:[a-z]*[/;,]", r"\bjavascript:", r"\bfile:/", r"//"):
        for text in active:
            for m in re.finditer(pattern, text, re.I):
                if not (
                    pattern == "//"
                    and text is script
                    and re.search(r"(?m)^\s*//[^\n]*$", text[text.rfind("\n", 0, m.start()) + 1 :])
                ):
                    bad(6, "an address, or the start of one: %r" % text[max(0, m.start() - 30) : m.end() + 30])
    for a in top.find("a"):
        if not re.fullmatch(g["links"], a.attrs.get("href") or ""):
            bad(6, "a link must lead to a place on this page or to a page in the Lean folder: %r" % a.attrs.get("href"))
    count("lines of script", len([l for l in script.split("\n") if l.strip()]))
    try:
        import html5lib
    except ImportError:
        counts["html5lib is not installed, so the strict parse was skipped"] = 1
        return
    try:
        html5lib.HTMLParser(strict=True).parse(page)
        counts["parse errors found by html5lib in strict mode"] = 0
    except Exception as e:  # html5lib raises its own ParseError
        bad(6, "html5lib, strict mode: %r" % (e,))


def check_heads(top, root, folder):
    """Check 7, first half: the four head texts are the four files, line for line."""
    heads = top.find("div", "head")
    expected = [(os.path.join(folder, "head.txt"), "body")]
    expected += [(os.path.join(folder, "head-%s.txt" % x), x) for x in ("how", "other", "onbytes")]
    if len(heads) != len(expected):
        bad(7, "the page has %d head texts, not %d" % (len(heads), len(expected)))
    for node, (path, place) in zip(heads, expected):
        lines = [fold(l) for l in read(path, "the head text", 100000).split("\n") if l.strip()]
        name = os.path.basename(path)
        plain = [re.sub(r"\[([^\]]+)\]\(%s\)" % HEAD_LINK, r"\1", l).replace(BACKTICK, "") for l in lines]
        if [fold(p.text()) for p in node.children("p")] != plain or len(node.children()) != len(plain):
            bad(7, "the head text at '%s' is not %s, line for line" % (place, name))
        parent = node.parent
        at = (
            parent.tag
            if place == "body"
            else "how" if parent.cls() == "how" else (parent.children("h2") or [parent])[0].attrs.get("id")
        )
        if at != place:
            bad(7, "%s is in the wrong place" % name)
        for p in node.children("p"):
            p.spend_text()
        for a in node.find("a"):
            a.spend_attrs("href")
        links = [(a.attrs.get("href"), a.text()) for a in node.find("a")]
        if links != [(y, x) for l in lines for x, y in re.findall(r"\[([^\]]+)\]\((%s)\)" % HEAD_LINK, l)]:
            bad(7, "the links in the head text at '%s' are not those of %s" % (place, name))
        for href, _ in links:
            count("links in the head texts to other pages")
            if not os.path.isfile(os.path.join(root, href or "")):
                bad(5, "%s links to %s, which is not in the Lean folder" % (name, href))
        if re.search(r"[⟨⟩\[\]]", node.text()):
            bad(7, "%s still has a place to fill in, or a link that was not read" % name)
        count("lines of head text", len(plain))
    return {id(n) for h in heads for n in h.walk()}


def read_entry(node, table):
    """What one <article> says, compared with the file. Covers checks 1, 2 and 4 for this entry."""
    e = Entry()
    e.node, e.ident, e.path, e.kind = (
        node,
        node.attrs.get("id", ""),
        node.attrs.get("data-file", ""),
        node.attrs.get("data-kind", ""),
    )
    e.ok, e.command, e.blocks, e.printed = False, None, [], False
    if node.shape() != ["h3", "div.two"] or node.children("div")[0].shape() != ["div.words", "div.lean"]:
        bad(7, "%s: an entry must be a title and two columns" % e.ident)
        return e
    h3 = node.children("h3")[0]
    e.words, e.lean = node.children("div")[0].children("div")
    if e.path not in table.files:
        bad(1, "%s: the file %s is not in the Lean folder" % (e.ident, e.path))
        return e
    L = e.L = table.files[e.path]
    where = (h3.children("span", "w") or [Node("span", [], None)])[0].text()
    m = re.fullmatch(r"(.+):(\d+)", where)
    if not m or m.group(1) != e.path:
        bad(1, "%s: the place in the title is not in the entry's file" % e.ident)
        return e
    e.line = int(m.group(2))
    c = next((c for c in L.commands() if c.line == e.line and c.kind), None)
    if c is None or c.kind != e.kind:
        bad(1, "%s: no '%s' begins at %s" % (e.ident, e.kind, where))
        return e
    e.command = c
    if c.trouble:
        barred = L.unknown and c.line >= L.unknown[0]
        bad(
            4,
            "%s: this program cannot %s: %s"
            % (e.ident, "hold it" if barred else "tell where the statement ends", c.trouble),
        )
        return e
    # the title: the full name by this program's own reading, the kind, the place
    name = c.full or c.kind
    want_shape = ["a", "span.k", "span.w"] if c.full else ["a", "span.w"]
    want_text = "%s %s %s" % (name, c.kind, where) if c.full else "%s %s" % (c.kind, where)
    if h3.shape() != want_shape or fold(h3.text()) != want_text or h3.children("a")[0].text() != name:
        bad(5, "%s: the title should read '%s'" % (e.ident, want_text))
    if e.ident != (c.full if c.full and "private" not in c.modifiers else where):
        bad(
            5,
            "%s: the id should be the full name %s (or the place, for a private or nameless declaration)"
            % (e.ident, c.full),
        )
    if h3.children("a")[0].attrs != {"href": "#" + e.ident}:
        bad(5, "%s: the title's link must lead to the entry itself" % e.ident)
    h3.spend_text()
    h3.children("a")[0].spend_attrs()
    node.spend_attrs("id", "data-file", "data-kind")  # each was compared with this program's own reading above
    e.name = name
    # check 2: the docstring
    if c.doc:
        compare_comment(e.words, L, c.doc[0], c.doc[1], 3, e.ident)
        count("docstrings compared")
    elif e.words.shape() != ["p.none"] or fold(e.words.text()) != "no docstring" or len(e.words.attrs) != 1:
        bad(2, "%s: the file has no docstring here; the left side must say 'no docstring'" % e.ident)
    else:
        e.words.spend_text()
        count("entries without a docstring")
    e.ok = True
    return e


def check_source(e, part):
    """Checks 1 and 4 for one entry: the blocks of Lean source."""
    c, L = e.command, e.L
    first, last = c.line, L.line_of(c.shown_end - 1)
    too_long = part == "other" and (last - first + 1 > MAX_LINES or c.shown_end - c.start > MAX_CHARACTERS)
    above = []
    for v in ([] if too_long else c.lines_above):
        text = L.plain()[v.start : v.end]  # a bracket in a comment or in a string is no bracket of the command
        if v.word == "variable" and not text.rstrip().endswith(" in"):
            groups, k = [], len("variable")
            while k < len(text):
                if text[k] in "([{⦃":
                    g = group_end(text, k)
                    if g < 0:
                        raise GiveUp("%s:%d: a bracket of this 'variable' command is not closed" % (L.path, v.line))
                    groups.append(text[k:g])
                    k = g
                else:
                    k += 1
            heads = [None if g[0] == "[" else NAMES_THEN_COLON.match(g) for g in groups]
            declared = {x for h in heads if h for x in h.group(1).split()}
            first_parts = lambda s: {x.split(".")[0] for x in NAME.findall(s)}
            named_elsewhere = any(
                declared & first_parts(L.plain()[o.start : o.end]) for o in c.lines_above if o is not v
            )
            again = set()
            for names, mentioned in c.binder_groups:  # does an own binder name one of them before it is bound again?
                named_elsewhere = named_elsewhere or bool((declared - again) & mentioned)
                again |= names
            if groups and all(heads) and declared <= c.binders and not named_elsewhere:
                count("'variable' lines rightly left out: the declaration binds all their names again")
                continue
        above.append((v.start, v.end))
    want = [("force", a, b) for a, b in above] + [("text", c.start, c.shown_end)]
    blocks = e.lean.children()
    if [b.tag + "." + b.cls() for b in blocks] != ["div." + w[0] for w in want]:
        bad(
            1,
            "%s: above the source the page shows %d blocks of lines; in the file %d are in force"
            % (e.ident, len(blocks) - 1, len(want) - 1),
        )
        return
    for b, (cls, start, end) in zip(blocks, want):
        a, z = L.line_of(start), L.line_of(end - 1)
        if (
            (b.attrs.get("data-from"), b.attrs.get("data-to")) != (str(a), str(z))
            or b.children("span", "ln")[0:1] == []
            or b.children("span", "ln")[0].text() != label(a, z)
        ):
            bad(1, "%s: a block should be labelled '%s'" % (e.ident, label(a, z)))
            continue
        b.spend_attrs("data-from", "data-to")
        b.children("span", "ln")[0].spend_text()
        if too_long:
            for p in b.children("p"):
                p.spend_text()
            if b.shape() != ["span.ln", "p.none"] or fold(b.children("p")[0].text()) != "not printed":
                bad(
                    3,
                    "%s: longer than %d lines or %d characters, so it must not be printed"
                    % (e.ident, MAX_LINES, MAX_CHARACTERS),
                )
            count("entries whose source is too long to print")
            continue
        if b.shape() != ["span.ln", "pre"]:
            bad(1, "%s: a block must be its line numbers and its text" % e.ident)
            continue
        if b.children("pre")[0].text().encode() != L.text[start:end].encode():
            which = (
                4
                if cls == "text" and c.kind in NO_PROOF and L.text[start:].startswith(b.children("pre")[0].text()[:40])
                else 1
            )
            bad(
                which,
                "%s: the text shown for %s is not the file's text from its first word to its end"
                % (e.ident, label(a, z)),
            )
            continue
        b.children("pre")[0].spend_text()
        last_token = [x for x in L.tokens() if x[0] != "c" and start <= x[1] < end][-1]
        if re.fullmatch(r":=|=>|[=≠<>≤≥+\-*/∧∨→↔,:;&^∘×⊆∈∉·←↦¬]", L.text[last_token[1] : last_token[2]]):
            bad(
                1,
                "%s: the text ends in '%s', which wants something after it"
                % (e.ident, L.text[last_token[1] : last_token[2]]),
            )
        # what the page dresses as a comment, a string or the declaration's own name must be just that in the file
        dressed, at = [], 0
        for k in b.children("pre")[0].kids:
            if isinstance(k, Node) and (k.tag == "b" or k.cls() in ("c", "s")):
                dressed.append((start + at, start + at + len(k.text()), k.tag if k.tag == "b" else k.cls()))
                if k.children():
                    bad(1, "%s: a comment, string or name on the page holds other elements" % e.ident)
            at += len(k if isinstance(k, str) else k.text())
        really = [(x, min(y, end), kind) for kind, x, y in L.tokens() if kind in "cs" and start <= x < end]
        if cls == "text" and c.name:
            really.append((c.name_start, c.name_start + len(c.name), "b"))
        if sorted(dressed) != sorted(really):
            bad(
                1,
                "%s: what %s shows as comments, strings and the declaration's name is not what the file has"
                % (e.ident, label(a, z)),
            )
        count("blocks of Lean source compared, character for character")
        count("bytes of Lean source compared", len(L.text[start:end].encode()))
        e.blocks.append((b.children("pre")[0], start, end))
    e.printed = not too_long and len(e.blocks) == len(want)
    if c.kind in NO_PROOF:
        count("statements shown up to the sign that opens the proof")
    elif not too_long:
        count("declarations shown whole")


def shown_comments(L):
    """(the opening comment or None, the '/-! ... -/' comments in the first column outside declarations)."""
    toks, margin = L.tokens(), set(L.offsets)
    opening = None
    for kind, a, b in toks:
        if kind != "c":
            break
        if L.text.startswith("/-", a) and not L.text.startswith("/--", a) and a in margin:
            opening = (a, b)
            break
    spans = [(c.start, c.end) for c in L.commands() if c.kind]
    later = [
        (a, b)
        for kind, a, b in toks
        if kind == "c"
        and L.text.startswith("/-!", a)
        and a in margin
        and (a, b) != opening
        and not any(s <= a < e for s, e in spans)
    ]
    return opening, later


def opener_length(L, start):
    return 3 if L.text.startswith("/-!", start) else 2


def marks_in(holder):
    """The text of a <pre> or <code>, and its links and marked names: {start: (end, 'a' or 'u', href or tooltip)}.
    Comments, strings and the declaration's own name are replaced by blanks."""
    pieces, marks = [], {}

    def go(n, blank):
        for k in n.kids:
            if isinstance(k, str):
                pieces.append(re.sub(r"[^\n]", " ", k) if blank else k)
            elif k.tag == "a" or (k.tag == "span" and k.cls() == "u"):
                at = sum(map(len, pieces))
                pieces.append(k.text())
                k.spend_attrs("href" if k.tag == "a" else "title")  # every mark is compared, or reported as left over
                marks[at] = (
                    at + len(k.text()),
                    "a" if k.tag == "a" else "u",
                    k.attrs.get("href", "").split("#", 1)[-1] if k.tag == "a" else k.attrs.get("title", ""),
                )
            else:
                go(k, True)

    go(holder, False)
    return "".join(pieces), marks


class Links:
    """Check 5: this program works out, by the written rule, what every name on the page should be."""

    def __init__(self, table, entries):
        self.table, self.entries = table, entries
        self.id_at = {(e.path, e.line): e.ident for e in entries if e.ok}
        self.bound_in_file, self.after_bracket, self.needed = {}, {}, {}

    def inherited(self, c, path, depth=0):
        out = set()
        for name in c.parents if depth < 8 else ():
            fit, length = self.table.lookup(name, c, path)
            if (
                len(fit) == 1
                and length == len(name.split("."))
                and fit[0] in self.table.types
                and self.table.types[fit[0]] is not c
            ):
                parent = self.table.types[fit[0]]
                out |= set(parent.members) | self.inherited(parent, fit[0][0], depth + 1)
        return out

    def prepare(self, e):
        """What the entry's source binds."""
        c, L = e.command, e.L
        spans = [(a, b) for _, a, b in e.blocks] if e.printed else [(c.start, c.shown_end)]
        code = "\n".join(L.plain()[a:b] for a, b in spans)
        where = re.search(r"(?<![%s])where(?![%s])" % (IDC, IDC), code) if c.kind not in NO_PROOF else None
        e.types = bound_in(code, where.end() if where else None)
        e.bound = set(e.types) | set(c.members) | (self.inherited(c, e.path) if c.parents else set())
        self.bound_in_file.setdefault(e.path, set()).update(e.bound)
        e.named, e.plainly = [], []  # what the source links; what it links by a name written plainly

    def one(self, name, c, path, everywhere=False):
        fit, length = self.table.lookup(name, c, path, everywhere)
        return (fit[0], 0, length) if len(fit) == 1 else None

    def in_source(self, e, name):
        """Rules 1, 2, 3 and 5 for a name in Lean source: None or (place, first part, number of parts)."""
        parts = name.split(".")
        if parts[0] not in e.bound:
            return self.one(name, e.command, e.path)
        written = e.types.get(parts[0], {None})
        if len(parts) < 2 or len(written) != 1 or None in written:
            return None
        type_name = next(iter(written))
        if type_name.split(".")[0] in e.bound:
            return None
        fit_type, length = self.table.lookup(type_name, e.command, e.path)
        if fit_type and (
            len(fit_type) != 1 or length != len(type_name.split(".")) or fit_type[0] not in self.table.name_at
        ):
            return None
        if not fit_type and type_name.split(".")[-1] in self.table.by_last:
            return None  # it may be one of ours that could not be told
        full_type = self.table.name_at[fit_type[0]] if fit_type else type_name  # a type of Lean's own: as written
        fit = self.table.look(full_type + "." + parts[1], e.path, False, False)
        return (fit[0], 1, 1) if len(fit) == 1 else None

    def in_comment(self, name, c, path, bound, beside, folded):
        """Rule 6."""
        one_part = "." not in name
        if folded:  # only a name written with a dot, if one full name in all files ends with it, and it has an entry
            parts = tuple(name.split("."))
            fit = {x for x in self.table.by_last.get(parts[-1], ()) if x[0][-len(parts) :] == parts}
            place = next(iter(fit))[1] if len(fit) == 1 and not one_part and len(name) > 2 else None
            return (place, 0, len(parts)) if place in self.id_at else None
        if len(name) <= 2 or name.split(".")[0] in bound:
            return None
        if beside is None and one_part and name in self.bound_in_file.get(path, ()):
            return None
        found = self.one(name, c, path) or self.one(name, c, path, everywhere=True)
        if found and one_part and beside is not None and any(f[-1] == name and p != found[0] for f, p in beside):
            return None
        return found

    def full_name(self, found, name):
        shown = tuple(name.split(".")[found[1] : found[1] + found[2]])
        full = tuple(self.table.name_at.get(found[0], "?").split("."))
        return full if full[-len(shown) :] == shown else full + (shown[-1],)

    def compare(self, what, s, marks, m, found, itself, first_layer, in_comment=False):
        """Compare what the page does with one name with what the rule gives."""
        name, a = m.group(), m.start()
        want = None
        if found and found[0] != itself:
            pieces = list(re.finditer(ONE, name))
            x, y = a + pieces[found[1]].start(), a + pieces[found[1] + found[2] - 1].end()
            if found[0] in self.id_at:
                want = (x, (y, "a", self.id_at[found[0]]))
            else:
                if not in_comment:  # rule 7: in comments nothing is marked
                    want = (x, (y, "u", "declared in %s:%d; not shown on this page" % found[0]))
                if first_layer and not any(within(found[0][0], f) for f in FOLDERS + ("OnBytes",)):
                    bad(
                        3,
                        "%s names %s, declared in %s:%d: it should have an entry among the other folders"
                        % ((what, name) + found[0]),
                    )
            if first_layer:
                self.needed[found[0]] = True
        got = [(x, marks.pop(x)) for x in sorted(marks) if a <= x < m.end()]
        if got != ([want] if want else []):
            bad(
                5,
                "%s: the name '%s': the page has %s; the rule gives %s"
                % (what, name, [g[1][1:] for g in got] or "no link", want[1][1:] if want else "no link"),
            )
        elif want:
            count("names linked as the rule says" if want[1][1] == "a" else "names marked as the rule says")

    def names(self, s):
        for m in NAME.finditer(s):
            a = m.start()
            if a > 0 and (re.match("[%s»]" % IDC, s[a - 1])):
                continue
            yield m, (a > 1 and s[a - 1] == "." and s[a - 2] == ")"), (a > 0 and s[a - 1] == ".")

    def source(self, e, part):
        for pre, _, _ in e.blocks:
            s, marks = marks_in(pre)
            for m, after_bracket, after_dot in self.names(s):
                if after_bracket:  # rule 4
                    last = m.group().split(".")[0]
                    allowed = part is None or any(u[0] is None for u in self.after_bracket.get(last, ()))
                    by_type = self.by_result_type(e, s, m.start() - 2, last) if allowed else None
                    if by_type:  # first half: by the written result type of the bracket's first name
                        self.after_bracket.setdefault(last, []).append((part, e, by_type))
                        e.named.append((self.full_name((by_type, 0, 1), last), by_type))
                        only_last = re.compile(re.escape(last)).match(s, m.start())
                        self.compare(e.ident, s, marks, only_last, (by_type, 0, 1), (e.path, e.line), part is None)
                        continue
                    fit = self.table.by_last.get(last, ())  # second half: the only name in all files that ends so
                    if len(fit) != 1 or last in LIKELY_ELSEWHERE or not allowed:
                        if marks.pop(m.start(), None):
                            bad(5, "%s: '.%s' after a bracket is linked or marked against rule 4" % (e.ident, last))
                        continue
                    place = next(iter(fit))[1]
                    self.after_bracket.setdefault(last, []).append((part, e, place))
                    e.named.append((next(iter(fit))[0], place))
                    only_last = re.compile(re.escape(last)).match(s, m.start())
                    self.compare(e.ident, s, marks, only_last, (place, 0, 1), (e.path, e.line), part is None)
                elif not after_dot:
                    found = self.in_source(e, m.group())
                    if found and found[0] != (e.path, e.line):
                        e.named.append((self.full_name(found, m.group()), found[0]))
                        if found[1] == 0:
                            e.plainly.append(e.named[-1])
                    self.compare(e.ident, s, marks, m, found, (e.path, e.line), part is None)
            for x in marks:
                bad(5, "%s: a link or mark that does not begin a name: %r" % (e.ident, s[x : marks[x][0]]))

    def by_result_type(self, e, s, close, last):
        """Rule 4, first half. s[close] is ')'. Returns the place of 'T.last', or None."""
        depth = 0
        for j in range(close, -1, -1):
            depth += (s[j] in CLOSE) - (s[j] in OPEN)
            if depth == 0:
                break
        g = NAME.match(s, j + 1 + len(s[j + 1 :]) - len(s[j + 1 :].lstrip())) if s[j] == "(" else None
        if not g or g.group().split(".")[0] in e.bound:
            return None
        found = self.one(g.group(), e.command, e.path)
        c = self.table.result_at.get(found[0]) if found and found[2] == len(g.group().split(".")) else None
        if c is None or c.result_type.split(".")[0] in c.binders:
            return None
        t = self.one(c.result_type, c, found[0][0])
        if not t or t[2] != len(c.result_type.split(".")) or t[0] not in self.table.name_at:
            return None
        fit = self.table.look(self.table.name_at[t[0]] + "." + last, e.path, False, False)
        return fit[0] if len(fit) == 1 else None

    def comment(self, what, node, c, path, bound, beside, itself, first_layer, folded=False):
        for code in node.find("code"):
            s, marks = marks_in(code)
            for m, _, after_dot in self.names(s):
                if not after_dot:
                    found = self.in_comment(m.group(), c, path, bound, beside, folded)
                    self.compare(what, s, marks, m, found, itself, first_layer, in_comment=True)
            for x in marks:
                bad(5, "%s: a link or mark in a comment that does not begin a name" % what)


def check_list(node, want, what):
    """A <ul> of links: each line's words and target must be the expected ones. want: [(id, words, kind or None)]."""
    got = []
    for li in node.children("li"):
        a = li.children("a")
        kind = li.children("span", "k")
        got.append(
            (
                a[0].attrs.get("href", "")[1:] if a else None,
                a[0].text() if a else None,
                kind[0].text() if kind else None,
            )
        )
        if fold(li.text()) != fold("%s %s" % (got[-1][1], got[-1][2] or "")):
            bad(7, "%s: a line has other words than a name" % what)
        if not a or a[0].attrs != {"class": "r", "href": "#%s" % got[-1][0]} or li.attrs:
            bad(5, "%s: a line must hold one link of the kind that opens a card" % what)
        li.spend_text()
        for x in a:
            x.spend_attrs()
    if got != want or len(node.children()) != len(got):
        k = next((k for k, (x, y) in enumerate(zip(got, want)) if x != y), min(len(got), len(want)))
        bad(
            5,
            "%s: line %d should be %s and is %s (%d lines, %d expected)"
            % (
                what,
                k + 1,
                want[k] if k < len(want) else "absent",
                got[k] if k < len(got) else "absent",
                len(got),
                len(want),
            ),
        )


def with_lean_table(path, entries, links, by_id):
    """Check 5 with Lean's own table: is the target of each link among the constants that Lean found?"""
    rows, kids, in_lines, undecided, confirmed_last = {}, {}, {}, [], set()
    for l in read(path, "Lean's table", 200000000).split("\n"):
        cells = l.split("\t")
        if len(cells) >= 4:
            rows[cells[1]] = (set(cells[3].split()), set(cells[4].split()) if len(cells) > 4 else set())
    for name in rows:
        if "." in name:
            kids.setdefault(name.rsplit(".", 1)[0], []).append(name)
    for e in entries:
        if not e.printed or e.part is not None:
            continue
        found = [
            (a, (e.path, pre.parent.attrs["data-from"], n) if pre.parent.cls() == "force" else None)
            for pre, _, _ in e.blocks
            for n, a in enumerate(pre.find("a", "r"))
        ]
        if e.ident not in rows:
            count("Lean's table: links in entries that it does not have (nameless or private)", len(found))
            continue
        used = set(rows[e.ident][0]) | (set() if e.kind in NO_PROOF else rows[e.ident][1])
        for k in kids.get(e.ident, ()):
            if e.kind in ("structure", "class", "inductive") or re.match(r"_|match_\d|proof_\d", k.rsplit(".", 1)[1]):
                used |= rows[k][0] | rows[k][1]
        for a, line_key in found:
            target, words = a.attrs["href"][1:], a.text()
            last = words.split(".")[-1]
            is_member = not (target == words or target.endswith("." + words))
            yes = (target + "." + last in used) if is_member else (target in used)
            namesakes = sorted(
                u for u in used if u.split(".")[-1] == last and u not in (target, target + "." + last, e.ident)
            )
            if yes:
                confirmed_last.add(last)
            if line_key:  # a declaration takes up only some variables: any declaration below the line may confirm
                state = in_lines.setdefault(line_key, [False, None, "%s -> %s" % (words, target)])
                state[0] = state[0] or yes
                state[1] = state[1] or (namesakes and (e.ident, namesakes))
            elif yes:
                count("Lean's table: links in sources confirmed")
            elif namesakes:
                bad(
                    5,
                    "%s: '%s' links to %s, but by Lean's table the declaration uses %s"
                    % (e.ident, words, target, namesakes),
                )
            else:
                count("Lean's table: links in sources that it cannot decide")
                undecided.append("%s: %s -> %s" % (e.ident, words, target))
        linked = {a.attrs["href"][1:] for a, _ in found}
        text = " ".join(pre.text() for pre, _, _ in e.blocks[-1:])
        for u in used:
            if (
                u in by_id
                and u not in linked
                and u != e.ident
                and re.search(r"(?<![%s])%s(?![%s])" % (IDC, re.escape(u.split(".")[-1]), IDC), text)
            ):
                count("Lean's table: constants with an entry whose last part is in the source without a link")
    for key, (yes, namesakes, what) in sorted(in_lines.items()):
        if yes:
            count("Lean's table: links in lines above declarations confirmed")
        elif namesakes:
            bad(
                5,
                "%s:%s: the link %s: no declaration below the line uses the target, and %s uses %s"
                % (key[:2] + (what,) + namesakes),
            )
        else:
            count("Lean's table: links in lines above declarations that it cannot decide")
    for last, uses in sorted(links.after_bracket.items()):
        if last not in confirmed_last:
            bad(
                5,
                "'.%s' after a bracket is linked (%d times), but Lean's table confirms no such link"
                % (last, len(uses)),
            )
    return undecided


# ------------------------------------------------------------------------------------ the short page
# What is held of it: see 'OF THE SHORT PAGE' at the top. The data files' formats: section 6 of the generator.
S_STYLE_SHA256 = "26771f3cd6ce355964b1416418681a958ed228e8d838c11ae7be63cc21d48609"
S_SCRIPT_SHA256 = "5c8695b4934dc134b65a718cb531b729359d631ecc17f93c79fa553b276a386b"
S_STATUSES = ("proved", "proved-under", "definition", "only-defined", "false-here", "not-proved")
# the last three: what a 'hypothesis' or an 'arithmetic' becomes with '| by THEOREM' or '| at-risk' behind it
S_HYPOTHESIS = (
    "assumed",
    "hypothesis",
    "arithmetic",
    "hypothesis-proved",
    "hypothesis-proved-under",
    "hypothesis-at-risk",
)
AUDITED = "scripts/top-theorems.txt"  # in the Lean folder: the theorems whose axioms the library's own audit looks at
S_FILLED = (
    {}
)  # '{assumed}', '{named}', '{proved}', '{open}' and so on -> the counts of hypotheses, for every line of words
S_KEYWORDS = set(
    "theorem lemma def abbrev structure inductive class instance example noncomputable private protected where "
    "extends fun let do pure if then else match with at by in return have show from Type Prop Sort".split()
)
# the labels that every short page needs; 'proved-under' is needed where claims.txt uses it
S_LABELS = ("proved",) + S_STATUSES[2:]
S_LABELS += ("title", "how-much", "reach", "index", "index-words", "all", "legend", "contents", "back")
S_LINK = r"%s|#s\d+|long-page(?:#[^\s)]+)?" % HEAD_LINK  # where a link in a line of words may lead
LEAVES = {"target": "_blank", "rel": "noopener"}  # on every link to the long page, and on no other
# One line of Lean: 'l iN', N its own indentation; 'l iN oK' if the piece was cut in mid-line, at column K (K is held)
S_LINES = {"l i%d" % n for n in range(41)} | {"l i%d o%d" % (n, k) for n in range(41) for k in range(1, 101)}
# fmt: off
S_ELEMENTS = dict(ELEMENTS, header=set(), pre={"data-from", "data-to"}, section={"id"}, nav={"id", "aria-label"},
                  li={"class", "id"}, div={"class", "id", "hidden", "data-from", "data-to"},
                  a={"class", "href", "id", "target", "rel", "aria-label"})
S_CLASSES = {
    "a": {"r", "x", "tile", "top"},
    "div": {"guide", "tiles", "rows", "row", "row wide", "row solo", "row solo aside", "role", "say", "say src", "lean",
            "remark", "index", "two", "words", "force", "text", "holes"},
    "p": {"p", "n", "i", "h1", "h2", "h3", "h4", "none", "print", "lead", "legend", "open", "reach", "tag", "full",
          "where", "path", "bar", "doc"},
    "details": {"fold", "above", "part"},
    "li": {"s1", "s2", "d1", "d2", "c1"} | {"st-" + s for s in S_HYPOTHESIS},
    "span": {"k", "w", "ln", "c", "s", "u", "kw", "kind", "status", "no", "t", "slot", "sw", "first"}
    | S_LINES | {"sample st-" + s for s in S_STATUSES + S_HYPOTHESIS + ("none",)},
    "article": {"e", "card st-none"} | {"card st-" + s for s in S_STATUSES + S_HYPOTHESIS},
}
# fmt: on
_LEAN = {"a.r", "a.x", "span.u", "span.c", "span.s", "span.kw", "b"}
_WORDS = {"code", "b", "a", "a.x"}
S_CHILDREN = {
    "#root": {"html"},
    "html": {"head", "body"},
    "head": {"meta", "title", "style"},
    "body": {"div", "a.top", "aside", "script"},
    "div": {"header", "main", "article.e"},
    "header": {"p.print", "h1", "div.tiles", "nav", "p.lead", "div.guide", "details.fold", "p.legend"},
    "details.fold": {"summary", "div.guide"},
    "summary": _WORDS,
    "div.guide": {"ul", "p"},
    "div.tiles": {"a.tile"},
    "a.tile": {"span.t", "span.status", "span.slot"},
    "span.slot": {"span.sw", "code"},
    "span.status": {"code", "a.r"},
    "nav": {"p"},
    "p": _WORDS,
    "li": _WORDS | {"span.kind", "a.r", "a.x", "span.w", "span.first"},
    "span.first": {"code", "b"},
    "main": {"section"},
    "section": {"h2", "p.open", "p.reach", "div.index", "details.part", "div.holes"}
    | {"article." + c for c in S_CLASSES["article"] if c != "e"},
    "div.holes": {"p.reach", "ul"},
    "details.part": {"summary", "p.open", "p.reach", "div.holes"}
    | {"article." + c for c in S_CLASSES["article"] if c != "e"},
    "h2": {"span.no"},
    "p.reach": _WORDS,
    "p.doc": {"code", "b"},
    "div.index": {"p.path", "ul"},
    "p.tag": {"span.kind", "span.w"},
    "h3": _WORDS | {"span.k", "span.w"},
    "div.rows": {"div.row", "div.row wide", "div.row solo", "div.row solo aside", "details.above"},
    "details.above": {"summary", "div.row", "div.row wide", "div.row solo"},
    "div.row": {"div.role", "div.say", "div.say src", "div.lean"},
    "div.row wide": {"div.role", "div.lean"},
    "div.row solo": {"div.lean"},
    "div.row solo aside": {"div.lean"},
    "div.say": {"p"},
    "div.say src": IN_A_COMMENT,
    "div.lean": {"pre", "div.force", "div.text"},
    "div.remark": {"ul", "p.where"},
    "p.full": {"a.r", "span.status"},
    "ul": {"li", "li.s1", "li.s2", "li.d1", "li.d2", "li.c1"} | {"li.st-" + s for s in S_HYPOTHESIS},
    "code": {"a.r", "a.x"},
    "b": {"code"},
    "a": {"wbr", "code"},
    "a.r": {"wbr"},
    "a.x": {"code"},
    "article.e": {"h3", "div.two"},
    "div.two": {"div.words", "div.lean"},
    "div.words": IN_A_COMMENT | {"p.none"},
    "div.force": {"span.ln", "pre"},
    "div.text": {"span.ln", "pre", "p.none"},
    "pre": {"span." + c for c in S_LINES},
    "aside": {"p.bar", "div"},
    "p.bar": {"button", "a"},
}
for _c in S_CLASSES["article"]:
    if _c != "e":
        S_CHILDREN["article." + _c] = {"p.tag", "h3", "p.doc", "div.rows", "div.remark", "p.full"}
for _c in S_LINES:
    S_CHILDREN["span." + _c] = _LEAN
for _c in S_HYPOTHESIS:
    S_CHILDREN["li.st-" + _c] = {"a.r", "span.status", "span.first"}
for _block in ("p.print", "p.lead", "p.legend", "p.open", "p.where"):
    S_CHILDREN[_block] = _WORDS | {"span.sample st-" + s for s in S_STATUSES + S_HYPOTHESIS + ("none",)}
for _block in ("p.p", "p.n", "p.i", "p.h1", "p.h2", "p.h3", "p.h4", "li.s1", "li.s2", "li.d1", "li.d2", "li.c1"):
    S_CHILDREN[_block] = {"code", "b"}


def s_lines(folder, name, needed=False):
    """The lines of a small text in short/, without blank lines and remarks."""
    path = os.path.join(folder, name)
    if not os.path.lexists(path):
        if needed:
            raise GiveUp("there is no file %s" % path)
        return []
    return [l.strip() for l in read(path, "a text of the short page", 400000).split("\n") if l.strip() and l[:1] != "#"]


def s_table(folder, name, columns, needed=False):
    rows = [[c.strip() for c in l.split("|", columns - 1)] for l in s_lines(folder, name, needed)]
    if any(len(r) != columns for r in rows):
        raise GiveUp("%s: a line has not %d parts between bars" % (os.path.join(folder, name), columns))
    return rows


def s_head_line(node, line, what, root, long_name, lead=None):
    """A line of words on the page: its words, its code, and its links (to a page of the Lean folder, to a section of
    this page, to the long page), and no other element but 'lead', which the caller has looked at."""
    for place, number in S_FILLED.items():
        line = line.replace(place, number)
    md = r"\[([^\]\n]+)\]\((%s)\)" % S_LINK
    code = "%s([^%s\n]+)%s" % ((BACKTICK,) * 3)
    plain = re.sub(code, r"\1", re.sub(md, r"\1", line))
    want = [
        (
            (words, dict(LEAVES, **{"class": "x", "href": long_name + to[len("long-page") :]}))
            if to.startswith("long-page")
            else (words, {"href": to})
        )
        for words, to in ((w.replace(BACKTICK, ""), t) for w, t in re.findall(md, line))
    ]
    links = node.find("a")
    if fold(node.text()) != fold(plain) or re.search("[⟨⟩‹›]", plain):
        bad(7, "%s should read %r; it reads %r" % (what, fold(plain)[:70], fold(node.text())[:70]))
        return
    if (
        [(a.text(), a.attrs) for a in links] != want
        or [c.text() for c in node.find("code")] != re.findall(code, re.sub(md, r"\1", line))
        or any(n.tag not in ("a", "code") and n is not node and n is not lead for n in node.walk())
    ):
        bad(
            7,
            "%s has the right words, but other links or code than its line, or an element more: %r"
            % (what, fold(plain)[:70]),
        )
        return
    for a in links:
        a.spend_attrs()
        if re.fullmatch(HEAD_LINK, a.attrs["href"]) and not os.path.isfile(os.path.join(root, a.attrs["href"])):
            bad(5, "%s links to %s, which is not in the Lean folder" % (what, a.attrs["href"]))
    node.spend_text()
    count("lines of words compared with the data files")


def s_running(node, line, what, links, e, bound):
    """Words beside a declaration: a phrase, a remark, a first sentence. Code and bold where the line has them; the
    names in the code linked by rule 6 of the generator's docstring, as in a comment of that declaration."""
    want = blocks_of(line)
    if len(want) != 1 or fold(shown_block(node)) != want[0][1]:
        bad(7, "%s should read %r; it reads %r" % (what, fold(line)[:70], fold(node.text())[:70]))
        return
    links.comment(what, node, e.command, e.path, bound, [], (e.path, e.line), False)
    node.spend_text()
    count("lines of words compared with the data files")


def s_dress(pre):
    """The text of a <pre>, and for each character how it is dressed: '' | 'c' | 's' | 'b' | ('a', id) | ('u', tooltip).
    The blocks that hold one line each, and the tint of keywords, dress nothing."""
    text, dress = [], []

    def go(n, now):
        for k in n.kids:
            if isinstance(k, str):
                text.append(k)
                dress.extend([now] * len(k))
            elif k.tag == "span" and (k.cls().startswith("l i") or k.cls() == "kw"):
                if k.cls() == "kw" and (k.text() not in S_KEYWORDS or now):
                    bad(6, "tinted as a keyword: %r" % k.text()[:30])
                go(k, now)
            elif k.tag == "a":
                go(k, ("a", (k.attrs.get("href") or "").split("#", 1)[-1]))
            elif k.tag == "span" and k.cls() == "u":
                go(k, ("u", k.attrs.get("title")))
            else:
                go(k, "b" if k.tag == "b" else k.cls())

    go(pre, "")
    return "".join(text), dress


def s_tokens(node):
    """An entry as a flat list, for comparing the short page's copy with the long page's entry: the blocks of one line
    and the keywords' tint are left out, a mark that was closed at a line's end and opened again is one, and a link
    counts by the id that it leads to."""
    out = []

    def go(n):
        for k in n.kids:
            if isinstance(k, str):
                if out and out[-1][0] == "t":
                    out[-1] = ("t", out[-1][1] + k)
                else:
                    out.append(("t", k))
            elif k.tag == "span" and (k.cls().startswith("l i") or k.cls() == "kw"):
                go(k)
            else:
                attrs = dict(k.attrs)
                if k.tag == "a" and "href" in attrs:
                    attrs["href"], attrs["class"] = attrs["href"].split("#", 1)[-1], attrs.get("class") and "r"
                    attrs.pop("target", None), attrs.pop("rel", None)  # (held for every link at the end)
                opened = ("<", k.tag, tuple(sorted(attrs.items(), key=lambda kv: kv[0])))
                if out and out[-1] == (">", opened) and k.cls() in ("c", "s"):
                    out.pop()
                else:
                    out.append(opened)
                go(k)
                out.append((">", opened))

    go(node)
    return out


def s_plain_copy(node):
    """A copy of a kept entry in the long page's form, so that the long page's checks can read it."""
    copy = Node(node.tag, node.attrs.items(), None)
    if node.tag == "a" and "href" in copy.attrs:
        copy.attrs["href"] = "#" + copy.attrs["href"].split("#", 1)[-1]
        if copy.attrs.get("class") == "x":
            copy.attrs["class"] = "r"
            copy.attrs.pop("target", None), copy.attrs.pop("rel", None)

    def add(k):
        last = copy.kids[-1] if copy.kids else None
        if isinstance(k, str) and isinstance(last, str):
            copy.kids[-1] = Text(last + k)
        elif isinstance(k, Node) and isinstance(last, Node) and k.cls() in ("c", "s") and last.cls() == k.cls():
            last.kids[-1] = Text(last.kids[-1] + k.kids[0])  # closed at a line's end and opened again
        else:
            copy.kids.append(Text(k) if isinstance(k, str) else k)
            if isinstance(k, Node):
                k.parent = copy

    for k in node.kids:
        if isinstance(k, str):
            add(k)
        elif k.tag == "span" and (k.cls().startswith("l i") or k.cls() == "kw"):
            for x in s_plain_copy(k).kids:
                add(x)
        else:
            add(s_plain_copy(k))
    return copy


S_NOT_FOUND = (
    "%srows.txt, '=== %s': '@ %s' is not found in its place in the statement. The first '@' must open the declaration; "
    "each further one must come behind the one before it. An anchor that begins with '/-' or '--' is sought where a "
    "comment opens, any other outside comments and not in the midst of a name"
)


def s_cuts(L, c, rows_text, label, margins, what):
    """A card's rows in rows.txt, read again here, step by step as the generator reads them. ((margin word, phrase or
    None) of the lines in force, [(start, end, margin word, phrase or None, doc comment or None)])."""
    text, above, out = L.text, ("", None), []

    def whole_line(at):
        start = text.rfind("\n", 0, at) + 1
        return start if not text[start:at].strip() else at

    def code(at, end):
        """The text from 'at' to 'end' with a blank for each comment: the margin word by sign goes by a piece's code."""
        out = ""
        for a, b in L.comments():
            if at <= a < end:
                out, at = out + text[at:a] + " ", b
        return out + text[at:end]

    def by_sign(piece):
        words = piece.split()
        while words and (words[0] in MODIFIERS or words[0].startswith("@[")):
            words.pop(0)
        for key, word in label.items():
            for sign in key[5:].split() if key.startswith("sign ") and words else ():
                if words[0] == sign or (not re.match("[%s]" % IDC, sign[-1]) and words[0].startswith(sign)):
                    return word
        return ""

    if rows_text is not None:
        marks, margin = [], None
        for l in rows_text.split("\n"):
            if l.startswith("# margin:"):
                margin = l[len("# margin:") :].strip()
            elif l.startswith("@"):
                marks.append([l[1:].strip(), margin, []])
                margin = None
            elif l.strip() and not l.startswith("#"):
                if not marks:
                    raise GiveUp("rows.txt, '=== %s': its rows begin with words, not with '@'" % what)
                marks[-1][2].append(l.strip())
        if marks and marks[0][0] == "^":
            above = (marks[0][1] or "", " ".join(marks[0][2]) or None)
            marks.pop(0)
        given, since, behind, places = any(m[1] is not None for m in marks), c.start, c.start, []
        for k, m in enumerate(marks):
            found = L.anchor(m[0], since, behind, c.shown_end) if m[0] else None
            if not found or (k == 0 and found[0] != c.start):
                raise GiveUp(S_NOT_FOUND % ("", what, m[0]))
            places.append(whole_line(found[1]) if k else found[0])
            since, behind = found[0], found[0] + len(m[0])
        places.append(c.shown_end)
        for k, m in enumerate(marks):
            word = (m[1] or "") if given else by_sign(code(places[k], places[k + 1]))
            out.append((places[k], places[k + 1], word, " ".join(m[2]) or None, None))
    elif c.kind in ("structure", "class"):
        docs = [
            (a, b)
            for kind, a, b in L.tokens()
            if kind == "c" and c.start <= a < c.shown_end and text.startswith("/--", a)
        ]
        starts = [whole_line(a) for a, _ in docs] + [c.shown_end]
        out.append((c.start, starts[0], by_sign(code(c.start, starts[0])), None, None))
        for k, doc in enumerate(docs):
            field = NAME.search(L.plain(), doc[1], starts[k + 1])
            out.append((starts[k], starts[k + 1], margins.get(field.group(), "") if field else "", None, doc))
    else:
        out.append((c.start, c.shown_end, by_sign(code(c.start, c.shown_end)), None, None))
    return above, out


def check_short(path, root, heads, table, links, good, failed_ids, long_name, reader_of):
    """All checks of the short page but check 8. Returns its bytes."""
    folder = os.path.join(heads, "short")
    S_FILLED.clear()
    page, top, reader = reader_of(path, "the short page")
    check_grammar(
        top,
        page,
        reader,
        {
            "elements": S_ELEMENTS,
            "classes": S_CLASSES,
            "children": S_CHILDREN,
            "hidden": ("store", "panel"),
            "style": S_STYLE_SHA256,
            "script": S_SCRIPT_SHA256,
            "links": r"#\S+|%s|%s(?:#\S+)?" % (HEAD_LINK, re.escape(long_name)),
        },
    )
    label = dict(s_table(folder, "labels.txt", 2, True))
    for key in S_LABELS:
        if key not in label:
            raise GiveUp("%s: no line for '%s'" % (os.path.join(folder, "labels.txt"), key))
    titles, remarks = dict(s_table(folder, "titles.txt", 2)), {}
    for name, words in s_table(folder, "remarks.txt", 2):
        remarks.setdefault(name, []).append(words)
    remarks_link = label.get("remarks-link", "")
    rows_of, fields_of, at = {}, {}, None
    rows_path = os.path.join(folder, "rows.txt")
    for l in read(rows_path, "the rows", 1000000).split("\n") if os.path.lexists(rows_path) else ():
        if l.startswith("==="):
            at = l[3:].strip()
            if at in rows_of:
                raise GiveUp("rows.txt has '=== %s' twice" % at)
            rows_of[at], fields_of[at] = [], {}
        elif l.startswith("%") and at:
            fields_of[at][l[1:].partition("|")[0].strip()] = l[1:].partition("|")[2].strip()
        elif at:
            rows_of[at].append(l)
        elif l.strip() and not l.startswith("#"):
            raise GiveUp("rows.txt begins with something else than a remark or '=== FULL.NAME'")
    body = top.find("body")[0]
    if body.shape() != ["div", "a.top", "div", "aside", "script"]:
        raise GiveUp("the short page is not built as expected: <body> holds %s" % body.shape())
    column, store = body.children("div")
    if (
        column.attrs != {"id": "column"}
        or store.attrs != {"id": "store", "hidden": None}
        or column.shape() != ["header", "main"]
    ):
        raise GiveUp("the short page is not built as expected: its column or its store")
    column.spend_attrs()
    store.spend_attrs()
    header, main = column.children()
    by_id = {}
    for n in top.walk():
        if "id" in n.attrs:
            if n.attrs["id"] in by_id or not n.attrs["id"] or re.search(r"\s", n.attrs["id"]):
                bad(5, "an id that is empty, has blanks or is used twice: %r" % n.attrs["id"])
            by_id[n.attrs["id"]] = n

    # ---- claims.txt: the sections, the cards and their status; each card's declaration by this program's own reading
    entry_at, long_places, long_ids = (
        {e.ident: e for e in good},
        {(e.path, e.line) for e in good},
        {e.ident for e in good},
    )
    kept = {n.attrs.get("id", ""): n for n in store.children("article")}
    extra = []

    def declaration(name):
        """The long page's entry of that id. A declaration without one: read from the copy that the short page keeps, by
        the long page's own checks."""
        if name in entry_at:
            return entry_at[name]
        if name in failed_ids:
            raise GiveUp(
                "%s: its entry on the long page has failed, so the short page cannot be held against it" % name
            )
        if "e:" + name not in kept:
            raise GiveUp("claims.txt names %s: neither page has an entry of that name" % name)
        copy = s_plain_copy(kept["e:" + name])
        copy.attrs["id"] = name
        e = read_entry(copy, table)
        if not e.ok or not e.command or e.command.trouble:
            raise GiveUp("%s: the entry that the short page keeps cannot be read" % name)
        e.part = "other"
        check_source(e, e.part)
        entry_at[name] = e
        extra.append(e)
        return e

    def with_name(name, line):
        e = declaration(name)
        if not e.command.full:
            raise GiveUp("%s: a declaration without a name can have a card and nothing else" % line)
        return e

    audited = os.path.join(root, *AUDITED.split("/"))
    audited = read(audited, "the list of the audit's theorems", 20000000) if os.path.lexists(audited) else ""
    audited = {l.split()[0] for l in audited.split("\n") if l.strip() and l[:1] != "#"}
    sections, also_indexed, proved_by, typed = [], [], {}, []  # typed: (a card's status in claims.txt, its id)
    for l in s_lines(folder, "claims.txt", True):
        if l.startswith("=="):
            sections.append([l[2:].lstrip("-").strip(), [], [], l.startswith("==-")])  # '==-': its cards are folded
        elif not sections:
            raise GiveUp("claims.txt: its first line must open a section: '== title'")
        elif l.startswith(">"):
            (sections[-1][2] if sections[-1][2] else sections[-1][1]).append(l[1:].strip())
        elif l.startswith(("! reach ", "! hypotheses ")):
            sections[-1][2].append([l.split()[1], with_name(l.split(None, 2)[2].strip(), "claims.txt: " + l)])
        elif l.startswith("! folder "):
            sections[-1][2].append(["folder", l[len("! folder ") :].strip()])
        elif l.startswith("+ "):
            also_indexed.append(with_name(l[2:].strip(), "claims.txt: " + l).ident)
        else:
            name, status, more = l.split("|")[0].strip(), "".join(l.split("|")[1:2]).strip(), l.split("|")[2:]
            more = [x.strip() for x in more]
            by = [x[3:].strip() for x in more if x.startswith("by ")]
            if (
                status not in S_STATUSES + ("-",) + S_HYPOTHESIS[:3]
                or len(set(more)) != len(more)
                or len(by) + ("at-risk" in more) > (status in S_HYPOTHESIS[1:3])
                or any(x not in ("doc", "at-risk") and not x.startswith("by ") for x in more)
            ):
                raise GiveUp("claims.txt: this line is no card: %s" % l)
            e = declaration(name)
            kind = e.command.kind
            if (
                (status in S_STATUSES[:2] and kind not in ("theorem", "lemma"))
                or (status in ("definition", "only-defined") + S_HYPOTHESIS[:3] and kind in NO_PROOF)
                or (status in S_STATUSES[:2] and e.command.full not in audited)
            ):
                bad(
                    3,
                    "claims.txt calls the %s %s '%s': 'proved' and 'proved-under' are for a theorem or lemma that has "
                    "a line in %s; definition, only-defined, assumed, hypothesis and arithmetic are for no theorem, "
                    "lemma or example" % (kind, name, status, AUDITED),
                )
            if by:
                proved_by[e.ident] = with_name(by[0], "claims.txt: " + l)
            typed.append((status, e.ident))
            shown = "hypothesis-at-risk" if "at-risk" in more else status
            sections[-1][2].append((e, shown, "doc" if "doc" in more else ""))
    cards = [m[0] for s in sections for m in s[2] if isinstance(m, tuple)]
    twice = sorted({e.ident for e in cards if sum(x is e for x in cards) > 1})
    if twice or not cards:
        raise GiveUp("claims.txt has two cards for %s" % ", ".join(twice) if twice else "claims.txt has no card")
    for e in extra:  # on the short page a name that means one of them is a link; on the long page it is a marked name
        links.id_at[(e.path, e.line)] = e.ident
    for e in extra:
        links.prepare(e)
        links.source(e, e.part)
        if e.command.doc:
            links.comment(e.ident, e.words, e.command, e.path, e.bound, e.plainly, (e.path, e.line), False)
        for x in e.node.walk():  # the copy: whatever no comparison has covered fails, as at the page's end
            for k in x.kids:
                if isinstance(k, Text) and not k.used and k.strip():
                    bad(7, "%s: words in the kept entry that no comparison covers: %r" % (e.ident, fold(k)[:80]))
            for a in x.attrs:
                if a != "class" and a not in x.used:
                    bad(
                        7, "%s: in the kept entry an attribute that no comparison covers: <%s %s>" % (e.ident, x.tag, a)
                    )
    marked_there = {"declared in %s:%d; not shown on this page" % (e.path, e.line): e.ident for e in extra}
    as_here = lambda d: (
        ("a", marked_there[d[1]]) if isinstance(d, tuple) and d[0] == "u" and d[1] in marked_there else d
    )
    place_entry = {(e.path, e.line): e for e in good}
    with_card, named = {e.ident for e in cards}, {}
    for e in cards:
        for _, place in e.named:
            t = place_entry.get(place)
            if t is not None and t.ident not in with_card:
                named.setdefault(t.ident, t)
    for name in also_indexed:
        if name in with_card:
            raise GiveUp("claims.txt: '+ %s': it has a card" % name)
        named.setdefault(name, entry_at[name])

    # ---- the hypotheses: which of them a theorem proves, as far as a text can tell; how many there are
    behind_name = lambda e, end: e.L.plain()[e.command.name_start + len(e.command.name) : end]
    taken = {(m[0].path, m[0].line) for s in sections for m in s[2] if isinstance(m, tuple) and m[1] == "assumed"}
    how, one_name = {}, r"\s*:\s*%s\s*" % NAME.pattern
    for ident, t in proved_by.items():
        h = entry_at[ident]
        if t.ident not in with_card:
            named.setdefault(t.ident, t)
        said, places = behind_name(t, t.command.shown_end), [place for _, place in t.named]
        if re.fullmatch(one_name, said) and places == [(h.path, h.line)]:
            how[ident] = "hypothesis-proved"
        elif re.fullmatch(one_name + r"(?:→|->)\s*%s\s*" % NAME.pattern, said) and places[1:] == [(h.path, h.line)]:
            how[ident] = "hypothesis-proved-under" if places[0] in taken else None
        if (
            not how.get(ident)
            or t.command.kind not in ("theorem", "lemma")
            or len(h.blocks) != 1  # no 'variable' line or the like in force: it could add a parameter or a premise
            or len(t.blocks) != 1
            or not re.match(r"\s*:\s*Prop\s*:=", behind_name(h, h.command.end))
            or re.search(r"(?<![%s.])sorry(?![%s])" % (IDC, IDC), t.L.plain()[t.command.shown_end : t.command.end])
            or t.command.full not in audited
        ):
            bad(
                3,
                "claims.txt says that %s proves the hypothesis %s. For that the one must be 'def NAME : Prop :=', the "
                "other 'theorem NAME : ' and the hypothesis's name, perhaps with 'A → ' before it, A being called "
                "assumed; no line in force at either, no 'sorry' in the proof, and a line in %s"
                % (t.ident, ident, AUDITED),
            )
        how[ident] = how.get(ident) or "hypothesis-proved"
    for s in sections:
        s[2] = [(m[0], how.get(m[0].ident, m[1]), m[2]) if isinstance(m, tuple) else m for m in s[2]]
    hypotheses = [m for s in sections for m in s[2] if isinstance(m, tuple) and m[1] in S_HYPOTHESIS]
    under = {"proved-under"} & {status for status, _ in typed}
    for key in {m[1] for m in hypotheses} | {m[0] for s in sections for m in s[2] if isinstance(m, list)} | under:
        if key not in label:
            raise GiveUp("%s: no line for '%s'" % (os.path.join(folder, "labels.txt"), key))

    def counts(some, behind=""):
        out = {"{all%s}" % behind: len(some), "{assumed%s}" % behind: sum(m[1] == "assumed" for m in some)}
        for key, front in (("hypothesis", "{"), ("arithmetic", "{arithmetic-")):
            now = [m[1] for m in some if (key, m[0].ident) in typed]
            out[front + "named" + behind + "}"], out[front + "at-risk" + behind + "}"] = len(now), now.count(
                S_HYPOTHESIS[5]
            )
            out[front + "open" + behind + "}"] = now.count(key) + now.count(S_HYPOTHESIS[5])
            out[front + "proved" + behind + "}"] = now.count("hypothesis-proved")
            out[front + "proved-under" + behind + "}"] = now.count("hypothesis-proved-under")
        return {place: str(number) for place, number in out.items()}

    # the plain places hold the first structure's counts; '{named S}' and so on those of S, by its short name
    holders = [m[1] for s in sections for m in s[2] if isinstance(m, list) and m[0] == "hypotheses"]
    of_holder, fields_of_holder = {}, {}
    S_FILLED.update(counts(hypotheses))
    at_place = {(e.path, e.line): e for e in entry_at.values()}

    def family(e, depth=0):
        """e and the structures that it extends: their fields are its fields."""
        out = [e]
        for name in e.command.parents if depth < 8 else ():
            fit, length = table.lookup(name, e.command, e.path)
            parent = at_place.get(fit[0]) if len(fit) == 1 and length == len(name.split(".")) else None
            if parent is not None and parent.command.kind == "structure" and parent is not e:
                out += family(parent, depth + 1)
        return out

    for holder in reversed(holders):
        places = {place for e in family(holder) for _, place in e.named}
        own = of_holder[holder.ident] = [m for m in hypotheses if (m[0].path, m[0].line) in places]
        fields = len(own)
        if holder.command.kind == "structure":
            fields = sum(len(e.command.members) - 1 for e in family(holder))
        fields_of_holder[holder.ident] = fields
        if own and fields != len(own):
            bad(
                3,
                "'! hypotheses %s': there should be one card called a hypothesis for each field, or none"
                % holder.ident,
            )
        for behind in (" " + holder.command.name, ""):
            S_FILLED.update(counts(own, behind))
            if not own:  # no card for any of them: its fields are the hypotheses, all open
                for place in ("all", "named", "open"):
                    S_FILLED["{%s%s}" % (place, behind)] = str(fields)
    if holders and any(not any(m in own for own in of_holder.values()) for m in hypotheses):
        bad(3, "a card is called a hypothesis, and no declaration behind '! hypotheses' names it in its Lean text")
    here = with_card | set(named)

    # ---- the cards
    shown_lines, shown_above = {}, {}

    def first_sentence(e):
        """Of the doc comment: up to the first full stop that a blank follows."""
        doc = e.command.doc
        words = " ".join(e.L.text[doc[0] + 3 : doc[1] - 2].split()) if doc else ""
        full_stop = re.search(r"\.\**(?= )", words)
        return words[: full_stop.end()] if full_stop else words

    def check_pre(pre, e, a, b, reference, what):
        """One piece of Lean: the file's text from a to b, dressed as the entry that has been checked is dressed
        there."""
        L = e.L
        text, dress = s_dress(pre)
        if text.encode() != L.text[a:b].encode():
            bad(
                1,
                "%s: a piece of Lean is not the file's text of lines %d to %d"
                % (what, L.line_of(a), L.line_of(max(a, b - 1))),
            )
            return
        if pre.attrs != {"data-from": str(L.line_of(a)), "data-to": str(L.line_of(max(a, b - 1)))}:
            bad(1, "%s: a piece's line numbers are wrong" % what)
        column = a - (L.text.rfind("\n", 0, a) + 1)
        moved = [(k, n.cls().split(" o")[1]) for k, n in enumerate(pre.children()) if " o" in n.cls()]
        if moved != ([(0, str(min(column, 100)))] if column else []):
            bad(1, "%s: only a piece that was cut in mid-line is moved to the right, and by its own column" % what)
        ref_pre, start, _ = reference
        _, ref = s_dress(ref_pre)
        if dress != [as_here(d) for d in ref[a - start : b - start]]:
            bad(
                5,
                "%s: lines %d to %d lack the links, marks and colours of this declaration's entry on the long page"
                % (what, L.line_of(a), L.line_of(max(a, b - 1))),
            )
            return
        pre.spend_text()
        pre.spend_attrs()
        for n in pre.find("a") + pre.find("span", "u"):
            n.spend_attrs("href", "title")
        count("pieces of Lean compared, character for character")
        count("bytes of Lean compared", len(text.encode()))

    def first_line_of(e):
        """Of a declaration without a name: its first line, without a closing 'where'."""
        return re.sub(r"\s+where$", "", e.L.text[e.command.start : e.command.shown_end].split("\n")[0].rstrip())

    def status_is(span, e, status):
        """The word for the status; behind it, a link to the theorem that proves a hypothesis."""
        proof = [({"class": "r", "href": "#" + t.ident}, t.command.name) for t in [proved_by.get(e.ident)] if t]
        return (
            span.text() == label[status] + (" " + proof[0][1] if proof else "")
            and [(a.attrs, a.text()) for a in span.children()] == proof
        )

    def check_card(node, e, status, more, section):
        c, L, what = e.command, e.L, e.ident
        if not e.printed:
            bad(1, "%s: its source is not printed in the checked entry, so the card cannot be compared" % what)
            return
        if node.attrs != {
            "class": "card st-" + (status if status != "-" else "none"),
            "id": e.ident,
            "data-file": e.path,
            "data-kind": c.kind,
        }:
            bad(3, "%s: the card's status, id, file or kind is not claims.txt's and the file's" % what)
        node.spend_attrs()
        notes = remarks.get(c.full or "", [])
        with_doc = more == "doc" and bool(c.doc)
        if node.shape() != ["p.tag", "h3"] + ["p.doc"] * with_doc + ["div.rows"] + ["div.remark"] * bool(notes) + [
            "p.full"
        ]:
            bad(
                7,
                "%s: a card is a tag, a title, the doc comment's first sentence if claims.txt asks for it, "
                "rows, a remark "
                "if remarks.txt has one, and a foot" % what,
            )
            return
        tag, h3, rows, foot = (
            node.children()[0],
            node.children()[1],
            node.children("div", "rows")[0],
            node.children()[-1],
        )
        if with_doc:
            s_running(
                node.children("p", "doc")[0],
                first_sentence(e),
                what + ", the doc comment's first sentence",
                links,
                e,
                set(),
            )
        last = L.line_of(c.shown_end - 1)
        where = "%s:%d–%d" % (e.path, c.line, last) if last > c.line else "%s:%d" % (e.path, c.line)
        if tag.shape() != ["span.kind", "span.w"] or [x.text() for x in tag.children()] != [c.kind, where]:
            bad(1, "%s: the tag should read '%s %s'" % (what, c.kind, where))
        tag.spend_text()
        first_line = first_line_of(e)
        lay = titles.get(c.full or "") or titles.get(e.ident)
        if lay:
            s_head_line(h3, lay, what + ", the title", root, long_name)
        elif (h3.shape(), h3.text()) != (["code"], c.name or first_line):
            bad(7, "%s: the title is neither titles.txt's nor the declaration's own name" % what)
        h3.spend_text()
        door = bool(c.doc) and "comment" in label
        if (
            foot.shape() != ["a.r"] * (1 + door) + ["span.status"] * (status != "-")
            or [a.text() for a in foot.children("a")] != [c.full or first_line] + [label.get("comment")] * door
            or any(a.attrs != {"class": "r", "href": "#" + e.ident} for a in foot.children("a"))
            or (status != "-" and not status_is(foot.children("span")[0], e, status))
        ):
            bad(
                3,
                "%s: the card should end with the full name, the link to the file's comment if labels.txt has a word "
                "for it, and the word that labels.txt has for claims.txt's status, with a link to the theorem if one "
                "proves a hypothesis" % what,
            )
        foot.spend_text()
        for a in foot.find("a"):
            a.spend_attrs()
        if notes:
            remark = node.children("div", "remark")[0]
            items = remark.children("ul")[0].children("li") if remark.children("ul") else []
            if remark.shape() != ["ul"] + ["p.where"] * bool(remarks_link) or len(items) != len(notes):
                bad(7, "%s: the remark should have remarks.txt's %d lines" % (what, len(notes)))
            else:
                for li, words in zip(items, notes):
                    if words.startswith("(doc) "):  # a passage of the declaration's own doc comment
                        words = words[len("(doc) ") :]
                        if not c.doc or fold(words) not in fold(L.text[c.doc[0] + 3 : c.doc[1] - 2]):
                            bad(
                                2,
                                "%s: its doc comment does not have this '(doc)' passage of remarks.txt: %r"
                                % (what, words[:70]),
                            )
                    s_running(li, words, what + ", a remark", links, e, e.bound)
                for p in remark.children("p"):
                    s_head_line(p, remarks_link, what + ", under the remark", root, long_name)
        mine = rows_of.get(c.full or "", [])
        rows_text = "\n".join(mine) if any(l.startswith("@") for l in mine) else None
        margins = fields_of.get(c.full or "", {})
        above, pieces = s_cuts(L, c, rows_text, label, margins, what)
        if "".join(L.text[a:b] for a, b, _, _, _ in pieces) != L.text[c.start : c.shown_end]:
            bad(1, "%s: the pieces that rows.txt cuts, joined, are not the declaration's text" % what)
            return
        shape = (
            "row"
            if above[1] or any(p[3] or p[4] for p in pieces)
            else "row wide" if above[0] or any(p[2] for p in pieces) else "row solo"
        )
        in_force, text_block = e.blocks[:-1], e.blocks[-1]
        aside = [b for b in in_force if L.plain()[b[1] : b[2]].startswith("attribute")]
        part_of_it = [b for b in in_force if b not in aside]
        want = [("row solo aside", "", None, None, [(b[1], b[2], b)]) for b in aside]
        lines = sum(1 for b in in_force for l in L.text[b[1] : b[2]].split("\n") if l.strip())
        earlier = e
        if part_of_it:  # folded, if an earlier card of this section shows them: the same lines of the same file
            earlier = shown_above.setdefault((section, e.path, tuple((b[1], b[2]) for b in part_of_it)), e)
            want.append((shape, above[0], above[1], None, [(b[1], b[2], b) for b in part_of_it]))
        elif above != ("", None):
            bad(7, "%s: rows.txt has words for lines in force, and none are in force" % what)
        folded = len(want) - 1 if earlier is not e and "same-lines" in label else None
        for a, b, margin, phrase, doc in pieces:
            if doc:
                a = doc[1] + 1 if L.text[doc[1] : doc[1] + 1] == "\n" else doc[1]
            want.append((shape, margin, phrase, doc, [(a, b, text_block)]))
            lines += sum(1 for l in L.text[a:b].split("\n") if l.strip())
        shown_lines[e.ident] = lines
        got = rows.children()
        if folded is not None and folded < len(got) and got[folded].shape() == ["summary", "div." + shape]:
            name = earlier.command.name or first_line_of(earlier)
            s_head_line(
                got[folded].children()[0],
                label["same-lines"].replace("{name}", name),
                what + ", the line over its folded lines in force",
                root,
                long_name,
            )
            got[folded] = got[folded].children()[1]
        elif folded is not None:
            bad(
                1,
                "%s: its lines in force stand on the card of %s too, so they should be folded here"
                % (what, earlier.ident),
            )
            return
        if [r.cls() for r in got] != [w[0] for w in want]:
            bad(
                1,
                "%s: the card should have %d rows of these kinds: %s"
                % (what, len(want), ", ".join(w[0] for w in want)[:200]),
            )
            return
        for r, (cls, margin, phrase, doc, ranges) in zip(got, want):
            say = "div.say src" if doc else "div.say"
            parts = {"row": ["div.role", say, "div.lean"], "row wide": ["div.role", "div.lean"]}.get(cls, ["div.lean"])
            if r.shape() != parts:
                bad(7, "%s: a row should hold %s; it holds %s" % (what, parts, r.shape()))
                continue
            if cls in ("row", "row wide"):
                if r.children()[0].text() != margin or r.children()[0].children():
                    bad(7, "%s: a margin word should be %r and is %r" % (what, margin, r.children()[0].text()[:40]))
                r.children()[0].spend_text()
            if cls == "row":
                words = r.children()[1]
                if doc:  # the field's own comment, its own column taken off the lines that go on
                    column_of = doc[0] - (L.text.rfind("\n", 0, doc[0]) + 1)
                    source = L.text[doc[0] + 3 : doc[1] - 2].split("\n")
                    source = source[:1] + [l[min(column_of, len(l) - len(l.lstrip())) :] for l in source[1:]]
                    blocks = [b for k in words.children() for b in (k.children("li") if k.tag == "ul" else [k])]
                    shown = [(b.cls(), shown_block(b) if b.cls() == "i" else fold(shown_block(b))) for b in blocks]
                    if shown != blocks_of("\n".join(source)):
                        bad(2, "%s: beside a field stands something else than the field's own comment" % what)
                    else:
                        links.comment(what, words, c, e.path, e.bound, [], (e.path, e.line), False)
                        for b in blocks:
                            b.spend_text()
                        count("fields' own comments compared")
                elif phrase:
                    if words.shape() != ["p"]:
                        bad(7, "%s: a phrase should be one paragraph" % what)
                    else:
                        s_running(words.children()[0], phrase, what + ", a phrase", links, e, e.bound)
                        count("phrases compared with rows.txt")
                elif words.kids:
                    bad(7, "%s: words beside a piece for which rows.txt has none" % what)
            pres = r.children()[-1].children()
            if [p.tag for p in pres] != ["pre"] * len(ranges):
                bad(
                    1,
                    "%s: a row should hold this many blocks of Lean: %d; it holds %d" % (what, len(ranges), len(pres)),
                )
                continue
            for pre, (a, b, reference) in zip(pres, ranges):
                check_pre(pre, e, a, b, reference, what)
        count("cards compared")

    def reach(e):
        seen, unshown, todo = {}, set(), [e]
        while todo:
            for full, place in todo.pop().named:
                if place in long_places:
                    if place not in seen and place != (e.path, e.line):
                        seen[place] = place_entry[place]
                        todo.append(place_entry[place])
                else:
                    unshown.add(full)
        return seen, unshown

    got_sections = main.children("section")
    if main.shape() != ["section"] * (len(sections) + 1):
        raise GiveUp(
            "the short page should have %d sections, the index among them; it has %d"
            % (len(sections) + 1, len(got_sections))
        )
    fixed = []
    for k, (node, (title, opening, members, folded)) in enumerate(zip(got_sections, sections), 1):
        top_of_it = ["h2"] + ["p.open"] * len(opening)
        want = [
            (
                "article.card st-" + (m[1] if m[1] != "-" else "none")
                if isinstance(m, tuple)
                else "p.open" if isinstance(m, str) else "div.holes" if m[0] == "hypotheses" else "p.reach"
            )
            for m in members
        ]
        inner = node.children()[len(top_of_it) :]
        if folded and node.shape() == top_of_it + ["details.part"] and inner[0].shape()[:1] == ["summary"]:
            if "folded" not in label:
                raise GiveUp("%s: no line for 'folded'" % os.path.join(folder, "labels.txt"))
            words = label["folded"].replace("{cards}", str(sum(isinstance(m, tuple) for m in members)))
            s_head_line(inner[0].children()[0], words, "the line over the folded section %d" % k, root, long_name)
            inner = inner[0].children()[1:]
        elif folded:
            inner = None
        if (
            node.attrs != {"id": "s%d" % k}
            or node.shape()[: len(top_of_it)] != top_of_it
            or inner is None
            or [n.tag + "." + n.cls() for n in inner] != want
        ):
            bad(
                3, "section %d does not hold what claims.txt lists, in its order, folded only if claims.txt says so" % k
            )
            continue
        node.spend_attrs()
        fixed.append((node.children("h2")[0], "%d %s" % (k, title), {}))
        for p, words in zip(node.children("p", "open"), opening):
            s_head_line(p, words, "the line under section %d" % k, root, long_name)
        for n, m in zip(inner, members):
            if isinstance(m, tuple):
                check_card(n, m[0], m[1], m[2], k)
                continue
            if isinstance(m, str):
                s_head_line(n, m, "a line between the cards of section %d" % k, root, long_name)
                continue
            if m[0] == "reach":
                seen, unshown = reach(m[1])
                counted = {"name": m[1].command.full, "declarations": len(seen), "unshown": len(unshown)}
                counted["files"] = len({p for p, _ in seen})
            elif m[0] == "folder":
                paths = {p for p in table.lines if within(p, m[1])}
                counted = {"folder": m[1], "files": len(paths), "lines": sum(table.lines[p] for p in paths)}
                counted["declarations"] = sum(1 for records in table.decl.values() for r in records if r[0] in paths)
            else:  # under the counted line, one line for each hypothesis: its name, its status, its first sentence
                counted = {"name": m[1].command.full, "fields": fields_of_holder[m[1].ident]}
                for place, number in S_FILLED.items():  # in its own line the plain places are its own counts
                    if place.endswith(" %s}" % m[1].command.name):
                        counted[place[1 : -len(m[1].command.name) - 2]] = number
                own = of_holder[m[1].ident]
                lines = n.children("ul")[0].children() if n.shape() == ["p.reach", "ul"] else None
                if lines is None or len(lines) != len(own):
                    bad(3, "under '! hypotheses' there should be one line for each of its %d hypotheses" % len(own))
                    continue
                for li, (e, how, _) in zip(lines, own):
                    kids = li.children()
                    if (
                        li.attrs != {"class": "st-" + how}
                        or li.shape() != ["a.r", "span.status", "span.first"]
                        or (kids[0].attrs, kids[0].text()) != ({"class": "r", "href": "#" + e.ident}, e.command.name)
                        or not status_is(kids[1], e, how)
                    ):
                        bad(
                            3,
                            "the list of hypotheses: the line of %s has not its name, its status and its link"
                            % e.ident,
                        )
                        continue
                    for x in kids[:2] + kids[1].children():
                        x.spend_text()
                        x.spend_attrs()
                    if first_sentence(e):
                        s_running(kids[2], first_sentence(e), "the list of hypotheses, " + e.ident, links, e, set())
                    elif kids[2].kids:
                        bad(2, "the list of hypotheses: %s has no doc comment, and the line has words" % e.ident)
                n = n.children()[0]
            words = label[m[0]]
            for key, value in counted.items():
                words = words.replace("{%s}" % key, str(value))
            s_head_line(n, words, "the counted line '! %s'" % m[0], root, long_name)
            count("lines counted by program, counted again")

    # ---- the index
    node, k = got_sections[-1], len(sections) + 1
    by_file = {}
    for t in sorted(named.values(), key=lambda t: (t.path, t.line)):
        by_file.setdefault(t.path, []).append(t)
    index = node.children("div", "index")
    if (
        node.attrs != {"id": "s%d" % k}
        or node.shape() != ["h2", "p.open", "div.index"]
        or index[0].shape() != ["p.path", "ul"] * len(by_file)
    ):
        bad(3, "the index should be a title, a line, and one list for each of %d files" % len(by_file))
    else:
        node.spend_attrs()
        fixed.append((node.children("h2")[0], "%d %s" % (k, label["index"]), {}))
        s_head_line(node.children("p")[0], label["index-words"], "the line under the index's title", root, long_name)
        for p, ul, (file_path, members) in zip(index[0].children("p"), index[0].children("ul"), by_file.items()):
            fixed.append((p, file_path, {"class": "path"}))
            if len(ul.children("li")) != len(members):
                bad(3, "the index: %s should have %d lines" % (file_path, len(members)))
                continue
            for li, t in zip(ul.children("li"), members):
                kids, there = li.children(), t.ident in long_ids
                if (
                    li.shape() != ["span.kind", "a.r", "span.w", "span.first"] + ["a.x"] * there
                    or li.attrs != {"id": t.ident}
                    or [x.text() for x in kids[:3] + kids[4:]]
                    != [t.kind, t.command.full, str(t.line)] + [label["all"]] * there
                    or kids[1].attrs != {"class": "r", "href": "#" + t.ident}
                    or (
                        there
                        and kids[4].attrs != dict(LEAVES, **{"class": "x", "href": "%s#%s" % (long_name, t.ident)})
                    )
                ):
                    bad(3, "the index: the line of %s is not as expected" % t.ident)
                    continue
                li.spend_attrs()
                for x in kids[:3] + kids[4:]:
                    x.spend_text()
                    x.spend_attrs()
                words = first_sentence(t)
                if words:
                    s_running(kids[3], words, "the index, " + t.ident, links, t, set())
                elif kids[3].kids:
                    bad(2, "the index: %s has no doc comment, and the line has words" % t.ident)
                count("lines of the index compared")

    # ---- the entries kept for the hover card and the side panel: the long page's
    for n in store.find("span", "kw"):
        if n.text() not in S_KEYWORDS or n.children():
            bad(6, "tinted as a keyword: %r" % n.text()[:30])
    want_kept = [e.ident for e in cards] + list(named)
    if [n.attrs.get("id") for n in store.children()] != ["e:" + i for i in want_kept]:
        bad(3, "the entries kept at the page's end should be those of the cards and of the index, in that order")
    for n in store.children("article"):
        ident = n.attrs.get("id", "")[2:]
        e = entry_at.get(ident)
        if e is None:
            bad(3, "an entry is kept for %s, which has neither a card nor a line in the index" % ident)
            continue
        if e not in extra:  # (those were read above, by the long page's own checks)
            theirs, mine = s_tokens(e.node), s_tokens(n)
            if marked_there:  # a name that the long page marks and this page links
                swap = {}
                for title, target in marked_there.items():
                    swap[("<", "span", (("class", "u"), ("title", title)))] = (
                        "<",
                        "a",
                        (("class", "r"), ("href", target)),
                    )
                theirs = [swap.get(x, (">", swap[x[1]]) if x[0] == ">" and x[1] in swap else x) for x in theirs]
            if mine != theirs or {k: v for k, v in n.attrs.items() if k != "id"} != {
                k: v for k, v in e.node.attrs.items() if k != "id"
            }:
                bad(1, "%s: the entry kept on the short page is not the long page's entry" % ident)
                continue
        n.spend_text()
        for x in n.walk():
            x.spend_attrs()
        count("kept entries compared with the long page's")

    # ---- the head
    head = [label["title"]] + s_lines(folder, "short-head.txt")
    title = head[0]
    marks, guide = s_lines(folder, "first-print-mark.txt"), s_lines(folder, "short-guide.txt")
    tiles = []
    for l in s_lines(folder, "tiles.txt"):
        cells = [x.strip() for x in l.lstrip("+").split("|")]
        if l.startswith("+") and tiles and len(cells) == 2:
            tiles[-1][3].append(cells)
        elif not l.startswith("+") and len(cells) == 3:
            tiles.append(cells + [[]])
        else:
            raise GiveUp("tiles.txt: this line is neither a tile nor a slot: %s" % l)
    want = ["p.print"] * len(marks) + ["h1"] + ["div.tiles"] * bool(tiles) + ["nav"] + ["p.lead"] * len(head[1:])
    want += ["details.fold" if "guide" in label else "div.guide"] * bool(guide) + ["p.legend"] * 2
    if header.shape() != want:
        raise GiveUp("the short page's head should hold %s; it holds %s" % (want, header.shape()))
    fixed += [(top.find("title")[0], title, {}), (header.children("h1")[0], title, {})]
    for p, words in zip(header.children("p", "print"), marks):
        s_head_line(p, words, "the mark at the top", root, long_name)
    for p, words in zip(header.children("p", "lead"), head[1:]):
        s_head_line(p, words, "a line of the head", root, long_name)
    first = [m[0] for m in sections[0][2] if isinstance(m, tuple)]
    total = lambda es: str(sum(shown_lines.get(e.ident, 0) for e in es))
    how_much = label["how-much"].replace("{cards}", str(len(cards))).replace("{lines}", total(cards))
    how_much = how_much.replace("{cards1}", str(len(first))).replace("{lines1}", total(first))
    called = [status for status, _ in typed]  # as claims.txt calls the cards
    how_much = how_much.replace("{theorems}", str(called.count("proved") + called.count("proved-under")))
    how_much = how_much.replace("{theorems-under}", str(called.count("proved-under")))
    if guide and "guide" in label and header.children("details")[0].shape() != ["summary", "div.guide"]:
        bad(7, "the fold at the top should hold one line and the guide's box")
    elif guide:
        box, shape = header.find("div", "guide")[0], []
        if "guide" in label:
            s_head_line(header.find("summary")[0], label["guide"], "the line over the guide's box", root, long_name)
        for l in guide:
            if not (l.startswith("- ") and shape and shape[-1] == "ul"):
                shape.append("ul" if l.startswith("- ") else "p")
        lines = [x for k in box.children() for x in (k.children("li") if k.tag == "ul" else [k])]
        if box.shape() != shape or len(lines) != len(guide):
            bad(7, "the guide's box should hold short-guide.txt's %d lines" % len(guide))
        else:
            for x, l in zip(lines, guide):
                s_head_line(
                    x,
                    re.sub("‹BY PROGRAM[^›]*›", lambda _: how_much, l[2 * l.startswith("- ") :]),
                    "the guide's box",
                    root,
                    long_name,
                )
    if tiles:
        got = header.children("div", "tiles")[0].children("a")
        if len(got) != len(tiles):
            bad(7, "there should be %d tiles" % len(tiles))
        for a, (words, status, name, slots) in zip(got, tiles):
            e = entry_at.get(name)
            spans = a.children()
            if e is None or e.ident not in with_card or a.attrs != {"class": "tile", "href": "#" + name}:
                bad(5, "the tile '%s' should lead to the card of %s" % (words, name))
                continue
            if a.shape() != ["span.t", "span.status"] + ["span.slot"] * (len(slots) + 1) or spans[0].text() != words:
                bad(
                    7,
                    "the tile '%s' should have its title, its words, %d slots and the Lean name" % (words, len(slots)),
                )
                continue
            a.spend_attrs()
            spans[0].spend_text()
            s_head_line(spans[1], status, "the tile '%s'" % words, root, long_name)
            for span, (slot, text) in zip(spans[2:], slots):
                if span.shape()[:1] != ["span.sw"] or span.children()[0].text() != slot:
                    bad(7, "the tile '%s': a slot should be called '%s'" % (words, slot))
                    continue
                s_head_line(
                    span, slot + " " + text, "the tile '%s', '%s'" % (words, slot), root, long_name, span.children()[0]
                )
            if spans[-1].shape() != ["code"] or spans[-1].text() != e.command.name:
                bad(5, "the tile '%s' should end with the name %s" % (words, e.command.name))
            spans[-1].spend_text()
    nav = header.children("nav")[0]
    names = [s[0] for s in sections] + [label["index"]]
    anchors = nav.children("p")[0].children("a") if nav.shape() == ["p"] else []
    if (
        nav.attrs != {"id": "contents", "aria-label": label["contents"]}
        or [(a.attrs, a.text()) for a in anchors]
        != [({"href": "#s%d" % k}, "%d %s" % (k, t)) for k, t in enumerate(names, 1)]
        or fold(nav.text()) != " · ".join("%d %s" % (k, t) for k, t in enumerate(names, 1))
    ):
        bad(5, "the line of contents should link the %d sections by number and title" % len(names))
    nav.spend_attrs()
    nav.spend_text()
    for a in anchors:
        a.spend_attrs()
    legends = header.children("p", "legend")
    used = [
        s
        for s in S_STATUSES + S_HYPOTHESIS
        if any(isinstance(m, tuple) and m[1] == s for sec in sections for m in sec[2])
    ]
    grey = "no-status" in label and any(isinstance(m, tuple) and m[1] == "-" for sec in sections for m in sec[2])
    if legends[0].shape() != ["span.sample st-" + s for s in used + ["none"] * grey] or fold(
        legends[0].text()
    ) != " ".join([label[s] for s in used] + [label.get("no-status")] * grey):
        bad(7, "the legend should show a sample and the word of each status that the page uses")
    legends[0].spend_text()
    s_head_line(legends[1], label["legend"], "the legend", root, long_name)
    fixed.append((body.children("a")[0], "↑", {"class": "top", "href": "#contents", "aria-label": label["contents"]}))
    aside = body.children("aside")[0]
    if (
        aside.attrs != {"id": "panel", "aria-label": "Entry", "hidden": None}
        or aside.shape() != ["p.bar", "div"]
        or aside.children("p")[0].shape() != ["button", "a", "button"]
        or aside.children("div")[0].kids
        or aside.children("div")[0].attrs != {"id": "panel-body"}
    ):
        bad(7, "the side panel is not the expected empty frame")
    else:
        aside.spend_attrs()
        aside.children("div")[0].spend_attrs()
        bar = aside.children("p")[0].children()
        fixed += [
            (bar[0], "back", {"type": "button", "id": "panel-back"}),
            (bar[1], "go to the entry", {"id": "panel-go", "href": "#s1"}),
            (bar[2], "close", {"type": "button", "id": "panel-close"}),
        ]
    for n, words, attrs in fixed:
        if fold(n.text()) != fold(words) or n.attrs != attrs:
            bad(
                7,
                "<%s> should read '%s' with the attributes %s; it reads '%s' with %s"
                % (n.tag, words, attrs, fold(n.text())[:60], n.attrs),
            )
        n.spend_text()
        n.spend_attrs()

    # ---- every link leads where its kind says; nothing is left that no comparison has covered
    for a in top.find("a"):
        href, cls = a.attrs.get("href") or "", a.cls()
        if {k: v for k, v in a.attrs.items() if k in LEAVES} != (LEAVES if cls == "x" else {}):
            bad(6, "a link to the long page, and no other, opens a tab of its own: %r" % href)
        a.spend_attrs("target", "rel")
        if cls == "r" and (href[:1] != "#" or href[1:] not in here):
            bad(
                5,
                "a link of the kind that opens a card leads to %r, which has neither a card nor a line in the index"
                % href,
            )
        elif (
            cls == "x"
            and href != long_name
            and (not href.startswith(long_name + "#") or href.split("#", 1)[1] not in long_ids)
        ):
            bad(5, "a link to the long page leads to %r, which is no entry there" % href)
        elif cls == "x" and href.split("#", 1)[-1] in here and a.parent.tag not in ("li", "p", "h3"):
            bad(5, "a name that has a card or a line in the index here is linked to the long page: %r" % href)
        elif cls not in ("r", "x") and href[:1] == "#" and href[1:] not in by_id:
            bad(5, "a link that leads nowhere on the page: %s" % href)
        else:
            count("links that lead where their kind says")
    for n in top.walk():
        for k in n.kids:
            if isinstance(k, Text) and not k.used and k.strip():
                bad(7, "words that no comparison covers, in <%s>: %r" % (n.tag, fold(k)[:80]))
        for a in n.attrs:
            if a != "class" and a not in n.used:
                bad(7, "an attribute that no comparison covers: <%s %s=%r>" % (n.tag, a, (n.attrs[a] or "")[:60]))
    return page.encode("utf-8")


# ------------------------------------------------------------------------------------ the front page
# The front page is built on the shell: a frame, a style sheet and a script (shell/ORIGIN.txt;
# the body's markup that this part writes, its elements and class names, follows the frame),
# used unchanged except for the lines listed in shell/turns.txt. This program builds the whole page again, from its own
# reading of the Lean files, the data files and the shell, and compares the page with the result, part by part. So every
# byte of the page is one that this program expects. It imports nothing from the generator. The data files' formats are
# described in section 7 of the generator; the code that reads them here was written after it, by the same author.

F_SHELL = ("page_template.html", "page.css", "page.js", "turns.txt")
F_LICENCE = ""  # the front page's comment is the two lines of every page
F_SHELL_SHA256 = {  # the shell as it ships with this program: check 6 holds the four files to these
    "page_template.html": "f208148e85bbe5b75d349260cdb85263b0c2b58e9e95bac569a2a78256264df5",
    "page.css": "4f1b2bb263a9fb28511cb175714195fe600ff8e0da57153e69a027904f652bc3",
    "page.js": "70c6a74cd3415ab17585007a843e4dfc4adfc9ac9e69db4efb79e13efa194ec6",
    "turns.txt": "5c370cfdf9006cc381c7da5c092ed771cc2288707c1a62bca062aeb83089af92",
}
F_PILLS = ("target", "cond", "full", "none")


def f_group_title(label, top):
    """What the page must print as the title of the group top in the list of definitions: the words of the line
    'group-TOP | words' of labels.txt if it is there and has words, else top itself."""
    words = label.get("group-" + top, "")
    return words if words else top


def f_idle_group_lines(label, tops):
    """The keys 'group-TOP' of labels.txt for which the list of definitions has no group TOP, in order."""
    there = {"group-" + top for top in tops}
    return sorted(key for key in label if key.startswith("group-") and key not in there)


def f_in_contents(label, level):
    """Whether the contents must have a line for a section of that level: always, but for a sub-section (level 3) where
    labels.txt has the line 'contents-depth | sections'."""
    if "contents-depth" in label and label["contents-depth"] != "sections":
        raise GiveUp("labels.txt: behind 'contents-depth' only 'sections' may stand: %s" % label["contents-depth"])
    return not (level == 3 and "contents-depth" in label)


F_BOXES = ("proved", "assumed", "outside")
F_COLOURS = ("def", "class", "thm", "lem", "chk")
F_CARD = {"definition": "def", "target": "class", "proved": "thm", "proved-under": "lem", "hypothesis": "chk"}
F_WORDS = ("by-definition", "by-construction", "proved", "ours", "open", "at-risk", "accepted", "names")
F_BRIGHT = ("proved", "by-definition", "by-construction")
F_SAY_CHECKED = ("theorem", "theorems", "lemma", "lemmas", "thm", "checked", "proven", "verified", "certified", "qed")
F_FOLLOWED = ("def", "abbrev", "structure", "class", "inductive", "instance", "opaque")
F_LABELS = (
    "brand title html-title description subtitle byline tiles-title tiles-note rows-words rows-lean remark limits-link "
    "appendix search-hint definitions-count back"
).split()
F_ID = r"[a-z][a-z0-9-]*"
F_COUNTED = re.compile(
    r"\{(cards|rows|embedded|embedded-files|links|lean-files|l"
    r"ines|reach|reach-lines|reach-files|reach-cards|reach-card-lines)"
    r"(?: ([A-Za-z0-9_./']+))?\}"
)
F_MOST = 40000
F_PIECE = 3000  # a stretch of Lean stands in the block of data in pieces of at most so many characters as JSON
F_LINE = 10000  # no line of the page is longer; the generator aims at some 4,000


def f_block(x):
    """x as the block of data writes it: JSON without blanks, '<' as its escape, and a line end behind every comma that
    follows ']' or '}' outside a string."""
    text = json.dumps(x, ensure_ascii=False, separators=(",", ":")).replace("<", "\\u003c")
    return re.sub(r'"(?:[^"\\]|\\.)*"|([\]}]),', lambda m: m.group(1) + ",\n" if m.group(1) else m.group(), text)


def f_pieces(first, lines):
    """The lines of a stretch of Lean, the first of which has the number 'first', as the block of data holds them: in
    pieces of whole lines, each of at most F_PIECE characters as JSON, or of one longer line."""
    out, begin, room = [], 0, F_PIECE
    for n, line in enumerate(lines + [None]):
        need = 0 if line is None else len(f_block(line))
        if n > begin and (line is None or need > room):
            out.append([first + begin, "\n".join(lines[begin:n])])
            begin, room = n, F_PIECE
        room -= need
    return out


F_BREAKS = re.compile(r'<div class="sbs-row|<div class="fl"|<li[ >]|<p[ >]|<tr[ >]')


def f_in_lines(text, before):
    """A stretch of the page's markup as the page has it: with a line end before every row of a card, line of Lean in a
    row, list item, paragraph and table row that does not begin a line already. 'before': the character before the
    stretch, or '' where the stretch begins one of the frame's places."""
    out, done = [], 0
    for m in F_BREAKS.finditer(text):
        if (text[m.start() - 1] if m.start() else before) not in ("", "\n"):
            out += [text[done : m.start()], "\n"]
            done = m.start()
    return "".join(out) + text[done:]


F_OPENERS = (":=", ":= by", "where")  # the bare sign that opens a proof may be embedded with the statement's last line


def f_esc(s):
    return (
        s.replace("&", "&amp;").replace("<", "&lt;").replace(">", "&gt;").replace('"', "&quot;").replace("'", "&#x27;")
    )


def flat_words(s):
    """The words of s in small letters, one blank between them and one at each end."""
    return " %s " % " ".join(re.findall("[a-z]+", s.lower()))


def f_lines(folder, name, needed=False):
    path = os.path.join(folder, name)
    if not os.path.lexists(path):
        if needed:
            raise GiveUp("%s: there is no such file" % path)
        return []
    return [l.strip() for l in read(path, "a data file", 400000).split("\n") if l.strip() and not l.startswith("#")]


def f_table(folder, name, columns, needed=False):
    rows = [[c.strip() for c in l.split("|", columns - 1)] for l in f_lines(folder, name, needed)]
    for r in rows:
        if len(r) != columns:
            raise GiveUp("%s: a line has not %d parts between bars: %s" % (os.path.join(folder, name), columns, r[0]))
    return rows


def f_plain(s, where):
    """s, for a place where no mark is rendered: a backtick or a link there would print as signs."""
    if "\x60" in s or "](" in s:
        raise GiveUp("%s: backticks and links are not rendered there: %s" % (where, s))
    return s


def f_units(s):
    """The length of s as a script counts it."""
    return len(s.encode("utf-16-le")) // 2


def f_script(script, turns):
    lines, old = script.split("\n"), None
    for l in turns.split("\n"):
        if l[:2] == "- " and old is None:
            old = l[2:]
        elif l[:2] == "+ " and old is not None:
            if lines.count(old) != 1:
                raise GiveUp("turns.txt: a line that does not stand once in page.js: %s" % old)
            lines[lines.index(old)] = l[2:]
            old = None
        elif l.strip() and l[:1] != "#":
            raise GiveUp("turns.txt: a line that is neither '- ', '+ ' in its turn nor a remark: %s" % l)
    if old is not None:
        raise GiveUp("turns.txt ends in a '- ' line")
    return "\n".join(lines)


def f_nameless(L, c):
    """How a declaration without a name is called: by its first line, without a closing 'where'."""
    return re.sub(r"\s+where$", "", L.text[c.start : c.shown_end].split("\n")[0].rstrip())


def f_bare(e):
    """e, for words that stand outside its card: names are looked up at its place, and nothing is bound."""
    x = Entry()
    x.__dict__.update(e.__dict__)
    x.bound = set()
    return x


def f_first_difference(got, want, where=""):
    """Where two values read from JSON first differ, in words."""
    if type(got) is not type(want):
        return "%s: %r where %r is due" % (where or "at the top", got, want)
    if isinstance(want, dict):
        for key in sorted(set(got) | set(want)):
            if got.get(key) != want.get(key):
                return f_first_difference(got.get(key), want.get(key), "%s[%s]" % (where, key))
    if isinstance(want, list):
        for n, (a, b) in enumerate(zip(got, want)):
            if a != b:
                return f_first_difference(a, b, "%s[%d]" % (where, n))
        return "%s: %d items where %d are due" % (where, len(got), len(want))
    if isinstance(want, str) and len(want) > 60:
        n = next((i for i, (a, b) in enumerate(zip(got, want)) if a != b), min(len(got), len(want)))
        return "%s: %r where %r is due" % (where, got[max(0, n - 20) : n + 40], want[max(0, n - 20) : n + 40])
    return "%s: %r where %r is due" % (where, got, want)


def in_force(L, c):
    """The lines in force above c that a page shows: all but a 'variable' line from which Lean can take nothing."""
    above = []
    for v in c.lines_above:
        text = L.plain()[v.start : v.end]
        if v.word == "variable" and not text.rstrip().endswith(" in"):
            groups, k = [], len("variable")
            while k < len(text):
                if text[k] in "([{⦃":
                    g = group_end(text, k)
                    if g < 0:
                        raise GiveUp("%s:%d: a bracket of this 'variable' command is not closed" % (L.path, v.line))
                    groups.append(text[k:g])
                    k = g
                else:
                    k += 1
            heads = [None if g[0] == "[" else NAMES_THEN_COLON.match(g) for g in groups]
            declared = {x for h in heads if h for x in h.group(1).split()}
            first_parts = lambda s: {x.split(".")[0] for x in NAME.findall(s)}
            elsewhere = any(declared & first_parts(L.plain()[o.start : o.end]) for o in c.lines_above if o is not v)
            again = set()
            for names, mentioned in c.binder_groups:
                elsewhere = elsewhere or bool((declared - again) & mentioned)
                again |= names
            if groups and all(heads) and declared <= c.binders and not elsewhere:
                continue
        above.append((v.start, v.end))
    return above


class Front:
    """The front page as this program would make it."""

    def __init__(self, root, table, links, long_name):
        self.root, self.table, self.rule4, self.long_name = root, table, links.after_bracket, long_name
        self.links = Links(table, [])
        self.links.after_bracket = links.after_bracket  # rule 4 looks at what the long page's first two folders link
        self.at, self.key, self.targets = {}, {}, set()  # place -> entry; place -> its key on the page, if embedded
        self.card_places = set()  # the places of the declarations that have a card
        self.pages = {}  # the pages of the Lean folder that the data quote: their words

    def lean(self, path):
        if path not in self.table.files:
            self.table.files[path] = Lean(self.root, path)
        return self.table.files[path]

    def entry(self, place):
        if place not in self.at:
            L = self.lean(place[0])
            c = next((c for c in L.commands() if c.line == place[1] and c.kind), None)
            if c is None or c.trouble:
                why = ": " + c.trouble if c else ""
                raise GiveUp("%s:%d: this program cannot read the declaration there%s" % (place + (why,)))
            e = Entry()
            e.path, e.line, e.command, e.L, e.ok, e.printed = place[0], place[1], c, L, True, True
            e.ident = c.full if c.full and "private" not in c.modifiers else "%s:%d" % place
            e.part = None if any(within(e.path, f) for f in FOLDERS) else "other"
            e.above = in_force(L, c)
            e.blocks = [(None, a, b) for a, b in e.above] + [(None, c.start, c.shown_end)]
            self.links.prepare(e)
            e.wants = None
            self.at[place] = e
        return self.at[place]

    def named(self, place):
        return bool(self.entry(place).command.full)

    def by_name(self, name):
        m = re.fullmatch(r"([A-Za-z0-9_]+(?:/[A-Za-z0-9_]+)*\.lean):([1-9]\d*)", name)
        if m:
            return self.entry((m.group(1), int(m.group(2))))
        fit = [r for r in self.table.decl.get(name, ()) if not r[4]]
        if len(fit) != 1:
            raise GiveUp("the data name %s: %d declarations of the Lean files have that full name" % (name, len(fit)))
        return self.entry(fit[0][:2])

    def wants(self, e):
        """[(place in the file, length, the declaration's place)]: each name in e's Lean text that the rules resolve."""
        if e.wants is None:
            e.wants, e.doubt, me = [], [], (e.path, e.line)
            for _, a, b in e.blocks:
                s = e.L.plain()[a:b]
                for m, after_bracket, after_dot in self.links.names(s):
                    if after_bracket:
                        last = m.group().split(".")[0]
                        if e.part is not None and not any(u[0] is None for u in self.rule4.get(last, ())):
                            continue
                        place = self.links.by_result_type(e, s, m.start() - 2, last)
                        fit = self.table.by_last.get(last, ())
                        if not place and len(fit) == 1 and last not in LIKELY_ELSEWHERE:
                            place = next(iter(fit))[1]
                        if place and place != me:
                            e.wants.append((a + m.start(), len(last), place))
                    elif not after_dot:
                        found = self.links.in_source(e, m.group())
                        if not found and a + m.start() != e.command.name_start:
                            e.doubt += self.several(e, m.group())
                        if found and found[0] != me:
                            parts = list(re.finditer(ONE, m.group()))
                            x, y = parts[found[1]].start(), parts[found[1] + found[2] - 1].end()
                            e.wants.append((a + m.start() + x, y - x, found[0]))
        return e.wants

    def several(self, e, name):
        """The places among which rule 2 cannot tell, for a name in e's Lean text or the written type of a bound one."""
        if name.split(".")[0] in e.bound:
            written = e.types.get(name.split(".")[0], {None})
            if "." not in name or len(written) != 1 or None in written or next(iter(written)).split(".")[0] in e.bound:
                return []
            name = next(iter(written))
        fit = self.table.lookup(name, e.command, e.path)[0]
        return fit if len(fit) > 1 else []

    # -- words
    def code(self, e, s):
        """What stands between backticks: names that rule 6 resolves to something embedded can be hovered."""
        out, i = [], 0
        strings = [m.span() for m in re.finditer('"[^"]*"', s)]  # no name in a string is a link
        for m, _, after_dot in self.links.names(s) if e else ():
            if after_dot or m.start() < i or any(a < m.start() < b for a, b in strings):
                continue
            found = self.links.in_comment(m.group(), e.command, e.path, e.bound, (), False)
            if not found and len(m.group()) > 2 and m.group().split(".")[0] not in e.bound:
                # the last rule, in words alone: the one card whose declaration's full name ends in this name
                fit = [
                    p
                    for p in sorted(self.card_places)
                    if self.named(p) and ("." + self.key[p]).endswith("." + m.group())
                ]
                found = (fit[0], 0, len(m.group().split("."))) if len(fit) == 1 else None
            if found and found[0] != (e.path, e.line) and found[0] in self.key:
                parts = list(re.finditer(ONE, m.group()))
                x, y = m.start() + parts[found[1]].start(), m.start() + parts[found[1] + found[2] - 1].end()
                out.append(
                    f_esc(s[i:x])
                    + '<span class="name-link" data-name="%s">%s</span>' % (f_esc(self.key[found[0]]), f_esc(s[x:y]))
                )
                i = y
        return "".join(out) + f_esc(s[i:])

    def plain(self, s, l):
        if "\x60" in s or "**" in s or "](" in s:
            raise GiveUp("the data: a backtick, '**' or '](' without its fellow, or one mark inside another: %s" % l)
        return f_esc(s)

    def inline(self, e, l):
        if len(l) > 6000:  # the search for marks takes time by the square of the line's length
            raise GiveUp("the data: a line of words of more than 6000 characters: %s ..." % l[:80])
        quote = re.match(r"quote ((?:[A-Za-z]+/)*[A-Z][A-Z-]*\.md) \|(?: |$)", l)
        if not quote and re.match(r"quote \S+ \|", l):
            raise GiveUp("the data: a quotation of something else than a page X.md or Folder/X.md: %s" % l)
        if quote:  # words that the data give as a quotation of a page in the Lean folder: they must stand there
            l = l[quote.end() :]
            if quote.group(1) not in self.pages:
                path = os.path.join(self.root, *quote.group(1).split("/"))
                self.pages[quote.group(1)] = read(path, "a page that the data quote", 4000000).split()
            there, words = (
                self.pages[quote.group(1)],
                l.split(),
            )  # word for word, so no run begins or ends inside a word
            if not words or not any(there[k : k + len(words)] == words for k, w in enumerate(there) if w == words[0]):
                bad(
                    7,
                    "the data give these words as a quotation of %s, and they do not stand there: %s"
                    % (quote.group(1), l),
                )
        l = F_COUNTED.sub(lambda m: "{:,}".format(self.number(m.group(1), m.group(2) or "", l)), l)
        out, i = [], 0
        for m in re.finditer(
            r"\[([^\]\n]+)\]\((#%s|(?:[A-Za-z]+/)*[A-Z][A-Z-]*\.md"
            r"|long-page|notes-page)\)|\*\*([^*\n]+)\*\*|%s([^%s\n]+)%s" % (F_ID, "\x60", "\x60", "\x60"),
            l,
        ):
            out.append(self.plain(l[i : m.start()], l))
            if m.group(2):
                if m.group(2) not in ("long-page", "notes-page"):
                    self.targets.add(m.group(2))
                words = re.sub("\x60([^\x60]+)\x60", r"<code>\1</code>", f_esc(m.group(1)))
                goal = {"long-page": self.long_name, "notes-page": self.notes_name}.get(m.group(2), m.group(2))
                if not goal:
                    raise GiveUp("the data link to the short page, and none is given (--short): %s" % l)
                out.append('<a href="%s">%s</a>' % (f_esc(goal), words))
            elif m.group(3):
                out.append("<b>%s</b>" % re.sub("\x60([^\x60]+)\x60", r"<code>\1</code>", f_esc(m.group(3))))
            else:
                if m.group(4)[0].isspace() or m.group(4)[-1].isspace():
                    raise GiveUp("the data: code that begins or ends with a blank: %s" % l)
                out.append(
                    "<code%s>%s</code>" % (' class="nw"' if len(m.group(4)) <= 28 else "", self.code(e, m.group(4)))
                )
            i = m.end()
        return "".join(out) + self.plain(l[i:], l)

    def words(self, e, lines, cls="bl"):
        out, depth = [], 0
        for l in lines:
            level = 2 if l[:3] == "-- " else 1 if l[:2] == "- " else 0
            if level == 2 and depth == 0:
                raise GiveUp("a bullet of the second level without one of the first: %s" % l)
            out.append("</li></ul>" * max(0, depth - level))
            depth = min(depth, level)
            if level and depth == level:
                out.append("</li>")
            for k in range(depth, level):
                out.append("<ul>" if k else '<ul class="%s">' % cls)
            depth = level
            text = self.inline(e, l[level + 1 :].strip() if level else l)
            out.append("<li>" + text if level else "<p>" + text + "</p>")
        return "".join(out) + "</li></ul>" * depth

    # -- Lean text
    def cell(self, L, ranges):
        out = []
        for a, b in ranges:
            for n in range(L.line_of(a), L.line_of(max(a, b - 1)) + 1):
                start = L.offsets[n - 1]
                line = L.text[start:].split("\n", 1)[0]
                s, t = max(a - start, 0), min(b - start, len(line))
                piece = line[s:t]
                s, t = s + len(piece) - len(piece.lstrip()), t - (len(piece) - len(piece.rstrip()))
                if s < t:
                    out.append(
                        '<div class="fl" data-l="%d" data-a="%d" data-b="%d" style="--i:%d">%s</div>'
                        % (
                            n,
                            f_units(line[:s]),
                            f_units(line[:t]),
                            min(len(line) - len(line.lstrip()), 40),
                            f_esc(line[s:t]),
                        )
                    )
        return "".join(out)

    def rows(self, e, rows_text):
        """[(margin word, the words' lines, ranges, what stands behind '# chip:')], read from rows.txt step by step."""
        L, c, marks, margin, chip = e.L, e.command, [], "", ""
        for l in rows_text:
            if l.startswith("# margin:"):
                margin = l[len("# margin:") :].strip()
            elif l.startswith("# chip:"):
                chip = l[len("# chip:") :].strip()
            elif l.startswith("@"):
                marks.append((l[1:].strip(), margin, [], chip))
                margin = chip = ""
            elif l.strip() and not l.startswith("#"):
                if not marks:
                    raise GiveUp("rows.txt, '=== %s': its rows begin with words, not with '@'" % e.ident)
                marks[-1][2].append(l.strip())
        out = []
        if marks and marks[0][0] == "^":
            out.append((marks[0][1], marks[0][2], list(e.above), marks[0][3]))
            marks = marks[1:]
        if bool(out) != bool(e.above):
            bad(1, "%s: the lines in force above it and the row '@^' of its rows go together" % e.ident)
        since, behind, places = c.start, c.start, []
        for k, m in enumerate(marks):
            found = L.anchor(m[0], since, behind, c.shown_end) if m[0] else None
            if not found or (k == 0 and found[0] != c.start):
                raise GiveUp(S_NOT_FOUND % ("front/", e.ident, m[0]))
            at = found[1] if k else found[0]
            line = L.text.rfind("\n", 0, at) + 1
            places.append(line if k and not L.text[line:at].strip() else at)
            since, behind = found[0], found[0] + len(m[0])
        if not marks:
            raise GiveUp("rows.txt, '=== %s': it has no row" % e.ident)
        places.append(c.shown_end)
        for k, m in enumerate(marks):
            out.append((m[1], m[2], [(places[k], places[k + 1])], m[3]))
        if any(not r[1] for r in out):
            bad(7, "%s: a row without words" % e.ident)
        return out


def f_first_sentence(front, e):
    c = e.command
    if not c.doc:
        return ""
    words = " ".join(e.L.text[c.doc[0] + 3 : c.doc[1] - 2].split())
    marks, seen = 0, 0
    for stop in re.finditer(r"\.\**(?= )", words):  # the first full stop outside code that a blank follows
        marks, seen = marks + words.count("\x60", seen, stop.start()), stop.start()
        if marks % 2 == 0:
            words = words[: stop.end()]
            break
    pieces = words.split("\x60")
    if len(pieces) % 2 == 0:
        return f_esc(words)
    out, bold, paired = [], False, sum(p.count("**") for p in pieces[0::2]) % 2 == 0
    for k, piece in enumerate(pieces):
        if k % 2:
            out.append("<code>%s</code>" % front.code(f_bare(e), piece))
        elif not paired:
            out.append(f_esc(piece))
        else:
            for j, part in enumerate(piece.split("**")):
                if j:
                    out.append("</b>" if bold else "<b>")
                    bold = not bold
                out.append(f_esc(part))
    return "".join(out)


def f_by_itself(page, root, front):
    """Held of the page as it is, apart from the comparison with what this program would have made: a slip in that
    picture must not let these through. (a) Every embedded line is its file's line, or the beginning of it and marked as
    cut. (b) No embedded line, and no part of one but the bare sign that opens it, lies in the proof of any theorem,
    lemma or example of its file. (c) Every piece of Lean in a row is the stretch of its file's line that its numbers
    name. (d) No id stands twice, and no key of a declaration: the script finds its data, its panel and a declaration by
    these, and would take the first or the last. (e) The lines that the block of data gives as in force above a
    declaration, which the hover card and the side panel show with it, are the ones that this program finds in force
    there, all of them, and each is embedded: by the same reading of the lines in force as the picture's, so that this
    is a second look at the numbers, not at that reading. (f) No embedded line stands at or below a command that this
    program does not know. (g) No line of the page has more than F_LINE characters, and no line end stands between a
    number's comma and the next number: a tool that searches a release for lists of numbers takes very long over long
    lines, and takes a line that ends so and the next for one list."""
    for n, line in enumerate(page.split("\n"), 1):
        if len(line) > F_LINE:
            bad(6, "line %d of the page has %d characters: more than %d" % (n, len(line), F_LINE))
    for m in re.finditer(r"[0-9],\n[0-9]", page):
        n = page.count("\n", 0, m.end())
        bad(
            6,
            "line %d of the page ends with a number and a comma, and the next begins with a number: the generator "
            "never writes that. Make the page again; if it stays, look at the files of shell/" % n,
        )
    tags_alone = re.sub(r"(?s)(<(script|style)\b[^>]*>).*?</\2>", r"\1", page)  # what these two hold is no markup
    ids = re.findall(r'<[a-zA-Z][^<>]*?\sid="([^"]*)"', tags_alone)
    for i in sorted({i for i in ids if ids.count(i) > 1}):
        bad(6, "the id '%s' stands %d times on the page" % (i, ids.count(i)))
    m = re.search(r'<script id="audit-data" type="application/json">(.*?)</script>', page, re.S)
    try:
        data = json.loads(m.group(1)) if m else None
        files, decls, cut, above = data["files"], data["decls"], data["cut"], data["above"]
    except (ValueError, KeyError, TypeError):
        return bad(6, "the block of data cannot be read")
    keys = [str(r[0]) for r in decls]
    for key in sorted({k for k in keys if keys.count(k) > 1}):
        bad(
            5, "the block of data has two declarations under the key %s: the script would show the later for both" % key
        )
    held = {}
    for k, f in enumerate(files):
        if not isinstance(f[0], str) or not re.fullmatch(r"[A-Za-z0-9_]+(/[A-Za-z0-9_]+)*\.lean", f[0]):
            return bad(1, "the block of data names a file that is no plain path inside the Lean folder: %r" % (f[0],))
        L = front.lean(f[0])
        lines = L.text.split("\n")
        for first, text in f[3]:
            for n, got in enumerate(text.split("\n"), first):
                if not 1 <= n <= len(lines) or (k, n) in held:
                    bad(1, "%s:%d: embedded twice, or no line of the file" % (f[0], n))
                    continue
                held[(k, n)] = got
                marked = str(n) in cut.get(str(k), {})
                if got != lines[n - 1] and not (marked and lines[n - 1].startswith(got)):
                    bad(1, "%s:%d: the embedded line is not the file's" % (f[0], n))
                if marked and cut[str(k)][str(n)] != f_units(lines[n - 1]):
                    bad(4, "%s:%d: the mark of a cut line does not give the line's length" % (f[0], n))
        commands = L.commands()  # it also sets L.unknown
        below = [n for kk, n in held if kk == k and L.unknown and n >= L.unknown[0]]
        if below:
            bad(1, "%s:%d: this line is embedded, and line %d of the file has %s" % ((f[0], min(below)) + L.unknown))
        for c in commands:
            if c.kind in NO_PROOF and not c.trouble:
                a, b = L.line_of(c.shown_end - 1), L.line_of(max(c.start, c.end - 1))
                for n in range(a, b + 1):
                    more = held.get((k, n), "")[c.shown_end - L.offsets[a - 1] :] if n == a else held.get((k, n), "")
                    if (k, n) in held and (n > a or more.strip() not in ("",) + F_OPENERS):
                        bad(
                            4,
                            "%s:%d: a line of the proof of %s, or a part of one, is embedded"
                            % (f[0], n, c.full or c.kind),
                        )
        count("files whose embedded lines were held by themselves")
    for k, d in enumerate(decls):
        e = front.entry((files[d[2]][0], d[3]))
        due = [[e.L.line_of(a), e.L.line_of(b - 1)] for a, b in e.above]
        if above.get(str(k), []) != due:
            bad(
                1,
                "%s: the block of data gives %s as the lines in force above it; in %s they are %s"
                % (d[0], above.get(str(k)) or "nothing", e.path, due or "none"),
            )
        for n in (n for a, b in due for n in range(a, b + 1) if (d[2], n) not in held):
            bad(1, "%s: line %d of %s is in force above it and is not embedded" % (d[0], n, e.path))
    for k in sorted(set(above) - {str(k) for k in range(len(decls))}):
        bad(1, "the block of data gives lines in force above a declaration number %s, and there is none" % k)
    count("declarations whose lines in force were held by themselves", len(decls))
    file_of = {d[0]: d[2] for d in decls}
    for box in re.finditer(
        r'<div class="sbs" data-decl="([^"]*)">(.*?)</div></div></div>(?=<div class="stmt-remark">|</div><div '
        r'class="card-foot">)',
        page,
        re.S,
    ):
        k = file_of.get(box.group(1).replace("&#x27;", "'").replace("&amp;", "&"))
        for p in re.finditer(
            r'<div class="fl" data-l="(\d+)" data-a="(\d+)" data-b="(\d+)" style="--i:\d+">([^<]*)</div>', box.group(2)
        ):
            n, a, b = (int(x) for x in p.groups()[:3])
            line = front.lean(files[k][0]).text.split("\n")[n - 1] if k is not None else ""
            units = line.encode("utf-16-le")[2 * a : 2 * b].decode("utf-16-le", "replace")
            if f_esc(units) != p.group(4) or not units.strip():
                bad(
                    1,
                    "%s: a piece of Lean in its rows is not line %d, columns %d to %d, of its file"
                    % (box.group(1), n, a, b),
                )
            count("pieces of Lean in rows held by themselves")


def check_front(path, root, heads, table, links, long_name, notes_name, ids_there):
    """All checks of the front page but check 8. Returns its bytes. ids_there: the ids of the short page's cards and
    entries."""
    folder, shell = os.path.join(heads, "front"), os.path.join(heads, "shell")
    page = read(path, "the front page", 200000000)
    parts = {name: read(os.path.join(shell, name), "a file of the shell", 400000) for name in F_SHELL}
    for name in F_SHELL:
        if hashlib.sha256(parts[name].encode("utf-8")).hexdigest() != F_SHELL_SHA256[name]:
            bad(
                6,
                "%s is not the file that ships with this program (its sha256 differs): take the folder shell/ from the "
                "release again" % os.path.join(shell, name),
            )
    script = f_script(parts["page.js"], parts["turns.txt"])
    label = dict(f_table(folder, "labels.txt", 2, True))
    for key in F_LABELS:
        if key not in label:
            raise GiveUp("%s: no line for '%s'" % (os.path.join(folder, "labels.txt"), key))
    titles, remarks, rows_of, at = dict(f_table(folder, "titles.txt", 2)), {}, {}, None
    for words in list(label.values()) + list(titles.values()):
        f_plain(words, "labels.txt or titles.txt")
    for key in sorted(label):  # the words that a reader sees for a status whose truth nothing holds
        kind, status = (key.split("-", 1) + [""])[:2]
        dull = status not in ["proved", "proved-under"] + ["hypothesis-" + w for w in F_BRIGHT]
        said = flat_words(label[key])
        if kind in ("type", "chip") and dull:
            if any(" %s " % w in said for w in F_SAY_CHECKED) or " proved " in said.replace(" not proved ", " "):
                bad(
                    3,
                    "labels.txt, '%s': this status's words say 'proved' (with no 'not' before it) or one of %s: %s"
                    % (key, ", ".join(F_SAY_CHECKED), label[key]),
                )
    for name in ("tiles.txt", "legend.txt"):
        for l in f_lines(folder, name):
            f_plain(l, name)
    for name, words in f_table(folder, "remarks.txt", 2):
        remarks.setdefault(name, []).append(words)
    rows_path = os.path.join(folder, "rows.txt")
    for l in read(rows_path, "the rows", 1000000).split("\n") if os.path.lexists(rows_path) else ():
        if l.startswith("==="):
            at = l[3:].strip()
            if at in rows_of:
                raise GiveUp("rows.txt has '=== %s' twice" % at)
            rows_of[at] = []
        elif at:
            rows_of[at].append(l)
        elif l.strip() and not l.startswith("#"):
            raise GiveUp("rows.txt begins with something else than a remark or '=== FULL.NAME'")
    limits, groups = {}, {}  # groups: limit -> [the title of its folded group, the lines in the group]
    for n, words in f_table(folder, "limits.txt", 2):
        if not re.fullmatch(r"[1-9]\d{0,2}", n):
            raise GiveUp("limits.txt: '%s' is no number" % n)
        n = int(n)
        if re.match(r"more *(\||$)", words):
            title = words.partition("|")[2].strip()
            if n in groups or n not in limits or not title:
                fault = (
                    "limit %d has such a line already" % n
                    if n in groups
                    else "it has no title" if n in limits else "it is the first line of limit %d" % n
                )
                raise GiveUp("limits.txt: 'n | more | title': %s: %d | %s" % (fault, n, words))
            groups[n] = [f_plain(title, "limits.txt, a group's title"), []]
        elif n in groups:
            groups[n][1].append(words)
        else:
            limits.setdefault(n, []).append(words)
    for n in sorted(groups):
        if not groups[n][1]:
            raise GiveUp("limits.txt: no line of limit %d follows its line 'more'" % n)
    audited = os.path.join(root, *AUDITED.split("/"))
    audited = read(audited, "the list of the audit's theorems", 20000000) if os.path.lexists(audited) else ""
    audited = {l.split()[0] for l in audited.split("\n") if l.strip() and l[:1] != "#"}
    front = Front(root, table, links, long_name)
    front.notes_name = notes_name
    # which declarations have a card on the short page: by that page's data; and each such card is there, by its id
    noted = {
        l.split("|")[0].strip()
        for l in (s_lines(os.path.join(heads, "short"), "claims.txt", True) if notes_name else ())
        if not l.startswith(("==", ">", "!", "+"))
    }
    for name in sorted(noted - ids_there):
        bad(5, "the short page's claims.txt has a card for %s, and that page has nothing of that id" % name)

    def listed(e, where):
        """Check 3 fails unless e is a theorem or lemma with a line in the audit's list and no 'sorry' in its proof."""
        c = e.command
        if c.kind not in ("theorem", "lemma") or c.full not in audited:
            bad(3, "%s, and it is no theorem or lemma that has a line in %s" % (where, AUDITED))
        elif re.search(r"(?<![%s.])(sorry|sorryAx|admit)(?![%s])" % (IDC, IDC), e.L.plain()[c.shown_end : c.end]):
            bad(3, "%s, and its proof has a 'sorry', 'sorryAx' or 'admit'" % where)

    given = {}  # where a status stands -> the theorems named behind it

    def a_status(said, where):
        """(status, word). Behind a hypothesis's three bright words, and there alone, stand the theorems it rests on."""
        words = said.split()
        status = words[0] if words else ""
        word = words[1] if status == "hypothesis" and len(words) > 1 else ""
        theorems = words[2 if status == "hypothesis" else 1 :]
        if status not in F_CARD or (status == "hypothesis" and word not in F_WORDS):
            raise GiveUp("%s: no status that this program knows: %s" % (where, said))
        if (word in F_BRIGHT) != bool(theorems) and not (status == "target" and where.startswith("claims.txt")):
            raise GiveUp(
                "%s: a hypothesis called %s names its theorems, a target's card may, and no other status names any: %s"
                % (where, ", ".join(F_BRIGHT), said)
            )
        for name in theorems:
            listed(front.by_name(name), "%s gives %s as a proof" % (where, name))
        given[where] = theorems
        return status, word

    # ---- claims.txt
    sections, cards, whole, also, own_words = [], [], [], [], {}
    for l in f_lines(folder, "claims.txt", True):
        if l.startswith("=="):
            title, _, ident = (x.strip() for x in l.lstrip("=").partition("|"))
            if not title or not re.fullmatch(F_ID, ident) or ident in [s["id"] for s in sections]:
                raise GiveUp("claims.txt: a section wants a title and an id of its own: %s" % l)
            if re.match("lim-|card-", ident) or ident in re.findall(r'id="([^"]*)"', parts["page_template.html"]):
                raise GiveUp("claims.txt: a section's id that the frame, a limit or a card could have too: %s" % l)
            f_plain(title, "claims.txt, a section's title")
            if l.startswith("===") and not sections:
                raise GiveUp("claims.txt: a sub-section before the first section")
            sections.append(
                {
                    "level": 3 if l.startswith("===") else 2,
                    "title": title,
                    "id": ident,
                    "pill": None,
                    "define": [],
                    "body": [],
                }
            )
            continue
        if not sections:
            raise GiveUp("claims.txt: its first line must open a section")
        sec = sections[-1]
        if l.startswith("! pill "):
            state, _, words = (x.strip() for x in l[7:].partition("|"))
            if state not in F_PILLS or not words or sec["pill"]:
                raise GiveUp("claims.txt: this line is no pill: %s" % l)
            sec["pill"] = (state, f_plain(words, "claims.txt, a pill"))
        elif l[:3] in ("!> ", "!- "):
            sec["define"].append(l[3:].strip() if l[1] == ">" else l[1:])
        elif l.startswith("! "):
            what = l[2:].split()
            if what[0] in ("whole", "also") and len(what) == 2:
                (whole if what[0] == "whole" else also).append(front.by_name(what[1]))
                continue
            if what[0] == "box":
                kind, _, title = (x.strip() for x in l[6:].partition("|"))
                if kind not in F_BOXES or not title:
                    raise GiveUp("claims.txt: this line is no box: %s" % l)
                sec["body"].append(("box", (kind, f_plain(title, "claims.txt, a box's title"), [])))
                continue
            if what[0] == "definitions" and what[1:] in ([], ["titled"]):
                sec["body"].append(("definitions", bool(what[1:])))
                continue
            if what[0] == "fold" or what == ["fold-end"]:
                marks = [k for k, _ in sec["body"] if k.startswith("fold")]
                title = " ".join(what[1:])
                if len(marks) % 2 != (what[0] != "fold") or (what[0] == "fold" and not title):
                    raise GiveUp(
                        "claims.txt: a fold inside a fold, an end without a fold, or a fold without a title: %s" % l
                    )
                sec["body"].append((what[0], f_plain(title, "claims.txt, a fold's title")))
                continue
            if what[0] not in ("table", "limits", "closing", "notes") or len(what) != 1 + (what[0] == "table"):
                raise GiveUp("claims.txt: unknown line: %s" % l)
            if what[0] == "table" and not re.fullmatch("[a-z]+", what[1]):
                raise GiveUp("claims.txt: a table's name is of small letters: %s" % l)
            sec["body"].append((what[0], what[-1]))
        elif l[:2] in ("> ", "- ") or l[:3] == "-- ":
            line = l[2:].strip() if l[0] == ">" else l
            if sec["body"] and sec["body"][-1][0] == "box":
                if l[:2] != "- ":
                    raise GiveUp("claims.txt: a box holds bullets of the first level alone: %s" % l)
                sec["body"][-1][1][2].append(l[2:].strip())
            elif sec["body"] and sec["body"][-1][0] in ("words", "bullets"):
                sec["body"][-1][1].append(line)
            else:
                sec["body"].append(("words", [line]))
        elif l.startswith("+ "):
            sec["body"] += [("label", f_plain(l[2:].strip(), "claims.txt, a small label")), ("bullets", [])]
        else:
            cells = [x.strip() for x in l.split("|", 2)]
            name, said, chip_words = cells[0], cells[1] if len(cells) > 1 else "", cells[2] if len(cells) > 2 else ""
            status, word = a_status(said, "claims.txt, %s" % name)
            bright_words = " proved " in flat_words(chip_words).replace(" not proved ", " ") or any(
                " %s " % w in flat_words(chip_words) for w in F_SAY_CHECKED
            )
            if chip_words and status != "target":
                raise GiveUp("claims.txt: chip words of its own on a card that is no target's: %s" % l)
            if status == "target" and (len(said.split()) > 1) != bool(chip_words) and (bright_words or not chip_words):
                raise GiveUp(
                    "claims.txt: a target's theorems and its chip words that speak of a proof go together: %s" % l
                )
            own_words[name] = (f_plain(chip_words, "claims.txt, a card's chip words"), given["claims.txt, %s" % name])
            e = front.by_name(name)
            if e.ident != name or any(x[0] is e for x in cards) or "private" in e.command.modifiers:
                raise GiveUp(
                    "claims.txt: %s: a card goes by its declaration's own id, once, and not to a private one" % name
                )
            if e.command.kind == "axiom":
                bad(3, "claims.txt: %s is an axiom: it can have no card" % name)
            theorem = e.command.kind in ("theorem", "lemma")
            if theorem != (status in ("proved", "proved-under")):
                bad(
                    3,
                    "claims.txt calls the %s %s '%s': proved and proved-under are for a theorem or lemma, the other "
                    "statuses for what is neither" % (e.command.kind, name, status),
                )
            elif theorem:
                listed(e, "claims.txt calls %s '%s'" % (name, status))
            cards.append((e, status, word))
            sec["body"].append(("card", len(cards) - 1))
    if not cards:
        raise GiveUp("claims.txt has no card")
    for x in cards:
        if x[0].ident not in titles or x[0].ident not in rows_of:
            raise GiveUp("%s has a card, and no title or no rows" % x[0].ident)
    for name in sorted((set(remarks) | set(rows_of)) - {x[0].ident for x in cards}):
        bad(7, "remarks.txt or rows.txt has lines for %s, which has no card: they are printed nowhere" % name)
    for sec in sections:
        if len([k for k, _ in sec["body"] if k.startswith("fold")]) % 2:
            raise GiveUp("claims.txt: a fold of the section '%s' is not closed" % sec["title"])

    # ---- what must be embedded: the cards; what their texts name; all that the declarations called whole reach
    is_card = front.card_places = {(e.path, e.line) for e, _, _ in cards}
    embedded, named_by_cards = {p: True for p in is_card}, {}

    def public(place):
        c = front.entry(place).command
        return bool(c.full) and "private" not in c.modifiers

    for e, _, _ in cards:
        for _, _, place in front.wants(e):
            if public(place):
                embedded[place] = True
                if front.entry(place).command.kind in F_FOLLOWED:
                    named_by_cards.setdefault(place, front.entry(place))
    for e in also:
        if public((e.path, e.line)):
            embedded[(e.path, e.line)] = True

    def walk(roots, counts):
        """The places that the roots' texts reach, definitions followed. Beyond what the rules resolve: every place
        among which rule 2 cannot tell."""
        seen, met, todo = set(), set(roots), list(roots)
        while todo:
            found = []
            for place in todo:
                x = front.entry(place)
                if public(place) and counts(place):
                    seen.add(place)
                    if x.command.kind in F_FOLLOWED or place in roots:
                        found += [p for _, _, p in front.wants(x)] + x.doubt
            todo = sorted(set(found) - met)
            met |= set(todo)
        return seen

    for place in walk([(e.path, e.line) for e in whole], lambda p: True):
        embedded[place] = True
    order = sorted(embedded)
    front.key = {p: front.entry(p).ident for p in order}
    if len(set(front.key.values())) != len(order):  # the script finds a declaration by its key
        twice = sorted(k for k in set(front.key.values()) if list(front.key.values()).count(k) > 1)
        for k in twice:
            places = ", ".join("%s:%d" % p for p in order if front.key[p] == k)
            bad(3, "two embedded declarations have one name, by which the script finds them: %s: %s" % (k, places))
    number = {p: k for k, p in enumerate(order)}
    paths = sorted({p[0] for p in order})
    kinds = sorted({front.entry(p).command.kind for p in order})

    # ---- the block of data, as it must be
    want_files, want_decls, want_links, want_cut, want_above, total = [], [], {}, {}, {}, 0
    ranges, ends = {p: [] for p in paths}, {p: {} for p in paths}
    for p in order:
        e = front.entry(p)
        L, c = e.L, e.command
        last = L.line_of(c.shown_end - 1)
        ranges[e.path].append((L.line_of(c.doc[0]) if c.doc else c.line, last))
        ranges[e.path] += [(L.line_of(a), L.line_of(b - 1)) for a, b in e.above]
        if e.above:  # the hover card and the side panel show these lines above the declaration
            want_above[str(number[p])] = [[L.line_of(a), L.line_of(b - 1)] for a, b in e.above]
        if L.text[c.shown_end :].split("\n", 1)[0].strip() not in ("",) + F_OPENERS:
            ends[e.path][last] = c.shown_end
        for at, length, place in front.wants(e):
            if place in number:
                n = L.line_of(at)
                line = L.text[L.offsets[n - 1] :].split("\n", 1)[0]
                col = at - L.offsets[n - 1]
                want_links.setdefault(e.path, {}).setdefault(n, {})[f_units(line[:col])] = (
                    f_units(line[col : col + length]),
                    number[place],
                )
        sign = L.plain().find(":=", c.start, c.shown_end) if c.kind in ("def", "abbrev", "instance", "opaque") else -1
        head_end = L.line_of(sign) if sign >= 0 else c.line if c.kind in ("structure", "class", "inductive") else last
        whole = c.shown_end if c.kind in F_FOLLOWED else c.end
        want_decls.append(
            [
                e.ident,
                kinds.index(c.kind),
                paths.index(e.path),
                c.line,
                head_end,
                L.line_of(max(c.start, whole - 1)),
                L.line_of(c.doc[0]) if c.doc else 0,
                last,
                0,
                "" if c.full else f_nameless(L, c),
            ]
        )
    for k, p in enumerate(paths):
        L = front.lean(p)
        lines, merged = L.text.split("\n"), []
        for a, b in sorted(ranges[p]):
            if merged and a <= merged[-1][1] + 1:
                merged[-1][1] = max(merged[-1][1], b)
            else:
                merged.append([a, b])
        segments, cut = [], {}
        for a, b in merged:
            text = lines[a - 1 : b]
            for n, end in ends[p].items():
                if a <= n <= b and not any(
                    x <= n < y for x, y in ranges[p]
                ):  # no other embedded text runs on below that line
                    text[n - a] = L.text[L.offsets[n - 1] : end].rstrip()
                    if text[n - a] != lines[n - 1]:
                        cut[str(n)] = f_units(lines[n - 1])
            segments += f_pieces(a, text)
            total += b - a + 1
        how_many = L.text.count("\n") + (not L.text.endswith("\n"))
        want_files.append([p, hashlib.sha256(ON_DISK.get(p, L.text).encode("utf-8")).hexdigest()[:12], how_many, segments, ""])
        want_cut[str(k)] = cut
    if total > F_MOST:
        bad(3, "the cards' texts reach %d lines of Lean: more than %d" % (total, F_MOST))
    want_links = {
        str(paths.index(p)): {
            str(n): [x for col in sorted(per) for x in (col,) + per[col]] for n, per in sorted(by.items())
        }
        for p, by in want_links.items()
    }

    # ---- the numbers in words, counted here
    reached = {}

    def reach(name):
        if name not in reached:
            first = front.by_name(name)
            root = (first.path, first.line)
            reached[name] = sorted(walk([root], lambda p: p == root or front.entry(p).command.kind in F_FOLLOWED))
        return reached[name]

    def number(key, arg, l):
        if not arg and key in ("cards", "rows", "embedded", "embedded-files", "links"):
            return {
                "cards": lambda: len(cards),
                "rows": lambda: sum(len(front.rows(x[0], rows_of.get(x[0].ident, ()))) for x in cards),
                "embedded": lambda: len(order),
                "embedded-files": lambda: len(paths),
                "links": lambda: sum(len(v) // 3 for f in want_links.values() for v in f.values()),
            }[key]()
        if key == "lean-files":
            return len([p for p in table.imports if not arg or p.startswith(arg.rstrip("/") + "/")])
        if key == "lines" and arg in table.lines:
            return table.lines[arg]
        if key.startswith("reach") and arg:
            places = [p for p in reach(arg) if "card" not in key or p in is_card]
            if key in ("reach", "reach-cards"):
                return len(places)
            if key == "reach-files":
                return len({p[0] for p in places})
            total_lines = 0
            for p in places:
                x = front.entry(p)
                first_line = x.L.line_of(x.command.doc[0]) if x.command.doc else x.command.line
                total_lines += x.L.line_of(x.command.shown_end - 1) - first_line + 1
            return total_lines
        raise GiveUp(
            "the data: a place for a number that cannot be filled: {%s%s} in: %s" % (key, " " + arg if arg else "", l)
        )

    front.number = number

    # ---- the page's parts, as they must be: (check to blame, what, text)
    pill = lambda p: '<span class="status st-%s">%s</span>' % (p[0], f_esc(p[1]))
    button = lambda e, small: '<button type="button" class="lean-link%s" data-name="%s">%s</button>' % (
        " small" if small else "",
        f_esc(e.ident),
        f_esc(e.command.full or f_nameless(e.L, e.command)),
    )
    used = set()

    def chip(status, word, own="", theorems=(), borrowed_from=""):
        key = status + ("-" + word if word else "")
        for k in ("type-", "chip-", "tip-"):
            if k + key not in label:
                raise GiveUp("labels.txt: no line for '%s%s'" % (k, key))
        bright = status == "proved" or word in F_BRIGHT
        if not own and not label["chip-" + key]:  # no words in labels.txt, none of the card's own: no chip
            return ""
        return '<span class="chip chip-%s" title="%s">%s</span>' % (
            "std" if bright else "other",
            f_esc(
                label["tip-" + key]
                + "; the chip of the card " * bool(borrowed_from)
                + borrowed_from
                + "; theorems named for it: " * bool(theorems)
                + ", ".join(theorems)
            ),
            f_esc(own or label["chip-" + key]),
        )

    def row_chip(where, said):
        if not said:
            return ""
        if said[0] == "=":
            status, word = a_status(said[1:], "%s: 'chip: %s'" % (where, said))
            if status.startswith("proved"):
                raise GiveUp(
                    "%s: 'chip: %s': 'proved' goes by a theorem's card alone: 'chip: FULL.NAME'" % (where, said)
                )
            return "<p>%s</p>" % chip(status, word, "", given["%s: 'chip: %s'" % (where, said)])
        fit = [x for x in cards if x[0].ident == said]
        if not fit:
            raise GiveUp("%s: 'chip: %s': no card of that name" % (where, said))
        return "<p>%s</p>" % chip(fit[0][1], fit[0][2], own_words[said][0], own_words[said][1], said)

    def card(e, status, word):
        key = status + ("-" + word if word else "")
        foot = chip(status, word, *own_words[e.ident])
        if e.ident not in titles or e.ident not in rows_of:
            raise GiveUp("%s has a card, and no title or no rows" % e.ident)
        L, c = e.L, e.command
        colour = "class" if word in ("open", "at-risk") else F_CARD[status]
        a, b = c.line, L.line_of(c.shown_end - 1)
        out = [
            (
                3,
                '<div class="formal %s-card" id="card-%s"><div class="card-head"><span class="formal-type %s-type">'
                "%s</span>" % (colour, f_esc(e.ident), colour, f_esc(label["type-" + key])),
            ),
            (7, '<span class="italic">%s</span>' % f_esc(titles[e.ident])),
            (
                1,
                '<span class="paper-ref">%s:%d%s</span></div><div class="card-desc"><div class="sbs" data-decl="%s">'
                % (f_esc(e.path), a, "–%d" % b if b > a else "", f_esc(e.ident)),
            ),
            (
                1,
                '<div class="sbs-row sbs-head"><div class="sbs-label"></div><div class="sbs-words">%s</div>'
                '<div class="sbs-lean sbs-lean-h">%s · %s, lines %d–%d</div></div>'
                % (f_esc(label["rows-words"]), f_esc(label["rows-lean"]), f_esc(e.path), a, b),
            ),
        ]
        shown = []
        for margin, words, where, said in front.rows(e, rows_of[e.ident]):
            out.append(
                (
                    7,
                    '<div class="sbs-row"><div class="sbs-label">%s</div><div class="sbs-words">%s'
                    % (f_esc(margin), front.words(e, words)),
                )
            )
            out.append((3, row_chip("rows.txt, '=== %s'" % e.ident, said) + "</div>"))
            out.append((1, '<div class="sbs-lean">%s</div></div>' % front.cell(L, where)))
            shown += where
        if "".join(L.text[x:y] for x, y in shown[len(e.above) :]) != L.text[c.start : c.shown_end]:
            bad(4, "%s: its rows, joined, are not its statement" % e.ident)
        blocks, notes = [], []
        for l in remarks.get(e.ident, ()):
            m = re.match(r"\[([^\]]+)\] +(\S.*)$", l)
            if re.fullmatch(r"limits( [1-9]\d{0,2})+", l):
                notes += [int(n) for n in l.split()[1:]]
            elif m and not m.group(1).startswith("SLOT"):
                blocks.append([m.group(1), [m.group(2)]])
            elif blocks:
                blocks[-1][1].append(l)
            else:
                blocks.append([label["remark"], [l]])
        for n in notes:
            if n not in limits:
                raise GiveUp("remarks.txt, %s: limits.txt has no limit %d" % (e.ident, n))
            used.add(n)
        if notes:
            line = "- %s %s" % (label["limits-link"], ", ".join("[%d](#lim-%d)" % (n, n) for n in notes))
            if blocks:
                blocks[-1][1].append(line)
            else:
                blocks.append([label["remark"], [line]])
        out.append(
            (
                7,
                "</div>"
                + "".join(
                    '<div class="stmt-remark"><div class="part-label">%s</div><div class="part-body">%s</div></div>'
                    % (f_esc(n), front.words(e, ls))
                    for n, ls in blocks
                ),
            )
        )
        way = ""
        if e.ident in noted:
            if "note-link" not in label:
                raise GiveUp("labels.txt: no line for 'note-link'")
            way = '<a class="lean-link small" href="%s#%s">%s</a>' % (
                f_esc(notes_name),
                f_esc(e.ident),
                f_esc(label["note-link"]),
            )
        out.append((3, '</div><div class="card-foot">%s%s' % (button(e, False), foot)))
        out.append((5, way + "</div></div>"))
        return out

    def filled(key, numbers):
        if key not in label:
            raise GiveUp("labels.txt: no line for '%s'" % key)
        said = label[key]
        for word in numbers:
            said = said.replace("{s:%s}" % word, "s" if numbers[word] != 1 else "").replace(
                "{%s}" % word, str(numbers[word])
            )
        return said

    def definitions(titled):
        out, tops = [], {}
        for place in sorted(p for p in named_by_cards if p not in is_card):
            tops.setdefault(place[0].split("/")[0], {}).setdefault(place[0], []).append(front.entry(place))
        for key in f_idle_group_lines(label, tops):
            raise GiveUp("labels.txt: '%s': the list of definitions has no group of that name" % key)
        for top, files in tops.items():
            n = sum(len(v) for v in files.values())
            said = filled("definitions-count", {"definitions": n, "files": len(files)})
            out.append(
                '<details class="defgroup"><summary>%s <span class="cnt">· %s</span></summary>'
                % (f_esc(f_group_title(label, top)), f_esc(said))
            )
            for p, es in files.items():
                out.append('<div class="deffile">%s</div><div class="deflist">' % f_esc(p.split("/", 1)[-1]))
                for e in es:
                    out.append(
                        '<div class="defrow"><span class="defkind">%s</span>%s<span class="defdesc">%s</span><span '
                        'class="defloc">:%d</span></div>'
                        % (
                            f_esc(e.command.kind),
                            button(e, True),
                            f_esc(titles.get(e.ident, "")) if titled else f_first_sentence(front, e),
                            e.line,
                        )
                    )
                out.append("</div>")
            out.append("</details>")
        return "\n".join(out)

    def a_table(name, e):
        path = os.path.join(folder, name + ".txt")
        rows = [l.split("\t") for l in read(path, "a table", 400000).split("\n") if l.strip()]
        if len(rows) < 2 or any(len(r) != len(rows[0]) for r in rows):
            raise GiveUp("%s: a head row and rows of as many cells, between tabs" % path)
        return (
            '<div class="tblwrap"><table class="tbl %s"><thead><tr>%s</tr></thead><tbody>%s</tbody></table></div>'
            % (
                name,
                "".join("<th>%s</th>" % f_esc(f_plain(x.strip(), name + ".txt, its head row")) for x in rows[0]),
                "".join(
                    "<tr>%s</tr>"
                    % "".join(
                        "<td>%s</td>"
                        % (
                            row_chip(name + ".txt", x.strip()[5:].strip())
                            if x.strip().startswith("chip:")
                            else (
                                front.words(e, [y.strip() for y in x.split("\\n")])
                                if "\\n" in x
                                else front.inline(e, x.strip())
                            )
                        )
                        for x in r
                    )
                    for r in rows[1:]
                ),
            )
        )

    first = cards[0][0]
    bare = lambda e: f_bare(e)
    body, contents = [], []  # body: a list of pieces, each a list of (check, text); the pieces are joined by line ends
    for sec in sections:
        own = [cards[v][0] for kind, v in sec["body"] if kind == "card"]
        e = bare(own[0] if own else first)
        if not f_in_contents(label, sec["level"]):
            pass
        elif sec["level"] == 3:
            contents[-1][1].append('<li><a href="#%s">%s</a></li>' % (sec["id"], f_esc(sec["title"])))
        else:
            contents.append(
                [
                    '<li><a href="#%s">%s</a>%s'
                    % (sec["id"], f_esc(sec["title"]), " " + pill(sec["pill"]) if sec["pill"] else ""),
                    [],
                ]
            )
        head = '<h%d id="%s">%s</h%d>' % (sec["level"], sec["id"], f_esc(sec["title"]), sec["level"])
        if sec["pill"] or sec["define"]:
            head += '<div class="prop-head">%s%s</div>' % (
                pill(sec["pill"]) if sec["pill"] else "",
                '<div class="prop-define">%s</div>' % front.words(e, sec["define"]) if sec["define"] else "",
            )
        piece = [(7, head)]
        for n, (kind, v) in enumerate(sec["body"]):
            if kind == "box":
                if not v[2]:
                    raise GiveUp("claims.txt: the box '%s' is empty" % v[1])
                opens = n == 0 or sec["body"][n - 1][0] != "box"
                closes = n + 1 == len(sec["body"]) or sec["body"][n + 1][0] != "box"
                piece.append(
                    (
                        7,
                        '%s<div class="box box-%s"><div class="box-title">%s</div><ul>%s</ul></div>%s'
                        % (
                            '<div class="boxes">' if opens else "",
                            v[0],
                            f_esc(v[1]),
                            "".join("<li>%s</li>" % front.inline(e, x) for x in v[2]),
                            "</div>" if closes else "",
                        ),
                    )
                )
            elif kind == "card":
                body.append(piece)
                body.append(card(*cards[v]))
                piece = []
            elif kind == "words":
                piece.append((7, front.words(e, v)))
            elif kind == "label":
                piece.append((7, '<div class="cards-label">%s</div>' % f_esc(v)))
            elif kind == "bullets":
                piece.append((7, front.words(e, v, "prop-notes")))
            elif kind == "table":
                piece.append((7, a_table(v, bare(first))))
            elif kind == "fold":
                many = 0
                for k, _ in sec["body"][n + 1 :]:
                    if k == "fold-end":
                        break
                    many += k == "card"
                count = ' <span class="cnt">· %s</span>' % f_esc(filled("fold-count", {"cards": many})) if many else ""
                opening = '<details class="defgroup" style="max-width:none"><summary>%s%s</summary>'
                piece.append((7, opening % (f_esc(v), count)))
            elif kind == "fold-end":
                piece.append((7, "</details>"))
            elif kind == "definitions":
                piece.append((3, definitions(v)))
            elif kind == "closing":
                piece.append((7, front.words(e, f_lines(folder, "closing.txt", True), "closing")))
            elif kind == "notes":
                piece.append(
                    (
                        5,
                        '<ul class="closing">%s</ul>'
                        % "".join(
                            '<li><a href="%s#%s">%s</a>: %s</li>'
                            % (
                                f_esc(notes_name),
                                f_esc(x[0].ident),
                                f_esc(x[0].command.full or f_nameless(x[0].L, x[0].command)),
                                f_esc(titles[x[0].ident]),
                            )
                            for x in cards
                            if x[0].ident in noted
                        ),
                    )
                )
            else:
                piece.append(
                    (
                        7,
                        '<ol class="closing">%s</ol>'
                        % "".join(
                            '<li id="lim-%d" value="%d">%s%s</li>'
                            % (
                                n,
                                n,
                                front.words(e, limits[n]),
                                '<details class="defgroup"><summary>%s</summary>%s</details>'
                                % (f_esc(groups[n][0]), front.words(e, groups[n][1]))
                                if n in groups
                                else "",
                            )
                            for n in sorted(limits)
                        ),
                    )
                )
        if piece:
            body.append(piece)
    tiles = []
    for l in f_lines(folder, "tiles.txt"):
        if l.startswith("+"):
            slot, _, words = (x.strip() for x in l[1:].partition("|"))
            if not tiles or not words:
                raise GiveUp("tiles.txt: '+ slot | words' under a tile: %s" % l)
            if tiles[-1][4] and not slot:
                tiles[-1][4][-1][1].append(words)
            else:
                tiles[-1][4].append((slot, [words]))
        else:
            cells = [x.strip() for x in l.split("|")]
            if len(cells) != 4 or cells[1] not in F_PILLS or not re.fullmatch("#" + F_ID, cells[3]):
                raise GiveUp("tiles.txt: 'title | STATE | status words | #id': %s" % l)
            front.targets.add(cells[3])
            tiles.append(cells + [[]])

    def slot_words(lines):
        if all(l[:2] == "- " for l in lines):
            return '<ul class="prop-ul">%s</ul>' % "".join("<li>%s</li>" % f_esc(l[2:].strip()) for l in lines)
        if len(lines) != 1 or lines[0][:2] == "- ":
            raise GiveUp("tiles.txt: a slot holds one line of words, or bullets alone: %s" % lines[0])
        return f_esc(lines[0])

    legend = f_table(folder, "legend.txt", 3)
    if any(r[0] not in F_COLOURS + ("chip-std", "chip-other") for r in legend):
        raise GiveUp("legend.txt: a colour that the sheet has not")
    sha = lambda s: base64.b64encode(hashlib.sha256(s.encode("utf-8")).digest()).decode("ascii")
    data = {
        "kinds": kinds,
        "files": want_files,
        "decls": want_decls,
        "links": want_links,
        "cut": want_cut,
        "above": want_above,
    }
    fill = {
        "LICENCE": (6, LICENCE.strip("\n") + F_LICENCE),
        "POLICY": (
            6,
            "default-src 'none'; style-src 'sha256-%s'; style-src-attr 'unsafe-inline'; script-src 'sha256-%s'; "
            "base-uri 'none'; form-action 'none'" % (sha("\n" + parts["page.css"] + "\n"), sha("\n" + script + "\n")),
        ),
        "HTML_TITLE": (7, f_esc(label["html-title"])),
        "META_DESC": (7, f_esc(label["description"])),
        "CSS": (6, parts["page.css"]),
        "BRAND": (7, f_esc(label["brand"])),
        "H1": (7, f_esc(label["title"])),
        "SUBTITLE": (7, f_esc(label["subtitle"])),
        "BYLINE": (7, f_esc(label["byline"])),
        "SETTING": (7, front.words(bare(first), f_lines(folder, "setting.txt", True))),
        "TILES_TITLE": (7, f_esc(label["tiles-title"])),
        "TILES_NOTE": (7, f_esc(label["tiles-note"])),
        "PROPS": (
            7,
            "".join(
                '<a class="prop st-%s" href="%s"><div class="prop-name">%s</div><div class="prop-status">%s</div><div '
                'class="prop-line">%s</div></a>\n'
                % (
                    t[1],
                    f_esc(t[3]),
                    f_esc(t[0]),
                    f_esc(t[2]),
                    "".join(
                        '<div class="prop-row"><span class="prop-row-label">%s</span>%s</div>'
                        % (f_esc(s), slot_words(ls))
                        for s, ls in t[4]
                    ),
                )
                for t in tiles
            ),
        ),
        "LEGEND": (
            7,
            "".join(
                '<div><div class="lt"><span class="%s">%s</span></div><div class="ld">%s</div></div>\n'
                % ("formal-type %s-type" % r[0] if r[0] in F_COLOURS else "chip " + r[0], f_esc(r[1]), f_esc(r[2]))
                for r in legend
            ),
        ),
        "TOC": (5, "".join(h + ("<ul>%s</ul>" % "".join(kids) if kids else "") + "</li>" for h, kids in contents)),
        "CARDS": None,
        "APPENDIX_SUMMARY": (7, f_esc(label["appendix"])),
        "N_DECLS": (3, "{:,}".format(len(order))),
        "SEARCH_HINT": (7, f_esc(label["search-hint"])),
        "DATA": None,
        "JS": (6, script),
    }
    printed = any(kind == "limits" for s in sections for kind, _ in s["body"])
    ids = {"#" + s["id"] for s in sections} | {"#lim-%d" % n for n in limits if printed}
    for t in sorted(front.targets):
        if t.startswith("#") and t not in ids:
            bad(5, "the data link to %s, and the page has no such place" % t)
        if not t.startswith("#") and not os.path.isfile(os.path.join(root, *t.split("/"))):
            bad(5, "the data link to %s, and the Lean folder has no such file" % t)
    if any(kind == "limits" for s in sections for kind, _ in s["body"]) and set(limits) - used:
        bad(5, "no card leads to limit %s" % ", ".join(str(n) for n in sorted(set(limits) - used)))

    # ---- the page against all this, from its first byte to its last
    frame = re.split(r"%%([A-Z0-9_]+)%%", parts["page_template.html"])
    if sorted(frame[1::2]) != sorted(fill):
        raise GiveUp("page_template.html: its places are not the %d that the page fills, each once" % len(fill))
    pos = 0

    def expect(check, what, text):
        """The page goes on with 'text', or the check fails. The caller then stops comparing: see 'fine'."""
        nonlocal pos
        if page.startswith(text, pos):
            pos += len(text)
            return True
        k = 0
        while k < len(text) and pos + k < len(page) and page[pos + k] == text[k]:
            k += 1
        bad(
            check,
            "%s: the page has %r where %r is due. The rest of the front page was not compared with what is due"
            % (what, page[pos + k - 20 if k > 20 else pos : pos + k + 40], text[max(0, k - 20) : k + 40]),
        )
        return False

    fine = True
    for k, chunk in enumerate(frame):
        if not fine:
            break
        if k % 2 == 0:
            fine = expect(6, "the frame", chunk)
        elif chunk == "CARDS":
            before = ""
            for n, piece in enumerate(body):
                for check, text in ([(6, "\n")] if n else []) + piece:
                    fine = fine and expect(check, "the sections and cards", f_in_lines(text, before))
                    before = text[-1:] or before
        elif chunk == "DATA":
            end = page.find("</script>", pos)
            payload = page[pos:end] if end >= 0 else ""
            if "<" in payload:
                bad(6, "a '<' in the block of data")
            try:
                got = json.loads(payload)
            except ValueError:
                got = None
            if not isinstance(got, dict) or sorted(got) != sorted(data):
                bad(6, "the block of data is no JSON object with the six keys %s" % ", ".join(data))
                fine = False
                continue
            for key, check, what in (
                ("kinds", 3, "the kinds"),
                ("files", 1, "the embedded lines of the files"),
                ("decls", 3, "the table of declarations"),
                ("links", 5, "the table of links"),
                ("cut", 4, "the lines that are cut short"),
                ("above", 1, "the lines in force above each declaration"),
            ):
                if got[key] != data[key]:
                    bad(check, "the block of data: %s: %s" % (what, f_first_difference(got[key], data[key])))
            fine = expect(6, "the block of data", f_block(data))
        else:
            made = chunk in ("SETTING", "PROPS", "LEGEND", "TOC")  # markup that the generator makes, as the cards are
            fine = expect(
                fill[chunk][0],
                "the place %s of the frame" % chunk,
                f_in_lines(fill[chunk][1], "") if made else fill[chunk][1],
            )
    if fine and pos != len(page):
        bad(6, "the page goes on behind its frame's end")
    f_by_itself(page, root, front)
    outside = page.replace(parts["page.css"], "", 1).replace(script, "", 1)
    for k, ch in enumerate(outside):
        if ch not in "\n\t" and (
            ch < " "
            or (ch > "~" and unicodedata.category(ch) in ("Cc", "Cf", "Zl", "Zp", "Zs"))
            or 0xFE00 <= ord(ch) <= 0xFE0F
            or 0xE0100 <= ord(ch) <= 0xE01EF
            or ord(ch) in (0x115F, 0x1160, 0x2800, 0x3164, 0xFFA0)
        ):
            bad(6, "the character U+%04X, which cannot be seen, outside the style and the script" % ord(ch))
    counts["front page: cards"] = len(cards)
    counts["front page: sections"] = len(sections)
    counts["front page: declarations embedded"] = len(order)
    counts["front page: lines of Lean embedded"] = total
    counts["front page: links in Lean text"] = sum(len(v) // 3 for f in want_links.values() for v in f.values())
    counts["front page: bytes held, one by one"] = len(page.encode("utf-8")) if fine else 0
    return page.encode("utf-8")


def open_page(path, what):
    """(text, tree, reader) of a page. Check 6's first steps: every element closed, no character that cannot be seen."""
    page = read(path, what, 200000000)
    reader = Reader()
    reader.feed(page)
    reader.close()
    top = reader.root
    if reader.at is not top:
        bad(6, "<%s> is not closed" % reader.at.tag)
    if "style-src-attr" in page[:2000]:  # in the policy line of the front page's frame, and of no other page
        raise GiveUp("%s: this file is the front page: give it as --front=FILE" % what)
    for tag in ("html", "head", "title", "body", "main"):
        if len(top.find(tag)) != 1:
            raise GiveUp("%s must have one <%s>; it has %d" % (what, tag, len(top.find(tag))))
    for k, ch in enumerate(page):
        if ch not in "\n\t" and (
            ch < " "
            or (ch > "~" and unicodedata.category(ch) in ("Cc", "Cf", "Zl", "Zp", "Zs"))
            or 0xFE00 <= ord(ch) <= 0xFE0F
            or 0xE0100 <= ord(ch) <= 0xE01EF
            or ord(ch) in (0x115F, 0x1160, 0x2800, 0x3164, 0xFFA0)
        ):
            bad(6, "the character U+%04X, which cannot be seen, in line %d" % (ord(ch), page.count("\n", 0, k) + 1))
    return page, top, reader


def run(argv):
    option = lambda name: [a.split("=", 1)[1] for a in argv if a.startswith("--%s=" % name)]
    table_path = option("uses-table")
    unknown = [
        a
        for a in argv[1:]
        if a.startswith("--")
        and a != "--skip-check-8"
        and not a.startswith(("--uses-table=", "--heads=", "--generator=", "--short=", "--front="))
    ]
    plain = [a for a in argv[1:] if not a.startswith("--")]
    if "--help" in argv or "-h" in argv:
        sys.stdout.write(__doc__.split("\n\nTHE CHECKS")[0] + "\n")
        return 0
    wrong_short = len(option("short")) > 1 or option("short") == [""]
    wrong_front = len(option("front")) > 1 or option("front") == [""]
    if unknown or len(plain) != 2 or wrong_short or wrong_front:
        sys.stderr.write(
            "".join("unknown switch: %s\n" % plainly(a) for a in unknown)
            + ("--short=FILE goes once, with a file's name\n" if wrong_short else "")
            + ("--front=FILE goes once, with a file's name\n" if wrong_front else "")
            + __doc__.split("\n\nTHE CHECKS")[0]
            + "\n"
        )
        return 2
    root, page_path = plain
    beside = os.path.dirname(os.path.abspath(__file__))
    heads = (option("heads") or [os.path.join(beside, "statements-html")])[-1]
    generator = (option("generator") or [os.path.join(beside, "make_statements_html.py")])[-1]
    why_skipped = None
    if "--skip-check-8" in argv:
        why_skipped = "--skip-check-8"
    elif not os.path.isfile(generator):
        raise GiveUp("there is no file %s; check 8 needs the generator (or give --skip-check-8)" % generator)
    global FOLDERS
    if not os.path.isdir(os.path.join(root, FOLDERS[0])):  # before also.txt is held against a wrong folder
        raise GiveUp("%s has no folder %s/. Is it the repository's lean/ folder?" % (root, FOLDERS[0]))
    also_txt, listed = os.path.join(heads, "also.txt"), []; read_unnumbered(heads)
    if os.path.lexists(also_txt):
        listed = [l.strip() for l in read(also_txt, "the list of further folders", 10000).split("\n") if l.strip()]
    for folder in listed:
        names, place, real = folder.split("/"), root, bool(re.fullmatch(r"[A-Za-z0-9_]+(?:/[A-Za-z0-9_]+)*", folder))
        for name in names if real else ():
            place = os.path.join(place, name)
            real = real and os.path.isdir(place) and not os.path.islink(place)
        overlaps = any(within(folder + "/x", f) or within(f + "/x", folder) for f in FOLDERS + ("OnBytes",))
        if not real or overlaps:
            raise GiveUp(
                "%s names %r: it must be a path of plain names, from %s, to a real folder (no link on the way) that "
                "neither holds nor lies in a folder that the page shows already" % (also_txt, folder, root)
            )
        FOLDERS = FOLDERS + (folder,)
    page, top, reader = open_page(page_path, "the page")
    raw = page.encode("utf-8")
    short_path, front_path = (option("short") or [None])[-1], (option("front") or [None])[-1]
    long_name, short_name = os.path.basename(page_path), os.path.basename(short_path or "")
    front_name = os.path.basename(front_path or "")
    first_name = front_name or short_name  # where the line at the long page's top leads
    if front_name:  # unless the front page's data send it to another front page, with which the long page is shared
        sent = dict(f_table(os.path.join(heads, "front"), "labels.txt", 2, True)).get("back-to")
        own = (long_name, short_name, front_name)
        named = sent and re.fullmatch(r"[A-Za-z][A-Za-z0-9-]*\.html", sent) and sent not in own
        if sent is not None and not (named and os.path.isfile(os.path.join(os.path.dirname(page_path), sent))):
            raise GiveUp(
                "front/labels.txt, 'back-to | %s': name another front page that lies beside the long page: letters, "
                "digits, '-', then '.html'" % sent
            )
        first_name = sent or front_name
    # the likeliest wrong calls, told apart by what <body> begins with
    frame = top.find("body")[0].shape()
    if frame[:1] == ["div"]:
        raise GiveUp(
            "%s is built as the short page is: give the long page first, and this one as --short=FILE" % page_path
        )
    if "p.back" in frame and not first_name:
        raise GiveUp(
            "the long page has the line that leads to another page: give the pages that were made with it, as "
            "--short=FILE and --front=FILE"
        )
    if "p.back" not in frame and first_name:
        raise GiveUp(
            "the long page has no line that leads to another page: it was made alone. Make all pages again in one call"
        )
    if short_path is not None:
        PREFIX[0] = "short page: "
        short_opened = open_page(short_path, "the short page")
        if short_opened[1].find("body")[0].shape()[:1] != ["div"]:
            raise GiveUp("%s is not built as the short page is. Is it a long page?" % short_path)
        PREFIX[0] = ""
    if not first_name:
        check_grammar(top, page, reader)
    else:  # the long page then has one line more, at its top: the way back to the short page, or to a front page
        check_grammar(
            top,
            page,
            reader,
            {
                "elements": ELEMENTS,
                "classes": dict(CLASSES, p=CLASSES["p"] | {"back"}),
                "children": dict(CHILDREN, **{"body": CHILDREN["body"] | {"p.back"}, "p.back": {"a"}}),
                "hidden": ("filter", "nomatch", "panel"),
                "style": STYLE_SHA256,
                "script": SCRIPT_SHA256,
                "links": r"#\S+|%s|%s" % (HEAD_LINK, re.escape(first_name)),
            },
        )
    in_heads = check_heads(top, root, heads)

    articles = top.find("article", "e")
    named_files = {n.attrs.get("data-file", "") for n in articles + top.find("div", "mod")}
    if short_path is not None:
        named_files |= {n.attrs.get("data-file", "") for n in short_opened[1].find("article")}
    for p in named_files:
        if not re.fullmatch(r"[A-Za-z0-9_]+(/[A-Za-z0-9_]+)*\.lean", p):
            raise GiveUp("the page names a file that is not a plain path inside the Lean folder: %r" % p)
    for folder in FOLDERS[2:]:
        if not any(p.startswith(folder + "/") for p in lean_paths(root)):
            raise GiveUp("also.txt names %s: the folder holds no Lean file" % folder)
    chosen = [p for p in lean_paths(root) if any(within(p, f) for f in FOLDERS[:2])]
    chosen += [p for folder in FOLDERS[2:] for p in lean_paths(root) if within(p, folder)]  # after the two
    table = Table(root, named_files | set(chosen))
    counts["Lean files read"] = len(table.imports)
    counts["declarations in all Lean files, by this program's reading"] = sum(len(v) for v in table.decl.values())

    by_id = {}
    for n in top.walk():
        if "id" in n.attrs:
            if n.attrs["id"] in by_id or not n.attrs["id"] or re.search(r"\s", n.attrs["id"]):
                bad(5, "an id that is empty, has blanks or is used twice: %r" % n.attrs["id"])
            by_id[n.attrs["id"]] = n
    entries = [read_entry(n, table) for n in articles]
    entry_of = {id(e.node): e for e in entries}

    # ---- the frame of the page (checks 3, 5 and 7)
    body = top.find("body")[0]
    back = ["p.back"] * bool(first_name)
    if body.shape() != ["a.skip", "h1"] + back + ["div.head", "details.how", "main", "a.top", "aside", "script"]:
        raise GiveUp("the page is not built as expected: <body> holds %s" % body.shape())
    main = body.children("main")[0]
    order = FIRST_FILES + [p for p in chosen if p not in FIRST_FILES]
    parts = [p for p in ("other", "onbytes") if p in by_id]
    if main.shape() != ["section", "nav", "nav"] + ["section"] * (len(order) + len(parts)) or parts != [
        "other",
        "onbytes",
    ]:
        raise GiveUp(
            "<main> should hold two lists and %d sections (the main theorem, %d files, two parts); it holds %d "
            "sections. Was the page made with another folder of head texts, or over other Lean files? Its also.txt "
            "says which folders are shown besides the two; here it is %s"
            % (
                len(order) + 3,
                len(order),
                len(main.children("section")),
                also_txt + (": " + ", ".join(listed) if listed else " (none)"),
            )
        )
    fixed = [
        (top.find("title")[0], TITLE, {}),
        (body.children("h1")[0], TITLE, {}),
        (body.children("a")[0], T_SKIP, {"class": "skip", "href": "#main-theorem"}),
        (body.children("a")[1], T_CONTENTS, {"class": "top", "href": "#contents"}),
        (body.children("details")[0].children("summary")[0], T_HOW, {}),
    ]
    if back:
        way_back = body.children("p", "back")[0]
        fixed.append(
            (
                way_back,
                (
                    dict(f_table(os.path.join(heads, "front"), "labels.txt", 2, True))
                    if front_path is not None
                    else dict(s_table(os.path.join(heads, "short"), "labels.txt", 2, True))
                ).get("back"),
                {"class": "back"},
            )
        )
        if way_back.shape() != ["a"] or way_back.children()[0].attrs != {"href": first_name} or way_back.own_text():
            bad(5, "the line at the top should be one link to %s" % first_name)
        for a in way_back.children("a"):
            a.spend_attrs()
            in_heads.add(id(a))
    aside = body.children("aside")[0]
    if (
        aside.attrs != {"id": "panel", "aria-label": "Entry", "hidden": None}
        or aside.shape() != ["p.bar", "div"]
        or aside.children("p")[0].shape() != ["button", "a", "button"]
        or aside.children("div")[0].kids
        or aside.children("div")[0].attrs != {"id": "panel-body"}
    ):
        bad(7, "the side panel is not the expected empty frame")
    else:
        aside.spend_attrs()
        aside.children("div")[0].spend_attrs()
        bar = aside.children("p")[0].children()
        fixed += [
            (bar[0], "back", {"type": "button", "id": "panel-back"}),
            (bar[1], "go to the entry", {"id": "panel-go", "href": "#main-theorem"}),
            (bar[2], "close", {"type": "button", "id": "panel-close"}),
        ]
    sections = main.children("section")
    fixed.append((sections[0].children("h2")[0], T_MAIN, {"class": "part", "id": "main-theorem"}))
    if body.children("details")[0].shape() != ["summary", "div.head"]:
        bad(7, "'%s' must hold its head text and nothing else" % T_HOW)
    if (
        sections[0].shape() != ["h2.part", "article.e", "article.e"]
        or [n.attrs.get("id") for n in sections[0].children("article")] != MAIN
    ):
        bad(3, "under '%s' must be the entries %s and nothing else" % (T_MAIN, " and ".join(MAIN)))

    # ---- the files, in the stated order; in each, comments and declarations in the file's order (checks 2 and 3)
    comment_jobs = []
    for section, path in zip(sections[1:], order):
        L = table.files[path]
        fixed.append((section.children("h2")[0], path, {"id": path}))
        opening, later = shown_comments(L)
        expected = sorted(
            [(c.start, c) for c in L.commands() if c.kind]
            + [(a, (a, b)) for a, b in ([opening] if opening else []) + later],
            key=lambda x: x[0],
        )
        nodes = section.children()[1:]
        if len(nodes) != len(expected):
            bad(
                3,
                "%s: the page shows %d comments and declarations; the file has %d" % (path, len(nodes), len(expected)),
            )
        for node, (_, x) in zip(nodes, expected):
            if isinstance(x, tuple):
                if node.tag + "." + node.cls() != "div.mod" or node.attrs.get("data-file") != path:
                    bad(3, "%s: the comment at line %d should come here" % (path, L.line_of(x[0])))
                    continue
                compare_comment(node, L, x[0], x[1], opener_length(L, x[0]), "%s:%d" % (path, L.line_of(x[0])))
                comment_jobs.append((node, L, x[0], True))
                count("comments of files compared")
            elif x.full in MAIN:
                a = node.children("a")
                if (
                    node.tag + "." + node.cls() != "p.moved"
                    or node.attrs.get("data-from") != str(x.line)
                    or len(a) != 1
                    or a[0].attrs != {"class": "r", "href": "#" + x.full}
                    or fold(node.text()) != x.full
                ):
                    bad(
                        3,
                        "%s:%d: here should be one line with the name %s, linked to its entry at the top"
                        % (path, x.line, x.full),
                    )
                node.spend_text()
                node.spend_attrs("data-from")
                for link in a:
                    link.spend_attrs()
                e = entry_of.get(id(by_id.get(x.full)))
                if e is None or (e.path, getattr(e, "line", 0)) != (path, x.line):
                    bad(3, "%s: the entry at the top is not the declaration at %s:%d" % (x.full, path, x.line))
            else:
                e = entry_of.get(id(node))
                if e is None or not e.ok or (e.path, e.line) != (path, x.line):
                    bad(3, "%s:%d: the entry of this %s should come here" % (path, x.line, x.kind))
            if not isinstance(x, tuple):
                count("declarations of the two folders, by tokens: " + x.kind)
        # an attribute: '@[ ... ]' on one line, brackets inside it up to four deep; each character fits in one way only
        inner = r"\[[^\[\]\n]*\]"
        for _ in range(3):
            inner = r"\[(?:[^\[\]\n]|%s)*\]" % inner
        pattern = r"^(?:@\[(?:[^\[\]\n]|%s)*\]\s*)*(?:(?:%s)\s+)*(?:%s)(?![\w.'])" % (
            inner,
            "|".join(MODIFIERS),
            "|".join(KINDS),
        )
        if len(re.findall(pattern, L.plain(), re.M)) != sum(1 for c in L.commands() if c.kind):
            bad(3, "%s: a plain count of lines that begin a declaration gives another number" % path)
        for c in L.commands():
            if c.trouble and not c.kind:
                bad(3, "%s:%d: %s: it would have no entry" % (path, c.line, c.trouble))
        margin = set(L.offsets)
        for a, b in L.comments():
            if (
                L.text.startswith("/-!", a)
                and a not in margin
                and not any(c.start <= a < c.end for c in L.commands() if c.kind)
            ):
                bad(3, "%s:%d: an indented '/-! ... -/' comment; neither program shows those" % (path, L.line_of(a)))
        for m in re.finditer(
            r"^[ \t]+(?:@\[[^\n]*\]\s*)?(?:(?:%s)\s+)*(?:%s)(?![\w.'])" % ("|".join(MODIFIERS), "|".join(KINDS)),
            L.plain(),
            re.M,
        ):
            bad(
                3,
                "%s:%d: an indented line begins like a declaration; neither program reads those"
                % (path, L.line_of(m.end())),
            )
    for e in entries:
        e.part = None

    # ---- the two last parts: by file, each file's opening comment folded above its entries
    for section, part in zip(sections[1 + len(order) :], parts):
        fixed.append((section.children("h2")[0], T_PART[part], {"class": "part", "id": part}))
        nodes, last_path, last_line = section.children(), "", 0
        if section.shape()[:2] != ["h2.part", "div.head"]:
            bad(7, "the part '%s' must begin with its title and its head text" % part)
        for k, node in enumerate(nodes[2:]):
            if node.tag == "article":
                e = entry_of[id(node)]
                e.part = part
                if e.ok and (e.path != last_path or e.line <= last_line):
                    bad(3, "%s: entries must be grouped by file and follow the file's order" % e.ident)
                last_line = getattr(e, "line", 0)
                continue
            path = (
                fold((node.children("summary")[0] if node.tag == "details" else node).text())
                if node.tag in ("details", "p")
                else ""
            )
            following = nodes[2 + k + 1] if 2 + k + 1 < len(nodes) else None
            if (
                path <= last_path
                or path not in table.files
                or following is None
                or following.attrs.get("data-file") != path
            ):
                bad(
                    3,
                    "the part '%s': the files must be in path order, each followed by its entries (at %r)"
                    % (part, path),
                )
                continue
            last_path, last_line = path, 0
            (node.children("summary")[0] if node.tag == "details" else node).spend_text()  # it is the next entry's file
            L = table.files[path]
            opening = shown_comments(L)[0]
            if opening is None:
                if node.tag + "." + node.cls() != "p.path":
                    bad(3, "%s has no opening comment, so only its path should be shown" % path)
            elif (
                node.tag + "." + node.cls() != "details.file"
                or node.shape() != ["summary", "div.mod"]
                or node.find("a", None)
                and any("id" in x.attrs for x in node.walk())
            ):
                bad(3, "%s: its opening comment should be folded above its entries" % path)
            else:
                mod = node.children("div")[0]
                if mod.attrs.get("data-file") != path:
                    bad(3, "%s: the folded comment is another file's" % path)
                compare_comment(
                    mod,
                    L,
                    opening[0],
                    opening[1],
                    opener_length(L, opening[0]),
                    "%s:%d" % (path, L.line_of(opening[0])),
                    as_lines=True,
                )
                comment_jobs.append((mod, L, opening[0], False))
                count("opening comments of other files compared")
    for e in entries:
        if e.ok:
            check_source(e, e.part)
            count("entries: " + (e.part or "the two folders"))
            if any(within(e.path, f) for f in FOLDERS) != (e.part is None) or (
                e.part == "onbytes"
            ) != e.path.startswith("OnBytes/"):
                bad(3, "%s: it is in the wrong part of the page" % e.ident)

    # ---- names (check 5)
    good = [e for e in entries if e.ok and e.command and not e.command.trouble]
    links = Links(table, good)
    for e in good:
        links.prepare(e)
    for e in good:
        links.source(e, e.part)
    for e in good:
        if e.command.doc:
            links.comment(e.ident, e.words, e.command, e.path, e.bound, e.plainly, (e.path, e.line), e.part is None)
    for node, L, start, first_layer in comment_jobs:
        declarations = [c for c in L.commands() if c.kind]
        if declarations:
            c = next((c for c in declarations if c.start >= start), declarations[-1])
            what = "%s:%d" % (L.path, L.line_of(start))
            links.comment(what, node, c, L.path, set(), None, None, first_layer, folded=not first_layer)
        elif node.find("a"):
            bad(5, "%s: links in a comment of a file that declares nothing" % L.path)
    first_two = {last for last, uses in links.after_bracket.items() if any(u[0] is None for u in uses)}
    for last in sorted(set(links.after_bracket) - first_two):
        bad(5, "'.%s' after a bracket is linked in the last two parts only" % last)
    print_after_bracket = ", ".join("%s (%d)" % (k, len(v)) for k, v in sorted(links.after_bracket.items()))

    # ---- what the part on other folders must hold: just what the first two folders' texts name (check 3)
    needed = {p for p in links.needed if not any(within(p[0], f) for f in FOLDERS + ("OnBytes",))}
    have = {(e.path, e.line) for e in good if e.part == "other"}
    for p in sorted(needed - have):
        bad(3, "%s:%d is named by a text of the first two folders but has no entry" % p)
    for p in sorted(have - needed):
        bad(3, "%s:%d has an entry among the other folders, but no text of the first two folders names it" % p)
    text = read(os.path.join(root, "OnBytes", "THEOREMS.md"), "OnBytes/THEOREMS.md", 1000000)
    first_table = re.search(r"^\|.*(?:\n\|.*)*", text, re.M)
    listed = [
        x
        for row in (first_table.group().split("\n")[2:] if first_table else ())
        for x in re.findall("%s([^%s]+)%s" % ((BACKTICK,) * 3), row.split("|")[1])
        if "/" not in x and not x.endswith(".lean")
    ]
    if not listed:
        bad(3, "no theorem's name found in the first column of the first table of OnBytes/THEOREMS.md")
    on = [e.ident for e in good if e.part == "onbytes"]
    if (
        sorted(on) != sorted(set(on))
        or len(on) != len(listed)
        or any(sum(1 for i in on if i == x or i.endswith("." + x)) != 1 for x in listed)
    ):
        bad(
            3,
            "the last part must hold exactly the %d theorems that OnBytes/THEOREMS.md lists; it holds %d entries"
            % (len(listed), len(on)),
        )
    cells = [
        re.findall("%s([^%s]+)%s" % ((BACKTICK,) * 3), row.split("|")[1])
        for row in (first_table.group().split("\n")[2:] if first_table else ())
    ]
    for cell in cells:  # a name that two theorems of OnBytes/ bear means the one in the file that the cell names next
        for k, x in enumerate(cell):
            same = {
                p
                for full, p in table.by_last.get(x.split(".")[-1], ())
                if ".".join(full).endswith("." + x)
                and p[0].startswith("OnBytes/")
                and any(r[:2] == p and r[2] in ("theorem", "lemma") for r in table.decl.get(".".join(full), ()))
            }
            file = next((y for y in cell[k + 1 :] if "/" in y or y.endswith(".lean")), None)
            if "/" in x or x.endswith(".lean") or len(same) < 2:
                continue
            for e in good:
                if e.part == "onbytes" and e.ident.endswith("." + x) and not e.path.startswith("OnBytes/" + str(file)):
                    bad(
                        3,
                        "OnBytes/THEOREMS.md names %s in %s, and the last part shows the one of %s" % (x, file, e.path),
                    )
    if any(e.kind not in ("theorem", "lemma") for e in good if e.part == "onbytes"):
        bad(3, "the last part holds something that is not a theorem")
    counts["theorems listed in OnBytes/THEOREMS.md"] = len(listed)

    # ---- the lists at the top (check 5)
    navs = main.children("nav")
    place_entry = {(e.path, e.line): e for e in good}
    layers, seen = [], set(MAIN)
    for _ in range(2):
        layer = []
        for e in (
            [place_entry[p] for p in [(x.path, x.line) for x in good if x.ident in MAIN]] if not layers else layers[-1]
        ):
            for _, place in e.named:
                t = place_entry.get(place)
                if t is not None and t.ident not in seen:
                    seen.add(t.ident)
                    layer.append(t)
        layers.append(layer)
    if not layers[0] or [x.ident for x in good if x.ident in MAIN] != MAIN:
        bad(5, "the two main entries could not be read, so the two lists at the top were not compared")
    wanted_shape = ["h2", "ul"] * sum(1 for l in layers if l)
    if navs[0].attrs != {"aria-label": T_LINKED} or navs[0].shape() != wanted_shape:
        bad(5, "'%s' should hold %d lists, each under its title" % (T_LINKED, len(wanted_shape) // 2))
    else:
        navs[0].spend_attrs()
        for h2, ul, title, layer in zip(navs[0].children("h2"), navs[0].children("ul"), T_NAMED, layers):
            fixed.append((h2, title, {}))
            check_list(ul, [(t.ident, t.name if t.command.full else t.ident, t.kind) for t in layer], title)
            if any(a.cls() != "r" for a in ul.find("a")):
                bad(5, "the names under '%s' must be links of the kind that opens a card" % title)
            count("names in the two lists at the top", len(layer))
    contents = navs[1].children("details")
    if (
        navs[1].attrs != {"aria-label": T_CONTENTS}
        or navs[1].shape() != ["details"]
        or contents[0].attrs != {"id": "contents"}
        or contents[0].shape() != ["summary", "input", "p.none"] + ["details"] * (len(order) + len(parts))
    ):
        bad(5, "the contents should be one folded list with the filter and one group for each file and part")
    else:
        navs[1].spend_attrs()
        contents[0].spend_attrs()
        contents[0].children("input")[0].spend_attrs()  # compared just below
        fixed.append((contents[0].children("summary")[0], T_CONTENTS, {}))
        fixed.append((contents[0].children("p")[0], "no match", {"class": "none", "id": "nomatch", "hidden": None}))
        if contents[0].children("input")[0].attrs != {
            "id": "filter",
            "type": "search",
            "placeholder": "Filter",
            "aria-label": "Filter",
            "hidden": None,
        }:
            bad(7, "the filter box is not the expected one")
        in_file = {}
        for e in good:
            in_file.setdefault(e.part or e.path, []).append(e)
        for group, key in zip(contents[0].children("details"), order + parts):
            a = group.children("summary")[0].children("a") if group.shape() == ["summary", "ul"] else []
            if (
                len(a) != 1
                or a[0].attrs != {"href": "#" + key}
                or fold(group.children("summary")[0].text()) != T_PART.get(key, key)
                or group.attrs
            ):
                bad(5, "the contents: the group for %s is not as expected" % key)
                continue
            group.children("summary")[0].spend_text()
            a[0].spend_attrs()
            members = sorted(in_file.get(key, []), key=lambda e: (e.path, e.line))
            check_list(
                group.children("ul")[0],
                [(e.ident, e.name if e.command.full else e.ident, None) for e in members],
                "the contents, " + key,
            )
            count("lines of the contents compared", len(members))

    # ---- fixed words, and nothing else outside entries and comments (check 7)
    for node, words, attrs in fixed:
        if fold(node.text()) != words or node.attrs != attrs:
            bad(
                7,
                "<%s> should read '%s' with the attributes %s; it reads '%s' with %s"
                % (node.tag, words, attrs, fold(node.text())[:60], node.attrs),
            )
        node.spend_text()
        node.spend_attrs()
    # whatever no comparison has covered is the page's own, and fails ('class' is held by the closed lists)
    for n in top.walk():
        for k in n.kids:
            if isinstance(k, Text) and not k.used and k.strip():
                bad(7, "words that no comparison covers, in <%s>: %r" % (n.tag, fold(k)[:80]))
        for a in n.attrs:
            if a != "class" and a not in n.used:
                bad(7, "an attribute that no comparison covers: <%s %s=%r>" % (n.tag, a, (n.attrs[a] or "")[:60]))
    for i in by_id:
        if i not in FIXED_IDS and i not in order and i not in {e.ident for e in entries}:
            bad(6, "an id that is neither an entry's, nor a file's, nor one of the fixed ones: %s" % i)
    for a in top.find("a"):
        href = a.attrs.get("href")
        if id(a) in in_heads:
            continue
        if not href or not href.startswith("#") or href[1:] not in by_id:
            bad(5, "a link that leads nowhere on the page: %s" % href)
        else:
            count("links that lead to a place on the page")
    for d in top.find("details"):
        if any("id" in x.attrs for x in d.walk() if x is not d and x.attrs.get("id") not in ("filter", "nomatch")):
            bad(5, "a folded block holds the target of a link")

    undecided = with_lean_table(table_path[0], good, links, by_id) if table_path else []

    # ---- the short page (checks 1 to 7 of it)
    raw_short = b""
    if short_path is not None:
        PREFIX[0] = "short page: "
        raw_short = check_short(
            short_path,
            root,
            heads,
            table,
            links,
            good,
            {e.ident for e in entries} - {e.ident for e in good},
            long_name,
            lambda *_: short_opened,
        )
        PREFIX[0] = ""

    # ---- the front page (checks 1 to 7 of it)
    raw_front = b""
    if front_path is not None:
        PREFIX[0] = "front page: "
        ids_there = set()
        if short_path is not None:
            ids_there = {n.attrs["id"] for n in short_opened[1].find("article") if "id" in n.attrs}
        raw_front = check_front(front_path, root, heads, table, links, long_name, short_name, ids_there)
        PREFIX[0] = ""

    # ---- check 8
    both_pages = ["--long-name=" + long_name] if first_name else []
    both_pages += ["--short=" + short_name] if short_path is not None else []
    both_pages += ["--front=" + front_name] if front_path is not None else []
    if not why_skipped:
        for k, seed in enumerate(("1", "4242")):  # two seeds, so that an order left to chance would show
            try:
                r = subprocess.run(  # -B: no bytecode is cached. Not -I: it would make Python ignore PYTHONHASHSEED
                    [sys.executable, "-B", generator, root, "-", "--heads=" + heads, *both_pages],
                    stdin=subprocess.DEVNULL,
                    stdout=subprocess.PIPE,
                    stderr=subprocess.PIPE,
                    env=dict(os.environ, PYTHONHASHSEED=seed),
                    timeout=1800,
                )
            except subprocess.TimeoutExpired:
                bad(8, "the generator had not ended after half an hour and was stopped")
                break
            except OSError as e:
                bad(8, "the generator could not be run: %s" % e)
                break
            if r.returncode != 0:
                bad(8, "the generator stopped: %s" % fold(r.stderr.decode("utf-8", "replace")[-300:]))
                continue
            # with both pages the long one comes first: it ends where its </html> ends. Each page is held for itself
            end = r.stdout.find(b"</html>\n") + len(b"</html>\n") if both_pages else len(r.stdout)
            if r.stdout[:end] != raw:
                bad(8, "run %d gives other bytes than the %s" % (k + 1, "long page" if both_pages else "page"))
            if r.stdout[end : end + len(raw_short)] != raw_short:
                bad(8, "run %d gives other bytes than the short page" % (k + 1))
            if r.stdout[end + len(raw_short) :] != raw_front:
                bad(8, "run %d gives other bytes than the front page, or more than the pages" % (k + 1))
            if r.stdout == raw + raw_short + raw_front:
                count("runs of the generator that give the page's bytes")

    what = {
        1: "the Lean source on the page is the files' text, and the lines above each declaration are those in force",
        2: "docstrings and files' comments are the files' words",
        3: "every declaration has one entry; order and parts are as stated",
        4: "no statement is cut short, and no proof is shown",
        5: "links, marked names and the lists at the top follow the written rule",
        6: "nothing from outside; only known elements; the expected style and script",
        7: "no words of the page's own beyond the head texts and the fixed titles",
        8: "two runs of the generator give the page's bytes",
    }
    if short_path is not None:
        what[7] = "no words of a page's own beyond the head texts, the short page's data files and the fixed titles"
        what[8] = "two runs of the generator give both pages' bytes"
    if front_path is not None:
        what[7] = "no words of a page's own beyond the head texts, the other pages' data files and the fixed titles"
        what[8] = "two runs of the generator give all the pages' bytes"
    show("%s: %s" % ("page" if short_path is None else "the long page", os.path.basename(page_path)))
    show("bytes: %d" % len(raw))
    show("sha256: %s" % hashlib.sha256(raw).hexdigest())
    if short_path is not None:
        show("the short page: %s" % short_name)
        show("bytes: %d" % len(raw_short))
        show("sha256: %s" % hashlib.sha256(raw_short).hexdigest())
    if front_path is not None:
        show("the front page: %s" % front_name)
        show("bytes: %d" % len(raw_front))
        show("sha256: %s" % hashlib.sha256(raw_front).hexdigest())
    failed = 0
    for k in range(1, 9):
        skipped = k == 8 and why_skipped
        show(
            "check %d: %s: %s"
            % (
                k,
                (
                    "SKIPPED (%s)" % why_skipped
                    if skipped
                    else "PASS" if not problems[k] else "FAIL (%d)" % len(problems[k])
                ),
                what[k],
            )
        )
        show_problems(k)
        failed += bool(problems[k])
    show("counts:")
    for k in sorted(counts):
        show("    %s: %d" % (k, counts[k]))
    show("last parts linked after a closing bracket: " + print_after_bracket)
    show("folders shown in full besides the two (from also.txt): %s" % (", ".join(FOLDERS[2:]) or "none"))
    show("Lean's own table: %s" % ("compared, under check 5" if table_path else "not given"))
    if undecided:
        show("links that Lean's table can neither confirm nor contradict:")
        for u in undecided:
            show("    " + u)
    if failed:
        show("RESULT: %d of the checks fail." % failed)
        show(
            "Make %s again with make_statements_html.py%s, or look at the first place named above."
            % (
                ("the page", "")
                if short_path is None and front_path is None
                else (
                    ("both pages", " and --short" if front_path is None else " and --front")
                    if short_path is None or front_path is None
                    else ("the three pages", ", --short and --front")
                )
            )
        )
    else:
        show("RESULT: checks 1 to 7 pass; check 8 was skipped" if why_skipped else "RESULT: all eight checks pass")
    return 1 if failed else 0


def main(argv):
    if sys.version_info < (3, 7):
        sys.stderr.write("This program needs Python 3.7 or later.\n")
        return 2
    for stream in (sys.stdout, sys.stderr):  # a terminal that cannot show a character gets its escape, not a traceback
        if hasattr(stream, "reconfigure"):
            stream.reconfigure(errors="backslashreplace")
    try:
        return run(argv)
    except GiveUp as e:
        for k in range(1, 9):  # what the checks had found before they had to end: it may name the cause
            if problems[k]:
                show("check %d: FAIL (%d), before the checks ended" % (k, len(problems[k])))
                show_problems(k)
        sys.stdout.flush()
        sys.stderr.write("CANNOT CHECK: %s%s\n" % (PREFIX[0], plainly(str(e))))
        return 1
    except KeyboardInterrupt:
        sys.stderr.write("\nInterrupted: NOTHING IS CHECKED. This program has written no file.\n")
        return 130
    except (RecursionError, MemoryError, OSError) as e:
        why = {
            RecursionError: "something on the page or in a Lean file is nested deeper than this program can follow",
            MemoryError: "the memory does not suffice",
        }.get(type(e)) or str(e)
        sys.stderr.write("CANNOT CHECK: %s\n" % plainly(why))
        return 1
    except (IndexError, KeyError, AttributeError, TypeError, ValueError) as e:
        # something that the checks take for granted is missing from the page
        line = e.__traceback__
        while line.tb_next:
            line = line.tb_next
        sys.stderr.write(
            "CANNOT CHECK: the page is not built as this program expects (%s at line %d of this program).\n"
            "Make the page again with make_statements_html.py.\n" % (type(e).__name__, line.tb_lineno)
        )
        return 1


# Numbers left out of comments (unnumbered.txt).
UNNUMBERED = []  # from unnumbered.txt: paths from the Lean folder, each a Lean file (A/B.lean) or a folder (A/)
ON_DISK = {}  # by path: a listed file's own text, for the sha256 of the file that the front page gives
ONE_NUMBER = re.compile(r"[0-9]+(?:\.[0-9]+)*")
_SEP = r"(?:,\s*(?:and\s+)?|\s+(?:and|to|or)\s+|[-–/])"
# A list goes on only with numbers of the same form; a list of whole numbers needs the plural (Sections 2 and 3), so
# 'Section 2, 128 bits' keeps its 128.
NUMBERED = re.compile(
    r"\b(?:[Dd]efinition|[Ss]ection|[Pp]roposition)"
    r"(?:s?\s+[0-9]+(?:\.[0-9]+)+(?:%s[0-9]+(?:\.[0-9]+)+)*" % _SEP
    + r"|s\s+[0-9]+(?!\.?[0-9])(?:%s[0-9]+(?!\.?[0-9]))*" % _SEP
    + r"|\s+[0-9]+(?!\.?[0-9]))"
)


def read_unnumbered(heads):
    """Fill UNNUMBERED from unnumbered.txt in the folder 'heads', if it lies there."""
    del UNNUMBERED[:]
    ON_DISK.clear()
    if os.path.lexists(os.path.join(heads, "unnumbered.txt")):
        lines = read(os.path.join(heads, "unnumbered.txt"), "the list unnumbered.txt", 10000).split("\n")
        UNNUMBERED.extend(l.strip() for l in lines if l.strip())


def unnumbered(path, text):
    """The text of the Lean file 'path' (a path from the Lean folder) as the pages are to show it. In a file that
    unnumbered.txt lists, or that lies in a folder it lists, the numbers behind Section, Definition or Proposition in
    comments and doc comments become '…'. Strings stay as they are. Two counts at the run's end give the numbers changed
    and the files read this way."""
    if not any(path == p or (p[-1] == "/" and path.startswith(p)) for p in UNNUMBERED):
        return text
    probe = Lean.__new__(Lean)  # not Lean(...): __init__ would read the file and call unnumbered() again
    probe.path, probe.text, probe._tokens = path, text, None
    probe.offsets = [0] + [m.end() for m in re.finditer("\n", text)]
    kept, done, before = [], 0, PREFIX[0]
    for _, a, b in (x for x in probe.tokens() if x[0] == "c"):
        kept += [text[done:a], NUMBERED.sub(lambda m: ONE_NUMBER.sub("…", m.group()), text[a:b])]
        done = b
    new = "".join(kept) + text[done:]
    if path not in ON_DISK:
        PREFIX[0] = ""
        count("numbers in comments compared as '…' (unnumbered.txt)", new.count("…") - text.count("…"))
        count("Lean files whose comments are compared with their numbers as '…' (unnumbered.txt)")
        PREFIX[0] = before
    ON_DISK[path] = text
    return new


if __name__ == "__main__":
    sys.exit(main(sys.argv))
