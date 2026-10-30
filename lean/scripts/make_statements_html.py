#!/usr/bin/env python3
# Copyright 2026 Anthropic PBC
# SPDX-License-Identifier: Apache-2.0
"""Make the reading pages from the Lean files: lean/STATEMENTS.html, the front page, with the statements to read in
rows, words beside Lean; and lean/STATEMENTS-ALL.html, the long page, with every declaration of VerifiableInference/
and IntegerModel/. With --short it makes a short page too, from the folder short/.

Usage, from the repository's lean/ folder:
    python3 scripts/make_statements_html.py . STATEMENTS-ALL.html --front=STATEMENTS.html

In general:
    make_statements_html.py LEAN_FOLDER OUTPUT_HTML [--short=SHORT_HTML] [--front=FRONT_HTML] [--long-name=NAME.html]
                            [--heads=FOLDER] [--list-theorems=FILE.tsv] [--overwrite]

OUTPUT_HTML is the long page. Without --short it alone is made, and it says nothing of a short page. With --short both
are made in one run, the long page has one line more at its top, which leads to the short page, and the short page's
links lead to the long page by its file name: the two belong in one folder. What the short page holds is data: nine
small files in the folder short/ among the head texts (section 6 of this program says what each is). With --front the
front page is made as well, in the same run; the line at the long page's top then leads to it (or where the label
'back-to' says: section 7), and its cards lead to their notes on the short page. What it holds is data too: the files
of the folder front/; and so are its frame, style sheet and script, in the folder shell/ (section 7 says what each file
is; shell/ORIGIN.txt says what they are).
Without --front neither folder is touched. For the short page and the front page the program also reads
LEAN_FOLDER/scripts/top-theorems.txt, the list of the theorems that the library's audit looks up. OUTPUT_HTML may be
'-': the page then goes to standard output and the counts to standard error. With --short all pages go there, the long
one first, the front page last; no file is written, and --long-name says how the long page is called in the links.
--heads names the folder with the four head texts, one paragraph per line: head.txt (the top of the page), head-how.txt
(folded under it), head-other.txt and head-onbytes.txt (the top of the last two parts). By default it is the folder
statements-html/ next to this program. If that folder also holds a file also.txt, each of its lines names one more
folder to show in full, after the two: its path from LEAN_FOLDER, such as A or A/B, without a '/' at its end. So the
head texts and what the page shows are chosen together. --list-theorems writes the theorems on the long page to FILE,
one per line: part, kind, full name, file. Needs Python 3.7 or later and only the standard library.

The program writes OUTPUT_HTML, SHORT_HTML, FRONT_HTML and FILE.tsv and nothing else. Their names must end in .html and
.tsv. It always refuses a name that is a link, a folder, a pipe or the like, and a file that has a second name (a hard
link). It replaces an empty file. It replaces another file only if that file begins like one of its own making and of
the same kind (a page: doctype and licence lines, a title that ends in 'Lean statements' on the long page and on no
other, the front page's four licence lines and a word of its policy line on the front page and on no other; the list:
its header line), or if --overwrite is given; that switch holds for every file named in the call, and what lay in a
replaced file is lost. It looks before the scan, and again at the file that it has opened. Where the system can do so
(not on Windows) it opens the file without following a link. It does not look at links among the folders above the file.
A file that lies there is emptied and filled in place, not written aside and renamed: if the write fails or the run is
killed in the middle, the file is left empty or cut short, and the same call makes it again.

The program sets no limit on its time or its memory, only on the size of each file that it reads. It writes
nothing before its scan has ended, so Ctrl-C during the scan leaves everything as it was. A file that it
reads may not itself be a link (links among the folders above it are not looked at). Where the system can open
a file without following such a link, it does so. Where it cannot (Windows), it looks first, refuses a link,
and then opens: two acts.

What the long page shows. For each declaration of VerifiableInference/ and IntegerModel/: on the left its
docstring, on the right its Lean source. A theorem, lemma or example is cut before its proof; every
other declaration is printed whole. Above the source come the lines that are in force there
('variable', 'include', 'omit', 'universe', notations) and the '... in' lines that belong to the
declaration. A 'variable' line is left out only if Lean can take nothing from it: it has no instance
binder, the declaration's own binders declare every one of its names again, and nothing names one of
them before that. Each file's opening comment and its '/-! ... -/' comments are shown too. The two
entries named in MAIN_THEOREMS open the page; a line with their name takes their place in their files.
Two more parts follow: declarations of other folders that the texts above name, and the theorems
listed in OnBytes/THEOREMS.md. There the entries are grouped by file, and of a file's comments only
the opening one is shown, folded, line for line. All text on that page is copied from the Lean files,
except the four head texts and a few fixed titles.

WHEN A NAME BECOMES A LINK. This program does not run Lean. It follows the rules below, and when in
doubt it makes no link.
 1. The first part of the name must not be bound anywhere in the shown source or in the lines in
    force (a binder, a pattern, a field, a name given a value inside brackets). The test leans
    towards calling a name bound.
 2. Lean's order of lookup must find exactly one declaration among those that the file can see (its
    own and those of the files it imports, directly or indirectly). Take the longest beginning of
    the name that is declared. Look first under the enclosing namespaces, including the namespace
    in the declaration's own name. Only if nothing is found there, take the name as written and
    under the 'open' lines in force. A protected name needs its namespace. If two fit: no link.
 3. 'x.f' where x is bound: a link only if every binding of x in the text writes the same plain type
    'T ...', and 'T.f' is declared or f is a field of T. Here T is what rules 1 and 2 find, or, if
    no name in the Lean files ends in T (a type of Lean's own, such as Array), T as written.
 4. '(g ...).f': if g is a link by rules 1 and 2 to a declaration whose source writes its result type
    as a plain 'T ...', T resolves there by rules 1 and 2, and 'T.f' is declared or f is a field
    of T: a link to that. Otherwise '( ... ).f' is a link only if exactly one full name in all Lean
    files ends in f, and f is not on the list of names that Lean's core or Mathlib are likely to
    have (LIKELY_ELSEWHERE). In the last two parts, rule 4 applies only to an f that it also links
    somewhere in the first two folders.
 5. A field or a constructor links to the entry of its structure or inductive type.
 6. Between backticks in a comment: rules 1, 2 and 5, and a file that is not imported counts as
    visible if exactly one declaration in all files fits. No link for a name of one or two
    characters. In a file's comment, no link for a one-part name that some shown declaration of
    that file binds. In a docstring, no link for a one-part name if the source beside it links the
    same last part, written plainly (not after a dot), to another declaration.
    In the folded opening comments of the last two parts, which are there for credits and not for
    walking: a link only for a name written with a dot, if exactly one full name in all files ends
    with it.
 7. A name in Lean source that these rules resolve to a declaration without an entry on the long page is
    not a link. It is marked, and its tooltip gives the file and line. In comments nothing is marked.
The short page follows the same rules. There a link leads to the declaration's card or index line, or else to its entry
on the long page. So does the front page: there a name that the rules resolve can be hovered and clicked if its
declaration is embedded on the page (section 7), and is left plain if not; nothing is marked. In the front page's words
one rule more, the last: a name that is not bound and that the rules resolve to nothing means the one card whose
declaration's full name ends in it, if there is just one such card.
Lean's core and Mathlib are unknown to this program. If one of their names and one of ours both fit
under an 'open' line, Lean chooses by type, and this program links ours.

What the scanner reads. It expects every command to begin in the first column. It stops, with file and line, at '#exit'
in any Lean file (it hides what is below it), and at anything in the shown files that it does not know: an unknown
command (it might declare names), an indented declaration, 'have', 'by', 'letI' and the like outside brackets in a
statement, a bar outside brackets of which it cannot tell whether it opens the proof, a text that ends in a sign such as
':=', a docstring in an unexpected place (before a command that is neither a declaration nor a 'notation' or 'local
notation', or before nothing), a character that cannot be seen. In any Lean file it also stops at one of the
words listed at COMMAND_WORDS, which open a command, if it stands inside another command (Lean would begin a command
there), at a command whose brackets do not pair, and at a string of which it cannot tell where Lean ends it. It takes a
command that begins with '#' to change nothing that a page shows, and it does not see what a macro or an elaborator of
the Lean files' own adds, changes or leaves out. Of 'open A renaming x → y' it follows nothing: the new names stay plain
text, without a link. A command that it does not know, or an 'open' line that it cannot read, in a file outside the
folders that are shown whole, it passes over and counts in its log, and it shows nothing that stands below such a
command in that file. All this fits Lean files written in this library's plain style. A file written to deceive the
scanner may still pass it. The pages show Lean text: what that text means to Lean, with the notations and macros
declared anywhere in the library, is Lean's to say.
"""

import sys

if __name__ == "__main__" and not sys.flags.isolated and not getattr(sys.flags, "safe_path", False):
    del sys.path[0]  # this program's own folder: a file there with the name of a library module must not be imported

import base64
import bisect
import errno
import hashlib
import html
import json
import os
import re
import stat
import unicodedata

# ------------------------------------------------------------------------------------------------
# What is shown, and in which order
# ------------------------------------------------------------------------------------------------

CHOSEN_FOLDERS = ["VerifiableInference", "IntegerModel"]

# The two files of the two entries that open the page, the files of the statements, then those of the model, in the
# order of the front page's sections. The other files follow in path order.
FIRST_FILES = [
    "Johnson/Goal/Skeleton/SoundOfVerifyAt.lean",
    "Johnson/PVR/SoundOfTheForm.lean",
    "VerifiableInference/Statements.lean",
    "VerifiableInference/RandomOracleModel.lean",
    "VerifiableInference/MoreStatements.lean",
    "VerifiableInference/Steps.lean",
    "VerifiableInference/ModelWeights.lean",
    "IntegerModel/Model.lean",
    "VerifiableInference/RequestOfTokens.lean",
    "VerifiableInference/CanServe.lean",
    "IntegerModel/TrueRequest.lean",
    "IntegerModel/ModelOutput.lean",
    "IntegerModel/Arrays/SameModel.lean",
    "VerifiableInference/Checks.lean",
    "VerifiableInference/ProbabilityGuards.lean",
    "VerifiableInference/ModelGuards.lean",
    "VerifiableInference/ModelGuardsAtReference.lean",
]

# These two entries open the page.
MAIN_THEOREMS = ["VerifierAndGoals.AtTheName.sound_of_verify_at", "PV.Ride.sound_of_the_form_at"]

# The last part shows the theorems named in the first column of the first table of ONBYTES_PAGE.
ONBYTES_FOLDER, ONBYTES_PAGE = "OnBytes", "OnBytes/THEOREMS.md"

# In the part on other folders, a longer source than this is not printed.
MAX_LINES, MAX_CHARACTERS = 60, 6000

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

# By the last words of its title main() knows a long page of its own making, whatever stands before these words. No
# other page's title may end so.
TITLE_ENDS = "Lean statements"
TITLE = "FlashProve: " + TITLE_ENDS
T_MAIN, T_CONTENTS = "The main theorem", "Contents"
T_LINKED = "Linked declarations"
T_NAMED = ["Linked from the two statements above", "Linked from the Lean texts of those"]
T_HOW = "How to read the entries"
T_PANEL, T_BACK, T_GO, T_CLOSE = "Entry", "back", "go to the entry", "close"
T_OTHER = "Declared in the library's other folders"
T_ONBYTES = "OnBytes/: the theorems that OnBytes/THEOREMS.md lists"
T_FILTER, T_NO_MATCH, T_SKIP = "Filter", "no match", "Skip to the statements"
T_NO_DOCSTRING, T_NOT_PRINTED = "no docstring", "not printed"
LICENCE = "Copyright 2026 Anthropic PBC\nSPDX-License-Identifier: Apache-2.0"  # the Lean files' two lines
FRONT_LICENCE = LICENCE  # at the head of the page that is made from the shell (section 7)
BACKTICK = chr(96)

NOTES = []  # remarks for the log
LEFT_OUT = set()  # (file, line of a declaration, line of a 'variable' line that is not shown with it)


class Stop(Exception):
    """The program cannot go on. The message says where and why."""


def stop(path, line, why):
    raise Stop("%s:%d: %s" % (path, line, why))


def plainly(s, keep="\n"):
    """For messages: a character that cannot be seen (a control character, a change of direction, a line end that is not
    in 'keep') is written as its escape, so that words quoted from a file cannot steer the reader's terminal."""
    return "".join(c if c.isprintable() or c in keep else c.encode("unicode_escape").decode("ascii") for c in s)


# ------------------------------------------------------------------------------------------------
# 1. Comments and strings
# ------------------------------------------------------------------------------------------------

_SPECIAL = re.compile(r'/-|--|"|\'|«')
_COMMENT_EDGE = re.compile(r"/-|-/")

# The characters of a Lean name. The Greek letters λ, Π and Σ are signs, not letters.
_START = "A-Za-z_\u0370-\u039f\u03a1\u03a2\u03a4-\u03ba\u03bc-\u03ff\u1f00-\u1ffe\u2100-\u214f\U0001d49c-\U0001d59f"
_REST = _START + "0-9'!?\u2080-\u2089\u2090-\u209c\u1d62-\u1d6a\u2c7c"
_PART = "(?:[%s][%s]*|«[^»\n]*»)" % (_START, _REST)
NAME = re.compile("%s(?:\\.%s)*" % (_PART, _PART))
_REST_CHAR = re.compile("[%s]" % _REST)
OPENERS, CLOSERS = "([{⟨⦃⟦⌈⌊", ")]}⟩⦄⟧⌉⌋"


def in_name(c):
    return _REST_CHAR.match(c) is not None


# Words at which Lean begins a command, wherever it meets them. scan() stops where one stands behind the first word of a
# first-column command; second_command() has the few places where such a word begins none. Not listed, because honest
# files have them as plain names or inside commands: seal, unseal, deriving, and '#' words other than '#exit'.
COMMAND_WORDS = (
    "theorem lemma def abbrev structure class inductive instance opaque axiom example "
    "variable include omit universe notation infix infixl infixr prefix postfix macro syntax macro_rules elab "
    "declare_syntax_cat namespace section end mutual open export import attribute set_option initialize "
    "builtin_initialize elab_rules run_cmd run_elab run_meta alias add_decl_doc suppress_compilation assert_not_exists "
    "library_note compile_inductive irreducible_def notation3 variable? binder_predicate unif_hint proof_wanted "
    "simproc dsimproc simproc_decl #exit"
).split()
COMMAND_WORD = re.compile(
    r"(?<![%s.«%s])(?:%s)(?![%s.»])"
    % (_REST, BACKTICK, "|".join(re.escape(w) for w in sorted(COMMAND_WORDS, key=len, reverse=True)), _REST)
)
_NAMES_AND_SIGNS = r"(?:\s+(?:%s|[(),→>-]))+?" % NAME.pattern
OPEN_IN = re.compile(r"open%s\s+in\s+\S" % _NAMES_AND_SIGNS)  # 'open A B in' before a term or a tactic: it ends with it
SET_OPTION_IN = re.compile(r"set_option\s+\S+\s+(?:\S+\s+)?in\s+\S")  # a value that is a string is blanked here
NEVER = re.compile(r"(?!)")
SYNTAX_WORD = re.compile(
    r"(?m)^(?:@\[[^\]\n]*\][ \t]*|(?:local|scoped(?:\[[^\]\n]*\])?)[ \t]+)*"
    r"(notation3?|infix[lr]?|prefix|postfix|macro|macro_rules|syntax|elab|elab_rules|declare_syntax_cat)(?![%s.])"
    % _REST
)


class Source:
    """One Lean file. 'spans' lists its comments and literals. 'code' is the text with all of these
    replaced by blanks, for reading the structure. 'solid' has only the comments replaced, for
    finding where a text ends: a string at the end of a definition is part of it."""

    def __init__(self, root, path):
        self.path = path
        data = small_bytes(os.path.join(root, path), MOST_LEAN, path)
        if data is None:
            stop(path, 1, "the file was there when the folder was listed and is gone now")
        try:
            self.text = unnumbered(path, data.decode("utf-8"))
        except UnicodeDecodeError:
            stop(path, 1, "the file is not UTF-8")
        if "\r" in self.text:
            stop(path, 1, "the file has carriage returns")
        self.line_starts = [0] + [m.end() for m in re.finditer("\n", self.text)]
        self.spans = []  # (start, end, kind); kind: line, block, doc, moddoc, string, char
        self._find_spans()
        self._span_starts = [s for s, _, _ in self.spans]
        code, solid, i = [], [], 0
        for s, e, kind in self.spans:
            blank = re.sub(r"[^\n]", " ", self.text[s:e])
            code += [self.text[i:s], blank]
            solid += [self.text[i:s], self.text[s:e] if kind in ("string", "char") else blank]
            i = e
        self.code = "".join(code) + self.text[i:]
        self.solid = "".join(solid) + self.text[i:]

    def line_of(self, pos):
        return bisect.bisect_right(self.line_starts, pos)

    def column_of(self, pos):
        return pos - self.line_starts[self.line_of(pos) - 1]

    def spans_between(self, a, b):
        i = bisect.bisect_left(self._span_starts, a)
        while i < len(self.spans) and self.spans[i][0] < b:
            yield self.spans[i]
            i += 1

    def _find_spans(self):
        t, n, i = self.text, len(self.text), 0
        while True:
            m = _SPECIAL.search(t, i)
            if not m:
                return
            s, sign = m.start(), m.group()
            if sign == "--":
                e = t.find("\n", s)
                e = n if e < 0 else e
                self.spans.append((s, e, "line"))
            elif sign == "/-":
                if t.startswith("/--/", s) or t.startswith("/-/", s):
                    stop(self.path, self.line_of(s), "this scanner does not read a comment that opens like this")
                kind = "doc" if t.startswith("/--", s) else "moddoc" if t.startswith("/-!", s) else "block"
                depth, e = 1, s + 2
                while depth:
                    edge = _COMMENT_EDGE.search(t, e)
                    if not edge:
                        stop(self.path, self.line_of(s), "the comment is not closed")
                    depth += 1 if edge.group() == "/-" else -1
                    e = edge.end()
                self.spans.append((s, e, kind))
            elif sign == '"':
                e = self._string_end(s)
                self.spans.append((s, e, "string"))
            elif sign == "'":
                if s > 0 and in_name(t[s - 1]):
                    e = s + 1  # a prime at the end of a name
                elif t.startswith("\\", s + 1):
                    e = t.find("'", s + 3) + 1
                    if e <= 0 or e - s > 11:
                        stop(self.path, self.line_of(s), "the character literal is not closed")
                    self.spans.append((s, e, "char"))
                elif s + 2 < n and t[s + 2] == "'":
                    e = s + 3
                    self.spans.append((s, e, "char"))
                else:
                    e = s + 1
            else:  # «
                e = t.find("»", s) + 1
                if e <= 0:
                    stop(self.path, self.line_of(s), "« is not closed")
            i = e

    def _string_end(self, s):
        """The position after the string whose opening quote is at s: plain, raw or interpolated."""
        t, hashes = self.text, 0
        while s - 1 - hashes >= 0 and t[s - 1 - hashes] == "#":
            hashes += 1
        r = s - 1 - hashes
        if r >= 0 and t[r] == "r" and not (r > 0 and in_name(t[r - 1])):  # r"..." or r#"..."#
            e = t.find('"' + "#" * hashes, s + 1)
            if e < 0:
                stop(self.path, self.line_of(s), "the raw string is not closed")
            return e + 1 + hashes
        if s >= 2 and t[s - 1] == "!" and in_name(t[s - 2]):
            if t[s - 2] in "smf" and not (
                s > 2 and (in_name(t[s - 3]) or t[s - 3] == ".")
            ):  # s!"...", m!"...", f!"..."
                return self._closing_quote(s, True)
            stop(
                self.path,
                self.line_of(s),
                "a string right behind '...!' other than s!, m! or f!: is it interpolated? Put a blank between the two",
            )
        return self._either_way(s)

    def _either_way(self, s):
        """The end of a string with no mark before it. A macro before it (throwError, say) may still make Lean read what
        stands between { and } as code, and this scanner cannot know. It reads the string both ways. Of two different
        ends it takes the later, so that nothing is taken for code that Lean may read as a string; and it stops if a
        command could begin between the two, for then one reading has a command that the other has not."""
        as_it_stands = self._closing_quote(s, False)
        if "{" not in self.text[s:as_it_stands]:
            return as_it_stands
        try:
            with_code = self._closing_quote(s, True)
        except Stop:
            with_code = None
        if with_code is None or COMMAND_WORD.search(self.text, as_it_stands, with_code):
            stop(
                self.path,
                self.line_of(s),
                "a string with a '{' in it ends at one place if Lean reads it as it stands and at another, or nowhere, "
                "if Lean reads { } in it as code, and a command may lie between: write the brace as \\x7b",
            )
        return with_code

    def _closing_quote(self, s, braces_hold_code):
        """The position after the quote that closes the string (no raw string) whose opening quote is at s."""
        t, n, j = self.text, len(self.text), s + 1
        while j < n:
            c = t[j]
            if c == "\\":
                j += 2
            elif c == '"':
                return j + 1
            elif c == "{" and braces_hold_code:  # code inside the string, perhaps with strings of its own
                depth = 0
                while j < n:
                    behind_a_name = in_name(t[j - 1]) or t[j - 1] == "#"
                    if t[j] == '"' and not behind_a_name:
                        j = self._either_way(j)
                        continue
                    if t.startswith(("--", "/-"), j) or t[j] in '«"' or (t[j] == "'" and not behind_a_name):
                        # Lean would skip a brace or a quote in there, and this scanner would count it
                        stop(
                            self.path,
                            self.line_of(j),
                            "between the braces of a string: a comment, a character, a name in « », or a string with a "
                            "mark before it",
                        )
                    depth += (t[j] == "{") - (t[j] == "}")
                    j += 1
                    if depth == 0:
                        break
            else:
                j += 1
        stop(self.path, self.line_of(s), "the string is not closed")


# ------------------------------------------------------------------------------------------------
# 2. Commands and declarations
# ------------------------------------------------------------------------------------------------

DECLARATIONS = {
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
}
CUT_BEFORE_PROOF = {"theorem", "lemma", "example"}
MODIFIERS = {"private", "protected", "noncomputable", "partial", "unsafe", "nonrec", "local", "scoped"}
# Commands whose lines stay in force for the declarations below them, up to the end of their section.
IN_FORCE = {
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
}
# Commands that change nothing that the page shows. So does every command that begins with '#'.
NO_EFFECT = {
    "import",
    "set_option",
    "attribute",
    "deriving",
    "initialize",
    "run_cmd",
    "assert_not_exists",
    "library_note",
    "add_decl_doc",
    "compile_inductive",
    "suppress_compilation",
    "unseal",
    "seal",
}
# Words in the first column that continue the declaration above them.
CONTINUES = {"termination_by", "decreasing_by", "where", "with"}
NOT_IN_A_STATEMENT = {"have", "show", "from", "by", "do", "match", "suffices", "letI", "haveI", "let_fun", "calc"}

_FIRST_COLUMN = re.compile(r"^(?=\S)", re.M)
_WORD = re.compile(r"[^\s(\[{:]+")
_INDENTED_DECLARATION = re.compile(
    r"^[ \t]+(?:@\[[^\n]*\]\s*)?(?:(?:%s)\s+)*(?:%s)(?![%s.])" % ("|".join(MODIFIERS), "|".join(DECLARATIONS), _REST),
    re.M,
)


class Declaration:
    """A declaration and where it is: 'start' is its first word (an attribute or modifier counts),
    'shown_end' the end of what the page prints, 'whole_end' its last character."""

    __slots__ = (
        "src",
        "kind",
        "written",
        "full",
        "private",
        "protected",
        "doc",
        "start",
        "name_end",
        "shown_end",
        "whole_end",
        "namespaces",
        "opens",
        "in_force",
        "ident",
        "members",
        "part",
        "result",
    )


def skip_blanks(code, i):
    n = len(code)
    while i < n and code[i].isspace():
        i += 1
    return i


def bracket_end(src, i, limit):
    """code[i] opens a bracket. Return the position after the bracket that closes it."""
    code, stack, j = src.code, [], i
    while j < limit:
        c = code[j]
        k = OPENERS.find(c)
        if k >= 0:
            stack.append(k)
        else:
            k = CLOSERS.find(c)
            if k >= 0:
                if not stack or stack[-1] != k:
                    stop(src.path, src.line_of(j), "the bracket %s closes nothing" % c)
                stack.pop()
                if not stack:
                    return j + 1
        j += 1
    stop(src.path, src.line_of(i), "the bracket %s is not closed inside its command" % code[i])


def word_at(code, i):
    m = _WORD.match(code, i)
    return m.group() if m else ""


def has_body(code, a, b):
    """Does code[a:b] hold a ':=' outside brackets?"""
    depth = 0
    for m in re.finditer("[%s%s]|:=" % (re.escape(OPENERS), re.escape(CLOSERS)), code[a:b]):
        if m.group() == ":=":
            if depth == 0:
                return True
        else:
            depth += 1 if m.group() in OPENERS else -1
    return False


def second_command(code, first_word, a, end):
    """The first word between a and end, behind a command's first word, at which Lean would begin another command."""
    for m in COMMAND_WORD.finditer(code, a, end):
        w, before = m.group(), code[max(a - 40, 0) : m.start()]
        if before.rstrip().endswith(BACKTICK + "("):  # quoted syntax, as in a macro's body
            continue
        if w == "instance" and re.search(r"[\[,]\s*(?:(?:local|scoped|-)\s*)*$", before):  # attribute [local instance]
            continue
        if not code[a : m.start()].strip() and (first_word, w) in SECOND_WORDS:
            continue
        ends_with_it = (OPEN_IN if w == "open" else SET_OPTION_IN if w == "set_option" else NEVER).match(
            code, m.start(), end
        )
        if ends_with_it and not any(
            x in COMMAND_WORDS + ["seal", "unseal"] for x in NAME.findall(code, m.end(), ends_with_it.end() - 1)
        ):
            continue
        return m
    return None


SECOND_WORDS = (("class", "inductive"), ("class", "abbrev"), ("deriving", "instance"))


def scan(src, shown=True):
    """The declarations of one file. Each one records the namespaces, the 'open' lines and the lines
    in force at its place. With shown=False (a file outside the chosen folders) only names and
    places are needed, so the scanner is lenient where Lean is, and cuts nothing yet."""
    code, path, n = src.code, src.path, len(src.code)
    starts = [m.start() for m in _FIRST_COLUMN.finditer(code)] + [n]
    docstring_before = {skip_blanks(src.text, e): (s, e) for s, e, k in src.spans if k == "doc"}
    used_docstrings, out = set(), []
    scopes, namespaces, opens, in_force = [], [], [], []  # a scope: (word, name, parts, len(opens), len(in_force))
    next_opens, next_lines = [], []  # from '... in' lines: for the next declaration only
    src.unknown = []  # (position, line, word) of the commands that were passed over: see cut()
    k = 0
    while k < len(starts) - 1:
        pos = starts[k]
        line = src.line_of(pos)
        i, modifiers = pos, []
        while True:  # attributes and modifiers, which may be on lines of their own
            i = skip_blanks(code, i)
            if code.startswith("@[", i):
                i = bracket_end(src, i + 1, n)
            elif code.startswith("scoped[", i):
                i = bracket_end(src, i + 6, n)
            elif word_at(code, i) in MODIFIERS:
                modifiers.append(word_at(code, i))
                i += len(modifiers[-1])
            else:
                break
        word, word_pos = word_at(code, i), i
        if shown and any(kind == "doc" for _, _, kind in src.spans_between(pos, word_pos)):
            stop(path, line, "a docstring after an attribute or modifier; put it first")
        k += 1
        while starts[k] < n and (
            starts[k] <= word_pos
            or word_at(code, starts[k]) in CONTINUES
            or code[starts[k]] in "|)]}⟩"
            or (code[starts[k]] in "([{⟨⦃" and not has_body(code, pos, starts[k]))  # a binder that is not indented
            or sum(code.count(x, pos, starts[k]) for x in OPENERS) > sum(code.count(x, pos, starts[k]) for x in CLOSERS)
            or re.match(r"deriving\s+(?!instance\b)", code[starts[k] : starts[k] + 40])
        ):
            k += 1
        end = starts[k]
        while end > pos and src.solid[end - 1].isspace():
            end -= 1
        body = code[word_pos:end]
        if any(code.count(a, pos, end) != code.count(b, pos, end) for a, b in zip(OPENERS, CLOSERS)):
            stop(path, line, "the brackets of the command that begins here do not balance")
        second = second_command(code, word, word_pos + len(word), end)
        if second:
            stop(
                path,
                src.line_of(second.start()),
                "'%s' stands inside the command that begins in line %d. Lean would begin a new command at that word, "
                "and this scanner, which looks for commands in the first column alone, would take it for a part of it"
                % (second.group(), line),
            )
        if word in DECLARATIONS:
            d = Declaration()
            d.src, d.kind, d.start, d.whole_end, d.shown_end = src, word, pos, end, None
            d.private, d.protected = "private" in modifiers, "protected" in modifiers
            d.doc = docstring_before.get(pos)
            used_docstrings.add(d.doc)
            d.namespaces, d.opens = list(namespaces), opens + next_opens
            d.in_force = in_force + next_lines
            d.members, d.part, d.full, d.ident, d.result = [], None, None, None, False
            read_name(d, word_pos + len(word))
            if shown:
                cut(d)
            out.append(d)
            next_opens, next_lines = [], []
            continue
        if pos in docstring_before:
            # Lean takes a docstring before 'notation' and 'local notation': it is that notation's comment. The page
            # shows the notation among the lines in force, from the command's first word, without the comment.
            if shown and not (word == "notation" and code[pos:word_pos].split() in ([], ["local"])):
                stop(path, line, "a docstring before '%s', which is not a declaration" % word)
            used_docstrings.add(docstring_before[pos])
        words = body.split()
        for k_in, w in enumerate(words[:-1]):
            nxt = words[k_in + 1]
            if shown and w == "in" and (nxt in MODIFIERS or nxt in DECLARATIONS or nxt.startswith("@[")):
                stop(path, line, "a declaration on the same line as '%s ... in'; put it on a line of its own" % word)
        if words and words[-1] == "in" and word not in ("namespace", "section", "end", "mutual"):
            next_lines.append((pos, end))  # it belongs to the next declaration and is shown with it
            if word == "open":
                try:
                    next_opens += read_open(src, line, words[1:-1], namespaces)
                except Stop:
                    if shown:
                        raise
                    src.unknown.append((pos, line, "open"))
            continue
        next_opens, next_lines = [], []
        if word == "namespace":
            parts = words[1].split(".")
            scopes.append((word, words[1], len(parts), len(opens), len(in_force)))
            namespaces.extend(parts)
        elif word in ("section", "mutual"):
            name = words[1] if word == "section" and len(words) > 1 else ""
            scopes.append((word, name, 0, len(opens), len(in_force)))
        elif word == "end":
            rest = words[1] if len(words) > 1 else ""
            while True:  # 'end A.B' may close 'namespace A' and 'namespace B'
                if not scopes:
                    stop(path, line, "'end' closes nothing")
                opened_by, name, parts, n_opens, n_lines = scopes.pop()
                del namespaces[len(namespaces) - parts :]
                del opens[n_opens:]
                del in_force[n_lines:]
                if rest == name:
                    break
                if opened_by == "namespace" and rest and name.endswith("." + rest):
                    # 'namespace A.B.C' opens three scopes, and 'end C' closes the innermost alone: A.B stays open
                    kept = name[: -len(rest) - 1]
                    scopes.append((opened_by, kept, len(kept.split(".")), n_opens, n_lines))
                    namespaces.extend(kept.split("."))
                    break
                if not name or not rest.endswith("." + name):
                    stop(path, line, "'end %s' closes '%s %s'" % (rest, opened_by, name))
                rest = rest[: -len(name) - 1]
        elif word == "open":
            try:
                opens += read_open(src, line, words[1:], namespaces)
            except Stop:
                if shown:
                    raise
                src.unknown.append((pos, line, "open"))
        elif word in IN_FORCE:
            in_force.append((pos, end))
        elif word == "export":
            if shown:
                stop(path, line, "this scanner does not read 'export'")
        elif word == "#exit":  # in any file: what is below it is not declared, and this scanner would index it
            stop(path, line, "'#exit': Lean reads nothing below it, and this scanner would")
        elif not (word in NO_EFFECT or word.startswith("#")):
            if shown:
                stop(path, line, "unknown command '%s'" % (word or code[pos : pos + 20].split("\n")[0]))
            src.unknown.append((pos, line, word or code[pos : pos + 20].split("\n")[0]))
    if shown:
        if scopes:  # Lean closes them itself at the end of the file
            NOTES.append("%s: '%s %s' is not closed at the end of the file" % ((path,) + scopes[-1][:2]))
        m = _INDENTED_DECLARATION.search(code)
        if m:
            stop(
                path, src.line_of(m.end()), "an indented declaration; this scanner reads them only in the first column"
            )
        for s, e, kind in src.spans:
            if kind == "moddoc" and src.column_of(s) and not any(d.start <= s < d.whole_end for d in out):
                stop(
                    path,
                    src.line_of(s),
                    "an indented '/-! ... -/' comment; the page shows them only from the first column",
                )
            if (
                kind == "doc"
                and (s, e) not in used_docstrings
                and not any(d.start <= s and e <= d.whole_end for d in out)
            ):
                stop(path, src.line_of(s), "a docstring that belongs to no declaration")
    return out


def read_open(src, line, words, namespaces):
    """'open A B', 'open A (x y)', 'open A hiding x', 'open scoped A', 'open A renaming x → y'. Returns (how, the
    namespaces at this place, the name, the listed names)."""
    here = list(namespaces)
    if words and words[0] == "scoped":
        return []
    if "renaming" in words:  # it opens nothing but the new names, and these the scanner does not follow: no link
        return []
    text = " ".join(words)
    m = re.match(r"^(\S+)\s*\(([^)]*)\)$", text)
    if m:
        return [("only", here, m.group(1), tuple(m.group(2).split()))]
    m = re.match(r"^(\S+)\s+hiding\s+(.*)$", text)
    if m:
        return [("hiding", here, m.group(1), tuple(m.group(2).split()))]
    for w in words:
        if not NAME.fullmatch(w):
            stop(src.path, line, "this scanner cannot read this 'open' line")
    return [("all", here, w, ()) for w in words]


def read_name(d, i):
    """Set d.written (the name as written, or None) and d.name_end."""
    src, code = d.src, d.src.code
    i = skip_blanks(code, i)
    if d.kind == "class" and word_at(code, i) in ("inductive", "abbrev"):  # 'class inductive Foo'
        i = skip_blanks(code, i + len(word_at(code, i)))
    d.written, d.name_end = None, i
    if d.kind == "example":
        return
    if d.kind == "instance" and code.startswith("(priority", i):
        i = skip_blanks(code, bracket_end(src, i, d.whole_end))
        d.name_end = i
    m = NAME.match(code, i)
    if m and m.end() <= d.whole_end:
        d.written, d.name_end = m.group(), m.end()
    elif d.kind != "instance":
        stop(src.path, src.line_of(i), "no name after '%s'" % d.kind)


def cut(d):
    """Set d.shown_end. A theorem, lemma or example ends before the sign that opens its proof: ':=',
    'where', or the first '| ... =>' line. Everything else is shown to its end, with a line comment
    that follows on the last line."""
    src, code = d.src, d.src.code
    for pos, line, word in src.unknown:
        if pos < d.start:  # it may have declared a name or put a line in force, and this scanner would not know
            stop(
                src.path,
                line,
                "this scanner does not know the command '%s', and the text of %s, below it in this file, is wanted"
                % (word, d.full or "a declaration"),
            )
    if d.kind not in CUT_BEFORE_PROOF:
        end = d.whole_end
        line_end = src.text.find("\n", end)
        for s, e, kind in src.spans_between(end, line_end if line_end >= 0 else len(src.text)):
            if kind == "line" and src.text[end:s].strip(" ") == "":
                end = e
            break
        d.shown_end = end
        refuse_open_end(d, d.whole_end)
        return
    i, lets, at = d.name_end, 0, None
    while i < d.whole_end:
        c = code[i]
        if c in OPENERS:
            i = bracket_end(src, i, d.whole_end)
            continue
        if c in CLOSERS:
            stop(src.path, src.line_of(i), "the bracket %s closes nothing" % c)
        if code.startswith(":=", i):
            if not lets:
                at = i
                break
            lets -= 1  # this ':=' belongs to a 'let' inside the statement
            i += 2
            continue
        if c == "|" and code[i + 1 : i + 2] != "|" and code[i - 1 : i] != "|":
            first_on_line = code[src.line_starts[src.line_of(i) - 1] : i].strip() == ""
            if re.search("(?<![%s.])(?:fun|λ|with)$" % _REST, code[d.name_end : i].rstrip()):
                stop(src.path, src.line_of(i), "a bar after 'fun', 'λ' or 'with' in a statement: it opens no proof")
            # the first arm of a proof: from the bar on, outside brackets, '=>' comes before any ':=', and before
            # that '=>' there is no 'fun' or 'λ' (a pattern cannot hold one) and no other bar (the two might be an
            # absolute value above a proof in arms)
            flat = outside_brackets(code[i : d.whole_end], keep_length=True)
            sign = re.search(":=|=>|λ|(?<![%s.])fun(?![%s])" % (_REST, _REST), flat)
            if (
                first_on_line
                and sign
                and sign.group() == "=>"
                and not re.search(r"(?<!\|)\|(?!\|)", flat[1 : sign.start()])
            ):
                at = i
                break
            if sign and sign.group() != "=>":  # it cannot open a proof: an absolute value, say; the statement goes on
                i += 1
                continue
            stop(
                src.path,
                src.line_of(i),
                "a bar outside brackets in a statement, and this scanner cannot tell whether it opens the proof",
            )
        m = NAME.match(code, i)
        if m:
            if m.group() == "where":  # the proof gives the fields of a structure
                at = i
                break
            if m.group() == "let":
                lets += 1
                NOTES.append(
                    "%s:%d: the ':=' of this 'let' was not taken for the start of the proof"
                    % (src.path, src.line_of(i))
                )
            elif m.group() in NOT_IN_A_STATEMENT:
                stop(src.path, src.line_of(i), "'%s' outside brackets in a statement" % m.group())
            i = m.end()
            continue
        i += 1
    if at is None:
        stop(
            src.path,
            src.line_of(d.start),
            "no ':=', 'where' or '|' ends this statement; does one of its lines begin in the first column?",
        )
    while at > d.start and src.solid[at - 1].isspace():
        at -= 1
    d.shown_end = at
    refuse_open_end(d, at)


def refuse_open_end(d, end):
    """Stop if the text ends in a sign that wants something after it: then the rest was taken for another command."""
    m = re.search(r"(?::=|=>|[=≠<>≤≥+\-*/∧∨→↔,:;&^∘×⊆∈∉·←↦¬])$", d.src.solid[d.start : end])
    if m:
        stop(
            d.src.path,
            d.src.line_of(end - 1),
            "the text ends in '%s'; does its next line begin in the first column?" % m.group(),
        )


# ------------------------------------------------------------------------------------------------
# 3. Names: what is declared, what a text binds, what a name in a text refers to
# ------------------------------------------------------------------------------------------------

_NAMES = "(?:%s\\s+)*%s" % (_PART, _PART)  # '_' is a name by _PART; a second arm for it made the search double per '_'
_BINDER_IN_BRACKETS = re.compile("[(\\[{⦃]\\s*(%s)\\s*:" % _NAMES)
_BINDER_WORD = re.compile(
    "(?<![%s.])(?:∀|∃!|∃|λ|Σ|Π|∑|∏|⨆|⨅|⋃|⋂|(?:fun|let|have|obtain|suffices)(?![%s]))" % (_REST, _REST)
)
_TACTIC = re.compile(  # where a tactic can begin: at the start of a line, or after 'by', ';', '·', '<;>'
    "(?:^|(?<![%s.])by|;|·|<;>)[ \\t]*(?:intro|intros|rintro|rcases|cases|induction|ext|funext|set|generalize|"
    "rename_i|next|case|choose)(?![%s])([^\\n]*)" % (_REST, _REST),
    re.M,
)
_GIVEN_A_VALUE = re.compile("(?<![%s.])(%s)\\s*:=" % (_REST, _PART))
_FOR = re.compile("(?<![%s.])for\\s+([^\\n]*?)\\s+in(?![%s])" % (_REST, _REST))
_NAMED_TEST = re.compile("(?<![%s.])(?:if|match)\\s+(%s)\\s*:" % (_REST, _PART))
_ARM = re.compile(r"\|([^|\n]*?)=>")
_SET_BUILDER = re.compile(r"\{([^{}|\n]*?)\|")
_ONE_PART = re.compile("(?<![%s.»])%s(?![%s.«])" % (_REST, _PART, _REST))
_APPLICATION = re.compile("^[%s\\s.«»]*$" % _REST)
_WHERE = re.compile("(?<![%s])where(?![%s])" % (_REST, _REST))


def one_part_names(s):
    return set(_ONE_PART.findall(s))


def outside_brackets(s, keep_length=False):
    """The text without the brackets and what is inside them; with keep_length, blanks take their place."""
    out, depth = [], 0
    for c in s:
        if c in OPENERS:
            depth += 1
            inside = True
        elif c in CLOSERS:
            depth -= 1
            inside = True
        else:
            inside = depth > 0
        if not inside or c == "\n":
            out.append(c)
        elif keep_length:
            out.append(" ")
    return "".join(out)


def closing(code, i):
    """The position after the bracket that closes the one at i, or -1."""
    depth = 0
    for j in range(i, len(code)):
        if code[j] in OPENERS:
            depth += 1
        elif code[j] in CLOSERS:
            depth -= 1
            if depth == 0:
                return j + 1
    return -1


def plain_type(s):
    """The first name of a type that is a plain application 'T a b'; otherwise None."""
    flat = outside_brackets(s).strip()
    if not flat or not _APPLICATION.match(flat):
        return None
    m = NAME.match(flat)
    return m.group() if m else None


def field_lines(code, after):
    """After a 'where': the lines at the indentation of the first line. Each begins with a field's
    name, perhaps followed by the names of its arguments."""
    lines = code[after:].split("\n")[1:] if code[after:].split("\n")[0].strip() == "" else code[after:].split("\n")
    filled = [l for l in lines if l.strip() and not l.strip().startswith("deriving")]
    if not filled:
        return
    indent = len(filled[0]) - len(filled[0].lstrip())
    for l in filled:
        if len(l) - len(l.lstrip()) == indent and not re.match("\\s*%s\\s*::" % _PART, l):  # not 'mk ::'
            m = re.match("\\s*(?:private\\s+|protected\\s+)?(%s)\\s*(?::|\\(|\\{|\\[|$)" % _NAMES, l)
            if m:
                yield m.group(1).split()
            else:
                m = _BINDER_IN_BRACKETS.match(l.strip())
                if m:
                    yield m.group(1).split()


def bound_names(code, after_where):
    """Returns (the names that this text binds somewhere, name -> first name of its type). The second
    holds a name only if every place that binds it writes the same plain type."""
    bound, typed, untyped = set(), {}, set()

    def bind(names, type_name):
        for x in names:
            bound.add(x)
            if type_name is None:
                untyped.add(x)
            else:
                typed.setdefault(x, set()).add(type_name)

    for m in _BINDER_IN_BRACKETS.finditer(code):
        e = closing(code, m.start())
        has_value = code.startswith(":=", m.end() - 1)
        bind(m.group(1).split(), None if e < 0 or has_value else plain_type(code[m.end() : e - 1].split(":=")[0]))
    for m in _BINDER_WORD.finditer(code):
        j, run = m.end(), []
        while True:
            j = skip_blanks(code, j)
            a = re.compile(_PART + "|_").match(code, j)
            if a and not code.startswith(".", a.end()):
                run.append(a.group())
                j = a.end()
            elif j < len(code) and code[j] in "([{⦃⟨":
                e = closing(code, j)
                if e < 0:
                    break
                if ":" not in outside_brackets(code[j + 1 : e - 1]):  # a pattern; a typed binder was read above
                    bind(one_part_names(code[j + 1 : e - 1]), None)
                j = e
            else:
                break
        if code.startswith(":", j) and not code.startswith(":=", j):
            depth, e = 0, j + 1
            while e < len(code):
                c = code[e]
                if c in OPENERS:
                    depth += 1
                elif c in CLOSERS:
                    if depth == 0:
                        break
                    depth -= 1
                elif depth == 0 and (c == "," or code.startswith(":=", e) or code.startswith("=>", e)):
                    break
                e += 1
            bind(run, plain_type(code[j + 1 : e]))
        else:
            bind(run, None)
    flat = outside_brackets(code, keep_length=True)
    for m in _GIVEN_A_VALUE.finditer(code):
        if flat[m.start()] == " ":  # inside brackets: a field in '{ x := ... }' or a named argument
            bind([m.group(1)], None)
    for pattern in (_TACTIC, _FOR, _ARM):
        for m in pattern.finditer(code):
            bind(one_part_names(m.group(1)), None)
    for m in _NAMED_TEST.finditer(code):
        bind([m.group(1)], None)
    for m in _SET_BUILDER.finditer(code):
        bind(one_part_names(re.split("[:∈]", m.group(1))[0]), None)
    if after_where is not None:
        for names in field_lines(code, after_where):
            bind(names, None)
    bound.discard("_")
    return bound, {x: next(iter(t)) for x, t in typed.items() if len(t) == 1 and x not in untyped}


def parts_of(name):
    return re.findall(_PART, name)


def read_members(d):
    """The fields of a structure or class, the constructors of an inductive type."""
    body = d.src.code[d.name_end : d.whole_end]
    if d.kind == "inductive" or (
        d.kind == "class" and not _WHERE.search(outside_brackets(body, True)) and "|" in outside_brackets(body)
    ):
        return re.findall("\\|\\s*(%s)" % _PART, outside_brackets(body, keep_length=True))
    w = re.search(_WHERE.pattern + "|:=", outside_brackets(body, keep_length=True))
    return [x for group in (field_lines(body, w.end()) if w else ()) for x in group if x != "_"] + ["mk"]


class Index:
    """Every declaration of every Lean file, by full name."""

    def __init__(self):
        self.public = {}  # full name -> [Declaration]
        self.private = {}  # (path, full name) -> Declaration
        self.member_of = {}  # full name of a field or constructor -> [Declaration of its type]
        self.by_last = {}  # last part -> {(full name as a tuple, id of the Declaration): Declaration}
        self.namespaces = set()
        self.imports = {}  # path -> the paths that it imports
        self.lines = {}  # path -> how many lines the file has
        self._visible = {}

    def visible_from(self, path):
        """The file itself and everything that it imports, directly or through other files."""
        seen = self._visible.get(path)
        if seen is None:
            seen, todo = {path}, [path]
            while todo:
                for q in self.imports.get(todo.pop(), ()):
                    if q not in seen:
                        seen.add(q)
                        todo.append(q)
            self._visible[path] = seen
        return seen

    def add(self, d):
        if d.written is None:
            return
        parts = parts_of(d.written)
        full = parts[1:] if parts[0] == "_root_" else d.namespaces + parts
        d.full = ".".join(full)
        is_type = d.kind in ("structure", "class", "inductive")
        for k in range(1, len(full) + is_type):
            self.namespaces.add(".".join(full[:k]))
        for k in range(1, len(d.namespaces) + 1):
            self.namespaces.add(".".join(d.namespaces[:k]))
        if d.private:
            self.private[(d.src.path, d.full)] = d
        else:
            self.public.setdefault(d.full, []).append(d)
        self.by_last.setdefault(full[-1], {})[(tuple(full), id(d))] = d
        if is_type:
            d.members = read_members(d)
            for x in d.members:
                self.member_of.setdefault(d.full + "." + x, []).append(d)
                self.by_last.setdefault(x, {})[(tuple(full) + (x,), id(d))] = d

    def fits(self, full, path, everywhere=False):
        """All the declarations with this full name that the file at 'path' can see."""
        if (path, full) in self.private:
            return [self.private[(path, full)]]
        visible = self.visible_from(path)
        for table in (self.public, self.member_of):
            fit = [d for d in table.get(full, ()) if everywhere or d.src.path in visible]
            if fit:
                return fit
        return []

    def get(self, full, path, everywhere=False):
        """The declaration with this full name that the file at 'path' can see, None if there is none,
        "several" if there are more. With everywhere=True all files count as visible."""
        d = self.private.get((path, full))
        if d:
            return d
        visible = self.visible_from(path)
        for table in (self.public, self.member_of):
            fit = [d for d in table.get(full, ()) if everywhere or d.src.path in visible]
            if len(fit) == 1:
                return fit[0]
            if fit:
                return "several"
        return None


class Tally:
    def __init__(self):
        self.several, self.how, self.links, self.after_bracket = {}, {}, 0, {}
        self.doubt = None  # part 7 sets a list here: it collects the declarations among which rule 2 could not tell

    def add(self, what):
        self.how[what] = self.how.get(what, 0) + 1


def opened_namespaces(index, d):
    """(how, full name of the namespace, listed names) for each 'open' line in force. Like Lean, look for
    the name under the enclosing namespaces and under the namespaces opened before it."""
    out = []
    for how, here, name, listed in d.opens:
        parts = parts_of(name)
        if parts[0] == "_root_":
            candidates = [".".join(parts[1:])]
        else:
            candidates = [".".join(here[:k] + parts) for k in range(len(here), -1, -1)]
            candidates += [o + "." + ".".join(parts) for _, o, _ in out]
        for c in candidates:
            if c in index.namespaces and (how, c, listed) not in out:
                out.append((how, c, listed))
    return out


def resolve(index, d, name, bound, types, tally, everywhere=False):
    """Rules 1, 2, 3 and 5. Returns None, or (the declaration, the index of the first part of 'name' that
    belongs to the link, the number of parts in the link, a word on how it was found)."""
    parts, path = parts_of(name), d.src.path
    if parts[0] in bound:
        type_name = types.get(parts[0])
        if type_name is None or len(parts) < 2:
            return None
        t = resolve(index, d, type_name, bound, {}, tally)
        if t and (t[2] != len(parts_of(type_name)) or t[0].full is None):
            return None
        if not t and (parts_of(type_name)[0] in bound or parts_of(type_name)[-1] in index.by_last):
            return None  # T is bound, or it may be one of ours that could not be told
        # if T is not ours (Array, say), 'T.f' may still be: a function of ours in the namespace of that type
        got = index.get((t[0].full if t else type_name) + "." + parts[1], path)
        return None if got in (None, "several") else (got, 1, 1, "after a bound name whose type is written")
    if parts[0] == "_root_":
        got = index.get(".".join(parts[1:]), path, everywhere)
        return None if got in (None, "several") else (got, 0, len(parts), "written with _root_")
    own = parts_of(d.written)[:-1] if d.written and not d.written.startswith("_root_") else []
    here, opened = d.namespaces + own, opened_namespaces(index, d)
    for length in range(len(parts), 0, -1):
        begin, one_part, found, names = parts[:length], length == 1, [], []

        def look(full):
            got = index.get(full, path, everywhere)
            if got is None or (got != "several" and one_part and got.protected and got.full == full):
                return False
            if got not in found:
                found.append(got)
            names.append(full)
            return True

        for k in range(len(here), 0, -1):
            look(".".join(here[:k] + begin))
        how = "under an enclosing namespace"
        if not found:
            how = "as written"
            look(".".join(begin))
            for mode, o, listed in opened:
                if mode == "only" and not (one_part and begin[0] in listed):
                    continue
                if mode == "hiding" and one_part and begin[0] in listed:
                    continue
                if look(".".join([o] + begin)):
                    how = "under an 'open' line"
        if len(found) == 1 and found[0] != "several":
            return found[0], 0, length, how
        if found:
            tally.several[name] = tally.several.get(name, 0) + 1
            if tally.doubt is not None:
                tally.doubt += [x for full in names for x in index.fits(full, path, everywhere)]
            return None
    return None


def full_name_of_link(found, name):
    """The full name, as a tuple, that a link stands for. For a field it ends in the field's name."""
    target, first, count = found[:3]
    shown = tuple(parts_of(name)[first : first + count])
    full = tuple(target.full.split("."))
    return full if full[-len(shown) :] == shown else full + (shown[-1],)


def written_result_type(d):
    """The first name of the result type that d's source writes, if it is a plain application; else None."""
    if d.result is False:
        code, i, colon = d.src.code, d.name_end, None
        while i < d.whole_end:
            c = code[i]
            if c in OPENERS:
                i = bracket_end(d.src, i, d.whole_end)
                continue
            word = NAME.match(code, i)
            if code.startswith(":=", i) or c == "|" or (word and word.group() == "where"):
                break
            if c == ":":
                colon = i
            i = word.end() if word else i + 1
        d.result = plain_type(code[colon + 1 : i]) if colon is not None else None
    return d.result


def first_name_in_bracket(s, close):
    """s[close] is ')'. The name right after the '(' that it closes, or None."""
    depth = 0
    for j in range(close, -1, -1):
        if s[j] in CLOSERS:
            depth += 1
        elif s[j] in OPENERS:
            depth -= 1
            if depth == 0:
                m = NAME.match(s, skip_blanks(s, j + 1))
                return m.group() if m and s[j] == "(" else None
    return None


def outside_dots(s):
    """The text with 'x.f' cut down to 'x', so that the first parts of dotted names are found as names."""
    return re.sub("\\.(?:%s)" % _PART, "", s)


def own_binders(d):
    """The names that the declaration binds in brackets between its name and the rest of its statement."""
    code, i, out = d.src.code, d.name_end, set()
    while True:
        i = skip_blanks(code, i)
        if i >= d.shown_end or code[i] not in "([{⦃":
            return out
        e = bracket_end(d.src, i, d.shown_end)
        m = _BINDER_IN_BRACKETS.match(code, i)
        if m and m.end() <= e:
            out.update(m.group(1).split())
        i = e


def lines_shown_with(d):
    """The lines in force at d, except a 'variable' line from which Lean can take nothing: it has no instance
    binder, the declaration's own binders declare every one of its names again, no other line in force names
    one of them, and no own binder names one of them before it is declared again."""
    own, out = own_binders(d), []
    groups, i = [], d.name_end  # the own binders in order: (names, the text after the colon)
    while True:
        i = skip_blanks(d.src.code, i)
        if i >= d.shown_end or d.src.code[i] not in "([{⦃":
            break
        e = bracket_end(d.src, i, d.shown_end)
        m = _BINDER_IN_BRACKETS.match(d.src.code, i)
        groups.append(
            (set(m.group(1).split()), d.src.code[m.end() : e]) if m and m.end() <= e else (set(), d.src.code[i:e])
        )
        i = e
    for a, b in d.in_force:
        text = d.src.code[a:b]
        if text.startswith("variable") and not text.rstrip().endswith(" in"):
            names, droppable, i = set(), True, len("variable")
            while i < len(text):
                if text[i] in "([{⦃":
                    e = closing(text, i)
                    if e < 0:
                        stop(
                            d.src.path,
                            d.src.line_of(a + i),
                            "the bracket %s is not closed inside its command" % text[i],
                        )
                    m = _BINDER_IN_BRACKETS.match(text, i)
                    if text[i] == "[" or not m or m.end() > e:
                        droppable = False
                    else:
                        names.update(m.group(1).split())
                    i = e
                else:
                    i += 1
            for a2, b2 in d.in_force:
                if (a2, b2) != (a, b) and names & one_part_names(outside_dots(d.src.code[a2:b2])):
                    droppable = False
            again = set()
            for bound_here, type_text in groups:
                if (names - again) & one_part_names(outside_dots(type_text)):
                    droppable = False
                again |= bound_here
            if droppable and names and names <= own:
                LEFT_OUT.add((d.src.path, d.src.line_of(d.start), d.src.line_of(a)))
                continue
        out.append((a, b))
    return out


# ------------------------------------------------------------------------------------------------
# 4. From Lean text to HTML
# ------------------------------------------------------------------------------------------------


def esc(s):
    return html.escape(s, quote=True)


def cannot_be_seen(c):
    """Control and format characters (one of them turns the direction of writing), separators other than the plain
    blank, variation selectors, and letters that are drawn as a blank."""
    return c not in "\n\t" and (
        c < " "
        or (
            c > "~"
            and (
                unicodedata.category(c) in ("Cc", "Cf", "Zl", "Zp", "Zs")
                or "\ufe00" <= c <= "\ufe0f"
                or "\U000e0100" <= c <= "\U000e01ef"
                or c in "\u115f\u1160\u2800\u3164\uffa0"
            )
        )
    )


def refuse_unseen_characters(src, a, b):
    """Stop at a character that cannot be seen: with it the reader would not see what Lean reads."""
    for k, c in enumerate(src.text[a:b]):
        if cannot_be_seen(c):
            stop(
                src.path,
                src.line_of(a + k),
                "the character U+%04X cannot be seen; it must not be in a shown text" % ord(c),
            )


class Page:
    """Turns declarations and comments into HTML. It is used three times: to collect what each file's
    sources name and bind, to find which declarations of other folders are needed, and to write."""

    def __init__(self, index):
        self.index, self.tally = index, Tally()
        self.has_entry = None  # ids of the declarations with an entry; None until they are known
        self.wanted = {}  # id -> declaration: every target met while has_entry is None
        self.named = None  # collects (full name, declaration) for the links of one source
        self.beside = None  # while a docstring is written: what the source beside it names
        self.collecting = False  # entry() returns what it collected instead of HTML
        self.in_file_comment = self.in_folded_comment = False
        self.after_bracket_ok = None  # rule 4 in the last two parts: the last parts linked in the first two folders
        self.spots = self.spot = None  # part 7: collects (place, length, declaration) for the names in a Lean text
        self.whole = False  # part 7: no declaration is too long to be read

    # -- names ------------------------------------------------------------------------------------
    def find(self, d, name, bound, types, in_comment, after_bracket, first_in_bracket=None):
        """Apply the rules. Returns None or (declaration, first part, number of parts, how)."""
        if after_bracket:  # rule 4
            last = parts_of(name)[0]
            if d.part in ("other", "onbytes") and last not in self.after_bracket_ok:
                return None
            g = (
                first_in_bracket
                and parts_of(first_in_bracket)[0] not in bound
                and resolve(self.index, d, first_in_bracket, bound, {}, Tally())
            )
            if g and g[2] == len(parts_of(first_in_bracket)) and g[0].kind not in ("structure", "class", "inductive"):
                if g[0].shown_end is None:
                    cut(g[0])
                type_name = written_result_type(g[0])
                t = (
                    type_name
                    and parts_of(type_name)[0] not in own_binders(g[0])
                    and resolve(self.index, g[0], type_name, set(), {}, Tally())
                )
                if t and t[2] == len(parts_of(type_name)) and t[0].full:
                    got = self.index.get(t[0].full + "." + last, d.src.path)
                    if got not in (None, "several"):
                        return got, 0, 1, "after a bracket whose first name has a written result type"
            fit = self.index.by_last.get(last, {})
            if len(fit) != 1 or last in LIKELY_ELSEWHERE:
                return None
            return next(iter(fit.values())), 0, 1, "after a closing bracket, the only name in all files that ends so"
        if not in_comment:
            return resolve(self.index, d, name, bound, types, self.tally)
        if len(name) <= 2:  # rule 6
            return None
        one_part = "." not in name
        if self.in_folded_comment:
            parts = tuple(parts_of(name))
            fit = [d for (full, _), d in self.index.by_last.get(parts[-1], {}).items() if full[-len(parts) :] == parts]
            return (
                None
                if one_part or len(fit) != 1
                else (fit[0], 0, len(parts), "the only name in all files that ends so")
            )
        if self.in_file_comment and one_part and name in d.src.bound_in_file:
            return None
        found = resolve(self.index, d, name, bound, {}, self.tally) or resolve(
            self.index, d, name, bound, {}, self.tally, everywhere=True
        )
        if (
            found
            and one_part
            and self.beside is not None
            and any(full[-1] == name and target is not found[0] for full, target in self.beside)
        ):
            self.tally.add("no link in a docstring: the source beside it links the same name elsewhere")
            return None
        return found

    def link(self, target, words):
        """The link to the entry of 'target', or None if the page has none."""
        if id(target) in self.has_entry:
            return '<a class="r" href="#%s">%s</a>' % (esc(target.ident), words)
        return None

    def mark(self, d, name, bound, types, in_comment=False, after_bracket=False, first_in_bracket=None):
        """HTML for one name in a text: a link, a marked name, or None if it is left as it is."""
        self.spot = None
        found = self.find(d, name, bound, types, in_comment, after_bracket, first_in_bracket)
        if not found:
            return None
        target, first, count, how = found
        if target is d and not self.in_file_comment:
            return None
        if self.named is not None and not in_comment:
            # a dict keeps the order of first appearance; the value: was the name written plainly, not after a dot?
            key = (full_name_of_link(found, name), target)
            self.named[key] = self.named.get(key, False) or (first == 0 and not after_bracket)
        if after_bracket and d.part is None:
            self.tally.after_bracket[parts_of(name)[0]] = self.tally.after_bracket.get(parts_of(name)[0], 0) + 1
        if self.has_entry is None:
            self.wanted[id(target)] = target
            return None
        pieces = list(re.finditer(_PART, name))
        a, b = pieces[first].start(), pieces[first + count - 1].end()
        self.spot = (a, b - a, target)
        linked = self.link(target, esc(name[a:b]))
        if linked:
            self.tally.links += 1
            self.tally.add("link: " + how + (", in a comment" if in_comment else ""))
            middle = linked
        elif in_comment:
            return None
        else:
            self.tally.add("marked: declared in the Lean files, no entry on the page")
            middle = '<span class="u" title="declared in %s:%d; not shown on this page">%s</span>' % (
                esc(target.src.path),
                target.src.line_of(target.start),
                esc(name[a:b]),
            )
        return esc(name[:a]) + middle + esc(name[b:])

    def code_html(self, d, s, bound, types, own_name_at=None, base=0, in_comment=False, floor=None):
        """Lean code without comments or strings. If it is a stretch of d's file, it begins at the character 'base', and
        a bracket that closes in it is looked for back to the character 'floor', over comments and strings."""
        out, i = [], 0
        for m in NAME.finditer(s):
            a, b = m.span()
            if a < i or (a > 0 and (in_name(s[a - 1]) or s[a - 1] == "»")):
                continue
            after_bracket = a > 1 and s[a - 1] == "." and s[a - 2] == ")" and not in_comment
            if a > 0 and s[a - 1] == "." and not after_bracket:
                continue
            if own_name_at is not None and base + a == own_name_at:
                piece = "<b>" + esc(m.group()) + "</b>"
            else:
                inside = None
                if after_bracket and floor is None:
                    inside = first_name_in_bracket(s, a - 2)
                elif after_bracket:
                    inside = first_name_in_bracket(d.src.code[floor : base + a - 1], base + a - 2 - floor)
                piece = self.mark(d, m.group(), bound, types, in_comment, after_bracket, inside)
                if self.spots is not None and piece is not None and self.spot and id(self.spot[2]) in self.has_entry:
                    self.spots.append((base + a + self.spot[0], self.spot[1], self.spot[2]))
            if piece is not None:
                out.append(esc(s[i:a]) + piece)
                i = b
        out.append(esc(s[i:]))
        return "".join(out)

    def source_html(self, d, a, b, bound, types, own_name_at=None):
        """The characters a to b of d's file: comments and strings marked, names in the code linked."""
        src, out, i = d.src, [], a
        floor = d.start if d.start <= a else a  # a piece of the declaration's own text, or lines in force above it
        for s, e, kind in src.spans_between(a, b):
            out.append(self.code_html(d, src.text[i:s], bound, types, own_name_at, i, floor=floor))
            out.append(
                '<span class="%s">%s</span>'
                % ("s" if kind in ("string", "char") else "c", esc(src.text[s : min(e, b)]))
            )
            i = min(e, b)
        out.append(self.code_html(d, src.text[i:b], bound, types, own_name_at, i, floor=floor))
        return "".join(out)

    # -- comments ---------------------------------------------------------------------------------
    def running_text(self, d, s, bound, keep_signs=False):
        """Text of a comment: code between backticks, bold between double asterisks (bold may run over a line
        break and hold code). Backticks or asterisks that do not pair up in a block are left as they are. With
        keep_signs the backticks and asterisks are printed too, so that the file's columns stay aligned."""
        pieces = s.split(BACKTICK)
        if len(pieces) % 2 == 0:
            return esc(s)
        paired = not keep_signs and sum(p.count("**") for p in pieces[0::2]) % 2 == 0
        sign = BACKTICK if keep_signs else ""
        out, bold = [], False
        for k, piece in enumerate(pieces):
            if k % 2:
                code = self.code_html(d, piece, bound, {}, in_comment=True) if d else esc(piece)
                out.append("%s<code>%s</code>%s" % (sign, code, sign))
            elif not paired:
                out.append(esc(piece))
            else:
                for j, part in enumerate(piece.split("**")):
                    if j:
                        out.append("</b>" if bold else "<b>")
                        bold = not bold
                    out.append(esc(part))
        return "".join(out)

    def comment_html(self, d, src, a, b, bound, as_lines=False, margin=0):
        """A comment as paragraphs, lists, titles and indented blocks. No word is changed, moved or left
        out. These marks are turned into form and are not printed: the '*' or '-' of a list item,
        the '#' of a title, backticks around code, double asterisks around bold text. Line breaks
        are kept only in indented blocks, where the common indentation is removed. With as_lines the
        whole comment is one such block: line for line and sign for sign as in the file."""
        refuse_unseen_characters(src, a, b)
        blocks, cur = [], None  # a block: [kind, lines]
        if as_lines:
            lines = [l.rstrip() for l in src.text[a:b].split("\n")]
            lines[0] = lines[0].lstrip()  # it follows the opening sign
            while lines and not lines[0]:
                del lines[0]
            while lines and not lines[-1]:
                del lines[-1]
            if lines:
                blocks.append(["i", lines])
        for k, line in enumerate(src.text[a:b].split("\n") if not as_lines else ()):
            if k == 0:
                line = line.lstrip()  # it follows the opening sign, so its blanks are no indentation
            elif margin:  # a comment that is itself indented (a field's): its own column is no indentation
                line = line[min(margin, len(line) - len(line.lstrip())) :]
            text = line.strip()
            if not text:
                cur = None
                continue
            item = re.match(r"^( *)([*-]) +(\S.*)$", line)
            title = re.match(r"^ {0,3}(#{1,4}) +(\S.*)$", line)
            numbered = re.match(r"^ {0,3}(?:\((?:\d{1,2}|[a-z]|[ivx]{1,4})\)|\d{1,2}\.) ", line)
            indented = line.startswith(" ")
            depth = len(line) - len(line.lstrip())
            if item:
                cur = [
                    "%s%d" % ("s" if item.group(2) == "*" else "d", 2 if len(item.group(1)) >= 2 else 1),
                    [item.group(3).strip()],
                ]
                inner_text_at = item.start(3)
                blocks.append(cur)
            elif cur is not None and cur[0] in ("s2", "d2") and 0 < depth < inner_text_at:
                cur = ["c1", [text]]  # back at the outer item's level: its text goes on after the inner items
                blocks.append(cur)
            elif title:
                blocks.append(["h%d" % len(title.group(1)), [title.group(2).strip()]])
                cur = None
            elif numbered:
                cur = ["n", [text]]
                blocks.append(cur)
            elif cur is not None and cur[0] == "i" and indented:
                cur[1].append(line.rstrip())
            elif cur is not None and cur[0] != "i" and indented == (cur[0] != "p"):
                cur[1].append(text)
            elif indented:
                cur = ["i", [line.rstrip()]]
                blocks.append(cur)
            else:
                cur = ["p", [text]]
                blocks.append(cur)
        out, in_list = [], False
        for kind, lines in blocks:
            if kind == "i":
                margin = min(len(l) - len(l.lstrip()) for l in lines if l)
                lines = [l[margin:] for l in lines]
            body = self.running_text(d, "\n".join(lines), bound, keep_signs=as_lines)
            is_item = kind[0] in "sdc"
            if is_item != in_list:
                out.append("<ul>" if is_item else "</ul>")
                in_list = is_item
            out.append('<%s class="%s">%s</%s>' % (("li", kind, body, "li") if is_item else ("p", kind, body, "p")))
        if in_list:
            out.append("</ul>")
        return "\n".join(out)

    def file_comment(self, src, s, e, opener, folded=False):
        """A file's opening comment or a '/-! ... -/' comment. Names in it are looked up as at the next
        declaration of the file."""
        at = next((d for d in src.declarations if d.start >= s), src.declarations[-1] if src.declarations else None)
        self.in_file_comment, self.in_folded_comment = True, folded
        words = self.comment_html(at, src, s + opener, e - 2, set(), as_lines=folded)
        self.in_file_comment = self.in_folded_comment = False
        return '<div class="mod" data-file="%s" data-from="%d" data-to="%d">\n%s\n</div>\n' % (
            esc(src.path),
            src.line_of(s),
            src.line_of(e - 1),
            words,
        )

    # -- entries ----------------------------------------------------------------------------------
    def block(self, cls, d, a, b, bound, types, own_name_at=None):
        refuse_unseen_characters(d.src, a, b)
        first, last = d.src.line_of(a), d.src.line_of(b - 1)
        return '<div class="%s" data-from="%d" data-to="%d"><span class="ln">%s</span><pre>%s</pre></div>' % (
            cls,
            first,
            last,
            line_label(first, last),
            self.source_html(d, a, b, bound, types, own_name_at),
        )

    def entry(self, d):
        src = d.src
        if d.shown_end is None:
            cut(d)
        first, last = src.line_of(d.start), src.line_of(d.shown_end - 1)
        too_long = (
            d.part == "other"
            and not self.whole
            and (last - first + 1 > MAX_LINES or d.shown_end - d.start > MAX_CHARACTERS)
        )
        lines = [] if too_long else lines_shown_with(d)
        shown = "\n".join([src.code[a:b] for a, b in lines] + [src.code[d.start : d.shown_end]])
        where = _WHERE.search(shown) if d.kind not in CUT_BEFORE_PROOF else None
        bound, types = bound_names(shown, where.end() if where else None)
        bound |= set(d.members)
        if d.kind in ("structure", "class"):
            bound |= self.inherited_fields(d, 0)
        self.named = {}
        if too_long:
            right = [
                '<div class="text" data-from="%d" data-to="%d"><span class="ln">%s</span><p class="none">%s</p></div>'
                % (first, last, line_label(first, last), T_NOT_PRINTED)
            ]
        else:
            right = [self.block("force", d, a, b, bound, types) for a, b in lines]
            right.append(
                self.block(
                    "text", d, d.start, d.shown_end, bound, types, d.name_end - len(d.written) if d.written else None
                )
            )
        named, plainly, self.named = list(self.named), [k for k, plain in self.named.items() if plain], None
        if self.collecting:
            return named, bound
        if d.doc:
            self.beside = plainly
            left = '<div class="words" data-from="%d" data-to="%d">\n%s\n</div>' % (
                src.line_of(d.doc[0]),
                src.line_of(d.doc[1] - 1),
                self.comment_html(d, src, d.doc[0] + 3, d.doc[1] - 2, bound),
            )
            self.beside = None
        else:
            left = '<div class="words"><p class="none">%s</p></div>' % T_NO_DOCSTRING
        title = (
            esc(d.full).replace(".", ".<wbr>") + '</a> <span class="k">%s</span>' % d.kind
            if d.full
            else d.kind + "</a>"
        )
        return (
            '<article class="e" id="%s" data-file="%s" data-kind="%s">\n'
            '<h3><a href="#%s">%s <span class="w">%s:%d</span></h3>\n'
            '<div class="two">\n%s\n<div class="lean">\n%s\n</div>\n</div>\n</article>\n'
            % (esc(d.ident), esc(src.path), d.kind, esc(d.ident), title, esc(src.path), first, left, "\n".join(right))
        )

    def inherited_fields(self, d, depth):
        """The fields of the structures that d extends. They are bound names in d's source."""
        m = re.search(
            "(?<![%s])extends(?![%s])(.*?)(?:%s|:=|$)" % (_REST, _REST, _WHERE.pattern),
            d.src.code[d.name_end : d.whole_end],
            re.S,
        )
        out = set()
        if m and depth < 8:
            for name in NAME.findall(outside_brackets(m.group(1))):
                found = resolve(self.index, d, name, set(), {}, Tally())
                if found and found[0].kind in ("structure", "class") and found[0] is not d:
                    out |= set(found[0].members) | self.inherited_fields(found[0], depth + 1)
        return out


def line_label(first, last):
    return "line %d" % first if first == last else "lines %d–%d" % (first, last)


MOST_LEAN = 20000000  # bytes in one Lean file; the largest in the library has under three million


def small_bytes(path, most, name=None):
    """The bytes of a plain file of at most 'most' bytes, or None if there is no such file. It is opened without
    following a link and without waiting (a pipe would make the program hang), and what was opened is looked at.
    Where os has no O_NOFOLLOW, a look by path stands in front of the open and refuses a link: two acts, not one.
    Stops with a reason, in which the file is called 'name'."""
    name = name or path
    if not hasattr(os, "O_NOFOLLOW") and os.path.islink(path):
        raise Stop("%s: it is a link" % name)
    try:
        fd = os.open(
            path, os.O_RDONLY | getattr(os, "O_NONBLOCK", 0) | getattr(os, "O_NOFOLLOW", 0) | getattr(os, "O_BINARY", 0)
        )
    except FileNotFoundError:
        return None
    except OSError as e:
        raise Stop("%s: %s" % (name, "it is a link" if e.errno == errno.ELOOP else e.strerror))
    if not stat.S_ISREG(os.fstat(fd).st_mode):
        os.close(fd)
        raise Stop("%s: it is a folder or a special file, not a plain file" % name)
    with os.fdopen(fd, "rb") as f:
        data = f.read(most + 1)
    if len(data) > most:
        raise Stop("%s: it has more than %d bytes" % (name, most))
    return data


def small_text(path, most):
    """The text of such a file, or None if there is no such file."""
    data = small_bytes(path, most)
    try:
        return None if data is None else data.decode("utf-8")
    except UnicodeDecodeError:
        raise Stop("%s: it is not UTF-8" % path)


def head_html(path):
    """A head text: one paragraph per line. [words](X.md) links to a page in the Lean folder."""
    text = small_text(path, 100000)
    if text is None:
        raise Stop("%s: there is no such file. Give the folder of the four head texts with --heads=FOLDER." % path)
    lines = [l.strip() for l in text.split("\n") if l.strip()]
    if not lines or any(c in l for l in lines for c in "⟨⟩"):
        raise Stop("%s: it is empty, or it still has a place to fill in, marked ⟨ ⟩" % path)
    out = []
    for l in lines:
        pieces, i = [], 0
        for m in re.finditer(
            r"\[([^\]\n]+)\]\(((?:[A-Za-z]+/)*[A-Z][A-Z-]*\.md)\)|%s([^%s\n]+)%s" % ((BACKTICK,) * 3), l
        ):
            pieces.append(esc(l[i : m.start()]))
            if m.group(2):
                pieces.append('<a href="%s">%s</a>' % (esc(m.group(2)), esc(m.group(1))))
            else:
                pieces.append("<code>%s</code>" % esc(m.group(3)))
            i = m.end()
        out.append("<p>%s</p>" % "".join(pieces + [esc(l[i:])]))
    return "\n".join(out)


# ------------------------------------------------------------------------------------------------
# 5. The page
# ------------------------------------------------------------------------------------------------

STYLE = """
:root { --bg: #ffffff; --fg: #1b1b1b; --soft: #f4f4f1; --line: #c9c9c2; --dim: #585858;
  --link: #0a4fa0; --str: #7a3b00; --mark: #fff2c2;
  --theorem: #005f96; --def: #a84a00; --structure: #00734f; --abbrev: #a03c74; --other: #5f5f5f; }
@media (prefers-color-scheme: dark) {
  :root { --bg: #16181b; --fg: #e8e8e6; --soft: #212429; --line: #4a4f57; --dim: #b0b0ac;
    --link: #8ec5ff; --str: #f0b27a; --mark: #4a3f12;
    --theorem: #56b4e9; --def: #e69f00; --structure: #35c79a; --abbrev: #e6a5c9; --other: #a0a0a0; } }
* { box-sizing: border-box; }
html { scroll-padding-top: 1rem; }
body { margin: 0 auto; padding: 1rem; max-width: 110rem; background: var(--bg); color: var(--fg);
  font: 1rem/1.5 system-ui, -apple-system, "Segoe UI", Roboto, sans-serif; }
pre, code, .w, .ln, h3, nav li, summary, h2, p.i, p.path, p.moved { font-family: ui-monospace, SFMono-Regular,
  Menlo, Consolas, "DejaVu Sans Mono", monospace; }
h1 { font-size: 1.5rem; margin: 0 0 .5rem; }
h2 { font-size: 1.15rem; margin: 2.5rem 0 .75rem; padding: .4rem .6rem; background: var(--soft);
  border-left: .3rem solid var(--link); overflow-wrap: anywhere; }
h2.part { font-family: inherit; font-size: 1.3rem; border-left-color: var(--fg); }
h3 { font-size: .95rem; margin: 0; padding: .35rem .6rem; background: var(--soft);
  border-bottom: 1px solid var(--line); overflow-wrap: anywhere; }
h3 a { color: inherit; text-decoration: none; }
.k { font-weight: bold; font-size: .8rem; margin-left: .6rem; color: var(--other); }
h3 .w { font-weight: normal; color: var(--dim); font-size: .85rem; margin-left: .6rem; }
a { color: var(--link); }
a.r { text-decoration: underline dotted; text-underline-offset: .15em; }
.u { border-bottom: 1px dashed var(--dim); cursor: help; }
a:focus-visible, summary:focus-visible, input:focus-visible, button:focus-visible {
  outline: .2rem solid var(--link); outline-offset: .1rem; border-radius: .1rem; }
.skip { position: absolute; left: -100rem; }
.skip:focus { position: static; }
.top { position: fixed; right: .8rem; bottom: .8rem; z-index: 3; padding: .3rem .7rem; background: var(--soft);
  border: 1px solid var(--dim); border-radius: .3rem; font-size: .85rem; }
.e { border: 1px solid var(--line); border-left: .3rem solid var(--other); margin: 0 0 1rem; }
.e[data-kind="theorem"], .e[data-kind="lemma"] { border-left-color: var(--theorem); }
.e[data-kind="def"] { border-left-color: var(--def); }
.e[data-kind="structure"], .e[data-kind="inductive"], .e[data-kind="class"] { border-left-color: var(--structure); }
.e[data-kind="abbrev"] { border-left-color: var(--abbrev); }
.e[data-kind="theorem"] .k, .e[data-kind="lemma"] .k { color: var(--theorem); }
.e[data-kind="def"] .k { color: var(--def); }
.e[data-kind="structure"] .k, .e[data-kind="inductive"] .k, .e[data-kind="class"] .k { color: var(--structure); }
.e[data-kind="abbrev"] .k { color: var(--abbrev); }
.e:target { box-shadow: 0 0 0 .15rem var(--link); }
.e:target > h3 { background: var(--mark); }
.two { display: grid; grid-template-columns: minmax(0, 5fr) minmax(0, 7fr); }
.words, .lean { padding: .5rem .8rem; min-width: 0; align-self: start; position: sticky; top: 0; }
.words { overflow-wrap: anywhere; }
.lean { border-left: 1px solid var(--line); }
.words p, .mod p, .head p { margin: 0 0 .5rem; }
.head { max-width: 60rem; margin: 0 0 1rem; }
.words ul, .mod ul { margin: 0 0 .5rem; padding-left: 1.3rem; }
li { margin: 0 0 .2rem; }
li.d1, li.d2 { list-style-type: "– "; }
li.s2, li.d2 { margin-left: 1.2rem; }
li.c1 { list-style-type: none; }
p.n { margin-left: 1.2rem; }
p.i { margin-left: 1.2rem; white-space: pre-wrap; font-size: .85rem; }
p.none { color: var(--dim); font-style: italic; }
p.moved, p.path { margin: 0 0 1rem; font-size: .88rem; overflow-wrap: anywhere; }
p.h1, p.h2, p.h3, p.h4 { font-weight: bold; }
p.h1, p.h2 { font-size: 1.1rem; }
.mod { margin: 1.2rem 0 1rem; padding: .6rem .9rem; border-left: .3rem solid var(--line);
  max-width: 60rem; overflow-wrap: anywhere; }
details.file { margin: 1.5rem 0 .6rem; }
details.file .mod { margin-top: .4rem; }
details.how { margin: 0 0 1rem; }
details.how > summary, #contents > summary { font-family: inherit; font-size: 1rem; }
#contents > summary { font-weight: bold; }
code { font-size: .9em; }
p.i code { font-size: 1em; }
pre { margin: 0 0 .5rem; font-size: .82rem; line-height: 1.45; white-space: pre-wrap;
  overflow-wrap: anywhere; tab-size: 2; }
.ln { display: block; font-size: .7rem; color: var(--dim); }
.c { color: var(--dim); font-style: italic; }
.s { color: var(--str); }
nav { border: 1px solid var(--line); border-radius: .3rem; padding: .6rem .9rem; margin: 1rem 0; }
nav h2 { font-family: inherit; margin: 0 0 .3rem; padding: 0; background: none; border: 0; font-size: 1rem; }
nav ul { margin: .2rem 0 .6rem; padding-left: 1.2rem; columns: 22rem auto; }
nav ul + h2 { border-top: 1px solid var(--line); padding-top: .5rem; }
nav li { font-size: .82rem; overflow-wrap: anywhere; break-inside: avoid; }
summary { cursor: pointer; font-size: .88rem; overflow-wrap: anywhere; }
input, button { font: inherit; color: inherit; background: var(--bg); border: 1px solid var(--dim);
  border-radius: .2rem; }
input { margin: .4rem 0; padding: .3rem .5rem; width: min(100%, 30rem); }
button { padding: .1rem .6rem; cursor: pointer; }
button:disabled { color: var(--dim); border-color: var(--line); cursor: default; }
#card, #panel { position: fixed; overflow: auto; overscroll-behavior: contain; background: var(--bg);
  box-shadow: 0 .4rem 1.4rem rgba(0, 0, 0, .35); }
#card { z-index: 6; width: min(52rem, 94vw); border: .15rem solid var(--link); border-radius: .4rem; }
#panel { z-index: 5; top: 0; left: 0; bottom: 0; width: min(41vw, 48rem); border-right: .15rem solid var(--link); }
#panel.right { left: auto; right: 0; border-right: 0; border-left: .15rem solid var(--link); }
#card .e, #panel .e { margin: 0; border-width: 0 0 0 .3rem; }
#card h3 { position: sticky; top: 0; z-index: 1; }
#card .two, #panel .two { display: flex; flex-direction: column-reverse; }
#card .words, #panel .words, #card .lean, #panel .lean { position: static; align-self: auto; border-left: 0; }
#card .words, #panel .words { border-top: 1px solid var(--line); }
#card.cut::after { content: ""; display: block; position: sticky; bottom: 0; height: 1.4rem;
  background: linear-gradient(transparent, var(--soft)); border-bottom: .3rem double var(--link); }
.bar { position: sticky; top: 0; z-index: 2; display: flex; gap: .8rem; align-items: center; margin: 0;
  padding: .4rem .6rem; background: var(--bg); border-bottom: 1px solid var(--line); font-size: .88rem; }
@media (max-width: 60rem) {
  .two { display: block; }
  .words, .lean { position: static; align-self: auto; }
  .lean { border-left: 0; border-top: 1px solid var(--line); }
  #main-theorem ~ .e .two { display: flex; flex-direction: column-reverse; }
  #main-theorem ~ .e .lean { border-top: 0; border-bottom: 1px solid var(--line); }
  #panel { width: 96vw; } }
@media print {
  nav, #card, #panel, .top, .skip { display: none; }
  body { max-width: none; font-size: 9pt; }
  .words, .lean { position: static; }
  .e { break-inside: avoid; }
  a { color: inherit; text-decoration: none; } }
"""

# The script only copies entries that are already on the page into a hover card or a side panel, and runs
# the filter of the contents. Without it every link is still a plain link to its entry.
SCRIPT = """
(function () {
  'use strict';
  function byId(id) { return document.getElementById(id); }
  var card = document.createElement('aside');
  card.id = 'card';
  card.hidden = true;
  document.body.appendChild(card);
  var panel = byId('panel'), panelBody = byId('panel-body'), back = byId('panel-back'), go = byId('panel-go');
  var shownFor = null, timer = 0, touch = false, trail = [], opener = null, quiet = false, focusedAt = 0;

  function nameLink(node) {
    while (node && node !== document) {
      if (node.nodeName === 'A' && node.className === 'r') { return node; }
      node = node.parentNode;
    }
    return null;
  }
  function idOf(a) { return a.getAttribute('href').slice(1); }
  function copyOf(id) {
    var target = byId(id);
    if (!target || target.nodeName !== 'ARTICLE') { return null; }
    var copy = target.cloneNode(true), all = copy.getElementsByTagName('*');
    copy.removeAttribute('id');
    for (var i = 0; i < all.length; i++) { all[i].removeAttribute('id'); }
    return copy;
  }
  function empty(node) { while (node.firstChild) { node.removeChild(node.firstChild); } }

  // the hover card
  function markCut() {
    card.className = card.scrollHeight - card.clientHeight - card.scrollTop > 4 ? 'cut' : '';
  }
  function hideCard() {
    window.clearTimeout(timer);
    card.hidden = true;
    shownFor = null;
    empty(card);
  }
  function showCard(a) {
    window.clearTimeout(timer);
    if (shownFor === a) { return; }
    var copy = copyOf(idOf(a));
    if (!copy) { return; }
    hideCard();
    card.appendChild(copy);
    card.hidden = false;
    shownFor = a;
    // below the link or above it, wherever there is more room; never over the link, never outside the window
    var r = a.getBoundingClientRect(), gap = 6, edge = 4;
    var below = window.innerHeight - r.bottom - gap - edge, above = r.top - gap - edge;
    card.style.maxHeight = Math.max(below, above, 80) + 'px';
    var h = card.offsetHeight;
    card.style.top = (below >= h || below >= above ? r.bottom + gap : Math.max(edge, r.top - gap - h)) + 'px';
    card.style.left = Math.max(edge, Math.min(r.left, window.innerWidth - card.offsetWidth - edge)) + 'px';
    card.scrollTop = 0;
    markCut();
  }
  function later(f, ms) { window.clearTimeout(timer); timer = window.setTimeout(f, ms); }
  card.addEventListener('scroll', markCut, { passive: true });

  // the side panel: it keeps the reader's place on the page
  function fillPanel() {
    var id = trail[trail.length - 1], copy = copyOf(id);
    empty(panelBody);
    panelBody.appendChild(copy);
    go.setAttribute('href', '#' + id);
    back.disabled = trail.length < 2;
    panel.hidden = false;
    panel.scrollTop = 0;
  }
  function closePanel() {
    panel.hidden = true;
    trail = [];
    empty(panelBody);
    if (opener && document.contains(opener)) {  // the focus goes back to where it was, without a card
      quiet = true;
      opener.focus({ preventScroll: true });
      quiet = false;
    }
    opener = null;
  }
  back.addEventListener('click', function () { if (trail.length > 1) { trail.pop(); fillPanel(); } });
  byId('panel-close').addEventListener('click', closePanel);
  go.addEventListener('click', function () { opener = null; closePanel(); });

  document.addEventListener('pointerdown', function (e) { touch = e.pointerType === 'touch'; }, true);
  document.addEventListener('mouseover', function (e) {
    if (touch) { return; }
    var a = nameLink(e.target);
    if (card.contains(e.target)) { window.clearTimeout(timer); }
    else if (a) { later(function () { showCard(a); }, 250); }
    else if (shownFor) { later(hideCard, 350); }
    else { window.clearTimeout(timer); }
  });
  document.addEventListener('focusin', function (e) {
    if (touch || quiet) { return; }
    var a = nameLink(e.target);
    if (a && !card.contains(a)) {
      showCard(a);
      focusedAt = Date.now();
    } else if (!card.contains(e.target)) {
      hideCard();
    }
  });
  document.addEventListener('focusout', function (e) {
    if (shownFor && e.target === shownFor && !card.contains(e.relatedTarget)) { hideCard(); }
  });
  panel.addEventListener('scroll', function () {
    if (shownFor && panel.contains(shownFor) && Date.now() - focusedAt > 200) { hideCard(); }
  }, { passive: true });
  document.addEventListener('click', function (e) {
    var a = nameLink(e.target);
    // a plain click or a tap opens the panel; the keyboard and clicks with a modifier key follow the link
    if (a && e.button === 0 && e.detail !== 0 && !e.metaKey && !e.ctrlKey && !e.shiftKey && !e.altKey
        && byId(idOf(a)) && byId(idOf(a)).nodeName === 'ARTICLE') {
      e.preventDefault();
      var fresh = !panel.contains(a) && !card.contains(a);
      if (fresh) {
        opener = a;
        trail = [];
        panel.className = '';
      }
      trail.push(idOf(a));
      hideCard();
      fillPanel();
      // at the left, unless it would cover the name that was clicked
      if (fresh && a.getBoundingClientRect().left < panel.offsetWidth) { panel.className = 'right'; }
      quiet = true;
      byId('panel-close').focus();
      quiet = false;
    } else {
      // a link inside the panel that is followed (the Enter key, the entry's title) leaves the panel, as 'go' does
      if (panel.contains(e.target) && e.target.nodeName === 'A' && e.target !== go) { opener = null; closePanel(); }
      if (!card.contains(e.target) || e.target.nodeName === 'A') { hideCard(); }
    }
  });
  document.addEventListener('keydown', function (e) {
    if (e.key !== 'Escape') { return; }
    if (!card.hidden) { hideCard(); } else if (!panel.hidden) { closePanel(); }
  });
  window.addEventListener('scroll', function () {
    // the scroll by which the browser brings a focused name into sight must not close its card
    if (shownFor && !panel.contains(shownFor) && Date.now() - focusedAt > 200) { hideCard(); }
  }, { passive: true });

  // the contents and their filter
  var box = byId('filter'), none = byId('nomatch'), groups = document.querySelectorAll('#contents details');
  box.hidden = false;
  document.querySelector('a.top').addEventListener('click', function () {
    byId('contents').open = true;
    window.setTimeout(function () { box.focus(); }, 0);
  });
  box.addEventListener('input', function () {
    var q = box.value.trim().toLowerCase(), found = false;
    for (var i = 0; i < groups.length; i++) {
      var whole = groups[i].firstElementChild.textContent.toLowerCase().indexOf(q) >= 0;
      var items = groups[i].getElementsByTagName('li'), any = whole;
      for (var j = 0; j < items.length; j++) {
        var hit = whole || items[j].textContent.toLowerCase().indexOf(q) >= 0;
        items[j].hidden = !hit;
        any = any || hit;
      }
      groups[i].hidden = !any;
      groups[i].open = q !== '' && any;
      found = found || any;
    }
    none.hidden = found;
  });
}());
"""


def sha256_base64(s):
    return base64.b64encode(hashlib.sha256(s.encode("utf-8")).digest()).decode("ascii")


def lean_files(root, folders=None):
    """The Lean files, as paths from 'root': those in the given folders, or all, those that lie right in 'root' among
    them. A folder whose name begins with '.' is skipped: '.lake' holds the build and other libraries."""
    out = []

    def take(folder, names):
        for x in names:
            if x.endswith(".lean"):
                path = os.path.relpath(os.path.join(folder, x), root).replace(os.sep, "/")
                if not stat.S_ISREG(os.lstat(os.path.join(folder, x)).st_mode):
                    raise Stop("%s: it is a link or a special file, not a plain file" % path)
                if not re.fullmatch(r"[A-Za-z0-9_]+(?:/[A-Za-z0-9_]+)*\.lean", path):
                    raise Stop("%r: a Lean file's path may hold only letters, digits, '_' and '/'" % path)
                out.append(path)

    if not folders:
        take(root, [x for x in os.listdir(root) if not os.path.isdir(os.path.join(root, x))])
    for top in sorted(folders if folders else os.listdir(root)):
        if top.startswith(".") or os.path.islink(os.path.join(root, top)):
            continue
        for folder, subfolders, names in os.walk(os.path.join(root, top)):
            subfolders[:] = sorted(x for x in subfolders if not x.startswith("."))
            take(folder, names)
    return sorted(out)


def listed_theorems(root, index):
    """The theorems named in the first column of the first table of ONBYTES_PAGE."""
    text = small_text(os.path.join(root, ONBYTES_PAGE), 1000000)
    if text is None:
        raise Stop("%s: there is no such file" % ONBYTES_PAGE)
    lines = text.split("\n")
    k = next((k for k, l in enumerate(lines) if l.startswith("|")), len(lines))
    rows = []
    while k < len(lines) and lines[k].startswith("|"):
        rows.append(lines[k])
        k += 1
    out = []
    for row in rows[2:]:
        named = re.findall("%s([^%s]+)%s" % ((BACKTICK,) * 3), row.split("|")[1])
        for at, name in enumerate(named):
            if not NAME.fullmatch(name) or name.endswith(".lean"):
                continue  # a folder or a file
            parts = tuple(parts_of(name))
            fit = [
                d
                for (full, _), d in index.by_last.get(parts[-1], {}).items()
                if full[-len(parts) :] == parts
                and d.full == ".".join(full)
                and d.kind in ("theorem", "lemma")
                and d.src.path.startswith(ONBYTES_FOLDER + "/")
            ]
            many = len(fit)
            if many > 1:
                # then the one in the file or folder that the cell names next: `main_zero` (`Shell/AtWhole.lean`)
                where = next((x for x in named[at + 1 :] if "/" in x or x.endswith(".lean")), "?")
                where = ONBYTES_FOLDER + "/" + where
                fit = [d for d in fit if d.src.path == where or (where.endswith("/") and d.src.path.startswith(where))]
            if len(fit) != 1:
                raise Stop(
                    "%s names %s, and %d theorems of %s/ have that name%s"
                    % (
                        ONBYTES_PAGE,
                        name,
                        many,
                        ONBYTES_FOLDER,
                        (
                            "; the file or folder that the cell names next picks out %d of them" % len(fit)
                            if many > 1
                            else ""
                        ),
                    )
                )
            out.append(fit[0])
    if not out:
        raise Stop(
            "%s: no theorem's name found between backticks in the first column of its first table" % ONBYTES_PAGE
        )
    return out


def opening_comment(src):
    """(start, end, length of the opening sign) of the first block comment before the first command."""
    first_code = len(src.code) - len(src.code.lstrip())
    for s, e, kind in src.spans:
        if kind in ("block", "moddoc") and src.column_of(s) == 0 and e <= first_code:
            return s, e, 3 if kind == "moddoc" else 2
    return None


def file_html(page, src, moved):
    """One shown file: its comments and declarations in the file's order. The entries in 'moved' are at
    the top of the page; a line with their name takes their place."""
    items = [(d.start, d) for d in src.declarations]
    top = opening_comment(src)
    if top:
        items.append((top[0], top))
    for s, e, kind in src.spans:
        if (
            kind == "moddoc"
            and src.column_of(s) == 0
            and (not top or s != top[0])
            and not any(d.start <= s < d.whole_end for d in src.declarations)
        ):
            items.append((s, (s, e, 3)))
    out = []
    for _, x in sorted(items, key=lambda item: item[0]):
        if isinstance(x, tuple):
            out.append(page.file_comment(src, *x))
        elif x in moved:
            out.append(
                '<p class="moved" data-from="%d"><a class="r" href="#%s">%s</a></p>\n'
                % (src.line_of(x.start), esc(x.ident), esc(x.full))
            )
        else:
            out.append(page.entry(x))
    return "".join(out)


def collect(page, src, shown):
    """Set src.bound_in_file, the names bound by the shown declarations of the file (rule 6), and src.names_of,
    what the source of each of them names, in the order of first appearance."""
    src.bound_in_file = set()
    page.collecting = True
    for d in shown:
        d_named, bound = page.entry(d)
        src.bound_in_file |= bound
        d.src.names_of[id(d)] = d_named
    page.collecting = False


def contents_group(ident, title, declarations):
    items = "".join(
        '<li><a class="r" href="#%s">%s</a></li>\n' % (esc(d.ident), esc(d.full or d.ident)) for d in declarations
    )
    return '<details>\n<summary><a href="#%s">%s</a></summary>\n<ul>\n%s</ul>\n</details>\n' % (
        esc(ident),
        esc(title),
        items,
    )


def build(root, heads, say=lambda s: None, theorems=None, short=None, front=None):
    """The long page. If 'short' is a dict with the two pages' file names, the short page is put into it as well; if
    'front'
    is a dict with the front page's file name, that page."""
    if not os.path.isdir(os.path.join(root, CHOSEN_FOLDERS[0])):
        raise Stop("%s: no folder %s/ in it. Is it the repository's lean/ folder?" % (root, CHOSEN_FOLDERS[0]))
    chosen = lean_files(root, CHOSEN_FOLDERS[:2])
    for folder in CHOSEN_FOLDERS[2:]:  # named in also.txt: after the two
        more = lean_files(root, [folder])
        if not more:
            raise Stop("also.txt names %s: the folder holds no Lean file" % folder)
        chosen += more
    for p in FIRST_FILES:
        if p not in chosen:
            raise Stop("%s: listed in FIRST_FILES in this program, but not found under %s" % (p, root))
    order = FIRST_FILES + [p for p in chosen if p not in FIRST_FILES]
    head_texts = {"": head_html(os.path.join(heads, "head.txt"))}
    for part in ("how", "other", "onbytes"):
        head_texts[part] = head_html(os.path.join(heads, "head-%s.txt" % part))

    index, sources, passed_over, new_syntax = Index(), {}, {}, {}
    for p in lean_files(root):
        is_chosen = any(p.startswith(f + "/") for f in CHOSEN_FOLDERS)
        src = Source(root, p)
        src.declarations = scan(src, is_chosen)
        for _, _, word in src.unknown:
            passed_over.setdefault(word, []).append(p)
        for word in SYNTAX_WORD.findall(src.code):
            new_syntax[word] = new_syntax.get(word, 0) + 1
        src.names_of = {}
        index.lines[p] = src.text.count("\n")
        index.imports[p] = [
            m.group(1).replace(".", "/") + ".lean" for m in re.finditer(r"^import\s+(\S+)", src.code, re.M)
        ]
        for d in src.declarations:
            index.add(d)
        if is_chosen:
            sources[p] = src

    entries = {}  # id on the page -> declaration

    def give_id(d, ident):
        d.ident = ident
        if ident in entries or ident in (
            "contents",
            "main-theorem",
            "other",
            "onbytes",
            "filter",
            "nomatch",
            "card",
            "panel",
            "panel-body",
            "panel-back",
            "panel-go",
            "panel-close",
        ):
            stop(d.src.path, d.src.line_of(d.start), "the page already has something called %s" % ident)
        entries[ident] = d

    for p in order:
        for d in sources[p].declarations:
            give_id(d, d.full if d.full and not d.private else "%s:%d" % (p, d.src.line_of(d.start)))
    page = Page(index)
    for p in order:
        collect(page, sources[p], sources[p].declarations)
    page.wanted = {}
    for p in order:  # which declarations of other folders do the sources and comments name?
        file_html(page, sources[p], ())
    page.after_bracket_ok = set(page.tally.after_bracket)
    by_place = lambda d: (d.src.path, d.start)
    other = sorted(
        (
            d
            for d in page.wanted.values()
            if d.src.path not in sources and not d.src.path.startswith(ONBYTES_FOLDER + "/")
        ),
        key=by_place,
    )
    onbytes = sorted(listed_theorems(root, index), key=by_place)
    for part, declarations in (("other", other), ("onbytes", onbytes)):
        for d in declarations:
            d.part = part
            if d.private:
                stop(d.src.path, d.src.line_of(d.start), "a private declaration is named from another file")
            give_id(d, d.full)
    for src in {id(d.src): d.src for d in other + onbytes}.values():
        collect(page, src, [d for d in other + onbytes if d.src is src])
    page.has_entry = {id(d) for d in entries.values()}
    page.tally = Tally()

    main = []
    for name in MAIN_THEOREMS:
        if name not in entries or entries[name].part:
            raise Stop("%s: listed in MAIN_THEOREMS in this program, but no shown file declares it" % name)
        main.append(entries[name])
    layers, seen = [], {id(d) for d in main}
    for _ in range(2):  # what the main entries' sources link to, then what those entries' sources link to,
        layer = {}  # each in the order in which the names first appear
        for d in (main if not layers else layers[-1]):
            for _, target in d.src.names_of.get(id(d), ()):
                if id(target) in page.has_entry and id(target) not in seen:
                    layer.setdefault(id(target), target)
        seen |= set(layer)
        layers.append(list(layer.values()))

    body, contents = [], []
    for p in order:
        body.append(
            '<section>\n<h2 id="%s">%s</h2>\n%s</section>\n' % (esc(p), esc(p), file_html(page, sources[p], main))
        )
        contents.append(contents_group(p, p, sources[p].declarations))
    for part, title, declarations in (("other", T_OTHER, other), ("onbytes", T_ONBYTES, onbytes)):
        if not declarations:
            continue
        pieces, last = [], None
        for d in declarations:
            if d.src is not last:
                last, top = d.src, opening_comment(d.src)
                if top:
                    pieces.append(
                        '<details class="file">\n<summary>%s</summary>\n%s</details>\n'
                        % (esc(d.src.path), page.file_comment(d.src, *top, folded=True))
                    )
                else:
                    pieces.append('<p class="path">%s</p>\n' % esc(d.src.path))
            pieces.append(page.entry(d))
        body.append(
            '<section>\n<h2 class="part" id="%s">%s</h2>\n<div class="head">\n%s\n</div>\n%s</section>\n'
            % (part, esc(title), head_texts[part], "".join(pieces))
        )
        contents.append(contents_group(part, title, declarations))
    named = "".join(
        "<h2>%s</h2>\n<ul>\n%s</ul>\n"
        % (
            title,
            "".join(
                '<li><a class="r" href="#%s">%s</a> <span class="k">%s</span></li>\n'
                % (esc(d.ident), esc(d.full or d.ident), d.kind)
                for d in layer
            ),
        )
        for title, layer in zip(T_NAMED, layers)
        if layer
    )
    document = (
        '<!DOCTYPE html>\n<!--\n%s\n-->\n<html lang="en">\n<head>\n<meta charset="utf-8">\n'
        '<meta name="viewport" content="width=device-width, initial-scale=1">\n'
        '<meta http-equiv="Content-Security-Policy" content="default-src \'none\'; '
        "style-src 'sha256-%s'; script-src 'sha256-%s'; base-uri 'none'; form-action 'none'\">\n"
        "<title>%s</title>\n<style>%s</style>\n</head>\n<body>\n"
        '<a class="skip" href="#main-theorem">%s</a>\n<h1>%s</h1>\n<div class="head">\n%s\n</div>\n'
        '<details class="how">\n<summary>%s</summary>\n<div class="head">\n%s\n</div>\n</details>\n<main>\n'
        '<section>\n<h2 class="part" id="main-theorem">%s</h2>\n%s</section>\n'
        '<nav aria-label="%s">\n%s</nav>\n'
        '<nav aria-label="%s">\n<details id="contents">\n<summary>%s</summary>\n'
        '<input id="filter" type="search" placeholder="%s" aria-label="%s" hidden>\n'
        '<p class="none" id="nomatch" hidden>%s</p>\n'
        '%s</details>\n</nav>\n%s</main>\n<a class="top" href="#contents">%s</a>\n'
        '<aside id="panel" aria-label="%s" hidden>\n<p class="bar"><button type="button" id="panel-back">%s</button> '
        '<a id="panel-go" href="#main-theorem">%s</a> <button type="button" id="panel-close">%s</button></p>\n'
        '<div id="panel-body"></div>\n</aside>\n<script>%s</script>\n</body>\n</html>\n'
        % (
            LICENCE,
            sha256_base64(STYLE),
            sha256_base64(SCRIPT),
            TITLE,
            STYLE,
            T_SKIP,
            TITLE,
            head_texts[""],
            T_HOW,
            head_texts["how"],
            T_MAIN,
            "".join(page.entry(d) for d in main),
            T_LINKED,
            named,
            T_CONTENTS,
            T_CONTENTS,
            T_FILTER,
            T_FILTER,
            T_NO_MATCH,
            "".join(contents),
            "".join(body),
            T_CONTENTS,
            T_PANEL,
            T_BACK,
            T_GO,
            T_CLOSE,
            SCRIPT,
        )
    )

    if short is not None:
        short["document"] = short_page(root, heads, page, entries, short["long"], say)
        back, goal = dict(short_table(os.path.join(heads, "short"), "labels.txt", 2, True))["back"], short["short"]
    if front is not None:  # the line at the long page's top then leads to the front page, or where 'back-to' says
        front["document"] = front_page(root, heads, page, entries, front["long"], short and short["short"], say)
        front_labels = dict(front_table(os.path.join(heads, "front"), "labels.txt", 2, True))
        back, goal = front_labels["back"], front_labels.get("back-to", front["front"])
        own = (front["long"], front["front"], short and short["short"])
        if "back-to" in front_labels and (not re.fullmatch(r"[A-Za-z][A-Za-z0-9-]*\.html", goal) or goal in own):
            raise Stop(
                "front/labels.txt, 'back-to | %s': name another front page: letters, digits, '-', then '.html'" % goal
            )
    if short is not None or front is not None:
        document = turned(
            document, "</h1>\n", '</h1>\n<p class="back"><a href="%s">%s</a></p>\n' % (esc(goal), esc(back))
        )
    shown = [d for p in order for d in sources[p].declarations]
    tally = page.tally
    say("Lean files read: %d" % len(index.imports))
    say("declarations in them: %d" % (sum(len(v) for v in index.public.values()) + len(index.private)))
    say(
        "commands that this scanner does not know, passed over (nothing below one in its file is shown): %s"
        % (", ".join("%s %d in %d files" % (w, len(f), len(set(f))) for w, f in sorted(passed_over.items())) or "none")
    )
    say(
        "commands that declare notation, macros or syntax, in all Lean files (they can change what Lean makes of a "
        "text in another file; a page shows them only above texts of their own file): %s"
        % (", ".join("%s %d" % x for x in sorted(new_syntax.items())) or "none")
    )
    say("folders shown in full besides the two (from also.txt): %s" % (", ".join(CHOSEN_FOLDERS[2:]) or "none"))
    say("files shown: %d" % len(order))
    say(
        "declarations in them: %d (%d with a docstring, %d without)"
        % (len(shown), sum(1 for d in shown if d.doc), sum(1 for d in shown if not d.doc))
    )
    kinds = {}
    for d in shown:
        kinds[d.kind] = kinds.get(d.kind, 0) + 1
    say("by kind: " + ", ".join("%s %d" % kv for kv in sorted(kinds.items())))
    say("entries from other folders: %d, from %d files" % (len(other), len({d.src.path for d in other})))
    say("theorems listed in %s: %d" % (ONBYTES_PAGE, len(onbytes)))
    say("names in the two lists at the top: %s" % " + ".join(str(len(l)) for l in layers))
    known = set(index.imports)
    say(
        "imported from outside this folder: "
        + ", ".join(
            sorted(
                {q.split("/")[0].replace(".lean", "") for qs in index.imports.values() for q in qs if q not in known}
            )
        )
    )
    say("links on names: %d" % tally.links)
    for k in sorted(tally.how):
        say("  %s: %d" % (k, tally.how[k]))
    say(
        "no link because two or more declarations fit: %d places, %d names: %s"
        % (
            sum(tally.several.values()),
            len(tally.several),
            ", ".join("%s (%d)" % kv for kv in sorted(tally.several.items())),
        )
    )
    say(
        "rule 4, last parts linked after a closing bracket in the first two folders: "
        + ", ".join("%s (%d)" % kv for kv in sorted(tally.after_bracket.items()))
    )
    say(
        "'variable' lines left out because the declaration's own binders declare all their names again: %d"
        % len(LEFT_OUT)
    )
    for t in sorted(LEFT_OUT):
        say("  %s:%d is shown without line %d" % t)
    for t in sorted(set(NOTES)):
        say("note: " + t)
    say("sha256 of the style, for the checker: %s" % hashlib.sha256(STYLE.encode("utf-8")).hexdigest())
    say("sha256 of the script, for the checker: %s" % hashlib.sha256(SCRIPT.encode("utf-8")).hexdigest())
    if theorems is not None:
        for part, declarations in (("the two folders", shown), ("other folders", other), ("OnBytes", onbytes)):
            theorems += [
                "%s\t%s\t%s\t%s" % (part, d.kind, d.full, d.src.path)
                for d in declarations
                if d.kind in ("theorem", "lemma")
            ]
    return document


STYLE_SHORT = """
:root { --bg: #f6f6f3; --paper: #ffffff; --fg: #20242a; --dim: #5d646e; --line: #d9d9d2; --lean: #e9edf5;
  --link: #0a4fa0; --name: #0b3f7a; --kw: #7a2e8e; --str: #7a3b00; --mark: #fff2c2;
  --proved: #1a7f5a; --definition: #3f6aa8; --weak: #8a6d1f; --false: #b0481e; }
@media (prefers-color-scheme: dark) {
  :root { --bg: #14161a; --paper: #1c1f24; --fg: #e6e6e3; --dim: #a9afb8; --line: #3a3f47; --lean: #2a303a;
    --link: #8ec5ff; --name: #b9d8fb; --kw: #d6a3e6; --str: #f0b27a; --mark: #4a3f12;
    --proved: #4fc79a; --definition: #86aee6; --weak: #d9b95a; --false: #f0956a; } }
* { box-sizing: border-box; }
html { scroll-padding-top: 1rem; }
body { margin: 0; background: var(--bg); color: var(--fg);
  font: 1rem/1.55 system-ui, -apple-system, "Segoe UI", Roboto, sans-serif; overflow-wrap: anywhere; }
#column { max-width: 90rem; margin: 0 auto; padding: 1.6rem 1.25rem 6rem; container-type: inline-size; }
.with-panel #column { margin: 0; max-width: none; width: calc(100vw - min(46vw, 50rem)); }
pre, code, .w, .full, .path, .index li { font-family: ui-monospace, SFMono-Regular, Menlo, Consolas,
  "DejaVu Sans Mono", monospace; }
code { font-size: .9em; }
a { color: var(--link); }
a.r, a.x { text-decoration: underline dotted; text-underline-offset: .18em; text-decoration-thickness: 1px; }
pre a.r, pre a.x { color: var(--name); text-decoration: none; }
a.x::after { content: "\\2197"; font-size: .8em; color: var(--dim); }
pre a.r:hover, pre a.x:hover, pre a.r:focus-visible, pre a.x:focus-visible { text-decoration: underline;
  text-decoration-color: var(--link); }
.u { border-bottom: 1px dashed var(--line); }
a:focus-visible, summary:focus-visible, button:focus-visible { outline: .2rem solid var(--link);
  outline-offset: .1rem; }
h1 { font-size: 1.9rem; line-height: 1.2; margin: 0 0 .8rem; letter-spacing: -.01em; }
.print { display: inline-block; margin: 0 0 .9rem; padding: .15rem .7rem; border: 1px solid var(--weak);
  border-radius: 1rem;
  color: var(--weak); font-size: .85rem; }
.lead { margin: 0 0 .4rem; max-width: 72rem; font-size: 1.02rem; }
.guide { margin: 1.2rem 0; padding: 1rem 1.3rem; background: var(--paper); border: 1px solid var(--line);
  border-radius: .5rem; columns: 30rem 2; column-gap: 2.5rem; font-size: .95rem; }
.guide ul, .guide p { break-inside: avoid; }
.guide p { margin: 0 0 .5rem; }
.guide p:last-child { margin: 0; }
.guide ul { margin: 0 0 .7rem; padding-left: 1.2rem; }
.guide li { margin: 0 0 .15rem; }
.fold { margin: 1.2rem 0; }
.part > summary { margin: 0 0 1.8rem; color: var(--link); }
.holes { margin: 0 0 1.8rem; }
.holes .reach { margin: 0 0 .5rem; color: inherit; font-size: 1rem; }
.holes ul { margin: 0; padding: 0; list-style: none; }
:where(.holes li) { border-left: .3rem solid var(--dim); }
.holes li { margin: 0 0 .25rem; padding: .1rem 0 .1rem .7rem; font-size: .9rem; }
.holes li > a { font-family: ui-monospace, SFMono-Regular, Menlo, Consolas, monospace; font-size: .85rem; }
.holes .first { color: var(--dim); }
.fold .guide { margin: .6rem 0 0; }
summary { cursor: pointer; }
.above > summary { padding: .3rem 0; border-bottom: 1px solid var(--line); color: var(--dim); font-size: .8rem; }
.tiles { display: grid; grid-template-columns: repeat(auto-fit, minmax(16rem, 1fr)); gap: .8rem; margin: 1.2rem 0; }
.tile { display: block; padding: .8rem 1rem; background: var(--paper); border: 1px solid var(--line);
  border-top: .25rem solid var(--dim); border-radius: .5rem; color: inherit; text-decoration: none; }
.tile .t { display: block; font-weight: 600; }
.tile .status { display: block; margin: 0 0 .4rem; }
.slot { display: block; margin: .25rem 0 0; font-size: .84rem; line-height: 1.4; }
.sw { display: block; color: var(--dim); font-size: .66rem; text-transform: uppercase; letter-spacing: .05em; }
.legend { margin: 0 0 .4rem; color: var(--dim); font-size: .9rem; max-width: 56rem; }
header nav { margin: 0 0 1rem; font-size: .92rem; }
header nav p { margin: 0; }
.sample { display: inline-block; width: .8rem; height: .8rem; margin: 0 .1rem 0 .7rem; vertical-align: -.08rem;
  border-left: .3rem solid var(--dim); }
.top { position: fixed; right: .3rem; bottom: .5rem; z-index: 3; width: 1.5rem; height: 1.5rem; line-height: 1.4rem;
  text-align: center; background: var(--paper); border: 1px solid var(--line); border-radius: 50%; font-size: .85rem;
  text-decoration: none; opacity: .75; }
.with-panel .top { display: none; }
h2 { margin: 4rem 0 1rem; font-size: 1.45rem; line-height: 1.25; }
h2 .no { display: inline-block; min-width: 1.6rem; color: var(--dim); font-weight: 400; }
.open { margin: 0 0 1rem; max-width: 52rem; }
.reach { margin: -1.2rem 0 1.8rem; max-width: 60rem; color: var(--dim); font-size: .85rem; }
.card { margin: 0 0 1.8rem; padding: 1.1rem 1.4rem 1rem; background: var(--paper); border: 1px solid var(--line);
  border-left: .3rem solid var(--dim); border-radius: .5rem; }
.card:target { box-shadow: 0 0 0 .15rem var(--link); }
.st-proved, .st-proved-under, .st-hypothesis-proved, .st-hypothesis-proved-under { border-left-color: var(--proved);
  border-top-color: var(--proved); }
.st-proved-under, .st-hypothesis-proved-under { border-left-style: dashed; }
.st-definition { border-left-color: var(--definition); border-top-color: var(--definition); }
.sample.st-none { border-left-color: var(--dim); }
.st-only-defined, .st-not-proved, .st-assumed, .st-hypothesis, .st-arithmetic { border-left-color: var(--weak);
  border-top-color: var(--weak); border-left-style: dashed; }
.st-false-here, .st-hypothesis-at-risk { border-left-color: var(--false); border-top-color: var(--false);
  border-left-style: dashed; }
.tag { display: flex; flex-wrap: wrap; gap: .2rem .7rem; align-items: baseline; margin: 0 0 .2rem;
  font-size: .82rem; }
.kind { color: var(--dim); text-transform: uppercase; letter-spacing: .06em; font-size: .74rem; }
.status { font-weight: 600; font-size: .82rem; }
.st-proved .status, .st-proved-under .status, .st-hypothesis-proved .status,
  .st-hypothesis-proved-under .status { color: var(--proved); }
.st-definition .status { color: var(--definition); }
.st-only-defined .status, .st-not-proved .status, .st-assumed .status, .st-hypothesis .status,
  .st-arithmetic .status { color: var(--weak); }
.st-false-here .status, .st-hypothesis-at-risk .status { color: var(--false); }
.tag .w { margin-left: auto; color: var(--dim); font-size: .76rem; }
h3 { margin: 0 0 .6rem; font-size: 1.15rem; line-height: 1.3; }
.doc { margin: 0 0 .6rem; max-width: 60rem; font-size: .93rem; }
.remark { margin: .9rem 0 0; max-width: 54rem; font-size: .93rem; }
.remark ul { margin: 0 0 .3rem; padding-left: 1.2rem; }
.remark li { margin: 0 0 .25rem; }
.where { margin: 0; color: var(--dim); font-size: .88rem; }
.rows { border-top: 1px solid var(--line); }
.row { display: grid; grid-template-columns: 5rem minmax(0, 3fr) minmax(0, 5fr); gap: 0 .8rem;
  border-bottom: 1px solid var(--line); }
.role { padding: .5rem 0; color: var(--dim); font-size: .7rem; text-transform: uppercase; letter-spacing: .04em;
  white-space: nowrap; }
.say { padding: .4rem 0; font-size: .93rem; line-height: 1.45; grid-column: 2; }
.say p { margin: 0 0 .3rem; }
.say ul { margin: 0 0 .3rem; padding-left: 1.2rem; }
.row .lean { grid-column: 3; padding: .4rem .8rem; background: var(--lean); min-width: 0; }
.row.wide .lean { grid-column: 2 / 4; }
.row.solo .lean { grid-column: 1 / 4; }
.row.aside .lean { background: none; padding: .25rem 0; color: var(--dim); }
.row.aside pre { font-size: .7rem; }
pre { margin: 0; font-size: .78rem; line-height: 1.55; white-space: pre-wrap; tab-size: 2; }
.l { display: block; }
.kw { color: var(--kw); }
.c { color: var(--dim); font-style: italic; }
.s { color: var(--str); }
pre b { font-weight: 700; }
.words p { margin: 0 0 .5rem; }
.words ul { margin: 0 0 .5rem; padding-left: 1.3rem; }
li.d1, li.d2 { list-style-type: "– "; }
li.s2, li.d2 { margin-left: 1.2rem; }
li.c1 { list-style-type: none; }
p.n { margin-left: 1.2rem; }
p.i { margin-left: 1.2rem; white-space: pre-wrap; font-size: .85rem; font-family: ui-monospace, monospace; }
p.none { color: var(--dim); font-style: italic; }
.full { display: flex; flex-wrap: wrap; gap: .2rem 1rem; align-items: baseline; margin: .8rem 0 0; font-size: .78rem; }
.full a { color: var(--dim); }
.full a + a { padding: 0 .6rem; border: 1px solid var(--line); border-radius: 1rem; text-decoration: none;
  color: var(--link);
  font-family: system-ui, -apple-system, "Segoe UI", Roboto, sans-serif; }
.full .status { margin-left: auto; font-family: system-ui, -apple-system, "Segoe UI", Roboto, sans-serif; }
.index .path { margin: 1rem 0 .2rem; font-size: .82rem; color: var(--dim); }
.index ul { margin: 0; padding: 0; list-style: none; }
.index li { padding: .15rem 0; font-size: .82rem; }
.index .first { font-family: system-ui, -apple-system, "Segoe UI", Roboto, sans-serif; font-size: .86rem;
  margin-left: .4rem; }
.index li:target { background: var(--mark); }
.index .w { color: var(--dim); }
.index li > a.x { font-family: system-ui, sans-serif; font-size: .76rem; color: var(--dim); margin-left: .5rem; }
button { font: inherit; color: inherit; background: var(--paper); border: 1px solid var(--dim); border-radius: .25rem;
  padding: .1rem .6rem; cursor: pointer; }
button:disabled { color: var(--dim); border-color: var(--line); cursor: default; }
#card, #panel { position: fixed; overflow: auto; overscroll-behavior: contain; background: var(--paper);
  box-shadow: 0 .4rem 1.6rem rgba(0, 0, 0, .25); }
#card { z-index: 6; width: min(46rem, 94vw); border: 1px solid var(--link); border-radius: .5rem; }
#panel { z-index: 5; top: 0; right: 0; bottom: 0; width: min(46vw, 50rem); border-left: 1px solid var(--line); }
.e h3 { position: sticky; top: 0; margin: 0; padding: .5rem .9rem; background: var(--paper);
  border-bottom: 1px solid var(--line);
  font: 600 .88rem/1.4 ui-monospace, SFMono-Regular, Menlo, Consolas, monospace; }
#panel .e h3 { top: 2.4rem; }
.e h3 a { color: inherit; text-decoration: none; }
.e .k { margin-left: .5rem; color: var(--dim); font-weight: 400; }
.e h3 .w { margin-left: .5rem; color: var(--dim); font-weight: 400; font-size: .78rem; }
.e .two { display: flex; flex-direction: column-reverse; }
.e .lean { padding: .6rem .9rem; background: var(--lean); }
.e .words { padding: .6rem .9rem; font-size: .92rem; }
.e .ln { display: block; font-size: .7rem; color: var(--dim); font-family: ui-monospace, monospace; }
.e .force { margin: 0 0 .5rem; }
#card.cut::after { content: ""; display: block; position: sticky; bottom: 0; height: 1.4rem;
  background: linear-gradient(transparent, var(--lean)); border-bottom: .25rem double var(--link); }
.bar { position: sticky; top: 0; z-index: 2; display: flex; gap: .8rem; align-items: center; margin: 0;
  height: 2.4rem;
  padding: 0 .9rem; background: var(--paper); border-bottom: 1px solid var(--line); font-size: .86rem; }
@container (max-width: 54rem) {
  span.l[class*=" o"] { margin-left: 2ch; }
  .row { display: block; padding: .3rem 0; }
  .role { padding: .2rem 0 0; }
  .say { padding: .1rem 0 .3rem; }
  .card { padding: .9rem .9rem .8rem; } }
@media (max-width: 48rem) {
  #column { padding: 1.2rem .7rem 4rem; }
  h1 { font-size: 1.55rem; }
  .with-panel #column { width: auto; }
  #panel { width: 100vw; } }
@media print {
  nav, #card, #panel, .top { display: none; }
  body { background: none; font-size: 9pt; }
  .card { break-inside: avoid; } }
"""


def turned(text, old, new):
    if text.count(old) != 1:
        raise AssertionError("the text to change has not exactly one %r" % old)
    return text.replace(old, new)


# The short page's script is the long page's with a few changes: what the hover card or the panel shows is taken from
# the entries kept at the page's end; the panel stands at the right, and the reading column shrinks beside it and keeps
# its place; no filter.
SCRIPT_SHORT = SCRIPT[: SCRIPT.index("  // the contents and their filter")] + """  function reveal() {
    var n = byId(decodeURIComponent(window.location.hash.slice(1)));
    while (n) { if (n.nodeName === 'DETAILS') { n.open = true; } n = n.parentNode; }
  }
  window.addEventListener('hashchange', reveal);
  reveal();
}());
"""
for _old, _new in (
    ("var target = byId(id);", "var target = byId('e:' + id);"),
    ("        && byId(idOf(a)) && byId(idOf(a)).nodeName === 'ARTICLE') {", "        && byId('e:' + idOf(a))) {"),
    (
        "    panel.hidden = false;\n",
        "    panel.hidden = false;\n    document.documentElement.className = 'with-panel';\n",
    ),
    (
        "    panel.hidden = true;\n",
        "    var at = opener && document.contains(opener) ? opener.getBoundingClientRect().top : null;\n"
        "    panel.hidden = true;\n    document.documentElement.className = '';\n"
        "    if (at !== null) { window.scrollBy(0, opener.getBoundingClientRect().top - at); }\n",
    ),
    ("        panel.className = '';\n", "        restX = e.clientX;\n        restY = e.clientY;\n"),
    (
        "    if (touch) { return; }\n    var a = nameLink(e.target);\n    if (card.contains",
        "    if (touch || (e.clientX === restX && e.clientY === restY)) { return; }  // the page moved, not the "
        "pointer\n    restX = restY = -1;\n    var a = nameLink(e.target);\n    if (card.contains",
    ),
    ("  var shownFor = null,", "  var restX = -1, restY = -1, shownFor = null,"),
    (
        "      hideCard();\n      fillPanel();\n",
        "      hideCard();\n      var at = fresh ? a.getBoundingClientRect().top : 0;\n      fillPanel();\n",
    ),
    (
        "      // at the left, unless it would cover the name that was clicked\n"
        "      if (fresh && a.getBoundingClientRect().left < panel.offsetWidth) { panel.className = 'right'; }\n",
        "      if (fresh) { window.scrollBy(0, a.getBoundingClientRect().top - at); }  // the reader's place is kept\n",
    ),
):
    SCRIPT_SHORT = turned(SCRIPT_SHORT, _old, _new)

# ------------------------------------------------------------------------------------------------
# 6. The short page: the final claims alone, each with the definitions that its statement names
# ------------------------------------------------------------------------------------------------
# From the top: the mark, the title, the tiles, the contents, the head's lines, the guide's box, the legend; the
# sections with their cards; the index; and, hidden, the entries that the hover card and the side panel show.
# What stands on it is data: nine small files with fixed names in the folder short/ among the head texts. All but
# claims.txt and labels.txt may be absent. A line that begins with '#' is a comment.
#   claims.txt   '== title' opens a section; '==- title' one whose cards are folded (the label 'folded'; {cards} is
#                their number). '> words' is a line of words, where it stands. 'FULL.NAME | status' is a card; a
#                declaration without a name goes by its place, FILE:LINE, and can have a card and nothing else. The
#                status is proved or proved-under (a theorem or lemma that has a line in scripts/top-theorems.txt, the
#                list of the library's audit; proved-under is meant for a theorem whose statement takes named
#                hypotheses: the program does not test which of the two fits, whoever writes claims.txt chooses),
#                definition or only-defined (no theorem, lemma or example),
#                false-here, not-proved, or '-': no word at the card's foot. '| doc' behind it lays the first sentence
#                of the doc comment under the card's title. '+ FULL.NAME' is a line in the index for a declaration that
#                no card's Lean text names.
#                Hypotheses of a theorem are definitions with the status assumed, hypothesis or arithmetic. Behind the
#                last two, '| by THEOREM' names a theorem that proves the hypothesis: proved_how() says what is asked
#                of it, and the card then says so, with a link; '| at-risk' marks an open one that may be false.
#                Lines that this program counts, each by the label of its name: '! reach FULL.NAME'; '! folder NAME'
#                (the files, declarations and lines of a folder); '! hypotheses FULL.NAME' (the declaration whose Lean
#                text names its hypotheses; if it is a structure, the structures that it extends count with it, and
#                there must be one card for each field, or none at all: then its fields are counted as the hypotheses,
#                all open; {fields} is their number).
#   rows.txt     '=== FULL.NAME' opens a card's rows. A row: '# margin: word' (optional), '@ characters at which the
#                piece begins', then the phrase's lines. '@^' is the row of the lines in force above the declaration. A
#                structure without '@' rows goes by field, each field's doc comment at the left; '% field | word'
#                gives that field's row its margin word.
#                Where a piece begins: the characters behind '@' are sought behind those of the '@' before. If they
#                begin with '/-' or '--', they are sought where a comment opens, and the piece begins there. If not,
#                they are sought outside comments and not in the midst of a name (between two of the characters A-Z,
#                a-z, 0-9, _ and '), and the piece also takes the comments that stand right before them, each the first
#                thing on its line. If the '@' before opens the first of these comments, all of them stay in that row.
#                No piece can begin at words in the midst of a comment. So a row is best anchored on code, with enough
#                characters that they stand nowhere else in the statement: then a renamed field stops the program, and
#                a comment above the field that is reworded, added or taken away does not.
#   titles.txt   'FULL.NAME | a card's title'; without one the title is the declaration's own short name
#   tiles.txt    'title | words | FULL.NAME of the card to jump to', and under it '+ slot | words'
#   remarks.txt  'FULL.NAME | one bullet under that card's rows'. 'FULL.NAME | (doc) words': the bullet is a passage
#                of the declaration's doc comment; the program stops if the comment no longer has it.
#   labels.txt   'key | words'. Needed: title, the status words except proved-under, how-much, reach, index,
#                index-words, all, legend, contents, back (the long page's line at its top). Optional: comment,
#                no-status, remarks-link; guide (the guide's box is folded under these words); same-lines (lines in
#                force that an earlier card of the same section shows are folded under these words; {name} is that
#                card's); 'sign ∀ | for every' (the margin word of a piece whose code begins with that sign, on cards
#                whose rows give no margin word at all). Needed where claims.txt uses them: folded, folder, hypotheses,
#                and the words for proved-under, assumed, hypothesis, arithmetic, hypothesis-proved,
#                hypothesis-proved-under, hypothesis-at-risk.
#   short-head.txt, short-guide.txt, first-print-mark.txt: one paragraph a line. In the guide '- ' opens a bullet, and
#                ‹BY PROGRAM› is where the label how-much goes. Numbers in that label: {cards}, {lines}: the page's
#                cards, their lines of Lean; {cards1}, {lines1}: section 1's; {theorems}: the cards called proved or
#                proved-under; {theorems-under}: those called proved-under.
# Backticks hold code, and [words](X.md), [words](#s3), [words](long-page), [words](long-page#ID) are links, in '>'
# lines, titles.txt, the three texts of the top and the labels how-much, reach, index-words, legend, remarks-link,
# guide, same-lines, folded, folder and hypotheses. Phrases, bullets and a tile's words take backticks alone. Every
# other place takes neither, and the program stops at a mark that a place does not take. It also stops at ⟨ ⟩ ‹ ›,
# which mark a place still to be filled in; only an '@' line, which is Lean text, may have them. Where links are
# taken, and in a tile's words, the counts of hypotheses are filled in: {all}; {assumed}; {named}, {proved},
# {proved-under}, {open}, {at-risk} (which are among the open) for the status hypothesis; the same five behind
# 'arithmetic-', as in {arithmetic-open}. They are those of the first '! hypotheses'; with a short name behind a
# blank, as in {named Holes}, those of that declaration. The program's own words on the page: Lean's keywords as
# kinds, the sign ↑, the side panel's labels, and what the kept entries have on the long page too.

KEYWORDS = set(
    "theorem lemma def abbrev structure inductive class instance example noncomputable private protected where "
    "extends fun let do pure if then else match with at by in return have show from Type Prop Sort".split()
)
STATUSES = ("proved", "proved-under", "definition", "only-defined", "false-here", "not-proved")  # and '-': no word
FOR_THEOREMS = STATUSES[:2]  # what is asked of a card that bears one of them: see 'claims.txt' above
# Hypotheses of a theorem, in three classes: 'assumed' (taken from elsewhere), 'hypothesis' (the library's own to
# prove), 'arithmetic' (could be checked by running). Where claims.txt names a theorem that proves one of the last two
# classes, this program sets its status: proved, or proved under a hypothesis that is called assumed. '| at-risk' behind
# one of them is a mark of the data's writers: it is open, and may be false
HYPOTHESIS = (
    "assumed",
    "hypothesis",
    "arithmetic",
    "hypothesis-proved",
    "hypothesis-proved-under",
    "hypothesis-at-risk",
)
AUDITED = "scripts/top-theorems.txt"  # in the Lean folder: the theorems whose axioms the library's own audit looks at
FILLED = (
    {}
)  # '{assumed}', '{named}', '{proved}', '{open}' and so on -> the counts of hypotheses, for every line of words


LEAVES = ' target="_blank" rel="noopener"'  # a link to the long page opens a tab of its own: the reader's place is kept
LONG_NAME = [""]  # the long page's file name, while the short page is made


def coded(s):
    """A link's words: backticks hold code there too."""
    return re.sub("%s([^%s]+)%s" % ((BACKTICK,) * 3), r"<code>\1</code>", esc(s))


def inline_html(l):
    """One line of the short page's words: backticks hold code; [words](X.md) links to a page in the Lean folder,
    [words](#s3) to a section of this page, [words](long-page) or [words](long-page#ID) to the long page."""
    for place, number in FILLED.items():
        l = l.replace(place, number)
    pieces, i = [], 0
    for m in re.finditer(
        r"\[([^\]\n]+)\]\(((?:[A-Za-z]+/)*[A-Z][A-Z-]*\.md|#s\d+|long-page(?:#[^\s)]+)?)\)|%s([^%s\n]+)%s"
        % ((BACKTICK,) * 3),
        l,
    ):
        pieces.append(esc(l[i : m.start()]))
        if m.group(2) and m.group(2).startswith("long-page"):
            pieces.append(
                '<a class="x" href="%s"%s>%s</a>'
                % (esc(LONG_NAME[0] + m.group(2)[len("long-page") :]), LEAVES, coded(m.group(1)))
            )
        elif m.group(2):
            pieces.append('<a href="%s">%s</a>' % (esc(m.group(2)), coded(m.group(1))))
        else:
            pieces.append("<code>%s</code>" % esc(m.group(3)))
        i = m.end()
    return "".join(pieces + [esc(l[i:])])


def short_lines(folder, name, needed=False):
    """The lines of a small text in short/, without blank lines and remarks."""
    text = small_text(os.path.join(folder, name), 400000)
    if text is None:
        if needed:
            raise Stop("%s: there is no such file" % os.path.join(folder, name))
        return []
    lines = [l.strip() for l in text.split("\n") if l.strip() and not l.startswith("#")]
    if name == "short-guide.txt":  # there alone: a place that the program fills with its counts
        lines = [re.sub("‹BY PROGRAM[^›]*›", "\x00", l.replace("\x00", "‹")) for l in lines]
    if any(c in l for l in lines for c in "⟨⟩‹›"):
        raise Stop("%s: it still has a place to fill in, marked ⟨ ⟩ or ‹ ›" % os.path.join(folder, name))
    return lines


def short_table(folder, name, columns, needed=False):
    rows = []
    for l in short_lines(folder, name, needed):
        cells = [c.strip() for c in l.split("|", columns - 1)]
        if len(cells) != columns:
            raise Stop("%s: this line has not %d parts between bars: %s" % (os.path.join(folder, name), columns, l))
        rows.append(cells)
    return rows


def as_typed(s, where, code=False):
    """s, for a place that renders no links and, unless 'code', no backticks: there such marks would print as signs."""
    if "](" in s or (BACKTICK in s and not code):
        raise Stop("%s: %s not rendered there: %s" % (where, "a link is" if code else "backticks and links are", s))
    return s


def rows_stop(d, folder, why):
    raise Stop("%srows.txt, '=== %s': %s" % (folder, d.full, why))


COMMENTS = ("line", "block", "doc", "moddoc")  # the kinds of Source.spans that are comments
MIDST = re.compile("[A-Za-z0-9_']{2}")  # two characters of one name; plain letters alone, to keep the rule simple
NOT_FOUND = (
    "'@ %s' is not found in its place in the statement (%s:%d). The first '@' must open the declaration; each further "
    "one must come behind the one before it. An anchor that begins with '/-' or '--' is sought where a comment opens, "
    "any other outside comments and not in the midst of a name"
)


def anchor_at(src, first, after, end):
    """Where the characters of an anchor of rows.txt stand next, from 'after' on and before 'end'; -1 if nowhere. An
    anchor that begins like a comment ('/-', '--') is sought where a comment opens. Any other is sought outside
    comments, so that the wording of a comment cannot catch it, and not in the midst of a name; a string counts as
    code."""
    if first.startswith(("/-", "--")):
        opens = {s for s, _, kind in src.spans_between(after, end) if kind in COMMENTS}
        at = src.text.find(first, after, end)
        while at >= 0 and at not in opens:
            at = src.text.find(first, at + 1, end)
        return at
    at = src.solid.find(first, after, end)
    while at >= 0 and (
        src.text[at : at + len(first)] != first  # the anchor's blanks matched the blanks that 'solid' has for a comment
        or (at and MIDST.match(src.text, at - 1))  # in the midst of a name: 'Proof' in 'PreProof'
    ):
        at = src.solid.find(first, at + 1, end)
    return at


def with_comments(src, at, since, behind):
    """'at', or the start of the first of the comments that stand right before it: nothing but blanks and line ends
    between, each comment the first thing on its line. So a field's row shows the field's doc comment, whatever its
    words are, and a comment at the end of the line above stays with that line. The anchor before stands from 'since' to
    'behind'. If the first of these comments is the one that the anchor before opens, all of them belong to that
    anchor's row, and the answer is 'at'."""
    # each comment by the place behind its last character that is no blank: a '--' comment runs on to its line's end
    comments = [(s, e) for s, e, kind in src.spans_between(since, at) if kind in COMMENTS]
    starts = {s + len(src.text[s:e].rstrip()): s for s, e in comments}
    first = at
    while True:
        end = first
        while end > since and src.text[end - 1].isspace():
            end -= 1
        s = starts.get(end)
        if s is None or src.text[src.text.rfind("\n", 0, s) + 1 : s].strip():
            return first
        if s < behind:
            return at
        first = s


def by_lines(html_text, column=0):
    """Lean text as HTML, each line in a block of its own, so that a wrapped line hangs behind its own indentation.
    No character is added or taken away: a mark that runs over a line end is closed there and opened again. A piece that
    was cut in the middle of a line begins at that line's 'column', so that the text's shape stays."""
    out, open_tags = [], []
    lines = html_text.split("\n")
    for k, line in enumerate(lines):
        if k == len(lines) - 1 and not line:
            break
        start = "".join(open_tags)
        for m in re.finditer(r"<(/?)(?:span|a|b)\b[^>]*>", line):
            if m.group(1):
                open_tags.pop()
            else:
                open_tags.append(m.group())
        end = "".join("</%s>" % re.match(r"<(\w+)", t).group(1) for t in reversed(open_tags))
        indent = len(line) - len(line.lstrip(" ")) if not start else 0
        out.append(
            '<span class="l i%d%s">%s%s%s%s</span>'
            % (
                min(indent, 40),
                " o%d" % min(column, 100) if column and not k else "",
                start,
                line,
                "\n" if k < len(lines) - 1 else "",
                end,
            )
        )
    return "".join(out)


class ShortPage(Page):
    """A name with a card or an index line here links to it; one with an entry on the long page alone, to that page."""

    def __init__(self, long_page, long_name):
        Page.__init__(self, long_page.index)
        self.has_entry, self.after_bracket_ok = long_page.has_entry, long_page.after_bracket_ok
        self.here, self.long_name, self.lines_on, self.shown_above, self.proved_by = set(), long_name, {}, {}, {}

    def link(self, target, words):
        if id(target) in self.here:
            return '<a class="r" href="#%s">%s</a>' % (esc(target.ident), words)
        if id(target) in self.has_entry:
            return '<a class="x" href="%s#%s"%s>%s</a>' % (esc(self.long_name), esc(target.ident), LEAVES, words)
        return None

    def mark(self, d, name, bound, types, in_comment=False, after_bracket=False, first_in_bracket=None):
        if not in_comment and name in KEYWORDS:
            return '<span class="kw">%s</span>' % esc(name)
        return Page.mark(self, d, name, bound, types, in_comment, after_bracket, first_in_bracket)

    def reading(self, d):
        """As in entry(): the lines in force, and what the shown text binds."""
        if d.shown_end is None:
            cut(d)
        lines = lines_shown_with(d)
        shown = "\n".join([d.src.code[a:b] for a, b in lines] + [d.src.code[d.start : d.shown_end]])
        where = _WHERE.search(shown) if d.kind not in CUT_BEFORE_PROOF else None
        bound, types = bound_names(shown, where.end() if where else None)
        bound |= set(d.members)
        if d.kind in ("structure", "class"):
            bound |= self.inherited_fields(d, 0)
        return lines, bound, types

    def proved_how(self, h, t, audited, assumed):
        """How the theorem t proves the hypothesis h, as far as a text can tell. 'hypothesis-proved': h is 'def H : Prop
        :=' and t is 'theorem T : H'. 'hypothesis-proved-under': t is 'theorem T : A → H', A one of the 'assumed'. No
        binder, no line in force at either, no 'sorry' written in the proof; the audit's list has t. Else it stops."""
        for d in (h, t):
            if d.shown_end is None:
                cut(d)
        said, why_not = t.src.code[t.name_end : t.shown_end], None
        names = [target for _, target in t.src.names_of.get(id(t), ())]
        if re.fullmatch(r"\s*:\s*%s\s*" % NAME.pattern, said) and names == [h]:
            how = "hypothesis-proved"
        elif (
            re.fullmatch(r"\s*:\s*%s\s*(?:→|->)\s*%s\s*" % (NAME.pattern, NAME.pattern), said)
            and names[1:] == [h]
            and any(names[0] is a for a in assumed)
        ):
            how = "hypothesis-proved-under"
        else:
            why_not = (
                "its statement is neither the hypothesis's name alone nor 'A → ' and that name, A being called assumed"
            )
        if t.kind not in ("theorem", "lemma"):
            why_not = "it is a %s" % t.kind
        elif lines_shown_with(h) or lines_shown_with(t):
            why_not = (
                "'variable' lines or the like are in force at one of the two: they could add a parameter or a premise"
            )
        elif not re.match(r"\s*:\s*Prop\s*:=", h.src.code[h.name_end : h.whole_end]):
            why_not = "the hypothesis is not written 'def NAME : Prop :='"
        elif re.search("(?<![%s.])sorry(?![%s])" % (_REST, _REST), t.src.code[t.shown_end : t.whole_end]):
            why_not = "its proof has a 'sorry'"
        elif t.full not in audited:
            why_not = "%s has no line for it" % AUDITED
        if why_not:
            raise Stop("claims.txt: %s does not count as a proof of %s: %s" % (t.full, h.full, why_not))
        return how

    def family(self, d, depth=0):
        """d and the structures that it extends."""
        m = re.search(
            "(?<![%s])extends(?![%s])(.*?)(?:%s|:=|$)" % (_REST, _REST, _WHERE.pattern),
            d.src.code[d.name_end : d.whole_end],
            re.S,
        )
        out = [d]
        for name in NAME.findall(outside_brackets(m.group(1))) if m and depth < 8 else ():
            found = resolve(self.index, d, name, set(), {}, Tally())
            if found and found[0].kind == "structure" and found[0] is not d:
                out += self.family(found[0], depth + 1)
        return out

    def line_start(self, src, at):
        """The start of the line if only blanks stand before 'at' on it, else 'at'."""
        start = src.text.rfind("\n", 0, at) + 1
        return start if not src.text[start:at].strip() else at

    def by_sign(self, text, label):
        """The margin word that the table in labels.txt gives for the first sign of a piece's code, or ''. 'text': the
        piece with its comments blanked."""
        words = text.split()
        while words and (words[0] in MODIFIERS or words[0].startswith("@[")):
            del words[0]
        for key, word in label.items():
            if key.startswith("sign ") and words:
                for sign in key[5:].split():
                    if words[0] == sign or (not in_name(sign[-1]) and words[0].startswith(sign)):
                        return word
        return ""

    def cuts(self, d, rows_text, label, margins):
        """((margin word, phrase or None) for the lines in force, [(start, end, margin word, phrase or None, doc comment
        or None)]). The ranges, joined, are the declaration's shown text."""
        src, out, above = d.src, [], ("", None)
        if rows_text is not None:
            marks, words, margin = [], None, None
            for l in rows_text.split("\n"):
                if l.startswith("# margin:"):
                    margin = as_typed(l[len("# margin:") :].strip(), "rows.txt, a margin word")
                elif l.startswith("#"):
                    continue
                elif l.startswith("@"):
                    words = []
                    marks.append((l[1:].strip(), margin, words))
                    margin = None
                elif l.strip():
                    if words is None:
                        rows_stop(d, "", "its rows begin with words, not with '@'")
                    words.append(as_typed(l.strip(), "rows.txt, a phrase", True))
            if marks and marks[0][0] == "^":
                above = (marks[0][1] or "", " ".join(marks[0][2]) or None)
                del marks[0]
            given = any(m[1] is not None for m in marks)  # do this card's rows give margin words at all?
            since, behind, places = d.start, d.start, []
            for k, (first, _, _) in enumerate(marks):
                at = anchor_at(src, first, behind, d.shown_end) if first else -1
                if at < 0 or (k == 0 and at != d.start):
                    rows_stop(d, "", NOT_FOUND % (first, src.path, src.line_of(d.start)))
                if k and not first.startswith(("/-", "--")):
                    places.append(self.line_start(src, with_comments(src, at, since, behind)))
                else:
                    places.append(self.line_start(src, at) if k else at)
                since, behind = at, at + len(first)
            for k, (_, margin, words) in enumerate(marks):
                end = places[k + 1] if k + 1 < len(places) else d.shown_end
                word = (margin or "") if given else self.by_sign(src.solid[places[k] : end], label)
                out.append((places[k], end, word, " ".join(words) or None, None))
        elif d.kind in ("structure", "class"):
            docs = [(s, e) for s, e, kind in src.spans_between(d.start, d.shown_end) if kind == "doc"]
            starts = [self.line_start(src, s) for s, _ in docs] + [d.shown_end]
            out.append((d.start, starts[0], self.by_sign(src.solid[d.start : starts[0]], label), None, None))
            for k, doc in enumerate(docs):
                field = NAME.search(src.code, doc[1], starts[k + 1])
                out.append((starts[k], starts[k + 1], margins.get(field.group(), "") if field else "", None, doc))
        else:
            out.append((d.start, d.shown_end, self.by_sign(src.solid[d.start : d.shown_end], label), None, None))
        if "".join(src.text[a:b] for a, b, _, _, _ in out) != src.text[d.start : d.shown_end]:
            stop(src.path, src.line_of(d.start), "the pieces of %s, joined, are not its text" % d.full)
        return above, out

    def pre(self, d, a, b, bound, types, own):
        refuse_unseen_characters(d.src, a, b)
        return '<pre data-from="%d" data-to="%d">%s</pre>' % (
            d.src.line_of(a),
            d.src.line_of(max(a, b - 1)),
            by_lines(self.source_html(d, a, b, bound, types, own), d.src.column_of(a)),
        )

    def card(self, d, status, title, remarks, rows_text, label, margins, with_doc):
        src = d.src
        lines, bound, types = self.reading(d)
        own = d.name_end - len(d.written) if d.written else None
        above, pieces = self.cuts(d, rows_text, label, margins)
        # with words somewhere: three columns throughout; with margin words alone: two; else the Lean alone
        shape = (
            "row"
            if above[1] or any(p[3] or p[4] for p in pieces)
            else "row wide" if above[0] or any(p[2] for p in pieces) else "row solo"
        )

        def row(margin, words, lean, cls=shape):
            return '<div class="%s">%s%s<div class="lean">%s</div></div>' % (
                cls,
                '<div class="role">%s</div>' % esc(margin) if not cls.startswith("row solo") else "",
                words if cls == "row" else "",
                lean,
            )

        say = lambda s: '<div class="say">%s</div>' % ("<p>%s</p>" % self.running_text(d, s, bound) if s else "")
        rows = []
        part_of_it = [(a, b) for a, b in lines if not src.code[a:b].startswith("attribute")]
        for a, b in lines:  # 'attribute ... in' lines: small, above the rows
            if (a, b) not in part_of_it:
                rows.append(row("", "", self.pre(d, a, b, bound, types, None), "row solo aside"))
        shown = sum(1 for a, b in lines for l in src.text[a:b].split("\n") if l.strip())
        if part_of_it:
            in_force = row(
                above[0], say(above[1]), "".join(self.pre(d, a, b, bound, types, None) for a, b in part_of_it)
            )
            # folded, if an earlier card of this section shows them: the same lines of the same file
            earlier = self.shown_above.setdefault((src.path, tuple(part_of_it)), d)
            if earlier is not d and "same-lines" in label:
                in_force = '<details class="above"><summary>%s</summary>%s</details>' % (
                    inline_html(label["same-lines"].replace("{name}", earlier.written or first_line(earlier))),
                    in_force,
                )
            rows.append(in_force)
        elif above != ("", None):
            rows_stop(d, "", "it has a row '@^', and no lines are in force there")
        for a, b, margin, phrase, doc in pieces:
            if doc:  # the field's own comment goes to the left; the Lean behind it to the right
                words = '<div class="say src">%s</div>' % self.comment_html(
                    d, src, doc[0] + 3, doc[1] - 2, bound, margin=src.column_of(doc[0])
                )
                a = doc[1] + 1 if src.text[doc[1] : doc[1] + 1] == "\n" else doc[1]
            else:
                words = say(phrase)
            rows.append(row(margin, words, self.pre(d, a, b, bound, types, own)))
            shown += sum(1 for l in src.text[a:b].split("\n") if l.strip())
        self.lines_on[id(d)] = shown
        remark = ""
        for l in remarks[:-1]:
            if l.startswith("(doc) "):  # a passage of the declaration's own doc comment: it must still stand there
                l = l[len("(doc) ") :]
                if not d.doc or " ".join(l.split()) not in " ".join(src.text[d.doc[0] + 3 : d.doc[1] - 2].split()):
                    raise Stop(
                        "remarks.txt: the doc comment of %s does not have this '(doc)' passage: %s" % (d.full, l)
                    )
            remark += "<li>%s</li>\n" % self.running_text(d, as_typed(l, "remarks.txt", True), bound)
        if remark:
            remark = "<ul>\n%s</ul>\n%s" % (
                remark,
                '<p class="where">%s</p>\n' % inline_html(remarks[-1]) if remarks[-1] else "",
            )
        name = esc(d.full).replace(".", ".<wbr>") if d.full else esc(first_line(d))
        first, last = src.line_of(d.start), src.line_of(d.shown_end - 1)
        return (
            '<article class="card st-%s" id="%s" data-file="%s" data-kind="%s">\n'
            '<p class="tag"><span class="kind">%s</span> <span class="w">%s:%s</span></p>\n'
            '<h3>%s</h3>\n%s<div class="rows">\n%s\n</div>\n%s'
            '<p class="full"><a class="r" href="#%s">%s</a>%s%s</p>\n</article>\n'
            % (
                status if status != "-" else "none",
                esc(d.ident),
                esc(src.path),
                d.kind,
                d.kind,
                esc(src.path),
                "%d–%d" % (first, last) if last > first else first,
                title,
                '<p class="doc">%s</p>\n' % self.first_sentence(d) if with_doc and d.doc else "",
                "\n".join(rows),
                '<div class="remark">\n%s</div>\n' % remark if remark else "",
                esc(d.ident),
                name,
                (
                    ' <a class="r" href="#%s">%s</a>' % (esc(d.ident), esc(label["comment"]))
                    if d.doc and "comment" in label
                    else ""
                ),
                self.status(d, status, label) if status != "-" else "",
            )
        )

    def status(self, d, status, label):
        """The word for a card's status; behind it, a link to the theorem that proves a hypothesis."""
        proof = self.proved_by.get(id(d))
        return ' <span class="status">%s%s</span>' % (
            esc(label[status]),
            " " + self.link(proof, esc(proof.written)) if proof else "",
        )

    def block(self, cls, d, a, b, bound, types, own_name_at=None):
        """As in the long page, but each line in a block of its own (by_lines)."""
        refuse_unseen_characters(d.src, a, b)
        first, last = d.src.line_of(a), d.src.line_of(b - 1)
        return '<div class="%s" data-from="%d" data-to="%d"><span class="ln">%s</span><pre>%s</pre></div>' % (
            cls,
            first,
            last,
            line_label(first, last),
            by_lines(self.source_html(d, a, b, bound, types, own_name_at)),
        )

    def first_sentence(self, d):
        """Of the doc comment, as running text: up to the first full stop that a blank follows."""
        if not d.doc:
            return ""
        words = " ".join(d.src.text[d.doc[0] + 3 : d.doc[1] - 2].split())
        stop_at = re.search(r"\.\**(?= )", words)
        return self.running_text(d, words[: stop_at.end()] if stop_at else words, set())

    def reach(self, d):
        """Every declaration that d's Lean text names, or that the text of one so found names, as long as it has an
        entry on the long page; and the full names met on the way that have none."""
        seen, unshown, todo = {}, set(), [d]
        while todo:
            at = todo.pop()
            for full, target in at.src.names_of.get(id(at), ()):
                if id(target) in self.has_entry:
                    if id(target) not in seen and target is not d:
                        seen[id(target)] = target
                        todo.append(target)
                else:
                    unshown.add(full)
        return list(seen.values()), unshown


def first_line(d):
    """Of a nameless declaration: its first line, without a closing 'where'."""
    return re.sub(r"\s+where$", "", d.src.text[d.start : d.shown_end].split("\n")[0].rstrip())


def short_page(root, heads, long_page, entries, long_name, say):
    folder = os.path.join(heads, "short")
    label = dict(short_table(folder, "labels.txt", 2, True))
    for key in STATUSES + ("title", "how-much", "reach", "index", "index-words", "all", "legend", "contents", "back"):
        if key not in label and key != "proved-under":  # that one is needed where claims.txt uses it: see below
            raise Stop("%s: no line for '%s'" % (os.path.join(folder, "labels.txt"), key))
    for key in STATUSES + ("title", "index", "contents", "all", "back", "comment", "no-status"):
        as_typed(label.get(key, ""), "labels.txt, '%s'" % key)
    if label["title"].endswith(TITLE_ENDS):  # by the title main() tells the two pages apart before it replaces a file
        raise Stop(
            "%s: the short page's title must not end with '%s', as the long page's does"
            % (os.path.join(folder, "labels.txt"), TITLE_ENDS)
        )
    titles, remarks = dict(short_table(folder, "titles.txt", 2)), {}
    for name, words in short_table(folder, "remarks.txt", 2):
        remarks.setdefault(name, []).append(words)
    remarks_link = label.get("remarks-link", "")
    rows_of, fields_of, at = {}, {}, None  # rows.txt: '=== FULL.NAME', then that card's rows; '% field | margin word'
    for l in (small_text(os.path.join(folder, "rows.txt"), 1000000) or "").split("\n"):
        if l.startswith("==="):
            at = l[3:].strip()
            if at in rows_of:
                raise Stop("rows.txt has '=== %s' twice" % at)
            rows_of[at], fields_of[at] = [], {}
        elif l.startswith("%") and at:
            field, _, word = l[1:].partition("|")
            fields_of[at][field.strip()] = as_typed(word.strip(), "rows.txt, a margin word")
        elif at:
            rows_of[at].append(l)
        elif l.strip() and not l.startswith("#"):
            raise Stop("rows.txt begins with something else than a remark or '=== FULL.NAME'")
    if any(c in l for ls in rows_of.values() for l in ls if not l.startswith("@") for c in "⟨⟩‹›"):  # '@': Lean text
        raise Stop("rows.txt still has a place to fill in, marked ⟨ ⟩ or ‹ ›")
    page = ShortPage(long_page, long_name)
    LONG_NAME[0] = long_name
    FILLED.clear()
    audited = small_text(os.path.join(root, *AUDITED.split("/")), 20000000) or ""
    audited = {l.split()[0] for l in audited.split("\n") if l.strip() and not l.startswith("#")}

    def declaration(name):
        """By its id on the long page; one that has no entry there, by its full name."""
        if name in entries:
            return entries[name]
        fit = page.index.public.get(name, ())
        if len(fit) != 1:
            raise Stop("claims.txt names %s: %d declarations of the Lean files have that full name" % (name, len(fit)))
        d = fit[0]
        d.ident, d.part = d.full, "other"
        page.collecting = True
        d.src.names_of[id(d)], bound = page.entry(d)
        page.collecting = False
        if not hasattr(d.src, "bound_in_file"):
            d.src.bound_in_file = set(bound)
        return d

    def with_name(name, line):
        d = declaration(name)
        if not d.full:
            raise Stop("%s: a declaration without a name can have a card and nothing else" % line)
        return d

    also_indexed = []  # '+ FULL.NAME': a line in the index, though no card's Lean text names it
    typed = []  # the hypotheses: (declaration, status in claims.txt, status on the page)
    assumed = [
        m.group(1)
        for m in map(re.compile(r"([^\s|>]+)\s*\|\s*assumed\b").match, short_lines(folder, "claims.txt"))
        if m
    ]
    # [title, opening lines, [(declaration, status, more); [kind, what]: a line that counts; a line of words]]
    sections = []
    for l in short_lines(folder, "claims.txt", True):
        if l.startswith("=="):
            title = as_typed(l[2:].lstrip("-").strip(), "claims.txt, a section's title")
            sections.append([title, [], [], l.startswith("==-")])  # '==-': its cards are folded
        elif not sections:
            raise Stop("claims.txt: its first line must open a section: '== title'")
        elif l.startswith(">"):  # under the title; behind a card: a line of words at that place
            (sections[-1][2] if sections[-1][2] else sections[-1][1]).append(l[1:].strip())
        elif l.startswith(("! reach ", "! hypotheses ")):
            sections[-1][2].append([l.split()[1], with_name(l.split(None, 2)[2].strip(), "claims.txt: " + l)])
        elif l.startswith("! folder "):
            sections[-1][2].append(["folder", l[len("! folder ") :].strip()])
        elif l.startswith("+ "):
            also_indexed.append(with_name(l[2:].strip(), "claims.txt: " + l))
        else:
            name, status, *more = [c.strip() for c in l.split("|")] + [""][: "|" not in l]
            by = [m[3:].strip() for m in more if m.startswith("by ")]
            if (
                status not in STATUSES + ("-",) + HYPOTHESIS[:3]
                or len(more) != len(set(more))
                or len(by) + ("at-risk" in more) > (status in HYPOTHESIS[1:3])
                or any(m not in ("doc", "at-risk") and not m.startswith("by ") for m in more)
            ):
                raise Stop(
                    "claims.txt: a card is 'FULL.NAME | status', with '| doc' behind it if wanted. The status is '-', "
                    "%s, assumed, hypothesis or arithmetic; behind the last two, '| by THEOREM' or '| at-risk' may "
                    "stand: %s" % (", ".join(STATUSES), l)
                )
            d = declaration(name)
            for_definitions = ("definition", "only-defined") + HYPOTHESIS[:3]
            if status in (for_definitions if d.kind in CUT_BEFORE_PROOF else FOR_THEOREMS) or (
                status in FOR_THEOREMS and d.kind == "example"
            ):
                raise Stop(
                    "claims.txt: 'proved' and 'proved-under' are for a theorem or lemma alone; %s are for no theorem, "
                    "lemma or example; this is a %s: %s" % (", ".join(for_definitions), d.kind, l)
                )
            if status in FOR_THEOREMS and d.full not in audited:
                raise Stop("claims.txt calls %s %s, and %s has no line for it" % (d.full, status, AUDITED))
            how = "hypothesis-at-risk" if "at-risk" in more else status
            if by:
                page.proved_by[id(d)] = with_name(by[0], "claims.txt: " + l)
                how = page.proved_how(d, page.proved_by[id(d)], audited, [declaration(a) for a in assumed])
            if status in HYPOTHESIS:
                typed.append((d, status, how))
            sections[-1][2].append((d, how, "doc" if "doc" in more else ""))
    cards = [m[0] for s in sections for m in s[2] if isinstance(m, tuple)]
    with_card = {id(d) for d in cards}
    twice = sorted({d.ident for d in cards if sum(x is d for x in cards) > 1})
    if twice or not cards:
        raise Stop("claims.txt has two cards for %s" % ", ".join(twice) if twice else "claims.txt has no card")
    named = {}
    for d in cards:  # what the cards' Lean texts link to, in the order of first appearance
        for _, target in d.src.names_of.get(id(d), ()):
            if id(target) in page.has_entry and id(target) not in with_card:
                named.setdefault(id(target), target)
    for d in also_indexed:
        if id(d) in with_card:
            raise Stop("claims.txt: '+ %s': it has a card" % d.full)
        named.setdefault(id(d), d)
    for d in page.proved_by.values():  # a theorem that proves a hypothesis has a card, or a line in the index
        if id(d) not in with_card:
            named.setdefault(id(d), d)
    page.here = with_card | set(named)
    for key in HYPOTHESIS + ("proved-under",):
        if any(isinstance(m, tuple) and m[1] == key for s in sections for m in s[2]):
            if key not in label:
                raise Stop("%s: no line for '%s'" % (os.path.join(folder, "labels.txt"), key))
            as_typed(label[key], "labels.txt, '%s'" % key)

    def counts(some, behind=""):
        """The places for the counts of these hypotheses [(declaration, status in claims.txt, status on the page)]."""
        out = {"{all%s}" % behind: len(some), "{assumed%s}" % behind: sum(1 for h in some if h[1] == "assumed")}
        for key, front in (("hypothesis", "{"), ("arithmetic", "{arithmetic-")):
            now = [h[2] for h in some if h[1] == key]
            for place, status in zip(("proved", "proved-under", "at-risk"), HYPOTHESIS[3:]):
                out[front + place + behind + "}"] = now.count(status)
            out[front + "named" + behind + "}"] = len(now)
            out[front + "open" + behind + "}"] = now.count(key) + now.count("hypothesis-at-risk")
        return {place: str(number) for place, number in out.items()}

    # '! hypotheses S': S's hypotheses are the cards so called that its Lean text names. The counts without a name
    # behind them are those of the first S; '{named S}' and so on are those of S, by its short name
    holders = [m[1] for s in sections for m in s[2] if isinstance(m, list) and m[0] == "hypotheses"]
    of_holder, fields_of_holder = {}, {}
    FILLED.update(counts(typed))
    for holder in reversed(holders):
        family = page.family(holder)  # with the structures that it extends: their fields are its fields
        for d in family:
            if id(d) not in d.src.names_of:
                raise Stop("claims.txt: '! hypotheses %s': it extends %s: give that a card" % (holder.full, d.full))
        its_names = {id(target) for d in family for _, target in d.src.names_of[id(d)]}
        own = of_holder[id(holder)] = [h for h in typed if id(h[0]) in its_names]
        fields = sum(len(d.members) - 1 for d in family) if holder.kind == "structure" else len(own)
        fields_of_holder[id(holder)] = fields
        if own and fields != len(own):
            raise Stop(
                "claims.txt: '! hypotheses %s': it has %d fields, and %d of the cards called assumed, hypothesis or "
                "arithmetic are named in its Lean text: there must be one for each field, or none"
                % (holder.full, fields, len(own))
            )
        for behind in (" " + holder.written, ""):
            FILLED.update(counts(own, behind))
            if not own:  # no card for any of them: its fields are the hypotheses, all open
                for place in ("all", "named", "open"):
                    FILLED["{%s%s}" % (place, behind)] = str(fields)
    left_out = [h[0].full for h in typed if holders and not any(h in own for own in of_holder.values())]
    if left_out:
        raise Stop(
            "claims.txt: no declaration behind '! hypotheses' names these in its Lean text: %s" % ", ".join(left_out)
        )
    body, contents = [], []
    for k, (title, opening, members, folded) in enumerate(sections, 1):
        pieces, page.shown_above = [], {}
        for m in members:
            if isinstance(m, str):
                pieces.append('<p class="open">%s</p>\n' % inline_html(m))
                continue
            if not isinstance(m, tuple):  # a line that this program counts
                if m[0] not in label:
                    raise Stop("%s: no line for '%s'" % (os.path.join(folder, "labels.txt"), m[0]))
                if m[0] == "reach":
                    further, unshown = page.reach(m[1])
                    counted = {"declarations": len(further), "unshown": len(unshown)}
                    counted.update(name=m[1].full, files=len({t.src.path for t in further}))
                elif m[0] == "folder":
                    paths = {p for p in page.index.lines if p.startswith(m[1] + "/")}
                    if not paths:
                        raise Stop("claims.txt: '! folder %s': no Lean file lies in such a folder" % m[1])
                    every = [d for ds in page.index.public.values() for d in ds] + list(page.index.private.values())
                    counted = {"folder": m[1], "files": len(paths), "lines": sum(page.index.lines[p] for p in paths)}
                    counted["declarations"] = sum(1 for d in every if d.src.path in paths)
                else:
                    counted = {"name": m[1].full, "fields": fields_of_holder[id(m[1])]}
                    for place, number in FILLED.items():  # in its own line the plain places are its own counts
                        if place.endswith(" %s}" % m[1].written):
                            counted[place[1 : -len(m[1].written) - 2]] = number
                words = label[m[0]]
                for key, value in counted.items():
                    words = words.replace("{%s}" % key, str(value))
                pieces.append('<p class="reach">%s</p>\n' % inline_html(words))
                if m[0] == "hypotheses":  # and one line for each hypothesis: its name, its status, its first sentence
                    pieces[-1] = '<div class="holes">\n%s<ul>\n%s</ul>\n</div>\n' % (
                        pieces[-1],
                        "".join(
                            '<li class="st-%s"><a class="r" href="#%s">%s</a>%s <span class="first">%s</span></li>\n'
                            % (how, esc(d.ident), esc(d.written), page.status(d, how, label), page.first_sentence(d))
                            for d, _, how in of_holder[id(m[1])]
                        ),
                    )
                continue
            d, status, more = m
            rows_text = "\n".join(rows_of.get(d.full, ()))
            rows_text = rows_text if any(l.startswith("@") for l in rows_of.get(d.full, ())) else None
            lay = titles.get(d.full) or titles.get(d.ident)
            pieces.append(
                page.card(
                    d,
                    status,
                    inline_html(lay) if lay else "<code>%s</code>" % esc(d.written or first_line(d)),
                    remarks.get(d.full, []) + [remarks_link],
                    rows_text,
                    label,
                    fields_of.get(d.full, {}),
                    more == "doc",
                )
            )
        if folded:
            if "folded" not in label:
                raise Stop("%s: no line for 'folded'" % os.path.join(folder, "labels.txt"))
            words = label["folded"].replace("{cards}", str(sum(isinstance(m, tuple) for m in members)))
            pieces = (
                ['<details class="part">\n<summary>%s</summary>\n' % inline_html(words)] + pieces + ["</details>\n"]
            )
        body.append(
            '<section id="s%d">\n<h2><span class="no">%d</span> %s</h2>\n%s%s</section>\n'
            % (k, k, esc(title), "".join('<p class="open">%s</p>\n' % inline_html(l) for l in opening), "".join(pieces))
        )
        contents.append('<a href="#s%d">%d %s</a>' % (k, k, esc(title)))
    by_file = {}
    for d in sorted(named.values(), key=lambda d: (d.src.path, d.start)):
        by_file.setdefault(d.src.path, []).append(d)
    index_html = "".join(
        '<p class="path">%s</p>\n<ul>\n%s</ul>\n'
        % (
            esc(p),
            "".join(
                '<li id="%s"><span class="kind">%s</span> <a class="r" href="#%s">%s</a> <span class="w">%d</span> '
                '<span class="first">%s</span>%s</li>\n'
                % (
                    esc(d.ident),
                    d.kind,
                    esc(d.ident),
                    esc(d.full),
                    d.src.line_of(d.start),
                    page.first_sentence(d),
                    (
                        ' <a class="x" href="%s#%s"%s>%s</a>'
                        % (esc(long_name), esc(d.ident), LEAVES, esc(label["all"]))
                        if id(d) in page.has_entry
                        else ""
                    ),
                )
                for d in ds
            ),
        )
        for p, ds in by_file.items()
    )
    k = len(sections) + 1
    body.append(
        '<section id="s%d">\n<h2><span class="no">%d</span> %s</h2>\n<p class="open">%s</p>\n<div '
        'class="index">\n%s</div>\n'
        "</section>\n" % (k, k, esc(label["index"]), inline_html(label["index-words"]), index_html)
    )
    contents.append('<a href="#s%d">%d %s</a>' % (k, k, esc(label["index"])))
    store = []
    for d in cards + list(named.values()):
        e = page.entry(d)
        marker = '<article class="e" id="%s"' % esc(d.ident)
        if not e.startswith(marker):
            raise Stop("%s: its entry does not begin as expected" % d.ident)
        store.append('<article class="e" id="e:%s"' % esc(d.ident) + e[len(marker) :])
    head = [label["title"]] + short_lines(folder, "short-head.txt")
    tiles = []
    for l in short_lines(folder, "tiles.txt"):
        cells = [c.strip() for c in l.lstrip("+").split("|")]
        if l.startswith("+") and tiles and len(cells) == 2:
            tiles[-1][3].append(cells)
        elif not l.startswith("+") and len(cells) == 3:
            tiles.append(cells + [[]])
        else:
            raise Stop("tiles.txt: neither 'title | words | full name' nor, under a tile, '+ slot | words': %s" % l)
        as_typed(cells[0], "tiles.txt, a tile's title or a slot's name")
        as_typed(cells[1], "tiles.txt, a tile's words", True)
    for tile in tiles:
        if id(with_name(tile[2], "tiles.txt: the tile '%s'" % tile[0])) not in with_card:
            raise Stop("tiles.txt: the tile '%s' leads to %s, which has no card" % (tile[0], tile[2]))
    tiles = "".join(
        '<a class="tile" href="#%s"><span class="t">%s</span> <span class="status">%s</span>%s '
        '<span class="slot"><code>%s</code></span></a>\n'
        % (
            esc(declaration(name).ident),
            esc(title),
            inline_html(words),
            "".join(
                ' <span class="slot"><span class="sw">%s</span> %s</span>' % (esc(s), inline_html(w)) for s, w in slots
            ),
            esc(declaration(name).written),
        )
        for title, words, name, slots in tiles
    )
    lean_lines = lambda ds: sum(page.lines_on[id(d)] for d in ds)
    first = [m[0] for m in sections[0][2] if isinstance(m, tuple)]
    called = [m[1] for s in sections for m in s[2] if isinstance(m, tuple)]  # each card's status
    how_much = (
        label["how-much"]
        .replace("{cards}", str(len(cards)))
        .replace("{lines}", str(lean_lines(cards)))
        .replace("{cards1}", str(len(first)))
        .replace("{lines1}", str(lean_lines(first)))
        .replace("{theorems}", str(sum(s in FOR_THEOREMS for s in called)))
        .replace("{theorems-under}", str(called.count("proved-under")))
    )
    guide, in_list = [], False
    for l in short_lines(folder, "short-guide.txt") + [""]:
        bullet = l.startswith("- ")
        if bullet != in_list:
            guide.append("<ul>\n" if bullet else "</ul>\n")
            in_list = bullet
        if l:
            guide.append(
                ("<li>%s</li>\n" if bullet else "<p>%s</p>\n") % inline_html(l[2 * bullet :].replace("\x00", how_much))
            )
    guide = '<div class="guide">\n%s</div>\n' % "".join(guide) if guide else ""
    if guide and "guide" in label:
        guide = '<details class="fold">\n<summary>%s</summary>\n%s</details>\n' % (inline_html(label["guide"]), guide)
    used = [
        s for s in STATUSES + HYPOTHESIS if any(isinstance(m, tuple) and m[1] == s for sec in sections for m in sec[2])
    ]
    samples = " ".join('<span class="sample st-%s"></span> %s' % (s, esc(label[s])) for s in used)
    if "no-status" in label and any(isinstance(m, tuple) and m[1] == "-" for sec in sections for m in sec[2]):
        samples += ' <span class="sample st-none"></span> %s' % esc(label["no-status"])
    first_print = "".join(
        '<p class="print">%s</p>\n' % inline_html(l) for l in short_lines(folder, "first-print-mark.txt")
    )
    style = STYLE_SHORT + "".join(
        ".i%d { padding-left: %dch; text-indent: -%dch; }\n" % (n, n + 8, n + 8) for n in range(41)
    )
    # a piece cut in mid-line begins at its own column, but never so far to the right that it has no room
    style += "".join(".o%d { margin-left: min(%dch, 30%%); }\n" % (n, n) for n in range(1, 101))
    title = head[0]
    document = (
        '<!DOCTYPE html>\n<!--\n%s\n-->\n<html lang="en">\n<head>\n<meta charset="utf-8">\n'
        '<meta name="viewport" content="width=device-width, initial-scale=1">\n'
        '<meta http-equiv="Content-Security-Policy" content="default-src \'none\'; '
        "style-src 'sha256-%s'; script-src 'sha256-%s'; base-uri 'none'; form-action 'none'\">\n"
        '<title>%s</title>\n<style>%s</style>\n</head>\n<body>\n<div id="column">\n<header>\n%s<h1>%s</h1>\n%s'
        '<nav id="contents" aria-label="%s">\n<p>%s</p>\n</nav>\n%s%s<p class="legend">%s</p>\n'
        '<p class="legend">%s</p>\n</header>\n<main>\n%s</main>\n</div>\n'
        '<a class="top" href="#contents" aria-label="%s">↑</a>\n<div id="store" hidden>\n%s</div>\n'
        '<aside id="panel" aria-label="%s" hidden>\n<p class="bar"><button type="button" id="panel-back">%s</button> '
        '<a id="panel-go" href="#s1">%s</a> <button type="button" id="panel-close">%s</button></p>\n'
        '<div id="panel-body"></div>\n</aside>\n<script>%s</script>\n</body>\n</html>\n'
        % (
            LICENCE,
            sha256_base64(style),
            sha256_base64(SCRIPT_SHORT),
            esc(title),
            style,
            first_print,
            esc(title),
            '<div class="tiles">\n%s</div>\n' % tiles if tiles else "",
            esc(label["contents"]),
            " · ".join(contents),
            "".join('<p class="lead">%s</p>\n' % inline_html(l) for l in head[1:]),
            guide,
            samples,
            inline_html(label["legend"]),
            "".join(body),
            esc(label["contents"]),
            "".join(store),
            T_PANEL,
            T_BACK,
            T_GO,
            T_CLOSE,
            SCRIPT_SHORT,
        )
    )
    say(
        "the short page: %d sections, %d cards with %d lines of Lean, %d lines in its index, %d entries kept for the "
        "hover card and the side panel" % (len(sections), len(cards), lean_lines(cards), len(named), len(store))
    )
    say(
        "the short page: cards and index lines of declarations that have no entry on the long page: %s"
        % (", ".join(d.full for d in cards + list(named.values()) if id(d) not in page.has_entry) or "none")
    )
    for what, names in (("remarks.txt", remarks), ("titles.txt", titles)):
        idle = sorted(set(names) - {d.full for d in cards} - {d.ident for d in cards})
        say(
            "the short page: %s has words for %d names that have no card: %s"
            % (what, len(idle), ", ".join(idle) or "none")
        )
    idle = sorted(set(rows_of) - {d.full for d in cards})
    say("the short page: rows.txt has rows for %d names that have no card: %s" % (len(idle), ", ".join(idle) or "none"))
    silent = [m[0].ident for s in sections for m in s[2] if isinstance(m, tuple) and m[2] == "doc" and not m[0].doc]
    say(
        "the short page: 'doc' is asked of %d cards that have no doc comment: %s"
        % (len(silent), ", ".join(silent) or "none")
    )
    say("the short page: sha256 of the style, for the checker: %s" % hashlib.sha256(style.encode("utf-8")).hexdigest())
    say(
        "the short page: sha256 of the script, for the checker: %s"
        % hashlib.sha256(SCRIPT_SHORT.encode("utf-8")).hexdigest()
    )
    say(
        "the short page: links to a place on it: %d ; to the long page: %d"
        % (document.count('<a class="r"'), document.count('<a class="x"'))
    )
    return document


# ------------------------------------------------------------------------------------------------
# 7. The front page, in the form of the shell: statements in rows; the Lean text held once, as data
# ------------------------------------------------------------------------------------------------
# The frame, the style sheet and the script of this form are data: three files in the folder shell/ among the head
# texts, laid into the page as they are, but for the lines of the script that turns.txt there replaces (ORIGIN.txt
# beside them says what they are). What stands on the page is data too: the files of the folder front/. This
# program writes the body's markup as the shell's frame has it (its elements, their order, their class names: the
# sheet and the script expect them; ORIGIN.txt says so too), and adds the Lean text and what follows from it: each
# card's place, its pieces of Lean, the block of data from which the script paints colours, links, the hover cards and
# the side panel. It keeps the page's lines short (in_pieces, block_text and in_lines, before front_page, say how).
#   claims.txt   '== title | id' a section, '=== title | id' a sub-section (an id of its own: none of the frame's, and
#                not like a limit's, 'lim-', or a card's, 'card-'). Under it: '! pill STATE | words' (target,
#                cond, full, none: at the section's head and in the contents); '!> words', '!- bullet': the block under
#                the pill; '> words', '- bullet', '-- bullet': words, where they stand; '+ label': a small label, the
#                bullets under it are its notes; 'FULL.NAME | status' a card; '! table NAME' the table of NAME.txt
#                (tabs between cells, the first line its head row; a cell 'chip: ...' is a chip, as in rows.txt);
#                '! fold Title' ... '! fold-end': what stands between them is folded away until the reader opens it;
#                '! definitions' the list of the definitions that the cards name, each with the first sentence of its
#                doc comment ('! definitions titled': with its line of titles.txt instead, or nothing); '! limits'
#                the limits of limits.txt; '! closing' closing.txt; '! notes' a list, made by this program, of the cards
#                whose declaration has a card on the short page, each with a link to it there (such a card has that
#                link in its foot too, under the label note-link); '! box KIND | title' (proved, assumed, outside) and
#                its bullets: a box; boxes in a run stand together. '! whole FULL.NAME': all that this declaration's
#                text reaches is embedded, definitions followed; where a name fits two declarations, so that rule 2
#                makes no link, both are embedded and followed. Else only the cards are embedded and what their own
#                texts name. '! also FULL.NAME': this one as well.
#                A card's status: definition, target, proved (a theorem or lemma with a line in the audit's list and no
#                'sorry', 'sorryAx' or 'admit' written in its proof), proved-under (the same, and the data's writers say
#                that it rests on hypotheses), hypothesis WORD (HYPOTHESIS_WORDS). Behind the three words with the
#                bright chip (BRIGHT) stand the full names of theorems that pass the same test: 'hypothesis proved
#                FULL.NAME ...'; whether they prove it is not held; the chip's tooltip (tip-STATUS) ends with their
#                names. A target's card may have chip words of its own: 'FULL.NAME | target | words', and 'FULL.NAME |
#                target THEOREM ... | words' if these words speak of a proof (SAYS_CHECKED). An axiom and a private
#                declaration can have no card.
#   titles.txt   'FULL.NAME | title': every card has one
#   rows.txt     '=== FULL.NAME' opens a card's rows. A row: '# margin: word' and '# chip: FULL.NAME' (that card's chip,
#                at the end of the row's words) or '# chip: = status' (as in claims.txt, but not proved, proved-under;
#                both lines optional), '@ characters at which the piece begins', then the words' lines. '@^' is the
#                row of the lines in force above the declaration. Where a piece begins: as on the short page (above).
#                Rows, and remarks, only for names that have a card.
#   remarks.txt  'FULL.NAME | words', '| - bullet', '| [Label] words' (a new block under that label), '| limits 3 7'
#   tiles.txt    'title | STATE | status words | #id', under it '+ slot | words' or '+ slot | - bullet'
#   legend.txt   'colour | Word | sentence' (a card's colour, or chip-std, chip-other)
#   setting.txt, closing.txt  words   limits.txt  'n | words'; 'n | more | title': the lines of limit n that follow are
#                folded away under that title until the reader opens it (at most once in a limit; behind at least one of
#                its lines; at least one line follows; the title takes no backticks and no links)
#   labels.txt   'key | words'. Optional: 'group-TOP | words', the title of the group TOP in the list of definitions
#                (else TOP itself); 'contents-depth | sections', no sub-sections in the contents.
#                In definitions-count: {definitions}, {files}, and {s:definitions}, {s:files}: an 's'
#                unless that number is 1. In fold-count, which a fold with cards needs: {cards}, {s:cards}. The words
#                type-STATUS and chip-STATUS of a status that is not held as above may not speak of a proof.
#                Optional: 'back-to | NAME.html': the line at the long page's top leads to that page and not to this
#                front page. So two front pages, each with its own data folder, can share one long page, if the head
#                texts and the label 'back' are the same in both folders.
# In words: backticks hold code, and a name in them that the rules of part 3 find, read at the card's declaration, and
# that is embedded on the page, can be hovered and clicked; **bold** (code in it is plain code); [words](#id),
# [words](X.md), [words](long-page), [words](notes-page) are links. A mark without its fellow stops the run. A line of
# words that begins 'quote X.md | ' is printed without that mark, and only if its words stand in the Lean folder's page
# X.md, word for word, in one run. A line of words has at most LONGEST_LINE characters. Numbers that this program
# counts: {cards}, {rows}, {embedded}, {embedded-files}, {links}; {lean-files} and {lean-files FOLDER}; {lines FILE};
# {reach NAME}, {reach-lines NAME}, {reach-files NAME}: the declaration and all the definitions that its text reaches,
# their lines with doc comments, their files; {reach-cards NAME}, {reach-card-lines NAME}: those of them that have a
# card. Only statements and definitions are embedded: a theorem's text ends where its statement ends, in mid-line if
# need be.

SHELL = ("page_template.html", "page.css", "page.js", "turns.txt")
PILLS = ("target", "cond", "full", "none")
BOXES = ("proved", "assumed", "outside")
COLOURS = ("def", "class", "thm", "lem", "chk")  # the sheet's five kinds of card
CHIPS = ("chip-std", "chip-other")  # and the two kinds of chip that this page uses
CARD_COLOUR = {"definition": "def", "target": "class", "proved": "thm", "proved-under": "lem", "hypothesis": "chk"}
HYPOTHESIS_WORDS = ("by-definition", "by-construction", "proved", "ours", "open", "at-risk", "accepted", "names")
BRIGHT = ("proved", "by-definition", "by-construction")  # a hypothesis's words that bear the chip of what Lean checked
FOLLOWED = ("def", "abbrev", "structure", "class", "inductive", "instance", "opaque")  # their text is embedded whole
SAYS_CHECKED = re.compile(
    r"(?i)(?<!\bnot )\bproved\b|\b(?:theorems?|lemmas?|thm|checked|proven|verified|certified|qed)\b"
)  # a list of words cannot close this: what the words of a status say is the data's
MOST_EMBEDDED = 40000  # lines of Lean on one page
LONGEST_LINE = 6000  # characters in a line of words: the search for marks takes time by the square of it
BARE_OPENERS = (":=", ":= by", "where")  # what may stand behind a statement on its last line and be embedded with it
FRONT_LABELS = (
    "brand title html-title description subtitle byline tiles-title tiles-note rows-words rows-lean remark limits-link "
    "appendix search-hint definitions-count back"
).split()
_ID = r"[a-z][a-z0-9-]*"


def group_title(label, top):
    """The title of one group in the list of definitions. top is the first part of the files' path: a folder's name,
    or the name of a file that lies in no folder. The line 'group-TOP | words' of labels.txt gives the title. Without
    that line, or with no words in it, the title is top itself."""
    return label.get("group-" + top) or top


def idle_group_lines(label, tops):
    """The lines 'group-TOP | words' of labels.txt whose TOP is no group of the list of definitions: a slip of the pen
    or a folder that has gone. The page would keep a folder's name in silence, so the program stops at one."""
    return sorted(key for key in label if key.startswith("group-") and key[len("group-") :] not in tops)


def in_contents(label, level):
    """Whether a section of that level gets a line in the contents. Every section does, unless labels.txt has the line
    'contents-depth | sections': then the sub-sections (level 3) get none. No other word may stand in that line."""
    depth = label.get("contents-depth")
    if depth not in (None, "sections"):
        raise Stop("front/labels.txt: 'contents-depth | sections', or no such line: %s" % depth)
    return level != 3 or depth is None


QUOTE = re.compile(r"quote ((?:[A-Za-z]+/)*[A-Z][A-Z-]*\.md) \|(?: |$)")
COUNTED = re.compile(  # places in words that this program fills with a number that it counts
    r"\{(cards|rows|embedded|embedded-files|links|lean-files|l"
    r"ines|reach|reach-lines|reach-files|reach-cards|reach-card-lines)"
    r"(?: ([A-Za-z0-9_./']+))?\}"
)


def front_lines(folder, name, needed=False):
    """The lines of a text in front/, without blank lines and remarks."""
    text = small_text(os.path.join(folder, name), 400000)
    if text is None:
        if needed:
            raise Stop("%s: there is no such file" % os.path.join(folder, name))
        return []
    lines = [l.strip() for l in text.split("\n") if l.strip() and not l.startswith("#")]
    if any(len(l) > 20000 for l in lines):
        raise Stop("%s: a line of more than 20000 characters" % os.path.join(folder, name))
    return lines


def front_table(folder, name, columns, needed=False):
    rows = []
    for l in front_lines(folder, name, needed):
        cells = [c.strip() for c in l.split("|", columns - 1)]
        if len(cells) != columns:
            raise Stop("%s: this line has not %d parts between bars: %s" % (os.path.join(folder, name), columns, l))
        rows.append(cells)
    return rows


def turned_script(script, turns, where):
    """page.js with the lines that turns.txt names replaced: '- ' a whole line, which stands there once, '+ ' its
    successor."""
    lines, old = script.split("\n"), None
    for l in turns.split("\n"):
        if l.startswith("- ") and old is None:
            old = l[2:]
        elif l.startswith("+ ") and old is not None:
            if lines.count(old) != 1:
                raise Stop("%s: this line stands %d times in page.js, not once: %s" % (where, lines.count(old), old))
            lines[lines.index(old)], old = l[2:], None
        elif l.strip() and not l.startswith("#"):
            raise Stop("%s: '- ' and '+ ' lines by turns, and remarks behind '#': %s" % (where, l))
    if old is not None:
        raise Stop("%s: its last '- ' line has no '+ ' line" % where)
    return "\n".join(lines)


def units(line, column):
    """A column as the script counts it: in UTF-16 units."""
    return len(line[:column].encode("utf-16-le")) // 2


class FrontPage(ShortPage):
    """Names in words become hover links to what is embedded; names in Lean text are collected as places."""

    def __init__(self, long_page, long_name):
        ShortPage.__init__(self, long_page, long_name)
        self.embedded = {}  # id -> declaration, in the order in which they were met
        self.cards = []  # the declarations that have a card
        self.root, self.quotable = None, {}  # the Lean folder; its pages that the data quote, blanks folded
        self.unlinked = []  # code in words in which no name is a link: told at the end, for the words' writers
        self.whole = True

    def link(self, target, words):
        if id(target) in self.embedded:
            return '<span class="name-link" data-name="%s">%s</span>' % (esc(target.ident), words)
        return None

    def mark(self, d, name, bound, types, in_comment=False, after_bracket=False, first_in_bracket=None):
        return Page.mark(self, d, name, bound, types, in_comment, after_bracket, first_in_bracket)

    def find(self, d, name, bound, types, in_comment, after_bracket, first_in_bracket=None):
        """As on the other pages. In words one rule more, the last: a name that the rules resolve to nothing, and that
        is not bound, means the one card whose declaration's full name ends in it, if there is just one."""
        found = Page.find(self, d, name, bound, types, in_comment, after_bracket, first_in_bracket)
        if found or not in_comment or len(name) <= 2 or parts_of(name)[0] in bound:
            return found
        fit = [t for t in self.cards if t.full and ("." + t.full).endswith("." + name)]
        return (fit[0], 0, len(parts_of(name)), "in words: the only card whose name ends so") if len(fit) == 1 else None

    def code_html(self, d, s, bound, types, own_name_at=None, base=0, in_comment=False, floor=None):
        """As on the other pages. In words, what stands between double quotes is a string: no name in it is a link."""
        if not in_comment:
            return Page.code_html(self, d, s, bound, types, own_name_at, base, in_comment, floor)
        out, i = [], 0
        for m in re.finditer(r'"[^"]*"', s):
            out += [Page.code_html(self, d, s[i : m.start()], bound, types, in_comment=True), esc(m.group())]
            i = m.end()
        return "".join(out) + Page.code_html(self, d, s[i:], bound, types, in_comment=True)

    def first_sentence(self, d):
        """Of the doc comment, as running text: up to the first full stop outside code that a blank follows."""
        if not d.doc:
            return ""
        words = " ".join(d.src.text[d.doc[0] + 3 : d.doc[1] - 2].split())
        end, in_code = len(words), False
        for m in re.finditer(r"%s|\.\**(?= )" % BACKTICK, words):
            if m.group() == BACKTICK:
                in_code = not in_code
            elif not in_code:
                end = m.end()
                break
        return self.running_text(d, words[:end], set())

    # -- words ------------------------------------------------------------------------------------
    def plain(self, s, l):
        """A stretch of words between two marks: it holds no half of a mark."""
        if BACKTICK in s or "**" in s or "](" in s:
            raise Stop("a backtick, '**' or '](' without its fellow, or one mark inside another: %s" % l)
        return esc(s)

    def quoted(self, name, words):
        """words, which the data give as a quotation of a page in the Lean folder: they must stand there, in one run."""
        if name not in self.quotable:
            text = small_text(os.path.join(self.root, *name.split("/")), 4000000)
            if text is None:
                raise Stop("the data quote %s, and the Lean folder has no such file" % name)
            self.quotable[name] = " %s " % " ".join(text.split())
        if not words.strip() or " %s " % " ".join(words.split()) not in self.quotable[name]:  # whole words
            raise Stop(
                "the data give these words as a quotation of %s, and they do not stand there: %s" % (name, words)
            )
        return words

    def inline(self, d, bound, l):
        if len(l) > LONGEST_LINE:
            raise Stop("a line of words of more than %d characters: %s ..." % (LONGEST_LINE, l[:80]))
        m = QUOTE.match(l)
        if m:
            l = self.quoted(m.group(1), l[m.end() :])
        elif re.match(r"quote \S+ \|", l):
            raise Stop("'quote X.md | words', X.md a page in the Lean folder or 'Folder/X.md': %s" % l)
        l = COUNTED.sub(lambda m: "{:,}".format(self.number(m.group(1), m.group(2) or "", l)), l)
        pieces, i = [], 0
        for m in re.finditer(
            r"\[([^\]\n]+)\]\((#%s|(?:[A-Za-z]+/)*[A-Z][A-Z-]*\.md"
            r"|long-page|notes-page)\)|\*\*([^*\n]+)\*\*|%s([^%s\n]+)%s" % ((_ID,) + (BACKTICK,) * 3),
            l,
        ):
            pieces.append(self.plain(l[i : m.start()], l))
            if m.group(2) in ("long-page", "notes-page"):
                goal = self.long_name if m.group(2) == "long-page" else self.notes_name
                if not goal:
                    raise Stop("a link to the short page, and no short page is made (--short): %s" % l)
                pieces.append('<a href="%s">%s</a>' % (esc(goal), coded(m.group(1))))
            elif m.group(2):
                self.links_to.add(m.group(2))
                pieces.append('<a href="%s">%s</a>' % (esc(m.group(2)), coded(m.group(1))))
            elif m.group(3):
                pieces.append("<b>%s</b>" % coded(m.group(3)))
            else:
                if m.group(4) != m.group(4).strip():
                    raise Stop("code that begins or ends with a blank: are its backticks paired as meant? %s" % l)
                code = self.code_html(d, m.group(4), bound, {}, in_comment=True) if d else esc(m.group(4))
                if "<span" not in code:
                    self.unlinked.append(m.group(4))
                pieces.append("<code%s>%s</code>" % (' class="nw"' if len(m.group(4)) <= 28 else "", code))
            i = m.end()
        return "".join(pieces + [self.plain(l[i:], l)])

    def words(self, d, bound, lines, cls="bl"):
        """Paragraphs and lists: a line is a paragraph; '- ' opens a bullet, '-- ' one of the second level."""
        out, depth = [], 0
        for l in lines:
            want = 2 if l.startswith("-- ") else 1 if l.startswith("- ") else 0
            if want == 2 and not depth:
                raise Stop("a bullet of the second level without one of the first: %s" % l)
            while depth > want:
                out.append("</li></ul>")
                depth -= 1
            if want and depth == want:
                out.append("</li>")
            while depth < want:
                out.append('<ul class="%s">' % cls if not depth else "<ul>")
                depth += 1
            text = self.inline(d, bound, l[want + 1 :].strip() if want else l)
            out.append("<li>" + text if want else "<p>%s</p>" % text)
        out.append("</li></ul>" * depth)
        return "".join(out)

    # -- Lean text --------------------------------------------------------------------------------
    def pieces(self, src, a, b):
        """The characters a to b as (line, first column, end column), line by line, blanks at both ends left out."""
        out = []
        for n in range(src.line_of(a), src.line_of(max(a, b - 1)) + 1):
            start = src.line_starts[n - 1]
            end = src.line_starts[n] - 1 if n < len(src.line_starts) else len(src.text)
            s, e = max(a, start), min(b, end)
            while s < e and src.text[s].isspace():
                s += 1
            while e > s and src.text[e - 1].isspace():
                e -= 1
            if s < e:
                out.append((n, s - start, e - start))
        return out

    def lean_cell(self, src, ranges):
        out = []
        for a, b in ranges:
            refuse_unseen_characters(src, a, b)
            for n, s, e in self.pieces(src, a, b):
                line = src.text[src.line_starts[n - 1] :].split("\n", 1)[0]
                out.append(
                    '<div class="fl" data-l="%d" data-a="%d" data-b="%d" style="--i:%d">%s</div>'
                    % (n, units(line, s), units(line, e), min(40, len(line) - len(line.lstrip())), esc(line[s:e]))
                )
        return "".join(out)

    def front_rows(self, d, rows_text):
        """[(margin word, the words' lines, [(start, end)], chip)]; the ranges behind the lines in force, joined, are
        d's
        text. The chip: '' or what stands behind '# chip:'."""
        src, marks, words, margin, chip = d.src, [], None, "", ""
        for l in rows_text:
            if l.startswith("# margin:"):
                margin = as_typed(l[len("# margin:") :].strip(), "front/rows.txt, a margin word")
            elif l.startswith("# chip:"):
                chip = l[len("# chip:") :].strip()
            elif l.startswith("#"):
                continue
            elif l.startswith("@"):
                words = []
                marks.append((l[1:].strip(), margin, words, chip))
                margin = chip = ""
            elif l.strip():
                if words is None:
                    rows_stop(d, "front/", "its rows begin with words, not with '@'")
                words.append(l.strip())
        out = []
        if marks and marks[0][0] == "^":
            out.append((marks[0][1], marks[0][2], list(self.reading(d)[0]), marks[0][3]))
            if not out[0][2]:
                rows_stop(d, "front/", "'@^': no line is in force above it")
            del marks[0]
        elif self.reading(d)[0]:
            rows_stop(d, "front/", "lines are in force above it (variable, open ... in): its rows must begin with '@^'")
        since, behind, places = d.start, d.start, []
        for k, (first, _, _, _) in enumerate(marks):
            at = anchor_at(src, first, behind, d.shown_end) if first else -1
            if at < 0 or (k == 0 and at != d.start):
                rows_stop(d, "front/", NOT_FOUND % (first, src.path, src.line_of(d.start)))
            if k and not first.startswith(("/-", "--")):
                places.append(self.line_start(src, with_comments(src, at, since, behind)))
            else:
                places.append(self.line_start(src, at) if k else at)
            since, behind = at, at + len(first)
        if not marks:
            rows_stop(d, "front/", "it has no row")
        for k, (_, margin, words, chip) in enumerate(marks):
            out.append((margin, words, [(places[k], places[k + 1] if k + 1 < len(places) else d.shown_end)], chip))
        for margin, words, _, _ in out:
            if not words:
                rows_stop(d, "front/", "a row without words")
        return out


# The front page's lines are to have about 4,000 characters at the most: tools that read a page line by line take very
# long over much longer ones. in_pieces, block_text and in_lines keep the lines short. The program prints the longest
# line's length. The longest lines are usually lines of number tables in Lean files. MOST_LINE lies well above the aim,
# so that such a line can grow a little without stopping the make. A tool that searches a release for lists of numbers
# joins a line that ends in a number and a comma with a next line that begins with a number, and would take the two for
# one list: so no line end may stand there.
MOST_PIECE, MOST_LINE = 3000, 10000


def json_text(x):
    """A string or a number as JSON. '<' is written as its escape, so that nothing in the block of data can close it."""
    return json.dumps(x, ensure_ascii=False).replace("<", "\\u003c")


def in_pieces(first, lines):
    """A stretch of Lean lines, the first of which has the number 'first', cut into pieces of whole lines:
    [[number of the piece's first line, the piece's text]]. A piece has as many lines as come, written as JSON, to at
    most MOST_PIECE characters. A longer line is a piece by itself. The page's script joins the pieces again
    (shell/turns.txt)."""
    out, size = [], 0
    for k, line in enumerate(lines):
        n = len(json_text(line))
        if out and size + n <= MOST_PIECE:
            out[-1][1] += "\n" + line
            size += n
        else:
            out.append([first + k, line])
            size = n
    return out


def block_text(x):
    """x as JSON without blanks, with a line end behind every comma that follows ']' or '}'. So every piece of Lean,
    every declaration's row and every line's links have a line of their own, and no line end stands between two
    numbers."""
    if isinstance(x, dict):
        # the keys must be strings already: a number would be written without quotes, which is no JSON
        items, ends = [json_text(k) + ":" + block_text(v) for k, v in x.items()], "{}"
    elif isinstance(x, (list, tuple)):
        items, ends = [block_text(v) for v in x], "[]"
    else:
        return json_text(x)
    return ends[0] + "".join(i + (",\n" if i[-1] in "]}" else ",") for i in items[:-1]) + "".join(items[-1:]) + ends[1]


BREAK_BEFORE = re.compile(r'(?<=[^\n])(?=<div class="sbs-row|<div class="fl"|<li[ >]|<p[ >]|<tr[ >])')


def in_lines(html):
    """html with a line end before every row of a card, line of Lean in a row, list item, paragraph and table row:
    except at html's very start and where a line end stands already. White space does not show at these places. What the
    data say is escaped, so these characters are always the program's own tags."""
    return BREAK_BEFORE.sub("\n", html)


def front_page(root, heads, long_page, entries, long_name, notes_name, say):
    folder, shell = os.path.join(heads, "front"), os.path.join(heads, "shell")
    # which declarations have a card on the short page, where the remarks and limits stand: by that page's own data
    noted = {
        l.split("|")[0].strip()
        for l in (short_lines(os.path.join(heads, "short"), "claims.txt", True) if notes_name else ())
        if not l.startswith(("==", ">", "!", "+"))
    }
    parts = {}
    for name in SHELL:
        parts[name] = small_text(os.path.join(shell, name), 400000)
        if parts[name] is None:
            raise Stop("%s: there is no such file" % os.path.join(shell, name))
    script = turned_script(parts["page.js"], parts["turns.txt"], os.path.join(shell, "turns.txt"))
    label = dict(front_table(folder, "labels.txt", 2, True))
    for key in FRONT_LABELS:
        if key not in label:
            raise Stop("%s: no line for '%s'" % (os.path.join(folder, "labels.txt"), key))
    for key, words in label.items():  # what a reader sees of a status: only the statuses that are held may say 'proved'
        kind, _, status = key.partition("-")
        held = ("proved", "proved-under") + tuple("hypothesis-" + w for w in BRIGHT)
        if kind in ("type", "chip") and status not in held:
            if SAYS_CHECKED.search(words):
                raise Stop(
                    "front/labels.txt, '%s': this status's words say '%s', which speaks of a proof ('proved' may stand "
                    "behind 'not' alone): %s" % (key, SAYS_CHECKED.search(words).group(), words)
                )
    if label["html-title"].endswith(TITLE_ENDS):
        raise Stop(
            "%s: html-title, the front page's, must not end with '%s', as the long page's does"
            % (os.path.join(folder, "labels.txt"), TITLE_ENDS)
        )
    titles, remarks = dict(front_table(folder, "titles.txt", 2)), {}
    for where, some in (
        ("labels.txt", label),
        ("titles.txt", titles),
    ):  # printed as they stand: a mark would show as signs
        for key, words in some.items():
            as_typed(words, "%s, '%s'" % (where, key))
    for name, words in front_table(folder, "remarks.txt", 2):
        remarks.setdefault(name, []).append(words)
    rows_of, at = {}, None
    for l in (small_text(os.path.join(folder, "rows.txt"), 1000000) or "").split("\n"):
        if l.startswith("==="):
            at = l[3:].strip()
            if at in rows_of:
                raise Stop("front/rows.txt has '=== %s' twice" % at)
            rows_of[at] = []
        elif at:
            rows_of[at].append(l)
        elif l.strip() and not l.startswith("#"):
            raise Stop("front/rows.txt begins with something else than a remark or '=== FULL.NAME'")
    limits, folded = {}, {}  # folded: limit -> (how many of its lines stand before its group, the group's title)
    for n, words in front_table(folder, "limits.txt", 2):
        if not re.fullmatch(r"[1-9]\d{0,2}", n):
            raise Stop("front/limits.txt: '%s' is no number" % n)
        if re.match(r"more *(\||$)", words):
            title = words.partition("|")[2].strip()
            fault = (
                "limit %s has such a line already" % n
                if int(n) in folded
                else "it is the first line of limit %s, which would show nothing" % n
                if int(n) not in limits
                else "" if title else "it has no title"
            )
            if fault:
                raise Stop("front/limits.txt: 'n | more | title': %s: %s | %s" % (fault, n, words))
            folded[int(n)] = (len(limits[int(n)]), as_typed(title, "front/limits.txt, a group's title"))
        else:
            limits.setdefault(int(n), []).append(words)
    for n, (before, _) in folded.items():
        if before == len(limits[n]):
            raise Stop("front/limits.txt: no line of limit %d follows its line 'more'" % n)
    audited = small_text(os.path.join(root, *AUDITED.split("/")), 20000000) or ""
    audited = {l.split()[0] for l in audited.split("\n") if l.strip() and not l.startswith("#")}
    page = FrontPage(long_page, long_name)
    page.root = root
    page.notes_name = notes_name
    page.links_to = set()

    def declaration(name):
        if name in entries:
            return entries[name]
        fit = page.index.public.get(name, ())
        if len(fit) != 1:
            raise Stop("the data name %s: %d declarations of the Lean files have that full name" % (name, len(fit)))
        if not fit[0].ident:
            fit[0].ident, fit[0].part = fit[0].full, "other"
        return fit[0]

    def on_the_list(d, where):
        """Stop unless d is a theorem or lemma that the audit's list names, with no 'sorry' written in its proof."""
        if d.kind not in ("theorem", "lemma") or d.full not in audited:
            raise Stop("%s, and %s has no line for a theorem or lemma of that name" % (where, AUDITED))
        if d.shown_end is None:
            cut(d)
        if re.search(
            "(?<![%s.])(?:sorry|sorryAx|admit)(?![%s])" % (_REST, _REST), d.src.code[d.shown_end : d.whole_end]
        ):
            raise Stop("%s, and its proof has a 'sorry', 'sorryAx' or 'admit'" % where)

    def status_of(said, where):
        """(status, word) of 'definition', 'hypothesis open', ... The words with the bright chip name their theorems."""
        status, rest = (said.split() + [""])[0], said.split()[1:]
        word, by = (rest[0], rest[1:]) if status == "hypothesis" and rest else ("", rest)
        if status not in CARD_COLOUR or (status == "hypothesis" and word not in HYPOTHESIS_WORDS):
            raise Stop("%s: unknown status: %s" % (where, said))
        if bool(by) != (word in BRIGHT) and status != "target":
            raise Stop(
                "%s: 'hypothesis %s FULL.NAME ...' name the theorems that they rest on; a target may name some; no "
                "other status names any" % (where, " | ".join(BRIGHT))
            )
        for name in by:
            on_the_list(declaration(name), "%s: %s is given as a proof" % (where, name))
        return status, word, by

    named, doubtful = {}, {}

    def names_of(d):
        """What d's shown text names, by the rules of part 3. (The long page's own note of it leaves out long texts.)"""
        if id(d) not in named:
            if not d.ident:
                d.ident, d.part = d.full, "other"
            page.collecting, page.tally.doubt = True, []
            named[id(d)] = page.entry(d)[0]
            page.collecting, doubtful[id(d)], page.tally.doubt = False, page.tally.doubt, None
        return named[id(d)]

    def walk(roots, counts):
        """The roots and all that their texts reach, definitions followed, as far as counts(declaration) is true. Where
        rule 2 finds two or more declarations for a name, Lean chooses by type and this program cannot: it makes no link
        and takes them all here, so as to find rather more than less. It does not see a function that is called only
        by a dot behind a value whose type is not written ('x.f'): rule 3 resolves nothing there. Nor does it follow
        what no name in the text stands for: instances that Lean finds by class, notations, coercions, 'deriving',
        anonymous constructors; and it leaves out private declarations."""
        seen, met, todo = {}, {id(d) for d in roots}, list(roots)
        while todo:
            found = []
            for d in todo:
                if not d.full or d.private or not counts(d):
                    continue
                seen[id(d)] = d
                if d.kind in FOLLOWED or any(d is r for r in roots):
                    found += [t for _, t in names_of(d)] + doubtful[id(d)]
            todo = []
            for t in found:
                if id(t) not in met:
                    met.add(id(t))
                    todo.append(t)
        return seen

    # -- the sections, as the data give them --------------------------------------------------------
    sections, cards, whole, also = (
        [],
        [],
        [],
        [],
    )  # a section: dict(level, title, id, pill, define, body); body: (kind, value)
    own_chip = {}  # of each card: (a target's own chip words or '', the theorems that the data name for its status)
    in_fold = lambda sec: [k for k, _ in sec["body"] if k in ("fold", "fold-end")][-1:] == ["fold"]
    for l in front_lines(folder, "claims.txt", True):
        if l.startswith("=="):
            level = 3 if l.startswith("===") else 2
            title, _, ident = (c.strip() for c in l.lstrip("=").partition("|"))
            if not title or not re.fullmatch(_ID, ident) or any(s["id"] == ident for s in sections):
                raise Stop("front/claims.txt: a section wants a title and, behind a bar, an id of its own: %s" % l)
            if ident.startswith(("lim-", "card-")) or 'id="%s"' % ident in parts["page_template.html"]:
                # the script finds its data and its panel by id, and takes the first element that has it
                raise Stop("front/claims.txt: this id is the frame's, or begins like a limit's or a card's: %s" % l)
            as_typed(title, "front/claims.txt, a section's title")
            if level == 3 and not sections:
                raise Stop("front/claims.txt: a sub-section before the first section: %s" % l)
            sections.append(dict(level=level, title=title, id=ident, pill=None, define=[], body=[]))
            continue
        if not sections:
            raise Stop("front/claims.txt begins with something else than '== title | id'")
        sec = sections[-1]
        if l.startswith("! pill "):
            state, _, words = (c.strip() for c in l[7:].partition("|"))
            if state not in PILLS or not words or sec["pill"]:
                raise Stop(
                    "front/claims.txt: '! pill STATE | words', once a section, STATE one of %s: %s"
                    % (", ".join(PILLS), l)
                )
            sec["pill"] = (state, as_typed(words, "front/claims.txt, a pill"))
        elif l.startswith(("!> ", "!- ")):
            sec["define"].append(l[3:].strip() if l[1] == ">" else l[1:])
        elif l.startswith("! "):
            what = l[2:].split()
            if what[0] in ("whole", "also") and len(what) == 2:
                (whole if what[0] == "whole" else also).append(declaration(what[1]))
                continue
            if what[0] == "box":
                kind, _, title = (c.strip() for c in l[6:].partition("|"))
                if kind not in BOXES or not title:
                    raise Stop("front/claims.txt: '! box KIND | title', KIND one of %s: %s" % (", ".join(BOXES), l))
                sec["body"].append(("box", (kind, as_typed(title, "front/claims.txt, a box's title"), [])))
                continue
            if what in (["definitions"], ["definitions", "titled"]):
                sec["body"].append(("definitions", len(what) == 2))
                continue
            if what[0] == "fold" or what == ["fold-end"]:
                title = " ".join(what[1:]) if what[0] == "fold" else ""
                if in_fold(sec) == (what[0] == "fold") or (what[0] == "fold" and not title):
                    raise Stop("front/claims.txt: '! fold Title' and '! fold-end' by turns, within one section: %s" % l)
                sec["body"].append((what[0], as_typed(title, "front/claims.txt, a fold's title")))
                continue
            if what[0] not in ("table", "limits", "closing", "notes") or len(what) != (2 if what[0] == "table" else 1):
                raise Stop("front/claims.txt: unknown line: %s" % l)
            if what[0] == "table" and not re.fullmatch(r"[a-z]+", what[1]):
                raise Stop("front/claims.txt: a table's name is of small letters: %s" % l)
            sec["body"].append((what[0], what[-1]))
        elif l.startswith(("> ", "- ", "-- ")):
            line = l[2:].strip() if l[0] == ">" else l
            if sec["body"] and sec["body"][-1][0] == "box":
                if not l.startswith("- "):
                    raise Stop("front/claims.txt: a box holds bullets of the first level alone: %s" % l)
                sec["body"][-1][1][2].append(l[2:].strip())
            elif sec["body"] and sec["body"][-1][0] in ("words", "bullets"):
                sec["body"][-1][1].append(line)
            else:
                sec["body"].append(("words", [line]))
        elif l.startswith("+ "):
            sec["body"].append(("label", as_typed(l[2:].strip(), "front/claims.txt, a small label")))
            sec["body"].append(("bullets", []))
        else:
            name, status, own = ([c.strip() for c in l.split("|", 2)] + ["", ""])[:3]
            named_proofs = len(status.split()) > 1
            status, word, by = status_of(status, "front/claims.txt, %s" % name)
            if own and status != "target":
                raise Stop("front/claims.txt: a target's card alone may have chip words of its own: %s" % l)
            if status == "target" and (named_proofs and not own or SAYS_CHECKED.search(own) and not named_proofs):
                raise Stop(
                    "front/claims.txt: 'NAME | target FULL.THEOREM ... | words': the theorems go with words of the "
                    "card's own, and words that speak of a proof ('proved' without 'not', 'verified' ...) go with "
                    "theorems: %s" % l
                )
            d = declaration(name)
            own_chip[d.ident] = (as_typed(own, "front/claims.txt, a card's chip words"), by)
            if any(c[0] is d for c in cards):
                raise Stop("front/claims.txt: two cards for %s" % name)
            if d.private or d.kind == "axiom":
                raise Stop("front/claims.txt: %s: a private declaration or an axiom can have no card" % name)
            is_theorem = d.kind in ("theorem", "lemma")
            if is_theorem != (status in ("proved", "proved-under")):
                raise Stop("front/claims.txt calls %s %s, and it is a %s" % (name, status, d.kind))
            if is_theorem:
                on_the_list(d, "front/claims.txt calls %s %s" % (name, status))
            cards.append((d, status, word))
            sec["body"].append(("card", len(cards) - 1))
    if not cards:
        raise Stop("front/claims.txt has no card")
    for d, _, _ in cards:
        if d.ident not in titles or d.ident not in rows_of:
            raise Stop(
                "%s has a card and no %s"
                % (d.ident, "title in front/titles.txt" if d.ident not in titles else "rows in front/rows.txt")
            )
    for what, names in (("remarks.txt", remarks), ("rows.txt", rows_of)):
        for name in names:  # a caveat must not leave the page in silence when its declaration is renamed
            if not any(c[0].ident == name for c in cards):
                raise Stop("front/%s has lines for %s, which has no card" % (what, name))
    for sec in sections:
        if in_fold(sec):
            raise Stop("front/claims.txt: the section '%s' ends in a fold that no '! fold-end' closes" % sec["title"])

    # -- what is embedded: the cards; what their own texts name; and from the declarations that the data call whole all
    #    that their texts reach, definitions followed. A name that leads to none of these stays plain.
    def embed(target):
        if not target.full or target.private or id(target) in page.embedded:
            return False
        if not target.ident:  # the long page has no entry for it
            target.ident, target.part = target.full, "other"
        page.embedded[id(target)] = target
        return True

    named_by_cards = {}
    page.cards = [d for d, _, _ in cards]
    for d, _, _ in cards:
        page.embedded[id(d)] = d
    for d, _, _ in cards:
        for _, target in names_of(d):
            embed(target)
            if target.full and not target.private and target.kind in FOLLOWED:
                named_by_cards.setdefault(id(target), target)
    for d in also:
        embed(d)
    for d in walk(whole, lambda d: True).values():
        embed(d)
    page.has_entry = set(page.embedded)
    for d in page.embedded.values():
        if d.shown_end is None:
            cut(d)

    # -- the block of data -----------------------------------------------------------------------
    order = sorted(page.embedded.values(), key=lambda d: (d.src.path, d.start))
    keys = [d.ident for d in order]  # the script finds a declaration by this key
    if len(set(keys)) != len(keys):
        twice = next(k for k in keys if keys.count(k) > 1)
        raise Stop(
            "two embedded declarations are called %s: %s. The page's script finds a declaration by its name: one of "
            "the two must go from what the data name or reach"
            % (twice, ", ".join("%s:%d" % (d.src.path, d.src.line_of(d.start)) for d in order if d.ident == twice))
        )
    number = {id(d): k for k, d in enumerate(order)}
    files = sorted({d.src.path: d.src for d in order}.items())
    file_number = {p: k for k, (p, _) in enumerate(files)}
    kinds = sorted({d.kind for d in order})
    ranges, links, cut_short, rows_data, above_data = {p: [] for p, _ in files}, {}, {}, [], {}
    for d in order:
        src = d.src
        in_force, bound, types = page.reading(d)
        first = src.line_of(d.doc[0]) if d.doc else src.line_of(d.start)
        last = src.line_of(d.shown_end - 1)
        ranges[src.path].append((first, last))
        for a, b in in_force:
            ranges[src.path].append((src.line_of(a), src.line_of(b - 1)))
        if in_force:  # the script prints these lines with the declaration in its hover card and in the side panel
            above_data[str(number[id(d)])] = [[src.line_of(a), src.line_of(b - 1)] for a, b in in_force]
        line_end = src.text.find("\n", d.shown_end)
        line_end = len(src.text) if line_end < 0 else line_end
        # the statement ends in mid-line: the rest of the line is not embedded, unless it is the bare sign of a proof
        if src.text[d.shown_end : line_end].strip() not in ("",) + BARE_OPENERS:
            cut_short.setdefault(src.path, {})[last] = d.shown_end
        page.spots = []
        for a, b in list(in_force) + [(d.start, d.shown_end)]:
            page.source_html(d, a, b, bound, types)
        for at, length, target in page.spots:
            n = src.line_of(at)
            line = src.text[src.line_starts[n - 1] :].split("\n", 1)[0]
            column = at - src.line_starts[n - 1]
            links.setdefault(src.path, {}).setdefault(n, {})[units(line, column)] = (
                units(line, column + length) - units(line, column),
                number[id(target)],
            )
        page.spots = None
        whole = d.whole_end if d.kind not in FOLLOWED else d.shown_end
        sign = src.code.find(":=", d.start, d.shown_end) if d.kind in ("def", "abbrev", "instance", "opaque") else -1
        rows_data.append(
            [
                d.ident,
                kinds.index(d.kind),
                file_number[src.path],
                src.line_of(d.start),
                (
                    src.line_of(sign)
                    if sign >= 0
                    else last if d.kind not in ("structure", "class", "inductive") else src.line_of(d.start)
                ),
                src.line_of(max(d.start, whole - 1)),
                src.line_of(d.doc[0]) if d.doc else 0,
                last,
                0,
                "" if d.full else first_line(d),
            ]
        )
    files_data, embedded_lines = [], 0
    for p, src in files:
        lines, merged = src.text.split("\n"), []
        for a, b in sorted(ranges[p]):
            if merged and a <= merged[-1][1] + 1:
                merged[-1][1] = max(merged[-1][1], b)
            else:
                merged.append([a, b])
        segments = []
        for a, b in merged:
            refuse_unseen_characters(
                src, src.line_starts[a - 1], src.line_starts[b] if b < len(src.line_starts) else len(src.text)
            )
            text = lines[a - 1 : b]
            for n, end in cut_short.get(p, {}).items():
                if a <= n <= b and not any(x <= n < y for x, y in ranges[p]):  # no other embedded text runs on below it
                    text[n - a] = src.text[src.line_starts[n - 1] : end].rstrip()
            segments += in_pieces(a, text)
            embedded_lines += b - a + 1
        count = len(lines) - (lines[-1] == "")  # what stands behind the last line end is no line
        files_data.append([p, hashlib.sha256(AS_IT_LIES.get(p, src.text).encode("utf-8")).hexdigest()[:12], count, segments, ""])
    if embedded_lines > MOST_EMBEDDED:
        raise Stop(
            "the cards' texts reach %d lines of Lean: more than %d on one page" % (embedded_lines, MOST_EMBEDDED)
        )
    cut_data = {}
    for p, src in files:
        per = {}
        for n, end in cut_short.get(p, {}).items():
            kept = next(
                t.split("\n")[n - a] for a, t in files_data[file_number[p]][3] if a <= n < a + t.count("\n") + 1
            )
            whole_line = src.text.split("\n")[n - 1]
            if kept != whole_line:
                per[str(n)] = units(whole_line, len(whole_line))
        cut_data[str(file_number[p])] = per
    links_data = {
        str(file_number[p]): {
            str(n): [x for c in sorted(per) for x in (c,) + per[c]] for n, per in sorted(by_line.items())
        }
        for p, by_line in links.items()
    }
    data = dict(kinds=kinds, files=files_data, decls=rows_data, links=links_data, cut=cut_data, above=above_data)
    payload = block_text(data)

    # -- the numbers that words may ask for ---------------------------------------------------------
    reached = {}

    def reach(name):
        """The declaration of that name and all the definitions that its text reaches, definitions followed."""
        if name not in reached:
            first = declaration(name)
            seen = walk([first], lambda d: d is first or d.kind in FOLLOWED)
            for d in seen.values():
                if d.shown_end is None:
                    cut(d)
            reached[name] = list(seen.values())
        return reached[name]

    def span(d):
        return d.src.line_of(d.shown_end - 1) - d.src.line_of(d.doc[0] if d.doc else d.start) + 1

    def number(key, arg, l):
        plain = {
            "cards": len(cards),
            "rows": sum(len(page.front_rows(c[0], rows_of.get(c[0].ident, ()))) for c in cards) if key == "rows" else 0,
            "embedded": len(order),
            "embedded-files": len(files),
            "links": sum(len(v) // 3 for f in links_data.values() for v in f.values()),
        }
        if key in plain and not arg:
            return plain[key]
        if key == "lean-files":
            return sum(1 for p in page.index.imports if not arg or p.startswith(arg.rstrip("/") + "/"))
        if key == "lines" and arg in page.index.lines:
            return page.index.lines[arg]
        if key.startswith("reach") and arg:
            some = reach(arg)
            if "card" in key:
                some = [d for d in some if any(c[0] is d for c in cards)]
            if key in ("reach", "reach-cards"):
                return len(some)
            return len({d.src.path for d in some}) if key == "reach-files" else sum(span(d) for d in some)
        raise Stop(
            "a place for a number that this program cannot fill: {%s%s} in: %s" % (key, " " + arg if arg else "", l)
        )

    page.number = number

    # -- the page ----------------------------------------------------------------------------------
    def pill(p):
        return '<span class="status st-%s">%s</span>' % (p[0], esc(p[1]))

    def place(d):
        a, b = d.src.line_of(d.start), d.src.line_of(d.shown_end - 1)
        return "%s:%d" % (d.src.path, a) + ("–%d" % b if b > a else "")

    def button(d, small=False):
        return '<button type="button" class="lean-link%s" data-name="%s">%s</button>' % (
            " small" if small else "",
            esc(d.ident),
            esc(d.full or first_line(d)),
        )

    limits_used = set()

    def need(key):
        if key not in label:
            raise Stop("front/labels.txt: no line for '%s'" % key)
        return label[key]

    def chip_html(status, word, own="", by=(), of=""):
        """The chip of a status. Its tooltip ends with the card whose chip it is, where a row or a cell borrows it, and
        with the theorems that the data name for the status: a reader can look. Without words there is no chip."""
        key = status + ("-" + word if word else "")
        for k in ("type-", "chip-", "tip-"):
            if k + key not in label:
                raise Stop("front/labels.txt: no line for '%s%s'" % (k, key))
        if not own and not label["chip-" + key]:  # no words in labels.txt, none of the card's own: no chip
            return ""
        return '<span class="chip chip-%s" title="%s">%s</span>' % (
            "std" if status == "proved" or word in BRIGHT else "other",
            esc(
                label["tip-" + key]
                + ("; the chip of the card " + of if of else "")
                + ("; theorems named for it: " + ", ".join(by) if by else "")
            ),
            esc(own or label["chip-" + key]),
        )

    def row_chip(where, said):
        """'chip: FULL.NAME': that card's own chip. 'chip: = status': for what has no card."""
        if not said:
            return ""
        if said.startswith("="):
            status, word, by = status_of(said[1:], "%s: 'chip: %s'" % (where, said))
            own = of = ""
            if status in ("proved", "proved-under"):  # these two stand on a theorem's card, or are that card's chip
                raise Stop("%s: 'chip: %s': name the theorem's card instead: 'chip: FULL.NAME'" % (where, said))
            if status == "target" and len(said.split()) > 2:
                raise Stop("%s: 'chip: %s': theorems go with a target's card, in front/claims.txt" % (where, said))
        else:
            fit = [c for c in cards if c[0].ident == said]
            if not fit:
                raise Stop("%s: 'chip: %s': no card of that name" % (where, said))
            status, word = fit[0][1:]
            (own, by), of = own_chip[said], said
        return "<p>%s</p>" % chip_html(status, word, own, by, of)

    def card_html(d, status, word):
        key = status + ("-" + word if word else "")
        chip = chip_html(status, word, *own_chip[d.ident])
        if d.ident not in titles or d.ident not in rows_of:
            raise Stop(
                "%s has a card and no %s"
                % (d.ident, "title in titles.txt" if d.ident not in titles else "rows in rows.txt")
            )
        _, bound, _ = page.reading(d)
        colour = CARD_COLOUR[status] if word not in ("open", "at-risk") else "class"
        a, b = d.src.line_of(d.start), d.src.line_of(d.shown_end - 1)
        rows = [
            '<div class="sbs-row sbs-head"><div class="sbs-label"></div><div class="sbs-words">%s</div>'
            '<div class="sbs-lean sbs-lean-h">%s · %s, lines %d–%d</div></div>'
            % (esc(label["rows-words"]), esc(label["rows-lean"]), esc(d.src.path), a, b)
        ]
        for margin, words, where, said in page.front_rows(d, rows_of[d.ident]):
            rows.append(
                '<div class="sbs-row"><div class="sbs-label">%s</div><div class="sbs-words">%s%s</div>'
                '<div class="sbs-lean">%s</div></div>'
                % (
                    esc(margin),
                    page.words(d, bound, words),
                    row_chip("front/rows.txt, '=== %s'" % d.full, said),
                    page.lean_cell(d.src, where),
                )
            )
        blocks, notes = [], []  # a remark's blocks: [label, lines]
        for l in remarks.get(d.ident, ()):
            m = re.match(r"\[([^\]]+)\] +(\S.*)$", l)
            if re.fullmatch(r"limits( [1-9]\d{0,2})+", l):
                notes += [int(n) for n in l.split()[1:]]
            elif m and not m.group(1).startswith("SLOT"):
                blocks.append([m.group(1), [m.group(2)]])
            elif blocks:
                blocks[-1][1].append(l)
            else:
                blocks.append([label["remark"], [l]])
        if notes:
            for n in notes:
                if n not in limits:
                    raise Stop("front/remarks.txt, %s: limits.txt has no limit %d" % (d.ident, n))
                limits_used.add(n)
            line = "- %s %s" % (label["limits-link"], ", ".join("[%d](#lim-%d)" % (n, n) for n in notes))
            if blocks:
                blocks[-1][1].append(line)
            else:
                blocks.append([label["remark"], [line]])
        to_notes = ""
        if d.ident in noted:  # its remarks and limits stand on the short page: the way there
            to_notes = '<a class="lean-link small" href="%s#%s">%s</a>' % (
                esc(notes_name),
                esc(d.ident),
                esc(need("note-link")),
            )
        return (
            '<div class="formal %s-card" id="card-%s"><div class="card-head"><span class="formal-type %s-type">'
            "%s</span>"
            '<span class="italic">%s</span><span class="paper-ref">%s</span></div><div class="card-desc">'
            '<div class="sbs" data-decl="%s">%s</div>%s</div><div class="card-foot">%s%s%s</div></div>'
            % (
                colour,
                esc(d.ident),
                colour,
                esc(label["type-" + key]),
                esc(titles[d.ident]),
                esc(place(d)),
                esc(d.ident),
                "".join(rows),
                "".join(
                    '<div class="stmt-remark"><div class="part-label">%s</div><div class="part-body">%s</div></div>'
                    % (esc(name), page.words(d, bound, lines))
                    for name, lines in blocks
                ),
                button(d),
                chip,
                to_notes,
            )
        )

    def counted(key, **numbers):
        """The label 'key' with each {word} filled with its number, and {s:word} with an 's' unless that number is 1."""
        if key not in label:
            raise Stop("front/labels.txt: no line for '%s'" % key)
        words = label[key]
        for word, n in numbers.items():
            words = words.replace("{%s}" % word, str(n)).replace("{s:%s}" % word, "" if n == 1 else "s")
        return words

    def definitions_html(titled):
        listed = sorted(
            (d for d in named_by_cards.values() if not any(c[0] is d for c in cards)),
            key=lambda d: (d.src.path, d.start),
        )
        out, by_top = [], {}
        for d in listed:
            by_top.setdefault(d.src.path.split("/")[0], {}).setdefault(d.src.path, []).append(d)
        if idle_group_lines(label, by_top):
            raise Stop(
                "front/labels.txt: '%s': the list of definitions has no group of that name"
                % idle_group_lines(label, by_top)[0]
            )
        for top, by_file in by_top.items():
            n = sum(len(v) for v in by_file.values())
            out.append(
                '<details class="defgroup"><summary>%s <span class="cnt">· %s</span></summary>'
                % (
                    esc(group_title(label, top)),
                    esc(counted("definitions-count", definitions=n, files=len(by_file))),
                )
            )
            for p, ds in by_file.items():
                out.append('<div class="deffile">%s</div><div class="deflist">' % esc(p.split("/", 1)[-1]))
                for d in ds:
                    out.append(
                        '<div class="defrow"><span class="defkind">%s</span>%s<span class="defdesc">%s</span>'
                        '<span class="defloc">:%d</span></div>'
                        % (
                            esc(d.kind),
                            button(d, True),
                            esc(titles.get(d.ident, "")) if titled else page.first_sentence(d),
                            d.src.line_of(d.start),
                        )
                    )
                out.append("</div>")
            out.append("</details>")
        return "\n".join(out)

    def table_html(name):
        rows = [
            l.split("\t")
            for l in (small_text(os.path.join(folder, name + ".txt"), 400000) or "").split("\n")
            if l.strip()
        ]
        if len(rows) < 2 or any(len(r) != len(rows[0]) for r in rows):
            raise Stop("%s.txt: a head row and rows of as many cells, between tabs" % os.path.join(folder, name))

        def cell(c):  # 'chip: ...' alone is a chip, as in a row; the two signs \n part a cell's paragraphs
            if c.startswith("chip:"):
                return row_chip(name + ".txt", c[len("chip:") :].strip())
            lines = [x.strip() for x in c.split("\\n")]
            return page.inline(context, set(), c) if len(lines) == 1 else page.words(context, set(), lines)

        return (
            '<div class="tblwrap"><table class="tbl %s"><thead><tr>%s</tr></thead><tbody>%s</tbody></table></div>'
            % (
                name,
                "".join("<th>%s</th>" % esc(as_typed(c.strip(), name + ".txt, its head row")) for c in rows[0]),
                "".join("<tr>%s</tr>" % "".join("<td>%s</td>" % cell(c.strip()) for c in r) for r in rows[1:]),
            )
        )

    body, contents = [], []
    context = cards[0][0] if cards else None
    for sec in sections:
        own = [cards[v][0] for kind, v in sec["body"] if kind == "card"]
        at = own[0] if own else context
        if not in_contents(label, sec["level"]):
            pass
        elif sec["level"] == 3:
            contents[-1][1].append('<li><a href="#%s">%s</a></li>' % (sec["id"], esc(sec["title"])))
        else:
            contents.append(
                [
                    '<li><a href="#%s">%s</a>%s'
                    % (sec["id"], esc(sec["title"]), " " + pill(sec["pill"]) if sec["pill"] else ""),
                    [],
                ]
            )
        head = '<h%d id="%s">%s</h%d>' % (sec["level"], sec["id"], esc(sec["title"]), sec["level"])
        if sec["pill"] or sec["define"]:
            head += '<div class="prop-head">%s%s</div>' % (
                pill(sec["pill"]) if sec["pill"] else "",
                '<div class="prop-define">%s</div>' % page.words(at, set(), sec["define"]) if sec["define"] else "",
            )
        piece = [head]
        for n, (kind, v) in enumerate(sec["body"]):
            if kind == "box":
                if not v[2]:
                    raise Stop("front/claims.txt: the box '%s' is empty" % v[1])
                piece.append(
                    '%s<div class="box box-%s"><div class="box-title">%s</div><ul>%s</ul></div>%s'
                    % (
                        '<div class="boxes">' if not n or sec["body"][n - 1][0] != "box" else "",
                        v[0],
                        esc(v[1]),
                        "".join("<li>%s</li>" % page.inline(at, set(), x) for x in v[2]),
                        "</div>" if n + 1 == len(sec["body"]) or sec["body"][n + 1][0] != "box" else "",
                    )
                )
            elif kind == "words":
                piece.append(page.words(at, set(), v))
            elif kind == "label":
                piece.append('<div class="cards-label">%s</div>' % esc(v))
            elif kind == "bullets":
                piece.append(page.words(at, set(), v, "prop-notes"))
            elif kind == "card":
                body.append("".join(piece))
                piece = []
                body.append(card_html(*cards[v]))
            elif kind == "table":
                piece.append(table_html(v))
            elif kind == "fold":
                inside = [k for k, _ in sec["body"][n + 1 :]]
                many = inside[: inside.index("fold-end")].count("card")
                piece.append(
                    '<details class="defgroup" style="max-width:none"><summary>%s%s</summary>'  # as wide as the cards
                    % (
                        esc(v),
                        ' <span class="cnt">· %s</span>' % esc(counted("fold-count", cards=many)) if many else "",
                    )
                )
            elif kind == "fold-end":
                piece.append("</details>")
            elif kind == "definitions":
                piece.append(definitions_html(v))
            elif kind == "closing":
                piece.append(page.words(at, set(), front_lines(folder, "closing.txt", True), "closing"))
            elif kind == "notes":
                piece.append(
                    '<ul class="closing">%s</ul>'
                    % "".join(
                        '<li><a href="%s#%s">%s</a>: %s</li>'
                        % (
                            esc(notes_name),
                            esc(c[0].ident),
                            esc(c[0].full or first_line(c[0])),
                            esc(titles[c[0].ident]),
                        )
                        for c in cards
                        if c[0].ident in noted
                    )
                )
            elif kind == "limits":
                items = []
                for n in sorted(limits):
                    before, title = folded.get(n, (len(limits[n]), ""))
                    words = page.words(at, set(), limits[n][:before])
                    if n in folded:
                        words += '<details class="defgroup"><summary>%s</summary>%s</details>' % (
                            esc(title),
                            page.words(at, set(), limits[n][before:]),
                        )
                    items.append('<li id="lim-%d" value="%d">%s</li>' % (n, n, words))
                piece.append('<ol class="closing">%s</ol>' % "".join(items))
        if piece:
            body.append("".join(piece))
    tiles, tile = [], None
    for l in front_lines(folder, "tiles.txt"):
        as_typed(l, "tiles.txt")
        if l.startswith("+"):
            slot, _, words = (c.strip() for c in l[1:].partition("|"))
            if tile is None or not words:
                raise Stop("front/tiles.txt: '+ slot | words' under a tile: %s" % l)
            if tile[4] and not slot:
                tile[4][-1][1].append(words)
            else:
                tile[4].append((slot, [words]))
        else:
            cells = [c.strip() for c in l.split("|")]
            if len(cells) != 4 or cells[1] not in PILLS or not re.fullmatch("#" + _ID, cells[3]):
                raise Stop("front/tiles.txt: 'title | STATE | status words | #id': %s" % l)
            page.links_to.add(cells[3])
            tile = cells + [[]]
            tiles.append(tile)

    def tile_words(lines):
        if all(l.startswith("- ") for l in lines):
            return '<ul class="prop-ul">%s</ul>' % "".join("<li>%s</li>" % esc(l[2:].strip()) for l in lines)
        if len(lines) != 1 or lines[0].startswith("- "):
            raise Stop("front/tiles.txt: a slot holds one line of words, or bullets alone: %s" % lines[0])
        return esc(lines[0])

    tiles_html = "".join(
        '<a class="prop st-%s" href="%s"><div class="prop-name">%s</div><div class="prop-status">%s</div>'
        '<div class="prop-line">%s</div></a>\n'
        % (
            state,
            esc(href),
            esc(title),
            esc(status),
            "".join(
                '<div class="prop-row"><span class="prop-row-label">%s</span>%s</div>' % (esc(slot), tile_words(lines))
                for slot, lines in slots
            ),
        )
        for title, state, status, href, slots in tiles
    )
    legend = []
    for colour, word, sentence in front_table(folder, "legend.txt", 3):
        as_typed(word + sentence, "legend.txt")
        if colour not in COLOURS + CHIPS:
            raise Stop("front/legend.txt: the colour is one of %s: %s" % (", ".join(COLOURS + CHIPS), colour))
        legend.append(
            '<div><div class="lt"><span class="%s">%s</span></div><div class="ld">%s</div></div>\n'
            % ("chip " + colour if colour in CHIPS else "formal-type %s-type" % colour, esc(word), esc(sentence))
        )
    ids = {"#" + s["id"] for s in sections}
    if any(kind == "limits" for s in sections for kind, _ in s["body"]):
        ids |= {"#lim-%d" % n for n in limits}
    for target in sorted(page.links_to):
        if target.startswith("#") and target not in ids:
            raise Stop("the data link to %s, and the page has no such place" % target)
        if not target.startswith("#") and not os.path.isfile(os.path.join(root, *target.split("/"))):
            raise Stop("the data link to %s, and the Lean folder has no such file" % target)
    if any(kind == "limits" for s in sections for kind, _ in s["body"]) and set(limits) - limits_used:
        raise Stop(
            "front/limits.txt: no card leads to limit %s" % ", ".join(str(n) for n in sorted(set(limits) - limits_used))
        )
    fill = {
        "LICENCE": FRONT_LICENCE,
        "POLICY": "default-src 'none'; style-src 'sha256-%s'; style-src-attr 'unsafe-inline'; script-src 'sha256-%s'; "
        "base-uri 'none'; form-action 'none'"
        % (sha256_base64("\n" + parts["page.css"] + "\n"), sha256_base64("\n" + script + "\n")),
        "HTML_TITLE": esc(label["html-title"]),
        "META_DESC": esc(label["description"]),
        "CSS": parts["page.css"],
        "BRAND": esc(label["brand"]),
        "H1": esc(label["title"]),
        "SUBTITLE": esc(label["subtitle"]),
        "BYLINE": esc(label["byline"]),
        "SETTING": in_lines(page.words(context, set(), front_lines(folder, "setting.txt", True))),
        "TILES_TITLE": esc(label["tiles-title"]),
        "TILES_NOTE": esc(label["tiles-note"]),
        "PROPS": in_lines(tiles_html),
        "LEGEND": in_lines("".join(legend)),
        "TOC": in_lines(
            "".join(h + ("<ul>%s</ul>" % "".join(kids) if kids else "") + "</li>" for h, kids in contents)
        ),
        "CARDS": in_lines("\n".join(body)),
        "APPENDIX_SUMMARY": esc(label["appendix"]),
        "N_DECLS": "{:,}".format(len(order)),
        "SEARCH_HINT": esc(label["search-hint"]),
        "DATA": payload,
        "JS": script,
    }
    asked = re.findall(r"%%([A-Z0-9_]+)%%", parts["page_template.html"])
    if sorted(asked) != sorted(fill):
        raise Stop(
            "%s: its places are not the %d that this program fills, each once"
            % (os.path.join(shell, SHELL[0]), len(fill))
        )
    for key, text in fill.items():  # the style sheet and the script are the shell's, and are printed as they are
        unseen = [c for c in text if c not in "\n\t" and cannot_be_seen(c)] if key not in ("CSS", "JS") else []
        if unseen:
            raise Stop(
                "the front page would hold the character U+%04X, which cannot be seen: it stands in a file of %s or in "
                "an embedded Lean text" % (ord(unseen[0]), folder)
            )
    document = re.sub(r"%%([A-Z0-9_]+)%%", lambda m: fill[m.group(1)], parts["page_template.html"])
    ids = re.findall(r'\sid="([^"]*)"', re.sub(r"%%(?:CSS|JS|DATA)%%", "", parts["page_template.html"]))
    ids += [
        i for key, text in fill.items() if key not in ("CSS", "JS", "DATA") for i in re.findall(r'\sid="([^"]*)"', text)
    ]
    if len(ids) != len(set(ids)):
        raise Stop("the front page would have the id '%s' twice" % next(i for i in ids if ids.count(i) > 1))
    longest = max(document.split("\n"), key=len)
    if len(longest) > MOST_LINE:
        raise Stop(
            "the front page would have a line of %d characters: more than %d. A paragraph, a list item, a table's row "
            "or a line of an embedded Lean file is that long: split it, or take it off the page. The line begins: %s"
            % (len(longest), MOST_LINE, longest[:120])
        )
    parted = re.search(r"[0-9],\n[0-9]", document)
    if parted:  # no data file can bring this about: a file of shell/, or a fault of this program
        raise Stop(
            "the front page's line %d would end with a number and a comma, and the next begin with a number: no line "
            "end may stand there. This program writes none itself: look at the files of shell/"
            % document.count("\n", 0, parted.end())
        )
    for name in SHELL:
        say(
            "the front page: sha256 of shell/%s, for the checker: %s"
            % (name, hashlib.sha256(parts[name].encode("utf-8")).hexdigest())
        )
    say(
        "the front page: %d sections, %d cards, %d declarations embedded from %d files, %d lines of Lean, %d links; "
        "its longest line has %d characters"
        % (
            len(sections),
            len(cards),
            len(order),
            len(files),
            embedded_lines,
            sum(len(v) // 3 for f in links_data.values() for v in f.values()),
            len(longest),
        )
    )
    if page.unlinked:
        some = sorted(set(page.unlinked))
        say(
            "the front page: code in words in which no name is a link (%d different): %s"
            % (len(some), " | ".join(some[:200]))
        )
    return document


LIST_HEADER = "part\tkind\tfull name\tfile"


FRONT_SIGN = b"style-src-attr"  # in the policy line of the front page's frame, and of no other page


def own_making(beginning, signs):
    """Does a file that begins with these bytes look like one that this program made, of the kind that is to be written?
    signs: (its first bytes, bytes that must come soon after, and then bytes that must not). An empty file is free."""
    return not beginning or (
        beginning.startswith(signs[0]) and signs[1] in beginning and not any(s and s in beginning for s in signs[2:])
    )


def why_not_write(path, ending, signs, overwrite):
    """The early, friendly look, before the long scan: None if the program may write 'path', else the reason."""
    if not path.endswith(ending):
        return "its name must end in %s" % ending
    if os.path.islink(path):
        return "it is a link"
    if not os.path.isdir(os.path.dirname(os.path.abspath(path))):
        return "its folder does not exist"
    if os.path.lexists(path):
        if not os.path.isfile(path):
            return "it exists and is not a plain file"
        if os.lstat(path).st_nlink > 1:
            return "it has a second name (a hard link)"
        if not os.access(path, os.W_OK):
            return "this user may not write it (a run under sudo, or by another user, leaves such a file)"
        try:  # without waiting, should the name have become a pipe since the line above
            fd = os.open(path, os.O_RDONLY | getattr(os, "O_NONBLOCK", 0) | getattr(os, "O_NOFOLLOW", 0))
            try:
                beginning = os.read(fd, 2000)
            finally:
                os.close(fd)
        except OSError as e:
            return "it cannot be read: %s" % e.strerror
        if not overwrite and not own_making(beginning, signs):
            return (
                "it %s (--overwrite replaces it all the same, and every other file that this call names: what lies in "
                "them now is then lost)"
                % (
                    "looks like another of this program's pages: OUTPUT_HTML is the long page, --short the short one, "
                    "--front the front page"
                    if beginning.startswith(("<!DOCTYPE html>\n<!--\n%s\n" % LICENCE).encode("utf-8"))
                    and b"<title>" in beginning
                    else "exists and was not made by this program"
                )
            )
    return None


BEING_WRITTEN = []  # the file that is being filled, for the message if the run ends there
STUMP = (
    "The file is now empty or cut short; what lay in it before, if anything, is lost. The same call makes it again; if "
    "it then refuses a short stump as not of its own making, give --overwrite"
)


def write_file(path, data, signs, overwrite):
    """Write by descriptor, and look at what was opened: the name may have changed hands since the early look.
    Returns True if the file was there before. Raises OSError, with a reason, if it will not write."""
    # not every system has these three; O_BINARY keeps the line ends as they are where text mode is the default
    flags = getattr(os, "O_NOFOLLOW", 0) | getattr(os, "O_BINARY", 0)
    try:
        fd, existed = os.open(path, os.O_WRONLY | os.O_CREAT | os.O_EXCL | flags, 0o666), False
    except FileExistsError:
        try:
            fd, existed = os.open(path, os.O_RDWR | getattr(os, "O_NONBLOCK", 0) | flags), True
        except OSError as e:
            raise OSError(0, "it is a link" if e.errno == errno.ELOOP else e.strerror)
        state = os.fstat(fd)
        try:  # a hard link may have been laid and taken away again: the name must still lead here, and be the only one
            there = os.lstat(path)
        except OSError:
            there = None
        if (
            not stat.S_ISREG(state.st_mode)
            or state.st_nlink > 1
            or there is None
            or not os.path.samestat(there, state)
            or there.st_nlink > 1
            or (not overwrite and not own_making(os.read(fd, 2000), signs))
        ):
            os.close(fd)
            raise OSError(0, "it has changed since the program began")
        os.lseek(fd, 0, 0)
    BEING_WRITTEN[:] = [path]
    if existed:
        os.ftruncate(fd, 0)
    try:
        with os.fdopen(fd, "wb") as f:
            f.write(data)
    except OSError as e:
        raise OSError(0, "%s. %s" % (e.strerror, STUMP))
    del BEING_WRITTEN[:]
    return existed


def main(argv):
    if sys.version_info < (3, 7):
        sys.stderr.write("This program needs Python 3.7 or later.\n")
        return 2
    for stream in (sys.stdout, sys.stderr):  # a terminal that cannot show a character gets its escape, not a traceback
        if hasattr(stream, "reconfigure"):
            stream.reconfigure(errors="backslashreplace")
    usage = __doc__.split("\n\nWHAT THE LONG PAGE")[0] + "\n"
    if "--help" in argv or "-h" in argv:
        sys.stdout.write(usage)
        return 0
    switches = [a for a in argv[1:] if a.startswith("--")]
    plain = [a for a in argv[1:] if not a.startswith("--")]
    with_value = ("--list-theorems=", "--heads=", "--short=", "--long-name=", "--front=")
    unknown = [a for a in switches if a != "--overwrite" and not a.startswith(with_value)]
    if len(plain) != 2 or unknown:
        sys.stderr.write("".join("unknown switch: %s\n" % plainly(a, "") for a in unknown) + usage)
        return 2
    value = lambda name: [a.split("=", 1)[1] for a in switches if a.startswith("--%s=" % name)]
    root, output = plain
    begins = ("<!DOCTYPE html>\n<!--\n%s\n-->\n" % LICENCE).encode("utf-8")
    long_title = b"%s</title>" % TITLE_ENDS.encode("utf-8")
    targets = [(output, ".html", (begins, long_title, b""))][: output != "-"]
    targets += [(p, ".tsv", ((LIST_HEADER + "\n").encode("utf-8"), b"", b"")) for p in value("list-theorems")]
    short = front = None
    if len(value("short")) > 1 or len(value("long-name")) > 1 or len(value("front")) > 1:
        sys.stderr.write("--short, --front and --long-name go once each\n")
        return 2
    if bool(value("long-name")) != (bool(value("short") or value("front")) and output == "-"):
        sys.stderr.write(
            "--long-name=NAME.html goes with --short or --front and '-', and only there: the pages then go to standard "
            "output, the long one first, and it says how the long page is called in the other pages' links\n"
        )
        return 2
    if value("short"):
        short = {
            "long": os.path.basename((value("long-name") + [output])[0]),
            "short": os.path.basename(value("short")[0]),
        }
        if short["long"] == short["short"] or not all(
            re.fullmatch(r"[A-Za-z0-9_.-]+\.html", n) for n in short.values()
        ):
            sys.stderr.write(
                "the two pages want two different file names, of letters, digits, '_', '-' and '.', ending in .html\n"
            )
            return 2
        if output != "-":
            targets.append((value("short")[0], ".html", (begins, b"<title>", long_title, FRONT_SIGN)))
    if value("front"):
        front = {
            "long": os.path.basename((value("long-name") + [output])[0]),
            "front": os.path.basename(value("front")[0]),
        }
        others = [front["long"]] + ([short["short"]] if short else [])
        if front["front"] in others or not all(re.fullmatch(r"[A-Za-z0-9_.-]+\.html", n) for n in front.values()):
            sys.stderr.write(
                "the pages want different file names, of letters, digits, '_', '-' and '.', ending in .html\n"
            )
            return 2
        if output != "-":
            front_begins = ("<!DOCTYPE html>\n<!--\n%s\n-->\n" % FRONT_LICENCE).encode("utf-8")
            targets.append((value("front")[0], ".html", (front_begins, FRONT_SIGN, long_title)))
    # before the long scan, and before anything is written; every refused file is named, not the first alone
    looks = [(path, why_not_write(path, ending, signs, "--overwrite" in switches)) for path, ending, signs in targets]
    if any(reason for _, reason in looks):
        sys.stderr.write("".join("will not write %s: %s\n" % (plainly(p, ""), r) for p, r in looks if r))
        return 2
    if not os.path.isdir(os.path.join(root, CHOSEN_FOLDERS[0])):  # before also.txt is held against a wrong folder
        sys.stderr.write(
            "%s: no folder %s/ in it. Is it the repository's lean/ folder?\n" % (plainly(root, ""), CHOSEN_FOLDERS[0])
        )
        return 2
    heads = (value("heads") or [os.path.join(os.path.dirname(os.path.abspath(__file__)), "statements-html")])[-1]
    try:
        for name in ("head.txt", "head-how.txt", "head-other.txt", "head-onbytes.txt"):
            small_text(os.path.join(heads, name), 100000)  # an early look: a link, a pipe, a huge file
        also = small_text(os.path.join(heads, "also.txt"), 10000) or ""; read_unnumbered(root, heads)
    except Stop as e:
        sys.stderr.write("%s\n" % plainly(str(e), ""))
        return 2
    for folder in [l.strip() for l in also.split("\n") if l.strip()]:
        parts = folder.split("/")
        steps = [os.path.join(root, *parts[: k + 1]) for k in range(len(parts))]
        if (
            not re.fullmatch(r"[A-Za-z0-9_]+(?:/[A-Za-z0-9_]+)*", folder)
            or not all(os.path.isdir(s) and not os.path.islink(s) for s in steps)
            or any(
                (folder + "/").startswith(f + "/") or (f + "/").startswith(folder + "/")
                for f in CHOSEN_FOLDERS + [ONBYTES_FOLDER]
            )
        ):
            sys.stderr.write(
                "%s names %r: it must be a path of plain names, from %s, to a real folder (no link on the way) that "
                "neither holds nor lies in a folder that the page shows already\n"
                % (plainly(os.path.join(heads, "also.txt"), ""), folder, plainly(root, ""))
            )
            return 2
        CHOSEN_FOLDERS.append(folder)
    log = sys.stderr if output == "-" else sys.stdout
    theorems = [LIST_HEADER]
    try:
        document = build(root, heads, lambda s: log.write(plainly(s) + "\n"), theorems, short, front)
    except Stop as e:
        sys.stderr.write(
            "STOPPED: %s\nNothing was written. If the place is in a Lean file, the scanner does not know that "
            "form: change the Lean text, or teach the scanner (section 2 of this program). If a .txt file is named, "
            "mend it: the head texts lie in %s, the short page's files in its folder short/, the front page's in "
            "front/ "
            "and shell/.\n" % (plainly(str(e), ""), plainly(heads, ""))
        )
        return 1
    except (RecursionError, MemoryError, OSError) as e:
        why = {
            RecursionError: "something in a Lean file is nested deeper than this program can follow",
            MemoryError: "the memory does not suffice",
        }.get(type(e)) or "%s: %s" % (getattr(e, "filename", None), getattr(e, "strerror", None) or e)
        sys.stderr.write("STOPPED: %s\nNothing was written.\n" % plainly(why, ""))
        return 1
    if output == "-":
        try:
            more = (short["document"] if short else "") + (front["document"] if front else "")
            sys.stdout.buffer.write((document + more).encode("utf-8"))
            sys.stdout.buffer.flush()
        except OSError as e:
            sys.stderr.write("could not write the page to standard output: %s\n" % e.strerror)
            sys.stderr.flush()
            os.dup2(os.open(os.devnull, os.O_WRONLY), sys.stdout.fileno())  # so that Python's own last flush is silent
            return 1
    texts = [document][: output != "-"] + ["\n".join(theorems) + "\n"] * len(value("list-theorems"))
    texts += [x["document"] for x in (short, front) if x and output != "-"]
    for (path, _, signs), text in zip(targets, texts):
        try:
            existed = write_file(path, text.encode("utf-8"), signs, "--overwrite" in switches)
        except OSError as e:
            sys.stderr.write("could not write %s: %s\n" % (plainly(path, ""), e.strerror))
            return 1
        log.write(
            "%s %s: %d bytes\n" % ("replaced" if existed else "wrote", plainly(path, ""), len(text.encode("utf-8")))
        )
    return 0


# Numbers left out of comments (unnumbered.txt).
UNNUMBERED = []  # from unnumbered.txt: paths from the Lean folder, each a Lean file (A/B.lean) or a folder (A/)
AS_IT_LIES = {}  # by path: a listed file's own text, for the sha256 of the file that the front page gives
_DOTTED, _WHOLE = r"[0-9]+(?:\.[0-9]+)+", r"[0-9]+(?!\.?[0-9])"
_NEXT = r"(?:,\s*and\s+|,\s*|\s+and\s+|\s+to\s+|\s+or\s+|[-–/])"
# A list goes on only with numbers of the same form; a list of whole numbers needs the plural (Sections 2 and 3), so
# 'Section 2, 128 bits' keeps its 128.
NUMBERED = re.compile(
    r"\b(?:[Dd]efinition|[Ss]ection|[Pp]roposition)(?:s?\s+{d}(?:{n}{d})*|s\s+{w}(?:{n}{w})*|\s+{w})".format(
        d=_DOTTED, w=_WHOLE, n=_NEXT
    )
)


def read_unnumbered(root, heads):
    """Fill UNNUMBERED from unnumbered.txt in the folder 'heads', if it lies there. Each line is the path, from the Lean
    folder 'root', of a Lean file (A/B.lean) or a folder (A/). Raises Stop on a line that is not such a path or that
    names no Lean file."""
    del UNNUMBERED[:]
    AS_IT_LIES.clear()
    files, where = None, plainly(os.path.join(heads, "unnumbered.txt"), "")
    lines = (small_text(os.path.join(heads, "unnumbered.txt"), 10000) or "").split("\n")
    for place in [l.strip() for l in lines if l.strip()]:
        files = lean_files(root) if files is None else files
        if not re.fullmatch(r"[A-Za-z0-9_]+(?:/[A-Za-z0-9_]+)*(?:/|\.lean)", place):
            raise Stop(
                "%s: the line %r is not a path of letters, digits, '_' and '/' that ends in .lean or '/'" % (where, place)
            )
        if not any(p == place or (place.endswith("/") and p.startswith(place)) for p in files):
            raise Stop(
                "%s: the line %r names no Lean file, and no folder with Lean files, under %s" % (where, place, root)
            )
        UNNUMBERED.append(place)


def unnumbered(path, text):
    """The text of the Lean file 'path' (a path from the Lean folder) as every page shows it. In a file that
    unnumbered.txt lists, or that lies in a folder it lists, the numbers behind Section, Definition or Proposition in
    comments and doc comments become '…' ("Definition …"). Strings stay as they are, and nothing else changes."""
    if not any(path == p or (p.endswith("/") and path.startswith(p)) for p in UNNUMBERED):
        return text
    probe = Source.__new__(Source)  # not Source(...): __init__ would read the file and call unnumbered() again
    probe.path, probe.text, probe.spans = path, text, []
    probe.line_starts = [0] + [m.end() for m in re.finditer("\n", text)]
    probe._find_spans()
    pieces, i = [], 0
    for s, e, kind in probe.spans:
        if kind not in ("string", "char"):
            pieces += [text[i:s], NUMBERED.sub(lambda m: re.sub(r"[0-9]+(?:\.[0-9]+)*", "…", m.group()), text[s:e])]
            i = e
    AS_IT_LIES[path] = text
    return "".join(pieces) + text[i:]


if __name__ == "__main__":
    try:
        sys.exit(main(sys.argv))
    except KeyboardInterrupt:
        sys.stderr.write(
            "\nInterrupted while writing %s. %s.\n" % (plainly(BEING_WRITTEN[0], ""), STUMP)
            if BEING_WRITTEN
            else "\nInterrupted. No file was being written.\n"
        )
        sys.exit(130)
