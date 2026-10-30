#!/usr/bin/env python3
# Copyright 2026 Anthropic PBC
# SPDX-License-Identifier: Apache-2.0
r"""Compare the stored full-size public files of the Lean library with the package's example files.

Usage, from the repository's lean/ folder:
    python3 -B scripts/check_stored_examples.py . ../examples
    python3 -B scripts/check_stored_examples.py . ../examples --self-test

In general:
    check_stored_examples.py LEAN_FOLDER EXAMPLES_FOLDER [--self-test]

WHY. The goals of Ladder.lean, and every theorem "at storedPublicFiles" or "at zGap", are about two
terms of Ladder/Stored.lean: three public files each (parameter file, layout file, scale file),
written out in Lean. No theorem ties these terms to a file on disk. What comes nearest in Lean is
evaluated, not proved: the scope test of 'verify' (VerifierAndGoals.InScope) compares the layout
file that it is given, and the parameter file but for eight numbers, with storedPublicFiles's; and
'#guard' tests compare each term's digest with digits written in the Lean files (B below). This
program compares the terms with the example files themselves, from outside:
    VerifierAndGoals.storedPublicFiles   with   EXAMPLES_FOLDER/full-size/config/
    VerifierAndGoals.zGap                with   EXAMPLES_FOLDER/full-size-clipped-gap/config/
in each folder policy.txt (field pol), layout.txt (field lay) and KL.bin (field KL).

WHAT IT IS FOR. It catches accidents and drift: a literal, a numeral, an example file or a
definition that was changed on one side and not on the other. It is no defence against an author
who changes the Lean files in order to deceive it. Against that stand the build, a reader, and the
sha256 sums of Ladder/Stored.lean and Ladder/Guards.lean in scripts/check.py (step 'words'). The
other five Lean files that are read here have no such sum anywhere, though two of them spell the
layout file and the scale file: what holds these two fields is the digest test, at a build.

It only reads: seven Lean files and six example files. It writes, creates and removes no file,
opens no connection, starts no program and runs no Lean. It is written for Python 3.7 or later
with the standard library alone (it was run on 3.12 and 3.13). Exit code 0: every comparison
holds; 1: one fails, or the program cannot go on (it prints what it has found and a line 'CANNOT
CHECK: ...'); 2: a wrong call. Each file must be a regular file of at most 1 MiB and not itself a
link (links among the folders above it are followed).

THE COMPARISONS
 B. Against values in Lean's own tests. Ladder/Guards.lean has tests ('#guard') that Lean evaluates
    when it compiles that file: the fields' sizes; that zGap shares two fields with
    storedPublicFiles; and the digest of each term's three fields under the format's hash function,
    against 64 hexadecimal digits. That digest is BLAKE2b (32 bytes, no key, zero salt and
    personalisation) of the 8-byte little-endian words 169, 2 and the number of files, then each
    file after the word of its length. This program computes it for the EXAMPLE FOLDER's three files
    and compares it with the digits in the text of Guards.lean; likewise the sizes and the shared
    files. If Guards.lean was compiled from these sources, Lean has tied the terms, as it elaborates
    them, to the same digits.
 A. Against the text. storedPublicFiles is not three literals: its parameter file is 'policyFile
    storedLines' (string literals, and eleven lines that Lean makes from eight numbers), its layout
    file one literal, its scale file 'wordsFile scalesF' (a list of numerals, four bytes each). This
    program reimplements policyFile, textOf and wordsFile in Python, computes the bytes from the
    literals and numerals in the Lean files, and compares them with the example files (it prints
    length and sha256). Six rows.
 C. The digest of B, computed for the bytes of A, against the same digits. It connects A and B.
 H. The lengths and sha256 sums in the comment at the top of Ladder/Stored.lean, against A's bytes.
 P. The Lean text on which all this relies, token for token, against patterns in this program
    (white space and comments aside, but that a command must begin at the start of a line and
    nothing else may). Stored.lean and the two files under OnBytes/Tie/Pv/Plan/ must
    consist of the expected commands and nothing else. In Guards.lean and three files under Fmt/
    every command must begin in one of the listed ways, the imports and namespaces must be the
    expected ones, and each reimplemented definition must be as expected. The common words and
    characters with which a file can change how Lean reads the rest are refused (the list is not
    complete), and so are a few forms of comments, names and literals on which this program's small
    tokenizer and Lean's might disagree. If anything under P has changed, the program stops: it no
    longer knows what it would be comparing.

WHAT A PASS IS WORTH
  - B counts only beside a build of these very sources (scripts/check.py, step 'build'). This
    program does not look at compiled files: it cannot know that Guards.lean was ever compiled.
    Without that build, B compares the example files with digits in a text file. A '#guard' is an
    evaluation by Lean's evaluator, not a proof checked by the kernel.
  - A, C and H see text, not what Lean elaborates.
  - All parts rely on this program's reading of seven files, and none follows imports. What
    '#guard', '==', 'String.join' or 'Fmt.blake2b' mean comes from files that are not read here.
  - B and C also rely on BLAKE2b (two different triples of files with one digest are taken to be out
    of reach), on Python's hashlib, and on Lean's Fmt.blake2b being BLAKE2b (Fmt/Blake2bKnown.lean).
  - Nothing is said about where the example files come from: not that the programs made them, not
    that they fit the other files of their folders; and nothing about the two small example sets,
    which no term of Ladder/ spells. The example's weights are synthetic.
  - So the connection is checked by a program that ships, not by Lean.

--self-test: negative tests of this program. It reads the same thirteen files, then plants one fault
at a time IN MEMORY (nothing is written) and repeats all comparisons. For each fault it prints which
comparisons failed, and compares them, as a set, with the ones that should. A few harmless changes
must be detected nowhere. Exit code 0 only if the unchanged files pass and every fault does just
what is expected. Not exercised: reading files from disk, and the refusals there. The self-test
finds its places by the Lean files' present line breaks: on files that were only laid out anew it
can stop ('does not find its place') though the plain call passes.
"""

import sys

if __name__ == '__main__' and not sys.flags.isolated and not getattr(sys.flags, 'safe_path', False):
    # This program's own folder leaves Python's search path before anything else is imported: a file
    # there with the name of a library module must not run in that module's place.
    del sys.path[0]

import hashlib
import os
import stat

MAX_BYTES = 1024 * 1024

STORED = 'Ladder/Stored.lean'
GUARDS = 'Ladder/Guards.lean'
KITS = 'OnBytes/Tie/Pv/Plan/PlanKits.lean'
LAYOUT = 'OnBytes/Tie/Pv/Plan/PlanLayoutFull.lean'
RULES1 = 'Fmt/Rules1.lean'
RULES23 = 'Fmt/Rules23.lean'
RULES4 = 'Fmt/Rules4.lean'
LEAN_FILES = [STORED, GUARDS, KITS, LAYOUT, RULES1, RULES23, RULES4]

FIELDS = [('pol', 'policy.txt'), ('lay', 'layout.txt'), ('KL', 'KL.bin')]
TERMS = [('storedPublicFiles', 'full-size/config'), ('zGap', 'full-size-clipped-gap/config')]
EXAMPLE_FILES = ['%s/%s' % (folder, name) for _, folder in TERMS for _, name in FIELDS]


USAGE = """Usage, from the repository's lean/ folder:
    python3 -B scripts/check_stored_examples.py . ../examples
    python3 -B scripts/check_stored_examples.py . ../examples --self-test"""


def plain(s):
    """For everything that is printed and may hold text out of a file or a folder's name: a
    character that cannot be seen (a control character, a line end, a change of direction) is
    written as its escape, so that it cannot forge a line or steer the reader's terminal."""
    return ''.join(c if c.isprintable() else c.encode('unicode_escape').decode('ascii') for c in s)


class CannotCheck(Exception):
    """The program cannot go on: a file is missing, or its text is not what can be read here."""


# ------------------------------------------------------------------------------------------------
# Lean's text, as tokens

class Lit(str):
    """The string that a literal spells; 'raw' is its text in the file, between the quotes."""
    raw = ''


ESCAPES = {'\\': '\\', '"': '"', "'": "'", 'n': '\n', 't': '\t', 'r': '\r'}
HEX = '0123456789abcdefABCDEF'


def word_char(c):
    return c.isalnum() or c in "_'.!?"


def read_escape(s, i, where, line):
    """s[i] is the character after a backslash. Returns the character that the escape stands for,
    and the place after the escape."""
    c = s[i] if i < len(s) else ''
    if c in ESCAPES:
        return ESCAPES[c], i + 1
    if c in ('x', 'u'):
        n = 2 if c == 'x' else 4
        digits = s[i + 1:i + 1 + n]
        if len(digits) == n and all(d in HEX for d in digits):
            value = int(digits, 16)
            if not 0xD800 <= value <= 0xDFFF:
                return chr(value), i + 1 + n
    raise CannotCheck('%s, line %d: an escape in a literal that this program does not know'
                      % (where, line))


def odd_opener(s, i, where, line):
    """Refuses the comments on whose end this program's reading and Lean's might disagree."""
    if s.startswith('/-/', i) or s.startswith('/--/', i) or s.startswith('/-!/', i):
        raise CannotCheck('%s, line %d: a comment that opens with %s' % (where, line, s[i:i + 4]))
    if s.startswith('/--', i) or s.startswith('/-!', i):
        j = i + 3
        while j < len(s) and s[j] in ' \t\n':
            j += 1
        if s.startswith('--', j) or s.startswith('/-', j):
            raise CannotCheck('%s, line %d: a comment that opens with %s and then another comment'
                              % (where, line, s[i:i + 3]))


def tokens(s, where):
    """The tokens of a Lean text, comments left out: a list of (kind, value, line, column). kind:
    'str' (a string literal; value: the string that it spells), 'chr', 'num', 'word', 'sign' (any
    other single character)."""
    out = []
    i, line, start = 0, 1, 0
    n = len(s)
    while i < n:
        c = s[i]
        if c == '\n':
            i += 1
            line += 1
            start = i
        elif c in ' \t\r':
            i += 1
        elif s.startswith('--', i):
            while i < n and s[i] != '\n':
                i += 1
        elif s.startswith('/-', i):
            depth, first = 1, line
            odd_opener(s, i, where, line)
            i += 2
            while depth:
                if i >= n:
                    raise CannotCheck('%s, line %d: a comment that does not end' % (where, first))
                if s.startswith('/-', i):
                    odd_opener(s, i, where, line)
                    depth += 1
                    i += 2
                elif s.startswith('-/', i):
                    depth -= 1
                    i += 2
                else:
                    if s[i] == '\n':
                        line += 1
                        start = i + 1
                    i += 1
        elif c == '"':
            first, column, opened = line, i - start, i + 1
            i += 1
            parts = []
            while True:
                if i >= n:
                    raise CannotCheck('%s, line %d: a literal that does not end' % (where, first))
                d = s[i]
                if d == '"':
                    i += 1
                    break
                if d == '\\':
                    if i + 1 < n and s[i + 1] == '\n':
                        # a backslash at a line's end: Lean skips the line break and the white
                        # space that follows it, and refuses a second line break there
                        i += 2
                        line += 1
                        start = i
                        while i < n and s[i] in ' \t':
                            i += 1
                        if i < n and s[i] == '\n':
                            raise CannotCheck('%s, line %d: an empty line after a backslash at a '
                                              "line's end, inside a literal" % (where, line))
                    else:
                        ch, i = read_escape(s, i + 1, where, line)
                        parts.append(ch)
                else:
                    if d == '\n':
                        line += 1
                        start = i + 1
                    parts.append(d)
                    i += 1
            lit = Lit(''.join(parts))
            lit.raw = s[opened:i - 1]
            out.append(('str', lit, first, column))
        elif c == "'" and i + 2 < n and s[i + 1] != '\\' and s[i + 2] == "'":
            out.append(('chr', s[i + 1], line, i - start))
            i += 3
        elif c == "'" and i + 1 < n and s[i + 1] == '\\':
            column = i - start
            ch, j = read_escape(s, i + 2, where, line)
            if j >= n or s[j] != "'":
                raise CannotCheck('%s, line %d: a character literal that does not end'
                                  % (where, line))
            out.append(('chr', ch, line, column))
            i = j + 1
        elif word_char(c) and c not in "'.!?":
            j = i
            while j < n and word_char(s[j]):
                j += 1
            text = s[i:j]
            if j < n and (s[j] == '"' and text != 's!' or s[j] == '#' and text == 'r'):
                raise CannotCheck('%s, line %d: a literal with the word %s right in front of it (a '
                                  'raw string, or a form that this program does not know)'
                                  % (where, line, text))
            out.append(('num' if text.isdigit() and text.isascii() else 'word', text, line,
                        i - start))
            i = j
        else:
            if c in '\u00ab\u00bb':
                raise CannotCheck('%s, line %d: a name in French quotes' % (where, line))
            out.append(('sign', c, line, i - start))
            i += 1
    return out


def bare(toks):
    """Tokens without their places, for comparisons."""
    return [(k, v) for k, v, _, _ in toks]


def commands(toks):
    """The tokens cut into commands: a command begins at a token in a line's first column."""
    out = []
    for t in toks:
        if t[3] == 0 or not out:
            out.append([])
        out[-1].append(t)
    return out


def named(cmds, where):
    """A dictionary: full name of a definition or structure -> its commands (a list, so that a name
    that is declared twice shows). The names of the namespaces that are open at the command are put
    in front."""
    out = {}
    stack = []
    for c in cmds:
        b = bare(c)
        head = b[0][1]
        if head == 'namespace' and len(b) == 2:
            stack.append(b[1][1])
        elif head == 'section':
            stack.append(None)
        elif head == 'end':
            if not stack:
                raise CannotCheck("%s, line %d: an 'end' that closes nothing" % (where, c[0][2]))
            stack.pop()
        elif head in ('def', 'structure') and len(b) > 1:
            full = '.'.join([x for x in stack if x] + [b[1][1]])
            out.setdefault(full, []).append(c)
    return out


# ------------------------------------------------------------------------------------------------
# What the Lean files must say

# Words with which a Lean file can change how what follows is read, or what a name means.
BARRED = ('macro macro_rules syntax notation notation3 infix infixl infixr prefix postfix elab '
          'elab_rules declare_syntax_cat attribute instance local scoped open export run_cmd '
          'run_elab run_meta initialize builtin_initialize unsafe implemented_by extern csimp '
          'binder_predicate unif_hint mutual include omit universe variable deriving private '
          'protected noncomputable partial nonrec').split()
# In the three files under Fmt/ two of these words are in order: 'deriving' (on a type that no
# pinned text uses) and 'variable' (one line of Fmt/Rules4.lean, which is pinned below).
BARRED_FMT = [w for w in BARRED if w not in ('deriving', 'variable')]

# Words that begin a command. They are refused in all seven files unless they stand at the start of
# a line, so that the cut into commands, and the namespaces that are open at a command, are what
# they seem.
COMMAND_WORDS = ('import namespace section end def abbrev theorem lemma example structure '
                 'inductive class opaque axiom set_option variable termination_by '
                 'decreasing_by').split()

# How a command may begin, file by file ('#guard': the character # and the word guard).
HEADS = {
    GUARDS: 'import namespace def #guard end'.split(),
    RULES1: 'namespace def theorem inductive termination_by abbrev #guard end'.split(),
    RULES23: 'import set_option namespace def structure theorem #guard end'.split(),
    RULES4: 'import namespace def structure section variable #guard end'.split(),
}

# Commands that must stand in a file just so, and no other command with the same first word.
FIXED = {
    GUARDS: ['import Ladder', 'namespace VerifierAndGoals', 'end VerifierAndGoals'],
    RULES1: ['namespace Fmt', 'end Fmt'],
    RULES23: ['import Fmt.Blake2b', 'import Fmt.Rules1', 'set_option autoImplicit false',
              'namespace Fmt', 'end Fmt'],
    RULES4: ['import Fmt.Plan', 'import Fmt.Rules23', 'namespace Fmt', 'section',
             'variable {m : Type → Type} [Monad m] '
             '(h : Nat → Nat → Nat → ByteArray → ByteArray → m ByteArray)',
             'end', 'namespace Toy4', 'end Toy4', 'end Fmt'],
}

# The definitions under Fmt/ that this program reimplements. The text is compared token for token.
# In a pattern, NUM stands for one numeral, STR for one string literal, NUMS and STRS for a list of
# them with commas between.
PINS = [
    (RULES1, 'Fmt.unhexDigit', r'''
def unhexDigit (c : Char) : UInt8 :=
  let n := c.toNat
  if 48 ≤ n ∧ n ≤ 57 then UInt8.ofNat (n - 48)
  else if 97 ≤ n ∧ n ≤ 102 then UInt8.ofNat (n - 87)
  else if 65 ≤ n ∧ n ≤ 70 then UInt8.ofNat (n - 55)
  else 0
'''),
    (RULES1, 'Fmt.unhexL', r'''
def unhexL : List Char → List UInt8
  | a :: b :: l => ((unhexDigit a <<< 4) ||| unhexDigit b) :: unhexL l
  | _ => []
'''),
    (RULES1, 'Fmt.unhex',
     'def unhex (s : String) : ByteArray := ⟨(unhexL s.toList).toArray⟩'),
    (RULES1, 'Fmt.u64', r'''
def u64 (x : UInt64) : ByteArray :=
  ⟨#[x.toUInt8, (x >>> 8).toUInt8, (x >>> 16).toUInt8, (x >>> 24).toUInt8, (x >>> 32).toUInt8,
    (x >>> 40).toUInt8, (x >>> 48).toUInt8, (x >>> 56).toUInt8]⟩
'''),
    (RULES1, 'Fmt.u64n', 'def u64n (x : Nat) : ByteArray := u64 (UInt64.ofNat x)'),
    (RULES1, 'Fmt.zeroBytes', 'def zeroBytes (n : Nat) : ByteArray := ⟨Array.replicate n 0⟩'),
    (RULES1, 'Fmt.zero32', 'def zero32 : ByteArray := zeroBytes 32'),
    (RULES1, 'Fmt.fit', r'''
def fit (n : Nat) (b : ByteArray) : ByteArray :=
  if n ≤ b.size then b.extract 0 n else b ++ zeroBytes (n - b.size)
'''),
    (RULES1, 'Fmt.cat',
     'def cat (l : List ByteArray) : ByteArray := l.foldl (· ++ ·) ByteArray.empty'),
    (RULES1, 'Fmt.text', 'def text (b : ByteArray) : ByteArray := u64n b.size ++ b'),
    (RULES23, 'Fmt.dlen', 'def dlen (number : Nat) : Nat := if number = 162 then 64 else 32'),
    (RULES23, 'Fmt.label', r'''
def label (number tree index : Nat) : ByteArray := u64n (number + 65536 * tree) ++ u64n index
'''),
    (RULES23, 'Fmt.formatHash', r'''
def formatHash (number tree index : Nat) (start bytes : ByteArray) : ByteArray :=
  blake2b (dlen number) ((fit 32 start).extract 0 16)
    ((fit 32 start).extract 16 32) (label number tree index ++ bytes)
'''),
    (RULES4, 'Fmt.configBytes', r'''
def configBytes (files : List ByteArray) : ByteArray := u64n files.length ++ cat (files.map text)
'''),
    (RULES4, 'Fmt.configDigestW', r'''
def configDigestW (files : List ByteArray) : m ByteArray := h 169 0 2 zero32 (configBytes files)
'''),
    (RULES4, 'Fmt.configDigest', r'''
def configDigest (files : List ByteArray) : ByteArray := configDigestW (m := Id) formatHash files
'''),
]

# Three files, whole: their commands, in order.
KITS_COMMANDS = [
    ('import', 'import OnBytes.Base'),
    ('option1', 'set_option autoImplicit false'),
    ('option2', 'set_option relaxedAutoImplicit false'),
    ('namespace', 'namespace OnBytes.Tie.Pv.Plan'),
    ('textOf', r'''
def textOf (l : List String) : ByteArray := (String.join (l.map (· ++ "\n"))).toUTF8
'''),
    ('wordsFile', r'''
def wordsFile (l : List Nat) : ByteArray :=
  ⟨(l.flatMap fun w => [w % 256, w / 256 % 256, w / 65536 % 256, w / 16777216 % 256].map
    (·.toUInt8)).toArray⟩
'''),
    ('policyS', 'def policyS : List String := [ STRS ]'),
    ('scalesS', 'def scalesS : List Nat := [ NUMS ]'),
    ('policyF', 'def policyF : List String := [ STRS ]'),
    ('scalesF', 'def scalesF : List Nat := [ NUMS ]'),
    ('end', 'end OnBytes.Tie.Pv.Plan'),
]

LAYOUT_COMMANDS = [
    ('import', 'import OnBytes.Base'),
    ('option1', 'set_option autoImplicit false'),
    ('option2', 'set_option relaxedAutoImplicit false'),
    ('namespace', 'namespace OnBytes.Tie.Pv.Plan'),
    ('layoutF', 'def layoutF : String := STR'),
    ('end', 'end OnBytes.Tie.Pv.Plan'),
]

STORED_COMMANDS = [
    ('import1', 'import OnBytes.Tie.Pv.Plan.PlanKits'),
    ('import2', 'import OnBytes.Tie.Pv.Plan.PlanLayoutFull'),
    ('option', 'set_option autoImplicit false'),
    ('namespace', 'namespace VerifierAndGoals'),
    ('lines32', 'def lines32 : List String := [ STRS ]'),
    ('behindA1', 'def behindA1 : String := STR'),
    ('behindA2', 'def behindA2 : String := STR'),
    ('behindA3', 'def behindA3 : String := STR'),
    ('behindB', 'def behindB : String := STR'),
    ('FreeLines', r'''
structure FreeLines where
  eps1 : Nat
  eps2 : Nat
  epsF : Nat
  MF : Nat
  KF : Nat
  C : Nat
  theta : Nat
  cap : Nat
'''),
    ('storedLines',
     'def storedLines : FreeLines := ⟨NUM, NUM, NUM, NUM, NUM, NUM, NUM, NUM⟩'),
    ('policyFile', r'''
def policyFile (v : FreeLines) : ByteArray :=
  OnBytes.Tie.Pv.Plan.textOf lines32 ++
    (behindA1 ++
      s!"eps1_lo {v.eps1 % 2 ^ 32}\neps1_hi {v.eps1 / 2 ^ 32}\n" ++
      s!"eps2_lo {v.eps2 % 2 ^ 32}\neps2_hi {v.eps2 / 2 ^ 32}\n" ++ behindA2 ++
      s!"MF {v.MF}\nKF {v.KF}\n" ++
      s!"epsF_lo {v.epsF % 2 ^ 32}\nepsF_hi {v.epsF / 2 ^ 32}\n" ++ behindA3 ++
      s!"C {v.C}\ntheta {v.theta}\ncap {v.cap}\n" ++ behindB).toUTF8
'''),
    ('PublicFiles', r'''
structure PublicFiles where
  pol : ByteArray
  lay : ByteArray
  KL : ByteArray
'''),
    ('storedPublicFiles', r'''
def storedPublicFiles : PublicFiles :=
  ⟨policyFile storedLines, OnBytes.Tie.Pv.Plan.layoutF.toUTF8,
    OnBytes.Tie.Pv.Plan.wordsFile OnBytes.Tie.Pv.Plan.scalesF⟩
'''),
    ('zGap', r'''
def zGap : PublicFiles :=
  { storedPublicFiles with pol := policyFile { storedLines with C := NUM, theta := NUM, cap := NUM } }
'''),
    ('end', 'end VerifierAndGoals'),
]

# The tests of Ladder/Guards.lean that B reads. Each must stand there just once.
GUARD_LINES = [
    ('sizes', '#guard storedPublicFiles.pol.size == NUM && storedPublicFiles.lay.size == NUM '
              '&& storedPublicFiles.KL.size == NUM'),
    ('gapsize', '#guard zGap.pol.size == NUM && zGap.pol != storedPublicFiles.pol'),
    ('shares', '#guard zGap.lay == storedPublicFiles.lay && zGap.KL == storedPublicFiles.KL'),
    ('storedPublicFiles',
     '#guard Fmt.configDigest [storedPublicFiles.pol, storedPublicFiles.lay, storedPublicFiles.KL] '
     '== Fmt.unhex STR'),
    ('zGap', '#guard Fmt.configDigest [zGap.pol, zGap.lay, zGap.KL] == Fmt.unhex STR'),
]

WHOLE = [(STORED, 'stored', STORED_COMMANDS), (KITS, 'kits', KITS_COMMANDS),
         (LAYOUT, 'layout', LAYOUT_COMMANDS)]

# Words that declare the name that follows them.
DECLARES = 'def abbrev theorem lemma structure inductive class opaque axiom'.split()

# Names on which the comparisons lean. In the seven files together, each may be declared just once
# under any prefix (its last part is what is counted); blake2b, the three fields and the names of
# Lean's own library that the compared texts use, not at all.
LEANED_ON = dict.fromkeys(
    'lines32 behindA1 behindA2 behindA3 behindB FreeLines storedLines policyFile PublicFiles '
    'storedPublicFiles zGap textOf wordsFile scalesF layoutF'.split()
    + [full.split('.')[-1] for _, full, _ in PINS], 1)
LEANED_ON.update(dict.fromkeys(
    'blake2b pol lay KL ofNat replicate empty extract join toUTF8 toUInt8 toArray toList toNat map '
    'flatMap foldl size length Nat ByteArray UInt64 UInt8 String List Array Char Id'.split(), 0))

HOLES = {'NUM': 'num', 'STR': 'str'}
LISTS = {'NUMS': 'num', 'STRS': 'str'}


PATTERNS = {}  # the patterns' tokens, each computed once


def match(pattern, cmd):
    """Compares a command's tokens with a pattern. Returns the values at the pattern's holes, in
    order (a list for NUMS or STRS), or None if the two differ."""
    if pattern not in PATTERNS:
        PATTERNS[pattern] = bare(tokens(pattern, 'a pattern of this program'))
    want = PATTERNS[pattern]
    have = bare(cmd)
    got = []
    j = 0
    for kind, value in want:
        if kind == 'word' and value in HOLES:
            if j >= len(have) or have[j][0] != HOLES[value]:
                return None
            got.append(have[j][1])
            j += 1
        elif kind == 'word' and value in LISTS:
            items = []
            while j < len(have) and have[j][0] == LISTS[value]:
                items.append(have[j][1])
                j += 1
                if j < len(have) and have[j] == ('sign', ','):
                    if j + 1 >= len(have) or have[j + 1][0] != LISTS[value]:
                        return None
                    j += 1
                else:
                    break
            got.append(items)
        else:
            if j >= len(have) or have[j] != (kind, value):
                return None
            if kind == 'str' and have[j][1].raw != value.raw:
                return None  # the same string, written otherwise: inside s!"..." that matters
            j += 1
    return got if j == len(have) else None


# ------------------------------------------------------------------------------------------------
# The Lean definitions, reimplemented

def text_of(lines):
    """OnBytes.Tie.Pv.Plan.textOf"""
    return ''.join(l + '\n' for l in lines).encode('utf-8')


def words_file(words):
    """OnBytes.Tie.Pv.Plan.wordsFile"""
    return b''.join(bytes([w % 256, w // 256 % 256, w // 65536 % 256, w // 16777216 % 256])
                    for w in words)


def policy_file(d, v):
    """VerifierAndGoals.policyFile. d: the five stored pieces; v: the eight free numbers, by
    name."""
    return text_of(d['lines32']) + (
        d['behindA1']
        + 'eps1_lo %d\neps1_hi %d\n' % (v['eps1'] % 2 ** 32, v['eps1'] // 2 ** 32)
        + 'eps2_lo %d\neps2_hi %d\n' % (v['eps2'] % 2 ** 32, v['eps2'] // 2 ** 32) + d['behindA2']
        + 'MF %d\nKF %d\n' % (v['MF'], v['KF'])
        + 'epsF_lo %d\nepsF_hi %d\n' % (v['epsF'] % 2 ** 32, v['epsF'] // 2 ** 32) + d['behindA3']
        + 'C %d\ntheta %d\ncap %d\n' % (v['C'], v['theta'], v['cap']) + d['behindB']
    ).encode('utf-8')


def u64(x):
    """Fmt.u64n"""
    return (x % 2 ** 64).to_bytes(8, 'little')


def config_digest(files):
    """Fmt.configDigest"""
    message = u64(169 + 65536 * 0) + u64(2) + u64(len(files)) + b''.join(
        u64(len(f)) + f for f in files)
    return hashlib.blake2b(message, digest_size=32, salt=bytes(16), person=bytes(16)).digest()


def unhex(s):
    """Fmt.unhex: whatever is no digit counts 0; a last digit without a partner is dropped"""
    def digit(c):
        n = ord(c)
        if 48 <= n <= 57:
            return n - 48
        if 97 <= n <= 102:
            return n - 87
        if 65 <= n <= 70:
            return n - 55
        return 0
    return bytes((digit(a) << 4) % 256 | digit(b) for a, b in zip(s[0::2], s[1::2]))


def number(text, where):
    """A numeral of a Lean file, as a number."""
    if len(text) > 40:
        raise CannotCheck('%s has a numeral of %d digits' % (where, len(text)))
    return int(text)


def sha(b):
    return hashlib.sha256(b).hexdigest()


# ------------------------------------------------------------------------------------------------
# The comparisons

def head_sums(text):
    """The three files' lengths and sums, as the comment at the top of Ladder/Stored.lean names
    them: {field: (length, sum)}."""
    out = {}
    lines = text.split('\n')
    for i, l in enumerate(lines[:-1]):
        for field, name in FIELDS:
            w = l.split()
            nxt = lines[i + 1].split()
            if (w[:1] == [name] and w[-1:] == ['bytes'] and ('\x60%s\x60)' % field) in w
                    and len(nxt) == 2 and nxt[0] == 'sha256' and len(nxt[1]) == 64):
                if field in out:
                    raise CannotCheck('%s names the sum of %s twice' % (STORED, name))
                length = w[-2].replace(',', '')
                if not (length.isdigit() and length.isascii() and len(length) < 20):
                    raise CannotCheck("%s's top comment gives %s a length that is no number"
                                      % (STORED, name))
                out[field] = (int(length), nxt[1])
    return out


def compare(inputs):
    """All comparisons, on the thirteen files' bytes. Returns the rows: (id, holds, lines to print).
    Raises CannotCheck where it cannot go on; the rows so far are its second argument."""
    rows = []

    def row(ident, holds, *lines):
        rows.append((ident, bool(holds), [plain(l) for l in lines]))

    try:
        text, toks, cmds = {}, {}, {}
        for f in LEAN_FILES:
            try:
                text[f] = inputs[f].decode('utf-8')
            except UnicodeDecodeError:
                raise CannotCheck('%s is not UTF-8' % f)
            if '\r' in text[f]:
                raise CannotCheck('%s has a carriage return (line ends of the Windows kind: '
                                  'check the files out with their line ends unchanged)' % f)
            toks[f] = tokens(text[f], f)
            cmds[f] = commands(toks[f])

        fmt = (RULES1, RULES23, RULES4)
        # P: words and characters that are refused
        for f in LEAN_FILES:
            barred = BARRED_FMT if f in fmt else BARRED
            hits = ['%s (line %d)' % (v, line) for k, v, line, _ in toks[f]
                    if k == 'word' and v in barred]
            hits += ['%s not at the start of its line (line %d)' % (v, line)
                     for k, v, line, column in toks[f]
                     if k == 'word' and v in COMMAND_WORDS and column > 0]
            for a, b in zip(toks[f], toks[f][1:] + [('', '', 0, 0)]):
                if a[:2] == ('sign', '@') and b[:2] == ('sign', '['):
                    hits.append('@[ (line %d)' % a[2])
                if a[:2] == ('sign', '#'):
                    test = (f in HEADS and a[3] == 0 and b[:2] == ('word', 'guard')
                            and b[2:] == (a[2], 1))
                    array = f in fmt and b[:2] == ('sign', '[')
                    if not (test or array):
                        hits.append('#%s (line %d)' % (b[1], a[2]))
            row('P:refused:' + f, not hits, 'expected: no refused word or character in %s' % f,
                *(['   found: ' + ', '.join(hits[:8])] if hits else []))

        # P: how the commands begin, and the commands that are fixed
        for f in (GUARDS,) + fmt:
            heads = [('#' + c[1][1] if c[0][1] == '#' and len(c) > 1 else c[0][1], c[0][2])
                     for c in cmds[f]]
            odd = ['%s (line %d)' % h for h in heads if h[0] not in HEADS[f]]
            row('P:heads:' + f, not odd,
                'expected: every command of %s begins with one of: %s' % (f, ' '.join(HEADS[f])),
                *(['   found: ' + ', '.join(odd[:8])] if odd else []))
            first = set(p.split()[0] for p in FIXED[f])
            row('P:fixed:' + f,
                [bare(c) for c in cmds[f] if c[0][1] in first]
                == [bare(tokens(p, 'a pattern of this program')) for p in FIXED[f]],
                'expected: the commands of %s that begin with %s are those in FIXED, in order'
                % (f, ', '.join(sorted(first))))

        # P: three files, whole
        data = {}
        for f, tag, wanted in WHOLE:
            have = cmds[f]
            first_odd = ([c[0][2] for (_, pattern), c in zip(wanted, have)
                          if match(pattern, c) is None]
                         + [c[0][2] for c in have[len(wanted):]])[:1]
            row('P:%s:commands' % tag, len(have) == len(wanted),
                'expected: %d commands in %s; found: %d' % (len(wanted), f, len(have)),
                *(['   the first command that is not the expected one: line %d' % first_odd[0]]
                  if first_odd and len(have) != len(wanted) else []))
            if len(have) != len(wanted):
                raise CannotCheck('a Lean text under P is not as expected')
            for (name, pattern), c in zip(wanted, have):
                got = match(pattern, c)
                row('P:%s:%s' % (tag, name), got is not None,
                    "expected: the command '%s' (%s, line %d) token for token as in this program"
                    % (name, f, c[0][2]))
                data['%s:%s' % (tag, name)] = got
        # P: the pinned definitions under Fmt/
        for f, full, pattern in PINS:
            found = named(cmds[f], f).get(full, [])
            got = match(pattern, found[0]) if len(found) == 1 else None
            row('P:pin:' + full, got is not None,
                'expected: the definition %s once in %s, token for token as in PINS; found it %d '
                'time(s)' % (full, f, len(found)))
        # P: the names on which all this leans
        counts = dict.fromkeys(LEANED_ON, 0)
        where = dict((k, []) for k in LEANED_ON)
        dotted = []
        for f in LEAN_FILES:
            for a, b in zip(toks[f], toks[f][1:]):
                if a[0] == 'word' and a[1] in DECLARES and b[0] == 'word':
                    if b[1].split('.')[-1] in counts:
                        counts[b[1].split('.')[-1]] += 1
                        where[b[1].split('.')[-1]].append('%s:%d' % (f, b[2]))
                    if f == GUARDS and '.' in b[1]:
                        dotted.append('%s (line %d)' % (b[1], b[2]))
        wrong = ['%s: declared %d time(s), expected %d (%s)'
                 % (k, counts[k], LEANED_ON[k], ', '.join(where[k]) or 'nowhere')
                 for k in sorted(counts) if counts[k] != LEANED_ON[k]]
        row('P:names', not wrong,
            'expected: each name in LEANED_ON is declared as often as listed there, under any '
            'prefix', *(['   found: ' + ', '.join(wrong[:8])] if wrong else []))
        row('P:guards:names', not dotted, 'expected: no declared name with a dot in %s' % GUARDS,
            *(['   found: ' + ', '.join(dotted[:8])] if dotted else []))
        # P: the tests of Guards.lean
        for name, pattern in GUARD_LINES:
            got = [g for g in (match(pattern, c) for c in cmds[GUARDS]) if g is not None]
            row('P:guard:' + name, len(got) == 1,
                "expected: the test '%s' once in %s; found it %d time(s)"
                % (name, GUARDS, len(got)))
            data['guard:' + name] = got[0] if len(got) == 1 else None
        if not all(r[1] for r in rows):
            raise CannotCheck('a Lean text under P is not as expected')

        # the reimplemented definitions, at the values in the files
        pieces = {'lines32': data['stored:lines32'][0]}
        for k in ('behindA1', 'behindA2', 'behindA3', 'behindB'):
            pieces[k] = data['stored:' + k][0]
        free = dict(zip('eps1 eps2 epsF MF KF C theta cap'.split(),
                        [number(x, STORED) for x in data['stored:storedLines']]))
        gap = dict(free)
        gap.update(zip('C theta cap'.split(), [number(x, STORED) for x in data['stored:zGap']]))
        lay = data['layout:layoutF'][0].encode('utf-8')
        scales = words_file([number(x, KITS) for x in data['kits:scalesF'][0]])
        lean = {'storedPublicFiles': {'pol': policy_file(pieces, free), 'lay': lay, 'KL': scales},
                'zGap': {'pol': policy_file(pieces, gap), 'lay': lay, 'KL': scales}}
        spelled = {'pol': 'policyFile storedLines (%s)' % STORED,
                   'lay': 'layoutF (%s)' % LAYOUT, 'KL': 'wordsFile scalesF (%s)' % KITS}
        gap_spelled = 'policyFile { storedLines with C, theta, cap as in zGap } (%s)' % STORED
        example = {t: {fd: inputs['%s/%s' % (folder, name)] for fd, name in FIELDS}
                   for t, folder in TERMS}

        # A
        for t, folder in TERMS:
            for fd, name in FIELDS:
                a, b = lean[t][fd], example[t][fd]
                row('A:%s.%s' % (t, fd), a == b,
                    '%s.%s and %s/%s' % (t, fd, folder, name),
                    '   Lean     %7d bytes  sha256 %s' % (len(a), sha(a)),
                    '            %s' % (gap_spelled if (t, fd) == ('zGap', 'pol') else spelled[fd]),
                    '   example  %7d bytes  sha256 %s' % (len(b), sha(b)))
        # H
        head = head_sums(text[STORED])
        for fd, name in FIELDS:
            a = lean['storedPublicFiles'][fd]
            row('H:' + fd, head.get(fd) == (len(a), sha(a)),
                "storedPublicFiles.%s and what %s's top comment says of %s" % (fd, STORED, name),
                '   comment  %s' % ('%7d bytes  sha256 %s' % head[fd] if fd in head
                                    else 'not found'))
        # B
        sizes = [number(x, GUARDS) for x in data['guard:sizes']]
        row('B:storedPublicFiles.sizes',
            sizes == [len(example['storedPublicFiles'][fd]) for fd, _ in FIELDS],
            "the three sizes in the test on storedPublicFiles and the files of %s" % TERMS[0][1],
            '   test     %s' % sizes,
            '   example  %s' % [len(example['storedPublicFiles'][fd]) for fd, _ in FIELDS])
        row('B:zGap.size',
            number(data['guard:gapsize'][0], GUARDS) == len(example['zGap']['pol'])
            and example['zGap']['pol'] != example['storedPublicFiles']['pol'],
            "zGap.pol's size in the test, and that it is not storedPublicFiles.pol; and "
            "%s/policy.txt" % TERMS[1][1],
            '   test     %s' % data['guard:gapsize'][0],
            '   example  %d' % len(example['zGap']['pol']))
        row('B:zGap.shares',
            all(example['zGap'][fd] == example['storedPublicFiles'][fd] for fd in ('lay', 'KL')),
            'as the test says of the terms: the two folders have one layout.txt and one KL.bin')
        for t, folder in TERMS:
            want = unhex(data['guard:' + t][0])
            got = config_digest([example[t][fd] for fd, _ in FIELDS])
            row('B:%s.digest' % t, want == got,
                "the configuration's digest of %s and the value in the test on %s" % (folder, t),
                '   test     %s' % want.hex(), '   example  %s' % got.hex())
        # C
        for t, _ in TERMS:
            want = unhex(data['guard:' + t][0])
            got = config_digest([lean[t][fd] for fd, _ in FIELDS])
            row('C:%s.digest' % t, want == got,
                "the configuration's digest of %s, computed from the text, and the value in its "
                'test' % t,
                '   test     %s' % want.hex(), '   computed %s' % got.hex())
    except CannotCheck as e:
        raise CannotCheck(str(e), rows)
    return rows


# ------------------------------------------------------------------------------------------------
# Reading the files

def read(path):
    try:
        st = os.lstat(path)
    except OSError:
        raise CannotCheck('%s does not exist or is not accessible' % path)
    if not stat.S_ISREG(st.st_mode):
        raise CannotCheck('%s is a link, a folder or something else that is no regular file' % path)
    if st.st_size > MAX_BYTES:
        raise CannotCheck('%s has more than %d bytes' % (path, MAX_BYTES))
    flags = os.O_RDONLY | getattr(os, 'O_NOFOLLOW', 0) | getattr(os, 'O_BINARY', 0)
    try:
        fd = os.open(path, flags)
    except OSError:
        raise CannotCheck('%s cannot be opened for reading' % path)
    with os.fdopen(fd, 'rb') as f:
        if not stat.S_ISREG(os.fstat(f.fileno()).st_mode):
            raise CannotCheck('%s is no regular file' % path)
        b = f.read(MAX_BYTES + 1)
    if len(b) > MAX_BYTES:
        raise CannotCheck('%s has more than %d bytes' % (path, MAX_BYTES))
    return b


def read_all(lean_folder, examples_folder):
    inputs = {}
    for f in LEAN_FILES:
        inputs[f] = read(os.path.join(lean_folder, *f.split('/')))
    for f in EXAMPLE_FILES:
        inputs[f] = read(os.path.join(examples_folder, *f.split('/')))
    return inputs


KINDS = {
    'B': 'the example files, against a value in the text of a test that Lean runs when it\n'
         '   compiles Guards.lean (whether it was compiled, this program does not look)',
    'A': 'the example files, against bytes that this program computes from the Lean text',
    'C': 'bytes that this program computes from the Lean text, against a value in such a test',
    'H': 'bytes that this program computes from the text, against a comment',
    'P': 'the text of a Lean file, token for token, against a pattern in this program',
}


def show(rows):
    """Prints the rows, B first. The rows under P that hold are counted, not printed one by one."""
    held_p = 0
    last = None
    for ident, holds, lines in sorted(rows, key=lambda r: 'BACHP'.index(r[0][0])):
        if ident[0] == 'P' and holds:
            held_p += 1
            continue
        if ident[0] != last:
            last = ident[0]
            print('%s. KIND OF EVIDENCE: %s' % (last, KINDS[last]))
        word = 'CHANGED' if ident[0] == 'P' else 'SAME' if holds else 'DIFFERS'
        print('%-8s %-15s %s' % (word, ident, lines[0]))
        for l in lines[1:]:
            print(' ' * 9 + l)
    if held_p:
        if last != 'P':
            print('P. KIND OF EVIDENCE: %s' % KINDS['P'])
        print('%-8s %-15s %d texts of the Lean files are as this program expects them (white'
              % ('SAME', 'P', held_p))
        print(' ' * 9 + 'space, but for the start of a line, and comments aside: a changed comment')
        print(' ' * 9 + 'changes no row but H, which reads the comment at the top of %s)' % STORED)


NO_VERDICT = 'No verdict was reached on the example files.'

AFTER_CHANGED = """If you changed nothing: this program and the Lean files of the package no longer
fit each other. That is a fault of the package, not of your machine or your call: please report
it."""

# What to change, by the kind of row that failed, if the change of the Lean file is intended.
ADVICE = [
    (('P:pin:',), 'PINS, and the Python function that reimplements the definition, together'),
    (('P:stored:', 'P:kits:', 'P:layout:'),
     'STORED_COMMANDS, KITS_COMMANDS or LAYOUT_COMMANDS; if the command is policyFile, textOf,\n'
     '     wordsFile, FreeLines, storedLines, PublicFiles, storedPublicFiles or zGap: also the\n'
     '     Python code for it'),
    (('P:guard:',), 'GUARD_LINES, and the comparisons under B and C that read the test'),
    (('P:heads:',), 'HEADS (how a command of that file may begin)'),
    (('P:fixed:',), 'FIXED (the imports, namespaces and the like of that file)'),
    (('P:refused:',), 'BARRED, BARRED_FMT or COMMAND_WORDS'),
    (('P:names', 'P:guards:names'), 'LEANED_ON'),
]

AFTER_ADVICE = """Before you widen a list: a new command is harmless here only if it declares
nothing that the compared definitions and tests use, and changes no syntax. Then run --self-test."""


def after_stop(rows):
    """What is printed after 'CANNOT CHECK' in a plain run. If no row under P failed, the line
    'CANNOT CHECK' itself says what is wrong: a folder, a missing file, line ends."""
    print(NO_VERDICT)
    failed = [r[0] for r in rows if not r[1]]
    if failed:
        print(AFTER_CHANGED)
    todo = [what for starts, what in ADVICE if any(x.startswith(starts) for x in failed)]
    if todo:
        print('If you changed a Lean file on purpose, change in this program:')
        for what in todo:
            print('   - %s' % what)
        print(AFTER_ADVICE)


PARTS = [
    ('A', 'an example file differs from the bytes that the Lean text spells'),
    ('B', 'an example file does not fit a value in a test of %s' % GUARDS),
    ('C', 'the bytes that the Lean text spells do not fit a value in a test of %s' % GUARDS),
    ('H', 'the comment at the top of %s does not fit the bytes that the Lean text spells' % STORED),
]


def after_fail(bad):
    """What is printed after 'n OF m COMPARISONS FAIL'."""
    letters = set(r[0][0] for r in bad)
    for letter, what in PARTS:
        if letter in letters:
            print('   %s: %s.' % (letter, what))
    if letters & set('AB'):
        print('Until A and B hold again, nothing that is said "at storedPublicFiles" or "at zGap"')
        print('may be read as said of these example files.')


AFTER_PASS = """The terms storedPublicFiles and zGap, as the Lean files spell them, and the values
in the tests of %s fit the six example files.
Part B counts only beside a build of these very sources: this program does not look whether
%s was ever compiled.
A check by a program, not by Lean; against accidents and drift, not against a deliberate change.
What a pass is worth: see the comment at the top of scripts/check_stored_examples.py.""" % (
    GUARDS, GUARDS)


# ------------------------------------------------------------------------------------------------
# The self-test: faults planted in memory

def place(b, marker, f):
    if b.count(marker) != 1:
        raise CannotCheck('the self-test does not find its place in %s (%r is there %d times)'
                          % (f, marker[:40], b.count(marker)))
    return b.index(marker)


def swap(f, old, new):
    """A fault: in file f the bytes old, which must be there just once, become new."""
    def fault(inputs):
        place(inputs[f], old, f)
        return dict(inputs, **{f: inputs[f].replace(old, new)})
    return fault


def flip(f, at):
    """A fault: the lowest bit of one byte of file f (counted from the end if negative)."""
    def fault(inputs):
        b = bytearray(inputs[f])
        if not b:
            raise CannotCheck('the self-test cannot change the empty file %s' % f)
        b[at % len(b)] ^= 1
        return dict(inputs, **{f: bytes(b)})
    return fault


def after(f, marker, skip=0):
    """A fault: the lowest bit of the byte that is 'skip' bytes after the marker in file f."""
    def fault(inputs):
        return flip(f, place(inputs[f], marker, f) + len(marker) + skip)(inputs)
    return fault


def drop_line(f, marker):
    """A fault: the whole line after the line in which the marker ends leaves file f."""
    def fault(inputs):
        b = inputs[f]
        i = b.index(b'\n', place(b, marker, f) + len(marker)) + 1
        return dict(inputs, **{f: b[:i] + b[b.index(b'\n', i) + 1:]})
    return fault


def before(f, marker, new):
    """A fault: the bytes new are put in front of the marker in file f."""
    return lambda inputs: swap(f, marker, new + marker)(inputs)


def insert(f, marker, skip, new):
    """A fault: the bytes new are put 'skip' bytes after the marker in file f."""
    def fault(inputs):
        i = place(inputs[f], marker, f) + len(marker) + skip
        return dict(inputs, **{f: inputs[f][:i] + new + inputs[f][i:]})
    return fault


def at_end(f, new):
    return lambda inputs: dict(inputs, **{f: inputs[f] + new})


def body(f, name):
    """A fault: the lowest bit of the first letter or digit after the first ':=' (or '=>') of the
    definition 'name' in file f: one token of its body becomes another."""
    def fault(inputs):
        b = inputs[f]
        i = place(b, ('\ndef %s ' % name).encode(), f)
        j = min(x for x in (b.find(b':=', i), b.find(b'=>', i)) if x >= 0) + 2
        while not (chr(b[j]).isalnum() and b[j] < 128):
            j += 1
        return flip(f, j)(inputs)
    return fault


def around_test(term, front, back=b''):
    """A fault: bytes in front of, and after, the two lines of the digest test on a term."""
    def fault(inputs):
        b = inputs[GUARDS]
        i = place(b, ('#guard Fmt.configDigest [%s.pol,' % term).encode(), GUARDS)
        j = b.index(b'\n', b.index(b'\n', i) + 1) + 1
        return dict(inputs, **{GUARDS: b[:i] + front + b[i:j] + back + b[j:]})
    return fault


def in_test(term, change):
    """A fault: the two lines of the digest test on a term, changed by a function."""
    def fault(inputs):
        b = inputs[GUARDS]
        i = place(b, ('#guard Fmt.configDigest [%s.pol,' % term).encode(), GUARDS)
        j = b.index(b'\n', b.index(b'\n', i) + 1) + 1
        return dict(inputs, **{GUARDS: b[:i] + change(b[i:j]) + b[j:]})
    return fault


def two_stored_lines(inputs):
    """Other numbers in storedLines after a comment that Lean ends earlier than this program would,
    and the true line inside a comment that Lean ends later."""
    b = inputs[STORED]
    i = place(b, b'def storedLines : FreeLines := ', STORED)
    j = b.index(b'\n', i) + 1
    good = b[i:j]
    other = good.replace(b'\xe2\x9f\xa8', b'\xe2\x9f\xa81', 1)
    return dict(inputs, **{STORED: b[:i] + b'/-/-/\n' + other + b'-- -/ -/\n/--/\n' + good
                           + b'-- -/\n' + b[j:]})


def comma_at_the_end(inputs):
    """A comma in front of the bracket that closes storedLines."""
    b = inputs[STORED]
    i = b.index(b'\xe2\x9f\xa9', place(b, b'def storedLines : FreeLines := ', STORED))
    return dict(inputs, **{STORED: b[:i] + b',' + b[i:]})


def sum_twice(inputs):
    """The two lines on policy.txt in the top comment of Stored.lean, twice."""
    b = inputs[STORED]
    i, j = place(b, b'  policy.txt (', STORED), place(b, b'  layout.txt (', STORED)
    return dict(inputs, **{STORED: b[:j] + b[i:j] + b[j:]})


def letter_for_a_digit(inputs):
    """In the value of the digest test on storedPublicFiles the first digit that is not 0 becomes a
    letter g."""
    def change(t):
        i = t.index(b'"') + 1
        while t[i:i + 1] == b'0':
            i += 1
        return t[:i] + b'g' + t[i + 1:]
    return in_test('storedPublicFiles', change)(inputs)


def comma_in_a_list(inputs):
    """A comma in front of the bracket that closes scalesF."""
    b = inputs[KITS]
    i = b.index(b']', place(b, SCALES_F, KITS) + len(SCALES_F))
    return dict(inputs, **{KITS: b[:i] + b',' + b[i:]})


def escape_a_letter(inputs):
    """In the first literal of lines32 the second character is written as \\x and two digits."""
    b = inputs[STORED]
    marker = b'List String :=\n  ["'
    i = place(b, marker, STORED) + len(marker) + 1
    return dict(inputs, **{STORED: b[:i] + ('\\x%02x' % b[i]).encode() + b[i + 1:]})


def no_backslash(inputs):
    """The first line of layoutF loses the backslash at its end: a line feed more in the string."""
    b = inputs[LAYOUT]
    i = b.index(b'\\n\\\n', place(b, b'def layoutF : String :=\n  "\\\n', LAYOUT))
    return dict(inputs, **{LAYOUT: b[:i + 2] + b[i + 3:]})


FULL, GAP = TERMS[0][1], TERMS[1][1]
POL = ['A:storedPublicFiles.pol', 'A:zGap.pol', 'H:pol', 'C:storedPublicFiles.digest',
       'C:zGap.digest']
LAY = ['A:storedPublicFiles.lay', 'A:zGap.lay', 'H:lay', 'C:storedPublicFiles.digest',
       'C:zGap.digest']
SCALES = ['A:storedPublicFiles.KL', 'A:zGap.KL', 'H:KL', 'C:storedPublicFiles.digest',
          'C:zGap.digest']
FIRST_TEST = b'#guard storedPublicFiles.pol.size =='
SCALES_F = b'def scalesF : List Nat :=\n  ['
OTHER_SCALES = b'def _root_.VerifierAndGoals.OnBytes.Tie.Pv.Plan.scalesF : List Nat := [1]\n'


def P(*names):
    """Expected: the program stops under P, and just these rows have failed."""
    return ('P', ['P:' + n for n in names])


def X(fragment):
    """Expected: the program stops while it reads a file, with this in its message."""
    return ('X', fragment)


def faults():
    """(what is changed, the fault, what is expected: a list of the rows that must fail, or P(...),
    or X(...); the empty list: a harmless change that must be detected nowhere)."""
    out = [
        # the example files
        ('a bit of %s/policy.txt' % FULL, flip(FULL + '/policy.txt', 100),
         ['A:storedPublicFiles.pol', 'B:storedPublicFiles.digest']),
        ('a bit of the last byte of %s/layout.txt' % FULL, flip(FULL + '/layout.txt', -1),
         ['A:storedPublicFiles.lay', 'B:zGap.shares', 'B:storedPublicFiles.digest']),
        ('a bit of the first byte of %s/KL.bin' % FULL, flip(FULL + '/KL.bin', 0),
         ['A:storedPublicFiles.KL', 'B:zGap.shares', 'B:storedPublicFiles.digest']),
        ('a bit of %s/policy.txt' % GAP, flip(GAP + '/policy.txt', 2000),
         ['A:zGap.pol', 'B:zGap.digest']),
        ('a bit of %s/layout.txt' % GAP, flip(GAP + '/layout.txt', 5000),
         ['A:zGap.lay', 'B:zGap.shares', 'B:zGap.digest']),
        ('a bit of the last byte of %s/KL.bin' % GAP, flip(GAP + '/KL.bin', -1),
         ['A:zGap.KL', 'B:zGap.shares', 'B:zGap.digest']),
        ("%s/policy.txt in the other folder's place" % FULL,
         lambda i: dict(i, **{GAP + '/policy.txt': i[FULL + '/policy.txt']}),
         ['A:zGap.pol', 'B:zGap.size', 'B:zGap.digest']),
        ('a byte more at the end of %s/KL.bin' % FULL, at_end(FULL + '/KL.bin', b'\0'),
         ['A:storedPublicFiles.KL', 'B:storedPublicFiles.sizes', 'B:zGap.shares',
          'B:storedPublicFiles.digest']),
        # the values in the Lean files
        ('a character in the first literal of lines32',
         after(STORED, b'List String :=\n  ["', 1), POL),
        ('a literal of lines32 dropped, with its comma',
         drop_line(STORED, b'List String :=\n  ["'), POL),
        ('the first line of lines32 dropped, with the bracket',
         drop_line(STORED, b'def lines32 '), P('stored:lines32')),
    ]
    for k in ('behindA1', 'behindA2', 'behindA3', 'behindB'):
        marker = ('def %s : String := "' % k).encode()
        out.append(('a character in %s' % k, after(STORED, marker, 1), POL))
        out.append(('a line of %s dropped' % k, drop_line(STORED, marker), POL))
    out += [
        ('a digit of storedLines', after(STORED, b'FreeLines := \xe2\x9f\xa8', 0), POL),
        ("a digit of zGap's C", after(STORED, b'storedLines with C := ', 0),
         ['A:zGap.pol', 'C:zGap.digest']),
        ('a character in layoutF', after(LAYOUT, b'def layoutF : String :=\n  "\\\n', 3), LAY),
        ('a line of layoutF dropped', drop_line(LAYOUT, b'def layoutF : String :=\n  "\\'), LAY),
        ("a line's end of layoutF without its backslash", no_backslash, LAY),
        ('a digit of scalesF', after(KITS, SCALES_F + b'\n   ', 0), SCALES),
        ('a line of scalesF dropped', drop_line(KITS, SCALES_F), SCALES),
        ("a digit of the sum of policy.txt in Stored.lean's top comment",
         lambda i: flip(STORED, i[STORED].index(b'    sha256 ') + 11)(i), ['H:pol']),
        ("a digit of the value in the test on storedPublicFiles's digest",
         in_test('storedPublicFiles',
                 lambda t: t.replace(b'unhex "', b'unhex "0', 1)[:-3] + b'"\n'),
         ['B:storedPublicFiles.digest', 'C:storedPublicFiles.digest']),
        ("a digit of the value in the test on zGap's digest",
         in_test('zGap', lambda t: t.replace(b'unhex "', b'unhex "0', 1)[:-3] + b'"\n'),
         ['B:zGap.digest', 'C:zGap.digest']),
        ("the last digit of the value in the test on zGap's digest",
         in_test('zGap', lambda t: t[:-3] + (b'0' if t[-3:-2] != b'0' else b'1') + t[-2:]),
         ['B:zGap.digest', 'C:zGap.digest']),
        ("a letter that is no digit (it counts 0) for the first digit that is not 0 in the value "
         "in the test on storedPublicFiles's digest", letter_for_a_digit,
         ['B:storedPublicFiles.digest', 'C:storedPublicFiles.digest']),
        ("a digit of a size in the test on storedPublicFiles's sizes",
         after(GUARDS, FIRST_TEST + b' ', 3), ['B:storedPublicFiles.sizes']),
        ("a digit of the size in the test on zGap", after(GUARDS, b'#guard zGap.pol.size == ', 3),
         ['B:zGap.size']),
        # a test that no longer runs, or no longer says the same
        ("'#exit' in front of the tests", before(GUARDS, FIRST_TEST, b'#exit\n'),
         P('refused:' + GUARDS, 'heads:' + GUARDS)),
        ("'#guard_msgs (drop error) in' above the digest test",
         around_test('storedPublicFiles', b'#guard_msgs (drop error) in\n'),
         P('refused:' + GUARDS, 'heads:' + GUARDS)),
        ("the same, indented, at the end of the test before",
         around_test('storedPublicFiles', b'  #guard_msgs (drop all) in\n'),
         P('refused:' + GUARDS, 'guard:shares')),
        ("'#eval' in front of the tests", before(GUARDS, FIRST_TEST, b'#eval 1\n'),
         P('refused:' + GUARDS, 'heads:' + GUARDS)),
        ("'set_option ... in' above the digest test",
         around_test('storedPublicFiles', b'set_option maxRecDepth 9 in\n'), P('heads:' + GUARDS)),
        ("'#check' for '#guard' in the digest test",
         in_test('storedPublicFiles', lambda t: t.replace(b'#guard', b'#check', 1)),
         P('refused:' + GUARDS, 'heads:' + GUARDS, 'guard:storedPublicFiles')),
        ('the digest test after --', around_test('storedPublicFiles', b'-- '),
         P('guard:shares', 'guard:storedPublicFiles')),
        ('the digest test inside a nested comment',
         around_test('storedPublicFiles', b'/- /- -/\n', b'-/\n'), P('guard:storedPublicFiles')),
        ('the digest test inside a string',
         in_test('storedPublicFiles',
                 lambda t: b'def js : String := "\n' + t.replace(b'"', b'\\"') + b'"\n'),
         P('guard:storedPublicFiles')),
        ('the digest test negated',
         in_test('storedPublicFiles', lambda t: t.replace(b'#guard Fmt', b'#guard !Fmt', 1)),
         P('guard:storedPublicFiles')),
        ("'|| true' after the digest test",
         in_test('storedPublicFiles', lambda t: t[:-1] + b' || true\n'),
         P('guard:storedPublicFiles')),
        ('the digest test twice', in_test('storedPublicFiles', lambda t: t + t),
         P('guard:storedPublicFiles')),
        ('the test on the shared fields twice',
         before(GUARDS, b'\nend VerifierAndGoals',
                b'\n#guard zGap.lay == storedPublicFiles.lay && zGap.KL == storedPublicFiles.KL'),
         P('guard:shares')),
        # comments, names and literals that Lean might read otherwise than this program
        ("the digest test after '/--/'", around_test('storedPublicFiles', b'/--/\n', b'-- -/\n'),
         X('/--/')),
        ("the digest test after '/-!/'", around_test('storedPublicFiles', b'/-!/\n', b'-- -/\n'),
         X('/-!/')),
        ("the digest test after '/-- -- -/'",
         around_test('storedPublicFiles', b'/-- -- -/\n', b'-- -/\n'),
         X('and then another comment')),
        ("two lines storedLines, one after '/-/-/', one after '/--/'", two_stored_lines,
         X('opens with /-/')),
        ('a name in French quotes declared in Guards.lean',
         before(GUARDS, FIRST_TEST, 'def Fmt.\u00abconfigDigest\u00bb : Nat := 0\n\n'.encode()),
         X('French quotes')),
        ('a raw string for behindB',
         swap(STORED, b'def behindB : String := "', b'def behindB : String := r"'),
         X('the word r right in front')),
        ('a raw string in PlanKits.lean that would swallow code',
         before(KITS, SCALES_F,
                b'def j1 : String := r"\\"\n' + OTHER_SCALES + b'def j2 : String := "x"\n'),
         X('the word r right in front')),
        ('an empty line after a backslash in layoutF',
         swap(LAYOUT, b'def layoutF : String :=\n  "\\\n', b'def layoutF : String :=\n  "\\\n\n'),
         X('an empty line after a backslash')),
        ('a half of a surrogate pair as an escape in lines32',
         swap(STORED, b'List String :=\n  ["', b'List String :=\n  ["\\ud800'), X('an escape')),
        ('the brace of an interpolation in policyFile written as an escape',
         swap(STORED, b's!"MF {v.MF}', b's!"MF \\x7bv.MF}'), P('stored:policyFile')),
        ('a numeral with an underscore in scalesF',
         insert(KITS, SCALES_F + b'\n   ', 1, b'_'), P('kits:scalesF')),
        ('a digit of another script in storedLines',
         swap(STORED, b'FreeLines := \xe2\x9f\xa8', b'FreeLines := \xe2\x9f\xa8\xd9\xa3'),
         P('stored:storedLines')),
        ('a comma after the last numeral of storedLines', comma_at_the_end,
         P('stored:storedLines')),
        ('a comma after the last numeral of scalesF', comma_in_a_list, P('kits:scalesF')),
        ("an array literal '#[' in Guards.lean",
         before(GUARDS, FIRST_TEST, b'def arr : Array Nat := #[1]\n\n'), P('refused:' + GUARDS)),
        ("the sum of policy.txt twice in Stored.lean's top comment", sum_twice, X('twice')),
        ("one 'end' too many in Fmt/Rules1.lean", at_end(RULES1, b'\nend Fmt\n'),
         P('fixed:' + RULES1)),
        ('a numeral in base 16 in storedLines',
         swap(STORED, b'FreeLines := \xe2\x9f\xa8', b'FreeLines := \xe2\x9f\xa80x'),
         P('stored:storedLines')),
        ('a numeral of 5000 digits in storedLines',
         swap(STORED, b'FreeLines := \xe2\x9f\xa8', b'FreeLines := \xe2\x9f\xa8' + b'9' * 5000),
         X('a numeral of')),
        ("a length that is no number in Stored.lean's top comment",
         lambda i: dict(i, **{STORED: i[STORED].replace(b' bytes\n', b' x bytes\n')}),
         X('a length that is no number')),
        # other commands, other names, other imports
        ('a notation in Stored.lean',
         swap(STORED, b'namespace VerifierAndGoals\n',
              b'namespace VerifierAndGoals\nnotation "x" => 1\n'),
         P('refused:' + STORED, 'stored:commands')),
        ("one more definition at Stored.lean's end",
         swap(STORED, b'\nend VerifierAndGoals\n',
              b'\ndef zFull2 : PublicFiles := zGap\n\nend VerifierAndGoals\n'),
         P('stored:commands')),
        ('an indented command in Stored.lean',
         before(STORED, b'structure FreeLines where', b'  def x : Nat := 1\n'),
         P('refused:' + STORED, 'stored:behindB')),
        ("'deriving BEq' on PublicFiles", swap(STORED, b'  KL : ByteArray\n',
                                      b'  KL : ByteArray\n  deriving BEq\n'),
         P('refused:' + STORED, 'stored:PublicFiles')),
        ("'public import' in Stored.lean",
         swap(STORED, b'import OnBytes.Tie.Pv.Plan.PlanKits\n',
              b'public import OnBytes.Tie.Pv.Plan.PlanKits\n'),
         P('refused:' + STORED, 'stored:import1')),
        ('a third import in Stored.lean',
         swap(STORED, b'import OnBytes.Tie.Pv.Plan.PlanKits\n',
              b'import OnBytes.Tie.Pv.Plan.PlanKits\nimport Other\n'), P('stored:commands')),
        ('one more import in Guards.lean',
         swap(GUARDS, b'import Ladder\n', b'import Ladder\nimport Other\n'), P('fixed:' + GUARDS)),
        ('one more import in PlanLayoutFull.lean',
         swap(LAYOUT, b'import OnBytes.Base\n', b'import OnBytes.Base\nimport Other\n'),
         P('layout:commands')),
        ("'open' in Guards.lean",
         swap(GUARDS, b'namespace VerifierAndGoals\n', b'namespace VerifierAndGoals\nopen Fmt\n'),
         P('refused:' + GUARDS, 'heads:' + GUARDS)),
        ("'open ... in' in PlanLayoutFull.lean", before(LAYOUT, b'def layoutF ', b'open Nat in\n'),
         P('refused:' + LAYOUT, 'layout:commands')),
        ('an attribute on textOf', swap(KITS, b'\ndef textOf ', b'\n@[simp] def textOf '),
         P('refused:' + KITS, 'kits:textOf')),
        ('a storedPublicFiles of its own declared in Guards.lean',
         before(GUARDS, FIRST_TEST, b'def storedPublicFiles : PublicFiles := zGap\n\n'),
         P('names')),
        ("the same after 'private'",
         before(GUARDS, FIRST_TEST, b'private def storedPublicFiles : PublicFiles := zGap\n'),
         P('refused:' + GUARDS, 'heads:' + GUARDS, 'names')),
        ('a name with a dot declared in Guards.lean',
         before(GUARDS, FIRST_TEST, b'def Fmt.other : Nat := 0\n\n'), P('guards:names')),
        ('a scalesF under _root_.VerifierAndGoals at the end of PlanKits.lean',
         at_end(KITS, b'\n' + OTHER_SCALES),
         P('kits:commands')),
        ('a wordsFile in a second namespace at the end of PlanKits.lean',
         at_end(KITS, b'\nnamespace VerifierAndGoals.OnBytes.Tie.Pv.Plan\n'
                      b'def wordsFile (l : List Nat) : ByteArray := ByteArray.empty\n'
                      b'end VerifierAndGoals.OnBytes.Tie.Pv.Plan\n'),
         P('kits:commands')),
        ('a String.join of its own in front of textOf',
         before(KITS, b'def textOf ', b'def String.join (_ : List String) : String := ""\n\n'),
         P('kits:commands')),
        ('an indented namespace in front of scalesF',
         before(KITS, b'def scalesF ', b'def dummy : Nat := 0\n namespace Other\n'),
         P('refused:' + KITS, 'kits:commands')),
        ("'#exit' in front of scalesF, another scalesF before it",
         before(KITS, b'def scalesF ',
                OTHER_SCALES.replace(b'VerifierAndGoals.', b'') + b'#exit\n'),
         P('refused:' + KITS, 'kits:commands')),
        ("'protected def scalesF' in front of textOf",
         before(KITS, b'def textOf ', b'protected def scalesF : Nat := 0\n'),
         P('refused:' + KITS, 'kits:commands')),
        ("'attribute [implemented_by ...]' at the end of Fmt/Rules4.lean",
         swap(RULES4, b'\nend Fmt\n',
              b'\nattribute [implemented_by other] configDigest\n\nend Fmt\n'),
         P('refused:' + RULES4, 'heads:' + RULES4)),
        ('a notation in Fmt/Rules1.lean',
         before(RULES1, b'def u64 ', b'local notation "x" => 1\n'),
         P('refused:' + RULES1, 'heads:' + RULES1)),
        ("one more argument in the line 'variable' of Fmt/Rules4.lean",
         swap(RULES4, b'(h : Nat \xe2\x86\x92 Nat', b'(g h : Nat \xe2\x86\x92 Nat'),
         P('fixed:' + RULES4)),
        ("a UInt64.ofNat of its own in front of u64n",
         before(RULES1, b'def u64n ', b'def UInt64.ofNat (_ : Nat) : UInt64 := 0\n\n'), P('names')),
        ("'abbrev Nat := Int' in Fmt/Rules1.lean",
         before(RULES1, b'def u64 ', b'abbrev Nat := Int\n\n'), P('names')),
        ('a second configDigest, under another prefix, in Fmt/Rules23.lean',
         swap(RULES23, b'\nend Fmt\n', b'\ndef Other.configDigest : Nat := 0\n\nend Fmt\n'),
         P('names')),
        # the reimplemented definitions: one token of each body
        ('storedPublicFiles made of another name',
         swap(STORED, b'\xe2\x9f\xa8policyFile storedLines,',
              b'\xe2\x9f\xa8policyFile storedLinez,'),
         P('stored:storedPublicFiles')),
        ('two pieces of policyFile in another order',
         swap(STORED, b'" ++ behindA2 ++', b'" ++ behindA3 ++'), P('stored:policyFile')),
        ('another field inside an interpolation of policyFile',
         swap(STORED, b'\\nKF {v.KF}', b'\\nKF {v.MF}'), P('stored:policyFile')),
        ('255 for 256 in wordsFile', swap(KITS, b'[w % 256, ', b'[w % 255, '),
         P('kits:wordsFile')),
        ('a token of the body of textOf', body(KITS, 'textOf'), P('kits:textOf')),
        ('168 for 169 in configDigestW', swap(RULES4, b'h 169 0 2 zero32 (configBytes',
                                              b'h 168 0 2 zero32 (configBytes'),
         P('pin:Fmt.configDigestW')),
        ('the length left out of Fmt.text', swap(RULES1, b':= u64n b.size ++ b\n', b':= b\n'),
         P('pin:Fmt.text')),
    ]
    for f, full, _ in PINS:
        out.append(('a token of the body of %s' % full, body(f, full.split('.')[-1]),
                    P('pin:' + full)))
    # one token of every other command that is compared whole
    plan = b'OnBytes.Tie.Pv.Plan'
    for f, tag in ((KITS, 'kits'), (LAYOUT, 'layout')):
        out += [
            ('another import in %s' % f,
             swap(f, b'import OnBytes.Base\n', b'import OnBytes.Basf\n'), P(tag + ':import')),
            ('autoImplicit true in %s' % f, swap(f, b'set_option autoImplicit false',
                                                 b'set_option autoImplicit true'),
             P(tag + ':option1')),
            ('relaxedAutoImplicit true in %s' % f, swap(f, b'set_option relaxedAutoImplicit false',
                                                        b'set_option relaxedAutoImplicit true'),
             P(tag + ':option2')),
            ('another namespace in %s' % f,
             swap(f, b'namespace ' + plan + b'\n', b'namespace ' + plan + b'x\n'),
             P(tag + ':namespace')),
            ("another name after 'end' in %s" % f,
             swap(f, b'\nend ' + plan + b'\n', b'\nend ' + plan + b'x\n'), P(tag + ':end')),
        ]
    for f, tag, name, kind in ((KITS, 'kits', 'policyS', b'List String'),
                               (KITS, 'kits', 'scalesS', b'List Nat'),
                               (KITS, 'kits', 'policyF', b'List String'),
                               (LAYOUT, 'layout', 'layoutF', b'String'),
                               (STORED, 'stored', 'behindA1', b'String'),
                               (STORED, 'stored', 'behindA2', b'String'),
                               (STORED, 'stored', 'behindA3', b'String')):
        marker = ('def %s : ' % name).encode() + kind
        out.append(('another type for %s' % name, swap(f, marker + b' :=', marker + b'x :='),
                    P('%s:%s' % (tag, name))))
    out += [
        ('another second import in Stored.lean',
         swap(STORED, b'import OnBytes.Tie.Pv.Plan.PlanLayoutFull\n',
              b'import OnBytes.Tie.Pv.Plan.PlanLayoutFulk\n'), P('stored:import2')),
        ('autoImplicit true in Stored.lean', swap(STORED, b'set_option autoImplicit false',
                                                  b'set_option autoImplicit true'),
         P('stored:option')),
        ('another namespace in Stored.lean',
         swap(STORED, b'namespace VerifierAndGoals\n', b'namespace VerifierAndGoalt\n'),
         P('stored:namespace')),
        ("another name after 'end' in Stored.lean",
         swap(STORED, b'\nend VerifierAndGoals\n', b'\nend VerifierAndGoalt\n'), P('stored:end')),
        ('another type for a field of FreeLines',
         swap(STORED, b'  theta : Nat\n', b'  theta : Int\n'), P('stored:FreeLines')),
        ('another field name in zGap', swap(STORED, b', cap := ', b', caq := '), P('stored:zGap')),
        ("another name after 'end' in Fmt/Rules1.lean",
         swap(RULES1, b'\nend Fmt\n', b'\nend Fmu\n'), P('fixed:' + RULES1)),
        ("another name after 'end' in Fmt/Rules23.lean",
         swap(RULES23, b'\nend Fmt\n', b'\nend Fmu\n'), P('fixed:' + RULES23)),
        ('a notation in Fmt/Rules23.lean',
         before(RULES23, b'def dlen ', b'local notation "x" => 1\n'),
         P('refused:' + RULES23, 'heads:' + RULES23)),
        ("'>=' for '==' in the test on storedPublicFiles's sizes",
         swap(GUARDS, FIRST_TEST, FIRST_TEST[:-2] + b'>='), P('guard:sizes')),
        ("'>=' for '==' in the test on zGap's size",
         swap(GUARDS, b'#guard zGap.pol.size ==', b'#guard zGap.pol.size >='), P('guard:gapsize')),
        ("the digest test on zGap negated",
         in_test('zGap', lambda t: t.replace(b'#guard Fmt', b'#guard !Fmt', 1)), P('guard:zGap')),
        ("a digit of zGap's theta", after(STORED, b', theta := ', 0),
         ['A:zGap.pol', 'C:zGap.digest']),
        ("a digit of zGap's cap", after(STORED, b', cap := ', 0), ['A:zGap.pol', 'C:zGap.digest']),
        ("a digit of the length of policy.txt in Stored.lean's top comment",
         lambda i: flip(STORED, i[STORED].index(b' bytes\n    sha256 ') - 1)(i), ['H:pol']),
        ('a carriage return in Guards.lean',
         swap(GUARDS, b'import Ladder\n', b'import Ladder\r\n'), X('a carriage return')),
        ('a byte that is not UTF-8 in PlanKits.lean', at_end(KITS, b'\xff'), X('is not UTF-8')),
    ]
    out += [
        # harmless changes
        ('HARMLESS: a letter of lines32 written as an escape of the same byte', escape_a_letter,
         []),
        ("HARMLESS: the digits of the value in the test on storedPublicFiles's digest in upper "
         "case",
         in_test('storedPublicFiles', lambda t: t[:t.index(b'"')] + t[t.index(b'"'):].upper()), []),
        ('HARMLESS: a comment more in PlanKits.lean',
         before(KITS, b'def textOf ', b'/-- Another comment. -/\n'), []),
        ('HARMLESS: a line break more inside wordsFile',
         swap(KITS, b'[w % 256, ', b'[w % 256,\n      '), []),
    ]
    return out


def self_test(inputs):
    if not all(r[1] for r in compare(inputs)):
        print('the self-test needs files that pass; these do not')
        return False
    good = True
    n = 0
    never = set(r[0] for r in compare(inputs))
    for what, fault, expected in faults():
        n += 1
        changed_inputs = fault(inputs)
        changed = [f for f in inputs if inputs[f] != changed_inputs[f]]
        message = ''
        try:
            failed = [r[0] for r in compare(changed_inputs) if not r[1]]
            stopped = False
        except CannotCheck as e:
            failed = [r[0] for r in e.args[1] if not r[1]]
            message = e.args[0]
            stopped = True
        if isinstance(expected, list):
            fine = not stopped and sorted(failed) == sorted(expected)
            want = ', '.join(expected) if expected else 'nothing'
        elif expected[0] == 'P':
            fine = stopped and sorted(failed) == sorted(expected[1])
            want = 'a stop, with just: ' + ', '.join(expected[1])
        else:
            fine = stopped and not failed and expected[1] in message
            want = "a stop while reading, with '%s' in the message" % expected[1]
        fine = fine and len(changed) == 1
        good = good and fine
        never -= set(failed)
        word = 'WRONG' if not fine else 'DETECTED' if expected else 'NO ALARM'
        print('%-9s %3d. %s' % (word, n, what))
        print('%14s failed: %s%s' % ('', ', '.join(failed) if failed else 'nothing',
                                     '; stopped: ' + plain(message) if stopped else ''))
        if not fine:
            print('%14s expected: %s' % ('', want))
    print()
    if never:
        good = False
        print('COMPARISONS THAT NO FAULT MADE FAIL: %s' % ', '.join(sorted(never)))
    else:
        print('Every comparison failed under at least one fault.')
    print('THE SELF-TEST: %d changes; %s' % (
        n, 'each fault made just the expected comparisons fail, and the harmless changes none'
        if good else 'AT LEAST ONE DID NOT DO WHAT WAS EXPECTED'))
    return good


def main(argv):
    for stream in (sys.stdout, sys.stderr):
        if hasattr(stream, 'reconfigure'):  # a character that the terminal cannot show: its escape
            stream.reconfigure(errors='backslashreplace')
    if '--help' in argv[1:] or '-h' in argv[1:]:
        print(__doc__ or USAGE)
        return 0
    args = [a for a in argv[1:] if not a.startswith('-')]
    options = [a for a in argv[1:] if a.startswith('-')]
    if len(args) != 2 or any(o != '--self-test' for o in options):
        print('Wrong call: expected two folders, and no option but --self-test.')
        print(USAGE)
        return 2
    for name, folder in (('LEAN_FOLDER', args[0]), ('EXAMPLES_FOLDER', args[1])):
        print('%-15s %s' % (name, plain(folder)))
        print('%-15s %s' % ('  absolute:', plain(os.path.abspath(folder))))
    try:
        inputs = read_all(args[0], args[1])
        print('The seven Lean files that were read%s:'
              % ('' if options else " (the example files' sums: under A)"))
        for f in LEAN_FILES:
            print('   sha256 %s  %s' % (sha(inputs[f]), f))
        print()
        if options:
            return 0 if self_test(inputs) else 1
        rows = compare(inputs)
    except CannotCheck as e:
        rows = e.args[1] if len(e.args) > 1 else []
        show(rows)
        print()
        print('CANNOT CHECK: %s' % plain(e.args[0]))
        if not options:
            after_stop(rows)
        return 1
    show(rows)
    bad = [r for r in rows if not r[1]]
    print()
    if bad:
        print('%d OF %d COMPARISONS FAIL: %s' % (len(bad), len(rows), ', '.join(r[0] for r in bad)))
        after_fail(bad)
        return 1
    n = dict((k, len([r for r in rows if r[0][0] == k])) for k in 'ABCHP')
    print('ALL %d COMPARISONS HOLD: %d with an example file (A %d, B %d), %d within the Lean files'
          % (len(rows), n['A'] + n['B'], n['A'], n['B'], n['C'] + n['H']))
    print("(C %d, H %d), %d of Lean text with this program's own patterns (P)."
          % (n['C'], n['H'], n['P']))
    print(AFTER_PASS)
    return 0


if __name__ == '__main__':
    sys.exit(main(sys.argv))
