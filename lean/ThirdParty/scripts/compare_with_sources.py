#!/usr/bin/env python3
# Copyright 2026 Anthropic PBC
# SPDX-License-Identifier: Apache-2.0
"""Compares the Lean files in lean/ThirdParty with the outside files they were taken from.

usage:
  compare_with_sources.py --arklib DIR --mathlib DIR [--tree DIR] [--write-list FILE]

  --arklib DIR    a checkout of https://github.com/Verified-zkEVM/ArkLib
                  at commit 2817d8c7d2f28d706b17f8de0f885880d0b2eb13
  --mathlib DIR   a checkout of https://github.com/leanprover-community/mathlib4
                  at commit 5ed2965256430c3649e86755f9576b54eca72435 (tag v4.34.0)
  --tree DIR      the folder ThirdParty (default: the folder above this program; the three tables
                  are always read from beside this program)
  --write-list F  write the list of everything taken over to F, instead of comparing it with
                  TAKEN-OVER.tsv in the tree; F must not exist yet: this program overwrites no file

"Ours" is a file under ThirdParty/ArkLib or ThirdParty/MathlibBackport; "the outside file" is the
file of the same path in ArkLib or Mathlib. White space never counts; comments count only where
named below. What is compared:
  1. First comment. Our file begins with the outside file's first comment (copyright, licence,
     authors), byte for byte.
  2. Which declarations. Every declaration of ours is a declaration of the outside file, under the
     same name and in the same order, and ours are exactly those of kept_declarations.tsv.
  3. Statement. It is the outside statement, word for word (a word is text between spaces). For a
     theorem or lemma the statement is the text up to the ":=" or "|" that starts the proof; for
     anything else (def, abbrev, structure, instance) it is the whole declaration, and a
     difference is called a changed definition. Attributes and the commands "open ... in",
     "omit ... in", "variable ... in" in front of a declaration count as part of its statement.
  4. Proof. It is the outside proof, word for word ("set_option ... in" in front counts as proof).
  5. Lines between declarations. Every line that starts in the first column and is neither a
     declaration nor an import (namespace, section, end, open, variable, universe, and so on), with
     the indented lines that continue it, is a line of the outside file, in the same order, and the
     lines in force at each declaration are the same. A difference is listed once per file.
  6. Doc comment. The comment /-- ... -/ of a declaration is the outside one.
  7. Long comments. For ArkLib, the comments /-! ... -/ are the outside ones, all and in order. In
     six files they name sources of their own. What the list says of these is fixed text in this
     program, which checks only that the mark of each such source (the name of a repository, or a
     commit) stands in the files for which the list names it, and in no other file taken over.
  8. Nothing else. Every line of code in our file belongs to a declaration, to an import or to a
     line of item 5. An import is the word "import" and one module of Mathlib, of Batteries (on
     which Mathlib rests) or of ThirdParty. The only other Lean files in the tree are our own two
     (ArkLibShim, ArkLibCheck); they have no outside file, and are held to a fingerprint.
  9. Note. The second comment of our file begins "Adapted from", and names the project's address,
     the outside file and the commit. The rest of the note (what was changed) is not looked at.
 10. Other files. ThirdParty/LICENSE, ArkLib/LICENSE and ArkLib/AUTHORS are ArkLib's files, and
     MathlibBackport/LICENSE is Mathlib's, byte for byte. Beside these, the Lean files, README.md,
     TAKEN-OVER.tsv, this program and its three tables, the tree holds no file.
 11. TAKEN-OVER.tsv in the tree is the list that this program writes (looked at only if there is
     no other complaint). Its last two rows are for files outside this folder (lean/Cb/Bridge),
     which are not looked at.

Every difference under 3 to 7 must have a row in listed_changes.tsv (our file, declaration, kind,
reason, fingerprint), and every row there must be a difference, but for the two rows of our own
files. The fingerprint is taken from our text, so a row covers the listed text and no other. It is
the first 16 hex digits of the SHA-256 of our words joined by single spaces; for lines between
declarations, of those lines and the names of the declarations, in the order of the file; for our
own two files, of all words of the file.

Lemmas of Lean and Mathlib that were renamed (renamed_lemmas.tsv: newer name, older name) are
turned back in the outside text first. A proof or definition that differs in nothing else is not
counted as changed, and the places are counted.

The exit status is 0 if all of this holds and 1 if not.

What is not looked at: comments other than those of items 1, 6, 7 and 9, among them every comment
/-! ... -/ in MathlibBackport (Mathlib's are not taken over); which modules of Mathlib a file
imports; the words of README.md. If the commit of DIR cannot be read (no git checkout, or no git),
the program says so and goes on.

The three tables lie beside this program: kept_declarations.tsv, listed_changes.tsv and
renamed_lemmas.tsv. If a text was changed on purpose, put the fingerprint that the complaint prints
into its row of listed_changes.tsv, see that the reason there still holds, and write the list anew.

This is a comparison of texts. That the files are correct mathematics is checked by Lean alone.
"""
import argparse, collections, difflib, hashlib, os, re, subprocess, sys

ARKLIB_URL = 'https://github.com/Verified-zkEVM/ArkLib'
ARKLIB_COMMIT = '2817d8c7d2f28d706b17f8de0f885880d0b2eb13'
MATHLIB_URL = 'https://github.com/leanprover-community/mathlib4'
MATHLIB_COMMIT = '5ed2965256430c3649e86755f9576b54eca72435'  # tag v4.34.0

OWN_FILES = {
    'ThirdParty/ArkLibShim/BivariateDegreeX.lean':
        'It defines Polynomial.Bivariate.degreeX and proves Polynomial.Bivariate.coeff_natDegree_le_degreeX, '
        'two names that ArkLib imports from the package CompPoly '
        '(module CompPoly.ToMathlib.Polynomial.BivariateDegree).',
    'ThirdParty/ArkLibCheck/Axioms.lean':
        'It makes the build fail unless the two theorems rest on propext, Classical.choice and Quot.sound alone.',
}
# what the list says in front of, and as the source of, a file of OWN_FILES; where nothing is given here: 'nothing: our own file. ' and 'none'
OWN_LEAD = {'ThirdParty/ArkLibShim/BivariateDegreeX.lean': 'two names of the package CompPoly, for which this file stands in. '}
OWN_FROM = {'ThirdParty/ArkLibShim/BivariateDegreeX.lean':
            'https://github.com/Verified-zkEVM/CompPoly, module CompPoly.ToMathlib.Polynomial.BivariateDegree'}
SHIM_MODULE = 'ThirdParty.ArkLibShim.BivariateDegreeX'
SHIM_SENTENCE = ("ArkLib's file imports the package CompPoly for Polynomial.Bivariate.degreeX and "
                 'Polynomial.Bivariate.coeff_natDegree_le_degreeX. Here the two names come from '
                 'ThirdParty/ArkLibShim/BivariateDegreeX.lean, which was written for this library.')
ARKLIB_FOUR_FILES = (
    '%s, under ArkLib/Data/CodingTheory/: ReedSolomon/MutualCorrelatedAgreement/Johnson/Agreement.lean, '
    'HiddenDerivative/Parameters/Johnson/FiniteBounds.lean, ReedSolomon/Agreement.lean and '
    'ReedSolomon/MutualCorrelatedAgreement/ExtensionDescent.lean, commit %s' % (ARKLIB_URL, ARKLIB_COMMIT))
ALSO_NAMED = ("; the file's head also names ReedSolomon/MutualCorrelatedAgreement/Johnson/Probability.lean there")
RS_LD_MCA = 'kz99/rs-ld-mca'
OLDER_ARKLIB = 'a5aa2677fee4e3a79d6bb05136631cce4a08587d'
OLDER_ARKLIB_2 = '66f3d089a41704597f54d641b78254d2a8f361f8'
PROXIMITY_PRIZE = '19bc7d3e21b2261257e1961acd720b2c395d87e1'
# outside file: (the marks that stand in it, what the list says behind its commit)
FURTHER_SOURCES = {
    'ArkLib/Data/CodingTheory/HiddenDerivative/Interpolation/Local/ConstraintMap.lean': (
        {RS_LD_MCA}, 'parts of the file are "adapted, with permission, from" Kai Zhe Zheng\'s formalization '
        + RS_LD_MCA),
    'ArkLib/Data/MvPolynomial/WeightedOrder.lean': (
        {RS_LD_MCA}, 'parts of the file are "adapted, with permission, from" Kai Zhe Zheng\'s formalization '
        + RS_LD_MCA),
    'ArkLib/Data/Polynomial/Differential/Types.lean': (
        {RS_LD_MCA}, 'the definitions are "adapted, with permission, from" ' + RS_LD_MCA),
    'ArkLib/Data/MvPolynomial/WeightedDegree.lean': (
        {OLDER_ARKLIB}, 'the partial-derivative and univariate-substitution bounds are "extracted from" '
        'ArkLib/Data/CodingTheory/ReedSolomon/HiddenDerivative/RootFinding/DegreeBounds/SpecializationDegree.lean '
        'at ArkLib revision ' + OLDER_ARKLIB),
    'ArkLib/Data/Polynomial/ResultantDegree.lean': (
        {OLDER_ARKLIB, OLDER_ARKLIB_2}, 'it is "Adapted from Alexander Hicks and Aleph\'s field-only result in '
        'ArkLib" (ArkLib/Data/CodingTheory/PolishchukSpielman/Resultant.lean at revision ' + OLDER_ARKLIB_2 +
        '), and the total-degree bounds are "ported from" ArkLib/ToMathlib/Polynomial/DerivativeResultantDegree.lean '
        'at ArkLib revision ' + OLDER_ARKLIB),
    'ArkLib/Data/Polynomial/FractionFieldResultant.lean': (
        {OLDER_ARKLIB, PROXIMITY_PRIZE}, 'it "generalizes the large-characteristic argument in Remco '
        'Bloemen\'s BCHKS formalization" (ProximityPrize/SubmissionLower/BCHKSConcreteGoodSpecialization.lean at '
        'commit ' + PROXIMITY_PRIZE + ' of https://github.com/proximity-prize/proximity-prize; "No donor proof is '
        'copied"), and the part on irreducible polynomials "is ported from" '
        'ArkLib/ToMathlib/Polynomial/SeparableResultant.lean at ArkLib revision ' + OLDER_ARKLIB),
}
# outside files whose statements stand word for word and yet ask more here than in the source: README.md, "What was
# changed", "The two statements". The comparison of words cannot see that, so the list says it from here.
# The test seeks the word as a premise: behind an opening square bracket, in the file's text with every comment
# removed. So a mention in a comment is none, nor is [StrongNormalizedGCDMonoid ...].
ASKS_MORE_PREMISE = '[NormalizedGCDMonoid '
ASKS_MORE = ('the premise NormalizedGCDMonoid stands word for word as in the source and asks more here than there: '
             "in this library's Mathlib that class is what Mathlib v4.34.0 calls StrongNormalizedGCDMonoid")
ASKS_MORE_FILES = ('ArkLib/ToMathlib/LinearAlgebra/Matrix/PrimitiveKernel.lean',
                   'Mathlib/RingTheory/PrincipalIdealDomain.lean')
OUTSIDE_THIS_FOLDER = (
    ('Cb/Bridge/CodeListRSFromLines.lean',
     "the content of three definitions. estM and est write out ArkLib's johnsonComparisonEstimate, with the "
     "definitions that it uses unfolded. LineFact restates in Mathlib's terms what ArkLib's two theorems give "
     'together: the statement of ReedSolomon.exists_johnson_line_exactCorrelatedPair, with johnsonAgreement written '
     "out, est in place of johnsonExceptionCount, agreement on a set of positions in place of ArkLib's agreement "
     'sets (polynomialAgreementSet, commonPolynomialAgreementSet), the premise of '
     'ReedSolomon.HiddenDerivative.johnsonExceptionCount_le_comparisonEstimate that the agreement fraction is at most '
     '1 added, and of the conclusion (HasExactCorrelatedPair) only that two polynomials of degree at most D agree '
     'with f and g on that set',
     ARKLIB_FOUR_FILES + ALSO_NAMED,
     'changed: see the second column; in Cb/Bridge/CodeListRSProved.lean, est_eq_arkLib proves that est is '
     "ArkLib's estimate, and lineFact proves LineFact from ArkLib's two theorems"),
    ('Cb/Bridge/CodeListRSProved.lean',
     "the use of ArkLib's two theorems and of definitions that their statements use. lineFact applies "
     'ReedSolomon.exists_johnson_line_exactCorrelatedPair, takes its conclusion (HasExactCorrelatedPair) apart, and '
     'names polynomialAgreementSet and commonPolynomialAgreementSet with their membership lemmas. arkLibCount_le_est '
     'applies ReedSolomon.HiddenDerivative.johnsonExceptionCount_le_comparisonEstimate and restates it, on '
     'johnsonExceptionCount, with johnsonAgreement written out and est in place of johnsonComparisonEstimate. '
     "est_eq_arkLib, agreement_eq_arkLib and arkLibEstimate_eq_bchksBound are equalities with ArkLib's "
     'johnsonComparisonEstimate and johnsonAgreement. Cb/Bridge/GlCodesProvedCheck.lean names the two theorems too, '
     'to print the axioms that they rest on',
     ARKLIB_FOUR_FILES + ALSO_NAMED,
     'not applicable: it imports the files from ThirdParty/ArkLib'),
)
COPIES = (('LICENSE', 'arklib', 'LICENSE'), ('ArkLib/LICENSE', 'arklib', 'LICENSE'),
          ('ArkLib/AUTHORS', 'arklib', 'AUTHORS'), ('MathlibBackport/LICENSE', 'mathlib', 'LICENSE'))
OTHER_FILES = ('README.md', 'TAKEN-OVER.tsv', 'scripts/compare_with_sources.py', 'scripts/kept_declarations.tsv',
               'scripts/listed_changes.tsv', 'scripts/renamed_lemmas.tsv')
ALL_LINES = '(lines between declarations)'
ALL_LONG_COMMENTS = '(long comments)'
WHOLE_FILE = '(whole file)'
HERE = os.path.dirname(os.path.abspath(__file__))


def blank_comments(text):
    """The text with every comment removed. Line breaks stay, so line numbers hold."""
    out, i, n, depth, in_string = [], 0, len(text), 0, False
    while i < n:
        c = text[i]
        if depth == 0 and not in_string and text.startswith('--', i):
            while i < n and text[i] != '\n':
                i += 1
            continue
        if not in_string and text.startswith('/-', i):
            depth += 1
            i += 2
            continue
        if depth > 0 and text.startswith('-/', i):
            depth -= 1
            i += 2
            continue
        if depth > 0:
            if c == '\n':
                out.append('\n')
            i += 1
            continue
        if c == '"':
            in_string = not in_string
        if in_string and c == '\\':
            out.append(text[i:i + 2])
            i += 2
            continue
        out.append(c)
        i += 1
    return ''.join(out)


KEYWORDS = 'theorem|lemma|def|abbrev|structure|class|instance|inductive|opaque|axiom|alias|example'
MODIFIERS = r'(?:(?:public|private|protected|noncomputable|nonrec|unsafe|partial|scoped|local|meta)\s+)*'
DECLARATION = re.compile(r'^(?:@\[.*?\]\s*)*' + MODIFIERS + r'(' + KEYWORDS + r')\b\s*([^\s:({\[⦃]+)?')
NOTATION = re.compile(r'^(?:@\[.*?\]\s*)*' + MODIFIERS +
                      r'(notation|infix|infixl|infixr|prefix|postfix|macro|syntax|macro_rules|elab)\b')
PREFIXABLE = re.compile(r'^(open|set_option|omit|include|variable|universe|attribute)\b')
ENDS_IN = re.compile(r'\bin\s*$')
SECTION_OPENER = re.compile(r'^(?:@\[expose\]\s+)?(?:public\s+)?(?:noncomputable\s+)?section\b\s*(\S*)')
MODULE_SYSTEM_SECTION = re.compile(r'^(@\[expose\]\s+)?public\s+section\s*$')   # binds nothing
IMPORT = re.compile(r'^(?:public\s+)?(?:meta\s+)?import\b\s*(?:all\s+)?(\S*)')


class Declaration:
    __slots__ = ('kind', 'name', 'first', 'last', 'keyword_line', 'in_force', 'doc')


class Parsed:
    __slots__ = ('declarations', 'code', 'between', 'skeleton', 'imports', 'long_comments', 'stray')


def parse(text):
    """Splits a Lean file into declarations, imports and the lines between declarations."""
    raw = text.split('\n')
    code = blank_comments(text).split('\n')
    result = Parsed()
    found, stack, in_force, covered = [], [], [], set()
    result.between, result.skeleton, result.imports = [], [], []
    pending, current, i = None, None, 0

    def continued(start):
        """the line after the indented lines that continue the command at line start"""
        j = start + 1
        while j < len(code) and code[j].startswith(' ') and code[j].strip():
            j += 1
        return j

    def close(at):
        nonlocal current
        if current is not None:
            end = at
            while end > current.first and not code[end - 1].strip():
                end -= 1
            current.last = end
            covered.update(range(current.first, end))
            found.append(current)
            current = None

    while i < len(code):
        line = code[i]
        if line and not line[0].isspace():
            namespace = '.'.join(s[1] for s in stack if s[0] == 'namespace')
            is_declaration, is_notation = DECLARATION.match(line), NOTATION.match(line)
            if not is_declaration and not is_notation and PREFIXABLE.match(line):
                j = continued(i)
                if ENDS_IN.search(code[j - 1]):   # a command that holds for the next declaration only
                    close(i)
                    if pending is None:
                        pending = i
                    i = j
                    continue
            if is_declaration or is_notation:
                start = pending if pending is not None else i
                close(start)
                d = Declaration()
                d.first, d.keyword_line = start, i
                if is_declaration:
                    d.kind, name = is_declaration.group(1), is_declaration.group(2)
                    if name is None:
                        name = '[anonymous %s]' % d.kind
                    d.name = name[7:] if name.startswith('_root_.') else \
                        (namespace + '.' if namespace else '') + name
                else:
                    d.kind, d.name = is_notation.group(1), '[%s]' % is_notation.group(1)
                d.in_force = tuple(in_force)
                result.skeleton.append('declaration ' + d.name)
                current, pending = d, None
            elif line.startswith('@[') and not SECTION_OPENER.match(line):
                close(i)
                if pending is None:
                    pending = i
            elif line.strip() == 'module' or IMPORT.match(line):
                close(i)
                pending = None
                j = continued(i)
                covered.update(range(i, j))
                result.imports.append(' '.join(' '.join(code[i:j]).split()))
            else:
                close(i)
                pending = None
                j = continued(i)
                covered.update(range(i, j))
                whole = ' '.join(' '.join(code[i:j]).split())
                words = whole.split()
                opener = SECTION_OPENER.match(line)
                if not MODULE_SYSTEM_SECTION.match(line):
                    result.between.append(whole)
                    result.skeleton.append(whole)
                    if words[0] == 'namespace' and len(words) > 1:
                        stack.append(('namespace', words[1], len(in_force)))
                        in_force.append(whole)
                    elif opener:
                        stack.append(('section', opener.group(1), len(in_force)))
                        if 'noncomputable' in line:
                            in_force.append('noncomputable section')
                    elif words[0] == 'end' and stack:
                        in_force = in_force[:stack.pop()[2]]
                    else:
                        in_force.append(whole)
        i += 1
    close(len(code))
    for d in found:                              # the doc comment: right above, or after "... in"
        j = d.first - 1
        while j >= 0 and not raw[j].strip():
            j -= 1
        d.doc = ''
        if j >= 0 and not code[j].strip() and raw[j].rstrip().endswith('-/'):
            k = j
            while k >= 0 and '/-' not in raw[k]:
                k -= 1
            if k >= 0 and raw[k].lstrip().startswith('/--'):
                d.doc = ' '.join(' '.join(raw[k:j + 1]).split())
        inside = '\n'.join(raw[d.first:d.keyword_line])
        at = inside.find('/--')
        if not d.doc and at >= 0 and inside.find('-/', at) >= 0:
            d.doc = ' '.join(inside[at:inside.find('-/', at) + 2].split())
    result.declarations, result.code = found, code
    result.long_comments = [' '.join(m.split()) for m in re.findall(r'/-!.*?-/', text, flags=re.S)]
    result.stray = [n + 1 for n, line in enumerate(code) if line.strip() and n not in covered]
    return result


def split_declaration(d, code):
    """(words of the statement, words of the proof) of a declaration."""
    lines = code[d.first:d.last]
    in_front = d.keyword_line - d.first
    head, options, k = [], [], 0
    while k < in_front:
        block = [lines[k]]
        while not ENDS_IN.search(block[-1]) and not block[0].startswith('@[') and k + len(block) < in_front:
            block.append(lines[k + len(block)])
        (options if block[0].startswith('set_option') else head).extend(block)
        k += len(block)
    body = '\n'.join(lines[in_front:])
    if d.kind not in ('theorem', 'lemma'):
        return ' '.join(head + [body]).split(), ' '.join(options).split()
    depth, open_lets = 0, 0
    for at, c in enumerate(body):
        if c in '([{⟨⦃':
            depth += 1
        elif c in ')]}⟩⦄':
            depth -= 1
        elif depth == 0 and re.match(r'(?<![\w.])(let|have)\b', body[at:at + 5]) and \
                (at == 0 or not (body[at - 1].isalnum() or body[at - 1] in "._'")):
            open_lets += 1                       # "let x := ..." inside the statement
        elif depth == 0 and body.startswith(':=', at):
            if open_lets:
                open_lets -= 1
                continue
            return ' '.join(head + [body[:at]]).split(), ' '.join(options + [body[at:]]).split()
        elif depth == 0 and c == '|' and body[:at].rstrip(' ').endswith('\n'):
            return ' '.join(head + [body[:at]]).split(), ' '.join(options + [body[at:]]).split()
    return ' '.join(head + [body]).split(), ' '.join(options).split()


def first_comment(text):
    end = text.find('-/')
    return text[:end + 2] if text.startswith('/-') and end >= 0 else ''


def count_of(number, noun):
    return '%d %s%s' % (number, noun, '' if number == 1 else 's')


def named(line):
    return '"%s"' % line if len(line.split()) <= 3 else 'a line that begins "%s"' % line.split()[0]


def in_words(names):
    return ', '.join(names) if names else 'none'


def second_comment(text, first):
    rest = text[len(first):].lstrip()
    end = rest.find('-/')
    return ' '.join(rest[2:end].split()) if rest.startswith('/-') and end >= 0 else ''


def fingerprint(words):
    return hashlib.sha256(' '.join(words).encode('utf-8')).hexdigest()[:16]


def read_table(name, columns):
    rows, path = [], os.path.join(HERE, name)
    if not os.path.exists(path):
        sys.exit('the table %s is missing; it belongs beside this program' % name)
    with open(path, encoding='utf-8') as table:
        for number, line in enumerate(table, 1):
            if number == 1 or not line.strip():
                continue
            cells = line.rstrip('\n').split('\t')
            if len(cells) != columns:
                sys.exit('%s, line %d: %d columns expected, %d found' % (name, number, columns, len(cells)))
            rows.append(tuple(cells))
    return rows


def commit_of(folder):
    """the commit that a git checkout is at, or None if it cannot be read"""
    if not os.path.exists(os.path.join(folder, '.git')):
        return None
    try:
        done = subprocess.run(['git', '-C', folder, 'rev-parse', 'HEAD'], capture_output=True, text=True)
    except OSError:
        return None
    return done.stdout.strip() if done.returncode == 0 else None


NAME_CHARACTER = r"[A-Za-z0-9_'!?]"


def main():
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawTextHelpFormatter)
    parser.add_argument('--arklib', required=True, metavar='DIR', help='see above')
    parser.add_argument('--mathlib', required=True, metavar='DIR', help='see above')
    parser.add_argument('--tree', default=os.path.dirname(HERE), metavar='DIR', help='see above')
    parser.add_argument('--write-list', metavar='F', help='see above')
    args = parser.parse_args()

    commits_read = []
    for folder, inner, url, commit in ((args.arklib, 'ArkLib', ARKLIB_URL, ARKLIB_COMMIT),
                                       (args.mathlib, 'Mathlib', MATHLIB_URL, MATHLIB_COMMIT)):
        if not os.path.isdir(os.path.join(folder, inner)):
            sys.exit('%s has no folder %s: is it a checkout of %s?' % (folder, inner, url))
        at = commit_of(folder)
        commits_read.append(at is not None)
        if at is None:
            print('note: the commit of %s could not be read, so it is not checked (wanted: %s)' % (folder, commit))
        elif at != commit:
            sys.exit('%s is at commit %s; wanted: %s' % (folder, at, commit))

    kept = collections.defaultdict(list)
    for path, name, kind in read_table('kept_declarations.tsv', 3):
        kept[path].append(name + ' (' + kind + ')')
    listed = {(f, d, k): (why, mark) for f, d, k, why, mark in read_table('listed_changes.tsv', 5)}
    renamed = [(re.compile(r'(?<!' + NAME_CHARACTER + r')' + re.escape(new.split('.')[-1]) +
                           r'(?!' + NAME_CHARACTER + r')'), new, old.split('.')[-1])
               for new, old in read_table('renamed_lemmas.tsv', 2)]

    def turn_back(words):
        """the outside words with the newer names of renamed lemmas replaced by the older names"""
        text, places, names = ' '.join(words), 0, []
        for pattern, new, old in renamed:
            text, n = pattern.subn(old, text)
            places += n
            if n:
                names.append(new)
        return text.split(), places, names

    complaints, met, rows, names_in_use = [], set(), [], set()
    counts = {'ArkLib': collections.Counter(), 'MathlibBackport': collections.Counter()}
    largest = [0, 0]

    def compare(part, outside_root, outside_prefix, url, commit):
        count = counts[part]

        def differs(our_file, name, kind, our_words, detail=''):
            key = (our_file, name, kind)
            met.add(key)
            count[kind] += 1
            if key not in listed:
                complaints.append('%s: %s: the %s differ%s from the outside file, and listed_changes.tsv has no '
                                  'row for it%s' % (our_file, name, kind, '' if kind.endswith('s') else 's', detail))
            elif listed[key][1] != fingerprint(our_words):
                complaints.append('%s: %s: the %s in the tree %s not the text that listed_changes.tsv covers '
                                  '(fingerprint %s in the tree, %s in the table; --help says what to do)'
                                  % (our_file, name, kind, 'are' if kind.endswith('s') else 'is',
                                     fingerprint(our_words), listed[key][1]))

        top = os.path.join(args.tree, part)
        for folder, _, names in sorted(os.walk(top)):
            for file_name in sorted(names):
                if not file_name.endswith('.lean'):
                    continue
                path = os.path.join(folder, file_name)
                inner = os.path.relpath(path, top).replace(os.sep, '/')
                our_file = 'ThirdParty/%s/%s' % (part, inner)
                outside_file = outside_prefix + '/' + inner
                outside_path = os.path.join(outside_root, outside_file)
                if not os.path.exists(outside_path):
                    complaints.append('%s: there is no file %s in the outside checkout' % (our_file, outside_file))
                    continue
                with open(path, encoding='utf-8') as f:
                    ours_text = f.read()
                with open(outside_path, encoding='utf-8') as f:
                    theirs_text = f.read()
                count['files'] += 1
                head = first_comment(theirs_text)
                if head and ours_text.startswith(head):
                    count['first comments'] += 1
                else:
                    complaints.append('%s: it does not begin with the first comment of the outside file, '
                                      'byte for byte' % our_file)
                note = second_comment(ours_text, head)
                wanted = 'Adapted from %s (%s), file %s, commit %s' % (outside_prefix, url, outside_file, commit)
                if not note.startswith(wanted):
                    complaints.append('%s: its second comment does not begin "%s"' % (our_file, wanted))
                ours, theirs = parse(ours_text), parse(theirs_text)
                for number in ours.stray:
                    complaints.append('%s, line %d: code that belongs to no declaration, import or line between '
                                      'declarations' % (our_file, number))
                for import_line in ours.imports:
                    words = import_line.split()
                    module = words[-1]
                    if len(words) != 2 or words[0] != 'import':
                        complaints.append('%s: "%s": in our files an import is the word "import" and one module, '
                                          'on one line' % (our_file, import_line))
                    elif module in ('Mathlib', 'Batteries'):
                        complaints.append('%s: it imports all of %s, not single modules' % (our_file, module))
                    elif not re.match(r'^(Mathlib|Batteries|ThirdParty)\.[\w.]+$', module):
                        complaints.append('%s: it imports %s, which is no module of Mathlib, Batteries or '
                                          'ThirdParty' % (our_file, module))
                    elif module.startswith('ThirdParty.') and not os.path.exists(
                            os.path.join(args.tree, *module.split('.')[1:]) + '.lean'):
                        complaints.append('%s: it imports %s, which is not in the tree' % (our_file, module))
                by_name = collections.defaultdict(list)
                for position, d in enumerate(theirs.declarations):
                    by_name[d.name].append((position, d))
                there = collections.Counter(d.name for d in theirs.declarations)
                last_position, changes, places, in_force_differs = -1, collections.defaultdict(list), 0, False
                for d in ours.declarations:
                    if not by_name[d.name]:
                        complaints.append('%s: %s %s' % (our_file, d.name,
                                          'occurs more often than in the outside file' if there[d.name]
                                          else 'is not a declaration of the outside file'))
                        continue
                    position, t = by_name[d.name].pop(0)
                    if position < last_position:
                        complaints.append('%s: %s does not stand in the order of the outside file' % (our_file, d.name))
                    last_position = position
                    count['declarations'] += 1
                    our_statement, our_proof = split_declaration(d, ours.code)
                    their_statement, their_proof = split_declaration(t, theirs.code)
                    kind = 'statement' if d.kind in ('theorem', 'lemma') else 'definition'
                    if our_statement != their_statement:
                        turned, n, names_met = turn_back(their_statement)
                        if kind == 'definition' and our_statement == turned:
                            places += n
                            names_in_use.update(names_met)
                            changes['renamed inside a definition'].append(d.name)
                        else:
                            differs(our_file, d.name, kind, our_statement)
                            changes[kind].append(d.name)
                    if our_proof != their_proof:
                        turned, n, names_met = turn_back(their_proof)
                        if our_proof == turned:
                            places += n
                            names_in_use.update(names_met)
                        else:
                            differs(our_file, d.name, 'proof', our_proof)
                            steps = difflib.SequenceMatcher(None, their_proof, our_proof, autojunk=False).get_opcodes()
                            removed = sum(b - a for op, a, b, _, _ in steps if op in ('delete', 'replace'))
                            added = sum(b - a for op, _, _, a, b in steps if op in ('insert', 'replace'))
                            largest[0], largest[1] = max(largest[0], removed), max(largest[1], added)
                            changes['proof'].append('%s (%s removed, %d added)'
                                                    % (d.name, count_of(removed, 'word'), added))
                    if d.in_force != t.in_force:
                        in_force_differs = True
                    if d.doc != t.doc:
                        differs(our_file, d.name, 'doc comment', d.doc.split())
                        changes['doc comment'].append(d.name)
                if in_force_differs or ours.between != theirs.between:
                    left, right = collections.Counter(theirs.between), collections.Counter(ours.between)
                    only_there, only_here = sorted((left - right).elements()), sorted((right - left).elements())
                    said = '; '.join(['"%s" in the outside file only' % x for x in only_there] +
                                     ['"%s" in ours only' % x for x in only_here]) \
                        or 'the same lines, in force at other declarations'
                    differs(our_file, ALL_LINES, 'lines', ours.skeleton, ': ' + said)
                    # the list names a long line by its first word; the complaint above quotes it
                    short = '; '.join([named(x) + ' in the outside file only' for x in only_there] +
                                      [named(x) + ' in ours only' for x in only_here]) \
                        or 'the same lines, in force at other declarations'
                    changes['lines'] = ['written anew'] if part == 'MathlibBackport' else [short]
                if part == 'ArkLib' and ours.long_comments != theirs.long_comments:
                    differs(our_file, ALL_LONG_COMMENTS, 'long comments', ours.long_comments)
                    changes['long comments'] = ['see listed_changes.tsv']
                want = collections.Counter(kept.get(outside_file, []))
                have = collections.Counter('%s (%s)' % (d.name, d.kind) for d in ours.declarations)
                if want != have:
                    complaints.append('%s: its declarations are not those of kept_declarations.tsv (in the table only: '
                                      '%s; in the file only: %s)' % (our_file, in_words(sorted((want - have).elements())),
                                                                     in_words(sorted((have - want).elements()))))
                count['places'] += places
                n_ours, n_theirs = len(ours.declarations), len(theirs.declarations)
                how = [('the one declaration kept' if n_ours == 1 else 'all %d declarations kept' % n_ours)
                       if n_ours == n_theirs else 'cut to %d of %s' % (n_ours, count_of(n_theirs, 'declaration'))]
                for kind, label in (('statement', 'statement changed'), ('definition', 'definition changed'),
                                    ('proof', 'proof changed'), ('lines', 'lines between declarations'),
                                    ('doc comment', 'doc comment changed'), ('long comments', 'long comments changed'),
                                    ('renamed inside a definition',
                                     'definition that calls a renamed lemma in a proof argument')):
                    if changes[kind]:
                        how.append('%s: %s' % (label, ', '.join(changes[kind])))
                if places:
                    how.append('renamed lemmas of Lean or Mathlib called by their older names, %d time%s'
                               % (places, '' if places == 1 else 's'))
                if part == 'MathlibBackport':
                    how.append('the long comments of the file not taken over')
                how.append('import lines set anew; "module", "public" and "@[expose] public section" removed')
                if outside_file in ASKS_MORE_FILES:
                    how.append(ASKS_MORE)
                    if ASKS_MORE_PREMISE not in blank_comments(ours_text):
                        complaints.append('%s: no premise %s...] stands in it, but the list says that this premise '
                                          'asks more here' % (our_file, ASKS_MORE_PREMISE))
                if SHIM_MODULE in [line.split()[-1] for line in ours.imports]:
                    how.append(SHIM_SENTENCE)
                marks, further = FURTHER_SOURCES.get(outside_file, (set(), ''))
                for mark in (RS_LD_MCA, OLDER_ARKLIB, OLDER_ARKLIB_2, PROXIMITY_PRIZE):
                    if (mark in ours_text) != (mark in marks):
                        complaints.append('%s: %s %s' % (our_file, mark, 'does not stand in it, but the list names it '
                                          'as a further source' if mark in marks else
                                          'stands in it, but the list does not name it as a further source'))
                rows.append((our_file, '%d of %s' % (n_ours, count_of(n_theirs, 'declaration')),
                             '%s, %s, commit %s' % (url, outside_file, commit) +
                             ("; by ArkLib's long comment in that file, " + further if further else ''),
                             'changed: ' + '; '.join(how)))

    compare('ArkLib', args.arklib, 'ArkLib', ARKLIB_URL, ARKLIB_COMMIT)
    compare('MathlibBackport', args.mathlib, 'Mathlib', MATHLIB_URL, MATHLIB_COMMIT)

    for path in kept:
        part = 'ArkLib' if path.startswith('ArkLib/') else 'MathlibBackport'
        if not os.path.exists(os.path.join(args.tree, part, path.split('/', 1)[1])):
            complaints.append('kept_declarations.tsv names %s, but the tree has no file for it' % path)
    for _, new, _ in renamed:
        if new not in names_in_use:
            complaints.append('renamed_lemmas.tsv names %s, but the comparison does not need it' % new)

    own = 0
    for folder, _, names in sorted(os.walk(args.tree)):
        for file_name in sorted(names):
            rel = 'ThirdParty/' + os.path.relpath(os.path.join(folder, file_name), args.tree).replace(os.sep, '/')
            if file_name.endswith('.lean') and not rel.startswith(('ThirdParty/ArkLib/', 'ThirdParty/MathlibBackport/')):
                if rel in OWN_FILES:
                    own += 1
                    rows.append((rel, OWN_LEAD.get(rel, 'nothing: our own file. ') + OWN_FILES[rel], OWN_FROM.get(rel, 'none'),
                                 'not applicable'))
                    key = (rel, WHOLE_FILE, 'own file')
                    met.add(key)
                    with open(os.path.join(folder, file_name), encoding='utf-8') as f:
                        mark = fingerprint(f.read().split())
                    if key not in listed:
                        complaints.append('%s: listed_changes.tsv has no row of kind "own file" for it' % rel)
                    elif listed[key][1] != mark:
                        complaints.append('%s: it is not the text that listed_changes.tsv covers (fingerprint %s in '
                                          'the tree, %s in the table; --help says what to do)'
                                          % (rel, mark, listed[key][1]))
                else:
                    complaints.append('%s: a Lean file that is neither taken over nor one of our own two' % rel)
    for rel in OWN_FILES:
        if not os.path.exists(os.path.join(args.tree, rel.split('/', 1)[1])):
            complaints.append('%s is missing' % rel)
    rows.extend(OUTSIDE_THIS_FOLDER)
    for rel, which, outside in COPIES:
        source = os.path.join(args.arklib if which == 'arklib' else args.mathlib, outside)
        copy = os.path.join(args.tree, rel)
        if not os.path.exists(source):
            complaints.append('%s has no file %s' % (os.path.dirname(source), outside))
        elif not os.path.exists(copy):
            complaints.append('ThirdParty/%s is missing' % rel)
        elif open(copy, 'rb').read() != open(source, 'rb').read():
            complaints.append('ThirdParty/%s is not the file %s of the outside checkout, byte for byte' % (rel, outside))
    expected = set(OTHER_FILES) | set(rel for rel, _, _ in COPIES)
    for folder, _, names in sorted(os.walk(args.tree)):
        for file_name in sorted(names):
            rel = os.path.relpath(os.path.join(folder, file_name), args.tree).replace(os.sep, '/')
            if not file_name.endswith('.lean') and rel not in expected:
                complaints.append('ThirdParty/%s: a file that does not belong here' % rel)
    for rel in OTHER_FILES:
        if rel != 'TAKEN-OVER.tsv' and not os.path.exists(os.path.join(args.tree, rel)):
            complaints.append('ThirdParty/%s is missing' % rel)
    for key in listed:
        if key not in met and not (key[2] == 'own file' and key[0] in OWN_FILES):
            complaints.append('%s: %s: listed_changes.tsv has a row of kind "%s", but there is no such difference' % key)

    text = 'our file\twhat was taken over\toutside file and commit\tchanged or not, and how\n' + \
        ''.join('\t'.join(row) + '\n' for row in rows)
    if args.write_list:
        try:
            with open(args.write_list, 'x', encoding='utf-8') as out:
                out.write(text)
        except FileExistsError:
            sys.exit('%s exists already, and this program overwrites no file. Name a file that does not exist yet, '
                     'look at it, and move it into place yourself.' % args.write_list)
    else:
        shipped = os.path.join(args.tree, 'TAKEN-OVER.tsv')
        if not complaints and (not os.path.exists(shipped) or open(shipped, encoding='utf-8').read() != text):
            complaints.append('TAKEN-OVER.tsv in the tree is not the list that this program writes '
                              '(--write-list writes it)')

    print('%-64s %8s %16s' % ('', 'ArkLib', 'MathlibBackport'))
    for label, key in (('files', 'files'), ('declarations', 'declarations'),
                       ('files that begin with the outside file\'s first comment', 'first comments'),
                       ('statements changed', 'statement'), ('definitions changed', 'definition'),
                       ('proofs changed', 'proof'), ('files with changed lines between declarations', 'lines'),
                       ('doc comments changed', 'doc comment'), ('files with changed long comments', 'long comments'),
                       ('places where a renamed lemma is called by its older name', 'places')):
        print('%-64s %8d %16d' % (label, counts['ArkLib'][key], counts['MathlibBackport'][key]))
    print('renamed lemmas in renamed_lemmas.tsv: %d' % len(renamed))
    print('largest change in a proof: %d words removed, %d words added' % tuple(largest))
    print('our own Lean files: %d' % own)
    if args.write_list:
        print('written: %s (%d rows)' % (args.write_list, len(rows)))
    for complaint in complaints:
        print('FAIL ' + complaint)
    if complaints:
        print('RESULT: %s; each line above that begins FAIL names one.%s' % (
              count_of(len(complaints), 'complaint'), '' if all(commits_read) else
              ' A checkout that is not at the commit named in a note above would cause complaints too.'))
        return 1
    print('RESULT: all as listed' + ('' if all(commits_read) else
                                     ' (if each checkout is at the commit named in a note above)'))
    return 0


if __name__ == '__main__':
    try:
        sys.exit(main())
    except (OSError, UnicodeDecodeError) as problem:
        sys.exit('cannot read or write a file: %s' % problem)
