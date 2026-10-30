# Copyright 2026 Anthropic PBC
# SPDX-License-Identifier: Apache-2.0
"""Helpers for check.py: file names, module names, and the imports in a Lean file's header."""

import hashlib, re

# The top-level module names of Lean, of Mathlib and of the packages that Mathlib depends on. No
# file of this library may use one of them as its first directory (check.py, step "tree"). Cache is
# Mathlib's download tool, which is compiled next to Mathlib.
PACKAGE_ROOTS = {
    'Mathlib',
    'Batteries',
    'Aesop',
    'Qq',
    'ProofWidgets',
    'Plausible',
    'LeanSearchClient',
    'ImportGraph',
    'Cli',
    'Lean',
    'Std',
    'Init',
    'Lake',
    'Cache',
}
NAME = re.compile(r'[A-Za-z_][A-Za-z0-9_]*(\.[A-Za-z_][A-Za-z0-9_]*)*')
REL = re.compile(r'[A-Za-z_][A-Za-z0-9_]*(/[A-Za-z_][A-Za-z0-9_]*)*\.lean')


def sha(b):
    """The sha256 of the bytes b, in hexadecimal."""
    return hashlib.sha256(b).hexdigest()


def mod_of(rel):
    """The module name of a path from the library's top directory: "A/B.lean" gives "A.B". That rel
    ends with ".lean" is not checked."""
    return rel[:-5].replace('/', '.')


def rel_of(mod):
    """The path, from the library's top directory, of a module: "A.B" gives "A/B.lean"."""
    return mod.replace('.', '/') + '.lean'


def imports_of(text):
    """Returns the modules that a Lean file imports. Reads the header as Lean 4.29.1 does: an
    optional "module" and "prelude", then any number of "[public] [meta] import [all] A.B".
    Raises ValueError for a header that it cannot be sure to read as Lean would. An import that it
    missed would escape every rule of check.py that goes by imports, and nothing else would notice;
    compared with Lean's own parser on 50,000 generated headers, it missed none.
    """
    n = len(text)

    def skip(i):
        # Skips white space and comments by Lean's rule (Lean.Parser.whitespace,
        # finishCommentBlock). "--" runs to the end of the line. "/-" opens a comment, except that
        # "/--" and "/-!" are tokens and end the header.
        while i < n:
            c = text[i]
            if c in ' \t\r\n':
                i += 1
            elif text.startswith('--', i):
                j = text.find('\n', i)
                i = n if j < 0 else j + 1
            elif text.startswith('/-', i):
                if i + 2 < n and text[i + 2] in '-!':
                    return i
                # Lean skips one character after "/-" before it counts nesting, so "/-/- -/" is one
                # closed comment.
                i += 3
                d = 1
                while d:
                    if i >= n:
                        raise ValueError('a comment in the header that does not end')
                    c = text[i]
                    i += 1
                    if c == '-' and i < n and text[i] == '/':
                        d -= 1
                        i += 1
                    elif c == '/' and i < n and text[i] == '-':
                        d += 1
                        i += 1
            else:
                break
        return i

    W = re.compile(r"[A-Za-z_][A-Za-z0-9_]*")

    def word(i):
        # A word ends where its letters end, not only at white space: "import/- c -/X" imports X.
        m = W.match(text, i)
        return (m.group(0), m.end()) if m else ('', i)

    def clean_end(j, what):
        """Raises ValueError unless white space, a comment or the end of the file follows at j."""
        if j < n and not (
            text[j] in ' \t\r\n' or text.startswith('--', j) or text.startswith('/-', j)
        ):
            raise ValueError(
                (
                    'in the header, "%s" is followed by "%s", which cannot be read '
                    'with certainty as Lean reads it'
                )
                % (what[:60], text[j : j + 12])
            )

    out, i, stage = [], 0, 0
    while True:
        i = skip(i)
        w, j = word(i)
        if w in ('module', 'prelude') and not out and stage == 0:
            clean_end(j, w)
            i = j
            continue
        pre = []
        k = i
        while w in ('public', 'meta'):
            if j < n and not (
                text[j] in ' \t\r\n' or text.startswith('--', j) or text.startswith('/-', j)
            ):
                break  # "public.x" or "meta'" is a different word, so the header has ended
            pre.append(w)
            k = skip(j)
            w, j = word(k)
        if w != 'import':
            if w.startswith('import') or (not pre and w in ('module', 'prelude')):
                raise ValueError(
                    (
                        'the header ends at the word "%s", which cannot be read with '
                        'certainty as Lean reads it'
                    )
                    % w[:60]
                )
            if text.startswith('#lang', k):
                raise ValueError(
                    'the header ends at "#lang": after a first line "#lang lean4" '
                    'Lean\'s command line drops that line and reads on '
                    '(Lean/Shell.lean:510-523), so imports that this parser does not '
                    'see may follow'
                )
            # Any other word starts a command. Lean accepts no import after a command.
            break
        i = k
        clean_end(j, w)
        stage = 1
        i = skip(j)
        w, j = word(i)
        if w == 'all' and not text.startswith('.', j):
            k = skip(j)
            w2, j2 = word(k)
            if w2 and w2 not in ('import', 'public', 'meta'):
                clean_end(j, 'all')
                # This is "import all X". A bare "import all" imports a module named all.
                i, w, j = k, w2, j2
        m = NAME.match(text, i)
        if not m:
            raise ValueError('an import that cannot be read: "%s"' % text[i : i + 40])
        clean_end(m.end(), m.group(0))
        out.append(m.group(0))
        i = m.end()
    return out
