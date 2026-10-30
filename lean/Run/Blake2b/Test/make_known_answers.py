#!/usr/bin/env python3
# Copyright 2026 Anthropic PBC
# SPDX-License-Identifier: Apache-2.0
"""Makes the text of Run/Blake2b/Test/KnownAnswers.lean, which is beside this script.
The expected digests come from hashlib.blake2b of the Python that runs it. The head that it writes
names CPython 3.13.16, so it writes under that version only. It compares under any version.

From the directory lean/:
    python3 -B Run/Blake2b/Test/make_known_answers.py
        compares: says whether KnownAnswers.lean is, byte for byte, what this script makes, and
        which Python ran. It writes nothing.
    python3 -B Run/Blake2b/Test/make_known_answers.py --out NEW-FILE
        writes the text to NEW-FILE, which must not exist yet. It never writes over a file.
Exit status: 0 the same, or written; 1 not the same; 2 a wrong call, --out under another Python, or
a file could not be read or wholly written (a part of NEW-FILE may remain).
"""
import hashlib
import os
import sys

LENGTHS = [0, 1, 63, 64, 127, 128, 129, 255, 256, 257, 1000, 4096, 65536]
# (key length, digest length, message length)
KEYED = [(1, 64, 0), (64, 64, 0), (64, 64, 1), (64, 64, 128), (64, 64, 129), (32, 32, 256),
         (17, 1, 1000), (0, 1, 0), (0, 32, 128), (0, 63, 4096)]
# The grid: every key length with every digest length and every message length.
# Keys: none, the shortest, the middle, the longest.
# Digests: the shortest, 16, 32 with its two neighbours, the longest.
# Messages: 0, 1, and the lengths just below, at and just above 1, 2 and 5 blocks of 128 bytes.
GRID_KEYS = [0, 1, 32, 64]
GRID_DIGESTS = [1, 16, 31, 32, 33, 64]
GRID_MESSAGES = [0, 1] + [128 * j + d for j in (1, 2, 5) for d in (-1, 0, 1)]
GRID = [(k, outlen, n) for k in GRID_KEYS for outlen in GRID_DIGESTS for n in GRID_MESSAGES]


def pattern(n):
    return bytes(i % 251 for i in range(n))


def ramp(n, s):
    return bytes((n + s * i) % 256 for i in range(n))


def row(numbers, digest, last):
    """One row of a table. A digest of more than 64 digits is written as two strings."""
    head = "  (" + ", ".join(str(x) for x in numbers) + ", "
    end = ")]" if last else "),"
    if len(digest) <= 64:
        return [head + '"' + digest + '"' + end]
    return [head + '"' + digest[:64] + '" ++', '    "' + digest[64:] + '"' + end]


lines = """-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Run/Blake2b/Test/KnownAnswers.lean

Expected digests for the tests in Vectors.lean and SpecKnown.lean: three tables, 287 rows.
make_known_answers.py, beside this file, makes its text; change the script, not this file. Called
without arguments, the script says whether this file is what it makes.
The digests are those that `hashlib.blake2b` of CPython 3.13.16 gives.
Limit: these values are not of another origin than the text under test. The BLAKE2b of that hashlib
is compiled from the BLAKE2 authors' own source code package, from which both Lean texts
(Run/Blake2b/Spec.lean, Run/Blake2b/Hash.lean) are adapted. Values of another code origin:
OtherOrigin.lean. Its table has all 13 digests of `known512`, and with them that of the grid's row
for the empty message with no key and a digest of 64 bytes: for these 14 rows the limit does not
hold.
-/
import Run.Blake2b.Test.Util

namespace Run.Blake2b.Test

/-- BLAKE2b-512 without a key: the length of the message and the digest. The message of n bytes is
`pattern n`. -/
def known512 : List (Nat × String) := [""".split("\n")
for j, n in enumerate(LENGTHS):
    lines += row([n], hashlib.blake2b(pattern(n)).hexdigest(), j + 1 == len(LENGTHS))
lines += """
/-- Other parameters: the length of the key, of the digest and of the message, and the digest. The
message of n bytes is `pattern n`, the key of k bytes `pattern k`. -/
def knownOther : List (Nat × Nat × Nat × String) := [""".split("\n")
for j, (k, outlen, n) in enumerate(KEYED):
    d = hashlib.blake2b(pattern(n), key=pattern(k), digest_size=outlen).hexdigest()
    lines += row([k, outlen, n], d, j + 1 == len(KEYED))
lines += """
/-- The grid's text of n bytes with the step s: byte i is (n + s i) mod 256. -/
def ramp (n s : Nat) : ByteArray :=
  (List.range n).foldl (fun o i => o.push ((n + s * i) % 256).toUInt8)
    (ByteArray.emptyWithCapacity n)

/-- The grid: the length of the key, of the digest and of the message, and the digest. The message
of n bytes is `ramp n 3`, the key of k bytes `ramp k 5`. Every key length of 0, 1, 32, 64 is
combined with every digest length of 1, 16, 31, 32, 33, 64 and every message length of 0, 1, 127,
128, 129, 255, 256, 257, 639, 640, 641 (just below, at and just above 1, 2 and 5 blocks). -/
def knownGrid : List (Nat × Nat × Nat × String) := [""".split("\n")
for j, (k, outlen, n) in enumerate(GRID):
    d = hashlib.blake2b(ramp(n, 3), key=ramp(k, 5), digest_size=outlen).hexdigest()
    lines += row([k, outlen, n], d, j + 1 == len(GRID))
lines += ["", "end Run.Blake2b.Test", ""]
text = "\n".join(lines).encode("utf-8")

ME = "make_known_answers.py"
HERE = os.path.dirname(os.path.realpath(__file__))
if len(sys.argv) == 1:
    try:
        with open(os.path.join(HERE, "KnownAnswers.lean"), "rb") as f:
            same = f.read() == text
    except OSError as e:
        sys.stderr.write("%s: cannot read KnownAnswers.lean beside this script: %s\n"
                         % (ME, e.strerror))
        sys.exit(2)
    print("KnownAnswers.lean %s what this script makes (run under %s %s)"
          % ("is, byte for byte," if same else "IS NOT",
             sys.implementation.name, sys.version.split()[0]))
    sys.exit(0 if same else 1)
if len(sys.argv) != 3 or sys.argv[1] != "--out" or sys.argv[2] == "" or sys.argv[2].startswith("-"):
    sys.stderr.write("use: %s [--out NEW-FILE]\n" % ME)
    sys.exit(2)
if sys.implementation.name != "cpython" or sys.version_info[:3] != (3, 13, 16):
    sys.stderr.write("%s: the head of the text names CPython 3.13.16; this is %s %s; "
                     "nothing was written\n"
                     % (ME, sys.implementation.name, sys.version.split()[0]))
    sys.exit(2)
try:
    with open(sys.argv[2], "xb") as f:  # "x": it fails if anything exists at that path
        f.write(text)
except OSError as e:
    sys.stderr.write("%s: cannot make %s: %s; no file was written over\n"
                     % (ME, sys.argv[2], e.strerror))
    sys.exit(2)
print("written: %s" % sys.argv[2])
