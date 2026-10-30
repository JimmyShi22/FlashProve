-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Run/Blake2b/Test/SpecKnown.lean

Build-time tests of the plain definition of BLAKE2b, `Spec.blake2b` (Run/Blake2b/Spec.lean), against
the 287 digests of KnownAnswers.lean. Vectors.lean compares the fast function with the same three
tables. So the plain definition is tested by itself with keys, shorter digests and messages of
several blocks. Compiling this file runs the tests in Lean's interpreter; if one fails, it does not
compile. Nothing imports this file.
Limits: the digests are those of the hashlib of CPython 3.13.16, which is not of another origin than
that definition (the head of KnownAnswers.lean). No test reaches the carry into the high word of
that definition's counter (`Spec.blake2b_increment_counter`); only theorems tie it to the fast
function's (`increment_at`, Run/Blake2b/LoadThm.lean; `blake2b_eq_spec_all`,
Run/Blake2b/SpecThm.lean). A `#guard` is not checked by Lean's kernel.
-/
import Run.Blake2b.Spec
import Run.Blake2b.Test.KnownAnswers

namespace Run.Blake2b.Test

-- The grid: 264 rows.
#guard knownGrid.all fun (k, outlen, n, d) =>
  Spec.blake2b (ramp k 5).data (ramp n 3).data outlen == (hex d).data
-- BLAKE2b-512 without a key: 13 rows.
#guard known512.all fun (n, d) => Spec.blake2b #[] (pattern n).data 64 == (hex d).data
-- Keys and shorter digests: 10 rows.
#guard knownOther.all fun (k, outlen, n, d) =>
  Spec.blake2b (pattern k).data (pattern n).data outlen == (hex d).data

end Run.Blake2b.Test
