-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Top/Own/OwnStoredFullRun.lean: tests on the public files `zStoredFull`, run by Lean's
evaluator at every build: the build fails where one says no. Written by a program; not to be edited
by hand.

States. No theorem. `#guard` lines: the BLAKE2b digests of the three files' terms are the sums that
were taken of the example's files outside Lean; `sizesRefB` and `scalesRefB` say yes;
`scalesOfFiles` returns a table; each of three tests says no at one altered or swapped file.
Under. No hypothesis.
Does not show.
  1. A theorem: an evaluation is not checked by Lean's kernel, and no statement can use these lines.
  2. That any hypothesis is proved: a test that passes here stays a hypothesis wherever it is used.
  3. That the terms are the shipped files: check that with the command in the notes.
  4. Anything on soundness.
Notes in full, with every limit at length, stand at the end of this file.

Terms: lean/GLOSSARY.md.

-/
import Johnson.Top.Own.OwnStoredFull
import Johnson.Top.Own.OwnScalesTest
import Johnson.Top.SizesRef
import Run.Blake2b.Hash
import Fmt.Rules1

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.K.Arm.Own.StoredFullRun

open VerifiableInference.OnPublicFiles

/-- The BLAKE2b digest of 32 bytes, without a key, in base 16: what `b2sum -l 256` prints of a
file. -/
def b2 (b : ByteArray) : String := Fmt.hex (Run.Blake2b.blake2b ByteArray.empty b 32)

/-- The scale file with its first byte one higher. -/
def klTurned : ByteArray := zStoredFull.KL.set! 0 (zStoredFull.KL.get! 0 + 1)

/-- The layout file with its last byte one higher. -/
def layTurned : ByteArray :=
  let i := zStoredFull.lay.size - 1
  zStoredFull.lay.set! i (zStoredFull.lay.get! i + 1)

-- the bytes of the three fields
#guard b2 zStoredFull.pol == "b44509b4d824b08c8ca2ad9496f85c5770c0f9f21afa28b86e791dbd8a7c379a"
#guard b2 zStoredFull.lay == "1e17e5f66d2e97209a66fed42c6146d86e2930743827eac6428b4227e72ece69"
#guard b2 zStoredFull.KL == "ecb0e21e81ac4b622499885637c44e20b53c6c6486665dd87eb9f0084bb3ceae"
-- the ten sizes are the reference's
#guard Flat.sizesRefB zStoredFull.pol
-- a table of scales is returned
#guard (OnBytes.Flat.scalesOfFiles zStoredFull.pol zStoredFull.KL).toOption.isSome
-- under the stricter reader it is the reference table
#guard scalesRefB zStoredFull.pol zStoredFull.KL
-- the tests can say no: a turned layout file; the scale file in the parameter file's place; a
-- turned scale file
#guard b2 layTurned != "1e17e5f66d2e97209a66fed42c6146d86e2930743827eac6428b4227e72ece69"
#guard !Flat.sizesRefB zStoredFull.KL
#guard !scalesRefB zStoredFull.pol klTurned

end OnBytes.K.Arm.Own.StoredFullRun

/-
Notes in full (other files' comments call these notes "the head of" this file).

Johnson/Top/Own/OwnStoredFullRun.lean: tests on the public files `zStoredFull`
(Johnson/Top/Own/OwnStoredFull.lean): EVALUATED AT EVERY BUILD; NO KERNEL PROOF. Each `#guard` line
below is checked by Lean's evaluator whenever this file compiles, and the file stands in the
library's default target: so a build fails where a line says no. WRITTEN BY A PROGRAM from the
example's three files; not to be turned by hand.

What is tested, at the shipped full-size example's three public files:
  the bytes: the BLAKE2b digest of 32 bytes, without a key, of each of the three fields, made by the
    library's own `Run.Blake2b.blake2b`, is the sum that the program took OUTSIDE Lean of the
    example's file of that name. So a turned byte in any of the three typed terms fails the build,
    unless the turned text has the same digest.
    To hold the sums against the files, from the repository's root:
      b2sum -l 256 examples/full-size/config/policy.txt examples/full-size/config/layout.txt \
        examples/full-size/config/KL.bin
  `sizesRefB` (Johnson/Top/SizesRef.lean): the parameter file's ten sizes are the reference's;
  `scalesOfFiles` (Johnson/Flat/ScalesOf.lean) returns a table;
  `scalesRefB` (Johnson/Top/Own/OwnScalesTest.lean): `scalesAtRef` returns a table, and it has the
    words of `Cm.sRef` at all 48 layers and its final normalisation;
  three turned files, at which the tests must say no: else a yes would be a yes for nothing.

What is not claimed. THESE ARE NO THEOREMS: an evaluation is not checked by Lean's kernel, and no
statement of the library can use a line of this file. A premise such as `scalesRefB zStoredFull.pol
zStoredFull.KL = true` stays a hypothesis, by name, wherever it is used; this file shows that Lean's
evaluator finds it true. THAT THE TYPED TERMS ARE THE SHIPPED EXAMPLE's FILES IS HELD OUTSIDE THIS
FILE, by the command above: the three sums here are what a program read off three files once.
Nothing on soundness.

Terms: lean/GLOSSARY.md.

-/
