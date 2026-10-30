-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Ask/KeyThirdChainFull.lean: an asking file: `third` (Johnson/KeyRun/Third.lean), a check of the
third of a key file's three hash chains as a plain function with code, is asked at the full-size
stored example's key file and at 24 changed copies of its arguments. The full-size twin of
Ask/KeyThirdChainSmall.lean, with fewer rows.

No soundness: a test. A yes from this run is not a verification of the key file.

Reads: examples/full-size/config/policy.txt, examples/full-size/config/KL.bin,
examples/full-size/config/layout.txt, examples/full-size/ivk/key.bin. Every change is made in
memory. Nothing is written to disk.

Command: from lean/, behind a build and the block of Ask/README.md, "The faster way", which makes
libvob.so out of the compiled modules of the text of verify-on-bytes:
`LEAN_ABORT_ON_PANIC=1 lake env lean -j1 --load-dynlib=./libvob.so --tstack=1000000 \
Ask/KeyThirdChainFull.lean`. Without the variable a panic in a row that expects no would count as
that no. Without `--load-dynlib=./libvob.so` Lean interprets all the code: that was not measured at
this size.

Takes: AS MEASURED at a form of this file with 22 of the 25 rows, from disk, on one
machine, with libvob.so (200 objects) and a stack of 1,000,000 KiB: 20 minutes and a peak of 6.0
GiB. An evaluation that reaches the last stage took 100 to 140 s; a row that is refused before the
proximity test took 2 s or less. `third` and the files of Fmt/ that it calls are no modules of the
text of verify-on-bytes: they are interpreted in this run too. This form, with all its rows, is not
what was measured.

Its print means: Lean's evaluator computed `third` at 25 inputs and printed each answer and whether
it is the answer that this file expects. The lines, the rows' numbers and their words are those of
Ask/KeyThirdChainSmall.lean: see its head at this label. Asked here: row 0; rows 1, 2 and 5 (values
of the first chain of which the claim is made); rows 6 and 8, KNOWN LIMITS, which expect a yes; rows
9, 10, 12 and 18; six rows on the views or the plan that are refused before the proximity test (21,
29, 30, 31, 33, 34); and rows 36, 37, 38, 45, 48, 50, 64, 65 and 67 on the plan. AT ROWS 38, 64, 65
AND 67 `dec₃` BY ITSELF SAYS YES, and one test on the plan alone says no: the eighth, the tenth, the
eighth, the sixth. The first, second, fourth, seventh and ninth test say no at no row of this file.
The first piece that says no is printed at the rows where that costs little; at rows 0 to 18 the yes
or no alone comes out, not which test said no. The last line says how many rows were asked: 25 of
100.

It does not mean: All that Ask/KeyThirdChainSmall.lean does not mean, with `dryKeyFull` for
`dryKeySmall`. This file's command loads libvob.so: trusted are the evaluator, Lean's compiler to C,
the C compiler, the linking, that libvob.so was made from these sources, and that the bytes on disk
are the named files'. That most rows on a view end at one and the same equation is printed at the
small size alone.

For which format: as in Ask/KeyThirdChainSmall.lean.

Terms: lean/GLOSSARY.md; chain 1, 2, 3 in the rows: a key file's one-time,
shared and second chain.

-/
import Johnson.KeyRun.ThirdAsk
import Johnson.G.DryKeyLit

set_option autoImplicit false

namespace Ask.KeyThirdChainFull

open Johnson.KeyRun.ThirdAsk (Pick)

/-- 32 bytes 0x5A, for the place of the public files' digest. -/
def fixed32 : ByteArray := ⟨Array.replicate 32 0x5A⟩

/-- Parts of the texts of the pieces that are expected to say no first. -/
def laid : List String := ["not just those that the test looks for"]
def admitted : String := "the plan: the first chain's public values fit together"

/-- The rows to ask behind row 0. -/
def which : List Pick :=
  [⟨1, [], none⟩, ⟨2, [], none⟩, ⟨5, [], none⟩, ⟨6, [], none⟩, ⟨8, [], none⟩, ⟨9, [], none⟩,
   ⟨10, [], none⟩, ⟨12, [], none⟩, ⟨18, [], none⟩, ⟨21, laid, none⟩, ⟨29, laid, none⟩,
   ⟨30, laid, none⟩, ⟨31, laid, none⟩, ⟨33, ["round 0: [rows ", "does not count"], some [8]⟩,
   ⟨34, laid, none⟩,
   ⟨36, ["the plan: the stages fit their codes and each other"] ++ laid, some [6, 8]⟩,
   ⟨37, [admitted], some [3, 5]⟩, ⟨38, ["round 8: [logN "], some [8]⟩,
   ⟨45, ["round 0: [name BATCH,", "is not BAT"], some [8]⟩,
   ⟨48, ["round 29: [no position", "not one for each stage"], some [8]⟩,
   ⟨50, [admitted, "has no split"], some [3, 5]⟩,
   ⟨64, ["the plan: no stage's code is longer than 2^32"], some [10]⟩,
   ⟨65, ["round 29: [logN "], some [8]⟩,
   ⟨67, ["the plan: the stages fit their codes and each other"], some [6]⟩]

end Ask.KeyThirdChainFull

set_option stderrAsMessages false

#eval Johnson.KeyRun.ThirdAsk.run (".." / "examples" / "full-size") Johnson.G.dryKeyFull
  Ask.KeyThirdChainFull.fixed32 Ask.KeyThirdChainFull.which
