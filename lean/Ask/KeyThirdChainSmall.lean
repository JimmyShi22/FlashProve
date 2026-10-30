-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Ask/KeyThirdChainSmall.lean: an asking file: `third` (Johnson/KeyRun/Third.lean), a check of the
third of a key file's three hash chains as a plain function with code, is asked at the small stored
example's key file and at 99 changed copies of its arguments.

No soundness: a test. A yes from this run is not a verification of the key file.

Reads: examples/accepted-proof/config/policy.txt, examples/accepted-proof/config/KL.bin,
examples/accepted-proof/config/layout.txt, examples/accepted-proof/ivk/key.bin. Every change is made
in memory. Nothing is written to disk.

Command: from lean/, behind a build:
`LEAN_ABORT_ON_PANIC=1 lake env lean -j1 --tstack=1000000 Ask/KeyThirdChainSmall.lean`. Without the
variable a panic in a row that expects no would count as that no. The faster way of Ask/README.md
serves here too.

Takes: AS MEASURED at a form of this file with 63 of the 100 rows, from disk, on one
machine, in Lean's interpreter alone, with a stack of 1,000,000 KiB: 29 minutes and a peak of 4.1
GiB. An evaluation that reaches the last stage took about 16 s, and a row makes up to three; a row
that is refused before the proximity test took about 5 s. This form, with all its rows, is not
what was measured.

Its print means: Lean's evaluator computed `third` at 100 inputs and printed each answer and whether
it is the answer that this file expects. The lines go to the error stream. The lines before the
rows: what the check is; which example is read; the files' sizes; that the key chains at which
`third` is asked hold 32 fixed bytes in the place of the public files' digest, and that these are
not that digest; that the entries of the lists under which the key file is read are the plan's
rounds; that the reader has read the whole file; in how many rounds of the first chain a value is
read; the names of the ten tests on the plan; what a row's line says. Row 0: at the plan and the
three views as they were read `third` says yes. Rows 6 and 8: it still says yes after a change of a
value of the first chain that it does not use: KNOWN LIMITS (the head of Johnson/KeyRun/Third.lean):
to catch these is the work of a check of the first chain, which this library does not have in this
form. Every other row: after the change that its line names it says no. Beneath a row stands the
first piece of the check that says no (Johnson/KeyRun/ThirdPieces.lean: one more evaluation) and
whether its text holds the part that this file expects; at rows 0, 6 and 8 none. Rows 1 to 31, 34,
35 and 90 to 98 change a view. Rows 32, 33, 36 to 89 and 99 change the plan. There further lines
name the tests on the plan (`thirdPublic`) that say no, held against the numbers that this file
expects, and give the answer of `dec₃`, in the print "the test on the views", by itself. AT ROWS 38,
40 TO 44, 52 TO 61, 63 TO 85, 87 AND 88 `dec₃` BY ITSELF SAYS YES: there the tests on the plan alone
stand between the changed plan and a yes. One test alone says no, and `dec₃` says yes, at rows 55
and 68 (the first test), 56 and 69 to 77 (the second), 57 (the third), 58 and 78 (the fourth), 53
and 59 (the fifth), 67 (the sixth), 54 and 60 (the seventh), 38, 40 to 42, 65, 66 and 79 to 85 (the
eighth), 52, 61, 87 and 88 (the ninth), 63 and 64 (the tenth). Rows 18 and 23 change the same word:
at this size the third stage's tree is the last. The last line of a row is the time of all its
evaluations. The last line of all says how many rows were asked: 100 of 100. If row 0 is not as
expected the other rows are not asked. If a line is not as expected the command ends with an error
and a status other than 0.

It does not mean: A THEOREM: an evaluation leaves no declaration; it is trusted that the evaluator
computes the terms as Lean's kernel would, and that the bytes on disk are the named files'; with
libvob.so also Lean's compiler to C, the C compiler, the linking, and that libvob.so was made from
these sources. Nor that the key file is accepted: `third` checks the third chain alone. Nor anything
on soundness. Nor that hashes, proof of work or openings are tried: every change is made behind the
reader. Nor that each changed value has a test of its own: most changes add 1 to one machine word,
or change one number, name or list; most rows that change a view end at one and the same equation,
the last stage's linear check. Nor that the rows on the plan try all that the tests on the plan ask.
THE LISTS UNDER WHICH THE KEY FILE IS READ ARE WRITTEN VALUES (`dryKeySmall`,
Johnson/G/DryKeyLit.lean), which a program wrote from a print of dry runs of blocks of the text of
verify-on-bytes (at which files: that file's head; here their entries alone are held against this
example's plan). So no dry run is made in this file, but each round's kind, items, openings and
stored tables come from one: they are not a function of the plan. The reader in front of `third` is
that text's own; only its top routine is written anew, so that it takes the lists
(Johnson/KeyRun/ThirdAsk.lean). One stored example, on made-up weights. All that the heads of
Johnson/KeyRun/Third.lean and ThirdAsk.lean do not claim.

For which format: the one that the library's Fmt/ describes in the tree in which this file lies. At
other public parameter files the run ends with one of the errors NO PLAN CAN BE MADE OF THE PUBLIC
PARAMETER FILES, THE LISTS OF ROUNDS ARE NOT THOSE OF THESE PUBLIC PARAMETER FILES, or THE READER
REFUSES THE KEY FILE.

Terms: lean/GLOSSARY.md; chain 1, 2, 3 in the rows: a key file's one-time,
shared and second chain.

-/
import Johnson.KeyRun.ThirdAsk
import Johnson.G.DryKeyLit

set_option autoImplicit false

namespace Ask.KeyThirdChainSmall

open Johnson.KeyRun.ThirdAsk (Pick)

/-- 32 bytes 0x5A, for the place of the public files' digest. -/
def fixed32 : ByteArray := ⟨Array.replicate 32 0x5A⟩

/-- Parts of the texts of the pieces that are expected to say no first. -/
def lin : List String := ["BASE's linear check"]
def sym : List String := ["BASE's symbols at the drawn positions"]
def laid : List String := ["not just those that the test looks for"]
def copies : String := "the plan: the first two chains hold the same codes and the same shape"
def settings : String := "the plan: the three plans have the same settings"
def admitted : String := "the plan: the first chain's public values fit together"
def powers : String := "the plan: every code's message length is a power of two"
def fits : String := "the plan: each member fits the group, and the first stage's codes are"
def stages : String := "the plan: the stages fit their codes and each other"
def builtIn : String := "the plan: one answer to a sample in all three plans"
def answers : String := "the plan: SEND answer stands behind each SEND seed"
def long : String := "the plan: no stage's code is longer than 2^32"

/-- The rows that change a view, and row 0. -/
def views : List Pick :=
  [⟨0, ["none"], none⟩, ⟨1, lin, none⟩, ⟨2, lin, none⟩, ⟨3, lin, none⟩, ⟨4, lin, none⟩,
   ⟨5, lin, none⟩, ⟨6, ["none"], none⟩, ⟨7, lin, none⟩, ⟨8, ["none"], none⟩, ⟨9, lin, none⟩,
   ⟨10, lin, none⟩, ⟨11, lin, none⟩, ⟨12, lin, none⟩, ⟨13, lin, none⟩, ⟨14, lin, none⟩,
   ⟨15, lin, none⟩, ⟨16, lin, none⟩, ⟨17, lin, none⟩, ⟨18, sym, none⟩, ⟨19, lin, none⟩,
   ⟨20, lin, none⟩, ⟨21, laid, none⟩, ⟨22, lin, none⟩, ⟨23, sym, none⟩, ⟨24, lin, none⟩,
   ⟨25, lin, none⟩, ⟨26, lin, none⟩, ⟨27, lin, none⟩, ⟨28, lin, none⟩, ⟨29, laid, none⟩,
   ⟨30, laid, none⟩, ⟨31, laid, none⟩, ⟨34, laid, none⟩, ⟨35, ["no round is left"], none⟩,
   ⟨90, ["does not draw one element"], none⟩, ⟨91, ["W's sample rows cannot be made"], none⟩,
   ⟨92, ["W's sample rows cannot be made"], none⟩,
   ⟨93, ["stage 1: FOLD epsilon sends one element"], none⟩,
   ⟨94, ["stage 1: the 3 FOLD rounds have the right counts"], none⟩,
   ⟨95, ["stage 1: SEND seed draws"], none⟩, ⟨96, ["stage 1: CS sends one element"], none⟩,
   ⟨97, ["BASE lambda sends one element"], none⟩, ⟨98, ["BASE has the right counts"], none⟩]

/-- The rows that change the plan. Where `dec₃` by itself is expected to say yes, its pieces are
asked for at three rows alone. -/
def plans : List Pick :=
  [⟨32, [copies, "BASE's linear check"], some [1]⟩,
   ⟨33, ["round 0: [rows ", "does not count"], some [8]⟩, ⟨36, [stages] ++ laid, some [6, 8]⟩,
   ⟨37, [admitted, "W's sample rows cannot be made"], some [3, 5]⟩,
   ⟨38, ["round 6: [logN ", "none"], some [8]⟩,
   ⟨39, [fits, "BASE's linear check"], some [5, 6]⟩, ⟨40, ["round 2: [name FOLD,"], some [8]⟩,
   ⟨41, ["round 5: [drawNZ "], some [8]⟩, ⟨42, ["round 6: [rows "], some [8]⟩,
   ⟨43, [builtIn], some [7, 8]⟩, ⟨44, [builtIn], some [7, 8]⟩,
   ⟨45, ["round 0: [name BATCH,", "is not BAT"], some [8]⟩,
   ⟨46, ["is not LIN point", "is not LIN point"], some []⟩,
   ⟨47, [answers, "has no round SEND seed"], some [9]⟩,
   ⟨48, ["round 15: [no position", "not one for each stage"], some [8]⟩,
   ⟨49, ["rounds, the test ", "are not the layout's"], some [8]⟩,
   ⟨50, [admitted, "has no split"], some [3, 5]⟩, ⟨51, [admitted, "over the base field"], some [3]⟩,
   ⟨52, [answers], some [9]⟩, ⟨53, [fits, "none"], some [5]⟩, ⟨54, [builtIn], some [7]⟩,
   ⟨55, [copies], some [1]⟩, ⟨56, [settings], some [2]⟩, ⟨57, [admitted], some [3]⟩,
   ⟨58, [powers], some [4]⟩, ⟨59, [fits], some [5]⟩, ⟨60, [builtIn], some [7]⟩,
   ⟨61, [answers], some [9]⟩, ⟨62, [builtIn] ++ laid, some [7, 8]⟩, ⟨63, [long], some [10]⟩,
   ⟨64, [long], some [10]⟩, ⟨65, ["round 15: [logN "], some [8]⟩,
   ⟨66, ["round 13: [logN "], some [8]⟩, ⟨67, [stages, "none"], some [6]⟩,
   ⟨68, [copies], some [1]⟩, ⟨69, [settings], some [2]⟩, ⟨70, [settings], some [2]⟩,
   ⟨71, [settings], some [2]⟩, ⟨72, [settings], some [2]⟩, ⟨73, [settings], some [2]⟩,
   ⟨74, [settings], some [2]⟩, ⟨75, [settings], some [2]⟩, ⟨76, [settings], some [2]⟩,
   ⟨77, [settings], some [2]⟩, ⟨78, [powers], some [4]⟩, ⟨79, ["round 2: [count "], some [8]⟩,
   ⟨80, ["round 2: [msg "], some [8]⟩, ⟨81, ["round 2: [roots "], some [8]⟩,
   ⟨82, ["round 2: [answers "], some [8]⟩, ⟨83, ["round 2: [drawE "], some [8]⟩,
   ⟨84, ["round 2: [trits "], some [8]⟩, ⟨85, ["round 2: [logN "], some [8]⟩,
   ⟨86, ["round 2: [poss ", "not one for each stage"], some [8]⟩, ⟨87, [answers], some [9]⟩,
   ⟨88, [answers], some [9]⟩,
   ⟨89, ["no claim is made of the first view", "no claim is made of the first view"], some []⟩,
   ⟨99, ["no claim is made of the first view", "no claim is made of the first view"], some []⟩]

end Ask.KeyThirdChainSmall

set_option stderrAsMessages false

#eval Johnson.KeyRun.ThirdAsk.run (".." / "examples" / "accepted-proof") Johnson.G.dryKeySmall
  Ask.KeyThirdChainSmall.fixed32 (Ask.KeyThirdChainSmall.views ++ Ask.KeyThirdChainSmall.plans)
