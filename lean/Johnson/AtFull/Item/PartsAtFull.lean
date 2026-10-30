-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Item/PartsAtFull.lean: at the parameter file of `VerifierAndGoals.storedPublicFiles` the item's reader and
the public part's reader agree: the closed facts.

Main names.
* `linesW`: the lines of that file as the item's reader cuts them, from the written lines
  (`read_policyFile`, Johnson/AtFull/Item/ReadAtPolicy.lean). `read_zFull`: it is what the reader
  returns.
* `numbers_W`, `call_W`, `callA_W`, `callH_W`: the tests of Johnson/AtFull/Item/Tests.lean pass, by
  evaluation in Lean's kernel, at the written scan `PW` and at twins of the layouts' makers
  (`withY`, Johnson/AtFull/Public/Values.lean; `withLaid`, Johnson/AtFull/Head/PubAtFull.lean). The
  ties to the makers are theorems (`withY_eq`, `withLaid_true`), which ItemAtFull.lean calls.
  NO HASH IS EVALUATED.
* `tokens_W`, `vocab_W`: 1,024 tokens; 202,048 entries of the vocabulary.
* Negative tests. `numbers_gap_no`: the lines of `zGap`'s parameter file against `storedPublicFiles`'s scan are
  rejected (by their definitions the two files part in the policy's three numbers; at which clause
  the test rejects is not shown). `call_no`, `callA_no`, `callH_no`: the lines of another name are
  rejected. `tokens_no`: another number of tokens is rejected. The last four tests give false also
  where a maker refuses, so they have content only beside `call_W`, `callA_W`, `callH_W` and
  `tokens_W`, which show that the makers return.

Limits. The parameter file of `VerifierAndGoals.storedPublicFiles` alone, and `zGap`'s for the one negative test: terms,
which no Lean ties to files in a folder. The tests compare two readers of this library with each
other; that either is the reader of a program is not shown. No soundness is claimed.
-/
import Johnson.AtFull.Item.Tests
import Johnson.AtFull.Item.ReadAtPolicy
import Johnson.AtFull.Public.Values
import Johnson.AtFull.Head.PubAtFull
import Johnson.Goal.Files.FilesReadProof

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Item
open OnBytes OnBytes.Proof OnBytes.Model OnBytes.Model.Verify OnBytes.K
open OnBytes.Road.K4.Trial.Values (PW withY)
open _root_.AtFull.Head (withLaid)

/-- The lines of the parameter file of `VerifierAndGoals.storedPublicFiles`, as the item's reader cuts them. -/
def linesW : ParamLines := ⟨(rawAt VerifierAndGoals.storedLines).map (splitAt 0x20)⟩

/-- The same for `VerifierAndGoals.zGap`. -/
def linesGap : ParamLines := ⟨(rawAt VerifierAndGoals.Read.gapLines).map (splitAt 0x20)⟩

/-- What the item's reader returns on `storedPublicFiles`'s parameter file. -/
theorem read_zFull : ParamLines.read VerifierAndGoals.storedPublicFiles.pol = linesW := by
  rw [VerifierAndGoals.pol_zFull, read_policyFile]
  rfl

/-- The test on the numbers passes. -/
theorem numbers_W : numbersB PW linesW = true := by decide +kernel

/-- Negative test: the lines of another parameter file against this scan. -/
theorem numbers_gap_no : numbersB PW linesGap = false := by decide +kernel

/-- The text of the lines call is the layers' calls, written out again. -/
theorem call_W :
    withY (fun y => textB linesW "call" (callText "call" y.calls.toList).toUTF8) = true := by
  decide +kernel

/-- Negative test: the lines of another name. -/
theorem call_no :
    withY (fun y => textB linesW "callH" (callText "call" y.calls.toList).toUTF8) = false := by
  decide +kernel

/-- The test on the attention's call lines, at what their reader returns. -/
def callAB (name : String) : Bool :=
  match Attention.readLines PW.polCallsA with
  | .ok l => textB linesW name (String.join (l.map Attention.Line.text)).toUTF8
  | .error _ => false

/-- The text of the lines callA is the attention's lines, written out again. -/
theorem callA_W : callAB "callA" = true := by decide +kernel

/-- Negative test: the lines of another name. -/
theorem callA_no : callAB "call" = false := by decide +kernel

/-- The text of the lines callH is the head's calls, written out again. -/
theorem callH_W :
    withLaid (fun H => textB linesW "callH" (callText "callH" H.calls.toList).toUTF8) = true := by
  decide +kernel

/-- Negative test: the lines of another name. -/
theorem callH_no :
    withLaid (fun H => textB linesW "call" (callText "callH" H.calls.toList).toUTF8) = false := by
  decide +kernel

/-- The layers' layout has 1,024 tokens. -/
theorem tokens_W : withY (fun y => y.T == 1024) = true := by decide +kernel

/-- Negative test. -/
theorem tokens_no : withY (fun y => y.T == 1025) = false := by decide +kernel

/-- The scan has 202,048 entries of the vocabulary. -/
theorem vocab_W : PW.h.V = 202048 := by decide +kernel

end Johnson.AtFull.Item

#print axioms Johnson.AtFull.Item.read_zFull
#print axioms Johnson.AtFull.Item.numbers_W
#print axioms Johnson.AtFull.Item.numbers_gap_no
#print axioms Johnson.AtFull.Item.call_W
#print axioms Johnson.AtFull.Item.call_no
#print axioms Johnson.AtFull.Item.callA_W
#print axioms Johnson.AtFull.Item.callA_no
#print axioms Johnson.AtFull.Item.callH_W
#print axioms Johnson.AtFull.Item.callH_no
#print axioms Johnson.AtFull.Item.tokens_W
#print axioms Johnson.AtFull.Item.tokens_no
#print axioms Johnson.AtFull.Item.vocab_W
#print axioms Johnson.AtFull.Item.linesW
#print axioms Johnson.AtFull.Item.linesGap
#print axioms Johnson.AtFull.Item.callAB
