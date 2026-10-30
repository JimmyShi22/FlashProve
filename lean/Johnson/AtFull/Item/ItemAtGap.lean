-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Item/ItemAtGap.lean: at `VerifierAndGoals.zGap`, for every request of the right length, the
item "request" is made and its comparison with the public part accepts.

`VerifierAndGoals.zGap` is `VerifierAndGoals.storedPublicFiles` with the acceptance policy (25856, 512, 1). This file is
Johnson/AtFull/Item/ItemAtFull.lean once more, at that parameter file's lines and at the scan with
that policy.

Main names.
* `numbers_gap`: the test on the numbers (Johnson/AtFull/Item/Tests.lean) passes at `linesGap` and
  the scan with that policy, by evaluation in Lean's kernel. `texts_gap`: the call lines of the two
  parameter files are the same. Negative test: `numbers_full_no`: the lines of `storedPublicFiles`'s parameter
  file against this scan are rejected.
* `item_zGap`: at every string req of 4 (X.T + 2) bytes, `Fmt.requestItem` at the format's second
  hash function returns an item, and `statementHeld X` accepts it, where X is what `publicOfO` returns at
  `zGap`.
* `facts_zGap`: X.P is the scan `PW` with the policy's three numbers replaced, `Parts` holds, and X
  has 1,024 tokens.

How. What `publicOfO` returns at `zGap` is the value at `storedPublicFiles` with the policy's three numbers
replaced (`LPFPol.gap_of_full`, Johnson/LPFPol/PublicInScope.lean): its three digests and its
layouts are those at `storedPublicFiles`.

Limits. Those of Johnson/AtFull/Item/ItemAtFull.lean, at `zGap`: hsz and hX are premises; the
three files of `VerifierAndGoals.zGap` alone, terms that no Lean ties to files in a folder; the earlier hash;
two of the seven steps of the tests on an instance, and the caller has to show that they stand at
`ProofFile.holdBy`'s own arguments; other places where a test on the public files can make the verifier
reject everything are known; that the verifier accepts any proof is not shown. No theorem here
states the vocabulary's size at `zGap`, or that no item is made at another length. Nothing on
soundness, on binding or on hiding.
-/
import Johnson.AtFull.Item.ItemAtFull
import Johnson.LPFPol.PublicInScope
import Johnson.Goal.Files.FilesReadChecks
import Johnson.AtFull.Public.AtX0All
import Johnson.Desc.Ok.PlanWritten.PublicAtLaws

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Item
open OnBytes OnBytes.Proof OnBytes.Model OnBytes.Model.Verify OnBytes.K
open VerifiableInference.PlanWritten
open OnBytes.Road.K4.Trial.Values (PW)

/-- What the item's reader returns on `zGap`'s parameter file. -/
theorem read_zGap : ParamLines.read VerifierAndGoals.zGap.pol = linesGap := by
  rw [VerifierAndGoals.pol_zGap, read_policyFile]
  rfl

/-- The test on the numbers passes. -/
theorem numbers_gap : numbersB (PW.withPol 25856 512 1) linesGap = true := by decide +kernel

/-- Negative test: the lines of another parameter file against this scan. -/
theorem numbers_full_no : numbersB (PW.withPol 25856 512 1) linesW = false := by decide +kernel

/-- The item's digest of the lines of one name hangs on their text alone. -/
theorem calls_of_same_text {L L' : ParamLines} {name : String} {ifNone : Option String}
    (h : L'.text name = L.text name) : L'.calls name ifNone = L.calls name ifNone := by
  unfold ParamLines.calls
  rw [h]

/-- The call lines of the two parameter files are the same. -/
theorem texts_gap : linesGap.text "call" = linesW.text "call" ∧
    linesGap.text "callA" = linesW.text "callA" ∧ linesGap.text "callH" = linesW.text "callH" := by
  decide +kernel

/-- What `publicOfO` returns at `VerifierAndGoals.zGap` has the scan of `VerifierAndGoals.storedPublicFiles` with the policy
replaced; the two readers agree there; it has 1,024 tokens. -/
theorem facts_zGap (hsz : VerifierAndGoals.storedPublicFiles.lay.size = 224975) {X : Public}
    (hX : publicOfO OnBytes.secondHashFunction VerifierAndGoals.zGap.pol VerifierAndGoals.zGap.KL (some VerifierAndGoals.zGap.lay) = .ok X) :
    X.P = PW.withPol 25856 512 1 ∧
      Parts X (ParamLines.read VerifierAndGoals.zGap.pol) (4 * (2 ^ 10 + 2)) ∧ X.T = 1024 := by
  obtain ⟨X₀, hX₀, -⟩ := Johnson.AtFull.Public.publicOfO_zFull_all hsz
  have hG := LPFPol.gap_of_full hX₀
  rw [← VerifierAndGoals.lay_zGap] at hG
  obtain rfl := Except.ok.inj (hG.symm.trans hX)
  have hP₀ := parts_zFull hsz hX₀
  rw [read_zFull] at hP₀
  have eP : X₀.P = PW :=
    Except.ok.inj ((publicOfO_scan hX₀).symm.trans OnBytes.Road.K4.Trial.Values.scan_zFull)
  have eP' : (X₀.withPol 25856 512 1).P = PW.withPol 25856 512 1 := by
    show X₀.P.withPol 25856 512 1 = _
    rw [eP]
  refine ⟨eP', ?_, ?_⟩
  · rw [read_zGap]
    exact parts_of_tests (by rw [eP']; exact numbers_gap)
      ((calls_of_same_text texts_gap.1).trans hP₀.call)
      ((calls_of_same_text texts_gap.2.1).trans hP₀.callA)
      ((calls_of_same_text texts_gap.2.2).trans hP₀.callH)
  · show X₀.T = 1024
    exact tokens_zFull hsz hX₀

/-- **AT `VerifierAndGoals.zGap`, FOR EVERY REQUEST OF THE RIGHT LENGTH, THE ITEM IS MADE AND THE COMPARISON
ACCEPTS.** -/
theorem item_zGap (hsz : VerifierAndGoals.storedPublicFiles.lay.size = 224975) {X : Public}
    (hX : publicOfO OnBytes.secondHashFunction VerifierAndGoals.zGap.pol VerifierAndGoals.zGap.KL (some VerifierAndGoals.zGap.lay) = .ok X) :
    ∀ req : ByteArray, req.size = 4 * (X.T + 2) →
      ∃ it, Fmt.requestItem OnBytes.secondHashFunction VerifierAndGoals.zGap.pol VerifierAndGoals.zGap.KL req = some it ∧
        statementHeld X it = .ok () := by
  obtain ⟨-, hP, hT⟩ := facts_zGap hsz hX
  intro req hreq
  rw [hT] at hreq
  obtain ⟨s, hs, -⟩ := olderTK_returns (w := VerifierAndGoals.zGap.KL) (by
    rw [VerifierAndGoals.Read.kl_zGap, Johnson.Unfolds.size_KL]
    decide)
  obtain ⟨r, hr, hr32⟩ := olderTK_returns (w := req) (by
    rw [hreq]
    decide)
  obtain ⟨it, h1, h2⟩ := held_of_parts hP hs hr32
  refine ⟨it, ?_, h2⟩
  rw [← OnBytes.Tie.Decl.RequestItemLaw.requestItem_eq, requestItem_eq_itemWith, hr, hreq]
  exact h1

end Johnson.AtFull.Item

#print axioms Johnson.AtFull.Item.read_zGap
#print axioms Johnson.AtFull.Item.numbers_gap
#print axioms Johnson.AtFull.Item.numbers_full_no
#print axioms Johnson.AtFull.Item.calls_of_same_text
#print axioms Johnson.AtFull.Item.texts_gap
#print axioms Johnson.AtFull.Item.facts_zGap
#print axioms Johnson.AtFull.Item.item_zGap
