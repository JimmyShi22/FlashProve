-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Law/Thread/CallsRow.lean: the kind "lookup" (K3): what the
library's table of joints holds in its row at the place of a lookup on the calls (`rowOf`, `segRow`:
Johnson/Desc/First/Borders.lean), whatever the sort of the link. One theorem; no definition; over
the library alone.

Why. At a place inside a segment the first chain's thread owes what the table's row opens, then what
it reads and leaves (`owes_at_link`, ExchangeParts.lean), and asks what the row closes, then what it
reads and leaves (`asks_at_link`, ExchangeRow.lean). At a lookup on the digits the library's
`digits_row` (Johnson/Desc/Sound/DigitsRow.lean) writes the three lists out. Here the same is done
at a lookup on the calls.

What is shown.
  `calls_row`: at a place a with a.link = some i, where the list of sorts has sub at i and a.piece
    is 2 + shift sub, the row's three lists:
      ins    constr i lookCalls (at the head's link: constr i lookCallsHeard), constr i rider
      outs   formsT "objects", worth "planes", worth "keys", worth "rider", each at i and that piece
      ctx    pin i 0, constr i small, and pinW unless sub is attention
    Binder for binder as `digits_row`, with that theorem's own proof.
The four outs are the items in which `all_attention`, `all_layers` (ExchangeAll.lean) and
`all_head` (ExchangeHeadAll.lean) end, at the piece 2 + shift sub, which at the head's link is 3. No
theorem of this file joins them.

Hypotheses that remain. hl, hs, hpc: the place's link, that link's sort, the place's piece. All
three are public.

Imported. Johnson/Desc/Sound/DigitsRow.lean, for the table's text that lies beneath it; `digits_row`
itself is not called.

Users. ExchangeSharesCallsAtHead.lean in this folder calls `calls_row`. The head of
ExchangeRiderLay.lean [not in this library] names it and does not import this file.

Limits. A fact on the table's text alone: which items a row lists, not whether one of them holds.
The library's own note on this row, in its field "whose": "the lookup on the calls (K3); small
stands in ctx": a note in plain words (Johnson/Desc/First/Borders.lean, "Limits", 1); that the items
a row lists hold is not shown here.

Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.Sound.DigitsRow

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Law.AtThr
open VerifiableInference.Desc (Place)
open VerifiableInference.Desc.First (ModelPart shift segRow)

/-- **The table's row at the place of a lookup on the calls.** -/
theorem calls_row (links : List ModelPart) (a : Place) (i : Nat) (sub : ModelPart) (hl : a.link = some i)
    (hs : links[i]? = some sub) (hpc : a.piece = 2 + shift sub) :
    (VerifiableInference.Desc.First.rowOf links a).ins =
        [.constr i (if sub == .head then .lookCallsHeard else .lookCalls), .constr i .rider] ∧
      (VerifiableInference.Desc.First.rowOf links a).outs =
        [.formsT i (2 + shift sub) "objects", .worth i (2 + shift sub) "planes",
          .worth i (2 + shift sub) "keys", .worth i (2 + shift sub) "rider"] ∧
      (VerifiableInference.Desc.First.rowOf links a).ctx =
        .pin i 0 :: .constr i .small :: (if sub == .attention then [] else [.pinW]) := by
  cases sub <;> simp [VerifiableInference.Desc.First.rowOf, segRow, shift, hl, hs, hpc]

end ProofFile.Honest.K3.Law.AtThr

#print axioms ProofFile.Honest.K3.Law.AtThr.calls_row
