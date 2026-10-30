-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/DataMeets.lean: THE DATA THAT THE TABLE'S FORMS READ OFF A WITNESS AND WHAT
THE OUTPUT HEAD'S OWN LAW READS OFF IT MEET AT ONE TABLE ENTRY: first part: the reader by number
against the accessor by seat; the mask row.

The head's law reads a message BY ITS NUMBER in segment 24's group (Johnson/Desc/Sound/ReadAt.lean:
readAt). The table's forms read it BY ITS SEAT in the record's book (Johnson/Desc/Sound/FormsQ.lean:
tabQ, dataQ; Johnson/Desc/First/Batch/FormsIn.lean: seatAt). Both end in the one accessor seatTab.

Main names (namespace VerifiableInference.Desc.Kinds.Head.Law.Came).
  readAt_at_seat: where segment 24's group has just one tenant with the number n, and x is a tenant
      of the group with that number: the reader by number is the accessor at x.
  mask_of_data: THE MASK ROW: entry j, j below the plan's number of entries in use, of the data's
      mask row, at the data read through the accessor, IS the reading of compCut's mask row's entry
      j, at pl := plAt n rb (Law/PlanK6At.lean), n the number of the tenant at which the record's
      book seats the segment's first message with mask rows, rb that message's bits of mask rows in
      the record's statement.

Every letter under "there is": none.
PREMISES THAT NOBODY PAYS HERE: ho: the frame names the message with the mask rows; hx: the book
seats it at x, a seat of own; hg: x is a tenant of segment 24's group (it follows from hx where own
is a part of the group); hn: its number is n; h1: the group has one tenant with that number
(PlanK6's maskNamed at plAt). ALL FIVE ARE FACTS ON PUBLIC NUMBERS AND ON THE RECORD'S BOOK AND
FRAME. What it does not say: anything from the plan's number of entries on; anything on the cells
(the second part: Law/DataMeetsCells.lean). Nothing on soundness.

-/
import Johnson.Desc.Sound.FormsQ
import Johnson.Desc.Kinds.Law.PlanK6At

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace VerifiableInference.Desc.Kinds.Head.Law.Came

open VerifiableInference.OnPublicFiles.Flat (GE)
open VerifiableInference.Desc.First (Numbers)
open VerifiableInference.Desc.Sound (Mem MsgT namedOnce)

variable {rows cols : Nat} (cs : OnBytes.Codes) {Tok : Type} (arr : Nat → Nat → Nat)
  (msR : List Mem) (N : Numbers) (s : Nat → Cb.Pv.Tail.Size)
  (seat : ∀ k, Fin (s k).NM → Nat → Nat → Nat × Nat × Nat) (Wp : OnBytes.Model.Verify.Public)

/-- **The reader by number is the accessor at the tenant with that number.** -/
theorem readAt_at_seat {Cells : Type} (k n : Nat) (w : Wit Cells Tok MsgT)
    (h1 : namedOnce arr N k n = true) (x : Nat × Nat) (hg : x ∈ N.group k)
    (hn : arr x.1 x.2 = n) :
    Sound.readAt cs arr msR N k w n = Sound.seatTab cs arr msR w x := by
  obtain ⟨x0, hf, e⟩ := Sound.readAt_of_named cs arr msR N k n w h1
  have hx : x ∈ (N.group k).filter fun y => arr y.1 y.2 == n :=
    List.mem_filter.2 ⟨hg, by simpa using hn⟩
  rw [hf, List.mem_singleton] at hx
  rw [e, hx]

/-- **The mask row.** -/
theorem mask_of_data (own : List (Nat × Nat)) (a : K9.Part)
    (w : Wit (Fin rows → Fin cols → GE) Tok MsgT) (o n : Nat) (x : Nat × Nat)
    (ho : K9L.maskOracle a.L.check.frame = some o) (hx : K9.seatAt own a.d.book o = some x)
    (hg : x ∈ N.group 24) (hn : arr x.1 x.2 = n) (h1 : namedOnce arr N 24 n = true) (j : Nat)
    (hj : j < Wp.H.ns) :
    (Sound.dataQ own a (Sound.seatTab cs arr msR w)).mask j =
      rd ((compCut cs arr msR N s seat Wp (plAt n (a.d.st.rowBits o .mask)) w).2 j) := by
  have e2 : (compCut cs arr msR N s seat Wp (plAt n (a.d.st.rowBits o .mask)) w).2 =
      maskQ cs arr msR N 24 Wp.H.ns (plAt n (a.d.st.rowBits o .mask)) w := rfl
  rw [e2, rd_maskQ cs arr msR N 24 Wp.H.ns _ w j hj]
  show _ = Sound.readAt cs arr msR N 24 w n true (j % 2 ^ a.d.st.rowBits o .mask)
    (j / 2 ^ a.d.st.rowBits o .mask)
  rw [readAt_at_seat cs arr msR N 24 n w h1 x hg hn]
  unfold Sound.dataQ K9L.dataOf
  show (match K9L.maskOracle a.L.check.frame with
    | some o => Sound.tabQ own a.d.st a.d.book (Sound.seatTab cs arr msR w) o .mask j
    | none => 0) = _
  rw [ho]
  show Sound.tabQ own a.d.st a.d.book (Sound.seatTab cs arr msR w) o .mask j = _
  unfold Sound.tabQ
  rw [hx]
  rfl

end VerifiableInference.Desc.Kinds.Head.Law.Came

#print axioms VerifiableInference.Desc.Kinds.Head.Law.Came.readAt_at_seat
#print axioms VerifiableInference.Desc.Kinds.Head.Law.Came.mask_of_data
