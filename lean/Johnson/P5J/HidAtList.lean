-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P5J/HidAtList.lean: THE TOWER'S LETTER H WITH arr AND num MADE OFF ONE PLANNER'S LIST, so
    that num IS PINNED TO arr BY THE MAKE.
  `hidAtList X cs ps ms N layout req dec hL hN hG` := `hidAtPlan` (HidAtPlan.lean) at arr :=
      `P5T.arrOf ps` and
    num := `P5T.numOfPlan ps` (Johnson/P5T/PlanSeats.lean, NumOfPlan.lean).

  **`num_is_arr`**: at every entry p of ps that is the first at its tree and tenant, and that holds
      link l's own
    message number k (at the original or at a kept copy: keyOf p = (0, l, k)): arrOf ps p.j p.t =
        numOfPlan ps l k:
    `arrOf_is_num`, restated at p's own seat. THIS is what "num is the number under which
        arr books
    that message's seats" means; `SeatsNamed` does not say it.
Limits. That keyOf's (0, l, k) is the layout's own numbering of a link's messages (ReqArray.message)
    is by reading
alone. ps is a letter: meant: all three chains' list (planSeatsAll). The full size alone.
Limits: that file's. A joining of rules: no member is known. Nothing on hiding.

Terms: lean/GLOSSARY.md.

-/
import Johnson.P5J.HidAtPlan
import Johnson.P5T.NumOfPlan

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P5J

open Meaning
open OnBytes OnBytes.Road
open OnBytes.Params (ReqLayout)
open VerifiableInference.OnPublicFiles.Flat (GE)
open VerifiableInference.Desc (Strs Wit)
open VerifiableInference.Desc.First (Numbers)
open VerifiableInference.Desc.Sound (SeatsNamed GroupsSeated MsgT Mem)

/-- **H WITH arr AND num OFF ONE LIST.** -/
noncomputable def hidAtList (X : Model.Verify.Public) {P Cells : Type} {rows cols : ℕ}
    (cs : OnBytes.Codes) (ps : List P5T.PSeat) (ms : List Mem) (N : Numbers) (layout : ReqLayout)
    (req : P × TS → TReq) (dec : P × TS → Strs → Option (Fin rows → Fin cols → GE))
    (hL : laidThere X (sizesOf X) layout = true)
    (hN : SeatsNamed (P5T.arrOf ps) N (sizesOf X)
      (seatsOf X (sizesOf X) layout (P5T.numOfPlan ps)))
    (hG : GroupsSeated ms N) : HidAt X P (Wit Cells ℕ MsgT) rows cols :=
  hidAtPlan X cs (P5T.arrOf ps) ms N layout (P5T.numOfPlan ps) req dec hL hN hG

/-- **num IS THE NUMBER UNDER WHICH arr BOOKS THE MESSAGE's SEATS, BY THE MAKE.** -/
theorem num_is_arr (ps : List P5T.PSeat) (p : P5T.PSeat)
    (h : ps.find? (fun q => q.j == p.j && q.t == p.t) = some p) (l k : ℕ)
    (hk : P5T.keyOf p = (0, l, k)) : P5T.arrOf ps p.j p.t = P5T.numOfPlan ps l k :=
  P5T.arrOf_is_num ps p.j p.t l k p h hk

end P5J

#print axioms P5J.num_is_arr
