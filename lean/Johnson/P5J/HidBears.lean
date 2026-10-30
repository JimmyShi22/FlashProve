-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P5J/HidBears.lean: THE COMPOSED MEANING'S LETTER H (`hidAtSeat`, MeansQ.lean) DOES NOT READ
    THE PADS: so an item "constr j p" rides over every sub-protocol whose row of the
table lays pads alone (a code switch's; a closing's).
  `PlacesOffPad cs arr ms N s seat`: every place that a segment's seats name, within its sizes, is
      off the pad of the copy that the
    segment's own group holds: `OffPad` (Johnson/Desc/Sound/ReadAt.lean) at ALL entries of the
        lists, not at the 24 seams alone
    (`PadsFree`, WordsAtQ.lean). A condition on public letters alone.
  `symAt_readAt`: under it, `SeatsNamed` and `GroupsSeated`, each segment's symbols, as the segment
      reads them, are the symbols of the witness's shared components.
  **`hid_bears`**: under the same three, two witnesses with the same shared components (msg) and the
      same token have the same hidden values and the same
    "the symbols are a packing of small integers" , segment by segment: whatever their pads, cells
        and other parts are.
Limits. PlacesOffPad is asked, not shown; no test with code for it stands here. A rule over letters:
    no member.
Limits: that file's. A joining of rules: no member is known. Nothing on hiding.

Terms: lean/GLOSSARY.md.

-/
import Johnson.P5J.MeansQ

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P5J

open Meaning
open Inst.Model
open OnBytes OnBytes.Road
open VerifiableInference.OnPublicFiles.Flat (GE)
open VerifiableInference.Desc (Strs Wit)
open VerifiableInference.Desc.First (Numbers)
open VerifiableInference.Desc.Sound (readAt readAt_offPad OffPad SeatsNamed GroupsSeated MsgT Mem)

section
variable {Cells Tok : Type} (cs : OnBytes.Codes) (arr : ℕ → ℕ → ℕ) (ms : List Mem) (N : Numbers)
  (s : ℕ → Cb.Pv.Tail.Size) (seat : ∀ k, Fin (s k).NM → ℕ → ℕ → ℕ × ℕ × ℕ)

/-- **Every place that a segment's seats name, within its sizes, is off the pad of the segment's own
    copy.** -/
def PlacesOffPad : Prop :=
  ∀ k (μ : Fin (s k).NM) (r c : ℕ), r < Alg.symRows ((s k).m μ) → c < (s k).k μ →
    OffPad cs arr ms N k (seat k μ r c).1 (seat k μ r c).2.1 (seat k μ r c).2.2

variable {cs arr ms N s seat}

/-- Each segment's symbols, as it reads them, are the symbols of the witness's shared components. -/
theorem symAt_readAt (hN : SeatsNamed arr N s seat) (hG : GroupsSeated ms N)
    (hO : PlacesOffPad cs arr ms N s seat) (w : Wit Cells Tok MsgT) (k : ℕ) :
    symAt (s k) (seat k) (readAt cs arr ms N k w) = symAt (s k) (seat k) w.msg := by
  funext μ r c
  exact readAt_offPad cs arr ms N k _ _ _ w (hN k μ r.val c.val r.isLt c.isLt) hG
    (hO k μ r.val c.val r.isLt c.isLt)

/-- **H DOES NOT READ THE PADS.** -/
theorem hid_bears (X : Model.Verify.Public) {P : Type} {rows cols : ℕ} (tokV : Tok → Fin ppref.V)
    (req : P × TS → TReq) (dec : P × TS → Strs → Option (Fin rows → Fin cols → GE))
    (hN : SeatsNamed arr N s seat) (hG : GroupsSeated ms N)
    (hO : PlacesOffPad cs arr ms N s seat) (w w' : Wit Cells Tok MsgT) (hm : w'.msg = w.msg)
    (ht : w'.tok = w.tok) :
    (hidAtSeat X cs arr ms N s seat tokV req dec hN hG).hid w' =
        (hidAtSeat X cs arr ms N s seat tokV req dec hN hG).hid w ∧
      ∀ j, (hidAtSeat X cs arr ms N s seat tokV req dec hN hG).base j w' ↔
        (hidAtSeat X cs arr ms N s seat tokV req dec hN hG).base j w := by
  have e : ∀ k, symAt (s k) (seat k) (readAt cs arr ms N k w') =
      symAt (s k) (seat k) (readAt cs arr ms N k w) := fun k => by
    rw [symAt_readAt hN hG hO w' k, symAt_readAt hN hG hO w k, hm]
  refine ⟨?_, fun j => ?_⟩
  · show hidOf X (tokV w'.tok) (ownOf s fun k => symAt (s k) (seat k) (readAt cs arr ms N k w')) =
      hidOf X (tokV w.tok) (ownOf s fun k => symAt (s k) (seat k) (readAt cs arr ms N k w))
    rw [ht, funext e]
  · show Cb.Pv.Tail.Base (symAt (s j) (seat j) (readAt cs arr ms N j w')) ↔
      Cb.Pv.Tail.Base (symAt (s j) (seat j) (readAt cs arr ms N j w))
    rw [e j]

end

end P5J

#print axioms P5J.symAt_readAt
#print axioms P5J.hid_bears
