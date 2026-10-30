-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Sound/SeatTabMsgs.lean: TWO READERS OF ONE MESSAGE OF THE WITNESS: BY SEAT (`seatTab`,
BordersFill.lean) AND BY A LIST's MEMBER (`msgsOf`, MsgSig.lean). Theorems, proved.
  `msgsOf_main`, `msgsOf_mask` (proved, by unfolding): the typed message of member i of a list, at
    an entry, is the witness's one accessor (`Wit.tab`) at the member's shape, the number that arr
    gives its seat, and its seat.
  `seatTab_of_mem` (proved): at a seat x: where the first member of ms that sits at x is y:
    `seatTab` is
    `memTab` of y.
  `seatTab_main`, `seatTab_mask` (proved): **so the two readers are one at every entry of member
    i**, where the member y of ms that `seatTab` finds at i's seat has i's SHAPE. The radius is read
    by neither.
Limits. hy (which member ms.find? gives at the seat) and hsh (its shape) are premises: facts on the
table's list of members. Where no member of ms sits at the seat `seatTab` is the zero message, in
silence: nothing is said there. Nothing on soundness.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Sound.BordersFill

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Sound
open OnBytes.Maker Cb Johnson.Pack OnBytes.Slice

section
variable (cs : OnBytes.Codes) {Cells Tok : Type} (arr : ℕ → ℕ → ℕ)
  (l : List (OnBytes.OracleShape × ℕ)) (seat : Fin l.length → ℕ × ℕ)

theorem msgsOf_main (w : Wit Cells Tok MsgT) (i : Fin l.length) (q) :
    msgsOf cs l seat arr w i (.inl q) =
      w.tab cs (l.get i).1 (arr (seat i).1 (seat i).2) (seat i).1 (seat i).2 false q.1.val
        q.2.val :=
  rfl

theorem msgsOf_mask (w : Wit Cells Tok MsgT) (i : Fin l.length) (q) :
    msgsOf cs l seat arr w i (.inr q) =
      w.tab cs (l.get i).1 (arr (seat i).1 (seat i).2) (seat i).1 (seat i).2 true q.1.val q.2.val :=
  rfl

theorem seatTab_of_mem (ms : List Mem) (w : Wit Cells Tok MsgT) (x : ℕ × ℕ) (y : Mem)
    (hy : (ms.find? fun y => decide (seatOf y = x)) = some y) :
    seatTab cs arr ms w x = memTab cs arr w y := by
  unfold seatTab
  rw [hy]

theorem seatTab_tab (ms : List Mem) (w : Wit Cells Tok MsgT) (i : Fin l.length) (y : Mem)
    (hy : (ms.find? fun y => decide (seatOf y = seat i)) = some y)
    (hsh : (y.1.l.get y.2).1 = (l.get i).1) :
    seatTab cs arr ms w (seat i) =
      w.tab cs (l.get i).1 (arr (seat i).1 (seat i).2) (seat i).1 (seat i).2 := by
  have hs : seatOf y = seat i := by
    have := List.find?_some hy
    exact of_decide_eq_true this
  rw [seatTab_of_mem cs arr ms w (seat i) y hy]
  show w.tab cs (y.1.l.get y.2).1 (arr (seatOf y).1 (seatOf y).2) (seatOf y).1 (seatOf y).2 = _
  rw [hsh, hs]

/-- **The two readers are one at a main entry.** -/
theorem seatTab_main (ms : List Mem) (w : Wit Cells Tok MsgT) (i : Fin l.length) (y : Mem)
    (hy : (ms.find? fun y => decide (seatOf y = seat i)) = some y)
    (hsh : (y.1.l.get y.2).1 = (l.get i).1) (q) :
    msgsOf cs l seat arr w i (.inl q) = seatTab cs arr ms w (seat i) false q.1.val q.2.val := by
  rw [seatTab_tab cs arr l seat ms w i y hy hsh]
  rfl

/-- **The two readers are one at a mask entry.** -/
theorem seatTab_mask (ms : List Mem) (w : Wit Cells Tok MsgT) (i : Fin l.length) (y : Mem)
    (hy : (ms.find? fun y => decide (seatOf y = seat i)) = some y)
    (hsh : (y.1.l.get y.2).1 = (l.get i).1) (q) :
    msgsOf cs l seat arr w i (.inr q) = seatTab cs arr ms w (seat i) true q.1.val q.2.val := by
  rw [seatTab_tab cs arr l seat ms w i y hy hsh]
  rfl

end

end VerifiableInference.Desc.Sound

#print axioms VerifiableInference.Desc.Sound.seatTab_tab
#print axioms VerifiableInference.Desc.Sound.seatTab_main
#print axioms VerifiableInference.Desc.Sound.seatTab_mask
