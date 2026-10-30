-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/K2Caller/SeatsOfN.lean: the code switch: THE LAW's TWO LETTERS «seat» (of the
old group's members) AND «seatN» (of the new sending's members) AS PLAIN TERMS WITH CODE OFF THE
TABLE OF JOINTS' NUMBERS N, at the switch that spends «carry m» (the switch into group m + 1), at a
typed structure r.
  seatOld      the member i of r.lo: the table's list of the kept seats of segment m (N.keptOf m) at
               i's place in r.kept; (0, 0) where the list has no such place. ONLY ITS VALUES AT KEPT
               MEMBERS ARE MEANT: elsewhere it is a stand-in
  seatNew      the member i of r.l: the table's list of segment m + 1's first sending's seats
               (N.sent (m + 1) 0) at the place i; (0, 0) where the list is too short
  seatOld_at   at a kept member, by place: where r.kept has i at the place a, no number twice, and
               the table's list has a place a: (N.keptOf m)[a]? = some (seatOld N m r i)
  seatNew_at   where the table's list has the place: (N.sent (m + 1) 0)[i]? = some (seatNew N m r
               i): TableSide.lean's one_number_of's premise hN
  keptSeatsAt  KeptSeatsB.lean's test at these terms
LIMITS. Definitions and two look-ups. That the law's seats ARE these (that a member of the table's
own list at such a seat is alike to the typed member) is not said here. No soundness is claimed.

-/
import Johnson.Top.H0.K2Caller.KeptSeatsB
import Johnson.Desc.First.Borders

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2Caller
open OnBytes
open VerifiableInference.Desc (FileDescription)
open VerifiableInference.Desc.First (Numbers)
open VerifiableInference.Desc.K12.Door (Laid)

def seatOld (N : Numbers) (m : ℕ) (r : SwRow) (i : Fin r.lo.length) : ℕ × ℕ :=
  (N.keptOf m).getD (r.kept.idxOf i.val) (0, 0)

def seatNew (N : Numbers) (m : ℕ) (r : SwRow) (i : Fin r.l.length) : ℕ × ℕ :=
  (N.sent (m + 1) 0).getD i.val (0, 0)

theorem seatOld_at (N : Numbers) (m : ℕ) (r : SwRow) (i : Fin r.lo.length) (a : ℕ)
    (hn : r.kept.Nodup) (hi : r.kept[a]? = some i.val) (ha : a < (N.keptOf m).length) :
    (N.keptOf m)[a]? = some (seatOld N m r i) := by
  have hl : a < r.kept.length := (List.getElem?_eq_some_iff.1 hi).1
  have e : r.kept.idxOf i.val = a := by
    have h1 : r.kept[a] = i.val := (List.getElem?_eq_some_iff.1 hi).2
    rw [← h1]
    exact List.idxOf_getElem hn a hl
  unfold seatOld
  rw [e, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem ha]
  rfl

theorem seatNew_at (N : Numbers) (m : ℕ) (r : SwRow) (i : Fin r.l.length)
    (h : i.val < (N.sent (m + 1) 0).length) :
    (N.sent (m + 1) 0)[i.val]? = some (seatNew N m r i) := by
  unfold seatNew
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]
  rfl

/-- **The test on the plan, at the table's own lists.** -/
def keptSeatsAt {Xi : Type} (G : FileDescription Xi) (L : Laid) (seats : List (ℕ × ℕ)) (trees : ℕ)
    (N : Numbers) (m : ℕ) (r : SwRow) (olds : List ℕ) : Bool :=
  keptSeatsB G r.cs L seats trees r.lo (seatOld N m r) r.kept olds

end VerifiableInference.Desc.First.K2Caller

#print axioms VerifiableInference.Desc.First.K2Caller.seatOld_at
#print axioms VerifiableInference.Desc.First.K2Caller.seatNew_at
