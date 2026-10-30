-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/K2Caller/MembersAtK2.lean: the code switch (the kind K2): ONE TEST WITH CODE ON
PUBLIC LISTS: THE TABLE's MEMBERS AT THE TENANTS OF A SWITCH ARE THE MEMBERS OF THE SWITCH's TWO
TYPED LISTS, BY PLACE. Definitions, and theorems with their proofs, over
Johnson/Desc/Sound/MembersAtB.lean.

r: the numbers of a place of the code switch (`SwRow`, Row.lean): r.lo: the typed list in front, of
which r.kept names the kept members; r.l: the typed list of the new sending. L: the plain lists of
which the table's members are made (`msOf L`). kq: the tenants that the segment in front keeps
(meant: `N.keptOf m`). nq: the tenants of the switch's first sending (meant: `N.sent (m + 1) 0`).

Main names:
  `keptEntries r`: the entries (shape, radius) of r's kept members, in the order of r.kept.
  `SeatsKept r kq seat`: what is asked of the seats of the typed list in front: the a-th kept member
    sits at kq[a]. Of the members that are not kept nothing is asked.
  `seatKept r kq`, `seatKept_fits`: the least such seats: EVERY MEMBER THAT IS NOT KEPT IS SENT TO
    (0, 0): whoever also needs the other members' true seats takes the next.
  `seatsKeptB r kq gq`, `seatsKept_of_B`: a test with code: the seats `seatsByPlace gq` (member i of
    r.lo sits at gq[i]; meant: gq := `N.group m`) are such seats.
  `membersK2B L kq nq r`: THE TEST: `sitsB` at (kq, the kept entries) and at (nq, r.l), `onceB` at
    kq, and: nq is as long as r.l.
  `kept_of_B`: where it passes: at every tenant of kq a member of the table sits; every such member
    is one of those whose pads the row lays, and is `Alike` to a kept member of r.lo, at any seats
    with `SeatsKept`; and the members whose pads the row lays have different seats.
  `new_of_B`: member by member: every member of the table that sits at the seat of the member i of
    r.l (nq by place) is `Alike` to that member; these seats are just the tenants nq; at each a
    member of the table sits.
  `kept_at_table`: `kept_of_B` with the picked members written as the table's own `minePadAt`.
Limits. ONE-SIDED: nothing says that every kept member has a tenant: kq may be shorter than r.kept,
and at an empty list of tenants the test passes. The test's value at a real plan is not shown here.
That L, kq and nq are the plan's is said by nothing here. Nothing on soundness. On hiding nothing.

-/
import Johnson.Desc.Sound.MembersAtB
import Johnson.Top.H0.K2Caller.Row

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2Caller
open OnBytes (OracleShape)
open VerifiableInference.Desc (MemberLists Place)
open VerifiableInference.Desc.Sound (Mem msOf SitsAt Alike seatOf sitsB onceB sits_of_B each_of_B
  nodup_of_B mem_filter_of_sits seatsByPlace minePadAt minePadAt_K2)
open VerifiableInference.Desc.First (ModelPart Numbers rowOf)

/-- The entries of the kept members, in the order of r.kept. -/
def keptEntries (r : SwRow) : List (OracleShape × ℕ) := r.kept.map fun i => r.lo.getD i default

/-- What is asked of the seats of the typed list in front: the a-th kept member sits at kq[a]. -/
def SeatsKept (r : SwRow) (kq : List (ℕ × ℕ)) (seat : Fin r.lo.length → ℕ × ℕ) : Prop :=
  ∀ (a : ℕ) (i : Fin r.lo.length), r.kept[a]? = some i.val → ∀ q, kq[a]? = some q → seat i = q

/-- The least such seats. A member that is not kept is sent to (0, 0). -/
def seatKept (r : SwRow) (kq : List (ℕ × ℕ)) : Fin r.lo.length → ℕ × ℕ :=
  fun i => kq.getD (r.kept.idxOf i.val) (0, 0)

theorem seatKept_fits {r : SwRow} (H : r.OK) (kq : List (ℕ × ℕ)) :
    SeatsKept r kq (seatKept r kq) := by
  intro a i hi q hq
  obtain ⟨ha', e'⟩ := List.getElem?_eq_some_iff.1 hi
  have hx' : r.kept.idxOf i.val = a := by
    rw [← e']
    exact List.idxOf_getElem H.nodup a ha'
  show kq.getD (r.kept.idxOf i.val) (0, 0) = q
  rw [hx', List.getD_eq_getElem?_getD, hq]
  rfl

/-- A test with code: at each place a of kq: the kept member number a of r sits, by gq, at kq[a]. -/
def seatsKeptB (r : SwRow) (kq gq : List (ℕ × ℕ)) : Bool :=
  (List.range kq.length).all fun a =>
    match r.kept[a]? with
    | some i => gq[i]? == kq[a]?
    | none => true

theorem seatsKept_of_B {r : SwRow} {kq gq : List (ℕ × ℕ)} (h : seatsKeptB r kq gq = true) :
    SeatsKept r kq (seatsByPlace gq r.lo.length) := by
  intro a i hi q hq
  have ha : a < kq.length := (List.getElem?_eq_some_iff.1 hq).1
  have e := List.all_eq_true.1 h a (List.mem_range.2 ha)
  rw [hi] at e
  have e2 : gq[i.val]? = kq[a]? := beq_iff_eq.1 e
  show gq.getD i.val (0, 0) = q
  rw [List.getD_eq_getElem?_getD, e2, hq]
  rfl

/-- **THE TEST.** -/
def membersK2B (L : MemberLists) (kq nq : List (ℕ × ℕ)) (r : SwRow) : Bool :=
  sitsB L kq (keptEntries r) && onceB L kq && sitsB L nq r.l && nq.length == r.l.length

variable {L : MemberLists} {kq nq : List (ℕ × ℕ)} {r : SwRow}

/-- **The table's members at a kept tenant are the typed kept members.** -/
theorem kept_of_B (H : r.OK) (h : membersK2B L kq nq r = true)
    (seat : Fin r.lo.length → ℕ × ℕ) (hseat : SeatsKept r kq seat) :
    (∀ q ∈ kq, (∃ x ∈ msOf L, SitsAt x q.1 q.2) ∧
      ∀ x ∈ msOf L, SitsAt x q.1 q.2 →
        x ∈ ((msOf L).filter fun x => kq.contains (x.1.seat x.2)) ∧
        ∃ i : Fin r.lo.length, i.val ∈ r.kept ∧ Alike x ⟨⟨r.lo, seat⟩, i⟩) ∧
      (((msOf L).filter fun x => kq.contains (x.1.seat x.2)).map seatOf).Nodup := by
  unfold membersK2B at h
  rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at h
  refine ⟨fun q hq => ?_, nodup_of_B h.1.1.2⟩
  obtain ⟨a, ha⟩ := List.getElem?_of_mem hq
  obtain ⟨e, he, h1, h2⟩ := sits_of_B h.1.1.1 a q ha
  refine ⟨h1, fun x hx hs => ⟨mem_filter_of_sits hx hq hs, ?_⟩⟩
  unfold keptEntries at he
  rw [List.getElem?_map] at he
  obtain ⟨i, hi, rfl⟩ := Option.map_eq_some_iff.1 he
  have hm : i ∈ r.kept := List.mem_of_getElem? hi
  have hlt : i < r.lo.length := by
    have hk := H.kept i hm
    obtain ⟨y, hy, -⟩ := Option.map_eq_some_iff.1 hk
    exact (List.getElem?_eq_some_iff.1 hy).1
  refine ⟨⟨i, hlt⟩, hm, ?_, ?_⟩
  · rw [h2 x hx hs]
    exact List.getD_eq_getElem _ _ hlt
  · show x.1.seat x.2 = seat ⟨i, hlt⟩
    rw [hseat a ⟨i, hlt⟩ hi q ha]
    exact hs

/-- **Whoever of the table's members sits at the seat of the member i of the typed new sending is
alike to that member**; the typed members' seats are just the tenants nq; and at each of these a
member of the table sits. -/
theorem new_of_B (h : membersK2B L kq nq r = true) :
    (∀ i : Fin r.l.length, ∀ x ∈ msOf L,
      SitsAt x (seatsByPlace nq r.l.length i).1 (seatsByPlace nq r.l.length i).2 →
        Alike x ⟨⟨r.l, seatsByPlace nq r.l.length⟩, i⟩) ∧
      (∀ q ∈ nq, ∃ i : Fin r.l.length, seatsByPlace nq r.l.length i = q) ∧
      (∀ i : Fin r.l.length, seatsByPlace nq r.l.length i ∈ nq) ∧
      ∀ q ∈ nq, ∃ x ∈ msOf L, SitsAt x q.1 q.2 := by
  unfold membersK2B at h
  rw [Bool.and_eq_true, Bool.and_eq_true] at h
  exact each_of_B h.1.2 (beq_iff_eq.1 h.2)

/-- `kept_of_B` at the table's own letters: N: the table's numbers; p: a place of the kind K2 whose
row lays; the picked members are the table's `minePadAt`. -/
theorem kept_at_table (H : r.OK) (N : Numbers) (links : List ModelPart) (p : Place) (hk : p.kind = .K2)
    (hl : (rowOf links p).lays = true)
    (h : membersK2B L (N.keptOf (p.link.getD links.length - 1)) nq r = true)
    (seat : Fin r.lo.length → ℕ × ℕ)
    (hseat : SeatsKept r (N.keptOf (p.link.getD links.length - 1)) seat) :
    (∀ q ∈ N.keptOf (p.link.getD links.length - 1), (∃ x ∈ msOf L, SitsAt x q.1 q.2) ∧
      ∀ x ∈ msOf L, SitsAt x q.1 q.2 → x ∈ minePadAt (msOf L) N links p ∧
        ∃ i : Fin r.lo.length, i.val ∈ r.kept ∧ Alike x ⟨⟨r.lo, seat⟩, i⟩) ∧
      ((minePadAt (msOf L) N links p).map seatOf).Nodup := by
  rw [minePadAt_K2 (msOf L) N links p hk hl]
  exact kept_of_B H h seat hseat

end VerifiableInference.Desc.First.K2Caller

#print axioms VerifiableInference.Desc.First.K2Caller.seatKept_fits
#print axioms VerifiableInference.Desc.First.K2Caller.seatsKept_of_B
#print axioms VerifiableInference.Desc.First.K2Caller.kept_of_B
#print axioms VerifiableInference.Desc.First.K2Caller.new_of_B
#print axioms VerifiableInference.Desc.First.K2Caller.kept_at_table
