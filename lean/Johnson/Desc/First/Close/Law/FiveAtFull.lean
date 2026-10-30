-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Close/Law/FiveAtFull.lean (kind K10): THE PLAN's FACTS AT LINK 0 AT THE FIVE-LIST
`loFive` (LinkZeroFive.lean: the written list's entries that have a main row): the terms for seat
and for a member's number, and the sentences of SeatsOfLink.lean, SeatsApart.lean and
MainAtFull.lean there: by evaluations in Lean's kernel. Definitions with code, and theorems.
Why. At link 0 the written list has six entries; one, the index masks' message, has no main row and
sits in no group. The typed group is cut over the five others: so the plan's facts are wanted at
that list and at the five seats.
  `seatsMain lo seats`: the seats at the places of lo that have a main row, in order. `seatsFive`,
    `seatFive`, `noFive`: these at link 0; the term for seat; the place of a member's seat in the
    plan's list.
  `num_inj_of_list`, `seat_inj_of_list`: SeatsApart.lean's two sentences at any list of seats.
  `fiveB_full`: **the five tests say yes at (`loFive`, `seatsFive`).** `seatsFive_is`: the five
    seats are the group's own list, in order. `noFive_is`: the five numbers are 0, 1, 2, 5, 6.
    `fiveB_twin`: THE NEGATIVE LINE: at the six-list's seats each of the five tests says no.
  `alike_five`, `hit_five`, `num_inj_five`, `seat_inj_five`, `grp_five`, `alikeMain_five`: the
    sentences at `seatFive`.
Limits. AT WRITTEN VALUES; link 0 alone. Nothing on soundness.

-/
import Johnson.Desc.First.Close.Law.LinkZeroFive
import Johnson.Desc.First.Close.Law.MainAtFull
import Johnson.Desc.First.Close.Law.SeatsApart
import Johnson.Desc.First.Close.Law.MembersAtFull

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Close
open OnBytes
open Johnson.G (memMain)
open VerifiableInference.Desc.Sound (msOf seatOf Alike)

/-- The seats at the places of lo that have a main row, in order. -/
def seatsMain (lo : List (OracleShape × ℕ)) (seats : List (ℕ × ℕ)) : List (ℕ × ℕ) :=
  ((List.range lo.length).filter (mainAtB lo)).map fun i => seats.getD i (0, 0)

/-- Link 0's five seats. -/
def seatsFive : List (ℕ × ℕ) := seatsMain loSix (seatsOfLink P5T.psFull 0)

/-- **THE TERM FOR seat AT THE FIVE-LIST.** -/
def seatFive : Fin loFive.length → ℕ × ℕ := fun i => seatsFive.getD i.val (0, 0)

/-- **THE TERM FOR A MEMBER's NUMBER AT THE FIVE-LIST.** -/
def noFive : Fin loFive.length → ℕ := fun i => seatsPlanW.idxOf (seatFive i)

/-- Different places bear different numbers: at any list of seats. -/
theorem num_inj_of_list {arr : ℕ → ℕ → ℕ} {lo : List (OracleShape × ℕ)} {seats : List (ℕ × ℕ)}
    (h : numsApartB arr lo.length seats = true) :
    ∀ i i' : Fin lo.length,
      arr (seats.getD i.val (0, 0)).1 (seats.getD i.val (0, 0)).2 =
        arr (seats.getD i'.val (0, 0)).1 (seats.getD i'.val (0, 0)).2 → i = i' := by
  unfold numsApartB at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨hn, hd⟩ := h
  intro i i' e
  have hi : i.val < seats.length := by
    rw [hn]
    exact i.isLt
  have hi' : i'.val < seats.length := by
    rw [hn]
    exact i'.isLt
  rw [List.getD_eq_getElem _ _ hi, List.getD_eq_getElem _ _ hi'] at e
  have hm : i.val < (seats.map fun q => arr q.1 q.2).length := by
    rw [List.length_map]
    exact hi
  have hm' : i'.val < (seats.map fun q => arr q.1 q.2).length := by
    rw [List.length_map]
    exact hi'
  have e2 : (seats.map fun q => arr q.1 q.2)[i.val]'hm =
      (seats.map fun q => arr q.1 q.2)[i'.val]'hm' := by
    rw [List.getElem_map, List.getElem_map]
    exact e
  exact Fin.ext ((List.Nodup.getElem_inj_iff hd).1 e2)

/-- So the places' seats are different. -/
theorem seat_inj_of_list {arr : ℕ → ℕ → ℕ} {lo : List (OracleShape × ℕ)} {seats : List (ℕ × ℕ)}
    (h : numsApartB arr lo.length seats = true) :
    Function.Injective fun i : Fin lo.length => seats.getD i.val (0, 0) := fun i i' e =>
  num_inj_of_list h i i' (by
    have e' : seats.getD i.val (0, 0) = seats.getD i'.val (0, 0) := e
    rw [e'])

/-! ## At the written values -/

set_option maxRecDepth 1000000 in
/-- **(W) The five tests say yes at the five-list and the five seats.** -/
theorem fiveB_full :
    (alikeB mlFull (P5T.N0Full.group 0) loFive seatsFive && hitB mlFull loFive seatsFive &&
      numsApartB arrFull loFive.length seatsFive && grpB loFive seatsFive (P5T.N0Full.group 0) &&
      alikeMainB mlFull (P5T.N0Full.group 0) loFive seatsFive) = true := by decide +kernel

set_option maxRecDepth 1000000 in
/-- The five seats are the group's own list, in order. -/
theorem seatsFive_is : seatsFive = P5T.N0Full.group 0 := by decide +kernel

set_option maxRecDepth 1000000 in
/-- The five numbers. -/
theorem noFive_is : (List.finRange loFive.length).map noFive = [0, 1, 2, 5, 6] := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- **(N)** At the six-list's seats each of the five tests says no. -/
theorem fiveB_twin :
    (alikeB mlFull (P5T.N0Full.group 0) loFive (seatsOfLink P5T.psFull 0) ||
      hitB mlFull loFive (seatsOfLink P5T.psFull 0) ||
      numsApartB arrFull loFive.length (seatsOfLink P5T.psFull 0) ||
      grpB loFive (seatsOfLink P5T.psFull 0) (P5T.N0Full.group 0) ||
      alikeMainB mlFull (P5T.N0Full.group 0) loFive (seatsOfLink P5T.psFull 0)) = false := by
  decide +kernel

theorem five_parts :
    alikeB mlFull (P5T.N0Full.group 0) loFive seatsFive = true ∧
      hitB mlFull loFive seatsFive = true ∧ numsApartB arrFull loFive.length seatsFive = true ∧
      grpB loFive seatsFive (P5T.N0Full.group 0) = true ∧
      alikeMainB mlFull (P5T.N0Full.group 0) loFive seatsFive = true := by
  have h := fiveB_full
  simp only [Bool.and_eq_true] at h
  exact ⟨h.1.1.1.1, h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩

theorem alike_five : ∀ x ∈ msOf mlFull, seatOf x ∈ P5T.N0Full.group 0 →
    ∃ i : Fin loFive.length, Alike x ⟨⟨loFive, seatFive⟩, i⟩ := alike_of_B five_parts.1

theorem hit_five : ∀ i : Fin loFive.length, ∃ x ∈ msOf mlFull, Alike x ⟨⟨loFive, seatFive⟩, i⟩ :=
  hit_of_B five_parts.2.1

theorem num_inj_five : ∀ i i' : Fin loFive.length,
    arrFull (seatFive i).1 (seatFive i).2 = arrFull (seatFive i').1 (seatFive i').2 → i = i' :=
  num_inj_of_list five_parts.2.2.1

theorem seat_inj_five : Function.Injective seatFive := seat_inj_of_list five_parts.2.2.1

theorem grp_five : ∀ i : Fin loFive.length, memMain loFive i → seatFive i ∈ P5T.N0Full.group 0 :=
  grp_of_B five_parts.2.2.2.1

theorem alikeMain_five : ∀ x ∈ msOf mlFull, seatOf x ∈ P5T.N0Full.group 0 →
    ∃ i : Fin loFive.length, memMain loFive i ∧ Alike x ⟨⟨loFive, seatFive⟩, i⟩ :=
  alikeMain_of_B five_parts.2.2.2.2

end VerifiableInference.Desc.First.Close

#print axioms VerifiableInference.Desc.First.Close.num_inj_of_list
#print axioms VerifiableInference.Desc.First.Close.seat_inj_of_list
#print axioms VerifiableInference.Desc.First.Close.fiveB_full
#print axioms VerifiableInference.Desc.First.Close.seatsFive_is
#print axioms VerifiableInference.Desc.First.Close.noFive_is
#print axioms VerifiableInference.Desc.First.Close.fiveB_twin
#print axioms VerifiableInference.Desc.First.Close.five_parts
#print axioms VerifiableInference.Desc.First.Close.alike_five
#print axioms VerifiableInference.Desc.First.Close.hit_five
#print axioms VerifiableInference.Desc.First.Close.num_inj_five
#print axioms VerifiableInference.Desc.First.Close.seat_inj_five
#print axioms VerifiableInference.Desc.First.Close.grp_five
#print axioms VerifiableInference.Desc.First.Close.alikeMain_five
