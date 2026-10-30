-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Close/Law/SeatsOfLink.lean (kind K10): A TERM FOR THE SEATS OF THE MEMBERS OF A
LINK's WRITTEN LIST, OFF THE PLAN's ENTRIES; AND THE TWO SENTENCES THAT K10's PINS AND ITS FIRST TIE
SPEND ON IT, EACH FROM ONE TEST WITH CODE ON PLAIN LISTS. Definitions with code, and theorems.
Why. K10's law reads a link's group through ONE list lo of all three sendings' sampled oracle
messages; the table of joints' members ms stand each in ITS OWN sending's list.
Johnson/Desc/Sound/PinMove.lean carries what is said of a member to every member that is alike
(`Alike`: one entry, shape and radius; one seat). PinsAtFa.lean and FrontAtK10.lean take "alike" as
a premise: there was no term for the seat.
  `seatsOfLink ps l`: the seats of the plan's entries of link l that have an out-of-domain sample,
    in the plan's own order; THE MESSAGE "AT START" (the index masks') AMONG THEM: at link 0 the
    written list holds it, the table's group does not. `seatK10 lo ps l`: the i-th of them; (0, 0)
    beyond.
  `plainMems ML`: the members of plain lists as pairs (entry, seat). `mem_plain`, `plain_mem`: these
    are just the members of `msOf ML` (Johnson/Desc/Sound/PlanMemProofs.lean).
  `alikeB ML own lo seats`, `alike_of_B`: **a yes gives: every member of `msOf ML` whose seat is in
    own is alike to the i-th of lo at the seats, for some i.** `hitB ML lo seats`, `hit_of_B`: **a
    yes gives: every i of lo is alike to a member.**
  `alike_at_R`, `hit_at_R`: the two at the composed meaning's own term for ms (`P5T.msAtR Z rad`,
    Johnson/P5T/MembersByMake.lean) and at `seatK10 lo (P5T.planSeats Z Z.D.1) l`.
  `alikeB_yes`, `alikeB_seat`, `alikeB_rad`, `hitB_no`: THE TESTS CAN SAY NO: by Lean's kernel at a
    small written list.
Limits. THE TWO TESTS' ANSWERS AT A REAL PLAN ARE NO THEOREM HERE. The shapes and seats are the
plan's; THE RADII ARE AN ARGUMENT (rad): held against nothing. Nothing on whether a seat is a
sampled tenant whose pin is open. Nothing on soundness.

-/
import Johnson.P5T.MembersByMake
import Johnson.Desc.Sound.PinMove
import Johnson.Desc.Sound.PlanMemProofs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Close
open OnBytes
open VerifiableInference.Desc (MemberLists)
open VerifiableInference.Desc.Sound (Mem Sending msOf sendsOf membersOf seatOf Alike)

/-- **THE SEATS OF A LINK's SAMPLED ORACLE MESSAGES**, in the plan's own order. -/
def seatsOfLink (ps : List P5T.PSeat) (l : ℕ) : List (ℕ × ℕ) :=
  (ps.filter fun p => p.seg.map (·.1) == some l && p.smpd).map (·.seat)

/-- **THE TERM FOR seat.** -/
def seatK10 (lo : List (OracleShape × ℕ)) (ps : List P5T.PSeat) (l : ℕ) :
    Fin lo.length → ℕ × ℕ := fun i => (seatsOfLink ps l).getD i.val (0, 0)

/-- The members of plain lists, as (entry, seat). -/
def plainMems (ML : MemberLists) : List ((OracleShape × ℕ) × (ℕ × ℕ)) :=
  ML.flatMap fun x => (List.range x.1.length).map fun j => (x.1.getD j default, x.2.getD j (0, 0))

/-- A member's pair is among them. -/
theorem mem_plain {ML : MemberLists} {x : Mem} (h : x ∈ msOf ML) :
    (x.1.l.get x.2, seatOf x) ∈ plainMems ML := by
  unfold msOf membersOf sendsOf at h
  obtain ⟨s, hs, hx⟩ := List.mem_flatMap.1 h
  obtain ⟨e, he, rfl⟩ := List.mem_map.1 hs
  obtain ⟨j, -, rfl⟩ := List.mem_map.1 hx
  refine List.mem_flatMap.2 ⟨e, he, List.mem_map.2 ⟨j.val, List.mem_range.2 j.isLt, ?_⟩⟩
  refine Prod.ext ?_ rfl
  have hj : j.val < e.1.length := j.isLt
  show e.1.getD j.val default = e.1.get ⟨j.val, hj⟩
  rw [List.getD_eq_getElem _ _ hj]
  rfl

/-- And each of them is a member's. -/
theorem plain_mem {ML : MemberLists} {y : (OracleShape × ℕ) × (ℕ × ℕ)} (h : y ∈ plainMems ML) :
    ∃ x ∈ msOf ML, x.1.l.get x.2 = y.1 ∧ seatOf x = y.2 := by
  obtain ⟨e, he, hy⟩ := List.mem_flatMap.1 h
  obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hy
  have hj' : j < e.1.length := List.mem_range.1 hj
  refine ⟨⟨Sending.ofLists e.1 e.2, ⟨j, hj'⟩⟩, ?_, ?_, rfl⟩
  · unfold msOf membersOf sendsOf
    exact List.mem_flatMap.2 ⟨_, List.mem_map.2 ⟨e, he, rfl⟩,
      List.mem_map.2 ⟨⟨j, hj'⟩, List.mem_finRange _, rfl⟩⟩
  · show e.1.get ⟨j, hj'⟩ = e.1.getD j default
    rw [List.getD_eq_getElem _ _ hj']
    rfl

/-- **Every member at a seat of own is alike to a place of lo**: as a test. -/
def alikeB (ML : MemberLists) (own : List (ℕ × ℕ)) (lo : List (OracleShape × ℕ))
    (seats : List (ℕ × ℕ)) : Bool :=
  ((plainMems ML).filter fun x => own.contains x.2).all fun x =>
    (List.range lo.length).any fun i =>
      decide (lo.getD i default = x.1) && seats.getD i (0, 0) == x.2

/-- **Every place of lo is alike to a member**: as a test. -/
def hitB (ML : MemberLists) (lo : List (OracleShape × ℕ)) (seats : List (ℕ × ℕ)) : Bool :=
  (List.range lo.length).all fun i =>
    (plainMems ML).any fun x => decide (lo.getD i default = x.1) && seats.getD i (0, 0) == x.2

/-- **WHAT A YES OF THE FIRST TEST GIVES.** -/
theorem alike_of_B {ML : MemberLists} {own : List (ℕ × ℕ)} {lo : List (OracleShape × ℕ)}
    {seats : List (ℕ × ℕ)} (h : alikeB ML own lo seats = true) :
    ∀ x ∈ msOf ML, seatOf x ∈ own →
      ∃ i : Fin lo.length, Alike x ⟨⟨lo, fun i => seats.getD i.val (0, 0)⟩, i⟩ := by
  intro x hx ho
  have hm : (x.1.l.get x.2, seatOf x) ∈ (plainMems ML).filter fun y => own.contains y.2 :=
    List.mem_filter.2 ⟨mem_plain hx, by simpa using ho⟩
  obtain ⟨i, hi, hb⟩ := List.any_eq_true.1 (List.all_eq_true.1 h _ hm)
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hb
  have hi' : i < lo.length := List.mem_range.1 hi
  refine ⟨⟨i, hi'⟩, ?_, hb.2.symm⟩
  show x.1.l.get x.2 = lo.get ⟨i, hi'⟩
  rw [← hb.1, List.getD_eq_getElem _ _ hi']
  rfl

/-- **WHAT A YES OF THE SECOND GIVES.** -/
theorem hit_of_B {ML : MemberLists} {lo : List (OracleShape × ℕ)} {seats : List (ℕ × ℕ)}
    (h : hitB ML lo seats = true) :
    ∀ i : Fin lo.length, ∃ x ∈ msOf ML, Alike x ⟨⟨lo, fun i => seats.getD i.val (0, 0)⟩, i⟩ := by
  intro i
  obtain ⟨y, hy, hb⟩ := List.any_eq_true.1 (List.all_eq_true.1 h i.val (List.mem_range.2 i.isLt))
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hb
  obtain ⟨x, hx, e1, e2⟩ := plain_mem hy
  refine ⟨x, hx, ?_, e2.trans hb.2.symm⟩
  show x.1.l.get x.2 = lo.get i
  rw [e1, ← hb.1, List.getD_eq_getElem _ _ i.isLt]
  rfl

/-! ## At the composed meaning's own term for ms -/

/-- The first sentence at `P5T.msAtR Z rad` and `seatK10`. -/
theorem alike_at_R (Z : ProofFile.Pub) (rad : ℕ → ℕ → ℕ) (own : List (ℕ × ℕ))
    (lo : List (OracleShape × ℕ)) (l : ℕ)
    (h : alikeB (P5T.memberListsR Z.made.proof.1.sends.length rad (P5T.planSeats Z Z.D.1)) own lo
      (seatsOfLink (P5T.planSeats Z Z.D.1) l) = true) :
    ∀ x ∈ P5T.msAtR Z rad, seatOf x ∈ own →
      ∃ i : Fin lo.length, Alike x ⟨⟨lo, seatK10 lo (P5T.planSeats Z Z.D.1) l⟩, i⟩ :=
  alike_of_B h

/-- The second. -/
theorem hit_at_R (Z : ProofFile.Pub) (rad : ℕ → ℕ → ℕ) (lo : List (OracleShape × ℕ)) (l : ℕ)
    (h : hitB (P5T.memberListsR Z.made.proof.1.sends.length rad (P5T.planSeats Z Z.D.1)) lo
      (seatsOfLink (P5T.planSeats Z Z.D.1) l) = true) :
    ∀ i : Fin lo.length, ∃ x ∈ P5T.msAtR Z rad,
      Alike x ⟨⟨lo, seatK10 lo (P5T.planSeats Z Z.D.1) l⟩, i⟩ :=
  hit_of_B h

/-! ## The tests can say no -/

/-- Two sendings: one member at the seat (1, 0), two at (2, 0) and (2, 1). -/
def mlToy : MemberLists :=
  [([(default, 7)], [(1, 0)]), ([(default, 7), (default, 9)], [(2, 0), (2, 1)])]

theorem alikeB_yes : alikeB mlToy [(1, 0), (2, 1)] [(default, 7), (default, 7), (default, 9)]
    [(1, 0), (2, 0), (2, 1)] = true := by decide +kernel

theorem alikeB_seat : alikeB mlToy [(1, 0), (2, 1)] [(default, 7), (default, 7), (default, 9)]
    [(2, 0), (2, 1), (1, 0)] = false := by decide +kernel

theorem alikeB_rad : alikeB mlToy [(1, 0), (2, 1)] [(default, 7), (default, 7), (default, 10)]
    [(1, 0), (2, 0), (2, 1)] = false := by decide +kernel

theorem hitB_no : hitB mlToy [(default, 7), (default, 8)] [(1, 0), (2, 0)] = false := by
  decide +kernel

end VerifiableInference.Desc.First.Close

#print axioms VerifiableInference.Desc.First.Close.mem_plain
#print axioms VerifiableInference.Desc.First.Close.plain_mem
#print axioms VerifiableInference.Desc.First.Close.alike_of_B
#print axioms VerifiableInference.Desc.First.Close.hit_of_B
#print axioms VerifiableInference.Desc.First.Close.alike_at_R
#print axioms VerifiableInference.Desc.First.Close.hit_at_R
#print axioms VerifiableInference.Desc.First.Close.alikeB_yes
#print axioms VerifiableInference.Desc.First.Close.alikeB_seat
#print axioms VerifiableInference.Desc.First.Close.alikeB_rad
#print axioms VerifiableInference.Desc.First.Close.hitB_no
