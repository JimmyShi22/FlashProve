-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Close/Law/MainAtFull.lean (kind K10): THREE MORE SENTENCES ON THE TERM FOR seat
(`seatK10`, SeatsOfLink.lean), IN THE FORMS THAT HQAtFa.lean's `k10_hQ_at_fa` ASKS (hGrp, hAl,
hSit): each from one test with code; at the written values of the full size by evaluations in Lean's
kernel. Definitions with code, and theorems.
  `grpB lo seats own`, `grp_of_B`: **every place of lo whose shape has a main row
    (`Johnson.G.memMain`, Johnson/G/SwitchKeptLit.lean) has its seat in own.** `alikeMainB ML own lo
    seats`, `alikeMain_of_B`: **every member at a seat of own is alike to a place of lo that has a
    main row.** `sitB ML own`, `sit_of_B`: **every seat of own is some member's** (`SitsAt`,
    Johnson/Desc/Sound/MeaningSig.lean).
  `grpB_full`, `alikeMainB_full`, `sitB_full`: the three tests say yes at every l < 26. THE NEGATIVE
    LINES, at link 0: `grpB_full_bare`: without the guard "has a main row" the first says no (place
    3, the index masks' message, sits in no group); `alikeMainB_full_zero`: with all main rows 0 the
    second says no; `sitB_full_more`: with a foreign seat more the third says no.
  `grp_full`, `alikeMain_full`, `sit_full`, `sit_sent_full`: the sentences at the written values, l
    < 26; the last at each of the three moments' tenants.
Limits. AT WRITTEN VALUES. Nothing on soundness.

-/
import Johnson.Desc.First.Close.Law.AlikeFull
import Johnson.G.SwitchKeptLit
import Johnson.Desc.Sound.MeaningSig

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Close
open OnBytes
open Johnson.G (memMain)
open VerifiableInference.Desc (MemberLists)
open VerifiableInference.Desc.Sound (msOf seatOf Alike SitsAt)

/-- The i-th entry's shape has a main row. -/
def mainAtB (lo : List (OracleShape × ℕ)) (i : ℕ) : Bool := (lo.getD i default).1.mainRows != 0

theorem mainAtB_iff (lo : List (OracleShape × ℕ)) (i : Fin lo.length) :
    mainAtB lo i.val = true ↔ memMain lo i := by
  unfold mainAtB memMain
  rw [List.getD_eq_getElem _ _ i.isLt]
  simp

/-- **Every place with a main row has its seat in own**: as a test. -/
def grpB (lo : List (OracleShape × ℕ)) (seats own : List (ℕ × ℕ)) : Bool :=
  (List.range lo.length).all fun i => !mainAtB lo i || own.contains (seats.getD i (0, 0))

/-- **Every member at a seat of own is alike to a place with a main row**: as a test. -/
def alikeMainB (ML : MemberLists) (own : List (ℕ × ℕ)) (lo : List (OracleShape × ℕ))
    (seats : List (ℕ × ℕ)) : Bool :=
  ((plainMems ML).filter fun x => own.contains x.2).all fun x =>
    (List.range lo.length).any fun i =>
      mainAtB lo i && decide (lo.getD i default = x.1) && seats.getD i (0, 0) == x.2

/-- **Every seat of own is some member's**: as a test. -/
def sitB (ML : MemberLists) (own : List (ℕ × ℕ)) : Bool :=
  own.all fun s => (plainMems ML).any fun x => x.2 == s

theorem grp_of_B {lo : List (OracleShape × ℕ)} {seats own : List (ℕ × ℕ)}
    (h : grpB lo seats own = true) :
    ∀ i : Fin lo.length, memMain lo i → seats.getD i.val (0, 0) ∈ own := by
  intro i hi
  have a := List.all_eq_true.1 h i.val (List.mem_range.2 i.isLt)
  rw [(mainAtB_iff lo i).2 hi] at a
  simpa using a

theorem alikeMain_of_B {ML : MemberLists} {own : List (ℕ × ℕ)} {lo : List (OracleShape × ℕ)}
    {seats : List (ℕ × ℕ)} (h : alikeMainB ML own lo seats = true) :
    ∀ x ∈ msOf ML, seatOf x ∈ own → ∃ i : Fin lo.length,
      memMain lo i ∧ Alike x ⟨⟨lo, fun i => seats.getD i.val (0, 0)⟩, i⟩ := by
  intro x hx ho
  have hm : (x.1.l.get x.2, seatOf x) ∈ (plainMems ML).filter fun y => own.contains y.2 :=
    List.mem_filter.2 ⟨mem_plain hx, by simpa using ho⟩
  obtain ⟨i, hi, hb⟩ := List.any_eq_true.1 (List.all_eq_true.1 h _ hm)
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hb
  have hi' : i < lo.length := List.mem_range.1 hi
  refine ⟨⟨i, hi'⟩, (mainAtB_iff lo ⟨i, hi'⟩).1 hb.1.1, ?_, hb.2.symm⟩
  show x.1.l.get x.2 = lo.get ⟨i, hi'⟩
  rw [← hb.1.2, List.getD_eq_getElem _ _ hi']
  rfl

theorem sit_of_B {ML : MemberLists} {own : List (ℕ × ℕ)} (h : sitB ML own = true) :
    ∀ s ∈ own, ∃ x ∈ msOf ML, SitsAt x s.1 s.2 := by
  intro s hs
  obtain ⟨y, hy, hb⟩ := List.any_eq_true.1 (List.all_eq_true.1 h s hs)
  obtain ⟨x, hx, -, e2⟩ := plain_mem hy
  exact ⟨x, hx, e2.trans (eq_of_beq hb)⟩

/-! ## At the written values -/

set_option maxRecDepth 1000000 in
theorem grpB_full :
    ((List.range 26).all fun l => grpB (Johnson.G.linksFullLit.getD l []) (seatsOfLink P5T.psFull l)
      (P5T.N0Full.group l)) = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem alikeMainB_full :
    ((List.range 26).all fun l => alikeMainB mlFull (P5T.N0Full.group l)
      (Johnson.G.linksFullLit.getD l []) (seatsOfLink P5T.psFull l)) = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem sitB_full :
    ((List.range 26).all fun l => sitB mlFull (P5T.N0Full.group l)) = true := by decide +kernel

set_option maxRecDepth 1000000 in
/-- **(N)** Without the guard "has a main row", link 0 fails. -/
theorem grpB_full_bare :
    ((List.range (Johnson.G.linksFullLit.getD 0 []).length).all fun i =>
      (P5T.N0Full.group 0).contains ((seatsOfLink P5T.psFull 0).getD i (0, 0))) = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- **(N)** With all main rows 0, link 0 fails. -/
theorem alikeMainB_full_zero :
    alikeMainB mlFull (P5T.N0Full.group 0)
      ((Johnson.G.linksFullLit.getD 0 []).map fun e => ({ e.1 with mainRows := 0 }, e.2))
      (seatsOfLink P5T.psFull 0) = false := by decide +kernel

set_option maxRecDepth 1000000 in
/-- **(N)** With a foreign seat more, link 0 fails. -/
theorem sitB_full_more : sitB mlFull (P5T.N0Full.group 0 ++ [(9999, 0)]) = false := by
  decide +kernel

theorem grp_full (l : ℕ) (hl : l < 26) :
    ∀ i : Fin (Johnson.G.linksFullLit.getD l []).length,
      memMain (Johnson.G.linksFullLit.getD l []) i →
      seatK10 (Johnson.G.linksFullLit.getD l []) P5T.psFull l i ∈ P5T.N0Full.group l :=
  grp_of_B (List.all_eq_true.1 grpB_full l (List.mem_range.2 hl))

theorem alikeMain_full (l : ℕ) (hl : l < 26) :
    ∀ x ∈ msOf mlFull, seatOf x ∈ P5T.N0Full.group l →
      ∃ i : Fin (Johnson.G.linksFullLit.getD l []).length,
        memMain (Johnson.G.linksFullLit.getD l []) i ∧
        Alike x ⟨⟨Johnson.G.linksFullLit.getD l [],
          seatK10 (Johnson.G.linksFullLit.getD l []) P5T.psFull l⟩, i⟩ :=
  alikeMain_of_B (List.all_eq_true.1 alikeMainB_full l (List.mem_range.2 hl))

theorem sit_full (l : ℕ) (hl : l < 26) :
    ∀ s ∈ P5T.N0Full.group l, ∃ x ∈ msOf mlFull, SitsAt x s.1 s.2 :=
  sit_of_B (List.all_eq_true.1 sitB_full l (List.mem_range.2 hl))

/-- At each of the three moments' tenants. -/
theorem sit_sent_full (l : ℕ) (hl : l < 26) (t : ℕ) (ht : t < 3) :
    ∀ s ∈ P5T.N0Full.sent l t, ∃ x ∈ msOf mlFull, SitsAt x s.1 s.2 := by
  intro s hs
  refine sit_full l hl s ?_
  unfold VerifiableInference.Desc.First.Numbers.group
  simp only [List.mem_append]
  rcases (by omega : t = 0 ∨ t = 1 ∨ t = 2) with rfl | rfl | rfl
  · exact Or.inl (Or.inl hs)
  · exact Or.inl (Or.inr hs)
  · exact Or.inr hs

end VerifiableInference.Desc.First.Close

#print axioms VerifiableInference.Desc.First.Close.mainAtB_iff
#print axioms VerifiableInference.Desc.First.Close.grp_of_B
#print axioms VerifiableInference.Desc.First.Close.alikeMain_of_B
#print axioms VerifiableInference.Desc.First.Close.sit_of_B
#print axioms VerifiableInference.Desc.First.Close.grpB_full
#print axioms VerifiableInference.Desc.First.Close.alikeMainB_full
#print axioms VerifiableInference.Desc.First.Close.sitB_full
#print axioms VerifiableInference.Desc.First.Close.grpB_full_bare
#print axioms VerifiableInference.Desc.First.Close.alikeMainB_full_zero
#print axioms VerifiableInference.Desc.First.Close.sitB_full_more
#print axioms VerifiableInference.Desc.First.Close.grp_full
#print axioms VerifiableInference.Desc.First.Close.alikeMain_full
#print axioms VerifiableInference.Desc.First.Close.sit_full
#print axioms VerifiableInference.Desc.First.Close.sit_sent_full
