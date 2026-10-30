-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K14/ArrAtHead.lean: kind K14: at the full size the library's numbering
of the witness's messages (P5J.At.arr, Johnson/P5J/LettersAt.lean) gives the seats of the shared
chain's three sampled messages three numbers, and none of the three to a seat in one of the first
chain's trees. One definition, a test with code; statements with their proofs.

A witness holds each message once, under a number, and the numbering says which number the tenant t
of the tree j bears. Whoever lays the shared chain's messages o_u, o_omega and o_sp into a witness
that also holds the first chain's messages needs both sentences: else one message would be laid over
another.

At the full size the numbering is the one at the library's written list of all three chains' seats
(seatsAllFull, Johnson/P5T/PlanSeatsFull.lean): P5J.L0.arr_at_head,
Johnson/P5J/L0/PlanFourAtJoin.lean.

  sharedNos_apart     at that list the seats (83, 0), (84, 0), (85, 0) bear three numbers, each
                      below the number of keys: so each seat is found in the list. An evaluation in
                      Lean's kernel
  offShared, firstNos_off, firstNos_bent   a test: no seat of the written list in a tree below
                      number n bears one of the three numbers. It accepts at 83, the number of the
                      first chain's trees; it rejects at 84. Two evaluations
  arrOf_or, written_off   so no pair (j, t) with j below 83 bears one of the three numbers, whether
                      or not the list has a seat there: beyond the list the numbering returns the
                      number of keys
  written_inj, shNums_tenant, first_trees_83   small steps
  harr_at_head        **at the full size the numbering is one to one on the three messages**, at the
                      tenants of the table Desc.K14.Law.Sh.nums at the plan P5J.AtMg.shPlan
  off_at_head, seat_off_at_head   **at the full size no tenant of a tree of the first chain bears
                      the number of one of the three messages**, nor is it the seat of one

Kin. arr_apart, harr_of_test (Johnson/P5T/ArrApart.lean), arr_apart_chains
(Johnson/P5T/ArrApartChains.lean), harr_of_found and far_of_found (Johnson/P5T/FoundInList.lean)
have the two sentences in general, under premises on what a search of the list finds, and
far_written (Johnson/Second/Seam/FarWritten.lean) evaluates these at the first chain's 199 listed
seats. off_at_head speaks of every pair below the first chain's number of trees.
numbers_written, seats_written, five_written, five_rejects (Johnson/HB/LLHARD/FiveWritten.lean)
evaluate the same three seats at the same list: their numbers are 163, 165 and 166.
Sh.paid_harr (Johnson/Desc/K14/Law/SharedConstTests.lean) has harr_at_head's sentence under a named
test. first_chain_83 (Honest/K14/BudBoth.lean) has first_trees_83's sentence at one hash, under
other premises. arr_apart_written, arr_can_meet (Johnson/P5J/L0/PlanFourAtJoin.lean) hold (84, 0)
against (1, 0) and (82, 0).

Limits.
  * THE PREMISE h IS A HYPOTHESIS: P5J.AtMg (Johnson/P5J/AtMg.lean). This file does not show it to
    be met.
  * Nothing on the second chain's own seats, nor on the shared chain's other seats (it sends eleven
    trees, and the first mask shares o_u's tree): that none of these bears one of the three numbers
    is not shown here.
  * maxRecDepth is raised to 1000000 in front of the three evaluations.

This file proves nothing about soundness, completeness, hiding or any other property of the
protocol.
-/
import Johnson.Desc.ProofFile.Honest.K14.TenantAtShPlan
import Johnson.Desc.Sound.TakenBelowOfData
import Johnson.P5J.L0.PlanFourAtJoin

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K14
open VerifiableInference.Desc (Chain)
open VerifiableInference.Desc.Shared (Msg2)
open _root_.Desc.K14.Law.Fence (tenantSh)
open _root_.Desc.K14.Law (layUFull layOFull)
open P5T (arrOf keyOf seatsAllFull)

set_option maxRecDepth 1000000 in
/-- At the written list of seats the three seats bear three numbers, each below the number of keys.
-/
theorem sharedNos_apart :
    arrOf seatsAllFull 83 0 ≠ arrOf seatsAllFull 84 0 ∧
      arrOf seatsAllFull 83 0 ≠ arrOf seatsAllFull 85 0 ∧
      arrOf seatsAllFull 84 0 ≠ arrOf seatsAllFull 85 0 ∧
      arrOf seatsAllFull 83 0 < ((seatsAllFull.map keyOf).eraseDups).length ∧
      arrOf seatsAllFull 84 0 < ((seatsAllFull.map keyOf).eraseDups).length ∧
      arrOf seatsAllFull 85 0 < ((seatsAllFull.map keyOf).eraseDups).length := by
  decide +kernel

/-- A test: no seat of the written list in a tree below number n bears one of the three numbers. -/
def offShared (n : Nat) : Bool :=
  seatsAllFull.all fun p => !decide (p.j < n) ||
    !([arrOf seatsAllFull 83 0, arrOf seatsAllFull 84 0, arrOf seatsAllFull 85 0].contains
      (arrOf seatsAllFull p.j p.t))

set_option maxRecDepth 1000000 in
/-- It accepts at 83, the number of the first chain's trees. -/
theorem firstNos_off : offShared 83 = true := by decide +kernel

set_option maxRecDepth 1000000 in
/-- It can reject: at 84, where o_u's own seat is among the seats asked. -/
theorem firstNos_bent : offShared 84 = false := by decide +kernel

/-- The list has a seat at (j, t), or the numbering returns the number of keys there. -/
theorem arrOf_or (ps : List P5T.PSeat) (j t : Nat) :
    (∃ p ∈ ps, p.j = j ∧ p.t = t) ∨ arrOf ps j t = ((ps.map keyOf).eraseDups).length := by
  cases hf : ps.find? (fun p => p.j == j && p.t == t) with
  | none =>
    right
    unfold arrOf
    simp only [hf]
  | some p =>
    left
    have a := List.find?_some hf
    simp only [Bool.and_eq_true, beq_iff_eq] at a
    exact ⟨p, List.mem_of_find?_eq_some hf, a.1, a.2⟩

/-- No pair with j below 83 bears one of the three numbers. -/
theorem written_off (j t : Nat) (hj : j < 83) :
    arrOf seatsAllFull j t ≠ arrOf seatsAllFull 83 0 ∧
      arrOf seatsAllFull j t ≠ arrOf seatsAllFull 84 0 ∧
      arrOf seatsAllFull j t ≠ arrOf seatsAllFull 85 0 := by
  obtain ⟨-, -, -, l1, l2, l3⟩ := sharedNos_apart
  rcases arrOf_or seatsAllFull j t with ⟨p, hp, rfl, rfl⟩ | e
  · have x := List.all_eq_true.1 firstNos_off p hp
    simp only [decide_eq_true hj, Bool.not_true, Bool.false_or, Bool.not_eq_true',
      List.contains_eq_mem, List.mem_cons, List.not_mem_nil, or_false, decide_eq_false_iff_not,
      not_or] at x
    exact x
  · rw [e]
    exact ⟨Nat.ne_of_gt l1, Nat.ne_of_gt l2, Nat.ne_of_gt l3⟩

/-- The numbering is one to one on the three messages, at the written values. -/
theorem written_inj : Function.Injective fun m : Msg2 =>
    arrOf seatsAllFull (tenantSh 83 layUFull layOFull m).1
      (tenantSh 83 layUFull layOFull m).2 := by
  obtain ⟨a, b, c⟩ := tenants_written
  obtain ⟨n1, n2, n3, -⟩ := sharedNos_apart
  intro m m' e
  cases m <;> cases m' <;> first
    | rfl
    | (exfalso
       simp only [a, b, c] at e
       first
         | exact n1 e | exact n2 e | exact n3 e
         | exact n1 e.symm | exact n2 e.symm | exact n3 e.symm)

variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain P5J.TS ProofFile.Cl}

/-- At the full size the description's first chain sends 83 trees. -/
theorem first_trees_83 (h : P5J.AtMg o Z D r Zp Np cF) : (P5J.F0T o Zp Np cF).t₁ = 83 :=
  (VerifiableInference.Desc.counts_of_data h.laid.data).1.symm.trans h.trees.1

/-- At the full size the table's three tenants are the written ones. -/
theorem shNums_tenant (h : P5J.AtMg o Z D r Zp Np cF) {P₀ P₁ Cells Tok : Type}
    (O : _root_.Desc.K14.Law.ShOpen P₀ P₁ Cells Tok h.shPlan.Q) :
    (_root_.Desc.K14.Law.Sh.nums h.shPlan O).tenant = tenantSh 83 layUFull layOFull :=
  IM.Seats.tenants_written_at_head h

/-- **At the full size the numbering is one to one on the three messages.** -/
theorem harr_at_head (h : P5J.AtMg o Z D r Zp Np cF) {P₀ P₁ Cells Tok : Type}
    (O : _root_.Desc.K14.Law.ShOpen P₀ P₁ Cells Tok h.shPlan.Q) :
    Function.Injective fun m : Msg2 =>
      P5J.At.arr Zp ((_root_.Desc.K14.Law.Sh.nums h.shPlan O).tenant m).1
        ((_root_.Desc.K14.Law.Sh.nums h.shPlan O).tenant m).2 := by
  rw [shNums_tenant h O, P5J.L0.arr_at_head h]
  exact written_inj

/-- **At the full size no tenant of a tree of the first chain bears the number of one of the three
messages.** -/
theorem off_at_head (h : P5J.AtMg o Z D r Zp Np cF) {P₀ P₁ Cells Tok : Type}
    (O : _root_.Desc.K14.Law.ShOpen P₀ P₁ Cells Tok h.shPlan.Q) :
    ∀ (m : Msg2) (j t : Nat), j < (P5J.F0T o Zp Np cF).t₁ →
      P5J.At.arr Zp j t ≠ P5J.At.arr Zp ((_root_.Desc.K14.Law.Sh.nums h.shPlan O).tenant m).1
        ((_root_.Desc.K14.Law.Sh.nums h.shPlan O).tenant m).2 := by
  rw [shNums_tenant h O, P5J.L0.arr_at_head h, first_trees_83 h]
  obtain ⟨a, b, c⟩ := tenants_written
  intro m j t hj
  obtain ⟨x1, x2, x3⟩ := written_off j t hj
  cases m
  · rw [a]
    exact x1
  · rw [b]
    exact x2
  · rw [c]
    exact x3

/-- **Nor is it the seat of one.** -/
theorem seat_off_at_head (h : P5J.AtMg o Z D r Zp Np cF) {P₀ P₁ Cells Tok : Type}
    (O : _root_.Desc.K14.Law.ShOpen P₀ P₁ Cells Tok h.shPlan.Q) :
    ∀ (m : Msg2) (j t : Nat), j < (P5J.F0T o Zp Np cF).t₁ →
      (_root_.Desc.K14.Law.Sh.nums h.shPlan O).tenant m ≠ (j, t) := by
  rw [shNums_tenant h O, first_trees_83 h]
  obtain ⟨a, b, c⟩ := tenants_written
  intro m j t hj e
  cases m
  · rw [a] at e
    have e1 : 83 = j := congrArg Prod.fst e
    omega
  · rw [b] at e
    have e1 : 84 = j := congrArg Prod.fst e
    omega
  · rw [c] at e
    have e1 : 85 = j := congrArg Prod.fst e
    omega

end ProofFile.Honest.K14

#print axioms ProofFile.Honest.K14.sharedNos_apart
#print axioms ProofFile.Honest.K14.firstNos_off
#print axioms ProofFile.Honest.K14.firstNos_bent
#print axioms ProofFile.Honest.K14.arrOf_or
#print axioms ProofFile.Honest.K14.written_off
#print axioms ProofFile.Honest.K14.written_inj
#print axioms ProofFile.Honest.K14.first_trees_83
#print axioms ProofFile.Honest.K14.shNums_tenant
#print axioms ProofFile.Honest.K14.harr_at_head
#print axioms ProofFile.Honest.K14.off_at_head
#print axioms ProofFile.Honest.K14.seat_off_at_head
