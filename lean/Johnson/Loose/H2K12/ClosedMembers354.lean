-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Loose/H2K12/ClosedMembers354.lean:
THE LAW OF THE PROXIMITY TEST (the kind K12) ON
THE PROOF FILE's FIRST CHAIN: TWO CLOSED TESTS OF THE TABLE ON ITS NUMBERS that K12's files' ties at
sub-protocol number 354 take as premises, at the full size's written values. Statements and proofs.
  laysNodup_told  the table's test "no two of the components that a row lays are one" (laysNodup,
                  Johnson/Desc/First/Borders.lean) reads nothing of what withRows
                  (Johnson/Desc/First/RowsAtPlan.lean) and withTold
                  (Johnson/Desc/First/BookNumbers.lean) lay over the numbers.
  laysOnce_full   the test at the written seats and the core of the numbers (seatsAllFull, N0Full,
                  Johnson/P5T/PlanSeatsFull.lean): decided by the kernel. laysOnce_full_no: it can
                  fail: where every seat has the number 0 it does. (That a test can fail does not
                  show that the premises below can be met.)
  laysOnce_of     THE TEST AT THE COMPUTED TERMS, where the two lists of seats off the list of
                  rounds are the written ones.
  rides_of_open   an item of the table's list of open items at a border is open there in the chain
                  of promises' own sense (openIsList, openL_iff_openSets,
                  Johnson/Desc/Sound/SpineList.lean).
  clearB_of_riders   "at no sub-protocol does an item that rides read a component that the row lays"
                  (RidersClearQ, Johnson/Desc/Sound/BordersSides.lean) gives K12's files' test at
                  one number (Rid354.clearB, H2K12/Rides354.lean), where the
                  stored table's pin and the index masks' pin ride there.
  clear_354_of_riders   at the written lists and number 354: they do: two lines by the kernel.
Limits. (1) hP and hA (the lists of seats are the written ones) are premises: their payer from the
pins on the written sendings is typed in another of K12's files. (2) RidersClearQ is a premise,
owed by other files, which are to show it at the one head: clear_354_of_riders RENAMES A DEBT, IT
PAYS NONE. (3) The full size alone. No soundness statement. Nothing on hiding.

-/
import Johnson.P5T.PlanSeatsFull
import Johnson.Desc.First.BookNumbers
import Johnson.Desc.First.RowsAtPlan
import Johnson.Loose.H2K12.Rides354

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace H2K12

open VerifiableInference.Desc (Place)
open VerifiableInference.Desc.First (ModelPart Item Numbers Comp laysNodup flatPlacesOf)
open VerifiableInference.Desc.Sound (linksFull)

/-! ## 1 No two of the components that a row lays are one -/

/-- The test reads nothing of what is laid over the core of the numbers. -/
theorem laysNodup_told (arr : ℕ → ℕ → ℕ) (N : Numbers) (sh : OnBytes.Params.ReqShape) (g : ℕ → ℕ)
    (n : ℕ) (ps' : List Place) (told : List (List VerifiableInference.Desc.Oracle))
    (links : List ModelPart) (ps : List Place) :
    laysNodup arr ((N.withRows sh g n).withTold ps' told) links ps = laysNodup arr N links ps :=
  rfl

set_option maxRecDepth 1000000 in
/-- By the kernel: the test at the written seats and the core of the numbers. -/
theorem laysOnce_full : laysNodup (P5T.arrOf P5T.seatsAllFull) P5T.N0Full linksFull
    (flatPlacesOf linksFull true) = true := by decide +kernel

set_option maxRecDepth 1000000 in
/-- The test can fail: where every seat has the number 0. -/
theorem laysOnce_full_no : laysNodup (fun _ _ => 0) P5T.N0Full linksFull
    (flatPlacesOf linksFull true) = false := by decide +kernel

/-- **THE TEST AT THE COMPUTED TERMS.** -/
theorem laysOnce_of {Zp : ProofFile.Pub} (hP : P5T.planSeats Zp Zp.D.1 = P5T.psFull)
    (hA : P5T.planSeatsAll Zp Zp.D = P5T.seatsAllFull) (sh : OnBytes.Params.ReqShape) (g : ℕ → ℕ)
    (n : ℕ) (ps' : List Place) (told : List (List VerifiableInference.Desc.Oracle)) :
    laysNodup (P5T.arrOf (P5T.planSeatsAll Zp Zp.D))
      (((P5T.numbersOf (P5T.planSeats Zp Zp.D.1)).withRows sh g n).withTold ps' told) linksFull
      (flatPlacesOf linksFull true) = true := by
  rw [laysNodup_told, hP, hA]
  exact laysOnce_full

/-! ## 2 What the row at 354 lays is read by no rider -/

/-- An item of the table's list of open items at a border is open there. -/
theorem rides_of_open (links : List ModelPart) (ps : List Place) (k : ℕ) (i : Item)
    (hro : VerifiableInference.Desc.First.readsOpen links ps
      (VerifiableInference.Desc.First.start links) = true)
    (hra : VerifiableInference.Desc.Sound.rowsApart links ps = true) (hk : k ≤ ps.length)
    (ho : i ∈ (VerifiableInference.Desc.First.openSets links ps
      (VerifiableInference.Desc.First.start links))[k]?.getD []) :
    VerifiableInference.Desc.Sound.openAfter (VerifiableInference.Desc.Sound.insQ links ps)
      (VerifiableInference.Desc.Sound.outsQ links ps)
      (· ∈ VerifiableInference.Desc.First.start links) k i :=
  (VerifiableInference.Desc.Sound.openIsList Item (VerifiableInference.Desc.Sound.insL links ps)
    (VerifiableInference.Desc.Sound.outsL links ps) (VerifiableInference.Desc.First.start links) k
    i).2 ((VerifiableInference.Desc.Sound.openL_iff_openSets links ps
      (VerifiableInference.Desc.First.start links) hro hra
      (List.mem_append_left _ List.mem_cons_self) k hk i).2 ho)

/-- **The rule's premise at every number gives K12's files' test at one.** -/
theorem clearB_of_riders (arr : ℕ → ℕ → ℕ) (N : Numbers) (links : List ModelPart) (ps : List Place)
    (k : ℕ) (hc : VerifiableInference.Desc.Sound.RidersClearQ arr N links ps)
    (hW : VerifiableInference.Desc.Sound.openAfter (VerifiableInference.Desc.Sound.insQ links ps)
      (VerifiableInference.Desc.Sound.outsQ links ps)
      (· ∈ VerifiableInference.Desc.First.start links) k .pinW)
    (hW' : ¬ VerifiableInference.Desc.Sound.insQ links ps k .pinW)
    (hI : VerifiableInference.Desc.Sound.openAfter (VerifiableInference.Desc.Sound.insQ links ps)
      (VerifiableInference.Desc.Sound.outsQ links ps)
      (· ∈ VerifiableInference.Desc.First.start links) k .pinI)
    (hI' : ¬ VerifiableInference.Desc.Sound.insQ links ps k .pinI) :
    Rid354.clearB arr N links ps k = true := by
  have a := hc k .pinW hW hW' .cells (by simp [Item.reads])
  have b := hc k .pinI hI hI' (.msg (arr N.index.1 N.index.2)) (by simp [Item.reads, Item.tenants])
  have c := hc k .pinI hI hI' (.pad N.index.1 N.index.2) (by simp [Item.reads, Item.tenants])
  unfold Rid354.clearB
  simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true, Bool.not_eq_true',
    List.contains_eq_mem, decide_eq_false_iff_not]
  exact ⟨a, b, c⟩

set_option maxRecDepth 1000000 in
/-- By the kernel: at the written lists the two pins are open in front of number 354. -/
theorem pins_open_written : Item.pinW ∈ (VerifiableInference.Desc.First.openSets linksFull
      (flatPlacesOf linksFull true) (VerifiableInference.Desc.First.start linksFull))[354]?.getD []
    ∧ Item.pinI ∈ (VerifiableInference.Desc.First.openSets linksFull
      (flatPlacesOf linksFull true)
      (VerifiableInference.Desc.First.start linksFull))[354]?.getD [] := by decide +kernel

/-- By the kernel: the row at the test's place neither closes nor reads them. -/
theorem pins_not_in_written : Item.pinW ∉ (VerifiableInference.Desc.First.rowOf linksFull
      Rid354.pK).ins ++ (VerifiableInference.Desc.First.rowOf linksFull Rid354.pK).ctx ++
      [Item.unmarked] ∧
    Item.pinI ∉ (VerifiableInference.Desc.First.rowOf linksFull Rid354.pK).ins ++
      (VerifiableInference.Desc.First.rowOf linksFull Rid354.pK).ctx ++ [Item.unmarked] := by
  decide +kernel

private theorem not_ins_written (i : Item)
    (h : i ∉ (VerifiableInference.Desc.First.rowOf linksFull Rid354.pK).ins ++
      (VerifiableInference.Desc.First.rowOf linksFull Rid354.pK).ctx ++ [Item.unmarked]) :
    ¬ VerifiableInference.Desc.Sound.insQ linksFull (flatPlacesOf linksFull true) 354 i := by
  intro hi
  apply h
  have h2 : i ∈ (VerifiableInference.Desc.Sound.rowQ linksFull (flatPlacesOf linksFull true)
      354).ins ++ (VerifiableInference.Desc.Sound.rowQ linksFull (flatPlacesOf linksFull true)
      354).ctx ++ [.unmarked] := hi
  unfold VerifiableInference.Desc.Sound.rowQ at h2
  rw [Rid354.place_written] at h2
  exact h2

/-- **K12's FILES' TEST AT THE WRITTEN LISTS AND NUMBER 354, FROM THE RULE's PREMISE.** -/
theorem clear_354_of_riders (arr : ℕ → ℕ → ℕ) (N : Numbers)
    (hc : VerifiableInference.Desc.Sound.RidersClearQ arr N linksFull
      (flatPlacesOf linksFull true)) :
    Rid354.clearB arr N linksFull (flatPlacesOf linksFull true) 354 = true :=
  have hk : 354 ≤ (flatPlacesOf linksFull true).length :=
    Nat.le_of_lt (List.getElem?_eq_some_iff.1 Rid354.place_written).1
  clearB_of_riders arr N linksFull _ 354 hc
    (rides_of_open _ _ 354 _ Rid354.readsOpen_written Rid354.rowsApart_written hk
      pins_open_written.1) (not_ins_written _ pins_not_in_written.1)
    (rides_of_open _ _ 354 _ Rid354.readsOpen_written Rid354.rowsApart_written hk
      pins_open_written.2) (not_ins_written _ pins_not_in_written.2)

end H2K12

#print axioms H2K12.laysNodup_told
#print axioms H2K12.laysOnce_full
#print axioms H2K12.laysOnce_full_no
#print axioms H2K12.laysOnce_of
#print axioms H2K12.rides_of_open
#print axioms H2K12.clearB_of_riders
#print axioms H2K12.pins_open_written
#print axioms H2K12.pins_not_in_written
#print axioms H2K12.clear_354_of_riders
