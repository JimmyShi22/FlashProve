-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Loose/H2K12/ReachedOfPins.lean:
THE LAW OF THE PROXIMITY TEST (the kind K12) ON THE PROOF FILE's
FIRST CHAIN: THE HEAD WITH THE FACTS ON EVERY REACHED STATE (AtMgR, Johnson/P5J/AtMgR.lean), AT THE
HEAD's OWN CONDITION "REACHED", FROM THE HEAD AND TWO ENTRY TESTS' ACCEPTS: two of the three
premises of reached_at_head (H2K12/ReachedAtHead.lean) are paid here. One
definition, statements and proofs.
Main names:
  msgs_written     under the four equations that the entry test madeRow gives (Written354,
                   H2K12/ClosedOfPins354.lean) the list of the planner's first
                   chain's oracle messages' shapes is the written seats' list of shapes (msgs_full,
                   rise_full there).
  startW, start_written, start_written_no   the body of the test startB
                   (Johnson/Top/H0/Fill/D1At.lean) at the written shapes: by Lean's kernel it
                   accepts at the number 4; at the numbers 3, 5 and 199 it rejects.
  startB_at        so startB accepts at the index masks' message's number in the table's numbers
                   (indexNo_at, H2K12/ClosedAtHead354.lean).
  laid_some        the laying of the first chain's listed places returns (laid_full,
                   H2K12/ClosedOfPins354.lean).
  reached_of_pins  the field reached of K12Rest₆ (H2K12/K12LeftOfRest.lean),
                   to the letter, at whichever L the laying returns.
  reached_some     there is such an L.
PREMISES THAT STAY. The head h · W : Written354 Zp with hy : madeRow Zp = true (W follows from hy
where the value is laid: written354_of_pins, H2K12/ClosedOfPins354.lean) · hc : the first chain's
cut is the written cut (cut_of_row from the entry test cutRow,
Johnson/Desc/Ok/PlanWritten/CutTestLaws.lean).
Limits. (1) EVERY FACT ON A REACHED STATE IS ANOTHER FILE's THEOREM, called through
reached_at_head. (2) THE WRITTEN CUT RESTS ON PRINTS OF LEAN's EVALUATOR
(Johnson/Desc/First/CutWritten.lean, its own Limits): startB_at and what follows inherit that. (3)
A MEMBER OF THE HEAD IS PROVED AT storedPublicFiles AND zGap ALONE (AT secondHashFunction; SIDE LIBRARY AtFullSide/Top/);
that W, hy and hc hold at any public files is no theorem. (4) At the
concrete second hash function alone; the full size alone. No soundness statement. Nothing on hiding.

-/
import Johnson.Desc.ReqLit.Full
import Johnson.Top.H0.Fill.D1At
import Johnson.Loose.H2K12.ClosedOfPins354
import Johnson.Loose.H2K12.ClosedAtHead354
import Johnson.Loose.H2K12.ReachedAtHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace H2K12

/-- Under the four equations the list of the first chain's oracle messages' shapes is the written
seats' list of shapes. -/
theorem msgs_written {Zp : ProofFile.Pub} (W : Written354 Zp) :
    VerifiableInference.Desc.K12.Door.msgsOfChain Zp.made.proof.1 = P5T.psFull.map (·.shape) := by
  unfold VerifiableInference.Desc.K12.Door.msgsOfChain
  rw [W.sends, List.mergeSort_of_pairwise rise_full]
  exact msgs_full

/-- The body of the test startB at the written shapes, at the number ix. -/
def startW (ix : ℕ) : Bool :=
  match (P5T.psFull.map (·.shape))[ix]? with
  | some sh => VerifiableInference.Desc.ReqLit.shapeFull.atStart.map (·.shape) == [sh]
  | none => false

set_option maxRecDepth 1000000 in
/-- By the kernel: at the number 4 it accepts. -/
theorem start_written : startW 4 = true := by decide +kernel

set_option maxRecDepth 1000000 in
/-- The line can fail: at the numbers beside it, and behind the list's end, it rejects. -/
theorem start_written_no : startW 5 = false ∧ startW 3 = false ∧ startW 199 = false := by
  decide +kernel

/-- **startB accepts at the index masks' message's number in the table's numbers.** -/
theorem startB_at {Zp : ProofFile.Pub} {cF : VerifiableInference.Desc.Chain P5J.TS ProofFile.Cl}
    (W : Written354 Zp) (hc : VerifiableInference.PlanWritten.cutOf cF.blocksInOrder =
      VerifiableInference.PlanWritten.cutFirstFull) :
    VerifiableInference.Desc.First.FillP1.startB Zp
      (VerifiableInference.Desc.K12.Door.msgsOfChain Zp.made.proof.1)
      (P5J.At.N Zp cF).indexNo = true := by
  unfold VerifiableInference.Desc.First.FillP1.startB
  rw [msgs_written W, indexNo_at W hc, W.shape]
  exact start_written

/-- **The laying of the first chain's listed places returns.** -/
theorem laid_some {Zp : ProofFile.Pub} (W : Written354 Zp) : ∃ L, P5J.At.laid? Zp = some L := by
  have e : VerifiableInference.Desc.K12.Door.laidAtCodes Zp.first.codes Zp.made.proof.1 =
      VerifiableInference.Desc.K12.Door.laidOf Johnson.G.codesFull2 noticesFull := by
    unfold VerifiableInference.Desc.K12.Door.laidAtCodes
    rw [W.codes, W.sends, List.mergeSort_of_pairwise rise_full]
    rfl
  obtain ⟨L, hL, _⟩ := Option.map_eq_some_iff.1 laid_full
  exact ⟨L, e.trans hL⟩

section
variable {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : VerifiableInference.Desc.Chain P5J.TS ProofFile.Cl}
  {x : VerifiableInference.Desc.First.Look.Place}

/-- **The head with the facts on every reached state, from the head and the two entry tests'
accepts**, at whichever L the laying returns. -/
theorem reached_of_pins (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (W : Written354 Zp)
    (hy : VerifiableInference.PlanWritten.madeRow Zp = true)
    (hc : VerifiableInference.PlanWritten.cutOf cF.blocksInOrder =
      VerifiableInference.PlanWritten.cutFirstFull)
    {L : VerifiableInference.Desc.K12.Door.Laid} (hl : P5J.At.laid? Zp = some L) :
    P5J.AtMgR OnBytes.secondHashFunction Z D r Zp Np cF h.toAtMg.rch (fun a => a.1) L :=
  reached_at_head h hl (startB_at W hc) hy

/-- There is such an L. -/
theorem reached_some (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (W : Written354 Zp)
    (hy : VerifiableInference.PlanWritten.madeRow Zp = true)
    (hc : VerifiableInference.PlanWritten.cutOf cF.blocksInOrder =
      VerifiableInference.PlanWritten.cutFirstFull) :
    ∃ L, P5J.AtMgR OnBytes.secondHashFunction Z D r Zp Np cF h.toAtMg.rch (fun a => a.1) L := by
  obtain ⟨L, hl⟩ := laid_some W
  exact ⟨L, reached_of_pins h W hy hc hl⟩

end

end H2K12

#print axioms H2K12.msgs_written
#print axioms H2K12.start_written
#print axioms H2K12.start_written_no
#print axioms H2K12.startB_at
#print axioms H2K12.laid_some
#print axioms H2K12.reached_of_pins
#print axioms H2K12.reached_some
