-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K1/Law/TieOpenAtDraw.lean: ON THE WRITTEN LISTS: IN FRONT OF EACH OF
THE 25 SEGMENTS' DRAWS THE ITEM "tie l" IS OPEN IN THE FIRST CHAIN's THREAD. At the full size's
lists of segments and places (P5J.At.links, P5J.At.ps): the thread's open set at a border is fwdOpen
(Honest/Thread/Thr.lean) of the table's start and the forward rows (Honest/Thread/FirstRows.lean);
the draw's border is the library's drawAt (Johnson/Desc/First/K8/TiePromise.lean). PUBLIC: closed
lists. Seven theorems; no definition. A TRIAL THAT COUNTS IN NO COLUMN.

- tieOpenB_full, tieBesideB_full, drawB_full: THREE CLOSED TESTS, each an evaluation in Lean's
    kernel (decide +kernel; no compiled code), over all 25 segments: "tie l" is open at drawAt l ·
    THE CONTROL: it is open neither one border in front (drawAt l - 1) nor one behind (drawAt l + 1)
    · drawAt l is one more than the number of the segment's "reads" (K1.noL l false).
- tie_open_at_draw, tie_shut_beside, draw_behind_reads: what the tests' yes gives, at each l < 25.
- head_tie_open: at the first chain's thread at the library's head (lettersHead,
    Honest/Thread/FirstHead.lean): Item.tie l lies in thread.opened (drawAt l): by ProofFile's head_opened
    (Honest/Law/Rule/OpenForms.lean), which is rfl. thread.opened is the thread's set of open ITEMS:
    another thing than the field "opened" (opened columns) that the frame's next issue brings.

Who calls. The authors of the kind K8, for their field "tie" at a stand at the draw's number: asked
for by them. By its authors' word twoAt_full_reads (AtFullSide/K8/TwoAtFullReads.lean) hands
 head_tie_open to its premise that the item is open.

Whose form. THE FORM FOLLOWS TWO OTHER HOUSES' FILES. A closed Boolean test over all 25, decided by
the kernel, and beside it a law that says what the test's yes gives: so the sealed k8PinsB_full and
k8_pins_open (Johnson/P1K8R/TableAtK8.lean). The open set's term, the three options in front of the
two heavy tests, a control one border off, head_tie_open's letters (OpenForms.lean's "variable"
lines, written out) and its proof's two steps: so ProofFile's forms_open, pins_open, forms_control and
head_pins_open (OpenForms.lean).

Kin. ProofFile's forms_open, pins_open (OpenForms.lean): the like at the batchings' borders, at other
items. The sealed k8_pins_open (Johnson/P1K8R/TableAtK8.lean): three pins open in front of the draw,
at the table's openSets, not at fwdOpen; k8_row_full (the same file) and row_at_draw_full
(Johnson/Desc/First/K8/RowAtDraw.lean): the table's row at the draw has "tie l" among its ins. Our
segRow_reads (FormsFwd.lean): the table's row at the reads has it among its outs; our owed_reads
(OwedAtMembers.lean): whatever the forward row at the reads owes lies in a list that holds "tie l",
or it is "pin l 0" or "constr l small" and is open in front of that member.

Limits. LISTS ALONE: nothing on what the item says, nor that it holds at any stand. That it is open
at no border further off than one is not said here. DECIDED AT ONE VERSION OF THE TABLE AND OF THE
LISTS. THE FULL SIZE ALONE. The head is a hypothesis of head_tie_open, which spends nothing of it
but the letters. IT STANDS ABOVE FILES OF L25's THAT TURN WITH THE FRAME's NEXT ISSUE
(Honest/Frame.lean and Honest/Law/Rule/WalkLaw.lean among them); by a walk by text it does not stand
above Honest/Law/Rule/Real.lean. A walk by text along the lines of imports rings once in its
closure: Honest/Thread/First.lean; its own code names no measure. Nothing on soundness, on
completeness or on any other property.
Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.ProofFile.Honest.Law.Rule.OpenForms
import Johnson.Desc.First.K8.TiePromise
import Johnson.Desc.K1.Law.LaterOne

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K1
open VerifiableInference.Desc
open VerifiableInference.Desc (Chain Strs Place)
open VerifiableInference.Desc.First (Item start)
open VerifiableInference.Desc.First.K8 (drawAt)
open VerifiableInference.Desc.Sound (MsgT)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS)
open ProofFile.Honest.FirstThread

set_option maxRecDepth 1000000 in
set_option synthInstance.maxSize 100000 in
set_option synthInstance.maxHeartbeats 2000000 in
/-- **THE TEST: "tie l" IS OPEN AT THE DRAW's BORDER**, at all 25 segments. -/
theorem tieOpenB_full : ((List.range 25).all fun l =>
    decide (Item.tie l ∈ fwdOpen (start P5J.At.links) (FirstRows.rows P5J.At.links P5J.At.ps)
      (drawAt l))) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option synthInstance.maxSize 100000 in
set_option synthInstance.maxHeartbeats 2000000 in
/-- THE CONTROL: one border in front and one behind it is not open. -/
theorem tieBesideB_full : ((List.range 25).all fun l =>
    decide (Item.tie l ∉ fwdOpen (start P5J.At.links) (FirstRows.rows P5J.At.links P5J.At.ps)
      (drawAt l - 1)) &&
    decide (Item.tie l ∉ fwdOpen (start P5J.At.links) (FirstRows.rows P5J.At.links P5J.At.ps)
      (drawAt l + 1))) = true := by
  decide +kernel

/-- The draw's border is one more than the number of the segment's "reads". -/
theorem drawB_full :
    ((List.range 25).all fun l => decide (drawAt l = K1.noL l false + 1)) = true := by
  decide +kernel

/-- **AT EACH OF THE 25: "tie l" IS OPEN IN FRONT OF THE DRAW.** -/
theorem tie_open_at_draw {l : ℕ} (hl : l < 25) :
    Item.tie l ∈ fwdOpen (start P5J.At.links) (FirstRows.rows P5J.At.links P5J.At.ps) (drawAt l) :=
  of_decide_eq_true (List.all_eq_true.1 tieOpenB_full l (List.mem_range.2 hl))

/-- It is open neither one border in front nor one behind. -/
theorem tie_shut_beside {l : ℕ} (hl : l < 25) :
    Item.tie l ∉ fwdOpen (start P5J.At.links) (FirstRows.rows P5J.At.links P5J.At.ps)
      (drawAt l - 1) ∧
    Item.tie l ∉ fwdOpen (start P5J.At.links) (FirstRows.rows P5J.At.links P5J.At.ps)
      (drawAt l + 1) := by
  have e := List.all_eq_true.1 tieBesideB_full l (List.mem_range.2 hl)
  rw [Bool.and_eq_true] at e
  exact ⟨of_decide_eq_true e.1, of_decide_eq_true e.2⟩

/-- What drawB_full's yes gives: at each of the 25 the draw's border is one more than the number of
the segment's "reads". -/
theorem draw_behind_reads {l : ℕ} (hl : l < 25) : drawAt l = K1.noL l false + 1 :=
  of_decide_eq_true (List.all_eq_true.1 drawB_full l (List.mem_range.2 hl))

/-- **AT THE HEAD's THREAD.** The head is a premise; the proof spends its letters alone. -/
theorem head_tie_open {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
    {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
    (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X : Type}
    (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
    (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
    (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
    (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
    (w : Local W₀ Rc ProofFile.Inst Tr) {l : ℕ} (hl : l < 25) :
    Item.tie l ∈ (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.opened
      (drawAt l) := by
  rw [head_opened]
  exact tie_open_at_draw hl

end ProofFile.Honest.K1

#print axioms ProofFile.Honest.K1.tieOpenB_full
#print axioms ProofFile.Honest.K1.tieBesideB_full
#print axioms ProofFile.Honest.K1.drawB_full
#print axioms ProofFile.Honest.K1.tie_open_at_draw
#print axioms ProofFile.Honest.K1.tie_shut_beside
#print axioms ProofFile.Honest.K1.draw_behind_reads
#print axioms ProofFile.Honest.K1.head_tie_open
