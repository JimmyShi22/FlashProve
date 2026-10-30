-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Law/Rule/OpenForms.lean: ON THE WRITTEN LISTS: IN FRONT OF EACH OF
THE 25 BATCHINGS EVERY ITEM THAT THE BATCHING CLOSES IS OPEN IN THE FIRST CHAIN's THREAD. At the
full size's list of segments and places (`P5J.At.links`, `P5J.At.ps`, Johnson/P5J/LettersAt.lean):
the thread's open set at a border is `fwdOpen` (Honest/Thread/Thr.lean) of the table's start and
the forward rows (Honest/Thread/FirstRows.lean); the items that a segment's batching closes are the
library's `formsOf` (Johnson/Desc/First/Borders.lean); the batching's border is the library's
`batchAt` (Johnson/Desc/First/Link/Law/K9KindTiedR.lean). Decided by Lean's kernel, as
Law/Rule/LedgerOpen.lean's sentences are. For the premise "hfront" of the authors of K9's and K10's
parts, its first third: before this file a line that is evaluated stood for it
(Honest/Thread/FirstRows.lean), and no lemma ended in "lies in the thread's open set".

  1  `batch_at`   the batching's border is 14 m + 9 at the 24 segments in front of the head's,
     and 347 at the head's
  2  `forms_open`   the sentence on the lists
  3  `pins_open`   so are the segment's three pins
  4  `behind_open`, `behind_owes`   one border on, in front of the member "the runs behind":
     "totalB m" and the pins are open, and the forward row owes "total m" and the pins
  5  `head_opened`, `head_forms_open`, `head_pins_open`, `head_behind`   at the first chain's
     thread at the library's head (`lettersHead`, Honest/Thread/FirstHead.lean); the last: the
     three evaluations that the generic lemmas' record "link m: behind the batching" takes as
     premises (Honest/Law/NoHouse/BehindHead.lean)

BY `decide +kernel` (Lean's kernel evaluates a closed, true sentence on the library's own written
lists): `batch_at`, `forms_open`, `pins_open`, `behind_open`, `behind_owes`, and the control
`forms_control`: in front of the batching "totalB m" is not open yet; behind it the batching's
first form is open no more.

Limits. LISTS ALONE: nothing on what an item says. From an entry of the gatherer's order to its
item, and what the item's sentence is, are the premise's other two thirds: not here. DECIDED AT ONE
VERSION OF THE TABLE AND OF THE LISTS. This file proves nothing about soundness, completeness,
hiding or any other property of the protocol.
-/
import Johnson.Desc.ProofFile.Honest.Thread.FirstHead
import Johnson.Desc.First.Link.Law.K9KindTiedR

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.FirstThread
open VerifiableInference.Desc (Chain Strs Place)
open VerifiableInference.Desc.First (Item ModelPart start formsOf pinsOf)
open VerifiableInference.Desc.LinkJoin (batchAt)
open VerifiableInference.Desc.Sound (MsgT)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS)

set_option maxRecDepth 1000000 in
set_option synthInstance.maxSize 100000 in
set_option synthInstance.maxHeartbeats 2000000 in
theorem batch_at : (∀ m, m < 24 → batchAt P5J.At.links P5J.At.ps m = 14 * m + 9) ∧
    batchAt P5J.At.links P5J.At.ps 24 = 347 := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option synthInstance.maxSize 100000 in
set_option synthInstance.maxHeartbeats 2000000 in
theorem forms_open : ∀ m, m < 25 → ∀ sub ∈ P5J.At.links[m]?, ∀ i ∈ formsOf sub m,
    i ∈ fwdOpen (start P5J.At.links) (FirstRows.rows P5J.At.links P5J.At.ps)
      (batchAt P5J.At.links P5J.At.ps m) := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option synthInstance.maxSize 100000 in
set_option synthInstance.maxHeartbeats 2000000 in
theorem pins_open : ∀ m, m < 25 → ∀ i ∈ pinsOf m,
    i ∈ fwdOpen (start P5J.At.links) (FirstRows.rows P5J.At.links P5J.At.ps)
      (batchAt P5J.At.links P5J.At.ps m) := by
  decide +kernel

/-! ### Behind the batching: in front of the member "the runs behind" -/

set_option maxRecDepth 1000000 in
set_option synthInstance.maxSize 100000 in
set_option synthInstance.maxHeartbeats 2000000 in
theorem behind_open : ∀ m, m < 25 → ∀ i ∈ Item.totalB m :: pinsOf m,
    i ∈ fwdOpen (start P5J.At.links) (FirstRows.rows P5J.At.links P5J.At.ps)
      (batchAt P5J.At.links P5J.At.ps m + 1) := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option synthInstance.maxSize 100000 in
set_option synthInstance.maxHeartbeats 2000000 in
theorem behind_owes : ∀ m, m < 25 →
    (FirstRows.rows P5J.At.links P5J.At.ps (batchAt P5J.At.links P5J.At.ps m + 1)).owes =
      Item.total m :: pinsOf m := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option synthInstance.maxSize 100000 in
set_option synthInstance.maxHeartbeats 2000000 in
theorem forms_control : ∀ m, m < 25 →
    Item.totalB m ∉ fwdOpen (start P5J.At.links) (FirstRows.rows P5J.At.links P5J.At.ps)
      (batchAt P5J.At.links P5J.At.ps m) ∧
    ∀ sub ∈ P5J.At.links[m]?, ∀ i ∈ (formsOf sub m).head?,
      i ∉ fwdOpen (start P5J.At.links) (FirstRows.rows P5J.At.links P5J.At.ps)
        (batchAt P5J.At.links P5J.At.ps m + 1) := by
  decide +kernel

section
variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w : Local W₀ Rc ProofFile.Inst Tr)

theorem head_opened (b : Nat) :
    (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.opened b =
      fwdOpen (start P5J.At.links) (FirstRows.rows P5J.At.links P5J.At.ps) b := rfl

/-- **In front of segment m's batching every item that the batching closes is open in the thread.**
-/
theorem head_forms_open {m : Nat} (hm : m < 25) {sub : ModelPart} (hs : P5J.At.links[m]? = some sub)
    {i : Item} (hi : i ∈ formsOf sub m) :
    i ∈ (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.opened
      (batchAt P5J.At.links P5J.At.ps m) := by
  rw [head_opened]
  exact forms_open m hm sub (by rw [hs]; exact rfl) i hi

theorem head_pins_open {m : Nat} (hm : m < 25) {i : Item} (hi : i ∈ pinsOf m) :
    i ∈ (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.opened
      (batchAt P5J.At.links P5J.At.ps m) := by
  rw [head_opened]
  exact pins_open m hm i hi

/-- The three evaluations on the table that the record "link m: behind the batching" takes as
premises (Honest/Law/NoHouse/BehindHead.lean: howes, hopen, hctxO), at ctx := the segment's pins. -/
theorem head_behind {m : Nat} (hm : m < 25) :
    ((lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.row
      (batchAt P5J.fullLinks P5J.At.ps m + 1)).owes = Item.total m :: pinsOf m ∧
    Item.totalB m ∈ (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.opened
      (batchAt P5J.fullLinks P5J.At.ps m + 1) ∧
    ∀ i ∈ pinsOf m, i ∈ (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.opened
      (batchAt P5J.fullLinks P5J.At.ps m + 1) :=
  ⟨behind_owes m hm, behind_open m hm _ List.mem_cons_self,
    fun i hi => behind_open m hm i (List.mem_cons_of_mem _ hi)⟩

end

end ProofFile.Honest.FirstThread

#print axioms ProofFile.Honest.FirstThread.batch_at
#print axioms ProofFile.Honest.FirstThread.forms_open
#print axioms ProofFile.Honest.FirstThread.pins_open
#print axioms ProofFile.Honest.FirstThread.behind_open
#print axioms ProofFile.Honest.FirstThread.behind_owes
#print axioms ProofFile.Honest.FirstThread.forms_control
#print axioms ProofFile.Honest.FirstThread.head_opened
#print axioms ProofFile.Honest.FirstThread.head_pins_open
#print axioms ProofFile.Honest.FirstThread.head_behind
#print axioms ProofFile.Honest.FirstThread.head_forms_open
