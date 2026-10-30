-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Law/Rule/LedgerLeft.lean: `LedgerIs` (Law/Rule/TiesFall.lean) IN
FRONT OF THE HEAD's CALLER's MEMBER (border 341), AND A SECOND WAY AT THE 24 OTHER CALLERS': FROM
THE SENTENCE OF A PUBLIC ITEM, NOT FROM ITS TEST. At 341 the two items whose tests say the ledger's
next free slot as a number elsewhere ("callerIn", "lookIn") are not open (Law/Rule/LedgerOpen.lean:
`not_open_head`). But the table's promise also holds, of every open public item, a SENTENCE
(`Meaning.pubP`); the item "left m" is open there, its sentence is "what the lookup on the calls
left" (`k3LeftItemAt`, Johnson/Desc/First/Look/K3LeftItem.lean), and the library's own `left_says`
(Johnson/Desc/Kinds/Law/K6LeftSays.lean) reads off it: the next free number is the lookup's first
slot plus its scalars. The road was pointed out by kind K6's authors.

  1  `open_left`   ON THE WRITTEN LISTS, by Lean's kernel: "left l" is open at 14 l + 4 (l below
     24) and "left 24" at 341
  2  `head_left`   the item's sentence at the head's letters
  3  `left_next`   from the sentence to the number
  4  `ledgerIs_left`, `ledgerIs_k6`   THE STATEMENTS

BY `decide +kernel` (Lean's kernel evaluates a closed, true sentence on the library's own written
lists): `open_left` and its control `left_control`: one border in front of where the item is made,
and one behind where it is dropped, it is not open.

Limits. THE FULL SIZE ALONE. The library's head has a member at the name under four premises on the
public files (the seal's `head_exists_at_name`, Johnson/P5J/HeadExistsAtName.lean); none of our
files calls it; no member of the head TOGETHER WITH the thread's sentence is shown. THE NUMBER IS
THE PLAN's. Two premises on the public parameters: the lookup's place, and its shape. AT 346 (in
front of the merge) no such sentence stands: there the rider of Honest/Law/Rule/LedgerRider.lean
(not in the sealed library) is the candidate. Nothing shows that the thread holds at any run. This
file proves nothing about soundness, completeness, hiding or any other property of the protocol.
-/
import Johnson.Desc.ProofFile.Honest.Thread.FormLawP
import Johnson.Desc.ProofFile.Honest.Law.Rule.LedgerLookups
import Johnson.Desc.Kinds.Law.K6LeftSays

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.FirstThread
open VerifiableInference.Desc (Chain Strs Place)
open VerifiableInference.Desc.First (pubSets leavesName)
open VerifiableInference.Desc.First.Look (placeAt)
open VerifiableInference.Desc.K9 (segAt?)
open VerifiableInference.Desc.Sound (MsgT)
open VerifiableInference.OnPublicFiles (k3LeftItemAt)
open H2K5.Door (moreOver9)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS)

set_option maxRecDepth 1000000 in
set_option synthInstance.maxSize 100000 in
set_option synthInstance.maxHeartbeats 2000000 in
theorem open_left : (∀ l, l < 24 → VerifiableInference.Desc.First.Pub.left l ∈
      (pubSets ((moreOver9 {}).strike leavesName) P5J.At.links P5J.At.ps)[14 * l + 4]?.getD []) ∧
    VerifiableInference.Desc.First.Pub.left 24 ∈ (pubSets ((moreOver9 {}).strike leavesName)
        P5J.At.links P5J.At.ps)[341]?.getD [] := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option synthInstance.maxSize 100000 in
set_option synthInstance.maxHeartbeats 2000000 in
theorem left_control :
    VerifiableInference.Desc.First.Pub.left 24 ∉ (pubSets ((moreOver9 {}).strike leavesName)
        P5J.At.links P5J.At.ps)[340]?.getD [] ∧
    VerifiableInference.Desc.First.Pub.left 24 ∉ (pubSets ((moreOver9 {}).strike leavesName)
        P5J.At.links P5J.At.ps)[342]?.getD [] ∧
    VerifiableInference.Desc.First.Pub.left 0 ∉ (pubSets ((moreOver9 {}).strike leavesName)
        P5J.At.links P5J.At.ps)[3]?.getD [] ∧
    VerifiableInference.Desc.First.Pub.left 0 ∉ (pubSets ((moreOver9 {}).strike leavesName)
        P5J.At.links P5J.At.ps)[5]?.getD [] := by
  decide +kernel

theorem left_next {X : OnBytes.Model.Verify.Public} {l : Nat}
    {p : VerifiableInference.Desc.First.Look.P} {hS : OnBytes.Model.Forest.Shape} {s : TS}
    {a : VerifiableInference.Desc.K9.Part} (hp : placeAt X l false = some p)
    (hs : p.shape = some hS) (hL : k3LeftItemAt X l s) (ha : segAt? s = some a) :
    a.F.next = p.first + OnBytes.Model.Forest.elems hS := by
  obtain ⟨p', hp', L⟩ := hL
  obtain rfl : p = p' := Option.some.inj (hp.symm.trans hp')
  obtain ⟨h', F', g, hs', hF, -, Y, -⟩ :=
    VerifiableInference.Desc.Kinds.Head.Law.left_says p s L
  obtain rfl : hS = h' := Option.some.inj (hs.symm.trans hs')
  have e : F' = a.F := Option.some.inj (hF.symm.trans (seg_fork ha))
  rw [← e]
  exact Y.next

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

theorem head_left (l : Nat) (a : ProofFile.InstPub × TS) :
    (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).mgP.pubP (.left l) a = k3LeftItemAt
        (P5J.At.X Zp) l a.2 := rfl

/-- **Where "left l" is open, the ledger's next free slot is the lookup's first slot plus its
scalars.** -/
theorem ledgerIs_left {b l : Nat} {p : VerifiableInference.Desc.First.Look.P}
    {hS : OnBytes.Model.Forest.Shape}
    (hq : VerifiableInference.Desc.First.Pub.left l ∈ (pubSets ((moreOver9 {}).strike leavesName)
        P5J.At.links P5J.At.ps)[b]?.getD [])
    (hp : placeAt (P5J.At.X Zp) l false = some p) (hs : p.shape = some hS) :
    LedgerIs (Thr (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread b) segAt? (fun a
        => a.F.next)
      (p.first + OnBytes.Model.Forest.elems hS) := by
  intro k s μ En hT a ha
  have hm : (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).mgP.more = (moreOver9
      {}).strike leavesName := H2K5.Door.hm_all h
  have hq' : VerifiableInference.Desc.First.Pub.left l ∈ ((pubSets (lettersHead h H Q test carryX
      item n₁ n₂ b₀ Vd Rd Kp w).mgP.more
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).links
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).ps)[b]?).getD [] := by
    rw [hm]
    exact hq
  have e := thr_pubP (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w) hT hq'
  rw [head_left h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w] at e
  exact left_next hp hs e ha

/-- **In front of the head's caller's member.** -/
theorem ledgerIs_k6 {p : VerifiableInference.Desc.First.Look.P} {hS : OnBytes.Model.Forest.Shape}
    (hp : placeAt (P5J.At.X Zp) 24 false = some p) (hs : p.shape = some hS) :
    LedgerIs (Thr (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread 341) segAt? (fun a
        => a.F.next)
      (p.first + OnBytes.Model.Forest.elems hS) :=
  ledgerIs_left h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w open_left.2 hp hs

end

end ProofFile.Honest.FirstThread

#print axioms ProofFile.Honest.FirstThread.open_left
#print axioms ProofFile.Honest.FirstThread.left_control
#print axioms ProofFile.Honest.FirstThread.left_next
#print axioms ProofFile.Honest.FirstThread.head_left
#print axioms ProofFile.Honest.FirstThread.ledgerIs_left
#print axioms ProofFile.Honest.FirstThread.ledgerIs_k6
