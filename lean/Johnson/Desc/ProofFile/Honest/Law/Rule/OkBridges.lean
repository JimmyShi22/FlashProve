-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Law/Rule/OkBridges.lean: FOUR BRIDGES BENEATH "OkFront" OF THE AUTHORS
OF K9's PART: from the first chain's thread at the library's head (`lettersHead`,
Honest/Thread/FirstHead.lean), at the border in front of a segment's batching, to four facts on the
verifier's state IN THE VERY FORMS THAT THEIR `okFill_lay`, `okFill_att`, `okFill_head` TAKE
(Honest/K9/OkLay.lean, OkAtt.lean, OkHead.lean: not in the sealed library): hB, hL, and at an
attention segment h5 and hpl. Each is a public item's test or sentence at an item that is open
there; which items are open is decided by Lean's kernel on the written lists, as in
Law/Rule/LedgerOpen.lean.

  1  `open_front`, `open_front_att`   ON THE WRITTEN LISTS: in front of each of the 25 batchings
     "ledger m" and "leftOn m" are open; in front of the 12 attention segments' also "K5.okAt" and
     "K5.plain"
  2  `bridge_hB`   a ledger is open, with its sizes
  3  `bridge_hL`   what the lookup on the calls left, in the form that stands at every later
     record
  4  `bridge_h5`, `bridge_hpl`   the attention caller's two tests

The fifth fact (hq: the state is reached) is given by `thrS_rchAt` (Honest/Thread/ReachAtHead.lean);
the sixth (hpart) comes with the batching's own yes, and is left to the authors of K9's part.

BY `decide +kernel` (a closed, true sentence on the library's own written lists, evaluated):
`open_front`, `open_front_att`, and the control that says no, `front_control`: "leftOn 0" stands in
the set neither one border in front of where it is made nor behind the batching, and at a layers'
segment "K5.okAt" does not stand in it.

Limits. THE FULL SIZE ALONE. The library's head has a member at the name under four premises on the
public files (the seal's `head_exists_at_name`, Johnson/P5J/HeadExistsAtName.lean); none of our
files calls it; no member of the head TOGETHER WITH the thread's sentence is shown. FROM `Thr`:
whoever has the thread with what is said hands its first half. Nothing shows that the thread holds
at any run. This file proves nothing about soundness, completeness, hiding or any other property of
the protocol.
-/
import Johnson.Desc.ProofFile.Honest.Thread.HeadForm
import Johnson.Desc.ProofFile.Honest.Thread.FormLawP
import Johnson.Desc.ProofFile.Honest.Law.Rule.LedgerCallers
import Johnson.Desc.ProofFile.Honest.Law.Rule.OpenForms
import Johnson.Desc.First.Link.Law.SizedRides
import Johnson.Desc.First.Att.SeatC

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.FirstThread
open VerifiableInference.Desc (Chain Strs Place)
open VerifiableInference.Desc.First (pubSets leavesName pubAll_more_okAt pubAll_more_plain)
open VerifiableInference.Desc.LinkJoin (batchAt)
open VerifiableInference.Desc.Sound (MsgT)
open VerifiableInference.OnPublicFiles (k3LeftOnItemAt)
open VerifiableInference.Desc.First.Att.P (parCOf)
open H2K5.Door (moreOver9 okThereB plainThereB)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS)

/-! ## 1 On the written lists -/

set_option maxRecDepth 1000000 in
set_option synthInstance.maxSize 100000 in
set_option synthInstance.maxHeartbeats 2000000 in
theorem open_front : ∀ m, m < 25 →
    VerifiableInference.Desc.First.Pub.ledger m ∈ (pubSets ((moreOver9 {}).strike leavesName)
        P5J.At.links P5J.At.ps)[batchAt P5J.At.links P5J.At.ps m]?.getD [] ∧
    VerifiableInference.Desc.First.Pub.leftOn m ∈ (pubSets ((moreOver9 {}).strike leavesName)
        P5J.At.links P5J.At.ps)[batchAt P5J.At.links P5J.At.ps m]?.getD [] := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option synthInstance.maxSize 100000 in
set_option synthInstance.maxHeartbeats 2000000 in
theorem open_front_att : ∀ g, g < 12 →
    VerifiableInference.Desc.First.Pub.more (some (2 * g + 1)) "K5.okAt" ∈
      (pubSets ((moreOver9 {}).strike leavesName) P5J.At.links P5J.At.ps)[batchAt P5J.At.links
          P5J.At.ps (2 * g + 1)]?.getD [] ∧
    VerifiableInference.Desc.First.Pub.more (some (2 * g + 1)) "K5.plain" ∈
      (pubSets ((moreOver9 {}).strike leavesName) P5J.At.links P5J.At.ps)[batchAt P5J.At.links
          P5J.At.ps (2 * g + 1)]?.getD [] := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option synthInstance.maxSize 100000 in
set_option synthInstance.maxHeartbeats 2000000 in
theorem front_control :
    VerifiableInference.Desc.First.Pub.leftOn 0 ∉ (pubSets ((moreOver9 {}).strike leavesName)
        P5J.At.links P5J.At.ps)[4]?.getD [] ∧
    VerifiableInference.Desc.First.Pub.leftOn 0 ∉ (pubSets ((moreOver9 {}).strike leavesName)
        P5J.At.links P5J.At.ps)[10]?.getD [] ∧
    VerifiableInference.Desc.First.Pub.more (some 0) "K5.okAt" ∉
      (pubSets ((moreOver9 {}).strike leavesName) P5J.At.links P5J.At.ps)[batchAt P5J.At.links
          P5J.At.ps 0]?.getD [] := by
  decide +kernel

/-! ## 2 The bridges -/

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

theorem head_sets (b : Nat) :
    ((pubSets (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).mgP.more
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).links
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).ps)[b]?).getD [] =
      (pubSets ((moreOver9 {}).strike leavesName) P5J.At.links P5J.At.ps)[b]?.getD [] := by
  have hm : (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).mgP.more = (moreOver9
      {}).strike leavesName := H2K5.Door.hm_all h
  rw [hm]
  rfl

/-- (hB) **A ledger is open, with its sizes.** -/
theorem bridge_hB {m : Nat} (hm : m < 25) {k : Coins Bk} {s : TS}
    {μ : Mid (Local W₀ Rc ProofFile.Inst Tr) X} {En : Env}
    (hT : Thr (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread (batchAt P5J.At.links
        P5J.At.ps m) k s μ En) :
    ∃ G', s.fork? = some G' ∧ OnBytes.PscRun.Sized G' :=
  (VerifiableInference.Desc.LinkJoin.ledgerOk_iff s).1
    (head_ledger h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hT (m := m)
      (by rw [head_sets]; exact (open_front m hm).1))

/-- (hL) **What the lookup on the calls left.** -/
theorem bridge_hL {m : Nat} (hm : m < 25) {k : Coins Bk} {s : TS}
    {μ : Mid (Local W₀ Rc ProofFile.Inst Tr) X} {En : Env}
    (hT : Thr (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread (batchAt P5J.At.links
        P5J.At.ps m) k s μ En) :
    k3LeftOnItemAt (P5J.At.X Zp) m s :=
  thr_pubP (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w) hT (q := .leftOn m)
    (by rw [head_sets]; exact (open_front m hm).2)

/-- (h5) **The attention caller's first test.** -/
theorem bridge_h5 {g : Nat} (hg : g < 12) {A : OnBytes.Attention.Plan}
    (hA : (P5J.At.X Zp).A[g]? = some A) {k : Coins Bk} {s : TS}
    {μ : Mid (Local W₀ Rc ProofFile.Inst Tr) X} {En : Env}
    (hT : Thr (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread
      (batchAt P5J.At.links P5J.At.ps (2 * g + 1)) k s μ En) :
    okThereB (parCOf A).geo s = true := by
  have e := thr_pub (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w) hT
    (q := .more (some (2 * g + 1)) "K5.okAt") (by rw [head_sets]; exact (open_front_att g hg).1)
  have e0 : (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).mgP.pub = (P5J.mgAtAll h).pub
      := rfl
  have h2 : h.𝔇.pubD.d5.isAtt (2 * g + 1) = true := (sorts_at g hg).2.1
  rw [e0, H2K5.Door.hpubPlus_all h, pubAll_more_okAt h.𝔇.pubD _ (2 * g + 1) h2] at e
  have e2 : (2 * g + 1) / 2 = g := by omega
  have hA' : h.𝔇.pubD.d5.W.A[(2 * g + 1) / 2]? = some A := by
    rw [e2]
    exact hA
  rw [hA'] at e
  exact e

/-- (hpl) **The attention caller's second test.** -/
theorem bridge_hpl {g : Nat} (hg : g < 12) {A : OnBytes.Attention.Plan}
    (hA : (P5J.At.X Zp).A[g]? = some A) {k : Coins Bk} {s : TS}
    {μ : Mid (Local W₀ Rc ProofFile.Inst Tr) X} {En : Env}
    (hT : Thr (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread
      (batchAt P5J.At.links P5J.At.ps (2 * g + 1)) k s μ En) :
    plainThereB (parCOf A).iU3 (parCOf A).nW s = true := by
  have e := thr_pub (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w) hT
    (q := .more (some (2 * g + 1)) "K5.plain") (by rw [head_sets]; exact (open_front_att g hg).2)
  have e0 : (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).mgP.pub = (P5J.mgAtAll h).pub
      := rfl
  have h2 : h.𝔇.pubD.d5.isAtt (2 * g + 1) = true := (sorts_at g hg).2.1
  rw [e0, H2K5.Door.hpubPlus_all h, pubAll_more_plain h.𝔇.pubD _ (2 * g + 1) h2] at e
  have e2 : (2 * g + 1) / 2 = g := by omega
  have hA' : h.𝔇.pubD.d5.W.A[(2 * g + 1) / 2]? = some A := by
    rw [e2]
    exact hA
  rw [hA'] at e
  exact e

end

end ProofFile.Honest.FirstThread

#print axioms ProofFile.Honest.FirstThread.open_front
#print axioms ProofFile.Honest.FirstThread.open_front_att
#print axioms ProofFile.Honest.FirstThread.front_control
#print axioms ProofFile.Honest.FirstThread.head_sets
#print axioms ProofFile.Honest.FirstThread.bridge_hB
#print axioms ProofFile.Honest.FirstThread.bridge_hL
#print axioms ProofFile.Honest.FirstThread.bridge_h5
#print axioms ProofFile.Honest.FirstThread.bridge_hpl
