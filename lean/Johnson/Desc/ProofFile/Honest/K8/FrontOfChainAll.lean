-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K8/FrontOfChainAll.lean: THE SMALLNESS TEST, THE HONEST PROVER's SIDE,
AT THE STANDS OF THE HONEST THREAD: THE NAMED PREMISE `FrontAtStandN`
(Johnson/Desc/ProofFile/Honest/K8/RestJoinOk.lean: at a stand, of the state in front: the window of
slots ends inside the ledger's number of slots; the lengths of the vectors of reads are the place's)
AT ALL 25 SEGMENTS: AT A GENERAL THREAD FROM `ChainThread`; AND AT THE FRAME's OWN THREAD, THAT OF
THE FIRST CHAIN's LETTERS AT THE LIBRARY's HEAD, UNDER THE HEAD, AN OPENING OF THE DESCRIPTION AND
ITS TEST ON ITS PLAN. Implications; none of the library's goals.

  `frontAtStandN_of_chain_head` the scope · the files read · an opening of the description · its
                   test on its plan · the built segment number 24 · ChainThread T b c Z 24 ⊢
                   FrontAtStandN Lk p φ Ok (ProofFile.k8NU Bs.G₀ Xl) T b
  **`frontAtStandN_of_chain_all`** the same at l < 25
  **`frontAtStandN_at_head_all`** the library's head h · the thread's letters, all free · an opening
                   of the description at cF · its test on its plan · l < 25 · the built segment Xl ⊢
                   FrontAtStandN Lk p φ Ok (ProofFile.k8NU Bs.G₀ Xl) (lettersHead …).thread (batchAt
                   P5J.At.links P5J.At.ps l), at every Lk, p, φ and Ok
By: `slot_at_head_seg` (Johnson/Desc/K8/Honest/SlotAtHeadSeg.lean) · `lengths_lot_at_batch`
(LengthsAtPlans.lean), which stands at l < 25 · `frontAtStandN_of_chain` (FrontOfChain.lean: l < 24)
· `chainThread_at_head` (ChainThreadAtHead.lean) · `reach_below`
(Johnson/Desc/ProofFile/Honest/Thread/SaidOk.lean), called at its statement.
ONE DEVICE STANDS IN IT: `attribute [-instance] Inst.Model.Scl.ref`. TACTICS THAT SEARCH: `omega` on
two lines, on numbers of segments alone.
Limits. NO MEMBER: THAT THE THREAD HOLDS AT ANY RUN, OR THAT A STAND EXISTS, IS NOT SHOWN: where
there is no stand all is idle. THE LIBRARY's HEAD IS A PREMISE OF THE THIRD. Lk, p, φ and Ok are
free: the promise Ok, which `FrontAtStandN` has in hand, is not spent. THE FULL SIZE ALONE, and the
format's second hash function alone. No prover stands in it.
Nothing is claimed on completeness, soundness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K8.ChainThreadAtHead
import Johnson.Desc.ProofFile.Honest.K8.FrontOfChain
import Johnson.Desc.K8.Honest.SlotAtHeadSeg

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K8
open OnBytes OnBytes.Model OnBytes.Model.HTailF2
open OnBytes.Model.Stages (LinkH)
open VerifiableInference VerifiableInference.Desc VerifiableInference.Desc.First
open VerifiableInference.Desc.First.K8.Honest
open VerifiableInference.Desc.Sound (MsgT)
open VerifiableInference.Desc.LinkJoin (batchAt)
open VerifiableInference.Desc.K9L (Pub9)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS)
open ProofFile.Honest.FirstThread (lettersHead WtF Script)
open ProofFile.Honest.K9 (BatStand)
open Johnson.Desc.First.Walk.Tied (Reach reach_raw)

section
variable {α : Type} {Lk : Link S Claim} {p : Desc.K9.Where} {φ : S → α}
  {Ok : α × Option Pub9 → Prop}
  {V W X Pb : Type} {Bk : ProverCoinCounts} {T : Thread Bk S Claim V W X Pb} {b : ℕ}
  {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Claim)} {c : Chain S Claim}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- **At the head's segment.** -/
theorem frontAtStandN_of_chain_head (hS : VerifierAndGoals.InScope P = true)
    (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (hOk : F.planOk = true)
    {Xl : LinkH} (e3 : Bs.G₀.built[24]? = some Xl)
    (C : ChainThread T b c Z 24) : FrontAtStandN Lk p φ Ok (ProofFile.k8NU Bs.G₀ Xl) T b := by
  intro κ s m En ds y cols s' x z G hSt _ tlS a ht ha
  obtain ⟨q, hq⟩ := C.begun κ m
  have r := reach_below T (ProofFile.startS Z) q C.len hq C.stored hSt.thr
  rw [C.ft, C.bs, C.border] at r
  exact ⟨slot_at_head_seg hS hR O hOk r ht (Desc.K9.get_fork s a ha),
    lengths_lot_at_batch hS hR O (by omega) e3 (reach_raw r) ht⟩

/-- **THE NAMED PREMISE FrontAtStandN, AT THE LOT's OWN LENGTHS, AT ALL 25 SEGMENTS.** -/
theorem frontAtStandN_of_chain_all (hS : VerifierAndGoals.InScope P = true)
    (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (hOk : F.planOk = true)
    {l : ℕ} (hl : l < 25) {Xl : LinkH} (e3 : Bs.G₀.built[l]? = some Xl)
    (C : ChainThread T b c Z l) : FrontAtStandN Lk p φ Ok (ProofFile.k8NU Bs.G₀ Xl) T b := by
  by_cases h24 : l = 24
  · subst h24
    exact frontAtStandN_of_chain_head hS hR O hOk e3 C
  · exact frontAtStandN_of_chain hS hR O hOk (by omega) e3 C

end

section
variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w : Local W₀ Rc ProofFile.Inst Tr)
  {F : FileDescription ProofFile.Inst} {Bs : ProofFile.PureBase} {base : List (Block S Claim)}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat} {Lk : Link S Claim} {p : Desc.K9.Where}

/-- **FrontAtStandN AT THE FIRST CHAIN's LETTERS AT THE LIBRARY's HEAD, AT ALL 25 SEGMENTS.** -/
theorem frontAtStandN_at_head_all {α : Type} {φ : S → α} {Ok : α × Option Pub9 → Prop}
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL F Zp Bs base cF A B) (hOk : F.planOk = true)
    {l : ℕ} (hl : l < 25) {Xl : LinkH} (e3 : Bs.G₀.built[l]? = some Xl) :
    FrontAtStandN Lk p φ Ok (ProofFile.k8NU Bs.G₀ Xl)
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread
      (batchAt P5J.At.links P5J.At.ps l) :=
  frontAtStandN_of_chain_all h.scope h.reads O hOk hl e3
    (chainThread_at_head h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hl)

end

end ProofFile.Honest.K8

#print axioms ProofFile.Honest.K8.frontAtStandN_of_chain_head
#print axioms ProofFile.Honest.K8.frontAtStandN_of_chain_all
#print axioms ProofFile.Honest.K8.frontAtStandN_at_head_all
