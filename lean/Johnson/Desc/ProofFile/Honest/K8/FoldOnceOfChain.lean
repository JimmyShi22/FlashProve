-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K8/FoldOnceOfChain.lean: THE SMALLNESS TEST, THE HONEST PROVER's SIDE,
AT THE STANDS OF THE HONEST THREAD: THE NAMED PREMISE `FoldOnce`
(Johnson/Desc/ProofFile/Honest/K8/CountsFrontK8.lean: at a stand the matrix is counted as drawn
once) AT THE OUTPUT HEAD's SEGMENT: AT A GENERAL THREAD FROM `ChainThread`; AND AT THE FRAME's OWN
THREAD, THAT OF THE FIRST CHAIN's LETTERS AT THE LIBRARY's HEAD, UNDER THE HEAD ALONE. Implications;
none of the library's goals.

  **`foldOnce_of_chain`** the scope · the files read · an opening of the description · its test on
                   its plan · ChainThread T b c Z 24 ⊢ FoldOnce Lk p T b, at every Lk and p
  **`foldOnce_at_head`** the library's head h · the thread's letters, all free ⊢ FoldOnce Lk p
                   (lettersHead …).thread (batchAt P5J.At.links P5J.At.ps 24), at every Lk and p
By: `fold_at_head_seg` (Johnson/Desc/K8/Honest/FoldAtHeadSeg.lean) · `reach_at_stand`
(FrontOfReach.lean) · `chainThread_at_head` (ChainThreadAtHead.lean). `FoldOnce` is spent by
`counts_front` (CountsFrontK8.lean), at the head's sort alone, and carried by the two lemmas of
CountsFrontSeal.lean.
ONE DEVICE STANDS IN IT: `attribute [-instance] Inst.Model.Scl.ref`. TACTICS THAT SEARCH: `omega` on
one line, on a number of a segment.
Limits. NO MEMBER: THAT THE THREAD HOLDS AT ANY RUN, OR THAT A STAND EXISTS, IS NOT SHOWN: where
there is no stand all is idle. THE LIBRARY's HEAD IS A PREMISE OF THE SECOND. Lk and p are free: at
a link or numbers at which no stand exists the sentences are idle. THE FULL SIZE ALONE, and the
format's second hash function alone. No prover stands in it.
Nothing is claimed on completeness, soundness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K8.ChainThreadAtHead
import Johnson.Desc.ProofFile.Honest.K8.CountsFrontK8
import Johnson.Desc.K8.Honest.FoldAtHeadSeg

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K8
open OnBytes OnBytes.Model
open VerifiableInference VerifiableInference.Desc VerifiableInference.Desc.First
open VerifiableInference.Desc.First.K8.Honest
open VerifiableInference.Desc.Sound (MsgT)
open VerifiableInference.Desc.LinkJoin (batchAt)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS)
open ProofFile.Honest.FirstThread (lettersHead WtF Script)
open ProofFile.Honest.K9 (BatStand)
open Johnson.Desc.First.Walk.Tied (Reach)

section
variable {Lk : Link S Claim} {p : Desc.K9.Where}
  {V W X Pb : Type} {Bk : ProverCoinCounts} {T : Thread Bk S Claim V W X Pb} {b : ℕ}
  {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Claim)} {c : Chain S Claim}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- **THE NAMED PREMISE FoldOnce AT THE HEAD's SEGMENT, FROM THE ONE NAMED PREMISE.** -/
theorem foldOnce_of_chain (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (hOk : F.planOk = true)
    (C : ChainThread T b c Z 24) : FoldOnce Lk p T b := by
  intro κ s m En ds y cols s' x z G hSt
  obtain ⟨q, hq⟩ := C.begun κ m
  have r := reach_at_stand (ProofFile.startS Z) q hSt C.len hq C.stored
  rw [C.ft, C.bs, C.border] at r
  obtain ⟨tl, ht, h1⟩ := fold_at_head_seg hS hR O hOk (z := q) (s := s) r
  rw [ht]
  show (tl.foldDrawn == 1) = true
  rw [h1]
  rfl

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
  (w : Local W₀ Rc ProofFile.Inst Tr) {Lk : Link S Claim} {p : Desc.K9.Where}

/-- **FoldOnce AT THE FIRST CHAIN's LETTERS AT THE LIBRARY's HEAD, UNDER THE HEAD ALONE.** -/
theorem foldOnce_at_head :
    FoldOnce Lk p (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread
      (batchAt P5J.At.links P5J.At.ps 24) := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  exact foldOnce_of_chain h.scope h.reads O h.laid.planOk
    (chainThread_at_head h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w (by omega))

end

end ProofFile.Honest.K8

#print axioms ProofFile.Honest.K8.foldOnce_of_chain
#print axioms ProofFile.Honest.K8.foldOnce_at_head
