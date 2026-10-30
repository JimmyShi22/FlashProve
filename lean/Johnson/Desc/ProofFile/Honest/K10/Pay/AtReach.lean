-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K10/Pay/AtReach.lean: the facts that the laws on the closing of a segment (K10) take from
"reached", at the states that the first chain's own blocks reach from its own start, under the library's head
(`P5J.AtMgA`, at the older hash). No thread and no prover is named.

  `foldFacts_reach`   the 26 fields of `FoldFacts` (Johnson/Desc/First/FoldFacts.lean) at "reached by the blocks' own steps"
  `facts_reached`     five of them at a state without a mark of failure: the statement is in order; its codes are the
                    head's; the live frame's shape is the head's; the live frame's groups are those of its shape; the
                    messages' shapes are the first of the chain's listed shapes
  `link_lt`           a link whose closing's number lies inside the chain is one of the 25
  `shapes_reached`    at the border in front of a closing: the group that the record's frame names holds the written
                    list's members (`ShapesAre`)

Limits. Whether the head can be had at any files is not shown here. The full size and the older hash alone.
-/
import Johnson.Desc.ProofFile.Honest.K10.Xch.Mask
import Johnson.Desc.ProofFile.Honest.K10.Xch.BaseAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K10
open VerifiableInference.Desc
open VerifiableInference.Desc.First (FoldFacts)
open VerifiableInference.Desc.First.Close (ShapesAre kbAt noK10)
open VerifiableInference.Desc.K12.Door (atFirstShapes msgsOfChain)
open VerifiableInference.Desc.ReqLit (shapeFull)
open Johnson.G (linksFullLit)
open Johnson.Desc.First.Walk.Tied (Reach)
open OnBytes.Means (InOrder)
open OnBytes.Maker (WholeD)
open P5J (AtMg AtMgA TS)
open ProofFile.Honest.FirstThread

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **`FoldFacts` at what the chain's own blocks reach.** -/
theorem foldFacts_reach (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) :
    FoldFacts (fun b (a : ProofFile.InstPub × TS) => Reach 0 cF.blocksInOrder (ProofFile.startS Zp) b a) (fun a => a)
      (P5J.At.foldD Zp cF VerifiableInference.Desc.K13.Law.LFull) P5J.At.reqW P5J.At.links P5J.At.ps :=
  foldFacts_raw h.toAtMg _ _ (fun _ _ hr => hr) (P5J.laid_at_head h.toAtMg) (P5J.startB_at_head h.toAtMg)
    (P5J.sendsB_of_madeRow h.toAtMg (P5J.madeRow_at_head h.toAtMg))

/-- Five facts at a reached state without a mark of failure. -/
theorem facts_reached (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {b : Nat} {z : ProofFile.InstPub} {s : TS}
    (hr : Reach 0 cF.blocksInOrder (ProofFile.startS Zp) b (z, s)) (hf : s.failed = none) :
    InOrder s.st ∧ s.st.codes = P5J.At.cs Zp ∧ s.live.frame.shape = P5J.At.shape Zp ∧
      s.live.frame.groups = OnBytes.reqGroups s.live.frame.shape ∧
      atFirstShapes (msgsOfChain Zp.made.proof.1) s = true := by
  have FF := foldFacts_reach h
  exact ⟨(OnBytes.Means.tidy4B_iff.1 (FF.tidy b (z, s) hr hf)).inOrder, FF.codes b (z, s) hr hf,
    FF.liveShape b (z, s) hr hf, FF.liveGroups b (z, s) hr hf, FF.msgShapes b (z, s) hr hf⟩

/-- A link whose closing's number lies inside the chain is one of the 25. -/
theorem link_lt (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {l : Nat}
    (hlt : 14 * l + IM.nAt l + 5 < cF.blocksInOrder.length) : l < 25 := by
  obtain ⟨Bs, base, O⟩ := h.toAtMg.laid.opened
  rw [Meaning.K2.flat_358 h.toAtMg.scope O] at hlt
  have h7 : 7 ≤ IM.nAt l := by
    unfold IM.nAt
    split <;> omega
  omega

/-- **In front of a closing the group that the record's frame names holds the written list's members.** -/
theorem shapes_reached (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {l : Nat} (hl : l < 25) {z : ProofFile.InstPub}
    {s : TS} (hr : Reach 0 cF.blocksInOrder (ProofFile.startS Zp) (14 * l + IM.nAt l + 5) (z, s)) (hf : s.failed = none) :
    ∀ G, (K9.recOf s).st.groups[(K9.recOf s).frame.group]? = some G →
      ShapesAre (K9.recOf s).st G (linksFullLit.getD l []) (kbAt shapeFull l (linksFullLit.getD l []))
        (noK10 (P5J.At.seats Zp) (linksFullLit.getD l []) (P5J.At.pseats Zp) l) := by
  intro G hG
  obtain ⟨hI, -, -, -, hM⟩ := facts_reached h hr hf
  exact hinge_raw_all h.toAtMg hl hr hI hM G hG

end ProofFile.Honest.K10

#print axioms ProofFile.Honest.K10.foldFacts_reach
#print axioms ProofFile.Honest.K10.facts_reached
#print axioms ProofFile.Honest.K10.link_lt
#print axioms ProofFile.Honest.K10.shapes_reached
