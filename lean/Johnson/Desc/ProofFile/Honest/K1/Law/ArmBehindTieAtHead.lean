-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K1/Law/ArmBehindTieAtHead.lean: THE KIND K1's SHARE AT THE ITEMS
"forms": ITS HEAVY PREMISE ArmBehindTieS (Honest/K1/Law/FormsShare.lean: behind the pair, the
member's step AND THE TIE AT THAT WITNESS, the committed cell is its stated function) AT THE FIRST
CHAIN's THREAD AT THE LIBRARY's HEAD, AT THE READS OF EACH OF THE 25 LINKS. One theorem; no
definition.

This letter is for the honest run's own forms alone: no statement on any other party may take it.
NEVER ON SOUNDNESS's ROAD: it stands over laws at the
meaning "honest", at which the clauses noColl, shown and decodes are True by definition: such a law
may stand beneath statements on completeness or zero knowledge only, never beneath a statement on
soundness.

  - armBehindTieS_head: UNDER h (the library's head: A HYPOTHESIS): at lettersHead, at every family
    Said that gives SaidOk (hSaid), l < 25, and an item formsT l j n that the reads' row takes in
    (hrun): ArmBehindTieS, at the forms' letters of the head's own data and the one stated function
    uBySort h.𝔇.uL h.𝔇.uA h.𝔇.uH.

How. arm_reach_head_b (Honest/K1/Twin/ArmReachHeadB.lean), fed from the pair and the step: the
block's yes and the link's built entry: yesOf_reads_head over yes_of_stepped
(Honest/K1/Law/YesAtFifty.lean) · the promise at "honest", AT EVERY y: inAt_head
(Honest/K1/Law/InAtOfThr.lean) · "a reached state inside that promise": the threads' thrS_rchAt
(Honest/Thread/ReachAtHead.lean: from the pair at SaidOk), the promise again, at any strings of the
head's frame: they are read by nothing · KeptBelow: at y' for y: reflexive · the tie: what
ArmBehindTieS hands, by unfolding: the tie reads the data's A1 alone.

IDLE LETTERS. dk, aN, R₁, R₂, R₃: the twins keep them from their elders; no clause of the end names
them. Whoever calls hands any.

WHAT IT DOES NOT SAY. THE TIE ITSELF (the item "tie l" at the thread's own witness) IS A PREMISE
INSIDE ArmBehindTieS: it is not shown. That the thread stands at any run. Under the head, of
which no member is shown. THE FULL SIZE; the format's second hash function. Nothing on any property.
Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.ProofFile.Honest.K1.Twin.ArmReachHeadB
import Johnson.Desc.ProofFile.Honest.K1.Law.FormsShare
import Johnson.Desc.ProofFile.Honest.K1.Law.InAtOfThr
import Johnson.Desc.ProofFile.Honest.K1.Law.YesAtFifty
import Johnson.Desc.ProofFile.Honest.Thread.ReachAtHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K1
open VerifiableInference.Desc
open VerifiableInference.Desc (Chain Strs Place Block)
open VerifiableInference.Desc.First (S Item flatPlacesOf)
open VerifiableInference.Desc.Sound (MsgT linksFull mgAll mgBase uBySort rowQ strsOf)
open VerifiableInference.Desc.K12.Door (K12Data)
open Johnson.Desc.First.Walk.Tied (RchPub)
open OnBytes.Params (Rounds)
open ProofFile.Honest.FirstThread
open OnBytes.Maker (WholeD)
open OnBytes.Slice (frS)
open P5J (AtMgA CellsM TS)

/-- **ArmBehindTieS AT THE HEAD, AT THE READS OF LINK l.** -/
theorem armBehindTieS_head {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
    {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
    (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X : Type}
    (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
    (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
    (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
    (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
    (w : Local W₀ Rc ProofFile.Inst Tr)
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop)
    (hSaid : ∀ b k m, Said b k m → SaidOk b k m)
    (dk : K12Data) (aN : ℕ) (R₁ R₂ R₃ : Rounds) {l : ℕ} (hl : l < 25) {j : ℕ} {n : String}
    (hrun : Item.formsT l j n ∈
      (rowQ linksFull (flatPlacesOf linksFull true) (K1.noL l false)).ins) :
    ArmBehindTieS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w) Said
      ⟨h.𝔇.pubD, h.𝔇.ms, h.𝔇.St, uBySort h.𝔇.uL h.𝔇.uA h.𝔇.uH, h.𝔇.after, h.𝔇.wt, h.𝔇.rw⟩
      h.𝔇.arr (K1.noL l false) l j n := by
  intro blk hblk k s μ E ds y cols s' hT hd hS v ht p hp a c ha hc
  obtain ⟨Bs, base₀, O⟩ := h.laid.opened
  have hT' : ThrS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread SaidOk
      (K1.noL l false) k s μ E := ⟨hT.1, hSaid _ _ _ hT.2⟩
  have hbl : K1.noL l false ≤ cF.blocksInOrder.length := (List.getElem?_eq_some_iff.1 hblk).1.le
  obtain ⟨X', arrs, hX, hy⟩ := yesOf_reads_head h O hl hblk (yes_of_stepped _ hS)
    μ.st.input.x.pub
  have hIn := inAt_head h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w Said hT
  have σ : (Sound.frameAt (D.at frS.P.T.a) (Sound.allOf (D.at frS.P.T.a))
      (D.at frS.P.T.a).key₁ 0).E.Str := (fun _ => default, fun _ => default)
  exact K1.arm_reach_head_b h O dk (fun _ => True) aN R₁ R₂ R₃ l hl X' arrs hX
    (μ.st.input.x.pub, s) (μ.st.input.x.pub, s') _ _ v hy (hIn _)
    (fun _ => ⟨l, hl, ((μ.st.input.x.pub, s), σ),
      ⟨thrS_rchAt h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w σ hbl hT', trivial⟩,
      (hIn (strsOf _ σ)).1, (hIn (strsOf _ σ)).2, rfl⟩)
    ⟨rfl, fun _ _ => ⟨rfl, fun _ => rfl⟩⟩ ht j n hrun p hp a c ha hc

end ProofFile.Honest.K1

#print axioms ProofFile.Honest.K1.armBehindTieS_head
