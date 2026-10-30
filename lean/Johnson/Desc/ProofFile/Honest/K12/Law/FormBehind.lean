-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/Law/FormBehind.lean: CONDITIONAL: THE THREAD's FORM BEHIND THE
STEP OF THE MEMBER THAT HOLDS THE PROXIMITY TEST AT THE FIRST CHAIN's FINISH (kind K12): THE MEMBER
NUMBER 354, at the first chain's thread at the library's head (`lettersHead`,
Honest/Thread/FirstHead.lean). THE THREAD IN FRONT AND THE MEMBER's STEP ARE PREMISES. General in
all letters of `lettersHead`. One statement with its proof; no definition.

Why. Whoever shows the thread along the first chain owes, at each member, the form one border on
from the thread in front and the member's step. This file pays that at the one member of the kind
K12.

How. The form is "no mark" and the table's promise at the honest letters, at no strings. One call of
`promise_behind` (Johnson/Desc/K12/Honest/Law/PromiseAtStep.lean), at these letters, a made-up frame
without a tree and one made-up value of its strings: at these letters the promise reads no string.
Its premises:
  * the member, "sits" and the tests on the test's numbers: `seat_354`
    (Johnson/Desc/K12/Honest/Law/SeatAtHead.lean); the way out: `laysOnly_outCore`
    (Johnson/Loose/H2K12/Hands354AtSeat.lean);
  * the lines on the table's lists, by the kernel: `pinI_open_written`
    (Johnson/Loose/H2K12/AcrossOfSits.lean), `Rid354.place_written` (Rides354.lean), `place_355`,
    `stand_355`, `open_355` (Hands354AtSeat.lean);
  * the plan's numbers and "no public item behind": three fields of `K12Left`
    (Johnson/Loose/H2K12/Owed354AtMg.lean); the facts on the state in front and its codes; all at
    one and the same data: `left_with_facts` (Johnson/Desc/K12/Honest/Law/FactsAtReach.lean).
    "Reached" comes out of the thread (`reach_of_made`, Honest/Thread/MadeLaw.lean);
  * the equations on the meaning's two public tests and on "held", and that "in order" reads the
    public part alone: by unfolding, as at the closed meaning: the honest letters do not turn these
    fields;
  * "decodes", "shown", "no collision": true at the honest letters by their text.
No mark behind: `IM.at_354` (Johnson/IMR/LastFour.lean).

Main name:
  `k12_form_behind`   **the form behind at 354**

CONDITIONAL on the hypothesis h on the public input (`P5J.AtMgA`, Johnson/P5J/MgAtAll.lean); blk is
the member number 354; the thread in front (`Thr`); the member's step (`Stepped`).
ON h. It can be met: at the full-size public files as Ladder/Stored.lean spells them it has a member
with no premise (`headMember_zFull`, AtFullSide/Top/HeadMemberAtFull.lean). This file does not call
it. These files are tied to the package's files by no theorem.

Limits. AN IMPLICATION: that a thread and a step can be met together at this number is shown nowhere
here. The form alone: nothing on the thread's other clauses behind the step (what rides, what is
kept, what was made). At the library's full size and at the format's second hash function alone: h is typed
there. Of the closed facts by the kernel beneath, five are named above, and a sixth stands right
beneath `seat_354` (`k12AllB_full`, Johnson/Loose/H2K12/K12LawR.lean); what lies deeper was not
walked. Through its imports the file stands above the files under ThirdParty/
(Johnson/Loose/H2K12/K12AtHead.lean's own limit). The file sets `maxHeartbeats` to 1000000 and
`maxRecDepth` to 100000.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.Thread.FirstHead
import Johnson.Desc.ProofFile.Honest.Thread.Pays
import Johnson.Desc.ProofFile.Honest.Thread.MadeLaw
import Johnson.Desc.K12.Honest.Law.PromiseAtStep
import Johnson.Desc.K12.Honest.Law.SeatAtHead
import Johnson.Desc.K12.Honest.Law.FactsAtReach
import Johnson.Loose.H2K12.Hands354AtSeat
import Johnson.IMR.LastFour

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K12
open VerifiableInference.Desc (Chain Strs Place)
open VerifiableInference.Desc.Sound (MsgT)
open VerifiableInference.Desc.First (onAt openSets pubSets start)
open OnBytes.Maker (WholeD)
open ProofFile.Honest.FirstThread (Script WtF lettersHead honest noStrs)
open P5J (AtMgA CellsM TS mgAtAll fullLinks)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w : Local W₀ Rc ProofFile.Inst Tr)

/-- **THE FORM BEHIND THE STEP OF THE MEMBER OF KIND K12: THE MEMBER NUMBER 354.** CONDITIONAL: the
hypothesis h; blk is the member number 354 of the first chain's flat list; the thread in front; the
member's step. -/
theorem k12_form_behind :
    ∀ blk, cF.blocksInOrder[354]? = some blk → ∀ k s m E ds y cols s',
      Thr (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread 354 k s m E →
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.Stepped blk k s m E ds y cols
        s' →
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.Form (354 + 1) k s' y.2 := by
  intro blk hblk k s m E ds y cols s' hT hS
  obtain ⟨Bs, base0, O⟩ := h.laid.opened
  -- the member is the proximity test's entry at the chain's finish
  obtain ⟨J, hJ, hSit, hplan, ho⟩ := H2K12.AtStep.seat_354 h
  obtain rfl : H2K.JointK.firstEntry ProofFile.sameReply J = blk := Option.some.inj (hJ.symm.trans hblk)
  -- no mark behind its yes
  obtain ⟨-, h1, -⟩ := IM.at_354 h.scope h.reads O hblk hS.2
  -- the closed facts, and the facts at every reached state, at one and the same data
  obtain ⟨L, K, hFacts⟩ := H2K12.left_with_facts h
  -- in front: no mark, the promise, reached
  obtain ⟨hf0, hon0⟩ := hT.2.2.1
  have h0 : s.failed = none := Option.isNone_iff_eq_none.1 hf0
  have hon : onAt (P5J.At.N Zp cF)
      (honest (mgAtAll h) (ansJT (P5J.At.cs Zp) (P5J.At.arr Zp) (P5J.At.smp Zp)
        (P5J.At.ms Zp Z.lay)) test) fullLinks P5J.At.ps[354]?
      (((openSets fullLinks P5J.At.ps (start fullLinks))[354]?).getD [])
      (((pubSets (mgAtAll h).more fullLinks P5J.At.ps)[354]?).getD [])
      (m.st.input.x.pub, s) noStrs := hon0
  have hr := reach_of_made (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread
    (ProofFile.startS Zp) m.st.input.x.pub
    (Nat.le_of_lt (List.getElem?_eq_some_iff.1 hblk).1) (fun _ e => e) hT.2.2.2.2.1
  obtain ⟨F, hcod⟩ := hFacts 354 (m.st.input.x.pub, s) hr h0
  -- the promise behind
  have hb := H2K12.AtStep.promise_behind (Fr := ⟨0, [], fun _ => 0, 0⟩) (H2K.JointK.pL Np)
    (P5J.At.foldD Zp cF L) (P5J.At.N Zp cF)
    (honest (mgAtAll h) (ansJT (P5J.At.cs Zp) (P5J.At.arr Zp) (P5J.At.smp Zp)
      (P5J.At.ms Zp Z.lay)) test) fullLinks P5J.At.ps 354 _ _ hSit
    (H2K12.laysOnly_outCore ProofFile.sameReply) (H2K.JointK.early_of_planOk _ hplan)
    (H2K.JointK.answers_of_planOk _ hplan) H2K12.pinI_open_written (fun _ => rfl) (fun _ => rfl) rfl
    K.indexListed hplan ho ⟨1, none, 2, .K12⟩ ⟨1, none, 3, .K13⟩ H2K12.Rid354.place_written
    H2K12.place_355 H2K12.stand_355 H2K12.open_355 K.pubsNone K.goOn
    (fun a a' e ha => by
      obtain ⟨z, t⟩ := a
      obtain ⟨z', t'⟩ := a'
      obtain rfl : z' = z := e
      exact ha)
    ((m.st.input.x.pub, s), (fun _ => (0, []), fun _ => []))
    ((m.st.input.x.pub, s'), (fun _ => (0, []), fun _ => [])) rfl hS.2 hon h0 F hcod
    (fun _ => trivial) (fun _ => ⟨trivial, trivial⟩)
  -- the input is as it was
  obtain ⟨⟨st, -, hy⟩, -⟩ := hS.1
  obtain ⟨ei, -, -⟩ := play_mid _ _ _ _ _ hy
  refine ⟨?_, ?_⟩
  · show s'.failed.isNone = true
    rw [h1]
    rfl
  · show onAt (P5J.At.N Zp cF)
      (honest (mgAtAll h) (ansJT (P5J.At.cs Zp) (P5J.At.arr Zp) (P5J.At.smp Zp)
        (P5J.At.ms Zp Z.lay)) test) fullLinks P5J.At.ps[354 + 1]?
      (((openSets fullLinks P5J.At.ps (start fullLinks))[354 + 1]?).getD [])
      (((pubSets (mgAtAll h).more fullLinks P5J.At.ps)[354 + 1]?).getD [])
      (y.2.st.input.x.pub, s') noStrs
    rw [ei]
    exact hb

end ProofFile.Honest.K12

#print axioms ProofFile.Honest.K12.k12_form_behind
