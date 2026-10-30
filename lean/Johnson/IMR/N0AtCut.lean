-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/IMR/N0AtCut.lean: IN FRONT OF EACH
OF THE 25 CODE SWITCHES OF THE PROOF FILE's FIRST CHAIN THE VERIFIER's STATE HOLDS JUST THE CLOSED
NUMBER n0At l OF ORACLE MESSAGES, in the goals' scope, from the fold's return alone. A JOIN: the
count is MsgsScope.lean's, the closed number Johnson/Top/H0/K2Hears/PlaceNums.lean's.

  toldBefore_eq: ToldTest.lean's toldBefore bs k is ((bs.take k).map toldMsgs).sum: by rfl (its
      toldBy is toldMsgs (Johnson/Goal/Meaning/CarryTold.lean) token for token: held by Lean).
  n0_at_link: **InScope P · readFiles P = .ok pp · O : Open OnBytes.secondHashFunction … · K1Told · K2Told ·
      cutOf c.blocksInOrder = cutFirstFull · 1 ≤ l ≤ 23 · every block of c.blocksInOrder.take (14 l + 2) passes its
      test on the plan · foldBlocks 0 (c.blocksInOrder.take (14 * l + 2)) (ProofFile.startS Z p) R C = .ok r ⇒
      r.1.st.oracles.size = n0At l.** n0_at_head: the cut 339: n0At 24. n0_at_finish: the cut 353:
      n0At 25.
THE ROAD. Johnson/IMR/MsgsScope.lean's msgs_at_cut_scope · toldBefore_eq · n0_of_cut
(Johnson/Desc/Ok/PlanWritten/CutNums.lean). n0At:
Johnson/Top/H0/K2Hears/PlaceNums.lean (n0_values writes the 26 numbers out).
PREMISES, AND WHO CAN PAY. K1Told · K2Told: see Johnson/IMR/MsgsScope.lean's head. cutOf c.blocksInOrder =
cutFirstFull ("the chain's blocks have the written cut"): cut_of_row from an accept of its row
for the proof file's entry tests (cutRow F Z = true), with F.first = c by the opening's field desc;
that row is a premise.
AT ANY OTHER CUT k ≤ 358 the count is Johnson/IMR/MsgsBehind.lean's counts_at_cut: toldBefore c.blocksInOrder
k; a
closed number there is whoever's has a written table that pins it.
OBJECT · USER · LETTERS.
Object: c := F.first, F := ProofFile.onlineDescription OnBytes.secondHashFunction's value, in scope, at the full size.
User: FrontNums' n0; K10's files; this folder's premises on the number of messages in front
of a switch. Letters: none.
Compiled with the whole library.
Limits. The 25 cuts alone. In scope alone; ft = 0. No member. Book-keeping. Nothing on soundness.

-/
import Johnson.IMR.MsgsBehind
import Johnson.Desc.Ok.PlanWritten.CutNums

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Meaning.Carry

open VerifiableInference.Desc
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.K2 (n0At)
open VerifiableInference.PlanWritten (cutOf cutFirstFull toldBefore n0_of_cut)
open ProofFile (Cl)

/-- toldBefore, ToldTest.lean's count of what the first k blocks tell, is the sum of toldMsgs. -/
theorem toldBefore_eq {T Cl : Type} (bs : List (Block T Cl)) (k : Nat) :
    toldBefore bs k = ((bs.take k).map toldMsgs).sum := rfl

variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- **IN FRONT OF THE SWITCH INTO GROUP l, 1 ≤ l ≤ 23 (the cut 14 l + 2), THE VERIFIER's STATE HOLDS
n0At l ORACLE MESSAGES.** -/
theorem n0_at_link (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (h1 : K1Told) (hT : K2Told)
    (hc : cutOf c.blocksInOrder = cutFirstFull) {l : Nat} (hl1 : 1 ≤ l) (hl : l ≤ 23)
    (hp : ∀ b ∈ c.blocksInOrder.take (14 * l + 2), b.planOk = true) (p : ProofFile.InstPub) (R : List Fmt.RoundView)
    (C : List OpenedColumn) (r : S × List Fmt.RoundView × List OpenedColumn)
    (h : foldBlocks 0 (c.blocksInOrder.take (14 * l + 2)) (ProofFile.startS Z p) R C = .ok r) :
    r.1.st.oracles.size = n0At l := by
  rw [msgs_at_cut_scope hS hR O h1 hT (by omega) hp p R C r h, ← toldBefore_eq]
  exact (n0_of_cut hc).1 l hl1 hl

/-- **In front of the head's link's switch (the cut 339): n0At 24.** -/
theorem n0_at_head (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (h1 : K1Told) (hT : K2Told)
    (hc : cutOf c.blocksInOrder = cutFirstFull) (hp : ∀ b ∈ c.blocksInOrder.take 339, b.planOk = true)
    (p : ProofFile.InstPub) (R : List Fmt.RoundView) (C : List OpenedColumn) (r : S × List Fmt.RoundView × List OpenedColumn)
    (h : foldBlocks 0 (c.blocksInOrder.take 339) (ProofFile.startS Z p) R C = .ok r) :
    r.1.st.oracles.size = n0At 24 := by
  rw [msgs_at_cut_scope hS hR O h1 hT (by decide) hp p R C r h, ← toldBefore_eq]
  exact (n0_of_cut hc).2.1

/-- **In front of the finish's switch (the cut 353): n0At 25.** -/
theorem n0_at_finish (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (h1 : K1Told) (hT : K2Told)
    (hc : cutOf c.blocksInOrder = cutFirstFull) (hp : ∀ b ∈ c.blocksInOrder.take 353, b.planOk = true)
    (p : ProofFile.InstPub) (R : List Fmt.RoundView) (C : List OpenedColumn) (r : S × List Fmt.RoundView × List OpenedColumn)
    (h : foldBlocks 0 (c.blocksInOrder.take 353) (ProofFile.startS Z p) R C = .ok r) :
    r.1.st.oracles.size = n0At 25 := by
  rw [msgs_at_cut_scope hS hR O h1 hT (by decide) hp p R C r h, ← toldBefore_eq]
  exact (n0_of_cut hc).2.2

#print axioms n0_at_link
#print axioms n0_at_head
#print axioms n0_at_finish

end Meaning.Carry
