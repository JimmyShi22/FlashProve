-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/IMR/ToldPaid.lean: THE TWO NAMED
PREMISES ON THE PLAN's TEXTS, K1Told (Johnson/IMR/MsgsSeat.lean) AND K2Told
(Johnson/IMR/MsgsSwitch.lean), ARE PAID,
EACH BY ITS OWN KIND's THEOREM, WITH NO PREMISE; AND THE COUNTS THAT STOOD UNDER THEM, WITHOUT
THEM.

MARK WELL: through Johnson/Desc/K1/Law/SentAt.lean this file stands over
Johnson/Desc/First/BookFit.lean.


  k1Told_paid : K1Told: K1.told_tenants_own (Johnson/Desc/K1/Law/ToldCounts.lean
      and five more of K1's files).
  k2Told_paid : K2Told: P1K2.told_tenants (Johnson/Top/H0/Tw/K2C/ToldTenants.lean,
      out of a set of files marked "not to be told as tied").

  counts_at_cut_paid: **InScope P · readFiles P = .ok pp · O : Open OnBytes.secondHashFunction … · k ≤ 358 ·
      every block of c.blocksInOrder.take k passes its test on the plan · foldBlocks 0 (c.blocksInOrder.take k)
      (ProofFile.startS Z p) R C = .ok r ⇒ r.1.st.oracles.size = ((c.blocksInOrder.take k).map toldMsgs).sum ∧
      r.1.book.place.size = r.1.st.oracles.size ∧ r.1.roots = rootsOf (declOf (c.blocksInOrder.take k)).**
  n0_at_link_paid · n0_at_head_paid · n0_at_finish_paid: Johnson/IMR/N0AtCut.lean's three, under
    cutOf c.blocksInOrder
      = cutFirstFull alone beside the tests on the plan and the fold's return.
  n0_behind_front_paid: n0At 25 at the state BEHIND the quiet step finishFrontQ, where the finish's
      switch itself runs: by
      finishFrontQ_size (K2C/StillKeeps.lean).
THE STANDING THEOREMS (counts_at_cut, n0_at_link, …) STAY AS THEY ARE: whoever has called them at
two premises lays k1Told_paid and k2Told_paid there.
OBJECT · USER · LETTERS. Object: as MsgsBehind.lean and N0AtCut.lean.
User: this folder's field "book" and counts by cut; FrontNums; K10's files.
Letters: none.
Compiled with the whole library.
Limits. In scope alone; ft = 0.
No member. Book-keeping. Nothing on soundness.
-/
import Johnson.IMR.N0AtCut
import Johnson.Desc.K1.Law.ToldCounts
import Johnson.Top.H0.Tw.K2C.ToldTenants

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Meaning.Carry

open VerifiableInference.Desc
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.K2 (n0At)
open VerifiableInference.PlanWritten (cutOf cutFirstFull)
open Johnson.G.OfPlan (rootsOf)
open ProofFile (Cl)

/-- **K1Told, PAID**: K1.told_tenants_own. -/
theorem k1Told_paid : K1Told := fun P h => K1.told_tenants_own P h

/-- **K2Told, PAID**: P1K2.told_tenants. -/
theorem k2Told_paid : K2Told := fun _ _ _ _ h => P1K2.told_tenants h

variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- **THE THREE COUNTS AT EVERY CUT OF THE FIRST CHAIN's FLAT LIST, TO ITS END, IN SCOPE: NO PREMISE
BUT THE BLOCKS' OWN TESTS ON THE PLAN AND THE FOLD's RETURN.** -/
theorem counts_at_cut_paid (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (p : ProofFile.InstPub)
    (R : List Fmt.RoundView) (C : List OpenedColumn) (k : Nat) (hk : k ≤ 358)
    (hp : ∀ b ∈ c.blocksInOrder.take k, b.planOk = true) (r : S × List Fmt.RoundView × List OpenedColumn)
    (h : foldBlocks 0 (c.blocksInOrder.take k) (ProofFile.startS Z p) R C = .ok r) :
    r.1.st.oracles.size = ((c.blocksInOrder.take k).map toldMsgs).sum ∧
      r.1.book.place.size = r.1.st.oracles.size ∧
      r.1.roots = rootsOf (H2K.First.declOf (c.blocksInOrder.take k)) :=
  counts_at_cut hS hR O k1Told_paid k2Told_paid p R C k hk hp r h

/-- In front of the switch into group l, 1 ≤ l ≤ 23. -/
theorem n0_at_link_paid (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    (hc : cutOf c.blocksInOrder = cutFirstFull) {l : Nat} (hl1 : 1 ≤ l) (hl : l ≤ 23)
    (hp : ∀ b ∈ c.blocksInOrder.take (14 * l + 2), b.planOk = true) (p : ProofFile.InstPub) (R : List Fmt.RoundView)
    (C : List OpenedColumn) (r : S × List Fmt.RoundView × List OpenedColumn)
    (h : foldBlocks 0 (c.blocksInOrder.take (14 * l + 2)) (ProofFile.startS Z p) R C = .ok r) :
    r.1.st.oracles.size = n0At l :=
  n0_at_link hS hR O k1Told_paid k2Told_paid hc hl1 hl hp p R C r h

/-- In front of the head's link's switch. -/
theorem n0_at_head_paid (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    (hc : cutOf c.blocksInOrder = cutFirstFull) (hp : ∀ b ∈ c.blocksInOrder.take 339, b.planOk = true)
    (p : ProofFile.InstPub) (R : List Fmt.RoundView) (C : List OpenedColumn) (r : S × List Fmt.RoundView × List OpenedColumn)
    (h : foldBlocks 0 (c.blocksInOrder.take 339) (ProofFile.startS Z p) R C = .ok r) :
    r.1.st.oracles.size = n0At 24 :=
  n0_at_head hS hR O k1Told_paid k2Told_paid hc hp p R C r h

/-- In front of the finish's switch. -/
theorem n0_at_finish_paid (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    (hc : cutOf c.blocksInOrder = cutFirstFull) (hp : ∀ b ∈ c.blocksInOrder.take 353, b.planOk = true)
    (p : ProofFile.InstPub) (R : List Fmt.RoundView) (C : List OpenedColumn) (r : S × List Fmt.RoundView × List OpenedColumn)
    (h : foldBlocks 0 (c.blocksInOrder.take 353) (ProofFile.startS Z p) R C = .ok r) :
    r.1.st.oracles.size = n0At 25 :=
  n0_at_finish hS hR O k1Told_paid k2Told_paid hc hp p R C r h

/-- The same at the state BEHIND the quiet step in front of the finish's switch: where the switch
itself runs. -/
theorem n0_behind_front_paid (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    (hc : cutOf c.blocksInOrder = cutFirstFull) (hp : ∀ b ∈ c.blocksInOrder.take 353, b.planOk = true)
    (p : ProofFile.InstPub) (R : List Fmt.RoundView) (C : List OpenedColumn) (r : S × List Fmt.RoundView × List OpenedColumn)
    (h : foldBlocks 0 (c.blocksInOrder.take 353) (ProofFile.startS Z p) R C = .ok r) {m : S}
    (hm : First.K2.finishFrontQ r.1 = .ok m) : m.st.oracles.size = n0At 25 := by
  rw [← n0_at_finish_paid hS hR O hc hp p R C r h]
  exact First.K2.finishFrontQ_size hm

#print axioms k1Told_paid
#print axioms k2Told_paid
#print axioms counts_at_cut_paid
#print axioms n0_at_link_paid
#print axioms n0_at_head_paid
#print axioms n0_at_finish_paid
#print axioms n0_behind_front_paid

end Meaning.Carry
