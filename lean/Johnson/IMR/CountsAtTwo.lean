-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/IMR/CountsAtTwo.lean: THE NUMBER OF ORACLE MESSAGES IN THE VERIFIER's STATE AT A BORDER OF
THE PROOF FILE's FIRST CHAIN, IN THE LETTERS OF «REACHED» OVER THE WRAPPED SUB-PROTOCOLS; AND AT THE
TWO BORDERS 2 AND 356 AS NUMERALS. For the premises hCount and hCount₂ of sampleTwoB_h4_paid
(Johnson/ToldDescR/SampleTwoOpen.lean) and ownSitsB_h3 (declared nowhere in this library).
Statements and proofs.

  count_below       in scope, at every border k ≤ 358, at every state reached by the wrapped sub-protocols' steps: as many oracle messages as the k sub-protocols in front tell (toldBefore), and as many places in the list of commitment trees: Meaning.Carry.counts_at_cut_paid (Johnson/IMR/ToldPaid.lean) through reach_raw and Reach.fold. No new premise.
  told_written      at the written cut of the full size: 0 messages are told in front of number 2, 197 in front of number 356 (by the kernel)
  told_can_fail     the closed fact can fail: in front of number 3 it is not 0
  told_of_cut2      so at a list of sub-protocols with the written cut
  **hCount_paid · hCount₂_paid**   the two premises, to the letter, at Rch := Reach 0 (c.blocksInOrder.map Sound.below) (ProofFile.startS Z), nW := 197, n₀ := 0
  hCount_told · hCount₂_told       the same without hc, at the letters toldBefore c.blocksInOrder 356 and toldBefore c.blocksInOrder 2

THE PREMISES. hS · hR: the goals' scope; the public files are read · O: the opening · hp: every sub-protocol of the first chain passes its test on the plan · hc : cutOf c.blocksInOrder = cutFirstFull: "the chain's sub-protocols have the written cut": cut_of_row gives it from an accept of the row cutRow F Z (Johnson/Desc/Ok/PlanWritten/CutTest.lean), with F.first = c by the opening's field desc.
The fences of the two premises (no mark; an accepting step at number 2) are not spent.
What is not claimed. Nothing at another family of reached states. Nothing outside the goals' scope or at another hash than the older one. That hc holds at any files. No member. No soundness.

-/
import Johnson.IMR.ToldPaid
import Johnson.Top.H0.Walk.Reach
import Johnson.Desc.Ok.PlanWritten.CutNums

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace IM

open VerifiableInference.Desc
open VerifiableInference.Desc.First (S)
open VerifiableInference.PlanWritten (cutOf cutFirstFull toldBefore toldOfRow toldBefore_cut)
open Johnson.Desc.First.Walk.Tied (Reach reach_raw)
open ProofFile (Cl)

variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- **The two counts at every border, in the letters of «reached» over the wrapped
sub-protocols.** -/
theorem count_below (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    (hp : ∀ b ∈ c.blocksInOrder, b.planOk = true) {k : ℕ} (hk : k ≤ 358) {z : ProofFile.InstPub} {s : S}
    (h : Reach 0 (c.blocksInOrder.map Sound.below) (ProofFile.startS Z) k (z, s)) :
    s.st.oracles.size = toldBefore c.blocksInOrder k ∧ s.book.place.size = s.st.oracles.size := by
  obtain ⟨-, rs, cols, f⟩ := (reach_raw h).fold
  obtain ⟨c1, c2, -⟩ := Meaning.Carry.counts_at_cut_paid hS hR O z rs cols k hk
    (fun b hb => hp b (List.mem_of_mem_take hb)) _ f
  exact ⟨c1, c2⟩

set_option maxRecDepth 1000000 in
/-- At the written cut: what is told in front of numbers 2 and 356. -/
theorem told_written : ((cutFirstFull.take 2).map toldOfRow).sum = 0 ∧
    ((cutFirstFull.take 356).map toldOfRow).sum = 197 := by decide +kernel

set_option maxRecDepth 1000000 in
/-- The closed fact can fail. -/
theorem told_can_fail : ((cutFirstFull.take 3).map toldOfRow).sum ≠ 0 := by decide +kernel

theorem told_of_cut2 {T C : Type} {bs : List (Block T C)} (h : cutOf bs = cutFirstFull) :
    toldBefore bs 2 = 0 ∧ toldBefore bs 356 = 197 := by
  rw [toldBefore_cut, toldBefore_cut, h]
  exact told_written

/-- **hCount, PAID**: the premise of ToldDesc.sampleTwoB_h4_paid, to the letter, at
Rch := Reach 0 (c.blocksInOrder.map Sound.below) (ProofFile.startS Z) and nW := 197. -/
theorem hCount_paid (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    (hp : ∀ b ∈ c.blocksInOrder, b.planOk = true) (hc : cutOf c.blocksInOrder = cutFirstFull) :
    ∀ (z : ProofFile.InstPub) (s₁ : S), Reach 0 (c.blocksInOrder.map Sound.below) (ProofFile.startS Z) 356 (z, s₁) →
      s₁.failed = none → s₁.st.oracles.size = 197 := fun _ _ h _ =>
  (count_below hS hR O hp (by decide) h).1.trans (told_of_cut2 hc).2

/-- **hCount₂, PAID**: likewise, at n₀ := 0. -/
theorem hCount₂_paid (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    (hp : ∀ b ∈ c.blocksInOrder, b.planOk = true) (hc : cutOf c.blocksInOrder = cutFirstFull) :
    ∀ (z : ProofFile.InstPub) (s : S) (b : Block S Cl) (ft : ℕ) (rs : List Fmt.RoundView) (cols : List OpenedColumn)
      (s' : S) (n : ℕ), Reach 0 (c.blocksInOrder.map Sound.below) (ProofFile.startS Z) 2 (z, s) →
      c.blocksInOrder[2]? = some b → b.step ft s rs cols = .ok (s', n) → s'.failed = none →
      s.st.oracles.size = 0 := fun _ _ _ _ _ _ _ _ h _ _ _ =>
  (count_below hS hR O hp (by decide) h).1.trans (told_of_cut2 hc).1

/-- hCount without hc, at the letter toldBefore c.blocksInOrder 356. -/
theorem hCount_told (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    (hp : ∀ b ∈ c.blocksInOrder, b.planOk = true) :
    ∀ (z : ProofFile.InstPub) (s₁ : S), Reach 0 (c.blocksInOrder.map Sound.below) (ProofFile.startS Z) 356 (z, s₁) →
      s₁.failed = none → s₁.st.oracles.size = toldBefore c.blocksInOrder 356 := fun _ _ h _ =>
  (count_below hS hR O hp (by decide) h).1

/-- hCount₂ without hc, at the letter toldBefore c.blocksInOrder 2. -/
theorem hCount₂_told (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    (hp : ∀ b ∈ c.blocksInOrder, b.planOk = true) :
    ∀ (z : ProofFile.InstPub) (s : S) (b : Block S Cl) (ft : ℕ) (rs : List Fmt.RoundView) (cols : List OpenedColumn)
      (s' : S) (n : ℕ), Reach 0 (c.blocksInOrder.map Sound.below) (ProofFile.startS Z) 2 (z, s) →
      c.blocksInOrder[2]? = some b → b.step ft s rs cols = .ok (s', n) → s'.failed = none →
      s.st.oracles.size = toldBefore c.blocksInOrder 2 := fun _ _ _ _ _ _ _ _ h _ _ _ =>
  (count_below hS hR O hp (by decide) h).1

end IM

#print axioms IM.count_below
#print axioms IM.told_written
#print axioms IM.told_can_fail
#print axioms IM.told_of_cut2
#print axioms IM.hCount_paid
#print axioms IM.hCount₂_paid
#print axioms IM.hCount_told
#print axioms IM.hCount₂_told
