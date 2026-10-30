-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Desc/SecondShare.lean: THE LAST CHAIN's SHARE OF THE LEDGER FOR "THE HEAD HAS A
  MEMBER AT THE FULL SIZE" (headMember_of_parts, Johnson/AtFull/Top/HeadMember.lean [not in this library]): three of its
  named premises speak of B, what ProofFile.onlineLastChain returns at the public part Z: (1)
  PlanWordOwed.b₃: every sub-protocol of the description's last chain passes its own test on the
  plan · (2) the last chain's part of PlanWordOwed.hC: its cut is the written one · (3) the second
  conjunct of PlanWordOwed.hF: B.fileOk. What the last chain's
  seat reads of Z is said FIELD BY FIELD, as hypotheses: FOUR
  EQUATIONS; no test of the proof file's entry tests is a
  premise, and no law at an opening is called. Theorems with
  their proofs.

THE FOUR EQUATIONS. z := Z.p.chains.made.sized.proof: z.set, z.codes, z.batch are proofSizedFull's
  (hset, hcodes, hbatch) · H2U.p12OwnOfMade Z.made 2 = piW (e₃): the parameters of the request's own
  proximity test are the written ones at that seat's place. They are four of the six on which
  later_of_members stands (Johnson/AtFull/Desc/LaterSeats.lean: whose secondAt, piW,
  later_return and cut_second_written are called here).
IT MOVES; IT DOES NOT MEET: three of the ledger's premises give way to four equations. WHAT MIGHT
  SHOW THESE, NOT CHECKED FOR THIS FILE: e₃ is said to be one conjunct of members_written (that
  statement was not read for this file). For hset, hcodes, hbatch the ledger's own premise
  RowsOwed.m₁ : MadeWritten Zp.p.chains.made LOOKS the likely source (a guess): its text was not
  read for this file: NOT HELD.

THE NAMES.
piW_stages: the written parameters of the own test have stages: by Lean's kernel.
places_of_own: e₃ alone ⊢ the places are made, and pOwn N = piW (the member is one match on
  placesOfMade's return, with parameters without a stage where it refuses).
secondPlanB, second_plan_rows: THE CLOSED FACT: at the written values each of the last chain's
  sub-protocols, carried to the description's type of claims and laid flat, passes its test on the
  plan: by Lean's kernel.
second_flat_four: that test is not idle: the flat list has four entries: by Lean's kernel.
second_plan_written: (1) at P2Third.secondSeatOf Z N, from hset, hcodes, hbatch and pOwn N = piW.
second_fileOk: (3) at that seat: by definition: the seat's text lays fileOk := true.
second_share: **the four equations ⊢ ∃ B, ProofFile.onlineLastChain Z = some B ∧ (1) ∧ (2) ∧ (3).**
second_share_of: the same at the ledger's own letter: at EVERY B that onlineLastChain Z returns (r₇).
b₃_of, cut₃_of: (1) and (2) in the ledger's words, at fileDescBy … A B … c: its field second is
  B.chain.retype by definition. FROM cut₃_of TO hC's THIRD FACTOR (sameRows … cutSecondFull inside
  cutIs) one step is left to whoever joins the three cuts: sameRows_iff
  (Johnson/Desc/Ok/PlanWritten/CutTestLaws.lean), right to left.

Limits. THE FOUR EQUATIONS ARE PREMISES: nothing here shows that they hold at any public files. (3)
  SAYS LITTLE: that seat has no test of its own on the file. A sub-protocol's test on the plan is a
  Bool of its own text: what it asks is not said here. THAT secondPlanB CAN SAY FALSE IS SHOWN BY NO
  LINE HERE: negative tests are not in this file. The full size alone. Nothing on soundness.

-/
import Johnson.AtFull.Desc.LaterSeats
import Johnson.Desc.ProofFile.Frames1

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Desc
open VerifiableInference.Desc VerifiableInference.Desc.K12 VerifiableInference.PlanWritten
open H2K.JointK (pOwn)

/-- The written parameters of the own test have stages. -/
theorem piW_stages : piW.nums.stages ≠ [] := by decide +kernel

/-- **From the own test's member at the written value: the places are made, and the equation on
them.** -/
theorem places_of_own (m : Johnson.G.OfPlan.Made) (e₃ : H2U.p12OwnOfMade m 2 = piW) :
    ∃ N, H2U.placesOfMade m = .ok N ∧ pOwn N = piW := by
  unfold H2U.p12OwnOfMade at e₃
  cases hN : H2U.placesOfMade m with
  | error w =>
    rw [hN] at e₃
    exact absurd (congrArg (·.nums.stages) e₃).symm piW_stages
  | ok N =>
    rw [hN] at e₃
    exact ⟨N, rfl, e₃⟩

/-- The test: each of the last chain's sub-protocols at the written values, carried to the
description's type of claims and laid flat, passes its own test on the plan. -/
def secondPlanB : Bool :=
  (((secondAt (Third.p₁₄Z proofSizedFull.set proofSizedFull.codes proofSizedFull.batch)
    piW).retype (Cl' := ProofFile.Cl)).blocksInOrder).all (·.planOk)

/-- **It accepts**: by Lean's kernel. -/
theorem second_plan_rows : secondPlanB = true := by decide +kernel

/-- The test is not idle: it ranges over four sub-protocols: by Lean's kernel. -/
theorem second_flat_four :
    (((secondAt (Third.p₁₄Z proofSizedFull.set proofSizedFull.codes proofSizedFull.batch)
      piW).retype (Cl' := ProofFile.Cl)).blocksInOrder).length = 4 := by decide +kernel

section
variable (Z : ProofFile.Pub) (N : H2U.Places4)
  (hset : Z.p.chains.made.sized.proof.set = proofSizedFull.set)
  (hcodes : Z.p.chains.made.sized.proof.codes = proofSizedFull.codes)
  (hbatch : Z.p.chains.made.sized.proof.batch = proofSizedFull.batch)
include hset hcodes hbatch

/-- **(1) at the seat.** -/
theorem second_plan_written (hW : pOwn N = piW) :
    ∀ b ∈ ((P2Third.secondSeatOf Z N).chain.retype (Cl' := ProofFile.Cl)).blocksInOrder, b.planOk = true := by
  have e : (P2Third.secondSeatOf Z N).chain =
      secondAt (Third.p₁₄Z Z.p.chains.made.sized.proof.set Z.p.chains.made.sized.proof.codes
        Z.p.chains.made.sized.proof.batch) (pOwn N) := rfl
  rw [e, hset, hcodes, hbatch, hW]
  exact List.all_eq_true.1 second_plan_rows

end

/-- **(3) at the seat**: by definition. -/
theorem second_fileOk (Z : ProofFile.Pub) (N : H2U.Places4) :
    (P2Third.secondSeatOf Z N).fileOk = true := rfl

/-- **THE LAST CHAIN's SHARE, FROM FOUR EQUATIONS.** -/
theorem second_share (Z : ProofFile.Pub)
    (hset : Z.p.chains.made.sized.proof.set = proofSizedFull.set)
    (hcodes : Z.p.chains.made.sized.proof.codes = proofSizedFull.codes)
    (hbatch : Z.p.chains.made.sized.proof.batch = proofSizedFull.batch)
    (e₃ : H2U.p12OwnOfMade Z.made 2 = piW) :
    ∃ B : ProofFile.SecondSeat, ProofFile.onlineLastChain Z = some B ∧
      (∀ b ∈ (B.chain.retype (Cl' := ProofFile.Cl)).blocksInOrder, b.planOk = true) ∧
      cutOf (B.chain.retype (Cl' := ProofFile.Cl)).blocksInOrder = cutSecondFull ∧ B.fileOk = true := by
  obtain ⟨N, hN, hW⟩ := places_of_own Z.made e₃
  exact ⟨_, (later_return Z N hN).2, second_plan_written Z N hset hcodes hbatch hW,
    cut_second_written Z N hset hcodes hbatch hW _, second_fileOk Z N⟩

/-- **The same at every B that the seat's maker returns.** -/
theorem second_share_of (Z : ProofFile.Pub)
    (hset : Z.p.chains.made.sized.proof.set = proofSizedFull.set)
    (hcodes : Z.p.chains.made.sized.proof.codes = proofSizedFull.codes)
    (hbatch : Z.p.chains.made.sized.proof.batch = proofSizedFull.batch)
    (e₃ : H2U.p12OwnOfMade Z.made 2 = piW) {B : ProofFile.SecondSeat}
    (r₇ : ProofFile.onlineLastChain Z = some B) :
    (∀ b ∈ (B.chain.retype (Cl' := ProofFile.Cl)).blocksInOrder, b.planOk = true) ∧
      cutOf (B.chain.retype (Cl' := ProofFile.Cl)).blocksInOrder = cutSecondFull ∧ B.fileOk = true := by
  obtain ⟨B', h', k⟩ := second_share Z hset hcodes hbatch e₃
  obtain rfl : B' = B := Option.some.inj (h'.symm.trans r₇)
  exact k

/-- **b₃, in the ledger's words.** -/
theorem b₃_of {σ : Type} (o : ProofFile.SecondHashFunctionArgument) (mk : ProofFile.LinksBy) (Z : ProofFile.Pub)
    (A : ProofFile.SharedSeat) {B : ProofFile.SecondSeat} (get : σ → First.S) (start : ProofFile.InstPub → σ)
    (c : Chain σ ProofFile.Cl)
    (hset : Z.p.chains.made.sized.proof.set = proofSizedFull.set)
    (hcodes : Z.p.chains.made.sized.proof.codes = proofSizedFull.codes)
    (hbatch : Z.p.chains.made.sized.proof.batch = proofSizedFull.batch)
    (e₃ : H2U.p12OwnOfMade Z.made 2 = piW) (r₇ : ProofFile.onlineLastChain Z = some B) :
    ∀ b ∈ (ProofFile.fileDescBy o mk Z A B get start c).second.blocksInOrder, b.planOk = true :=
  (second_share_of Z hset hcodes hbatch e₃ r₇).1

/-- The last chain's cut, in the ledger's words. -/
theorem cut₃_of {σ : Type} (o : ProofFile.SecondHashFunctionArgument) (mk : ProofFile.LinksBy) (Z : ProofFile.Pub)
    (A : ProofFile.SharedSeat) {B : ProofFile.SecondSeat} (get : σ → First.S) (start : ProofFile.InstPub → σ)
    (c : Chain σ ProofFile.Cl)
    (hset : Z.p.chains.made.sized.proof.set = proofSizedFull.set)
    (hcodes : Z.p.chains.made.sized.proof.codes = proofSizedFull.codes)
    (hbatch : Z.p.chains.made.sized.proof.batch = proofSizedFull.batch)
    (e₃ : H2U.p12OwnOfMade Z.made 2 = piW) (r₇ : ProofFile.onlineLastChain Z = some B) :
    cutOf (ProofFile.fileDescBy o mk Z A B get start c).second.blocksInOrder = cutSecondFull :=
  (second_share_of Z hset hcodes hbatch e₃ r₇).2.1

end Johnson.AtFull.Desc

#print axioms Johnson.AtFull.Desc.piW_stages
#print axioms Johnson.AtFull.Desc.places_of_own
#print axioms Johnson.AtFull.Desc.second_plan_rows
#print axioms Johnson.AtFull.Desc.second_flat_four
#print axioms Johnson.AtFull.Desc.second_plan_written
#print axioms Johnson.AtFull.Desc.second_fileOk
#print axioms Johnson.AtFull.Desc.second_share
#print axioms Johnson.AtFull.Desc.second_share_of
#print axioms Johnson.AtFull.Desc.b₃_of
#print axioms Johnson.AtFull.Desc.cut₃_of
