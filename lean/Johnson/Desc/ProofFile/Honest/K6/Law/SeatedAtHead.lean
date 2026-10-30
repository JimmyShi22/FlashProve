-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K6/Law/SeatedAtHead.lean.
WHAT IT IS NOT. EVERY STATEMENT IS CONDITIONAL ON THE HYPOTHESIS P5J.AtMgA AND ON ONE NAMED PREMISE
ON THE PROVER's HALVES (K6HalfAt). (Of the first the library has a member under four premises on the
three public files: P5J.head_exists_at_name, Johnson/P5J/HeadExistsAtName.lean; nothing here calls
that.) K6HalfAt IS SHOWN OF NO PROVER; that the thread holds at any run is shown nowhere. The ends
are definitions of the honest side's frame, premises' forms of its rules: none of the library's
goals, and no verifier's accept. At the format's second hash function OnBytes.secondHashFunction, the full size, the
goals' scope alone. Nothing on soundness, on completeness or on hiding.
WHAT IT IS. AT THE FIRST CHAIN's THREAD AT THE LIBRARY's OWN LETTERS (lettersHead,
Honest/Thread/FirstHead.lean), AT ALL ITS ARGUMENTS, THE DEBTS PlaysS AND AcceptedS
(Honest/Thread/PaysS.lean) AT BORDER 341, THE SUB-PROTOCOL "THE OUTPUT HEAD's OWN ROUNDS" (K6), HANG
ON THAT HYPOTHESIS AND ON K6HalfAt ALONE. Calls and ties: no new mathematics.
  K6HalfAt Zp H wit     the one premise: which half of the prover's stands at the sub-protocol's
                        place.
  k6Seated_at_head      the structure K6Seated (Honest/K6/Law/Seated.lean) at number 341 of the flat
                        list: four of its five fields are paid under the hypothesis; the fifth is
                        the premise.
  k6_playsS_at_head     PlaysS there, at every sentence Said.
  k6_acceptedS_at_head  AcceptedS there, at every sentence Said and every fall.
CALLED: k6_member_at_mg (Kinds/Law/K6WayUpAtSeat.lean), member_is (Honest/K6/Law/MemberIs.lean),
k6_playsS (Honest/K6/Law/Plays.lean), k6_acceptedS (Honest/K6/Law/Accepted.lean), k6Fronted_at_head
(Honest/K6/Law/FrontedAtHead.lean).

-/
import Johnson.Desc.ProofFile.Honest.K6.Law.FrontedAtHead
import Johnson.Desc.ProofFile.Honest.K6.Law.MemberIs

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K6
open VerifiableInference.Desc (Chain Place Strs Block Claim)
open VerifiableInference.Desc.Sound (MsgT)
open VerifiableInference.Desc.Kinds (Head.parOf)
open VerifiableInference.Desc.Kinds.Head.Law (workOf)
open ProofFile.Honest.FirstThread (Script WtF lettersHead)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **THE ONE PREMISE ON THE PROVER's HALVES**: among the first chain's halves of the prover H, the
first that stands at the place of the output head's own rounds is the sub-protocol's row, at the
reader wit of the small input and at the public numbers of the description's public parameters. A
sentence on public data and the prover: no run is in it. WHAT ITS PAYER OWES, by our reading: (i)
the prover's halves of the first chain are the lots' halves at the description's letters; (ii) the
head's lot's own test on these letters says yes (Honest/K6/Part.lean); (iii) the description has a
block for the sub-protocol; (iv) it has 25 segments, and the lots' public parameters are the
description's (both: IMR/K6Seat.lean, IMR/SeatOpen.lean); (v) no half earlier in the list stands at
that place.
A definition: a premise's form. Nothing is claimed of it. -/
def K6HalfAt (Zp : ProofFile.Pub) {W₀ Rc Ky Tr X₀ X : Type} (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
    (wit : Local W₀ Rc ProofFile.Inst Tr → HeadAsk) : Prop :=
  H.first.find? (fun g => g.place == IM.k6Place) =
    some ⟨IM.k6Place, headRow wit (Head.parOf (P5J.At.X Zp).hS (workOf (P5J.At.X Zp))) IM.k6Place⟩

/-- **THE STRUCTURE K6Seated AT THE LIBRARY's OWN LETTERS.** CONDITIONAL on the hypothesis that ties
the table's letters to the proof file's description, and on the one premise on the prover's halves.
blk: pinned by its place in the flat list. -/
theorem k6Seated_at_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts}
    {W₀ Rc Ky Tr X₀ X : Type} (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
    (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    (test : Nat → TS → Option String)
    (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop) (item n₁ n₂ b₀ : Nat)
    (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop) (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop)
    (Kp : Place → TS → TS → Prop) (w : Local W₀ Rc ProofFile.Inst Tr)
    (wit : Local W₀ Rc ProofFile.Inst Tr → HeadAsk) (hH : K6HalfAt Zp H wit) :
    ∃ blk : Block TS ProofFile.Cl, cF.blocksInOrder[341]? = some blk ∧
      K6Seated (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread 341 wit
        (Head.parOf (P5J.At.X Zp).hS (workOf (P5J.At.X Zp))) IM.k6Place blk := by
  obtain ⟨blk, hblk, M⟩ := P4.k6_member_at_mg h.toAtMg
  obtain ⟨hp, hr, ho⟩ := member_is M
  exact ⟨blk, hblk, hblk, hp, hr, ho, by rw [hp]; exact hH⟩

/-- **IT PLAYS, AT THE LIBRARY's OWN LETTERS**: the debt `PlaysS` at border 341, at every letter
Said. CONDITIONAL on the same two. -/
theorem k6_playsS_at_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts}
    {W₀ Rc Ky Tr X₀ X : Type} (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
    (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    (test : Nat → TS → Option String)
    (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop) (item n₁ n₂ b₀ : Nat)
    (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop) (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop)
    (Kp : Place → TS → TS → Prop) (w : Local W₀ Rc ProofFile.Inst Tr)
    (wit : Local W₀ Rc ProofFile.Inst Tr → HeadAsk) (hH : K6HalfAt Zp H wit)
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop) :
    PlaysS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said 341 := by
  obtain ⟨blk, _, Hs⟩ := k6Seated_at_head h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w wit hH
  exact k6_playsS _ Hs Said

/-- **IT IS ACCEPTED, AT THE LIBRARY's OWN LETTERS**: the debt `AcceptedS` at border 341, at every
letter Said and every letter fall. CONDITIONAL on the same two. -/
theorem k6_acceptedS_at_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts}
    {W₀ Rc Ky Tr X₀ X : Type} (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
    (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    (test : Nat → TS → Option String)
    (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop) (item n₁ n₂ b₀ : Nat)
    (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop) (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop)
    (Kp : Place → TS → TS → Prop) (w : Local W₀ Rc ProofFile.Inst Tr)
    (wit : Local W₀ Rc ProofFile.Inst Tr → HeadAsk) (hH : K6HalfAt Zp H wit)
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop)
    (fall : Nat → TS → List Fmt.Drawn → Option String) :
    AcceptedS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said fall 341 := by
  obtain ⟨blk, e, Hs⟩ := k6Seated_at_head h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w wit hH
  obtain ⟨blk', _, _, e', _, _, Hf⟩ :=
    k6Fronted_at_head h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w Said
  obtain rfl : blk = blk' := Option.some.inj (e.symm.trans e')
  exact k6_acceptedS Hs Hf fall

end ProofFile.Honest.K6

#print axioms ProofFile.Honest.K6.k6Seated_at_head
#print axioms ProofFile.Honest.K6.k6_playsS_at_head
#print axioms ProofFile.Honest.K6.k6_acceptedS_at_head
