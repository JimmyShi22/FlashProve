-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/- Johnson/AtFull/Rounds/K6.lean: THE SECOND ROW OF THE LOT OF THE OUTPUT HEAD'S OWN ROUNDS
(P4.k6Lot): WHAT ITS BLOCK DECLARES: in the goals' scope every block of the lot stands at the
written place and declares the written list that the table bears at the name "H:4"
(Johnson/AtFull/Rounds/ListAt.lean: listAt). Definitions, statements and proofs; two closed facts
by evaluation in Lean's kernel.
WHAT IT DOES NOT SHOW, FIRST. THE ROW SPEAKS OF "EVERY BLOCK OF THE LOT": WHERE THE LOT HAS NO BLOCK
IT HOLDS FOR NOTHING: that there is just one is not shown here, and wants two
premises more. THAT ANY FILES MEET THE PREMISES: by no theorem. NO EXAMPLE OF THE HEAD IS SHOWN IN
THIS FILE; two, at storedPublicFiles and at zGap alone, are AtFullSide.Top.headMember_zFull and headMember_zGap,
whose own Limits say what they are worth. That these 82 are the protocol's right rounds, or that the
programs' plan has them. At
the second hash function OnBytes.secondHashFunction alone. Nothing on the block's decision, its errors, or
soundness.
WHAT THE CLOSED FACT HOLDS AGAINST WHAT. The written list was printed off an evaluation of this same
description: so off this very block's rounds: NO INDEPENDENT WITNESS. The other side is not the
block's maker: it is THE PLANNER's closed list (OnBytes.Tie.Pv.Head.headOwnList). The maker comes in
by the proved Prices.k6_entries alone (Johnson/Desc/Kinds/Law/HeadPrices.lean; general in
the sizes; no kernel). So two texts and a print agree.

Main names (namespace Johnson.AtFull.Rounds).
  k6RoundsAt w lt lPd: the planner's list for the head's own rounds, each entry dressed as a
      declared round that opens nothing: a function of the bits of work and two numbers of bits
      alone. It is the kind's declared rounds WHERE 0 < lt.
  k6_rounds_seated: GENERAL: where 0 < lt the block as a lot seats it declares just these, at every
      public record, link and list "before".
  k6_rounds_written [kernel]: at work 0, lt = 10, lPd = 13 they are listAt "H:4". k6_rounds_bent
      [kernel]: THE TEST CAN SAY NO, seven arms: lPd = 12 · work 1 · lt = 11 with lPd = 11 (82
          members too) · the list of the name "H:3" · of a name that the table has not · the written
          list with its last member's message halved · the written list with a stored tree laid into
          every round: each evaluates to false.
  k6_rounds_row: THE ROW: from the goals' scope · the goals' reader's return · the plain public
      part's return · the blank letters' return.
  k6_lists_at: THE ROW IN ITS USER's LETTERS: at any function N from places to names that gives
      "H:4" at the written place: b.rounds = [] ∨ b.rounds = listAt (N b.place): which is
      ProofFile.Sk.Lst listAt (N b.place) b.rounds, unfolded (Law/Skel/SkelLists.lean is not imported).
  k6_no_batch: the lot brings no batching.

The theorems called in scope: numbers_in_scope, work_ref (Johnson/Goal/Meaning/HeadCondScope.lean),
Meaning.HeadS.frame_in_scope, IM.ground_publicK, ground_gets. None at an opening, under a pin, or at
a return of the chain. It stands on
ListAt.lean with the two that it imports (one of them, a written literal, lies in a
folder named Unfolds; nothing of that folder's tactic is used) · K6Row.lean (for lPdAt and
k6_blocks) and five files on skeletons beneath it.

-/
import Johnson.AtFull.Rounds.ListAt
import Johnson.AtFull.Desc.Lots.K6Row
import Johnson.IMR.PureJoin
import Johnson.Goal.Meaning.HeadCondScope

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace Johnson.AtFull.Rounds

open OnBytes
open VerifiableInference.Desc (Block Claim Place)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Kinds.Head (seatedClaims blockClaims sizesOf rounds)
open VerifiableInference.Desc.Kinds.Head.Law (seatedClaims_some workOf)
open VerifiableInference.Desc.Kinds.Head.Law.Prices (recAt k6_entries)
open VerifiableInference.Desc.Kinds.Head.Law.InScope (numbers_in_scope work_ref)
open Johnson.AtFull.Lots (lPdAt k6_blocks)

/-- The planner's list for the head's own rounds at given bits of work and two numbers of bits, each
entry dressed as a declared round that opens nothing. It is the kind's declared rounds where 0 < lt
(k6_rounds_seated); at lt = 0 and work other than 0 the two part. -/
def k6RoundsAt (w lt lPd : Nat) : List Fmt.DeclaredRound :=
  (OnBytes.Tie.Pv.Head.headOwnList w (recAt lt lPd)).map fun e => { entry := e }

/-- **GENERAL: what the block as a lot seats it declares.** -/
theorem k6_rounds_seated {W : Model.Verify.Public} {l : Nat} {ms : List (Nat × Nat)}
    {b : Block S Claim} (h : seatedClaims W l ms = some b) (hlt : 0 < W.hS.lt) :
    b.rounds = k6RoundsAt (workOf W) W.hS.lt (lPdAt W.hS) := by
  obtain ⟨b0, h0, rfl⟩ := seatedClaims_some h
  unfold blockClaims at h0
  obtain ⟨iU3, -, rfl⟩ := Option.map_eq_some_iff.mp h0
  have e := @k6_entries (sizesOf W.hS) (workOf W) hlt
  show (@rounds (sizesOf W.hS)).map
    (fun r => ({ entry := VerifiableInference.Desc.Kinds.Round.entry (workOf W) r } :
      Fmt.DeclaredRound)) = _
  unfold k6RoundsAt
  rw [show OnBytes.Tie.Pv.Head.headOwnList (workOf W) (recAt W.hS.lt (lPdAt W.hS)) =
    (@rounds (sizesOf W.hS)).map (VerifiableInference.Desc.Kinds.Round.entry (workOf W))
    from e.symm, List.map_map]
  rfl

set_option maxRecDepth 100000 in
/-- **The closed fact.** -/
theorem k6_rounds_written : Decidable.decide (k6RoundsAt 0 10 13 = listAt "H:4") = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- **The test can say no.** -/
theorem k6_rounds_bent : (Decidable.decide (k6RoundsAt 0 10 12 = listAt "H:4") ||
    Decidable.decide (k6RoundsAt 1 10 13 = listAt "H:4") ||
    Decidable.decide (k6RoundsAt 0 11 11 = listAt "H:4") ||
    Decidable.decide (k6RoundsAt 0 10 13 = listAt "H:3") ||
    Decidable.decide (k6RoundsAt 0 10 13 = listAt "H:0") ||
    Decidable.decide (k6RoundsAt 0 10 13 =
      (listAt "H:4").dropLast ++ [{ entry := { name := "PSC values", msg := 24 } }]) ||
    Decidable.decide (k6RoundsAt 0 10 13 =
      (listAt "H:4").map fun r => { r with stored := [default] })) = false := by
  decide +kernel

variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {Z : ProofFile.Pub} {G : ProofFile.Ground}

/-- **THE ROW.** -/
theorem k6_rounds_row (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (hZ : ProofFile.pubPlain OnBytes.secondHashFunction P.pol lay P.KL = .ok Z)
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Z = some G) :
    ∀ b ∈ (P4.k6Lot Z).blocks G, b.place = ⟨1, some 24, 4, .K6⟩ ∧ b.rounds = listAt "H:4" := by
  intro b hb
  have hW := IM.ground_publicK hZ hG
  have N := numbers_in_scope hS hR hW
  have hw : workOf G.W = 0 := by
    unfold workOf
    rw [_root_.Meaning.HeadS.frame_in_scope hS hR hW]
    exact work_ref
  have hl : lPdAt G.W.hS = 13 := by
    unfold lPdAt VerifiableInference.Desc.Kinds.Norm.lPd
    rw [show (letI := sizesOf G.W.hS; VerifiableInference.Desc.Kinds.Norm.d) = 5120 from N.d]
    decide
  rw [k6_blocks] at hb
  unfold P4.k6Hear at hb
  obtain ⟨ms, hs⟩ : ∃ ms, seatedClaims G.W (G.built.size - 1) ms = some b := by
    cases hB : P4.headBefore Z G with
    | none =>
      rw [hB] at hb
      simp at hb
    | some ms =>
      rw [hB] at hb
      exact ⟨ms, Option.mem_toList.1 hb⟩
  refine ⟨?_, ?_⟩
  · have hp : b.place = ⟨1, some (G.built.size - 1), 4, .K6⟩ := by
      obtain ⟨b0, h0, rfl⟩ := seatedClaims_some hs
      unfold blockClaims at h0
      obtain ⟨iU3, -, rfl⟩ := Option.map_eq_some_iff.mp h0
      rfl
    have e24 : G.built.size - 1 = 24 := by
      have := (IM.ground_gets hS hR hZ hG).1
      omega
    rw [hp, e24]
  · rw [k6_rounds_seated hs (by rw [N.lt]; decide), hw, N.lt, hl]
    exact of_decide_eq_true k6_rounds_written

/-- **THE ROW IN ITS USER's LETTERS.** The conclusion is ProofFile.Sk.Lst listAt (N
b.place) b.rounds, unfolded. -/
theorem k6_lists_at (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (hZ : ProofFile.pubPlain OnBytes.secondHashFunction P.pol lay P.KL = .ok Z)
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Z = some G) (N : Place → String)
    (hN : N ⟨1, some 24, 4, .K6⟩ = "H:4") :
    ∀ b ∈ (P4.k6Lot Z).blocks G, b.rounds = [] ∨ b.rounds = listAt (N b.place) := by
  intro b hb
  obtain ⟨hp, hr⟩ := k6_rounds_row hS hR hZ hG b hb
  exact Or.inr (by rw [hp, hN]; exact hr)

/-- The lot brings no batching. -/
theorem k6_no_batch (Z : ProofFile.Pub) (G : ProofFile.Ground) (a : Place) : (P4.k6Lot Z).batch G a = none :=
  rfl

end Johnson.AtFull.Rounds

#print axioms Johnson.AtFull.Rounds.k6_rounds_seated
#print axioms Johnson.AtFull.Rounds.k6_rounds_written
#print axioms Johnson.AtFull.Rounds.k6_rounds_bent
#print axioms Johnson.AtFull.Rounds.k6_rounds_row
#print axioms Johnson.AtFull.Rounds.k6_lists_at
#print axioms Johnson.AtFull.Rounds.k6_no_batch
