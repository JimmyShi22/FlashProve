-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
AtFullSide/K1/FirstScriptFixed.lean: THE TREES OF THE FIRST CHAIN's SCRIPT AT THE BASE PROVER ARE FIXED IN TIME: a tree that is declared before a border
is fixed by the challenges before that border. One statement with its proof.

  treesFixed_first   **the statement**, at firstScriptAt (AtFullSide/K1/FirstScript.lean), under the head and the maker's return alone

How. ofLots_hfix (Honest/Thread/ScriptLots.lean) at front 0 asks that no tree's table reads more of its member's own challenges than
the member has rounds. Each member that declares a tree is K1's, the code switch's or number 354 (the field trees of joinFit_first).
K1's and the code switch's tables read none (off_at_join, Honest/K5/Law/OffAtJoin.lean); at 354 the bound is off_at_354
(Honest/K12/OffAt354.lean), at the proximity test's job, whose stages are the written plan's under the head.

Limits. The head h and the return hA are hypotheses. It speaks of when the trees are fixed: nothing on what they hold. That the first
thread's Script is firstScriptAt is not said here. This file proves nothing about soundness, completeness, hiding or any other
property of the protocol.
-/
import AtFullSide.K1.FirstScript
import Johnson.Desc.ProofFile.Honest.K5.Law.OffAtJoin
import Johnson.Desc.ProofFile.Honest.K12.OffAt354

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace ProofFile.Honest.K1
open VerifiableInference.Desc (Chain)
open OnBytes.Maker (WholeD)
open P5J (AtMgA TS)
open ProofFile.Honest.FirstThread

variable {W₀ : Type} {Z : VerifierAndGoals.PublicFiles} {I : WiderIn W₀} {S : OnBytes.HonestTrace.Sz} {Op : OnlineProverArguments}
  {A : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit} {D : WholeD} {r : LPFD.Full.RunPF} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **THE TREES OF THE FIRST CHAIN's SCRIPT ARE FIXED IN TIME.** -/
theorem treesFixed_first (h : AtMgA OnBytes.secondHashFunction Z D r A.Z Np cF x)
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL (onlineProverPartsInUse I OnBytes.secondHashFunction S Op) = .ok A) :
    ∀ b, b ≤ cF.blocksInOrder.length → ∀ j, j < treesTo cF.blocksInOrder b →
      (firstScriptAt I S Op A cF).fixed (.own j) ≤ roundsTo cF.blocksInOrder b := by
  intro b hb j hj
  obtain ⟨pl, -, e⟩ := otherSenders_at_head h hA
  have F := joinFit_first h hA
  have hst : (testJobAt I S A.Z A.G pl).p.nums.stages = H2K.Member.piLFull.nums.stages := by
    show (H2U.p12OfMade A.Z.made).nums.stages = _
    rw [K12.AtProof.numbersL_at_head h.toAtMg, K12.Light.nums_head_L h.toAtMg]
  have hoff := ProofFile.Honest.K5.off_at_join (wit := witB I A.Z) (own₀ := ()) (A₀ := switchShareB I S A cF)
    F.trees
    (K2.Law.shareIn_add_left _ _)
    (fun _ hm k => ProofFile.Honest.K5.switchShareAt_off_zero cF.blocksInOrder 0 A.Z A.G _ _ noTree hm k)
    (by
      intro c hc hs blk hblk k hk
      rw [e] at hc ⊢
      have hc' : c ∈ (testShareOf I S A cF pl).tn := by
        rcases List.mem_append.1 hc with h1 | h1
        · exact absurd h1 hs
        · exact h1
      have ec : c = 354 := List.mem_singleton.1 hc'
      subst ec
      rw [Others.add_tl_right hs]
      show (K12.testTl 0 (testJobAt I S A.Z A.G pl) () (roundsTo cF.blocksInOrder 354)
        testOk 354 noTree 354).off k ≤ _
      unfold K12.testTl
      rw [if_pos rfl]
      exact K12.off_at_354 h.toAtMg 0 _ hst () _ _ blk hblk k hk)
  have e' := ofLots_hfix cF.blocksInOrder 0 (cellsB I A.Z) tokB
    (joinPl cF.blocksInOrder (k1MembersW (jobTwoAt S A.Z A.G) (jobLaterAt S A.Z A.G) (jobWAt Op A.Z A.G))
      (otherSendersAt I S A cF))
    (joinTl (witB I A.Z) () (k1MembersW (jobTwoAt S A.Z A.G) (jobLaterAt S A.Z A.G) (jobWAt Op A.Z A.G))
      (otherSendersAt I S A cF))
    (joinMl cF.blocksInOrder 0 (P5J.At.arr A.Z) (witB I A.Z) ()
      (k1MembersW (jobTwoAt S A.Z A.G) (jobLaterAt S A.Z A.G) (jobWAt Op A.Z A.G))
      (otherSendersAt I S A cF))
    hoff b hb j hj
  rw [Nat.zero_add] at e'
  exact e'

end ProofFile.Honest.K1

#print axioms ProofFile.Honest.K1.treesFixed_first
