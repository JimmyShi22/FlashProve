-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K11/Plays/GoodAllStatement.lean: THE FRAME's `Good` (Honest/Side.lean)
AT THE SIDE OF THE MERGE OF THE CLAIMS ON THE WEIGHTS, WITH NO PREMISE ON THE SUMCHECK's PART:
STATEMENTS ALONE: five, each a definition of a proposition. NOTHING IS PROVED IN THIS FILE, and none
of the five is one of the library's goals: they are lemmas' statements. WHAT FOLLOWS FROM `Good` IS
NOT SAID HERE.

`HeadMergeGood` (GoodStatement.lean of this folder) takes the field exact at the row's member number
1 for a premise. A law on the frame's masked sumcheck's part beside its simulator
(`exact_sumPart_field`, Honest/SumLaw/SumExact.lean) gives that field's text at a member WRITTEN
OUT, under three premises on public data beside the field's own. Here: that the row's member number
1 IS such a member; the three premises AT THE KIND's OWN DECLARED ROUNDS; and `Good`.

  `MergeShapeOk`      the call's shape passes the library's test on a shape (`shapeOk`,
                      Johnson/Desc/Part/MaskedSum4.lean), at every number of column bits
  `MergeStated`       the merge's declared rounds behind the batching round state just the call's
                      scalars, round by round, and no oracle message (`StatedBy`,
                      Honest/SumLaw/Fits.lean)
  `MergeBetaMarked`   among these rounds the one that samples the further variable's challenge marks
                      it as never 0 (`betaMarked`, Honest/SumLaw/BetaMarked.lean)
  `MergeSumMember`    under the two premises on σ of `HeadMergeGood`: the side's members are two:
                      number 0, the batching round, the frame's part that sends nothing, its
                      simulator; and: number 1, these rounds, the sumcheck's part lifted
                      (`headMergeSum`), the simulator beside it at the kind's place
  `HeadMergeGoodAll`  under these two and unspent (no entry of the book lets any part spend a coin
                      of a part of this row): `Good pre φ σ Bk ord chain firstTree A' B' On bud` at
                      A' := B' := False, On := True, bud := True

Limits. The three premises of `HeadMergeGoodAll` (the two on σ; unspent) are shown at no side and no
book. plays and acc hold from False: nothing is shown by them. Of exact: the law that is called
speaks of ONE PART AT A TIME, over the two stretches of coins that the part SPENDS, TAKEN as uniform
and independent, all else fixed before the coins: that the parts which own these stretches hand them
on so is the field fresh AT THOSE PARTS: it is not said here. The law holds at every job, right or
wrong: so it says nothing on whether the job is the protocol's. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K11.Plays.GoodStatement
import Johnson.Desc.ProofFile.Honest.SumLaw.BetaMarked
import Johnson.Desc.ProofFile.Honest.SumLaw.Fits

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K11
open OnBytes.Model (WsClaim)
open VerifiableInference.Desc (Claim Place Oracle)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Part.MaskedSum (shapeOk)
open Johnson.Desc.First.ForkMerge (HeadMergeP headClaimMergeKind mergeEntries)
open ProofFile.Honest.SumLaw (StatedBy betaMarked)

/-- The merge's declared rounds behind the batching round, each with no oracle message. -/
def sumRounds (lk work : Nat) : List (Fmt.DeclaredRound × List Oracle) :=
  (mergeEntries lk 1 work).tail.map fun e => ({ entry := e }, [])

/-- The statement on the shape. Not proved here; a lemma's statement, none of the library's goals.
-/
def MergeShapeOk : Prop := ∀ lk : Nat, shapeOk (headMergeShape lk) = true

/-- The statement on what the rounds state. Not proved here; a lemma's statement, none of the
library's goals. -/
def MergeStated : Prop :=
  ∀ lk work : Nat, StatedBy (scalarsOf (headMergeShape lk)) (sumRounds lk work)

/-- The statement on the mark. Not proved here; a lemma's statement, none of the library's goals. -/
def MergeBetaMarked : Prop :=
  ∀ lk work : Nat, betaMarked (headMergeShape lk) (sumRounds lk work) = true

/-- The statement on the side's members. d₀: the batching round as the kind's block declares it. Not
proved here; a lemma's statement, none of the library's goals. -/
def MergeSumMember : Prop :=
  ∀ (W₀ Rc Xi Tr X : Type) (σ : Side S Claim (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Xi)
    (P : HeadMergeP) (claims : Xi → List Fmt.Drawn → List WsClaim) (weights : W₀ → Weights)
    (name : String),
    σ.block = IM.seatedAs ProofFile.sameReply (headClaimMergeKind P) name (headMergePlace P) →
    σ.row = headMergeSided P claims weights →
    ∃ d₀ : Fmt.DeclaredRound, d₀.items.filter (· != .root) = [] ∧
      σ.members = [⟨0, [(d₀, [])], quietPart 1, quietSim ⟨headMergePlace P, 0⟩ 1⟩,
        ⟨1, sumRounds P.lay.lk P.work, headMergeSum P claims weights,
          sumSim ⟨headMergePlace P, 1⟩ (headMergeShape P.lay.lk)⟩]

/-- The statement. Not proved here; a lemma's statement, none of the library's goals. pre is tied to
no description. -/
def HeadMergeGoodAll : Prop :=
  ∀ (W₀ Rc Xi Tr X : Type) (σ : Side S Claim (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Xi)
    (φ : Face (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) Xi) (Bk : ProverCoinCounts) (ord : List Place)
    (chain firstTree : Nat) (pre : List (Nat × Nat × List Fmt.DeclaredRound)) (P : HeadMergeP)
    (claims : Xi → List Fmt.Drawn → List WsClaim) (weights : W₀ → Weights) (name : String),
    σ.block = IM.seatedAs ProofFile.sameReply (headClaimMergeKind P) name (headMergePlace P) →
    σ.row = headMergeSided P claims weights →
    (∀ j q, Bk.spentBy ⟨σ.block.place, j⟩ q = []) →
    Good pre φ σ Bk ord chain firstTree (fun _ _ _ _ => False) (fun _ _ _ _ => False)
      (fun _ _ _ _ => True) (fun _ _ _ => True)

end ProofFile.Honest.K11
