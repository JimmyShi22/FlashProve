-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K11/Plays/AcceptedSStatement.lean: THE THREAD's DEBT `AcceptedS`
(Honest/Thread/PaysS.lean: `Accepted` asked from the pair of the thread and what is said) AT THE
MERGE's MEMBER, WITH ITS PREMISE ON THE STATE STATED FROM THAT PAIR: STATEMENTS ALONE: three
definitions of propositions. NOTHING IS PROVED IN THIS FILE, and none is one of the library's goals:
they are lemmas' statements.

Why. `HeadMergeAccepted` (AcceptedStatement.lean of this folder) ends in `Accepted T fall b` and
takes "the state is ready" at every stand at which the thread holds (`Thr`). The frame asks a
premise from the thread in front to the state to be stated from the pair (`ThrS T Said`). A payer
that goes by the library's facts at reached states has the pair in hand, not the thread alone, as
ours does (MaskAtHead.lean of this folder). From `Accepted` the frame's own lemma gives `AcceptedS`;
but the premise from `Thr` could then not be paid.

  `HeadMergeSteppedAt`          AT ONE STAND, NO THREAD: the member is the kind's block at its seat;
                                the row's half stands in the list; THE STATE IS READY (`MergeReady P
                                s`); the challenges fit; the half's play has moved: then the
                                member's step says yes on that play
  `HeadMergeAcceptedS`          so, where the state is ready at every stand at which the pair holds:
                                `AcceptedS T Said fall b`, at every letter Said and every fall
  `HeadMergeAcceptedOfGuardS`   the same from the test with code on the state's shape
                                (`mergeGuardB`, Johnson/Desc/K11/Shape/StepStatement.lean)

Limits. Those of AcceptedStatement.lean: that the state is ready is a premise, shown at no thread;
the member and the half are premises on the thread's letters. Nothing on what holds behind the yes.
Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K11.Plays.AcceptedOfGuardStatement
import Johnson.Desc.ProofFile.Honest.Thread.PaysS

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K11
open OnBytes.Model (WsClaim)
open VerifiableInference.Desc (Claim Place)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.Shape (chainSh)
open Johnson.Desc.First.ForkMerge (HeadMergeP headClaimMergeKind)
open Johnson.Desc.First.ForkMerge.ShapeStep (mergeGuardB)

/-- The statement at one stand. Not proved here; a lemma's statement, none of the library's goals.
-/
def HeadMergeSteppedAt : Prop :=
  ∀ (Bk : ProverCoinCounts) (W₀ Rc Xi Tr X Pb : Type)
    (T : Thread Bk S Claim (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Pb) (b : Nat)
    (P : HeadMergeP) (claims : Xi → List Fmt.Drawn → List WsClaim) (weights : W₀ → Weights)
    (name : String) (pl : Place),
    T.bs[b]? = some (IM.seatedAs ProofFile.sameReply (headClaimMergeKind P) name pl) →
    (T.hs.find? fun g => g.place == pl) = some (headMergeHalf claims weights P) →
    ∀ blk, T.bs[b]? = some blk → ∀ k s m E ds y cols, MergeReady P s →
      drawsFit blk.rounds ds = true → T.Moved blk k m E ds y cols →
      ∃ s', T.Stepped blk k s m E ds y cols s'

/-- The statement from the pair. Not proved here; a lemma's statement, none of the library's goals.
-/
def HeadMergeAcceptedS : Prop :=
  ∀ (Bk : ProverCoinCounts) (W₀ Rc Xi Tr X Pb : Type)
    (T : Thread Bk S Claim (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Pb)
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc Xi Tr) X → Prop) (b : Nat)
    (P : HeadMergeP) (claims : Xi → List Fmt.Drawn → List WsClaim) (weights : W₀ → Weights)
    (name : String) (pl : Place),
    T.bs[b]? = some (IM.seatedAs ProofFile.sameReply (headClaimMergeKind P) name pl) →
    (T.hs.find? fun g => g.place == pl) = some (headMergeHalf claims weights P) →
    (∀ k s m E, ThrS T Said b k s m E → MergeReady P s) →
    ∀ fall, AcceptedS T Said fall b

/-- The statement from the pair, at the test on the shape. Not proved here; a lemma's statement,
none of the library's goals. -/
def HeadMergeAcceptedOfGuardS : Prop :=
  ∀ (Bk : ProverCoinCounts) (W₀ Rc Xi Tr X Pb : Type)
    (T : Thread Bk S Claim (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Pb)
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc Xi Tr) X → Prop) (b : Nat)
    (P : HeadMergeP) (claims : Xi → List Fmt.Drawn → List WsClaim) (weights : W₀ → Weights)
    (name : String) (pl : Place),
    T.bs[b]? = some (IM.seatedAs ProofFile.sameReply (headClaimMergeKind P) name pl) →
    (T.hs.find? fun g => g.place == pl) = some (headMergeHalf claims weights P) →
    (∀ k s m E, ThrS T Said b k s m E → mergeGuardB P (chainSh s) = true) →
    ∀ fall, AcceptedS T Said fall b

end ProofFile.Honest.K11
