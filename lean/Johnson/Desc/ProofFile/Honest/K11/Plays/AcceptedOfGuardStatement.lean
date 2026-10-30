-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K11/Plays/AcceptedOfGuardStatement.lean: THE THREAD's DEBT `Accepted`
(Honest/Thread/Pays.lean) AT THE MEMBER THAT IS THE MERGE OF THE CLAIMS ON THE WEIGHTS, WITH ITS ONE
DEBT SAID AS A TEST WITH CODE ON THE FIRST CHAIN's SHAPE: STATEMENTS ALONE: two, each a definition
of a proposition. NOTHING IS PROVED IN THIS FILE, and neither is one of the library's goals: they
are lemmas' statements.

  `ReadyIsReady`               the two definitions of "the verifier's state is ready for the merge's
                               decision" are one sentence: `MergeReady`
                               (Honest/K11/Plays/AcceptedStatement.lean) and `StateReady`
                               (Johnson/Desc/K11/Shape/StepStatement.lean)
  `HeadMergeAcceptedOfGuard`   THE THREAD T IS A VARIABLE. Under member and half, as in
                               `HeadMergeAccepted`, and
                                 guardAt   A DEBT: from the thread in front: the kind's test
                                           (`mergeGuardB P`) says yes at the shape of the verifier's
                                           state (`chainSh`, Johnson/Desc/First/Shape/Chain.lean):
                               `Accepted T fall b` at every fall

Limits. The three premises are shown at no thread. guardAt is a debt still: a Bool at every stand of
the thread; that the shape's own run pays it is not said here. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K11.Plays.AcceptedStatement
import Johnson.Desc.K11.Shape.StepStatement

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K11
open OnBytes.Model (WsClaim)
open VerifiableInference.Desc (Claim Place)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.Shape (chainSh)
open Johnson.Desc.First.ForkMerge (HeadMergeP headClaimMergeKind)
open Johnson.Desc.First.ForkMerge.ShapeStep (mergeGuardB StateReady)

/-- The statement that the two definitions are one sentence. Not proved here; a lemma's statement,
none of the library's goals. -/
def ReadyIsReady : Prop := ∀ (P : HeadMergeP) (s : S), MergeReady P s ↔ StateReady P s

/-- The statement. The letters: as in `HeadMergeAccepted`. Not proved here; a lemma's statement,
none of the library's goals. -/
def HeadMergeAcceptedOfGuard : Prop :=
  ∀ (Bk : ProverCoinCounts) (W₀ Rc Xi Tr X Pb : Type)
    (T : Thread Bk S Claim (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Pb) (b : Nat)
    (P : HeadMergeP) (claims : Xi → List Fmt.Drawn → List WsClaim) (weights : W₀ → Weights)
    (name : String) (pl : Place),
    T.bs[b]? = some (IM.seatedAs ProofFile.sameReply (headClaimMergeKind P) name pl) →
    (T.hs.find? fun g => g.place == pl) = some (headMergeHalf claims weights P) →
    (∀ k s m E, Thr T b k s m E → mergeGuardB P (chainSh s) = true) →
    ∀ fall, Accepted T fall b

end ProofFile.Honest.K11
