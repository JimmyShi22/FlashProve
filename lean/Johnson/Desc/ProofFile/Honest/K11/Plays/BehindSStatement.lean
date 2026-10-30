-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K11/Plays/BehindSStatement.lean: THE THREAD's DEBT `BehindS`
(Honest/Thread/PaysS.lean: `Behind` asked from the pair of the thread and what is said) AT THE
MERGE's MEMBER, WITH ITS PREMISES ON THE STATE BEHIND STATED FROM THAT PAIR: STATEMENTS ALONE: two
definitions of propositions. NOTHING IS PROVED IN THIS FILE, and neither is one of the library's
goals: they are lemmas' statements.

Why. As in AcceptedSStatement.lean of this folder: `HeadMergeBehind` (BehindStatement.lean) and
`HeadMergeBehindOf` (RidersStatement.lean) take their premises at every stand at which the thread
holds (`Thr`); the frame asks them from the pair.

  `HeadMergeBehindS`     `HeadMergeBehind`'s text with the pair for the thread in its three premises
                         (the public form behind · the promise behind · the riders behind) and
                         `BehindS T Said b` for its end; Said is a variable
  `HeadMergeBehindOfS`   `HeadMergeBehindOf`'s text likewise: the rider is a list of clauses; the
                         clauses that span the member stay (`StaysBy`: no thread in it); each clause
                         that begins behind the member is one on the head's own part that the kind's
                         clause of keeps lays

Limits. THE FORM BEHIND (both halves) IS A PREMISE: it is shown at no thread. So is the tie from the
kind's clause into the thread's letter keeps. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K11.Plays.RidersStatement
import Johnson.Desc.ProofFile.Honest.Thread.SharesS

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K11
open VerifiableInference.Desc (Claim Place)
open VerifiableInference.Desc.First (S)
open Johnson.Desc.First.ForkMerge (HeadMergeP headClaimMergeKind)
open Johnson.Desc.First.ForkMerge.Returns (K11Keeps)

/-- The statement. Not proved here; a lemma's statement, none of the library's goals. -/
def HeadMergeBehindS : Prop :=
  ∀ (Bk : ProverCoinCounts) (V W X Pb : Type) (T : Thread Bk S Claim V W X Pb)
    (Said : Nat → Coins Bk → Mid W X → Prop) (b : Nat) (P : HeadMergeP)
    (name : String) (pl : Place),
    T.bs[b]? = some (IM.seatedAs ProofFile.sameReply (headClaimMergeKind P) name pl) →
    (∀ s s', K11Keeps P s s' → T.keeps b s s') →
    (∀ blk k s m E ds y cols s', ThrS T Said b k s m E → T.Stepped blk k s m E ds y cols s' →
      T.bs[b]? = some blk → K11Keeps P s s' → T.form (b + 1) (T.seat k y.2 s') = true) →
    (∀ blk k s m E ds y cols s', ThrS T Said b k s m E → T.Stepped blk k s m E ds y cols s' →
      T.bs[b]? = some blk → K11Keeps P s s' → T.formP (b + 1) (T.seat k y.2 s')) →
    (∀ blk k s m E ds y cols s', ThrS T Said b k s m E → T.Stepped blk k s m E ds y cols s' →
      T.bs[b]? = some blk → K11Keeps P s s' → T.rides (b + 1) y.2.st.input s') →
    BehindS T Said b

/-- The statement where the rider is a list of clauses. Not proved here; a lemma's statement, none
of the library's goals. -/
def HeadMergeBehindOfS : Prop :=
  ∀ (Bk : ProverCoinCounts) (V W X Pb : Type) (T : Thread Bk S Claim V W X Pb)
    (Said : Nat → Coins Bk → Mid W X → Prop) (b : Nat) (P : HeadMergeP)
    (name : String) (pl : Place) (cs : List (RiderCl W S)),
    T.bs[b]? = some (IM.seatedAs ProofFile.sameReply (headClaimMergeKind P) name pl) →
    (∀ c w s, T.rides c w s ↔ ridersOf cs c w s) →
    (∀ s s', K11Keeps P s s' → T.keeps b s s') →
    (∀ blk k s m E ds y cols s', ThrS T Said b k s m E → T.Stepped blk k s m E ds y cols s' →
      T.bs[b]? = some blk → K11Keeps P s s' → T.form (b + 1) (T.seat k y.2 s') = true) →
    (∀ blk k s m E ds y cols s', ThrS T Said b k s m E → T.Stepped blk k s m E ds y cols s' →
      T.bs[b]? = some blk → K11Keeps P s s' → T.formP (b + 1) (T.seat k y.2 s')) →
    (∀ c ∈ cs, c.lo ≤ b → b + 1 ≤ c.hi → StaysBy T b c) →
    (∀ c ∈ cs, c.lo = b + 1 → ∃ hi Q, c = riderHead (b + 1) hi Q ∧
      ∀ s s', K11Keeps P s s' → ∃ a, s'.here = .head a ∧ Q a) →
    BehindS T Said b

end ProofFile.Honest.K11
