-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K11/Plays/RidersStatement.lean: AT THE MEMBER THAT IS THE MERGE OF THE
CLAIMS ON THE WEIGHTS, WHERE A THREAD's RIDER IS A LIST OF CLAUSES (Honest/Thread/Riders.lean): THE
CLAUSE THAT THE MEMBER LAYS; WHAT OF THE HEAD's OWN PART STAYS PAST IT; AND THE THREAD's DEBT
`Behind` (Honest/Thread/Pays.lean): STATEMENTS ALONE: four, each a definition of a proposition.
NOTHING IS PROVED IN THIS FILE, and none of the four is one of the library's goals: they are lemmas'
statements.

THE THREAD T AND THE MEMBER's NUMBER b ARE VARIABLES.
  `HeadMergeLaysOf`      under member (the member number b is the kind's block as it stands alone at
                         a seat): `LaysAt T b` of every clause `riderHead lo hi Q` whose sentence Q
                         on the head's own part the kind's clause `K11Keeps`
                         (Johnson/Desc/K11/Returns/KeepsStatement.lean) gives behind
  `HeadMergeLaysWo`      under member: `LaysAt T b` of the clause "the chain stands in the head's
                         link, and what the merge left is laid"
                         (`riderHead lo hi fun a => a.wo.isSome = true`), at every lo and hi
  `HeadStaysPastMerge`   no thread in it: under `K11Keeps`: a sentence Q on the head's
                         own part that does not read the four fields which the merge turns (what it
                         left, the ledger, the ledger kept aside, the next free slot) holds behind
                         if it holds in front
  `HeadMergeBehindOf`    `Behind T b`, under:
                           member
                           rides   the thread's letter rides is the rider of a list of clauses cs
                           keeps   the thread's letter keeps at b follows from `K11Keeps`
                           form    from the thread in front, the member's step and `K11Keeps`: the
                                   thread's test form behind b passes
                           formP   A DEBT: from the same three: the thread's letter formP behind b
                           stays   each clause of cs that speaks in front of b and behind it stays
                                   past b (`StaysBy`): whoever lays the thread pays it
                           laid    each clause of cs that begins behind b is of the sort
                                   `riderHead`, with a sentence that `K11Keeps` gives behind

Limits. The premises are shown at no thread. formP is a debt in its own right. What the lemmas
themselves bring: that the member's step, its yes in hand, gives `K11Keeps`, and with it the clause
that the member lays. Not spent: that the challenges fit the rounds; the thread in front, but for
its rider. `HeadStaysPastMerge` does not serve a sentence that reads the ledger. Nothing on any
property.
-/
import Johnson.Desc.ProofFile.Honest.Thread.Riders
import Johnson.Desc.K11.Returns.KeepsStatement

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K11
open VerifiableInference.Desc (Claim Place)
open VerifiableInference.Desc.First (S HeadOwn)
open Johnson.Desc.First.ForkMerge (HeadMergeP headClaimMergeKind)
open Johnson.Desc.First.ForkMerge.Returns (K11Keeps)

/-- The statement on every clause of that sort which the kind's clause gives. Q: a sentence on the
head's own part. Not proved here; a lemma's statement, none of the library's goals. -/
def HeadMergeLaysOf : Prop :=
  ∀ (Bk : ProverCoinCounts) (V W X Pb : Type) (T : Thread Bk S Claim V W X Pb) (b : Nat) (P : HeadMergeP)
    (name : String) (pl : Place) (lo hi : Nat) (Q : HeadOwn → Prop),
    T.bs[b]? = some (IM.seatedAs ProofFile.sameReply (headClaimMergeKind P) name pl) →
    (∀ s s', K11Keeps P s s' → ∃ a, s'.here = .head a ∧ Q a) →
    LaysAt T b (riderHead lo hi Q)

/-- The statement on the clause that the member lays. Not proved here; a lemma's statement, none of
the library's goals. -/
def HeadMergeLaysWo : Prop :=
  ∀ (Bk : ProverCoinCounts) (V W X Pb : Type) (T : Thread Bk S Claim V W X Pb) (b : Nat) (P : HeadMergeP)
    (name : String) (pl : Place) (lo hi : Nat),
    T.bs[b]? = some (IM.seatedAs ProofFile.sameReply (headClaimMergeKind P) name pl) →
    LaysAt T b (riderHead lo hi fun a => a.wo.isSome = true)

/-- The statement on what stays. Q: a sentence on the head's own part. Not proved here; a lemma's
statement, none of the library's goals. -/
def HeadStaysPastMerge : Prop :=
  ∀ (P : HeadMergeP) (s s' : S) (Q : HeadOwn → Prop),
    (∀ a wo F Fm slot, Q a → Q { a with wo := wo, F := F, Fm := Fm, slot := slot }) →
    K11Keeps P s s' → (∃ a, s.here = .head a ∧ Q a) → ∃ a, s'.here = .head a ∧ Q a

/-- The statement on `Behind`. cs: the rider's clauses. Not proved here; a lemma's statement, none
of the library's goals. -/
def HeadMergeBehindOf : Prop :=
  ∀ (Bk : ProverCoinCounts) (V W X Pb : Type) (T : Thread Bk S Claim V W X Pb) (b : Nat) (P : HeadMergeP)
    (name : String) (pl : Place) (cs : List (RiderCl W S)),
    T.bs[b]? = some (IM.seatedAs ProofFile.sameReply (headClaimMergeKind P) name pl) →
    (∀ c w s, T.rides c w s ↔ ridersOf cs c w s) →
    (∀ s s', K11Keeps P s s' → T.keeps b s s') →
    (∀ blk k s m E ds y cols s', Thr T b k s m E → T.Stepped blk k s m E ds y cols s' →
      T.bs[b]? = some blk → K11Keeps P s s' → T.form (b + 1) (T.seat k y.2 s') = true) →
    (∀ blk k s m E ds y cols s', Thr T b k s m E → T.Stepped blk k s m E ds y cols s' →
      T.bs[b]? = some blk → K11Keeps P s s' → T.formP (b + 1) (T.seat k y.2 s')) →
    (∀ c ∈ cs, c.lo ≤ b → b + 1 ≤ c.hi → StaysBy T b c) →
    (∀ c ∈ cs, c.lo = b + 1 → ∃ hi Q, c = riderHead (b + 1) hi Q ∧
      ∀ s s', K11Keeps P s s' → ∃ a, s'.here = .head a ∧ Q a) →
    Behind T b

end ProofFile.Honest.K11
