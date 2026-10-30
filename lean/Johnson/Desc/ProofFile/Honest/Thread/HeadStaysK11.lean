-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Thread/HeadStaysK11.lean: lemmas of the form `StaysBy` (Riders.lean)
for rider clauses about the output head's own part of the verifier's state, at the merge in the
head's segment (kind K11). They continue HeadStays.lean and HeadStaysK3.lean, which cover the four
sub-protocols before it. No definition.

The fact about the merge is not proved here. It is `headStaysPastMerge`
(Honest/K11/Plays/Riders.lean): a fact on
the head's own part that reads none of the fields `wo`, `F`, `Fm` and `slot` survives a step that
satisfies the kind's clause `K11Keeps`. This file puts it into the form `StaysBy`, first for any
such fact, then for three clauses of the list `csHead` (CsHead.lean).

  1  `staysBy_head_k11`   for any fact `Q` that reads none of the four fields
  2  `staysBy_x_k11`, `staysBy_t_k11`   the clauses on the fields `x` and `t`
  3  `staysBy_fold_k11`   a clause on the number `tl.foldDrawn`

Limits.
  * Each lemma has the hypothesis `hk`: the thread's `keeps` at `b` gives `K11Keeps`. It is not
    proved here at any thread.
  * The clause `st 24` of `csHead`, which also holds on both sides of the merge, is not covered: its
    statement is a parameter of the list.
  * The lemmas prove no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K11.Plays.Riders

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc.First (S HeadOwn)

variable {Cl V W X Pb : Type} {Bk : ProverCoinCounts} (T : Thread Bk S Cl V W X Pb)

/-- A fact `Q` on the head's own part survives the merge, if `Q` reads none of the fields `wo`, `F`,
`Fm` and `slot`. -/
theorem staysBy_head_k11 {P : Johnson.Desc.First.ForkMerge.HeadMergeP} {b lo hi : Nat}
    {Q : HeadOwn → Prop}
    (hk : ∀ s s', T.keeps b s s' → Johnson.Desc.First.ForkMerge.Returns.K11Keeps P s s')
    (hQ : ∀ a wo F Fm slot, Q a → Q { a with wo := wo, F := F, Fm := Fm, slot := slot }) :
    StaysBy T b (riderHead lo hi Q) :=
  fun _ s s' hK h => ProofFile.Honest.K11.headStaysPastMerge P s s' Q hQ (hk s s' hK) h

/-- The clause "the field `x` is set" survives the merge. -/
theorem staysBy_x_k11 {P : Johnson.Desc.First.ForkMerge.HeadMergeP} {b lo hi : Nat}
    (hk : ∀ s s', T.keeps b s s' → Johnson.Desc.First.ForkMerge.Returns.K11Keeps P s s') :
    StaysBy T b (riderHead lo hi fun a => a.x.isSome = true) :=
  staysBy_head_k11 T hk fun _ _ _ _ _ h => h

/-- The clause "the field `t` is set" survives the merge. -/
theorem staysBy_t_k11 {P : Johnson.Desc.First.ForkMerge.HeadMergeP} {b lo hi : Nat}
    (hk : ∀ s s', T.keeps b s s' → Johnson.Desc.First.ForkMerge.Returns.K11Keeps P s s') :
    StaysBy T b (riderHead lo hi fun a => a.t.isSome = true) :=
  staysBy_head_k11 T hk fun _ _ _ _ _ h => h

/-- A clause "the number `tl.foldDrawn` is `n`" survives the merge. -/
theorem staysBy_fold_k11 {P : Johnson.Desc.First.ForkMerge.HeadMergeP} {b lo hi n : Nat}
    (hk : ∀ s s', T.keeps b s s' → Johnson.Desc.First.ForkMerge.Returns.K11Keeps P s s') :
    StaysBy T b (riderHead lo hi fun a => a.tl.foldDrawn = n) :=
  staysBy_head_k11 T hk fun _ _ _ _ _ h => h

end ProofFile.Honest

#print axioms ProofFile.Honest.staysBy_head_k11
#print axioms ProofFile.Honest.staysBy_x_k11
#print axioms ProofFile.Honest.staysBy_t_k11
#print axioms ProofFile.Honest.staysBy_fold_k11
