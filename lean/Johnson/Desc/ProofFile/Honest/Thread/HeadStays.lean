-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Thread/HeadStays.lean: lemmas of the form `StaysBy` (Riders.lean) for
rider clauses about the output head's own part of the verifier's state. A rider clause holds from
border `lo` to border `hi`; `StaysBy T b c` says that clause `c` survives sub-protocol number `b`,
given only what that sub-protocol's clause of `keeps` says. The file covers three sorts of
sub-protocol in the head's segment: the sending of the reads (kind K1), the draw of the smallness
test (kind K8) and a later commitment (kind K1). No definition.

The facts about these three sorts are not proved here. They are `head_stays_reads` and
`head_stays_commit` (Honest/K1/Law/KeepsReads.lean) and `keeps_head`
(Desc/K8/Honest/KeepsMark.lean). This
file puts them into the form `StaysBy`, first for any fact `P`, then for the clauses of the list
`csHead` (CsHead.lean).

  1  `staysBy_head_reads`, `staysBy_head_k8`, `staysBy_head_commit`   for any fact `P` that does not
     read what the sub-protocol changes
  2  `staysBy_x_reads`, `staysBy_x_k8`, `staysBy_x_commit`   the clause on the field `x`
  3  `staysBy_t_k8`, `staysBy_t_commit`   the clause on the field `t`
  4  `staysBy_fold_commit`   a clause on the number `tl.foldDrawn`

Limits.
  * Each lemma has the hypothesis `hk`: the thread's `keeps` at `b` gives the kind's own clause. It
    is not shown here at any thread.
  * The lookup argument on the digits, the merge and the sub-protocols after it are not covered.
  * No property of the protocol is proved.
-/
import Johnson.Desc.ProofFile.Honest.Thread.RidersStayH
import Johnson.Desc.ProofFile.Honest.K1.Law.KeepsReads
import Johnson.Desc.K8.Honest.KeepsMark

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc.First (S HeadOwn)

variable {Cl V W X Pb : Type} {Bk : ProverCoinCounts} (T : Thread Bk S Cl V W X Pb)

/-- A fact `P` on the head's own part survives the sending of the reads, if `P` reads none of the
four fields that this sub-protocol changes (`L`, `F`, `t`, `tl`). -/
theorem staysBy_head_reads {b lo hi : Nat} {P : HeadOwn → Prop}
    (hk : ∀ s s', T.keeps b s s' → ProofFile.Honest.K1.K1ReadsKeeps s s')
    (hP : ∀ a L F t tl, P a → P { a with L := L, F := F, t := some t, tl := tl }) :
    StaysBy T b (riderHead lo hi P) :=
  fun _ s s' hK h => ProofFile.Honest.K1.head_stays_reads P hP (hk s s' hK) h

/-- A fact `P` on the head's own part survives the draw of the smallness test, if `P` does not read
the field `tl`. -/
theorem staysBy_head_k8 {b lo hi : Nat} {P : HeadOwn → Prop}
    (hk : ∀ s s', T.keeps b s s' → VerifiableInference.Desc.First.K8.Honest.K8Keeps s s')
    (hP : ∀ a tl', P a → P { a with tl := tl' }) : StaysBy T b (riderHead lo hi P) :=
  staysBy_head_tl T
    (fun s s' hK _ ha => VerifiableInference.Desc.First.K8.Honest.keeps_head (hk s s' hK) ha) hP

/-- A fact `P` on the head's own part survives a later commitment, if `P` reads neither `L` nor
`F`. -/
theorem staysBy_head_commit {b lo hi : Nat} {P : HeadOwn → Prop}
    (hk : ∀ s s', T.keeps b s s' → ProofFile.Honest.K1.K1CommitKeeps s s')
    (hP : ∀ a L F, P a → P { a with L := L, F := F }) : StaysBy T b (riderHead lo hi P) :=
  fun _ s s' hK h => ProofFile.Honest.K1.head_stays_commit P hP (hk s s' hK) h

/-- The clause "the field `x` is set" survives the sending of the reads. -/
theorem staysBy_x_reads {b lo hi : Nat}
    (hk : ∀ s s', T.keeps b s s' → ProofFile.Honest.K1.K1ReadsKeeps s s') :
    StaysBy T b (riderHead lo hi fun a => a.x.isSome = true) :=
  staysBy_head_reads T hk fun _ _ _ _ _ h => h

/-- The clause "the field `x` is set" survives the draw of the smallness test. -/
theorem staysBy_x_k8 {b lo hi : Nat}
    (hk : ∀ s s', T.keeps b s s' → VerifiableInference.Desc.First.K8.Honest.K8Keeps s s') :
    StaysBy T b (riderHead lo hi fun a => a.x.isSome = true) :=
  staysBy_head_k8 T hk fun _ _ h => h

/-- The clause "the field `x` is set" survives a later commitment. -/
theorem staysBy_x_commit {b lo hi : Nat}
    (hk : ∀ s s', T.keeps b s s' → ProofFile.Honest.K1.K1CommitKeeps s s') :
    StaysBy T b (riderHead lo hi fun a => a.x.isSome = true) :=
  staysBy_head_commit T hk fun _ _ _ h => h

/-- The clause "the field `t` is set" survives the draw of the smallness test. -/
theorem staysBy_t_k8 {b lo hi : Nat}
    (hk : ∀ s s', T.keeps b s s' → VerifiableInference.Desc.First.K8.Honest.K8Keeps s s') :
    StaysBy T b (riderHead lo hi fun a => a.t.isSome = true) :=
  staysBy_head_k8 T hk fun _ _ h => h

/-- The clause "the field `t` is set" survives a later commitment. -/
theorem staysBy_t_commit {b lo hi : Nat}
    (hk : ∀ s s', T.keeps b s s' → ProofFile.Honest.K1.K1CommitKeeps s s') :
    StaysBy T b (riderHead lo hi fun a => a.t.isSome = true) :=
  staysBy_head_commit T hk fun _ _ _ h => h

/-- A clause "the number `tl.foldDrawn` is `n`" survives a later commitment. -/
theorem staysBy_fold_commit {b lo hi n : Nat}
    (hk : ∀ s s', T.keeps b s s' → ProofFile.Honest.K1.K1CommitKeeps s s') :
    StaysBy T b (riderHead lo hi fun a => a.tl.foldDrawn = n) :=
  staysBy_head_commit T hk fun _ _ _ h => h

end ProofFile.Honest

#print axioms ProofFile.Honest.staysBy_head_reads
#print axioms ProofFile.Honest.staysBy_head_k8
#print axioms ProofFile.Honest.staysBy_head_commit
#print axioms ProofFile.Honest.staysBy_x_reads
#print axioms ProofFile.Honest.staysBy_x_k8
#print axioms ProofFile.Honest.staysBy_x_commit
#print axioms ProofFile.Honest.staysBy_t_k8
#print axioms ProofFile.Honest.staysBy_t_commit
#print axioms ProofFile.Honest.staysBy_fold_commit
