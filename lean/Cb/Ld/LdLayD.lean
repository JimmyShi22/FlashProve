-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdLayD.lean: zero knowledge of a reference request, reduced to data: the record
`LdReqRefLayD` on places, layouts and data maps, and the statement that it gives the three clauses
`lay`, `layT`, `layB`. (what is reduced: the three hypotheses `lay`, `layT`, `layB` of `LdReqRefDS`,
Cb/Req1/LdReqRefStd.lean; not to data alone, and only under the hypotheses of
`Spec.ldReqRefLay_data`: see "What the clauses are made of")

In standard terms: book-keeping for the honest prover's side of a request's sub-protocol, a chain of
interactive oracle reductions. The file has one record of conditions (which entries of earlier
oracle messages a later step uses, who reads which entries in between, how each message is laid out;
what its clauses are made of: under "Main names") and one statement that, under further hypotheses,
derives three hypotheses on honest provers from it.

A record and one statement (`Cb.Spec.ldReqRefLay_data`); its proof is in Cb/Ld/LdLayDProofs.lean; it
is applied in Cb/Ld/LdLayDTopProofs.lean and Cb/Obj/LdObjectDataRefJU.lean.

Why: oracle messages that hold masks go out early; later blocks use entries of them; in between
nobody looks. In the record of the reference request with standard senders (`LdReqRefDS`,
Cb/Req1/LdReqRefStd.lean) this stands as three hypotheses, `lay`, `layT`, `layB`, which unfold,
block for block, to "given all that has been shown the block's masks are still uniform" (exactly:
`Honest.Fresh`, Ior/KnowCollRulesMask.lean) and "no step before the block reads them": properties of
honest provers.
The request: first (one first sending) ; the segments of L, each with its closing ; the last
segment T ; the final batching.

Main names:
  `LdReqRefLayD Q pp R first b L T` (Q: what is asked of a layout: a parameter,
    Cb/Ld/LdLayDKit.lean; `LdLayQ.ok`: the layout's own conditions as they stand):
    `segs`: `L.LayD Q pp (first.LaysD Q)` (Cb/Ld/LdLayDList.lean): for each segment: what zero
      knowledge asks of its body, beside its hypotheses, in the form `A.ZkD`
      (Cb/Ld/LdLayDBody.lean), at the blocks that its entry step's own condition hands on from
      blocks pending before it;
    `last`: the same for the last segment's body;
    `fin`: some block pending before the last segment passes that segment (entry step, body, exit
      step: Cb/Ld/LdLayDTail.lean) and arrives as the block of the final batching's own masks, at a
      reading that holds what the batching reads.
  Which blocks are pending (`L.PendD`; a pending block: `LdPend`, Cb/Ld/LdMia.lean): behind the
    first sending: masks at injective families of free entries of a layout for which "first" is the
    standard sending, in either of two forms of reading; behind a segment: such masks of its
    closing's one sending, and blocks that cross the segment, each with the cut's condition
    (`S.CutD`, Cb/Ld/LdLayDList.lean); each set closed under pairs, smaller readings, other types
    for the same masks, the same own entries and values written otherwise. So each own entry of each
    block may have a holder of its own: a sending and a free entry of its layout; one block's masks
    may come from any number of sendings. No kind of block is wired to a message.
  What the clauses are made of. Equations "this sender is the standard sender of this layout and
    data map"; the layouts' laws (Q; sound: it gives `Y.OK`: among its clauses two are semantic:
    every member's sample is private under its pad; the encoders hide the given numbers of
    positions); injective families of free entries; `DatBlind` of each data map that a pending block
    passes; who reads what (the front's nested readings, the late blocks' places, "quiet"); every
    member of a closing's group is seen whole and holds no own entry of a block that crosses; the
    cuts' conditions; the configuration's further oracles have a string (`Nonempty I.C.E0.Str`, in
    `LdRefD.ZkD`, Cb/Ld/LdLayDBody.lean); the core is the ghost (`A.Ghost`,
    Cb/Req1/LdSegRefAll.lean); what is read back off the data with what is handed on is the further
    witness (in `LdSendD.StdBl`, Cb/Ld/LdLayDKit.lean); and, inside the front's places, some clauses
    on relations, on a claim, on numbers and tags (`LdRefF.OK`, Cb/Req1/LdSegRefCross.lean;
    `LdPreD.ZkOK`, Cb/Req1/LdSegRefLkpPreZk.lean; `LdPreD.OK`, Cb/Req1/LdSegRefLkpPre.lean): not all
    kinds are named here.
  The model's, named as such: `LdPend.StepD` at the maps `S.m`, `T.m`, `T.m'` of the entry and exit
    steps: these steps are free moves, their honest maps are the model's, and "overwriting the
    masks changes nothing else" is a condition on these maps. A write-up of ours
    (lean/CREDITS.md) has no counterpart:
    it has no such steps (neighbouring relations are equal); a request built as the
    write-up's meets the clause with maps that hand the messages on and compute the rest off what is
    not own.
    These clauses stand in this record, not in the model's duty (`LdModelDuty`). Also the model's:
    the sets of entries that its maps read, on which the conditions on places speak.
  The parameter Q is packaging (checked by reading the definitions; no theorem in this library says
    it): it stands in positive places only (in `StdBl` and `LaysD`; the sets of pending blocks grow
    with it, and a body's record asks memberships in them), so the record at a sound Q gives the
    record at `LdLayQ.ok`, and that one is sound: "for every sound Q" says no more and no less than
    the case `LdLayQ.ok`. It is there so that whoever has the layouts' conditions as theorems from
    data can put that form in.
  `Spec.ldReqRefLay_data`: E of characteristic pp; Q is sound; the model's side (`LdReqModel L T`);
    standard senders and the groups' own links in the segments and in the last body (`L.ProtoSA pp`,
    `T.A.ProtoSA pp`, Cb/Req1/LdReqStdAny.lean: the pads' field chosen sending by sending; not all
    clauses of the two records are named here: see `LdRefD.ProtoSA`, `LdRefS.ProtoSA` there);
    `LdReqRefLayD ..` ⇒ `lay` ∧ `layT` ∧ `layB`, letter for letter as in `LdReqRefDS`. (That "first"
    is a standard sending is not among the premises: the clause `first.LaysD` holds its own
    equation. The model's side is: every rule that carries a fact through a body takes the body's
    whole bundle, which is the model's side and the protocol's together.)

Limits: this file does not say that the record can be met. This file gives no instance that meets
its hypotheses, so as far as this file shows its theorems may hold of nothing.
That the record names no property of an honest prover, of a sender or of a link is one writer's
reading, not a theorem.


How it compares with the write-up's lemma on masks sent in advance: head of
Cb/Ld/LdMia.lean (the same idea as one inductive predicate on a program of moves);
the differences listed there hold here too: exact hiding only; no vectors of numbers of queries; a
message is one word.
A layout has one pads' field for the whole family of a sending: a sending whose family mixes
messages over the large field and over the base field must be taken all over the large field; the
write-up's first sending and each closing's sending are such.
This file says nothing on a splitting.
One wide reading serves all blocks of a body (each block's fact comes down to it as a smaller
reading); blocks that cross have readings of their own.
A block laid in the form "whichever new members" cannot cross the closing of a group that holds a
member of the same sending: what crosses is of the form "one new member", or pairs of such.
Not this file's, but the request's term lacks them: the fold's fresh mask goes out in the fold's own
round (the write-up then moves it forward), and the reply's round before the last sending of
cells.
A body's own sendings lay no masks (so does the write-up's request: all masks of a segment's
blocks lie in messages sent before it; only its corollary on the range check, stated by itself, is
wider).
A block that crosses a closing lies in messages that are no members of that closing's group.
This file has no form for sets of instances: it speaks of one statement at a time (the
write-up uses its lemma for N instances, for the request followed by the test for linear
constraints).
The reference segment is Cb/Req1/LdSegRefAll.lean's: whether it has the last
form that the write-up gives to the batching of tensor rows is not this file's matter.
That a mask stays uniform where the honest prover can give up needs no clause: the calculus speaks
at each value of the verifier's randomness that is not withheld, and the withheld set is covered by
a set that the core fixes.

Terms: lean/GLOSSARY.md.
"The write-up": one of our own texts on this protocol (lean/CREDITS.md); it is not in this
repository.
-/
import Cb.Ld.LdLayDList
import Cb.Ld.LdLayDTail
import Cb.Req1.LdReqStdAny

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood IOR IOR.Chain

/-- The record. -/
structure LdReqRefLayD {F E Kc : Type} [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E]
    (Q : LdLayQ E) (pp : ℕ) (R : LdORE F E Kc) {a : LdStage E Kc} (first : LdSendD a)
    (b : LdStage E Kc) (L : LdRefL E Kc R.ix first.tgt b) (T : LdRefT R b) : Prop where
  segs : L.LayD Q pp (first.LaysD Q)
  last : T.A.ZkD Q pp fun γ => ∃ β, L.PendD Q pp (first.LaysD Q) β ∧ LdPend.StepD T.m β γ
  fin  : ∃ (Rd : R.S.Ent → Prop) (Rr : R.S.O → Prop), (∀ n, R.Rd n → Rd n) ∧ ∃ β, L.PendD Q pp (first.LaysD Q) β ∧
           T.TailD Q pp β (⟨Rd, Rr, R.X.atOwn R.X.wAt, R.X.mask.Mk, fun M => R.X.atVal R.X.wAt M⟩ : LdPend R.X.src)

/-- `lay`, `layT`, `layB` from `LdReqRefLayD`. (not all hypotheses are named here: see the statement
below) -/
def Spec.ldReqRefLay_data : Prop :=
  ∀ (F E Kc : Type) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E] (pp : ℕ) [CharP E pp]
      (R : LdORE F E Kc) (a : LdStage E Kc) (first : LdSendD a) (b : LdStage E Kc)
      (L : LdRefL E Kc R.ix first.tgt b) (T : LdRefT R b) (Q : LdLayQ E),
    Q.Sound → LdReqModel L T → L.ProtoSA pp → T.A.ProtoSA pp → LdReqRefLayD Q pp R first b L T →
    L.LayJ pp (ldReqRef1 R first b L T).base₀ ∧
    T.A.ZkAt pp (fun f =>
      ∃ g,
        L.LaidJ (ldReqRef1 R first b L T).base₀ g ∧
        ∀ Y : MaskFact b.J.W → Prop, Y g → T.entry.After Y f) ∧
    ∃ (Rd : R.S.Ent → Prop) (Rr : R.S.O → Prop),
      (∀ n, R.Rd n → Rd n) ∧
      ∃ g,
        L.LaidJ (ldReqRef1 R first b L T).base₀ g ∧
        ∀ Y : MaskFact b.J.W → Prop, Y g →
          T.tail.After Y
            (R.X.src.wideFact Rd Rr (R.X.atOwn R.X.wAt) R.X.mask.Mk fun M => R.X.atVal R.X.wAt M)

end Cb
