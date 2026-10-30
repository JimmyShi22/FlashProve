-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Req1/LdReqRefLay.lean: where the masks of a reference request come from: laid down by the sending
before the segment that uses them, or carried across closings.

Definitions and statements (each a `Prop` in `Cb.Spec`); the proofs are in
Cb/Req1/LdReqRefLayProofs.lean.
The reference request r is the term `ldReqRef`, with its list L (`LdRefL`) of segments S (`LdRefS`)
and its last segment T (Cb/Req1/LdReqRef.lean). Facts: A `MaskFact W` is a reading `kc` of witnesses
of type W into a type `Kc`, a finite, non-empty type `Mk`, and a map `put : Mk → Kc → Kc`. It, and
"fresh after a chain": Cb/Req1/LdSegFresh.lean; wide facts: `LdStage.wideFact`
(Cb/Req1/LdSegCarry.lean); `After`, `Zk`: Cb/Req1/LdReq.lean.
Cb/Req1/LdReqRefZkP.lean reduces what honest-verifier zero knowledge asks of the reference request
(`r.Zk`), beside its hypotheses, under the hypotheses of its statement, to places and to
memberships: "the fact that this block needs is fresh at the entry of its segment". Here these
memberships are chained from segment to segment.

The convention (a write-up of ours (lean/CREDITS.md), in our own words).
  (1) The own masks of the blocks of a segment stand in oracle messages that the one sending of the
      closing before that segment sends with the next segment's first messages (for the first
      segment: the request's first sending: one first prover message).
      Exception: the inner masks of revealed maps that are linear in the index stand in the
      index-mask message of (2), not in the segment's messages.
  (2) The own masks of all batchings of tensor rows on the encoded index stand in one message, sent
      in the request's one first prover message. It is kept at every closing, is no member of a
      group that closes and is not held in a folded word: its masks cross the closings.

Main names:
  `S.New g` (the calculus: this row to `L.Lay`): the fact g, at the stage where the segment S ends,
    is laid down by S's one sending: the sending is `Fresh` for it, and the cut of the locations
    does not look at it (masks laid by the closing's one sending).
  `S.Enters g f`: the entry step of S hands the fact g on as f.
  `S.Carries g' g`: the whole segment hands the fact g' (at its first stage) on as g (at its last):
    masks that cross a whole body and a closing.
  `L.Laid base g`: g, at the stage where the list L ends, is: in "base", if L is empty; else, for
    the last segment S of L: `S.New g`, or `S.Carries g' g` for some g' that is laid at the end of
    the list before S.
  `L.Lay pp base`: for each segment S of L: what zero knowledge asks of its body (`A.ZkAt pp`),
    beside its hypotheses, at the facts f that `S.Enters g f` hands on from some g laid before S.
  `Spec.ldReqRefLay_after`: `L.Laid base g → L.segs.After base g`.
  `Spec.ldReqRefLay_mono`: `A.ZkAt pp` is monotone in the set of facts.
  `Spec.ldReqRefLay_segs`: `L.Lay pp base → L.ZkP pp base`.
  `Spec.ldReqRefLay_new`: `S.New g` gives: g is fresh after S, whatever was fresh before.
  `Spec.ldReqRefLay_enters`: the entry step hands a fact on, from the step's own condition:
    overwriting the masks changes neither the new explicit part nor, but by the overwriting, the new
    reading.
  `Spec.ldReqRefLay_cross`: the wide fact crosses a reference segment: under the hypotheses of its
    statement, `S.Carries g'` (the wide fact at S's last stage, sets written out), from:
    `S.Enters g'` (the wide fact at the body's entry); quiet for the front, the two senders of the
    body do not look; neither late block reads an own entry (each reads only entries of the wide
    reading that are not own); the closing: of the witness the other lot's link reads the group's
    members only and hands the rest on; every member of the group is seen whole and holds no own
    entry (the mask message is no member); the one sending's sender does not look; the cut reads new
    entries in RdN only.
  `Spec.ldReqRefLay`: for pp the characteristic of E (`[CharP E pp]`): `r.Zk` from: `L.OK pp`,
    `T.OK pp`, the final batching's conditions; `L.Lay pp` at the facts that are fresh behind the
    first sendings; the last segment's `A.ZkAt` at the facts handed on from facts laid before it; a
    fact laid before the last segment that its moves hand on as the wide fact of the final
    batching's own masks, in a reading that holds what the batching reads.

Limits: a gap, known: own masks of one block from two sendings. By the exception, a sumcheck of a
segment behind the first that ends at a map of the index has its hiding coefficients in the
segment's mask rows (laid by the closing before) and its inner masks in the index-mask message (laid
by the first sending, carried across closings): own masks of one block from two sendings. The
calculus has no rule that joins two facts into the fact of the pair, and "fresh after a chain"
(Cb/Req1/LdSegFresh.lean) is a recursion with two cases: the last link sends the masks, or it does
not look and they were fresh before. So, by reading of the definitions (no lemma, no counter-example
compiled): for that layout `L.Lay` cannot be met at such a segment: unmeetable, not unsound. Also by
reading only (no instance): another layout would meet it: an index-mask message of its own for each
segment, sent with the segment's first messages, member of no group, kept to the end: all own masks
of a block then come from one sending. Closed in: Ior/FreshJoin.lean (the rule that joins two facts
at one reading), Cb/Req1/LdReqS.lean (`r.ZkS`: the sets of fresh facts closed under join at each
segment's entry; the whole bundle from `r.Hyp` and it), Cb/Req1/LdReqRefLayJ.lean (`L.LaidJ`,
`L.LayJ`: this calculus in the closed sets). The records of Cb/Req1/LdReqRefFinal.lean and above ask
those; `L.Laid` of this file gives `L.LaidJ` (`Spec.ldReqRefLayJ_of`, Cb/Req1/LdReqRefLayJ.lean).
Meant: facts that are laid are wide; they are narrowed by "Enters". The second clause of `S.New`
(the cut of the locations does not look) is the locations' own premise: their prover computes
symbols of the word that is cut out of the new messages; so a fact survives them only if its reading
determines that cut. A narrow fact (a reading that holds little more than what the masks overwrite)
meets the clause only if the cut is constant. So: what `S.New` lays down are facts with a wide
reading, which shows every entry that the cut reads, and the one sending has to be `Fresh` for that
reading; the narrow facts that the blocks of the next segment use come from them through
`S'.Enters g f`: a step lets the new reading be any reading that the old one determines
(`Spec.ldReqRefLay_enters`). `L.Lay` asks `A.ZkAt` exactly at the facts f with g laid and
`Enters g f`.
Two wide readings. The reading W of `Spec.ldReqRefLay_cross` must show every member of the closing's
group whole (entries and randomness); the reading W inside `A.ZkAt`, with which the two late blocks
of the body get their own masks, need keep neither pads nor encoding randomness of what it need not
see.
They are different letters: the statements allow that.
This file does not say that a layout with (1), (2) meets the conditions: an instance's matter. It
says nothing on segments with two groups.
Terms: lean/GLOSSARY.md.
"The write-up": one of our own texts on this protocol (lean/CREDITS.md); it is not in this
repository.
-/
/- Limits: no theorem of this library states that the hypotheses of `ldReqRefLay` can be met
   together. -/
import Cb.Req1.LdReqRefZkP
import Cb.Req1.LdSegWholeAfter
import Cb.Req1.LdSegCarryClose
import Cb.Req1.LdSegRefTenLook

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood IOR IOR.Chain

namespace LdRefS
variable {E Kc : Type} [Field E] [Fintype E] {I : LdRefIx E}
  {a : LdStage E Kc} (S : LdRefS E Kc I a)

/-- Laid down by the one sending. -/
def New (g : MaskFact S.d.J.W) : Prop :=
  S.Qc.snd.link.H.Fresh S.K.R.c1.fold.tgt.J.rels.rel S.Qc.snd.link.P.bud g.kc g.Mk g.put ∧
  ∀ (w w' : S.Qc.loc.src.J.W) M, g.kc w' = g.put M (g.kc w) →
    S.Qc.loc.cut (S.Qc.loc.S.msgs w'.1) = S.Qc.loc.cut (S.Qc.loc.S.msgs w.1)

/-- the entry step hands g on as f -/
def Enters (g : MaskFact a.J.W) (f : MaskFact S.A.V.Fp.s0.J.W) : Prop :=
  ∀ Y : MaskFact a.J.W → Prop, Y g → S.entry.After Y f

/-- the segment hands g' on as g -/
def Carries (g' : MaskFact a.J.W) (g : MaskFact S.d.J.W) : Prop :=
  ∀ Y : MaskFact a.J.W → Prop, Y g' → S.seg.After Y g

end LdRefS

namespace LdRefL
variable {E Kc : Type} [Field E] [Fintype E] {I : LdRefIx E} {a : LdStage E Kc}

/-- Laid at the end of the list. -/
def Laid (base : MaskFact a.J.W → Prop) :
    {b : LdStage E Kc} → LdRefL E Kc I a b → MaskFact b.J.W → Prop
  | _, .nil, g => base g
  | _, .snoc L S, g => S.New g ∨ ∃ g', L.Laid base g' ∧ S.Carries g' g

def Lay (pp : ℕ) (base : MaskFact a.J.W → Prop) : {b : LdStage E Kc} → LdRefL E Kc I a b → Prop
  | _, .nil => True
  | _, .snoc L S => L.Lay pp base ∧ S.A.ZkAt pp fun f => ∃ g, L.Laid base g ∧ S.Enters g f

end LdRefL

/-- what is asked of a wide fact beside "it is fresh": quiet for the front; the two senders of the
body do not look -/
structure LdRefW.PassQ {E Kc : Type} [Field E] [Fintype E] {I : LdRefIx E} {A : LdRefD E Kc I}
    (W : LdRefW A) (F : LdRefF A) (own : A.Xa.Q.D.S.Ent → Prop) (Mk : Type) [Fintype Mk]
    [Nonempty Mk] (val : Mk → A.Xa.Q.D.S.Ent → E) : Prop where
  quiet  : F.Quiet (W.fact own Mk val)
  send1  : A.Xa.Q.D.d1.NoLook W.Rd W.Rr own
  send3  : A.Xa.Q.D.d3.NoLook (A.Xa.Q.D.S.sumP A.Xa.Q.D.N W.Rd W.RdN)
    (A.Xa.Q.D.S.sumO A.Xa.Q.D.N W.Rr W.RrN) (A.Xa.Q.D.S.sumP A.Xa.Q.D.N own fun _ => False)

namespace Spec

def ldReqRefLay_after : Prop :=
  ∀ (E Kc : Type) [Field E] [Fintype E] (I : LdRefIx E) (a b : LdStage E Kc) (L : LdRefL E Kc I a b)
      (base : MaskFact a.J.W → Prop) (g : MaskFact b.J.W),
    L.Laid base g → L.segs.After base g

def ldReqRefLay_mono : Prop :=
  ∀ (E Kc : Type) [Field E] [Fintype E] (I : LdRefIx E) (A : LdRefD E Kc I)
      (pp : ℕ) (X X' : MaskFact A.V.Fp.s0.J.W → Prop),
    (∀ f, X f → X' f) → A.ZkAt pp X → A.ZkAt pp X'

def ldReqRefLay_segs : Prop :=
  ∀ (E Kc : Type) [Field E] [Fintype E] (I : LdRefIx E) (a b : LdStage E Kc) (L : LdRefL E Kc I a b)
      (pp : ℕ) (base : MaskFact a.J.W → Prop),
    L.Lay pp base → L.ZkP pp base

def ldReqRefLay_new : Prop :=
  ∀ (E Kc : Type) [Field E] [Fintype E] (I : LdRefIx E) (a : LdStage E Kc)
      (S : LdRefS E Kc I a) (g : MaskFact S.d.J.W),
    S.New g → ∀ Y : MaskFact a.J.W → Prop, S.seg.After Y g

def ldReqRefLay_enters : Prop :=
  ∀ (E Kc : Type) [Field E] [Fintype E] (I : LdRefIx E) (a : LdStage E Kc) (S : LdRefS E Kc I a)
      (g : MaskFact a.J.W) (K' : Type) (kc' : S.A.V.Fp.s0.J.W → K') (put' : g.Mk → K' → K'),
    (∀ x (w w' : a.W) M, g.kc w' = g.put M (g.kc w) →
      (S.m (x, w')).1 = (S.m (x, w)).1 ∧ kc' (S.m (x, w')).2 = put' M (kc' (S.m (x, w)).2)) →
    S.Enters g ⟨K', kc', g.Mk, put'⟩

/-- Under the hypotheses below, the wide fact crosses a reference segment. -/
def ldReqRefLay_cross : Prop :=
  ∀ (E Kc : Type) [Field E] [Fintype E] (pp : ℕ) [CharP E pp] (I : LdRefIx E)
      (a : LdStage E Kc) (S : LdRefS E Kc I a) [Nonempty I.C.E0.Str] (W : LdRefW S.A)
      (F : LdRefF S.A) (κ : S.A.Gh → Kc) (own : S.A.Xa.Q.D.S.Ent → Prop) (Mk : Type)
      [Fintype Mk] [Nonempty Mk] (val : Mk → S.A.Xa.Q.D.S.Ent → E) (RdN : S.Qc.N.Ent → Prop)
      (RrN : S.Qc.N.O → Prop) (g' : MaskFact a.J.W),
    S.A.OK pp → S.A.Ghost κ → F.OK pp → W.PassQ F own Mk val → S.A.Xa.A.MaskOK S.A.Xa.Dt →
    (∀ n, S.A.Xa.A.srAll S.A.Xa.Dt n → W.Rd2 n ∧ ¬ S.A.own2 own n) → S.A.X.Own →
    (∀ n, S.A.Rdt n → W.Rd2 n ∧ ¬ S.A.own2 own n) →
    (∀ (w w' : S.K.R.c1.fold.src.J.W) x c ρ, S.K.R.c1.fold.G.wit w'.1 = S.K.R.c1.fold.G.wit w.1 →
      ((S.l.H.strat w' x c).run ρ).1 = ((S.l.H.strat w x c).run ρ).1 ∧
      ((S.l.H.strat w' x c).run ρ).2.1 = ((S.l.H.strat w x c).run ρ).2.1 ∧
      ((S.l.H.strat w' x c).run ρ).2.2.1 = ((S.l.H.strat w x c).run ρ).2.2.1) →
    (∀ (w : S.K.R.c1.fold.src.J.W) x c ρ, ((S.l.H.strat w x c).run ρ).2.2.2 =
      (S.K.R.c1.fold.S.res (T := OMsg.Wit) S.K.R.c1.fold.kp w.1, w.2)) →
    (∀ o, S.K.R.c1.fold.G.mem o → W.Rr2 o ∧ ∀ j, W.Rd2 ⟨o, j⟩ ∧ ¬ S.A.own2 own ⟨o, j⟩) →
    S.Qc.Sn.Laws (S.K.R.c1.fold.tgt.S.backN S.Qc.N S.Qc.snd.bk) →
    (∀ w w' : S.K.R.c1.fold.tgt.W,
      S.K.R.c1.fold.tgt.S.Alike
        (S.K.R.c1.fold.S₁.subQ _ (S.K.R.c1.fold.S.subQ S.K.R.c1.fold.kp W.Rd2))
        (S.K.R.c1.fold.S₁.subQ _ (S.K.R.c1.fold.S.subQ S.K.R.c1.fold.kp (S.A.own2 own)))
        (S.K.R.c1.fold.tgt.S.msgs w.1) (S.K.R.c1.fold.tgt.S.msgs w'.1) →
      (∀ o : S.K.R.c1.fold.tgt.S.O, W.Rr2 o.1.1 → (w'.1 o).2 = (w.1 o).2) → w'.2 = w.2 →
      (∀ k, S.Qc.Sn.put w' k = S.Qc.Sn.put w k) ∧ (S.Qc.Sn.rest w').2 = (S.Qc.Sn.rest w).2) →
    (∀ m m' : S.Qc.N.Msg,
      (∀ n : S.Qc.N.Ent, RdN n → m' n.1 n.2 = m n.1 n.2) → S.Qc.cutN m' = S.Qc.cutN m) →
    S.Enters g' (W.fact own Mk val) →
    S.Carries g'
      (S.Qc.loc.tgt.wideFact
        (S.K.R.c1.fold.tgt.S.sumP S.Qc.N
          (S.K.R.c1.fold.S₁.subQ _ (S.K.R.c1.fold.S.subQ S.K.R.c1.fold.kp W.Rd2)) RdN)
        (S.K.R.c1.fold.tgt.S.sumO S.Qc.N (fun a => W.Rr2 a.1.1) RrN)
        (S.K.R.c1.fold.tgt.S.sumP S.Qc.N
          (S.K.R.c1.fold.S₁.subQ _ (S.K.R.c1.fold.S.subQ S.K.R.c1.fold.kp (S.A.own2 own)))
          fun _ => False)
        Mk fun M =>
          S.K.R.c1.fold.tgt.S.sumV S.Qc.N
            (S.K.R.c1.fold.S₁.subF _ (S.K.R.c1.fold.S.subF S.K.R.c1.fold.kp (S.A.val2 val M)))
            fun _ => 0)

/-- What zero knowledge asks of the reference request, beside its hypotheses, the masks chained. -/
def ldReqRefLay : Prop :=
  ∀ (F E Kc : Type) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E] (pp : ℕ) [CharP E pp]
      (R : LdORE F E Kc) (a : LdStage E Kc) (first : LdSendD a) (a₁ : LdStage E Kc)
      (more : LdProg first.tgt a₁) (hm : more.All fun t => t = .send ∨ t = .step) (b : LdStage E Kc)
      (L : LdRefL E Kc R.ix a₁ b) (T : LdRefT R b) (Rd : R.S.Ent → Prop) (Rr : R.S.O → Prop),
    L.OK pp → T.OK pp → 2 ≤ R.n → R.Z.OK → R.Tie → R.X.Own → (∀ n, R.Rd n → Rd n) →
    L.Lay pp (ldReqRef R first a₁ more hm b L T).base₀ →
    T.A.ZkAt pp (fun f =>
      ∃ g,
        L.Laid (ldReqRef R first a₁ more hm b L T).base₀ g ∧
        ∀ Y : MaskFact b.J.W → Prop, Y g → T.entry.After Y f) →
    (∃ g,
      L.Laid (ldReqRef R first a₁ more hm b L T).base₀ g ∧
      ∀ Y : MaskFact b.J.W → Prop, Y g →
        T.tail.After Y
          (R.X.src.wideFact Rd Rr (R.X.atOwn R.X.wAt) R.X.mask.Mk fun M => R.X.atVal R.X.wAt M)) →
    (ldReqRef R first a₁ more hm b L T).Zk

end Spec
end Cb
