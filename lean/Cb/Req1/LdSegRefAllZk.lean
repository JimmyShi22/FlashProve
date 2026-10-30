-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Req1/LdSegRefAllZk.lean: what zero knowledge asks of the closed body of the reference segment,
beside its hypotheses, in one statement: from places, and from facts that are fresh at the
segment's entry. (not all hypotheses are named here: see `Spec.ldSegRefAll_zk`)

Definitions and the statement (`Cb.Spec.ldSegRefAll_zk`); the proof is in
Cb/Req1/LdSegRefAllZkProofs.lean.

Why: the body (Cb/Req1/LdSegRefAll.lean) holds these masked blocks: in the front: the lookup, the
zerocheck's sumcheck, the further sumchecks; after two sendings: the digits' lookup; after that:
the batching of the tensor rows. All their own masks are sent before the segment. Zero knowledge of
a request asks, at each of them, that the fact which the block needs is fresh at its place
(Cb/Req1/LdReq.lean).
The front's blocks need their facts in "base" as they are (no sending stands before them):
`A.FrontFacts F base` (the clauses of Cb/Req1/LdSegFrontRefZk.lean).
The two late blocks stand behind sendings, and a sending carries only wide facts
(Cb/Req1/LdSegCarry.lean). So for each of them it is asked that "base" holds the wide fact of its
masks. And `W.Pass` (Cb/Req1/LdSegRefCross.lean): in "base"; quiet for the front; the two senders do
not look.
Names: `MaskFact`, `Chain.FreshGiven`: Cb/Req1/LdSegFresh.lean; `LdStage.wideFact`:
Cb/Req1/LdSegCarry.lean; `ldQuiet`: Cb/Req1/LdSegFrontTabZk.lean; `LdProg.Zk`: Cb/Req1/LdReq.lean.

Main names:
  `A.ownL`, `A.valL RdL`: the own masks of the digits' lookup, as entries of the messages at the
    entry, with their values (mask values: those of the lookup's letters).
  `A.ownT`, `A.valT`: the same for the batching.
  On places (`F.OK pp`; the fields of `A.Late W F RdL base` but passL, passT): the front's
    (`F.OK`: the front's conditions, among them on places, on numbers and on the claim Cc:
    Cb/Req1/LdSegRefCross.lean); the digits' lookup's own masks at pairwise different places outside
    its data (among what `A.Xa.A.MaskOK A.Xa.Dt` asks: Cb/Ld/LdLkpMaskAsm2.lean); the batching's
    (`X.Own`); the own masks of both lie in messages that are open at the entry; what each block
    reads lies in the wide reading; the digits' lookup reads no own mask of the batching.
  `Spec.ldSegRefAll_zk`: under `A.OK pp` (pp the characteristic of E), `A.Ghost κ`, `F.OK pp`,
    `A.FrontFacts F base`, `A.Late W F RdL base` and `Nonempty I.C.E0.Str`: (A.body St₁ fz Az).Zk
    base.

No hypothesis on a link or on an honest prover of a block is left; of the two senders it is asked
that they do not look (a property of the senders); `A.OK pp` holds the hypotheses of the two
sendings (`d1.Hyp`, `d3.Hyp`).
Limits: three choices that the conditions force (not every layout with pairwise different places
can meet them).
  (1) The front's readings are nested. The facts of the front's blocks are narrow: what a block's
      reading forgets may differ arbitrarily between two witnesses. So "quiet" (q0, qL, qZ, qS) can
      hold only if the reading of each block shows every entry that the blocks before it read, and
      holds no own mask of a later block: what the lookup reads ⊆ Rd0 ⊆ RdS 0 ⊆ RdS 1 ⊆ .. With
      each block reading just what it needs the clauses are false.
  (2) The wide reading W of this file is not that of a crossing. A fact on the segment's own masks
      forgets pad and encoding randomness of the member that holds them; a fact that crosses a
      closing must show every member of the closing's group whole. Each statement takes its own W.
  (3) The type of masks is the block's, from the sender on. passL asks the wide fact with the
      lookup's own type of masks and values through its places; no rule changes the type of masks
      of a fact that is given.
This file does not say that the facts are in "base": the matter of the sending before the segment.
It does not say which facts are fresh after the body. It says nothing on the closing. It does not
say that the conditions can be met together. No theorem of this library states that the hypotheses
of `ldSegRefAll_zk` can be met together.
Terms: lean/GLOSSARY.md.
-/
import Cb.Req1.LdSegRefCross
import Cb.Ld.LdLkpMaskPutLkp2
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Cb.Rng Cb.RngPk Cb.Lkp Cb.LdLkp IOR

namespace LdRefD
variable {E Kc : Type} [Field E] [Fintype E] {I : LdRefIx E} (A : LdRefD E Kc I)

/-- the places of the own masks of the digits' lookup -/
def plL (RdL : A.Xa.Q.T.Ent → Prop) :
    (A.Xa.A.mjChain I.C.E0 A.Xa.Q.T.Msg (I.C.PIdx × (A.W₁ × A.Gh)) Kc A.Xa.Q.T.ents RdL).Pl :=
  A.Xa.A.plChain I.C.E0 A.Xa.Q.T.Msg (I.C.PIdx × (A.W₁ × A.Gh)) Kc A.Xa.Q.T.ents RdL

/-- The own masks of the digits' lookup, as entries of the messages at the entry; their values. -/
def ownL (n : A.Xa.Q.D.S.Ent) : Prop := A.Xa.A.swAll (A.up n)
def valL (RdL : A.Xa.Q.T.Ent → Prop) (M : (A.Xa.dm RdL).Mk) (n : A.Xa.Q.D.S.Ent) :
    E :=
  Function.extend (A.plL RdL).pl ((A.plL RdL).ve M) (fun _ => 0) (A.up n)

/-- The own masks of the batching. -/
def ownT (n : A.Xa.Q.D.S.Ent) : Prop := ∃ i, A.wAt i = A.up n
def valT (M : A.X.mask.Mk) (n : A.Xa.Q.D.S.Ent) : E :=
  Function.extend A.wAt M (fun _ => 0) (A.up n)

/-- The facts of the front's blocks: in "base", and quiet for the blocks that run before. -/
structure FrontFacts (F : LdRefF A) (base : MaskFact A.V.Fp.s0.J.W → Prop) : Prop where
  lk  : base (A.V.Fp.dm F.RdK F.Cc).fact
  f0  : base (A.V.tab.f0 F.Rd0)
  q0  : ldQuiet A.Xa.Q.D.S (A.V.tab.f0 F.Rd0) A.V.Fp.msg (A.V.Fp.A.srAll F.Dt)
  f   : ∀ i ≤ A.V.m, base (A.V.tab.f i (F.RdS i))
  qL  : ∀ i ≤ A.V.m, ldQuiet A.Xa.Q.D.S (A.V.tab.f i (F.RdS i)) A.V.Fp.msg (A.V.Fp.A.srAll F.Dt)
  qZ  : ∀ i ≤ A.V.m, ldQuiet A.Xa.Q.D.S (A.V.tab.f i (F.RdS i)) A.V.Fp.msg0 F.Rd0
  qS  : ∀ i ≤ A.V.m, ∀ j < i, ldQuiet A.Xa.Q.D.S (A.V.tab.f i (F.RdS i)) (A.V.msg j) (F.RdS j)

/-- The conditions on the two late blocks. -/
structure Late (W : LdRefW A) (F : LdRefF A) (RdL : A.Xa.Q.T.Ent → Prop)
    (base : MaskFact A.V.Fp.s0.J.W → Prop) : Prop where
  /-- the digits' lookup -/
  maskL : A.Xa.A.MaskOK A.Xa.Dt
  rdL   : ∀ j, A.Xa.A.srAll A.Xa.Dt j → RdL j
  inL   : ∀ j, A.Xa.A.swAll j → ∃ n, A.up n = j
  wideL : ∀ n, RdL n → W.Rd2 n
  passL : W.Pass F base A.ownL (A.Xa.dm RdL).Mk (A.valL RdL)
  /-- the batching -/
  ownT  : A.X.Own
  inT   : ∀ i, ∃ n, A.up n = A.wAt i
  wideT : ∀ n, A.Rdt n → W.Rd2 n
  passT : W.Pass F base A.ownT A.X.mask.Mk A.valT
  /-- the digits' lookup reads entries of the wide reading, and no own mask of the batching -/
  apart : ∀ n, A.Xa.A.srAll A.Xa.Dt n → W.Rd2 n ∧ ¬ A.own2 A.ownT n

end LdRefD

/-- What zero knowledge asks of the closed body, beside its hypotheses. -/
def Spec.ldSegRefAll_zk : Prop :=
  ∀ (E Kc : Type) [Field E] [Fintype E] (pp : ℕ) [CharP E pp] (I : LdRefIx E) (A : LdRefD E Kc I)
      [Nonempty I.C.E0.Str] (W : LdRefW A) (F : LdRefF A) (κ : A.Gh → Kc)
      (RdL : A.Xa.Q.T.Ent → Prop) (St₁ : Type) (fz : A.X.bt.par.Mid → St₁)
      (Az : Rels Kc St₁ I.C.E0 (A.Xa.Q.T.Msg × (I.C.PIdx × (A.W₁ × A.Gh))))
      (base : MaskFact A.V.Fp.s0.J.W → Prop),
    A.OK pp → A.Ghost κ → F.OK pp → A.FrontFacts F base →
    A.Late W F RdL base → (A.body St₁ fz Az).Zk base

end Cb
