-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Req1/LdReqS.lean: the preamble of a request with blocks whose own masks were sent at different
steps: what honest-verifier zero knowledge asks (`r.ZkS`), beside its hypotheses (`r.Hyp`), and the
whole bundle from it. (hypotheses: see `Spec.ldReqS_goodT`)

Definitions and statements (Cb.Spec.ldReqS_*); the proofs are in Cb/Req1/LdReqSProofs.lean. By
composition only.
It builds on Cb/Req1/LdReq.lean (a request: first sendings, segments, a last part) and
Cb/Req1/LdSegFreshS.lean (a piece with `FreshGiven`, `OkGiven` behind a chain with `FreshS`, `OkS`
(`Spec.freshS_of_given`, `Spec.okS_of_given`)).
A `MaskFact W` is a reading `kc` of witnesses of type W into a type `Kc`, a finite, non-empty type
`Mk`, and a map `put : Mk → Kc → Kc`. (facts: `IOR.MaskFact`, Cb/Req1/LdSegFresh.lean.)
Names and paths: "the whole bundle": `Link.GoodT`
(Ior/KnowCollRulesChain.lean; `IOR.GoodT`, Ior/KnowCollGood.lean); "does not look": `Honest.Blind`
(Ior/KnowCollRulesMask.lean).

Why: `r.Zk` follows the fresh masks through the lists by a recursion on the links: a fact is made at
the one link that sends its masks and carried by links that do not look. In a write-up of
ours (lean/CREDITS.md) a sumcheck of a later segment that ends at a map of the index has its hiding
coefficients in the segment's own mask rows (sent by the one sending of the closing before) and its
inner masks in the message with the masks for the rows on the encoded index (sent with the request's
first sendings).
Both are own masks of one block. The fact of that block is in no set S.After base:
r.Zk cannot be met by such a layout.
At the entry of each segment, and before the last part, the set of fresh facts is closed under join
(two facts with one reading), a coarser reading, another type for the same masks (`X.JCl`,
Cb/Req1/LdSegFreshS.lean). Inside a segment nothing changes: `s.After`, `s.Zk` are those of
Cb/Req1/LdReq.lean.

Main names:
  `S.AfterJ base`: the facts that are fresh after the segments S: the closure of "base", if S is
    empty; else the closure of what is fresh after the last segment, given S'.AfterJ base before it.
  `S.ZkJ base`: each segment's s.Zk, at the closed set of facts before it.
  `r.ZkS`: the segments at r.base₀; the last part at r.segs.AfterJ r.base₀.
  `Spec.ldReqS_prog_fresh`, `Spec.ldReqS_prog_ok`, `Spec.ldReqS_seg_fresh`, `Spec.ldReqS_seg_ok`
    (further premises: the two on what is fresh: `c₀.AllB`, and `p.Hyp` or `s.Hyp`; the two others:
    `c₀.OkS`, and `p.Hyp`, `p.Zk base` or `s.Hyp`, `s.Zk base`): a list of moves, a segment, behind
    a chain c₀ after which all facts of "base" are fresh in the sense of Cb/Req1/LdSegFreshS.lean:
    the analogues of `ldReq_prog_fresh`, `ldReq_prog_ok`, `ldReq_seg_fresh`, `ldReq_seg_ok`
    (Cb/Req1/LdReq.lean) with `FreshS`, `OkS` for `FreshFor`, `Ok`.
  `Spec.ldReqS_mono`: p.After, p.Zk, s.After, s.Zk are monotone in the set of facts.
  `Spec.ldReqS_of_zk`: r.Zk → r.ZkS.
  `Spec.ldReqS_goodT`: r.Hyp, r.ZkS ⇒ the preamble of a request, as one link, has the whole bundle:
    the conclusion of `ldReq_goodT`, word for word.

How the block's fact is had: at the entry of its segment both parts are fresh at wide readings (by
the rules of Cb/Req1/LdSegCarry.lean, each under its conditions): the inner masks' wide fact has
crossed the closings, the hiding coefficients' was laid by the last sending. Two wide facts in a
closed set can be brought to one reading and joined, and the pair is again a wide fact
(Cb/Req1/LdSegCarryJoin.lean: `wideJ_pair`); carried part and laid part land in one set at one stage
(by the definition of `LdRefL.LaidJ`, Cb/Req1/LdReqRefLayJ.lean). Then: a coarser reading; the
block's own type of masks.

Limits: This file gives no instance that meets its hypotheses, so as far as this file shows its
theorems may hold of nothing. A closure inside a segment (masks of one block from a sending of the
body and from an earlier one) is not here; the write-up does not need it: there the own
masks of all blocks of a segment stand in oracle messages that are open at the segment's entry.
Terms: lean/GLOSSARY.md.
"The write-up": one of our own texts on this protocol (lean/CREDITS.md); it is not in this
repository.
-/
import Cb.Req1.LdReq
import Cb.Req1.LdSegFreshS

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Cb.Ood IOR

section
variable {E Kc : Type} [Field E] [Fintype E]

namespace LdSegs

/-- What is fresh after the segments, the set closed at each segment's entry. -/
def AfterJ : {a b : LdStage E Kc} → LdSegs a b → (MaskFact a.J.W → Prop) → MaskFact b.J.W → Prop
  | _, _, .nil _, base => MaskFact.JCl base
  | _, _, .snoc S s, base => MaskFact.JCl (s.After (AfterJ S base))

def ZkJ : {a b : LdStage E Kc} → LdSegs a b → (MaskFact a.J.W → Prop) → Prop
  | _, _, .nil _, _ => True
  | _, _, .snoc S s, base => ZkJ S base ∧ s.Zk (AfterJ S base)

end LdSegs

/-- What zero knowledge asks of a request, beside its hypotheses. -/
structure LdReq.ZkS {a z : LdStage E Kc} (r : LdReq a z) : Prop where
  segs : r.segs.ZkJ r.base₀
  last : r.last.Zk (r.segs.AfterJ r.base₀)

end

namespace Spec
section
variable (E Kc : Type) [Field E] [Fintype E]

def ldReqS_prog_fresh : Prop :=
  ∀ (A : Joint Kc) (a b : LdStage E Kc) (c₀ : Chain Kc A a.J)
      (p : LdProg a b) (base : MaskFact a.J.W → Prop),
    c₀.AllB → p.Hyp → (∀ g, base g → c₀.FreshS g.kc g.Mk g.put) →
    ∀ f, p.After base f → (p.onto c₀).FreshS f.kc f.Mk f.put

def ldReqS_prog_ok : Prop :=
  ∀ (A : Joint Kc) (a b : LdStage E Kc) (c₀ : Chain Kc A a.J)
      (p : LdProg a b) (base : MaskFact a.J.W → Prop),
    c₀.OkS → (∀ g, base g → c₀.FreshS g.kc g.Mk g.put) → p.Hyp → p.Zk base → (p.onto c₀).OkS

def ldReqS_seg_fresh : Prop :=
  ∀ (A : Joint Kc) (a d : LdStage E Kc) (c₀ : Chain Kc A a.J)
      (s : LdSeg a d) (base : MaskFact a.J.W → Prop),
    c₀.AllB → s.Hyp → (∀ g, base g → c₀.FreshS g.kc g.Mk g.put) →
    ∀ f, s.After base f → (s.onto c₀).FreshS f.kc f.Mk f.put

def ldReqS_seg_ok : Prop :=
  ∀ (A : Joint Kc) (a d : LdStage E Kc) (c₀ : Chain Kc A a.J)
      (s : LdSeg a d) (base : MaskFact a.J.W → Prop),
    c₀.OkS → (∀ g, base g → c₀.FreshS g.kc g.Mk g.put) → s.Hyp → s.Zk base → (s.onto c₀).OkS

/-- More facts before: more facts after, and less is asked. -/
def ldReqS_mono : Prop :=
  (∀ (a b : LdStage E Kc) (p : LdProg a b) (X X' : MaskFact a.J.W → Prop),
    (∀ g, X g → X' g) → (∀ f, p.After X f → p.After X' f) ∧ (p.Zk X → p.Zk X')) ∧
  ∀ (a d : LdStage E Kc) (s : LdSeg a d) (X X' : MaskFact a.J.W → Prop),
    (∀ g, X g → X' g) → (∀ f, s.After X f → s.After X' f) ∧ (s.Zk X → s.Zk X')

/-- `r.Zk → r.ZkS`. -/
def ldReqS_of_zk : Prop := ∀ (a z : LdStage E Kc) (r : LdReq a z), r.Zk → r.ZkS

/-- Under `r.Hyp` and `r.ZkS`: the preamble of a request has the whole bundle. -/
def ldReqS_goodT : Prop :=
  ∀ (a z : LdStage E Kc) (r : LdReq a z) (w₀ : a.W), r.Hyp → r.ZkS → (r.chain.link w₀).GoodT

end
end Spec
end Cb
