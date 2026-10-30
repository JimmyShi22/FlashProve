-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Req1/LdReq.lean: the preamble of a request: one first sending, any number of segments, a last
part; its whole bundle, honest-verifier zero knowledge included. (not all hypotheses are named here:
see `Spec.ldReq_goodT`)

Definitions and statements (Cb.Spec.ldReq_*); the proofs are in Cb/Req1/LdReqProofs.lean. By
composition only.
In standard terms: a request's preamble is a sequence of interactive oracle reductions (`IOR.Chain`,
Ior/KnowCollRulesChain.lean). This file composes it from a first sending of oracle messages, further
sendings, segments and a last part, and states properties of the composition from those of its
steps.
It builds on Cb/Req1/LdSeg.lean, Cb/Req1/LdSegFresh.lean (masks that are fresh at the start of a
piece) and Ior/KnowCollRulesChain.lean (chains; the rule for masks sent in advance). The head of
Cb/Req1/LdSegFresh.lean has the Lean names and paths for "the whole bundle", "the bundle without its
clause on zero knowledge", "masked block" and "does not look"; "of the two kinds": `Chain.Ok`
(Ior/KnowCollRulesChain.lean), `Chain.OkGiven` (Cb/Req1/LdSegFresh.lean).

The protocol (`LdReq a z`: from the stage a to the stage z):
  first: a sending; more: a list of further sendings (and steps without rounds), which may be empty.
    Together: the oracle message with the masks for the rows on the encoded index, and the first
    oracle messages of the first segment, in one prover message or in several.
  segs: the segments, one after the other (`LdSegs`: a list of any length); each ends with the first
    oracle messages of the next one sent.
  last: a list of moves of the kinds "sub" and "step": the pending tensor rows on the encoded index
    become one; claims are written in the form in which the test that follows needs them.
    The kinds restrict nothing: every move, a sending too, is a sub-protocol (its own chain) and can
    be entered here as such, with the same links (Cb/Req1/LdReqLast.lean). So the last segment,
    which has no closing of its own, is here: its body with its sendings.
  What is open at the end (the oracle messages that the last closings have sent, the mask message)
  is left to whoever follows.
  `r.chain`: all links (`IOR.Link`, Ior/KnowCollRulesChain.lean) in a row, bracketed to the left,
    beginning with the first sending. No round is added, none is merged.
The bundle without its clause on zero knowledge goes link by link, as for a segment (`r.Hyp`: the
hypotheses of all moves).
Zero knowledge is a property of the whole. The masks of a segment's sumchecks and splits stand in
oracle messages that were sent earlier, most of them in the one sending of the segment before. The
rule (Ior/KnowCollRulesChain.lean: `c.Ok`, `chain_ok`) asks for each masked block that its masks are
fresh after all that comes before it: some earlier link sent them and left them uniform given all
that it shows, and no link in between looks at them (exactly: `Chain.FreshFor`, in that file;
`Honest.Fresh`, told below, and `Honest.Blind`, Ior/KnowCollRulesMask.lean). Here that is followed
through the lists:
  "base": a set of facts (`IOR.MaskFact`: a reading of the witness, some mask entries in it) that
    are fresh at a stage.
  `m.After base`: the facts that are fresh after the move m, if those of "base" are fresh before it
    (`IOR.Chain.FreshGiven` of the move's chain): the move sends these masks and leaves them fresh;
    or it does not look at them and they were fresh before.
  `p.After`, `s.After`, `S.After`: the same through a list of moves, a segment, a list of segments.
  `m.Zk base`: what zero knowledge asks of a move beside `m.Hyp`. A "sub": its chain is of the two
    kinds, given "base" (`OkGiven`). A split: its mask entry is fresh: `D.mask.fact` is in "base".
    All other moves: nothing.
  `p.Zk`, `s.Zk`, `S.Zk`: the same through the lists: each move is asked at the facts that are fresh
    before it.
  `r.base₀`: the facts that are fresh before the first segment: those for which the first sending
    is Fresh (Ior/KnowCollRulesMask.lean), followed through the further sendings.
  `r.Zk`: the segments at `r.base₀`, the last part at what is fresh after the segments.
`H.Fresh Ri bud kc Mk put`: for every (x, y, w) in Ri, every ρ outside `H.withheld w x` and every T
with `bud ρ T`: the distribution of `H.seen …` over uniform coins does not change if its third part
is overwritten by `put M` at an independent uniform M. (`Honest.Fresh`, `Honest.seen`,
Ior/KnowCollRulesMask.lean.) In this file it stands in the definition `r.base₀` (of
`r.first.link.H`), so in the premise `r.Zk` of `Spec.ldReq_goodT`; `Chain.FreshFor`, which is
defined with it (Ior/KnowCollRulesChain.lean), stands in `Spec.ldReq_prog_fresh` and
`Spec.ldReq_seg_fresh` as a premise and as the conclusion, in `Spec.ldReq_prog_ok` and
`Spec.ldReq_seg_ok` as a premise; `Chain.Ok`, which is defined with `FreshFor` (the same file),
stands in these two as a premise and as the conclusion; `Chain.FreshGiven`, which is defined with
`Fresh`, and `Chain.OkGiven`, which is defined with `FreshGiven` (Cb/Req1/LdSegFresh.lean), stand in
the definitions `m.After`, `s.After`, `m.Zk` and `s.Zk`, and `OkGiven` is the conclusion of
`Spec.ldReq_mv_ok`.

Main names:
  `Spec.ldReq_mv_ok`: a move with m.Hyp and m.Zk base: its chain is of the two kinds, given "base".
  `Spec.ldReq_prog_fresh`, `Spec.ldReq_prog_ok` (the second under `p.Hyp`, `p.Zk base`): a list of
    moves behind a chain c₀ after which all facts of "base" are fresh: what is in p.After base is
    fresh after p.onto c₀; and p.onto c₀ is of the two kinds if c₀ is.
  `Spec.ldReq_seg_fresh`, `Spec.ldReq_seg_ok` (the second under `s.Hyp`, `s.Zk base`): the same for
    a segment.
  `Spec.ldReq_goodB`: the bundle without its clause on zero knowledge, from r.Hyp alone beside
    whatever the arguments hold as proofs.
  `Spec.ldReq_goodT`: the preamble of a request has the whole bundle: from r.Hyp and r.Zk: strings
    (`point`), local, complete outside a public set and a hidden one, knowledge sound round by round
    on collision-free statements that also meet `a.A.on` into collision-free statements, with the
    composed extractor and the errors of the moves in a row, honest-verifier exact zero knowledge at
    the composed budget outside a hidden set (`IOR.GoodT.exact`: `Honest.Exact`, Ior/Honest.lean).
  `Spec.ldReq_nums`: the list of parameters: rounds of both kinds and the two numbers `P.pBad`,
    `P.pHid` (of `IOR.Nums`, Ior/Chain.lean; what pBad and pHid bound: `GoodT`,
    Ior/KnowCollGood.lean) are: the first sending's, plus the further sendings' (`more`), plus the
    sum over the segments, plus the last part's. (The first sending's: 2 for all rounds; no term in
    the two numbers.)
  `Spec.ldReq_alpha`: completeness holds outside two sets of verifier messages, a public one and a
    hidden one. If each segment's number for the one (`s.pBad`), or for the other (`s.pHid`), is at
    most α, the segments' is at most (number of segments) · α. A range check whose window event is
    withheld in secret pays in the hidden one; that term is also what it adds to the zero-knowledge
    error.
  `Spec.ldReq_zk_free`: a list without "sub" and "split" is asked nothing for zero knowledge, beside
    its hypotheses.

What the conditions of the written lemma on masks sent in advance become: the head of
Ior/KnowCollRulesMask.lean.
Why: "No test on a group that holds an oracle message comes before a block with masks in it": a
bridge-to-fold reads encoding randomness, so it does not carry a fact whose reading it would have to
look through; such a fact is simply not in m.After base.
Under the hypotheses of their statements, that a sending is Fresh for masks that it lays down, and
does not look at masks in older oracle messages, are theorems (stated in Cb/Ld/LdSendFresh.lean,
proved in Cb/Ld/LdSendFreshProofs.lean; Cb/Ld/LdSendBlind.lean).

Limits: declared differences to a write-up of ours (lean/CREDITS.md).
 (1) Honest-verifier zero knowledge in our exact form (every set of further positions within
   the budget; a hidden withheld set in place of an error), where the write-up has classes
   of distinguishers.
 (2) The written lemma goes backwards through the blocks, or through an analysis protocol in another
   order; here the rule goes forwards, prefix by prefix.
 (3) Early sending of the folds' fresh masks is not applied here.
 (4) The nested budget is not discharged here.
This file says nothing on the step from this bundle to the parameter list of a preamble of the
holographic protocol (Cb/Ld/LdWfClose.lean has the rule). It does not say that r.Zk can be met: no
instance is given here. Nothing on running times.
The order of a request's parts restates the write-up in our own
words (lean/CREDITS.md).
Terms: lean/GLOSSARY.md.
"The write-up": one of our own texts on this protocol (lean/CREDITS.md); it is not in this
repository.
-/
import Cb.Req1.LdSeg
import Cb.Req1.LdSegFresh
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Cb.Ood
open scoped ENNReal

section
variable {E Kc : Type} [Field E] [Fintype E]

/-! ## 1. What is fresh after a move; what zero knowledge asks of it -/

namespace LdMv

/-- The facts that are fresh after the move, given those before it. -/
def After {a b : LdStage E Kc} (m : LdMv a b) (base : IOR.MaskFact a.J.W → Prop) :
    IOR.MaskFact b.J.W → Prop :=
  m.chain.FreshGiven base

/-- What zero knowledge asks of a move, beside its hypotheses. -/
def Zk : {a b : LdStage E Kc} → LdMv a b → (IOR.MaskFact a.J.W → Prop) → Prop
  | _, _, .sub _ _ c, base => c.OkGiven base
  | _, _, .split D, base => base D.mask.fact
  | _, _, .send _ _, _ => True
  | _, _, .bat _, _ => True
  | _, _, .fold _ _, _ => True
  | _, _, .loc _, _ => True
  | _, _, .step _ _ _ _ _ _, _ => True

end LdMv

namespace LdProg

def After :
    {a b : LdStage E Kc} → LdProg a b → (IOR.MaskFact a.J.W → Prop) → IOR.MaskFact b.J.W → Prop
  | _, _, .nil _, base => base
  | _, _, .snoc p m, base => m.After (p.After base)

def Zk : {a b : LdStage E Kc} → LdProg a b → (IOR.MaskFact a.J.W → Prop) → Prop
  | _, _, .nil _, _ => True
  | _, _, .snoc p m, base => p.Zk base ∧ m.Zk (p.After base)

end LdProg

namespace LdSeg
variable {a d : LdStage E Kc} (s : LdSeg a d)

/-- the facts that are fresh before the one sending -/
def mid (base : IOR.MaskFact a.J.W → Prop) : IOR.MaskFact s.c.J.W → Prop :=
  s.fold.After (s.bat.After (s.body.After base))

def After (base : IOR.MaskFact a.J.W → Prop) : IOR.MaskFact d.J.W → Prop :=
  s.loc.After ((IOR.Chain.one s.snd.link).FreshGiven (s.mid base))

structure Zk (base : IOR.MaskFact a.J.W → Prop) : Prop where
  body : s.body.Zk base
  bat  : s.bat.Zk (s.body.After base)
  fold : s.fold.Zk (s.bat.After (s.body.After base))
  loc  : s.loc.Zk ((IOR.Chain.one s.snd.link).FreshGiven (s.mid base))

end LdSeg

/-! ## 2. Segments in a row -/

/-- A list of segments. -/
inductive LdSegs : LdStage E Kc → LdStage E Kc → Type 1
  | nil (a : LdStage E Kc) : LdSegs a a
  | snoc {a b c : LdStage E Kc} (S : LdSegs a b) (s : LdSeg b c) : LdSegs a c

namespace LdSegs

def onto {A : IOR.Joint Kc} :
    {a b : LdStage E Kc} → IOR.Chain Kc A a.J → LdSegs a b → IOR.Chain Kc A b.J
  | _, _, c, .nil _ => c
  | _, _, c, .snoc S s => s.onto (onto c S)

def Hyp : {a b : LdStage E Kc} → LdSegs a b → Prop
  | _, _, .nil _ => True
  | _, _, .snoc S s => S.Hyp ∧ s.Hyp

def After :
    {a b : LdStage E Kc} → LdSegs a b → (IOR.MaskFact a.J.W → Prop) → IOR.MaskFact b.J.W → Prop
  | _, _, .nil _, base => base
  | _, _, .snoc S s, base => s.After (S.After base)

def Zk : {a b : LdStage E Kc} → LdSegs a b → (IOR.MaskFact a.J.W → Prop) → Prop
  | _, _, .nil _, _ => True
  | _, _, .snoc S s, base => S.Zk base ∧ s.Zk (S.After base)

/-- the number of segments -/
def len : {a b : LdStage E Kc} → LdSegs a b → ℕ
  | _, _, .nil _ => 0
  | _, _, .snoc S _ => S.len + 1

def nAll : {a b : LdStage E Kc} → LdSegs a b → ℕ
  | _, _, .nil _ => 0
  | _, _, .snoc S s => S.nAll + s.nAll

def nVer : {a b : LdStage E Kc} → LdSegs a b → ℕ
  | _, _, .nil _ => 0
  | _, _, .snoc S s => S.nVer + s.nVer

def pBad : {a b : LdStage E Kc} → LdSegs a b → ℝ≥0∞
  | _, _, .nil _ => 0
  | _, _, .snoc S s => S.pBad + s.pBad

def pHid : {a b : LdStage E Kc} → LdSegs a b → ℝ≥0∞
  | _, _, .nil _ => 0
  | _, _, .snoc S s => S.pHid + s.pHid

/-- every segment's number for the public withheld set (`s.pBad`), for the hidden one (`s.pHid`), is
at most α -/
def BadLE (α : ℝ≥0∞) : {a b : LdStage E Kc} → LdSegs a b → Prop
  | _, _, .nil _ => True
  | _, _, .snoc S s => S.BadLE α ∧ s.pBad ≤ α

def HidLE (α : ℝ≥0∞) : {a b : LdStage E Kc} → LdSegs a b → Prop
  | _, _, .nil _ => True
  | _, _, .snoc S s => S.HidLE α ∧ s.pHid ≤ α

end LdSegs

/-! ## 3. The preamble of a request -/

/-- The preamble of a request. -/
structure LdReq (a z : LdStage E Kc) : Type 1 where
  /-- the first sending, and further ones -/
  first : LdSendD a
  a₁    : LdStage E Kc
  more  : LdProg first.tgt a₁
  /-- the stage after the last segment -/
  b     : LdStage E Kc
  segs  : LdSegs a₁ b
  last  : LdProg b z
  moreT : more.All fun t => t = .send ∨ t = .step
  lastT : last.All fun t => t = .sub ∨ t = .step

namespace LdReq
variable {a z : LdStage E Kc} (r : LdReq a z)

structure Hyp : Prop where
  first : r.first.Hyp
  more  : r.more.Hyp
  segs  : r.segs.Hyp
  last  : r.last.Hyp

/-- All links in a row. -/
def chain : IOR.Chain Kc a.J z.J :=
  r.last.onto (r.segs.onto (r.more.onto (.one r.first.link)))

/-- the facts that are fresh before the first segment -/
def base₀ : IOR.MaskFact r.a₁.J.W → Prop :=
  r.more.After fun f => r.first.link.H.Fresh a.J.rels.rel r.first.link.P.bud f.kc f.Mk f.put

structure Zk : Prop where
  segs : r.segs.Zk r.base₀
  last : r.last.Zk (r.segs.After r.base₀)

end LdReq
end

/-! ## The statements -/

namespace Spec
open IOR

/-- A move with its hypotheses and what zero knowledge asks of it. -/
def ldReq_mv_ok : Prop :=
  ∀ (E Kc : Type) [Field E] [Fintype E] (a b : LdStage E Kc)
      (m : LdMv a b) (base : MaskFact a.J.W → Prop),
    m.Hyp → m.Zk base → m.chain.OkGiven base

/-- A list of moves behind a chain: what is fresh. -/
def ldReq_prog_fresh : Prop :=
  ∀ (E Kc : Type) [Field E] [Fintype E] (A : Joint Kc) (a b : LdStage E Kc) (c₀ : Chain Kc A a.J)
      (p : LdProg a b) (base : MaskFact a.J.W → Prop),
    (∀ g, base g → c₀.FreshFor g.kc g.Mk g.put) →
    ∀ f, p.After base f → (p.onto c₀).FreshFor f.kc f.Mk f.put

def ldReq_prog_ok : Prop :=
  ∀ (E Kc : Type) [Field E] [Fintype E] (A : Joint Kc) (a b : LdStage E Kc) (c₀ : Chain Kc A a.J)
      (p : LdProg a b) (base : MaskFact a.J.W → Prop),
    c₀.Ok → (∀ g, base g → c₀.FreshFor g.kc g.Mk g.put) → p.Hyp → p.Zk base → (p.onto c₀).Ok

/-- The same for a segment. -/
def ldReq_seg_fresh : Prop :=
  ∀ (E Kc : Type) [Field E] [Fintype E] (A : Joint Kc) (a d : LdStage E Kc) (c₀ : Chain Kc A a.J)
      (s : LdSeg a d) (base : MaskFact a.J.W → Prop),
    (∀ g, base g → c₀.FreshFor g.kc g.Mk g.put) →
    ∀ f, s.After base f → (s.onto c₀).FreshFor f.kc f.Mk f.put

def ldReq_seg_ok : Prop :=
  ∀ (E Kc : Type) [Field E] [Fintype E] (A : Joint Kc) (a d : LdStage E Kc) (c₀ : Chain Kc A a.J)
      (s : LdSeg a d) (base : MaskFact a.J.W → Prop),
    c₀.Ok → (∀ g, base g → c₀.FreshFor g.kc g.Mk g.put) → s.Hyp → s.Zk base → (s.onto c₀).Ok

/-- The bundle without its clause on zero knowledge. -/
def ldReq_goodB : Prop :=
  ∀ (E Kc : Type) [Field E] [Fintype E] (a z : LdStage E Kc) (r : LdReq a z) (w₀ : a.W),
    r.Hyp → (r.chain.link w₀).GoodB

/-- Under `r.Hyp` and `r.Zk`: the preamble of a request has the whole bundle. -/
def ldReq_goodT : Prop :=
  ∀ (E Kc : Type) [Field E] [Fintype E] (a z : LdStage E Kc) (r : LdReq a z) (w₀ : a.W),
    r.Hyp → r.Zk → (r.chain.link w₀).GoodT

/-- The list of parameters. -/
def ldReq_nums : Prop :=
  ∀ (E Kc : Type) [Field E] [Fintype E] (a z : LdStage E Kc) (r : LdReq a z) (w₀ : a.W),
    (r.chain.link w₀).R.shape.nAll = 2 + r.more.nAll + r.segs.nAll + r.last.nAll ∧
    (r.chain.link w₀).R.shape.nVer =
      r.first.link.R.shape.nVer + r.more.nVer + r.segs.nVer + r.last.nVer ∧
    (r.chain.link w₀).P.pBad = r.more.pBad + r.segs.pBad + r.last.pBad ∧
    (r.chain.link w₀).P.pHid = r.more.pHid + r.segs.pHid + r.last.pHid

/-- The segments' numbers for the public and the hidden withheld set (`S.pBad`, `S.pHid`). -/
def ldReq_alpha : Prop :=
  ∀ (E Kc : Type) [Field E] [Fintype E] (a b : LdStage E Kc) (S : LdSegs a b) (α : ℝ≥0∞),
    (S.BadLE α → S.pBad ≤ S.len * α) ∧ (S.HidLE α → S.pHid ≤ S.len * α)

/-- A list without "sub" and "split" is asked nothing for zero knowledge, beside its hypotheses. -/
def ldReq_zk_free : Prop :=
  ∀ (E Kc : Type) [Field E] [Fintype E] (a b : LdStage E Kc)
      (p : LdProg a b) (base : MaskFact a.J.W → Prop),
    (p.All fun t => t ≠ .sub ∧ t ≠ .split) → p.Zk base

end Spec
end Cb
