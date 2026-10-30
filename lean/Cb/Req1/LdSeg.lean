-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Req1/LdSeg.lean: a segment of the preamble of a request, as a statement over lists of moves.

Definitions and statements (Cb.Spec.ldSeg_*); the proofs are in Cb/Req1/LdSegProofs.lean, that of
`ldSeg_kept` in Cb/Req1/LdSegProofsFold.lean. The data of the moves: Cb/Req1/LdSegKit.lean. By
composition only: no block is proved here.
In standard terms: book-keeping for how the preamble of one request, a chain of interactive oracle
reductions (`LdReq`, Cb/Req1/LdReq.lean), is cut into pieces. A piece (a segment) is a sequence of
interactive oracle reductions; the main statement (`Spec.ldSeg_goodB`) says that the sequence, as
one reduction, is complete outside two sets of verifier messages and round-by-round knowledge sound,
if each reduction meets its own hypotheses.
`IOR.Link` (Ior/KnowCollRulesChain.lean) is an interactive oracle reduction (`IOR`, Ior/Ior.lean)
with its honest prover, knowledge extractor and numbers (`IOR.Nums`); `IOR.Chain` is a sequence of
these, and `Chain.link` their composition. A stage fixes two relations (`Sig.over`,
Cb/Ld/LdSig.lean). Exact: every oracle word is the encoding of its message, the message has the
answers of its sample (a seed with answers), and what the stage's base joint `a.A` claims of the
messages (its `rel`) holds. Relaxed: every word decodes with its sample to the witness's message,
that is, to the nearest codeword whose message has the answers, if that is within the radius
(`OMsg.dec`), and what the stage's base joint `a.A` claims of the messages (its `relR`) holds.
Collision-free: at the seed no two messages of a word's list have the same answers (`OMsg.Clash`).
In `a.J` the condition (collision-free, and A's own) is moved into the relaxed relation: a statement
outside it is related to every witness (`Rels.cf`, Ior/KnowCollGood.lean).
Names and paths: the bundle: `IOR.GoodT` (Ior/KnowCollGood.lean); `IOR.GoodB` and `IOR.GoodM` are in
Ior/Masked.lean.

What a segment is: the preamble of a request treats the computation piece by piece. A segment starts
at a statement whose first oracle messages have been sent and sampled, and ends at a statement of
the same kind for the next segment. Both ends are relaxed by decoding with a sample, on
collision-free statements (a stage, Cb/Req1/LdSegKit.lean: `LdStage`, `a.J`). In between, in this
order:
  body: the segment's own reductions: lookups, zerochecks and sumchecks, reads, the range check, the
    batching of tensor rows; and the sendings of whatever further oracle messages these need, at
    whatever moments.
  bat: many rows into one, then all splits: a row for each group.
  fold: for each group that closes now: the bridge to the existential relaxation, the arrangement,
    the fold. Its test stays open.
  snd: one sending of a family: what the closings carry on, the kept messages encoded anew, and the
    first oracle messages of the next segment. It runs while the tests are open.
  loc: for each open test: the locations. The cut between two segments is here.
The parameters. Nothing is counted in advance: each of the four parts body, bat, fold, loc is a list
of moves (`LdProg`) of any length; the stages between the moves, so the number and content of the
oracle messages, the moments at which they are sent, the number of lookups and of whatever they are
made of, the number of groups, are read off the lists.

Main names:
  `LdMv a b`, a move from the stage a to the stage b, is one of
    send d: one sending of a family (Cb/Ld/LdSigSum.lean); b is the stage over the old and the new
      oracle messages.
    sub c: any chain of links from a to b: a sub-protocol, or one block, defined elsewhere. What it
      claims at its two ends is a parameter; the form of the two ends is not: they are stages.
    bat D: many rows into one (Cb/Ld/LdBatSig.lean).
    split D: a row on two groups into a row on each (Cb/Ld/LdSplit.lean).
    fold D l: bridge, arrangement, fold on one group (l: their link, a parameter), then the step
      that lets the kept messages be read in the folded word.
    loc D: the locations of one open test; the kept messages held in it leave here.
    step: a step without rounds (a claim is written in another form).
  `m.Hyp`: what is asked of a move: the hypotheses of its block in the form in which they are stated
    for that block. For "sub": every link has all of the bundle but zero knowledge (`IOR.GoodB`)
    between its joints. For "fold": `IOR.GoodT` of l is asked (`LdFoldD.Hyp.good`). For "loc": no
    block is assumed: only that the stage has the form named, and the laws of the slots.
  `LdSeg a d`: the five parts, with the kinds of moves that each part may hold (fields `bodyT`,
    `batT`, `foldT`, `locT`).
  `Spec.ldSeg_mv`: a move with its hypotheses: every link of its chain is GoodB;
    `Spec.ldSeg_mvT`: and, if it is neither "sub" nor "split", GoodT: the sending, the batching,
    bridge-to-fold, the locations and the steps have honest-verifier exact zero knowledge of their
    own (`GoodT.exact`: `Honest.Exact`, Ior/Honest.lean).
  `Spec.ldSeg_split`: a split with its hypotheses is a masked block (`IOR.GoodM`) with the data
    `D.mask`.
  `Spec.ldSeg_kept`: the lemma on kept messages, on vectors: under `h.Laws e`, on a statement
    without collision, a pair within the radius of the open word whose slot has the answers of the
    old sample has the decoding of the held message in that slot. So the carried predicates read the
    same cells before and after the locations.
  `Spec.ldSeg_goodB`: under `s.Hyp`: the segment as one link (`s.chain.link w₀`, for every default
    w₀ of the extractor): all of the bundle but zero knowledge, from a.J to d.J: strings (`point`),
    local, complete outside a public set and a hidden one, cores, the two probabilities,
    round-by-round knowledge soundness with the composed extractor and the errors of the moves in a
    row.
  `Spec.ldSeg_into`: under `s.Hyp`: its knowledge soundness written out: on collision-free
    statements of the first stage that also meet A's own condition (`a.A.on`) into collision-free
    statements of the last (Ior/KnowColl.lean).
  `Spec.ldSeg_onto`: after any chain c₀: `c₀.AllB → s.Hyp → (s.onto c₀).AllB`; the form in which a
    request uses it.
  `Spec.ldSeg_nums`: the parameter list is derived: all rounds, rounds with a non-empty verifier
    message, the number for the public withheld set (`s.pBad`) and the number for the hidden
    withheld set (`s.pHid`; both are sums of the links' numbers `pBad`, `pHid`, fields of
    `IOR.Nums`, Ior/Chain.lean; what pBad and pHid bound: `GoodB`, Ior/Masked.lean) are the sums
    over the five parts; nothing is merged.
  `Spec.ldSeg_rounds`: the moves whose block is named: a sending has 2 rounds, a batching 1, a split
    1, the locations 1, a step 0; sending, batching, split, locations and steps add nothing to the
    two numbers.
  `Spec.ldSeg_sub_goodT`, `Spec.ldSeg_sub_goodM`, `Spec.ldSeg_lift`: how statements of other forms
    enter a "sub": a bundle between the joints S.over A, S'.over B (the condition not yet moved); a
    masked block; a reduction on claims about messages that is knowledge sound for each fixed tuple
    (Cb/Ld/LdSigLift.lean).

Why: that an oracle message is sampled before the first challenge that speaks of it holds by type: a
claim at a stage reads the messages of the oracle messages of that stage, which carry their samples;
what is not yet sent is a further witness.

Limits: zero knowledge is not an item of a segment. The masks of a segment's sumchecks and splits
stand in oracle messages that the segment before it has sent: they are in the segment's input
witness. (This is not forced by type: `LdReq.base₀`, Cb/Req1/LdReq.lean, is built from `r.first` and
`r.more`, which no segment precedes; `LdSeg.bodyT` lets a segment's own body hold a sending.) Zero
knowledge is a property of the whole preamble (Cb/Req1/LdReq.lean).
Declared differences to a write-up of ours (lean/CREDITS.md).
 (1) A fresh mask of a fold is sent by the fold, in a round of its own, where the write-up
     lets
   it ride in an earlier prover message: that is a rule on early sending which is applied last, to a
   whole protocol (for the bundle `Good`, Ior/Chain.lean, not for `GoodT` or `GoodB`:
   `Spec.good_hoist`, `Spec.exact_hoist`, Ior/Hoist.lean; it is not applied in this file).
 (2) From the fold to the locations a kept message stands among the further oracles, as a slot of
   the folded word, and not in the signature. What is said of it does not change: it decodes with
   its sample, the carried predicates read that decoding, "no collision" is a condition. It leaves
   at the locations, as in the write-up.
 (3) The write-up's table of a reference segment (which oracle message holds what; one
     lookup and
   the digits') is an instance and is not in this file. Which identities and keys a segment has is
   the model's side.
 (4) The number of groups is any number. The locations of several open tests come one after the
   other, the test that was opened last first.
 (5) Errors are counts, in a row; no sum of errors is formed.
This file does not say that hypotheses of this form can be met together (`Spec.ldSeg_toy`,
Cb/Req1/LdSegToy.lean, says so for a whole toy segment without body, batching and rider of a next
segment, if the bridge's evader evades); an instance is not given here. Nothing on running times,
sizes, trees.
The cut of a segment, its order of blocks and its parameters restate the write-up in our own
words (lean/CREDITS.md).
Terms: lean/GLOSSARY.md.
"The write-up": one of our own texts on this protocol (lean/CREDITS.md); it is not in this
repository.
-/
import Cb.Req1.LdSegKit
import Cb.Ld.LdSigLift
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Cb.Ood
open scoped ENNReal

/-- the kinds of moves -/
inductive LdTag
  | send | sub | bat | split | fold | loc | step

section
variable {E Kc : Type} [Field E] [Fintype E]

/-- A move of a preamble. -/
inductive LdMv : LdStage E Kc → LdStage E Kc → Type 1
  | send (a : LdStage E Kc) (d : LdSendD a) : LdMv a d.tgt
  | sub (a b : LdStage E Kc) (c : IOR.Chain Kc a.J b.J) : LdMv a b
  | bat (D : LdBatD E Kc) : LdMv D.src D.tgt
  | split (D : LdSplD E Kc) : LdMv D.src D.tgt
  | fold (D : LdFoldD E Kc) (l : IOR.Link Kc D.src.J D.mid) : LdMv D.src D.tgt
  | loc (D : LdLocD E Kc) : LdMv D.src D.tgt
  | step (a b : LdStage E Kc) (f : a.X → Option b.X) (g : ExtMap a.Ex b.Ex)
      (m : a.X × a.W → b.X × b.W) (back : a.X × a.Ex.Str → b.W → a.W) : LdMv a b

namespace LdMv

def tag : {a b : LdStage E Kc} → LdMv a b → LdTag
  | _, _, .send _ _ => .send
  | _, _, .sub _ _ _ => .sub
  | _, _, .bat _ => .bat
  | _, _, .split _ => .split
  | _, _, .fold _ _ => .fold
  | _, _, .loc _ => .loc
  | _, _, .step _ _ _ _ _ _ => .step

/-- The move as a chain. -/
def chain : {a b : LdStage E Kc} → LdMv a b → IOR.Chain Kc a.J b.J
  | _, _, .send _ d => .one d.link
  | _, _, .sub _ _ c => c
  | _, _, .bat D => .one D.link
  | _, _, .split D => .one D.link
  | _, _, .fold D l => .one (D.link l)
  | _, _, .loc D => .one D.link
  | _, _, .step _ _ f g m back =>
    .one ⟨IOR.pure f g, IOR.Honest.pure f g m, fun x _ w => back x w, IOR.Nums.pure Kc f g⟩

/-- What is asked of a move. -/
def Hyp : {a b : LdStage E Kc} → LdMv a b → Prop
  | _, _, .send _ d => d.Hyp
  | _, _, .sub _ _ c => c.AllB
  | _, _, .bat D => D.Hyp
  | _, _, .split D => D.Hyp
  | _, _, .fold D l => D.Hyp l
  | _, _, .loc D => D.Hyp
  | _, _, .step a b f g m back => IOR.StepT f g m back a.J.rels b.J.rels

end LdMv

/-- A list of moves. -/
inductive LdProg : LdStage E Kc → LdStage E Kc → Type 1
  | nil (a : LdStage E Kc) : LdProg a a
  | snoc {a b c : LdStage E Kc} (p : LdProg a b) (m : LdMv b c) : LdProg a c

namespace LdProg

/-- The links of the list after a chain. -/
def onto {A : IOR.Joint Kc} :
    {a b : LdStage E Kc} → IOR.Chain Kc A a.J → LdProg a b → IOR.Chain Kc A b.J
  | _, _, c, .nil _ => c
  | _, _, c, .snoc p m => (onto c p).append m.chain

def Hyp : {a b : LdStage E Kc} → LdProg a b → Prop
  | _, _, .nil _ => True
  | _, _, .snoc p m => p.Hyp ∧ m.Hyp

/-- every move is of a kind with q -/
def All (q : LdTag → Prop) : {a b : LdStage E Kc} → LdProg a b → Prop
  | _, _, .nil _ => True
  | _, _, .snoc p m => p.All q ∧ q m.tag

def nAll : {a b : LdStage E Kc} → LdProg a b → ℕ
  | _, _, .nil _ => 0
  | _, _, .snoc p m => p.nAll + m.chain.nAll

def nVer : {a b : LdStage E Kc} → LdProg a b → ℕ
  | _, _, .nil _ => 0
  | _, _, .snoc p m => p.nVer + m.chain.nVer

def pBad : {a b : LdStage E Kc} → LdProg a b → ℝ≥0∞
  | _, _, .nil _ => 0
  | _, _, .snoc p m => p.pBad + m.chain.pBad

def pHid : {a b : LdStage E Kc} → LdProg a b → ℝ≥0∞
  | _, _, .nil _ => 0
  | _, _, .snoc p m => p.pHid + m.chain.pHid

end LdProg

/-- A segment, from the stage a (its first oracle messages are sent and sampled) to the stage d
(those of the next segment are). -/
structure LdSeg (a d : LdStage E Kc) : Type 1 where
  /-- the stages before the batching, before the folds, and with all tests open -/
  b  : LdStage E Kc
  b₁ : LdStage E Kc
  c  : LdStage E Kc
  body : LdProg a b
  bat  : LdProg b b₁
  fold : LdProg b₁ c
  /-- the one sending -/
  snd  : LdSendD c
  loc  : LdProg snd.tgt d
  bodyT : body.All fun t => t = .send ∨ t = .sub ∨ t = .step
  batT  : bat.All fun t => t = .bat ∨ t = .split ∨ t = .step
  foldT : fold.All fun t => t = .fold ∨ t = .step
  locT  : loc.All fun t => t = .loc ∨ t = .step

namespace LdSeg
variable {a d : LdStage E Kc} (s : LdSeg a d)

structure Hyp : Prop where
  body : s.body.Hyp
  bat  : s.bat.Hyp
  fold : s.fold.Hyp
  snd  : s.snd.Hyp
  loc  : s.loc.Hyp

/-- The segment's links after a chain. -/
def onto {A : IOR.Joint Kc} (c₀ : IOR.Chain Kc A a.J) : IOR.Chain Kc A d.J :=
  s.loc.onto (.snoc (s.fold.onto (s.bat.onto (s.body.onto c₀))) s.snd.link)

/-- The segment alone. -/
def chain : IOR.Chain Kc a.J d.J := s.onto (.one a.idLink)

def nAll : ℕ :=
  s.body.nAll + s.bat.nAll + s.fold.nAll + s.snd.link.R.shape.nAll + s.loc.nAll
def nVer : ℕ :=
  s.body.nVer + s.bat.nVer + s.fold.nVer + s.snd.link.R.shape.nVer + s.loc.nVer
def pBad : ℝ≥0∞ :=
  s.body.pBad + s.bat.pBad + s.fold.pBad + s.snd.link.P.pBad + s.loc.pBad
def pHid : ℝ≥0∞ :=
  s.body.pHid + s.bat.pHid + s.fold.pHid + s.snd.link.P.pHid + s.loc.pHid

end LdSeg

/-- A reduction on claims about the messages, over the oracle messages of a stage
(Cb/Ld/LdSigLift.lean), as a link. -/
def LdStage.lift (a : LdStage E Kc) {St' Wp' : Type} {E₀' : ExtSpec}
    (B : IOR.Rels Kc St' E₀' (a.S.Msg × Wp')) (R : IOR a.St a.E₀ St' E₀')
    (H : R.Honest (a.S.Msg × a.Wp) (a.S.Msg × Wp'))
    (ext : a.S.Msg → a.St × a.E₀.Str → Tr R.shape → Wp' → a.Wp) (P : IOR.Nums Kc R) :
    IOR.Link Kc a.J (⟨a.S, St', E₀', Wp', B⟩ : LdStage E Kc).J :=
  ⟨R.keep a.S.Smp a.S.ext,
    a.S.liftH H,
    fun x τ w => (w.1, ext (a.S.msgs w.1) (x.1.1, x.2.1) τ w.2),
    P.keep a.S.Smp a.S.ext⟩

end

/-! ## The statements -/

namespace Spec
open IOR

/-- A move with its hypotheses: the bundle without its clause on zero knowledge, link by link. -/
def ldSeg_mv : Prop :=
  ∀ (E Kc : Type) [Field E] [Fintype E] (a b : LdStage E Kc) (m : LdMv a b), m.Hyp → m.chain.AllB

/-- Under the hypotheses below, the moves whose block is named and has no masks in its input have
the whole bundle. -/
def ldSeg_mvT : Prop :=
  ∀ (E Kc : Type) [Field E] [Fintype E] (a b : LdStage E Kc) (m : LdMv a b),
    m.Hyp → m.tag ≠ .sub → m.tag ≠ .split → m.chain.AllT

/-- A split with its hypotheses is a masked block. -/
def ldSeg_split : Prop :=
  ∀ (E Kc : Type) [Field E] [Fintype E] (D : LdSplD E Kc), D.Hyp → D.link.GoodM D.mask

/-- The lemma on kept messages. -/
def ldSeg_kept : Prop :=
  ∀ (E P : Type) [Field E] [Fintype E] [Fintype P] (C : LdCode E P) (e : ℕ) (h : LdHeld E C),
    h.Laws e →
    ∀ (f : C.Word) (w : C.N.Wit) (k : h.K) (σ : (h.o k).Smp), ¬ (h.o k).ClashW (h.sW k f) σ.1 →
      C.Near e f (C.enc w.1 w.2) → (h.o k).Z.val σ.1 (h.msg w.1 k) = σ.2 →
      (h.o k).decW (h.sW k f) σ = some (h.msg w.1 k)

/-- The segment: all of the bundle but zero knowledge. -/
def ldSeg_goodB : Prop :=
  ∀ (E Kc : Type) [Field E] [Fintype E] (a d : LdStage E Kc) (s : LdSeg a d) (w₀ : a.W),
    s.Hyp → (s.chain.link w₀).GoodB

/-- Its knowledge soundness, written out: on collision-free statements that also meet `a.A.on` into
collision-free statements. -/
def ldSeg_into : Prop :=
  ∀ (E Kc : Type) [Field E] [Fintype E] (a d : LdStage E Kc) (s : LdSeg a d) (w₀ : a.W), s.Hyp →
    (s.chain.link w₀).R.red.KnowInto (a.S.over a.A).on (d.S.over d.A).on (a.S.over a.A).relR
      (d.S.over d.A).relR (s.chain.link w₀).ext (s.chain.link w₀).P.err

/-- After any chain. -/
def ldSeg_onto : Prop :=
  ∀ (E Kc : Type) [Field E] [Fintype E] (A : Joint Kc) (a d : LdStage E Kc)
      (c₀ : Chain Kc A a.J) (s : LdSeg a d),
    c₀.AllB → s.Hyp → (s.onto c₀).AllB

/-- The parameter list is derived: sums over the five parts. -/
def ldSeg_nums : Prop :=
  ∀ (E Kc : Type) [Field E] [Fintype E] (A : Joint Kc) (a d : LdStage E Kc)
      (c₀ : Chain Kc A a.J) (s : LdSeg a d),
    ((s.onto c₀).nAll = c₀.nAll + s.nAll ∧
      (s.onto c₀).nVer = c₀.nVer + s.nVer ∧
      (s.onto c₀).pBad = c₀.pBad + s.pBad ∧
      (s.onto c₀).pHid = c₀.pHid + s.pHid) ∧
    ∀ w₀ : a.W,
      (s.chain.link w₀).R.shape.nAll = s.nAll ∧
      (s.chain.link w₀).R.shape.nVer = s.nVer ∧
      (s.chain.link w₀).P.pBad = s.pBad ∧
      (s.chain.link w₀).P.pHid = s.pHid

/-- The moves whose block is named. -/
def ldSeg_rounds : Prop :=
  ∀ (E Kc : Type) [Field E] [Fintype E],
    (∀ (a : LdStage E Kc) (d : LdSendD a),
      d.link.R.shape.nAll = 2 ∧ d.link.R.shape.nVer ≤ 1 ∧ d.link.P.pBad = 0 ∧ d.link.P.pHid = 0) ∧
    (∀ D : LdBatD E Kc, D.link.R.shape.nAll = 1 ∧ D.link.P.pBad = 0 ∧ D.link.P.pHid = 0) ∧
    (∀ D : LdSplD E Kc,
      D.link.R.shape.nAll = 1 ∧ D.link.R.shape.nVer = 0 ∧ D.link.P.pBad = 0 ∧ D.link.P.pHid = 0) ∧
    (∀ D : LdLocD E Kc, D.link.R.shape.nAll = 1 ∧ D.link.P.pBad = 0 ∧ D.link.P.pHid = 0) ∧
    (∀ (D : LdFoldD E Kc) (l : Link Kc D.src.J D.mid),
      (D.link l).R.shape = l.R.shape ∧
      (D.link l).P.pBad = l.P.pBad ∧
      (D.link l).P.pHid = l.P.pHid) ∧
    (∀ (a b : LdStage E Kc) f g m back,
      (LdMv.step a b f g m back).chain.nAll = 0 ∧
      (LdMv.step a b f g m back).chain.nVer = 0 ∧
      (LdMv.step a b f g m back).chain.pBad = 0 ∧
      (LdMv.step a b f g m back).chain.pHid = 0)

/-- How a bundle between the joints S.over A and S'.over B enters a chain of stages. -/
def ldSeg_sub_goodT : Prop :=
  ∀ (E Kc : Type) [Field E] [Fintype E] (a b : LdStage E Kc) (l : Link Kc a.J b.J),
    IOR.GoodT l.R l.H (a.S.over a.A) (b.S.over b.A) l.ext l.P → l.GoodT

def ldSeg_sub_goodM : Prop :=
  ∀ (E Kc : Type) [Field E] [Fintype E] (a b : LdStage E Kc)
      (l : Link Kc a.J b.J) (D : MaskData l.R a.J.W),
    IOR.GoodM l.R l.H (a.S.over a.A) (b.S.over b.A) l.ext l.P D → l.GoodM D

/-- How a reduction on claims about the messages enters. -/
def ldSeg_lift : Prop :=
  ∀ (E Kc : Type) [Field E] [Fintype E] (a : LdStage E Kc) (St' Wp' : Type) (E₀' : ExtSpec)
      (B : Rels Kc St' E₀' (a.S.Msg × Wp')) (R : IOR a.St a.E₀ St' E₀')
      (H : R.Honest (a.S.Msg × a.Wp) (a.S.Msg × Wp'))
      (ext : a.S.Msg → a.St × a.E₀.Str → Tr R.shape → Wp' → a.Wp) (P : Nums Kc R),
    GoodAt R H a.A B ext P →
    (a.lift B R H ext P).GoodB ∧ (H.Exact a.A.rel P.bud → (a.lift B R H ext P).GoodT)

end Spec
end Cb
