-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Gen/FullErrReq.lean: the honest side of the preamble of a request (`LdReq`, Cb/Req1/LdReq.lean)
without the knowledge side of its folds: the same request with the errors of every fold's link
overwritten by the full list (`Err.full`, Cb/Gen/FullErr.lean).

In standard terms: in the sequence of reductions that makes up a request's preamble, the errors of
round-by-round knowledge soundness of every fold are replaced by the trivial ones (probability 1 in
every round).

Definitions, statements (in `Cb.Spec`) and proofs. Any request: no protocol's data occur. Nothing
assumed beyond the hypotheses of the statements and whatever the arguments hold as proofs.
A request r : `LdReq a z` has a first sending, further ones, segments (`LdSeg`, Cb/Req1/LdSeg.lean)
and a last part; `r.chain` is all its links in a row, `r.Hyp` the hypotheses of these four parts.
`r.ZkS` is in Cb/Req1/LdReqS.lean, `Chain.Fmt` in Cb/Req1/LdReqFormat.lean. The knowledge side of a
link is the clause know of `GoodT` (Ior/KnowCollGood.lean): round-by-round knowledge soundness at
the link's errors.

Why: of the moves of a request (`LdMv`, Cb/Req1/LdSeg.lean) one kind alone, "fold D l", holds a link
l as a parameter, and asks the whole bundle of it (`D.Hyp l`: `GoodT` of l at l's own numbers). (The
move "sub a b c" holds a chain c and asks `c.AllB` of it: `GoodB` of each link, know at that link's
own errors included; `LdMv.hon` leaves it as it stands.) Where the knowledge side of that bundle at
the true errors rests on a fact that is only assumed (agreement of codes), r.Hyp is had only under
that fact, and with it all that the library draws from r.Hyp: completeness, formats and hiding of
the request too. The type of the move "fold D l" does not name l: so l can be exchanged for `l.full`
(Cb/Gen/FullErrChain.lean) and the request stays a request between the same stages.

Main names:
  `m.hon`, `p.hon`, `s.hon`, `S.hon`, `r.hon`: a move, a list of moves, a segment (its part "fold"
    alone is touched), a list of segments, a request (its segments alone), with `l.full` for l at
    each move "fold D l".
  `r.hon.Hyp`: the honest form of r.Hyp: all moves' hypotheses as they stand, but a fold's link is
    asked `GoodT` at the full list: nothing on the chance of a cheating prover in the rounds of a
    fold. Of the four clauses of a fold's hypothesis (`D.Hyp l`: good, word, wit, laws) the first
    alone is touched: "word" (every statement that l puts out, on true and on false inputs, has the
    held messages' words in the folded word's slots), "wit" and "laws" are asked as they stand.
  `Spec.fullReq_hyp`: r.Hyp → r.hon.Hyp (the honest form asks less).
  `Spec.fullReq_chain`: r.hon.chain.full = r.chain.full; so (`Spec.fullReq_link`)
    (r.hon.chain.link d).full = (r.chain.link d).full: the two requests, as one link, are the same
    reduction, honest side, extractor and numbers but for the errors.
  `Spec.fullReq_zk`: r.ZkS ↔ r.hon.ZkS (what zero knowledge asks beside the hypotheses reads no
    error of a fold's link). Not so of c at a move "sub a b c" (`LdMv.Zk`, Cb/Req1/LdReq.lean:
    `c.OkGiven base`, Cb/Req1/LdSegFresh.lean; `GoodT.know`, Ior/KnowCollGood.lean).
  `Spec.fullReq_goodT`: r.hon.Hyp, r.ZkS ⇒ (r.chain.link w₀).full.GoodT: r's own chain as one link
    has the whole bundle at the full list.
  `Spec.fullReq_start`: the same for the request as one reduction from a statement without oracle
    messages (Cb/Req1/LdReqStart.lean).
  `Spec.fullReq_startFmt`: the four conclusions of `Cb.Spec.ldReqStart_fmt` at r itself (index left
    alone, record handed on, prover encoded index handed on, the budget bears what follows) from
    r.hon.Hyp in the place of r.Hyp. (not all hypotheses are named here: see its statement)

Limits: under the hypotheses of `Spec.fullReq_goodT` and `Spec.fullReq_startFmt`: from r.hon.Hyp,
r.ZkS and the format one has of r itself, not of another request: point structures, locality, the
honest prover is accepted outside the two withheld sets, their chances are below r's own pBad, pHid,
honest-verifier exact zero knowledge at r's own budget (`GoodT.exact`: `Honest.Exact`,
Ior/Honest.lean: `ρ ∉ H.Hid w x →`), the four formats. `Spec.fullReq_goodT`, `Spec.fullReq_start`
and `Spec.fullReq_startFmt` conclude nothing on the chance of a cheating prover: at the full list
the knowledge side of a reduction with a round says nothing. This file does not say that a request
has r.hon.Hyp without r.Hyp: that is for each kind of fold. It says nothing on numerals. r.ZkS and
r.chain.Fmt φ ψ are premises here: whoever wants them without the fact that r.Hyp rests on has to
prove them so.


Terms: lean/GLOSSARY.md.
-/
import Cb.Gen.FullErrChain
import Cb.Obj.LdObjectReqSegS
import Cb.Req1.LdSegFormat

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Cb.Ood IOR IOR.Chain

section
variable {E Kc : Type} [Field E] [Fintype E]

/-- the move, with the full list for the errors of a fold's link -/
def LdMv.hon : {a b : LdStage E Kc} → LdMv a b → LdMv a b
  | _, _, .send a d => .send a d
  | _, _, .sub a b c => .sub a b c
  | _, _, .bat D => .bat D
  | _, _, .split D => .split D
  | _, _, .fold D l => .fold D l.full
  | _, _, .loc D => .loc D
  | _, _, .step a b f g m back => .step a b f g m back

def LdProg.hon : {a b : LdStage E Kc} → LdProg a b → LdProg a b
  | _, _, .nil a => .nil a
  | _, _, .snoc p m => .snoc p.hon m.hon

theorem LdMv.tag_hon {a b : LdStage E Kc} (m : LdMv a b) : m.hon.tag = m.tag := by cases m <;> rfl

theorem LdProg.hon_nil (a : LdStage E Kc) : (LdProg.nil a).hon = .nil a := by rw [LdProg.hon]
theorem LdProg.hon_snoc {a b c : LdStage E Kc} (p : LdProg a b) (m : LdMv b c) :
    (p.snoc m).hon = p.hon.snoc m.hon := by rw [LdProg.hon]

theorem LdProg.all_hon (q : LdTag → Prop) {a b : LdStage E Kc} (p : LdProg a b) (h : p.All q) :
    p.hon.All q := by
  induction p with
  | nil => rw [LdProg.hon_nil]; exact h
  | snoc p m ih =>
      rw [LdProg.hon_snoc]
      obtain ⟨h1, h2⟩ := (LdProg.all_snoc q p m).1 h
      exact (LdProg.all_snoc q _ _).2 ⟨ih h1, by rw [LdMv.tag_hon]; exact h2⟩

/-- the segment: its part "fold" alone is touched -/
def LdSeg.hon {a d : LdStage E Kc} (s : LdSeg a d) : LdSeg a d :=
  { s with fold := s.fold.hon, foldT := LdProg.all_hon _ s.fold s.foldT }

def LdSegs.hon : {a b : LdStage E Kc} → LdSegs a b → LdSegs a b
  | _, _, .nil a => .nil a
  | _, _, .snoc S s => .snoc S.hon s.hon

theorem LdSegs.hon_nil (a : LdStage E Kc) : (LdSegs.nil a).hon = .nil a := by rw [LdSegs.hon]
theorem LdSegs.hon_snoc {a b c : LdStage E Kc} (S : LdSegs a b) (s : LdSeg b c) :
    (S.snoc s).hon = S.hon.snoc s.hon := by rw [LdSegs.hon]

/-- The request with the full list for the errors of every fold's link. -/
def LdReq.hon {a z : LdStage E Kc} (r : LdReq a z) : LdReq a z := { r with segs := r.segs.hon }

end

namespace Spec
section
variable (E Kc : Type) [Field E] [Fintype E]

def fullReq_hyp : Prop := ∀ (a z : LdStage E Kc) (r : LdReq a z), r.Hyp → r.hon.Hyp

def fullReq_chain : Prop := ∀ (a z : LdStage E Kc) (r : LdReq a z), r.hon.chain.full = r.chain.full

def fullReq_link : Prop :=
  ∀ (a z : LdStage E Kc) (r : LdReq a z) (d : a.W),
    (r.hon.chain.link d).full = (r.chain.link d).full

def fullReq_zk : Prop := ∀ (a z : LdStage E Kc) (r : LdReq a z), r.ZkS ↔ r.hon.ZkS

def fullReq_fmt : Prop :=
  ∀ (a z : LdStage E Kc) (r : LdReq a z) (E0 : ExtSpec) (Rc Pw : Type)
      (φ : JFmt Kc E0 Rc Pw a.J) (ψ : JFmt Kc E0 Rc Pw z.J),
    r.chain.Fmt φ ψ ↔ r.hon.chain.Fmt φ ψ

/-- States: under `r.hon.Hyp` and `r.ZkS` the request's own chain, as one link, has the whole bundle
at the full list. -/
def fullReq_goodT : Prop :=
  ∀ (a z : LdStage E Kc) (r : LdReq a z) (w₀ : a.W),
    r.hon.Hyp → r.ZkS → (r.chain.link w₀).full.GoodT

end

/-- The request as one reduction from a statement without oracle messages. -/
def fullReq_start : Prop :=
  ∀ (E Kc Xi Wi : Type) (E0 : ExtSpec) [Field E] [Fintype E] (A : Rels Kc Xi E0 Wi)
      (z : LdStage E Kc) (r : LdReq (LdStage.start E Kc A) z) (w₀ : Wi),
    r.hon.Hyp → r.ZkS → GoodT (r.F w₀) (r.FH w₀) A z.J.rels (r.Fext w₀) (r.FP w₀).full

open Classical in
/-- The formats, at r itself. -/
def fullReq_startFmt : Prop :=
  ∀ (E Kc Xi Wi Rc Pw : Type) (E0 : ExtSpec) [Field E] [Fintype E] (A : Rels Kc Xi E0 Wi)
      (S : Sig E) (St Wp : Type) (B : Rels Kc St E0 (S.Msg × Wp))
      (r : LdReq (LdStage.start E Kc A) ⟨S, St, E0, Wp, B⟩) (w₀ : Wi)
      (φ : JFmt Kc E0 Rc Pw (LdStage.start E Kc A).J)
      (ψ : JFmt Kc E0 Rc Pw (⟨S, St, E0, Wp, B⟩ : LdStage E Kc).J) (qa : Finset E0.Pos → Prop),
    r.hon.Hyp → r.chain.Fmt φ ψ → φ.ix = IxAt.left E0 (Sig.nil E).ext → ψ.ix = IxAt.left E0 S.ext →
    (∀ U, φ.q U → qa (U.biUnion (ldStartE E E0).src)) →
    (r.F w₀).IdxPrefix ∧
    (r.F w₀).Passes (fun x => φ.rc (ldStartX E x)) ψ.rc ∧
    (r.FH w₀).Hands A.rel (fun w => φ.px (ldStartW E w)) ψ.px ∧
    (r.F w₀).Bears (r.FP w₀).bud qa ψ.q

end Spec

section
variable {E Kc : Type} [Field E] [Fintype E]

/-! ## a move -/

/-- `D.link l` (l, then a step without rounds) reads the errors of l in the field err alone -/
theorem LdFoldD.link_full (D : LdFoldD E Kc) (l : Link Kc D.src.J D.mid) :
    (D.link l.full).full = (D.link l).full := rfl

theorem LdMv.chain_hon {a b : LdStage E Kc} (m : LdMv a b) : m.hon.chain.full = m.chain.full := by
  cases m with
  | fold D l =>
      show (Chain.one (D.link l.full)).full = (Chain.one (D.link l)).full
      rw [full_one, full_one, LdFoldD.link_full]
  | send _ _ => rfl
  | sub _ _ _ => rfl
  | bat _ => rfl
  | split _ => rfl
  | loc _ => rfl
  | step _ _ _ _ _ _ => rfl

theorem LdMv.after_hon {a b : LdStage E Kc} (m : LdMv a b) (base : MaskFact a.J.W → Prop) :
    m.hon.After base = m.After base := by
  funext f
  apply propext
  show m.hon.chain.FreshGiven base f ↔ m.chain.FreshGiven base f
  rw [← (chainFull_blind Kc _ _ m.hon.chain).2.1 base f,
    ← (chainFull_blind Kc _ _ m.chain).2.1 base f, LdMv.chain_hon]

theorem LdMv.zk_hon {a b : LdStage E Kc} (m : LdMv a b) (base : MaskFact a.J.W → Prop) :
    m.hon.Zk base ↔ m.Zk base := by
  cases m <;> exact Iff.rfl

theorem LdMv.hyp_hon {a b : LdStage E Kc} (m : LdMv a b) (h : m.Hyp) : m.hon.Hyp := by
  cases m with
  | fold D l => exact ⟨goodT_full _ _ _ _ _ _ _ _ _ _ _ _ _ h.good, h.word, h.wit, h.laws⟩
  | send _ _ => exact h
  | sub _ _ _ => exact h
  | bat _ => exact h
  | split _ => exact h
  | loc _ => exact h
  | step _ _ _ _ _ _ => exact h

theorem LdMv.fmt_hon {a b : LdStage E Kc} (m : LdMv a b) {E0 : ExtSpec} {Rc Pw : Type}
    (φ : JFmt Kc E0 Rc Pw a.J) (ψ : JFmt Kc E0 Rc Pw b.J) : m.hon.Fmt φ ψ ↔ m.Fmt φ ψ := by
  show m.hon.chain.Fmt φ ψ ↔ m.chain.Fmt φ ψ
  rw [← (chainFull_blind Kc _ _ m.hon.chain).2.2 E0 Rc Pw φ ψ,
    ← (chainFull_blind Kc _ _ m.chain).2.2 E0 Rc Pw φ ψ, LdMv.chain_hon]

/-! ## a list of moves -/

theorem LdProg.fmt_hon {a b : LdStage E Kc} (p : LdProg a b) {E0 : ExtSpec}
    {Rc Pw : Type} (φ : JFmt Kc E0 Rc Pw a.J) :
    ∀ ψ : JFmt Kc E0 Rc Pw b.J, p.hon.Fmt φ ψ ↔ p.Fmt φ ψ := by
  induction p with
  | nil => intro ψ; rw [LdProg.hon_nil]
  | snoc p m ih =>
      intro ψ
      rw [LdProg.hon_snoc, LdProg.fmt_snoc, LdProg.fmt_snoc]
      exact exists_congr fun χ => and_congr (ih χ) (m.fmt_hon χ ψ)

theorem LdProg.after_hon {a b : LdStage E Kc} (p : LdProg a b) (base : MaskFact a.J.W → Prop) :
    p.hon.After base = p.After base := by
  induction p with
  | nil => rw [LdProg.hon_nil]
  | snoc p m ih => rw [LdProg.hon_snoc, LdProg.after_snoc, LdProg.after_snoc, ih, LdMv.after_hon]

theorem LdProg.zk_hon {a b : LdStage E Kc} (p : LdProg a b) (base : MaskFact a.J.W → Prop) :
    p.hon.Zk base ↔ p.Zk base := by
  induction p with
  | nil => rw [LdProg.hon_nil]
  | snoc p m ih =>
    rw [LdProg.hon_snoc, LdProg.zk_snoc, LdProg.zk_snoc, ih, LdProg.after_hon, LdMv.zk_hon]

theorem LdProg.hyp_hon {a b : LdStage E Kc} (p : LdProg a b) (h : p.Hyp) : p.hon.Hyp := by
  induction p with
  | nil => rw [LdProg.hon_nil]; exact h
  | snoc p m ih =>
      rw [LdProg.hon_snoc]
      exact (LdProg.hyp_snoc _ _).2
        ⟨ih ((LdProg.hyp_snoc p m).1 h).1, m.hyp_hon ((LdProg.hyp_snoc p m).1 h).2⟩

/-- a list of moves after chains that are equal but for their errors -/
theorem LdProg.onto_full {A : Joint Kc} {a b : LdStage E Kc} (p : LdProg a b)
    (c c' : Chain Kc A a.J) (h : c.full = c'.full) :
    (p.onto c).full = (p.onto c').full := by
  induction p with
  | nil => rw [LdProg.onto_nil, LdProg.onto_nil]; exact h
  | snoc p m ih => rw [LdProg.onto_snoc, LdProg.onto_snoc, chainFull_append, chainFull_append, ih]

theorem LdProg.onto_hon {A : Joint Kc} {a b : LdStage E Kc} (p : LdProg a b)
    (c c' : Chain Kc A a.J) (h : c.full = c'.full) :
    (p.hon.onto c).full = (p.onto c').full := by
  induction p with
  | nil => rw [LdProg.hon_nil, LdProg.onto_nil, LdProg.onto_nil]; exact h
  | snoc p m ih =>
    rw [LdProg.hon_snoc, LdProg.onto_snoc, LdProg.onto_snoc, chainFull_append,
      chainFull_append, ih, LdMv.chain_hon]

/-! ## a segment -/

theorem LdSeg.after_hon {a d : LdStage E Kc} (s : LdSeg a d) (base : MaskFact a.J.W → Prop) :
    s.hon.After base = s.After base := by
  show s.loc.After
      ((Chain.one s.snd.link).FreshGiven (s.fold.hon.After (s.bat.After (s.body.After base)))) =
    s.loc.After ((Chain.one s.snd.link).FreshGiven (s.fold.After (s.bat.After (s.body.After base))))
  rw [LdProg.after_hon]

theorem LdSeg.zk_hon {a d : LdStage E Kc} (s : LdSeg a d) (base : MaskFact a.J.W → Prop) :
    s.hon.Zk base ↔ s.Zk base := by
  have e : s.hon.mid base = s.mid base := LdProg.after_hon s.fold _
  constructor
  · intro h
    exact ⟨h.body, h.bat, (LdProg.zk_hon s.fold _).1 h.fold,
      by have := h.loc; rw [e] at this; exact this⟩
  · intro h
    exact ⟨h.body, h.bat, (LdProg.zk_hon s.fold _).2 h.fold, by rw [e]; exact h.loc⟩

theorem LdSeg.fmt_hon {a d : LdStage E Kc} (s : LdSeg a d) {E0 : ExtSpec} {Rc Pw : Type}
    (φ : JFmt Kc E0 Rc Pw a.J) (ψ : JFmt Kc E0 Rc Pw d.J) : s.hon.Fmt φ ψ ↔ s.Fmt φ ψ :=
  exists_congr fun _ =>
    exists_congr fun φb₁ =>
      exists_congr fun φc =>
        exists_congr fun _ =>
          and_congr Iff.rfl (and_congr Iff.rfl (and_congr (s.fold.fmt_hon φb₁ φc) Iff.rfl))

theorem LdSeg.hyp_hon {a d : LdStage E Kc} (s : LdSeg a d) (h : s.Hyp) : s.hon.Hyp :=
  ⟨h.body, h.bat, s.fold.hyp_hon h.fold, h.snd, h.loc⟩

theorem LdSeg.onto_hon {A : Joint Kc} {a d : LdStage E Kc} (s : LdSeg a d)
    (c c' : Chain Kc A a.J) (h : c.full = c'.full) :
    (s.hon.onto c).full = (s.onto c').full := by
  show (s.loc.onto (.snoc (s.fold.hon.onto (s.bat.onto (s.body.onto c))) s.snd.link)).full =
    (s.loc.onto (.snoc (s.fold.onto (s.bat.onto (s.body.onto c'))) s.snd.link)).full
  refine LdProg.onto_full _ _ _ ?_
  rw [full_snoc, full_snoc,
    LdProg.onto_hon s.fold _ _ (LdProg.onto_full s.bat _ _ (LdProg.onto_full s.body _ _ h))]

/-! ## segments in a row -/

theorem LdSegs.afterJ_hon {a b : LdStage E Kc} (S : LdSegs a b) (base : MaskFact a.J.W → Prop) :
    S.hon.AfterJ base = S.AfterJ base := by
  induction S with
  | nil => rw [LdSegs.hon_nil]
  | snoc S s ih => rw [LdSegs.hon_snoc, LdSegs.afterJ_snoc, LdSegs.afterJ_snoc, ih, LdSeg.after_hon]

theorem LdSegs.zkJ_hon {a b : LdStage E Kc} (S : LdSegs a b) (base : MaskFact a.J.W → Prop) :
    S.hon.ZkJ base ↔ S.ZkJ base := by
  induction S with
  | nil => rw [LdSegs.hon_nil]
  | snoc S s ih =>
    rw [LdSegs.hon_snoc, LdSegs.zkJ_snoc, LdSegs.zkJ_snoc, ih, LdSegs.afterJ_hon, LdSeg.zk_hon]

theorem LdSegs.hyp_hon {a b : LdStage E Kc} (S : LdSegs a b) (h : S.Hyp) : S.hon.Hyp := by
  induction S with
  | nil => rw [LdSegs.hon_nil]; exact h
  | snoc S s ih =>
      rw [LdSegs.hon_snoc]
      exact (LdSegs.hyp_snoc _ _).2
        ⟨ih ((LdSegs.hyp_snoc S s).1 h).1, s.hyp_hon ((LdSegs.hyp_snoc S s).1 h).2⟩

theorem LdSegs.onto_hon {A : Joint Kc} {a b : LdStage E Kc} (S : LdSegs a b)
    (c c' : Chain Kc A a.J) (h : c.full = c'.full) :
    (S.hon.onto c).full = (S.onto c').full := by
  induction S with
  | nil => rw [LdSegs.hon_nil, LdSegs.onto_nil, LdSegs.onto_nil]; exact h
  | snoc S s ih => rw [LdSegs.hon_snoc, LdSegs.onto_snoc, LdSegs.onto_snoc]; exact s.onto_hon _ _ ih

end

/-! ## the request -/

section
variable (E Kc : Type) [Field E] [Fintype E]

theorem fullReq_hyp : Spec.fullReq_hyp E Kc := fun _ _ r h =>
  ⟨h.first, h.more, r.segs.hyp_hon h.segs, h.last⟩

theorem fullReq_chain : Spec.fullReq_chain E Kc := fun _ _ r =>
  LdProg.onto_full r.last _ _ (r.segs.onto_hon _ _ rfl)

theorem fullReq_link : Spec.fullReq_link E Kc := fun a z r d =>
  chainFull_linkOf (fullReq_chain E Kc a z r) d

theorem fullReq_zk : Spec.fullReq_zk E Kc := by
  intro a z r
  have e : r.hon.segs.AfterJ r.hon.base₀ = r.segs.AfterJ r.base₀ := LdSegs.afterJ_hon r.segs r.base₀
  constructor
  · intro h
    exact ⟨(LdSegs.zkJ_hon r.segs r.base₀).2 h.segs, by rw [e]; exact h.last⟩
  · intro h
    exact ⟨(LdSegs.zkJ_hon r.segs r.base₀).1 h.segs, by have := h.last; rw [e] at this; exact this⟩

theorem fullReq_fmt : Spec.fullReq_fmt E Kc := by
  intro a z r E0 Rc Pw φ ψ
  rw [← (chainFull_blind Kc _ _ r.chain).2.2 E0 Rc Pw φ ψ,
    ← (chainFull_blind Kc _ _ r.hon.chain).2.2 E0 Rc Pw φ ψ, fullReq_chain]

theorem fullReq_goodT : Spec.fullReq_goodT E Kc := by
  intro a z r w₀ h hz
  rw [← fullReq_link]
  exact (linkFull_good Kc _ _ _).2.1
    (ldReqS_goodT E Kc a z r.hon w₀ h ((fullReq_zk E Kc a z r).1 hz))

end

section
variable {E Kc Xi Wi : Type}
  {E0 : ExtSpec} [Field E] [Fintype E] {A : Rels Kc Xi E0 Wi} {z : LdStage E Kc}

/-- a link from the start stage as one reduction from the statement without oracle messages: the
whole bundle at the full list -/
def LdStartGood (l : Link Kc (LdStage.start E Kc A).J z.J) : Prop :=
  GoodT (l.R.pre (fun x => some (ldStartX E x)) (ldStartE E E0))
    (l.H.pre (fun x => some (ldStartX E x)) (ldStartE E E0) fun p =>
      (ldStartX E p.1, ldStartW E p.2))
    A z.J.rels (fun a τ w => (l.ext (ldStartX E a.1, (ldStartE E E0).map a.2) τ w).2)
    (l.P.pre (fun x => some (ldStartX E x)) (ldStartE E E0)).full

omit [Fintype E] in
theorem LdStartGood.of {l l' : Link Kc (LdStage.start E Kc A).J z.J}
    (e : l'.full = l.full) (h : LdStartGood l') : LdStartGood l := by
  have h1 : LdStartGood l'.full := h
  rw [e] at h1
  exact h1

end

theorem fullReq_start : Spec.fullReq_start := by
  intro E Kc Xi Wi E0 _ _ A z r w₀ h hz
  have g : LdStartGood (r.hon.chain.link (ldStartW E w₀)) :=
    goodT_full _ _ _ _ _ _ _ _ _ _ _ _ _
      (ldReqStartS_goodT E Kc Xi Wi E0 A z r.hon w₀ h ((fullReq_zk E Kc _ z r).1 hz))
  exact g.of (fullReq_link E Kc _ z r _)

section
variable {E Kc Xi Wi Rc Pw : Type} {E0 : ExtSpec} [Field E] [Fintype E] {A : Rels Kc Xi E0 Wi}
  {S : Sig E} {St Wp : Type} {B : Rels Kc St E0 (S.Msg × Wp)}

open Classical in
/-- the four formats of such a link as one reduction -/
def LdStartFmt (l : Link Kc (LdStage.start E Kc A).J (⟨S, St, E0, Wp, B⟩ : LdStage E Kc).J)
    (φ : JFmt Kc E0 Rc Pw (LdStage.start E Kc A).J)
    (ψ : JFmt Kc E0 Rc Pw (⟨S, St, E0, Wp, B⟩ : LdStage E Kc).J) (qa : Finset E0.Pos → Prop) :
    Prop :=
  (l.R.pre (fun x => some (ldStartX E x)) (ldStartE E E0)).IdxPrefix ∧
  (l.R.pre (fun x => some (ldStartX E x)) (ldStartE E E0)).Passes
    (fun x => φ.rc (ldStartX E x)) ψ.rc ∧
  (l.H.pre (fun x => some (ldStartX E x)) (ldStartE E E0) fun p =>
      (ldStartX E p.1, ldStartW E p.2)).Hands
    A.rel (fun w => φ.px (ldStartW E w)) ψ.px ∧
  (l.R.pre (fun x => some (ldStartX E x)) (ldStartE E E0)).Bears
    (l.P.pre (fun x => some (ldStartX E x)) (ldStartE E E0)).bud qa ψ.q

omit [Fintype E] in
theorem LdStartFmt.of
    {l l' : Link Kc (LdStage.start E Kc A).J (⟨S, St, E0, Wp, B⟩ : LdStage E Kc).J}
    {φ : JFmt Kc E0 Rc Pw (LdStage.start E Kc A).J}
    {ψ : JFmt Kc E0 Rc Pw (⟨S, St, E0, Wp, B⟩ : LdStage E Kc).J} {qa : Finset E0.Pos → Prop}
    (e : l'.full = l.full) (h : LdStartFmt l' φ ψ qa) : LdStartFmt l φ ψ qa := by
  have h1 : LdStartFmt l'.full φ ψ qa := h
  rw [e] at h1
  exact h1

end

theorem fullReq_startFmt : Spec.fullReq_startFmt := by
  intro E Kc Xi Wi Rc Pw E0 _ _ A S St Wp B r w₀ φ ψ qa h hF hφ hψ hq
  have g : LdStartFmt (r.hon.chain.link (ldStartW E w₀)) φ ψ qa :=
    ldReqStart_fmt E Kc Xi Wi Rc Pw E0 A S St Wp B r.hon w₀ φ ψ qa h
      ((fullReq_fmt E Kc _ _ r E0 Rc Pw φ ψ).1 hF) hφ hψ hq
  exact g.of (fullReq_link E Kc _ _ r _)

end Cb
