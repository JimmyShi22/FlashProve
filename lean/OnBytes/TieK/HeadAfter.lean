-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TieK/HeadAfter.lean: a proof's first chain's block, from the end of the last link's routine
to the block's own end, with every state named and tied to the one before it.

"The program" is the Lean program verify-on-bytes. OnBytes/TieK/HeadAt.lean takes the block
Proof.firstBlock apart from its first context to the end of the last link's routine. This file goes
on from there, to the context on which the verdict rests:
 - LinkClosed, runLinkH_whole: what runLinkH does behind the routine: two public tests; if the link
   leaves a row on the weight table, the call that makes that row; and the value that runLinkH
   returns: the chain's state as the routine has left it, and the result so far;
 - AfterHead: then the call after the last link (ChainCheck.finish: it holds the links' last
   proximity test); what the links' block returns; the reply as received; the named test that
   compares it with the caller's; the number of rows; the first part of the test on the table, on
   the index-mask message and the rows that the links return; the round in which the chain is
   sealed;
 - head_whole_of_links, head_whole_of_first_yes: HeadAt and AfterHead together, at the same letters.
So what the last link leaves for the rest of the file stands in clauses: the chain's state Lc'.check
for the call after the links; the result's index-mask message and rows for the test on the table.
Nothing is asked of any routine. Every state is a letter; each clause is a run of one call of the
program's own text from one state to the next, or a public test that has passed.

What is not here. That the named test on the reply was TRUE: where it fails it leaves a mark and the
block goes on. What any of the calls does.

Main definitions: outOf, LinkClosed, AfterHead.
Main theorems: runLinkH_whole, head_whole_of_links, head_whole_of_first_yes.
It claims nothing on soundness. The program does not import this file.
-/
import OnBytes.TieK.HeadAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.TieK

/-- The result so far with which runLinkH calls the link's routine: at the head's link the first
plain scalar of the chain's state is entered as the reply received. -/
@[reducible] def outOf (X : Model.Stages.LinkH) (chk : Model.ChainCheck)
    (out1 : Proof.LinksResult) : Proof.LinksResult :=
  if X.kind == 2 then { out1 with reply := chk.plain[0]? } else out1

/-- What runLinkH has done behind the routine of the link X. o, Lc', F', c2: what the routine has
returned and left. r, c': what runLinkH returns and leaves. -/
structure LinkClosed (p : Params.First) (wsLay : Model.WsLay) (X : Model.Stages.LinkH)
    (chk : Model.ChainCheck) (out1 : Proof.LinksResult) (o : Option Model.WsForkOut)
    (Lc' : Model.LinkCtx) (F' : Model.Fork) (c2 : Ctx) (r : Model.ChainCheck × Proof.LinksResult)
    (c' : Ctx) : Prop where
  /-- the routine has closed its link -/
  closed : (Lc'.handed && Lc'.done) = true
  /-- under the plan from which the link's record was made -/
  same_plan : Model.Stages.samePlan X F' Lc'.list = true
  /-- the chain's state goes on as the routine has left it -/
  next : r.1 = Lc'.check
  /-- a link that leaves a row on the weight table: the call that makes the row; else nothing -/
  row : (X.fv = true ∧ ∃ o' row, o = some o' ∧
      (Model.Stages.pendingRowH wsLay (outOf X chk out1).indexMasks o' X.NCL p.lin).Yields c2 row
        c' ∧
      r.2 = { outOf X chk out1 with pending := (outOf X chk out1).pending ++ [row] }) ∨
    (¬ X.fv = true ∧ c' = c2 ∧ r.2 = outOf X chk out1)

/-- **One link, whole.** -/
theorem runLinkH_whole {links : Array Model.Stages.LinkH} {p : Params.First} {wsLay : Model.WsLay}
    {l : Nat} {X : Model.Stages.LinkH} {check : Model.ChainCheck} {out : Proof.LinksResult}
    {c c' : Ctx} {r : Model.ChainCheck × Proof.LinksResult}
    (h : (Model.Stages.runLinkH links p wsLay l X check out).Yields c r c') :
    ∃ chk c0 out1 c1 o Lc' F' c2,
      LinkOpened links p l X check out c chk c0 out1 c1 ∧
      (StateT.run (StateT.run X.run
        { check := chk, link := l, arrayOf := X.arrayOf, list := X.Tp }) X.Fp).Yields c1
        ((o, Lc'), F') c2 ∧
      LinkClosed p wsLay X chk out1 o Lc' F' c2 r c' := by
  unfold Model.Stages.runLinkH at h
  obtain ⟨chk, c0, h0, g1⟩ := bindY h
  obtain ⟨out1, ca, hm, g2⟩ := iteY g1
  obtain ⟨_, ca1, m1, g3⟩ := bindY g2
  obtain ⟨t1, e1⟩ := (mustAsY _ _ _ _ _).1 m1
  obtain ⟨_, ca2, m2, g4⟩ := bindY g3
  obtain ⟨t2, e2⟩ := (Blk.yields_must _ _ _).1 m2
  obtain ⟨⟨⟨o, Lc'⟩, F'⟩, ca3, m3, g5⟩ := bindY g4
  have m3' := (inPlaceY _ _ _ _ _).1 m3
  rw [e2, e1] at m3'
  obtain ⟨_, ca4, m4, g6⟩ := bindY g5
  obtain ⟨t4, e4⟩ := (mustAsY _ _ _ _ _).1 m4
  obtain ⟨_, ca5, m5, g7⟩ := bindY g6
  obtain ⟨t5, e5⟩ := (mustAsY _ _ _ _ _).1 m5
  rw [e5, e4] at g7
  have hmasks : ((l == 0) = true ∧ ∃ im, (Model.Stages.indexMasksH links p chk).Yields c0 im ca ∧
      out1 = { out with indexMasks := im }) ∨ (¬ (l == 0) = true ∧ out1 = out ∧ ca = c0) := by
    rcases hm with ⟨hp, im, cm, k1, k2⟩ | ⟨hp, k1⟩
    · obtain ⟨q1, q2⟩ := (Blk.yields_pure _ _ _ _).1 k2
      rw [q2]
      exact Or.inl ⟨hp, im, k1, q1⟩
    · obtain ⟨q1, q2⟩ := (Blk.yields_pure _ _ _ _).1 k1
      exact Or.inr ⟨hp, q1, q2⟩
  have hclosed : LinkClosed p wsLay X chk out1 o Lc' F' ca3 r c' := by
    by_cases hf : X.fv = true
    · rw [if_pos hf] at g7
      cases o with
      | none =>
        have k := (Blk.yields_iff _ _ _ _).1 g7
        cases k
      | some o' =>
        obtain ⟨row, cb, hr, g8⟩ := bindY g7
        obtain ⟨k1, k2⟩ := (Blk.yields_pure _ _ _ _).1 g8
        rw [k2]
        exact ⟨t4, t5, by rw [k1], Or.inl ⟨hf, o', row, rfl, hr, by rw [k1]⟩⟩
    · rw [if_neg hf] at g7
      obtain ⟨k1, k2⟩ := (Blk.yields_pure _ _ _ _).1 g7
      exact ⟨t4, t5, by rw [k1], Or.inr ⟨hf, k2, by rw [k1]⟩⟩
  exact ⟨chk, c0, out1, ca, o, Lc', F', ca3, ⟨h0, hmasks, eq_of_beq t1, eq_of_beq t2⟩, m3', hclosed⟩

/-- What a proof's first chain's block has done from the end of the last link's routine (w, Lc', F',
c4) to its own end (real, cEnd). rE, c5: what runLinkH has returned and left at the last link. res,
cL: what the links' block has returned and left. got: the reply as received. -/
structure AfterHead (p : Params.First) (wsLay : Model.WsLay) (Xh : Model.Stages.LinkH) (reply : E)
    (chk : Model.ChainCheck) (out1 : Proof.LinksResult) (w : Option Model.WsForkOut)
    (Lc' : Model.LinkCtx) (F' : Model.Fork) (c4 : Ctx)
    (rE : Model.ChainCheck × Proof.LinksResult) (c5 : Ctx) (res : Proof.LinksResult) (cL : Ctx)
    (got : E) (c6 : Ctx) (lin : LinFirst) (c7 : Ctx) (real : Proof.FirstEnd) (cEnd : Ctx) :
    Prop where
  /-- the last link, behind its routine -/
  link_closed : LinkClosed p wsLay Xh chk out1 w Lc' F' c4 rE c5
  /-- the call after the last link -/
  finish : rE.1.finish.Yields c5 () cL
  /-- what the links' block returns -/
  result : res = rE.2
  /-- a reply was received -/
  reply_got : res.reply = some got
  /-- the named test that compares it with the caller's reply -/
  reply_test : (Blk.check Proof.replyCheck (got == reply)).Yields cL () c6
  /-- as many rows on the table as the parameter bytes say -/
  rows : (res.pending.length == p.pendingRows) = true
  /-- the first part of the test on the table -/
  member : (memberFirstVerify p.lin res.indexMasks res.pending).Yields c6 lin c7
  /-- the seal, and what the block returns -/
  sealing : (Proof.firstEnd lin).Yields c7 real cEnd

/-- **All links of a proof, whole**, for a list of links that ends in a link of kind 2. -/
theorem head_whole_of_links {Xs : List Model.Stages.LinkH} {Xh : Model.Stages.LinkH}
    {p : Params.First} {wsLay : Model.WsLay} {c c' : Ctx} {res : Proof.LinksResult}
    (h : (Model.Stages.runLinksH (Xs ++ [Xh]).toArray p wsLay).Yields c res c') :
    ∃ ck0 c0 ck o1 c1 chk c2 out1 c3 w Lc' F' c4 rE c5,
      HeadAt p wsLay Xs Xh c ck0 c0 ck o1 c1 chk c2 out1 c3 w Lc' F' c4 ∧
      LinkClosed p wsLay Xh chk out1 w Lc' F' c4 rE c5 ∧
      rE.1.finish.Yields c5 () c' ∧ res = rE.2 := by
  unfold Model.Stages.runLinksH at h
  obtain ⟨ck0, c0, h0, g1⟩ := bindY h
  obtain ⟨⟨ckE, oE⟩, cE, h1, g2⟩ := bindY g1
  obtain ⟨_, cF, hfin, g3⟩ := bindY g2
  obtain ⟨e, ec⟩ := (Blk.yields_pure _ _ _ _).1 g3
  obtain ⟨ck, o1, c1, k1, k2⟩ := runLinksFrom_split Xs Xh 0 ck0 {} c0 cE (ckE, oE) h1
  obtain ⟨chk, c2, out1, c3, w, Lc', F', c4, q1, q2, q3⟩ := runLinkH_whole k2
  rw [ec]
  exact ⟨ck0, c0, ck, o1, c1, chk, c2, out1, c3, w, Lc', F', c4, (ckE, oE), cE,
    ⟨h0, k1, q1, q2, q3.closed, q3.same_plan⟩, q3, hfin, e⟩

/-- **From the yes of a proof's first chain's block on a view, whole.** -/
theorem head_whole_of_first_yes {Xs : List Model.Stages.LinkH} {Xh : Model.Stages.LinkH}
    {p : Params.First} {wsLay : Model.WsLay} {reply : E} {v : Fmt.View} {real : Proof.FirstEnd}
    (h : (Proof.firstBlock p (Model.Stages.runLinksH (Xs ++ [Xh]).toArray p wsLay) reply).runOn
      (Proof.firstStart p) v = .ok real) :
    ∃ cEnd res cL ck0 c0 ck o1 c1 chk c2 out1 c3 w Lc' F' c4 rE c5 got c6 lin c7,
      RanAt (Proof.firstBlock p (Model.Stages.runLinksH (Xs ++ [Xh]).toArray p wsLay) reply)
        (Proof.firstStart p) v real cEnd ∧
      (Model.Stages.runLinksH (Xs ++ [Xh]).toArray p wsLay).Yields
        (startCtx (Proof.firstStart p) v) res cL ∧
      HeadAt p wsLay Xs Xh (startCtx (Proof.firstStart p) v) ck0 c0 ck o1 c1 chk c2 out1 c3 w Lc' F'
        c4 ∧
      AfterHead p wsLay Xh reply chk out1 w Lc' F' c4 rE c5 res cL got c6 lin c7 real cEnd := by
  obtain ⟨cEnd, R⟩ := runOn_at h
  have hrun := R.run
  unfold Proof.firstBlock at hrun
  obtain ⟨res, cL, h1, g1⟩ := bindY hrun
  obtain ⟨got, cG, h2, g2⟩ := bindY g1
  obtain ⟨t2, e2⟩ := (Blk.yields_get _ _ _ _).1 h2
  obtain ⟨_, c6, h3, g3⟩ := bindY g2
  obtain ⟨_, cM, h4, g4⟩ := bindY g3
  obtain ⟨t4, e4⟩ := (Blk.yields_must _ _ _).1 h4
  obtain ⟨lin, c7, h5, g5⟩ := bindY g4
  rw [e2] at h3
  rw [e4] at h5
  obtain ⟨ck0, c0, ck, o1, c1, chk, c2, out1, c3, w, Lc', F', c4, rE, c5, H, q1, q2, q3⟩ :=
    head_whole_of_links h1
  exact ⟨cEnd, res, cL, ck0, c0, ck, o1, c1, chk, c2, out1, c3, w, Lc', F', c4, rE, c5, got, c6,
    lin, c7, R, h1, H, ⟨q1, q2, q3, t2, h3, t4, h5, g5⟩⟩

end OnBytes.TieK
