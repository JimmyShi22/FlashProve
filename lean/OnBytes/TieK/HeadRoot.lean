-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/TieK/HeadRoot.lean: from what the exit code 0 says of the proof file to the run of the
output head's routine and on to the first chain's end, tied to the files at every step.

"The program" is the Lean program verify-on-bytes. A statement of the form "if the proof file is
accepted, the head's routine was run" says little as long as the context of that run stands under
"there is": one accepted file would make it true of every other. Here the road from the files to
that run is whole, as one record of facts, Root, on one record of values, RootData:
 1. the plan p, the request's words so, the covered positions cov, the statement's item and the
    links made for the request are what the program's functions make of the files
    (OnBytes/TieK/PortCommon.lean);
 2. the list of links that the program runs is Xs and then Xh; Xh is of kind 2, its routine is the
    head's for cov, its planned state and list of arrays are the head's plan's
    (links_end, OnBytes/TieK/LinksEnd.lean);
 3. the proof file's three chains were read by the strict reader under descriptions that are named,
    no byte is left over, and the three blocks have said yes on the three views
    (ThreeChains, OnBytes/TieK/Chains.lean);
 4. the first chain's block has run from the context D.start, a term of the first chain's view, and
    from there, call by call, to the head's routine (HeadAt, OnBytes/TieK/HeadAt.lean) and from the
    routine's end to the block's own end (AfterHead, OnBytes/TieK/HeadAfter.lean).
p, so, cov, item, links stand with an equation that makes each from the files. The readings and the
states stand each with the run or the reading that gives it from the one before; readers and blocks
are functions. head_root puts the one record of values under "there is".

OF ALL THAT THE EXIT CODE 0 SAYS OF THE BYTES (K.PortYesAt) THIS FILE KEEPS THE CLAUSE ON THE PROOF
FILE ALONE. The yes on the key file and on the entry file, the commitment's ID and the tie between
the chains are dropped. The table "further", against which the proof file is checked, is a letter
here; the premise says where it comes from.

What is not here. That the states are those of a run on a view, that they bear no mark of a failed
named test, that the reply received is the caller's: each of these hangs on what other calls of the
program's text do not do. What any routine does. The link's number is written 0 + Xs.length, as the
split of the list gives it.

Main definitions: Made, RootData, Root. Main theorems: AfterHead.reply_is, head_root.
It claims nothing on soundness. The program does not import this file.
-/
import OnBytes.TieK.PortCommon
import OnBytes.TieK.Chains
import OnBytes.TieK.HeadAfter
import OnBytes.TieK.LinksEnd

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.TieK

/-- What the program's functions make of the files, before the proof file is opened. -/
structure Made (F : K.Files) (p : Model.Verify.Planned) (so : Model.Head.StOwn)
    (cov : Model.Head.Covered) (item : ByteArray) (links : Array Model.Stages.LinkH)
    (Xs : List Model.Stages.LinkH) (Xh : Model.Stages.LinkH) : Prop where
  plan : Model.Verify.planned F.pol F.KL (some F.lay) = .ok p
  own : Model.Head.stFromCall (Model.Verify.words32 F.request) (Model.Verify.words32 F.y) p.X.T =
    .ok so
  covered : Model.Head.coveredOf so p.X.T p.X.P.h.V = .ok cov
  item_made : Proof.requestItem F.pol F.KL F.request = some item
  links_made : Model.Verify.linksOf p.X cov = .ok links
  built : Model.Verify.builtOf p.X p.chains = .ok p.built
  /-- the list that the program runs -/
  list : p.built.links.zipWith (fun b l => { b with run := l.run }) links = (Xs ++ [Xh]).toArray
  kind : Xh.kind = 2
  routine : Xh.run = (Model.Verify.headPlanOf p.X cov).run
  state : Xh.Fp = p.X.H.Fp
  arrays : Xh.Tp = p.X.H.Tp

/-- At a link of kind 2 the reply that the links' block returns is the first plain scalar of the
chain's state from which the link's routine was called. -/
theorem AfterHead.reply_is {p : Params.First} {wsLay : Model.WsLay} {Xh : Model.Stages.LinkH}
    {reply : E} {chk : Model.ChainCheck} {out1 : Proof.LinksResult} {w : Option Model.WsForkOut}
    {Lc' : Model.LinkCtx} {F' : Model.Fork} {c4 : Ctx}
    {rE : Model.ChainCheck × Proof.LinksResult} {c5 : Ctx} {res : Proof.LinksResult} {cL : Ctx}
    {got : E} {c6 : Ctx} {lin : LinFirst} {c7 : Ctx} {real : Proof.FirstEnd} {cEnd : Ctx}
    (A : AfterHead p wsLay Xh reply chk out1 w Lc' F' c4 rE c5 res cL got c6 lin c7 real cEnd)
    (hk : Xh.kind = 2) : res.reply = chk.plain[0]? := by
  have ek : (Xh.kind == 2) = true := by rw [hk]; rfl
  have e0 : (outOf Xh chk out1).reply = chk.plain[0]? := by
    unfold outOf
    rw [if_pos ek]
  rw [A.result]
  rcases A.link_closed.row with ⟨_, o', row, _, _, e⟩ | ⟨_, _, e⟩
  · rw [e]
    exact e0
  · rw [e]
    exact e0

/-- **The values on the road**, in its order. -/
structure RootData where
  /-- all that follows from the three public files -/
  p : Model.Verify.Planned
  /-- the request's and the reply's words as read -/
  so : Model.Head.StOwn
  /-- the request's tokens and covered positions -/
  cov : Model.Head.Covered
  /-- the statement's item "request" -/
  item : ByteArray
  /-- the links made for the request -/
  links : Array Model.Stages.LinkH
  /-- the links that the program runs before the last -/
  Xs : List Model.Stages.LinkH
  /-- the last link that it runs: the head's -/
  Xh : Model.Stages.LinkH
  /-- the place of the first chain's first byte -/
  i : Nat
  /-- the first chain's rounds and end by the dry run of its block; its description -/
  rounds1 : Params.Rounds
  dry : Proof.FirstEnd
  S1 : Fmt.SpecX
  /-- the proof file as read -/
  r : Proof.TailRead
  /-- the seals of the first and of the shared chain -/
  seal1 : ByteArray
  seal2 : ByteArray
  /-- the shared chain's rounds and end by the dry run; its description -/
  rounds2 : Params.Rounds
  dry2 : Proof.SharedEnd
  S2 : Fmt.SpecX
  /-- the second chain's rounds and description -/
  rounds3 : Params.Rounds
  S3 : Fmt.SpecX
  /-- what the first and the shared chain's blocks have returned on their views -/
  real : Proof.FirstEnd
  real2 : Proof.SharedEnd
  /-- after the start of the calls over the links: the chain's state, the context -/
  ck0 : Model.ChainCheck
  c0 : Ctx
  /-- after all links before the last: the chain's state, the result so far, the context -/
  ck : Model.ChainCheck
  o1 : Proof.LinksResult
  c1 : Ctx
  /-- after the last link's first call: the chain's state, the context -/
  chk : Model.ChainCheck
  c2 : Ctx
  /-- where the head's routine is called: the result so far, THE CONTEXT FROM WHICH IT RUNS -/
  out1 : Proof.LinksResult
  c3 : Ctx
  /-- what the head's routine has returned and left: value, link's state, state, context -/
  w : Option Model.WsForkOut
  Lc1 : Model.LinkCtx
  F1 : Model.Fork
  c4 : Ctx
  /-- what runLinkH has returned and left at the last link -/
  rE : Model.ChainCheck × Proof.LinksResult
  c5 : Ctx
  /-- what the links' block has returned and left -/
  res : Proof.LinksResult
  cL : Ctx
  /-- the reply as received; the context after the named test on it -/
  got : E
  c6 : Ctx
  /-- what the first part of the test on the table has returned and left -/
  lin : LinFirst
  c7 : Ctx
  /-- the context at the block's end, on which the verdict rests -/
  cEnd : Ctx

namespace RootData

/-- The parameter bytes of the proof's first chain, read. -/
@[reducible] def first (D : RootData) : Params.First := D.p.chains.proof.first

/-- The layout of the weight table. -/
@[reducible] def wsLay (D : RootData) : Model.WsLay := D.p.X.layers.wsLay

/-- The links' block that the program runs. -/
@[reducible] def linksBlock (D : RootData) : Blk Proof.LinksResult :=
  Model.Stages.runLinksH (D.Xs ++ [D.Xh]).toArray D.first D.wsLay

/-- The first chain's block that the program runs. -/
@[reducible] def block (D : RootData) : Blk Proof.FirstEnd :=
  Proof.firstBlock D.first D.linksBlock (Model.ofNat D.so.y)

/-- THE CONTEXT FROM WHICH THAT BLOCK RUNS: a term of the first chain's view. -/
@[reducible] def start (D : RootData) : Ctx := startCtx (Proof.firstStart D.first) D.r.first.view

/-- The link's state from which the head's routine runs, with the head's plan's list of arrays. -/
@[reducible] def linkState (D : RootData) : Model.LinkCtx :=
  { check := D.chk, link := 0 + D.Xs.length, arrayOf := D.Xh.arrayOf, list := D.p.X.H.Tp }

end RootData

/-- **The root of the head's walk.** -/
structure Root (F : K.Files) (further : Params.TableName) (D : RootData) : Prop where
  made : Made F D.p D.so D.cov D.item D.links D.Xs D.Xh
  head_read : Proof.readProofHead D.first.given.plan.field F.proof = .ok (F.entry, D.i)
  params_ok : (D.first.given.plan.field != .two || D.first.given.cfg == Fmt.zero32) = false
  first_spec : D.first.describe further F.entry D.item F.request D.rounds1 = some D.S1
  chains : ThreeChains (Proof.tailPublic D.p.chains.proof further) D.block
    (Proof.firstStart D.first) F.proof D.i D.rounds1 D.dry D.S1 D.r D.seal1 D.seal2 D.rounds2 D.dry2
    D.S2 D.rounds3 D.S3 D.real D.real2
  ran : RanAt D.block (Proof.firstStart D.first) D.r.first.view D.real D.cEnd
  links_ran : D.linksBlock.Yields D.start D.res D.cL
  head_at : HeadAt D.first D.wsLay D.Xs D.Xh D.start D.ck0 D.c0 D.ck D.o1 D.c1 D.chk D.c2 D.out1
    D.c3 D.w D.Lc1 D.F1 D.c4
  after : AfterHead D.first D.wsLay D.Xh (Model.ofNat D.so.y) D.chk D.out1 D.w D.Lc1 D.F1 D.c4 D.rE
    D.c5 D.res D.cL D.got D.c6 D.lin D.c7 D.real D.cEnd

/-- The reply that the links' block returns is the first plain scalar of the chain's state from
which the head's routine was called. -/
theorem Root.reply_is {F : K.Files} {further : Params.TableName} {D : RootData}
    (R : Root F further D) : D.res.reply = D.chk.plain[0]? :=
  R.after.reply_is R.made.kind

/-- That state has one plain scalar. -/
theorem Root.one_plain {F : K.Files} {further : Params.TableName} {D : RootData}
    (R : Root F further D) : D.chk.plain.size = 1 := by
  have ek : (D.Xh.kind == 2) = true := by rw [R.made.kind]; rfl
  have t := R.head_at.opened.plain
  rw [if_pos ek] at t
  exact t

/-- **From what the exit code 0 says of the bytes.** -/
theorem head_root {F : K.Files} {id : String} {table further : Params.TableName}
    (h : K.PortYesAt F id table further) : ∃ D, Root F further D := by
  obtain ⟨p, so, cov, item, links, hp, h1, h2, h3, h4, hc, hb⟩ := port_common h
  obtain ⟨Xs, Xh, e, hk, hrun, hFp, hTp⟩ := links_end hb h4
  rw [e] at hc
  obtain ⟨i, rounds1, dry, S1, r, seal1, seal2, rounds2, dry2, S2, rounds3, S3, real, real2, g1, g0,
    g2, T⟩ := proof_check_chains _ _ _ _ _ _ _ _ hc
  obtain ⟨cEnd, res, cL, ck0, c0, ck, o1, c1, chk, c2, out1, c3, w, Lc', F', c4, rE, c5, got, c6,
    lin, c7, R, hL, H, A⟩ := head_whole_of_first_yes T.first_yes
  exact ⟨⟨p, so, cov, item, links, Xs, Xh, i, rounds1, dry, S1, r, seal1, seal2, rounds2, dry2, S2,
    rounds3, S3, real, real2, ck0, c0, ck, o1, c1, chk, c2, out1, c3, w, Lc', F', c4, rE, c5, res,
    cL, got, c6, lin, c7, cEnd⟩,
    ⟨⟨hp, h1, h2, h3, h4, hb, e, hk, hrun, hFp, hTp⟩, g1, g0, g2, T, R, hL, H, A⟩⟩

end OnBytes.TieK
