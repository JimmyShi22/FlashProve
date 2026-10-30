-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TieK/HeadAt.lean: from the yes of a proof's first chain's block to the run of the last
link's routine, with every state on the way named and tied to the one before it.

"The program" is the Lean program verify-on-bytes. On a proof's first chain it runs the block
Proof.firstBlock, whose first part is the links' block Model.Stages.runLinksH: the start of the
calls over the request's links; the links one after the other (runLinksFrom, runLinkH); the call
after the last link. A link begins with the chain's first call for it, public tests, and then the
link's own routine. The output head's link is the last.

This file takes that text apart as far as the last link's routine. Nothing is asked of any routine.
 - runLinksFrom_split: a run of the links Xs and then Xh is a run of the program's own runLinksFrom
   on Xs, followed by a run of runLinkH on Xh from what that has left.
 - LinkOpened, runLinkH_open: what runLinkH has done before it calls the link's routine, the call of
   the routine itself, the two public tests behind it, and the reply that is returned.
 - HeadAt, head_at_of_links: the same for the whole links' block.
 - head_at_of_first_yes: the same from the block's yes on a view: THE FIRST CONTEXT IS THE TERM
   startCtx (firstStart p) v (OnBytes/TieK/RunAt.lean).
HeadAt is a record whose states are all letters. Each clause is a run of one call of the program's
own text from one of these states to the next. The theorems put the letters under "there are"; a
block is a function, so from the first context on each is the one state that the text gives.

What is not here. That the reply which the last link returns is the caller's: the one test that
compares them is a named test, which leaves a mark and does not stop the block; the equation needs
that no later call wipes the mark. What the routine does. That the list of links which the program
runs on a request ends in the head's link.

It claims nothing on soundness. The program does not import this file.
-/
import OnBytes.TieK.RunAt
import OnBytes.Model.StagesLinks
import OnBytes.Proof.File

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.TieK

/-! ## Tools -/

/-- One block after another. -/
theorem bindY {α β : Type} {b1 : Blk α} {b2 : α → Blk β} {c c2 : Ctx} {y : β}
    (h : (b1 >>= b2).Yields c y c2) : ∃ x c1, b1.Yields c x c1 ∧ (b2 x).Yields c1 y c2 :=
  (Blk.yields_bind b1 b2 c c2 y).1 h

/-- Either of two beginnings, chosen by a condition, and one continuation. -/
theorem iteY {α β γ : Type} {p : Prop} [Decidable p] {x : Blk γ} {g : γ → Blk α} {x' : Blk α}
    {jp : α → Blk β} {c c2 : Ctx} {y : β}
    (h : (if p then x >>= fun a => g a >>= jp else x' >>= jp).Yields c y c2) :
    ∃ b c1, ((p ∧ ∃ a c0, x.Yields c a c0 ∧ (g a).Yields c0 b c1) ∨ (¬ p ∧ x'.Yields c b c1)) ∧
      (jp b).Yields c1 y c2 := by
  by_cases hp : p
  · rw [if_pos hp] at h
    obtain ⟨a, c0, h1, h2⟩ := bindY h
    obtain ⟨b, c1, h3, h4⟩ := bindY h2
    exact ⟨b, c1, Or.inl ⟨hp, a, c0, h1, h3⟩, h4⟩
  · rw [if_neg hp] at h
    obtain ⟨b, c1, h1, h2⟩ := bindY h
    exact ⟨b, c1, Or.inr ⟨hp, h1⟩, h2⟩

/-- Naming the place of a failure changes no run that succeeds. -/
theorem inPlaceY {α : Type} (s : String) (b : Blk α) (c : Ctx) (x : α) (c' : Ctx) :
    (Blk.inPlace s b).Yields c x c' ↔ b.Yields c x c' := by
  rw [Blk.yields_iff, Blk.yields_iff]
  have e : Blk.inPlace s b c = match b c with
      | .error e => .error (if e.place.isEmpty then { e with place := s } else e)
      | .ok x => .ok x := rfl
  rw [e]
  cases b c with
  | error e => simp
  | ok y => exact Iff.rfl

/-- A public condition under a name succeeds exactly if it holds, and leaves the context. -/
theorem mustAsY (n : String) (b : Bool) (c c' : Ctx) (u : Unit) :
    (Model.mustAs n b).Yields c u c' ↔ b = true ∧ c' = c := by
  rw [Blk.yields_iff]
  cases b
  · have e : Model.mustAs n false c = .error { name := n } := rfl
    rw [e]
    simp
  · have e : Model.mustAs n true c = .ok ((), c) := rfl
    rw [e]
    constructor
    · intro h
      cases h
      exact ⟨rfl, rfl⟩
    · rintro ⟨-, rfl⟩
      rfl

/-! ## The links before the last -/

/-- **The links Xs and then Xh**: the program's own runLinksFrom on Xs, then runLinkH on Xh. -/
theorem runLinksFrom_split {links : Array Model.Stages.LinkH} {p : Params.First}
    {wsLay : Model.WsLay} :
    ∀ (Xs : List Model.Stages.LinkH) (Xh : Model.Stages.LinkH) (l : Nat)
    (check : Model.ChainCheck) (out : Proof.LinksResult) (c c' : Ctx)
    (r : Model.ChainCheck × Proof.LinksResult),
    (Model.Stages.runLinksFrom links p wsLay (Xs ++ [Xh]) l check out).Yields c r c' →
    ∃ ck o1 c1,
      (Model.Stages.runLinksFrom links p wsLay Xs l check out).Yields c (ck, o1) c1 ∧
      (Model.Stages.runLinkH links p wsLay (l + Xs.length) Xh ck o1).Yields c1 r c'
  | [], Xh, l, check, out, c, c', r, h => by
    rw [List.nil_append, Model.Stages.runLinksFrom] at h
    obtain ⟨⟨ck, o1⟩, c1, h1, h2⟩ := bindY h
    obtain ⟨e, ec⟩ := (Blk.yields_pure (ck, o1) r c1 c').1 h2
    refine ⟨check, out, c, ?_, ?_⟩
    · rw [Model.Stages.runLinksFrom]
      exact (Blk.yields_pure _ _ _ _).2 ⟨rfl, rfl⟩
    · rw [e, ec]
      exact h1
  | X :: Xs, Xh, l, check, out, c, c', r, h => by
    rw [List.cons_append, Model.Stages.runLinksFrom] at h
    obtain ⟨⟨ck, o1⟩, c1, h1, h2⟩ := bindY h
    obtain ⟨ck', o', c2, k1, k2⟩ := runLinksFrom_split Xs Xh (l + 1) ck o1 c1 c' r h2
    have el : l + 1 + Xs.length = l + (X :: Xs).length := by
      rw [List.length_cons]
      omega
    rw [el] at k2
    refine ⟨ck', o', c2, ?_, k2⟩
    rw [Model.Stages.runLinksFrom]
    exact (Blk.yields_bind _ _ _ _ _).2 ⟨(ck, o1), c1, h1, k1⟩

/-! ## One link, up to its routine -/

/-- What runLinkH has done before it calls the routine of the link X, number l. check, out, c: what
it was given. chk, c0: the chain's state and the context after the link's first call. out1, c1: the
result so far and the context from which the routine is called. -/
structure LinkOpened (links : Array Model.Stages.LinkH) (p : Params.First) (l : Nat)
    (X : Model.Stages.LinkH) (check : Model.ChainCheck) (out : Proof.LinksResult) (c : Ctx)
    (chk : Model.ChainCheck) (c0 : Ctx) (out1 : Proof.LinksResult) (c1 : Ctx) : Prop where
  /-- the chain's first call for the link -/
  first : check.first.Yields c chk c0
  /-- at the first link, the test on the index-mask message; at another link nothing -/
  masks : ((l == 0) = true ∧ ∃ im, (Model.Stages.indexMasksH links p chk).Yields c0 im c1 ∧
      out1 = { out with indexMasks := im }) ∨ (¬ (l == 0) = true ∧ out1 = out ∧ c1 = c0)
  /-- one plain scalar at the head's link, none at another -/
  plain : chk.plain.size = (if X.kind == 2 then 1 else 0)
  /-- the chain's walk is at this link -/
  at_link : chk.link = l

/-- **One link.** -/
theorem runLinkH_open {links : Array Model.Stages.LinkH} {p : Params.First} {wsLay : Model.WsLay}
    {l : Nat} {X : Model.Stages.LinkH} {check : Model.ChainCheck} {out : Proof.LinksResult}
    {c c' : Ctx} {r : Model.ChainCheck × Proof.LinksResult}
    (h : (Model.Stages.runLinkH links p wsLay l X check out).Yields c r c') :
    ∃ chk c0 out1 c1 o Lc' F' c2,
      LinkOpened links p l X check out c chk c0 out1 c1 ∧
      (StateT.run (StateT.run X.run
        { check := chk, link := l, arrayOf := X.arrayOf, list := X.Tp }) X.Fp).Yields c1
        ((o, Lc'), F') c2 ∧
      (Lc'.handed && Lc'.done) = true ∧ Model.Stages.samePlan X F' Lc'.list = true ∧
      r.2.reply = (if (X.kind == 2) = true then chk.plain[0]? else out.reply) := by
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
  have hmasks : ((l == 0) = true ∧ ∃ im, (Model.Stages.indexMasksH links p chk).Yields c0 im ca ∧
      out1 = { out with indexMasks := im }) ∨ (¬ (l == 0) = true ∧ out1 = out ∧ ca = c0) := by
    rcases hm with ⟨hp, im, cm, k1, k2⟩ | ⟨hp, k1⟩
    · obtain ⟨q1, q2⟩ := (Blk.yields_pure _ _ _ _).1 k2
      rw [q2]
      exact Or.inl ⟨hp, im, k1, q1⟩
    · obtain ⟨q1, q2⟩ := (Blk.yields_pure _ _ _ _).1 k1
      exact Or.inr ⟨hp, q1, q2⟩
  have ho : out1.reply = out.reply := by
    rcases hmasks with ⟨_, im, _, q⟩ | ⟨_, q, _⟩
    · rw [q]
    · rw [q]
  have hout : (if (X.kind == 2) = true then
      ({ out1 with reply := chk.plain[0]? } : Proof.LinksResult) else out1).reply =
      (if (X.kind == 2) = true then chk.plain[0]? else out.reply) := by
    by_cases hk : (X.kind == 2) = true
    · rw [if_pos hk, if_pos hk]
    · rw [if_neg hk, if_neg hk]
      exact ho
  have hrep : r.2.reply = (if (X.kind == 2) = true then chk.plain[0]? else out.reply) := by
    by_cases hf : X.fv = true
    · rw [if_pos hf] at g7
      cases o with
      | none =>
        have k := (Blk.yields_iff _ _ _ _).1 g7
        cases k
      | some o' =>
        obtain ⟨row, cb, hr, g8⟩ := bindY g7
        obtain ⟨k1, _⟩ := (Blk.yields_pure _ _ _ _).1 g8
        rw [k1]
        exact hout
    · rw [if_neg hf] at g7
      obtain ⟨k1, _⟩ := (Blk.yields_pure _ _ _ _).1 g7
      rw [k1]
      exact hout
  exact ⟨chk, c0, out1, ca, o, Lc', F', ca3, ⟨h0, hmasks, eq_of_beq t1, eq_of_beq t2⟩, m3', t4, t5,
    hrep⟩

/-! ## The whole links' block -/

/-- What the links' block has done, from the context c, up to the end of the last link's routine.
Every state is a letter; each clause goes from one to the next. -/
structure HeadAt (p : Params.First) (wsLay : Model.WsLay) (Xs : List Model.Stages.LinkH)
    (Xh : Model.Stages.LinkH) (c : Ctx) (ck0 : Model.ChainCheck) (c0 : Ctx)
    (ck : Model.ChainCheck) (o1 : Proof.LinksResult) (c1 : Ctx) (chk : Model.ChainCheck) (c2 : Ctx)
    (out1 : Proof.LinksResult) (c3 : Ctx) (w : Option Model.WsForkOut) (Lc' : Model.LinkCtx)
    (F' : Model.Fork) (c4 : Ctx) : Prop where
  /-- the start of the calls over the request's links -/
  start : (Model.ChainCheck.start p.shape p.layout).Yields c ck0 c0
  /-- all links before the last, by the program's own function -/
  before :
    (Model.Stages.runLinksFrom (Xs ++ [Xh]).toArray p wsLay Xs 0 ck0 {}).Yields c0 (ck, o1) c1
  /-- the last link, up to its routine -/
  opened : LinkOpened (Xs ++ [Xh]).toArray p (0 + Xs.length) Xh ck o1 c1 chk c2 out1 c3
  /-- the last link's routine -/
  run : (StateT.run (StateT.run Xh.run
    { check := chk, link := 0 + Xs.length, arrayOf := Xh.arrayOf, list := Xh.Tp }) Xh.Fp).Yields c3
    ((w, Lc'), F') c4
  /-- the routine has closed its link, under the plan from which the link's record was made -/
  closed : (Lc'.handed && Lc'.done) = true
  same_plan : Model.Stages.samePlan Xh F' Lc'.list = true

/-- **All links of a proof**, for a list of links that ends in a link of kind 2. -/
theorem head_at_of_links {Xs : List Model.Stages.LinkH} {Xh : Model.Stages.LinkH}
    {p : Params.First} {wsLay : Model.WsLay} {c c' : Ctx} {res : Proof.LinksResult}
    (h : (Model.Stages.runLinksH (Xs ++ [Xh]).toArray p wsLay).Yields c res c')
    (hk : Xh.kind = 2) :
    ∃ ck0 c0 ck o1 c1 chk c2 out1 c3 w Lc' F' c4,
      HeadAt p wsLay Xs Xh c ck0 c0 ck o1 c1 chk c2 out1 c3 w Lc' F' c4 ∧
      res.reply = chk.plain[0]? ∧ chk.plain.size = 1 := by
  unfold Model.Stages.runLinksH at h
  obtain ⟨ck0, c0, h0, g1⟩ := bindY h
  obtain ⟨⟨ckE, oE⟩, cE, h1, g2⟩ := bindY g1
  obtain ⟨_, cF, _, g3⟩ := bindY g2
  obtain ⟨e, _⟩ := (Blk.yields_pure _ _ _ _).1 g3
  obtain ⟨ck, o1, c1, k1, k2⟩ := runLinksFrom_split Xs Xh 0 ck0 {} c0 cE (ckE, oE) h1
  obtain ⟨chk, c2, out1, c3, w, Lc', F', c4, q1, q2, q3, q4, q5⟩ := runLinkH_open k2
  have ek : (Xh.kind == 2) = true := by rw [hk]; rfl
  rw [if_pos ek] at q5
  have hs : chk.plain.size = 1 := by
    have t := q1.plain
    rw [if_pos ek] at t
    exact t
  exact ⟨ck0, c0, ck, o1, c1, chk, c2, out1, c3, w, Lc', F', c4, ⟨h0, k1, q1, q2, q3, q4⟩,
    by rw [e]; exact q5, hs⟩

/-- **From the yes of a proof's first chain's block on a view.** The block has run from the context
startCtx (firstStart p) v and has used up plan and view; its first part, the links' block, has run
from that same context; and so on to the last link's routine. -/
theorem head_at_of_first_yes {Xs : List Model.Stages.LinkH} {Xh : Model.Stages.LinkH}
    {p : Params.First} {wsLay : Model.WsLay} {reply : E} {v : Fmt.View} {real : Proof.FirstEnd}
    (h : (Proof.firstBlock p (Model.Stages.runLinksH (Xs ++ [Xh]).toArray p wsLay) reply).runOn
      (Proof.firstStart p) v = .ok real) (hk : Xh.kind = 2) :
    ∃ cEnd res cL ck0 c0 ck o1 c1 chk c2 out1 c3 w Lc' F' c4,
      RanAt (Proof.firstBlock p (Model.Stages.runLinksH (Xs ++ [Xh]).toArray p wsLay) reply)
        (Proof.firstStart p) v real cEnd ∧
      (Model.Stages.runLinksH (Xs ++ [Xh]).toArray p wsLay).Yields
        (startCtx (Proof.firstStart p) v) res cL ∧
      HeadAt p wsLay Xs Xh (startCtx (Proof.firstStart p) v) ck0 c0 ck o1 c1 chk c2 out1 c3 w Lc' F'
        c4 ∧
      res.reply = chk.plain[0]? ∧ chk.plain.size = 1 := by
  obtain ⟨cEnd, R⟩ := runOn_at h
  have hrun := R.run
  unfold Proof.firstBlock at hrun
  obtain ⟨res, cL, h1, _⟩ := bindY hrun
  obtain ⟨ck0, c0, ck, o1, c1, chk, c2, out1, c3, w, Lc', F', c4, H, q1, q2⟩ :=
    head_at_of_links h1 hk
  exact ⟨cEnd, res, cL, ck0, c0, ck, o1, c1, chk, c2, out1, c3, w, Lc', F', c4, R, h1, H, q1, q2⟩

end OnBytes.TieK
