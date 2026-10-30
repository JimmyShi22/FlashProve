-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P1K2R/MadeSentHear.lean: code switching (K2): hMade AT «H:2» (sub-protocol number 339),
EVERY ITEM JOINED: the last two ("frame.sentIs" · "ledger.treesAre" at segment 24) in hMade's own
letters, by Johnson/Top/H0/Tw/K2C/HeadSentIs.lean; then hMade and the share. The twin, at the
head, of made_sent (Johnson/Road/K4/Rec/MadeSent.lean) and of
Johnson/P1K2R/MadeFirstSent.lean. NO BLOCK IMPORTS THIS FILE.
  headFit · head_fit · head_bent   BY THE KERNEL, at the written lists: the table's first place of
                                   segment 24 with piece 2 is entry 339 of the written list of
                                   places; A NEGATIVE TEST: at entry 340 the test rejects
  HeadFence shape s   WHAT IS ASKED OF THE STATE IN FRONT BESIDE THE BOOK-KEEPING: the chain's
                      frame's groups are reqGroups of its shape · its shape is «shape» · its link
                      is 24 · the head's own part's frame has no own message yet, and its groups
                      are the chain's frame's
  made_sent_hear      the two tests accept behind every accept of the lot's own sub-protocol at
                      «H:2»
  hMade_hearW · share_hearW   hMade to the letter; K2's share of e₁ at 339
THE LOT's OTHER DRESS THERE (a link's): hands_head_other at an E of our choice, as in
MadeAtHear.lean.
THE PREMISES, SORTED BY WHAT THEY READ: CLOSED ON THE PLAN: HeadPlan · hdS (the public data's
SentData is the made datum) · hFp (the built link 24's planned ledger's arrays are the head's
letters') · AT THE FENCED STATES: HeadFence (unmarked) · hU · ON THE NUMBERS AND THE REST: the
share's hgrp · fresh · «D» · htok.
LIMITS. A GATHERING. e₁ IS NOT PAID: every premise named is still owed; none is shown at a value.
No soundness is claimed.
-/
import Johnson.P1K2R.MadeHear
import Johnson.Top.H0.Tw.K2C.HeadSentIs

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace P1K2
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Block Place OpenedColumn KindName)
open VerifiableInference.Desc.First (S ModelPart Numbers Pub PubData pubAll shift bookAt
  pubAll_more_sentIs pubAll_more_treesAre)
open VerifiableInference.Desc.First.K2 (SwitchDebts HeadFresh frontAt frameAt k2_step_two
  head_sentIs_at head_treesAre_at)
open VerifiableInference.Desc.First.FillSent (sentDataAt)
open ProofFile (Cl)
open IM (HandsR Hands XK Yes xk_parts linksW placesW k2P)
open _root_.Tw.K2 (switchNotices)

/-- A test on the written lists: the first place of segment 24 with piece 2 is entry k. -/
def headFit (k : Nat) : Bool :=
  decide ((placesW.find? fun q => q.link == some 24 &&
    q.piece == 1 + ((linksW[24]?).map shift).getD 0) = placesW[k]?) && (placesW[k]?).isSome

set_option maxRecDepth 1000000 in
theorem head_fit : headFit 339 = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem head_bent : headFit 340 = false := by decide +kernel

theorem head_at : ∃ pl, placesW[339]? = some pl ∧
    (placesW.find? fun q => q.link == some 24 &&
      q.piece == 1 + ((linksW[24]?).map shift).getD 0) = some pl := by
  have h := head_fit
  unfold headFit at h
  rw [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨pl, hp⟩ := Option.isSome_iff_exists.1 h.2
  exact ⟨pl, hp, h.1.trans hp⟩

/-- What is asked of the state in front beside the book-keeping. -/
structure HeadFence (shape : Params.ReqShape) (s : S) : Prop where
  groups : s.check.frame.groups = reqGroups s.check.frame.shape
  shape : s.check.frame.shape = shape
  link : s.check.frame.link = 24
  own : ∀ a, s.here = .head a → a.fr.own = #[] ∧ a.fr.groups = s.check.frame.groups

variable {Q : Type}

theorem made_sent_hear {Fk : Nat → S → Prop} {Z : ProofFile.Pub} {G₀ : ProofFile.Ground} {b' : Block S Cl}
    (hlot : ∃ L ∈ ProofFile.onlineFirstChainBlockTables Z, b' ∈ L.blocks G₀)
    (hpl : b'.place = { chain := 1, link := some 24, piece := 2, kind := .K2 })
    {N : Numbers} {ft : Nat} (D₀ : PubData) (base : Pub → Q × S → Bool) (z : Q)
    {E : Nat → S → Bool} {shape : Params.ReqShape}
    (hdS : D₀.dS = sentDataAt shape N linksW placesW Z.p.built.links)
    (hFp : ∀ HP, pureLetters G₀ 24 = some HP →
      ∃ X, Z.p.built.links[24]? = some X ∧ X.Fp.trees = HP.X.Fp.trees)
    (hF : ∀ s, Fk 339 s → s.failed = none → HeadFence shape s) :
    ∀ s s', Fk 339 s → Yes ft b' s s' → s.failed = none → s'.failed = none →
      XK N linksW placesW E 339 s = true →
      pubAll D₀ base (.more (some 24) "frame.sentIs") (z, s') = true ∧
        pubAll D₀ base (.more (some 24) "ledger.treesAre") (z, s') = true := by
  intro s s' hf hy hu hu' hx
  obtain ⟨L, hL, hb'⟩ := hlot
  obtain ⟨x, hx', rfl⟩ := IM.lot_K2 hL hb' (by rw [hpl])
  have hi := IM.k2_mem hx'
  rw [show x.place = _ from hpl] at hi
  rcases hi with ⟨_, hm⟩ | ⟨Pp, n, _, _, hA⟩
  · exact absurd hy (never_of_mute hm s s')
  · rcases hA with ⟨h0, _⟩ | ⟨l, HP, hl, hHP, hxe⟩ | ⟨l, _, hxe⟩
    · cases h0
    · obtain rfl : 24 = l := Option.some.inj hl
      have hS := sits_under_head x.name
        { chain := 1, link := some 24, piece := 2, kind := .K2 }
        (k2P Z { chain := 1, link := some 24, piece := 2, kind := .K2 } x.name .head n) HP
      rw [← hxe] at hS
      obtain ⟨rs, cols, k, e⟩ := hy
      obtain ⟨t, t', e1, e2, e3⟩ := hS.step ft s s' rs cols k e
      obtain rfl : s = t := Except.ok.inj e1
      obtain ⟨r₁, r₂, gs, _, hdc⟩ := k2_step_two e2
      have hl24 : HP.l = 24 := letters_l hHP
      have Fc := hF s hf hu
      obtain ⟨pl, hp, hfind⟩ := head_at
      have hbk := (xk_parts hx).2.2.2.1
      rw [hp] at hbk
      have hn : s.st.oracles.size = N.msgsAt (some pl) := by
        simp only [bookAt, Bool.and_eq_true, beq_iff_eq] at hbk
        exact hbk.2
      obtain ⟨X, hX, hXF⟩ := hFp HP hHP
      rw [pubAll_more_sentIs, pubAll_more_treesAre, hdS]
      refine ⟨?_, head_treesAre_at e3 hX hXF⟩
      have h4 := head_sentIs_at (N := N) (links := linksW) (ps := placesW)
        (built := Z.p.built.links) (pl := pl) (shape := shape) rfl hdc e3
        (by rw [hl24]; exact Fc.link) (by rw [hl24]; decide) Fc.groups Fc.own
        (by rw [hl24]; exact hfind) hn Fc.shape
      rw [hl24] at h4
      exact h4
    · have hS := sits_under_link x.name
        { chain := 1, link := some 24, piece := 2, kind := .K2 }
        (k2P Z { chain := 1, link := some 24, piece := 2, kind := .K2 } x.name .link n)
      rw [← hxe] at hS
      have H := hands_head_other rfl hS door_bare_link (N := N)
        (E := fun j t => if j = 339 + 1 then
          (pubAll D₀ base (.more (some 24) "frame.sentIs") (z, t) &&
            pubAll D₀ base (.more (some 24) "ledger.treesAre") (z, t))
          else E j t) (ft := ft)
      have hx2 := H.more s s' hy hu hu' (by
        rw [xk_same (E := E)]
        · exact hx
        · exact if_neg (by omega))
      rw [if_pos rfl, Bool.and_eq_true] at hx2
      exact hx2

theorem hMade_hearW {Fk : Nat → S → Prop} {Z : ProofFile.Pub} {G₀ : ProofFile.Ground} {b' : Block S Cl}
    (hlot : ∃ L ∈ ProofFile.onlineFirstChainBlockTables Z, b' ∈ L.blocks G₀)
    (hpl : b'.place = { chain := 1, link := some 24, piece := 2, kind := .K2 })
    (D : PubData) (base : Pub → Q × S → Bool) (z : Q) (Pl : HeadPlan G₀ D)
    {N : Numbers} {E : Nat → S → Bool} {ft : Nat}
    (hU : ∀ s, Fk 339 s → XK N linksW placesW E 339 s = true →
      ∀ a, s.here = .head a → a.tl.heard = none ∧ a.lookHeard = none)
    {shape : Params.ReqShape} (hdS : D.dS = sentDataAt shape N linksW placesW Z.p.built.links)
    (hFp : ∀ HP, pureLetters G₀ 24 = some HP →
      ∃ X, Z.p.built.links[24]? = some X ∧ X.Fp.trees = HP.X.Fp.trees)
    (hF : ∀ s, Fk 339 s → s.failed = none → HeadFence shape s) :
    ∀ s s', Fk 339 s → Yes ft b' s s' → s.failed = none → s'.failed = none →
      XK N linksW placesW E 339 s = true →
      ∀ e ∈ madeAt 24 3 false, pubAll D base e (z, s') = true :=
  hMade_hear hlot hpl D base z Pl hU (made_sent_hear hlot hpl D base z hdS hFp hF)

theorem share_hearW {Fk : Nat → S → Prop} {Z : ProofFile.Pub} {G₀ : ProofFile.Ground} {b' : Block S Cl}
    (hlot : ∃ L ∈ ProofFile.onlineFirstChainBlockTables Z, b' ∈ L.blocks G₀)
    (hpl : b'.place = { chain := 1, link := some 24, piece := 2, kind := .K2 })
    {N : Numbers} {ft : Nat} (D₀ : PubData) (base : Pub → Q × S → Bool) (z : Q)
    (Pl : HeadPlan G₀ D₀)
    (hgrp : ∀ P n, prepOf Z G₀ = some P → numsAt P (some 24) = some n → N.groupAt 24 = n.grp)
    (fresh : ∀ s, Fk 339 s → XK N linksW placesW (EP D₀ base z) 339 s = true → HeadFresh s)
    (D : ∀ nm P n (s : S) x W lay, prepOf Z G₀ = some P → numsAt P (some 24) = some n →
      Fk 339 s → XK N linksW placesW (EP D₀ base z) 339 s = true →
      frontAt (k2P Z { chain := 1, link := some 24, piece := 2, kind := .K2 } nm .head n) s =
        some x → frameAt x = some W →
      OnBytes.layTrees x.st.codes (switchNotices x.T x.others) = some lay →
      SwitchDebts N 24 placesW[339]? placesW[339 + 1]? s.book.trees.size n.positions
        (1 + x.T.kept.size + x.own.length) x W lay)
    (htok : ∀ s s', Fk 339 s → Yes ft b' s s' → s.failed = none → s'.failed = none →
      pubAll D₀ base .tokenSmall (z, s) = true → pubAll D₀ base .tokenSmall (z, s') = true)
    (hU : ∀ s, Fk 339 s → XK N linksW placesW (EP D₀ base z) 339 s = true →
      ∀ a, s.here = .head a → a.tl.heard = none ∧ a.lookHeard = none)
    {shape : Params.ReqShape} (hdS : D₀.dS = sentDataAt shape N linksW placesW Z.p.built.links)
    (hFp : ∀ HP, pureLetters G₀ 24 = some HP →
      ∃ X, Z.p.built.links[24]? = some X ∧ X.Fp.trees = HP.X.Fp.trees)
    (hF : ∀ s, Fk 339 s → s.failed = none → HeadFence shape s) :
    HandsR Fk N linksW placesW (EP D₀ base z) ft 339 b' :=
  share_hearM hlot hpl D₀ base z Pl hgrp fresh D htok hU
    (made_sent_hear hlot hpl D₀ base z hdS hFp hF)

end P1K2

#print axioms P1K2.head_fit
#print axioms P1K2.head_bent
#print axioms P1K2.made_sent_hear
#print axioms P1K2.hMade_hearW
#print axioms P1K2.share_hearW
