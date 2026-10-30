-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P1K2R/SharesE.lean (over
MoreLeft.lean and SitsLeft.lean): code switching (K2): ITS THREE SHARES OF e₁ («the
half of the table of joints' promise that reads the verifier's state is handed on») AT E :=
EQ Mg linksW placesW z («in order» and the promise's public test at the public part z),
WITH THE FIELD «more» BROUGHT DOWN TO THE MAKINGS. NO BLOCK IMPORTS THIS FILE.
  left_first · left_bare_hear   every accept of the sub-protocol at a link's first place (the
                                switch joined with the frame's «opened») | of the lot's own
                                sub-protocol at «H:2» gives Left (left_of_keepsJoined |
                                left_headOpen, called)
  share_firstE   HandsR Fk N linksW placesW (EQ …) ft (14 * l + 2) b, 1 ≤ l < 24 : share_firstR's
                 premises BUT «more»; in its place hMade: at every accept from a fenced, unmarked
                 state with X in front, to an unmarked state: the test of each item of madeAt l 2
                 ‹attention?› holds behind
  share_hearE    the same at 339, with hMade at madeAt 24 3 false and htok: «tokenSmall» rides
  (share_backE: MoreLeft.lean: at 353 nothing is made)
COMMON TO THE THREE: Mg.pub = pubAll D₀ base · Mg.more = moreAll (at the composed meaning: by
unfolding) · hIn: «in order» reads the public part alone.
LIMITS. The debts on the numbers, «the head's group is fresh», the makings and «tokenSmall» stay
premises, each asked at fenced states alone. No soundness is claimed.
-/
import Johnson.P1K2R.MoreLeft
import Johnson.P1K2R.SitsLeft

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace P1K2
open VerifiableInference.Desc (Block Place OpenedColumn KindName)
open VerifiableInference.Desc.First (S ModelPart Numbers Pub Meaning PubData pubAll)
open VerifiableInference.Desc.First.K2 (P2 codeSwitchKind headOpenQ LinkDebts SwitchDebts HeadFresh frontAt
  frameAt)
open VerifiableInference.Desc.First.K2Ties (Left left_headOpen)
open VerifiableInference.Desc.Sound (moreAll)
open H2K.JointK (Sits)
open ProofFile (Cl)
open IM (HandsR XK Yes linksW placesW subW k2P Joined)
open _root_.Tw.K2 (firstFront switchNotices)

theorem left_first {Z : ProofFile.Pub} {G₀ : ProofFile.Ground} {l : Nat} (h1 : 1 ≤ l) {b b' : Block S Cl}
    (hlot : ∃ L ∈ ProofFile.onlineFirstChainBlockTables Z, b' ∈ L.blocks G₀)
    (hpl : b'.place = { chain := 1, link := some l, piece := 1, kind := .K2 })
    (hJ : Joined Z l b b' { chain := 1, link := some l, piece := 1, kind := .K2 }) {ft : Nat}
    {s s' : S} (hy : Yes ft b s s') : Left s s' := by
  obtain ⟨L, hL, hb'⟩ := hlot
  obtain ⟨x, hx, rfl⟩ := IM.lot_K2 hL hb' (by rw [hpl])
  have hi := IM.k2_mem hx
  rw [show x.place = _ from hpl] at hi
  rcases hi with ⟨_, hm⟩ | hd
  · obtain ⟨rs, cols, n, e⟩ := hy
    obtain ⟨fs, f, m, _, _, e3, _⟩ := hJ.step e
    exact absurd ⟨rs, cols, n, e3⟩ (never_of_mute hm s m)
  · obtain ⟨fs, f, hfs, hf, hSJ⟩ := sits_of_joined hJ (fun e => by cases e) rfl hd
    obtain ⟨p, enter, leave, hS, hD⟩ :=
      left_of_keepsJoined hfs hf (by omega) (sitsJoined_keeps hfs hf hSJ)
    exact left_of_sits hS hD.1 hD.2 hy

theorem left_bare_hear {Z : ProofFile.Pub} {G₀ : ProofFile.Ground} {b' : Block S Cl}
    (hlot : ∃ L ∈ ProofFile.onlineFirstChainBlockTables Z, b' ∈ L.blocks G₀)
    (hpl : b'.place = { chain := 1, link := some 24, piece := 2, kind := .K2 }) {ft : Nat}
    {s s' : S} (hy : Yes ft b' s s') : Left s s' := by
  obtain ⟨L, hL, hb'⟩ := hlot
  obtain ⟨x, hx, rfl⟩ := IM.lot_K2 hL hb' (by rw [hpl])
  have hi := IM.k2_mem hx
  rw [show x.place = _ from hpl] at hi
  rcases hi with ⟨_, hm⟩ | ⟨P, n, hP, hn, hA⟩
  · exact absurd hy (never_of_mute hm s s')
  · rcases hA with ⟨h0, _⟩ | ⟨l, HP, hl, hHP, hx'⟩ | ⟨l, _, hx'⟩
    · cases h0
    · have hS := sits_under_head x.name
        { chain := 1, link := some 24, piece := 2, kind := .K2 }
        (k2P Z { chain := 1, link := some 24, piece := 2, kind := .K2 } x.name .head n) HP
      rw [← hx'] at hS
      exact left_of_sits hS (fun _ _ e => left_id e) (fun _ _ _ e => left_headOpen e) hy
    · have hS := sits_under_link x.name
        { chain := 1, link := some 24, piece := 2, kind := .K2 }
        (k2P Z { chain := 1, link := some 24, piece := 2, kind := .K2 } x.name .link n)
      rw [← hx'] at hS
      exact left_of_sits hS (fun _ _ e => left_id e) (fun _ _ _ e => left_id e) hy

variable {P W : Type}

theorem share_firstE {Fk : Nat → S → Prop} {Z : ProofFile.Pub} {G₀ : ProofFile.Ground} {l : Nat}
    (h1 : 1 ≤ l) (h24 : l < 24)
    {b b' : Block S Cl} (hlot : ∃ L ∈ ProofFile.onlineFirstChainBlockTables Z, b' ∈ L.blocks G₀)
    (hpl : b'.place = { chain := 1, link := some l, piece := 1, kind := .K2 })
    (hJ : Joined Z l b b' { chain := 1, link := some l, piece := 1, kind := .K2 })
    {X : OnBytes.Model.Stages.LinkH} (hX : Z.p.built.links[l]? = some X) (hk : X.kind ≠ 2)
    (hsort : (X.kind = 0 → subW l = .layers) ∧ (X.kind = 1 → subW l = .attention))
    {N : Numbers} {Mg : Meaning P W} {z : P} {ft : Nat} (D₀ : PubData)
    (base : Pub → P × S → Bool) (hpub : Mg.pub = pubAll D₀ base) (hmore : Mg.more = moreAll)
    (hIn : ∀ s s' : S, Mg.inOrder (z, s) = true → Mg.inOrder (z, s') = true)
    (hgrp : ∀ P n, prepOf Z G₀ = some P → numsAt P (some l) = some n → N.groupAt l = n.grp)
    (D : ∀ P n (s : S) x W lay, prepOf Z G₀ = some P → numsAt P (some l) = some n →
      Fk (14 * l + 2) s → XK N linksW placesW (EQ Mg linksW placesW z) (14 * l + 2) s = true →
      firstFront s.st s.check.frame = .ok x → frameAt x = some W →
      OnBytes.layTrees x.st.codes (switchNotices x.T x.others) = some lay →
      LinkDebts N l placesW[14 * l + 2]? placesW[14 * l + 3]? s n.positions x W lay)
    (hMade : ∀ s s', Fk (14 * l + 2) s → Yes ft b s s' → s.failed = none → s'.failed = none →
      XK N linksW placesW (EQ Mg linksW placesW z) (14 * l + 2) s = true →
      ∀ q ∈ madeAt l 2 (decide (subW l = .attention)), Mg.pub q (z, s') = true) :
    HandsR Fk N linksW placesW (EQ Mg linksW placesW z) ft (14 * l + 2) b :=
  share_firstR h1 h24 hlot hpl hJ hX hk hsort hgrp D fun s s' hf hy h0 h1' hx =>
    more_link_left h1 h24 D₀ base hpub hmore hx (hIn s s') (left_first h1 hlot hpl hJ hy)
      (hMade s s' hf hy h0 h1' hx)

theorem share_hearE {Fk : Nat → S → Prop} {Z : ProofFile.Pub} {G₀ : ProofFile.Ground} {b' : Block S Cl}
    (hlot : ∃ L ∈ ProofFile.onlineFirstChainBlockTables Z, b' ∈ L.blocks G₀)
    (hpl : b'.place = { chain := 1, link := some 24, piece := 2, kind := .K2 })
    (hl24 : ∀ HP, pureLetters G₀ 24 = some HP → HP.l = 24)
    {N : Numbers} {Mg : Meaning P W} {z : P} {ft : Nat} (D₀ : PubData)
    (base : Pub → P × S → Bool) (hpub : Mg.pub = pubAll D₀ base) (hmore : Mg.more = moreAll)
    (hIn : ∀ s s' : S, Mg.inOrder (z, s) = true → Mg.inOrder (z, s') = true)
    (hgrp : ∀ P n, prepOf Z G₀ = some P → numsAt P (some 24) = some n → N.groupAt 24 = n.grp)
    (fresh : ∀ s, Fk 339 s → XK N linksW placesW (EQ Mg linksW placesW z) 339 s = true →
      HeadFresh s)
    (D : ∀ nm P n (s : S) x W lay, prepOf Z G₀ = some P → numsAt P (some 24) = some n →
      Fk 339 s → XK N linksW placesW (EQ Mg linksW placesW z) 339 s = true →
      frontAt (k2P Z { chain := 1, link := some 24, piece := 2, kind := .K2 } nm .head n) s =
        some x → frameAt x = some W →
      OnBytes.layTrees x.st.codes (switchNotices x.T x.others) = some lay →
      SwitchDebts N 24 placesW[339]? placesW[339 + 1]? s.book.trees.size n.positions
        (1 + x.T.kept.size + x.own.length) x W lay)
    (htok : ∀ s s', Fk 339 s → Yes ft b' s s' → s.failed = none → s'.failed = none →
      Mg.pub .tokenSmall (z, s) = true → Mg.pub .tokenSmall (z, s') = true)
    (hMade : ∀ s s', Fk 339 s → Yes ft b' s s' → s.failed = none → s'.failed = none →
      XK N linksW placesW (EQ Mg linksW placesW z) 339 s = true →
      ∀ q ∈ madeAt 24 3 false, Mg.pub q (z, s') = true) :
    HandsR Fk N linksW placesW (EQ Mg linksW placesW z) ft 339 b' :=
  share_hearR hlot hpl hl24 hgrp fresh D fun s s' hf hy h0 h1' hx =>
    more_head_left D₀ base hpub hmore hx (hIn s s') (left_bare_hear hlot hpl hy)
      (htok s s' hf hy h0 h1') (hMade s s' hf hy h0 h1' hx)

end P1K2

#print axioms P1K2.left_first
#print axioms P1K2.left_bare_hear
#print axioms P1K2.share_firstE
#print axioms P1K2.share_hearE
