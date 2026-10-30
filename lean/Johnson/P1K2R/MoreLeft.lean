-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P1K2R/MoreLeft.lean (over MoreAtSwitch.lean, HandsShares.lean and
Johnson/Top/H0/K2Ties/Doors.lean):
code switching (K2): THE RIDING HALF OF THE FIELD «more», FROM «WHAT AN ACCEPT OF THE
SWITCH LEAVES OF THE VERIFIER's STATE» (Left, K2Ties/Left.lean: its fields out and grows);
AND THE FINISH's SHARE OF e₁ WITH «more» NO PREMISE ANY MORE. NO BLOCK IMPORTS THIS FILE.
  there_of_left    Left s s' : every oracle message's number that is there in front is there
                   behind
  left_of_sits     where b sits over the kind's own sub-protocol behind a door whose way in and
                   way out each give Left: every accept of b gives Left
  left_bare_back   the lot's own sub-protocol at «F:1»: every accept gives Left (left_finishFront
                   · left_of_yes · left_finishBehind, called)
  more_link_left · more_head_left · more_finish_left   more_link | more_head | more_finish with
                                                       Left in the place of the two facts on the
                                                       step
  share_backE      THE SHARE «back» AT E := EQ Mg linksW placesW z : HandsR Fk N linksW placesW
                   (EQ …) ft 353 b' from share_backR's premises BUT «more», with: Mg.pub = pubAll
                   D base · Mg.more = moreAll · «in order» reads the public part alone
LIMITS. The debts on the numbers stay. At the 24 other places the makings stay (and «tokenSmall»
at 339). No soundness is claimed.
-/
import Johnson.P1K2R.MoreAtSwitch
import Johnson.P1K2R.HandsShares
import Johnson.Top.H0.K2Ties.Doors

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace P1K2
open VerifiableInference.Desc (Block Place OpenedColumn KindName)
open VerifiableInference.Desc.First (S ModelPart Numbers Pub Meaning PubData pubAll)
open VerifiableInference.Desc.First.K2 (P2 codeSwitchKind finishFrontQ finishBehindQ SwitchDebts frontAt
  frameAt k2_step_two)
open VerifiableInference.Desc.First.K2Ties (Left left_of_yes left_finishFront left_finishBehind)
open VerifiableInference.Desc.Sound (moreAll)
open H2K.JointK (Sits)
open ProofFile (Cl)
open IM (HandsR XK Yes linksW placesW subW k2P)
open _root_.Tw.K2 (switchNotices)

theorem there_of_left {s s' : S} (L : Left s s') (j : Nat)
    (h : (s.st.oracles[j]?).isSome = true) : (s'.st.oracles[j]?).isSome = true := by
  obtain ⟨x, hx⟩ := Option.isSome_iff_exists.1 h
  obtain ⟨x', hx', _⟩ := L.grows.2.2 j x hx
  rw [hx']
  rfl

theorem left_of_sits {ft : Nat} {b : Block S Cl} {p : P2} {enter : S → Except String S}
    {leave : S → S → Except String S} (hs : Sits b (codeSwitchKind p : Block S Unit) enter leave)
    (hin : ∀ s t, enter s = .ok t → Left s t) (hout : ∀ s t s', leave s t = .ok s' → Left t s')
    {s s' : S} (hy : Yes ft b s s') : Left s s' := by
  obtain ⟨rs, cols, n, e⟩ := hy
  obtain ⟨t, t', e1, e2, e3⟩ := hs.step ft s s' rs cols n e
  obtain ⟨r₁, r₂, gs, _, hd⟩ := k2_step_two e2
  exact (hin s t e1).trans ((left_of_yes hd).trans (hout s t' s' e3))

theorem left_bare_back {Z : ProofFile.Pub} {G₀ : ProofFile.Ground} {b' : Block S Cl}
    (hlot : ∃ L ∈ ProofFile.onlineFirstChainBlockTables Z, b' ∈ L.blocks G₀)
    (hpl : b'.place = { chain := 1, link := none, piece := 1, kind := .K2 }) {ft : Nat}
    {s s' : S} (hy : Yes ft b' s s') : Left s s' := by
  obtain ⟨L, hL, hb'⟩ := hlot
  obtain ⟨x, hx, rfl⟩ := IM.lot_K2 hL hb' (by rw [hpl])
  have hi := IM.k2_mem hx
  rw [show x.place = _ from hpl] at hi
  rcases hi with ⟨_, hm⟩ | ⟨P, n, hP, hn, hA⟩
  · exact absurd hy (never_of_mute hm s s')
  · rcases hA with ⟨_, hx'⟩ | ⟨l, HP, hl, _⟩ | ⟨l, hl, _⟩
    · have hS := sits_under_finish x.name IM.k2PlaceF (k2P Z IM.k2PlaceF x.name .finish n)
      rw [← hx'] at hS
      exact left_of_sits hS (fun _ _ e => left_finishFront e)
        (fun _ _ _ e => left_finishBehind e) hy
    · cases hl
    · cases hl

variable {P W : Type}

theorem more_finish_left {N : Numbers} {Mg : Meaning P W} {z : P} {s s' : S} (D : PubData)
    (base : Pub → P × S → Bool) (hpub : Mg.pub = pubAll D base) (hmore : Mg.more = moreAll)
    (hx : XK N linksW placesW (EQ Mg linksW placesW z) 353 s = true)
    (hIn : Mg.inOrder (z, s) = true → Mg.inOrder (z, s') = true) (L : Left s s') :
    EQ Mg linksW placesW z (353 + 1) s' = true :=
  more_finish D base hpub hmore hx hIn L.out (there_of_left L)

theorem more_link_left {N : Numbers} {Mg : Meaning P W} {z : P} {l : Nat} (h1 : 1 ≤ l)
    (h24 : l < 24) {s s' : S} (D : PubData) (base : Pub → P × S → Bool)
    (hpub : Mg.pub = pubAll D base) (hmore : Mg.more = moreAll)
    (hx : XK N linksW placesW (EQ Mg linksW placesW z) (14 * l + 2) s = true)
    (hIn : Mg.inOrder (z, s) = true → Mg.inOrder (z, s') = true) (L : Left s s')
    (hMade : ∀ q ∈ madeAt l 2 (decide (subW l = .attention)), Mg.pub q (z, s') = true) :
    EQ Mg linksW placesW z (14 * l + 2 + 1) s' = true :=
  more_link h1 h24 D base hpub hmore hx hIn L.out (there_of_left L) hMade

theorem more_head_left {N : Numbers} {Mg : Meaning P W} {z : P} {s s' : S} (D : PubData)
    (base : Pub → P × S → Bool) (hpub : Mg.pub = pubAll D base) (hmore : Mg.more = moreAll)
    (hx : XK N linksW placesW (EQ Mg linksW placesW z) 339 s = true)
    (hIn : Mg.inOrder (z, s) = true → Mg.inOrder (z, s') = true) (L : Left s s')
    (htok : Mg.pub .tokenSmall (z, s) = true → Mg.pub .tokenSmall (z, s') = true)
    (hMade : ∀ q ∈ madeAt 24 3 false, Mg.pub q (z, s') = true) :
    EQ Mg linksW placesW z (339 + 1) s' = true :=
  more_head D base hpub hmore hx hIn L.out (there_of_left L) htok hMade

theorem share_backE {Fk : Nat → S → Prop} {Z : ProofFile.Pub} {G₀ : ProofFile.Ground} {b' : Block S Cl}
    (hlot : ∃ L ∈ ProofFile.onlineFirstChainBlockTables Z, b' ∈ L.blocks G₀)
    (hpl : b'.place = { chain := 1, link := none, piece := 1, kind := .K2 })
    {N : Numbers} {Mg : Meaning P W} {z : P} {ft : Nat} (D₀ : PubData)
    (base : Pub → P × S → Bool) (hpub : Mg.pub = pubAll D₀ base) (hmore : Mg.more = moreAll)
    (hIn : ∀ s s' : S, Mg.inOrder (z, s) = true → Mg.inOrder (z, s') = true)
    (hgrp : ∀ P n, prepOf Z G₀ = some P → numsAt P none = some n → N.groupAt 25 = n.grp)
    (D : ∀ nm P n (s t : S) x W lay, prepOf Z G₀ = some P → numsAt P none = some n →
      Fk 353 s → XK N linksW placesW (EQ Mg linksW placesW z) 353 s = true →
      finishFrontQ s = .ok t →
      frontAt (k2P Z IM.k2PlaceF nm .finish n) t = some x → frameAt x = some W →
      OnBytes.layTrees x.st.codes (switchNotices x.T x.others) = some lay →
      SwitchDebts N 25 placesW[353]? placesW[353 + 1]? s.book.trees.size n.positions
        (1 + x.T.kept.size) x W lay) :
    HandsR Fk N linksW placesW (EQ Mg linksW placesW z) ft 353 b' :=
  share_backR hlot hpl hgrp D fun s s' _ hy _ _ hx =>
    more_finish_left D₀ base hpub hmore hx (hIn s s') (left_bare_back hlot hpl hy)

end P1K2

#print axioms P1K2.left_of_sits
#print axioms P1K2.left_bare_back
#print axioms P1K2.more_finish_left
#print axioms P1K2.more_link_left
#print axioms P1K2.more_head_left
#print axioms P1K2.share_backE
