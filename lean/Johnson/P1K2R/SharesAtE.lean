-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P1K2R/SharesAtE.lean (over SharesE.lean and Johnson/Desc/First/EPubAt.lean):
code switching (K2): ITS THREE
SHARES OF e₁, 25 SUB-PROTOCOLS, IN THE FORM THAT A WORKING LIST FOR e₁ (NOT NAMED HERE) COUNTS:
IM.HandsR Fk N linksW placesW E ft k b AT E := THE PROMISE's PUBLIC TEST BY THE BORDER's NUMBER
(ePubAt) AT THE COMPOSED PUBLIC TESTS (pubAll D base) AND THE ROWS moreAll, at a
public part z. General in Fk · N · ft · D · base · z. NO BLOCK IMPORTS THIS FILE.
  EP D base z     fun k s => ePubAt (pubAll D base) moreAll linksW placesW k (z, s)
  ep_step         the rule: what is asked behind and was asked in front rides; the rest is made
  ep_link · ep_head · ep_finish   at the three sorts of place, from Left and the makings
  share_firstP (23: k = 14 l + 2, 1 ≤ l < 24) · share_hearP (339) · share_backP (353)
EVERY PREMISE ON A STATE IN FRONT STANDS UNDER THE FENCE Fk k s. THE PREMISES, BY NAME: hgrp
(N.groupAt m is the place's own number of the group: on the plan alone) · D (LinkDebts |
SwitchDebts: six equations on N at the front of a fenced state) · fresh (339 alone: the head's
group is fresh at a fenced state) · hMade (24 places: the tests of the six | eight items that the
place makes hold behind an accept) · htok (339 alone: «tokenSmall» rides) · at the 23: hX · hk ·
hsort (the link's sort by the plan is the written list's) · at 339: hl24. AT 353 «more» IS NO
PREMISE. No soundness is claimed.
-/
import Johnson.P1K2R.SharesE
import Johnson.Desc.First.EPubAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace P1K2
open VerifiableInference.Desc (Block Place OpenedColumn KindName)
open VerifiableInference.Desc.First (S ModelPart Numbers Pub PubData pubAll ePubAt)
open VerifiableInference.Desc.First.K2 (finishFrontQ LinkDebts SwitchDebts HeadFresh frontAt
  frameAt pub_rides3)
open VerifiableInference.Desc.First.K2Ties (Left)
open VerifiableInference.Desc.Sound (moreAll)
open ProofFile (Cl)
open IM (HandsR XK Yes xk_parts linksW placesW subW k2P Joined)
open _root_.Tw.K2 (firstFront switchNotices)

variable {P : Type}

/-- The promise's public test at border k of the written list, at the public part z. -/
def EP (D : PubData) (base : Pub → P × S → Bool) (z : P) (k : Nat) (s : S) : Bool :=
  ePubAt (pubAll D base) moreAll linksW placesW k (z, s)

theorem ep_step (D : PubData) (base : Pub → P × S → Bool) (z : P) {k : Nat} {s s' : S}
    {front behind : List Pub} (hA : askedB k front behind = true) (h : EP D base z k s = true)
    (hk : ∀ q ∈ behind, q ∈ front → pubAll D base q (z, s) = true →
      pubAll D base q (z, s') = true)
    (hm : ∀ q ∈ behind, ¬ q ∈ front → pubAll D base q (z, s') = true) :
    EP D base z (k + 1) s' = true := by
  obtain ⟨e1, e2⟩ := asked_parts hA
  have h' : (askedW moreAll k).all (fun q => pubAll D base q (z, s)) = true := h
  show (askedW moreAll (k + 1)).all (fun q => pubAll D base q (z, s')) = true
  rw [e1] at h'
  rw [e2]
  apply List.all_eq_true.2
  intro q hq
  by_cases hf : q ∈ front
  · exact hk q hq hf (List.all_eq_true.1 h' q hf)
  · exact hm q hq hf

theorem ep_finish (D : PubData) (base : Pub → P × S → Bool) (z : P) {s s' : S}
    (h : EP D base z 353 s = true) (L : Left s s') : EP D base z (353 + 1) s' = true :=
  ep_step D base z asked_finish h
    (fun q hq _ e => pub_rides3 D base z L.out (there_of_left L) q (List.mem_cons_of_mem _ hq) e)
    fun _ hq hn => absurd hq hn

theorem ep_link (D : PubData) (base : Pub → P × S → Bool) (z : P) {l : Nat} (h1 : 1 ≤ l)
    (h24 : l < 24) {s s' : S} (h : EP D base z (14 * l + 2) s = true) (L : Left s s')
    (hMade : ∀ q ∈ madeAt l 2 (decide (subW l = .attention)), pubAll D base q (z, s') = true) :
    EP D base z (14 * l + 2 + 1) s' = true := by
  have hA := List.all_eq_true.1 asked_links l (List.mem_range'_1.2 ⟨h1, by omega⟩)
  refine ep_step D base z hA h
    (fun q _ hf e => pub_rides3 D base z L.out (there_of_left L) q hf e) fun q hq hn => ?_
  rcases List.mem_cons.1 hq with rfl | hq
  · exact absurd (List.mem_cons_self) hn
  · rcases List.mem_append.1 hq with hq | hq
    · exact hMade q hq
    · exact absurd (List.mem_cons_of_mem _ hq) hn

theorem ep_head (D : PubData) (base : Pub → P × S → Bool) (z : P) {s s' : S}
    (h : EP D base z 339 s = true) (L : Left s s')
    (htok : pubAll D base .tokenSmall (z, s) = true → pubAll D base .tokenSmall (z, s') = true)
    (hMade : ∀ q ∈ madeAt 24 3 false, pubAll D base q (z, s') = true) :
    EP D base z (339 + 1) s' = true := by
  refine ep_step D base z asked_head h (fun q _ hf e => ?_) fun q hq hn => ?_
  · rcases List.mem_cons.1 hf with rfl | hf
    · exact htok e
    · exact pub_rides3 D base z L.out (there_of_left L) q (List.mem_cons_of_mem _ hf) e
  · rcases List.mem_cons.1 hq with rfl | hq
    · exact absurd (List.mem_cons_self) hn
    · rcases List.mem_append.1 hq with hq | hq
      · exact hMade q hq
      · exact absurd (List.mem_cons_of_mem _ hq) hn

theorem share_backP {Fk : Nat → S → Prop} {Z : ProofFile.Pub} {G₀ : ProofFile.Ground} {b' : Block S Cl}
    (hlot : ∃ L ∈ ProofFile.onlineFirstChainBlockTables Z, b' ∈ L.blocks G₀)
    (hpl : b'.place = { chain := 1, link := none, piece := 1, kind := .K2 })
    {N : Numbers} {ft : Nat} (D₀ : PubData) (base : Pub → P × S → Bool) (z : P)
    (hgrp : ∀ P n, prepOf Z G₀ = some P → numsAt P none = some n → N.groupAt 25 = n.grp)
    (D : ∀ nm P n (s t : S) x W lay, prepOf Z G₀ = some P → numsAt P none = some n →
      Fk 353 s → XK N linksW placesW (EP D₀ base z) 353 s = true → finishFrontQ s = .ok t →
      frontAt (k2P Z IM.k2PlaceF nm .finish n) t = some x → frameAt x = some W →
      OnBytes.layTrees x.st.codes (switchNotices x.T x.others) = some lay →
      SwitchDebts N 25 placesW[353]? placesW[353 + 1]? s.book.trees.size n.positions
        (1 + x.T.kept.size) x W lay) :
    HandsR Fk N linksW placesW (EP D₀ base z) ft 353 b' :=
  share_backR hlot hpl hgrp D fun _ _ _ hy _ _ hx =>
    ep_finish D₀ base z (xk_parts hx).2.2.2.2 (left_bare_back hlot hpl hy)

theorem share_firstP {Fk : Nat → S → Prop} {Z : ProofFile.Pub} {G₀ : ProofFile.Ground} {l : Nat}
    (h1 : 1 ≤ l) (h24 : l < 24)
    {b b' : Block S Cl} (hlot : ∃ L ∈ ProofFile.onlineFirstChainBlockTables Z, b' ∈ L.blocks G₀)
    (hpl : b'.place = { chain := 1, link := some l, piece := 1, kind := .K2 })
    (hJ : Joined Z l b b' { chain := 1, link := some l, piece := 1, kind := .K2 })
    {X : OnBytes.Model.Stages.LinkH} (hX : Z.p.built.links[l]? = some X) (hk : X.kind ≠ 2)
    (hsort : (X.kind = 0 → subW l = .layers) ∧ (X.kind = 1 → subW l = .attention))
    {N : Numbers} {ft : Nat} (D₀ : PubData) (base : Pub → P × S → Bool) (z : P)
    (hgrp : ∀ P n, prepOf Z G₀ = some P → numsAt P (some l) = some n → N.groupAt l = n.grp)
    (D : ∀ P n (s : S) x W lay, prepOf Z G₀ = some P → numsAt P (some l) = some n →
      Fk (14 * l + 2) s → XK N linksW placesW (EP D₀ base z) (14 * l + 2) s = true →
      firstFront s.st s.check.frame = .ok x → frameAt x = some W →
      OnBytes.layTrees x.st.codes (switchNotices x.T x.others) = some lay →
      LinkDebts N l placesW[14 * l + 2]? placesW[14 * l + 3]? s n.positions x W lay)
    (hMade : ∀ s s', Fk (14 * l + 2) s → Yes ft b s s' → s.failed = none → s'.failed = none →
      XK N linksW placesW (EP D₀ base z) (14 * l + 2) s = true →
      ∀ q ∈ madeAt l 2 (decide (subW l = .attention)), pubAll D₀ base q (z, s') = true) :
    HandsR Fk N linksW placesW (EP D₀ base z) ft (14 * l + 2) b :=
  share_firstR h1 h24 hlot hpl hJ hX hk hsort hgrp D fun s s' hf hy h0 h1' hx =>
    ep_link D₀ base z h1 h24 (xk_parts hx).2.2.2.2 (left_first h1 hlot hpl hJ hy)
      (hMade s s' hf hy h0 h1' hx)

theorem share_hearP {Fk : Nat → S → Prop} {Z : ProofFile.Pub} {G₀ : ProofFile.Ground} {b' : Block S Cl}
    (hlot : ∃ L ∈ ProofFile.onlineFirstChainBlockTables Z, b' ∈ L.blocks G₀)
    (hpl : b'.place = { chain := 1, link := some 24, piece := 2, kind := .K2 })
    (hl24 : ∀ HP, pureLetters G₀ 24 = some HP → HP.l = 24)
    {N : Numbers} {ft : Nat} (D₀ : PubData) (base : Pub → P × S → Bool) (z : P)
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
    (hMade : ∀ s s', Fk 339 s → Yes ft b' s s' → s.failed = none → s'.failed = none →
      XK N linksW placesW (EP D₀ base z) 339 s = true →
      ∀ q ∈ madeAt 24 3 false, pubAll D₀ base q (z, s') = true) :
    HandsR Fk N linksW placesW (EP D₀ base z) ft 339 b' :=
  share_hearR hlot hpl hl24 hgrp fresh D fun s s' hf hy h0 h1' hx =>
    ep_head D₀ base z (xk_parts hx).2.2.2.2 (left_bare_hear hlot hpl hy)
      (htok s s' hf hy h0 h1') (hMade s s' hf hy h0 h1' hx)

end P1K2

#print axioms P1K2.ep_step
#print axioms P1K2.share_firstP
#print axioms P1K2.share_hearP
#print axioms P1K2.share_backP
