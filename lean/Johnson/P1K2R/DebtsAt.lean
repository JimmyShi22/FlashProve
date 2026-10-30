-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P1K2R/DebtsAt.lean: the code switch: «D», THE PREMISE ON THE TABLE's NUMBERS OF
K2's TEXT's THREE SHARES OF «Hands» (Johnson/P1K2R/HandsShares.lean: share_firstR ·
share_hearR · share_backR), IN THE SHARES' OWN LETTERS, at numbers of the form N₀.atBlocks sh links
bs: PAID OUT OF A NAMED LIST.
  d_link · d_head · d_finish  «D» at a link's switch (number 14 l + 2), at the head's (339), at the
               finish's (353)
  share_first_d · share_hear_d · share_back_d  the three shares with «D» paid so: LEAN ITSELF HOLDS
               THE LETTERS OF d_link | d_head | d_finish TO THE SHARES'
WHAT STANDS IN «D»'s PLACE. CLOSED, ON THE WRITTEN LIST OF SUB-PROTOCOLS AND THE PLAN: hps: the
sub-protocols' places are the written list · hnd: no place twice · hbk: the sub-protocol at the
number · hok: the plan's shape is lawful · hlenC: the table keeps as many seats of the segment in
front as the plan's target of the group keeps members · hcl, at the plan's numbers n of the place:
what the sub-protocol tells is oraclesAt n.grp n.codes n.sent · the test sentFitB accepts · the
table's count of positions is n.positions. ON THE FENCED STATES (Fk, and the promise's Bools XK):
hst: SwState (DebtsState.lean: six facts) · the switch's notices are n.sent (the fence's first
clause) · at each entry of the frame's kept list the front's statement has a message whose shape
counts one answer.
LIMITS. Joins. None of the premises is shown at a real value here. The shares' other premises (hgrp,
fresh, more, the lot's) stand as they are. No soundness is claimed.
-/
import Johnson.Top.H0.Tw.K2C.DebtsState
import Johnson.P1K2R.HandsShares

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P1K2
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Block Place)
open VerifiableInference.Desc.First (S ModelPart Numbers blockPlaces possAt)
open VerifiableInference.Desc.First.K2 (finishFrontQ LinkDebts SwitchDebts frontAt frameAt FrontOf
  SwState sentFitB debts_at_front debts_at_finish frontOf_iff)
open IM (XK xk_parts linksW placesW k2P)
open _root_.Tw.K2 (firstFront switchNotices)

variable {St Cl' : Type} {N₀ : Numbers} {sh : Params.ReqShape} {links : List ModelPart}
  {bs : List (Block St Cl')} {Fk : Nat → S → Prop} {E : Nat → S → Bool} {Z : ProofFile.Pub}
  {G₀ : ProofFile.Ground}

/-- **«D» OF THE SHARE AT A LINK's SWITCH** (share_firstR | share_firstP), 1 ≤ l. -/
theorem d_link {l : Nat} (hl : l ≠ 0) (hps : blockPlaces bs = placesW) (hnd : placesW.Nodup)
    {b : Block St Cl'} (hbk : bs[14 * l + 2]? = some b) (hok : reqShapeOk sh = true)
    (hlenC : (N₀.keptOf (l - 1)).length = ((reqGroups sh).getD l {}).target.kept.size)
    (hcl : ∀ P n, prepOf Z G₀ = some P → numsAt P (some l) = some n →
      b.oracles.flatten = oraclesAt n.grp n.codes n.sent ∧
      sentFitB (N₀.atBlocks sh links bs) l placesW[14 * l + 2]? n.codes n.sent = true ∧
      possAt bs links.length l = n.positions)
    (hst : ∀ P n (s : S), prepOf Z G₀ = some P → numsAt P (some l) = some n →
      Fk (14 * l + 2) s → XK (N₀.atBlocks sh links bs) linksW placesW E (14 * l + 2) s = true →
      SwState sh l n.codes s ∧
      (∀ x, firstFront s.st s.check.frame = .ok x → switchNotices x.T x.others = n.sent) ∧
      ∀ x W, firstFront s.st s.check.frame = .ok x → frameAt x = some W → ∀ κ ∈ W.kept,
        ∃ xo : OnBytes.Oracle, x.st.oracles[κ.old]? = some xo ∧ xo.shape.answers = 1) :
    ∀ P n (s : S) x W lay, prepOf Z G₀ = some P → numsAt P (some l) = some n →
      Fk (14 * l + 2) s → XK (N₀.atBlocks sh links bs) linksW placesW E (14 * l + 2) s = true →
      firstFront s.st s.check.frame = .ok x → frameAt x = some W →
      OnBytes.layTrees x.st.codes (switchNotices x.T x.others) = some lay →
      LinkDebts (N₀.atBlocks sh links bs) l placesW[14 * l + 2]? placesW[14 * l + 3]? s
        n.positions x W lay := by
  intro P n s x W lay hP hn hf hx hfr hW hlay
  obtain ⟨c1, c2, c3⟩ := hcl P n hP hn
  obtain ⟨Q, s1, s2⟩ := hst P n s hP hn hf hx
  have hFO : ∀ y, FrontOf (k2P Z default "" .link n) s y →
      firstFront s.st s.check.frame = .ok y := by
    intro y hy
    rcases hy with ⟨_, e⟩ | ⟨c, _⟩ | ⟨c, _⟩
    · exact e
    · cases c
    · cases c
  exact (debts_at_front (p := k2P Z default "" .link n) hps hnd hbk c1 hl c2 c3 hok hlenC
    (xk_parts hx).2.2.2.1 Q (fun e => nomatch e) (fun y hy => s1 y (hFO y hy))
    (frontOf_iff.1 (Or.inl ⟨rfl, hfr⟩)) hW hlay (s2 x W hfr hW)).1

/-- **«D» OF THE SHARE AT THE HEAD's SWITCH** (share_hearR | share_hearP). -/
theorem d_head (hps : blockPlaces bs = placesW) (hnd : placesW.Nodup)
    {b : Block St Cl'} (hbk : bs[339]? = some b) (hok : reqShapeOk sh = true)
    (hlenC : (N₀.keptOf (24 - 1)).length = ((reqGroups sh).getD 24 {}).target.kept.size)
    (hcl : ∀ P n, prepOf Z G₀ = some P → numsAt P (some 24) = some n →
      b.oracles.flatten = oraclesAt n.grp n.codes n.sent ∧
      sentFitB (N₀.atBlocks sh links bs) 24 placesW[339]? n.codes n.sent = true ∧
      possAt bs links.length 24 = n.positions)
    (hst : ∀ nm P n (s : S), prepOf Z G₀ = some P → numsAt P (some 24) = some n →
      Fk 339 s → XK (N₀.atBlocks sh links bs) linksW placesW E 339 s = true →
      SwState sh 24 n.codes s ∧
      (∀ x, frontAt (k2P Z { chain := 1, link := some 24, piece := 2, kind := .K2 } nm .head n) s =
        some x → switchNotices x.T x.others = n.sent) ∧
      ∀ x W, frontAt (k2P Z { chain := 1, link := some 24, piece := 2, kind := .K2 } nm .head n) s =
        some x → frameAt x = some W → ∀ κ ∈ W.kept,
        ∃ xo : OnBytes.Oracle, x.st.oracles[κ.old]? = some xo ∧ xo.shape.answers = 1) :
    ∀ nm P n (s : S) x W lay, prepOf Z G₀ = some P → numsAt P (some 24) = some n →
      Fk 339 s → XK (N₀.atBlocks sh links bs) linksW placesW E 339 s = true →
      frontAt (k2P Z { chain := 1, link := some 24, piece := 2, kind := .K2 } nm .head n) s =
        some x → frameAt x = some W →
      OnBytes.layTrees x.st.codes (switchNotices x.T x.others) = some lay →
      SwitchDebts (N₀.atBlocks sh links bs) 24 placesW[339]? placesW[339 + 1]? s.book.trees.size
        n.positions (1 + x.T.kept.size + x.own.length) x W lay := by
  intro nm P n s x W lay hP hn hf hx hfr hW hlay
  obtain ⟨c1, c2, c3⟩ := hcl P n hP hn
  obtain ⟨Q, s1, s2⟩ := hst nm P n s hP hn hf hx
  exact (debts_at_front
    (p := k2P Z { chain := 1, link := some 24, piece := 2, kind := .K2 } nm .head n) hps hnd hbk c1
    (by decide) c2 c3 hok hlenC (xk_parts hx).2.2.2.1 Q (fun e => nomatch e)
    (fun y hy => s1 y (frontOf_iff.1 hy)) hfr hW hlay (s2 x W hfr hW)).2

/-- **«D» OF THE SHARE AT THE FINISH's SWITCH** (share_backR | share_backP). -/
theorem d_finish (hps : blockPlaces bs = placesW) (hnd : placesW.Nodup)
    {b : Block St Cl'} (hbk : bs[353]? = some b) (hok : reqShapeOk sh = true)
    (hlenC : (N₀.keptOf (25 - 1)).length = ((reqGroups sh).getD 25 {}).target.kept.size)
    (hcl : ∀ P n, prepOf Z G₀ = some P → numsAt P none = some n →
      b.oracles.flatten = oraclesAt n.grp n.codes n.sent ∧
      sentFitB (N₀.atBlocks sh links bs) 25 placesW[353]? n.codes n.sent = true ∧
      possAt bs links.length 25 = n.positions)
    (hst : ∀ nm P n (s t : S), prepOf Z G₀ = some P → numsAt P none = some n →
      Fk 353 s → XK (N₀.atBlocks sh links bs) linksW placesW E 353 s = true →
      finishFrontQ s = .ok t → SwState sh 25 n.codes s ∧
      (∀ x, frontAt (k2P Z IM.k2PlaceF nm .finish n) t = some x →
        switchNotices x.T x.others = n.sent) ∧
      ∀ x W, frontAt (k2P Z IM.k2PlaceF nm .finish n) t = some x → frameAt x = some W →
        ∀ κ ∈ W.kept, ∃ xo : OnBytes.Oracle, x.st.oracles[κ.old]? = some xo ∧
          xo.shape.answers = 1) :
    ∀ nm P n (s t : S) x W lay, prepOf Z G₀ = some P → numsAt P none = some n →
      Fk 353 s → XK (N₀.atBlocks sh links bs) linksW placesW E 353 s = true →
      finishFrontQ s = .ok t →
      frontAt (k2P Z IM.k2PlaceF nm .finish n) t = some x → frameAt x = some W →
      OnBytes.layTrees x.st.codes (switchNotices x.T x.others) = some lay →
      SwitchDebts (N₀.atBlocks sh links bs) 25 placesW[353]? placesW[353 + 1]? s.book.trees.size
        n.positions (1 + x.T.kept.size) x W lay := by
  intro nm P n s t x W lay hP hn hf hx he hfr hW hlay
  obtain ⟨c1, c2, c3⟩ := hcl P n hP hn
  obtain ⟨Q, s1, s2⟩ := hst nm P n s t hP hn hf hx he
  exact debts_at_finish hps hnd hbk c1 (by decide) c2 c3 hok hlenC (xk_parts hx).2.2.2.1 Q he rfl
    (fun y hy => s1 y (frontOf_iff.1 hy)) hfr hW hlay (s2 x W hfr hW)

/-! ## The three shares with «D» paid: so Lean itself holds d_link | d_head | d_finish to them -/

section
open IM (HandsR Yes subW Joined)
open ProofFile (Cl)
open VerifiableInference.Desc.First.K2 (HeadFresh)
variable {ft : Nat}

theorem share_first_d {l : Nat} (hl : l ≠ 0) (hps : blockPlaces bs = placesW) (hnd : placesW.Nodup)
    {bk : Block St Cl'} (hbk : bs[14 * l + 2]? = some bk) (hok : reqShapeOk sh = true)
    (hlenC : (N₀.keptOf (l - 1)).length = ((reqGroups sh).getD l {}).target.kept.size)
    (hcl : ∀ P n, prepOf Z G₀ = some P → numsAt P (some l) = some n →
      bk.oracles.flatten = oraclesAt n.grp n.codes n.sent ∧
      sentFitB (N₀.atBlocks sh links bs) l placesW[14 * l + 2]? n.codes n.sent = true ∧
      possAt bs links.length l = n.positions)
    (hst : ∀ P n (s : S), prepOf Z G₀ = some P → numsAt P (some l) = some n →
      Fk (14 * l + 2) s → XK (N₀.atBlocks sh links bs) linksW placesW E (14 * l + 2) s = true →
      SwState sh l n.codes s ∧
      (∀ x, firstFront s.st s.check.frame = .ok x → switchNotices x.T x.others = n.sent) ∧
      ∀ x W, firstFront s.st s.check.frame = .ok x → frameAt x = some W → ∀ κ ∈ W.kept,
        ∃ xo : OnBytes.Oracle, x.st.oracles[κ.old]? = some xo ∧ xo.shape.answers = 1)
    (h1 : 1 ≤ l) (h24 : l < 24) {b b' : Block S Cl}
    (hlot : ∃ L ∈ ProofFile.onlineFirstChainBlockTables Z, b' ∈ L.blocks G₀)
    (hpl : b'.place = { chain := 1, link := some l, piece := 1, kind := .K2 })
    (hJ : Joined Z l b b' { chain := 1, link := some l, piece := 1, kind := .K2 })
    {X : OnBytes.Model.Stages.LinkH} (hX : Z.p.built.links[l]? = some X) (hk : X.kind ≠ 2)
    (hsort : (X.kind = 0 → subW l = .layers) ∧ (X.kind = 1 → subW l = .attention))
    (hgrp : ∀ P n, prepOf Z G₀ = some P → numsAt P (some l) = some n →
      (N₀.atBlocks sh links bs).groupAt l = n.grp)
    (more : ∀ s s', Fk (14 * l + 2) s → Yes ft b s s' → s.failed = none → s'.failed = none →
      XK (N₀.atBlocks sh links bs) linksW placesW E (14 * l + 2) s = true →
      E (14 * l + 2 + 1) s' = true) :
    HandsR Fk (N₀.atBlocks sh links bs) linksW placesW E ft (14 * l + 2) b :=
  share_firstR h1 h24 hlot hpl hJ hX hk hsort hgrp (d_link hl hps hnd hbk hok hlenC hcl hst) more

theorem share_hear_d (hps : blockPlaces bs = placesW) (hnd : placesW.Nodup)
    {bk : Block St Cl'} (hbk : bs[339]? = some bk) (hok : reqShapeOk sh = true)
    (hlenC : (N₀.keptOf (24 - 1)).length = ((reqGroups sh).getD 24 {}).target.kept.size)
    (hcl : ∀ P n, prepOf Z G₀ = some P → numsAt P (some 24) = some n →
      bk.oracles.flatten = oraclesAt n.grp n.codes n.sent ∧
      sentFitB (N₀.atBlocks sh links bs) 24 placesW[339]? n.codes n.sent = true ∧
      possAt bs links.length 24 = n.positions)
    (hst : ∀ nm P n (s : S), prepOf Z G₀ = some P → numsAt P (some 24) = some n →
      Fk 339 s → XK (N₀.atBlocks sh links bs) linksW placesW E 339 s = true →
      SwState sh 24 n.codes s ∧
      (∀ x, frontAt (k2P Z { chain := 1, link := some 24, piece := 2, kind := .K2 } nm .head n) s =
        some x → switchNotices x.T x.others = n.sent) ∧
      ∀ x W, frontAt (k2P Z { chain := 1, link := some 24, piece := 2, kind := .K2 } nm .head n) s =
        some x → frameAt x = some W → ∀ κ ∈ W.kept,
        ∃ xo : OnBytes.Oracle, x.st.oracles[κ.old]? = some xo ∧ xo.shape.answers = 1)
    {b' : Block S Cl} (hlot : ∃ L ∈ ProofFile.onlineFirstChainBlockTables Z, b' ∈ L.blocks G₀)
    (hpl : b'.place = { chain := 1, link := some 24, piece := 2, kind := .K2 })
    (hl24 : ∀ HP, pureLetters G₀ 24 = some HP → HP.l = 24)
    (hgrp : ∀ P n, prepOf Z G₀ = some P → numsAt P (some 24) = some n →
      (N₀.atBlocks sh links bs).groupAt 24 = n.grp)
    (fresh : ∀ s, Fk 339 s → XK (N₀.atBlocks sh links bs) linksW placesW E 339 s = true →
      HeadFresh s)
    (more : ∀ s s', Fk 339 s → Yes ft b' s s' → s.failed = none → s'.failed = none →
      XK (N₀.atBlocks sh links bs) linksW placesW E 339 s = true → E (339 + 1) s' = true) :
    HandsR Fk (N₀.atBlocks sh links bs) linksW placesW E ft 339 b' :=
  share_hearR hlot hpl hl24 hgrp fresh (d_head hps hnd hbk hok hlenC hcl hst) more

theorem share_back_d (hps : blockPlaces bs = placesW) (hnd : placesW.Nodup)
    {bk : Block St Cl'} (hbk : bs[353]? = some bk) (hok : reqShapeOk sh = true)
    (hlenC : (N₀.keptOf (25 - 1)).length = ((reqGroups sh).getD 25 {}).target.kept.size)
    (hcl : ∀ P n, prepOf Z G₀ = some P → numsAt P none = some n →
      bk.oracles.flatten = oraclesAt n.grp n.codes n.sent ∧
      sentFitB (N₀.atBlocks sh links bs) 25 placesW[353]? n.codes n.sent = true ∧
      possAt bs links.length 25 = n.positions)
    (hst : ∀ nm P n (s t : S), prepOf Z G₀ = some P → numsAt P none = some n →
      Fk 353 s → XK (N₀.atBlocks sh links bs) linksW placesW E 353 s = true →
      finishFrontQ s = .ok t → SwState sh 25 n.codes s ∧
      (∀ x, frontAt (k2P Z IM.k2PlaceF nm .finish n) t = some x →
        switchNotices x.T x.others = n.sent) ∧
      ∀ x W, frontAt (k2P Z IM.k2PlaceF nm .finish n) t = some x → frameAt x = some W →
        ∀ κ ∈ W.kept, ∃ xo : OnBytes.Oracle, x.st.oracles[κ.old]? = some xo ∧
          xo.shape.answers = 1)
    {b' : Block S Cl} (hlot : ∃ L ∈ ProofFile.onlineFirstChainBlockTables Z, b' ∈ L.blocks G₀)
    (hpl : b'.place = { chain := 1, link := none, piece := 1, kind := .K2 })
    (hgrp : ∀ P n, prepOf Z G₀ = some P → numsAt P none = some n →
      (N₀.atBlocks sh links bs).groupAt 25 = n.grp)
    (more : ∀ s s', Fk 353 s → Yes ft b' s s' → s.failed = none → s'.failed = none →
      XK (N₀.atBlocks sh links bs) linksW placesW E 353 s = true → E (353 + 1) s' = true) :
    HandsR Fk (N₀.atBlocks sh links bs) linksW placesW E ft 353 b' :=
  share_backR hlot hpl hgrp (d_finish hps hnd hbk hok hlenC hcl hst) more

end

end P1K2

#print axioms P1K2.d_head
#print axioms P1K2.share_first_d
#print axioms P1K2.share_hear_d
#print axioms P1K2.share_back_d
#print axioms P1K2.d_finish

#print axioms P1K2.d_link
