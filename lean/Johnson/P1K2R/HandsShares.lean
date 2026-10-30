-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P1K2R/HandsShares.lean (over HandsLinks.lean and HandsEnds.lean): code
switching (K2): ITS THREE SHARES IN THE BINDERS OF THE JOIN (structure
IM.Shares, Johnson/IMR/GrownJoin.lean): first (at 1 ≤ l < 24) · hear (at l = 24, i = 1) · back (at
j = 0). NO BLOCK IMPORTS THIS FILE.
  never_of_mute   a sub-protocol of the lot's table whose decision always rejects never accepts
  door_bare_head · door_bare_finish · door_bare_link   «a mark stays a mark» at the lot's BARE
                                                       sub-protocols' doors (no guard of the seat)
  share_firstR · share_hearR · share_backR   THE THREE AT
                                             HandsR Fk (Johnson/IMR/HandsFence.lean): HeadFresh,
                                             the debts on the numbers and «more» are asked AT
                                             FENCED STATES ALONE (Fk k s beside X k s): so a debt
                                             that reads the front can be paid from facts along the
                                             fold. The proofs stand at these; the three names
                                             without R are their case «no fence»
  share_first     b' a sub-protocol of the seat's lots at ⟨1, some l, 1, K2⟩ · Joined Z l b b' at
                  that address: Hands N linksW placesW E ft (14 * l + 2) b
  share_hear      b' a sub-protocol of the seat's lots at ⟨1, some 24, 2, K2⟩: Hands N linksW
                  placesW E ft 339 b' (339 = 14 * 24 + 1 + 2)
  share_back      b' a sub-protocol of the seat's lots at ⟨1, none, 1, K2⟩: Hands N linksW placesW
                  E ft 353 b' (353 = 353 + 0)
IN hear AND back THE SUB-PROTOCOL IS THE LOT's OWN, BARE: no guard of the seat stands behind it.
WHERE THE LOT's TABLE HAS A MUTE (its decision always rejects) nothing is owed.
THE PREMISES are those of hands_at_link | hands_head_of | hands_finish_of, each bound to the
place's own numbers n (prepOf Z G₀ = some P · numsAt P ‹the link› = some n), for every name nm:
hsort · hl24 · hgrp · LinkDebts | SwitchDebts · HeadFresh · more. No soundness is claimed.

-/
import Johnson.P1K2R.HandsLinks
import Johnson.P1K2R.HandsEnds

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace P1K2
open VerifiableInference.Desc (Block Place OpenedColumn KindName)
open VerifiableInference.Desc.First (S ModelPart Numbers)
open VerifiableInference.Desc.First.K2 (P2 codeSwitchKind headOpenQ finishFrontQ finishBehindQ LinkDebts
  SwitchDebts HeadFresh frameAt frontAt HeadPar)
open Johnson.Desc.First.Walk.Seat (LinkFrame framesOf)
open H2K.JointK (Sits)
open ProofFile (Cl)
open IM (Hands HandsR XK Yes linksW placesW subW k2P Joined)
open _root_.Tw.K2 (firstFront switchNotices)

theorem never_of_mute {x : Block S Unit} (hm : ∀ s rs gs, ∃ e, x.decide s rs gs = .error e)
    {ft : Nat} (s s' : S) : ¬ Yes ft (x.retype : Block S Cl) s s' := by
  rintro ⟨rs, cols, n, e⟩
  have hd := ((VerifiableInference.Desc.Sound.step_ok_iff ft _ s s' rs cols n).1 e).2.2.2
  obtain ⟨er, he⟩ := hm s _ _
  have hd' : x.decide s _ _ = .ok s' := hd
  rw [he] at hd'
  cases hd'

theorem door_bare_head (HP : HeadPar) :
    MarkDoor (fun s => .ok s) fun _ t => headOpenQ HP t :=
  ⟨fun s t e => by cases e; rfl, fun _ t' s' e hm => by
    rw [(VerifiableInference.Desc.First.K2.headOpenOpens HP t' s' e).2.2]
    exact hm⟩

theorem door_bare_link : MarkDoor (fun s => .ok s) fun (_ : S) t => .ok t :=
  ⟨fun s t e => by cases e; rfl, fun _ t' s' e hm => by cases e; exact hm⟩

theorem door_bare_finish : MarkDoor finishFrontQ fun _ t => finishBehindQ t :=
  ⟨fun s t e => (VerifiableInference.Desc.First.K2.finishFrontQ_rest e).2.2.2.1,
    fun _ t' s' e hm => by
      obtain ⟨a, m, _, _, rfl⟩ := (VerifiableInference.Desc.First.K2.finishBehindQ_iff t' s').1 e
      exact hm⟩

/-- **first**, at 1 ≤ l < 24. -/
theorem share_firstR {Fk : Nat → S → Prop} {Z : ProofFile.Pub} {G₀ : ProofFile.Ground} {l : Nat} (h1 : 1 ≤ l)
    (h24 : l < 24)
    {b b' : Block S Cl} (hlot : ∃ L ∈ ProofFile.onlineFirstChainBlockTables Z, b' ∈ L.blocks G₀)
    (hpl : b'.place = { chain := 1, link := some l, piece := 1, kind := .K2 })
    (hJ : Joined Z l b b' { chain := 1, link := some l, piece := 1, kind := .K2 })
    {X : OnBytes.Model.Stages.LinkH} (hX : Z.p.built.links[l]? = some X) (hk : X.kind ≠ 2)
    (hsort : (X.kind = 0 → subW l = .layers) ∧ (X.kind = 1 → subW l = .attention))
    {N : Numbers} {E : Nat → S → Bool} {ft : Nat}
    (hgrp : ∀ P n, prepOf Z G₀ = some P → numsAt P (some l) = some n → N.groupAt l = n.grp)
    (D : ∀ P n (s : S) x W lay, prepOf Z G₀ = some P → numsAt P (some l) = some n →
      Fk (14 * l + 2) s → XK N linksW placesW E (14 * l + 2) s = true →
      firstFront s.st s.check.frame = .ok x → frameAt x = some W →
      OnBytes.layTrees x.st.codes (switchNotices x.T x.others) = some lay →
      LinkDebts N l placesW[14 * l + 2]? placesW[14 * l + 3]? s n.positions x W lay)
    (more : ∀ s s', Fk (14 * l + 2) s → Yes ft b s s' → s.failed = none → s'.failed = none →
      XK N linksW placesW E (14 * l + 2) s = true → E (14 * l + 2 + 1) s' = true) :
    HandsR Fk N linksW placesW E ft (14 * l + 2) b := by
  obtain ⟨L, hL, hb'⟩ := hlot
  obtain ⟨x, hx, rfl⟩ := IM.lot_K2 hL hb' (by rw [hpl])
  have hi := IM.k2_mem hx
  rw [show x.place = _ from hpl] at hi
  rcases hi with ⟨_, hm⟩ | hd
  · refine (hands_of_never fun s s' hy => ?_).fenced
    obtain ⟨rs, cols, n, e⟩ := hy
    obtain ⟨fs, f, m, _, _, e3, _⟩ := hJ.step e
    exact never_of_mute hm s m ⟨rs, cols, n, e3⟩
  · obtain ⟨fs, f, hfs, hf, hSJ⟩ := sits_of_joined hJ (fun e => by cases e) rfl hd
    exact hands_at_linkR h1 h24 hfs hf hX hk hsort (sitsJoined_keeps hfs hf hSJ) hgrp D more

/-- first, without a fence. -/
theorem share_first {Z : ProofFile.Pub} {G₀ : ProofFile.Ground} {l : Nat} (h1 : 1 ≤ l) (h24 : l < 24)
    {b b' : Block S Cl} (hlot : ∃ L ∈ ProofFile.onlineFirstChainBlockTables Z, b' ∈ L.blocks G₀)
    (hpl : b'.place = { chain := 1, link := some l, piece := 1, kind := .K2 })
    (hJ : Joined Z l b b' { chain := 1, link := some l, piece := 1, kind := .K2 })
    {X : OnBytes.Model.Stages.LinkH} (hX : Z.p.built.links[l]? = some X) (hk : X.kind ≠ 2)
    (hsort : (X.kind = 0 → subW l = .layers) ∧ (X.kind = 1 → subW l = .attention))
    {N : Numbers} {E : Nat → S → Bool} {ft : Nat}
    (hgrp : ∀ P n, prepOf Z G₀ = some P → numsAt P (some l) = some n → N.groupAt l = n.grp)
    (D : ∀ P n (s : S) x W lay, prepOf Z G₀ = some P → numsAt P (some l) = some n →
      XK N linksW placesW E (14 * l + 2) s = true →
      firstFront s.st s.check.frame = .ok x → frameAt x = some W →
      OnBytes.layTrees x.st.codes (switchNotices x.T x.others) = some lay →
      LinkDebts N l placesW[14 * l + 2]? placesW[14 * l + 3]? s n.positions x W lay)
    (more : ∀ s s', Yes ft b s s' → s.failed = none → s'.failed = none →
      XK N linksW placesW E (14 * l + 2) s = true → E (14 * l + 2 + 1) s' = true) :
    Hands N linksW placesW E ft (14 * l + 2) b :=
  (share_firstR (Fk := fun _ _ => True) h1 h24 hlot hpl hJ hX hk hsort hgrp
    (fun P n s x W lay a b _ => D P n s x W lay a b) fun s s' _ => more s s').free

/-- **hear**, at l = 24, i = 1: the lot's own sub-protocol at «H:2». -/
theorem share_hearR {Fk : Nat → S → Prop} {Z : ProofFile.Pub} {G₀ : ProofFile.Ground} {b' : Block S Cl}
    (hlot : ∃ L ∈ ProofFile.onlineFirstChainBlockTables Z, b' ∈ L.blocks G₀)
    (hpl : b'.place = { chain := 1, link := some 24, piece := 2, kind := .K2 })
    (hl24 : ∀ HP, pureLetters G₀ 24 = some HP → HP.l = 24)
    {N : Numbers} {E : Nat → S → Bool} {ft : Nat}
    (hgrp : ∀ P n, prepOf Z G₀ = some P → numsAt P (some 24) = some n → N.groupAt 24 = n.grp)
    (fresh : ∀ s, Fk 339 s → XK N linksW placesW E 339 s = true → HeadFresh s)
    (D : ∀ nm P n (s : S) x W lay, prepOf Z G₀ = some P → numsAt P (some 24) = some n →
      Fk 339 s → XK N linksW placesW E 339 s = true →
      frontAt (k2P Z { chain := 1, link := some 24, piece := 2, kind := .K2 } nm .head n) s =
        some x → frameAt x = some W →
      OnBytes.layTrees x.st.codes (switchNotices x.T x.others) = some lay →
      SwitchDebts N 24 placesW[339]? placesW[339 + 1]? s.book.trees.size n.positions
        (1 + x.T.kept.size + x.own.length) x W lay)
    (more : ∀ s s', Fk 339 s → Yes ft b' s s' → s.failed = none → s'.failed = none →
      XK N linksW placesW E 339 s = true → E (339 + 1) s' = true) :
    HandsR Fk N linksW placesW E ft 339 b' := by
  obtain ⟨L, hL, hb'⟩ := hlot
  obtain ⟨x, hx, rfl⟩ := IM.lot_K2 hL hb' (by rw [hpl])
  have hi := IM.k2_mem hx
  rw [show x.place = _ from hpl] at hi
  rcases hi with ⟨_, hm⟩ | ⟨P, n, hP, hn, hA⟩
  · exact (hands_of_never (never_of_mute hm)).fenced
  · rcases hA with ⟨h0, _⟩ | ⟨l, HP, hl, hHP, hx'⟩ | ⟨l, _, hx'⟩
    · cases h0
    · obtain rfl : 24 = l := Option.some.inj hl
      have hS := sits_under_head x.name
        { chain := 1, link := some 24, piece := 2, kind := .K2 }
        (k2P Z { chain := 1, link := some 24, piece := 2, kind := .K2 } x.name .head n) HP
      rw [← hx'] at hS
      exact hands_head_ofR (HP := HP) rfl hS (door_bare_head HP) (fun _ _ _ e => e) (hl24 HP hHP)
        (hgrp P n hP hn) fresh (fun s y W lay => D x.name P n s y W lay hP hn) more
    · have hS := sits_under_link x.name
        { chain := 1, link := some 24, piece := 2, kind := .K2 }
        (k2P Z { chain := 1, link := some 24, piece := 2, kind := .K2 } x.name .link n)
      rw [← hx'] at hS
      exact (hands_head_other rfl hS door_bare_link).fenced

/-- hear, without a fence. -/
theorem share_hear {Z : ProofFile.Pub} {G₀ : ProofFile.Ground} {b' : Block S Cl}
    (hlot : ∃ L ∈ ProofFile.onlineFirstChainBlockTables Z, b' ∈ L.blocks G₀)
    (hpl : b'.place = { chain := 1, link := some 24, piece := 2, kind := .K2 })
    (hl24 : ∀ HP, pureLetters G₀ 24 = some HP → HP.l = 24)
    {N : Numbers} {E : Nat → S → Bool} {ft : Nat}
    (hgrp : ∀ P n, prepOf Z G₀ = some P → numsAt P (some 24) = some n → N.groupAt 24 = n.grp)
    (fresh : ∀ s, XK N linksW placesW E 339 s = true → HeadFresh s)
    (D : ∀ nm P n (s : S) x W lay, prepOf Z G₀ = some P → numsAt P (some 24) = some n →
      XK N linksW placesW E 339 s = true →
      frontAt (k2P Z { chain := 1, link := some 24, piece := 2, kind := .K2 } nm .head n) s =
        some x → frameAt x = some W →
      OnBytes.layTrees x.st.codes (switchNotices x.T x.others) = some lay →
      SwitchDebts N 24 placesW[339]? placesW[339 + 1]? s.book.trees.size n.positions
        (1 + x.T.kept.size + x.own.length) x W lay)
    (more : ∀ s s', Yes ft b' s s' → s.failed = none → s'.failed = none →
      XK N linksW placesW E 339 s = true → E (339 + 1) s' = true) :
    Hands N linksW placesW E ft 339 b' :=
  (share_hearR (Fk := fun _ _ => True) hlot hpl hl24 hgrp (fun s _ => fresh s)
    (fun nm P n s x W lay a b _ => D nm P n s x W lay a b) fun s s' _ => more s s').free

/-- **back**, at j = 0: the lot's own sub-protocol at «F:1». -/
theorem share_backR {Fk : Nat → S → Prop} {Z : ProofFile.Pub} {G₀ : ProofFile.Ground} {b' : Block S Cl}
    (hlot : ∃ L ∈ ProofFile.onlineFirstChainBlockTables Z, b' ∈ L.blocks G₀)
    (hpl : b'.place = { chain := 1, link := none, piece := 1, kind := .K2 })
    {N : Numbers} {E : Nat → S → Bool} {ft : Nat}
    (hgrp : ∀ P n, prepOf Z G₀ = some P → numsAt P none = some n → N.groupAt 25 = n.grp)
    (D : ∀ nm P n (s t : S) x W lay, prepOf Z G₀ = some P → numsAt P none = some n →
      Fk 353 s → XK N linksW placesW E 353 s = true → finishFrontQ s = .ok t →
      frontAt (k2P Z IM.k2PlaceF nm .finish n) t = some x → frameAt x = some W →
      OnBytes.layTrees x.st.codes (switchNotices x.T x.others) = some lay →
      SwitchDebts N 25 placesW[353]? placesW[353 + 1]? s.book.trees.size n.positions
        (1 + x.T.kept.size) x W lay)
    (more : ∀ s s', Fk 353 s → Yes ft b' s s' → s.failed = none → s'.failed = none →
      XK N linksW placesW E 353 s = true → E (353 + 1) s' = true) :
    HandsR Fk N linksW placesW E ft 353 b' := by
  obtain ⟨L, hL, hb'⟩ := hlot
  obtain ⟨x, hx, rfl⟩ := IM.lot_K2 hL hb' (by rw [hpl])
  have hi := IM.k2_mem hx
  rw [show x.place = _ from hpl] at hi
  rcases hi with ⟨_, hm⟩ | ⟨P, n, hP, hn, hA⟩
  · exact (hands_of_never (never_of_mute hm)).fenced
  · rcases hA with ⟨_, hx'⟩ | ⟨l, HP, hl, _⟩ | ⟨l, hl, _⟩
    · have hS := sits_under_finish x.name IM.k2PlaceF (k2P Z IM.k2PlaceF x.name .finish n)
      rw [← hx'] at hS
      exact hands_finish_ofR rfl hS door_bare_finish (fun _ _ _ e => e) (hgrp P n hP hn)
        (fun s t y W lay => D x.name P n s t y W lay hP hn) more
    · cases hl
    · cases hl

/-- back, without a fence. -/
theorem share_back {Z : ProofFile.Pub} {G₀ : ProofFile.Ground} {b' : Block S Cl}
    (hlot : ∃ L ∈ ProofFile.onlineFirstChainBlockTables Z, b' ∈ L.blocks G₀)
    (hpl : b'.place = { chain := 1, link := none, piece := 1, kind := .K2 })
    {N : Numbers} {E : Nat → S → Bool} {ft : Nat}
    (hgrp : ∀ P n, prepOf Z G₀ = some P → numsAt P none = some n → N.groupAt 25 = n.grp)
    (D : ∀ nm P n (s t : S) x W lay, prepOf Z G₀ = some P → numsAt P none = some n →
      XK N linksW placesW E 353 s = true → finishFrontQ s = .ok t →
      frontAt (k2P Z IM.k2PlaceF nm .finish n) t = some x → frameAt x = some W →
      OnBytes.layTrees x.st.codes (switchNotices x.T x.others) = some lay →
      SwitchDebts N 25 placesW[353]? placesW[353 + 1]? s.book.trees.size n.positions
        (1 + x.T.kept.size) x W lay)
    (more : ∀ s s', Yes ft b' s s' → s.failed = none → s'.failed = none →
      XK N linksW placesW E 353 s = true → E (353 + 1) s' = true) :
    Hands N linksW placesW E ft 353 b' :=
  (share_backR (Fk := fun _ _ => True) hlot hpl hgrp
    (fun nm P n s t x W lay a b _ => D nm P n s t x W lay a b) fun s s' _ => more s s').free

end P1K2

#print axioms P1K2.share_firstR
#print axioms P1K2.share_hearR
#print axioms P1K2.share_backR
#print axioms P1K2.share_first
#print axioms P1K2.share_hear
#print axioms P1K2.share_back
