-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P1K2R/SharesScope.lean: code switching (K2): ITS SHARES OF e₁ AT THE SHEET's KEY
(Johnson/P1K2R/SharesAtE.lean) WITH FOUR SMALL PREMISES ON THE PLAN TAKEN AWAY. NO BLOCK IMPORTS
THIS FILE.
  letters_l       the head's link's letters off the public values bear the link's own number (by
                  P1K2.pureLetters' text): share_hearP's hl24
  kinds_of_subs   where the driver's list of segments has the written list's sort at l < 24: the
                  plan's link number l is there, is not the head's kind, and its kind is the
                  written sort: share_firstP's hX · hk · hsort
  subs_W          IN SCOPE the driver's list has the written sort at every l < 24
                  (subs_at | subs_att, called)
  share_hearQ     share_hearP without hl24
  share_firstQ    share_firstP with hsub : (ProofFile.subsOf Z)[l]? = some (subW l) in the place of hX ·
                  hk · hsort
LIMITS. The other premises stay as they are. No soundness is claimed.
-/
import Johnson.P1K2R.SharesAtE
import Johnson.IMR.Subs

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace P1K2
open VerifiableInference.Desc (Block Place OpenedColumn KindName)
open VerifiableInference.Desc.First (S ModelPart Numbers Pub PubData pubAll)
open VerifiableInference.Desc.First.K2 (HeadPar LinkDebts SwitchDebts HeadFresh frontAt frameAt)
open ProofFile (Cl)
open IM (HandsR XK Yes linksW placesW subW k2P Joined)
open _root_.Tw.K2 (firstFront switchNotices)

theorem letters_l {G : ProofFile.Ground} {l : Nat} {HP : HeadPar} (h : pureLetters G l = some HP) :
    HP.l = l := by
  unfold pureLetters at h
  obtain ⟨X, _, rfl⟩ := Option.map_eq_some_iff.1 h
  rfl

theorem kinds_of_subs {Z : ProofFile.Pub} {l : Nat} (h24 : l < 24)
    (h : (ProofFile.subsOf Z)[l]? = some (subW l)) :
    ∃ X, Z.p.built.links[l]? = some X ∧ X.kind ≠ 2 ∧
      (X.kind = 0 → subW l = .layers) ∧ (X.kind = 1 → subW l = .attention) := by
  unfold ProofFile.subsOf at h
  rw [List.getElem?_map, Array.getElem?_toList] at h
  obtain ⟨X, hX, e⟩ := Option.map_eq_some_iff.1 h
  refine ⟨X, hX, fun h2 => ?_, fun h0 => ?_, fun h1 => ?_⟩
  · rw [h2] at e
    have e' : ModelPart.head = subW l := e
    unfold subW at e'
    rw [if_neg (by omega)] at e'
    split at e' <;> cases e'
  · rw [h0] at e
    exact e.symm
  · rw [h1] at e
    exact e.symm

theorem subs_W {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {Z : ProofFile.Pub}
    {G₀ : ProofFile.Ground} (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (hZ : ProofFile.pubPlain OnBytes.secondHashFunction P.pol lay P.KL = .ok Z)
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Z = some G₀) {l : Nat} (h24 : l < 24) :
    (ProofFile.subsOf Z)[l]? = some (subW l) := by
  unfold subW
  rw [if_neg (by omega)]
  by_cases he : l % 2 = 0
  · rw [if_pos he]
    have e : l = 2 * (l / 2) := by omega
    rw [e]
    exact IM.subs_at hS hR hZ hG (by omega)
  · rw [if_neg he]
    have e : l = 2 * (l / 2) + 1 := by omega
    rw [e]
    exact IM.subs_att hS hR hZ hG (by omega)

variable {P : Type}

theorem share_hearQ {Fk : Nat → S → Prop} {Z : ProofFile.Pub} {G₀ : ProofFile.Ground} {b' : Block S Cl}
    (hlot : ∃ L ∈ ProofFile.onlineFirstChainBlockTables Z, b' ∈ L.blocks G₀)
    (hpl : b'.place = { chain := 1, link := some 24, piece := 2, kind := .K2 })
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
  share_hearP hlot hpl (fun _ h => letters_l h) D₀ base z hgrp fresh D htok hMade

theorem share_firstQ {Fk : Nat → S → Prop} {Z : ProofFile.Pub} {G₀ : ProofFile.Ground} {l : Nat}
    (h1 : 1 ≤ l) (h24 : l < 24)
    {b b' : Block S Cl} (hlot : ∃ L ∈ ProofFile.onlineFirstChainBlockTables Z, b' ∈ L.blocks G₀)
    (hpl : b'.place = { chain := 1, link := some l, piece := 1, kind := .K2 })
    (hJ : Joined Z l b b' { chain := 1, link := some l, piece := 1, kind := .K2 })
    (hsub : (ProofFile.subsOf Z)[l]? = some (subW l))
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
    HandsR Fk N linksW placesW (EP D₀ base z) ft (14 * l + 2) b := by
  obtain ⟨X, hX, hk, hsort⟩ := kinds_of_subs h24 hsub
  exact share_firstP h1 h24 hlot hpl hJ hX hk hsort D₀ base z hgrp D hMade

end P1K2

#print axioms P1K2.letters_l
#print axioms P1K2.kinds_of_subs
#print axioms P1K2.subs_W
#print axioms P1K2.share_hearQ
#print axioms P1K2.share_firstQ
