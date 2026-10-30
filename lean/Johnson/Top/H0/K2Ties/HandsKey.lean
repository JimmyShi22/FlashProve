-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/K2Ties/HandsKey.lean: the code switch (K2): THE FIELD hHands OF ITS CONDITION
(Johnson/P1K2R/Shorter.lean: «the table's tests along the fold, at this sub-protocol», IM.HandsR) IN
THE FIELD's OWN LETTERS, AT EACH OF THE 25 PLACES, FROM OUR THREE SHARES. A file beneath the
condition. A law file; no running text imports it.

The knot. The field's key is EQ (mgAll 𝔇 mgBase) links ps z (Johnson/P1K2R/TieTwo.lean): «in order»
and the promise's public test at the one term. The shares end at the key EP D₀ base z
(Johnson/P1K2R/SharesAtE.lean): the public test alone, at letters D₀, base. No file tied the two.

  noPub           the closed meaning beneath's public test (it rejects all): mgBase.pub.
  eq_is_ep        EQ (mgAll 𝔇 mgBase) linksW placesW z k s =
                  ((Meaning.backReq (𝔇.reqB z)).isSome && EP 𝔇.pubD noPub z k s). By four facts that
                  lie: mgAll_pub · mgAll_more_base with mgMore_is · mgAll_inOrder_base («in order»
                  at the one term is a test on the public part alone) · ePubAt's text.
  HandsR.key      free of any kind: where E' k s = (c && E k s) with one Bool c that no state turns,
                  HandsR at the key E gives HandsR at the key E'.
  hands_at_key    so: HandsR at EP 𝔇.pubD noPub z gives HandsR at the field's key.
  hHands_link     at k = 14 l + 2, 1 ≤ l < 24 (23 places) · hHands_head at 339 · hHands_fin at 353:
                  one call of a share each (share_firstX, share_hearX:
                  Johnson/P1K2R/FencesReached.lean · share_backP: SharesAtE.lean) at D₀ := 𝔇.pubD,
                  base := noPub. The field is «∀ z, … (Fk z) …»: take Fk := Fk z.
WHAT STAYS IN FRONT IS WHAT THE SHARES LEAVE, TO THE LETTER, at D₀ := 𝔇.pubD: link: hFk (under the
fence the state is reached) · hlot hpl hJ · LinkPlan · K5Plan, hμc (at attention's segments) · hD5 ·
hgrp · Dd (LinkDebts) · hdS ‖ head: hFk · hlot hpl · HeadPlan · hgrp · fresh · D (SwitchDebts) ·
htok · hU · hdS · hFp ‖ finish: hlot hpl · hgrp · D. NONE OF THESE IS PAID HERE.
Limits. At links := linksW, ps := placesW (that these are the constant's own lists is another
file's: two rewrites). The full size alone. Nothing on soundness.

-/
import Johnson.P1K2R.FencesReached
import Johnson.P1K2R.TieTwo
import Johnson.Desc.Sound.MgBase
import Johnson.Desc.Sound.MoreAll
import Johnson.Desc.First.EPubAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace IM

/-- **One Bool that no state turns, in front of the key.** -/
theorem HandsR.key {Fk : Nat → VerifiableInference.Desc.First.S → Prop}
    {N : VerifiableInference.Desc.First.Numbers} {links : List VerifiableInference.Desc.First.ModelPart}
    {ps : List VerifiableInference.Desc.Place}
    {E E' : Nat → VerifiableInference.Desc.First.S → Bool} {c : Bool} {ft k : Nat}
    {b : VerifiableInference.Desc.Block VerifiableInference.Desc.First.S ProofFile.Cl}
    (h : ∀ k s, E' k s = (c && E k s)) (H : HandsR Fk N links ps E ft k b) :
    HandsR Fk N links ps E' ft k b := by
  have hx : ∀ k s, XK N links ps E' k s = true → XK N links ps E k s = true ∧ c = true := by
    intro k s e
    unfold XK at e ⊢
    rw [h, Bool.and_eq_true, Bool.and_eq_true] at e
    exact ⟨by rw [e.1, e.2.2]; rfl, e.2.1⟩
  exact ⟨H.mark, fun s s' f y u u' e => H.shape s s' f y u u' (hx k s e).1,
    fun s s' f y u u' e => H.rows s s' f y u u' (hx k s e).1,
    fun s s' f y u u' e => H.members s s' f y u u' (hx k s e).1,
    fun s s' f y u u' e => H.book s s' f y u u' (hx k s e).1,
    fun s s' f y u u' e => by
      rw [h, (hx k s e).2, H.more s s' f y u u' (hx k s e).1]
      rfl⟩

end IM

namespace Meaning.K2
open OnBytes OnBytes.Model
open VerifiableInference.Desc
open VerifiableInference.Desc.First
open ProofFile (Cl)
open Johnson.Desc.First.Walk.Tied (Reach)
open VerifiableInference.Desc.Sound (below mgAll mgBase MgData mgAll_inOrder_base mgAll_more_base
  moreAll)
open P1K2 (LinkPlan K5Plan HeadPlan EP EQ prepOf numsAt pureLetters)
open VerifiableInference.Desc.First.K2 (LinkDebts SwitchDebts HeadFresh frontAt frameAt
  finishFrontQ)
open VerifiableInference.Desc.First.FillSent (sentDataAt)
open IM (HandsR XK Yes linksW placesW subW Joined k2P)
open _root_.Tw.K2 (firstFront switchNotices)

/-- The closed meaning beneath's public test. -/
abbrev noPub {Q : Type} : Pub → Q × S → Bool := (mgBase (P := Q) (W := Unit)).pub

variable {Xi Q Tok : Type} {rows cols nR : ℕ} {X₀ : OnBytes.Model.Verify.Public}
  (𝔇 : MgData Xi Q Tok rows cols nR X₀)

/-- **The two keys.** -/
theorem eq_is_ep (z : Q) (k : Nat) (s : S) :
    EQ (mgAll 𝔇 mgBase) linksW placesW z k s =
      ((_root_.Meaning.backReq (𝔇.reqB z)).isSome && EP 𝔇.pubD noPub z k s) := by
  unfold EQ EP P1K2.pubAt
  rw [mgAll_inOrder_base, mgAll_more_base]
  rfl

theorem hands_at_key (z : Q) {Fk : Nat → S → Prop} {N : Numbers} {ft k : Nat} {b : Block S Cl}
    (H : HandsR Fk N linksW placesW (EP 𝔇.pubD noPub z) ft k b) :
    HandsR Fk N linksW placesW (EQ (mgAll 𝔇 mgBase) linksW placesW z) ft k b :=
  HandsR.key (eq_is_ep 𝔇 z) H

variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub}
  {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl} {A : ProofFile.SharedSeat}
  {B : ProofFile.SecondSeat}

/-- **At the 23 places that open a segment's link.** -/
theorem hHands_link (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {Fk : Nat → S → Prop}
    {G₀ : ProofFile.Ground} {l : Nat} (h1 : 1 ≤ l) (h24 : l < 24)
    (hFk : ∀ s, Fk (14 * l + 2) s →
      ∃ z, Reach 0 (c.blocksInOrder.map below) (ProofFile.startS Z) (14 * l + 2) (z, s))
    {b b' : Block S Cl} (hlot : ∃ L ∈ ProofFile.onlineFirstChainBlockTables Z, b' ∈ L.blocks G₀)
    (hpl : b'.place = { chain := 1, link := some l, piece := 1, kind := .K2 })
    (hJ : Joined Z l b b' { chain := 1, link := some l, piece := 1, kind := .K2 })
    {N : Numbers} {ft : Nat} (z : Q)
    (Pl : LinkPlan Z l 𝔇.pubD) {q : Attention.Plan} {μ : Nat}
    (P5 : subW l = .attention → K5Plan Z l 𝔇.pubD N Z.first.layout q μ)
    (hD5 : 𝔇.pubD.d5.shape = Z.first.shape)
    (hμc : subW l = .attention →
      μ < (((Z.first.shape.link[l]?.map (·.messages)).getD []).filter
        fun y => y.moment == 0).length)
    (hgrp : ∀ P n, prepOf Z G₀ = some P → numsAt P (some l) = some n → N.groupAt l = n.grp)
    (Dd : ∀ P n (s : S) x W lay, prepOf Z G₀ = some P → numsAt P (some l) = some n →
      Fk (14 * l + 2) s → XK N linksW placesW (EP 𝔇.pubD noPub z) (14 * l + 2) s = true →
      firstFront s.st s.check.frame = .ok x → frameAt x = some W →
      layTrees x.st.codes (switchNotices x.T x.others) = some lay →
      LinkDebts N l placesW[14 * l + 2]? placesW[14 * l + 3]? s n.positions x W lay)
    (hdS : 𝔇.pubD.dS = sentDataAt Z.first.shape N linksW placesW Z.p.built.links) :
    HandsR Fk N linksW placesW (EQ (mgAll 𝔇 mgBase) linksW placesW z) ft (14 * l + 2) b :=
  hands_at_key 𝔇 z (share_firstX hS hR O h1 h24 hFk hlot hpl hJ 𝔇.pubD noPub z Pl P5 hD5 hμc
    hgrp Dd hdS)

/-- **At the head's place.** -/
theorem hHands_head (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {Fk : Nat → S → Prop}
    {G₀ : ProofFile.Ground}
    (hFk : ∀ s, Fk 339 s → ∃ z, Reach 0 (c.blocksInOrder.map below) (ProofFile.startS Z) 339 (z, s))
    {b' : Block S Cl} (hlot : ∃ L ∈ ProofFile.onlineFirstChainBlockTables Z, b' ∈ L.blocks G₀)
    (hpl : b'.place = { chain := 1, link := some 24, piece := 2, kind := .K2 })
    {N : Numbers} {ft : Nat} (z : Q)
    (Pl : HeadPlan G₀ 𝔇.pubD)
    (hgrp : ∀ P n, prepOf Z G₀ = some P → numsAt P (some 24) = some n → N.groupAt 24 = n.grp)
    (fresh : ∀ s, Fk 339 s → XK N linksW placesW (EP 𝔇.pubD noPub z) 339 s = true → HeadFresh s)
    (D : ∀ nm P n (s : S) x W lay, prepOf Z G₀ = some P → numsAt P (some 24) = some n →
      Fk 339 s → XK N linksW placesW (EP 𝔇.pubD noPub z) 339 s = true →
      frontAt (k2P Z { chain := 1, link := some 24, piece := 2, kind := .K2 } nm .head n) s =
        some x → frameAt x = some W →
      OnBytes.layTrees x.st.codes (switchNotices x.T x.others) = some lay →
      SwitchDebts N 24 placesW[339]? placesW[339 + 1]? s.book.trees.size n.positions
        (1 + x.T.kept.size + x.own.length) x W lay)
    (htok : ∀ s s', Fk 339 s → Yes ft b' s s' → s.failed = none → s'.failed = none →
      pubAll 𝔇.pubD noPub .tokenSmall (z, s) = true →
      pubAll 𝔇.pubD noPub .tokenSmall (z, s') = true)
    (hU : ∀ s, Fk 339 s → XK N linksW placesW (EP 𝔇.pubD noPub z) 339 s = true →
      ∀ a, s.here = .head a → a.tl.heard = none ∧ a.lookHeard = none)
    (hdS : 𝔇.pubD.dS = sentDataAt Z.first.shape N linksW placesW Z.p.built.links)
    (hFp : ∀ HP, pureLetters G₀ 24 = some HP →
      ∃ X, Z.p.built.links[24]? = some X ∧ X.Fp.trees = HP.X.Fp.trees) :
    HandsR Fk N linksW placesW (EQ (mgAll 𝔇 mgBase) linksW placesW z) ft 339 b' :=
  hands_at_key 𝔇 z (share_hearX hS hR O hFk hlot hpl 𝔇.pubD noPub z Pl hgrp fresh D htok hU hdS
    hFp)

/-- **At the finish.** -/
theorem hHands_fin {Fk : Nat → S → Prop} {Z : ProofFile.Pub} {G₀ : ProofFile.Ground} {b' : Block S Cl}
    (hlot : ∃ L ∈ ProofFile.onlineFirstChainBlockTables Z, b' ∈ L.blocks G₀)
    (hpl : b'.place = { chain := 1, link := none, piece := 1, kind := .K2 })
    {N : Numbers} {ft : Nat} (z : Q)
    (hgrp : ∀ P n, prepOf Z G₀ = some P → numsAt P none = some n → N.groupAt 25 = n.grp)
    (D : ∀ nm P n (s t : S) x W lay, prepOf Z G₀ = some P → numsAt P none = some n →
      Fk 353 s → XK N linksW placesW (EP 𝔇.pubD noPub z) 353 s = true → finishFrontQ s = .ok t →
      frontAt (k2P Z IM.k2PlaceF nm .finish n) t = some x → frameAt x = some W →
      OnBytes.layTrees x.st.codes (switchNotices x.T x.others) = some lay →
      SwitchDebts N 25 placesW[353]? placesW[353 + 1]? s.book.trees.size n.positions
        (1 + x.T.kept.size) x W lay) :
    HandsR Fk N linksW placesW (EQ (mgAll 𝔇 mgBase) linksW placesW z) ft 353 b' :=
  hands_at_key 𝔇 z (P1K2.share_backP hlot hpl 𝔇.pubD noPub z hgrp D)

end Meaning.K2

#print axioms IM.HandsR.key
#print axioms Meaning.K2.eq_is_ep
#print axioms Meaning.K2.hands_at_key
#print axioms Meaning.K2.hHands_link
#print axioms Meaning.K2.hHands_head
#print axioms Meaning.K2.hHands_fin
