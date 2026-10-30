-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K9/XkFront.lean: BETWEEN THE PROMISE's SIX Bools AT A MEANING's OWN LETTERS AND THE FIVE
AT THE LIBRARY's WRITTEN LIST: the library's `IM.XK` at the test `P1K2.EQ` ("in order" and the public items' test)
against `IM.XK` at the public test alone (`ePubAt`; at the written list: `LPFK9.HandsAt.EW`), at one border and one
state. No thread, no head. Three statements and their proofs; no goal is stated.
  `xk_five_of_six`   all letters free: `IM.XK N links ps (P1K2.EQ Mg links ps z) k s = true` ⊢ `IM.XK N links ps (fun
      k s => ePubAt Mg.pub Mg.more links ps k (z, s)) k s = true`
  **`xk_ew_of_eq`**   under FOUR EQUATIONS ON THE LETTERS (Mg.pub = pubAll D base · Mg.more = moreAll · IM.linksW =
      links · IM.placesW = ps): the six at Mg's letters ⊢ `IM.XK N IM.linksW IM.placesW (EW D base z) k s = true`:
      what Honest/K9/XkBat.lean, XkClose.lean and XkAtHead.lean take in front
  **`ew_gives_pub`**   under the same four: `EW D base z k s = true` ⊢ `ePubAt Mg.pub Mg.more links ps k (z, s) =
      true`: the premise hE of the frame's `xk_eq_of_pub` | `head_xk_of_pub`, which lead back to the six, once the
      caller has turned XK's own two lists by the same hl · hp
THE FOUR EQUATIONS stand in the direction in which the frame says them of its letters at the library's head
(its `head_pub_all`, `head_more_all`, `head_links_W`, `head_ps_W`: not laid here). That N is
`P5J.At.N Zp cF` there is its `head_xk_is`.
WHAT IS NOT CLAIMED. XK at any state. Any of the four equations at any letters. "In order" at any state (the frame's
`xk_eq_of_pub` asks it). `samplesHeld`. pubP. No member: `xk_five_of_six` is called by `xk_ew_of_eq`; the two others
by no line. Nothing on any property.
-/
import Johnson.P1K2R.TieTwo
import Johnson.Desc.First.EPubAt
import Johnson.LPFK9R.SharesAtE

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K9
open VerifiableInference.Desc (Place)
open VerifiableInference.Desc.First (S ModelPart Numbers Meaning PubData pubAll ePubAt)
open VerifiableInference.Desc.Sound (moreAll)
open LPFK9.HandsAt (EW)

/-- The six give the five. -/
theorem xk_five_of_six {P W : Type} {N : Numbers} {Mg : Meaning P W} {links : List ModelPart} {ps : List Place} {z : P}
    {k : Nat} {s : S} (hx : IM.XK N links ps (P1K2.EQ Mg links ps z) k s = true) :
    IM.XK N links ps (fun k s => ePubAt Mg.pub Mg.more links ps k (z, s)) k s = true := by
  obtain ⟨c1, c2, c3, c4, c5⟩ := IM.xk_parts hx
  unfold P1K2.EQ at c5
  rw [Bool.and_eq_true] at c5
  have hp : ePubAt Mg.pub Mg.more links ps k (z, s) = true := c5.2
  unfold IM.XK IM.BK
  rw [c1, c2, c3, c4]
  exact hp

/-- **From the six at a meaning's own letters to the five at `EW`**, under four equations on the letters. -/
theorem xk_ew_of_eq {P W : Type} {N : Numbers} {Mg : Meaning P W} {links : List ModelPart} {ps : List Place} {z : P}
    {D : PubData} {base : VerifiableInference.Desc.First.Pub → P × S → Bool} (hpub : Mg.pub = pubAll D base)
    (hmore : Mg.more = moreAll) (hl : IM.linksW = links) (hp : IM.placesW = ps) {k : Nat} {s : S}
    (hx : IM.XK N links ps (P1K2.EQ Mg links ps z) k s = true) :
    IM.XK N IM.linksW IM.placesW (EW D base z) k s = true := by
  subst hl hp
  have h5 := xk_five_of_six hx
  rw [hpub, hmore] at h5
  exact h5

/-- **The way back at the test itself**, under the same four. -/
theorem ew_gives_pub {P W : Type} {Mg : Meaning P W} {links : List ModelPart} {ps : List Place} {z : P} {D : PubData}
    {base : VerifiableInference.Desc.First.Pub → P × S → Bool} (hpub : Mg.pub = pubAll D base)
    (hmore : Mg.more = moreAll) (hl : IM.linksW = links) (hp : IM.placesW = ps) {k : Nat} {s : S}
    (he : EW D base z k s = true) :
    ePubAt Mg.pub Mg.more links ps k (z, s) = true := by
  subst hl hp
  rw [hpub, hmore]
  exact he

end ProofFile.Honest.K9

#print axioms ProofFile.Honest.K9.xk_five_of_six
#print axioms ProofFile.Honest.K9.xk_ew_of_eq
#print axioms ProofFile.Honest.K9.ew_gives_pub
