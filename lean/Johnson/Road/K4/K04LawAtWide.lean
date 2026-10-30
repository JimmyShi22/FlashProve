-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/K04LawAtWide.lean: THE KIND K4's SHARE OF THE CHAIN OF PROMISES, IN THE SECOND FORM,
AT THE COMPOSED MEANING `mgAll 𝔇 Mg`, OUT OF THE SHARE IN THE FIRST FORM AT THE WIDER MEANING
`mgWide 𝔇 E Mg`. One statement with its proof: one call of `k04_tiedR_of_wide` (K04LawWide.lean) at
the terms of `mgWide`'s own text (below). No new argument. IT PAYS NOTHING.

`mgWide 𝔇 E Mg` (Johnson/Desc/Sound/MgWide.lean) is, by its text, `widen (mgAll 𝔇
Mg) (moreW 𝔇 Mg) (pubWide …) (ioWide 𝔇 E Mg)`: the composed meaning with the thirteen names that
left its door laid over it again, each at its own authors' test. It is no
reference form: it is one side of a bridge: a law shown at it counts only when the bridge is paid.

  `k04_kindTiedR_mgAll`: from `KindTied N (mgWide 𝔇 E Mg) linksFull (flatPlacesOf linksFull true) Ex
    l KindName.K4`: `KindTiedR N (mgAll 𝔇 Mg) linksFull (flatPlacesOf linksFull true) Rch Ex l
    KindName.K4`. OF THE BRIDGE's PREMISES TWO ARE CONCLUDED HERE, by MgWide.lean's `mgWide_hand`
    and `mgWide_io`. THREE STAY: hD, the test on the two doors at the borders 28 g + 4 and 28 g + 5;
    hF, the facts of the class wherever Rch holds, AT THESE TWENTY-FOUR BORDERS ALONE;
    hs, an accepting run of the piece hands Rch on.

Limits. hD: evaluated true by a run at all 359 borders of the written list, at
`mgBase`'s closed doors, with two negative tests: NOT BY THE KERNEL, and not called here. hF ASKS,
AT THESE BORDERS, EVERY NAME OF THE CLASS THAT IS OPEN AT THE WIDER DOOR THERE, NOT ONLY WHAT K4
SPENDS, AND THE WIDER "IN ORDER" WHOLE: most of it is owed. hs has a lemma general in the kind
(`handsOn_map`, Johnson/Top/H0/Walk/ReachHands.lean: its statement read; not called here). THE
PREMISE H, K4's SHARE AT THE WIDER MEANING, IS WHAT `k04_law_of` ENDS IN, UNDER BINDERS OF WHICH NO
MEMBER IS SHOWN AT ANY MEANING. Rch is a letter: at «never» every tie is free. Nothing on soundness.

-/
import Johnson.Road.K4.K04LawWide
import Johnson.Desc.Sound.MgWide

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Road.K4
open _root_.Run.PQ (CK)
open VerifiableInference.Desc (KindName Wit)
open VerifiableInference.Desc.First (S Meaning Numbers flatPlacesOf classA pubWide)
open VerifiableInference.Desc.Sound

/-- **K4's share at the composed meaning, in the second form, out of its share at the wider
meaning.** -/
theorem k04_kindTiedR_mgAll {Xi P Tok Cl : Type} {rows cols nR : ℕ}
    {X : OnBytes.Model.Verify.Public} {C : CK} {Fr : Frame}
    (𝔇 : MgData Xi P Tok rows cols nR X) (E : WideData P)
    (Mg : Meaning P (Wit (CellsQ rows cols) Tok MsgT)) (N : Numbers)
    (Rch : ℕ → (P × S) × Fr.E.Str → Prop)
    (Ex : ℕ → (P × S) × Fr.E.Str → (P × S) × Fr.E.Str → Wit (CellsQ rows cols) Tok MsgT →
      Wit (CellsQ rows cols) Tok MsgT)
    (l : List (Piece C Fr (P × S) Cl (Wit (CellsQ rows cols) Tok MsgT)))
    (H : KindTied N (mgWide 𝔇 E Mg) linksFull (flatPlacesOf linksFull true) Ex l KindName.K4)
    (hD : ∀ g, g < 12 →
      doorsFitB (mgAll 𝔇 Mg).more (moreW 𝔇 Mg) classA linksFull (flatPlacesOf linksFull true)
          (28 * g + 4) = true ∧
        doorsFitB (mgAll 𝔇 Mg).more (moreW 𝔇 Mg) classA linksFull (flatPlacesOf linksFull true)
          (28 * g + 4 + 1) = true)
    (hF : ∀ g, g < 12 →
      (∀ a, Rch (28 * g + 4) a →
        FactsAt (mgAll 𝔇 Mg) (moreW 𝔇 Mg) (pubWide E.d12 E.dP 𝔇.pubD Mg.pub) (ioWide 𝔇 E Mg)
          classA linksFull (flatPlacesOf linksFull true) (fun a => a) (28 * g + 4) a) ∧
        ∀ b, Rch (28 * g + 4 + 1) b →
          FactsAt (mgAll 𝔇 Mg) (moreW 𝔇 Mg) (pubWide E.d12 E.dP 𝔇.pubD Mg.pub) (ioWide 𝔇 E Mg)
            classA linksFull (flatPlacesOf linksFull true) (fun a => a) (28 * g + 4 + 1) b)
    (hs : ∀ g, g < 12 → ∀ q, l[28 * g + 4]? = some q →
      HandsOn Rch (28 * g + 4) (q.withMap (Ex (28 * g + 4)))) :
    KindTiedR N (mgAll 𝔇 Mg) linksFull (flatPlacesOf linksFull true) Rch Ex l KindName.K4 :=
  k04_tiedR_of_wide N (mgAll 𝔇 Mg) (moreW 𝔇 Mg) (pubWide E.d12 E.dP 𝔇.pubD Mg.pub)
    (ioWide 𝔇 E Mg) classA Rch Ex l H (mgWide_hand 𝔇 E Mg) (mgWide_io 𝔇 E Mg) hD hF hs

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.k04_kindTiedR_mgAll
