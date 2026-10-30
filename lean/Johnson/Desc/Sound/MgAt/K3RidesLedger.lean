-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
ridesAtR_calls_ledger: no parameters Dm are shown here that meet its
premises.
Johnson/Desc/Sound/MgAt/K3RidesLedger.lean: the kind "lookup" (K3) AT THE COMPOSED MEANING mgAll:
WHAT RIDES PAST A SEATED LOOKUP ON A LINK's CALLS, SECOND FORM, UNDER THE KIND's LEDGER's OWN
SENTENCES ON Dm (K3OwedR's es, hD, hd: Johnson/Desc/Sound/MgAt/K3Owed.lean): three of the five
premises on Dm's letters of ridesAtR_calls_mgAll (Johnson/Desc/Sound/MgAt/K3Rides.lean) are paid
by them. One theorem: a joining. No error term. NO SOUNDNESS IS CLAIMED.

HOW. hDec: the ledger's hd says that Dm.decT reads the public part alone · hSmp: the ledger's es
says that Dm.smp is smpNamed, which reads the statement alone · hDig: the ledger's hD says that
Dm.digitsPart is digitsPartK3, which reads neither the state nor the strings.
WHAT IS LEFT ON Dm: hReq (Dm.H.req gives one thing at two states that are SameBut) · hHead
(Dm.headPart p i goes back).

OBJECT: the composed meaning's fields; RidesAtR.
Used by K03RidesAt.lean (Johnson/P5J/) and K3RidesLed.lean (Johnson/Desc/Sound/MgAt/).
LETTERS: Dm, Mg, seats; Rch, k, q, b', a.
IMPORTS:
  Johnson/Desc/Sound/MgAt/K3Rides.lean;
  Johnson/Desc/Sound/SmpNamed.lean;
  Johnson/Desc/First/Look/K3FillDigits.lean.
  Compiled with the whole library.
Limits. At the calls alone.
Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Desc.Sound.MgAt.K3Rides
import Johnson.Desc.Sound.SmpNamed
import Johnson.Desc.First.Look.K3FillDigits

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace VerifiableInference.Desc.Sound
open OnBytes.Maker Cb Johnson.Pack OnBytes.Slice Fo.Peel
open _root_.Run (ckP)
open VerifiableInference.Desc.First (ModelPart Item Meaning Numbers start flatPlacesOf)
open VerifiableInference.OnPublicFiles (SameBut relOf RidesAtR digitsPartK3)

section
variable {Xi P Tok : Type} {rows cols nR : ℕ} {X : OnBytes.Model.Verify.Public}
variable (Dm : MgData Xi P Tok rows cols nR X) (Mg : Meaning P (Wit (CellsQ rows cols) Tok MsgT))

/-- **WHAT RIDES PAST A LOOKUP ON THE CALLS, UNDER THE LEDGER's OWN SENTENCES ON Dm.** -/
theorem ridesAtR_calls_ledger {Cl : Type} {Fr : Frame} (seats : List (ℕ × ℕ))
    (es : Dm.smp = smpNamed Dm.cs seats) (hD : Dm.digitsPart = digitsPartK3 X Dm.sent Dm.l3)
    (hd : ∀ c (y y' : P × First.S), y'.1 = y.1 → Dm.decT c y' = Dm.decT c y)
    (Rch : ℕ → (P × First.S) × Fr.E.Str → Prop) (k : ℕ)
    (q : Piece (ckP .two) Fr (P × First.S) Cl (Wit (CellsQ rows cols) Tok MsgT))
    (b' : Block First.S Cl) {a : Place}
    (ha : (flatPlacesOf linksFull true)[k]? = some a) (hK : a.kind = .K3) (hp : a.piece ≤ 3)
    (hback : q.back = [])
    (hRel : ∀ B', SeatOf b' B' → ∀ u τ v,
      (⟨below B', q.base, q.ds, q.back, fun _ _ w => w, q.err⟩ :
        Piece (ckP .two) Fr First.S Cl (Wit (CellsQ rows cols) Tok MsgT)).ior.red.out u τ =
          some v → SameBut u.1 v.1)
    (hj : Dm.N.index.1 < q.base)
    (hReq : ∀ (z : P) s s', SameBut s s' → Dm.H.req (z, s) = Dm.H.req (z, s'))
    (hHead : ∀ p i, GoesBack (relOf SameBut q.base) (Dm.headPart p i)) :
    RidesAtR Dm.N (mgAll Dm Mg) Rch k q b' :=
  ridesAtR_calls_mgAll Dm Mg (fun c z s s' _ => hd c (z, s') (z, s) rfl) Rch k q b' ha hK hp hback
    hRel hj
    (fun z s s' hs x _ _ => by
      rw [es]
      unfold smpNamed
      rw [hs.st])
    hReq
    (fun m => by
      rw [hD]
      exact fun _ _ _ _ _ _ h => h)
    hHead

end

end VerifiableInference.Desc.Sound

#print axioms VerifiableInference.Desc.Sound.ridesAtR_calls_ledger
