-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K14/Law/LedgerSmpPaid.lean: THE LETTER Y OF THE FILLING XK, FILLED BY smpK, WITH
NOTHING OWED. Johnson/Desc/K14/Law/LedgerSmpLaid.lean has Y's six hand-ons and the content that the
last call at the seam spends, each from a statement on smpY | smpK taken as a premise.
These statements have been proved as they were typed
(Johnson/Desc/K14/Law/LedgerSmp.lean, LedgerSmpK.lean, LedgerSmpEarn.lean). HERE they are
substituted BY NAME: smpKEarly · smpKHandsAt · smpEarnAt · smpKOnGu · smpKOnGomega · smpSeat.

  smpK_first_paid, smpK_front_paid, smpK_two_paid   XK_first | XK_front | XK_point's premise on Y.
  smpK_hands_paid handsAt_XK's hY.
  smpK_ten_paid, smpK_eleven_paid   nine_at_K's hY10, ten_at_K's hY11.
  smpK_nine_says_paid, smpK_ten_says_paid   core_nine_K | core_ten_K's hYc.
WHAT STAYS. In smpK_hands_paid: the two sendings' tests on the plan (hp2, hp5) · K1's condition at
both places (hC2, hC5) · PlanY at the three shapes (closed tests on the plan) · that the three
messages are there and sampled.
What is not claimed. NO MEMBER OF THE PROMISE IS SHOWN. No soundness of a verifier; no level.

-/
import Johnson.Desc.K14.Law.LedgerSmpLaid
import Johnson.Desc.K14.Law.LedgerSmpK
import Johnson.Desc.K14.Law.LedgerSmpEarn

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Law
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Maker Desc.Plain Cb Johnson.Pack
open Iop Prob _root_.Run
open VerifiableInference.Desc (Block FileDescription Strs Wit)
open VerifiableInference.Desc.K12 (P12 T12 proximityTestKind guardedProximityTestParts Seat.onGu Seat.onGomega)
open VerifiableInference.Desc.K12.Coin
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.Shared
open Desc.K14.Law.Fence

variable (Q : P14) (shU shO shS : OracleShape) (sentU : Array OracleNotice)

theorem smpK_first_paid (key : TableKey) :
    (smpK Q.codes shU shO shS sentU.size) 0 (first Q.codes key) = true :=
  smpK_first Q shU shO shS sentU smpKEarly key

theorem smpK_front_paid (s : St) (h₀ : (smpK Q.codes shU shO shS sentU.size) 0 s =
    true) : (smpK Q.codes shU shO shS sentU.size) 1 s = true :=
  smpK_front Q shU shO shS sentU smpKEarly s h₀

theorem smpK_two_paid (s : St) : (smpK Q.codes shU shO shS sentU.size) 2 s = true :=
  smpK_two Q shU shO shS sentU smpKEarly s

theorem smpK_nine_says_paid (s : St) (h : (smpK Q.codes shU shO shS sentU.size) 9 s =
    true) :
    (∀ z, s.st.oracles[0]? = some z → ∀ m : H2K.First.Seat1, m.sh = shU → m.id = 0 →
      H2K.Pin.ok (H2K.Pin.sampleL Q.codes m z) = true) ∧
    ∀ z, s.st.oracles[sentU.size + 1]? = some z → ∀ m : H2K.First.Seat1, m.sh = shS →
      m.id = sentU.size + 1 → H2K.Pin.ok (H2K.Pin.sampleL Q.codes m z) = true :=
  smpK_nine_says Q shU shO shS sentU smpSeat s h

theorem smpK_ten_says_paid (s : St) (h : (smpK Q.codes shU shO shS sentU.size) 10 s =
    true) :
    (∀ z, s.st.oracles[sentU.size]? = some z → ∀ m : H2K.First.Seat1, m.sh = shO →
      m.id = sentU.size → H2K.Pin.ok (H2K.Pin.sampleL Q.codes m z) = true) ∧
    ∀ z, s.st.oracles[sentU.size + 1]? = some z → ∀ m : H2K.First.Seat1, m.sh = shS →
      m.id = sentU.size + 1 → H2K.Pin.ok (H2K.Pin.sampleL Q.codes m z) = true :=
  smpK_ten_says Q shU shO shS sentU smpSeat s h


variable {Cells : Type} (decT₂ : (ℕ → Option (ℕ × List UInt64)) → St → Option Cells)
  (Pm₁ : PromMeaning St) (n nU : ℕ) (cs : Codes) {Xi P₁ Cl Tok : Type} (G : FileDescription Xi)
  (ms : List Mem) (N : NumbersS) (Oc : P₁ → Strs → Prop) {Fr : Frame} (oNo : Mem → ℕ)
  (layU layO : TreeLay) (f : Piece (ckP .two) Fr (P₁ × St) Cl (Wit Cells Tok MsgT)) (l : List (Piece
      (ckP .two) Fr (P₁ × St) Cl (Wit Cells Tok MsgT)))

theorem smpK_ten_paid (hsU : sentU.size = 2) (π : P12) (x : Piece (ckP .two) Fr (P₁ ×
    St) Cl (Wit Cells Tok MsgT))
    (hb : Alike (held (P := P₁) (Seat.onGu (proximityTestKind guardedProximityTestParts π : Block T12 Unit))) x.b)
    (he : π.early = true) (ha1 : π.answers = 1) (a : (P₁ × St) × Fr.E.Str)
    (τ : Iop.Tr (uLT (ckP .two) x.ds)) (b : (P₁ × St) × Fr.E.Str)
    (ha : onQ₂ N (pmX cs G ms N (pmE decT₂ Pm₁ Q n nU sentU.size (shU, shO, shS, smpK Q.codes shU
        shO shS sentU.size)) oNo Q sentU layU layO) Oc true f l 9 a) (hout : x.ior.red.out a τ =
        some b) :
    (smpK Q.codes shU shO shS sentU.size) 10 b.1.2 = true :=
  smpK_ten Q shU shO shS sentU decT₂ Pm₁ n nU cs G ms N Oc oNo layU layO f l smpKOnGu hsU π x hb he
      ha1 a τ b ha hout

theorem smpK_eleven_paid (π : P12) (x : Piece (ckP .two) Fr (P₁ × St) Cl (Wit
    Cells Tok MsgT))
    (hb : Alike (held (P := P₁) (Seat.onGomega (proximityTestKind guardedProximityTestParts π : Block T12 Unit))) x.b)
    (he : π.early = true) (ha1 : π.answers = 1) (a : (P₁ × St) × Fr.E.Str)
    (τ : Iop.Tr (uLT (ckP .two) x.ds)) (b : (P₁ × St) × Fr.E.Str)
    (ha : onQ₂ N (pmX cs G ms N (pmE decT₂ Pm₁ Q n nU sentU.size (shU, shO, shS, smpK Q.codes shU
        shO shS sentU.size)) oNo Q sentU layU layO) Oc true f l 10 a) (hout : x.ior.red.out a τ =
        some b) :
    (smpK Q.codes shU shO shS sentU.size) 11 b.1.2 = true :=
  smpK_eleven Q shU shO shS sentU decT₂ Pm₁ n nU cs G ms N Oc oNo layU layO f l smpKOnGomega π x hb
      he ha1 a τ b ha hout


section hands
open VerifiableInference.Desc.K1 (shapesOf shapeAt sampledAt condPort)

theorem smpK_hands_paid (b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit)
    (hbl : blocks Q = some [b1, b2, b3, b4, b5, b6, b7, b8]) (hUw : withU Q.S = some sentU)
    (hp2 : b2.planOk = true) (hp5 : b5.planOk = true)
    (on : ℕ → (P₁ × St) × Fr.E.Str → Prop)
    (hU0 : 0 < (shapesOf (parU Q sentU)).length) (hkU : sampledAt (parU Q sentU) ⟨0, hU0⟩)
    (h0 : 0 < (shapesOf (parO Q)).length) (hk : sampledAt (parO Q) ⟨0, h0⟩)
    (h1 : 1 < (shapesOf (parO Q)).length) (hkS : sampledAt (parO Q) ⟨1, h1⟩)
    (rad2 rad5 : ℕ → ℕ) (hC2 : condPort (parU Q sentU) rad2 = true)
    (hC5 : condPort (parO Q) rad5 = true)
    (pyU : PlanY Q.codes (shapeAt (parU Q sentU) ⟨0, hU0⟩))
    (pyO : PlanY Q.codes (shapeAt (parO Q) ⟨0, h0⟩))
    (pyS : PlanY Q.codes (shapeAt (parO Q) ⟨1, h1⟩))
    (hon : ∀ k a, on k a → XK Q sentU layU layO (shapeAt (parU Q sentU) ⟨0, hU0⟩,
      shapeAt (parO Q) ⟨0, h0⟩, shapeAt (parO Q) ⟨1, h1⟩,
      smpK Q.codes (shapeAt (parU Q sentU) ⟨0, hU0⟩) (shapeAt (parO Q) ⟨0, h0⟩) (shapeAt (parO Q)
          ⟨1, h1⟩) sentU.size) sentU.size k a.1.2 = true) :
    HandsAt (Cl := Cl) (Cells := Cells) (Tok := Tok) on [b1, b2, b3, b4, b5, b6, b7, b8]
      (smpK Q.codes (shapeAt (parU Q sentU) ⟨0, hU0⟩) (shapeAt (parO Q) ⟨0, h0⟩) (shapeAt (parO Q)
          ⟨1, h1⟩) sentU.size) :=
  smpK_hands Q sentU layU layO smpKHandsAt smpEarnAt b1 b2 b3 b4 b5 b6 b7 b8 hbl hUw hp2 hp5 on hU0
      hkU h0 hk h1 hkS rad2 rad5 hC2 hC5 pyU pyO pyS hon

end hands

end Desc.K14.Law

#print axioms Desc.K14.Law.smpK_first_paid
#print axioms Desc.K14.Law.smpK_front_paid
#print axioms Desc.K14.Law.smpK_two_paid
#print axioms Desc.K14.Law.smpK_nine_says_paid
#print axioms Desc.K14.Law.smpK_ten_says_paid
#print axioms Desc.K14.Law.smpK_ten_paid
#print axioms Desc.K14.Law.smpK_eleven_paid
#print axioms Desc.K14.Law.smpK_hands_paid
