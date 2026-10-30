-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K14/Law/LedgerSmpLaid.lean: THE LETTER Y OF THE FILLING OF RECORD, FILLED: Y := smpK
("each of o_u, o_omega, o_sp passes K12's test on a member's sample",
Johnson/Desc/K14/Law/LedgerSmpKOwed.lean). XK (Johnson/Desc/K14/Law/LedgerNineTen.lean) asks six
hand-ons of its letter, and the last call at the seam (LedgerCore.lean) one premise on its content.
HERE each of the seven is had FROM THE STATEMENTS THAT ARE OWED FOR smpY | smpK, TAKEN AS PREMISES
BY NAME (they are propositions by def; a hand proves them apart): when a proof lies, it is one
substitution.

  smpK_first, smpK_front, smpK_two   Y at the borders 0, 1, 2: from SmpKEarlyOwed.
  smpK_ten, smpK_eleven   nine_at_K's hY10 and ten_at_K's hY11: from SmpKOnGuOwed |
                  SmpKOnGomegaOwed, the piece's yes (held_decides) and, at 9, "the first mask is
                  message 1" out of the promise.
  smpK_hands      handsAt_XK's hY: HandsAt for smpK: SmpKHandsAtOwed's conclusion, its two earnings
                  at the pieces of the two sendings by SmpEarnAtOwed, at the record's size in front
                  (0 | sentU.size, out of sharedX).
  smpY_says, smpK_nine_says, smpK_ten_says   the content (LedgerCore's hYc): from the test's own
                  text and SmpSeatOwed.
WHAT STAYS. The owed statements themselves · in smpK_hands: the two sendings' tests on the plan
(hp2, hp5) · K1's condition at both places (hC2, hC5) · PlanY at the three shapes (closed tests on
the plan) · what handsAt_XK asks.
What is not claimed. That the owed statements hold. NO MEMBER IS SHOWN. No soundness; no level.

-/
import Johnson.Desc.K14.Law.LedgerSmpKOwed
import Johnson.Desc.K14.Law.LedgerAtSeam

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

theorem smpK_first (E : SmpKEarlyOwed) (key : TableKey) :
    (smpK Q.codes shU shO shS sentU.size) 0 (first Q.codes key) = true := E _ _ _ _ _ 0 _ (by omega)

theorem smpK_front (E : SmpKEarlyOwed) (s : St) (_ : (smpK Q.codes shU shO shS sentU.size) 0 s =
    true) : (smpK Q.codes shU shO shS sentU.size) 1 s = true :=
  E _ _ _ _ _ 1 s (by omega)

theorem smpK_two (E : SmpKEarlyOwed) (s : St) : (smpK Q.codes shU shO shS sentU.size) 2 s = true :=
    E _ _ _ _ _ 2 s (by omega)

/-- **What smpY says of the record behind its border.** -/
theorem smpY_says (Se : SmpSeatOwed) (cs : Codes) (sh : OracleShape) (o k₀ k : ℕ) (hk : k₀ < k)
    (s : St) (h : smpY cs sh o k₀ k s = true) (z : OnBytes.Oracle)
    (hz : s.st.oracles[o]? = some z) (m : H2K.First.Seat1) (h1 : m.sh = sh) (h2 : m.id = o) :
    H2K.Pin.ok (H2K.Pin.sampleL cs m z) = true := by
  unfold smpY at h
  rw [hz] at h
  have h' : H2K.Pin.ok (H2K.Pin.sampleL cs (seatY sh o) z) = true := by
    rcases Bool.or_eq_true_iff.1 h with h0 | h0
    · exact absurd (of_decide_eq_true h0) (by omega)
    · exact h0
  rw [Se cs (seatY sh o) m z h1 h2]
  exact h'

theorem smpK_parts (cs : Codes) (sU k : ℕ) (s : St) (h : smpK cs shU shO shS sU k s = true) :
    smpY cs shU 0 2 k s = true ∧ smpY cs shO sU 5 k s = true ∧
      smpY cs shS (sU + 1) 5 k s = true := by
  unfold smpK at h
  obtain ⟨h12, h3⟩ := Bool.and_eq_true_iff.1 h
  obtain ⟨h1, h2⟩ := Bool.and_eq_true_iff.1 h12
  exact ⟨h1, h2, h3⟩

/-- LedgerCore's hYc at block 9. -/
theorem smpK_nine_says (Se : SmpSeatOwed) (s : St) (h : (smpK Q.codes shU shO shS sentU.size) 9 s =
    true) :
    (∀ z, s.st.oracles[0]? = some z → ∀ m : H2K.First.Seat1, m.sh = shU → m.id = 0 →
      H2K.Pin.ok (H2K.Pin.sampleL Q.codes m z) = true) ∧
    ∀ z, s.st.oracles[sentU.size + 1]? = some z → ∀ m : H2K.First.Seat1, m.sh = shS →
      m.id = sentU.size + 1 → H2K.Pin.ok (H2K.Pin.sampleL Q.codes m z) = true := by
  obtain ⟨h1, _, h3⟩ := smpK_parts shU shO shS Q.codes sentU.size 9 s h
  exact ⟨fun z hz m a b => smpY_says Se _ _ _ 2 9 (by omega) s h1 z hz m a b,
    fun z hz m a b => smpY_says Se _ _ _ 5 9 (by omega) s h3 z hz m a b⟩

/-- LedgerCore's hYc at block 10. -/
theorem smpK_ten_says (Se : SmpSeatOwed) (s : St) (h : (smpK Q.codes shU shO shS sentU.size) 10 s =
    true) :
    (∀ z, s.st.oracles[sentU.size]? = some z → ∀ m : H2K.First.Seat1, m.sh = shO →
      m.id = sentU.size → H2K.Pin.ok (H2K.Pin.sampleL Q.codes m z) = true) ∧
    ∀ z, s.st.oracles[sentU.size + 1]? = some z → ∀ m : H2K.First.Seat1, m.sh = shS →
      m.id = sentU.size + 1 → H2K.Pin.ok (H2K.Pin.sampleL Q.codes m z) = true := by
  obtain ⟨_, h2, h3⟩ := smpK_parts shU shO shS Q.codes sentU.size 10 s h
  exact ⟨fun z hz m a b => smpY_says Se _ _ _ 5 10 (by omega) s h2 z hz m a b,
    fun z hz m a b => smpY_says Se _ _ _ 5 10 (by omega) s h3 z hz m a b⟩

variable {Cells : Type} (decT₂ : (ℕ → Option (ℕ × List UInt64)) → St → Option Cells)
  (Pm₁ : PromMeaning St) (n nU : ℕ) (cs : Codes) {Xi P₁ Cl Tok : Type} (G : FileDescription Xi)
  (ms : List Mem) (N : NumbersS) (Oc : P₁ → Strs → Prop) {Fr : Frame} (oNo : Mem → ℕ)
  (layU layO : TreeLay) (f : Piece (ckP .two) Fr (P₁ × St) Cl (Wit Cells Tok MsgT)) (l : List (Piece
      (ckP .two) Fr (P₁ × St) Cl (Wit Cells Tok MsgT)))

/-- **nine_at_K's hY10 at Y := smpK.** -/
theorem smpK_ten (U : SmpKOnGuOwed) (hsU : sentU.size = 2) (π : P12) (x : Piece (ckP .two) Fr (P₁ ×
    St) Cl (Wit Cells Tok MsgT))
    (hb : Alike (held (P := P₁) (Seat.onGu (proximityTestKind guardedProximityTestParts π : Block T12 Unit))) x.b)
    (he : π.early = true) (ha1 : π.answers = 1) (a : (P₁ × St) × Fr.E.Str)
    (τ : Iop.Tr (uLT (ckP .two) x.ds)) (b : (P₁ × St) × Fr.E.Str)
    (ha : onQ₂ N (pmX cs G ms N (pmE decT₂ Pm₁ Q n nU sentU.size (shU, shO, shS, smpK Q.codes shU
        shO shS sentU.size)) oNo Q sentU layU layO) Oc true f l 9 a) (hout : x.ior.red.out a τ =
        some b) :
    (smpK Q.codes shU shO shS sentU.size) 10 b.1.2 = true := by
  obtain ⟨rs, gs, hd, _⟩ := held_decides _ x hb a b τ hout
  have hM := ((sharedX_parts Q sentU layU layO 9 _).1 (shared_of_on decT₂ Pm₁ Q n nU sentU.size
      (shU, shO, shS, smpK Q.codes shU shO shS sentU.size) cs G ms N Oc oNo sentU layU layO f l 9 a
      ha)).2.2.1
  exact U _ _ _ _ _ (by omega) π he ha1 _ _ rs gs hd (membX_nine sentU.size _ hM).2
    (letter_of_on decT₂ Pm₁ Q n nU sentU.size (shU, shO, shS, smpK Q.codes shU shO shS sentU.size)
        cs G ms N Oc oNo sentU layU layO f l 9 a ha)

/-- **ten_at_K's hY11 at Y := smpK.** -/
theorem smpK_eleven (O : SmpKOnGomegaOwed) (π : P12) (x : Piece (ckP .two) Fr (P₁ × St) Cl (Wit
    Cells Tok MsgT))
    (hb : Alike (held (P := P₁) (Seat.onGomega (proximityTestKind guardedProximityTestParts π : Block T12 Unit))) x.b)
    (he : π.early = true) (ha1 : π.answers = 1) (a : (P₁ × St) × Fr.E.Str)
    (τ : Iop.Tr (uLT (ckP .two) x.ds)) (b : (P₁ × St) × Fr.E.Str)
    (ha : onQ₂ N (pmX cs G ms N (pmE decT₂ Pm₁ Q n nU sentU.size (shU, shO, shS, smpK Q.codes shU
        shO shS sentU.size)) oNo Q sentU layU layO) Oc true f l 10 a) (hout : x.ior.red.out a τ =
        some b) :
    (smpK Q.codes shU shO shS sentU.size) 11 b.1.2 = true := by
  obtain ⟨rs, gs, hd, _⟩ := held_decides _ x hb a b τ hout
  exact O _ _ _ _ _ π he ha1 _ _ rs gs hd (letter_of_on decT₂ Pm₁ Q n nU sentU.size (shU, shO, shS,
      smpK Q.codes shU shO shS sentU.size) cs G ms N Oc oNo sentU layU layO f l 10 a ha)

section hands
open VerifiableInference.Desc.K1 (shapesOf shapeAt sampledAt condPort)

/-- **handsAt_XK's hY at Y := smpK**: SmpKHandsAtOwed's conclusion, its two earnings by
SmpEarnAtOwed at the record's size in front (0 | sentU.size: out of sharedX). -/
theorem smpK_hands (H : SmpKHandsAtOwed) (Ea : SmpEarnAtOwed)
    (b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit)
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
          ⟨1, h1⟩) sentU.size) := by
  obtain ⟨u, hu, e2, e5⟩ := blocks_two Q b1 b2 b3 b4 b5 b6 b7 b8 hbl
  obtain rfl : u = sentU := Option.some.inj (hu.symm.trans hUw)
  have mb : ∀ k a, on k a → membX u.size k a.1.2 = true := fun k a ha =>
    ((sharedX_parts Q u layU layO k _).1 ((XK_iff Q u.size _ u layU layO k _).1 (hon k a
        ha)).1).2.2.1
  subst e2 e5
  refine H P₁ Cl Cells Tok Fr Q.codes Q _ _ _ _ _ _ _ _ hbl on _ _ _ _
    (fun k a ha => ((XK_iff Q u.size _ u layU layO k _).1 (hon k a ha)).2.2.2.2.2.2)
    (fun c hc hr x hx a τ y ha hout => ?_) fun c hc hr x hx a τ y ha hout => ⟨?_, ?_⟩
  · have e := Ea P₁ Cl Cells Tok Fr Q _ (parU Q u) _ _ _ (behindU_book Q.par) hp2 rad2 hC2 ⟨0, hU0⟩
      hkU pyU c hc hr x hx a τ y hout 2 3
    rw [((membX2 u.size a.1.2).1 (mb 2 a ha)).2.2.2] at e
    exact e
  · have e := Ea P₁ Cl Cells Tok Fr Q _ (parO Q) _ _ _ (behindOmega_book Q.par) hp5 rad5 hC5 ⟨0, h0⟩
      hk pyO c hc hr x hx a τ y hout 5 6
    rw [((membX45 u.size a.1.2 5 (.inr rfl)).1 (mb 5 a ha)).2.2.2.1] at e
    exact e
  · have e := Ea P₁ Cl Cells Tok Fr Q _ (parO Q) _ _ _ (behindOmega_book Q.par) hp5 rad5 hC5 ⟨1, h1⟩
      hkS pyS c hc hr x hx a τ y hout 5 6
    rw [((membX45 u.size a.1.2 5 (.inr rfl)).1 (mb 5 a ha)).2.2.2.1] at e
    exact e

end hands

end Desc.K14.Law

#print axioms Desc.K14.Law.smpK_hands
#print axioms Desc.K14.Law.smpK_first
#print axioms Desc.K14.Law.smpK_front
#print axioms Desc.K14.Law.smpK_two
#print axioms Desc.K14.Law.smpY_says
#print axioms Desc.K14.Law.smpK_nine_says
#print axioms Desc.K14.Law.smpK_ten_says
#print axioms Desc.K14.Law.smpK_ten
#print axioms Desc.K14.Law.smpK_eleven
