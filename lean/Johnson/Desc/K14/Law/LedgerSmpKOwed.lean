-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K14/Law/LedgerSmpKOwed.lean: A DEFINITION, AND FOUR STATEMENTS ON IT THAT ARE OWED FOR
K14's LAW, AS PROPOSITIONS BY def: NO PROOF HERE. smpY (Johnson/Desc/K14/Law/LedgerSmpOwed.lean) at
the shared chain's three sampled messages, laid together: what is meant in the letter Y at the end
of the test XK (Johnson/Desc/K14/Law/LedgerNineTen.lean). That file asks six things of Y: at the
chain's first record; over the front; behind "LIN point"; HandsAt over the kind's other seven blocks
and the end; over each of the two proximity tests.

  smpK            smpY at o_u (number 0, behind border 2), o_omega (sU, behind 5), o_sp (sU + 1, 5)
  SmpKEarlyOwed   at the borders 0, 1 and 2 it says yes of every record: the first three
  SmpKHandsAtOwed HandsAt, from the earning at the two sendings' pieces: the fourth
  SmpKOnGuOwed, SmpKOnGomegaOwed   the two tests' decisions hand it on: the decision's form of the
                  fifth and the sixth
What is not claimed. That they hold.
(They are proved in Johnson/Desc/K14/Law/LedgerSmpK.lean: smpKEarly, smpKHandsAt, smpKOnGu,
smpKOnGomega.)
Nothing on soundness.

-/
import Johnson.Desc.K14.Law.LedgerSmpOwed

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Law
open OnBytes OnBytes.Params OnBytes.Slice Desc.Plain
open Iop Run OnBytes.Maker
open VerifiableInference.Desc (Block Wit)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.K12 (P12 proximityTestKind guardedProximityTestParts)

/-- **smpY at the three messages.** sU: how many messages o_u's sending has. -/
def smpK (cs : Codes) (shU shO shS : OracleShape) (sU : ℕ) : ℕ → St → Bool := fun k s =>
  smpY cs shU 0 2 k s && smpY cs shO sU 5 k s && smpY cs shS (sU + 1) 5 k s

/-- OWED: idle at the first three borders. -/
def SmpKEarlyOwed : Prop :=
  ∀ (cs : Codes) (shU shO shS : OracleShape) (sU k : ℕ) (s : St), k ≤ 2 →
    smpK cs shU shO shS sU k s = true

/-- OWED: HandsAt for smpK: earned at the pieces of "send o_u" and "send o_omega", kept else. -/
def SmpKHandsAtOwed : Prop :=
  ∀ (P₁ Cl Cells Tok : Type) (Fr : Frame) (cs : Codes) (Q : P14)
    (b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit), blocks Q = some [b1, b2, b3, b4, b5, b6, b7, b8] →
    ∀ (on : ℕ → (P₁ × St) × Fr.E.Str → Prop) (shU shO shS : OracleShape) (sU : ℕ),
    (∀ k a, on k a → smpK cs shU shO shS sU k a.1.2 = true) →
    (∀ c : Block St Cl, DecidesAs c b2 → c.rounds = b2.rounds →
      ∀ x : Piece (ckP .two) Fr (P₁ × St) Cl (Wit Cells Tok MsgT), x.b = heldW c → ∀ a τ y,
        on 2 a → x.ior.red.out a τ = some y → smpY cs shU 0 2 3 y.1.2 = true) →
    (∀ c : Block St Cl, DecidesAs c b5 → c.rounds = b5.rounds →
      ∀ x : Piece (ckP .two) Fr (P₁ × St) Cl (Wit Cells Tok MsgT), x.b = heldW c → ∀ a τ y,
        on 5 a → x.ior.red.out a τ = some y →
        smpY cs shO sU 5 6 y.1.2 = true ∧ smpY cs shS (sU + 1) 5 6 y.1.2 = true) →
    HandsAt (Cl := Cl) (Cells := Cells) (Tok := Tok) on [b1, b2, b3, b4, b5, b6, b7, b8]
      (smpK cs shU shO shS sU)

/-- OWED: the test on G_u hands smpK on, where the first mask is the message number 1 and o_u's
sending has two messages at least. -/
def SmpKOnGuOwed : Prop :=
  ∀ (cs : Codes) (shU shO shS : OracleShape) (sU : ℕ), 2 ≤ sU → ∀ p : P12, p.early = true →
    p.answers = 1 → ∀ (d d' : St) (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64))),
    (VerifiableInference.Desc.K12.Seat.onGu (proximityTestKind guardedProximityTestParts p)).decide d rs gs = .ok d' →
    d.loc.firstMask = some 1 → smpK cs shU shO shS sU 9 d = true →
    smpK cs shU shO shS sU 10 d' = true

/-- OWED: the test on G_omega hands smpK on. -/
def SmpKOnGomegaOwed : Prop :=
  ∀ (cs : Codes) (shU shO shS : OracleShape) (sU : ℕ) (p : P12), p.early = true →
    p.answers = 1 → ∀ (d d' : St) (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64))),
    (VerifiableInference.Desc.K12.Seat.onGomega (proximityTestKind guardedProximityTestParts p)).decide d rs gs = .ok d' →
    smpK cs shU shO shS sU 10 d = true → smpK cs shU shO shS sU 11 d' = true

end Desc.K14.Law
