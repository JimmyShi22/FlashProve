-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K14/Law/SharedConstLastOn.lean: WHAT THE SHARED TABLE's PROMISE AT ITS LAST BORDER
HANDS TO THE LAST CHAIN, IN ONE SENTENCE. The last chain's table asks, at its first border, that the
shared chain has ended AND that the tests X in the promise's slot accept the shared chain's last
state ("endedX X"). Both stand in the condition in front at border 12 of the shared
table at the constant: "ended" out of the clause "nothing is left", X out of the clause shape 12. So
the two tables' rows are payable TOGETHER at one promise.

  Sh.shape_of_on  the clause shape 12 out of the condition in front at border 12.
  Sh.X_of_on      the tests in the slot: Sh.X A 12.
  Sh.last_of_on   **the sentence**: there is an o with K14.ended d = some o, and Sh.X A 12 d, and
                  the last chain's door's tests (doorSharedB A.p d).
  Sh.endedIf_of_on   the same in the form "if X then ended else none" is some.
A CAUTION. "ended is some" alone holds at the chain's first state too; X A 12 does not (it asks a
message at o_omega's number). Spend the two together, as here.
What is not claimed. That the proximity tests ran. No soundness; no level.

-/
import Johnson.Desc.K14.Law.SharedConstEnd
import Johnson.Desc.K14.Law.SharedConstShape

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Law
open OnBytes OnBytes.Params OnBytes.Slice Desc.Plain
open Iop Prob Run OnBytes.Maker OnBytes.Flat
open OnBytes.Means (Words wordsOn)
open Johnson.Pack
open _root_.Run.PQ (CK)
open Cb Cb.Ood Blocks Cb.Pv Cb.Pv.Lin Cb.Bridge
open VerifiableInference.Desc (Block Strs Wit FileDescription First.S Grows)
open VerifiableInference.Desc.ChainEnd (untestedL Exact)
open VerifiableInference.Desc.K1 (sendPiece sampledAt shapeAt shapesOf condPort errPort seedEntry
  seedMaps)
open VerifiableInference.Desc.First (Meaning Numbers ModelPart Pub pubSets openSets start)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.Shared
open VerifiableInference.Desc.K13 (Where)
open VerifiableInference.Desc.K12 (P12 T12 proximityTestKind guardedProximityTestParts Seat.onGu Seat.onGomega)
open VerifiableInference.Desc.K12.Coin
open Desc.K14.Law.Fence
open H2K.Pin (NTuple)
open H2K.Pub (johOk batV0 PayPub)
open H2K.First (batOneOk)
open VerifiableInference.Desc.K13.Law (EvalAt laidOf wSitsItem wSitsMore)
open VerifiableInference.Desc.Third (P₁₄)

namespace Sh

variable {Xi P₀ P₁ Cl Cells Tok : Type} {Fr : Frame} (A : ShPlan Xi)
  (O : ShOpen P₀ P₁ Cells Tok A.Q)

theorem shape_of_on (f : Piece (ckP .two) Fr (P₁ × St) Cl (Wit Cells Tok MsgT)) (l : List (Piece
    (ckP .two) Fr (P₁ × St) Cl (Wit Cells Tok MsgT))) (a : (P₁ × St) × Fr.E.Str)
    (ha : onQ₂ (nums A O) (pm A O) (own A O) true f l 12 a) :
    (pm A O).shape 12 a.1.2 = true :=
  ha.1 (.shape 12) (by decide)

theorem X_of_on (f : Piece (ckP .two) Fr (P₁ × St) Cl (Wit Cells Tok MsgT)) (l : List (Piece (ckP
    .two) Fr (P₁ × St) Cl (Wit Cells Tok MsgT))) (a : (P₁ × St) × Fr.E.Str)
    (ha : onQ₂ (nums A O) (pm A O) (own A O) true f l 12 a) : X A 12 a.1.2 = true :=
  X_of_shape A O a.1.2 (shape_of_on A O f l a ha)

/-- **What the promise at the last border hands to the last chain.** -/
theorem last_of_on (f : Piece (ckP .two) Fr (P₁ × St) Cl (Wit Cells Tok MsgT)) (l : List (Piece (ckP
    .two) Fr (P₁ × St) Cl (Wit Cells Tok MsgT))) (a : (P₁ × St) × Fr.E.Str)
    (ha : onQ₂ (nums A O) (pm A O) (own A O) true f l 12 a) :
    (∃ o, ended a.1.2 = some o) ∧ X A 12 a.1.2 = true ∧
      VerifiableInference.Desc.Last.doorSharedB A.p a.1.2 = true :=
  ⟨Option.isSome_iff_exists.1 (ended_of_on A O f l a ha), X_of_on A O f l a ha,
    door_of_shape A O a.1.2 (shape_of_on A O f l a ha)⟩

theorem endedIf_of_on (f : Piece (ckP .two) Fr (P₁ × St) Cl (Wit Cells Tok MsgT)) (l : List (Piece
    (ckP .two) Fr (P₁ × St) Cl (Wit Cells Tok MsgT))) (a : (P₁ × St) × Fr.E.Str)
    (ha : onQ₂ (nums A O) (pm A O) (own A O) true f l 12 a) :
    (if X A 12 a.1.2 = true then ended a.1.2 else none).isSome = true := by
  rw [if_pos (X_of_on A O f l a ha)]
  exact ended_of_on A O f l a ha

end Sh

end Desc.K14.Law

#print axioms Desc.K14.Law.Sh.shape_of_on
#print axioms Desc.K14.Law.Sh.X_of_on
#print axioms Desc.K14.Law.Sh.last_of_on
#print axioms Desc.K14.Law.Sh.endedIf_of_on
