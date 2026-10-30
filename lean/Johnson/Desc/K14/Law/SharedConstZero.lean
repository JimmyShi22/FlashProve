-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K14/Law/SharedConstZero.lean: THE JOINT OF THE FIRST AND THE SHARED CHAIN, AT THE
SHARED TABLE's CONSTANT: THE RELATION's WAY BACK, AND THE FENCE LAID BESIDE. In the form used here
the constant's meaning is tied to the first table's own meaning, as terms: so the second half
of the joint (relEndOfZero, Johnson/Desc/Sound/TieEnd.lean) is called at the
constant's letters. The promise's way forward stands in Johnson/Desc/K14/Law/SharedConstZeroAt.lean,
at one state.


  on_with         the fence laid beside a condition at a border: general.
  Sh.mg_tied      the constant's meaning is tied to the first table's own meaning: as terms.
  Sh.rel_end_of_zero   **the joint's second half at the constant**: what the shared chain claims at
                  its first border, at the state that start₂ makes, gives what the first chain
                  claims at its last. It asks hlen (the first chain's pieces are as many as the
                  table's places), hEnd (what is open behind the first chain's last border is on the
                  joint's list) and hPW (the committed table's pin, from the shared table's reading
                  to the first's).
What is not claimed. No soundness; no level.

-/
import Johnson.Desc.K14.Law.SharedConstStart
import Johnson.Desc.Sound.TieEnd

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

/-- The fence laid beside. -/
theorem on_with {P₁ S₂ Cl Wt : Type} {C : PQ.CK} {Fr : Frame} (N : NumbersS) (Pm : PromMeaning S₂)
    (Oc : P₁ → Strs → Prop) (R : P₁ → Prop) (split : Bool) (p : Piece C Fr (P₁ × S₂) Cl Wt)
    (l : List (Piece C Fr (P₁ × S₂) Cl Wt)) (k : ℕ) (a : (P₁ × S₂) × Fr.E.Str)
    (h : onQ₂ N Pm Oc split p l k a) (hr : R a.1.1) : onQ₂ N Pm (ocWith Oc R) split p l k a :=
  ⟨h.1, h.2, hr⟩

namespace Sh

variable {Xi P₀ P S₁' S₃' Y X₁ X₂ Cl Cells Tok : Type} (A : ShPlan Xi)
  (O : ShOpen P₀ (P × S₁') Cells Tok A.Q)

/-- The constant's meaning is tied to the first table's own: as terms. -/
theorem mg_tied : tiedMeaning O.get O.Mg₁ (mg A O) = mg A O := rfl

/-- **THE RELATION GOES BACK OVER THE JOINT**: what the shared chain claims at its first border, at
the state that start₂ makes, gives what the first chain claims at its last. -/
theorem rel_end_of_zero (D : WholeD) (all : List LeftT) (start₂ : P → St)
    (T : Three (ckP .two) D all Y (P × S₁') ((P × S₁') × St) ((P × S₁' × St) × S₃') X₁ X₂ Cl
      (Wit Cells Tok MsgT))
    (Q : Places D all (P × S₁') ((P × S₁') × St) ((P × S₁' × St) × S₃') (Wit Cells Tok MsgT))
    (R₀ : (P × S₁') × (EAll D all).Str → Wit Cells Tok MsgT → Prop)
    (hlen : 1 + T.l₁.length = (ps A O).length)
    (hEnd : ∀ i, openAfter (insQ O.links (ps A O)) (outsQ O.links (ps A O)) (· ∈ start O.links)
      (ps A O).length i → i ∈ endFirst)
    (hPW : ∀ (b : (P × S₁') × (EAll D all).Str) (w : Wit Cells Tok MsgT),
      (mg A O).pinT (start₂ b.1.1) (strsOfAct (frameAt D all D.key₂ T.ft₂)
        ((actQ (nums A O) T.p₂ T.l₂ 0).2 ((b.1, start₂ b.1.1), b.2))) w →
      O.Mg₁.pinW (O.get b.1) (strsOf (frameAt D all D.key₁ T.ft₁) b.2) w)
    (b : (P × S₁') × (EAll D all).Str) (w : Wit Cells Tok MsgT)
    (h : relQ₂ (nums A O) (mg A O) true T.p₂ T.l₂ 0 ((b.1, start₂ b.1.1), b.2) w) :
    (placesM T.ft₁ O.N₁ O.Mg₁ O.links (ps A O) O.get R₀ Q).R₁ (1 + T.l₁.length) b w :=
  relEndOfZero (ckP .two) D all Y P P₀ S₁' St S₃' X₁ X₂ Cl _ start₂ T Q O.get O.N₁ O.Mg₁ O.links
    (ps A O) R₀ (numbersSh (t₁ A) (layU A) (layO A) (0, 0) (0, 0)) (mg A O) (pm A O) true hlen hEnd
    hPW b w h

end Sh

end Desc.K14.Law

#print axioms Desc.K14.Law.on_with
#print axioms Desc.K14.Law.Sh.mg_tied
#print axioms Desc.K14.Law.Sh.rel_end_of_zero
