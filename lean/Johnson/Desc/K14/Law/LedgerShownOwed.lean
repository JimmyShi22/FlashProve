-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K14/Law/LedgerShownOwed.lean: THREE STATEMENTS THAT ARE OWED FOR K14's LAW, AS
PROPOSITIONS BY def: NO PROOF HERE. The law of a sending on the shared chain (blocks 2 and 5: "send
o_u", "send o_omega") asks of the sending's piece that behind it every new member is shown: every
leaf of the member's tree shows its symbol (Piece.ShownAll, Johnson/Desc/Sound/ShownOfData.lean).
That file proves it of every piece that the maker cuts, at every description (shownOfData). The law
speaks of K1's own piece (sendPiece, Johnson/Desc/K1/Law/GoodSend3.lean), which has the same base
and the same two rounds' data as the maker's piece, and another extractor and other errors. OWED:
the step from the one to the other.

  ShownSameOwed     ShownAll reads of a piece its base and its rounds' data alone
  ShownAtSendOwed   so it goes over from any piece with two rounds to K1's piece at that base
  ShownAtCutOwed    so at every description, at every piece of two rounds that the maker cuts of the
                    shared chain, K1's piece shows every member of a list whose seats fit
What is not claimed. That they hold.
(They are proved in Johnson/Desc/K14/Law/LedgerShown.lean: shownSame, shownAtSend, shownAtCut.)
That the seats fit (SeatFits: a test on the plan) at any
member. Nothing on soundness.

-/
import Johnson.Desc.Sound.ShownOfData
import Johnson.Desc.Sound.World
import Johnson.Desc.K1.Law.GoodSend3

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Law
open OnBytes OnBytes.Maker _root_.Run
open VerifiableInference.Desc (Block FileDescription)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.K1 (sendPiece)
open _root_.Run.PQ (CK)

/-- OWED: ShownAll reads of a piece its base and its rounds' data alone. -/
def ShownSameOwed : Prop :=
  ∀ (C : CK) (Fr : Frame) (S Cl W S' Cl' W' Xi : Type) (p : Piece C Fr S Cl W)
    (q : Piece C Fr S' Cl' W') (G : FileDescription Xi) (cs : Codes) (m : List (OracleShape × ℕ))
    (seat : Fin m.length → ℕ × ℕ), q.base = p.base → q.ds = p.ds →
    p.ShownAll G cs m seat → q.ShownAll G cs m seat

/-- OWED: from a piece with two rounds to K1's piece at its base and its rounds' data. -/
def ShownAtSendOwed : Prop :=
  ∀ (Fr : Frame) (S Cl W S' Cl' W' Xi : Type) (p : Piece (ckP .two) Fr S Cl W)
    (blk : Block S' Cl') (base : ℕ) (d₁ d₂ : RDT) (c e : ℕ) (G : FileDescription Xi) (cs : Codes)
    (m : List (OracleShape × ℕ)) (seat : Fin m.length → ℕ × ℕ), p.base = base →
    p.ds = [d₁, d₂] → p.ShownAll G cs m seat →
    (sendPiece (W := W') (F := Fr) blk base d₁ d₂ c e).ShownAll G cs m seat

/-- OWED: the law's premise on what a sending shows, at the maker's pieces of the shared chain. -/
def ShownAtCutOwed : Prop :=
  ∀ (Xi : Type) (F : FileDescription Xi) (file : String) (D : WholeD), F.data file = .ok D →
    F.sentFit = true → (VerifiableInference.Desc.oraclesOf F.first.blocksInOrder).length = D.t₁ →
    (VerifiableInference.Desc.oraclesOf F.shared.blocksInOrder).length = D.t₂ →
    ∀ (Y S₁ S₂ S₃ X₁ X₂ Cl W : Type) (T : Three (ckP .two) D (allOf D) Y S₁ S₂ S₃ X₁ X₂ Cl W)
      (b₁ : Block S₁ Cl) (l₁ : List (Block S₁ Cl)) (b₂ : Block S₂ Cl) (l₂ : List (Block S₂ Cl))
      (b₃ : Block S₃ Cl) (l₃ : List (Block S₃ Cl)) rest₁ rest₂ rest₃ (r : Fmt.RoundView),
      T.IsCut b₁ l₁ b₂ l₂ b₃ l₃ rest₁ rest₂ rest₃ r →
    ∀ p ∈ T.p₂ :: T.l₂, ∀ d₁ d₂ : RDT, p.ds = [d₁, d₂] →
    ∀ (S' Cl' W' : Type) (blk : Block S' Cl') (c e : ℕ) (cs : Codes) (new : List Mem),
      (∀ x ∈ new, SeatFits F cs x.1.l x.1.seat) →
      ∀ x ∈ new, (sendPiece (W := W') (F := frameAt D (allOf D) D.key₂ T.ft₂) blk p.base d₁ d₂ c
        e).ShownAll F cs x.1.l x.1.seat

end Desc.K14.Law
