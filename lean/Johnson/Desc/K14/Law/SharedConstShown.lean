-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K14/Law/SharedConstShown.lean: THE NEW SAMPLED MEMBERS OF THE TWO SENDINGS ARE SHOWN AT
THE ROW's OWN PIECES, AT THE SHARED TABLE's CONSTANT. The ledger's top asks (hSh2, hSh5): at each
member that "send o_u" | "send o_omega" lays anew, the sending's piece shows the member's words.
shown_of_told (Johnson/Second/Seam/ShownOfTold.lean) gives it for a list of members
of the two sendings, at a piece of the maker's cut. HERE it is called at the constant's two lists
new2 | new5 (Johnson/Desc/K14/Law/LedgerMembersAt.lean), and its premise on the list is paid: "hnew
at new2 | new5".

  Sh.shown_two, Sh.shown_five   the two calls. The members' first number is Sh.t₁ A, the count of
                  the first chain's messages: the maker's D.t₁ by c₁.
What is not claimed. No soundness; no level.

-/
import Johnson.Desc.K14.Law.SharedConst
import Johnson.Desc.K14.Law.LedgerMembersAt
import Johnson.Second.Seam.ShownOfTold

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
open VerifiableInference.Desc.K1 (sendPiece)

namespace Sh

variable {Xi : Type} (A : ShPlan Xi)

theorem shown_two (file : String) (D : WholeD) (ch : Model.Verify.Chains) (tests : List (Block St
    Unit))
    (last : List (Block St Unit) → Block St Unit) (hUw : withU A.Q.S = some (sentU A))
    (hG : VerifiableInference.Desc.oraclesOf A.G.shared.blocksInOrder = VerifiableInference.Desc.oraclesOf
        (chainOf ch A.Q tests last).blocksInOrder)
    (hB : Second.Seam.toldFitB A.Q.codes A.Q.S (layU A) (layO A) = true)
    (hD : A.G.data file = .ok D) (hs : A.G.sentFit = true)
    (c₁ : (VerifiableInference.Desc.oraclesOf A.G.first.blocksInOrder).length = D.t₁)
    (c₂ : (VerifiableInference.Desc.oraclesOf A.G.shared.blocksInOrder).length = D.t₂)
    {Y S₁ S₂ S₃ X₁ X₂ Cl W : Type} (T : Three (ckP .two) D (allOf D) Y S₁ S₂ S₃ X₁ X₂ Cl W)
    (b₁ : Block S₁ Cl) (l₁ : List (Block S₁ Cl)) (b₂ : Block S₂ Cl) (l₂ : List (Block S₂ Cl))
    (b₃ : Block S₃ Cl) (l₃ : List (Block S₃ Cl)) rest₁ rest₂ rest₃ (r : Fmt.RoundView)
    (hc : T.IsCut b₁ l₁ b₂ l₂ b₃ l₃ rest₁ rest₂ rest₃ r)
    (p) (hp : p ∈ T.p₂ :: T.l₂) (d₁ d₂ : RDT) (hd : p.ds = [d₁, d₂])
    {S' Cl' W' : Type} (blk : Block S' Cl') (c e : ℕ) :
    ∀ x ∈ new2 A.Q (layU A) (layO A) (t₁ A) A.rad2 A.rad5,
      (sendPiece (W := W') (F := frameAt D (allOf D) D.key₂ T.ft₂) blk p.base d₁ d₂ c
        e).ShownAll A.G A.Q.codes x.1.l x.1.seat :=
  Second.Seam.shown_of_told A.G file D A.Q (layU A) (layO A) ch tests last hUw hG hB (A.rad2 0)
    (A.rad5 0) (A.rad5 1) hD hs c₁ c₂ T b₁ l₁ b₂ l₂ b₃ l₃ rest₁ rest₂ rest₃ r hc p hp d₁ d₂ hd blk c
        e _
    (fun x hx => by
      obtain rfl := List.mem_singleton.1 hx
      left
      rw [← c₁]
      rfl)

theorem shown_five (file : String) (D : WholeD) (ch : Model.Verify.Chains) (tests : List (Block St
    Unit))
    (last : List (Block St Unit) → Block St Unit) (hUw : withU A.Q.S = some (sentU A))
    (hG : VerifiableInference.Desc.oraclesOf A.G.shared.blocksInOrder = VerifiableInference.Desc.oraclesOf
        (chainOf ch A.Q tests last).blocksInOrder)
    (hB : Second.Seam.toldFitB A.Q.codes A.Q.S (layU A) (layO A) = true)
    (hD : A.G.data file = .ok D) (hs : A.G.sentFit = true)
    (c₁ : (VerifiableInference.Desc.oraclesOf A.G.first.blocksInOrder).length = D.t₁)
    (c₂ : (VerifiableInference.Desc.oraclesOf A.G.shared.blocksInOrder).length = D.t₂)
    {Y S₁ S₂ S₃ X₁ X₂ Cl W : Type} (T : Three (ckP .two) D (allOf D) Y S₁ S₂ S₃ X₁ X₂ Cl W)
    (b₁ : Block S₁ Cl) (l₁ : List (Block S₁ Cl)) (b₂ : Block S₂ Cl) (l₂ : List (Block S₂ Cl))
    (b₃ : Block S₃ Cl) (l₃ : List (Block S₃ Cl)) rest₁ rest₂ rest₃ (r : Fmt.RoundView)
    (hc : T.IsCut b₁ l₁ b₂ l₂ b₃ l₃ rest₁ rest₂ rest₃ r)
    (p) (hp : p ∈ T.p₂ :: T.l₂) (d₁ d₂ : RDT) (hd : p.ds = [d₁, d₂])
    {S' Cl' W' : Type} (blk : Block S' Cl') (c e : ℕ) :
    ∀ x ∈ new5 A.Q (layU A) (layO A) (t₁ A) A.rad2 A.rad5,
      (sendPiece (W := W') (F := frameAt D (allOf D) D.key₂ T.ft₂) blk p.base d₁ d₂ c
        e).ShownAll A.G A.Q.codes x.1.l x.1.seat :=
  Second.Seam.shown_of_told A.G file D A.Q (layU A) (layO A) ch tests last hUw hG hB (A.rad2 0)
    (A.rad5 0) (A.rad5 1) hD hs c₁ c₂ T b₁ l₁ b₂ l₂ b₃ l₃ rest₁ rest₂ rest₃ r hc p hp d₁ d₂ hd blk c
        e _
    (fun x hx => by
      right
      rw [← c₁]
      rcases List.mem_cons.1 hx with rfl | hx
      · rfl
      · obtain rfl := List.mem_singleton.1 hx
        rfl)

end Sh

end Desc.K14.Law

#print axioms Desc.K14.Law.Sh.shown_two
#print axioms Desc.K14.Law.Sh.shown_five
