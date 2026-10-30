-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Second/Seam/ShownOfTold.lean: What the shared chain's two sendings show, with SeatFits paid: shownAtCut (Johnson/Desc/K14/Law/LedgerShown.lean) called at seatFits_of_told (SeatOfTold.lean): at any IOP as written in Lean G whose shared chain tells what K14's chainOf tells, at every piece of two rounds that the maker cuts of the shared chain, K1's own piece shows every member of a list whose sendings are sendingU | sendingO at the seat's parameters. The premises hSh2 | hSh5 of the ledger's top row are of this form. Statement and proof.
  shown_of_told   shownAtCut's premises but for «the seats fit» · hU · hG · toldFitB's yes · «each member's sending is one of the two» ⟹ ShownAll at each member. hlo is shownAtCut's own premise on the first chain's told trees, at t₁ := D.t₁.
Limits. SeatOfTold.lean's and LedgerShown.lean's: ShownAll speaks only of a member whose tree is one that the piece's own stretch sends. toldFitB's yes stays a premise: a closed test on the seat's parameters. That a given list of new members (the ledger's new2 | new5) has its sendings among the two is a premise here: these two lists' definitions (LedgerMembersAt.lean) are not imported here. No soundness is claimed.

-/
import Johnson.Second.Seam.SeatOfTold
import Johnson.Desc.K14.Law.LedgerShown

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Second.Seam
open OnBytes OnBytes.Params OnBytes.Maker _root_.Run
open VerifiableInference.Desc VerifiableInference.Desc.Sound
open VerifiableInference.Desc.K1 (sendPiece)
open Desc.K14.Law.Fence (sendingU sendingO)


theorem shown_of_told {Xi : Type} (G : FileDescription Xi) (file : String) (D : WholeD)
    (P : _root_.Desc.K14.P14) (layU layO : TreeLay) (ch : Model.Verify.Chains)
    (tests : List (Block _root_.Desc.K14.St Unit))
    (last : List (Block _root_.Desc.K14.St Unit) → Block _root_.Desc.K14.St Unit)
    {sentU : Array OracleNotice} (hU : _root_.Desc.K14.withU P.S = some sentU)
    (hG : oraclesOf G.shared.blocksInOrder = oraclesOf (_root_.Desc.K14.chainOf ch P tests last).blocksInOrder)
    (hB : toldFitB P.codes P.S layU layO = true) (rU rO rSp : ℕ)
    (hD : G.data file = .ok D) (hs : G.sentFit = true)
    (c₁ : (oraclesOf G.first.blocksInOrder).length = D.t₁) (c₂ : (oraclesOf G.shared.blocksInOrder).length = D.t₂)
    {Y S₁ S₂ S₃ X₁ X₂ Cl W : Type} (T : Three (ckP .two) D (allOf D) Y S₁ S₂ S₃ X₁ X₂ Cl W)
    (b₁ : Block S₁ Cl) (l₁ : List (Block S₁ Cl)) (b₂ : Block S₂ Cl) (l₂ : List (Block S₂ Cl))
    (b₃ : Block S₃ Cl) (l₃ : List (Block S₃ Cl)) rest₁ rest₂ rest₃ (r : Fmt.RoundView)
    (hc : T.IsCut b₁ l₁ b₂ l₂ b₃ l₃ rest₁ rest₂ rest₃ r)
    (p) (hp : p ∈ T.p₂ :: T.l₂) (d₁ d₂ : RDT) (hd : p.ds = [d₁, d₂])
    {S' Cl' W' : Type} (blk : Block S' Cl') (c e : ℕ) (new : List Mem)
    (hnew : ∀ x ∈ new, x.1 = sendingU P.S rU D.t₁ layU layO ∨
      x.1 = sendingO P.S rO rSp D.t₁ layU layO) :
    ∀ x ∈ new, (sendPiece (W := W') (F := frameAt D (allOf D) D.key₂ T.ft₂) blk p.base d₁ d₂ c
      e).ShownAll G P.codes x.1.l x.1.seat := by
  have hF := seatFits_of_told G P D.t₁ layU layO ch tests last hU c₁ hG hB rU rO rSp
  refine _root_.Desc.K14.Law.shownAtCut Xi G file D hD hs c₁ c₂ Y S₁ S₂ S₃ X₁ X₂ Cl W T b₁ l₁ b₂ l₂
    b₃ l₃ rest₁ rest₂ rest₃ r hc p hp d₁ d₂ hd S' Cl' W' blk c e P.codes new ?_
  intro x hx
  rcases hnew x hx with h | h
  · rw [h]
    exact hF.1
  · rw [h]
    exact hF.2

end Second.Seam

#print axioms Second.Seam.shown_of_told
