-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Flat/Last/LastCutCap.lean: last_list_at (LastCut.lean) AT THE LIST's "rest" THAT IS MEANT: restCap e (Johnson/Desc/Sound/BoundsAtCap.lean): a family of extractors e, and every piece's errors the cap Err.cap 128. The third fact of make (hrest) is then A CHOICE OF e AND NOTHING ELSE.

  extsLast: THE CHOICE: at number 2 the row's own extractor (extAt … mine [] …, which reads neither the stretch nor the transcript); at every other number the identity.
  capB | capT: the cap's two parts at the stretch dB :: dt: the number for "BAT"'s round, and the errors of the rounds behind.
  **last_list_cap**: at rest₃ := restCap extsLast: the last chain's pieces ARE [x₀, x₁, pieceTwoT … (capB …) (capT …) …, x₃], from TWO facts of make: the third block is the kind K12's block at a seat; the third stretch is dB :: dt. The other three: the maker's own pieces over held c₀ | c₁ | c₃.
  idle_zero | idle_one | idle_three: ONE family e serves all four pieces: at this choice the other three have THE IDENTITY for their extractor: that is what row 0's law (hext) and row 1's (RowOneOwed.idle) ask; row 3 asks nothing of it.

Every "there is", walked: no statement has one.
Limits. SO THE ERRORS OF BLOCK 2 ARE THE CAP's: e₀ := capB, εt := capT: THE KIND's LAW's TWO PRICES
MUST FIT UNDER THEM: BatAtN's count at most capB (not shown here; `four_at_W`,
Johnson/Loose/H2K12/LastRestAtW.lean, shows it at the proof file's own description, under its
premises: ClosedL, two numbers of the place, the description's data) and AtPlace.bears at capT (the
chain's errors at most the cap, round by round): NUMBERS: EVALUATED NOWHERE HERE. Nothing on
soundness.

-/
import Johnson.Flat.Last.LastCut
import Johnson.Desc.Sound.BoundsAtCap

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace VerifiableInference.OnPublicFiles.Last
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Slice.ProxRun OnBytes.Maker Fo.Peel Cb Johnson.Pack
open Iop Prob _root_.Run
open _root_.Run.PQ (CK SgX)
open VerifiableInference.Desc VerifiableInference.Desc.K12 VerifiableInference.Desc.Sound
open VerifiableInference.Desc.K12.Coin

/-- The cap's number for the first round of a stretch, and its errors for the rounds behind. -/
def capB (dB : RDT) (dt : List RDT) : ℕ := (Err.cap 128 (uLT (ckP .two) (dB :: dt))).1
def capT (dB : RDT) (dt : List RDT) : Err (uLT (ckP .two) dt) := (Err.cap 128 (uLT (ckP .two) (dB :: dt))).2

section
variable {Xi Cells Tok : Type} (F : FileDescription Xi) (D : WholeD)
  (a₁ : Block F.S₁ F.Cl) (k₁ : List (Block F.S₁ F.Cl)) (a₂ : Block F.S₂ F.Cl) (k₂ : List (Block F.S₂ F.Cl))
  (c₀ c₁ c₂ c₃ : Block F.S₃ F.Cl)
  (rest₁ : (i : ℕ) → (ds : List RDT) → Rest (ckP .two) (frameAt D (allOf D) D.key₁ 0) (F.XiPub × F.S₁) (Wit Cells Tok MsgT) ds)
  (rest₂ : (i : ℕ) → (ds : List RDT) → Rest (ckP .two) (frameAt D (allOf D) D.key₂ 0) ((F.XiPub × F.S₁) × F.S₂) (Wit Cells Tok MsgT) ds)
  (d wEnd : Wit Cells Tok MsgT)
  (cs : OnBytes.Codes) {Xi' : Type} (G : FileDescription Xi') (arr : ℕ → ℕ → ℕ)
  (smp : ((F.XiPub × F.S₁ × F.S₂) × F.S₃) → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp)
  (decT : (ℕ → Option (ℕ × List UInt64)) → ((F.XiPub × F.S₁ × F.S₂) × F.S₃) → Option Cells) (c₀' : Cells)
  (π : P12) (dB : RDT) (dt : List RDT)
  (enter : F.S₃ → Except String T12) (leave : F.S₃ → T12 → Except String F.S₃) (mine : List Mem)

/-- **The choice of the extractors.** -/
def extsLast : (i : ℕ) → (ds : List RDT) →
    ((F.XiPub × F.S₁ × F.S₂) × F.S₃) × (frameAt D (allOf D) D.key₃ F.lastChainFirstTreeNumber).E.Str → Iop.Tr (uLT (ckP .two) ds) →
      Wit Cells Tok MsgT → Wit Cells Tok MsgT :=
  fun i _ a _ w => if i = 2 then extAt cs G arr smp decT c₀' mine [] false none a.1 (strsOf _ a.2) w else w

/-- **The list at the cap, from two facts of make.** -/
theorem last_list_cap
    (hc : c₂ = (proximityTestKind guardedProximityTestParts π : Block T12 F.Cl).inside enter leave)
    (hds : ds₂ D.ds₃ (held (P := F.XiPub × F.S₁ × F.S₂) c₀) (held (P := F.XiPub × F.S₁ × F.S₂) c₁) (held (P := F.XiPub × F.S₁ × F.S₂) c₂) = dB :: dt) :
    (atDesc F (piecesAt (ckP .two) F D a₁ k₁ a₂ k₂ c₀ [c₁, c₂, c₃] rest₁ rest₂
          (restCap (extsLast F D cs G arr smp decT c₀' mine)) d wEnd)).p₃ ::
        (atDesc F (piecesAt (ckP .two) F D a₁ k₁ a₂ k₂ c₀ [c₁, c₂, c₃] rest₁ rest₂
          (restCap (extsLast F D cs G arr smp decT c₀' mine)) d wEnd)).l₃ =
      [pieceZeroAt F D c₀ (restCap (extsLast F D cs G arr smp decT c₀' mine)),
        pieceOneAt F D c₀ c₁ (restCap (extsLast F D cs G arr smp decT c₀' mine)),
        pieceTwoT cs G arr smp decT c₀' π (baseTwoAt F D c₀ c₁) dB dt (capB dB dt) (capT dB dt) enter leave mine,
        pieceThreeAt F D c₀ c₁ c₂ c₃ (restCap (extsLast F D cs G arr smp decT c₀' mine))] :=
  last_list_at F D a₁ k₁ a₂ k₂ c₀ c₁ c₂ c₃ rest₁ rest₂ _ d wEnd cs G arr smp decT c₀' π dB dt (capB dB dt) (capT dB dt) enter leave mine
    hc hds rfl

/-- At that choice the other three pieces' extractor is the identity: as row 0's law (hext of row0_each, Johnson/Desc/Third/Law/Row0Frames.lean) and row 1's (RowOneOwed.idle) ask. -/
theorem idle_zero (a) (τ) (w : Wit Cells Tok MsgT) : (pieceZeroAt F D c₀ (restCap (extsLast (Tok := Tok) F D cs G arr smp decT c₀' mine))).ext a τ w = w := rfl
theorem idle_one (a) (τ) (w : Wit Cells Tok MsgT) : (pieceOneAt F D c₀ c₁ (restCap (extsLast (Tok := Tok) F D cs G arr smp decT c₀' mine))).ext a τ w = w := rfl
theorem idle_three (a) (τ) (w : Wit Cells Tok MsgT) : (pieceThreeAt F D c₀ c₁ c₂ c₃ (restCap (extsLast (Tok := Tok) F D cs G arr smp decT c₀' mine))).ext a τ w = w := rfl

end

end VerifiableInference.OnPublicFiles.Last

#print axioms VerifiableInference.OnPublicFiles.Last.last_list_cap
#print axioms VerifiableInference.OnPublicFiles.Last.idle_zero
#print axioms VerifiableInference.OnPublicFiles.Last.idle_one
#print axioms VerifiableInference.OnPublicFiles.Last.idle_three
