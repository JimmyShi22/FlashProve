-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/LLT25R/LastSeat.lean: THE SEAT's JOIN FOR THE LAST CHAIN:
at the proof file's own description FP (BackAtPure.lean) with the seat of the last chain
(`P2Third.secondSeatOf Z N`, Johnson/Desc/ProofFile/Lot/LastChain.lean), THE LIST OF THE LAST CHAIN's PIECES, AS THE MAKER CUTS THEM, IS THE LIST
OF `eachOwn_last` (Johnson/Flat/Last/LastOnePage.lean): [x₀, x₁, pieceTwoT …, x₃]: FROM ONE FACT OF
MAKE.
  `c0`, `c1`, `c2`, `c3`: the four blocks as the description holds them: K14's second part, the
    taken trees' sources, the request's own proximity test, the chain's end, each carried to the
    file's type of claims.
  `last_flat_pure`: FP's last chain's flat list is [c0, c1, c2, c3]: through `FileDescription.pull` (by
    rfl) and `Chain.retype` (`ToldDesc.last_blocks_in`).
  `c2_is`: c2 IS `(proximityTestKind guardedProximityTestParts π : Block T12 ProofFile.Cl).inside enterOwn leaveOwn`, π := `H2U.proximityTestParametersAt ⟨3,
    none, 2, .K12⟩ N.W`: by `retype_onOwn` (Johnson/Flat/Last/RetypeK12.lean): the first of
    `last_list_cap`'s two facts of make.
  `last_list_pure`: **so the list's equation at FP, at the extractors `extsLast` and the cap's
    errors, from hds alone**: the third stretch of the data is dB :: dt.
  `last_list_of_flat`: the same of WHATEVER head and tail FP's own last chain's flat list has (it
    spends `last_flat_pure`): so Lean holds that the pieces are cut from the description's own list.
Limits. hds is a premise: that the data D of the written rounds has a third stretch that is not
empty is the makers' count, not shown here. a₁ k₁ a₂ k₂ (the two earlier chains' blocks) are
letters: `piecesAt` takes them as they are handed. Nothing on what the blocks do. Nothing on
soundness.
-/
import Johnson.LLT25R.BackAtPure
import Johnson.ToldDescR.LastBlocks
import Johnson.Flat.Last.LastCutCap
import Johnson.Flat.Last.RetypeK12

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace LLT25
open OnBytes OnBytes.Maker
open _root_.Run
open VerifiableInference VerifiableInference.OnPublicFiles VerifiableInference.OnPublicFiles.Last
open VerifiableInference.Desc VerifiableInference.Desc.K12 VerifiableInference.Desc.Sound
open VerifiableInference.Desc.K12.Seat (onOwn enterOwn leaveOwn)
open VerifiableInference.Desc.Third (S₃ takenSources batchLinearConstraintsSecondPart end₃)
open VerifiableInference.Desc.First (S)
open ProofFile (SecondHashFunctionArgument LinksBy SharedSeat Cl)
open ToldDesc (p14At ownAt)

variable (o : SecondHashFunctionArgument) (mk : LinksBy) (Z : ProofFile.Pub) (A : SharedSeat) (N : H2U.Places4)
  (c : Chain S Cl)

/-- The proof file's description at the seat of the last chain `P2Third.secondSeatOf Z N`. -/
abbrev FL : FileDescription (LPFD.Full.XF × OnBytes.Flat.RecFull) := FP o mk Z A (P2Third.secondSeatOf Z N) c

def c0 : Block S₃ Cl := (batchLinearConstraintsSecondPart (p14At Z) : Block S₃ Unit).retype
def c1 : Block S₃ Cl := (takenSources (ownAt N)).retype
def c2 : Block S₃ Cl := (ownAt N).retype
def c3 : Block S₃ Cl :=
  (end₃ [batchLinearConstraintsSecondPart (p14At Z), takenSources (ownAt N), ownAt N] : Block S₃ Unit).retype

/-- **The description's last chain is these four blocks.** -/
theorem last_flat_pure : (FL o mk Z A N c).second.blocksInOrder = [c0 Z, c1 N, c2 N, c3 Z N] :=
  ToldDesc.last_blocks_in o mk Z A N c

/-- **The third is the kind's block at its seat, at the file's own type of claims.** -/
theorem c2_is : c2 N =
    (proximityTestKind guardedProximityTestParts (H2U.proximityTestParametersAt ⟨3, none, 2, .K12⟩ N.W) : Block T12 Cl).inside enterOwn leaveOwn :=
  retype_onOwn guardedProximityTestParts (H2U.proximityTestParametersAt ⟨3, none, 2, .K12⟩ N.W)

section
open OnBytes.Params OnBytes.Slice OnBytes.Slice.ProxRun Fo.Peel Cb Johnson.Pack
open Iop Prob VerifiableInference.Desc.Plain VerifiableInference.Desc.K12.Coin
variable {Cells Tok : Type} (D : WholeD)
  (a₁ : Block (FL o mk Z A N c).S₁ (FL o mk Z A N c).Cl)
  (k₁ : List (Block (FL o mk Z A N c).S₁ (FL o mk Z A N c).Cl))
  (a₂ : Block (FL o mk Z A N c).S₂ (FL o mk Z A N c).Cl)
  (k₂ : List (Block (FL o mk Z A N c).S₂ (FL o mk Z A N c).Cl))
  (rest₁ : (i : ℕ) → (ds : List RDT) → Rest (ckP .two) (frameAt D (allOf D) D.key₁ 0)
    ((FL o mk Z A N c).XiPub × (FL o mk Z A N c).S₁) (Wit Cells Tok MsgT) ds)
  (rest₂ : (i : ℕ) → (ds : List RDT) → Rest (ckP .two) (frameAt D (allOf D) D.key₂ 0)
    (((FL o mk Z A N c).XiPub × (FL o mk Z A N c).S₁) × (FL o mk Z A N c).S₂)
    (Wit Cells Tok MsgT) ds)
  (d wEnd : Wit Cells Tok MsgT) (cs : OnBytes.Codes) {Xi' : Type} (G : FileDescription Xi')
  (arr : ℕ → ℕ → ℕ)
  (smp : (((FL o mk Z A N c).XiPub × (FL o mk Z A N c).S₁ × (FL o mk Z A N c).S₂) ×
    (FL o mk Z A N c).S₃) → (s : Sending) → (i : Fin s.l.length) →
      Option ((sigOf cs s.l).om i).Smp)
  (decT : (ℕ → Option (ℕ × List UInt64)) →
    (((FL o mk Z A N c).XiPub × (FL o mk Z A N c).S₁ × (FL o mk Z A N c).S₂) ×
      (FL o mk Z A N c).S₃) → Option Cells)
  (c₀' : Cells) (dB : RDT) (dt : List RDT) (mine : List Mem)

/-- **The list of the last chain's pieces at the proof file's own description, from one fact of
make.** -/
theorem last_list_pure
    (hds : ds₂ D.ds₃
      (held (P := (FL o mk Z A N c).XiPub × (FL o mk Z A N c).S₁ × (FL o mk Z A N c).S₂) (c0 Z))
      (held (P := (FL o mk Z A N c).XiPub × (FL o mk Z A N c).S₁ × (FL o mk Z A N c).S₂) (c1 N))
      (held (P := (FL o mk Z A N c).XiPub × (FL o mk Z A N c).S₁ × (FL o mk Z A N c).S₂) (c2 N)) =
        dB :: dt) :
    (atDesc (FL o mk Z A N c) (piecesAt (ckP .two) (FL o mk Z A N c) D a₁ k₁ a₂ k₂ (c0 Z)
          [c1 N, c2 N, c3 Z N] rest₁ rest₂
          (restCap (extsLast (FL o mk Z A N c) D cs G arr smp decT c₀' mine)) d wEnd)).p₃ ::
        (atDesc (FL o mk Z A N c) (piecesAt (ckP .two) (FL o mk Z A N c) D a₁ k₁ a₂ k₂ (c0 Z)
          [c1 N, c2 N, c3 Z N] rest₁ rest₂
          (restCap (extsLast (FL o mk Z A N c) D cs G arr smp decT c₀' mine)) d wEnd)).l₃ =
      [pieceZeroAt (FL o mk Z A N c) D (c0 Z)
          (restCap (extsLast (FL o mk Z A N c) D cs G arr smp decT c₀' mine)),
        pieceOneAt (FL o mk Z A N c) D (c0 Z) (c1 N)
          (restCap (extsLast (FL o mk Z A N c) D cs G arr smp decT c₀' mine)),
        pieceTwoT cs G arr smp decT c₀' (H2U.proximityTestParametersAt ⟨3, none, 2, .K12⟩ N.W)
          (baseTwoAt (FL o mk Z A N c) D (c0 Z) (c1 N)) dB dt (capB dB dt) (capT dB dt) enterOwn
          leaveOwn mine,
        pieceThreeAt (FL o mk Z A N c) D (c0 Z) (c1 N) (c2 N) (c3 Z N)
          (restCap (extsLast (FL o mk Z A N c) D cs G arr smp decT c₀' mine))] :=
  last_list_cap (FL o mk Z A N c) D a₁ k₁ a₂ k₂ (c0 Z) (c1 N) (c2 N) (c3 Z N) rest₁ rest₂ d wEnd cs
    G arr smp decT c₀' (H2U.proximityTestParametersAt ⟨3, none, 2, .K12⟩ N.W) dB dt enterOwn leaveOwn mine (c2_is N)
    hds

/-- **The same, of whatever head and tail the description's OWN last chain's flat list has**: so the
pieces are cut from that list and from no other. -/
theorem last_list_of_flat (b₀ : Block (FL o mk Z A N c).S₃ (FL o mk Z A N c).Cl)
    (l : List (Block (FL o mk Z A N c).S₃ (FL o mk Z A N c).Cl))
    (hflat : (FL o mk Z A N c).second.blocksInOrder = b₀ :: l)
    (hds : ds₂ D.ds₃
      (held (P := (FL o mk Z A N c).XiPub × (FL o mk Z A N c).S₁ × (FL o mk Z A N c).S₂) (c0 Z))
      (held (P := (FL o mk Z A N c).XiPub × (FL o mk Z A N c).S₁ × (FL o mk Z A N c).S₂) (c1 N))
      (held (P := (FL o mk Z A N c).XiPub × (FL o mk Z A N c).S₁ × (FL o mk Z A N c).S₂) (c2 N)) =
        dB :: dt) :
    (atDesc (FL o mk Z A N c) (piecesAt (ckP .two) (FL o mk Z A N c) D a₁ k₁ a₂ k₂ b₀ l rest₁ rest₂
          (restCap (extsLast (FL o mk Z A N c) D cs G arr smp decT c₀' mine)) d wEnd)).p₃ ::
        (atDesc (FL o mk Z A N c) (piecesAt (ckP .two) (FL o mk Z A N c) D a₁ k₁ a₂ k₂ b₀ l rest₁
          rest₂ (restCap (extsLast (FL o mk Z A N c) D cs G arr smp decT c₀' mine)) d wEnd)).l₃ =
      [pieceZeroAt (FL o mk Z A N c) D (c0 Z)
          (restCap (extsLast (FL o mk Z A N c) D cs G arr smp decT c₀' mine)),
        pieceOneAt (FL o mk Z A N c) D (c0 Z) (c1 N)
          (restCap (extsLast (FL o mk Z A N c) D cs G arr smp decT c₀' mine)),
        pieceTwoT cs G arr smp decT c₀' (H2U.proximityTestParametersAt ⟨3, none, 2, .K12⟩ N.W)
          (baseTwoAt (FL o mk Z A N c) D (c0 Z) (c1 N)) dB dt (capB dB dt) (capT dB dt) enterOwn
          leaveOwn mine,
        pieceThreeAt (FL o mk Z A N c) D (c0 Z) (c1 N) (c2 N) (c3 Z N)
          (restCap (extsLast (FL o mk Z A N c) D cs G arr smp decT c₀' mine))] := by
  have e := (last_flat_pure o mk Z A N c).symm.trans hflat
  obtain ⟨e₀, e₁⟩ := List.cons.inj e
  subst e₀ e₁
  exact last_list_pure o mk Z A N c D a₁ k₁ a₂ k₂ rest₁ rest₂ d wEnd cs G arr smp decT c₀' dB dt
    mine hds

end

end LLT25

#print axioms LLT25.last_list_of_flat
#print axioms LLT25.last_list_pure
#print axioms LLT25.last_flat_pure
#print axioms LLT25.c2_is
