-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/LLT25R/LastRowOne.lean: OF ROW 1's FOUR FIELDS (`RowOneOwed`,
Johnson/Desc/Sound/QuietRows.lean) THE TWO THAT READ NO TABLE, PAID AT THE SEATED PIECE: the second
piece that the maker cuts of the proof file's own last chain (`pieceOneAt FL D c0 c1 …`,
Johnson/LLT25R/LastSeat.lean).
  `rowOne_leaves_pure`: that piece hands the whole record on as it is (`Piece.LeavesOut id`): by
    `takenSources_leaves`, `leaves_id_seat` (Johnson/Flat/Last/SourcesLeaves.lean) and
    `leavesOutOfBlock`. Carrying the block to the file's type of claims turns no sign of its
    decision, so the block's law serves as it lies.
  `rowOne_same_pure`: so the field `same`, at every promise.
  `rowOne_of_two`: **RowOneOwed at the seated piece FROM ITS FIELDS prom AND pins ALONE** (`idle`:
    by rfl, at the extractors `extsLast`).
Limits. prom and pins speak of the table's promise and of the meaning's letters: they are premises.
Nothing on soundness.
-/
import Johnson.LLT25R.LastOwn
import Johnson.Flat.Last.SourcesLeaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace LLT25
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Slice.ProxRun OnBytes.Maker Fo.Peel Cb
    Johnson.Pack
open Iop Prob _root_.Run
open VerifiableInference VerifiableInference.OnPublicFiles VerifiableInference.OnPublicFiles.Last
open VerifiableInference.Desc VerifiableInference.Desc.K12 VerifiableInference.Desc.Sound
open VerifiableInference.Desc.Plain VerifiableInference.Desc.K12.Coin
open VerifiableInference.Desc.Shared VerifiableInference.Desc.Last
open VerifiableInference.Desc.First (S)
open ProofFile (SecondHashFunctionArgument LinksBy SharedSeat Cl)
open ToldDesc (ownAt)

variable (o : SecondHashFunctionArgument) (mk : LinksBy) (Z : ProofFile.Pub) (A : SharedSeat) (N : H2U.Places4)
  (c : Chain S Cl) {Cells Tok : Type} (D : WholeD)
  (rest₃ : (i : ℕ) → (ds : List RDT) → Rest (ckP .two) (frameAt D (allOf D) D.key₃ (FL o mk Z A N
      c).lastChainFirstTreeNumber) (((FL o mk Z A N c).XiPub × (FL o mk Z A N c).S₁ × (FL o mk Z A N c).S₂) × (FL
                    o mk Z A N c).S₃) (Wit Cells Tok MsgT) ds)

/-- **The seated second piece hands the whole record on as it is.** -/
theorem rowOne_leaves_pure : (pieceOneAt (FL o mk Z A N c) D (c0 Z) (c1 N) rest₃).LeavesOut id :=
  leavesOutOfBlock _ _ _ _ _ _ id (pieceOneAt (FL o mk Z A N c) D (c0 Z) (c1 N) rest₃)
    (leaves_id_seat (c1 N) (takenSources_leaves (ownAt N)))

variable (cs : OnBytes.Codes) {Xi' : Type} (G : FileDescription Xi') (arr : ℕ → ℕ → ℕ)
  (smp : (((FL o mk Z A N c).XiPub × (FL o mk Z A N c).S₁ × (FL o mk Z A N c).S₂) × (FL o mk Z A N
      c).S₃) → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp)
  (decT : (ℕ → Option (ℕ × List UInt64)) → (((FL o mk Z A N c).XiPub × (FL o mk Z A N c).S₁ × (FL o
      mk Z A N c).S₂) × (FL o mk Z A N c).S₃) → Option Cells)
  (c₀' : Cells) (mine : List Mem)
  (Nn : NumbersS) (Mg : MeaningS (FL o mk Z A N c).S₂ ((FL o mk Z A N c).XiPub × (FL o mk Z A N
      c).S₁) (Wit Cells Tok MsgT))
  (ML : MeaningL (FL o mk Z A N c).S₃ (Wit Cells Tok MsgT)) (Pm : PromMeaning (FL o mk Z A N c).S₂)
  (PLm : PromMeaningL (FL o mk Z A N c).S₂ (FL o mk Z A N c).S₃ ((FL o mk Z A N c).XiPub × (FL o mk
      Z A N c).S₁))
  (Oc : (FL o mk Z A N c).XiPub × (FL o mk Z A N c).S₁ → Strs → Prop)

/-- The field `same`, at every promise. -/
theorem rowOne_same_pure (a) (τ) (b) (_ : onQ₃ Nn Mg Pm PLm Oc 1 a)
    (h : (pieceOneAt (FL o mk Z A N c) D (c0 Z) (c1 N) rest₃).ior.red.out a τ = some b) : b.1 = a.1
        :=
  rowOne_leaves_pure o mk Z A N c D rest₃ a τ b h

/-- **RowOneOwed at the seated piece, from prom and pins alone.** -/
theorem rowOne_of_two
    (prom : ∀ a τ b, onQ₃ Nn Mg Pm PLm Oc 1 a →
      (pieceOneAt (FL o mk Z A N c) D (c0 Z) (c1 N) (restCap (extsLast (Tok := Tok) (FL o mk Z A N
          c) D cs G arr
          smp decT c₀' mine))).ior.red.out a τ = some b → onQ₃ Nn Mg Pm PLm Oc 2 b)
    (pins : PinsReadBelow (S₃ := (FL o mk Z A N c).S₃) Nn Mg ML (pieceOneAt (FL o mk Z A N c) D (c0
        Z) (c1 N) (restCap (extsLast (Tok := Tok) (FL o mk Z A N c) D cs G arr smp decT c₀'
            mine))).base) :
    RowOneOwed Nn Mg ML Pm PLm Oc (pieceOneAt (FL o mk Z A N c) D (c0 Z) (c1 N) (restCap (extsLast
        (Tok := Tok) (FL o mk Z A N c) D cs G arr smp decT c₀' mine))) :=
  ⟨fun a τ b ha h => rowOne_same_pure o mk Z A N c D _ Nn Mg Pm PLm Oc a τ b ha h, fun _ _ _ => rfl,
      prom, pins⟩

end LLT25

#print axioms LLT25.rowOne_same_pure
#print axioms LLT25.rowOne_of_two
#print axioms LLT25.rowOne_leaves_pure
