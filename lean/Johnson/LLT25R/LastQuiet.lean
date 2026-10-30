-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/LLT25R/LastQuiet.lean: ROWS 1 AND 3 OF THE LAST CHAIN's TABLE AT THE SEATED PIECES, AT
THE FILLING OF THE BOOK-KEEPING (`fillAt p R hand ended`,
Johnson/Desc/Last/ShapeAtTable.lean): what is left of them is two conditions ON THE TABLE's LETTERS.
  `yesAtOwn_one`, `yesAtOwn_three`: `YesAtOwn x b` (Johnson/Desc/Last/ShapeRows.lean) at the second
    and fourth piece of FL's own last chain: by LastYes.lean: SO LEAN HOLDS that what that
    file states is this condition.
  `rowOne_pure`: **RowOneOwed at the seated second piece, at the filling with R := the third block's
    declared rounds, FROM `PromReadsBelow` at that piece's base AND `PinsReadBelow` there**: same,
    idle: paid at the seat; prom: by `rowOne_prom`.
  `rowThree_pure`: **RowThreeOwed at the seated fourth piece FROM `PromReadsBelow` at its base**: by
    `rowThree_owed`.
Row 0 is left to other files: nothing of it is typed here.
Limits. PromReadsBelow and PinsReadBelow are conditions on Oc, Pm, Mg, ML: shown at no filling here.
hand and ended are letters. Nothing on soundness.
-/
import Johnson.LLT25R.LastYes
import Johnson.LLT25R.LastRowOne
import Johnson.Desc.Last.ShapeRows

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
open VerifiableInference.Desc.Third (S₃ takenSources batchLinearConstraintsSecondPart end₃ SharedOut)
open VerifiableInference.Desc.First (S)
open ProofFile (SecondHashFunctionArgument LinksBy SharedSeat Cl)
open ToldDesc (p14At ownAt)

variable (o : SecondHashFunctionArgument) (mk : LinksBy) (Z : ProofFile.Pub) (A : SharedSeat) (N : H2U.Places4)
  (c : Chain S Cl) {Cells Tok : Type} (D : WholeD)
  (rest₃ : (i : ℕ) → (ds : List RDT) → Rest (ckP .two) (frameAt D (allOf D) D.key₃ (FL o mk Z A N
      c).lastChainFirstTreeNumber) (((FL o mk Z A N c).XiPub × (FL o mk Z A N c).S₁ × (FL o mk Z A N c).S₂) × (FL
                    o mk Z A N c).S₃) (Wit Cells Tok MsgT) ds)

theorem yesAtOwn_one : YesAtOwn (pieceOneAt (FL o mk Z A N c) D (c0 Z) (c1 N) rest₃) (takenSources
    (c2 N)) :=
  yes_one_pure o mk Z A N c D rest₃

theorem yesAtOwn_three : YesAtOwn (pieceThreeAt (FL o mk Z A N c) D (c0 Z) (c1 N) (c2 N) (c3 Z N)
    rest₃) (end₃ [batchLinearConstraintsSecondPart (p14At Z), takenSources (c2 N), c2 N]) :=
  yes_three_pure o mk Z A N c D rest₃

variable (cs : OnBytes.Codes) {Xi' : Type} (G : FileDescription Xi') (arr : ℕ → ℕ → ℕ)
  (smp : (((FL o mk Z A N c).XiPub × (FL o mk Z A N c).S₁ × (FL o mk Z A N c).S₂) × (FL o mk Z A N
      c).S₃) → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp)
  (decT : (ℕ → Option (ℕ × List UInt64)) → (((FL o mk Z A N c).XiPub × (FL o mk Z A N c).S₁ × (FL o
      mk Z A N c).S₂) × (FL o mk Z A N c).S₃) → Option Cells)
  (c₀' : Cells) (mine : List Mem)
  (Nn : NumbersS) (Mg : MeaningS (FL o mk Z A N c).S₂ ((FL o mk Z A N c).XiPub × (FL o mk Z A N
      c).S₁) (Wit Cells Tok MsgT))
  (ML : MeaningL (FL o mk Z A N c).S₃ (Wit Cells Tok MsgT)) (Pm : PromMeaning (FL o mk Z A N c).S₂)
  (Oc : (FL o mk Z A N c).XiPub × (FL o mk Z A N c).S₁ → Strs → Prop) (p : Third.P₁₄) (R : List
      Fmt.DeclaredRound)
  (hand : (FL o mk Z A N c).XiPub × (FL o mk Z A N c).S₁ → Option Handed) (ended : (FL o mk Z A N
      c).S₂ → Option SharedOut)

/-- **Row 1 at the seated piece, from two conditions on the table's letters.** -/
theorem rowOne_pure
    (hr : PromReadsBelow Nn Pm Oc (pieceOneAt (FL o mk Z A N c) D (c0 Z) (c1 N) (restCap (extsLast
        (Tok := Tok) (FL o mk Z A N c) D cs G arr smp decT c₀' mine))).base)
    (pins : PinsReadBelow (S₃ := (FL o mk Z A N c).S₃) Nn Mg ML (pieceOneAt (FL o mk Z A N c) D (c0
        Z) (c1 N) (restCap (extsLast (Tok := Tok) (FL o mk Z A N c) D cs G arr smp decT c₀'
        mine))).base) :
    RowOneOwed Nn Mg ML Pm (fillAt p (c2 N).rounds hand ended) Oc (pieceOneAt (FL o mk Z A N c) D
        (c0 Z) (c1 N) (restCap (extsLast (Tok := Tok) (FL o mk Z A N c) D cs G arr smp decT c₀'
        mine))) :=
  rowOne_of_two o mk Z A N c D cs G arr smp decT c₀' mine Nn Mg ML Pm _ Oc
    (rowOne_prom Nn Mg Pm Oc p hand ended (c2 N) _ (yesAtOwn_one o mk Z A N c D _) hr) pins

/-- **Row 3 at the seated piece, from one condition on the table's letters.** -/
theorem rowThree_pure
    (hr : PromReadsBelow Nn Pm Oc (pieceThreeAt (FL o mk Z A N c) D (c0 Z) (c1 N) (c2 N) (c3 Z N)
        rest₃).base) :
    RowThreeOwed Nn Mg Pm (fillAt p R hand ended) Oc (pieceThreeAt (FL o mk Z A N c) D (c0 Z) (c1 N)
        (c2 N) (c3 Z N) rest₃) :=
  rowThree_owed Nn Mg Pm Oc p R hand ended _ _ (yesAtOwn_three o mk Z A N c D rest₃) hr

end LLT25

#print axioms LLT25.yesAtOwn_one
#print axioms LLT25.yesAtOwn_three
#print axioms LLT25.rowOne_pure
#print axioms LLT25.rowThree_pure
