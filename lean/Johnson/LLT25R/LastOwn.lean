-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/LLT25R/LastOwn.lean: THIS FOLDER's HALF OF THE FIELD `leads3_last_chains_table`, AT THE PROOF
FILE's OWN DESCRIPTION: `EachOwn` at the table of the last chain's joints (
Johnson/Desc/Last/BordersLast.lean, Johnson/Desc/Sound/BordersLastQ.lean) OVER THE PIECES THAT THE
MAKER CUTS OF FP's OWN LAST CHAIN, from the four rows' named debts AT THOSE PIECES and one fact of
make.
  `eachOwn_pure`: RowZeroOwed at the first piece, RowOneOwed at the second, RowTwoAtTable at the
    kind's numbers off the plan, the maker's base, the cap's errors and the seat's own enter and
    leave, RowThreeOwed at the fourth, and hds (the third stretch of the data is dB :: dt) give
    `EachOwn (onQ₃ …) (meansQ₃ …) insQ₃ outsQ₃ (· ∈ startLast) 0 (p₃ :: l₃)` at `atDesc FL (piecesAt
    … b₀ l …)`, b₀ :: l whatever FL's own last chain's flat list is. By `last_list_of_flat`
    (LastSeat.lean) and `eachOwn_last` (Johnson/Flat/Last/LastOnePage.lean).
  `rowOne_idle_pure`: of RowOneOwed's four fields `idle` is paid there: the second piece's extractor
    is the identity at the extractors `extsLast`: by rfl.
That conclusion is the premise of the table's files' `leadsThreeAt`
(Johnson/Desc/Sound/TablesGlues.lean), word for word as read in a state of that file that
may differ from the one that ships; that file is not imported here.
Limits. A JOINING: NOTHING OF THE FOUR DEBTS IS PAID, but for `idle`. The table's letters Nn Mg ML
Pm PLm Oc are free: they are not the tied ones of the proof file's chosen letters. No member is
shown. Nothing on soundness.
-/
import Johnson.LLT25R.LastSeat

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
open VerifiableInference.Desc.K12.Seat (enterOwn leaveOwn)
open VerifiableInference.Desc.First (S)
open ProofFile (SecondHashFunctionArgument LinksBy SharedSeat Cl)

variable (o : SecondHashFunctionArgument) (mk : LinksBy) (Z : ProofFile.Pub) (A : SharedSeat) (N : H2U.Places4)
  (c : Chain S Cl) {Cells Tok : Type} (D : WholeD)
  (a₁ : Block (FL o mk Z A N c).S₁ (FL o mk Z A N c).Cl) (k₁ : List (Block (FL o mk Z A N c).S₁ (FL
      o mk Z A N c).Cl))
  (a₂ : Block (FL o mk Z A N c).S₂ (FL o mk Z A N c).Cl) (k₂ : List (Block (FL o mk Z A N c).S₂ (FL
      o mk Z A N c).Cl))
  (rest₁ : (i : ℕ) → (ds : List RDT) → Rest (ckP .two) (frameAt D (allOf D) D.key₁ 0) ((FL o mk Z A
      N c).XiPub × (FL o mk Z A N c).S₁) (Wit Cells Tok MsgT) ds)
  (rest₂ : (i : ℕ) → (ds : List RDT) → Rest (ckP .two) (frameAt D (allOf D) D.key₂ 0) (((FL o mk Z A
      N c).XiPub × (FL o mk Z A N c).S₁) × (FL o mk Z A N c).S₂) (Wit Cells Tok MsgT) ds)
  (d wEnd : Wit Cells Tok MsgT) (cs : OnBytes.Codes) {Xi' : Type} (G : FileDescription Xi') (arr : ℕ → ℕ →
             ℕ)
  (smp : (((FL o mk Z A N c).XiPub × (FL o mk Z A N c).S₁ × (FL o mk Z A N c).S₂) × (FL o mk Z A N
      c).S₃) → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp)
  (decT : (ℕ → Option (ℕ × List UInt64)) → (((FL o mk Z A N c).XiPub × (FL o mk Z A N c).S₁ × (FL o
      mk Z A N c).S₂) × (FL o mk Z A N c).S₃) → Option Cells)
  (c₀' : Cells) (dB : RDT) (dt : List RDT) (mine : List Mem)
  (Nn : NumbersS) (Mg : MeaningS (FL o mk Z A N c).S₂ ((FL o mk Z A N c).XiPub × (FL o mk Z A N
      c).S₁) (Wit Cells Tok MsgT))
  (ML : MeaningL (FL o mk Z A N c).S₃ (Wit Cells Tok MsgT)) (Pm : PromMeaning (FL o mk Z A N c).S₂)
  (PLm : PromMeaningL (FL o mk Z A N c).S₂ (FL o mk Z A N c).S₃ ((FL o mk Z A N c).XiPub × (FL o mk
      Z A N c).S₁))
  (Oc : (FL o mk Z A N c).XiPub × (FL o mk Z A N c).S₁ → Strs → Prop)

/-- **This folder's half of the last chain's field, at the proof file's own description.** -/
theorem eachOwn_pure {num : Fmt.TreeSource → ℕ} {no : ℕ → ℕ} {L mC mS mW : Sg → ℕ → ℕ} {rad : Sg → ℕ}
    {rd : ℕ → ℕ}
    (b₀ : Block (FL o mk Z A N c).S₃ (FL o mk Z A N c).Cl) (l : List (Block (FL o mk Z A N c).S₃ (FL
        o mk Z A N c).Cl))
    (hflat : (FL o mk Z A N c).second.blocksInOrder = b₀ :: l)
    (hds : ds₂ D.ds₃ (held (P := (FL o mk Z A N c).XiPub × (FL o mk Z A N c).S₁ × (FL o mk Z A N
        c).S₂) (c0 Z)) (held (P := (FL o mk Z A N c).XiPub × (FL o mk Z A N c).S₁ × (FL o mk Z A N
        c).S₂) (c1 N)) (held (P := (FL o mk Z A N c).XiPub × (FL o mk Z A N c).S₁ × (FL o mk Z A N
        c).S₂) (c2 N)) = dB :: dt)
    (h₀ : RowZeroOwed Nn Mg ML Pm PLm Oc (pieceZeroAt (FL o mk Z A N c) D (c0 Z) (restCap (extsLast
        (FL o mk Z A N c) D cs G arr smp decT c₀' mine))))
    (h₁ : RowOneOwed Nn Mg ML Pm PLm Oc (pieceOneAt (FL o mk Z A N c) D (c0 Z) (c1 N) (restCap
        (extsLast (FL o mk Z A N c) D cs G arr smp decT c₀' mine))))
    (T₂ : RowTwoAtTable (Fr := frameAt D (allOf D) D.key₃ (FL o mk Z A N c).lastChainFirstTreeNumber) Nn Mg ML Pm
        PLm Oc cs G arr smp (H2U.proximityTestParametersAt ⟨3, none, 2, .K12⟩ N.W) (baseTwoAt (FL o mk Z A N c) D (c0 Z)
                            (c1 N)) dB dt (capB dB dt) (capT dB dt) enterOwn leaveOwn mine num no L mC mS mW rad rd)
    (h₃ : RowThreeOwed Nn Mg Pm PLm Oc (pieceThreeAt (FL o mk Z A N c) D (c0 Z) (c1 N) (c2 N) (c3 Z
        N) (restCap (extsLast (FL o mk Z A N c) D cs G arr smp decT c₀' mine)))) :
    EachOwn (onQ₃ Nn Mg Pm PLm Oc) (meansQ₃ Nn Mg ML) insQ₃ outsQ₃ (· ∈ startLast) 0
      ((atDesc (FL o mk Z A N c) (piecesAt (ckP .two) (FL o mk Z A N c) D a₁ k₁ a₂ k₂ b₀ l rest₁
          rest₂ (restCap (extsLast (FL o mk Z A N c) D cs G arr smp decT c₀' mine)) d wEnd)).p₃ ::
        (atDesc (FL o mk Z A N c) (piecesAt (ckP .two) (FL o mk Z A N c) D a₁ k₁ a₂ k₂ b₀ l rest₁
            rest₂ (restCap (extsLast (FL o mk Z A N c) D cs G arr smp decT c₀' mine)) d wEnd)).l₃)
            := by
  rw [last_list_of_flat o mk Z A N c D a₁ k₁ a₂ k₂ rest₁ rest₂ d wEnd cs G arr smp decT c₀' dB dt
      mine b₀ l hflat hds]
  exact eachOwn_last decT c₀' _ _ _ h₀ h₁ T₂ h₃

/-- Of row 1's four fields `idle` is paid at the seated piece. -/
theorem rowOne_idle_pure (a) (τ) (w : Wit Cells Tok MsgT) :
    (pieceOneAt (FL o mk Z A N c) D (c0 Z) (c1 N) (restCap (extsLast (Tok := Tok) (FL o mk Z A N c)
        D cs G arr smp decT c₀' mine))).ext a τ w = w := rfl

end LLT25

#print axioms LLT25.eachOwn_pure
#print axioms LLT25.rowOne_idle_pure
