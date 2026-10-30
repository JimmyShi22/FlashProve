-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/LLT25R/LastLeads.lean: e₃ AT THE PROOF FILE's OWN DESCRIPTION: the premise `EachLeads
Pl.on₃ Pl.Q₃ 0 (p₃ :: l₃)` of the plain form's rule for a file (`file_leads₃`,
Johnson/Desc/Plain/FileChains.lean), at `Pl.on₃ := onQ₃ …`, `Pl.Q₃ := stepQ₃ …` (the table of the
last chain's joints: Johnson/Desc/Sound/BordersLastQ.lean, TablesGlues.lean), over
the pieces that the maker cuts of FL's own last chain.
  `e3_pure`: from the four rows' named debts at these pieces and hds: by the table's files'
    `leadsThreeAt` at `eachOwn_pure` (LastOwn.lean). So Lean holds that the latter's
    conclusion IS that rule's premise.
hds is paid by `hds_of_planOk` (LastStretch.lean) from the data's yes and the tests on the
plan.
Limits. A JOINING: nothing of the four debts is paid here. The table's letters Nn Mg ML Pm PLm Oc
are free. No member. Nothing on soundness.
-/
import Johnson.LLT25R.LastOwn
import Johnson.LLT25R.LastStretch
import Johnson.Desc.Sound.TablesGlues

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

/-- **The last chain's blocks' plain laws at the table, at the proof file's own description.** -/
theorem e3_pure {num : Fmt.TreeSource → ℕ} {no : ℕ → ℕ} {L mC mS mW : Sg → ℕ → ℕ} {rad : Sg → ℕ} {rd :
       ℕ → ℕ}
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
    EachLeads (onQ₃ (Fr := frameAt D (allOf D) D.key₃ (atDesc (FL o mk Z A N c) (piecesAt (ckP .two)
        (FL o mk Z A N c) D a₁ k₁ a₂ k₂ b₀ l rest₁ rest₂ (restCap (extsLast (FL o mk Z A N c) D cs G
        arr smp decT c₀' mine)) d wEnd)).ft₃) Nn Mg Pm PLm Oc)
      (stepQ₃ (atDesc (FL o mk Z A N c) (piecesAt (ckP .two) (FL o mk Z A N c) D a₁ k₁ a₂ k₂ b₀ l
          rest₁ rest₂ (restCap (extsLast (FL o mk Z A N c) D cs G arr smp decT c₀' mine)) d wEnd))
          Nn Mg ML Pm PLm Oc) 0
      ((atDesc (FL o mk Z A N c) (piecesAt (ckP .two) (FL o mk Z A N c) D a₁ k₁ a₂ k₂ b₀ l rest₁
          rest₂ (restCap (extsLast (FL o mk Z A N c) D cs G arr smp decT c₀' mine)) d wEnd)).p₃ ::
          (atDesc (FL o mk Z A N c) (piecesAt (ckP .two) (FL o mk Z A N c) D a₁ k₁ a₂ k₂ b₀ l rest₁
          rest₂ (restCap (extsLast (FL o mk Z A N c) D cs G arr smp decT c₀' mine)) d wEnd)).l₃) :=
  leadsThreeAt (atDesc (FL o mk Z A N c) (piecesAt (ckP .two) (FL o mk Z A N c) D a₁ k₁ a₂ k₂ b₀ l
      rest₁ rest₂ (restCap (extsLast (FL o mk Z A N c) D cs G arr smp decT c₀' mine)) d wEnd)) Nn Mg
      ML Pm PLm Oc
    (eachOwn_pure o mk Z A N c D a₁ k₁ a₂ k₂ rest₁ rest₂ d wEnd cs G arr smp decT c₀' dB dt mine Nn
        Mg ML Pm PLm Oc b₀ l hflat hds h₀ h₁ T₂ h₃)

end LLT25

#print axioms LLT25.e3_pure
