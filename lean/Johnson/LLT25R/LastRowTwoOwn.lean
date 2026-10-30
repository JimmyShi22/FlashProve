-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/LLT25R/LastRowTwoOwn.lean: ROW 2's OWN LAW AT THE TABLE FROM "THE ONE ROW THAT IS
OWED" ITSELF, and this file's half of the last chain's field with row 2 in that form.
  `rowTwo_own_of_cand`: general in the table's letters: `Piece.Own` at row 2, at `pieceTwoT`
    (Johnson/Flat/Last/LastOnePage.lean), FROM `TestGivesCand` at that piece
    (Johnson/Desc/Sound/WordsLaw.lean), the three tests on the plan (nodup, seats, fence), prom and
    pins. It is `rowTwo_own`'s proof with the debt `RowTwoOwes` taken out: `TestGivesCand` is
    a premise, to be had from `rowTwo_cand_game` (Johnson/Desc/K12/Coin/RowTwoGame.lean),
    where three of that debt's six fields are gone.
  `eachOwn_of_own`, `e3_of_own`: `eachOwn_pure` and `e3_pure` (LastOwn.lean, LastLeads.lean)
    with row 2's premise in the form `Piece.Own`.
Limits. A JOINING. Nothing on soundness.
-/
import Johnson.LLT25R.LastLeads

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

section
variable {P S₁ S₂ S₃ Cells Tok Cl' : Type} {Fr : Frame} (Nn : NumbersS)
  (Mg : MeaningS S₂ (P × S₁) (Wit Cells Tok MsgT)) (ML : MeaningL S₃ (Wit Cells Tok MsgT)) (Pm :
      PromMeaning S₂)
  (PLm : PromMeaningL S₂ S₃ (P × S₁)) (Oc : P × S₁ → Strs → Prop)
  (cs : OnBytes.Codes) {Xi : Type} (G : FileDescription Xi) (arr : ℕ → ℕ → ℕ)
  (smp : ((P × S₁ × S₂) × S₃) → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om
      i).Smp)
  (decT : (ℕ → Option (ℕ × List UInt64)) → ((P × S₁ × S₂) × S₃) → Option Cells) (c₀ : Cells)
  (π : P12) (base : ℕ) (dB : RDT) (dt : List RDT) (e₀ : ℕ) (εt : Err (uLT (ckP .two) dt))
  (enter : S₃ → Except String T12) (leave : S₃ → T12 → Except String S₃) (mine : List Mem)

/-- **Row 2's own law at the table, from the one row that is owed.** -/
theorem rowTwo_own_of_cand
    (hC : TestGivesCand cs G arr smp (pieceTwoT (Fr := Fr) (Cl := Cl') (Tok := Tok) cs G arr smp
        decT c₀ π base dB dt e₀ εt enter leave mine) mine (onQ₃ Nn Mg Pm PLm Oc 2) (onQ₃ Nn Mg Pm
        PLm Oc 3) (fun a w => ML.rows a.1.2 w) (relAt (meansQ₃ Nn Mg ML) (outsQ₃ 2)))
    (nodup : (mine.map (numOf arr)).Nodup) (seats : SeatsFit cs G mine) (fence : Fenced base mine)
    (prom : ∀ a : ((P × S₁ × S₂) × S₃) × Fr.E.Str, onQ₃ Nn Mg Pm PLm Oc 2 a → Promised cs G smp mine
        a.1 (strsOf Fr a.2))
    (pins : ∀ (a : ((P × S₁ × S₂) × S₃) × Fr.E.Str) w, onQ₃ Nn Mg Pm PLm Oc 2 a → Pinned cs G arr
        smp mine a.1 (strsOf Fr a.2) w →
      meansQ₃ Nn Mg ML .pinV a w ∧ meansQ₃ Nn Mg ML .pinI a w ∧ meansQ₃ Nn Mg ML .pinO a w) :
    (pieceTwoT (Fr := Fr) (Cl := Cl') cs G arr smp decT c₀ π base dB dt e₀ εt enter leave mine).Own
        (onQ₃ Nn Mg Pm PLm Oc 2) (onQ₃ Nn Mg Pm PLm Oc 3)
      (meansQ₃ Nn Mg ML) (insQ₃ 2) (outsQ₃ 2) := by
  intro a ha
  have hG := goodIn_of_words cs G arr smp decT c₀ _ mine (onQ₃ Nn Mg Pm PLm Oc 2) (onQ₃ Nn Mg Pm PLm
      Oc 3) (fun a w => ML.rows a.1.2 w) (relAt (meansQ₃ Nn Mg ML) (outsQ₃ 2)) seats fence (fun _ _
      _ _ _ => rfl)
    (words_of_cand cs G arr smp decT c₀ _ mine _ _ _ _ nodup hC)
  refine Doomed.mono _ _ ?_ (hG a ⟨ha, prom a ha⟩)
  intro τ hτ b hb
  refine ⟨(hτ b hb).1, fun w hw i hi => ?_⟩
  obtain ⟨hp, hr⟩ := (hτ b hb).2 w hw
  obtain ⟨pV, pI, pO⟩ := pins a _ ha hp
  have e' : insL₃ 2 = [.rows, .pinV, .pinI, .pinO] := by decide
  have hi' : i ∈ insL₃ 2 := hi
  rw [e'] at hi'
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi'
  rcases hi' with rfl | rfl | rfl | rfl
  · exact hr
  · exact pV
  · exact pI
  · exact pO

end

section
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


/-- This file's half of the last chain's field, with row 2's premise in the form `Piece.Own`. -/
theorem eachOwn_of_own
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
    (own₂ : (pieceTwoT (Cl := (FL o mk Z A N c).Cl) (Fr := frameAt D (allOf D) D.key₃ (FL o mk Z A N
        c).lastChainFirstTreeNumber) cs G arr smp decT c₀' (H2U.proximityTestParametersAt ⟨3, none, 2, .K12⟩ N.W) (baseTwoAt (FL o mk
                                          Z A N c) D (c0 Z) (c1 N)) dB dt (capB dB dt) (capT dB dt) enterOwn leaveOwn mine).Own (onQ₃
                                          Nn Mg Pm PLm Oc 2) (onQ₃ Nn Mg Pm PLm Oc 3) (meansQ₃ Nn Mg ML) (insQ₃ 2) (outsQ₃ 2))
    (h₃ : RowThreeOwed Nn Mg Pm PLm Oc (pieceThreeAt (FL o mk Z A N c) D (c0 Z) (c1 N) (c2 N) (c3 Z
        N) (restCap (extsLast (FL o mk Z A N c) D cs G arr smp decT c₀' mine)))) :
    EachOwn (onQ₃ Nn Mg Pm PLm Oc) (meansQ₃ Nn Mg ML) insQ₃ outsQ₃ (· ∈ startLast) 0
      ((atDesc (FL o mk Z A N c) (piecesAt (ckP .two) (FL o mk Z A N c) D a₁ k₁ a₂ k₂ b₀ l rest₁
          rest₂ (restCap (extsLast (FL o mk Z A N c) D cs G arr smp decT c₀' mine)) d wEnd)).p₃ ::
          (atDesc (FL o mk Z A N c) (piecesAt (ckP .two) (FL o mk Z A N c) D a₁ k₁ a₂ k₂ b₀ l rest₁
          rest₂ (restCap (extsLast (FL o mk Z A N c) D cs G arr smp decT c₀' mine)) d wEnd)).l₃) :=
          by
  rw [last_list_of_flat o mk Z A N c D a₁ k₁ a₂ k₂ rest₁ rest₂ d wEnd cs G arr smp decT c₀' dB dt
      mine b₀ l hflat hds]
  exact eachOwn_of_rows Nn Mg ML Pm PLm Oc _ _ _ _ h₀ h₁ ⟨own₂, frames_rowTwo Nn Mg ML Pm PLm Oc _⟩
      h₃

/-- e₃ likewise. -/
theorem e3_of_own
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
    (own₂ : (pieceTwoT (Cl := (FL o mk Z A N c).Cl) (Fr := frameAt D (allOf D) D.key₃ (FL o mk Z A N
        c).lastChainFirstTreeNumber) cs G arr smp decT c₀' (H2U.proximityTestParametersAt ⟨3, none, 2, .K12⟩ N.W) (baseTwoAt (FL o mk
                                          Z A N c) D (c0 Z) (c1 N)) dB dt (capB dB dt) (capT dB dt) enterOwn leaveOwn mine).Own (onQ₃
                                          Nn Mg Pm PLm Oc 2) (onQ₃ Nn Mg Pm PLm Oc 3) (meansQ₃ Nn Mg ML) (insQ₃ 2) (outsQ₃ 2))
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
    (eachOwn_of_own o mk Z A N c D a₁ k₁ a₂ k₂ rest₁ rest₂ d wEnd cs G arr smp decT c₀' dB dt mine
        Nn Mg ML Pm PLm Oc b₀ l hflat hds h₀ h₁ own₂ h₃)

end

end LLT25

#print axioms LLT25.eachOwn_of_own
#print axioms LLT25.e3_of_own
#print axioms LLT25.rowTwo_own_of_cand
