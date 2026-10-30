-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/LLT25R/LastRowB.lean: THE LAST TABLE's LAW WITH ROW 0's DEBT AS ONE PREMISE, IN ITS
PAYER's OWN CONCLUSION's FORM. `own3_at_rc` | `e3_at_rc` (LastAtRc.lean) take row 0 apart by
one law of row 0's files (`rowZeroOwed_oc`) and so ask joint and dot. Those files have
tighter laws with the same end. Here the end itself is the premise.
  `own3_at_rowB`, `e3_at_rowB`: **`own3_at_rc`'s | `e3_at_rc`'s statements with
    row0B : `RowZeroOwed … (fillAt … (endedX X)) Oc ‹row 0's piece›` in the place of joint and
    dot.** `fillAt … (endedX X)` is `besideL (fillZ …) X` (`beside_is_fill`,
    LastRowZeroB.lean). The law lifts row0B to the layer on the last chain's own state
    (`ownLiftS`, `framesLiftS`; `earn₀_tree`). Neither Pw nor wSeat is a letter here.
  `own3_at_rowB_letter`, `e3_at_rowB_letter`: the same at a meaning M₁ that is its own `meaningSig
    …`.
What kind of premise row0B is: a law of ONE piece between the promises at two borders (its own law
and "what rides"): of the kinds' laws' kind; no fact asked at every state.
Limits: those of LastAtRc.lean. WHICH OF ROW 0's FILES' LAWS END IN row0B's TERM TO THE SIGN, AT
WHICH LETTERS, IS HELD HERE FOR `rowZeroOwed_oc` ALONE. NO MEMBER. Nothing on soundness.

-/
import Johnson.LLT25R.LastRcCore

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
open VerifiableInference.Desc.K12.Seat (enterOwn leaveOwn onOwn)
open VerifiableInference.Desc.Third (SharedOut firstOfS sharedOfEnd)
open VerifiableInference.Desc.Third.Law
open VerifiableInference.Desc.First (S ModelPart Item Meaning Numbers openSets sampledIn start)
open VerifiableInference.Desc.K13 (Where)
open _root_.Desc.K14 (St)
open ProofFile (SecondHashFunctionArgument LinksBy SharedSeat Cl)
open ToldDesc (p14At)
open _root_.Desc.K14.Law.Fence (CoreFacts MemberFacts)
open H2K.Pin (NTuple)

variable (o : SecondHashFunctionArgument) (mk : LinksBy) (Z : ProofFile.Pub) (N : H2U.Places4) (c : Chain S Cl) {Cells Tok
          P₀ : Type} (D : WholeD) {Xi' : Type} (G : FileDescription Xi') (arr : ℕ → ℕ → ℕ) (dB : RDT) (dt : List
                 RDT) (get : (FL o mk Z (seatK Z N) N c).XiPub × (FL o mk Z (seatK Z N) N c).S₁ → P₀ × First.S)
    (smp₁ : P₀ × First.S → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf (p14At Z).codes
    s.l).om i).Smp) (smp₂ : St → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf (p14At
    Z).codes s.l).om i).Smp) (ms₁ ms₂ : List Mem) (decT₁ : (ℕ → Option (ℕ × List UInt64)) → P₀ ×
    First.S → Option Cells) (decT₂ : (ℕ → Option (ℕ × List UInt64)) → St → Option Cells) (M₁ :
    Meaning P₀ (Wit Cells Tok MsgT)) (MS : MeaningS St ((FL o mk Z (seatK Z N) N c).XiPub × (FL o mk
    Z (seatK Z N) N c).S₁) (Wit Cells Tok MsgT)) (stOf : St → OnBytes.Statement) (bookOf : St →
    OnBytes.TreeBook) (Pm₀ : PromMeaning St) (N₁ : Numbers) (Ns : NumbersS) (links : List ModelPart) (X :
          St → Bool) (r : Fmt.M1.Stage → ℕ) (Ld :
          VerifiableInference.Desc.K12.Door.Laid)

variable (decT : (ℕ → Option (ℕ × List UInt64)) → (((FL o mk Z (seatK Z N) N c).XiPub × (FL o mk Z
    (seatK Z N) N c).S₁ × St) × (FL o mk Z (seatK Z N) N c).S₃) → Option Cells) (c₀' : Cells) (a₁ :
    Block (FL o mk Z (seatK Z N) N c).S₁ (FL o mk Z (seatK Z N) N c).Cl) (k₁ : List (Block (FL o mk
    Z (seatK Z N) N c).S₁ (FL o mk Z (seatK Z N) N c).Cl)) (a₂ : Block St (FL o mk Z (seatK Z N) N
    c).Cl) (k₂ : List (Block St (FL o mk Z (seatK Z N) N c).Cl)) (rest₁ : (i : ℕ) → (ds : List RDT)
    → Rest (ckP .two) (frameAt D (allOf D) D.key₁ 0) ((FL o mk Z (seatK Z N) N c).XiPub × (FL o mk Z
    (seatK Z N) N c).S₁) (Wit Cells Tok MsgT) ds) (rest₂ : (i : ℕ) → (ds : List RDT) → Rest (ckP
    .two) (frameAt D (allOf D) D.key₂ 0) (((FL o mk Z (seatK Z N) N c).XiPub × (FL o mk Z (seatK Z
    N) N c).S₁) × St) (Wit Cells Tok MsgT) ds) (d wEnd : Wit Cells Tok MsgT)

variable (Rc : (FL o mk Z (seatK Z N) N c).XiPub × (FL o mk Z (seatK Z N) N c).S₁ → Prop)

variable (Rc : (FL o mk Z (seatK Z N) N c).XiPub × (FL o mk Z (seatK Z N) N c).S₁ → Prop)

/-- **e₃ with row 0's debt as one premise.** -/
theorem e3_at_rowB (hRc : ∀ q y, ocEnd get N₁ (meaningSig (p14At Z).codes G arr smp₁ ms₁ decT₁ M₁)
    links (First.flatPlaces true links true) q y → Rc q → (get q).2.failed = none → ToldDesc.rcLastB
    0 (vAt Z N₁) Ld (p14At Z).codes (get q).2 = true) (hP : PlanOk₃ o mk Z N c D G arr dB dt ms₁ ms₂
    N₁ Ns links (First.flatPlaces true links true) r (N₁.treesAt none) 0 1 (vAt Z N₁) Ld) (hX :
    XSamples (p14At Z).codes (p14At Z).S X) (hR : Readers₃ o mk Z N c D G arr get smp₁ smp₂ ms₁ ms₂
    decT₁ decT₂ M₁ MS stOf bookOf Pm₀ N₁ Ns X (fun q y => ocEnd get N₁ (meaningSig (p14At Z).codes G
    arr smp₁ ms₁ decT₁ M₁) links (First.flatPlaces true links true) q y ∧ Rc q) 1 (vAt Z N₁)) (row0B
    : RowZeroOwed (tiedNumbers N₁ Ns) (tiedMeaning get (meaningSig (p14At Z).codes G arr smp₁ ms₁
    decT₁ M₁) (meaningSigS (p14At Z).codes G arr smp₂ ms₂ decT₂ MS)) (⟨rowsOpen (p14At Z).codes arr
    D.t₁ D.t₂⟩ : MeaningL (FL o mk Z (seatK Z N) N c).S₃ (Wit Cells Tok MsgT)) (promSigS (p14At
    Z).codes G smp₂ ms₂ stOf bookOf Pm₀) (fillAt (p14At Z) (c2 N).rounds (fun q => firstOfS (get
    q).2) (endedX X)) (fun q y => ocEnd get N₁ (meaningSig (p14At Z).codes G arr smp₁ ms₁ decT₁ M₁)
    links (First.flatPlaces true links true) q y ∧ Rc q) (pieceZeroAt (FL o mk Z (seatK Z N) N c) D
    (c0 Z) (restCap (extsLast (Tok := Tok) (FL o mk Z (seatK Z N) N c) D (p14At Z).codes G arr
    (smpLast (p14At Z).codes smp₁ smp₂ get Ns) decT c₀' (mineOf ms₁ ms₂ N₁ Ns))))) (b₀ : Block (FL o
    mk Z (seatK Z N) N c).S₃ (FL o mk Z (seatK Z N) N c).Cl) (l : List (Block (FL o mk Z (seatK Z N)
    N c).S₃ (FL o mk Z (seatK Z N) N c).Cl)) (hflat : (FL o mk Z (seatK Z N) N c).second.blocksInOrder = b₀
    :: l) : EachLeads (onQ₃ (Fr := frameAt D (allOf D) D.key₃ (atDesc (FL o mk Z (seatK Z N) N c)
    (piecesAt (ckP .two) (FL o mk Z (seatK Z N) N c) D a₁ k₁ a₂ k₂ b₀ l rest₁ rest₂ (restCap
    (extsLast (Tok := Tok) (FL o mk Z (seatK Z N) N c) D (p14At Z).codes G arr (smpLast (p14At
    Z).codes smp₁ smp₂ get Ns) decT c₀' (mineOf ms₁ ms₂ N₁ Ns))) d wEnd)).ft₃) (tiedNumbers N₁ Ns)
    (tiedMeaning get (meaningSig (p14At Z).codes G arr smp₁ ms₁ decT₁ M₁) (meaningSigS (p14At
    Z).codes G arr smp₂ ms₂ decT₂ MS)) (promSigS (p14At Z).codes G smp₂ ms₂ stOf bookOf Pm₀)
    (besideS (fillAt (p14At Z) (c2 N).rounds (fun q => firstOfS (get q).2) (endedX X)) (yTree (p14At
    Z).codes (p14At Z).S)) (fun q y => ocEnd get N₁ (meaningSig (p14At Z).codes G arr smp₁ ms₁ decT₁
    M₁) links (First.flatPlaces true links true) q y ∧ Rc q)) (stepQ₃ (atDesc (FL o mk Z (seatK Z N)
    N c) (piecesAt (ckP .two) (FL o mk Z (seatK Z N) N c) D a₁ k₁ a₂ k₂ b₀ l rest₁ rest₂ (restCap
    (extsLast (Tok := Tok) (FL o mk Z (seatK Z N) N c) D (p14At Z).codes G arr (smpLast (p14At
    Z).codes smp₁ smp₂ get Ns) decT c₀' (mineOf ms₁ ms₂ N₁ Ns))) d wEnd)) (tiedNumbers N₁ Ns)
    (tiedMeaning get (meaningSig (p14At Z).codes G arr smp₁ ms₁ decT₁ M₁) (meaningSigS (p14At
    Z).codes G arr smp₂ ms₂ decT₂ MS)) (⟨rowsOpen (p14At Z).codes arr D.t₁ D.t₂⟩ : MeaningL (FL o mk
    Z (seatK Z N) N c).S₃ (Wit Cells Tok MsgT)) (promSigS (p14At Z).codes G smp₂ ms₂ stOf bookOf
    Pm₀) (besideS (fillAt (p14At Z) (c2 N).rounds (fun q => firstOfS (get q).2) (endedX X)) (yTree
    (p14At Z).codes (p14At Z).S)) (fun q y => ocEnd get N₁ (meaningSig (p14At Z).codes G arr smp₁
    ms₁ decT₁ M₁) links (First.flatPlaces true links true) q y ∧ Rc q)) 0 ((atDesc (FL o mk Z (seatK
    Z N) N c) (piecesAt (ckP .two) (FL o mk Z (seatK Z N) N c) D a₁ k₁ a₂ k₂ b₀ l rest₁ rest₂
    (restCap (extsLast (Tok := Tok) (FL o mk Z (seatK Z N) N c) D (p14At Z).codes G arr (smpLast
    (p14At Z).codes smp₁ smp₂ get Ns) decT c₀' (mineOf ms₁ ms₂ N₁ Ns))) d wEnd)).p₃ :: (atDesc (FL o
    mk Z (seatK Z N) N c) (piecesAt (ckP .two) (FL o mk Z (seatK Z N) N c) D a₁ k₁ a₂ k₂ b₀ l rest₁
    rest₂ (restCap (extsLast (Tok := Tok) (FL o mk Z (seatK Z N) N c) D (p14At Z).codes G arr
    (smpLast (p14At Z).codes smp₁ smp₂ get Ns) decT c₀' (mineOf ms₁ ms₂ N₁ Ns))) d wEnd)).l₃) :=
  e3_of_core decT c₀' a₁ k₁ a₂ k₂ rest₁ rest₂ d wEnd (LastCore₃.atRc Rc hP (FoldFirst₃.ofRc o mk Z N
      c D G arr dB dt get smp₁ smp₂ ms₁ ms₂ decT₁ decT₂ M₁ MS stOf bookOf Pm₀ N₁ Ns links X r Ld Rc
      hRc hP) (FoldRest₃.ofX hP hX) hR) row0B b₀ l hflat

/-- **The same in the tables' files' own form (`EachOwn`, Johnson/Desc/Sound/Spine.lean).** -/
theorem own3_at_rowB (hRc : ∀ q y, ocEnd get N₁ (meaningSig (p14At Z).codes G arr smp₁ ms₁ decT₁ M₁)
    links (First.flatPlaces true links true) q y → Rc q → (get q).2.failed = none → ToldDesc.rcLastB
    0 (vAt Z N₁) Ld (p14At Z).codes (get q).2 = true) (hP : PlanOk₃ o mk Z N c D G arr dB dt ms₁ ms₂
    N₁ Ns links (First.flatPlaces true links true) r (N₁.treesAt none) 0 1 (vAt Z N₁) Ld) (hX :
    XSamples (p14At Z).codes (p14At Z).S X) (hR : Readers₃ o mk Z N c D G arr get smp₁ smp₂ ms₁ ms₂
    decT₁ decT₂ M₁ MS stOf bookOf Pm₀ N₁ Ns X (fun q y => ocEnd get N₁ (meaningSig (p14At Z).codes G
    arr smp₁ ms₁ decT₁ M₁) links (First.flatPlaces true links true) q y ∧ Rc q) 1 (vAt Z N₁)) (row0B
    : RowZeroOwed (tiedNumbers N₁ Ns) (tiedMeaning get (meaningSig (p14At Z).codes G arr smp₁ ms₁
    decT₁ M₁) (meaningSigS (p14At Z).codes G arr smp₂ ms₂ decT₂ MS)) (⟨rowsOpen (p14At Z).codes arr
    D.t₁ D.t₂⟩ : MeaningL (FL o mk Z (seatK Z N) N c).S₃ (Wit Cells Tok MsgT)) (promSigS (p14At
    Z).codes G smp₂ ms₂ stOf bookOf Pm₀) (fillAt (p14At Z) (c2 N).rounds (fun q => firstOfS (get
    q).2) (endedX X)) (fun q y => ocEnd get N₁ (meaningSig (p14At Z).codes G arr smp₁ ms₁ decT₁ M₁)
    links (First.flatPlaces true links true) q y ∧ Rc q) (pieceZeroAt (FL o mk Z (seatK Z N) N c) D
    (c0 Z) (restCap (extsLast (Tok := Tok) (FL o mk Z (seatK Z N) N c) D (p14At Z).codes G arr
    (smpLast (p14At Z).codes smp₁ smp₂ get Ns) decT c₀' (mineOf ms₁ ms₂ N₁ Ns))))) (b₀ : Block (FL o
    mk Z (seatK Z N) N c).S₃ (FL o mk Z (seatK Z N) N c).Cl) (l : List (Block (FL o mk Z (seatK Z N)
    N c).S₃ (FL o mk Z (seatK Z N) N c).Cl)) (hflat : (FL o mk Z (seatK Z N) N c).second.blocksInOrder = b₀
    :: l) : EachOwn (onQ₃ (Fr := frameAt D (allOf D) D.key₃ (atDesc (FL o mk Z (seatK Z N) N c)
    (piecesAt (ckP .two) (FL o mk Z (seatK Z N) N c) D a₁ k₁ a₂ k₂ b₀ l rest₁ rest₂ (restCap
    (extsLast (Tok := Tok) (FL o mk Z (seatK Z N) N c) D (p14At Z).codes G arr (smpLast (p14At
    Z).codes smp₁ smp₂ get Ns) decT c₀' (mineOf ms₁ ms₂ N₁ Ns))) d wEnd)).ft₃) (tiedNumbers N₁ Ns)
    (tiedMeaning get (meaningSig (p14At Z).codes G arr smp₁ ms₁ decT₁ M₁) (meaningSigS (p14At
    Z).codes G arr smp₂ ms₂ decT₂ MS)) (promSigS (p14At Z).codes G smp₂ ms₂ stOf bookOf Pm₀)
    (besideS (fillAt (p14At Z) (c2 N).rounds (fun q => firstOfS (get q).2) (endedX X)) (yTree (p14At
    Z).codes (p14At Z).S)) (fun q y => ocEnd get N₁ (meaningSig (p14At Z).codes G arr smp₁ ms₁ decT₁
    M₁) links (First.flatPlaces true links true) q y ∧ Rc q)) (meansQ₃ (tiedNumbers N₁ Ns)
    (tiedMeaning get (meaningSig (p14At Z).codes G arr smp₁ ms₁ decT₁ M₁) (meaningSigS (p14At
    Z).codes G arr smp₂ ms₂ decT₂ MS)) (⟨rowsOpen (p14At Z).codes arr D.t₁ D.t₂⟩ : MeaningL (FL o mk
    Z (seatK Z N) N c).S₃ (Wit Cells Tok MsgT))) insQ₃ outsQ₃ (· ∈ startLast) 0 ((atDesc (FL o mk Z
    (seatK Z N) N c) (piecesAt (ckP .two) (FL o mk Z (seatK Z N) N c) D a₁ k₁ a₂ k₂ b₀ l rest₁ rest₂
    (restCap (extsLast (Tok := Tok) (FL o mk Z (seatK Z N) N c) D (p14At Z).codes G arr (smpLast
    (p14At Z).codes smp₁ smp₂ get Ns) decT c₀' (mineOf ms₁ ms₂ N₁ Ns))) d wEnd)).p₃ :: (atDesc (FL o
    mk Z (seatK Z N) N c) (piecesAt (ckP .two) (FL o mk Z (seatK Z N) N c) D a₁ k₁ a₂ k₂ b₀ l rest₁
    rest₂ (restCap (extsLast (Tok := Tok) (FL o mk Z (seatK Z N) N c) D (p14At Z).codes G arr
    (smpLast (p14At Z).codes smp₁ smp₂ get Ns) decT c₀' (mineOf ms₁ ms₂ N₁ Ns))) d wEnd)).l₃) :=
  own3_of_core decT c₀' a₁ k₁ a₂ k₂ rest₁ rest₂ d wEnd (LastCore₃.atRc Rc hP (FoldFirst₃.ofRc o mk Z
      N c D G arr dB dt get smp₁ smp₂ ms₁ ms₂ decT₁ decT₂ M₁ MS stOf bookOf Pm₀ N₁ Ns links X r Ld
      Rc hRc hP) (FoldRest₃.ofX hP hX) hR) row0B b₀ l hflat

/-- **e₃ so, at a meaning that is its own `meaningSig …`.** -/
theorem e3_at_rowB_letter (hSig : meaningSig (p14At Z).codes G arr smp₁ ms₁ decT₁ M₁ = M₁) (hRc : ∀
    q y, ocEnd get N₁ M₁ links (First.flatPlaces true links true) q y → Rc q → (get q).2.failed =
    none → ToldDesc.rcLastB 0 (vAt Z N₁) Ld (p14At Z).codes (get q).2 = true) (hP : PlanOk₃ o mk Z N
    c D G arr dB dt ms₁ ms₂ N₁ Ns links (First.flatPlaces true links true) r (N₁.treesAt none) 0 1
    (vAt Z N₁) Ld) (hX : XSamples (p14At Z).codes (p14At Z).S X) (hR : Readers₃ o mk Z N c D G arr
    get smp₁ smp₂ ms₁ ms₂ decT₁ decT₂ M₁ MS stOf bookOf Pm₀ N₁ Ns X (fun q y => ocEnd get N₁ M₁
    links (First.flatPlaces true links true) q y ∧ Rc q) 1 (vAt Z N₁)) (row0B : RowZeroOwed
    (tiedNumbers N₁ Ns) (tiedMeaning get M₁ (meaningSigS (p14At Z).codes G arr smp₂ ms₂ decT₂ MS))
    (⟨rowsOpen (p14At Z).codes arr D.t₁ D.t₂⟩ : MeaningL (FL o mk Z (seatK Z N) N c).S₃ (Wit Cells
    Tok MsgT)) (promSigS (p14At Z).codes G smp₂ ms₂ stOf bookOf Pm₀) (fillAt (p14At Z) (c2 N).rounds
    (fun q => firstOfS (get q).2) (endedX X)) (fun q y => ocEnd get N₁ M₁ links (First.flatPlaces
    true links true) q y ∧ Rc q) (pieceZeroAt (FL o mk Z (seatK Z N) N c) D (c0 Z) (restCap
    (extsLast (Tok := Tok) (FL o mk Z (seatK Z N) N c) D (p14At Z).codes G arr (smpLast (p14At
    Z).codes smp₁ smp₂ get Ns) decT c₀' (mineOf ms₁ ms₂ N₁ Ns))))) (b₀ : Block (FL o mk Z (seatK Z
    N) N c).S₃ (FL o mk Z (seatK Z N) N c).Cl) (l : List (Block (FL o mk Z (seatK Z N) N c).S₃ (FL o
    mk Z (seatK Z N) N c).Cl)) (hflat : (FL o mk Z (seatK Z N) N c).second.blocksInOrder = b₀ :: l) :
    EachLeads (onQ₃ (Fr := frameAt D (allOf D) D.key₃ (atDesc (FL o mk Z (seatK Z N) N c) (piecesAt
    (ckP .two) (FL o mk Z (seatK Z N) N c) D a₁ k₁ a₂ k₂ b₀ l rest₁ rest₂ (restCap (extsLast (Tok :=
    Tok) (FL o mk Z (seatK Z N) N c) D (p14At Z).codes G arr (smpLast (p14At Z).codes smp₁ smp₂ get
    Ns) decT c₀' (mineOf ms₁ ms₂ N₁ Ns))) d wEnd)).ft₃) (tiedNumbers N₁ Ns) (tiedMeaning get M₁
    (meaningSigS (p14At Z).codes G arr smp₂ ms₂ decT₂ MS)) (promSigS (p14At Z).codes G smp₂ ms₂ stOf
    bookOf Pm₀) (besideS (fillAt (p14At Z) (c2 N).rounds (fun q => firstOfS (get q).2) (endedX X))
    (yTree (p14At Z).codes (p14At Z).S)) (fun q y => ocEnd get N₁ M₁ links (First.flatPlaces true
    links true) q y ∧ Rc q)) (stepQ₃ (atDesc (FL o mk Z (seatK Z N) N c) (piecesAt (ckP .two) (FL o
    mk Z (seatK Z N) N c) D a₁ k₁ a₂ k₂ b₀ l rest₁ rest₂ (restCap (extsLast (Tok := Tok) (FL o mk Z
    (seatK Z N) N c) D (p14At Z).codes G arr (smpLast (p14At Z).codes smp₁ smp₂ get Ns) decT c₀'
    (mineOf ms₁ ms₂ N₁ Ns))) d wEnd)) (tiedNumbers N₁ Ns) (tiedMeaning get M₁ (meaningSigS (p14At
    Z).codes G arr smp₂ ms₂ decT₂ MS)) (⟨rowsOpen (p14At Z).codes arr D.t₁ D.t₂⟩ : MeaningL (FL o mk
    Z (seatK Z N) N c).S₃ (Wit Cells Tok MsgT)) (promSigS (p14At Z).codes G smp₂ ms₂ stOf bookOf
    Pm₀) (besideS (fillAt (p14At Z) (c2 N).rounds (fun q => firstOfS (get q).2) (endedX X)) (yTree
    (p14At Z).codes (p14At Z).S)) (fun q y => ocEnd get N₁ M₁ links (First.flatPlaces true links
    true) q y ∧ Rc q)) 0 ((atDesc (FL o mk Z (seatK Z N) N c) (piecesAt (ckP .two) (FL o mk Z (seatK
    Z N) N c) D a₁ k₁ a₂ k₂ b₀ l rest₁ rest₂ (restCap (extsLast (Tok := Tok) (FL o mk Z (seatK Z N)
    N c) D (p14At Z).codes G arr (smpLast (p14At Z).codes smp₁ smp₂ get Ns) decT c₀' (mineOf ms₁ ms₂
    N₁ Ns))) d wEnd)).p₃ :: (atDesc (FL o mk Z (seatK Z N) N c) (piecesAt (ckP .two) (FL o mk Z
    (seatK Z N) N c) D a₁ k₁ a₂ k₂ b₀ l rest₁ rest₂ (restCap (extsLast (Tok := Tok) (FL o mk Z
    (seatK Z N) N c) D (p14At Z).codes G arr (smpLast (p14At Z).codes smp₁ smp₂ get Ns) decT c₀'
    (mineOf ms₁ ms₂ N₁ Ns))) d wEnd)).l₃) := by
  have T := e3_at_rowB o mk Z N c D G arr dB dt get smp₁ smp₂ ms₁ ms₂ decT₁ decT₂ M₁ MS stOf bookOf
      Pm₀ N₁ Ns links X r Ld decT c₀' a₁ k₁ a₂ k₂ rest₁ rest₂ d wEnd Rc
  rw [hSig] at T
  exact T hRc hP hX hR row0B b₀ l hflat

/-- **The same in the tables' files' own form (`EachOwn`, Johnson/Desc/Sound/Spine.lean).** -/
theorem own3_at_rowB_letter (hSig : meaningSig (p14At Z).codes G arr smp₁ ms₁ decT₁ M₁ = M₁) (hRc :
    ∀ q y, ocEnd get N₁ M₁ links (First.flatPlaces true links true) q y → Rc q → (get q).2.failed =
    none → ToldDesc.rcLastB 0 (vAt Z N₁) Ld (p14At Z).codes (get q).2 = true) (hP : PlanOk₃ o mk Z N
    c D G arr dB dt ms₁ ms₂ N₁ Ns links (First.flatPlaces true links true) r (N₁.treesAt none) 0 1
    (vAt Z N₁) Ld) (hX : XSamples (p14At Z).codes (p14At Z).S X) (hR : Readers₃ o mk Z N c D G arr
    get smp₁ smp₂ ms₁ ms₂ decT₁ decT₂ M₁ MS stOf bookOf Pm₀ N₁ Ns X (fun q y => ocEnd get N₁ M₁
    links (First.flatPlaces true links true) q y ∧ Rc q) 1 (vAt Z N₁)) (row0B : RowZeroOwed
    (tiedNumbers N₁ Ns) (tiedMeaning get M₁ (meaningSigS (p14At Z).codes G arr smp₂ ms₂ decT₂ MS))
    (⟨rowsOpen (p14At Z).codes arr D.t₁ D.t₂⟩ : MeaningL (FL o mk Z (seatK Z N) N c).S₃ (Wit Cells
    Tok MsgT)) (promSigS (p14At Z).codes G smp₂ ms₂ stOf bookOf Pm₀) (fillAt (p14At Z) (c2 N).rounds
    (fun q => firstOfS (get q).2) (endedX X)) (fun q y => ocEnd get N₁ M₁ links (First.flatPlaces
    true links true) q y ∧ Rc q) (pieceZeroAt (FL o mk Z (seatK Z N) N c) D (c0 Z) (restCap
    (extsLast (Tok := Tok) (FL o mk Z (seatK Z N) N c) D (p14At Z).codes G arr (smpLast (p14At
    Z).codes smp₁ smp₂ get Ns) decT c₀' (mineOf ms₁ ms₂ N₁ Ns))))) (b₀ : Block (FL o mk Z (seatK Z
    N) N c).S₃ (FL o mk Z (seatK Z N) N c).Cl) (l : List (Block (FL o mk Z (seatK Z N) N c).S₃ (FL o
    mk Z (seatK Z N) N c).Cl)) (hflat : (FL o mk Z (seatK Z N) N c).second.blocksInOrder = b₀ :: l) : EachOwn
    (onQ₃ (Fr := frameAt D (allOf D) D.key₃ (atDesc (FL o mk Z (seatK Z N) N c) (piecesAt (ckP .two)
    (FL o mk Z (seatK Z N) N c) D a₁ k₁ a₂ k₂ b₀ l rest₁ rest₂ (restCap (extsLast (Tok := Tok) (FL o
    mk Z (seatK Z N) N c) D (p14At Z).codes G arr (smpLast (p14At Z).codes smp₁ smp₂ get Ns) decT
    c₀' (mineOf ms₁ ms₂ N₁ Ns))) d wEnd)).ft₃) (tiedNumbers N₁ Ns) (tiedMeaning get M₁ (meaningSigS
    (p14At Z).codes G arr smp₂ ms₂ decT₂ MS)) (promSigS (p14At Z).codes G smp₂ ms₂ stOf bookOf Pm₀)
    (besideS (fillAt (p14At Z) (c2 N).rounds (fun q => firstOfS (get q).2) (endedX X)) (yTree (p14At
    Z).codes (p14At Z).S)) (fun q y => ocEnd get N₁ M₁ links (First.flatPlaces true links true) q y
    ∧ Rc q)) (meansQ₃ (tiedNumbers N₁ Ns) (tiedMeaning get M₁ (meaningSigS (p14At Z).codes G arr
    smp₂ ms₂ decT₂ MS)) (⟨rowsOpen (p14At Z).codes arr D.t₁ D.t₂⟩ : MeaningL (FL o mk Z (seatK Z N)
    N c).S₃ (Wit Cells Tok MsgT))) insQ₃ outsQ₃ (· ∈ startLast) 0 ((atDesc (FL o mk Z (seatK Z N) N
    c) (piecesAt (ckP .two) (FL o mk Z (seatK Z N) N c) D a₁ k₁ a₂ k₂ b₀ l rest₁ rest₂ (restCap
    (extsLast (Tok := Tok) (FL o mk Z (seatK Z N) N c) D (p14At Z).codes G arr (smpLast (p14At
    Z).codes smp₁ smp₂ get Ns) decT c₀' (mineOf ms₁ ms₂ N₁ Ns))) d wEnd)).p₃ :: (atDesc (FL o mk Z
    (seatK Z N) N c) (piecesAt (ckP .two) (FL o mk Z (seatK Z N) N c) D a₁ k₁ a₂ k₂ b₀ l rest₁ rest₂
    (restCap (extsLast (Tok := Tok) (FL o mk Z (seatK Z N) N c) D (p14At Z).codes G arr (smpLast
    (p14At Z).codes smp₁ smp₂ get Ns) decT c₀' (mineOf ms₁ ms₂ N₁ Ns))) d wEnd)).l₃) := by
  have T := own3_at_rowB o mk Z N c D G arr dB dt get smp₁ smp₂ ms₁ ms₂ decT₁ decT₂ M₁ MS stOf
      bookOf Pm₀ N₁ Ns links X r Ld decT c₀' a₁ k₁ a₂ k₂ rest₁ rest₂ d wEnd Rc
  rw [hSig] at T
  exact T hRc hP hX hR row0B b₀ l hflat

end LLT25

#print axioms LLT25.e3_at_rowB
#print axioms LLT25.own3_at_rowB
#print axioms LLT25.e3_at_rowB_letter
#print axioms LLT25.own3_at_rowB_letter
