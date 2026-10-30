-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/LLT25R/LastUnpulled.lean: THE PULL IS NOT SEEN. The last chain's ledger stands at `FL
o mk Z (seatK Z N) N c`, which is the proof file's description PULLED BACK along the reading of the
verifier's instance (`FileDescription.pull instanceAsPlainRecord`). The tables' files' tower states its field at a
description that is not pulled back. Here: the law at `FU o mk Z N c` := `ProofFile.fileDescBy o mk Z
(seatK Z N) (P2Third.secondSeatOf Z N) (fun s => s) (ProofFile.startS Z) c`.
  `FL_pull`: the ledger's description is `(FU …).pull instanceAsPlainRecord`, by rfl.
  `own3_at_top_unpulled`, `e3_at_top_unpulled`: **`own3_at_top`'s | `e3_at_top`'s statements
    (LastTop.lean) with `FU o mk Z N c` in the place of `FL o mk Z (seatK Z N) N c` at all 37
    places; each proof is the plain call of the pulled law at the same
    letters**: Lean takes every premise and the conclusion for the other's by unfolding: the types,
    the three chains, the starts, the data and the pieces do not read the instance's type.
Limits: those of LastTop.lean. That the tower's own name of the description unfolds to `FU …`
at its letters is not shown here. NO MEMBER. Nothing on soundness.
-/
import Johnson.LLT25R.LastTop

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

/-- The description, not pulled back along the reading of the verifier's instance. -/
abbrev FU (o : SecondHashFunctionArgument) (mk : LinksBy) (Z : ProofFile.Pub) (N : H2U.Places4) (c : Chain First.S Cl) :=
  ProofFile.fileDescBy o mk Z (seatK Z N) (P2Third.secondSeatOf Z N) (fun s => s) (ProofFile.startS Z) c

/-- The ledger's description is that one, pulled back. -/
theorem FL_pull (o : SecondHashFunctionArgument) (mk : LinksBy) (Z : ProofFile.Pub) (N : H2U.Places4) (c : Chain First.S
          Cl) :
    FL o mk Z (seatK Z N) N c = (FU o mk Z N c).pull LPFD.Full.instanceAsPlainRecord := rfl

variable (seats : List (ℕ × ℕ)) (oNo : Mem → ℕ)

variable (o : SecondHashFunctionArgument) (mk : LinksBy) (Z : ProofFile.Pub) (N : H2U.Places4) (c : Chain S Cl) {Cells Tok
          P₀ : Type} (D : WholeD) {Xi' : Type} (G : FileDescription Xi') (arr : ℕ → ℕ → ℕ) (dB : RDT) (dt : List
                 RDT) (get : (FU o mk Z N c).XiPub × (FU o mk Z N c).S₁ → P₀ × First.S) (ms₁ ms₂ : List Mem)
    (decT₁ : (ℕ → Option (ℕ × List UInt64)) → P₀ × First.S → Option Cells) (decT₂ : (ℕ → Option (ℕ ×
    List UInt64)) → St → Option Cells) (M₁ : Meaning P₀ (Wit Cells Tok MsgT)) (MS : MeaningS St ((FU
    o mk Z N c).XiPub × (FU o mk Z N c).S₁) (Wit Cells Tok MsgT)) (stOf : St → OnBytes.Statement)
    (bookOf : St → OnBytes.TreeBook) (Pm₀ : PromMeaning St) (N₁ : Numbers) (Ns : NumbersS) (links :
    List ModelPart) (X : St → Bool) (r : Fmt.M1.Stage → ℕ) (Ld : VerifiableInference.Desc.K12.Door.Laid)

variable (decT : (ℕ → Option (ℕ × List UInt64)) → (((FU o mk Z N c).XiPub × (FU o mk Z N c).S₁ × St)
    × (FU o mk Z N c).S₃) → Option Cells) (c₀' : Cells) (a₁ : Block (FU o mk Z N c).S₁ (FU o mk Z N
    c).Cl) (k₁ : List (Block (FU o mk Z N c).S₁ (FU o mk Z N c).Cl)) (a₂ : Block St (FU o mk Z N
    c).Cl) (k₂ : List (Block St (FU o mk Z N c).Cl)) (rest₁ : (i : ℕ) → (ds : List RDT) → Rest (ckP
    .two) (frameAt D (allOf D) D.key₁ 0) ((FU o mk Z N c).XiPub × (FU o mk Z N c).S₁) (Wit Cells Tok
    MsgT) ds) (rest₂ : (i : ℕ) → (ds : List RDT) → Rest (ckP .two) (frameAt D (allOf D) D.key₂ 0)
    (((FU o mk Z N c).XiPub × (FU o mk Z N c).S₁) × St) (Wit Cells Tok MsgT) ds) (d wEnd : Wit Cells
    Tok MsgT)

variable (Rc : (FU o mk Z N c).XiPub × (FU o mk Z N c).S₁ → Prop)

/-- **The last chain's field at the description that is not pulled back.** -/
theorem own3_at_top_unpulled (hSig : meaningSig (p14At Z).codes G arr (smpNamed (p14At Z).codes
    seats) ms₁ decT₁ M₁ = M₁) (hRc : ∀ q y, ocEnd get N₁ M₁ links (First.flatPlaces true links true)
    q y → Rc q → (get q).2.failed = none → ToldDesc.rcLastB 0 (vAt Z N₁) Ld (p14At Z).codes (get
    q).2 = true) (hP : PlanOk₃ o mk Z N c D G arr dB dt ms₁ ms₂ N₁ Ns links (First.flatPlaces true
    links true) r (N₁.treesAt none) 0 1 (vAt Z N₁) Ld) (hX : XSamples (p14At Z).codes (p14At Z).S X)
    (hS : ∀ q y, ocEnd get N₁ M₁ links (First.flatPlaces true links true) q y → Rc q → (get
    q).2.failed = none → ∀ f, firstOfS (get q).2 = some f → SeatsNumber seats f.book) (hN : ∀ x ∈
    (mineOf ms₁ ms₂ N₁ Ns), seatOf x = (D.t₁ + 1, 0) → ∀ d, X d = true → oNo x = d.loc.oOmega)
    (row0B : RowZeroOwed (tiedNumbers N₁ Ns) (tiedMeaning get M₁ (meaningSigS (p14At Z).codes G arr
    (smpSt (p14At Z).codes oNo stSh) ms₂ decT₂ MS)) (⟨rowsOpen (p14At Z).codes arr D.t₁ D.t₂⟩ :
    MeaningL (FU o mk Z N c).S₃ (Wit Cells Tok MsgT)) (promSigS (p14At Z).codes G (smpSt (p14At
    Z).codes oNo stSh) ms₂ stOf bookOf Pm₀) (fillAt (p14At Z) (c2 N).rounds (fun q => firstOfS (get
    q).2) (endedX X)) (fun q y => ocEnd get N₁ M₁ links (First.flatPlaces true links true) q y ∧ Rc
    q) (pieceZeroAt (FU o mk Z N c) D (c0 Z) (restCap (extsLast (Tok := Tok) (FU o mk Z N c) D
    (p14At Z).codes G arr (smpLast (p14At Z).codes (smpNamed (p14At Z).codes seats) (smpSt (p14At
    Z).codes oNo stSh) get Ns) decT c₀' (mineOf ms₁ ms₂ N₁ Ns))))) (b₀ : Block (FU o mk Z N c).S₃
    (FU o mk Z N c).Cl) (l : List (Block (FU o mk Z N c).S₃ (FU o mk Z N c).Cl)) (hflat : (FU o mk Z
    N c).second.blocksInOrder = b₀ :: l) : EachOwn (onQ₃ (Fr := frameAt D (allOf D) D.key₃ (atDesc (FU o mk Z
             N c) (piecesAt (ckP .two) (FU o mk Z N c) D a₁ k₁ a₂ k₂ b₀ l rest₁ rest₂ (restCap (extsLast (Tok
             := Tok) (FU o mk Z N c) D (p14At Z).codes G arr (smpLast (p14At Z).codes (smpNamed (p14At
             Z).codes seats) (smpSt (p14At Z).codes oNo stSh) get Ns) decT c₀' (mineOf ms₁ ms₂ N₁ Ns))) d
             wEnd)).ft₃) (tiedNumbers N₁ Ns) (tiedMeaning get M₁ (meaningSigS (p14At Z).codes G arr (smpSt
             (p14At Z).codes oNo stSh) ms₂ decT₂ MS)) (promSigS (p14At Z).codes G (smpSt (p14At Z).codes oNo
             stSh) ms₂ stOf bookOf Pm₀) (besideS (fillAt (p14At Z) (c2 N).rounds (fun q => firstOfS (get
             q).2) (endedX X)) (yTree (p14At Z).codes (p14At Z).S)) (fun q y => ocEnd get N₁ M₁ links
             (First.flatPlaces true links true) q y ∧ Rc q)) (meansQ₃ (tiedNumbers N₁ Ns) (tiedMeaning get M₁
             (meaningSigS (p14At Z).codes G arr (smpSt (p14At Z).codes oNo stSh) ms₂ decT₂ MS)) (⟨rowsOpen
             (p14At Z).codes arr D.t₁ D.t₂⟩ : MeaningL (FU o mk Z N c).S₃ (Wit Cells Tok MsgT))) insQ₃ outsQ₃
    (· ∈ startLast) 0 ((atDesc (FU o mk Z N c) (piecesAt (ckP .two) (FU o mk Z N c) D a₁ k₁ a₂ k₂ b₀
    l rest₁ rest₂ (restCap (extsLast (Tok := Tok) (FU o mk Z N c) D (p14At Z).codes G arr (smpLast
    (p14At Z).codes (smpNamed (p14At Z).codes seats) (smpSt (p14At Z).codes oNo stSh) get Ns) decT
    c₀' (mineOf ms₁ ms₂ N₁ Ns))) d wEnd)).p₃ :: (atDesc (FU o mk Z N c) (piecesAt (ckP .two) (FU o
    mk Z N c) D a₁ k₁ a₂ k₂ b₀ l rest₁ rest₂ (restCap (extsLast (Tok := Tok) (FU o mk Z N c) D
    (p14At Z).codes G arr (smpLast (p14At Z).codes (smpNamed (p14At Z).codes seats) (smpSt (p14At
    Z).codes oNo stSh) get Ns) decT c₀' (mineOf ms₁ ms₂ N₁ Ns))) d wEnd)).l₃) :=
  own3_at_top seats oNo o mk Z N c D G arr dB dt get ms₁ ms₂ decT₁ decT₂ M₁ MS stOf bookOf Pm₀ N₁ Ns
      links X r Ld decT c₀' a₁ k₁ a₂ k₂ rest₁ rest₂ d wEnd Rc hSig hRc hP hX hS hN row0B b₀ l hflat

/-- **The same in the form "each leads".** -/
theorem e3_at_top_unpulled (hSig : meaningSig (p14At Z).codes G arr (smpNamed (p14At Z).codes seats)
    ms₁ decT₁ M₁ = M₁) (hRc : ∀ q y, ocEnd get N₁ M₁ links (First.flatPlaces true links true) q y →
    Rc q → (get q).2.failed = none → ToldDesc.rcLastB 0 (vAt Z N₁) Ld (p14At Z).codes (get q).2 =
    true) (hP : PlanOk₃ o mk Z N c D G arr dB dt ms₁ ms₂ N₁ Ns links (First.flatPlaces true links
    true) r (N₁.treesAt none) 0 1 (vAt Z N₁) Ld) (hX : XSamples (p14At Z).codes (p14At Z).S X) (hS :
    ∀ q y, ocEnd get N₁ M₁ links (First.flatPlaces true links true) q y → Rc q → (get q).2.failed =
    none → ∀ f, firstOfS (get q).2 = some f → SeatsNumber seats f.book) (hN : ∀ x ∈ (mineOf ms₁ ms₂
    N₁ Ns), seatOf x = (D.t₁ + 1, 0) → ∀ d, X d = true → oNo x = d.loc.oOmega) (row0B : RowZeroOwed
    (tiedNumbers N₁ Ns) (tiedMeaning get M₁ (meaningSigS (p14At Z).codes G arr (smpSt (p14At
    Z).codes oNo stSh) ms₂ decT₂ MS)) (⟨rowsOpen (p14At Z).codes arr D.t₁ D.t₂⟩ : MeaningL (FU o mk
    Z N c).S₃ (Wit Cells Tok MsgT)) (promSigS (p14At Z).codes G (smpSt (p14At Z).codes oNo stSh) ms₂
    stOf bookOf Pm₀) (fillAt (p14At Z) (c2 N).rounds (fun q => firstOfS (get q).2) (endedX X)) (fun
    q y => ocEnd get N₁ M₁ links (First.flatPlaces true links true) q y ∧ Rc q) (pieceZeroAt (FU o
    mk Z N c) D (c0 Z) (restCap (extsLast (Tok := Tok) (FU o mk Z N c) D (p14At Z).codes G arr
    (smpLast (p14At Z).codes (smpNamed (p14At Z).codes seats) (smpSt (p14At Z).codes oNo stSh) get
    Ns) decT c₀' (mineOf ms₁ ms₂ N₁ Ns))))) (b₀ : Block (FU o mk Z N c).S₃ (FU o mk Z N c).Cl) (l :
    List (Block (FU o mk Z N c).S₃ (FU o mk Z N c).Cl)) (hflat : (FU o mk Z N c).second.blocksInOrder = b₀ ::
    l) : EachLeads (onQ₃ (Fr := frameAt D (allOf D) D.key₃ (atDesc (FU o mk Z N c) (piecesAt (ckP
    .two) (FU o mk Z N c) D a₁ k₁ a₂ k₂ b₀ l rest₁ rest₂ (restCap (extsLast (Tok := Tok) (FU o mk Z
    N c) D (p14At Z).codes G arr (smpLast (p14At Z).codes (smpNamed (p14At Z).codes seats) (smpSt
    (p14At Z).codes oNo stSh) get Ns) decT c₀' (mineOf ms₁ ms₂ N₁ Ns))) d wEnd)).ft₃) (tiedNumbers
    N₁ Ns) (tiedMeaning get M₁ (meaningSigS (p14At Z).codes G arr (smpSt (p14At Z).codes oNo stSh)
    ms₂ decT₂ MS)) (promSigS (p14At Z).codes G (smpSt (p14At Z).codes oNo stSh) ms₂ stOf bookOf Pm₀)
    (besideS (fillAt (p14At Z) (c2 N).rounds (fun q => firstOfS (get q).2) (endedX X)) (yTree (p14At
    Z).codes (p14At Z).S)) (fun q y => ocEnd get N₁ M₁ links (First.flatPlaces true links true) q y
    ∧ Rc q)) (stepQ₃ (atDesc (FU o mk Z N c) (piecesAt (ckP .two) (FU o mk Z N c) D a₁ k₁ a₂ k₂ b₀ l
    rest₁ rest₂ (restCap (extsLast (Tok := Tok) (FU o mk Z N c) D (p14At Z).codes G arr (smpLast
    (p14At Z).codes (smpNamed (p14At Z).codes seats) (smpSt (p14At Z).codes oNo stSh) get Ns) decT
    c₀' (mineOf ms₁ ms₂ N₁ Ns))) d wEnd)) (tiedNumbers N₁ Ns) (tiedMeaning get M₁ (meaningSigS
    (p14At Z).codes G arr (smpSt (p14At Z).codes oNo stSh) ms₂ decT₂ MS)) (⟨rowsOpen (p14At Z).codes
    arr D.t₁ D.t₂⟩ : MeaningL (FU o mk Z N c).S₃ (Wit Cells Tok MsgT)) (promSigS (p14At Z).codes G
    (smpSt (p14At Z).codes oNo stSh) ms₂ stOf bookOf Pm₀) (besideS (fillAt (p14At Z) (c2 N).rounds
    (fun q => firstOfS (get q).2) (endedX X)) (yTree (p14At Z).codes (p14At Z).S)) (fun q y => ocEnd
    get N₁ M₁ links (First.flatPlaces true links true) q y ∧ Rc q)) 0 ((atDesc (FU o mk Z N c)
    (piecesAt (ckP .two) (FU o mk Z N c) D a₁ k₁ a₂ k₂ b₀ l rest₁ rest₂ (restCap (extsLast (Tok :=
    Tok) (FU o mk Z N c) D (p14At Z).codes G arr (smpLast (p14At Z).codes (smpNamed (p14At Z).codes
    seats) (smpSt (p14At Z).codes oNo stSh) get Ns) decT c₀' (mineOf ms₁ ms₂ N₁ Ns))) d wEnd)).p₃ ::
    (atDesc (FU o mk Z N c) (piecesAt (ckP .two) (FU o mk Z N c) D a₁ k₁ a₂ k₂ b₀ l rest₁ rest₂
    (restCap (extsLast (Tok := Tok) (FU o mk Z N c) D (p14At Z).codes G arr (smpLast (p14At Z).codes
    (smpNamed (p14At Z).codes seats) (smpSt (p14At Z).codes oNo stSh) get Ns) decT c₀' (mineOf ms₁
    ms₂ N₁ Ns))) d wEnd)).l₃) :=
  e3_at_top seats oNo o mk Z N c D G arr dB dt get ms₁ ms₂ decT₁ decT₂ M₁ MS stOf bookOf Pm₀ N₁ Ns
      links X r Ld decT c₀' a₁ k₁ a₂ k₂ rest₁ rest₂ d wEnd Rc hSig hRc hP hX hS hN row0B b₀ l hflat

end LLT25

#print axioms LLT25.own3_at_top_unpulled
#print axioms LLT25.e3_at_top_unpulled
