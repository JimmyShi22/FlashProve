-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/LLT25R/LastTop.lean: THE LAST CHAIN's FIELD (`leads3_last_chains_table`; e₃) IN THE
FORM THAT IS MEANT FOR THE JOIN: the two turns of Johnson/LLT25R/LastNamed.lean (the two
tables' own readers of OOD samples) and LastRowB.lean (row 0's debt as one premise) together. Two
theorems; each proof is one call.
  `own3_at_top`: **`EachOwn (onQ₃ … PLm Oc) (meansQ₃ …) insQ₃ outsQ₃ (· ∈ startLast) 0 (p₃ ::
    l₃)`**, the tables' files' field's own shape, AT Oc := `ocEnd … ∧ Rc` (Rc a letter) · PLm :=
    `besideS (fillAt (p14At Z) (c2 N).rounds (fun q => firstOfS (get q).2) (endedX X)) (yTree cs S)`
    · smp₁ := `smpNamed cs seats` · smp₂ := `smpSt cs oNo stSh`, FROM EIGHT PREMISES:
    hSig (the first table's meaning M₁ is its own `meaningSig …`) · hRc and hS (TWO FACTS ON THE
      FIRST CHAIN's LAST STATE, each under its whole last promise, Rc and "no mark": the five tests
      `rcLastB`; the handed book numbers the messages as the list seats does) · hP (`PlanOk₃`:
      thirty-three tests on the plan) · hX and hN (TWO CONDITIONS ON THE LETTER X: what its yes says
      of Omega's message; of Omega's number) · row0B (THE LAW OF ROW 0's PIECE, in its files' own
      conclusion's form) · hflat (the last chain's flat list is b₀ :: l).
  `e3_at_top`: the same in the form "each leads".
Beside row0B, WHICH IS A LAW OF ONE PIECE BETWEEN THE PROMISES AT BORDERS 0 AND 1 (of the kinds'
laws' kind: it does speak of every statement inside the promise at border 0, as every such law
does), no premise quantifies over the statements inside a promise of the last table; none speaks of
the last chain's own state.
Limits: those of the two files. NO MEMBER: that the promise, at this Oc and these two layers, is met
by the states of an honest run is shown by nobody. Nothing on soundness.
-/
import Johnson.LLT25R.LastNamedCore
import Johnson.LLT25R.LastRowB

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

variable (seats : List (ℕ × ℕ)) (oNo : Mem → ℕ)

variable (o : SecondHashFunctionArgument) (mk : LinksBy) (Z : ProofFile.Pub) (N : H2U.Places4) (c : Chain S Cl) {Cells Tok
          P₀ : Type} (D : WholeD) {Xi' : Type} (G : FileDescription Xi') (arr : ℕ → ℕ → ℕ) (dB : RDT) (dt : List
                 RDT) (get : (FL o mk Z (seatK Z N) N c).XiPub × (FL o mk Z (seatK Z N) N c).S₁ → P₀ × First.S)
    (ms₁ ms₂ : List Mem) (decT₁ : (ℕ → Option (ℕ × List UInt64)) → P₀ × First.S → Option Cells)
    (decT₂ : (ℕ → Option (ℕ × List UInt64)) → St → Option Cells) (M₁ : Meaning P₀ (Wit Cells Tok
    MsgT)) (MS : MeaningS St ((FL o mk Z (seatK Z N) N c).XiPub × (FL o mk Z (seatK Z N) N c).S₁)
    (Wit Cells Tok MsgT)) (stOf : St → OnBytes.Statement) (bookOf : St → OnBytes.TreeBook) (Pm₀ :
    PromMeaning St) (N₁ : Numbers) (Ns : NumbersS) (links : List ModelPart) (X : St → Bool) (r :
          Fmt.M1.Stage → ℕ) (Ld : VerifiableInference.Desc.K12.Door.Laid)

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

/-- **The last chain's field, in the form that is meant for the join.** -/
theorem own3_at_top (hSig : meaningSig (p14At Z).codes G arr (smpNamed (p14At Z).codes seats) ms₁
    decT₁ M₁ = M₁) (hRc : ∀ q y, ocEnd get N₁ M₁ links (First.flatPlaces true links true) q y → Rc q
    → (get q).2.failed = none → ToldDesc.rcLastB 0 (vAt Z N₁) Ld (p14At Z).codes (get q).2 = true)
    (hP : PlanOk₃ o mk Z N c D G arr dB dt ms₁ ms₂ N₁ Ns links (First.flatPlaces true links true) r
    (N₁.treesAt none) 0 1 (vAt Z N₁) Ld) (hX : XSamples (p14At Z).codes (p14At Z).S X) (hS : ∀ q y,
    ocEnd get N₁ M₁ links (First.flatPlaces true links true) q y → Rc q → (get q).2.failed = none →
    ∀ f, firstOfS (get q).2 = some f → SeatsNumber seats f.book) (hN : ∀ x ∈ (mineOf ms₁ ms₂ N₁ Ns),
    seatOf x = (D.t₁ + 1, 0) → ∀ d, X d = true → oNo x = d.loc.oOmega) (row0B : RowZeroOwed
    (tiedNumbers N₁ Ns) (tiedMeaning get M₁ (meaningSigS (p14At Z).codes G arr (smpSt (p14At
    Z).codes oNo stSh) ms₂ decT₂ MS)) (⟨rowsOpen (p14At Z).codes arr D.t₁ D.t₂⟩ : MeaningL (FL o mk
    Z (seatK Z N) N c).S₃ (Wit Cells Tok MsgT)) (promSigS (p14At Z).codes G (smpSt (p14At Z).codes
    oNo stSh) ms₂ stOf bookOf Pm₀) (fillAt (p14At Z) (c2 N).rounds (fun q => firstOfS (get q).2)
    (endedX X)) (fun q y => ocEnd get N₁ M₁ links (First.flatPlaces true links true) q y ∧ Rc q)
    (pieceZeroAt (FL o mk Z (seatK Z N) N c) D (c0 Z) (restCap (extsLast (Tok := Tok) (FL o mk Z
    (seatK Z N) N c) D (p14At Z).codes G arr (smpLast (p14At Z).codes (smpNamed (p14At Z).codes
    seats) (smpSt (p14At Z).codes oNo stSh) get Ns) decT c₀' (mineOf ms₁ ms₂ N₁ Ns))))) (b₀ : Block
    (FL o mk Z (seatK Z N) N c).S₃ (FL o mk Z (seatK Z N) N c).Cl) (l : List (Block (FL o mk Z
    (seatK Z N) N c).S₃ (FL o mk Z (seatK Z N) N c).Cl)) (hflat : (FL o mk Z (seatK Z N) N
    c).second.blocksInOrder = b₀ :: l) : EachOwn (onQ₃ (Fr := frameAt D (allOf D) D.key₃ (atDesc (FL o mk Z
             (seatK Z N) N c) (piecesAt (ckP .two) (FL o mk Z (seatK Z N) N c) D a₁ k₁ a₂ k₂ b₀ l rest₁ rest₂
             (restCap (extsLast (Tok := Tok) (FL o mk Z (seatK Z N) N c) D (p14At Z).codes G arr (smpLast
             (p14At Z).codes (smpNamed (p14At Z).codes seats) (smpSt (p14At Z).codes oNo stSh) get Ns) decT
             c₀' (mineOf ms₁ ms₂ N₁ Ns))) d wEnd)).ft₃) (tiedNumbers N₁ Ns) (tiedMeaning get M₁ (meaningSigS
             (p14At Z).codes G arr (smpSt (p14At Z).codes oNo stSh) ms₂ decT₂ MS)) (promSigS (p14At Z).codes
             G (smpSt (p14At Z).codes oNo stSh) ms₂ stOf bookOf Pm₀) (besideS (fillAt (p14At Z) (c2 N).rounds
             (fun q => firstOfS (get q).2) (endedX X)) (yTree (p14At Z).codes (p14At Z).S)) (fun q y => ocEnd
             get N₁ M₁ links (First.flatPlaces true links true) q y ∧ Rc q)) (meansQ₃ (tiedNumbers N₁ Ns)
             (tiedMeaning get M₁ (meaningSigS (p14At Z).codes G arr (smpSt (p14At Z).codes oNo stSh) ms₂
             decT₂ MS)) (⟨rowsOpen (p14At Z).codes arr D.t₁ D.t₂⟩ : MeaningL (FL o mk Z (seatK Z N) N c).S₃
             (Wit Cells Tok MsgT))) insQ₃ outsQ₃ (· ∈ startLast) 0 ((atDesc (FL o mk Z (seatK Z N) N c)
             (piecesAt (ckP .two) (FL o mk Z (seatK Z N) N c) D a₁ k₁ a₂ k₂ b₀ l rest₁ rest₂ (restCap
             (extsLast (Tok := Tok) (FL o mk Z (seatK Z N) N c) D (p14At Z).codes G arr (smpLast (p14At
             Z).codes (smpNamed (p14At Z).codes seats) (smpSt (p14At Z).codes oNo stSh) get Ns) decT c₀'
             (mineOf ms₁ ms₂ N₁ Ns))) d wEnd)).p₃ :: (atDesc (FL o mk Z (seatK Z N) N c) (piecesAt (ckP .two)
             (FL o mk Z (seatK Z N) N c) D a₁ k₁ a₂ k₂ b₀ l rest₁ rest₂ (restCap (extsLast (Tok := Tok) (FL o
             mk Z (seatK Z N) N c) D (p14At Z).codes G arr (smpLast (p14At Z).codes (smpNamed (p14At Z).codes
             seats) (smpSt (p14At Z).codes oNo stSh) get Ns) decT c₀' (mineOf ms₁ ms₂ N₁ Ns))) d wEnd)).l₃)
    :=
  own3_at_rowB_letter o mk Z N c D G arr dB dt get (smpNamed (p14At Z).codes seats) (smpSt (p14At
      Z).codes oNo stSh) ms₁ ms₂ decT₁ decT₂ M₁ MS stOf bookOf Pm₀ N₁ Ns links X r Ld decT c₀' a₁ k₁
      a₂ k₂ rest₁ rest₂ d wEnd Rc hSig hRc hP hX (Readers₃.ofNamed seats oNo o mk Z N c D G arr dB
      dt get ms₁ ms₂ decT₁ decT₂ M₁ MS stOf bookOf Pm₀ N₁ Ns links X r Ld Rc hP hS hN) row0B b₀ l
      hflat

/-- **The same in the form "each leads".** -/
theorem e3_at_top (hSig : meaningSig (p14At Z).codes G arr (smpNamed (p14At Z).codes seats) ms₁
    decT₁ M₁ = M₁) (hRc : ∀ q y, ocEnd get N₁ M₁ links (First.flatPlaces true links true) q y → Rc q
    → (get q).2.failed = none → ToldDesc.rcLastB 0 (vAt Z N₁) Ld (p14At Z).codes (get q).2 = true)
    (hP : PlanOk₃ o mk Z N c D G arr dB dt ms₁ ms₂ N₁ Ns links (First.flatPlaces true links true) r
    (N₁.treesAt none) 0 1 (vAt Z N₁) Ld) (hX : XSamples (p14At Z).codes (p14At Z).S X) (hS : ∀ q y,
    ocEnd get N₁ M₁ links (First.flatPlaces true links true) q y → Rc q → (get q).2.failed = none →
    ∀ f, firstOfS (get q).2 = some f → SeatsNumber seats f.book) (hN : ∀ x ∈ (mineOf ms₁ ms₂ N₁ Ns),
    seatOf x = (D.t₁ + 1, 0) → ∀ d, X d = true → oNo x = d.loc.oOmega) (row0B : RowZeroOwed
    (tiedNumbers N₁ Ns) (tiedMeaning get M₁ (meaningSigS (p14At Z).codes G arr (smpSt (p14At
    Z).codes oNo stSh) ms₂ decT₂ MS)) (⟨rowsOpen (p14At Z).codes arr D.t₁ D.t₂⟩ : MeaningL (FL o mk
    Z (seatK Z N) N c).S₃ (Wit Cells Tok MsgT)) (promSigS (p14At Z).codes G (smpSt (p14At Z).codes
    oNo stSh) ms₂ stOf bookOf Pm₀) (fillAt (p14At Z) (c2 N).rounds (fun q => firstOfS (get q).2)
    (endedX X)) (fun q y => ocEnd get N₁ M₁ links (First.flatPlaces true links true) q y ∧ Rc q)
    (pieceZeroAt (FL o mk Z (seatK Z N) N c) D (c0 Z) (restCap (extsLast (Tok := Tok) (FL o mk Z
    (seatK Z N) N c) D (p14At Z).codes G arr (smpLast (p14At Z).codes (smpNamed (p14At Z).codes
    seats) (smpSt (p14At Z).codes oNo stSh) get Ns) decT c₀' (mineOf ms₁ ms₂ N₁ Ns))))) (b₀ : Block
    (FL o mk Z (seatK Z N) N c).S₃ (FL o mk Z (seatK Z N) N c).Cl) (l : List (Block (FL o mk Z
    (seatK Z N) N c).S₃ (FL o mk Z (seatK Z N) N c).Cl)) (hflat : (FL o mk Z (seatK Z N) N
    c).second.blocksInOrder = b₀ :: l) : EachLeads (onQ₃ (Fr := frameAt D (allOf D) D.key₃ (atDesc (FL o mk Z
             (seatK Z N) N c) (piecesAt (ckP .two) (FL o mk Z (seatK Z N) N c) D a₁ k₁ a₂ k₂ b₀ l rest₁ rest₂
             (restCap (extsLast (Tok := Tok) (FL o mk Z (seatK Z N) N c) D (p14At Z).codes G arr (smpLast
             (p14At Z).codes (smpNamed (p14At Z).codes seats) (smpSt (p14At Z).codes oNo stSh) get Ns) decT
             c₀' (mineOf ms₁ ms₂ N₁ Ns))) d wEnd)).ft₃) (tiedNumbers N₁ Ns) (tiedMeaning get M₁ (meaningSigS
             (p14At Z).codes G arr (smpSt (p14At Z).codes oNo stSh) ms₂ decT₂ MS)) (promSigS (p14At Z).codes
             G (smpSt (p14At Z).codes oNo stSh) ms₂ stOf bookOf Pm₀) (besideS (fillAt (p14At Z) (c2 N).rounds
             (fun q => firstOfS (get q).2) (endedX X)) (yTree (p14At Z).codes (p14At Z).S)) (fun q y => ocEnd
             get N₁ M₁ links (First.flatPlaces true links true) q y ∧ Rc q)) (stepQ₃ (atDesc (FL o mk Z
             (seatK Z N) N c) (piecesAt (ckP .two) (FL o mk Z (seatK Z N) N c) D a₁ k₁ a₂ k₂ b₀ l rest₁ rest₂
             (restCap (extsLast (Tok := Tok) (FL o mk Z (seatK Z N) N c) D (p14At Z).codes G arr (smpLast
             (p14At Z).codes (smpNamed (p14At Z).codes seats) (smpSt (p14At Z).codes oNo stSh) get Ns) decT
             c₀' (mineOf ms₁ ms₂ N₁ Ns))) d wEnd)) (tiedNumbers N₁ Ns) (tiedMeaning get M₁ (meaningSigS
             (p14At Z).codes G arr (smpSt (p14At Z).codes oNo stSh) ms₂ decT₂ MS)) (⟨rowsOpen (p14At Z).codes
             arr D.t₁ D.t₂⟩ : MeaningL (FL o mk Z (seatK Z N) N c).S₃ (Wit Cells Tok MsgT)) (promSigS (p14At
             Z).codes G (smpSt (p14At Z).codes oNo stSh) ms₂ stOf bookOf Pm₀) (besideS (fillAt (p14At Z) (c2
             N).rounds (fun q => firstOfS (get q).2) (endedX X)) (yTree (p14At Z).codes (p14At Z).S)) (fun q
             y => ocEnd get N₁ M₁ links (First.flatPlaces true links true) q y ∧ Rc q)) 0 ((atDesc (FL o mk Z
             (seatK Z N) N c) (piecesAt (ckP .two) (FL o mk Z (seatK Z N) N c) D a₁ k₁ a₂ k₂ b₀ l rest₁ rest₂
             (restCap (extsLast (Tok := Tok) (FL o mk Z (seatK Z N) N c) D (p14At Z).codes G arr (smpLast
             (p14At Z).codes (smpNamed (p14At Z).codes seats) (smpSt (p14At Z).codes oNo stSh) get Ns) decT
             c₀' (mineOf ms₁ ms₂ N₁ Ns))) d wEnd)).p₃ :: (atDesc (FL o mk Z (seatK Z N) N c) (piecesAt (ckP
             .two) (FL o mk Z (seatK Z N) N c) D a₁ k₁ a₂ k₂ b₀ l rest₁ rest₂ (restCap (extsLast (Tok := Tok)
             (FL o mk Z (seatK Z N) N c) D (p14At Z).codes G arr (smpLast (p14At Z).codes (smpNamed (p14At
             Z).codes seats) (smpSt (p14At Z).codes oNo stSh) get Ns) decT c₀' (mineOf ms₁ ms₂ N₁ Ns))) d
             wEnd)).l₃) :=
  e3_at_rowB_letter o mk Z N c D G arr dB dt get (smpNamed (p14At Z).codes seats) (smpSt (p14At
      Z).codes oNo stSh) ms₁ ms₂ decT₁ decT₂ M₁ MS stOf bookOf Pm₀ N₁ Ns links X r Ld decT c₀' a₁ k₁
      a₂ k₂ rest₁ rest₂ d wEnd Rc hSig hRc hP hX (Readers₃.ofNamed seats oNo o mk Z N c D G arr dB
      dt get ms₁ ms₂ decT₁ decT₂ M₁ MS stOf bookOf Pm₀ N₁ Ns links X r Ld Rc hP hS hN) row0B b₀ l
      hflat

end LLT25

#print axioms LLT25.own3_at_top
#print axioms LLT25.e3_at_top
