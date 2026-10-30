-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/LLT25R/LastEnd.lean: TWO SMALL CLOSINGS ON THE LAST CHAIN's FIELD.
  `own3_at_end`, `e3_at_end`: `own3_at_top_unpulled`'s | `e3_at_top_unpulled`'s statements
    (LastUnpulled.lean) AT b₀ := `c0 Z`, l := [`c1 N`, `c2 N`, `c3 Z N`]:
    THE PREMISE hflat IS PAID: that the description's last chain is these four sub-protocols is
    `last_flat_pure` (LastSeat.lean; `last_blocks_in`). SEVEN PREMISES
    ARE LEFT: hSig · hRc · hS · hP · hX · hN · row0B.
  `closed_in_scope`: **THE TEST closed OF `PlanOk₃` IS A THEOREM IN THE GOALS' SCOPE, AT r :=
    `rWFull`**: ∃ ch b₁ b₂ T, `ClosedL` (the place W's parameters) rWFull ch b₁ b₂ T, by
    `closedL_in_scope_W` (Johnson/Loose/H2K12/ClosedAtSeats.lean; witnesses 2 · 83
    · 2 · `TWFull`) and `planOk_tie` (LastTie.lean). Its premises are that law's: the scope; the
    public files' reading; the places; the description's own test on the plan (here at the ledger's
    name of the description); one of the door's pins (seatPinnedProof). THE FULL SIZE ALONE.
Limits: those of the files
called. NO MEMBER. Nothing on soundness.
-/
import Johnson.LLT25R.LastUnpulled
import Johnson.LLT25R.LastTie
import Johnson.Loose.H2K12.ClosedAtSeats

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

/-- **The test closed of `PlanOk₃`, in the goals' scope.** -/
theorem closed_in_scope {o : SecondHashFunctionArgument} {S : VerifierAndGoals.PublicFiles} (hS : VerifierAndGoals.InScope S = true) (Z :
            ProofFile.Pub)
    (hZ : ProofFile.pubPlain o S.pol S.lay S.KL = .ok Z) (mk : LinksBy) (N : H2U.Places4)
    (c : Chain First.S Cl) (hN : H2U.placesOfMade Z.made = .ok N)
    (hp : (FL o mk Z (seatK Z N) N c).planOk = true)
    (hpin : VerifiableInference.PlanWritten.seatPinnedProof S.pol
      (H2K.JointK.descN o mk guardedProximityTestParts Z N c) = true) :
    ∃ ch b₁ b₂ T, ClosedL (H2U.proximityTestParametersAt ⟨3, none, 2, .K12⟩ N.W) H2K.Member.rWFull ch b₁ b₂ T :=
  ⟨2, 83, 2, _, (H2K.JointK.closedL_in_scope_W hS Z hZ mk N c hN
    ((planOk_tie o mk Z N c).symm.trans hp) hpin).1⟩

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

/-- **The last chain's field at the description's own four sub-protocols.** -/
theorem own3_at_end (hSig : meaningSig (p14At Z).codes G arr (smpNamed (p14At Z).codes seats) ms₁
    decT₁ M₁ = M₁) (hRc : ∀ q y, ocEnd get N₁ M₁ links (First.flatPlaces true links true) q y → Rc q
    → (get q).2.failed = none → ToldDesc.rcLastB 0 (vAt Z N₁) Ld (p14At Z).codes (get q).2 = true)
    (hP : PlanOk₃ o mk Z N c D G arr dB dt ms₁ ms₂ N₁ Ns links (First.flatPlaces true links true) r
    (N₁.treesAt none) 0 1 (vAt Z N₁) Ld) (hX : XSamples (p14At Z).codes (p14At Z).S X) (hS : ∀ q y,
    ocEnd get N₁ M₁ links (First.flatPlaces true links true) q y → Rc q → (get q).2.failed = none →
    ∀ f, firstOfS (get q).2 = some f → SeatsNumber seats f.book) (hN : ∀ x ∈ (mineOf ms₁ ms₂ N₁ Ns),
    seatOf x = (D.t₁ + 1, 0) → ∀ d, X d = true → oNo x = d.loc.oOmega) (row0B : RowZeroOwed
    (tiedNumbers N₁ Ns) (tiedMeaning get M₁ (meaningSigS (p14At Z).codes G arr (smpSt (p14At
    Z).codes oNo stSh) ms₂ decT₂ MS)) (⟨rowsOpen (p14At Z).codes arr D.t₁ D.t₂⟩ : MeaningL (FU o mk
    Z N c).S₃ (Wit Cells Tok MsgT)) (promSigS (p14At Z).codes G (smpSt (p14At Z).codes oNo stSh) ms₂
    stOf bookOf Pm₀) (fillAt (p14At Z) (c2 N).rounds (fun q => firstOfS (get q).2) (endedX X)) (fun
    q y => ocEnd get N₁ M₁ links (First.flatPlaces true links true) q y ∧ Rc q) (pieceZeroAt (FU o
    mk Z N c) D (c0 Z) (restCap (extsLast (Tok := Tok) (FU o mk Z N c) D (p14At Z).codes G arr
    (smpLast (p14At Z).codes (smpNamed (p14At Z).codes seats) (smpSt (p14At Z).codes oNo stSh) get
    Ns) decT c₀' (mineOf ms₁ ms₂ N₁ Ns))))) : EachOwn (onQ₃ (Fr := frameAt D (allOf D) D.key₃
    (atDesc (FU o mk Z N c) (piecesAt (ckP .two) (FU o mk Z N c) D a₁ k₁ a₂ k₂ (c0 Z) [c1 N, c2 N,
    c3 Z N] rest₁ rest₂ (restCap (extsLast (Tok := Tok) (FU o mk Z N c) D (p14At Z).codes G arr
    (smpLast (p14At Z).codes (smpNamed (p14At Z).codes seats) (smpSt (p14At Z).codes oNo stSh) get
    Ns) decT c₀' (mineOf ms₁ ms₂ N₁ Ns))) d wEnd)).ft₃) (tiedNumbers N₁ Ns) (tiedMeaning get M₁
    (meaningSigS (p14At Z).codes G arr (smpSt (p14At Z).codes oNo stSh) ms₂ decT₂ MS)) (promSigS
    (p14At Z).codes G (smpSt (p14At Z).codes oNo stSh) ms₂ stOf bookOf Pm₀) (besideS (fillAt (p14At
    Z) (c2 N).rounds (fun q => firstOfS (get q).2) (endedX X)) (yTree (p14At Z).codes (p14At Z).S))
    (fun q y => ocEnd get N₁ M₁ links (First.flatPlaces true links true) q y ∧ Rc q)) (meansQ₃
    (tiedNumbers N₁ Ns) (tiedMeaning get M₁ (meaningSigS (p14At Z).codes G arr (smpSt (p14At
    Z).codes oNo stSh) ms₂ decT₂ MS)) (⟨rowsOpen (p14At Z).codes arr D.t₁ D.t₂⟩ : MeaningL (FU o mk
    Z N c).S₃ (Wit Cells Tok MsgT))) insQ₃ outsQ₃ (· ∈ startLast) 0 ((atDesc (FU o mk Z N c)
    (piecesAt (ckP .two) (FU o mk Z N c) D a₁ k₁ a₂ k₂ (c0 Z) [c1 N, c2 N, c3 Z N] rest₁ rest₂
    (restCap (extsLast (Tok := Tok) (FU o mk Z N c) D (p14At Z).codes G arr (smpLast (p14At Z).codes
    (smpNamed (p14At Z).codes seats) (smpSt (p14At Z).codes oNo stSh) get Ns) decT c₀' (mineOf ms₁
    ms₂ N₁ Ns))) d wEnd)).p₃ :: (atDesc (FU o mk Z N c) (piecesAt (ckP .two) (FU o mk Z N c) D a₁ k₁
    a₂ k₂ (c0 Z) [c1 N, c2 N, c3 Z N] rest₁ rest₂ (restCap (extsLast (Tok := Tok) (FU o mk Z N c) D
    (p14At Z).codes G arr (smpLast (p14At Z).codes (smpNamed (p14At Z).codes seats) (smpSt (p14At
    Z).codes oNo stSh) get Ns) decT c₀' (mineOf ms₁ ms₂ N₁ Ns))) d wEnd)).l₃) :=
  own3_at_top_unpulled seats oNo o mk Z N c D G arr dB dt get ms₁ ms₂ decT₁ decT₂ M₁ MS stOf bookOf
      Pm₀ N₁ Ns links X r Ld decT c₀' a₁ k₁ a₂ k₂ rest₁ rest₂ d wEnd Rc hSig hRc hP hX hS hN row0B
      (c0 Z) [c1 N, c2 N, c3 Z N] (last_flat_pure o mk Z (seatK Z N) N c)

/-- **The same in the form "each leads".** -/
theorem e3_at_end (hSig : meaningSig (p14At Z).codes G arr (smpNamed (p14At Z).codes seats) ms₁
    decT₁ M₁ = M₁) (hRc : ∀ q y, ocEnd get N₁ M₁ links (First.flatPlaces true links true) q y → Rc q
    → (get q).2.failed = none → ToldDesc.rcLastB 0 (vAt Z N₁) Ld (p14At Z).codes (get q).2 = true)
    (hP : PlanOk₃ o mk Z N c D G arr dB dt ms₁ ms₂ N₁ Ns links (First.flatPlaces true links true) r
    (N₁.treesAt none) 0 1 (vAt Z N₁) Ld) (hX : XSamples (p14At Z).codes (p14At Z).S X) (hS : ∀ q y,
    ocEnd get N₁ M₁ links (First.flatPlaces true links true) q y → Rc q → (get q).2.failed = none →
    ∀ f, firstOfS (get q).2 = some f → SeatsNumber seats f.book) (hN : ∀ x ∈ (mineOf ms₁ ms₂ N₁ Ns),
    seatOf x = (D.t₁ + 1, 0) → ∀ d, X d = true → oNo x = d.loc.oOmega) (row0B : RowZeroOwed
    (tiedNumbers N₁ Ns) (tiedMeaning get M₁ (meaningSigS (p14At Z).codes G arr (smpSt (p14At
    Z).codes oNo stSh) ms₂ decT₂ MS)) (⟨rowsOpen (p14At Z).codes arr D.t₁ D.t₂⟩ : MeaningL (FU o mk
    Z N c).S₃ (Wit Cells Tok MsgT)) (promSigS (p14At Z).codes G (smpSt (p14At Z).codes oNo stSh) ms₂
    stOf bookOf Pm₀) (fillAt (p14At Z) (c2 N).rounds (fun q => firstOfS (get q).2) (endedX X)) (fun
    q y => ocEnd get N₁ M₁ links (First.flatPlaces true links true) q y ∧ Rc q) (pieceZeroAt (FU o
    mk Z N c) D (c0 Z) (restCap (extsLast (Tok := Tok) (FU o mk Z N c) D (p14At Z).codes G arr
    (smpLast (p14At Z).codes (smpNamed (p14At Z).codes seats) (smpSt (p14At Z).codes oNo stSh) get
    Ns) decT c₀' (mineOf ms₁ ms₂ N₁ Ns))))) : EachLeads (onQ₃ (Fr := frameAt D (allOf D) D.key₃
    (atDesc (FU o mk Z N c) (piecesAt (ckP .two) (FU o mk Z N c) D a₁ k₁ a₂ k₂ (c0 Z) [c1 N, c2 N,
    c3 Z N] rest₁ rest₂ (restCap (extsLast (Tok := Tok) (FU o mk Z N c) D (p14At Z).codes G arr
    (smpLast (p14At Z).codes (smpNamed (p14At Z).codes seats) (smpSt (p14At Z).codes oNo stSh) get
    Ns) decT c₀' (mineOf ms₁ ms₂ N₁ Ns))) d wEnd)).ft₃) (tiedNumbers N₁ Ns) (tiedMeaning get M₁
    (meaningSigS (p14At Z).codes G arr (smpSt (p14At Z).codes oNo stSh) ms₂ decT₂ MS)) (promSigS
    (p14At Z).codes G (smpSt (p14At Z).codes oNo stSh) ms₂ stOf bookOf Pm₀) (besideS (fillAt (p14At
    Z) (c2 N).rounds (fun q => firstOfS (get q).2) (endedX X)) (yTree (p14At Z).codes (p14At Z).S))
    (fun q y => ocEnd get N₁ M₁ links (First.flatPlaces true links true) q y ∧ Rc q)) (stepQ₃
    (atDesc (FU o mk Z N c) (piecesAt (ckP .two) (FU o mk Z N c) D a₁ k₁ a₂ k₂ (c0 Z) [c1 N, c2 N,
    c3 Z N] rest₁ rest₂ (restCap (extsLast (Tok := Tok) (FU o mk Z N c) D (p14At Z).codes G arr
    (smpLast (p14At Z).codes (smpNamed (p14At Z).codes seats) (smpSt (p14At Z).codes oNo stSh) get
    Ns) decT c₀' (mineOf ms₁ ms₂ N₁ Ns))) d wEnd)) (tiedNumbers N₁ Ns) (tiedMeaning get M₁
    (meaningSigS (p14At Z).codes G arr (smpSt (p14At Z).codes oNo stSh) ms₂ decT₂ MS)) (⟨rowsOpen
    (p14At Z).codes arr D.t₁ D.t₂⟩ : MeaningL (FU o mk Z N c).S₃ (Wit Cells Tok MsgT)) (promSigS
    (p14At Z).codes G (smpSt (p14At Z).codes oNo stSh) ms₂ stOf bookOf Pm₀) (besideS (fillAt (p14At
    Z) (c2 N).rounds (fun q => firstOfS (get q).2) (endedX X)) (yTree (p14At Z).codes (p14At Z).S))
    (fun q y => ocEnd get N₁ M₁ links (First.flatPlaces true links true) q y ∧ Rc q)) 0 ((atDesc (FU
    o mk Z N c) (piecesAt (ckP .two) (FU o mk Z N c) D a₁ k₁ a₂ k₂ (c0 Z) [c1 N, c2 N, c3 Z N] rest₁
    rest₂ (restCap (extsLast (Tok := Tok) (FU o mk Z N c) D (p14At Z).codes G arr (smpLast (p14At
    Z).codes (smpNamed (p14At Z).codes seats) (smpSt (p14At Z).codes oNo stSh) get Ns) decT c₀'
    (mineOf ms₁ ms₂ N₁ Ns))) d wEnd)).p₃ :: (atDesc (FU o mk Z N c) (piecesAt (ckP .two) (FU o mk Z
    N c) D a₁ k₁ a₂ k₂ (c0 Z) [c1 N, c2 N, c3 Z N] rest₁ rest₂ (restCap (extsLast (Tok := Tok) (FU o
    mk Z N c) D (p14At Z).codes G arr (smpLast (p14At Z).codes (smpNamed (p14At Z).codes seats)
    (smpSt (p14At Z).codes oNo stSh) get Ns) decT c₀' (mineOf ms₁ ms₂ N₁ Ns))) d wEnd)).l₃) :=
  e3_at_top_unpulled seats oNo o mk Z N c D G arr dB dt get ms₁ ms₂ decT₁ decT₂ M₁ MS stOf bookOf
      Pm₀ N₁ Ns links X r Ld decT c₀' a₁ k₁ a₂ k₂ rest₁ rest₂ d wEnd Rc hSig hRc hP hX hS hN row0B
      (c0 Z) [c1 N, c2 N, c3 Z N] (last_flat_pure o mk Z (seatK Z N) N c)

end LLT25

#print axioms LLT25.closed_in_scope
#print axioms LLT25.own3_at_end
#print axioms LLT25.e3_at_end
