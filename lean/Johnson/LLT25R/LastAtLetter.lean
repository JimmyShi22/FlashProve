-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/LLT25R/LastAtLetter.lean, over LastAt.lean:
THE LAST TABLE's LAW AT A LETTER FOR THE FIRST TABLE's MEANING.
`e3_at_last` (LastAt.lean) speaks at `meaningSig cs G arr smp₁ ms₁ decT₁ M₁`, M₁ a letter. Here: at
M₁ ITSELF, wherever M₁ is its own `meaningSig …`.
  `meaningSig_self`: a meaning whose six fields pin, noColl, shown, held, pinW, decodes are the
    fillings by signature is its own `meaningSig …`.
  `e3_at_letter`: **`e3_at_last`'s statement with M₁ in the place of `meaningSig … M₁`, everywhere
    from hSig.** The proof rewrites `e3_at_last`.
Why. The tables' files' composed meaning, `mgAll 𝔇 Mg` (Johnson/Desc/Sound/MgAll.lean),
has the six equations as its own lemmas, each by rfl (mgAll_pin,
mgAll_noColl, mgAll_shown, mgAll_held, mgAll_pinW, mgAll_decodes) [by reading: that file is
not imported here].
THEY STAND AT THAT MEANING's OWN LETTERS 𝔇.cs, 𝔇.G, 𝔇.arr, 𝔇.smp, 𝔇.ms, 𝔇.decT: so hSig
holds there where G, arr, smp₁, ms₁, decT₁ are laid as these AND 𝔇.cs IS (p14At Z).codes: the last
is a condition on the composed constant, read by nobody here. IT HAS BEEN COMPILED,
general in 𝔇 and Mg: mgAll 𝔇 Mg = meaningSig 𝔇.cs 𝔇.G 𝔇.arr 𝔇.smp 𝔇.ms 𝔇.decT (mgAll 𝔇 Mg) := rfl (a
rough check, which is not in this library; not shown here).
Limits: those of LastAt.lean. NO MEMBER. Nothing on soundness.
-/
import Johnson.LLT25R.LastAt

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
open VerifiableInference.Desc.K13.Law (EvalLaid WRow)
open _root_.Desc.K14 (St)
open _root_.Desc.K14.Law (DotOmAt JointFour)
open ProofFile (SecondHashFunctionArgument LinksBy SharedSeat Cl)
open ToldDesc (p14At)
open _root_.Desc.K14.Law.Fence (CoreFacts MemberFacts)
open H2K.Pin (NTuple)

/-- **A meaning whose six fields are the fillings by signature is its own `meaningSig …`.** -/
theorem meaningSig_self {P Cells Tok Xi : Type} (cs : OnBytes.Codes) (G : FileDescription Xi) (arr : ℕ → ℕ
           → ℕ)
    (smp : P × First.S → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp)
    (ms : List Mem) (decT : (ℕ → Option (ℕ × List UInt64)) → P × First.S → Option Cells)
    (Mg : Meaning P (Wit Cells Tok MsgT))
    (h1 : Mg.pin = pinJT cs G arr smp ms) (h2 : Mg.noColl = noCollJT cs G smp ms)
    (h3 : Mg.shown = shownJT cs G ms)
    (h4 : Mg.held = fun j t (a : P × First.S) => smpHeld a.2.st a.2.book j t)
    (h5 : Mg.pinW = pinWOf decT) (h6 : Mg.decodes = decodesOf decT) :
    meaningSig cs G arr smp ms decT Mg = Mg := by
  unfold meaningSig
  rw [← h1, ← h2, ← h3, ← h4, ← h5, ← h6]

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
          St → Bool) (r : Fmt.M1.Stage → ℕ) (Pw : Where) (wSeat : ℕ × ℕ) (Ld :
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

/-- **e₃ AT THE LAST TABLE's CLOSED LETTERS, AT A MEANING THAT IS ITS OWN `meaningSig …`.** -/
theorem e3_at_letter (hSig : meaningSig (p14At Z).codes G arr smp₁ ms₁ decT₁ M₁ = M₁) (hP : PlanOk₃
    o mk Z N c D G arr dB dt ms₁ ms₂ N₁ Ns links (First.flatPlaces true links true) r (N₁.treesAt
    none) 0 1 (vAt Z N₁) Ld) (hX : XSamples (p14At Z).codes (p14At Z).S X) (hR : Readers₃ o mk Z N c
    D G arr get smp₁ smp₂ ms₁ ms₂ decT₁ decT₂ M₁ MS stOf bookOf Pm₀ N₁ Ns X (fun q y => ocEnd get N₁
    M₁ links (First.flatPlaces true links true) q y ∧ ToldDesc.rcLastB 0 (vAt Z N₁) Ld (p14At
    Z).codes (get q).2 = true) 1 (vAt Z N₁)) (joint : JointFour (p14At Z).codes G arr smp₁ ms₁ (fun
    a => a.2.st) (fun a w => tabAt a.2.st.codes arr (seatBy noFirst a.2.book) a.2.st w) Pw wSeat M₁)
    (dot : ∀ a w, onOcX (frameAt D (allOf D) D.key₃ (FL o mk Z (seatK Z N) N c).lastChainFirstTreeNumber) (p14At
                  Z).codes G arr get smp₂ ms₂ decT₂ M₁ MS stOf bookOf Pm₀ N₁ Ns (p14At Z) (c2 N).rounds X (fun q y
                  => ocEnd get N₁ M₁ links (First.flatPlaces true links true) q y ∧ ToldDesc.rcLastB 0 (vAt Z N₁)
                  Ld (p14At Z).codes (get q).2 = true) 0 a → DotOmAt (p14At Z).S (gOfS (get (a.1.1.1,
                  a.1.1.2.1)).2) a.1.1.2.2 (wordsShared arr D.t₁ a.1.1.2.2.st a.1.1.2.2.book w) (wvW arr (p14At Z)
                  (fun q => (get q).2) (a.1.1.1, a.1.1.2.1) w) → MS.dot (a.1.1.1, a.1.1.2.1) a.1.1.2.2 (strsOf
                  (frameAt D (allOf D) D.key₃ (FL o mk Z (seatK Z N) N c).lastChainFirstTreeNumber) a.2) w) (b₀ : Block (FL o mk
                                Z (seatK Z N) N c).S₃ (FL o mk Z (seatK Z N) N c).Cl) (l : List (Block (FL o mk Z (seatK Z N) N
                                c).S₃ (FL o mk Z (seatK Z N) N c).Cl)) (hflat : (FL o mk Z (seatK Z N) N c).second.blocksInOrder = b₀ ::
                                l) : EachLeads (onQ₃ (Fr := frameAt D (allOf D) D.key₃ (atDesc (FL o mk Z (seatK Z N) N c)
                                (piecesAt (ckP .two) (FL o mk Z (seatK Z N) N c) D a₁ k₁ a₂ k₂ b₀ l rest₁ rest₂ (restCap
                                (extsLast (Tok := Tok) (FL o mk Z (seatK Z N) N c) D (p14At Z).codes G arr (smpLast (p14At
                                Z).codes smp₁ smp₂ get Ns) decT c₀' (mineOf ms₁ ms₂ N₁ Ns))) d wEnd)).ft₃) (tiedNumbers N₁ Ns)
                                (tiedMeaning get M₁ (meaningSigS (p14At Z).codes G arr smp₂ ms₂ decT₂ MS)) (promSigS (p14At
                                Z).codes G smp₂ ms₂ stOf bookOf Pm₀) (besideS (fillAt (p14At Z) (c2 N).rounds (fun q => firstOfS
                                (get q).2) (endedX X)) (yTree (p14At Z).codes (p14At Z).S)) (fun q y => ocEnd get N₁ M₁ links
                                (First.flatPlaces true links true) q y ∧ ToldDesc.rcLastB 0 (vAt Z N₁) Ld (p14At Z).codes (get
                                q).2 = true)) (stepQ₃ (atDesc (FL o mk Z (seatK Z N) N c) (piecesAt (ckP .two) (FL o mk Z (seatK
                                Z N) N c) D a₁ k₁ a₂ k₂ b₀ l rest₁ rest₂ (restCap (extsLast (Tok := Tok) (FL o mk Z (seatK Z N)
                                N c) D (p14At Z).codes G arr (smpLast (p14At Z).codes smp₁ smp₂ get Ns) decT c₀' (mineOf ms₁ ms₂
                                N₁ Ns))) d wEnd)) (tiedNumbers N₁ Ns) (tiedMeaning get M₁ (meaningSigS (p14At Z).codes G arr
                                smp₂ ms₂ decT₂ MS)) (⟨rowsOpen (p14At Z).codes arr D.t₁ D.t₂⟩ : MeaningL (FL o mk Z (seatK Z N)
                                N c).S₃ (Wit Cells Tok MsgT)) (promSigS (p14At Z).codes G smp₂ ms₂ stOf bookOf Pm₀) (besideS
                                (fillAt (p14At Z) (c2 N).rounds (fun q => firstOfS (get q).2) (endedX X)) (yTree (p14At Z).codes
                                (p14At Z).S)) (fun q y => ocEnd get N₁ M₁ links (First.flatPlaces true links true) q y ∧
                                ToldDesc.rcLastB 0 (vAt Z N₁) Ld (p14At Z).codes (get q).2 = true)) 0 ((atDesc (FL o mk Z (seatK
                                Z N) N c) (piecesAt (ckP .two) (FL o mk Z (seatK Z N) N c) D a₁ k₁ a₂ k₂ b₀ l rest₁ rest₂
                                (restCap (extsLast (Tok := Tok) (FL o mk Z (seatK Z N) N c) D (p14At Z).codes G arr (smpLast
                                (p14At Z).codes smp₁ smp₂ get Ns) decT c₀' (mineOf ms₁ ms₂ N₁ Ns))) d wEnd)).p₃ :: (atDesc (FL o
                                mk Z (seatK Z N) N c) (piecesAt (ckP .two) (FL o mk Z (seatK Z N) N c) D a₁ k₁ a₂ k₂ b₀ l rest₁
                                rest₂ (restCap (extsLast (Tok := Tok) (FL o mk Z (seatK Z N) N c) D (p14At Z).codes G arr
                                (smpLast (p14At Z).codes smp₁ smp₂ get Ns) decT c₀' (mineOf ms₁ ms₂ N₁ Ns))) d wEnd)).l₃) := by
  have T := e3_at_last o mk Z N c D G arr dB dt get smp₁ smp₂ ms₁ ms₂ decT₁ decT₂ M₁ MS stOf bookOf
      Pm₀ N₁ Ns
    links X r Pw wSeat Ld decT c₀' a₁ k₁ a₂ k₂ rest₁ rest₂ d wEnd
  rw [hSig] at T
  exact T hP hX hR joint dot b₀ l hflat

/-- **The same in the tables' files' own form (`EachOwn`, Johnson/Desc/Sound/Spine.lean).** -/
theorem own3_at_letter (hSig : meaningSig (p14At Z).codes G arr smp₁ ms₁ decT₁ M₁ = M₁) (hP :
    PlanOk₃ o mk Z N c D G arr dB dt ms₁ ms₂ N₁ Ns links (First.flatPlaces true links true) r
    (N₁.treesAt none) 0 1 (vAt Z N₁) Ld) (hX : XSamples (p14At Z).codes (p14At Z).S X) (hR :
    Readers₃ o mk Z N c D G arr get smp₁ smp₂ ms₁ ms₂ decT₁ decT₂ M₁ MS stOf bookOf Pm₀ N₁ Ns X (fun
    q y => ocEnd get N₁ M₁ links (First.flatPlaces true links true) q y ∧ ToldDesc.rcLastB 0 (vAt Z
    N₁) Ld (p14At Z).codes (get q).2 = true) 1 (vAt Z N₁)) (joint : JointFour (p14At Z).codes G arr
    smp₁ ms₁ (fun a => a.2.st) (fun a w => tabAt a.2.st.codes arr (seatBy noFirst a.2.book) a.2.st
    w) Pw wSeat M₁) (dot : ∀ a w, onOcX (frameAt D (allOf D) D.key₃ (FL o mk Z (seatK Z N) N
    c).lastChainFirstTreeNumber) (p14At Z).codes G arr get smp₂ ms₂ decT₂ M₁ MS stOf bookOf Pm₀ N₁ Ns (p14At Z)
    (c2 N).rounds X (fun q y => ocEnd get N₁ M₁ links (First.flatPlaces true links true) q y ∧
    ToldDesc.rcLastB 0 (vAt Z N₁) Ld (p14At Z).codes (get q).2 = true) 0 a → DotOmAt (p14At Z).S
    (gOfS (get (a.1.1.1, a.1.1.2.1)).2) a.1.1.2.2 (wordsShared arr D.t₁ a.1.1.2.2.st a.1.1.2.2.book
    w) (wvW arr (p14At Z) (fun q => (get q).2) (a.1.1.1, a.1.1.2.1) w) → MS.dot (a.1.1.1, a.1.1.2.1)
    a.1.1.2.2 (strsOf (frameAt D (allOf D) D.key₃ (FL o mk Z (seatK Z N) N c).lastChainFirstTreeNumber) a.2) w)
    (b₀ : Block (FL o mk Z (seatK Z N) N c).S₃ (FL o mk Z (seatK Z N) N c).Cl) (l : List (Block (FL
    o mk Z (seatK Z N) N c).S₃ (FL o mk Z (seatK Z N) N c).Cl)) (hflat : (FL o mk Z (seatK Z N) N
    c).second.blocksInOrder = b₀ :: l) : EachOwn (onQ₃ (Fr := frameAt D (allOf D) D.key₃ (atDesc (FL o mk Z
             (seatK Z N) N c) (piecesAt (ckP .two) (FL o mk Z (seatK Z N) N c) D a₁ k₁ a₂ k₂ b₀ l rest₁ rest₂
             (restCap (extsLast (Tok := Tok) (FL o mk Z (seatK Z N) N c) D (p14At Z).codes G arr (smpLast
             (p14At Z).codes smp₁ smp₂ get Ns) decT c₀' (mineOf ms₁ ms₂ N₁ Ns))) d wEnd)).ft₃) (tiedNumbers
             N₁ Ns) (tiedMeaning get M₁ (meaningSigS (p14At Z).codes G arr smp₂ ms₂ decT₂ MS)) (promSigS
             (p14At Z).codes G smp₂ ms₂ stOf bookOf Pm₀) (besideS (fillAt (p14At Z) (c2 N).rounds (fun q =>
             firstOfS (get q).2) (endedX X)) (yTree (p14At Z).codes (p14At Z).S)) (fun q y => ocEnd get N₁ M₁
             links (First.flatPlaces true links true) q y ∧ ToldDesc.rcLastB 0 (vAt Z N₁) Ld (p14At Z).codes
             (get q).2 = true)) (meansQ₃ (tiedNumbers N₁ Ns) (tiedMeaning get M₁ (meaningSigS (p14At Z).codes
             G arr smp₂ ms₂ decT₂ MS)) (⟨rowsOpen (p14At Z).codes arr D.t₁ D.t₂⟩ : MeaningL (FL o mk Z (seatK
             Z N) N c).S₃ (Wit Cells Tok MsgT))) insQ₃ outsQ₃ (· ∈ startLast) 0 ((atDesc (FL o mk Z (seatK Z
             N) N c) (piecesAt (ckP .two) (FL o mk Z (seatK Z N) N c) D a₁ k₁ a₂ k₂ b₀ l rest₁ rest₂ (restCap
             (extsLast (Tok := Tok) (FL o mk Z (seatK Z N) N c) D (p14At Z).codes G arr (smpLast (p14At
             Z).codes smp₁ smp₂ get Ns) decT c₀' (mineOf ms₁ ms₂ N₁ Ns))) d wEnd)).p₃ :: (atDesc (FL o mk Z
             (seatK Z N) N c) (piecesAt (ckP .two) (FL o mk Z (seatK Z N) N c) D a₁ k₁ a₂ k₂ b₀ l rest₁ rest₂
             (restCap (extsLast (Tok := Tok) (FL o mk Z (seatK Z N) N c) D (p14At Z).codes G arr (smpLast
             (p14At Z).codes smp₁ smp₂ get Ns) decT c₀' (mineOf ms₁ ms₂ N₁ Ns))) d wEnd)).l₃) := by
  have T := own3_at_last o mk Z N c D G arr dB dt get smp₁ smp₂ ms₁ ms₂ decT₁ decT₂ M₁ MS stOf
      bookOf
      Pm₀ N₁ Ns
    links X r Pw wSeat Ld decT c₀' a₁ k₁ a₂ k₂ rest₁ rest₂ d wEnd
  rw [hSig] at T
  exact T hP hX hR joint dot b₀ l hflat

end LLT25

#print axioms LLT25.meaningSig_self
#print axioms LLT25.e3_at_letter
#print axioms LLT25.own3_at_letter
