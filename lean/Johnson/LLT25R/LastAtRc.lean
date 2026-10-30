-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/LLT25R/LastAtRc.lean: THE LAST TABLE's LAW AT ANY CONDITION Rc ON WHAT THE FIRST CHAIN
HANDS ON THAT GIVES THE FIVE TESTS. `e3_at_last` | `own3_at_last` (LastAt.lean) speak at Oc :=
`ocEnd … ∧ rcLastB 0 (vAt Z N₁) Ld cs`. The tables' files lay Oc := `ocEnd … ∧ Rc` at an Rc of their
own ("reached at the first chain's end", and more). `EachOwn` is not monotone in Oc: it stands in
front and behind. But the law beneath is general in Rc.
  `FoldFirst₃.ofRc`: the four facts on what the first chain hands on, at Oc := `ocEnd … ∧ Rc`, Rch
    := Rc of what is handed, FROM hRc : ∀ q y, `ocEnd … q y` → Rc q → (get q).2.failed = none →
    `rcLastB 0 (vAt Z N₁) Ld cs (get q).2 = true` (THE PAYER HAS THE FIRST CHAIN's WHOLE LAST
    PROMISE AND "NO MARK" IN HAND: not shown here),
    and `PlanOk₃`.
  `e3_at_rc`, `own3_at_rc`: **`e3_at_last`'s | `own3_at_last`'s statements with Rc q in the place of
    the five tests, from hRc.** `e3_at_rc_letter`, `own3_at_rc_letter`: the same
    at a meaning M₁ that is its own `meaningSig …` (as in LastAtLetter.lean).
Limits: those of LastAt.lean. hRc is a premise: whoever lays Rc owes it. NO MEMBER. Nothing on
soundness.
-/
import Johnson.LLT25R.LastAtLetter
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
open VerifiableInference.Desc.K13.Law (EvalLaid WRow)
open _root_.Desc.K14 (St)
open _root_.Desc.K14.Law (DotOmAt JointFour)
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

variable (Rc : (FL o mk Z (seatK Z N) N c).XiPub × (FL o mk Z (seatK Z N) N c).S₁ → Prop)

/-- **e₃ at any Rc that gives the five tests.** -/
theorem e3_at_rc (hRc : ∀ q y, ocEnd get N₁ (meaningSig (p14At Z).codes G arr smp₁ ms₁ decT₁ M₁)
    links (First.flatPlaces true links true) q y → Rc q → (get q).2.failed = none → ToldDesc.rcLastB
    0 (vAt Z N₁) Ld (p14At Z).codes (get q).2 = true) (hP : PlanOk₃ o mk Z N c D G arr dB dt ms₁ ms₂
    N₁ Ns links (First.flatPlaces true links
    true) r (N₁.treesAt none) 0 1 (vAt Z N₁) Ld) (hX : XSamples (p14At Z).codes (p14At Z).S X) (hR :
    Readers₃ o mk Z N c D G arr get smp₁ smp₂ ms₁ ms₂ decT₁ decT₂ M₁ MS stOf bookOf Pm₀ N₁ Ns X (fun
    q y => ocEnd get N₁ (meaningSig (p14At Z).codes G arr smp₁ ms₁ decT₁ M₁) links (First.flatPlaces
    true links true) q y ∧ Rc q) 1 (vAt Z N₁)) (joint : JointFour (p14At Z).codes G arr smp₁ ms₁
    (fun a => a.2.st) (fun a w => tabAt a.2.st.codes arr (seatBy noFirst a.2.book) a.2.st w) Pw
    wSeat (meaningSig (p14At Z).codes G arr smp₁ ms₁ decT₁ M₁)) (dot : ∀ a w, onOcX (frameAt D
    (allOf D) D.key₃ (FL o mk Z (seatK Z N) N c).lastChainFirstTreeNumber) (p14At Z).codes G arr get smp₂ ms₂
    decT₂ (meaningSig (p14At Z).codes G arr smp₁ ms₁ decT₁ M₁) MS stOf bookOf Pm₀ N₁ Ns (p14At Z)
    (c2 N).rounds X (fun q y => ocEnd get N₁ (meaningSig (p14At Z).codes G arr smp₁ ms₁ decT₁ M₁)
    links (First.flatPlaces true links true) q y ∧ Rc q) 0 a → DotOmAt (p14At Z).S (gOfS (get
    (a.1.1.1, a.1.1.2.1)).2) a.1.1.2.2 (wordsShared arr D.t₁ a.1.1.2.2.st a.1.1.2.2.book w) (wvW arr
    (p14At Z) (fun q => (get q).2) (a.1.1.1, a.1.1.2.1) w) → MS.dot (a.1.1.1, a.1.1.2.1) a.1.1.2.2
    (strsOf (frameAt D (allOf D) D.key₃ (FL o mk Z (seatK Z N) N c).lastChainFirstTreeNumber) a.2) w) (b₀ : Block
                  (FL o mk Z (seatK Z N) N c).S₃ (FL o mk Z (seatK Z N) N c).Cl) (l : List (Block (FL o mk Z
                  (seatK Z N) N c).S₃ (FL o mk Z (seatK Z N) N c).Cl)) (hflat : (FL o mk Z (seatK Z N) N
                  c).second.blocksInOrder = b₀ :: l) : EachLeads (onQ₃ (Fr := frameAt D (allOf D) D.key₃ (atDesc (FL o mk Z
                           (seatK Z N) N c) (piecesAt (ckP .two) (FL o mk Z (seatK Z N) N c) D a₁ k₁ a₂ k₂ b₀ l rest₁ rest₂
                           (restCap (extsLast (Tok := Tok) (FL o mk Z (seatK Z N) N c) D (p14At Z).codes G arr (smpLast
                           (p14At Z).codes smp₁ smp₂ get Ns) decT c₀' (mineOf ms₁ ms₂ N₁ Ns))) d wEnd)).ft₃) (tiedNumbers
                           N₁ Ns) (tiedMeaning get (meaningSig (p14At Z).codes G arr smp₁ ms₁ decT₁ M₁) (meaningSigS (p14At
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
  e3_of_owed decT c₀' a₁ k₁ a₂ k₂ rest₁ rest₂ d wEnd (LastOwed.atRc Rc hP (FoldFirst₃.ofRc o mk Z N
      c D G arr dB dt get smp₁ smp₂ ms₁ ms₂ decT₁ decT₂ M₁ MS stOf bookOf Pm₀ N₁ Ns links X r Ld Rc
      hRc hP) (FoldRest₃.ofX hP hX) hR rfl joint dot) b₀ l hflat

/-- **The same in the tables' files' own form (`EachOwn`, Johnson/Desc/Sound/Spine.lean).** -/
theorem own3_at_rc (hRc : ∀ q y, ocEnd get N₁ (meaningSig (p14At Z).codes G arr smp₁ ms₁ decT₁ M₁)
    links (First.flatPlaces true links true) q y → Rc q → (get q).2.failed = none → ToldDesc.rcLastB
    0 (vAt Z N₁) Ld (p14At Z).codes (get q).2 = true) (hP : PlanOk₃ o mk Z N c D G arr dB dt ms₁ ms₂
    N₁ Ns links (First.flatPlaces true links
    true) r (N₁.treesAt none) 0 1 (vAt Z N₁) Ld) (hX : XSamples (p14At Z).codes (p14At Z).S X) (hR :
    Readers₃ o mk Z N c D G arr get smp₁ smp₂ ms₁ ms₂ decT₁ decT₂ M₁ MS stOf bookOf Pm₀ N₁ Ns X (fun
    q y => ocEnd get N₁ (meaningSig (p14At Z).codes G arr smp₁ ms₁ decT₁ M₁) links (First.flatPlaces
    true links true) q y ∧ Rc q) 1 (vAt Z N₁)) (joint : JointFour (p14At Z).codes G arr smp₁ ms₁
    (fun a => a.2.st) (fun a w => tabAt a.2.st.codes arr (seatBy noFirst a.2.book) a.2.st w) Pw
    wSeat (meaningSig (p14At Z).codes G arr smp₁ ms₁ decT₁ M₁)) (dot : ∀ a w, onOcX (frameAt D
    (allOf D) D.key₃ (FL o mk Z (seatK Z N) N c).lastChainFirstTreeNumber) (p14At Z).codes G arr get smp₂ ms₂
    decT₂ (meaningSig (p14At Z).codes G arr smp₁ ms₁ decT₁ M₁) MS stOf bookOf Pm₀ N₁ Ns (p14At Z)
    (c2 N).rounds X (fun q y => ocEnd get N₁ (meaningSig (p14At Z).codes G arr smp₁ ms₁ decT₁ M₁)
    links (First.flatPlaces true links true) q y ∧ Rc q) 0 a → DotOmAt (p14At Z).S (gOfS (get
    (a.1.1.1, a.1.1.2.1)).2) a.1.1.2.2 (wordsShared arr D.t₁ a.1.1.2.2.st a.1.1.2.2.book w) (wvW arr
    (p14At Z) (fun q => (get q).2) (a.1.1.1, a.1.1.2.1) w) → MS.dot (a.1.1.1, a.1.1.2.1) a.1.1.2.2
    (strsOf (frameAt D (allOf D) D.key₃ (FL o mk Z (seatK Z N) N c).lastChainFirstTreeNumber) a.2) w) (b₀ : Block
                  (FL o mk Z (seatK Z N) N c).S₃ (FL o mk Z (seatK Z N) N c).Cl) (l : List (Block (FL o mk Z
                  (seatK Z N) N c).S₃ (FL o mk Z (seatK Z N) N c).Cl)) (hflat : (FL o mk Z (seatK Z N) N
                  c).second.blocksInOrder = b₀ :: l) : EachOwn (onQ₃ (Fr := frameAt D (allOf D) D.key₃ (atDesc (FL o mk Z
                           (seatK Z N) N c) (piecesAt (ckP .two) (FL o mk Z (seatK Z N) N c) D a₁ k₁ a₂ k₂ b₀ l rest₁ rest₂
                           (restCap (extsLast (Tok := Tok) (FL o mk Z (seatK Z N) N c) D (p14At Z).codes G arr (smpLast
                           (p14At Z).codes smp₁ smp₂ get Ns) decT c₀' (mineOf ms₁ ms₂ N₁ Ns))) d wEnd)).ft₃) (tiedNumbers
                           N₁ Ns) (tiedMeaning get (meaningSig (p14At Z).codes G arr smp₁ ms₁ decT₁ M₁) (meaningSigS (p14At
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
  own3_of_owed decT c₀' a₁ k₁ a₂ k₂ rest₁ rest₂ d wEnd (LastOwed.atRc Rc hP (FoldFirst₃.ofRc o mk Z
      N c D G arr dB dt get smp₁ smp₂ ms₁ ms₂ decT₁ decT₂ M₁ MS stOf bookOf Pm₀ N₁ Ns links X r Ld
      Rc hRc hP) (FoldRest₃.ofX hP hX) hR rfl joint dot) b₀ l hflat

/-- **e₃ at any such Rc, at a meaning that is its own `meaningSig …`.** -/
theorem e3_at_rc_letter (hSig : meaningSig (p14At Z).codes G arr smp₁ ms₁ decT₁ M₁ = M₁) (hRc : ∀ q
    y, ocEnd get N₁ M₁ links (First.flatPlaces true links true) q y → Rc q → (get q).2.failed = none
    → ToldDesc.rcLastB 0 (vAt Z N₁) Ld (p14At Z).codes (get q).2 = true) (hP : PlanOk₃ o mk Z N
    c D G arr dB dt ms₁ ms₂ N₁ Ns links (First.flatPlaces true links true) r (N₁.treesAt none) 0 1
    (vAt Z N₁) Ld) (hX : XSamples (p14At Z).codes (p14At Z).S X) (hR : Readers₃ o mk Z N c D G arr
    get smp₁ smp₂ ms₁ ms₂ decT₁ decT₂ M₁ MS stOf bookOf Pm₀ N₁ Ns X (fun q y => ocEnd get N₁ M₁
    links (First.flatPlaces true links true) q y ∧ Rc q) 1 (vAt Z N₁)) (joint : JointFour (p14At
    Z).codes G arr smp₁ ms₁ (fun a => a.2.st) (fun a w => tabAt a.2.st.codes arr (seatBy noFirst
    a.2.book) a.2.st w) Pw wSeat M₁) (dot : ∀ a w, onOcX (frameAt D (allOf D) D.key₃ (FL o mk Z
    (seatK Z N) N c).lastChainFirstTreeNumber) (p14At Z).codes G arr get smp₂ ms₂ decT₂ M₁ MS stOf bookOf Pm₀ N₁
    Ns (p14At Z) (c2 N).rounds X (fun q y => ocEnd get N₁ M₁ links (First.flatPlaces true links
    true) q y ∧ Rc q) 0 a → DotOmAt (p14At Z).S (gOfS (get (a.1.1.1, a.1.1.2.1)).2) a.1.1.2.2
    (wordsShared arr D.t₁ a.1.1.2.2.st a.1.1.2.2.book w) (wvW arr (p14At Z) (fun q => (get q).2)
    (a.1.1.1, a.1.1.2.1) w) → MS.dot (a.1.1.1, a.1.1.2.1) a.1.1.2.2 (strsOf (frameAt D (allOf D)
    D.key₃ (FL o mk Z (seatK Z N) N c).lastChainFirstTreeNumber) a.2) w) (b₀ : Block (FL o mk Z (seatK Z N) N
                  c).S₃ (FL o mk Z (seatK Z N) N c).Cl) (l : List (Block (FL o mk Z (seatK Z N) N c).S₃ (FL o mk Z
                  (seatK Z N) N c).Cl)) (hflat : (FL o mk Z (seatK Z N) N c).second.blocksInOrder = b₀ :: l) : EachLeads
    (onQ₃ (Fr := frameAt D (allOf D) D.key₃ (atDesc (FL o mk Z (seatK Z N) N c) (piecesAt (ckP .two)
    (FL o mk Z (seatK Z N) N c) D a₁ k₁ a₂ k₂ b₀ l rest₁ rest₂ (restCap (extsLast (Tok := Tok) (FL o
    mk Z (seatK Z N) N c) D (p14At Z).codes G arr (smpLast (p14At Z).codes smp₁ smp₂ get Ns) decT
    c₀' (mineOf ms₁ ms₂ N₁ Ns))) d wEnd)).ft₃) (tiedNumbers N₁ Ns) (tiedMeaning get M₁ (meaningSigS
    (p14At Z).codes G arr smp₂ ms₂ decT₂ MS)) (promSigS (p14At Z).codes G smp₂ ms₂ stOf bookOf Pm₀)
    (besideS (fillAt (p14At Z) (c2 N).rounds (fun q => firstOfS (get q).2) (endedX X)) (yTree (p14At
    Z).codes (p14At Z).S)) (fun q y => ocEnd get N₁ M₁ links (First.flatPlaces true links true) q y
    ∧ Rc q)) (stepQ₃ (atDesc (FL o mk Z (seatK Z N) N c) (piecesAt (ckP .two) (FL o mk Z (seatK Z N)
    N c) D a₁ k₁ a₂ k₂ b₀ l rest₁ rest₂ (restCap (extsLast (Tok := Tok) (FL o mk Z (seatK Z N) N c)
    D (p14At Z).codes G arr (smpLast (p14At Z).codes smp₁ smp₂ get Ns) decT c₀' (mineOf ms₁ ms₂ N₁
    Ns))) d wEnd)) (tiedNumbers N₁ Ns) (tiedMeaning get M₁ (meaningSigS (p14At Z).codes G arr smp₂
    ms₂ decT₂ MS)) (⟨rowsOpen (p14At Z).codes arr D.t₁ D.t₂⟩ : MeaningL (FL o mk Z (seatK Z N) N
    c).S₃ (Wit Cells Tok MsgT)) (promSigS (p14At Z).codes G smp₂ ms₂ stOf bookOf Pm₀) (besideS
    (fillAt (p14At Z) (c2 N).rounds (fun q => firstOfS (get q).2) (endedX X)) (yTree (p14At Z).codes
    (p14At Z).S)) (fun q y => ocEnd get N₁ M₁ links (First.flatPlaces true links true) q y ∧ Rc q))
    0 ((atDesc (FL o mk Z (seatK Z N) N c) (piecesAt (ckP .two) (FL o mk Z (seatK Z N) N c) D a₁ k₁
    a₂ k₂ b₀ l rest₁ rest₂ (restCap (extsLast (Tok := Tok) (FL o mk Z (seatK Z N) N c) D (p14At
    Z).codes G arr (smpLast (p14At Z).codes smp₁ smp₂ get Ns) decT c₀' (mineOf ms₁ ms₂ N₁ Ns))) d
    wEnd)).p₃ :: (atDesc (FL o mk Z (seatK Z N) N c) (piecesAt (ckP .two) (FL o mk Z (seatK Z N) N
    c) D a₁ k₁ a₂ k₂ b₀ l rest₁ rest₂ (restCap (extsLast (Tok := Tok) (FL o mk Z (seatK Z N) N c) D
    (p14At Z).codes G arr (smpLast (p14At Z).codes smp₁ smp₂ get Ns) decT c₀' (mineOf ms₁ ms₂ N₁
    Ns))) d wEnd)).l₃) := by
  have T := e3_at_rc o mk Z N c D G arr dB dt get smp₁ smp₂ ms₁ ms₂ decT₁ decT₂ M₁ MS stOf bookOf
      Pm₀ N₁ Ns links X r Pw wSeat Ld decT c₀' a₁ k₁ a₂ k₂ rest₁ rest₂ d wEnd Rc
  rw [hSig] at T
  exact T hRc hP hX hR joint dot b₀ l hflat

/-- **The same in the tables' files' own form (`EachOwn`, Johnson/Desc/Sound/Spine.lean).** -/
theorem own3_at_rc_letter (hSig : meaningSig (p14At Z).codes G arr smp₁ ms₁ decT₁ M₁ = M₁) (hRc : ∀
    q y, ocEnd get N₁ M₁ links (First.flatPlaces true links true) q y → Rc q → (get q).2.failed =
    none → ToldDesc.rcLastB 0 (vAt Z N₁) Ld (p14At Z).codes (get q).2 = true) (hP : PlanOk₃ o mk
    Z N c D G arr dB dt ms₁ ms₂ N₁ Ns links (First.flatPlaces true links true) r (N₁.treesAt none) 0
    1 (vAt Z N₁) Ld) (hX : XSamples (p14At Z).codes (p14At Z).S X) (hR : Readers₃ o mk Z N c D G arr
    get smp₁ smp₂ ms₁ ms₂ decT₁ decT₂ M₁ MS stOf bookOf Pm₀ N₁ Ns X (fun q y => ocEnd get N₁ M₁
    links (First.flatPlaces true links true) q y ∧ Rc q) 1 (vAt Z N₁)) (joint : JointFour (p14At
    Z).codes G arr smp₁ ms₁ (fun a => a.2.st) (fun a w => tabAt a.2.st.codes arr (seatBy noFirst
    a.2.book) a.2.st w) Pw wSeat M₁) (dot : ∀ a w, onOcX (frameAt D (allOf D) D.key₃ (FL o mk Z
    (seatK Z N) N c).lastChainFirstTreeNumber) (p14At Z).codes G arr get smp₂ ms₂ decT₂ M₁ MS stOf bookOf Pm₀ N₁
    Ns (p14At Z) (c2 N).rounds X (fun q y => ocEnd get N₁ M₁ links (First.flatPlaces true links
    true) q y ∧ Rc q) 0 a → DotOmAt (p14At Z).S (gOfS (get (a.1.1.1, a.1.1.2.1)).2) a.1.1.2.2
    (wordsShared arr D.t₁ a.1.1.2.2.st a.1.1.2.2.book w) (wvW arr (p14At Z) (fun q => (get q).2)
    (a.1.1.1, a.1.1.2.1) w) → MS.dot (a.1.1.1, a.1.1.2.1) a.1.1.2.2 (strsOf (frameAt D (allOf D)
    D.key₃ (FL o mk Z (seatK Z N) N c).lastChainFirstTreeNumber) a.2) w) (b₀ : Block (FL o mk Z (seatK Z N) N
                  c).S₃ (FL o mk Z (seatK Z N) N c).Cl) (l : List (Block (FL o mk Z (seatK Z N) N c).S₃ (FL o mk Z
                  (seatK Z N) N c).Cl)) (hflat : (FL o mk Z (seatK Z N) N c).second.blocksInOrder = b₀ :: l) : EachOwn
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
  have T := own3_at_rc o mk Z N c D G arr dB dt get smp₁ smp₂ ms₁ ms₂ decT₁ decT₂ M₁ MS stOf bookOf
      Pm₀ N₁ Ns links X r Pw wSeat Ld decT c₀' a₁ k₁ a₂ k₂ rest₁ rest₂ d wEnd Rc
  rw [hSig] at T
  exact T hRc hP hX hR joint dot b₀ l hflat

end LLT25

#print axioms LLT25.e3_at_rc
#print axioms LLT25.own3_at_rc
#print axioms LLT25.e3_at_rc_letter
#print axioms LLT25.own3_at_rc_letter
