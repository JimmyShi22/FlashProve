-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/LLT25R/LastAt.lean, over `LastOwed`
(treeO IS A THEOREM, NO PREMISE:
the shape of the tree of Omega's copy rides as a layer on the last chain's own state, earned at
K14's second part's own accepting run): THE LAST TABLE's LAW AT ITS CLOSED LETTERS: e₃ (which gives
`leads3_last_chains_table`) FROM NAMED LISTS. One definition, one theorem; the proof is four calls.
  `vAt Z N₁`: where the handed own group's two members sit and which shapes they have: the index
    masks' seat N₁.index with the shape of the first notice of the sized proof's request.atStart;
    W's seat N₁.w with the shape (p14At Z).S.w.
  `e3_at_last`: AT nΩ := 1 · V := `vAt Z N₁` · n₁ := N₁.treesAt none · ft := 0 · ps := the links'
    own flat list · Oc := `ocEnd … ∧ rcLastB 0 (vAt Z N₁) Ld cs` of the first chain's last state ·
    Rch := that test of what is handed: **e₃ FROM `PlanOk₃` (33) · `Readers₃` (2) · ROW 0's joint
    AND dot · AND ONE CONDITION ON THE LETTER X, `XSamples`. NO FACT ON THE VERIFIER's STATE IS A
    PREMISE.** By `LastOwed.atRc`, `FoldFirst₃.ofRcLast`, `FoldRest₃.ofX`, `e3_of_owed`.
  THE BOOK-KEEPING IN ITS CONCLUSION: `besideS (fillAt … (endedX X)) (yTree cs S)`:
    `fillAt`, with two layers: X on the shared chain's last state (`fillAt … (endedX X)` is
    `besideL (fillZ …) X`: `beside_is_fill`, LastRowZeroB.lean) and `yTree` on the last chain's
    own state (LastLayerS.lean, LastTreeO.lean). WHOEVER LAYS THE LAST TABLE's LETTER PL
    LAYS THIS TERM; at border 0 `yTree` says yes of every state, so what the start owes does not
    grow.
That these are the values which the plan means is an evaluation, not a theorem: at them, of
`PlanOk₃`'s thirty-three tests, twenty-nine are seen true at both real sizes (files of evaluations
LastTests.lean and LastMore.lean, which are not in this library): twenty-three with a negative
test that rings; six (dataIs, planOk, ownMask, twoStages, places, free0) as printed values or a
routine's yes. NOT EVALUATED: closed (K12's files'); planShapes; planTreeO; elderBelow (by the
printed seats (1, 0) and (82, 0) | (21, 0) against D.t₁ = 83 | 22 it holds; no file of evaluations
has the line). planAt's clause on the radius holds where the shared table's list ms₂ bears Omega's
radius := W's own; at a list with 0 there it fails.
Limits. NO MEMBER IS SHOWN. That Rc is earned where the first chain ends, and X at the shared
chain's end, is other files' to show (reach_at_end, P5J/SevenOfTiedR.lean; `Sh.X_reached`,
Desc/K14/Law/SharedConstReached.lean). LETTERS OF THE LAST TABLE: X (meant: `Sh.X A 12`, at
which `XSamples` is `Sh.omega_sampled_at`) · wSeat (meant: N₁.w) · Ld (meant: the plan's own list of
the first chain's trees' shapes) · r (in scope: rWFull) · Pw · dB | dt (by the field stretch; by
evaluation the whole of D.ds₃) · the extractor's decT | c₀'; and whatever is the first table's or
the shared table's: get, the readers smp₁ | smp₂, the lists ms₁ | ms₂, N₁ | Ns, M₁ | MS, links, arr,
G. First arm of the proximity test. Nothing on soundness.
-/
import Johnson.LLT25R.LastOwed
import Johnson.LLT25R.LastV
import Johnson.LLT25R.LastRestX

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

/-- **e₃ AT THE LAST TABLE's CLOSED LETTERS.** -/
theorem e3_at_last
    (hP : PlanOk₃ o mk Z N c D G arr dB dt ms₁ ms₂ N₁ Ns links (First.flatPlaces true links true) r
        (N₁.treesAt none) 0 1 (vAt Z N₁) Ld)
    (hX : XSamples (p14At Z).codes (p14At Z).S X)
    (hR : Readers₃ o mk Z N c D G arr get smp₁ smp₂ ms₁ ms₂ decT₁ decT₂ M₁ MS stOf bookOf Pm₀ N₁ Ns
        X (fun q y => ocEnd get N₁ (meaningSig (p14At Z).codes G arr smp₁ ms₁ decT₁ M₁) links
        (First.flatPlaces true links true) q y ∧ ToldDesc.rcLastB 0 (vAt Z N₁) Ld (p14At Z).codes
        (get q).2 = true) 1 (vAt Z N₁))
    (joint : JointFour (p14At Z).codes G arr smp₁ ms₁ (fun a => a.2.st) (fun a w => tabAt
        a.2.st.codes arr (seatBy noFirst a.2.book) a.2.st w) Pw wSeat (meaningSig (p14At Z).codes G
        arr smp₁ ms₁ decT₁ M₁))
    (dot : ∀ a w, onOcX (frameAt D (allOf D) D.key₃ (FL o mk Z (seatK Z N) N c).lastChainFirstTreeNumber) (p14At
                      Z).codes G arr get smp₂ ms₂ decT₂ (meaningSig (p14At Z).codes G arr smp₁ ms₁ decT₁ M₁) MS
        stOf bookOf Pm₀ N₁ Ns (p14At Z) (c2 N).rounds X (fun q y => ocEnd get N₁ (meaningSig (p14At
        Z).codes G arr smp₁ ms₁ decT₁ M₁) links (First.flatPlaces true links true) q y ∧
        ToldDesc.rcLastB 0 (vAt Z N₁) Ld (p14At Z).codes (get q).2 = true) 0 a → DotOmAt (p14At Z).S
        (gOfS (get (a.1.1.1, a.1.1.2.1)).2) a.1.1.2.2 (wordsShared arr D.t₁ a.1.1.2.2.st
        a.1.1.2.2.book w) (wvW arr (p14At Z) (fun q => (get q).2) (a.1.1.1, a.1.1.2.1) w) → MS.dot
        (a.1.1.1, a.1.1.2.1) a.1.1.2.2 (strsOf (frameAt D (allOf D) D.key₃ (FL o mk Z (seatK Z N) N
        c).lastChainFirstTreeNumber) a.2) w)
    (b₀ : Block (FL o mk Z (seatK Z N) N c).S₃ (FL o mk Z (seatK Z N) N c).Cl) (l : List (Block (FL
        o mk Z (seatK Z N) N c).S₃ (FL o mk Z (seatK Z N) N c).Cl)) (hflat : (FL o mk Z (seatK Z N)
        N c).second.blocksInOrder = b₀ :: l) :
    EachLeads (onQ₃ (Fr := frameAt D (allOf D) D.key₃ (atDesc (FL o mk Z (seatK Z N) N c) (piecesAt
        (ckP .two) (FL o mk Z (seatK Z N) N c) D a₁ k₁ a₂ k₂ b₀ l rest₁ rest₂ (restCap (extsLast
        (Tok := Tok) (FL o mk Z (seatK Z N) N c) D (p14At Z).codes G arr (smpLast (p14At Z).codes
        smp₁ smp₂ get Ns) decT c₀' (mineOf ms₁ ms₂ N₁ Ns))) d wEnd)).ft₃) (tiedNumbers N₁ Ns)
        (tiedMeaning get (meaningSig (p14At Z).codes G arr smp₁ ms₁ decT₁ M₁) (meaningSigS (p14At
        Z).codes G arr smp₂ ms₂ decT₂ MS)) (promSigS (p14At Z).codes G smp₂ ms₂ stOf bookOf Pm₀)
        (besideS (fillAt (p14At Z) (c2 N).rounds (fun q => firstOfS (get q).2) (endedX X)) (yTree
        (p14At Z).codes (p14At Z).S)) (fun q y => ocEnd get N₁ (meaningSig (p14At Z).codes G arr
        smp₁ ms₁ decT₁ M₁) links (First.flatPlaces true links true) q y ∧ ToldDesc.rcLastB 0 (vAt Z
        N₁) Ld (p14At Z).codes (get q).2 = true)) (stepQ₃ (atDesc (FL o mk Z (seatK Z N) N c)
        (piecesAt (ckP .two) (FL o mk Z (seatK Z N) N c) D a₁ k₁ a₂ k₂ b₀ l rest₁ rest₂ (restCap
        (extsLast (Tok := Tok) (FL o mk Z (seatK Z N) N c) D (p14At Z).codes G arr (smpLast (p14At
        Z).codes smp₁ smp₂ get Ns) decT c₀' (mineOf ms₁ ms₂ N₁ Ns))) d wEnd)) (tiedNumbers N₁ Ns)
        (tiedMeaning get (meaningSig (p14At Z).codes G arr smp₁ ms₁ decT₁ M₁) (meaningSigS (p14At
        Z).codes G arr smp₂ ms₂ decT₂ MS)) (⟨rowsOpen (p14At Z).codes arr D.t₁ D.t₂⟩ : MeaningL (FL
        o mk Z (seatK Z N) N c).S₃ (Wit Cells Tok MsgT)) (promSigS (p14At Z).codes G smp₂ ms₂ stOf
        bookOf Pm₀) (besideS (fillAt (p14At Z) (c2 N).rounds (fun q => firstOfS (get q).2) (endedX
        X)) (yTree (p14At Z).codes (p14At Z).S)) (fun q y => ocEnd get N₁ (meaningSig (p14At
        Z).codes G arr smp₁ ms₁ decT₁ M₁) links (First.flatPlaces true links true) q y ∧
        ToldDesc.rcLastB 0 (vAt Z N₁) Ld (p14At Z).codes (get q).2 = true)) 0 ((atDesc (FL o mk Z
        (seatK Z N) N c) (piecesAt (ckP .two) (FL o mk Z (seatK Z N) N c) D a₁ k₁ a₂ k₂ b₀ l rest₁
        rest₂ (restCap (extsLast (Tok := Tok) (FL o mk Z (seatK Z N) N c) D (p14At Z).codes G arr
        (smpLast (p14At Z).codes smp₁ smp₂ get Ns) decT c₀' (mineOf ms₁ ms₂ N₁ Ns))) d wEnd)).p₃ ::
        (atDesc (FL o mk Z (seatK Z N) N c) (piecesAt (ckP .two) (FL o mk Z (seatK Z N) N c) D a₁ k₁
        a₂ k₂ b₀ l rest₁ rest₂ (restCap (extsLast (Tok := Tok) (FL o mk Z (seatK Z N) N c) D (p14At
        Z).codes G arr (smpLast (p14At Z).codes smp₁ smp₂ get Ns) decT c₀' (mineOf ms₁ ms₂ N₁ Ns)))
        d wEnd)).l₃) :=
  e3_of_owed decT c₀' a₁ k₁ a₂ k₂ rest₁ rest₂ d wEnd (LastOwed.atRc (fun q => ToldDesc.rcLastB 0
      (vAt Z N₁) Ld (p14At Z).codes (get q).2 = true) hP (FoldFirst₃.ofRcLast hP) (FoldRest₃.ofX hP
      hX) hR rfl joint dot) b₀ l hflat

/-- **The same in the tables' files' own form (`EachOwn`, Johnson/Desc/Sound/Spine.lean).** -/
theorem own3_at_last (hP : PlanOk₃ o mk Z N c D G arr dB dt ms₁ ms₂ N₁ Ns links (First.flatPlaces
    true links true) r (N₁.treesAt none) 0 1 (vAt Z N₁) Ld) (hX : XSamples (p14At Z).codes (p14At
    Z).S X) (hR : Readers₃ o mk Z N c D G arr get smp₁ smp₂ ms₁ ms₂ decT₁ decT₂ M₁ MS stOf bookOf
    Pm₀ N₁ Ns X (fun q y => ocEnd get N₁ (meaningSig (p14At Z).codes G arr smp₁ ms₁ decT₁ M₁) links
    (First.flatPlaces true links true) q y ∧ ToldDesc.rcLastB 0 (vAt Z N₁) Ld (p14At Z).codes (get
    q).2 = true) 1 (vAt Z N₁)) (joint : JointFour (p14At Z).codes G arr smp₁ ms₁ (fun a => a.2.st)
    (fun a w => tabAt a.2.st.codes arr (seatBy noFirst a.2.book) a.2.st w) Pw wSeat (meaningSig
    (p14At Z).codes G arr smp₁ ms₁ decT₁ M₁)) (dot : ∀ a w, onOcX (frameAt D (allOf D) D.key₃ (FL o
    mk Z (seatK Z N) N c).lastChainFirstTreeNumber) (p14At Z).codes G arr get smp₂ ms₂ decT₂ (meaningSig (p14At
                  Z).codes G arr smp₁ ms₁ decT₁ M₁) MS stOf bookOf Pm₀ N₁ Ns (p14At Z) (c2 N).rounds X (fun q y =>
                  ocEnd get N₁ (meaningSig (p14At Z).codes G arr smp₁ ms₁ decT₁ M₁) links (First.flatPlaces true
                  links true) q y ∧ ToldDesc.rcLastB 0 (vAt Z N₁) Ld (p14At Z).codes (get q).2 = true) 0 a →
    DotOmAt (p14At Z).S (gOfS (get (a.1.1.1, a.1.1.2.1)).2) a.1.1.2.2 (wordsShared arr D.t₁
    a.1.1.2.2.st a.1.1.2.2.book w) (wvW arr (p14At Z) (fun q => (get q).2) (a.1.1.1, a.1.1.2.1) w) →
    MS.dot (a.1.1.1, a.1.1.2.1) a.1.1.2.2 (strsOf (frameAt D (allOf D) D.key₃ (FL o mk Z (seatK Z N)
    N c).lastChainFirstTreeNumber) a.2) w) (b₀ : Block (FL o mk Z (seatK Z N) N c).S₃ (FL o mk Z (seatK Z N) N
                  c).Cl) (l : List (Block (FL o mk Z (seatK Z N) N c).S₃ (FL o mk Z (seatK Z N) N c).Cl)) (hflat :
                  (FL o mk Z (seatK Z N) N c).second.blocksInOrder = b₀ :: l) : EachOwn (onQ₃ (Fr := frameAt D (allOf D)
                           D.key₃ (atDesc (FL o mk Z (seatK Z N) N c) (piecesAt (ckP .two) (FL o mk Z (seatK Z N) N c) D a₁
                           k₁ a₂ k₂ b₀ l rest₁ rest₂ (restCap (extsLast (Tok := Tok) (FL o mk Z (seatK Z N) N c) D (p14At
                           Z).codes G arr (smpLast (p14At Z).codes smp₁ smp₂ get Ns) decT c₀' (mineOf ms₁ ms₂ N₁ Ns))) d
                           wEnd)).ft₃) (tiedNumbers N₁ Ns) (tiedMeaning get (meaningSig (p14At Z).codes G arr smp₁ ms₁
                           decT₁ M₁) (meaningSigS (p14At Z).codes G arr smp₂ ms₂ decT₂ MS)) (promSigS (p14At Z).codes G
                           smp₂ ms₂ stOf bookOf Pm₀) (besideS (fillAt (p14At Z) (c2 N).rounds (fun q => firstOfS (get q).2)
                           (endedX X)) (yTree (p14At Z).codes (p14At Z).S)) (fun q y => ocEnd get N₁ (meaningSig (p14At
                           Z).codes G arr smp₁ ms₁ decT₁ M₁) links (First.flatPlaces true links true) q y ∧
                           ToldDesc.rcLastB 0 (vAt Z N₁) Ld (p14At Z).codes (get q).2 = true)) (meansQ₃ (tiedNumbers N₁ Ns)
                           (tiedMeaning get (meaningSig (p14At Z).codes G arr smp₁ ms₁ decT₁ M₁) (meaningSigS (p14At
                           Z).codes G arr smp₂ ms₂ decT₂ MS)) (⟨rowsOpen (p14At Z).codes arr D.t₁ D.t₂⟩ : MeaningL (FL o mk
                           Z (seatK Z N) N c).S₃ (Wit Cells Tok MsgT))) insQ₃ outsQ₃ (· ∈ startLast) 0 ((atDesc (FL o mk Z
                           (seatK Z N) N c) (piecesAt (ckP .two) (FL o mk Z (seatK Z N) N c) D a₁ k₁ a₂ k₂ b₀ l rest₁ rest₂
                           (restCap (extsLast (Tok := Tok) (FL o mk Z (seatK Z N) N c) D (p14At Z).codes G arr (smpLast
                           (p14At Z).codes smp₁ smp₂ get Ns) decT c₀' (mineOf ms₁ ms₂ N₁ Ns))) d wEnd)).p₃ :: (atDesc (FL o
                           mk Z (seatK Z N) N c) (piecesAt (ckP .two) (FL o mk Z (seatK Z N) N c) D a₁ k₁ a₂ k₂ b₀ l rest₁
                           rest₂ (restCap (extsLast (Tok := Tok) (FL o mk Z (seatK Z N) N c) D (p14At Z).codes G arr
                           (smpLast (p14At Z).codes smp₁ smp₂ get Ns) decT c₀' (mineOf ms₁ ms₂ N₁ Ns))) d wEnd)).l₃) :=
  own3_of_owed decT c₀' a₁ k₁ a₂ k₂ rest₁ rest₂ d wEnd (LastOwed.atRc (fun q => ToldDesc.rcLastB 0
      (vAt Z N₁) Ld (p14At Z).codes (get q).2 = true) hP (FoldFirst₃.ofRcLast hP) (FoldRest₃.ofX hP
      hX) hR rfl joint dot) b₀ l hflat

end LLT25

#print axioms LLT25.e3_at_last
#print axioms LLT25.own3_at_last
