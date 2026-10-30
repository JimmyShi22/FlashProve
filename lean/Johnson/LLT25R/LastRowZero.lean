-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/LLT25R/LastRowZero.lean (`seatK`, `sharedSeatAt_is`, `beside_is_fill`,
`LastLeftB` and what stands on it lie in LastRowZeroB.lean (`endedX` in PlmCode.lean),
which this file imports: so that the law with row 0's debt as one premise draws no file of row 0's
own laws; `LastLeftB`: THE SAME STRUCTURE WITH ROW 0's DEBT AS ONE PREMISE,
row0B, IN ITS PAYER's OWN CONCLUSION's FORM; `LastLeftB.left`, `LastLeftK.toB`, `own3_of_leftB`,
`e3_of_leftB`; row0 is
lifted to the layer Y on the last chain's own state by `ownLiftS` and `framesLiftS`; ONE FIELD MORE:
earn₀: row 0's accepting run earns Y at border 1; decT and c₀' are letters of `LastLeftK`;
ROW 0's DEBT GOES BY ITS OWN FILES' LAW AT TWO LETTERS AND A LAYER, WHOSE PREMISES
ARE FIELDS HERE: `rowZeroOwed_oc`, Johnson/Flat/Last/RowZeroOc.lean):

THE LEDGER OF THE LAST CHAIN's
FIELD WITH ROW 0's LAW TAKEN APART: at K14's own shared seat and at the closed
book-keeping, the field `row0` of `LastLeft` (LastLedger.lean) GIVES WAY TO ITS PAYER's OWN
PREMISES.
  `seatK Z N`: the shared seat that the description's own seat lays (`Desc.K14.sharedSeatAt`,
    Johnson/Desc/ProofFile/Lot/K14SeatAtZ.lean, where the places are N): so the shared chain's state
    is K14's `St`.
  `beside_is_fill`: **the layer beside the book-keeping IS the book-keeping at a narrower "ended"**:
    `besideL (fillAt p R hand ended) X = fillAt p R hand (ended, where X says yes)`. So the ledger,
    which is general in hand and ended, stands at the layer without a turn; and whoever has "ended …
    = some e" in hand has X's yes of the shared chain's last state.
  `endedX X`: K14's end carried by `sharedOfEnd`, where X says yes.
  `LastLeftK`: `LastRest`'s eighteen fields at that seat, at hand := `firstOfS` of what `get` reads
    and ended := `endedX X`, WITH: psIs (the places are the links' own flat list); joint (
    `JointFour` at the first table's meaning: four equations); and TWO IMPLICATIONS BETWEEN
    LETTERS AND TERMS, each inside the promise at the layer: rows, dot.
  `LastLeftK.left`: it gives `LastLeft`. `e3_of_leftK`: **e₃ from `LastLeftK`.**
Limits. NO MEMBER. The two implications are the identity where ML.rows, MS.dot ARE the terms. Pw,
wSeat, t₁, t₂, X are letters. All limits of LastLedger.lean and of the law called. Nothing on
soundness.
-/
import Johnson.LLT25R.LastRowZeroB
import Johnson.Flat.Last.RowZeroOc

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
open VerifiableInference.Desc.Third (SharedOut firstOfS sharedOfEnd)
open VerifiableInference.Desc.Third.Law
open VerifiableInference.Desc.First (S ModelPart Item Meaning Numbers openSets sampledIn start)
open VerifiableInference.Desc.K13 (Where)
open VerifiableInference.Desc.K13.Law (EvalLaid WRow)
open _root_.Desc.K14 (St)
open _root_.Desc.K14.Law (DotOmAt JointFour)
open VerifiableInference.Desc.Third (P₁₄)
open ProofFile (SecondHashFunctionArgument LinksBy SharedSeat Cl)
open ToldDesc (p14At)

variable (o : SecondHashFunctionArgument) (mk : LinksBy) (Z : ProofFile.Pub) (N : H2U.Places4)
  (c : Chain S Cl) {Cells Tok P₀ : Type} (D : WholeD)
  (cs : OnBytes.Codes) {Xi' : Type} (G : FileDescription Xi') (arr : ℕ → ℕ → ℕ)
  (smp : (((FL o mk Z (seatK Z N) N c).XiPub × (FL o mk Z (seatK Z N) N c).S₁ × St) × (FL o mk Z
      (seatK Z N) N c).S₃) → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om
      i).Smp)
  (decT : (ℕ → Option (ℕ × List UInt64)) → (((FL o mk Z (seatK Z N) N c).XiPub × (FL o mk Z (seatK Z
      N) N c).S₁ × St) × (FL o mk Z (seatK Z N) N c).S₃) → Option Cells)
  (c₀' : Cells) (dB : RDT) (dt : List RDT) (mine : List Mem)
  (get : (FL o mk Z (seatK Z N) N c).XiPub × (FL o mk Z (seatK Z N) N c).S₁ → P₀ × First.S)
  (smp₁ : P₀ × First.S → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp)
  (smp₂ : St → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp)
  (ms₁ ms₂ : List Mem) (decT₁ : (ℕ → Option (ℕ × List UInt64)) → P₀ × First.S → Option Cells)
  (decT₂ : (ℕ → Option (ℕ × List UInt64)) → St → Option Cells)
  (M₁ : Meaning P₀ (Wit Cells Tok MsgT)) (MS : MeaningS St ((FL o mk Z (seatK Z N) N c).XiPub × (FL
      o mk Z (seatK Z N) N c).S₁) (Wit Cells Tok MsgT))
  (ML : MeaningL (FL o mk Z (seatK Z N) N c).S₃ (Wit Cells Tok MsgT)) (stOf : St →
      OnBytes.Statement)
  (bookOf : St → OnBytes.TreeBook) (Pm₀ : PromMeaning St) (N₁ : Numbers) (Ns : NumbersS)
  (links : List ModelPart) (ps : List VerifiableInference.Desc.Place)
  (Oc : (FL o mk Z (seatK Z N) N c).XiPub × (FL o mk Z (seatK Z N) N c).S₁ → Strs → Prop)
  (Y : ℕ → (FL o mk Z (seatK Z N) N c).S₃ → Bool)
  (num : Fmt.TreeSource → ℕ) (no : ℕ → ℕ) (rd : ℕ → ℕ) (r : Fmt.M1.Stage → ℕ)
  (Pw : Where) (t₁ t₂ : ℕ) (X : St → Bool) (wSeat : ℕ × ℕ)

/-- **ALL THAT IS STILL OWED FOR e₃, WITH ROW 0's LAW TAKEN APART.** -/
structure LastLeftK : Prop extends LastRest o mk Z (seatK Z N) N c D cs G arr smp dB dt mine get
    smp₁ smp₂ ms₁ ms₂ decT₁ decT₂ M₁ MS ML stOf bookOf Pm₀ N₁ Ns links ps Oc Y (fun q => firstOfS
        (get q).2) (endedX X) num no rd r where
  /-- THE PLACES ARE THE LINKS' OWN FLAT LIST. -/
  psIs : ps = First.flatPlaces true links true
  /-- WHAT ROW 0 SPENDS OF THE FIRST TABLE's MEANING: four equations (`JointFour`):
  the
  pin by signature (by make here); (Eval)'s row; the public items "(Eval) is laid" and "W sits". -/
  joint : JointFour cs G arr smp₁ ms₁ (fun a => a.2.st) (fun a w => tabAt a.2.st.codes arr (seatBy
      noFirst a.2.book) a.2.st w) Pw wSeat (meaningSig cs G arr smp₁ ms₁ decT₁ M₁)
  /-- AN IMPLICATION, inside the promise at border 1: what ML.rows says gives that every open row of
  the own group says its claim of the witness's words. PAYER: whoever lays ML.rows (the identity
  where it IS that term). -/
  rows : ∀ b w, onOcX (frameAt D (allOf D) D.key₃ (FL o mk Z (seatK Z N) N c).lastChainFirstTreeNumber) cs G arr
      get smp₂ ms₂ decT₂ (meaningSig cs G arr smp₁ ms₁ decT₁ M₁) MS stOf bookOf Pm₀ N₁ Ns (p14At Z)
      (c2 N).rounds X Oc 1 b → ML.rows b.1.2 w → ∃ t, enterOwn b.1.2 = .ok t ∧ ∀ i,
      OnBytes.Means.OpenSays OnBytes.Model.Reading.gl t.st t.g i (OnBytes.Means.wordsOn t.st (tabAt
      (p14At Z).codes arr (seatBy (noLast t₁ t₂ b.1.2.loc.firstTree) b.1.2.book) t.st w))
  /-- AN IMPLICATION, inside the promise at border 0: (Dot)'s equation at Omega as the shared
  chain's last state and book read it gives MS.dot. PAYER: whoever lays MS.dot. -/
  dot : ∀ a w, onOcX (frameAt D (allOf D) D.key₃ (FL o mk Z (seatK Z N) N c).lastChainFirstTreeNumber) cs G arr
      get smp₂ ms₂ decT₂ (meaningSig cs G arr smp₁ ms₁ decT₁ M₁) MS stOf bookOf Pm₀ N₁ Ns (p14At Z)
      (c2 N).rounds X Oc 0 a → DotOmAt (p14At Z).S (gOfS (get (a.1.1.1, a.1.1.2.1)).2) a.1.1.2.2
      (wordsShared arr t₁ a.1.1.2.2.st a.1.1.2.2.book w) (wvW arr (p14At Z) (fun q => (get q).2)
      (a.1.1.1, a.1.1.2.1) w) → MS.dot (a.1.1.1, a.1.1.2.1) a.1.1.2.2 (strsOf (frameAt D (allOf D)
      D.key₃ (FL o mk Z (seatK Z N) N c).lastChainFirstTreeNumber) a.2) w
  /-- ON THE LAYER Y: ROW 0's ACCEPTING RUN EARNS IT AT BORDER 1. -/
  earn₀ : ∀ a τ b, onQ₃ (Fr := (frameAt D (allOf D) D.key₃ (FL o mk Z (seatK Z N) N c).lastChainFirstTreeNumber))
      (tiedNumbers N₁ Ns) (tiedMeaning get (meaningSig cs G arr smp₁ ms₁ decT₁ M₁) (meaningSigS cs G
      arr smp₂ ms₂ decT₂ MS)) (promSigS cs G smp₂ ms₂ stOf bookOf Pm₀) (fillAt (p14At Z) (c2
      N).rounds (fun q => firstOfS (get q).2) (endedX X)) Oc 0 a → Y 0 a.1.2 = true → (pieceZeroAt
      (FL o mk Z (seatK Z N) N c) D (c0 Z) (restCap (extsLast (Tok := Tok) (FL o mk Z (seatK Z N) N
      c) D cs G arr smp decT c₀' mine))).ior.red.out a τ = some b → Y 1 b.1.2 = true

variable {o mk Z N c D cs G arr smp dB dt mine get smp₁ smp₂ ms₁ ms₂ decT₁ decT₂ M₁ MS ML stOf
    bookOf Pm₀ N₁ Ns links ps Oc Y num no rd r Pw t₁ t₂ X wSeat}

/-- Row 0's debt by its own files' law at two letters and a layer. -/
theorem LastLeftK.toB (L : LastLeftK o mk Z N c D cs G arr smp decT c₀' dB dt mine get smp₁ smp₂ ms₁
    ms₂ decT₁ decT₂ M₁ MS ML stOf bookOf Pm₀ N₁ Ns links ps Oc Y num no rd r Pw t₁ t₂ X wSeat) :
    LastLeftB o mk Z N c D cs G arr smp decT c₀' dB dt mine get smp₁ smp₂ ms₁ ms₂ decT₁ decT₂ M₁ MS
    ML stOf bookOf Pm₀ N₁ Ns links ps Oc Y num no rd r X where
  toLastRest := L.toLastRest
  row0B :=
      (beside_is_fill (p14At Z) (c2 N).rounds (fun q => firstOfS (get q).2) (fun d =>
          (_root_.Desc.K14.ended d).map sharedOfEnd) X) ▸
      rowZeroOwed_oc cs G arr get smp₁ smp₂ ms₁ ms₂ decT₂ Pw wSeat (meaningSig cs G arr smp₁ ms₁
          decT₁ M₁) MS stOf bookOf Pm₀ N₁ Ns links (p14At Z) (c2 N).rounds X ML t₁ t₂ (D.t₁ + D.t₂)
          _ _ _ (fun _ _ _ => rfl) L.joint Oc (L.psIs ▸ L.ocIs) L.ocBelow L.omega
          L.toLastRest.pinsRead L.rows L.dot
  earn₀ := L.earn₀

/-- **It gives the ledger's structure.** -/
theorem LastLeftK.left (L : LastLeftK o mk Z N c D cs G arr smp decT c₀' dB dt mine get smp₁ smp₂
    ms₁ ms₂ decT₁ decT₂ M₁ MS ML stOf bookOf Pm₀ N₁ Ns links ps Oc Y num no rd r Pw t₁ t₂ X wSeat) :
    LastLeft o mk Z (seatK Z N) N c D cs G arr smp decT c₀' dB dt mine get smp₁ smp₂ ms₁ ms₂ decT₁
    decT₂ M₁ MS ML stOf bookOf Pm₀ N₁ Ns links ps Oc Y (fun q => firstOfS (get q).2) (endedX X) num
    no rd r :=
  L.toB.left

variable (a₁ : Block (FL o mk Z (seatK Z N) N c).S₁ (FL o mk Z (seatK Z N) N c).Cl) (k₁ : List
    (Block (FL o mk Z (seatK Z N) N c).S₁ (FL o mk Z (seatK Z N) N c).Cl))
  (a₂ : Block St (FL o mk Z (seatK Z N) N c).Cl) (k₂ : List (Block St (FL o mk Z (seatK Z N) N
      c).Cl))
  (rest₁ : (i : ℕ) → (ds : List RDT) → Rest (ckP .two) (frameAt D (allOf D) D.key₁ 0) ((FL o mk Z
      (seatK Z N) N c).XiPub × (FL o mk Z (seatK Z N) N c).S₁) (Wit Cells Tok MsgT) ds)
  (rest₂ : (i : ℕ) → (ds : List RDT) → Rest (ckP .two) (frameAt D (allOf D) D.key₂ 0) (((FL o mk Z
      (seatK Z N) N c).XiPub × (FL o mk Z (seatK Z N) N c).S₁) × St) (Wit Cells Tok MsgT) ds)
  (d wEnd : Wit Cells Tok MsgT)

/-- **e₃ AT THE PROOF FILE's OWN DESCRIPTION, FROM THE LEDGER WITH ROW 0 TAKEN APART.** -/
theorem e3_of_leftK (L : LastLeftK o mk Z N c D cs G arr smp decT c₀' dB dt mine get smp₁ smp₂ ms₁
    ms₂ decT₁
    decT₂ M₁ MS ML stOf bookOf Pm₀ N₁ Ns links ps Oc Y num no rd r Pw t₁ t₂ X wSeat)
    (b₀ : Block (FL o mk Z (seatK Z N) N c).S₃ (FL o mk Z (seatK Z N) N c).Cl) (l : List (Block (FL
        o mk Z (seatK Z N) N c).S₃ (FL o mk Z (seatK Z N) N c).Cl))
    (hflat : (FL o mk Z (seatK Z N) N c).second.blocksInOrder = b₀ :: l)
    (hds : ds₂ D.ds₃ (held (P := (FL o mk Z (seatK Z N) N c).XiPub × (FL o mk Z (seatK Z N) N c).S₁
        × St) (c0 Z)) (held (P := (FL o mk Z (seatK Z N) N c).XiPub × (FL o mk Z (seatK Z N) N c).S₁
        × St) (c1 N)) (held (P := (FL o mk Z (seatK Z N) N c).XiPub × (FL o mk Z (seatK Z N) N c).S₁
        × St) (c2 N)) = dB :: dt) :
    EachLeads (onQ₃ (Fr := frameAt D (allOf D) D.key₃ (atDesc (FL o mk Z (seatK Z N) N c) (piecesAt
        (ckP .two) (FL o mk Z (seatK Z N) N c) D a₁ k₁ a₂ k₂ b₀ l rest₁ rest₂ (restCap (extsLast
        (Tok := Tok) (FL o mk Z (seatK Z N) N c) D cs G arr smp decT c₀' mine)) d wEnd)).ft₃)
        (tiedNumbers N₁ Ns) (tiedMeaning get (meaningSig cs G arr smp₁ ms₁ decT₁ M₁) (meaningSigS cs
        G arr smp₂ ms₂ decT₂ MS)) (promSigS cs G smp₂ ms₂ stOf bookOf Pm₀) (besideS (fillAt (p14At
            Z) (c2 N).rounds (fun q => firstOfS (get q).2) (endedX X)) Y) Oc)
      (stepQ₃ (atDesc (FL o mk Z (seatK Z N) N c) (piecesAt (ckP .two) (FL o mk Z (seatK Z N) N c) D
          a₁ k₁ a₂ k₂ b₀ l rest₁ rest₂ (restCap (extsLast (Tok := Tok) (FL o mk Z (seatK Z N) N c) D
          cs G arr smp decT c₀' mine)) d wEnd)) (tiedNumbers N₁ Ns) (tiedMeaning get (meaningSig cs
          G arr smp₁ ms₁ decT₁ M₁) (meaningSigS cs G arr smp₂ ms₂ decT₂ MS)) ML (promSigS cs G smp₂
          ms₂ stOf bookOf Pm₀) (besideS (fillAt (p14At Z) (c2 N).rounds (fun q => firstOfS (get
              q).2) (endedX X)) Y) Oc) 0
      ((atDesc (FL o mk Z (seatK Z N) N c) (piecesAt (ckP .two) (FL o mk Z (seatK Z N) N c) D a₁ k₁
          a₂ k₂ b₀ l rest₁ rest₂ (restCap (extsLast (Tok := Tok) (FL o mk Z (seatK Z N) N c) D cs G
          arr smp decT c₀' mine)) d wEnd)).p₃ :: (atDesc (FL o mk Z (seatK Z N) N c) (piecesAt (ckP
          .two) (FL o mk Z (seatK Z N) N c) D a₁ k₁ a₂ k₂ b₀ l rest₁ rest₂ (restCap (extsLast (Tok
          := Tok) (FL o mk Z (seatK Z N) N c) D cs G arr smp decT c₀' mine)) d wEnd)).l₃) :=
  e3_of_left a₁ k₁ a₂ k₂ rest₁ rest₂ d wEnd (L.left decT c₀') b₀ l hflat hds

/-- **The same in the tables' files' own form (`EachOwn`, Johnson/Desc/Sound/Spine.lean).** -/
theorem own3_of_leftK (L : LastLeftK o mk Z N c D cs G arr smp decT c₀' dB dt mine get smp₁ smp₂ ms₁
    ms₂ decT₁ decT₂ M₁ MS ML stOf bookOf Pm₀ N₁ Ns links ps Oc Y num no rd r Pw t₁ t₂ X wSeat) (b₀ :
    Block (FL o mk Z (seatK Z N) N c).S₃ (FL o mk Z (seatK Z N) N c).Cl) (l : List (Block (FL o mk Z
    (seatK Z N) N c).S₃ (FL o mk Z (seatK Z N) N c).Cl)) (hflat : (FL o mk Z (seatK Z N) N
    c).second.blocksInOrder = b₀ :: l) (hds : ds₂ D.ds₃ (held (P := (FL o mk Z (seatK Z N) N c).XiPub × (FL o
             mk Z (seatK Z N) N c).S₁ × St) (c0 Z)) (held (P := (FL o mk Z (seatK Z N) N c).XiPub × (FL o mk
             Z (seatK Z N) N c).S₁ × St) (c1 N)) (held (P := (FL o mk Z (seatK Z N) N c).XiPub × (FL o mk Z
             (seatK Z N) N c).S₁ × St) (c2 N)) = dB :: dt) : EachOwn (onQ₃ (Fr := frameAt D (allOf D) D.key₃
             (atDesc (FL o mk Z (seatK Z N) N c) (piecesAt (ckP .two) (FL o mk Z (seatK Z N) N c) D a₁ k₁ a₂
             k₂ b₀ l rest₁ rest₂ (restCap (extsLast (Tok := Tok) (FL o mk Z (seatK Z N) N c) D cs G arr smp
             decT c₀' mine)) d wEnd)).ft₃) (tiedNumbers N₁ Ns) (tiedMeaning get (meaningSig cs G arr smp₁ ms₁
             decT₁ M₁) (meaningSigS cs G arr smp₂ ms₂ decT₂ MS)) (promSigS cs G smp₂ ms₂ stOf bookOf Pm₀)
             (besideS (fillAt (p14At Z) (c2 N).rounds (fun q => firstOfS (get q).2) (endedX X)) Y) Oc)
    (meansQ₃ (tiedNumbers N₁ Ns) (tiedMeaning get (meaningSig cs G arr smp₁ ms₁ decT₁ M₁)
    (meaningSigS cs G arr smp₂ ms₂ decT₂ MS)) ML) insQ₃ outsQ₃ (· ∈ startLast) 0 ((atDesc (FL o mk Z
    (seatK Z N) N c) (piecesAt (ckP .two) (FL o mk Z (seatK Z N) N c) D a₁ k₁ a₂ k₂ b₀ l rest₁ rest₂
    (restCap (extsLast (Tok := Tok) (FL o mk Z (seatK Z N) N c) D cs G arr smp decT c₀' mine)) d
    wEnd)).p₃ :: (atDesc (FL o mk Z (seatK Z N) N c) (piecesAt (ckP .two) (FL o mk Z (seatK Z N) N
    c) D a₁ k₁ a₂ k₂ b₀ l rest₁ rest₂ (restCap (extsLast (Tok := Tok) (FL o mk Z (seatK Z N) N c) D
    cs G arr smp decT c₀' mine)) d wEnd)).l₃) :=
  own3_of_left a₁ k₁ a₂ k₂ rest₁ rest₂ d wEnd (L.left decT c₀') b₀ l hflat hds

end LLT25

#print axioms LLT25.e3_of_leftK
#print axioms LLT25.own3_of_leftK
#print axioms LLT25.LastLeftK.left
