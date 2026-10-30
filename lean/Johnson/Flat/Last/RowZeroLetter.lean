-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Flat/Last/RowZeroLetter.lean: ROW 0's DEBT OF THE LAST CHAIN's LEDGER, WITH THE FIRST
TABLE's MEANING A LETTER, AS FAR AS ITS LINKS GO BY CALLS: rowZeroOwed_layers
(Johnson/Flat/Last/RowZeroLayers.lean) with the link dot paid from its ties and "W sits" had by
calls: the forms of dot_beside (RowZeroBeside.lean) and hW_at_words (RowZeroWSits.lean) at any Mg₁
that meets the table's files' JointSays. Three theorems: joinings; the two proofs are those two's,
with the table's files' hEL_layers | hW_layers (Johnson/Desc/Sound/PointAtLayers.lean; reached here through hEL_four | hW_four, Johnson/Flat/Last/JointFour.lean) called in place of hEL_at_ocEnd | hW_at_ocEnd.

Why. Whoever composes the last table (Johnson/LLT25R/LastRowZero.lean, which calls rowZeroOwed_oc of Johnson/Flat/Last/RowZeroOc.lean) calls row 0 at a letter Mg₁ under JointSays: the first table's
constant is other files' to fix.

OBJECT, FIELD as in Johnson/Flat/Last/RowZeroAtSig.lean.
USER     the field row0 of the last chain's ledger. rowZeroOwed_letter is called in
         Johnson/Flat/Last/RowZeroReads.lean.

  dot_letter          the link dot, at the letter, at the layer besideL … X.
  hW_letter           "W sits" at the ruled reader, at the letter. h3 (the item "K13.wSits" is open
                      at the first table's last border, at Mg₁'s own door) is asked outright.
  rowZeroOwed_letter  **the debt.** LEFT: hr · J · hOc · omega · pins · rows (rowZeroOwed_layers'
                      own) · hS · h3 · hlay · hsh · hseat · hB · hO · hdot.
What is not claimed. J at the composed meaning: untried. hB: where the names that carry facts on
the verifier's state leave the door, it is had from "reached", not from the promise: then it is to
be asked so. NO MEMBER. All that RowZeroLayers.lean, RowZeroBeside.lean and RowZeroWSits.lean do
not claim. No soundness.
J is JointFour (Johnson/Flat/Last/JointFour.lean): the table's files'
JointSays without its clause pileOne, which no law here spends and which does not close at the
composed meaning; the letter matC has left with it. JointSays.four gives J to whoever has the
five.

-/
import Johnson.Flat.Last.RowZeroLayers
import Johnson.Flat.Last.RowZeroWSits

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace VerifiableInference.OnPublicFiles.Last
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Maker OnBytes.Flat Fo.Peel Cb
open Johnson.Pack
open Iop Prob _root_.Run
open OnBytes.Means (Words)
open VerifiableInference.Desc VerifiableInference.Desc.Sound
open VerifiableInference.Desc.Shared VerifiableInference.Desc.Last
open VerifiableInference.Desc.First (ModelPart Item Meaning Numbers openSets start)
open VerifiableInference.Desc.Book (BookFits)
open VerifiableInference.Desc.Third (S₃ P₁₄)
open VerifiableInference.Desc.Third.Law
open VerifiableInference.Desc.K13 (Where)
open VerifiableInference.Desc.K13.Law (EvalAt laidOf vecAt wSitsMore wSits_open_all placeSeal)
open _root_.Desc.K14 (St)
open _root_.Desc.K14.Law (DotEq omegaOf gLaid WSits hW_at_ocEnd)

open VerifiableInference.Desc.First (Pub pubSets More)
open VerifiableInference.Desc.Third (firstOfS)
open VerifiableInference.Desc.K13.Law (EvalLaid laidOf_ok evalLaid_open_all wSitsItem)
open _root_.Desc.K14.Law (DotOmAt JointFour hEL_four hW_four)

/-- **The link dot from its ties, at a letter for the first table's meaning.** -/
theorem dot_letter {P S₁ P₀ Cells Tok Xi : Type} {Fr : Frame} (cs : OnBytes.Codes)
    (G : FileDescription Xi) (arr : ℕ → ℕ → ℕ) (get : P × S₁ → P₀ × First.S)
    (smp₁ : P₀ × First.S → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp)
    (smp₂ : St → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp)
    (ms₁ ms₂ : List Mem) (decT₂ : (ℕ → Option (ℕ × List UInt64)) → St → Option Cells)
    (Pw : Where) (wSeat : ℕ × ℕ)
    (Mg₁ : Meaning P₀ (Wit Cells Tok MsgT))
    (MS : MeaningS St (P × S₁) (Wit Cells Tok MsgT)) (stOf : St → OnBytes.Statement)
    (bookOf : St → OnBytes.TreeBook) (Pm₀ : PromMeaning St) (N₁ : Numbers) (Ns : NumbersS)
    (links : List ModelPart) (p : P₁₄) (R : List Fmt.DeclaredRound) (X : St → Bool)
    (t₁ : ℕ) (xW : Mem) (lay₀ : VectorLay) (omW : Wit Cells Tok MsgT → ℕ → GE)
    (J : JointFour cs G arr smp₁ ms₁ (fun a => a.2.st)
      (fun a w => tabAt a.2.st.codes arr (seatBy noFirst a.2.book) a.2.st w) Pw wSeat Mg₁)
    (hS : Pw.lin = p.S)
    (hW : ∀ q y D,
      ocEnd get N₁ Mg₁ links (First.flatPlaces true links true) q y →
      (get q).2.failed = none → laidOf Pw (get q).2 = some D →
      WSits (Cells := Cells) (Tok := Tok) cs arr xW lay₀ (fun q => (get q).2.st)
        (fun q w => tabAt (get q).2.st.codes arr (seatBy noFirst (get q).2.book) (get q).2.st w)
        q D)
    (hO : ∀ (d : St) (w : Wit Cells Tok MsgT), X d = true → ∀ y < p.S.matrixRows,
      omegaOf d.loc (linLayOmega d.st.codes p.S) (wordsShared arr t₁ d.st d.book w) y = omW w y)
    (hdot : ∀ q (s : St) y w,
      DotEq p.S.matrixRows p.S.kCol (gLaid Pw get q) (omW w)
        (s.loc.psiSh.map OnBytes.Model.Reading.gl.val)
        (vecAt lay₀ (xW.1.l.get xW.2).1 (wTab cs arr xW w)) → MS.dot q s y w) :
    ∀ a w,
      onLetX Fr cs G arr get smp₂ ms₂ decT₂ Mg₁ MS stOf bookOf Pm₀ N₁ Ns links p R X 0 a →
      DotOmAt p.S (gOfS (get (a.1.1.1, a.1.1.2.1)).2) a.1.1.2.2
        (wordsShared arr t₁ a.1.1.2.2.st a.1.1.2.2.book w)
        (wvW arr p (fun q => (get q).2) (a.1.1.1, a.1.1.2.1) w) →
      MS.dot (a.1.1.1, a.1.1.2.1) a.1.1.2.2 (strsOf Fr a.2) w := by
  intro a w ha h
  obtain ⟨ha', hx⟩ := (onQ₃_beside _ _ _ _ _ X 0 a).1 ha
  have hL : EvalLaid Pw (get (a.1.1.1, a.1.1.2.1)).2 :=
    hEL_four J get N₁ links _
      (evalLaid_open_all Mg₁.more links) _ _ ha.1 ha.2.1
  obtain ⟨D, hD, _⟩ := laidOf_ok hL
  exact hdot _ _ _ _ (dotEq_of_dotOmAt (gLaid_is_gOfS Pw get _ hL) (hO _ w hx)
    (wTie cs arr xW lay₀ p Pw get hS _ D hL hD (hW _ _ D ha.1 ha.2.1 hD)
      (started_first (started_fillZ ha')) w) h)

/-- **"W sits" at the ruled reader, at a letter for the first table's meaning.** -/
theorem hW_letter {P S₁ P₀ Cells Tok Xi : Type} (cs : OnBytes.Codes) (G : FileDescription Xi)
    (arr : ℕ → ℕ → ℕ) (get : P × S₁ → P₀ × First.S)
    (smp₁ : P₀ × First.S → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp)
    (ms₁ : List Mem)
    (Pw : Where) (wSeat : ℕ × ℕ)
    (Mg₁ : Meaning P₀ (Wit Cells Tok MsgT)) (N₁ : Numbers) (links : List ModelPart) (xW : Mem)
    (lay₀ : VectorLay)
    (J : JointFour cs G arr smp₁ ms₁ (fun a => a.2.st)
      (fun a w => tabAt a.2.st.codes arr (seatBy noFirst a.2.book) a.2.st w) Pw wSeat Mg₁)
    (h3 : wSitsItem ∈ (First.pubSets Mg₁.more links
      (First.flatPlaces true links true))[(First.flatPlaces true links true).length]?.getD [])
    (hlay : lay₀ = linLayW cs Pw.lin) (hsh : Pw.lin.w = (xW.1.l.get xW.2).1)
    (hseat : xW.1.seat xW.2 = wSeat)
    (hB : ∀ q y,
      ocEnd get N₁ Mg₁ links (First.flatPlaces true links true) q y →
      (get q).2.failed = none →
      NumberedBook 0 (get q).2.book ∧ BookFits (get q).2.book ∧
        ∀ o, o < (get q).2.st.oracles.size → ∃ r : ℕ × ℕ, (get q).2.book.place[o]? = some r) :
    ∀ q y D,
      ocEnd get N₁ Mg₁ links (First.flatPlaces true links true) q y →
      (get q).2.failed = none → laidOf Pw (get q).2 = some D →
      WSits (Cells := Cells) (Tok := Tok) cs arr xW lay₀ (fun q => (get q).2.st)
        (fun q w => tabAt (get q).2.st.codes arr (seatBy noFirst (get q).2.book) (get q).2.st w)
        q D := by
  intro q y D ho hm hD
  have W := hW_four J get N₁ links _ xW lay₀
    (fun q => (get q).2.st) (fun q w => tabByPlace cs arr (get q).2 w)
    h3 (fun _ => rfl) hlay
    (fun p w n j t sh => tabByPlace_book cs arr (get p).2 w n j t sh) hsh hseat q y D ho hm hD
  obtain ⟨hN, hF, hP⟩ := hB q y ho hm
  obtain ⟨x, hx, _⟩ := W.there
  have hst : D.st = (get q).2.st := W.st
  rw [hst] at hx
  have hlt : D.w < (get q).2.st.oracles.size := (Array.getElem?_eq_some_iff.1 hx).1
  obtain ⟨r, hr⟩ := hP D.w hlt
  have hs := seatFirst_place (get q).2.book hN hF D.w r hr
  have hc : (get q).2.st.codes = cs := by rw [← hst]; exact W.codes
  refine { W with tab := fun w => ?_ }
  rw [← W.tab w]
  show tabAt (get q).2.st.codes arr (seatBy noFirst (get q).2.book) (get q).2.st w D.w =
    tabByPlace cs arr (get q).2 w D.w
  unfold Sound.tabAt tabByPlace
  rw [hs, hr, hx, hc]

/-- **Row 0's debt at a letter for the first table's meaning, its link dot paid from its ties and
"W sits" by calls.** -/
theorem rowZeroOwed_letter {Cl : Type} {P S₁ P₀ Cells Tok Xi : Type} {Fr : Frame}
    (cs : OnBytes.Codes)
    (G : FileDescription Xi) (arr : ℕ → ℕ → ℕ) (get : P × S₁ → P₀ × First.S)
    (smp₁ : P₀ × First.S → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp)
    (smp₂ : St → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp)
    (ms₁ ms₂ : List Mem) (decT₂ : (ℕ → Option (ℕ × List UInt64)) → St → Option Cells)
    (Pw : Where) (wSeat : ℕ × ℕ)
    (Mg₁ : Meaning P₀ (Wit Cells Tok MsgT))
    (MS : MeaningS St (P × S₁) (Wit Cells Tok MsgT)) (stOf : St → OnBytes.Statement)
    (bookOf : St → OnBytes.TreeBook) (Pm₀ : PromMeaning St) (N₁ : Numbers) (Ns : NumbersS)
    (links : List ModelPart) (p : P₁₄) (R : List Fmt.DeclaredRound) (X : St → Bool)
    (ML : MeaningL S₃ (Wit Cells Tok MsgT)) (t₁ t₂ base : ℕ) (ds : List RDT) (back : List Fmt.RoundView)
    (r : Rest (ckP .two) Fr ((P × S₁ × St) × S₃) (Wit Cells Tok MsgT) ds)
    (hr : ∀ a τ w, r.ext a τ w = w)
    (J : JointFour cs G arr smp₁ ms₁ (fun a => a.2.st)
      (fun a w => tabAt a.2.st.codes arr (seatBy noFirst a.2.book) a.2.st w) Pw wSeat Mg₁)
    (hOc : OcReadsBelow base (ocEnd get N₁ Mg₁ links (First.flatPlaces true links true)))
    (omega : (Ns.tenant .oOmega).1 < base)
    (pins : PinsReadBelow (S₃ := S₃) (tiedNumbers N₁ Ns)
      (tiedMeaning get Mg₁ (meaningSigS cs G arr smp₂ ms₂ decT₂ MS)) ML base)
    (rows : ∀ b w,
      onLetX Fr cs G arr get smp₂ ms₂ decT₂ Mg₁ MS stOf bookOf Pm₀ N₁ Ns links p R X 1 b →
      ML.rows b.1.2 w →
      ∃ t, VerifiableInference.Desc.K12.Seat.enterOwn b.1.2 = .ok t ∧
        ∀ i, OnBytes.Means.OpenSays OnBytes.Model.Reading.gl t.st t.g i
          (OnBytes.Means.wordsOn t.st
            (tabAt p.codes arr (seatBy (noLast t₁ t₂ b.1.2.loc.firstTree) b.1.2.book) t.st w)))
    (xW : Mem) (lay₀ : VectorLay) (omW : Wit Cells Tok MsgT → ℕ → GE) (hS : Pw.lin = p.S)
    (h3 : wSitsItem ∈ (First.pubSets Mg₁.more links
      (First.flatPlaces true links true))[(First.flatPlaces true links true).length]?.getD [])
    (hlay : lay₀ = linLayW cs Pw.lin) (hsh : Pw.lin.w = (xW.1.l.get xW.2).1)
    (hseat : xW.1.seat xW.2 = wSeat)
    (hB : ∀ q y,
      ocEnd get N₁ Mg₁ links (First.flatPlaces true links true) q y →
      (get q).2.failed = none →
      NumberedBook 0 (get q).2.book ∧ BookFits (get q).2.book ∧
        ∀ o, o < (get q).2.st.oracles.size → ∃ r : ℕ × ℕ, (get q).2.book.place[o]? = some r)
    (hO : ∀ (d : St) (w : Wit Cells Tok MsgT), X d = true → ∀ y < p.S.matrixRows,
      omegaOf d.loc (linLayOmega d.st.codes p.S) (wordsShared arr t₁ d.st d.book w) y = omW w y)
    (hdot : ∀ q (s : St) y w,
      DotEq p.S.matrixRows p.S.kCol (gLaid Pw get q) (omW w)
        (s.loc.psiSh.map OnBytes.Model.Reading.gl.val)
        (vecAt lay₀ (xW.1.l.get xW.2).1 (wTab cs arr xW w)) → MS.dot q s y w) :
    RowZeroOwed (tiedNumbers N₁ Ns)
      (tiedMeaning get Mg₁ (meaningSigS cs G arr smp₂ ms₂ decT₂ MS))
      ML (promSigS cs G smp₂ ms₂ stOf bookOf Pm₀) (besideL (fillZ p R fun q => (get q).2) X)
      (ocEnd get N₁ Mg₁ links (First.flatPlaces true links true))
      (pieceOf (heldZero (P := P × S₁ × St) (Cl := Cl) p) base ds back r) :=
  rowZeroOwed_layers cs G arr get smp₁ smp₂ ms₁ ms₂ decT₂ Pw wSeat Mg₁ MS stOf bookOf Pm₀ N₁ Ns
    links p R X ML t₁ t₂ base ds back r hr J hOc omega pins rows
    (dot_letter cs G arr get smp₁ smp₂ ms₁ ms₂ decT₂ Pw wSeat Mg₁ MS stOf bookOf Pm₀ N₁ Ns
      links p R X t₁ xW lay₀ omW J hS
      (hW_letter cs G arr get smp₁ ms₁ Pw wSeat Mg₁ N₁ links xW lay₀ J h3 hlay hsh hseat hB)
      hO hdot)

end VerifiableInference.OnPublicFiles.Last
