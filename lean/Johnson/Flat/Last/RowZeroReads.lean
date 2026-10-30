-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Flat/Last/RowZeroReads.lean: ROW 0's TWO PREMISES "READS BELOW" (hOc: the first chain's
last promise reads the oracles' strings below the piece's base · pins: so do the three pins) AT A
LETTER FOR THE FIRST TABLE's MEANING, BY CALLS. Two theorems.

Why. The table's files have them general in Mg₁ (Johnson/Desc/Sound/ReadsBelowEq.lean): from three
equations of fields (decodes · shown · noColl are the fillings by signature: each by rfl at the
composed meaning, not shown here) and JointSays' own first field (pin). Here these are
called, with endTests_all (Johnson/Desc/K13/Law/EndTestsAll.lean) for the test "sampled".

OBJECT, FIELD as in Johnson/Flat/Last/RowZeroAtSig.lean.
USER     the field row0 of the last chain's ledger. pins_letter is called in
         Johnson/Flat/Last/RowZeroOc.lean; no file of this tree calls rowZeroOwed_reads.

  pins_letter        PinsReadBelow at tiedMeaning get Mg₁ (meaningSigS …), from Mg₁.pin = the
                     filling by signature and three comparisons (the index masks', W's and
                     o_omega's trees lie below lo). THE CALLS: pin₁_col_eq · pinJT_col.
  rowZeroOwed_reads  **the debt**: rowZeroOwed_letter with hOc and pins so paid. IN THEIR PLACE:
                     hd · hsn · hn (the three equations) · hl₀ (the list of segments is lawful) ·
                     hI · hV (two comparisons; omega, the third, stood already).
What is not claimed. The three equations and J at the composed meaning: untried here. The
comparisons: facts on the public parameters' numbers. NO MEMBER. All that RowZeroLetter.lean does
not claim. No soundness.
J is JointFour (Johnson/Flat/Last/JointFour.lean): JointSays
(Johnson/Desc/Sound/PointAtLayers.lean) without its clause pileOne, which no law here spends and
which does not close at the composed meaning; the letter matC has left with it. JointSays.four
gives J to whoever has the five.

-/
import Johnson.Flat.Last.RowZeroLetter
import Johnson.Desc.K13.Law.EndTestsAll
import Johnson.Desc.Sound.ReadsBelowEq

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

open VerifiableInference.Desc.First (linksOk)
open VerifiableInference.Desc.K13.Law (endTests_all)

/-- **The three pins read the strings below lo, at a letter for the first table's meaning.** -/
theorem pins_letter {P S₁ P₀ Cells Tok Xi : Type} (cs : OnBytes.Codes) (G : FileDescription Xi)
    (arr : ℕ → ℕ → ℕ) (get : P × S₁ → P₀ × First.S)
    (smp₁ : P₀ × First.S → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp)
    (smp₂ : St → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp)
    (ms₁ ms₂ : List Mem) (decT₂ : (ℕ → Option (ℕ × List UInt64)) → St → Option Cells)
    (Mg₁ : Meaning P₀ (Wit Cells Tok MsgT)) (MS : MeaningS St (P × S₁) (Wit Cells Tok MsgT))
    (N₁ : Numbers) (Ns : NumbersS) (ML : MeaningL S₃ (Wit Cells Tok MsgT)) (lo : ℕ)
    (hp : Mg₁.pin = fun j t a y w => pinJT cs G arr smp₁ ms₁ j t a y w) (hI : N₁.index.1 < lo)
    (hV : N₁.w.1 < lo) (hO : (Ns.tenant .oOmega).1 < lo) :
    PinsReadBelow (S₃ := S₃) (tiedNumbers N₁ Ns)
      (tiedMeaning get Mg₁ (meaningSigS cs G arr smp₂ ms₂ decT₂ MS)) ML lo := by
  intro i hi q e s y y' w _ hc h
  rcases hi with rfl | rfl | rfl
  · exact pin₁_col_eq cs G arr smp₁ ms₁ Mg₁ hp get _ _ _ q y' y w
      (fun z => (hc _ z hI).symm) h
  · exact pin₁_col_eq cs G arr smp₁ ms₁ Mg₁ hp get _ _ _ q y' y w
      (fun z => (hc _ z hV).symm) h
  · exact pinJT_col cs G arr smp₂ ms₂ _ _ e y' y w (fun z => (hc _ z hO).symm) h

/-- **Row 0's debt at a letter for the first table's meaning, the two "reads below" paid by
calls.** -/
theorem rowZeroOwed_reads {Cl : Type} {P S₁ P₀ Cells Tok Xi : Type} {Fr : Frame}
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
    (decT₁ : (ℕ → Option (ℕ × List UInt64)) → P₀ × First.S → Option Cells)
    (hd : Mg₁.decodes = decodesOf decT₁) (hsn : Mg₁.shown = shownJT cs G ms₁)
    (hn : Mg₁.noColl = noCollJT cs G smp₁ ms₁) (hl₀ : linksOk links = true)
    (hI : N₁.index.1 < base) (hV : N₁.w.1 < base)
    (omega : (Ns.tenant .oOmega).1 < base)
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
  rowZeroOwed_letter cs G arr get smp₁ smp₂ ms₁ ms₂ decT₂ Pw wSeat Mg₁ MS stOf bookOf Pm₀ N₁ Ns
    links p R X ML t₁ t₂ base ds back r hr J
    (ocEnd_readsBelow_eq cs G smp₁ ms₁ decT₁ Mg₁ hd hsn hn get base N₁ links _
      (endTests_all links hl₀ base N₁ hI hV).1)
    omega (pins_letter cs G arr get smp₁ smp₂ ms₁ ms₂ decT₂ Mg₁ MS N₁ Ns ML base J.pin hI hV omega)
    rows xW lay₀ omW hS h3 hlay hsh hseat hB hO hdot

end VerifiableInference.OnPublicFiles.Last
