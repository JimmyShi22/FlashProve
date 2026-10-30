-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Flat/Last/RowZeroWSits.lean: "W SITS" AT THE RULED READER (wordsFirst: the record's own
codes; the seat by the record's book through the tree's number), INSIDE THE FIRST CHAIN's LAST
PROMISE: the premise hW of dot_of_ties | dot_beside | rowZeroOwed_ties, BY CALLS. One definition,
statements with their proofs.

Why. The table's owner's hW_at_ocEnd (Johnson/Desc/Sound/AtOcEnd.lean) gives WSits at any reader
tabP that meets hbook: "at the book's place (j, t) and the statement's shape sh the table is w.tab
cs sh (arr j t) j t", asked at every handed part with no promise in front. The ruled reader meets
that only where the record's codes are the plan's and the book is in order. So: the owner's law is
called at a reader BY PLACE, which meets hbook by its make; and inside the promise the two readers
are one at W's number: the codes by WSits' own clause; the seat by
seatFirst_place (Johnson/Desc/Sound/SeamAt.lean).

OBJECT, FIELD as in Johnson/Flat/Last/RowZeroAtSig.lean.
USER     hW of rowZeroOwed_ties (Johnson/Flat/Last/RowZeroBeside.lean).
         rowZeroOwed_sits is called in Johnson/Flat/Last/RowZeroOmega.lean.

  tabByPlace         the reader by the book's place, at the plan's codes.
  tabByPlace_book    it meets hbook.
  hW_at_words        **hW, to the letter.** LEFT: hA (Mg₁'s door's row at the seal does not drop
                     "K13.wSits") · hlay · hsh · hseat (three equations on the plan: the owner's) ·
                     hB: inside the promise the book is numbered from 0 (NumberedBook 0), fits
                     (BookFits), and every message of the statement has a place in it.
  rowZeroOwed_sits   **row 0's debt at the layer**: rowZeroOwed_ties with hW so paid.
What is not claimed. hB IS A PREMISE: its first half is the public item "K12.bookInOrder" at ft := 0
(numbers_of_book0, Johnson/Desc/K12/Door/DoorGives.lean): in the composed filling, not in mg1Joint;
its earning along the chain: descPure_bookOrd. NO MEMBER. No soundness.

-/
import Johnson.Flat.Last.RowZeroBeside
import Johnson.Desc.Sound.SeamAt

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

/-- The reader by the book's place, at the plan's codes. -/
def tabByPlace {Cells Tok : Type} (cs : OnBytes.Codes) (arr : ℕ → ℕ → ℕ) (s : First.S)
    (w : Wit Cells Tok MsgT) (n : ℕ) : MsgT :=
  match s.book.place[n]?, s.st.oracles[n]? with
  | some q, some x => w.tab cs x.shape (arr q.1 q.2) q.1 q.2
  | _, _ => fun _ _ _ => 0

/-- It meets the owner's condition on a reader, at every record. -/
theorem tabByPlace_book {Cells Tok : Type} (cs : OnBytes.Codes) (arr : ℕ → ℕ → ℕ) (s : First.S)
    (w : Wit Cells Tok MsgT) (n j t : ℕ) (sh : OracleShape) (hp : s.book.place[n]? = some (j, t))
    (hs : (s.st.oracles[n]?).map (·.shape) = some sh) :
    tabByPlace cs arr s w n = w.tab cs sh (arr j t) j t := by
  obtain ⟨x, hx, rfl⟩ := Option.map_eq_some_iff.1 hs
  unfold tabByPlace
  rw [hp, hx]

/-- **"W sits" at the ruled reader, inside the first chain's last promise.** -/
theorem hW_at_words {P S₁ P₀ Cells Tok Xi : Type} (cs : OnBytes.Codes) (G : FileDescription Xi)
    (arr : ℕ → ℕ → ℕ) (get : P × S₁ → P₀ × First.S)
    (smp₁ : P₀ × First.S → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp)
    (ms₁ : List Mem) (decT₁ : (ℕ → Option (ℕ × List UInt64)) → P₀ × First.S → Option Cells)
    (Pw : Where) (wSeat : ℕ × ℕ) (matC : Cells → ℕ → ℕ → GE)
    (Mg₁ : Meaning P₀ (Wit Cells Tok MsgT)) (N₁ : Numbers) (links : List ModelPart) (xW : Mem)
    (lay₀ : VectorLay)
    (hA : ((none, "K13.wSits") : First.MoreName) ∉ (Mg₁.more.rows links placeSeal).drops)
    (hlay : lay₀ = linLayW cs Pw.lin) (hsh : Pw.lin.w = (xW.1.l.get xW.2).1)
    (hseat : xW.1.seat xW.2 = wSeat)
    (hB : ∀ q y,
      ocEnd get N₁ (mg1W cs G arr smp₁ ms₁ decT₁ Pw wSeat matC Mg₁) links
        (First.flatPlaces true links true) q y →
      (get q).2.failed = none →
      NumberedBook 0 (get q).2.book ∧ BookFits (get q).2.book ∧
        ∀ o, o < (get q).2.st.oracles.size → ∃ r : ℕ × ℕ, (get q).2.book.place[o]? = some r) :
    ∀ q y D,
      ocEnd get N₁ (mg1W cs G arr smp₁ ms₁ decT₁ Pw wSeat matC Mg₁) links
        (First.flatPlaces true links true) q y →
      (get q).2.failed = none → laidOf Pw (get q).2 = some D →
      WSits (Cells := Cells) (Tok := Tok) cs arr xW lay₀ (fun q => (get q).2.st)
        (fun q w => tabAt (get q).2.st.codes arr (seatBy noFirst (get q).2.book) (get q).2.st w)
        q D := by
  intro q y D ho hm hD
  have W := hW_at_ocEnd cs G arr smp₁ ms₁ decT₁ _ _ Pw wSeat matC Mg₁ get N₁ links _ xW lay₀
    (fun q => (get q).2.st) (fun q w => tabByPlace cs arr (get q).2 w)
    (wSits_open_all Mg₁.more links hA) (fun _ => rfl) hlay
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

/-- **Row 0's debt at the layer, "W sits" paid by calls.** -/
theorem rowZeroOwed_sits {Cl : Type} {P S₁ P₀ Cells Tok Xi : Type} {Fr : Frame} (cs : OnBytes.Codes)
    (G : FileDescription Xi) (arr : ℕ → ℕ → ℕ) (get : P × S₁ → P₀ × First.S)
    (smp₁ : P₀ × First.S → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp)
    (smp₂ : St → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp)
    (ms₁ ms₂ : List Mem) (decT₁ : (ℕ → Option (ℕ × List UInt64)) → P₀ × First.S → Option Cells)
    (decT₂ : (ℕ → Option (ℕ × List UInt64)) → St → Option Cells) (Pw : Where) (wSeat : ℕ × ℕ)
    (matC : Cells → ℕ → ℕ → GE) (Mg₁ : Meaning P₀ (Wit Cells Tok MsgT))
    (MS : MeaningS St (P × S₁) (Wit Cells Tok MsgT)) (stOf : St → OnBytes.Statement)
    (bookOf : St → OnBytes.TreeBook) (Pm₀ : PromMeaning St) (N₁ : Numbers) (Ns : NumbersS)
    (links : List ModelPart) (p : P₁₄) (R : List Fmt.DeclaredRound) (X : St → Bool)
    (ML : MeaningL S₃ (Wit Cells Tok MsgT)) (t₁ t₂ base : ℕ) (ds : List RDT) (back : List Fmt.RoundView)
    (r : Rest (ckP .two) Fr ((P × S₁ × St) × S₃) (Wit Cells Tok MsgT) ds)
    (hr : ∀ a τ w, r.ext a τ w = w)
    (sampled : sampledBelow base N₁ ((openSets links (First.flatPlaces true links true)
      (start links))[(First.flatPlaces true links true).length]?.getD []) = true)
    (omega : (Ns.tenant .oOmega).1 < base)
    (pins : PinsReadBelow (S₃ := S₃) (tiedNumbers N₁ Ns)
      (tiedMeaning get (mg1W cs G arr smp₁ ms₁ decT₁ Pw wSeat matC Mg₁)
        (meaningSigS cs G arr smp₂ ms₂ decT₂ MS)) ML base)
    (rows : ∀ b w,
      onSigX Fr cs G arr get smp₁ smp₂ ms₁ ms₂ decT₁ decT₂ Pw wSeat matC Mg₁ MS stOf bookOf Pm₀ N₁
        Ns links p R X 1 b →
      ML.rows b.1.2 w →
      ∃ t, VerifiableInference.Desc.K12.Seat.enterOwn b.1.2 = .ok t ∧
        ∀ i, OnBytes.Means.OpenSays OnBytes.Model.Reading.gl t.st t.g i
          (OnBytes.Means.wordsOn t.st
            (tabAt p.codes arr (seatBy (noLast t₁ t₂ b.1.2.loc.firstTree) b.1.2.book) t.st w)))
    (xW : Mem) (lay₀ : VectorLay) (omW : Wit Cells Tok MsgT → ℕ → GE) (hS : Pw.lin = p.S)
    (hA : ((none, "K13.wSits") : First.MoreName) ∉ (Mg₁.more.rows links placeSeal).drops)
    (hlay : lay₀ = linLayW cs Pw.lin) (hsh : Pw.lin.w = (xW.1.l.get xW.2).1)
    (hseat : xW.1.seat xW.2 = wSeat)
    (hB : ∀ q y,
      ocEnd get N₁ (mg1W cs G arr smp₁ ms₁ decT₁ Pw wSeat matC Mg₁) links
        (First.flatPlaces true links true) q y →
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
      (tiedMeaning get (mg1W cs G arr smp₁ ms₁ decT₁ Pw wSeat matC Mg₁)
        (meaningSigS cs G arr smp₂ ms₂ decT₂ MS))
      ML (promSigS cs G smp₂ ms₂ stOf bookOf Pm₀) (besideL (fillZ p R fun q => (get q).2) X)
      (ocEnd get N₁ (mg1W cs G arr smp₁ ms₁ decT₁ Pw wSeat matC Mg₁) links
        (First.flatPlaces true links true))
      (pieceOf (heldZero (P := P × S₁ × St) (Cl := Cl) p) base ds back r) :=
  rowZeroOwed_ties cs G arr get smp₁ smp₂ ms₁ ms₂ decT₁ decT₂ Pw wSeat matC Mg₁ MS stOf bookOf Pm₀
    N₁ Ns links p R X ML t₁ t₂ base ds back r hr sampled omega pins rows xW lay₀ omW hS
    (hW_at_words cs G arr get smp₁ ms₁ decT₁ Pw wSeat matC Mg₁ N₁ links xW lay₀ hA hlay hsh hseat
      hB) hO hdot

end VerifiableInference.OnPublicFiles.Last
