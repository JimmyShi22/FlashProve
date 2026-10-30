-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Flat/Last/RowZeroAtLists.lean: ROW 0's DEBT OF THE LAST CHAIN's LEDGER AT THE TABLE's
FILES' OWN FILLING (Johnson/Flat/Last/RowZeroAtJoint.lean) AND AT THE TWO WRITTEN LISTS OF THE
FIRST TABLE: THE ONE TEST h2 ("(Eval) is laid" is open at the first chain's last border) IS PAID BY
THE KERNEL: evalLaid_open (Johnson/Desc/K13/Law/LaidToEnd.lean): CALLED. Two theorems: a joining.


OBJECT, USER, FIELD as in Johnson/Flat/Last/RowZeroAtSig.lean.
LETTERS  RowZeroAtJoint's, with links one of linksSmall | linksFull
         (Johnson/Desc/K13/Law/AtTableRow.lean) and ps := First.flatPlaces true links true.

  evalLaid_at_lists    h2 at either list, at a door M.merge wSitsMore with M = {}.
  rowZeroOwed_atLists  **the debt.** LEFT: hl (the list is one of the two) · hM (Mg₁'s own door is
                       empty) · hr · sampled · omega · pins (the ledger's own four) · rows · dot.
What is not claimed. NO MEMBER. That the two lists are a plan's, or a description's own places. At a
door into which other files' items are merged the test is to be run anew. All that
RowZeroAtJoint.lean does not claim. No soundness.

-/
import Johnson.Flat.Last.RowZeroAtJoint
import Johnson.Desc.K13.Law.LaidToEnd

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
open VerifiableInference.Desc.First (ModelPart Item Meaning Numbers openSets start Pub pubSets More)
open VerifiableInference.Desc.Third (S₃ P₁₄)
open VerifiableInference.Desc.Third.Law
open VerifiableInference.Desc.K13 (Where)
open VerifiableInference.Desc.K13.Law (wSitsMore linksSmall linksFull evalLaid_open)
open _root_.Desc.K14 (St)
open _root_.Desc.K14.Law (DotOmAt)

/-- The one test on the first table, at either written list. -/
theorem evalLaid_at_lists (M : More) (hM : M = {}) (links : List ModelPart)
    (hl : links = linksSmall ∨ links = linksFull) :
    Pub.evalLaid ∈ (pubSets (M.merge wSitsMore) links (First.flatPlaces true links
      true))[(First.flatPlaces true links true).length]?.getD [] := by
  subst hM
  rcases hl with rfl | rfl
  · exact evalLaid_open.2.2.1
  · exact evalLaid_open.2.2.2

/-- **Row 0's debt at the table's files' own filling and at the two written lists.** -/
theorem rowZeroOwed_atLists {P S₁ P₀ Cells Tok Xi Cl : Type} {Fr : Frame} (cs : OnBytes.Codes)
    (G : FileDescription Xi) (arr : ℕ → ℕ → ℕ) (get : P × S₁ → P₀ × First.S)
    (smp₁ : P₀ × First.S → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp)
    (smp₂ : St → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp)
    (ms₁ ms₂ : List Mem) (decT₁ : (ℕ → Option (ℕ × List UInt64)) → P₀ × First.S → Option Cells)
    (decT₂ : (ℕ → Option (ℕ × List UInt64)) → St → Option Cells) (Pw : Where) (wSeat : ℕ × ℕ)
    (matC : Cells → ℕ → ℕ → GE) (Mg₁ : Meaning P₀ (Wit Cells Tok MsgT))
    (MS : MeaningS St (P × S₁) (Wit Cells Tok MsgT)) (stOf : St → OnBytes.Statement)
    (bookOf : St → OnBytes.TreeBook) (Pm₀ : PromMeaning St) (N₁ : Numbers) (Ns : NumbersS)
    (links : List ModelPart) (hl : links = linksSmall ∨ links = linksFull) (hM : Mg₁.more = {})
    (p : P₁₄) (R : List Fmt.DeclaredRound) (ML : MeaningL S₃ (Wit Cells Tok MsgT)) (t₁ t₂ base : ℕ)
    (ds : List RDT) (back : List Fmt.RoundView)
    (r : Rest (ckP .two) Fr ((P × S₁ × St) × S₃) (Wit Cells Tok MsgT) ds)
    (hr : ∀ a τ w, r.ext a τ w = w)
    (sampled : sampledBelow base N₁ ((openSets links (First.flatPlaces true links true)
      (start links))[(First.flatPlaces true links true).length]?.getD []) = true)
    (omega : (Ns.tenant .oOmega).1 < base)
    (pins : PinsReadBelow (S₃ := S₃) (tiedNumbers N₁ Ns)
      (tiedMeaning get (mg1W cs G arr smp₁ ms₁ decT₁ Pw wSeat matC Mg₁)
        (meaningSigS cs G arr smp₂ ms₂ decT₂ MS)) ML base)
    (rows : ∀ b w,
      onSig Fr cs G arr get smp₁ smp₂ ms₁ ms₂ decT₁ decT₂
        (mg1W cs G arr smp₁ ms₁ decT₁ Pw wSeat matC Mg₁) MS stOf bookOf Pm₀ N₁ Ns links
        (First.flatPlaces true links true) p R 1 b →
      ML.rows b.1.2 w →
      ∃ t, VerifiableInference.Desc.K12.Seat.enterOwn b.1.2 = .ok t ∧
        ∀ i, OnBytes.Means.OpenSays OnBytes.Model.Reading.gl t.st t.g i
          (OnBytes.Means.wordsOn t.st
            (tabAt p.codes arr (seatBy (noLast t₁ t₂ b.1.2.loc.firstTree) b.1.2.book) t.st w)))
    (dot : ∀ a w,
      onSig Fr cs G arr get smp₁ smp₂ ms₁ ms₂ decT₁ decT₂
        (mg1W cs G arr smp₁ ms₁ decT₁ Pw wSeat matC Mg₁) MS stOf bookOf Pm₀ N₁ Ns links
        (First.flatPlaces true links true) p R 0 a →
      DotOmAt p.S (gOfS (get (a.1.1.1, a.1.1.2.1)).2) a.1.1.2.2
        (wordsShared arr t₁ a.1.1.2.2.st a.1.1.2.2.book w)
        (wvW arr p (fun q => (get q).2) (a.1.1.1, a.1.1.2.1) w) →
      MS.dot (a.1.1.1, a.1.1.2.1) a.1.1.2.2 (strsOf Fr a.2) w) :
    RowZeroOwed (tiedNumbers N₁ Ns)
      (tiedMeaning get (mg1W cs G arr smp₁ ms₁ decT₁ Pw wSeat matC Mg₁)
        (meaningSigS cs G arr smp₂ ms₂ decT₂ MS))
      ML (promSigS cs G smp₂ ms₂ stOf bookOf Pm₀) (fillZ p R fun q => (get q).2)
      (ocEnd get N₁ (mg1W cs G arr smp₁ ms₁ decT₁ Pw wSeat matC Mg₁) links
        (First.flatPlaces true links true))
      (pieceOf (heldZero (P := P × S₁ × St) (Cl := Cl) p) base ds back r) :=
  rowZeroOwed_atJoint cs G arr get smp₁ smp₂ ms₁ ms₂ decT₁ decT₂ Pw wSeat matC Mg₁ MS stOf bookOf
    Pm₀ N₁ Ns links (First.flatPlaces true links true) p R ML t₁ t₂ base ds back r hr sampled omega
    pins (evalLaid_at_lists Mg₁.more hM links hl) rows dot

end VerifiableInference.OnPublicFiles.Last
