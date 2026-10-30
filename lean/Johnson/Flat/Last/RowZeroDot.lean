-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Flat/Last/RowZeroDot.lean: ROW 0's LINK dot, ASSEMBLED FROM ITS FOUR TIES INSIDE THE LAST
TABLE's PROMISE AT BORDER 0: what row 0 proves of (Dot)'s equation at ITS readers gives the shared
table's sentence dot wherever that sentence is (Dot)'s equation at the owner's readers: the row
weights gLaid Pw get q · a fixed reader omW of Omega · W's member's table under the plan's layout
(the shape of mgPoint's dot, Johnson/Desc/Sound/PointAtFilling.lean). Two theorems: a joining.

OBJECT, FIELD as in Johnson/Flat/Last/RowZeroAtSig.lean.
USER     the premise dot of rowZeroOwed_atPlaces (Johnson/Flat/Last/RowZeroAtPlaces.lean).
LETTERS  RowZeroAtJoint's; xW · lay₀ · omW: the shared table's filling's.

  started_first   inside the promise the first chain's last record hands on its end.
  dot_of_ties     **the link.** PAID HERE, INSIDE THE PROMISE: (Eval) is laid (the owner's
                  hEL_at_ocEnd at evalLaid_open_all) · the row weights' two readers (gLaid_is_gOfS)
                  · W's two readers (wTie, Johnson/Flat/Last/RowZeroWTie.lean; its premise "the
                  record hands on its end": started_first). LEFT: hS (Pw.lin = p.S) · hW (W sits:
                  the conclusion of the owner's hW_at_ocEnd, to the letter) · **hO (Omega's two
                  readers agree, inside the promise)** · hdot (the shared table's dot is no more
                  than that equation).
What is not claimed. hO IS NOT TO BE HAD FROM THE PROMISE AS IT STANDS: omegaTie
(Johnson/Desc/K14/Law/OmegaTie.lean) gives it from three tests on the shared chain's LAST RECORD
(sharedX · codY · omY at border 12), and the last table's promise at border 0 (onL,
Johnson/Desc/Last/BordersLast.lean) holds of that record Omega's "no collision" and fillZ's shape 0
alone: the three tests are to be laid into the shape at border 0 and earned at the last chain's
door. NO MEMBER. All that RowZeroAtJoint.lean does not claim. No soundness.

-/
import Johnson.Flat.Last.RowZeroAtPlaces
import Johnson.Flat.Last.RowZeroWeights
import Johnson.Flat.Last.RowZeroWTie

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
open VerifiableInference.Desc.Third (S₃ P₁₄ firstOfS startAtEnds start₃F)
open VerifiableInference.Desc.Third.Law
open VerifiableInference.Desc.K13 (Where)
open VerifiableInference.Desc.K13.Law (EvalAt EvalLaid laidOf laidOf_ok vecAt wSitsMore
  evalLaid_open_all)
open _root_.Desc.K14 (St)
open _root_.Desc.K14.Law (DotOmAt DotEq omegaOf gLaid WSits hEL_at_ocEnd)

/-- Inside "the record in front is the start's" the first chain's last record hands on its end. -/
theorem started_first {P S₁ Y : Type} {p : P₁₄} {fs : P × S₁ → First.S}
    {a : ((P × S₁ × St) × S₃) × Y} (h : Started p fs a) :
    (firstOfS (fs (a.1.1.1, a.1.1.2.1))).isSome := by
  obtain ⟨e, _, hs⟩ := h
  unfold startAtEnds start₃F at hs
  cases hf : firstOfS (fs (a.1.1.1, a.1.1.2.1)) with
  | none => rw [hf] at hs; cases hs
  | some f => rfl

/-- **Row 0's link dot, from its ties.** -/
theorem dot_of_ties {P S₁ P₀ Cells Tok Xi : Type} {Fr : Frame} (cs : OnBytes.Codes)
    (G : FileDescription Xi) (arr : ℕ → ℕ → ℕ) (get : P × S₁ → P₀ × First.S)
    (smp₁ : P₀ × First.S → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp)
    (smp₂ : St → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp)
    (ms₁ ms₂ : List Mem) (decT₁ : (ℕ → Option (ℕ × List UInt64)) → P₀ × First.S → Option Cells)
    (decT₂ : (ℕ → Option (ℕ × List UInt64)) → St → Option Cells) (Pw : Where) (wSeat : ℕ × ℕ)
    (matC : Cells → ℕ → ℕ → GE) (Mg₁ : Meaning P₀ (Wit Cells Tok MsgT))
    (MS : MeaningS St (P × S₁) (Wit Cells Tok MsgT)) (stOf : St → OnBytes.Statement)
    (bookOf : St → OnBytes.TreeBook) (Pm₀ : PromMeaning St) (N₁ : Numbers) (Ns : NumbersS)
    (links : List ModelPart) (p : P₁₄) (R : List Fmt.DeclaredRound) (t₁ : ℕ) (xW : Mem) (lay₀ : VectorLay)
    (omW : Wit Cells Tok MsgT → ℕ → GE) (hS : Pw.lin = p.S)
    (hW : ∀ q y D,
      ocEnd get N₁ (mg1W cs G arr smp₁ ms₁ decT₁ Pw wSeat matC Mg₁) links
        (First.flatPlaces true links true) q y →
      (get q).2.failed = none → laidOf Pw (get q).2 = some D →
      WSits (Cells := Cells) (Tok := Tok) cs arr xW lay₀ (fun q => (get q).2.st)
        (fun q w => tabAt (get q).2.st.codes arr (seatBy noFirst (get q).2.book) (get q).2.st w)
        q D)
    (hO : ∀ a w,
      onSig Fr cs G arr get smp₁ smp₂ ms₁ ms₂ decT₁ decT₂
        (mg1W cs G arr smp₁ ms₁ decT₁ Pw wSeat matC Mg₁) MS stOf bookOf Pm₀ N₁ Ns links
        (First.flatPlaces true links true) p R 0 a →
      ∀ y < p.S.matrixRows,
        omegaOf a.1.1.2.2.loc (linLayOmega a.1.1.2.2.st.codes p.S)
          (wordsShared arr t₁ a.1.1.2.2.st a.1.1.2.2.book w) y = omW w y)
    (hdot : ∀ q (s : St) y w,
      DotEq p.S.matrixRows p.S.kCol (gLaid Pw get q) (omW w)
        (s.loc.psiSh.map OnBytes.Model.Reading.gl.val)
        (vecAt lay₀ (xW.1.l.get xW.2).1 (wTab cs arr xW w)) → MS.dot q s y w) :
    ∀ a w,
      onSig Fr cs G arr get smp₁ smp₂ ms₁ ms₂ decT₁ decT₂
        (mg1W cs G arr smp₁ ms₁ decT₁ Pw wSeat matC Mg₁) MS stOf bookOf Pm₀ N₁ Ns links
        (First.flatPlaces true links true) p R 0 a →
      DotOmAt p.S (gOfS (get (a.1.1.1, a.1.1.2.1)).2) a.1.1.2.2
        (wordsShared arr t₁ a.1.1.2.2.st a.1.1.2.2.book w)
        (wvW arr p (fun q => (get q).2) (a.1.1.1, a.1.1.2.1) w) →
      MS.dot (a.1.1.1, a.1.1.2.1) a.1.1.2.2 (strsOf Fr a.2) w := by
  intro a w ha h
  have hL : EvalLaid Pw (get (a.1.1.1, a.1.1.2.1)).2 :=
    hEL_at_ocEnd cs G arr smp₁ ms₁ decT₁ _ _ Pw wSeat matC Mg₁ get N₁ links _
      (evalLaid_open_all (Mg₁.more.merge wSitsMore) links) _ _ ha.1 ha.2.1
  obtain ⟨D, hD, _⟩ := laidOf_ok hL
  exact hdot _ _ _ _ (dotEq_of_dotOmAt (gLaid_is_gOfS Pw get _ hL) (hO a w ha)
    (wTie cs arr xW lay₀ p Pw get hS _ D hL hD (hW _ _ D ha.1 ha.2.1 hD)
      (started_first (started_fillZ ha)) w) h)

end VerifiableInference.OnPublicFiles.Last
