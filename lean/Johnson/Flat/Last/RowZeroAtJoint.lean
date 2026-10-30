-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Flat/Last/RowZeroAtJoint.lean: ROW 0's DEBT OF THE LAST CHAIN's LEDGER AT THE TABLE's
FILES' OWN FILLING OF THE FIRST TABLE's MEANING (mg1Joint, Johnson/Desc/Sound/JointFilling.lean),
the words' reader the one that the table's files name (wordsFirst arr s.st s.book w): hEL
IS PAID BY hEL_at_ocEnd OF THE SAME FILE, CALLED; the link ev is the identity. One abbreviation,
three theorems: a joining.

OBJECT   as in Johnson/Flat/Last/RowZeroAtSig.lean.
USER     the field row0 of LastLeft (Johnson/LLT25R/LastLedger.lean), at M₁ := mg1Joint ….
LETTERS  RowZeroAtSig's, with M₁ laid: wSeat · matC · Mg₁ are mg1Joint's own.
FIELD    leads3_last_chains_table (Johnson/Goal/Skeleton/ProofFile.lean), through row 0.

  mg1W                 mg1Joint at stOf₁ a := a.2.st and tabP₁ a w := wordsFirst's own table.
  sig_of_joint         meaningSig of mg1Joint is mg1Joint: by rfl (the structures' eta).
  dot_at_point         the link dot where the shared table's dot is (Dot)'s equation at a fixed
                       reader omW of Omega and a reader V of W (the shape of mgPoint's dot,
                       Johnson/Desc/Sound/PointAtFilling.lean): from dotEq_of_dotOmAt.
  rowZeroOwed_atJoint  **the debt.** LEFT: hr · sampled · omega · pins (the ledger's own four) · h2
                       (THE ONE TEST ON THE FIRST TABLE: Pub.evalLaid is open at the last border:
                       evalLaid_open, Johnson/Desc/K13/Law/LaidToEnd.lean, has it by the kernel at
                       both written lists: called in Johnson/Flat/Last/RowZeroAtLists.lean) · rows
                       · dot.
What is not claimed. NO MEMBER. All that RowZeroAtSig.lean does not claim. No soundness.

-/
import Johnson.Desc.Sound.JointFilling
import Johnson.Flat.Last.RowZeroAtSig

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
open VerifiableInference.Desc.First (ModelPart Item Meaning Numbers openSets start Pub pubSets)
open VerifiableInference.Desc.Third (S₃ P₁₄)
open VerifiableInference.Desc.Third.Law
open VerifiableInference.Desc.K13 (Where)
open VerifiableInference.Desc.K13.Law (EvalLaid WRow wSitsMore)
open _root_.Desc.K14 (St)
open _root_.Desc.K14.Law (DotOmAt DotEq omegaOf mg1Joint hEL_at_ocEnd)

section
variable {P S₁ P₀ Cells Tok Xi : Type} (cs : OnBytes.Codes)
  (G : FileDescription Xi) (arr : ℕ → ℕ → ℕ)
  (smp₁ : P₀ × First.S → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp)
  (ms₁ : List Mem) (decT₁ : (ℕ → Option (ℕ × List UInt64)) → P₀ × First.S → Option Cells)
  (Pw : Where) (wSeat : ℕ × ℕ) (matC : Cells → ℕ → ℕ → GE)
  (Mg₁ : Meaning P₀ (Wit Cells Tok MsgT))

/-- The first table's meaning as the table's files fill it, at the words' reader by the record's own
book. -/
abbrev mg1W : Meaning P₀ (Wit Cells Tok MsgT) :=
  mg1Joint cs G arr smp₁ ms₁ decT₁ (fun a => a.2.st)
    (fun a w => tabAt a.2.st.codes arr (seatBy noFirst a.2.book) a.2.st w) Pw wSeat matC Mg₁

/-- meaningSig of the table's files' filling is that filling. -/
theorem sig_of_joint :
    meaningSig cs G arr smp₁ ms₁ decT₁ (mg1W cs G arr smp₁ ms₁ decT₁ Pw wSeat matC Mg₁) =
      mg1W cs G arr smp₁ ms₁ decT₁ Pw wSeat matC Mg₁ := rfl

end

/-- The link dot, where the table's dot is (Dot)'s equation at other readers of Omega and of W. -/
theorem dot_at_point {S S' : LinShape} (hS : S' = S) {g g' : Nat → GE} {d : St} {m : Words GE}
    {V V' om' : Nat → GE} (hg : g' = g)
    (hO : ∀ y < S.matrixRows, omegaOf d.loc (linLayOmega d.st.codes S) m y = om' y)
    (hV : ∀ c < 2 ^ S.kCol, V c = V' c) (h : DotOmAt S g d m V) :
    DotEq S'.matrixRows S'.kCol g' om' (d.loc.psiSh.map OnBytes.Model.Reading.gl.val) V' := by
  subst hS
  exact dotEq_of_dotOmAt hg hO hV h

section
variable {P S₁ P₀ Cells Tok Xi : Type} {Fr : Frame} (cs : OnBytes.Codes)
  (G : FileDescription Xi) (arr : ℕ → ℕ → ℕ) (get : P × S₁ → P₀ × First.S)
  (smp₁ : P₀ × First.S → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp)
  (smp₂ : St → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp)
  (ms₁ ms₂ : List Mem) (decT₁ : (ℕ → Option (ℕ × List UInt64)) → P₀ × First.S → Option Cells)
  (decT₂ : (ℕ → Option (ℕ × List UInt64)) → St → Option Cells)
  (Pw : Where) (wSeat : ℕ × ℕ) (matC : Cells → ℕ → ℕ → GE)
  (Mg₁ : Meaning P₀ (Wit Cells Tok MsgT)) (MS : MeaningS St (P × S₁) (Wit Cells Tok MsgT))
  (stOf : St → OnBytes.Statement) (bookOf : St → OnBytes.TreeBook) (Pm₀ : PromMeaning St)
  (N₁ : Numbers) (Ns : NumbersS) (links : List ModelPart) (ps : List VerifiableInference.Desc.Place)
  (p : P₁₄) (R : List Fmt.DeclaredRound)

/-- **Row 0's debt at the table's files' own filling of the first table's meaning.** -/
theorem rowZeroOwed_atJoint {Cl : Type} (ML : MeaningL S₃ (Wit Cells Tok MsgT))
    (t₁ t₂ base : ℕ) (ds : List RDT) (back : List Fmt.RoundView)
    (r : Rest (ckP .two) Fr ((P × S₁ × St) × S₃) (Wit Cells Tok MsgT) ds)
    (hr : ∀ a τ w, r.ext a τ w = w)
    (sampled : sampledBelow base N₁ ((openSets links ps (start links))[ps.length]?.getD []) = true)
    (omega : (Ns.tenant .oOmega).1 < base)
    (pins : PinsReadBelow (S₃ := S₃) (tiedNumbers N₁ Ns)
      (tiedMeaning get (mg1W cs G arr smp₁ ms₁ decT₁ Pw wSeat matC Mg₁)
        (meaningSigS cs G arr smp₂ ms₂ decT₂ MS)) ML base)
    (h2 : Pub.evalLaid ∈ (pubSets (Mg₁.more.merge wSitsMore) links ps)[ps.length]?.getD [])
    (rows : ∀ b w,
      onSig Fr cs G arr get smp₁ smp₂ ms₁ ms₂ decT₁ decT₂
        (mg1W cs G arr smp₁ ms₁ decT₁ Pw wSeat matC Mg₁) MS stOf bookOf Pm₀ N₁ Ns links ps p R
        1 b →
      ML.rows b.1.2 w →
      ∃ t, VerifiableInference.Desc.K12.Seat.enterOwn b.1.2 = .ok t ∧
        ∀ i, OnBytes.Means.OpenSays OnBytes.Model.Reading.gl t.st t.g i
          (OnBytes.Means.wordsOn t.st
            (tabAt p.codes arr (seatBy (noLast t₁ t₂ b.1.2.loc.firstTree) b.1.2.book) t.st w)))
    (dot : ∀ a w,
      onSig Fr cs G arr get smp₁ smp₂ ms₁ ms₂ decT₁ decT₂
        (mg1W cs G arr smp₁ ms₁ decT₁ Pw wSeat matC Mg₁) MS stOf bookOf Pm₀ N₁ Ns links ps p R
        0 a →
      DotOmAt p.S (gOfS (get (a.1.1.1, a.1.1.2.1)).2) a.1.1.2.2
        (wordsShared arr t₁ a.1.1.2.2.st a.1.1.2.2.book w)
        (wvW arr p (fun q => (get q).2) (a.1.1.1, a.1.1.2.1) w) →
      MS.dot (a.1.1.1, a.1.1.2.1) a.1.1.2.2 (strsOf Fr a.2) w) :
    RowZeroOwed (tiedNumbers N₁ Ns)
      (tiedMeaning get (mg1W cs G arr smp₁ ms₁ decT₁ Pw wSeat matC Mg₁)
        (meaningSigS cs G arr smp₂ ms₂ decT₂ MS))
      ML (promSigS cs G smp₂ ms₂ stOf bookOf Pm₀) (fillZ p R fun q => (get q).2)
      (ocEnd get N₁ (mg1W cs G arr smp₁ ms₁ decT₁ Pw wSeat matC Mg₁) links ps)
      (pieceOf (heldZero (P := P × S₁ × St) (Cl := Cl) p) base ds back r) :=
  rowZeroOwed_atSig cs G arr get smp₁ smp₂ ms₁ ms₂ decT₁ decT₂
    (mg1W cs G arr smp₁ ms₁ decT₁ Pw wSeat matC Mg₁) MS stOf bookOf Pm₀ N₁ Ns links ps p R ML Pw
    t₁ t₂ base ds back r hr sampled omega pins
    (hEL_at_ocEnd cs G arr smp₁ ms₁ decT₁ _ _ Pw wSeat matC Mg₁ get N₁ links ps h2)
    rows (fun _ _ _ h => h) dot

end

end VerifiableInference.OnPublicFiles.Last
