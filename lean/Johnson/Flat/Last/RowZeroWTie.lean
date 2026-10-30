-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Flat/Last/RowZeroWTie.lean: W's TWO READERS AGREE, WHERE (Eval) IS LAID, W SITS AND THE
FIRST CHAIN's LAST RECORD HANDS ON W's NUMBER. One definition of a proposition, two theorems.

OBJECT   wvW (Johnson/Desc/Third/Law/Row0AtWords.lean) · vecAt of W's member's table.
USER     the premise hV of dot_at_point (Johnson/Flat/Last/RowZeroAtJoint.lean), for row 0's dot.
FIELD    leads3_last_chains_table (Johnson/Goal/Skeleton/ProofFile.lean), through row 0.
LETTERS  cs, arr, xW, lay₀ (the plan's codes, the file's map from a seat to a message's number, W's
         member, W's layout by the plan) · p, Pw · get : what was handed → the first chain's last
         record.

  WTie            the statement.
  w₁Of_of_first   where firstOfS gives a record, w₁Of is the number of W that linAt's record names.
  wTie            **the statement holds**: the right side by hvec_paid
                  (Johnson/HB/PointStepBack.lean), CALLED at the fence "it is q"; the left side by
                  unfolding; W's number by w₁Of_of_first; W's layout by laidOf_ok
                  (Johnson/Desc/K13/Law/LaidAt.lean).

THE PREMISE «(firstOfS (get q).2).isSome». Without it the statement is false: both readers take W's
number off one field (the record's lin, its w), but firstOfS goes through S.firstEnd?
(Johnson/Desc/First/State.lean:760), which gives none where W's number is noId (2 ^ 32 - 1,
OnBytes/Iop/Ground.lean:71): there w₁Of falls back on 0, while linAt still names 2 ^ 32 - 1, and
EvalLaid and WSits ask of W's number only that it is below the count of the statement's messages. At
the user's place the premise is had: Started p fs a gives firstOfS (fs q) = some f.
What is not claimed. NO MEMBER: that a record has EvalLaid, WSits or the premise is shown here of no
record. The counter-case above is on paper, not through Lean. No soundness; nothing on hiding.

-/
import Johnson.Desc.Sound.AtOcEnd
import Johnson.Desc.Third.Law.Row0Ev

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.OnPublicFiles.Last
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Maker
open OnBytes.Means (wordsOn)
open VerifiableInference.Desc VerifiableInference.Desc.Sound
open VerifiableInference.Desc.Third (P₁₄ firstOfS)
open VerifiableInference.Desc.Third.Law (wvW linAt_of_firstEnd)
open VerifiableInference.Desc.K13 (Where)
open VerifiableInference.Desc.K13.Law (EvalAt EvalLaid laidOf laidOf_ok linAt vecAt)
open _root_.Desc.K14.Law (WSits hvec_paid)

/-- **(A4), THE STATEMENT.** Row 0's reader of W (wvW: the words at the first chain's last record's
own number of W, under W's layout at the record's codes) is the shared table's (vecAt of W's
member's table under the plan's layout), below 2 ^ kCol. -/
def WTie {P S₁ P₀ Cells Tok : Type} (cs : OnBytes.Codes) (arr : ℕ → ℕ → ℕ) (xW : Mem)
    (lay₀ : VectorLay) (p : P₁₄) (Pw : Where) (get : P × S₁ → P₀ × First.S) : Prop :=
  Pw.lin = p.S → ∀ (q : P × S₁) (D : EvalAt), EvalLaid Pw (get q).2 →
    laidOf Pw (get q).2 = some D →
    WSits (Cells := Cells) (Tok := Tok) cs arr xW lay₀ (fun q => (get q).2.st)
      (fun q w => tabAt (get q).2.st.codes arr (seatBy noFirst (get q).2.book) (get q).2.st w) q D →
    (firstOfS (get q).2).isSome →
    ∀ (w : Wit Cells Tok MsgT), ∀ c < 2 ^ p.S.kCol,
      wvW arr p (fun q => (get q).2) q w c = vecAt lay₀ (xW.1.l.get xW.2).1 (wTab cs arr xW w) c

/-- Where the first chain's last record hands on W's number, it is the number that K13's law
reads. -/
theorem w₁Of_of_first {s : First.S} (h : (firstOfS s).isSome) {l : LinFirst}
    (hl : linAt s = some l) : Third.Law.w₁Of s = l.w := by
  cases hx : s.firstEnd? with
  | none =>
    unfold firstOfS at h
    rw [hx] at h
    cases h
  | some x =>
    have e := linAt_of_firstEnd s x hx
    rw [hl] at e
    obtain rfl := Option.some.inj e
    unfold Third.Law.w₁Of firstOfS
    rw [hx]
    rfl

/-- **(A4): W's two readers agree.** -/
theorem wTie {P S₁ P₀ Cells Tok : Type} (cs : OnBytes.Codes) (arr : ℕ → ℕ → ℕ) (xW : Mem)
    (lay₀ : VectorLay) (p : P₁₄) (Pw : Where) (get : P × S₁ → P₀ × First.S) :
    WTie (Cells := Cells) (Tok := Tok) cs arr xW lay₀ p Pw get := by
  intro hS q D hL hD hW hF w c hc
  obtain ⟨D', hD', hok, _, _, l, hlin, hw, hlay, _⟩ := laidOf_ok hL
  rw [hD] at hD'
  obtain rfl := Option.some.inj hD'
  have key := hvec_paid cs arr xW lay₀ Pw.lin (fun q => (get q).2.st)
    (fun q w => tabAt (get q).2.st.codes arr (seatBy noFirst (get q).2.book) (get q).2.st w)
    (fun q' _ => q' = q) (fun q => laidOf Pw (get q).2)
    (fun q' _ D' e h => by
      subst e
      obtain rfl := Option.some.inj (hD.symm.trans h)
      exact hok)
    (fun q' _ D' e h => by
      subst e
      obtain rfl := Option.some.inj (hD.symm.trans h)
      exact hW)
    q ⟨fun _ => none, fun _ _ => []⟩ D w rfl hD c (by rw [hS]; exact hc)
  rw [← key]
  show wordsOn (get q).2.st
      (tabAt (get q).2.st.codes arr (seatBy noFirst (get q).2.book) (get q).2.st w)
      (Third.Law.w₁Of (get q).2) .main ((linLayW (get q).2.st.codes p.S).index c) = _
  rw [w₁Of_of_first hF hlin, hw, hlay, hS]

end VerifiableInference.OnPublicFiles.Last
