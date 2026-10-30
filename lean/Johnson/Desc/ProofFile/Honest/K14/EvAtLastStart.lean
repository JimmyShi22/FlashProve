-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K14/EvAtLastStart.lean: kind K14, second part, the first member of the
proof file's last chain: the link from the item "ev" in front of that member to what the member's
law reads: every open row of the request's own group holds of the witness's words (`RowsHold`,
Johnson/Desc/Third/Law/Row0.lean). One definition; statements with their proofs.

What it is for. `second_exchangeS_atWords` and `second_exchangeS_atOpen` (SecondWords.lean of this
folder) take a premise hEv: where the form's test at border 0 says yes, the item "ev" gives
`RowsHold` at the words of the last chain's reader (`wordsLast`).

Which meaning of "ev". The library's filling `evI` (Johnson/Desc/Third/Law/Row0Ev.lean) says that
the one row (Eval) says its claim. hEv's only premise on the first chain's last state is the form's
test at border 0, and no clause of that test bounds the number of the own group's open rows: it says
only that there is one (`started_of_shape`, Johnson/Desc/Last/ShapeGives.lean). So hEv is not had
from `evI` by what its binder gives. It is shown here at the meaning `evAll`: every open row of the
own group at the first chain's last state holds of the words read through that state's own book.
That (Eval) is the group's one open row is a fact of states that a run reaches; `evAll_of_wRow`
takes it as the premise `EvalAlone` (Johnson/Desc/K13/Honest/EvalAlone.lean).

Main names.
  `evAll arr fs`: **the meaning.**
  `rowsHold_atWords`: the way back of the library's `ev_atWords`, for all open rows in place of the
    one: at a record that is the start's of what was handed, `evAll`'s sentence gives `RowsHold` at
    `wordsLast`'s words.
  `second_hEv`: **hEv, in the words of `second_exchangeS_atWords`**, from hMg: the meaning of "ev"
    is `evAll`, at every input. Mg, the items' meaning as a function of the input, is a variable: a
    thread's parameter, or the field from which a thread is made.
  `evAll_of_wRow`: `evAll` from `evI`'s sentence and `EvalAlone` at the first chain's last state.

Limits. hMg is a premise on Mg, which has no value here. NOTHING HERE SHOWS THAT THE ITEM "ev"
HOLDS: `second_hEv` starts from it. Who shows it at the last chain's start is not said here;
`evAll_of_wRow` says from what it follows. Under hMg the link is a change of reader, and it uses the
test's clause that the first chain's book fits: the start copies the first chain's statement, book
and own group's number, and through such a record a message has the words that it has through the
first chain's own reading. Where the form's test at border 0 is false `second_hEv` says nothing.

What is not claimed. None of these is one of the library's goals. Nothing on soundness, completeness
or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K14.SecondWords
import Johnson.Desc.Third.Law.Row0Ev
import Johnson.Desc.K13.Honest.EvalAlone

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K14
open VerifiableInference.Desc (Wit Strs)
open VerifiableInference.Desc.Sound (MsgT wordsFirst wordsLast)
open VerifiableInference.Desc.Third (S₃ P₁₄ firstOfS)
open VerifiableInference.Desc.Third.Law (RowsHold Started started_own words_first_at says_congr)
open VerifiableInference.Desc.Last (fillZ shapeAt_of_fill started_of_shape firstOfS_parts)
open VerifiableInference.Desc.Book (placed_of_fits)
open VerifiableInference.Desc.Shared (MeaningS)
open VerifiableInference.Desc.K13 (Where)
open VerifiableInference.Desc.K13.Law (linAt WRow)
open VerifiableInference.Desc.K13.Honest (EvalAlone allSay_of_wRow)
open OnBytes.Means (AllSay)
open Desc.K14 (St)

section
variable {P S₁ Cells Tok : Type}

/-- **The meaning of the item "ev"**: every open row of the request's own group, at the first
chain's last state, holds of the words read through that state's own book. -/
def evAll (arr : ℕ → ℕ → ℕ) (fs : P × S₁ → VerifiableInference.Desc.First.S) :
    P × S₁ → Strs → Wit Cells Tok MsgT → Prop :=
  fun q _ w => ∀ l G, linAt (fs q) = some l → (fs q).st.groups[l.own]? = some G →
    AllSay OnBytes.Model.Reading.gl (fs q).st G.rows.toList
      (wordsFirst arr (fs q).st (fs q).book w)

variable {arr : ℕ → ℕ → ℕ} {t₁ t₂ : ℕ} {p : P₁₄}
  {fs : P × S₁ → VerifiableInference.Desc.First.S}

/-- **At a record that is the start's of what was handed: if every open row of the own group at the
first chain's last state holds of that state's words, every open row of the own group in the record
holds of the last chain's words.** placed: every place of the first chain's last book names a tree
that is there. -/
theorem rowsHold_atWords {Y : Type} {a : ((P × S₁ × St) × S₃) × Y} (h : Started p fs a)
    (placed : ∀ (i : ℕ) (q : ℕ × ℕ), (fs (a.1.1.1, a.1.1.2.1)).book.place[i]? = some q →
      q.1 < (fs (a.1.1.1, a.1.1.2.1)).book.trees.size)
    (y : Strs) (w : Wit Cells Tok MsgT) (hv : evAll arr fs (a.1.1.1, a.1.1.2.1) y w) :
    RowsHold OnBytes.Model.Reading.gl a.1.2 (wordsLast arr t₁ t₂ a.1.2 w) := by
  obtain ⟨e1, e2, e3, l, hl, ho⟩ := started_own h
  intro G hG r hr
  have hS := hv l G hl (by rw [← e1, ← ho]; exact hG) r hr
  rw [← e1, ← e2] at hS
  exact (says_congr OnBytes.Model.Reading.gl a.1.2.st r _ _ fun o _ part i =>
    words_first_at arr t₁ t₂ a.1.2 (by rw [e2]; exact placed) e3 w o part i).2 hS

/-- **The meaning, from the one row and that it is alone**: where (Eval) is the own group's one open
row at the first chain's last state, and says its claim of that state's words. -/
theorem evAll_of_wRow (Pw : Where) (q : P × S₁) (y : Strs) (w : Wit Cells Tok MsgT)
    (hA : EvalAlone Pw (fs q)) (hR : WRow Pw (fs q) (wordsFirst arr (fs q).st (fs q).book w)) :
    evAll arr fs q y w :=
  allSay_of_wRow hA _ hR

end

/-- hMg is a premise on the meaning Mg. **The premise hEv of `second_exchangeS_atWords`**, where the
meaning of the item "ev" is `evAll`. -/
theorem second_hEv {In P S₁ Cells Tok : Type}
    (Mg : In → MeaningS St (P × S₁) (Wit Cells Tok MsgT)) (p : P₁₄) (R : List Fmt.DeclaredRound)
    (fs : P × S₁ → VerifiableInference.Desc.First.S) (arr : ℕ → ℕ → ℕ) (t₁ t₂ : ℕ)
    (hMg : ∀ inp, (Mg inp).ev = evAll arr fs) :
    ∀ inp a e s y v, (fillZ p R fs).shape 0 a e s = true → (Mg inp).ev a y v →
      RowsHold OnBytes.Model.Reading.gl s (wordsLast arr t₁ t₂ s v) := by
  intro inp a e s y v hs hv
  rw [hMg] at hv
  obtain ⟨f, o, hf, _, hs'⟩ := shapeAt_of_fill p R _ _ hs
  have H := (started_of_shape hs').2.1
  have hf' : firstOfS (fs (a.1, a.2)) = some f := hf
  refine rowsHold_atWords (a := (((a.1, a.2, e), s), ())) (started_of_fillZ hs)
    (fun i q hq => ?_) y v hv
  have hq' : (fs (a.1, a.2)).book.place[i]? = some q := hq
  rw [← (firstOfS_parts hf').2.1] at hq' ⊢
  exact placed_of_fits H.fits₁ i q hq'

end ProofFile.Honest.K14

#print axioms ProofFile.Honest.K14.evAll
#print axioms ProofFile.Honest.K14.rowsHold_atWords
#print axioms ProofFile.Honest.K14.evAll_of_wRow
#print axioms ProofFile.Honest.K14.second_hEv
