-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K14/DotAtLastStart.lean: kind K14, second part, the first member of
the proof file's last chain: the link from the item "dot" in front of that member to the semantic
(Dot) that the member's law reads (`DotSem`, Johnson/Desc/Third/Law/Row0Words.lean). Statements with
their proofs; no definition.

What it is for. `second_exchangeS_atWords` and `second_exchangeS_atOpen` (SecondWords.lean of this
folder) take a premise hDot: where the form's test at border 0 says yes, the item "dot" gives
`DotSem` at the library's readers of Omega and of W (`omWW`, `wvW`,
Johnson/Desc/Third/Law/Row0AtWords.lean). This file shows hDot where the item's meaning is the
library's filling `dotI` (Johnson/Desc/Third/Law/Row0DotOm.lean) at these readers: (Dot)'s equation
at the shared chain's last record, its own reading of the witness's words, and the row weights of
the first chain's last record.

Main names.
  `border_of_started`: the record that the last chain's start returns names a border.
  `dotSem_atWords`: the converse of the library's `dot_atWords`: at a record that is the start's of
    what was handed, `DotOmAt` at the shared record's own reading gives `DotSem` at the readers.
  `dotSem_of_dotI`: the same from the form's test at border 0 and `dotI`.
  `second_hDot`: **hDot, in the words of `second_exchangeS_atWords`**, from hMg: the meaning of
    "dot" is that filling, at every input. Mg, the items' meaning as a function of the input, is a
    variable: a thread's parameter, or the field from which a thread is made.

Limits. hMg is a premise on Mg, which has no value here. NOTHING HERE SHOWS THAT THE ITEM "dot"
HOLDS: the statements start from it. Who shows it at the last chain's start is not said here. Under
hMg the link is a change of form: the same equation, read once at the shared record and once at the
border that the start lays; what is used is that the start copies the shared point and the one
pending row's weights, and that the two records have one table of codes. Where the form's test at
border 0 is false the statements say nothing.

What is not claimed. None of these is one of the library's goals. Nothing on soundness, completeness
or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K14.SecondWords

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K14
open VerifiableInference.Desc (Wit Strs)
open VerifiableInference.Desc.Sound (MsgT wordsShared omegaWords)
open VerifiableInference.Desc.Third (S₃ P₁₄)
open VerifiableInference.Desc.Third.Law (DotSem Started started_inv border_atWords omWW wvW omOf
  gOfS dotI dotSem_of_dotOmAt start₃E_border_row)
open VerifiableInference.Desc.Last (fillZ)
open VerifiableInference.Desc.Shared (MeaningS)
open Desc.K14 (St)
open Desc.K14.Law (DotOmAt omegaOf)

section
variable {P S₁ Cells Tok : Type} {arr : ℕ → ℕ → ℕ} {t₁ : ℕ} {p : P₁₄}
  {fs : P × S₁ → VerifiableInference.Desc.First.S}

/-- The record that the last chain's start returns names a border. -/
theorem border_of_started {Y : Type} {a : ((P × S₁ × St) × S₃) × Y} (h : Started p fs a) :
    ∃ b, a.1.2.loc.border = some b := by
  obtain ⟨f, _, _, _, _, hs⟩ := started_inv h
  obtain ⟨r, _, hb⟩ := start₃E_border_row _ _ _ _ _ _ _ _ _ _ _ hs
  exact ⟨_, hb⟩

/-- **At a record that is the start's of what was handed: (Dot)'s equation at the shared record's
own reading of the words gives the semantic (Dot) at the library's readers of Omega and of W.** -/
theorem dotSem_atWords {Y : Type} {a : ((P × S₁ × St) × S₃) × Y} (h : Started p fs a)
    (w : Wit Cells Tok MsgT)
    (hd : DotOmAt p.S (gOfS (fs (a.1.1.1, a.1.1.2.1))) a.1.1.2.2
      (wordsShared arr t₁ a.1.1.2.2.st a.1.1.2.2.book w)
      (wvW arr p fs (a.1.1.1, a.1.1.2.1) w)) :
    DotSem OnBytes.Model.Reading.gl p (omWW arr t₁ p fs a.1.1)
      (wvW arr p fs (a.1.1.1, a.1.1.2.1)) a.1.2 w := by
  obtain ⟨hB, hc⟩ := border_atWords h
  obtain ⟨b, hb⟩ := border_of_started h
  have e : omWW (Cells := Cells) (Tok := Tok) arr t₁ p fs a.1.1 =
      omOf p.S a.1.1.2.2 (fun w => wordsShared arr t₁ a.1.1.2.2.st a.1.1.2.2.book w) := by
    unfold omWW omOf omegaWords omegaOf
    rw [← hc]
    rfl
  rw [e]
  exact dotSem_of_dotOmAt p _ _ a.1.2
    (fun w => wordsShared arr t₁ a.1.1.2.2.st a.1.1.2.2.book w) _ w hB b hb hd

/-- The same from the form's test at border 0 and the library's filling of "dot". -/
theorem dotSem_of_dotI {R : List Fmt.DeclaredRound} {a : P × S₁} {e : St} {s : S₃} (y : Strs)
    (v : Wit Cells Tok MsgT) (hs : (fillZ p R fs).shape 0 a e s = true)
    (hd : dotI p.S (fun q => gOfS (fs q)) (fun d w => wordsShared arr t₁ d.st d.book w)
      (fun q => wvW arr p fs q) a e y v) :
    DotSem OnBytes.Model.Reading.gl p (omWW arr t₁ p fs (a.1, a.2, e)) (wvW arr p fs a) s v :=
  dotSem_atWords (a := (((a.1, a.2, e), s), ())) (started_of_fillZ hs) v hd

end

/-- hMg is a premise on the meaning Mg. **The premise hDot of `second_exchangeS_atWords`**,
where the meaning of the item "dot" is the library's filling at the shared record's own
reading of the words, the first record's row weights and W's reader. -/
theorem second_hDot {In P S₁ Cells Tok : Type}
    (Mg : In → MeaningS St (P × S₁) (Wit Cells Tok MsgT)) (p : P₁₄) (R : List Fmt.DeclaredRound)
    (fs : P × S₁ → VerifiableInference.Desc.First.S) (arr : ℕ → ℕ → ℕ) (t₁ : ℕ)
    (hMg : ∀ inp, (Mg inp).dot = dotI p.S (fun q => gOfS (fs q))
      (fun d w => wordsShared arr t₁ d.st d.book w) (fun q => wvW arr p fs q)) :
    ∀ inp a e s y v, (fillZ p R fs).shape 0 a e s = true → (Mg inp).dot a e y v →
      DotSem OnBytes.Model.Reading.gl p (omWW arr t₁ p fs (a.1, a.2, e)) (wvW arr p fs a) s v := by
  intro inp a e s y v hs hd
  rw [hMg] at hd
  exact dotSem_of_dotI y v hs hd

end ProofFile.Honest.K14

#print axioms ProofFile.Honest.K14.border_of_started
#print axioms ProofFile.Honest.K14.dotSem_atWords
#print axioms ProofFile.Honest.K14.dotSem_of_dotI
#print axioms ProofFile.Honest.K14.second_hDot
