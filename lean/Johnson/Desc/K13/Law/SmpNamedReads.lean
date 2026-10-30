-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K13/Law/SmpNamedReads.lean: THE TWO PREMISES THAT KIND K13's TIES LAY ON THE SAMPLE's
READER (`SmpReads`, Johnson/Desc/K13/Law/SmpReads.lean; `SmpOld`, SmpEarlierMessages.lean), AT THE READER THAT
OTHER FILES NAME AS MEANT (`smpNamed cs seats`, Johnson/Desc/Sound/SmpNamed.lean: of the pair it
reads the statement alone: at the number that the list of seats gives the member's seat: that
message's first kept sample row, as a linear form, and its target). Statements with their proofs.
  `forms_of_sample`, `ans_of_sample`: the form and the target at a number hang on that message's
  sample rows alone.
  `smpReads_named`: **`SmpReads` holds of it.**
  `smpOld_named`: **`SmpOld N p ms` holds of it** where the list of seats gives the index masks'
  seat a number below the plan's count of messages in front of the place p (one test on the plan).
What is not claimed. That the composed filling lays that reader. The test on the plan. Nothing on
soundness.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.K13.Law.SmpReads
import Johnson.Desc.K13.Law.SmpEarlierMessages
import Johnson.Desc.Sound.SmpNamed

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K13.Law
open OnBytes OnBytes.Model OnBytes.Slice OnBytes.Maker
open VerifiableInference.Desc.First (S Numbers)
open VerifiableInference.Desc.Sound (Sending Mem SitsAt smpNamed smpNamed_stays numAt seatOf)

/-- One shape, mark, sample rows and pad at a number: one list of sample rows there. -/
theorem rows_of_sample {St St' : Statement} {o : ℕ} (h : sampleOf St' o = sampleOf St o) :
    (St'.oracles[o]?).map (·.sampleRows) = (St.oracles[o]?).map (·.sampleRows) := by
  have e := congrArg (Option.map fun t : OracleShape × Bool × Array OnBytes.Row ×
    List (OnBytes.Part × ℕ) => t.2.2.1) h
  unfold sampleOf at e
  simpa [Option.map_map, Function.comp_def] using e

theorem forms_of_sample (cs : Codes) (sh : OracleShape) {St St' : Statement} {o : ℕ}
    (h : sampleOf St' o = sampleOf St o) : K1.formsAt cs sh St' o = K1.formsAt cs sh St o := by
  have e := rows_of_sample h
  unfold K1.formsAt
  cases h1 : St.oracles[o]? with
  | none =>
    rw [h1, Option.map_none, Option.map_eq_none_iff] at e
    rw [e]
  | some a =>
    rw [h1, Option.map_some] at e
    obtain ⟨b, hb, eb⟩ := Option.map_eq_some_iff.1 e
    rw [hb]
    simp only [Option.bind_some, eb]

theorem ans_of_sample {St St' : Statement} {o : ℕ} (h : sampleOf St' o = sampleOf St o) :
    K1.ansAt St' o = K1.ansAt St o := by
  have e := rows_of_sample h
  unfold K1.ansAt
  cases h1 : St.oracles[o]? with
  | none =>
    rw [h1, Option.map_none, Option.map_eq_none_iff] at e
    rw [e]
  | some a =>
    rw [h1, Option.map_some] at e
    obtain ⟨b, hb, eb⟩ := Option.map_eq_some_iff.1 e
    rw [hb]
    simp only [Option.bind_some, eb]

section
variable {Pp : Type} (cs : Codes) (seats : List (ℕ × ℕ))

/-- **`SmpReads` holds of the named reader.** -/
theorem smpReads_named : SmpReads (Pp := Pp) (cs := cs) (smpNamed cs seats) :=
  fun x x' m _ _ h3 =>
    smpNamed_stays cs seats x x' m.1 m.2 (forms_of_sample cs _ (h3.2 _)) (ans_of_sample (h3.2 _))

/-- **`SmpOld` holds of it**, under one test on the plan. -/
theorem smpOld_named (N : Numbers) (p : Option Place) (ms : List Mem)
    (hn : seats.idxOf N.index < N.msgsAt p) :
    SmpOld (Pp := Pp) (cs := cs) N p ms (smpNamed cs seats) := by
  intro x x' m _ hs _ hb _ ho
  unfold First.bookAt at hb
  simp only [Bool.and_eq_true, beq_iff_eq] at hb
  have hs' : m.1.seat m.2 = N.index := hs
  have hnum : numAt seats ⟨m.1, m.2⟩ < x.2.st.oracles.size := by
    rw [hb.2]
    unfold numAt seatOf
    rw [hs']
    exact hn
  exact smpNamed_stays cs seats x x' m.1 m.2 (forms_of_sample cs _ (ho.2.1 _ hnum))
    (ans_of_sample (ho.2.1 _ hnum))

end

end VerifiableInference.Desc.K13.Law

#print axioms VerifiableInference.Desc.K13.Law.smpReads_named
#print axioms VerifiableInference.Desc.K13.Law.smpOld_named
