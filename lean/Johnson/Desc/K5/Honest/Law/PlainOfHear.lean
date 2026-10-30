-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K5/Honest/Law/PlainOfHear.lean: WHEREVER THE HEARING OF AN ATTENTION SEGMENT's OWN
ROUNDS RETURNS, THE START FORM OF EACH SUMCHECK THAT IT HAS HEARD NAMES NO ENTRY
(`K5Law.HeardPlain`, Johnson/Desc/First/Att/Claims/HeardPlain.lean). NO PREMISE ON THE LEDGER. On
the verifier's text alone.

Why. The library makes `HeardPlain` from the hearing's law (`hear_said`,
Johnson/Desc/First/Att/K5SaidAll.lean, then `heardPlain_of_said`), and that law asks that the arrays
of the ledger in front have their length (`Sized`). Of a state of which one knows only that the
chain's own sub-protocols reach it, that premise is not at hand. `HeardPlain` does not need it: what
the hearing keeps of a sumcheck has as its start the very form that the hearing's text hands that
sumcheck, whatever the ledger.

How. `sum_spec` (Johnson/Desc/First/Att/K5Shape.lean) and `MaskedSum.hear_spec`
(Johnson/Desc/Part/MaskedSumShape.lean) open a sumcheck's return; `hear_ran` (K5Shape.lean) opens
the hearing's, verb by verb. The forms handed are a slot, a batch of slots, or a constant: these
name no entry (`cov_slot`, `cov_ofConst`, Johnson/Desc/First/Att/Claims/Covered.lean; `cov_batched`,
Johnson/Desc/First/Att/K05RowsCov.lean; `noEnts_of_cov0`, HeardPlain.lean).

Main names:
  `sum_start`: what is heard of a sumcheck starts at the form that the sumcheck was handed.
  `units_start`: so at each softmax-table unit.
  `heardPlain_of_hear`: **the whole.**

Limits. One direction, from a return; that the hearing returns at any rounds is not shown here. It
says nothing of the ledger behind, of the slots that the forms name, or of any other field of what
was heard.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.First.Att.Claims.HeardPlain

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace H2K5.Honest
open OnBytes OnBytes.Model
open VerifiableInference.Desc.Part
open VerifiableInference.Desc.Part.MaskedSum (Var Ends)
open VerifiableInference.Desc.First.Att
open VerifiableInference.Desc.First.Att.P (Heard St UnitsRan hear hear_ran sum_spec cov_batched)
open K5Law (HeardPlain noEnts_of_cov0 cov_slot cov_ofConst)

/-- What is heard of a sumcheck starts at the form that the sumcheck was handed. Conditional: h: the
return. -/
theorem sum_start {C : Aff} {vs : List Var} {e : Ends} {hh : MaskedSum.Heard} {s s' : St}
    (h : P.sum C (.sum vs e) s = some (hh, s')) : hh.start = C := by
  obtain ⟨F, rs, lead⟩ := s
  obtain ⟨G, rs', lead'⟩ := s'
  obtain ⟨_, _, G1, f, a1, _⟩ := sum_spec h
  obtain ⟨_, T, R, _, _, b3, _⟩ := MaskedSum.hear_spec a1
  rw [b3]

/-- Each softmax-table unit's sumcheck starts at the slot six behind the unit's first.
Conditional: the units have run. -/
theorem units_start : ∀ (us : List (ℕ × ℕ)) (os : List (ℕ × MaskedSum.Heard)) (s s' : St),
    UnitsRan us os s s' → ∀ o ∈ os, o.2.start = Aff.slot (o.1 + 6)
  | [], [], _, _, _ => fun _ ho => by cases ho
  | _ :: us, o :: os, _, s', ⟨s1, ⟨_, _, h2⟩, h3⟩ => fun o' ho => by
    rcases List.mem_cons.1 ho with rfl | ho
    · exact sum_start h2
    · exact units_start us os s1 s' h3 o' ho
  | [], _ :: _, _, _, h => h.elim
  | _ :: _, [], _, _, h => h.elim

/-- **Wherever the hearing returns, no start form of a heard sumcheck names an entry.**
Conditional: hh: the return, from whatever ledger, rounds and lead. -/
theorem heardPlain_of_hear {x : Params.AttentionRounds} {s0 s' : St} {h : Heard}
    (hh : hear x s0 = some (h, s')) : HeardPlain h := by
  obtain ⟨sa, sb, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, pt, _, hb, _, _,
    _, h4, _, _, h7, h8, _, _, _, _, h12, _, h14, _, h16⟩ := (hear_ran hh).ran
  exact
    ⟨fun o ho => noEnts_of_cov0 (iU3 := 0) (K := 0) (by
        rw [units_start _ _ _ _ hb o ho]
        exact cov_slot _),
      noEnts_of_cov0 (iU3 := 0) (K := 0) (by rw [sum_start h4]; exact cov_slot _),
      noEnts_of_cov0 (iU3 := 0) (K := 0) (by rw [sum_start h7]; exact cov_slot _),
      noEnts_of_cov0 (iU3 := 0) (K := 0) (by rw [sum_start h8]; exact cov_slot _),
      noEnts_of_cov0 (iU3 := 0) (K := 0) (by rw [sum_start h12]; exact cov_batched _ _ _ _ _),
      noEnts_of_cov0 (iU3 := 0) (K := 0) (by rw [sum_start h14]; exact cov_batched _ _ _ _ _),
      noEnts_of_cov0 (iU3 := 0) (K := 0) (by rw [sum_start h16]; exact cov_ofConst _)⟩

end H2K5.Honest

#print axioms H2K5.Honest.sum_start
#print axioms H2K5.Honest.units_start
#print axioms H2K5.Honest.heardPlain_of_hear
