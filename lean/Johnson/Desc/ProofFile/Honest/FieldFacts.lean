-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/FieldFacts.lean: four small lemmas on the definition `FieldAt`
(Field.lean), general in all its parameters. They stand over Field.lean alone, so that any file can
name them.

  `FieldAt.opened_some`, `not_fieldAt_of_none`   it is false where no columns are handed
  `FieldAt.base_eq`   at the other six letters fixed it fixes `base`
  `fieldAt_nil`   with no declared rounds it says that the field is `base`

Limits.
  * `FieldAt.opened_some` says that the field is `some` list, not which.
  * That `FieldAt` holds at any state of a run is not said here: `fieldAt_nil` turns it, at no
    declared rounds, into an equation on the field, which somebody has to prove of a run's own
    start.
  * The lemmas prove no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Field

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc (OpenedColumn)

section
variable {W Y : Type} {chain firstTree skip : Nat} {decls : List Fmt.DeclaredRound}
  {base base' : List OpenedColumn} {m : Mid W Y} {E : Env}

theorem FieldAt.opened_some (h : FieldAt chain firstTree decls base skip m E) :
    ∃ cs, m.opened = some cs := by
  obtain ⟨cols, -, h⟩ := h
  exact ⟨_, h⟩

/-- Where no columns are handed it is false. -/
theorem not_fieldAt_of_none (hm : m.opened = none) :
    ¬ FieldAt chain firstTree decls base skip m E := by
  rintro ⟨cols, -, h⟩
  rw [hm] at h
  cases h

/-- At the other six letters fixed it fixes `base`. The pair (`decls`, `base`) is not fixed by the
state: with no declared rounds the whole field is a `base` (`fieldAt_nil`). -/
theorem FieldAt.base_eq (h : FieldAt chain firstTree decls base skip m E)
    (h' : FieldAt chain firstTree decls base' skip m E) : base = base' := by
  obtain ⟨cols, h1, h2⟩ := h
  obtain ⟨cols', h1', h2'⟩ := h'
  have e : cols = cols' := Except.ok.inj (h1.symm.trans h1')
  subst e
  exact List.append_cancel_right (Option.some.inj (h2.symm.trans h2'))

/-- With no declared rounds it says that the field is `base`. -/
theorem fieldAt_nil : FieldAt chain firstTree [] base skip m E ↔ m.opened = some base := by
  have e : readsOf chain firstTree E.stored E.tree [] (m.st.heard.drop skip) = [] := by
    simp [readsOf]
  constructor
  · rintro ⟨cols, h1, h2⟩
    rw [e] at h1
    have e' : ([] : List OpenedColumn) = cols := Except.ok.inj h1
    subst e'
    rw [h2, List.append_nil]
  · intro h
    refine ⟨[], ?_, ?_⟩
    · rw [e]
      rfl
    · rw [h, List.append_nil]

end

end ProofFile.Honest

#print axioms ProofFile.Honest.FieldAt.opened_some
#print axioms ProofFile.Honest.not_fieldAt_of_none
#print axioms ProofFile.Honest.FieldAt.base_eq
#print axioms ProofFile.Honest.fieldAt_nil
