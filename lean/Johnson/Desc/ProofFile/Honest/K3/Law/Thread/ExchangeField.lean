-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Law/Thread/ExchangeField.lean: the honest side of the kind "lookup"
(K3): THE ITEM "objects" AS A FIELD OF A FILLING OF THE TABLE OF JOINTS: formsT (the lookup on the
calls) and forms (the lookup on the digits), at every filling whose field HAS THE LIBRARY'S TEXT,
and at the honest letters over it. Theorems with proofs; no definition.

The library's one filling lays these two fields by a text that runs over the list of runs for which
an item's name stands (Johnson/Desc/Sound/BordersForms.lean, `meaningForms`; that its filling's
fields are that text is there by unfolding: Johnson/Desc/Sound/MgAll.lean). Here the text is a
premise: an equation on the field, at letters.

  `formsT_field`   CONDITIONAL ON the field's equation; the name "objects" stands for the runs
                   "objects" and "guests" of one piece; the sentence `formsTQ` at both: the field
                   at "objects"
  `forms_field`    the same for forms and `formsQ`; the text's test "this run's forms may name
                   what is ahead" rejects both runs
  `honest_formsT`, `honest_forms`   the honest letters turn neither field
  `text_formsT`, `text_forms`   INSTANCES OF THE TWO PREMISES ON THE FIELD: the library's own text
                   `meaningForms`, over every filling, by unfolding
  `formsT_at_text`, `forms_at_text`   the two theorems called there

Limits. No instance of the hypotheses on the sentences (h1, h2) is exhibited in this file.
Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.ExchangeForms
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.AtBorder
import Johnson.Desc.Sound.BordersForms

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Law.Exchange
open VerifiableInference.Desc (Strs)
open VerifiableInference.Desc.First (Meaning)
open VerifiableInference.Desc.K9 (Readers)
open VerifiableInference.Desc.Sound (formsQ formsTQ formsQA Stated MsgQ)
open ProofFile.Honest.FirstThread (honest)

local notation "FS" => VerifiableInference.Desc.First.S

variable {P Wt : Type}

/-- **CONDITIONAL ON the field's equation, the list of runs, and the sentence at both runs: the
field formsT at the name "objects".** Of the field's equation an instance stands below
(`text_formsT`); no instance of h1, h2 is exhibited in this file. -/
theorem formsT_field (Mg : Meaning P Wt) (runs : Nat → Nat → String → List (Nat × String))
    (Rd : Nat → Readers) (St : Stated) (own : Nat → List (Nat × Nat))
    (tabOf : Wt → Nat × Nat → MsgQ) (wt : Nat → P × FS → Strs → Wt → Prop)
    (hT : Mg.formsT = fun m k r a y w =>
      (∀ p ∈ runs m k r, formsTQ (Rd m) St (own m) p.1 p.2 a.2 (tabOf w)) ∧
        (r = "weights" → wt m a y w))
    (m pc piece : Nat) (hr : runs m pc "objects" = [(piece, "objects"), (piece, "guests")])
    (a : P × FS) (y : Strs) (v : Wt)
    (h1 : formsTQ (Rd m) St (own m) piece "objects" a.2 (tabOf v))
    (h2 : formsTQ (Rd m) St (own m) piece "guests" a.2 (tabOf v)) :
    Mg.formsT m pc "objects" a y v := by
  rw [hT]
  show (∀ p ∈ runs m pc "objects", formsTQ (Rd m) St (own m) p.1 p.2 a.2 (tabOf v)) ∧
    ("objects" = "weights" → wt m a y v)
  rw [hr]
  exact objects_itemT (Rd m) St (own m) piece a.2 (tabOf v) _ h1 h2

/-- **CONDITIONAL ON the field's equation, the list of runs, the text's test rejecting both runs,
and the sentence at both runs: the field forms at the name "objects".** Of the field's equation an
instance stands below (`text_forms`); no instance of h1, h2 is exhibited in this file. -/
theorem forms_field (Mg : Meaning P Wt) (runs : Nat → Nat → String → List (Nat × String))
    (Rd : Nat → Readers) (sent : Nat → Nat → List (Nat × Nat)) (own : Nat → List (Nat × Nat))
    (ah : Nat → String → Bool) (tabOf : Wt → Nat × Nat → MsgQ)
    (wt : Nat → P × FS → Strs → Wt → Prop)
    (hT : Mg.forms = fun m k r a y w =>
      (∀ p ∈ runs m k r,
        if ah p.1 p.2 = true then formsQA (sent m) (own m) (Rd m) p.1 p.2 a.2 (tabOf w)
        else formsQ (Rd m) (own m) p.1 p.2 a.2 (tabOf w)) ∧ (r = "weights" → wt m a y w))
    (m pc piece : Nat) (hr : runs m pc "objects" = [(piece, "objects"), (piece, "guests")])
    (ha1 : ah piece "objects" = false) (ha2 : ah piece "guests" = false) (a : P × FS) (y : Strs)
    (v : Wt) (h1 : formsQ (Rd m) (own m) piece "objects" a.2 (tabOf v))
    (h2 : formsQ (Rd m) (own m) piece "guests" a.2 (tabOf v)) :
    Mg.forms m pc "objects" a y v := by
  rw [hT]
  show (∀ p ∈ runs m pc "objects",
    if ah p.1 p.2 = true then formsQA (sent m) (own m) (Rd m) p.1 p.2 a.2 (tabOf v)
    else formsQ (Rd m) (own m) p.1 p.2 a.2 (tabOf v)) ∧ ("objects" = "weights" → wt m a y v)
  rw [hr]
  refine ⟨fun p hp => ?_, fun h => absurd h (by decide)⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · rw [if_neg (by rw [ha1]; decide)]
    exact h1
  · rw [if_neg (by rw [ha2]; decide)]
    exact h2

/-- The honest letters turn neither field. -/
theorem honest_formsT (Mg : Meaning P Wt) (ans : Nat → Nat → P × FS → Strs → Wt → Prop)
    (test : Nat → FS → Option String) : (honest Mg ans test).formsT = Mg.formsT := rfl

theorem honest_forms (Mg : Meaning P Wt) (ans : Nat → Nat → P × FS → Strs → Wt → Prop)
    (test : Nat → FS → Option String) : (honest Mg ans test).forms = Mg.forms := rfl

/-! ## The premise's form, held against the library's own text -/

section
open VerifiableInference.Desc (Wit)
open VerifiableInference.Desc.First (Numbers)
open VerifiableInference.Desc.Sound (meaningForms seatTab Mem MsgT)

variable {Pp Cells Tok : Type} (cs : OnBytes.Codes) (arr : Nat → Nat → Nat) (ms : List Mem)
  (Rd : Nat → Readers) (runs : Nat → Nat → String → List (Nat × String)) (St : Stated)
  (after : Nat → FS → Except String FS) (N : Numbers)
  (wt : Nat → Pp × FS → Strs → Wit Cells Tok MsgT → Prop) (rw' : Nat → FS → Bool)
  (ah : Nat → String → Bool) (Mg : Meaning Pp (Wit Cells Tok MsgT))

/-- **An instance of `formsT_field`'s premise on the field**: the library's own text that lays the
four fields on forms, over every filling: by unfolding. -/
theorem text_formsT :
    (meaningForms cs arr ms Rd runs St after N wt rw' ah Mg).formsT = fun m k r a y w =>
      (∀ p ∈ runs m k r, formsTQ (Rd m) St ((fun m => N.sent m 0) m) p.1 p.2 a.2
        (seatTab cs arr ms w)) ∧ (r = "weights" → wt m a y w) := rfl

/-- **An instance of `forms_field`'s premise on the field**: the same text: by unfolding. -/
theorem text_forms :
    (meaningForms cs arr ms Rd runs St after N wt rw' ah Mg).forms = fun m k r a y w =>
      (∀ p ∈ runs m k r,
        if ah p.1 p.2 = true then
          formsQA (N.sent m) (N.group m) (Rd m) p.1 p.2 a.2 (seatTab cs arr ms w)
        else formsQ (Rd m) (N.group m) p.1 p.2 a.2 (seatTab cs arr ms w)) ∧
        (r = "weights" → wt m a y w) := rfl

/-- So `formsT_field` can be called at that text. -/
theorem formsT_at_text (m pc piece : Nat)
    (hr : runs m pc "objects" = [(piece, "objects"), (piece, "guests")]) (a : Pp × FS) (y : Strs)
    (v : Wit Cells Tok MsgT)
    (h1 : formsTQ (Rd m) St (N.sent m 0) piece "objects" a.2 (seatTab cs arr ms v))
    (h2 : formsTQ (Rd m) St (N.sent m 0) piece "guests" a.2 (seatTab cs arr ms v)) :
    (meaningForms cs arr ms Rd runs St after N wt rw' ah Mg).formsT m pc "objects" a y v :=
  formsT_field _ runs Rd St (fun m => N.sent m 0) (seatTab cs arr ms) wt
    (text_formsT cs arr ms Rd runs St after N wt rw' ah Mg) m pc piece hr a y v h1 h2

/-- So `forms_field` can be called at that text. -/
theorem forms_at_text (m pc piece : Nat)
    (hr : runs m pc "objects" = [(piece, "objects"), (piece, "guests")])
    (ha1 : ah piece "objects" = false) (ha2 : ah piece "guests" = false) (a : Pp × FS) (y : Strs)
    (v : Wit Cells Tok MsgT)
    (h1 : formsQ (Rd m) (N.group m) piece "objects" a.2 (seatTab cs arr ms v))
    (h2 : formsQ (Rd m) (N.group m) piece "guests" a.2 (seatTab cs arr ms v)) :
    (meaningForms cs arr ms Rd runs St after N wt rw' ah Mg).forms m pc "objects" a y v :=
  forms_field _ runs Rd N.sent N.group ah (seatTab cs arr ms) wt
    (text_forms cs arr ms Rd runs St after N wt rw' ah Mg) m pc piece hr ha1 ha2 a y v h1 h2

end

#print axioms ProofFile.Honest.K3.Law.Exchange.formsT_field
#print axioms ProofFile.Honest.K3.Law.Exchange.forms_field
#print axioms ProofFile.Honest.K3.Law.Exchange.honest_formsT
#print axioms ProofFile.Honest.K3.Law.Exchange.honest_forms
#print axioms ProofFile.Honest.K3.Law.Exchange.text_formsT
#print axioms ProofFile.Honest.K3.Law.Exchange.text_forms
#print axioms ProofFile.Honest.K3.Law.Exchange.formsT_at_text
#print axioms ProofFile.Honest.K3.Law.Exchange.forms_at_text

end ProofFile.Honest.K3.Law.Exchange
