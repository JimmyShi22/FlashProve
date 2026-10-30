-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Shell/AtOptions.lean: the commitment ID that the options of a whole call hold as read stands
right behind `-id` among the call's options.

The theorems on the exit code 0 (OnBytes/Shell/AtWholeId.lean, OnBytes/Tie/ZeroNamed.lean) speak of
the ID that the options as read hold. This file ties it to the arguments of the call.

Main theorems.
- `readOptions_id`: what `readOptions` returns holds the ID with which it began, or the options hold
  `-id` and, right behind it, the ID that is returned.
- `kindOf_whole`: the arguments that `kindOf` reads as a whole call are `verify`, five names and the
  options, which `readOptions` has read, beginning with no option set.
- `whole_id_named`: so the ID that the options as read hold stands among the call's options, behind
  the five names, right behind `-id`.

What is not claimed. That the pair of `-id` and the ID stands in the options once is not stated. By
the code, `readOptions` refuses a second `-id`, at an option's place or as another option's value;
that is no theorem. A name may itself be `-id`: the five names are not read as options.
`whole_id_named` follows from its two hypotheses, on what `kindOf` returns and on the ID in it: in a
statement that has both, it says openly what they fix of the arguments and adds no further fact.
That the ID has 64 hex digits is not stated here. Nothing on the `-id` of a call on one file alone.
Nothing on the other options. Nothing on capital and small letters: the ID is taken as it stands;
`Verify.idAsked` makes the small letters. That the caller took the ID from where the commitment is
published is the caller's matter. The arguments are those that the entry function is given; nothing
on how a shell forms them. The program is the Lean text `verify-on-bytes`; nothing here is said of
the C++ program `cp_verify` or of how its results compare. For proofs only; the program does not
import this file.
-/
import OnBytes.Shell.Call

set_option autoImplicit false

namespace OnBytes.Shell

/-- What the reader of the options returns holds the ID with which it began, or the options hold
`-id` and, right behind it, the ID that is returned. That the pair stands in the options once is not
stated; by the code, `readOptions` refuses a second `-id`, which is no theorem. -/
theorem readOptions_id (opts : List String) (a0 a : Asked) :
    readOptions opts a0 = .ok a →
      a.options.id = a0.options.id ∨
        ∃ pre post x, opts = pre ++ "-id" :: x :: post ∧ a.options.id = some x := by
  fun_induction readOptions opts a0 <;> intro h <;>
  first
    | (cases h; done)
    | (cases h; exact Or.inl rfl)
    | (rename_i ih
       rcases ih h with e | ⟨pre, post, x, e1, e2⟩
       · first
           | exact Or.inl e
           | exact Or.inr ⟨[], _, _, rfl, e⟩
       · first
           | exact Or.inr ⟨_ :: pre, post, x, by rw [e1]; rfl, e2⟩
           | exact Or.inr ⟨_ :: _ :: pre, post, x, by rw [e1]; rfl, e2⟩)

/-- What `toyKind` returns, on any bits and any arguments, is never a whole call. -/
theorem toyKind_not_whole (bits : Nat) (front : List String) {config ivk request y proof : String}
    {a : Asked} : toyKind bits front ≠ .whole config ivk request y proof a := by
  intro h
  unfold toyKind at h
  split at h <;> cases h

/-- The arguments of a whole call: `verify`, five names, and the options, which `readOptions` has
read, beginning with no option set. -/
theorem kindOf_whole {args : List String} {config ivk request y proof : String} {a : Asked}
    (h : kindOf args = .whole config ivk request y proof a) :
    ∃ options, args = "verify" :: config :: ivk :: request :: y :: proof :: options ∧
      readOptions options {} = .ok a := by
  unfold kindOf at h
  split at h
  · split at h <;> cases h
  · split at h <;> cases h
  · split at h
    · cases h
    · rename_i hr
      cases h
      exact ⟨_, rfl, hr⟩
  · cases h
  · split at h <;> cases h
  · split at h
    · exact absurd h (toyKind_not_whole _ _)
    · cases h

/-- The ID that the options of a whole call hold as read stands among the call's options: the
arguments are `verify`, the five names, and options that hold `-id` and, right behind it, that ID.
That the pair stands in the options once is not stated; by the code, `readOptions` refuses a second
`-id`, which is no theorem. -/
theorem whole_id_named {args : List String} {config ivk request y proof id : String} {a : Asked}
    (hk : kindOf args = .whole config ivk request y proof a) (hi : a.options.id = some id) :
    ∃ pre post, args =
      "verify" :: config :: ivk :: request :: y :: proof :: (pre ++ "-id" :: id :: post) := by
  obtain ⟨options, e, hr⟩ := kindOf_whole hk
  rcases readOptions_id options {} a hr with h0 | ⟨pre, post, x, e1, e2⟩
  · rw [hi] at h0
    cases h0
  · rw [hi] at e2
    cases e2
    exact ⟨pre, post, by rw [e, e1]⟩

end OnBytes.Shell

#print axioms OnBytes.Shell.readOptions_id
#print axioms OnBytes.Shell.whole_id_named
#print axioms OnBytes.Shell.kindOf_whole
