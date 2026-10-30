-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Run/TableOracle.lean: a lookup table of a function's own values, in front of that function on byte
strings. This is so that Lean's kernel can evaluate a run that asks a hash without unfolding the
hash inside the run.

Definitions that compute, with their laws. Generic: no format, no hash, no verifier. Imports
nothing.

Why: "this verifier accepts this file, with the real hash" is a closed statement, and the kernel
can decide it by evaluation. But in a run each answer of the hash enters the next query: left to
itself the kernel carries nested unevaluated hashes. So the strings that the run asks, with their
answers as literals, are laid down in a table; that each entry is the hash's value is shown entry
by entry (one hash at a time); the run is evaluated at the function that looks into the table
first; that function is the hash.

Main names:
  `mix O tab`: x ↦ the table's answer at x, if there is one; else O x. On a hit O x is not
    evaluated.
  `TabOK O tab`: every entry holds O's value; `tabOKb`: the same as a truth value, for evaluation;
    `tabOKb_iff`.
  `tabOK_nil`, `tabOK_cons`, `tabOK_append`, `tabOK_flatten`: a table has `TabOK` if its parts
    have: so the entries can be checked in parts that fit the kernel's memory.
  `mix_eq`: TabOK O tab → mix O tab = O.
  `of_mix`: P (mix O tab) → TabOK O tab → P O: the form in which a run's result is carried over.
A wrong or missing entry can make nothing false true: a wrong entry fails `TabOK`; a missing one
only sends the evaluation into O.

Limits: this file does not say which strings a run asks. It does not say anything on a hash.
-/

namespace Run

/-- The answer that the first entry with the string x holds; none if there is none. -/
def tabFind : List (ByteArray × ByteArray) → ByteArray → Option ByteArray
  | [], _ => none
  | e :: t, x => if e.1 = x then some e.2 else tabFind t x

/-- The table first, then the function. -/
def mix (O : ByteArray → ByteArray) (tab : List (ByteArray × ByteArray)) (x : ByteArray) :
    ByteArray :=
  match tabFind tab x with
  | some y => y
  | none => O x

/-- Every entry holds the function's value. -/
def TabOK (O : ByteArray → ByteArray) (tab : List (ByteArray × ByteArray)) : Prop :=
  ∀ e ∈ tab, O e.1 = e.2

/-- The same as a truth value (`tabOKb_iff`). -/
def tabOKb (O : ByteArray → ByteArray) : List (ByteArray × ByteArray) → Bool
  | [] => true
  | e :: t => decide (O e.1 = e.2) && tabOKb O t

theorem tabOK_nil (O : ByteArray → ByteArray) : TabOK O [] := fun _ h => nomatch h

theorem tabOK_cons (O : ByteArray → ByteArray) (e : ByteArray × ByteArray)
    (t : List (ByteArray × ByteArray)) (h : O e.1 = e.2) (ht : TabOK O t) :
    TabOK O (e :: t) := fun x hx => by
  rcases List.mem_cons.1 hx with rfl | hx
  · exact h
  · exact ht x hx

theorem tabOK_append (O : ByteArray → ByteArray) (a b : List (ByteArray × ByteArray))
    (ha : TabOK O a) (hb : TabOK O b) :
    TabOK O (a ++ b) := fun x hx => by
  rcases List.mem_append.1 hx with hx | hx
  · exact ha x hx
  · exact hb x hx

theorem tabOK_flatten (O : ByteArray → ByteArray)
    (l : List (List (ByteArray × ByteArray))) (h : ∀ a ∈ l, TabOK O a) :
    TabOK O l.flatten := fun x hx => by
  obtain ⟨a, ha, hxa⟩ := List.mem_flatten.1 hx
  exact h a ha x hxa

theorem tabOKb_iff (O : ByteArray → ByteArray) : ∀ tab, tabOKb O tab = true ↔ TabOK O tab
  | [] => ⟨fun _ => tabOK_nil O, fun _ => rfl⟩
  | e :: t => by
      unfold tabOKb
      rw [Bool.and_eq_true, decide_eq_true_iff, tabOKb_iff O t]
      exact ⟨fun h => tabOK_cons O e t h.1 h.2,
        fun h => ⟨h e (List.mem_cons_self), fun x hx => h x (List.mem_cons_of_mem _ hx)⟩⟩

theorem tabFind_mem :
    ∀ (tab : List (ByteArray × ByteArray)) (x y : ByteArray), tabFind tab x = some y → (x, y) ∈ tab
  | [], _, _, h => nomatch h
  | e :: t, x, y, h => by
      unfold tabFind at h
      by_cases he : e.1 = x
      · rw [if_pos he] at h
        have : e = (x, y) := Prod.ext he (Option.some.inj h)
        rw [this]
        exact List.mem_cons_self
      · rw [if_neg he] at h
        exact List.mem_cons_of_mem _ (tabFind_mem t x y h)

/-- If `TabOK O tab`, the function behind its table is the function. -/
theorem mix_eq (O : ByteArray → ByteArray) (tab : List (ByteArray × ByteArray)) (h : TabOK O tab) :
    mix O tab = O := by
  funext x
  unfold mix
  cases hf : tabFind tab x with
  | none => rfl
  | some y => exact (h (x, y) (tabFind_mem tab x y hf)).symm

/-- If `TabOK O tab`, what holds of the function behind its table holds of the function. -/
theorem of_mix {P : (ByteArray → ByteArray) → Prop} (O : ByteArray → ByteArray)
    (tab : List (ByteArray × ByteArray)) (hP : P (mix O tab)) (h : TabOK O tab) : P O :=
  mix_eq O tab h ▸ hP

/-- All strings of a list are in the table (a test for the table's maker). -/
def hits (tab : List (ByteArray × ByteArray)) (xs : List ByteArray) : Bool :=
  xs.all fun x => (tabFind tab x).isSome

/-! ## Guards (#guard) -/

#guard tabFind [(⟨#[1]⟩, ⟨#[7]⟩), (⟨#[2]⟩, ⟨#[8]⟩), (⟨#[1]⟩, ⟨#[9]⟩)] ⟨#[1]⟩ == some ⟨#[7]⟩
#guard tabFind [(⟨#[1]⟩, ⟨#[7]⟩)] ⟨#[3]⟩ == none
#guard mix id [(⟨#[1]⟩, ⟨#[7]⟩)] ⟨#[1]⟩ == ⟨#[7]⟩ && mix id [(⟨#[1]⟩, ⟨#[7]⟩)] ⟨#[3]⟩ == ⟨#[3]⟩
#guard tabOKb id [(⟨#[1]⟩, ⟨#[1]⟩)] && !tabOKb id [(⟨#[1]⟩, ⟨#[7]⟩)]
#guard hits [(⟨#[1]⟩, ⟨#[7]⟩)] [⟨#[1]⟩] && !hits [(⟨#[1]⟩, ⟨#[7]⟩)] [⟨#[1]⟩, ⟨#[2]⟩]

end Run
