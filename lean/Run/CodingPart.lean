-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Run/CodingPart.lean: partial codes: a code that writes only some points as strings, and how it is
made total with an escape prefix.

Definitions that compute, with their laws. Generic: no format, no oracle.
A point is an element of a type A; a string is a `List Bool`. A total code (`StrCode A`,
Rom/Hotel.lean) writes every point as a string, injectively, and has a parser that reads the string
back.

Why: replacing a family of typed oracles by one oracle on bit strings (the one-oracle exit; `OracleCoding`,
Rom/Family.lean) needs every typed point written as a bit string, injectively, with a parser. A
format of programs writes only the points that its verifier asks, in its own way: a typed query
whose fields do not fit the format (a chain value of another length, a round that the plan does not
have) has no string there. So the format gives a partial code; the other points are written by any
total code behind a prefix with which no string of the format begins.

Main names:
  `PCode A`: put, parse and the two laws: parse s = some a exactly if put a = some s.
  `PCode.orElse p c e he`: a total code (`StrCode`, Rom/Hotel.lean); asked (`he`): no string of p
    begins with e.
  `PCode.orElse_not_prefix`: its doc comment tells it.

Limits: this file does not say which format. It does not say how the strings that are no code of a
point are dealt with (a hotel: `hotelE`, Run/HotelEsc.lean).

Terms: lean/GLOSSARY.md.
-/
import Rom.Hotel

namespace Run
open Rom

/-- A partial code with a parser. -/
structure PCode (A : Type) where
  put : A → Option (List Bool)
  parse : List Bool → Option A
  parse_put : ∀ a s, put a = some s → parse s = some a
  put_parse : ∀ s a, parse s = some a → put a = some s

namespace PCode
variable {A B : Type}

theorem inj (p : PCode A) {a b : A} {s : List Bool}
    (ha : p.put a = some s) (hb : p.put b = some s) : a = b :=
  Option.some.inj ((p.parse_put a s ha).symm.trans (p.parse_put b s hb))

/-- The partial code that writes nothing. -/
def empty (A : Type) : PCode A where
  put := fun _ => none
  parse := fun _ => none
  parse_put := fun _ _ h => nomatch h
  put_parse := fun _ _ h => nomatch h

/-- The partial code p carried along a bijection e. -/
def congr (p : PCode A) (e : A ≃ B) : PCode B where
  put := fun b => p.put (e.symm b)
  parse := fun s => (p.parse s).map e
  parse_put := fun b s h => by rw [p.parse_put _ s h]; simp
  put_parse := fun s b h => by
    cases hp : p.parse s with
    | none => rw [hp] at h; cases h
    | some a =>
        rw [hp] at h
        have hb : e a = b := Option.some.inj h
        rw [← hb, Equiv.symm_apply_apply]
        exact p.put_parse s a hp

/-- The partial code p on the points where ok holds. -/
def sub (p : PCode A) (ok : A → Bool) : PCode A where
  put := fun a => if ok a then p.put a else none
  parse := fun s => (p.parse s).filter ok
  parse_put := fun a s h => by
    by_cases hk : ok a = true
    · rw [if_pos hk] at h
      rw [p.parse_put a s h]
      simp [hk]
    · rw [if_neg hk] at h
      cases h
  put_parse := fun s a h => by
    obtain ⟨h1, h2⟩ := Option.filter_eq_some_iff.1 h
    rw [if_pos h2]
    exact p.put_parse s a h1

/-- The partial codes p and q together, on a sum, if no string is written by both (`h`). -/
def sum (p : PCode A) (q : PCode B) (h : ∀ a b s, p.put a = some s → q.put b ≠ some s) :
    PCode (A ⊕ B) where
  put := fun x => match x with
    | .inl a => p.put a
    | .inr b => q.put b
  parse := fun s => match p.parse s with
    | some a => some (.inl a)
    | none => (q.parse s).map .inr
  parse_put := fun x s hx => by
    rcases x with a | b
    · have := p.parse_put a s hx
      simp [this]
    · cases hp : p.parse s with
      | some a => exact absurd hx (h a b s (p.put_parse s a hp))
      | none =>
          have := q.parse_put b s hx
          simp [this]
  put_parse := fun s x hx => by
    cases hp : p.parse s with
    | some a =>
        simp only [hp] at hx
        rw [← Option.some.inj hx]
        exact p.put_parse s a hp
    | none =>
        simp only [hp] at hx
        cases hq : q.parse s with
        | none => rw [hq] at hx; cases hx
        | some b =>
            rw [hq] at hx
            rw [← Option.some.inj hx]
            exact q.put_parse s b hq

end PCode

/-- The string s without its prefix e, if it has that prefix. -/
def strip : List Bool → List Bool → Option (List Bool)
  | [], s => some s
  | _ :: _, [] => none
  | a :: e, b :: s => if a = b then strip e s else none

theorem strip_append : ∀ e r : List Bool, strip e (e ++ r) = some r
  | [], _ => rfl
  | a :: e, r => by
      show (if a = a then strip e (e ++ r) else none) = some r
      rw [if_pos rfl]
      exact strip_append e r

theorem eq_of_strip : ∀ (e s r : List Bool), strip e s = some r → s = e ++ r
  | [], s, r, h => by rw [← Option.some.inj h]; rfl
  | _ :: _, [], _, h => by cases h
  | a :: e, b :: s, r, h => by
      by_cases hab : a = b
      · have h' : strip e s = some r := by
          have h2 : (if a = b then strip e s else none) = some r := h
          rwa [if_pos hab] at h2
        rw [eq_of_strip e s r h', hab]
        rfl
      · have h2 : (if a = b then strip e s else none) = some r := h
        rw [if_neg hab] at h2
        cases h2

namespace PCode
variable {A : Type}

/-- What the total code `orElse` writes. -/
def putE (p : PCode A) (c : StrCode A) (e : List Bool) (a : A) : List Bool :=
  match p.put a with
  | some s => s
  | none => e ++ c.put a

/-- How the total code `orElse` reads. -/
def parseE (p : PCode A) (c : StrCode A) (e : List Bool) (s : List Bool) : Option A :=
  match p.parse s with
  | some a => some a
  | none => match strip e s with
    | none => none
    | some r => (c.parse r).filter fun a => (p.put a).isNone

theorem putE_some (p : PCode A) (c : StrCode A) (e : List Bool) {a : A}
    {s : List Bool} (h : p.put a = some s) : p.putE c e a = s := by
  unfold putE
  rw [h]

theorem putE_none (p : PCode A) (c : StrCode A) (e : List Bool) {a : A} (h : p.put a = none) :
    p.putE c e a = e ++ c.put a := by
  unfold putE
  rw [h]

/-- A partial code made total: its own string where there is one; elsewhere the escape e and then
the string of a total code. Asked (`he`): no string of p begins with e. -/
def orElse (p : PCode A) (c : StrCode A) (e : List Bool)
    (he : ∀ a s, p.put a = some s → ¬ e <+: s) : StrCode A where
  put := p.putE c e
  parse := p.parseE c e
  parse_put := fun a => by
    cases hp : p.put a with
    | some s =>
        rw [putE_some p c e hp]
        unfold parseE
        rw [p.parse_put a s hp]
    | none =>
        rw [putE_none p c e hp]
        unfold parseE
        cases hq : p.parse (e ++ c.put a) with
        | some b => exact absurd ⟨c.put a, rfl⟩ (he b _ (p.put_parse _ b hq))
        | none =>
            show (match strip e (e ++ c.put a) with
              | none => none
              | some r => (c.parse r).filter fun a => (p.put a).isNone) = some a
            rw [strip_append]
            show (c.parse (c.put a)).filter (fun a => (p.put a).isNone) = some a
            rw [c.parse_put]
            simp [hp]
  put_parse := fun s a h => by
    unfold parseE at h
    cases hq : p.parse s with
    | some b =>
        rw [hq] at h
        have hb : b = a := Option.some.inj h
        rw [← hb]
        exact putE_some p c e (p.put_parse s b hq)
    | none =>
        rw [hq] at h
        cases hs : strip e s with
        | none => rw [hs] at h; cases h
        | some r =>
            rw [hs] at h
            obtain ⟨h1, h2⟩ := Option.filter_eq_some_iff.1 h
            have h3 : p.put a = none := Option.isNone_iff_eq_none.1 h2
            rw [putE_none p c e h3, c.put_parse r a h1, eq_of_strip e s r hs]

theorem orElse_put_some (p : PCode A) (c : StrCode A) (e : List Bool)
    (he : ∀ a s, p.put a = some s → ¬ e <+: s) {a : A} {s : List Bool} (h : p.put a = some s) :
    (p.orElse c e he).put a = s :=
  putE_some p c e h

theorem orElse_put_none (p : PCode A) (c : StrCode A) (e : List Bool)
    (he : ∀ a s, p.put a = some s → ¬ e <+: s) {a : A} (h : p.put a = none) :
    (p.orElse c e he).put a = e ++ c.put a :=
  putE_none p c e h

/-- A prefix f with which no string of p begins (`hp`), and no string that begins with e (`hf`), is
the prefix of no string that the total code `orElse` (with its `he`) writes. -/
theorem orElse_not_prefix (p : PCode A) (c : StrCode A) (e : List Bool)
    (he : ∀ a s, p.put a = some s → ¬ e <+: s) (f : List Bool)
    (hp : ∀ a s, p.put a = some s → ¬ f <+: s) (hf : ∀ r, ¬ f <+: e ++ r) (a : A) :
    ¬ f <+: (p.orElse c e he).put a := by
  cases h : p.put a with
  | some s => rw [orElse_put_some p c e he h]; exact hp a s h
  | none => rw [orElse_put_none p c e he h]; exact hf _

end PCode
end Run
