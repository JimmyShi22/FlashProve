-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Run/HotelEsc.lean: an explicit bijection A ⊕ {0,1}* ≃ {0,1}* in which a point of A is written as its
own code, with nothing in front; room for the other strings is made by an escape.

Definitions, theorems. Generic; no choice; all data compute.
The file starts from an injective code of A in bit strings with a parser (`StrCode A`,
Rom/Hotel.lean: put, parse); a code is a string put a.

Why: Rom/Hotel.lean has such a bijection in which a point a is written true :: put a. A format that
fixes the oracle's strings to the byte leaves no room for a bit in front: the string of a typed
point must be put a itself. What such a format can grant is an escape: a string e, not empty, with
which no code begins.

Main names:
  `freeE`: s is free: s is not of the form e ++ .. ++ e ++ put a (any number of copies of e, none
    too).
  `encE`: inl a ↦ put a; inr s ↦ s if s is free, e ++ s if not.
  `decE`: the inverse (under `hp`; see `hotelE`).
  `hotelE`: the bijection, if e is not empty (`he`) and no code begins with e (`hp`).

Limits: this file does not say which format, which escape. It says nothing on a hash.
-/
import Rom.Hotel

set_option autoImplicit false

namespace Rom
namespace StrCode
variable {A : Type} (c : StrCode A) (e : List Bool)

/-- The string s without the escape in front, if it stands there. -/
def strip (s : List Bool) : Option (List Bool) :=
  if e.isPrefixOf s then some (s.drop e.length) else none

theorem strip_some {e s t : List Bool} (h : strip e s = some t) : s = e ++ t := by
  unfold strip at h
  split at h
  · rename_i hp
    obtain ⟨r, rfl⟩ := List.isPrefixOf_iff_prefix.1 hp
    simp at h
    rw [h]
  · cases h

theorem strip_append (e t : List Bool) : strip e (e ++ t) = some t := by
  unfold strip
  rw [if_pos (List.isPrefixOf_iff_prefix.2 (List.prefix_append e t))]
  simp

theorem strip_lt {e s t : List Bool} (he : e ≠ []) (h : strip e s = some t) :
    t.length < s.length := by
  rw [strip_some h, List.length_append]
  have : 0 < e.length := List.length_pos_iff.2 he
  omega

/-- The string is not: copies of the escape, then a code. -/
def freeE (he : e ≠ []) (s : List Bool) : Bool :=
  match c.parse s with
  | some _ => false
  | none =>
    match h : strip e s with
    | some t =>
      have : t.length < s.length := strip_lt he h
      freeE he t
    | none => true
termination_by s.length

def encE (he : e ≠ []) : A ⊕ List Bool → List Bool
  | .inl a => c.put a
  | .inr s => if c.freeE e he s then s else e ++ s

def decE (he : e ≠ []) (s : List Bool) : A ⊕ List Bool :=
  match c.parse s with
  | some a => .inl a
  | none =>
    match strip e s with
    | some t => if c.freeE e he t then .inr s else .inr t
    | none => .inr s

variable {c e}

theorem freeE_some (he : e ≠ []) {s : List Bool} {a : A} (h : c.parse s = some a) :
    c.freeE e he s = false := by
  rw [freeE]
  split
  · rfl
  · rename_i h'
    rw [h] at h'
    cases h'

theorem freeE_strip (he : e ≠ []) {s t : List Bool}
    (h : c.parse s = none) (hs : strip e s = some t) :
    c.freeE e he s = c.freeE e he t := by
  rw [freeE]
  split
  · rename_i h'
    rw [h] at h'
    cases h'
  · split
    · rename_i t' ht'
      rw [hs] at ht'
      cases ht'
      rfl
    · rename_i ht'
      rw [hs] at ht'
      cases ht'

theorem freeE_none (he : e ≠ []) {s : List Bool} (h : c.parse s = none) (hs : strip e s = none) :
    c.freeE e he s = true := by
  rw [freeE]
  split
  · rename_i h'
    rw [h] at h'
    cases h'
  · split
    · rename_i t' ht'
      rw [hs] at ht'
      cases ht'
    · rfl

/-- A free string is no code. -/
theorem parse_of_free (he : e ≠ []) {s : List Bool} (h : c.freeE e he s = true) :
    c.parse s = none := by
  cases hp : c.parse s with
  | none => rfl
  | some a => rw [freeE_some he hp] at h; cases h

/-- Nothing that begins with the escape is a code, if no code begins with it (`hp`). -/
theorem parse_esc (hp : ∀ a t, c.put a ≠ e ++ t) (t : List Bool) : c.parse (e ++ t) = none := by
  cases h : c.parse (e ++ t) with
  | none => rfl
  | some a => exact absurd (c.put_parse _ a h) (hp a t)

theorem decE_encE (he : e ≠ []) (hp : ∀ a t, c.put a ≠ e ++ t) :
    ∀ x, c.decE e he (c.encE e he x) = x
  | .inl a => by
      show c.decE e he (c.put a) = _
      unfold decE
      rw [c.parse_put]
  | .inr s => by
      by_cases h : c.freeE e he s = true
      · have h0 : c.encE e he (.inr s) = s := if_pos h
        rw [h0]
        unfold decE
        rw [parse_of_free he h]
        cases hs : strip e s with
        | none => rfl
        | some t =>
            have ht : c.freeE e he t = true := by
              rw [← freeE_strip he (parse_of_free he h) hs]; exact h
            show (if c.freeE e he t = true then Sum.inr s else Sum.inr t) = _
            rw [if_pos ht]
      · have h0 : c.encE e he (.inr s) = e ++ s := if_neg h
        rw [h0]
        unfold decE
        rw [parse_esc hp s, strip_append]
        show (if c.freeE e he s = true then Sum.inr (e ++ s) else Sum.inr s) = _
        rw [if_neg h]

theorem encE_decE (he : e ≠ []) (s : List Bool) : c.encE e he (c.decE e he s) = s := by
  unfold decE
  cases hp : c.parse s with
  | some a => exact c.put_parse s a hp
  | none =>
      cases hs : strip e s with
      | none => exact if_pos (freeE_none he hp hs)
      | some t =>
          by_cases ht : c.freeE e he t = true
          · show c.encE e he (if c.freeE e he t = true then Sum.inr s else Sum.inr t) = s
            rw [if_pos ht]
            exact if_pos (by rw [freeE_strip he hp hs]; exact ht)
          · show c.encE e he (if c.freeE e he t = true then Sum.inr s else Sum.inr t) = s
            rw [if_neg ht]
            exact (if_neg ht).trans (strip_some hs).symm

variable (c e)

/-- The bijection. -/
def hotelE (he : e ≠ []) (hp : ∀ a t, c.put a ≠ e ++ t) : A ⊕ List Bool ≃ List Bool :=
  ⟨c.encE e he, c.decE e he, decE_encE he hp, encE_decE he⟩

/-- A point's string is its code. -/
theorem hotelE_inl (he : e ≠ []) (hp : ∀ a t, c.put a ≠ e ++ t) (a : A) :
    c.hotelE e he hp (.inl a) = c.put a := rfl

/-- A free string is written as itself. -/
theorem hotelE_free (he : e ≠ []) (hp : ∀ a t, c.put a ≠ e ++ t)
    (s : List Bool) (h : c.freeE e he s = true) : c.hotelE e he hp (.inr s) = s := if_pos h

end StrCode
end Rom
