-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/Raw.lean: raw strings.

Two descriptions of one protocol can give the strings under a hash tree's root two types,
Fin n₁ → S₁ and Fin n₂ → S₂, although n₁ = n₂ can be proved and the symbols can be read alike. A
property that is to be said of both is said here of a third thing, a raw string: a function from the
natural numbers to "a symbol or nothing". The raw string of a string of n symbols has a symbol at
each place below n and nothing from n on.

Main definitions: `Raw`, `rawOf`, `Raw.HasLen`.
Main theorems.
 `rawOf_congr`    two strings of equal length whose symbols are read alike at each place have one
                  raw string; that the lengths are equal is a hypothesis, not a matter of types.
 `rawOf_hasLen`   the raw string of a string of n symbols has exactly n symbols.
 `Raw.HasLen.unique`, `Raw.HasLen.eq_rawOf`   a raw string has at most one length; one with exactly
                  n symbols is the raw string of a string of n symbols.
 `rawOf_eq_iff`   two strings have one raw string exactly if their lengths are equal and their
                  symbols are read alike at each place.

Not claimed. Nothing on hash trees, on protocols or on what is read under a root.

-/
import Mathlib.Data.Nat.Notation
import Mathlib.Logic.Equiv.Defs

set_option autoImplicit false

namespace OnBytes.Slice

/-- A raw string. Meant: a symbol at each place below some length and nothing from there on; `rawOf`
makes only such. The type does not ask it: it also holds functions with gaps, and functions without
an end. -/
abbrev Raw (Sg : Type) : Type := ℕ → Option Sg

/-- A string of n symbols as a raw string, its symbols read through u. -/
def rawOf {n : ℕ} {S Sg : Type} (u : S ≃ Sg) (y : Fin n → S) : Raw Sg :=
  fun j => if h : j < n then some (u (y ⟨j, h⟩)) else none

/-- Two strings of equal length whose symbols are read alike at each place are one raw string. The
two lengths may be different terms: that they are equal is a hypothesis. -/
theorem rawOf_congr {n₁ n₂ : ℕ} {S₁ S₂ Sg : Type} (hn : n₁ = n₂) (u₁ : S₁ ≃ Sg) (u₂ : S₂ ≃ Sg)
    (y₁ : Fin n₁ → S₁) (y₂ : Fin n₂ → S₂)
    (h : ∀ (q₁ : Fin n₁) (q₂ : Fin n₂), q₁.val = q₂.val → u₁ (y₁ q₁) = u₂ (y₂ q₂)) :
    rawOf u₁ y₁ = rawOf u₂ y₂ := by
  funext j
  unfold rawOf
  by_cases hj : j < n₁
  · rw [dif_pos hj, dif_pos (hn ▸ hj), h ⟨j, hj⟩ ⟨j, hn ▸ hj⟩ rfl]
  · rw [dif_neg hj, dif_neg (hn ▸ hj)]

/-- The raw string has exactly n symbols: one at each place below n, none from n on. -/
def Raw.HasLen {Sg : Type} (f : Raw Sg) (n : ℕ) : Prop := ∀ j, f j = none ↔ n ≤ j

/-- The raw string of a string of n symbols has exactly n symbols. -/
theorem rawOf_hasLen {n : ℕ} {S Sg : Type} (u : S ≃ Sg) (y : Fin n → S) :
    Raw.HasLen (rawOf u y) n := by
  intro j
  unfold rawOf
  by_cases h : j < n
  · rw [dif_pos h]
    exact ⟨fun e => (by cases e), fun e => absurd h (Nat.not_lt.2 e)⟩
  · rw [dif_neg h]
    exact ⟨fun _ => Nat.le_of_not_lt h, fun _ => rfl⟩

/-- A raw string has at most one length. -/
theorem Raw.HasLen.unique {Sg : Type} {f : Raw Sg} {n₁ n₂ : ℕ} (h₁ : Raw.HasLen f n₁)
    (h₂ : Raw.HasLen f n₂) : n₁ = n₂ :=
  Nat.le_antisymm ((h₁ n₂).1 ((h₂ n₂).2 (Nat.le_refl _))) ((h₂ n₁).1 ((h₁ n₁).2 (Nat.le_refl _)))

/-- A raw string with exactly n symbols is the raw string of a string of n symbols. -/
theorem Raw.HasLen.eq_rawOf {Sg : Type} {f : Raw Sg} {n : ℕ} (h : Raw.HasLen f n) :
    ∃ y : Fin n → Sg, f = rawOf (Equiv.refl _) y := by
  have hs : ∀ p : Fin n, (f p.val).isSome = true := fun p =>
    Option.isSome_iff_ne_none.2 fun e => absurd ((h _).1 e) (Nat.not_le.2 p.isLt)
  refine ⟨fun p => (f p.val).get (hs p), ?_⟩
  funext j
  unfold rawOf
  by_cases hj : j < n
  · rw [dif_pos hj]
    exact (Option.some_get (hs ⟨j, hj⟩)).symm
  · rw [dif_neg hj]
    exact (h j).2 (Nat.le_of_not_lt hj)

/-- Two strings have one raw string exactly if their lengths are equal and their symbols are read
alike at each place. -/
theorem rawOf_eq_iff {n₁ n₂ : ℕ} {S₁ S₂ Sg : Type} (u₁ : S₁ ≃ Sg) (u₂ : S₂ ≃ Sg)
    (y₁ : Fin n₁ → S₁) (y₂ : Fin n₂ → S₂) :
    rawOf u₁ y₁ = rawOf u₂ y₂ ↔
      n₁ = n₂ ∧ ∀ (q₁ : Fin n₁) (q₂ : Fin n₂), q₁.val = q₂.val → u₁ (y₁ q₁) = u₂ (y₂ q₂) := by
  constructor
  · intro h
    refine ⟨(rawOf_hasLen u₁ y₁).unique (h ▸ rawOf_hasLen u₂ y₂), fun q₁ q₂ hq => ?_⟩
    have h1 := congrFun h q₁.val
    unfold rawOf at h1
    rw [dif_pos q₁.isLt, dif_pos (hq ▸ q₂.isLt)] at h1
    have h2 : (⟨q₁.val, hq ▸ q₂.isLt⟩ : Fin n₂) = q₂ := Fin.ext hq
    rw [h2] at h1
    exact Option.some.inj h1
  · rintro ⟨hn, h⟩
    exact rawOf_congr hn u₁ u₂ y₁ y₂ h

end OnBytes.Slice
