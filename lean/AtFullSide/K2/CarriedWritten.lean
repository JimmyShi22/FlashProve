-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K2/CarriedWritten.lean: the entries that the written book carries to the code switch's parts
are the written list (CarriedLit.lean), piece by piece of the book.

  carriedLit_is     they are the written book's carried entries at the kind's parts
  carry_at_written  at a part of the kind, the carried entries of the book are those of the list

Nothing on soundness, completeness or hiding.
-/
import AtFullSide.K2.CarriedPieces.Seg0
import AtFullSide.K2.CarriedPieces.Seg1
import AtFullSide.K2.CarriedPieces.Seg2
import AtFullSide.K2.CarriedPieces.Seg3
import AtFullSide.K2.CarriedPieces.Wants
import AtFullSide.K2.CarriedPieces.Small

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtFullSide.K2
open VerifiableInference.Desc (KindName Place)
open ProofFile.Honest
open ProofFile.Honest.K14
open AtFullSide.K14

theorem eq_of_four {α : Type} {l m : List α} (h₀ : l.take 600 = m.take 600)
    (h₁ : (l.drop 600).take 600 = (m.drop 600).take 600)
    (h₂ : ((l.drop 600).drop 600).take 600 = ((m.drop 600).drop 600).take 600)
    (h₃ : ((l.drop 600).drop 600).drop 600 = ((m.drop 600).drop 600).drop 600) : l = m := by
  rw [← List.take_append_drop 600 l, ← List.take_append_drop 600 m, h₀,
    ← List.take_append_drop 600 (l.drop 600), ← List.take_append_drop 600 (m.drop 600), h₁,
    ← List.take_append_drop 600 ((l.drop 600).drop 600),
    ← List.take_append_drop 600 ((m.drop 600).drop 600), h₂, h₃]

/-- **The written book's entries at the kind's parts are these.** -/
theorem carriedLit_is : (rawAheadW.filter keepK2).map tupOf = carriedLit := by
  have hs : (rawSegW.filter keepK2).map tupOf = carriedLit :=
    eq_of_four segKept_0 segKept_1 segKept_2 segKept_3
  have hw := wantsKept_none
  have ho := smallKept_none
  simp only [List.filter_append, List.append_eq_nil_iff] at ho
  obtain ⟨⟨⟨⟨⟨⟨o₁, o₂⟩, o₃⟩, o₄⟩, o₅⟩, o₆⟩, o₇⟩ := ho
  unfold rawAheadW
  simp only [List.filter_append, List.filter_nil, hw, o₁, o₂, o₃, o₄, o₅, o₆, o₇, List.nil_append,
    List.append_nil]
  exact hs

theorem aheadOf_tupOf {e : Ahead} (h : e.once = false) : aheadOf (tupOf e) = e := by
  cases e
  simp_all [aheadOf, tupOf]

/-- The book's entries at the kind's parts, as entries. -/
theorem keep_is : rawAheadW.filter keepK2 = carriedLitA := by
  unfold carriedLitA
  rw [← carriedLit_is, List.map_map]
  conv => lhs; rw [← List.map_id (rawAheadW.filter keepK2)]
  refine List.map_congr_left fun e he => ?_
  have hk : keepK2 e = true := (List.mem_filter.1 he).2
  have ho : e.once = false := by
    simp only [keepK2, Bool.and_eq_true, Bool.not_eq_true'] at hk
    exact hk.1.1
  exact (aheadOf_tupOf ho).symm

/-- What the tests read of a list at a part. -/
abbrev carryOf (es : List Ahead) (a : Addr) : List Ahead :=
  (es.filter fun e => e.spender == a).filter fun e => !e.once

/-- At a part of the kind, keeping the kind's carried entries first changes nothing. -/
theorem carryOf_keep (es : List Ahead) {a : Addr} (hk : a.place.kind = KindName.K2)
    (hp : a.part = 0) : carryOf (es.filter keepK2) a = carryOf es a := by
  simp only [carryOf, List.filter_filter]
  refine List.filter_congr fun e _ => ?_
  by_cases hs : e.spender = a
  · subst hs
    simp [keepK2, hk, hp]
  · have : (e.spender == a) = false := by simpa using hs
    simp [this]

/-- **At a part of the kind the written book carries what the list says.** -/
theorem carry_at_written {a : Addr} (hk : a.place.kind = KindName.K2) (hp : a.part = 0) :
    carryOf rawAheadW a = carryOf carriedLitA a := by
  rw [← carryOf_keep rawAheadW hk hp, keep_is]

end AtFullSide.K2

#print axioms AtFullSide.K2.carriedLit_is
#print axioms AtFullSide.K2.carry_at_written
