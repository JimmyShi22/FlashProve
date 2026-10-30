-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/Walk/FrameNone.lean: NoneBetween (FrameTied.lean: the plan's numbers of trees and of
messages are the same in front of block k and behind it) AT THE NUMBERS THAT ARE FILLED OFF WHAT THE
CHAIN's BLOCKS TELL (Numbers.withTold, Johnson/Desc/First/BookNumbers.lean): paid outright, without
a test's yes, wherever block k tells nothing and no place stands twice in the list.

  borderOf_at, borderOf_end   in a list without a repeat the border in front of the block at entry k
                    is k; the chain's last border is the list's length
  noneBetween_withTold

Limits. That a block tells nothing (told[k]? = some []) is its place's law. No soundness statement.

-/
import Johnson.Top.H0.Walk.FrameTied
import Johnson.Desc.First.BookNumbers

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Desc.First.Walk.Tied
open VerifiableInference.Desc (Place Oracle)
open VerifiableInference.Desc.First (Numbers borderOf treesTold msgsTold told_succ_nil)

theorem borderOf_at {ps : List Place} (hn : ps.Nodup) {k : Nat} (hk : k < ps.length) :
    borderOf ps ps[k]? = k := by
  rw [List.getElem?_eq_getElem hk]
  exact List.idxOf_getElem hn k hk

theorem borderOf_end (ps : List Place) : borderOf ps ps[ps.length]? = ps.length := by
  rw [List.getElem?_eq_none (Nat.le_refl _)]
  rfl

theorem borderOf_le {ps : List Place} (hn : ps.Nodup) {k : Nat} (hk : k ≤ ps.length) :
    borderOf ps ps[k]? = k := by
  rcases Nat.lt_or_eq_of_le hk with h | h
  · exact borderOf_at hn h
  · subst h
    exact borderOf_end ps

/-- **Paid at the numbers off the blocks' own telling.** -/
theorem noneBetween_withTold (N : Numbers) {ps : List Place} {told : List (List Oracle)}
    (hn : ps.Nodup) {k : Nat} (hk : k < ps.length) (ht : told[k]? = some []) :
    NoneBetween (N.withTold ps told) ps k := by
  have e1 := borderOf_le hn (Nat.succ_le_of_lt hk)
  have e0 := borderOf_at hn hk
  obtain ⟨c1, c2⟩ := told_succ_nil told k ht
  refine ⟨?_, ?_⟩
  · show treesTold told (borderOf ps ps[k + 1]?) = treesTold told (borderOf ps ps[k]?)
    rw [e1, e0, c1]
  · show msgsTold told (borderOf ps ps[k + 1]?) = msgsTold told (borderOf ps ps[k]?)
    rw [e1, e0, c2]

#print axioms noneBetween_withTold

end Johnson.Desc.First.Walk.Tied
