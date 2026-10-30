-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/LPFK9R/SlotsSize.lean: A RIDER TO Johnson/LPFK9R/SlotsSeat.lean: "THE OPEN LEDGER's LIST LS
HAS
AS MANY COEFFICIENTS AS THE LEDGER HAS SLOTS", WITHOUT A WORD ON THE LINK: from the invariant
`SlotsInv (nsZ Z nH) s` and "a ledger is open" alone. Two short theorems.
  `link_of_fork`: where a ledger is open a link is open.
  `lsSize_of_slots`: **SlotsInv (nsZ Z nH) s → s.fork? = some G → G.LS.size = G.ns.**
Limits. Nothing on soundness.

-/
import Johnson.LPFK9R.SlotsSeat

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Model
open VerifiableInference.Desc.First (S)

theorem link_of_fork {s : S} {G : Fork} (h : s.fork? = some G) : ∃ L, s.link? = some L := by
  unfold S.fork? at h
  unfold S.link?
  cases hh : s.here with
  | lay a => exact ⟨_, rfl⟩
  | att a => exact ⟨_, rfl⟩
  | head a =>
    rw [hh] at h
    dsimp only at h ⊢
    split at h
    · rename_i ho
      exact ⟨a.L, by rw [if_pos ho]⟩
    · cases h
  | between => rw [hh] at h; cases h
  | fin a => rw [hh] at h; cases h
  | mem a => rw [hh] at h; cases h

theorem lsSize_of_slots {Z : ProofFile.Pub} {nH : ℕ} {s : S} (h : SlotsInv (nsZ Z nH) s) {G : Fork}
    (hG : s.fork? = some G) : G.LS.size = G.ns := by
  obtain ⟨L, hL⟩ := link_of_fork hG
  exact (slots_field h hG hL rfl).2

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.lsSize_of_slots
