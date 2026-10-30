-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Ends/FoLookLay.lean.
The caller's entries with one entry more, read along a lay's addresses.

The lookup's side names the places of its claims by maps into Option J and reads them by
Cb.Fo.zext m, which is 0 at none. The ledger's side reads the entries m : J → K by addresses
(OnBytes.Road.Rows.Lay.cellAt, Lay.maskAt), which are 0 at an address that no entry has. This file
lays the first on the second.

Main names:
  `entryOf Y a`: the entry of J with the address a, or none. There is at most one (Lay.inj); it is
    taken by choice, so the definition is noncomputable.
  `zext_entryOf`: zext m (entryOf Y a) is the sum over the entries with the address a.
  `zext_cell`, `zext_mask`: zext m (entryOf Y (.cell t r c)) = Y.cellAt m t r c;
    zext m (entryOf Y (.mask j)) = Y.maskAt m j.
Needs: OnBytes/Tie/Pv/Led/LedLay.lean and OnBytes/Tie/Pv/Led/LedJoint.lean.
Does not say: that the places of a lookup's claims are of the form entryOf Y a.
Not claimed: anything on soundness, completeness or hiding.

-/
import OnBytes.Tie.Pv.Lookup.Ends.FoLookBatch
import OnBytes.Tie.Pv.Led.LedLay

set_option autoImplicit false

namespace Fo
open TWhole OnBytes.Road.Rows Cb.Fo

section
variable {K J : Type} [Field K] [Fintype J] (Y : Lay J) (m : J → K)

open Classical in
/-- The entry with the address a, or none. -/
noncomputable def entryOf {J : Type} (Y : Lay J) (a : Addr) : Option J :=
  if h : ∃ i, Y.addr i = a then some h.choose else none

theorem zext_entryOf (a : Addr) :
    zext m (entryOf Y a) = ∑ k, if Y.addr k = a then m k else 0 := by
  unfold entryOf
  split
  · rename_i h
    exact (Y.sum_at m a h.choose h.choose_spec).symm
  · rename_i h
    exact (Y.sum_none m a fun k hk => h ⟨k, hk⟩).symm

theorem zext_cell (t r c : ℕ) : zext m (entryOf Y (.cell t r c)) = Y.cellAt m t r c :=
  zext_entryOf Y m _

theorem zext_mask (j : ℕ) : zext m (entryOf Y (.mask j)) = Y.maskAt m j := zext_entryOf Y m _

end
end Fo
