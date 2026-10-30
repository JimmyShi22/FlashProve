-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Means/FrameKeeps.lean: three invariants on the statement, in the form in which a kind's
step is proved once for every relation that the ground's plain functions keep.

Johnson/Desc/GroundKeeps.lean names what a relation on statements owes so that every step which
writes the statement through the ground's plain functions keeps it. This file shows that "no open
row is marked as a sample row" (OpenKinds), "an oracle message that is not marked as sampled has no
sample row" (NoneYet) and "every member of a group is marked as sampled" (SampledMembers), each read
as the relation "if it holds before, it holds behind", are such relations, and joins the three.

Main theorems: groundKeeps_openKinds, groundKeeps_noneYet, groundKeeps_members, groundKeeps_three.

What is not claimed. InOrder is no such relation: the admitting keeps it only if the rows handed in
are on the message, and the copying from another statement only if that statement is in order. The
beginning of a test is outside the record; see beginRunP_kinds, beginRunP_none, beginRunP_members.

-/
import Johnson.Desc.GroundKeeps
import Johnson.Desc.Means.Kinds
import Johnson.Desc.Means.BackP
import Johnson.Desc.Means.Entry

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Means

open VerifiableInference.Desc VerifiableInference.Desc.Ground Desc.Plain

/-- "No open row is marked as a sample row" goes along the ground's plain functions. -/
theorem groundKeeps_openKinds : GroundKeeps fun a b => OpenKinds a → OpenKinds b where
  refl := fun _ h => h
  trans := fun h k x => k (h x)
  newGroup := fun _ _ _ _ _ h => newGroupP_kinds h
  recv := fun _ _ _ _ _ h => recvP_kinds h
  admit := fun _ _ _ _ h => admitP_kinds h
  join := fun _ _ _ _ _ h => joinP_kinds h
  addRow := fun _ _ _ _ h => addRowP_kinds h
  takeMask := fun _ _ _ _ h => takeMaskP_kinds h
  closeLedger := fun _ _ _ h => closeLedgerP_kinds h
  spendAsMask := fun _ _ _ h => spendAsMaskP_kinds h
  adopt := fun _ _ _ _ _ h => adoptP_kinds h
  elsewhere := fun _ _ _ _ _ h => elsewhereP_kinds h

/-- "An oracle message that is not marked as sampled has no sample row" goes along them too. -/
theorem groundKeeps_noneYet : GroundKeeps fun a b => NoneYet a → NoneYet b where
  refl := fun _ h => h
  trans := fun h k x => k (h x)
  newGroup := fun _ _ _ _ _ h => newGroupP_none h
  recv := fun _ _ _ _ _ h => recvP_none h
  admit := fun _ _ _ _ h => admitP_none h
  join := fun _ _ _ _ _ h => joinP_none h
  addRow := fun _ _ _ _ h => addRowP_none h
  takeMask := fun _ _ _ _ h => takeMaskP_none h
  closeLedger := fun _ _ _ h => closeLedgerP_none h
  spendAsMask := fun _ _ _ h => spendAsMaskP_none h
  adopt := fun _ _ _ _ _ h => adoptP_none h
  elsewhere := fun _ _ _ _ _ h => elsewhereP_none h

/-- "Every member of a group is marked as sampled" goes along them too. -/
theorem groundKeeps_members : GroundKeeps fun a b => SampledMembers a → SampledMembers b where
  refl := fun _ h => h
  trans := fun h k x => k (h x)
  newGroup := fun _ _ _ _ _ h => newGroupP_members h
  recv := fun _ _ _ _ _ h => recvP_members h
  admit := fun _ _ _ _ h => admitP_members h
  join := fun _ _ _ _ _ h => joinP_members h
  addRow := fun _ _ _ _ h => addRowP_members h
  takeMask := fun _ _ _ _ h => takeMaskP_members h
  closeLedger := fun _ _ _ h => closeLedgerP_members h
  spendAsMask := fun _ _ _ h => spendAsMaskP_members h
  adopt := fun _ _ _ _ _ h => adoptP_members h
  elsewhere := fun _ _ _ _ _ h => elsewhereP_members h

/-- The three together. -/
theorem groundKeeps_three : GroundKeeps fun a b =>
    ((OpenKinds a → OpenKinds b) ∧ (NoneYet a → NoneYet b)) ∧
      (SampledMembers a → SampledMembers b) :=
  (groundKeeps_openKinds.and groundKeeps_noneYet).and groundKeeps_members

end OnBytes.Means
