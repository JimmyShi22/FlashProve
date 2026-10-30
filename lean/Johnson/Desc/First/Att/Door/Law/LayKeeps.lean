-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
-- Johnson/Desc/First/Att/Door/Law/LayKeeps.lean: WHAT THE KIND's LAY LEAVES OF OUR OWN ITEMS' Bools, AND THE TEN PUBLIC ITEMS THAT ARE OPEN IN FRONT OF THE KIND's BLOCK AT OUR DOOR's ROWS. Mathlib beneath.
import Johnson.Desc.First.Att.Door.Law.FillK5Keeper
import Johnson.Desc.First.Att.Door.Law.ReadsThereTie

set_option autoImplicit false

namespace H2K5.Door
open OnBytes OnBytes.Model
open VerifiableInference.Desc.First
open VerifiableInference.Desc.First.Att.P (behind hear Heard)
open VerifiableInference.Desc.First.Att.P (fork_front sized_of_B hear_below)

/-- «K5.readsThere»'s Bool rides over the kind's lay, where the open ledger is sized. -/
theorem readsThereB_behind (W : Verify.Public) (own : List (Nat × Nat)) {s : S} {a : AttOwn}
    {x : Params.AttentionRounds} {rs : List Fmt.RoundView} {h : Heard} {G : Fork} (e : s.here = .att a)
    (hh : hear x (a.F, rs, 0) = some (h, G, [], 0)) (hz : s.fork?.any VerifiableInference.Desc.K3.sizedB = true)
    (hv : readsThereB W own s = true) : readsThereB W own (behind s a h G) = true := by
  rw [fork_front e] at hz
  obtain ⟨_, bl⟩ := hear_below hh (sized_of_B hz)
  unfold readsThereB at hv ⊢
  rw [e] at hv
  show ((W.A[a.L.link / 2]?).any fun p => readsAtB own p.iU3 p.nW a.L G s.book) = true
  unfold readsAtB at hv ⊢
  rw [bl.trees]
  exact hv

/-- «K5.liveReq»'s Bool reads the open link's own check alone, which the lay leaves. -/
theorem liveReqB_behind (born : Array (Nat × Nat)) {s : S} {a : AttOwn} {h : Heard} {G : Fork} (e : s.here = .att a)
    (hv : Att.P.liveReqB born s = true) : Att.P.liveReqB born (behind s a h G) = true := by
  unfold Att.P.liveReqB S.link? at hv ⊢
  rw [e] at hv
  exact hv

/-- The ten public items that are open in front of the kind's block at our door's rows. -/
def ten (m : Nat) : List Pub :=
  [.unheard, .ledger m, .linkFresh m, .freeAbove m, .more (some m) "K5.readsThere", .more (some m) "K5.liveReq",
    .lookOut m 2, .look m, .left m, .callerIn m]

/-- A TEST ON THE TABLE: at border k every open public item is one of the ten. -/
def tenB (M : More) (links : List ModelPart) (ps : List VerifiableInference.Desc.Place) (k m : Nat) : Bool :=
  ((pubSets M links ps)[k]?.getD []).all fun q => (ten m).contains q

#print axioms readsThereB_behind
#print axioms liveReqB_behind

end H2K5.Door
