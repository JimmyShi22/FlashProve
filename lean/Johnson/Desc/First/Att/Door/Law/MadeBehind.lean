-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/Door/Law/MadeBehind.lean: kind K5: THE KIND's TWO PUBLIC ITEMS «K5.okAt» AND «K5.plain» ARE MADE BY THE KIND's BLOCK, SAID AT THE HEARING's RETURN: at the verifier's state after the block has laid what it heard
(behind s att hd G) the two tests with code say yes. Theorems.
  ok_made_behind: from the hearing's return from a ledger with its sizes, and GeoFits g x (the place's shape fits the rounds' plan).
  plain_made_behind: from the hearing's return from a ledger with its sizes, and the yes in front of the public test «K5.readsThere» (it has the array of the reads, one own row, nW columns): the hearing leaves the arrays.
For whom: whoever shows of the table's filling that what the block's row "makes" holds after the block.
Over Door/Law/OkThereTie.lean, Door/Law/PlainThereTie.lean (what the two tests mean), Door/Law/ReadsThereTie.lean (width_of_sheet), Att/K05HearBelow.lean (hear_below), Att/K05BehindLay.lean (behind).
IS IT EMPTY HERE? Where the hearing does not return nothing is said.
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.Door.Law.OkThereTie
import Johnson.Desc.First.Att.Door.Law.PlainThereTie
import Johnson.Desc.First.Att.Door.Law.ReadsThereTie
import Johnson.Desc.First.Att.K05BehindLay
import Johnson.Desc.First.Att.K05HearBelow

set_option autoImplicit false

namespace H2K5.Door
open OnBytes OnBytes.Model
open VerifiableInference.Desc.First (S AttOwn)
open VerifiableInference.Desc.First.Att
open VerifiableInference.Desc.First.Att.P (Geo Heard behind hear hear_below hear_said sized_of_B fork_front)
open K5Law

variable {s : S} {att : AttOwn} {x : Params.AttentionRounds} {rs : List Fmt.RoundView} {hd : Heard} {G : Fork}

/-- **«K5.okAt» is made.** -/
theorem ok_made_behind {g : Geo} (e : s.here = .att att) (hh : hear x (att.F, rs, 0) = some (hd, G, [], 0))
    (hz : s.fork?.any VerifiableInference.Desc.K3.sizedB = true) (gf : P.GeoFits g x) :
    okThereB g (behind s att hd G) = true := by
  rw [fork_front e] at hz
  obtain ⟨b, zG⟩ := heardSlots_of_hear hh (sized_of_B hz) gf
  exact (okThereB_iff g _).2 ⟨G, hd, rfl, rfl, ⟨zG.vp, zG.mf, zG.got⟩, b⟩

/-- **«K5.plain» is made.** -/
theorem plain_made_behind (W : Verify.Public) (ownL : List (ℕ × ℕ)) {A : Attention.Plan} (e : s.here = .att att)
    (hp : W.A[att.L.link / 2]? = some A) (hh : hear x (att.F, rs, 0) = some (hd, G, [], 0))
    (hz : s.fork?.any VerifiableInference.Desc.K3.sizedB = true) (hv : readsThereB W ownL s = true) :
    plainThereB A.iU3 A.nW (behind s att hd G) = true := by
  rw [fork_front e] at hz
  obtain ⟨_, _, _, _, hs, _, _⟩ := hear_said hh (sized_of_B hz)
  obtain ⟨_, bl⟩ := hear_below hh (sized_of_B hz)
  obtain ⟨T, hT, _, hK⟩ := width_of_sheet W ownL s att e A hp hv
  exact (plainThereB_iff A.iU3 A.nW _).2 ⟨G, hd, rfl, rfl, heardPlain_of_said hs, T, by rw [bl.trees]; exact hT, hK⟩

end H2K5.Door

#print axioms H2K5.Door.ok_made_behind
#print axioms H2K5.Door.plain_made_behind
