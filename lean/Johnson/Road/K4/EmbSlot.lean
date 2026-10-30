-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/EmbSlot.lean: the clause slot of EmbDict (Johnson/Road/K4/EmbPort.lean), on the
tape's side: in the first group, in the world of every ledger later than the one behind the laying
of the embedding's hidden value, the hidden value under the slot sVE is the first word that the
round at the merge's cut sent, read, less the mask at the slot's number.

Main names:
  `emb_slot`: the tape's side, from the record LedG (Johnson/Road/K4/OwnLedgersG.lean).
  `embSlot_of_led`: the clause, at library-side letters sh and mu.
Limits. LedG is a premise here (own_ledG has it where the hearing returns). TWO TIES STAY PREMISES
of embSlot_of_led, each between two texts' letters: that the library-side scalar sh is the reading
of that word; that the library-side mask entry mu is the mask at the slot's number. One direction.
Nothing on soundness or on hiding.


-/
import Johnson.Road.K4.OwnLedgersG
import Johnson.Road.K4.SlotsAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4
open OnBytes OnBytes.K.Kc OnBytes.Desc.First.K4
open OnBytes.Model hiding layerObject stackRounds wsForkLin
open OnBytes.Model.Layer hiding shownRun hearNorms hearTerms joinStart hearStack hearGated
  claimsNorms claimRowBatch claimsTerms claimsEnds claimsGated claimsOneHot claimsPlanes
  claimEmbedding freeSlotTest
open OnBytes.Desc.First.P1 (sentOf claimsIn_spec)

variable {K : Type} [Field K] (ρ : Reading K) (mask : ℕ → K) (entry : ℕ → ℕ → ℕ → K)
  {P : Pub} {hp : HPlan2} {g : ℕ} {fo : Forest.Heard} {o : Own} {F G : Fork} {t0 u : Tape}
  {H1 : Heard} {hd2 : Level} {tT : Tsc} {F4 F7 F8 G1 G1' G2 G3 G3' G4 G5 : Fork} {u5 : Tape}

/-- **Under the embedding's slot**, in the world of every ledger later than G5. -/
theorem emb_slot (L : LedG P hp g fo o F G t0 u H1 hd2 tT F4 F7 F8 G1 G1' G2 G3 G3' G4 G5 u5)
    (hg : (g == 0) = true) {Hl : Fork} (lH : Fo.Later G5 Hl) :
    (Hl.worldOf ρ mask entry).slot o.sVE =
      ρ.val ((sentOf ((ksOf P hp).tcW (t0.drop (k0 g)))).getD 0 zeroE) - mask o.sVE := by
  have e6 := L.front
  unfold mergeFront at e6
  rw [if_pos hg] at e6
  obtain ⟨hj, v, hs, -, -, hrun⟩ := claimsIn_spec e6
  have hG4' : PscRun.Sized ({ G4 with next := G4.next + 1 } : Fork) := L.sG4
  have s := run_slot ρ mask entry hG4' hrun lH (i := 0) (by omega)
  have q := hideRun_shown hG4' hrun rfl lH 0 (by omega)
  rw [Nat.add_zero] at s q
  rw [ρ.one, one_mul] at s
  have e1 : v.toList.getD 0 zeroE =
      (sentOf ((ksOf P hp).tcW (t0.drop (k0 g)))).getD 0 zeroE := by
    rw [← q, ← hj]
    exact (L.emb hg).2 Hl lH
  rw [hj, s, e1]

/-- The clause slot of EmbDict, in such a world. -/
theorem embSlot_of_led
    (L : LedG P hp g fo o F G t0 u H1 hd2 tT F4 F7 F8 G1 G1' G2 G3 G3' G4 G5 u5)
    (hg : (g == 0) = true) {Hl : Fork} (lH : Fo.Later G5 Hl) {sh mu : K}
    (hsh : sh = ρ.val ((sentOf ((ksOf P hp).tcW (t0.drop (k0 g)))).getD 0 zeroE))
    (hmu : mu = mask o.sVE) :
    (Hl.worldOf ρ mask entry).slot o.sVE = sh - mu := by
  rw [emb_slot ρ mask entry L hg lH, hsh, hmu]

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.emb_slot
#print axioms OnBytes.Road.K4.embSlot_of_led
