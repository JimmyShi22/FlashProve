-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Road/K4/OwnD2.lean: (D2) OF A SUMCHECK'S OWN ROW, ITS HALF THAT READS NO TYPED LETTER. (D2)
asks that the typed incoming form is the target's reading less the start form's worth in the world
(`SumSaid.row`, OnBytes/Tie/Pv/Lay/SumSaid.lean; `stgT_row`, OwnRows.lean). Here that difference is
written out, for every form and every ledger that shows the form's public part. Statements and
proofs.

  `maskSum H C mask`: over the slots that C names: the coefficient, read, times the slot's factor in
    H, read, times the mask's entry at the slot.
  `entSum C entry`: over the entries of virtual rows that C names: the coefficient, read, times the
    entry.
  `public_less_value`: if H shows t as the public part of C: `gl.val t - C.value gl (H.worldOf gl
  mask entry) = maskSum H C mask - entSum C entry`.
  `d2_of_public`: so (D2) holds for a record p whose target H shows as the public part of its start
    form, if the typed incoming form at m is `maskSum H p.start (mask m) - entSum p.start (entry
    m)`.
  `maskSum_slot`, `entSum_slot`: at the form `Aff.slot j` (a token sumcheck's start form; the first
    gated layer's): the factor under j, read, times the mask's entry at j; and 0.

NO NEW ARGUMENT: `public_value` (OnBytes/Tie/Pv/Att/HearSaid.lean) and the definition of
a form's value.

Limits. THE TYPED HALF IS A PREMISE: that a value's incoming form is this sum is said nowhere here.
That a LATER ledger shows the same public part is `Fo.publicPart_later`. Nothing on (D3),
(D4). Nothing on soundness.
-/
import OnBytes.Tie.Pv.Att.HearSaid
import OnBytes.Desc.First.P1.RoundRead
import Cb.Ld.LdPsc

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Road.K4
open Cb OnBytes OnBytes.Model
open OnBytes.Tie.Pv.Att (public_value shownW)
open OnBytes.Desc.First.P1 (gl)
open OnBytes.Slice (GE)

/-- Over the slots that the form names: coefficient times factor times mask entry. -/
def maskSum (H : Fork) (C : Aff) (mask : ℕ → GE) : GE :=
  (C.slots.toList.map fun x => gl.val x.2 * (gl.val (H.mf.getD x.1 zeroE) * mask x.1)).sum

/-- Over the entries of virtual rows that the form names: coefficient times entry. -/
def entSum (C : Aff) (entry : ℕ → ℕ → ℕ → GE) : GE :=
  (C.ents.toList.map fun x => gl.val x.coef * entry x.tree x.row x.idx).sum

/-- **The public part less the worth.** -/
theorem public_less_value (H : Fork) (C : Aff) (t : E) (h : H.publicPart C = some t)
    (mask : ℕ → GE) (entry : ℕ → ℕ → ℕ → GE) :
    gl.val t - C.value gl (H.worldOf gl mask entry) = maskSum H C mask - entSum C entry := by
  rw [public_value gl H C t h]
  have hs : ∀ l : List (ℕ × E), (l.map (slotValue gl (shownW gl H))).sum -
      (l.map (slotValue gl (H.worldOf gl mask entry))).sum =
      (l.map fun x => gl.val x.2 * (gl.val (H.mf.getD x.1 zeroE) * mask x.1)).sum := by
    intro l
    induction l with
    | nil => simp
    | cons x l ih =>
      simp only [List.map_cons, List.sum_cons]
      rw [← ih]
      simp only [slotValue, Fork.worldOf, shownW]
      ring
  have he : (C.ents.toList.map (Ent.value gl (shownW gl H))).sum = 0 :=
    List.sum_eq_zero fun x hx => by
      obtain ⟨e, _, rfl⟩ := List.mem_map.1 hx
      simp [Ent.value, shownW]
  have he' : (C.ents.toList.map (Ent.value gl (H.worldOf gl mask entry))).sum =
      entSum C entry := rfl
  unfold Aff.value maskSum
  rw [he, he', ← hs C.slots.toList]
  ring

/-- **(D2), from the typed half.** -/
theorem d2_of_public (Y : PscPar GE) (st : Y.St) {p : Psc} {H : Fork}
    (h : H.publicPart p.start = some p.target) (mask : (Y.J → GE) → ℕ → GE)
    (entry : (Y.J → GE) → ℕ → ℕ → ℕ → GE) (m : Y.J → GE)
    (hinc : Y.inc st m = maskSum H p.start (mask m) - entSum p.start (entry m)) :
    Y.inc st m = gl.val p.target - p.start.value gl (H.worldOf gl (mask m) (entry m)) := by
  rw [public_less_value H p.start p.target h, hinc]

theorem maskSum_slot (H : Fork) (j : ℕ) (mask : ℕ → GE) :
    maskSum H (Aff.slot j) mask = gl.val (H.mf.getD j zeroE) * mask j := by
  simp [maskSum, Aff.slot, gl.one]

theorem entSum_slot (j : ℕ) (entry : ℕ → ℕ → ℕ → GE) : entSum (Aff.slot j) entry = 0 := by
  simp [entSum, Aff.slot]

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.public_less_value
#print axioms OnBytes.Road.K4.d2_of_public
#print axioms OnBytes.Road.K4.maskSum_slot
#print axioms OnBytes.Road.K4.entSum_slot
