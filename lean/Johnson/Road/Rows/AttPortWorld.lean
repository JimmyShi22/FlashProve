-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Road/Rows/AttPortWorld.lean: the two ties between the verifier's world and the library-side
entries of an attention sub-proof (SlotAt, LateAt), in the world that committed entries give at a
state of the verifier.

Johnson/Road/Rows/AttPortCl.lean and the files beside it stand under two premises on a world W.
SlotAt: the hidden value under an end value's slot is what was shown, less the last coordinate times
the mask entry. LateAt: the late entry of a name is the entry of the vector of tables at the name's
place. This file takes for W the world portWorld of OnBytes/Tie/Pv/Led/LedPort.lean: the world that
the committed entries, early ones m and late ones u, give at a state H under a lay (each entry has
an address: a cell of an array, or the mask entry of a slot). There both premises follow from facts
on addresses and on what H holds, for all m and u.

Main definitions.
 - lateOf good at' inj: the record of the late entries' names that a map at' from names to late
   entries gives, if at' is one-to-one on the good names.
 - U3Lay: what is asked of the lay and of the state on the vector of tables: the virtual row in
   which entry number e lies has the weight 1 on one row of the array and 0 on the others, and the
   late entry of a good name has the address of that cell.
Main theorems.
 - slotAt_port: SlotAt, from three facts: what was shown is what H holds for the slot; the last
   coordinate is the factor that H holds for the slot; the mask entry's address is the slot's.
 - lateAt_port: LateAt, from U3Lay, for all m and u.

What is not claimed. That a run's state and lay meet the premises. That the map from names to
entries of the vector is one-to-one: it is tried at the small configuration in
Johnson/Road/Rows/TestAttPlaces.lean. Nothing is said about probabilities or about hiding. The
program does not import this file.


-/
import Johnson.Road.Rows.AttPortCl
import OnBytes.Tie.Pv.Led.LedLate

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Road.Rows

open OnBytes.Model (Reading Fork)
open OnBytes.Attention (Heard)
open OnBytes.Road.Hd (rdW)
open Inst.Model.AttSeg (Raw)
open Cb.Pv.Att (PlainSc)
open Cb.Pv.Att.End (LateLay AttTab)

/-! ## A record of names from a one-to-one map -/

section Names
variable {Tn J₂ : Type} [Inhabited (Tn × Raw)]

open Classical in
/-- The record of the late entries' names that a map from names to late entries gives. The name of a
late entry is the good name that is mapped to it, if there is one. -/
noncomputable def lateOf (good : Tn × Raw → Prop) (at' : Tn × Raw → J₂)
    (inj : ∀ x y, good x → good y → at' x = at' y → x = y) : LateLay Tn J₂ where
  nm := fun j => if h : ∃ x, good x ∧ at' x = j then h.choose else default
  at' := at'
  good := good
  ok := fun x hx => by
    have h : ∃ y, good y ∧ at' y = at' x := ⟨x, hx, rfl⟩
    rw [dif_pos h]
    exact inj _ _ h.choose_spec.1 hx h.choose_spec.2

end Names

variable {K : Type} [Field K]

/-! ## The slots -/

/-- SlotAt in the world of the committed entries. -/
theorem slotAt_port [Fintype K] (ρ : Reading K) (T : PlainSc K) {J₂ : Type} [Fintype T.J]
    [Fintype J₂] (Y' : Lay (T.J ⊕ J₂)) (H : Fork) (o : T.our.par.Out) (x : T.J ⊕ J₂ → K) (j : ℕ)
    (a : T.A) (vals : o.vals a = ρ.val (H.vp.getD j zeroE))
    (beta : T.our.lst o.st (T.our.par.hp o.st o.pt) = ρ.val (H.mf.getD j zeroE))
    (addr : Y'.addr (.inl (T.cAt a)) = .mask j) :
    SlotAt (portWorld ρ Y' H x) T o x j a := by
  unfold SlotAt
  rw [portWorld_slot, Y'.maskAt_addr x j _ addr, vals, beta]

/-! ## The late entries -/

/-- What is asked of the lay and of the state on the vector of tables. row e: the row of the array
in which entry number e of the vector lies. -/
structure U3Lay (ρ : Reading K) {J₁ J₂ : Type} (Y' : Lay (J₁ ⊕ J₂)) (H : Fork) (h : Heard) (K3 : ℕ)
    (Y : LateLay AttTab J₂) (tabOf : AttTab → ℕ) (place : AttTab → Raw → ℕ) (row : ℕ → ℕ) :
    Prop where
  /-- the virtual rows of the vector are rows of the array -/
  unit : ∀ T r, Y.good (T, r) →
    rowWeight ρ H.trees h.iU3 ((tabOf T + place T r) / K3) =
      fun k => if k = row (tabOf T + place T r) then 1 else 0
  /-- the late entry of a good name lies at the name's place -/
  addr : ∀ T r, Y.good (T, r) → Y'.addr (.inr (Y.at' (T, r))) =
    .cell h.iU3 (row (tabOf T + place T r)) ((tabOf T + place T r) % K3)

/-- LateAt in the world of the committed entries, for all early entries m and late entries u. -/
theorem lateAt_port (ρ : Reading K) {J₁ J₂ : Type} [Fintype J₁] [Fintype J₂]
    (Y' : Lay (J₁ ⊕ J₂)) (H : Fork) (h : Heard) (K3 : ℕ) (Y : LateLay AttTab J₂)
    (tabOf : AttTab → ℕ) (place : AttTab → Raw → ℕ) (row : ℕ → ℕ)
    (U : U3Lay ρ Y' H h K3 Y tabOf place row) (m : J₁ → K) (u : J₂ → K) :
    LateAt (portWorld ρ Y' H (Sum.elim m u)) h K3 Y tabOf place u := by
  intro T r hr
  show _ = (portWorld ρ Y' H (Sum.elim m u)).entry h.iU3 ((tabOf T + place T r) / K3)
    ((tabOf T + place T r) % K3)
  rw [portWorld_entry_late ρ Y' H m u h.iU3 _ (row (tabOf T + place T r)) _ (Y.at' (T, r))
    (U.unit T r hr) (U.addr T r hr)]

end OnBytes.Road.Rows

#print axioms OnBytes.Road.Rows.lateOf
#print axioms OnBytes.Road.Rows.slotAt_port
#print axioms OnBytes.Road.Rows.lateAt_port
