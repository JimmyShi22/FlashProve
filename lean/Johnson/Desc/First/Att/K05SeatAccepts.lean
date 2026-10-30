-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/K05SeatAccepts.lean: THE SEAM's EMPTINESS AT THE SEAT THAT SITS: where the
kind's
piece at the hearing's seat seatSO (Att/SeatO.lean) puts out: seam_accepts (Att/K05SeamBack.lean)
with
its premises on the seat read off the first chain's record.

Main names:
  `seatSO_lays`: where an attention segment is open, the lookup has laid what it heard, the
  segment's
    own rounds have not been heard yet and the record bears no mark: seatSO.lay returns, whatever is
    heard.
  `ReadyO s`: these four; no count of rows waits; the segment's ledger is Sized and has room for the
    kind's slots.
  `seam_accepts_SO`: **at every record with ReadyO, at every oracles, the kind's piece at seatSO
  puts
    out at EVERY written transcript whose work passes**, if planOk p = true.
  `seam_member_SO`: so there are τ and b.

Limits. That a record with ReadyO stands in front of the kind's block in a run of the first chain is
not shown: no record is built here. It is no honest run: the hearing tests the shape and the room,
nothing of the values. planOk is evaluated at no real place here.
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.K05SeamBack
import Johnson.Desc.First.Att.SeatO

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Att.P
open Iop OnBytes OnBytes.Model OnBytes.Model.Road OnBytes.Flat OnBytes.Maker
open VerifiableInference.Desc.Part
open VerifiableInference.Desc.Sound (Frame Piece)
open _root_.Run (ckP)

/-- Where the hearing's seat lays. -/
theorem seatSO_lays {s : First.S} {a : First.AttOwn} {g : Forest.Heard} (hh : s.here = .att a)
    (hg : a.g = some g) (h5 : a.heard5 = none) (hf : s.failed = none) (h : Heard) (G : Fork) :
    ∃ s', seatSO.lay s h G = some s' := by
  refine ⟨{ s with rowsOwed := none, here := .att { a with F := G, heard5 := some h } }, ?_⟩
  show (match s.here with
    | .att a => a.g.bind fun _ =>
      (First.S.hear5? { s with rowsOwed := none, here := .att { a with F := G } } h).toOption
    | _ => none) = _
  rw [hh]
  simp only [hg, Option.bind_some, First.S.hear5?, First.S.hear5, h5, Option.isSome_none,
    Bool.false_eq_true, if_false, First.S.unmarked, hf, Except.toOption]

/-- The record is ready for the kind's hearing. -/
structure ReadyO (p : Par) (s : First.S) : Prop where
  open_ : ∃ a g, s.here = .att a ∧ a.g = some g ∧ a.heard5 = none ∧ Sized a.F ∧
    MaskedSum.Free a.F a.F.next (slotsOf (script p.own))
  clean : s.failed = none
  none_ : s.noneWaits = true

section
variable {Cl W : Type} {F : Frame}

/-- **The kind's piece at the seat that sits puts out at every written transcript whose work
passes.** -/
theorem seam_accepts_SO
    (claims : List (String × (Nat → First.S → Except String (List Cl × First.S)))) (p : Par)
    (base : ℕ) (err : Err (uLT (ckP .two) (written p))) (hpl : planOk p = true)
    (a : First.S × F.E.Str) (hr : ReadyO p a.1) (τ : Tr (uLT (ckP .two) (written p)))
    (hp : passT (ckP .two) (written p) (rhoT (ckP .two) (written p) τ) = true) :
    ∃ b, (k5Piece (W := W) (ckP .two) F seatSO claims p base (written p) err).ior.red.out a τ =
      some b := by
  obtain ⟨at_, g, hh, hg, h5, hz, hfree⟩ := hr.open_
  refine seam_accepts seatSO claims p base err hpl a (F0 := at_.F) ?_ ?_ hz hfree
    (seatSO_lays hh hg h5 hr.clean) τ hp
  · show (if a.1.noneWaits then none else a.1.rowsOwed) = none
    rw [hr.none_]
    rfl
  · show (match a.1.here with
      | .att a => some a.F
      | _ => none) = some at_.F
    rw [hh]

theorem seam_member_SO
    (claims : List (String × (Nat → First.S → Except String (List Cl × First.S)))) (p : Par)
    (base : ℕ) (err : Err (uLT (ckP .two) (written p))) (hpl : planOk p = true)
    (a : First.S × F.E.Str) (hr : ReadyO p a.1) :
    ∃ τ b, (k5Piece (W := W) (ckP .two) F seatSO claims p base (written p) err).ior.red.out a τ =
      some b :=
  ⟨passing (ckP .two) (written p), seam_accepts_SO claims p base err hpl a hr _ (passing_passes _ _)⟩

end

end VerifiableInference.Desc.First.Att.P

#print axioms VerifiableInference.Desc.First.Att.P.seatSO_lays
#print axioms VerifiableInference.Desc.First.Att.P.seam_accepts_SO
#print axioms VerifiableInference.Desc.First.Att.P.seam_member_SO
