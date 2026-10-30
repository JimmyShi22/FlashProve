-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/Riders/ObjectsAtLot.lean: THE BLOCK THAT THE LOOKUPS' LOT SEATS AT THE CALLS' PLACE
OF A LINK WITHOUT A CALLER's READERS (K3.theStated, Johnson/Desc/First/Look/K3Stated.lean; at a
layers' link the readers give nothing) STATES JUST THE TWO RUNS "objects", "guests", AN ObjRun AND A
GuestRun (Johnson/Road/K4/Riders/Objects.lean). A statement and its proof: the three makes
theStated, theWhole, theOwn unfolded down to the kind's own block, where
Johnson/Road/K4/Riders/ObjectsAtK3.lean's via_runs speaks.

  `piece_ne`: a link's two lookups stand at two numbers.
  `stated_runs`: the statement.
No new argument.
**Limits.** Premises: the make returns a block b; the address names link i and the calls' piece of
it; readers i gives nothing. BLOCK NUMBER 1 OF A SEATED LINK's HEARING BLOCKS IS NOT THIS b: its
runs are b's with the driver's guard behind each: Johnson/Road/K4/Riders/ObjectsGuarded.lean, which
names what is owed there. claim is the literal "the form a as a claim". Nothing on soundness.
K04_law, the law of K4's block itself, IS NOT PROVED.


-/
import Johnson.Road.K4.Riders.ObjectsAtK3
import Johnson.Desc.First.Look.K3Stated

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Desc.First.K4.Riders

open OnBytes OnBytes.Model
open VerifiableInference.Desc (Claim Block Place roundlessBlock K3.theStated K3.theWhole K3.theOwn
  K3.pieceAt K3.Readers)
open VerifiableInference.Desc.First (S)

/-- A link's two lookups stand at two numbers. -/
theorem piece_ne (X : Verify.Public) (i : Nat) :
    (K3.pieceAt X i false != K3.pieceAt X i true) = true := by
  unfold K3.pieceAt
  split <;> rfl

/-- **The lot's block at the calls' place of a link without a caller's readers.** -/
theorem stated_runs {readers : Nat → Option (K3.Readers S)} {X : Verify.Public} {codes : Codes}
    {shape : Params.ReqShape} {a : Place} {b : Block S Claim} {i : Nat}
    (h : K3.theStated lit readers X codes shape a = some b) (hl : a.link = some i)
    (hp : a.piece = K3.pieceAt X i false) (hr : readers i = none) :
    ∃ R1 R2, b.claims = [("objects", R1), ("guests", R2)] ∧ ObjRun R1 ∧ GuestRun R2 := by
  unfold K3.theStated at h
  obtain ⟨b1, hw, h⟩ := Option.bind_eq_some_iff.1 h
  have e1 : b1 = b := by simpa [hl, hp, hr] using h
  subst e1
  unfold K3.theWhole at hw
  obtain ⟨b0, ho, rfl⟩ := Option.map_eq_some_iff.1 hw
  have key : ∃ R1 R2, b0.claims = [("objects", R1), ("guests", R2)] ∧ ObjRun R1 ∧ GuestRun R2 := by
    unfold K3.theOwn at ho
    split at ho
    · cases ho
    · rw [hl, Option.bind_some] at ho
      obtain ⟨dg, _, hd⟩ := List.exists_of_findSome?_eq_some ho
      cases dg with
      | true =>
        rw [if_pos (by rw [hp]; exact piece_ne X i)] at hd
        cases hd
      | false =>
        rw [if_neg (by rw [hp]; simp)] at hd
        obtain ⟨p, _, hd⟩ := Option.bind_eq_some_iff.1 hd
        obtain ⟨sent, _, hd⟩ := Option.bind_eq_some_iff.1 hd
        obtain ⟨laid, _, hd⟩ := Option.bind_eq_some_iff.1 hd
        obtain ⟨key, _, rfl⟩ := Option.map_eq_some_iff.1 hd
        exact via_runs a.piece laid sent p
  obtain ⟨R1, R2, e, h1, h2⟩ := key
  refine ⟨R1, R2, ?_, h1, h2⟩
  split
  · exact (List.append_nil _).trans e
  · exact e

end OnBytes.Desc.First.K4.Riders

#print axioms OnBytes.Desc.First.K4.Riders.piece_ne
#print axioms OnBytes.Desc.First.K4.Riders.stated_runs
