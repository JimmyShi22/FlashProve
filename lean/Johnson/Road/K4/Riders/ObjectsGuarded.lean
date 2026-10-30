-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/Riders/ObjectsGuarded.lean: THE LOOKUP's TWO RUNS OF CLAIMS BEHIND THE DRIVER's
GUARD (Block.guarded, Johnson/Desc/SeatGuard.lean: behind each run the guard asks that
a part of the verifier's state is as it was in front, and refuses otherwise) ARE STILL AN ObjRun AND
A GuestRun (Johnson/Road/K4/Riders/Objects.lean), wherever the guard's test says yes at two states
with one field out. And so the four premises on the runs of the structure ObjAsks
(Johnson/Road/K4/Riders/ObjectsAtMeans.lean) hold at a link whose block number 1 is such a guarded
block. Statements and proofs.

  `guardRun same R`: the guard's text around a run R, as Block.guarded has it.
  `putFork_out`: laying a ledger leaves the state's field out.
  `objRun_guarded`, `guestRun_guarded`: the two runs behind the guard.
  `guarded_claims`: Block.guarded's list of runs, by its own text.
  **`runs_at_guarded`**: l.hear[1]? = some B · B's runs are b's behind the guard · b states just an
    ObjRun "objects" and a GuestRun "guests": then both are found in K9.statesOfLink l 1 under their
    names, an ObjRun and a GuestRun.
No new argument.
**Limits.** Premises: hsame (the guard's test says yes wherever out is the same: true of a test that
compares the reply in out) · hb (block number 1 of the link's hearing blocks is B) · hcl (B's list
of runs is b's behind the guard): NEITHER hb NOR hcl IS SHOWN OF A SEATED LINK HERE: what else a
driver lays around b is its make's. Nothing on soundness. K04_law, the law of K4's block itself, IS
NOT PROVED.


-/
import Johnson.Road.K4.Riders.ObjectsAtK3
import Johnson.Desc.SeatGuard
import Johnson.Desc.First.Batch.ReadersOfLink

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Desc.First.K4.Riders

open OnBytes OnBytes.Model
open VerifiableInference.Desc (Claim Block Link Place seatSame K9.statesOfLink)
open VerifiableInference.Desc.First (S)

/-- The guard's text around a run. -/
def guardRun (same : S → S → Bool) (R : Nat → S → Except String (List Claim × S)) :
    Nat → S → Except String (List Claim × S) :=
  fun n t => (R n t).bind fun y => (seatSame same t y.2).map fun _ => y

/-- Laying a ledger leaves the state's field out. -/
theorem putFork_out (s : S) (F : Fork) : (s.putFork F).out = s.out := by
  unfold S.putFork
  split
  · rfl
  · rfl
  · split <;> rfl
  · rfl

variable {same : S → S → Bool} {R : Nat → S → Except String (List Claim × S)}

theorem objRun_guarded (h : ObjRun R) (hsame : ∀ t s : S, s.out = t.out → same t s = true) :
    ObjRun (guardRun same R) := by
  intro s F g hF hg
  show ((R 0 s).bind fun y => (seatSame same s y.2).map fun _ => y) = _
  rw [h s F g hF hg]
  show ((seatSame same s (s.putFork (F.paid g.owedObjects))).map fun _ => _) = _
  unfold seatSame
  rw [if_pos (hsame s _ (putFork_out s _))]
  rfl

theorem guestRun_guarded (h : GuestRun R) (hsame : ∀ t s : S, s.out = t.out → same t s = true) :
    GuestRun (guardRun same R) := by
  intro s
  show ((R 0 s).bind fun y => (seatSame same s y.2).map fun _ => y) = _
  rw [h s]
  show ((seatSame same s s).map fun _ => _) = _
  unfold seatSame
  rw [if_pos (hsame s s rfl)]
  rfl

/-- Block.guarded's list of runs, by its own text. -/
theorem guarded_claims (but : Place → Bool) (b : Block S Claim) :
    (b.guarded same but).claims = b.claims.map fun c => (c.1, guardRun same c.2) := rfl

/-- **The four premises on the runs, at a link whose block number 1 is a guarded block.** -/
theorem runs_at_guarded {l : Link S Claim} {B b : Block S Claim} (hb : l.hear[1]? = some B)
    (hcl : B.claims = b.claims.map fun c => (c.1, guardRun same c.2))
    (hsame : ∀ t s : S, s.out = t.out → same t s = true)
    (hr : ∃ R1 R2, b.claims = [("objects", R1), ("guests", R2)] ∧ ObjRun R1 ∧ GuestRun R2) :
    ∃ runO runG,
      (K9.statesOfLink l 1).find? (fun r => r.1 == "objects") = some ("objects", runO) ∧
      ObjRun runO ∧
      (K9.statesOfLink l 1).find? (fun r => r.1 == "guests") = some ("guests", runG) ∧
      GuestRun runG := by
  obtain ⟨R1, R2, e, h1, h2⟩ := hr
  have es : K9.statesOfLink l 1 =
      [("objects", guardRun same R1), ("guests", guardRun same R2)] := by
    show ((l.hear[1]?).map fun x => x.claims).getD [] = _
    rw [hb]
    show B.claims = _
    rw [hcl, e]
    rfl
  refine ⟨guardRun same R1, guardRun same R2, ?_, objRun_guarded h1 hsame, ?_,
    guestRun_guarded h2 hsame⟩
  · rw [es]
    exact find_objects _ _
  · rw [es]
    exact find_guests _ _

end OnBytes.Desc.First.K4.Riders

#print axioms OnBytes.Desc.First.K4.Riders.putFork_out
#print axioms OnBytes.Desc.First.K4.Riders.objRun_guarded
#print axioms OnBytes.Desc.First.K4.Riders.guestRun_guarded
#print axioms OnBytes.Desc.First.K4.Riders.guarded_claims
#print axioms OnBytes.Desc.First.K4.Riders.runs_at_guarded
