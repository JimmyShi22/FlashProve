-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K5/Honest/Law/FrameFacts.lean: CONDITIONAL: four facts on the verifier's state just
behind the lay of an attention segment's own rounds, which the laws on the array of the segment's
tables spend, paid from one premise of the library on the state in front (`FrontAll`,
Johnson/Desc/First/Att/K05BehindWorth.lean) and the return of the hearing.

The four: the array of the tables stands in the open ledger; it has the planned number of columns
there; the open link names it; it is of the segment's second sending.

Main names:
  `frame_of_front`: the four facts at the state behind the lay.
  `readsStated_behind`: so the world in which the library's sentence on forms that name a later
    array evaluates them reads the array of the tables as the stated function
    (`ReadsStated`, Johnson/Desc/K5/Honest/Law/Planes.lean), at that state.
  `planes_say_behind`: so what the forms for the planes are worth in that world (`planes_say`).

Who pays `FrontAll`: the library has it from a list of tests with code on the state in front
(`frontAll_of_door`, Johnson/Desc/First/Att/K05FrontOfDoor.lean). That these tests say yes at a
state of an honest run is not shown here. That they follow from the promise which the table of the
verifier's blocks carries in front of this block is not shown in this file;
Johnson/Desc/K5/Honest/Law/DoorNarrow.lean (`doorYes_narrow`) and DoorAtHead.lean (`door_at_head`,
`front_at_head`) show it under premises named in their heads, not from the promise alone: among them
that eight public items are open in the caller's list, which is not decided at the table's own list.
Limits. At the state just behind the lay alone: that later blocks leave the four facts is not said
here. All three are conditional.
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.K5.Honest.Law.Planes
import Johnson.Desc.First.Att.K05BehindWorth

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace H2K5.Honest
open OnBytes OnBytes.Model OnBytes.Params
open VerifiableInference.Desc (First.S First.AttOwn)
open VerifiableInference.Desc.First.Att
open VerifiableInference.Desc.First.Att.P (FrontAll U3At behind partAt hear)
open VerifiableInference.Desc.First.Look (Sent)
open VerifiableInference.Desc.K9L (Bound)
open VerifiableInference.Desc.Sound (GQ Stated second worldOwn)

section
variable {x : VerifiableInference.Desc.First.Look.Place} {A : Attention.Plan} {D : Sent}
  {own : List (ℕ × ℕ)} {ps : List (ℕ × (ℕ × ℕ))} {qs : List (ℕ × OracleShape)} {hi : ℕ}
  {gL : Forest.Heard} {s : First.S} {a : First.AttOwn} {xr : Params.AttentionRounds}
  {rs : List Fmt.RoundView} {h : P.Heard} {G : Fork}

/-- **Four facts at the state behind the lay.** Conditional: Fa: the library's premise on the
state in front; hs: an attention segment is open there; hh: the hearing of the segment's own rounds
returns from that segment's ledger. -/
theorem frame_of_front (Fa : FrontAll x A D own ps qs hi gL s) (hs : s.here = .att a)
    (hh : hear xr (a.F, rs, 0) = some (h, G, [], 0)) :
    U3At A (P.plannedK A) G ∧
      (P.seatCO (P.parCOf A)).cols (behind s a h G) = some (P.plannedK A) ∧
      ∃ b, a.L.arrayOf[A.iU3]? = some b ∧ second (behind s a h G) b = true := by
  have hl : P.seatSO.ledger s = some a.F := by
    show (match s.here with | .att a => some a.F | _ => none) = _
    rw [hs]
  obtain ⟨hz, _, T, hT, hK, hW, hR⟩ := Fa.ledger a.F hl
  obtain ⟨_, bl⟩ := P.hear_below hh hz
  have hTG : G.trees[A.iU3]? = some T := by
    rw [bl.trees]
    exact hT
  have hL : s.link? = some a.L := by
    unfold First.S.link?
    rw [hs]
  obtain ⟨h1, h2⟩ := P.secL_gives (Fa.sec a.L hL) (s := behind s a h G) P.segAt_behind rfl
  obtain ⟨b, hb⟩ := Option.isSome_iff_exists.1 h1
  refine ⟨⟨T, hTG, hK, hW, hR⟩, ?_, b, hb, h2 b hb⟩
  show (G.trees[A.iU3]?).map (·.K) = _
  rw [hTG, ← hK]
  rfl

/-- **The world of the library's sentence reads the array of the tables as the stated function,
behind the lay.** Conditional: as above, and hSt: the letter St reads that array as the stated
function at the state behind the lay (paid by `hSt_of_arm`,
Johnson/Desc/First/Att/K05StatedArm.lean). -/
theorem readsStated_behind (Fa : FrontAll x A D own ps qs hi gL s) (hs : s.here = .att a)
    (hh : hear xr (a.F, rs, 0) = some (h, G, [], 0)) {St : Stated}
    (hSt : P.StatedAtt St A (K5Law.funsAt A) (behind s a h G)) (late : List (ℕ × E × E))
    (Dt : Bound GQ) :
    ∃ b, ReadsStated A (behind s a h G) Dt b
      (worldOwn (partAt s a G none) late (St.at1 (behind s a h G) Dt)) := by
  obtain ⟨_, _, b, hb, h2⟩ := frame_of_front Fa hs hh
  exact ⟨b, readsStated_own hSt (a := partAt s a G none) hb h2 late Dt⟩

/-- **What the forms for the planes are worth in that world.** Conditional: as above, and hA, hp,
hr as in `planes_say`. -/
theorem planes_say_behind (Fa : FrontAll x A D own ps qs hi gL s) (hs : s.here = .att a)
    (hh : hear xr (a.F, rs, 0) = some (h, G, [], 0)) {St : Stated}
    (hSt : P.StatedAtt St A (K5Law.funsAt A) (behind s a h G)) (hA : K5Law.OfPlan A)
    (hp : K5Law.PosG (P.geoOf A.S)) {r : (ℕ → ℕ → Option Aff) × (ℕ → Option Aff)}
    (hr : P.readersOfO A (behind s a h G) = some r) (late : List (ℕ × E × E)) (Dt : Bound GQ) :
    ∃ lk, (P.seatCO (P.parCOf A)).look (behind s a h G) = some lk ∧
      (∀ e col f, r.1 e col = some f →
        f.value Reading.gl (worldOwn (partAt s a G none) late (St.at1 (behind s a h G) Dt)) =
          planeSum A.S (matsAt A (behind s a h G) Dt) (if e == 0 then lk.phiB0 else lk.phiB1)
            col) ∧
      ∀ col f, r.2 col = some f →
        f.value Reading.gl (worldOwn (partAt s a G none) late (St.at1 (behind s a h G) Dt)) =
          planeSum A.S (matsAt A (behind s a h G) Dt) lk.phiP col := by
  obtain ⟨b, hW⟩ := readsStated_behind Fa hs hh hSt late Dt
  exact planes_say A hA hp hr (frame_of_front Fa hs hh).2.1 hW

end

end H2K5.Honest

#print axioms H2K5.Honest.frame_of_front
#print axioms H2K5.Honest.readsStated_behind
#print axioms H2K5.Honest.planes_say_behind
