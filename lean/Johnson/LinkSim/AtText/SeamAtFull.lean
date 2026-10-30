-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/LinkSim/AtText/SeamAtFull.lean: at the full-size parameters, the schedule of the link's
proximity test, and the fact that every position the verifier asks of a tree of the prover is in it.
Terms: Johnson/LinkSim/Spec.lean; for the prover's algorithm, Johnson/LinkSim/AtText/Defs.lean.

What this file proves. The rounds' description is dsFull. Each closed fact is checked by evaluation
in Lean's kernel, and only public numbers occur in the statements.
  schF          the schedule of the link's proximity test (sched, SeamGroups.lean): for each of its
                five stages, the round that sends the stage's tree, the round whose verifier
                challenges open that tree, and the tree's depth.
  fr_sched      its value: (1, 16, 24), (15, 24, 21), (23, 31, 17), (30, 38, 13), (37, 40, 14). So
                the first stage's tree is sent in round 1, opened by round 16, and has depth 24.
  fr_wantOk     the test wantOkL (SeamGroups.lean) accepts dsFull with this schedule.
  fr_wantNo     a control that checks that this test can fail: with the last entry removed from the
                schedule, wantOkL rejects.
  fr_wantTie    hence WantTie holds at dsFull for every list of verifier challenges (one entry a
                round): every position that the challenges ask of a tree of the prover is in the
                schedule, with the round that sent that tree.

How it fits. fr_wantTie is used in the proof of homeExact (Johnson/LinkSim/AtHome/Home.lean):
Johnson/LinkSim/AtHome/HomeTies.lean uses it to meet the premise WantTie at homeR b Z (home_want).

Limits.
- Everything is at the full-size parameters alone.

Notes. Each closed fact raises a limit of elaboration (Johnson/LinkSim/Spec.lean, "maxRecDepth").
Terms: lean/GLOSSARY.md.

-/
import Johnson.LinkSim.AtText.SeamGroups
import Johnson.Prover.Link.ChainSeats

set_option autoImplicit false

noncomputable section

namespace OnBytes.LinkSim.Seam
open OnBytes.Flat (dsFull)
open _root_.Desc.K15 (frP p12Of)

/-- The proximity test's schedule at the full-size parameters: for each stage, (the round that sends
its tree, the round whose challenges open it, the tree's depth). -/
def schF : List (ℕ × ℕ × ℕ) :=
  match (p12Of frP).nums.stages with
  | first :: rest => sched rest first 6 1
  | [] => []

set_option maxRecDepth 100000 in
/-- The schedule's value at the full-size parameters, checked by evaluation in Lean's kernel. -/
theorem fr_sched :
    schF = [(1, 16, 24), (15, 24, 21), (23, 31, 17), (30, 38, 13), (37, 40, 14)] := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The test wantOkL accepts the full-size rounds' description dsFull with the schedule schF. -/
theorem fr_wantOk : wantOkL dsFull schF 0 dsFull = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- A control that checks that the test can fail: without the schedule's last entry, wantOkL
rejects dsFull. -/
theorem fr_wantNo : wantOkL dsFull schF.dropLast 0 dsFull = false := by decide +kernel

/-- **Every position that the verifier's challenges ask of a tree of the prover is in the
schedule**, for every list of challenges. -/
theorem fr_wantTie (first : Fmt.M1.Stage) (rest : List Fmt.M1.Stage)
    (hs : (p12Of frP).nums.stages = first :: rest) (Ds : List Fmt.Drawn) :
    WantTie dsFull (sched rest first 6 1) Ds := by
  have h := fr_wantOk
  unfold schF at h
  rw [hs] at h
  exact wantTie_of_ok dsFull _ Ds h

end OnBytes.LinkSim.Seam

#print axioms OnBytes.LinkSim.Seam.fr_sched
#print axioms OnBytes.LinkSim.Seam.fr_wantOk
#print axioms OnBytes.LinkSim.Seam.fr_wantNo
#print axioms OnBytes.LinkSim.Seam.fr_wantTie
