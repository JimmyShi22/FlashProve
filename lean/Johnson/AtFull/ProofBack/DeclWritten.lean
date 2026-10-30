-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/ProofBack/DeclWritten.lean: for three plans whose rounds are the written rounds'
entries and which have no other entry, the value of `Johnson.G.OfPlan.fileOf` at the proof file's
written values of the full size (Johnson/AtFull/ProofBack/Decl.lean) IS THE WRITTEN LIST OF DECLARED
ROUNDS: the 136 values `VerifiableInference.PlanWritten.declRecsFull`
(Johnson/Unfolds/DeclRecsLit.lean) along the written rounds' own runs (Johnson/G/DryProofLit.lean).

Definition.
  `openB d`: the round opens a tree or a stored tree.
Statements.
  `ents`, `quiet`, `same`: BY THE KERNEL, on the 136 values: their entries are those of the 136
    distinct written rounds; a value that draws no positions opens nothing; a value draws positions
    just if it opens something.
  `map_runs`, `decl_of`: along ANY runs: from one equation (a premise there): what the values that
    open something open, along these runs, is the given lists: `fillL` at the written entries and
    these lists is the values along the runs. By `Johnson.Unfolds.fillL_eq_of` and
    Johnson/G/Runs.lean.
  `plans0`, `plans1`, `plans2`: BY THE KERNEL, behind the laws of Johnson/Unfolds/ on Lean's
    library: that equation at each chain's runs and at `plan0`, `plan1`, `plan2`.
  `decl0`, `decl1`, `decl2`; **`fileOf_runs`**: under `fileOf_written`'s six equations on the three
    plans, `fileOf "proof file" …` returns the three lists `unrunG declRecsFull dryProofRunsFull0`,
    `… 1`, `… 2`.
  Negative test, BY THE KERNEL: `plans2_no`: with one run of the second chain turned to another
    value the lists are not `plan2`.

Limits. The full size alone. THE SIX EQUATIONS ON THE THREE PLANS ARE PREMISES. IT SPEAKS OF WRITTEN
VALUES: that the written sendings, rounds and sizes are what `sendsOf` and the planner make of any
public files is not said here. That `declRecsFull` has 136 members is held by no theorem here.
Nothing on soundness. On hiding nothing.

-/
import Johnson.AtFull.ProofBack.Decl
import Johnson.Unfolds.FillEq
import Johnson.Unfolds.DeclRecsLit
import Johnson.G.Runs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.ProofBack
open OnBytes OnBytes.Params Johnson.G Johnson.G.OfPlan Johnson.G.Runs Johnson.Unfolds
open VerifiableInference.PlanWritten (declRecsFull)

/-- BY THE KERNEL: the entries of the 136 declared values are the entries of the 136 distinct
written rounds, in order. -/
theorem ents : declRecsFull.map (·.entry) = dryProofRecsFull.map (·.1.entry) := by
  decide +kernel

/-- BY THE KERNEL: a value that draws no positions opens no tree and no stored tree. -/
theorem quiet :
    declRecsFull.all (fun d => posB d.entry || (d.stored.isEmpty && d.opens.isEmpty)) = true := by
  decide +kernel

/-- The round opens a tree or a stored tree. -/
def openB (d : Fmt.DeclaredRound) : Bool := !(d.opens.isEmpty && d.stored.isEmpty)

/-- BY THE KERNEL: a value draws positions just if it opens a tree or a stored tree. -/
theorem same : declRecsFull.all (fun d => posB d.entry == openB d) = true := by
  decide +kernel

/-- The entries along any runs. -/
theorem map_runs (runs : List (Nat × Nat)) :
    (unrunG declRecsFull runs).map (·.entry) =
      (unrunR dryProofRecsFull runs).map (·.1.entry) := by
  rw [map_unrunG, ents]
  exact (map_unrunG (fun x : Fmt.Round × List Fmt.Stored => x.1.entry) dryProofRecsFull runs).symm

/-- **`fillL` along any runs**: where what the values that open something open, along these runs, is
the given lists: `fillL` at the written entries and these lists is the 136 values along the runs. -/
theorem decl_of (runs : List (Nat × Nat)) (plan : List (List Told × List Fmt.Stored))
    (h : (expand ((valRuns declRecsFull runs).filter fun x => openB x.2)).map
      (fun d => (d.opens, d.stored)) = plan) :
    fillL ((unrunR dryProofRecsFull runs).map (·.1.entry)) plan = unrunG declRecsFull runs := by
  rw [← map_runs]
  refine fillL_eq_of _ _ (fun d hd hb => ?_) ?_
  · have q := List.all_eq_true.1 quiet d (mem_unrunG hd)
    rw [hb, Bool.false_or, Bool.and_eq_true, List.isEmpty_iff, List.isEmpty_iff] at q
    exact q
  · have e : ((unrunG declRecsFull runs).filter fun d => posB d.entry) =
        (unrunG declRecsFull runs).filter openB :=
      List.filter_congr fun d hd => eq_of_beq (List.all_eq_true.1 same d (mem_unrunG hd))
    rw [e, filter_unrunG]
    exact h

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
/-- BY THE KERNEL: along the first chain's runs, what the values that open something open is
`plan0`. -/
theorem plans0 :
    (expand ((valRuns declRecsFull dryProofRunsFull0).filter fun x => openB x.2)).map
      (fun d => (d.opens, d.stored)) = plan0 := by
  unfold plan0 t0 sortedW sentsOf extra0 sentAt sendTag
  simp only [Johnson.Unfolds.mergeSort_eq, Johnson.Unfolds.splitOn_eq, Johnson.Unfolds.toNat?_eq,
    Johnson.Unfolds.slice_toNat?_eq]
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
/-- BY THE KERNEL: the like along the shared chain's runs: `plan1`. -/
theorem plans1 :
    (expand ((valRuns declRecsFull dryProofRunsFull1).filter fun x => openB x.2)).map
      (fun d => (d.opens, d.stored)) = plan1 := by
  unfold plan1 t1 sortedW sentsOf extra1 sentAt sendTag
  simp only [Johnson.Unfolds.mergeSort_eq, Johnson.Unfolds.splitOn_eq, Johnson.Unfolds.toNat?_eq,
    Johnson.Unfolds.slice_toNat?_eq]
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
/-- BY THE KERNEL: the like along the second chain's runs: `plan2`. -/
theorem plans2 :
    (expand ((valRuns declRecsFull dryProofRunsFull2).filter fun x => openB x.2)).map
      (fun d => (d.opens, d.stored)) = plan2 := by
  unfold plan2 t0 t1 t2 sortedW sentsOf extra0 extra1 extra2 sentAt sendTag
  simp only [Johnson.Unfolds.mergeSort_eq, Johnson.Unfolds.splitOn_eq, Johnson.Unfolds.toNat?_eq,
    Johnson.Unfolds.slice_toNat?_eq]
  decide +kernel

/-- The first chain's declared rounds are the 136 values along its runs. -/
theorem decl0 : fillL es0 plan0 = unrunG declRecsFull dryProofRunsFull0 := by
  show fillL ((unrunR dryProofRecsFull dryProofRunsFull0).map (·.1.entry)) plan0 = _
  exact decl_of _ _ plans0

/-- The shared chain's declared rounds are the 136 values along its runs. -/
theorem decl1 : fillL es1 plan1 = unrunG declRecsFull dryProofRunsFull1 := by
  show fillL ((unrunR dryProofRecsFull dryProofRunsFull1).map (·.1.entry)) plan1 = _
  exact decl_of _ _ plans1

/-- The second chain's declared rounds are the 136 values along its runs. -/
theorem decl2 : fillL es2 plan2 = unrunG declRecsFull dryProofRunsFull2 := by
  show fillL ((unrunR dryProofRecsFull dryProofRunsFull2).map (·.1.entry)) plan2 = _
  exact decl_of _ _ plans2

/-- **For three plans whose rounds are the written entries and which have no other entry: `fileOf`
at the proof file's written values returns the written list of declared rounds.** -/
theorem fileOf_runs {P0 P1 P2 : Fmt.Plan} (e0 : P0.rounds = es0)
    (o0 : P0.entries.length - P0.rounds.length = 0) (e1 : P1.rounds = es1)
    (o1 : P1.entries.length - P1.rounds.length = 0) (e2 : P2.rounds = es2)
    (o2 : P2.entries.length - P2.rounds.length = 0) :
    fileOf "proof file" shapeW P0 P1 P2 proofSends0 proofSends1 proofSends2
      (fun ts es => frameOpens ridersW ts (es.filter fun e => e.name == "LOC").length) inputW =
      .ok (unrunG declRecsFull dryProofRunsFull0, unrunG declRecsFull dryProofRunsFull1,
        unrunG declRecsFull dryProofRunsFull2) := by
  rw [fileOf_written e0 o0 e1 o1 e2 o2, decl0, decl1, decl2]

/-! ## A negative test, stated positively -/

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
/-- BY THE KERNEL: with one run of the second chain turned to another value (131 for 130) the lists
are not `plan2`. -/
theorem plans2_no :
    decide ((expand ((valRuns declRecsFull (dryProofRunsFull2.set 4 (1, 131))).filter
      fun x => openB x.2)).map (fun d => (d.opens, d.stored)) = plan2) = false := by
  unfold plan2 t0 t1 t2 sortedW sentsOf extra0 extra1 extra2 sentAt sendTag
  simp only [Johnson.Unfolds.mergeSort_eq, Johnson.Unfolds.splitOn_eq, Johnson.Unfolds.toNat?_eq,
    Johnson.Unfolds.slice_toNat?_eq]
  decide +kernel

end Johnson.AtFull.ProofBack

#print axioms Johnson.AtFull.ProofBack.ents
#print axioms Johnson.AtFull.ProofBack.quiet
#print axioms Johnson.AtFull.ProofBack.same
#print axioms Johnson.AtFull.ProofBack.map_runs
#print axioms Johnson.AtFull.ProofBack.decl_of
#print axioms Johnson.AtFull.ProofBack.plans0
#print axioms Johnson.AtFull.ProofBack.plans1
#print axioms Johnson.AtFull.ProofBack.plans2
#print axioms Johnson.AtFull.ProofBack.decl0
#print axioms Johnson.AtFull.ProofBack.decl1
#print axioms Johnson.AtFull.ProofBack.decl2
#print axioms Johnson.AtFull.ProofBack.fileOf_runs
#print axioms Johnson.AtFull.ProofBack.plans2_no
