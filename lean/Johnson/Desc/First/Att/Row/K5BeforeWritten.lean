-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Att/Row/K5BeforeWritten.lean: kind K5's row: **THE PREMISE "before" OF
k5_row_plans (Johnson/Desc/First/Att/Row/K5RowPlans.lean) FROM TWO EQUATIONS BY FIELD OF THE PUBLIC
PART AGAINST WRITTEN VALUES THAT STAND IN OTHER FILES**: where the public part's table of stretches
is the written one (Johnson.AtFull.Cut.cutWritten) and its first chain's declared entries are the
written ones (P5T.esFull.1): H2K5.k5Before? Z ("A" ++ toString g) = some [(1, 4 + 6 g)] at each
g below 12. A joining; the one closed fact is before_closed
(Johnson/Desc/First/Att/Row/K5BeforeClosed.lean). No new literal.

Main names (namespace H2K5.Row):
  foldl_roots · rootsOf_is: the lot's fold over the first k declared rounds is P5T.rootsIn of their
    entries.
  rootsIn_full: P5T.rootsIn P5T.esFull.1 = P5T.sumBelow P5T.seedRoots: three laws of
    Johnson/P5T/PlanSeatsAt.lean | PlanSeatsFull.lean joined (P5T.rootsIn_unrun · rootsRuns_rooted ·
    rooted_written: as inside the proof of P5T.psFull_is, PlanSeatsFull.lean).
  **k5Before_of_pairs**: at the pairs (look, take) of the public part's table: just what the lot
    reads of it. **k5Before_written**: its corollary where the whole table (five fields a row) is
    the written one.
IS IT EMPTY HERE? AN IMPLICATION: THAT THE TWO EQUATIONS HOLD AT ANY PUBLIC FILES IS NOT SHOWN
HERE. THE PAYERS OF THE SECOND EQUATION (K5's files'
H2K5.Door.entries_written, Johnson/Desc/First/Att/Door/Law/RoundsWritten.lean; H2K12.Written354's
fourth equation in Johnson/Loose/H2K12/ClosedOfPins354.lean) STAND UNDER THE HEAD, OR UNDER
"the value is laid": NOT FOR A MEMBER OF THE HEAD. A payer off the front of the proof file's IOP's
maker alone is named by nobody here.
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.Row.K5BeforeClosed

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace H2K5.Row

/-- A fold that adds is a sum. -/
theorem foldl_roots (l : List Fmt.DeclaredRound) (a : ℕ) : l.foldl (fun n r => n + r.entry.roots) a = a + (l.map (·.entry.roots)).sum := by
  induction l generalizing a with
  | nil => rfl
  | cons x l ih => rw [List.foldl_cons, ih, List.map_cons, List.sum_cons, Nat.add_assoc]

/-- The lot's roots in front of a round, in terms of P5T.rootsIn (Johnson/P5T/PlanSeatsAt.lean). -/
theorem rootsOf_is (Z : ProofFile.Pub) (k : ℕ) : rootsOf Z k = P5T.rootsIn (Z.D.1.map (·.entry)) k := by
  unfold rootsOf P5T.rootsIn
  rw [foldl_roots, Nat.zero_add, ← List.map_take, List.map_map]
  rfl

/-- The written entries' roots, off the 82 pairs. -/
theorem rootsIn_full : P5T.rootsIn P5T.esFull.1 = P5T.sumBelow P5T.seedRoots := by
  have e : P5T.esFull.1 = (Johnson.G.unrunR Johnson.G.dryProofRecsFull Johnson.G.dryProofRunsFull0).map (·.1.entry) := rfl
  funext k
  rw [e, P5T.rootsIn_unrun, P5T.rootsRuns_rooted _ _ 0 k, P5T.rooted_written, Nat.zero_add]

/-- **"before" AT THE TWELVE, FROM TWO EQUATIONS BY FIELD: AT JUST WHAT THE LOT READS.** -/
theorem k5Before_of_pairs {Z : ProofFile.Pub} (hc : (Z.cuts.map fun c => (c.look, c.take)) = cutPairsW) (hD : Z.D.1.map (·.entry) = P5T.esFull.1) (g : ℕ)
    (hg : g < 12) : H2K5.k5Before? Z ("A" ++ toString g) = some [(1, 4 + 6 * g)] := by
  have hr : rootsOf Z = P5T.sumBelow P5T.seedRoots := by
    rw [← rootsIn_full, ← hD]
    exact funext (rootsOf_is Z)
  rw [k5Before_by, hc, hr]
  have h := List.all_eq_true.1 before_closed g (List.mem_range.2 hg)
  exact of_decide_eq_true h

/-- The like where the whole table of stretches is the written one. -/
theorem k5Before_written {Z : ProofFile.Pub} (hc : Z.cuts = Johnson.AtFull.Cut.cutWritten) (hD : Z.D.1.map (·.entry) = P5T.esFull.1) (g : ℕ) (hg : g < 12) :
    H2K5.k5Before? Z ("A" ++ toString g) = some [(1, 4 + 6 * g)] :=
  k5Before_of_pairs (congrArg (List.map fun c => (c.look, c.take)) hc) hD g hg

end H2K5.Row

#print axioms H2K5.Row.rootsOf_is
#print axioms H2K5.Row.rootsIn_full
#print axioms H2K5.Row.k5Before_of_pairs
#print axioms H2K5.Row.k5Before_written
#print axioms H2K5.Row.foldl_roots
