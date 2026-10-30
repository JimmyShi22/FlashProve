-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K13/Tie.lean: kind K13, the members' batching: THE SCALARS THAT THE
FRAME's PART SENDS AT K13's JOB (`k13Job`, Part.lean of this folder; the formulas `plainFirst`,
`plainRound`, SumReads.lean) READ AS THE SCALARS OF THE KIND's HONEST PROVER (`sumU`, `sent` at
`tabsOf`: Johnson/Desc/K13/Honest/Moves.lean, MovesAtM3.lean), where the stretch of coins holds the
mask entries that were taken. Statements with their proofs.
Main names:
  `tabsOf_mat`: the tables read the matrix alone, no mask entry.
  `k13Round`, `k13Job_round`: the job's three coefficients, of the pile, x and the challenges so
    far: the job's own `round`, by its text.
  `k13Round_reads`: they read as the tables' three coefficients.
  `k13_first_reads`, `k13_rounds_read`: **the sum; the pairs.**

What is not claimed. That `sumPart`'s moves, played, yield the formulas `plainFirst` and
`plainRound`: the statements here are of these formulas, not of `sumPart`. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K13.Part
import Johnson.Desc.ProofFile.Honest.K13.SumReads
import Johnson.Desc.K13.Law.Pin

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K13
open OnBytes (E TensorRow Slot zeroE)
open OnBytes.Slice (GE toE ofE)
open OnBytes.Model (Reading)
open VerifiableInference.Desc.K13.Law (Wit ρg gl_section colOf)
open VerifiableInference.Desc.K13.Honest (tabsOf quadAll foldsAll maskAt sumU sent sentL sent_eq)

/-- **The tables read the matrix alone.** -/
theorem tabsOf_mat {nR k : Nat} {w w' : Wit GE nR k} (h : w.mat = w'.mat) (pile : List TensorRow)
    (a : GE) : tabsOf ρg w pile a = tabsOf ρg w' pile a := by
  have e : ∀ v, colOf w v = colOf w' v := fun v => by
    unfold colOf
    rw [h]
  unfold tabsOf
  simp only [e]

/-- The job's three coefficients, of the pile, x and the challenges so far. -/
def k13Round (nR k : Nat) (w : K13Ask) (pile : List TensorRow) (x : E) (rs : List E) : List E :=
  let c := quadAll (foldsAll (rs.map Reading.gl.val)
    (tabsOf Reading.gl (k13Wit nR k w) pile (Reading.gl.val x)))
  [k13E c.1, k13E c.2.1, k13E c.2.2]

/-- **The job's `round` is this function**, at the pile that the small input makes of the challenges
in front, and at x, the last of these. -/
theorem k13Job_round (nR k : Nat) (w : K13Ask) (fr : Front Unit) (rs : List E) :
    (k13Job nR k).round w fr rs =
      k13Round nR k w (w.pile fr.heard)
        ((drawnE (fr.heard.drop (fr.heard.length - 1))).headD zeroE) rs := rfl

/-- They read as the tables' three coefficients. -/
theorem k13Round_reads (N nR k : Nat) (w : K13Ask) (pile : List TensorRow) (x : E) :
    ReadsAs ρg N (k13Round nR k w pile x)
      (fun seen => quadAll (foldsAll seen (tabsOf ρg (k13Wit nR k w) pile (ρg.val x)))) :=
  fun rs _ => ⟨_, _, _, rfl, by
    show _ = (ρg.val (k13E _), ρg.val (k13E _), ρg.val (k13E _))
    unfold k13E
    rw [gl_section, gl_section, gl_section]⟩

variable {nR k : Nat}

/-- **The sum that the part sends first, read.** W: the matrix and the mask entries. fresh: the mask
entries that were taken. u: the stretch of coins. -/
theorem k13_first_reads (W : Wit GE nR k) (fresh : List Slot) (u : List E)
    (hu : ∀ j, j < 2 * k + 1 → ρg.val (u.getD j zeroE) = maskAt W fresh j) :
    ρg.val (plainFirst k u) = sumU (maskAt W fresh) k :=
  tail_reads ρg (maskAt W fresh) k u 0 (fun j hj => by rw [hu j hj, Nat.zero_add])

/-- **The pairs that the part sends, read.** -/
theorem k13_rounds_read (w : K13Ask) (W : Wit GE nR k) (hmat : W.mat = (k13Wit nR k w).mat)
    (pile : List TensorRow) (fresh : List Slot) (u : List E)
    (hu : ∀ j, j < 2 * k + 1 → ρg.val (u.getD j zeroE) = maskAt W fresh j) (x eps : E)
    (gs : List E) (hg : gs.length = k) :
    (List.range k).map (fun t =>
        readPair ρg (plainRound k u eps (gs.take t) (k13Round nR k w pile x (gs.take t)))) =
      sent (maskAt W fresh) (ρg.val eps) k 0 (tabsOf ρg W pile (ρg.val x)) (gs.map ρg.val) := by
  have h := rounds_read ρg (maskAt W fresh) eps (k13Round_reads k nR k w pile x) k u 0 [] gs zeroE
    (Nat.zero_add k) (fun j hj => by rw [hu j hj, Nat.zero_add]) hg
  have e := sent_eq (maskAt W fresh) (ρg.val eps) (tabsOf ρg (k13Wit nR k w) pile (ρg.val x)) k 0 []
    (gs.map ρg.val)
  rw [tabsOf_mat hmat]
  show _ = sent _ _ k 0 (foldsAll [] (tabsOf ρg (k13Wit nR k w) pile (ρg.val x))) _
  rw [e]
  exact h

end ProofFile.Honest.K13

#print axioms ProofFile.Honest.K13.tabsOf_mat
#print axioms ProofFile.Honest.K13.k13Job_round
#print axioms ProofFile.Honest.K13.k13Round_reads
#print axioms ProofFile.Honest.K13.k13_first_reads
#print axioms ProofFile.Honest.K13.k13_rounds_read
