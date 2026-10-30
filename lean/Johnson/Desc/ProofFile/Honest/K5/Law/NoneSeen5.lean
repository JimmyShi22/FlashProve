-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K5/Law/NoneSeen5.lean: NOT a law on a distribution, and NOT a sentence
on what a real run's challenges hang on: A SENTENCE THAT CAN FAIL in the stead of a reading of a
text: NO MOVE OF A MEMBER OF THE SIDE AT THE ROW OF AN ATTENTION SEGMENT's OWN ROUNDS (kind K5: the
label of that sub-protocol in the description) READS ANYTHING OF WHAT HAS BEEN SEEN
(Part.readsNoneSeen, Honest/Small/NoneSeen.lean). Statements with their proofs.

  jobOf_noneSeen a job that jobOf (Honest/K5/Job.lean) makes of a lead and a summand that read of
                 the front what was heard alone reads nothing of what has been seen
                 (SumJob.readsNoneSeen, Honest/Small/NoneSeenSum.lean)
  partAt_noneSeen   so does each part of the row, at every shape, number, place, reader of the
                 challenges and list of jobs: no premise
  partOf5_noneSeen  so does the part as it is seated, at every reader of cells and every seat
  k5_members_noneSeen   **CONDITIONAL: so does the part of EVERY MEMBER OF THE SIDE**: σ.row is K5's

Why. The theorems from which exact is had at this row (Honest/K5/Law/GoodPaid.lean) fix what was
shown in front before the coins; where a job reads an item that was sent under an entry which is
spent here, that is not so in a run. A part that reads nothing of what has been seen does not walk
that road.

Limits. Those of Honest/Small/NoneSeen.lean: IT SHUTS ONE ROAD, AT THIS STOREY: nothing on the
challenges heard, which at the compiled storey hang on all that was sent, and which by type hold a
sealed digest too; here they are handed on whole, and the seat's reader of the key points is a free
function of them; nothing on the input; nothing on the runs that a part is handed: the summand at Y
is handed the run of the end values that the same job spends, by the frame's letter: that is no
reading of what was seen. IN THIS FOLDER ONE FILE SPENDS THESE: Honest/K5/Law/SLotK3.lean.
No property is claimed. Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K5.Law.RowIs
import Johnson.Desc.ProofFile.Honest.Small.NoneSeenSum

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K5
open OnBytes (E)
open VerifiableInference.Desc (Place)
open VerifiableInference.Desc.Part.MaskedSum (Call)
open H2K5.Honest (PartShape Chal Summand)
open ProofFile.Honest.Small

/-- **A job that is made of a lead and a summand that read what was heard alone.** No premise. -/
theorem jobOf_noneSeen {W X : Type} (shape : Call) (lead : W → List Fmt.Drawn → List E)
    (S : W → List Fmt.Drawn → Summand) :
    (jobOf (X := X) shape (fun w fr => lead w fr.heard)
      fun w fr => S w fr.heard).readsNoneSeen := by
  intro w fr fr' hh _
  simp only [jobOf, hh, and_self]

/-- **No move of a part of the row reads anything of what has been seen.** No premise. -/
theorem partAt_noneSeen {W' : Type} (a : Place) (chalOf : List Fmt.Drawn → Chal) (J : Jobs W') :
    ∀ s : PartShape × Nat, (K5.partAt a chalOf J s).readsNoneSeen
  | (.sum k, j) =>
    sumPart_noneSeen _ _ _
      (jobOf_noneSeen k (fun w h => J.alone j w (chalOf h)) fun w h => J.sum j w (chalOf h))
  | (.one 0, _) => quietPart_noneSeen 1
  | (.one (_ + 1), _) => scalarsPart_noneSeen _ _ _ fun _ _ _ hh _ => by rw [hh]

variable {W₀ Rc Xi Tr X Pb S Cl : Type}

/-- **Nor does a move of the part as it is seated.** No premise. -/
theorem partOf5_noneSeen (cells : Tr → Cells) (Z : Seat5) (j : Nat) (s : PartShape) :
    (partOf5 (W₀ := W₀) (Rc := Rc) (Xi := Xi) (X := X) cells Z j s).readsNoneSeen :=
  lift_noneSeen _ _ _ _ _ (partAt_noneSeen Z.place (chalOf Z) (jobs Z.P) (s, j))

/-- **NO MOVE OF A MEMBER OF THE SIDE READS ANYTHING OF WHAT HAS BEEN SEEN.** CONDITIONAL: the
side's row is K5's. By member_at (Honest/K5/Law/RowIs.lean): every member is written out. -/
theorem k5_members_noneSeen {σ : Side S Cl (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Pb}
    {cells : Tr → Cells} {Z : Seat5} (hr : σ.row = k5Pairs cells Z) :
    ∀ u ∈ σ.members, u.part.readsNoneSeen := by
  intro u hu
  obtain ⟨j, s, -, rfl⟩ := member_at hr hu
  exact partOf5_noneSeen cells Z j s

end ProofFile.Honest.K5

#print axioms ProofFile.Honest.K5.jobOf_noneSeen
#print axioms ProofFile.Honest.K5.partAt_noneSeen
#print axioms ProofFile.Honest.K5.partOf5_noneSeen
#print axioms ProofFile.Honest.K5.k5_members_noneSeen
