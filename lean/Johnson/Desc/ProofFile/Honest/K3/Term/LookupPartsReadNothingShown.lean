-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K3/Term/LookupPartsReadNothingShown.lean: AT ANY FILLING. The kind
"lookup" (K3): no part of a lookup's row reads anything of what has been shown before it: neither
the rounds shown (so no scalar that an earlier part of the same lookup, or any other part, has sent)
nor the opened columns. In Lean: `Part.readsNoneSeen` (Honest/Small/NoneSeen.lean) holds of every
part of every row of the lot. Theorems; no definition. General in the filling. No premise.

  `lookupJobReadsNothingShown`     `SumJob.readsNoneSeen` (Honest/Small/NoneSeenSum.lean) of a
      stage's job
  `lookupPartReadsNothingShown`    `Part.readsNoneSeen` of a stage's part
  `lookupRowReadsNothingShown`     of every part of every row of the lot

Why it is stated. The law on the masked sumcheck's part (Honest/SumLaw/SumExact.lean, head) warns: a
job may read the rounds shown in front of the part; where an item that it reads was sent under a
coin which the part spends, these are not fixed before the coins in a run. A lookup's jobs read of
what stands in front the challenges alone.

What it does NOT say. That the STATE before a lookup's part is free of the coins that the part
spends. It need not be: what the owner has shown stands among the rounds shown (by the design, its
out-of-domain answer reads the mask row; not shown in these files). That what the owner shows is
independent IN LAW of the entries that are lent is what the field fresh at the owner ASKS; it is
meant to come from the row's pad; THIS FILE DOES NOT PROVE IT.

They call: `sumPart_noneSeen`, `quietPart_noneSeen`, `lift_noneSeen`.

The sites of a public part (`lookSites`) are PLACES OF THE PROOF FILE ALONE (fifty under the
library's hypothesis at the full size): THE KEY FILE'S TWO LOOKUPS ARE NOT SPOKEN OF.

Limits. Those of Honest/Small/NoneSeen.lean and NoneSeenSum.lean. Nothing on any property of the
protocol.
-/
import Johnson.Desc.ProofFile.Honest.Small.NoneSeenSum
import Johnson.Desc.ProofFile.Honest.K3.RowQuietIs
import Johnson.Desc.ProofFile.Honest.K3.Term.LookupSimulatorLot

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Term
open VerifiableInference.Desc.Part.MaskedSum (Call)
open ProofFile.Honest.Small (sumPart_noneSeen quietPart_noneSeen lift_noneSeen)
open ProofFile.Honest.K3.Law

/-- A stage's job reads nothing of what has been shown. -/
theorem lookupJobReadsNothingShown {W : Type} (R : Reads) (J : LookJobs W) (a : At) (stage : Stage)
    (call : Call) : (jobOf R J a stage call).readsNoneSeen := by
  intro w fr fr' sameHeard _
  simp only [jobOf, sameHeard]
  exact ⟨trivial, trivial, trivial, trivial, trivial⟩

/-- A stage's part reads nothing of what has been shown. -/
theorem lookupPartReadsNothingShown {V W : Type} (R : Reads) (J : LookJobs W) (a : At)
    (stage : Stage) (number : Nat) : (partOf (V := V) R J a stage number).readsNoneSeen := by
  unfold partOf
  cases stage.call a.face with
  | none =>
    show (quiet : Part V W Unit).readsNoneSeen
    rw [quiet_is]
    exact quietPart_noneSeen 1
  | some call => exact sumPart_noneSeen _ _ _ (lookupJobReadsNothingShown R J a stage call)

/-- **NO PART OF A ROW OF THE LOT READS ANYTHING OF WHAT HAS BEEN SHOWN BEFORE IT.** No premise. -/
theorem lookupRowReadsNothingShown {V W X Pb : Type} (F : Pub → Fill W) (publicPart : Pub)
    (ground : Ground) (row : Unlettered V W X Pb)
    (inLot : row ∈ (lookupSimulatorLot F).rows publicPart ground) :
    ∀ part ∈ row.half.parts, part.readsNoneSeen := by
  obtain ⟨s, _, rfl⟩ := lookupSimulatorRowOfLot F publicPart ground row inLot
  rw [lookupSimulatorRowHalf]
  intro part inRow
  obtain ⟨p, inLookRow, rfl⟩ := List.mem_map.1 inRow
  obtain ⟨y, _, rfl⟩ := List.mem_map.1 inLookRow
  exact lift_noneSeen _ _ _ _ _
    (lookupPartReadsNothingShown theReads ((F publicPart).jobs s).asked s.at_ y.1 y.2)

end ProofFile.Honest.K3.Term

#print axioms ProofFile.Honest.K3.Term.lookupJobReadsNothingShown
#print axioms ProofFile.Honest.K3.Term.lookupPartReadsNothingShown
#print axioms ProofFile.Honest.K3.Term.lookupRowReadsNothingShown
