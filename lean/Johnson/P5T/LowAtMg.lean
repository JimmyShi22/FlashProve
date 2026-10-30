-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P5T/LowAtMg.lean: IN THE GOALS' SCOPE, WHERE THE VERIFIER's OWN VALUE IS LAID, THE FIFTH
TIE's CLOSED TEST `lowAtB` ACCEPTS AT THE TABLE's OWN NUMBERS `At.N Zp cF` AND ITS OWN COUNT OF
TREES, AT ALL 100 PLACES OF THE KIND K9. Eight theorems. A joining: the evaluation is
Johnson/P5T/LowFull.lean's.
Why. The condition of the kind K9 at the closed constant asks, at each of the 25 segments,
`lowAtB (At.N Zp cF) ((At.N Zp cF).treesAt At.ps[k]?) k = true`
at four places.
  `lowB_core`, `lowAtB_core`: the test reads of the numbers four fields alone: `sent`, `keptOf`,
  `index`, `w`.
  `LaidAt.trees`: the table's count of trees is the written one's: what the sub-protocols tell is
  the written cut's (`pins_of_laid`, Johnson/Goal/Skeleton/PinsOfLaid.lean; `told_at_written`,
  Johnson/Desc/First/CutWritten.lean).
  `LaidAt.low`: **the test accepts at every place of `k9Places`**: from the scope and "the value is
  laid" alone: by `LaidAt.N_core` (Johnson/P5T/CoreAtMg.lean) and `low_full`.
  `AtMg.low`: at the head.
  `batch_is`, `batch_mem`: by the kernel: the number of a segment's batching in the written list
  of places is `batchIx`; that number and 1, 2, 4 behind it are in `k9Places`.
  `AtMg.low_at_batch`: **in the form in which the condition asks it**: at `batchAt fullLinks At.ps
  m + j`, j of 0, 1, 2, 4, m below 25.
Limits. WHAT THE TEST DOES NOT SEE: `low_blind` (LowFull.lean): it says nothing of W's seat. It
stands over the verifier's list of thirteen entry tests (Johnson/Desc/Laid/ProofAsksFirstThirteenTests.lean)
alone. Whether `LaidAt` can be met at the release's own files is not shown here. The full size
alone. No probability: no soundness follows.
Terms: lean/GLOSSARY.md.

-/
import Johnson.P5T.LowFull
import Johnson.P5T.CoreAtMg
import Johnson.Desc.First.Link.Law.K9KindTiedR

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P5J
open VerifiableInference
open VerifiableInference.Desc (Chain Place)
open VerifiableInference.Desc.First (Numbers Item placesCut toldCut placesCut_is told_at_written
  treesTold borderOf flatPlacesOf)
open VerifiableInference.Desc.Sound (linksFull)
open VerifiableInference.Desc.LinkJoin (lowB lowAtB ridersAt batchAt batchIx)
open OnBytes.Maker (WholeD)

/-- The test at an item reads four fields of the numbers alone. -/
theorem lowB_core {N N' : Numbers} (h1 : N.sent = N'.sent) (h2 : N.keptOf = N'.keptOf)
    (h3 : N.index = N'.index) (h4 : N.w = N'.w) (b : ℕ) (i : Item) : lowB N b i = lowB N' b i := by
  cases i with
  | pin m t =>
    show ((N.sent m t).all fun x => decide (x.1 < b)) = (N'.sent m t).all fun x => decide (x.1 < b)
    rw [h1]
  | pinKept m =>
    show ((N.keptOf m).all fun x => decide (x.1 < b)) = (N'.keptOf m).all fun x => decide (x.1 < b)
    rw [h2]
  | pinI =>
    show decide (N.index.1 < b) = decide (N'.index.1 < b)
    rw [h3]
  | pinV =>
    show decide (N.w.1 < b) = decide (N'.w.1 < b)
    rw [h4]
  | _ => rfl

/-- So does the test at a place. -/
theorem lowAtB_core {N N' : Numbers} (h1 : N.sent = N'.sent) (h2 : N.keptOf = N'.keptOf)
    (h3 : N.index = N'.index) (h4 : N.w = N'.w) (b k : ℕ) : lowAtB N b k = lowAtB N' b k := by
  unfold lowAtB
  exact congrArg (ridersAt k).all (funext fun i => lowB_core h1 h2 h3 h4 b i)

variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}

/-- In scope, where the value is laid, the table's count of trees is the written one's. -/
theorem LaidAt.trees (L : LaidAt o Z.pol Z.lay Z.KL D r Zp Np cF)
    (hW : VerifierAndGoals.InScope Z = true) (p : Option Place) :
    (At.N Zp cF).treesAt p = P5T.NFull.treesAt p := by
  have hc : PlanWritten.cutOf cF.blocksInOrder = PlanWritten.cutFirstFull := (pins_of_laid hW L).2
  have ht : At.told cF = toldCut := by
    rw [At.told_is]
    exact (told_at_written hc).2
  show treesTold (At.told cF) (borderOf (flatPlacesOf linksFull true) p) =
    treesTold toldCut (borderOf placesCut p)
  rw [ht, placesCut_is]

/-- **In scope, where the value is laid, the test accepts at every place of the kind K9.** -/
theorem LaidAt.low (L : LaidAt o Z.pol Z.lay Z.KL D r Zp Np cF) (hW : VerifierAndGoals.InScope Z = true)
    {k : ℕ} (hk : k ∈ P5T.k9Places) :
    lowAtB (At.N Zp cF) ((At.N Zp cF).treesAt At.ps[k]?) k = true := by
  obtain ⟨e1, e2, e3, e4, -, -⟩ := L.N_core hW
  rw [L.trees hW, lowAtB_core (N' := P5T.NFull) e1 e2 e3 e4]
  show lowAtB P5T.NFull (P5T.NFull.treesAt (flatPlacesOf linksFull true)[k]?) k = true
  rw [← placesCut_is]
  exact List.all_eq_true.1 P5T.low_full k hk

/-- At the head. -/
theorem AtMg.low (h : AtMg o Z D r Zp Np cF) {k : ℕ} (hk : k ∈ P5T.k9Places) :
    lowAtB (At.N Zp cF) ((At.N Zp cF).treesAt At.ps[k]?) k = true := h.laid.low h.scope hk

set_option maxRecDepth 1000000 in
/-- By the kernel: the number of a segment's batching in the written list of places. -/
theorem batch_is : ∀ m < 25, batchAt fullLinks At.ps m = batchIx m := by decide +kernel

set_option maxRecDepth 1000000 in
/-- By the kernel: that number, and 1, 2 and 4 behind it, are among the 100 places. -/
theorem batch_mem : ∀ m < 25, ∀ j ∈ [0, 1, 2, 4], batchIx m + j ∈ P5T.k9Places := by decide +kernel

/-- **In the form in which the condition of the kind K9 asks it.** -/
theorem AtMg.low_at_batch (h : AtMg o Z D r Zp Np cF) (m : ℕ) (hm : m < 25) :
    ∀ j ∈ [0, 1, 2, 4],
      lowAtB (At.N Zp cF) ((At.N Zp cF).treesAt At.ps[batchAt fullLinks At.ps m + j]?)
        (batchAt fullLinks At.ps m + j) = true := by
  intro j hj
  rw [batch_is m hm]
  exact h.low (batch_mem m hm j hj)

end P5J

#print axioms P5J.lowB_core
#print axioms P5J.lowAtB_core
#print axioms P5J.LaidAt.trees
#print axioms P5J.LaidAt.low
#print axioms P5J.AtMg.low
#print axioms P5J.batch_is
#print axioms P5J.batch_mem
#print axioms P5J.AtMg.low_at_batch
