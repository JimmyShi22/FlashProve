-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K6/Honest/TruthOfTables.lean: THE OUTPUT HEAD'S OWN ROUNDS, THE HONEST PROVER'S SIDE:
WHERE WHAT LIES HIDDEN IS Tables.lean'S VALUES, IT IS THE TRUTH OF THE CELLS.
WHAT IT IS NOT. No prover, no round, no coin: THAT ANY LEDGER HIDES THESE VALUES IS NOT SHOWN HERE,
and no example is given. Nothing on whether the verifier accepts, on soundness, on completeness or
on what a proof hides. CONDITIONAL: on the structure HidesTables, on five sizes and on zt's size.
THIRTEEN OF ITS FOURTEEN CLAUSES ARE EQUATIONS IN THE FIELD K, BETWEEN READINGS: a test with code
can try "the two elements read alike", not the reading itself. Mathlib and Johnson/Desc/Kinds/Law/
are in the closure of its imports.
WHAT IT IS. At all sizes. H: what the verifier's hearing returned; G: the ledger behind it; the
world is worldE G mask noEnt (Johnson/Desc/Kinds/Law/K06Glue.lean).
  HidesTables c mask H G   in that world: the nine and the seven hidden scalars' variables are worth
       the readings of wScalars and pScalars at H's point; the three claimed sums' variables those
       of prLead, nmLead, lgLead; the ten end values' variables those of the four sums' ends at H's
       own challenges; THE FOUR SUMCHECKS' OWN FORMS ARE WORTH 0, in the texts of
       Law/OpenedNorm.lean's NormTruthW and of Law/OpenedSent.lean's headTruth_of_values; and the
       constant of the second end value's variable of the head's own sumcheck is written
       canonically. These four forms and that last clause say nothing of Tables.lean: they are
       handed through. (The last clause can be had of that sumcheck's return: Law/OpenedSent.lean's
       sumcheck_okEnds; here it stays a clause.)
  truth_of_tables          HidesTables and the sizes give NormTruthW, HeadTruth
       (Law/OpenedHead.lean) and NormedClaimed (Law/K06ClosedTruth.lean). FOUR FIELDS OF THESE TWO
       STRUCTURES (sqRow, prRow, nmRow; row) ARE THE FOUR FORMS: THEY GO IN AS THEY COME OUT.
  truthHeard_of_tables     with the hearing's return: Law/K06EveryList.lean's TruthHeard, and
       NormedClaimed.
CALLED: TablesLaw.lean's readings (wScalars_reads, pScalars_reads, prLead_batch, lgLead_reads, the
four on end values, the numbers of variables) and the library's headTruth_of_values.

-/
import Mathlib
import Johnson.Desc.K6.Honest.TablesLaw
import Johnson.Desc.Kinds.Law.K06ClosedTruth

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

namespace VerifiableInference.Desc.Kinds.Head.Honest

open OnBytes (E okE)
open OnBytes.Model (Fork)
open Norm (lt lPd)
open Law (rd worldE noEnt)
open Law.Came (val)

variable [Sizes] [Policy] [Request] [Token] [FinalNorm.In] [In]

/-- **WHAT LIES HIDDEN IS Tables.lean'S VALUES**, at what was heard H and the ledger G; and the four
sumchecks' own forms are worth 0 (sqRow, prRow, nmRow, lgRow), which says nothing of Tables.lean. -/
structure HidesTables (c : Law.NCells) (mask : Nat → E) (H : HeardAll) (G : Fork) : Prop where
  w : ∀ s, s < 9 → val (worldE G mask noEnt) (H.1.W.getD s {}).var =
    rd ((wScalars c H.1.pV).getD s 0)
  p : ∀ n, n < 7 → val (worldE G mask noEnt) (H.1.P.getD n {}).var =
    rd ((pScalars c H.1.pV).getD n 0)
  sqRow : val (worldE G mask noEnt)
    (H.1.squares.left ((H.1.squares.end_ 0).shown * (H.1.squares.end_ 1).shown)) = 0
  sqEnd : ∀ j, j < 2 → val (worldE G mask noEnt) (H.1.squares.end_ j).var =
    rd (((sqSum c H.1.pV H.1.gam).ends H.1.squares.r.toList).getD j 0)
  prClaimed : val (worldE G mask noEnt) H.1.products.claimed.var = rd (prLead c H.1.pV H.1.om)
  prRow : val (worldE G mask noEnt) (H.1.products.left (sumTo 1 fun i =>
    OnBytes.Desc.First.P6.summand (fun n => H.1.om ^ (7 * i + n))
      fun j => (H.1.products.end_ (4 * i + j)).shown)) = 0
  prEnd : ∀ q, q < 4 → val (worldE G mask noEnt) (H.1.products.end_ q).var =
    rd (((prSum c H.1.pV H.1.om).ends H.1.products.r.toList).getD q 0)
  nmClaimed : val (worldE G mask noEnt) H.2.1.normed.claimed.var = rd (nmLead c)
  nmRow : val (worldE G mask noEnt)
    (H.2.1.normed.left ((H.2.1.normed.end_ 0).shown * (H.2.1.normed.end_ 1).shown)) = 0
  nmEnd : ∀ j, j < 2 → val (worldE G mask noEnt) (H.2.1.normed.end_ j).var =
    rd (((nmSum c).ends H.2.1.normed.r.toList).getD j 0)
  lgClaimed : val (worldE G mask noEnt) H.2.2.logits.claimed.var = rd (lgLead c.toCells)
  lgRow : val (worldE G mask noEnt)
    (H.2.2.logits.left ((H.2.2.logits.end_ 0).shown * (H.2.2.logits.end_ 1).shown)) = 0
  lgEnd : ∀ j, j < 2 → val (worldE G mask noEnt) (H.2.2.logits.end_ j).var =
    rd (((lgSum c.toCells).ends H.2.2.logits.r.toList).getD j 0)
  ok1 : okE (H.2.2.logits.end_ 1).var.const = true

/-- **IT IS THE TRUTH OF THE CELLS.** The four sumchecks' own forms and the clause on canonical
writing are handed through as they come. -/
theorem truth_of_tables (c : Law.NCells) (mask : Nat → E) (H : HeardAll) (G : Fork)
    (A : HidesTables c mask H G) (sPV : H.1.pV.size = lt)
    (sS : H.1.squares.r.size = lPd + lt) (sP : H.1.products.r.size = lt)
    (sN : H.2.1.normed.r.size = lt) (sL : H.2.2.logits.r.size = lt + lPd)
    (hzt : (FinalNorm.zt).size = lt) :
    (letI : Norm.Heard := H.1
     letI : FinalNorm.Heard := H.2.1
     letI : FinalNorm.Reads := Law.normReadsAtCells c
     Law.NormTruthW (worldE G mask noEnt) c) ∧
    (letI : Heard := H.2.2
     letI : Reads := Law.readsAt c.toCells
     Law.HeadTruth c.toCells G mask noEnt) ∧
    Law.NormedClaimed c mask H G := by
  have lS : H.1.squares.r.toList.length = lPd + lt := by rw [Array.length_toList, sS]
  have lP : H.1.products.r.toList.length = lt := by rw [Array.length_toList, sP]
  have lN : H.2.1.normed.r.toList.length = lt := by rw [Array.length_toList, sN]
  have lL : H.2.2.logits.r.toList.length = lt + lPd := by rw [Array.length_toList, sL]
  have eS : ∀ j, j < 2 → rd (((sqSum c H.1.pV H.1.gam).ends H.1.squares.r.toList).getD j 0) =
      Blocks.ext (lPd + lt) ((Law.dataOf c).sqTab lPd (rd H.1.gam)) (Law.ptK H.1.squares.r) := by
    intro j hj
    have e := sqEnds_ext c H.1.pV H.1.gam H.1.squares.r.toList sPV lS j hj
    rw [Array.toArray_toList] at e
    exact e
  have eP : ∀ q, q < 4 → rd (((prSum c H.1.pV H.1.om).ends H.1.products.r.toList).getD q 0) =
      Blocks.ext lt (Law.fieldK c q) (Law.ptK H.1.products.r) := by
    intro q hq
    have e := prEnds_ext c H.1.pV H.1.om H.1.products.r.toList sPV lP q hq
    rw [Array.toArray_toList] at e
    exact e
  have eN := nmEnds_reads c H.2.1.normed.r.toList (by rw [nm_vars, hzt, lN])
  rw [lN] at eN
  have eL := lgEnds_reads c.toCells H.2.2.logits.r.toList (by rw [lg_vars, hzt, lL])
  rw [lL] at eL
  refine ⟨?_, ?_, A.nmClaimed⟩
  · letI : Norm.Heard := H.1
    letI : FinalNorm.Heard := H.2.1
    letI : FinalNorm.Reads := Law.normReadsAtCells c
    exact
      { sums := fun s hs => (A.w s hs).trans (wScalars_reads c H.1.pV sPV s hs)
        prods := fun n hn => (A.p n hn).trans (pScalars_reads c H.1.pV sPV n hn)
        sqRow := A.sqRow
        sq0 := (A.sqEnd 0 (by omega)).trans (eS 0 (by omega))
        sq1 := (A.sqEnd 1 (by omega)).trans (eS 1 (by omega))
        prClaimed := A.prClaimed.trans (prLead_batch c H.1.pV H.1.om sPV)
        prRow := A.prRow
        prEnd := fun q hq => (A.prEnd q hq).trans (eP q hq)
        nmRow := A.nmRow
        nm0 := (A.nmEnd 0 (by omega)).trans eN.1
        nm1 := (A.nmEnd 1 (by omega)).trans eN.2 }
  · letI : Heard := H.2.2
    letI : Reads := Law.readsAt c.toCells
    exact Law.headTruth_of_values c.toCells G mask noEnt hzt sL
      (A.lgClaimed.trans (lgLead_reads c.toCells hzt)) A.lgRow
      ((A.lgEnd 0 (by omega)).trans eL.1) ((A.lgEnd 1 (by omega)).trans eL.2) A.ok1

/-- **WITH THE HEARING'S RETURN**: the structure that Law/K06EveryList.lean's tops take, and the one
more value that Law/K06ClosedTruth.lean's take. -/
theorem truthHeard_of_tables (c : Law.NCells) (mask : Nat → E) {F G : Fork} {rs : List Fmt.RoundView}
    {H : HeardAll} (hh : hear F rs = some (H, G, [])) (A : HidesTables c mask H G)
    (sPV : H.1.pV.size = lt) (sS : H.1.squares.r.size = lPd + lt)
    (sP : H.1.products.r.size = lt) (sN : H.2.1.normed.r.size = lt)
    (sL : H.2.2.logits.r.size = lt + lPd) (hzt : (FinalNorm.zt).size = lt) :
    Law.TruthHeard c mask F rs H G ∧ Law.NormedClaimed c mask H G := by
  obtain ⟨a, b, e⟩ := truth_of_tables c mask H G A sPV sS sP sN sL hzt
  exact ⟨⟨hh, sPV, sS, sP, sN, a, b⟩, e⟩

end VerifiableInference.Desc.Kinds.Head.Honest

#print axioms VerifiableInference.Desc.Kinds.Head.Honest.truth_of_tables
#print axioms VerifiableInference.Desc.Kinds.Head.Honest.truthHeard_of_tables
