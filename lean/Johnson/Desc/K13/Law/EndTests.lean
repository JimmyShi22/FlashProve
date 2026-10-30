-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K13/Law/EndTests.lean: THE LAST CHAIN's LEDGER's TESTS ON THE FIRST TABLE's LAST BORDER
(sampled · wIn · iIn), FROM WHAT THE TABLE COMPUTES AS OPEN THERE AND TWO COMPARISONS OF THE PLAN's
NUMBERS. One definition, statements with their proofs.

Why. Row 0 of the last chain's table and the ledger above it take as premises: every sampled tenant
that is open at the first chain's last border sits in a tree below the last chain's first
(sampledBelow, Johnson/Desc/Sound/ReadsBelowAt.lean), and W's and the index masks' tenants are among
these. Evaluated, at both real sizes, in a file of evaluations that is not named here; no theorem.

OBJECT   First.openSets links ps (First.start links) at the border ps.length: the table's own text.
USER     sampled of rowZeroOwed_atSig | _atJoint | _atPlaces (Johnson/Flat/Last/) · the fields
         sampled | wIn | iIn of the last chain's ledger. Called in
         Johnson/Desc/K13/Law/EndTestsAll.lean (sampledBelow_of_open, w_sampled, index_sampled).
LETTERS  N · lo · links.
FIELD    leads3_last_chains_table (Johnson/Goal/Skeleton/ProofFile.lean).

  sampledBelow_of_open   nothing but "no mark", three pins and the one claim is open · N.index.1 <
                         lo · N.w.1 < lo ⟹ sampledBelow lo N O = true: sampled_of_open CALLED.
  w_sampled | index_sampled   pinV | pinI is open ⟹ N.w | N.index is among the sampled tenants
                         (the second is idx_of_pin, Johnson/Desc/K13/Law/AtTable.lean: CALLED).
  endOpenB · endOpen_both   the facts on the table as one test with code, and members: the two
                         written lists, border 78 | 358.
  endTests_small | _full **the three tests at the two lists**, at every N with the two comparisons.
What is not claimed. THE TWO COMPARISONS STAY PREMISES: N is a letter. The ledger's "omega" speaks
of the shared table's numbers: not here. The two lists are as the table's walk writes them: tied to
no plan. Nothing on soundness.

-/
import Johnson.Desc.K13.Law.AtTableSealRow
import Johnson.Desc.Sound.ReadsBelowAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K13.Law
open VerifiableInference.Desc.First (ModelPart Item Numbers sampledIn openSets start)
open VerifiableInference.Desc.Sound (sampledBelow)

/-- The test on the plan's numbers, from what is open and two comparisons. -/
theorem sampledBelow_of_open (lo : ℕ) (N : Numbers) (O : List Item)
    (hO : ∀ i ∈ O, i = .unmarked ∨ i = .pinW ∨ i = .pinI ∨ i = .pinV ∨ i = .pileOne)
    (hI : N.index.1 < lo) (hV : N.w.1 < lo) : sampledBelow lo N O = true := by
  unfold sampledBelow
  refine List.all_eq_true.2 fun t ht => decide_eq_true ?_
  rcases sampled_of_open N O hO t ht with rfl | rfl
  · exact hI
  · exact hV

/-- W's tenant's sample is asked where W's pin is open. -/
theorem w_sampled (N : Numbers) {O : List Item} (h : Item.pinV ∈ O) : N.w ∈ sampledIn N O :=
  List.mem_flatMap.2 ⟨.pinV, h, List.mem_singleton.2 rfl⟩

/-- So is the index masks'. -/
theorem index_sampled (N : Numbers) {O : List Item} (h : Item.pinI ∈ O) :
    N.index ∈ sampledIn N O := idx_of_pin N h

/-- **The facts on the table at border k, as one test with code.** -/
def endOpenB (links : List ModelPart) (ps : List Place) (k : ℕ) : Bool :=
  openSealB links ps k && (openAt links ps k).contains .pinV && (openAt links ps k).contains .pinI

set_option maxRecDepth 1000000 in
/-- **Members**: the last border of the two written lists. -/
theorem endOpen_both :
    endOpenB linksSmall (First.flatPlaces true linksSmall true)
        (First.flatPlaces true linksSmall true).length = true ∧
      endOpenB linksFull (First.flatPlaces true linksFull true)
        (First.flatPlaces true linksFull true).length = true := by
  decide +kernel

/-- The three tests from the one. -/
theorem endTests_of_test (links : List ModelPart) (ps : List Place)
    (h : endOpenB links ps ps.length = true) (lo : ℕ) (N : Numbers) (hI : N.index.1 < lo)
    (hV : N.w.1 < lo) :
    sampledBelow lo N ((openSets links ps (start links))[ps.length]?.getD []) = true ∧
      N.w ∈ sampledIn N ((openSets links ps (start links))[ps.length]?.getD []) ∧
      N.index ∈ sampledIn N ((openSets links ps (start links))[ps.length]?.getD []) := by
  unfold endOpenB at h
  simp only [Bool.and_eq_true] at h
  exact ⟨sampledBelow_of_open lo N _ (open_of_test links ps _ h.1.1) hI hV,
    w_sampled N (List.contains_iff_mem.1 h.1.2), index_sampled N (List.contains_iff_mem.1 h.2)⟩

/-- **The three tests at the small list.** -/
theorem endTests_small (lo : ℕ) (N : Numbers) (hI : N.index.1 < lo) (hV : N.w.1 < lo) :
    sampledBelow lo N ((openSets linksSmall (First.flatPlaces true linksSmall true)
        (start linksSmall))[(First.flatPlaces true linksSmall true).length]?.getD []) = true ∧
      N.w ∈ sampledIn N ((openSets linksSmall (First.flatPlaces true linksSmall true)
        (start linksSmall))[(First.flatPlaces true linksSmall true).length]?.getD []) ∧
      N.index ∈ sampledIn N ((openSets linksSmall (First.flatPlaces true linksSmall true)
        (start linksSmall))[(First.flatPlaces true linksSmall true).length]?.getD []) :=
  endTests_of_test linksSmall (First.flatPlaces true linksSmall true) endOpen_both.1 lo N hI hV

/-- **At the full list.** -/
theorem endTests_full (lo : ℕ) (N : Numbers) (hI : N.index.1 < lo) (hV : N.w.1 < lo) :
    sampledBelow lo N ((openSets linksFull (First.flatPlaces true linksFull true)
        (start linksFull))[(First.flatPlaces true linksFull true).length]?.getD []) = true ∧
      N.w ∈ sampledIn N ((openSets linksFull (First.flatPlaces true linksFull true)
        (start linksFull))[(First.flatPlaces true linksFull true).length]?.getD []) ∧
      N.index ∈ sampledIn N ((openSets linksFull (First.flatPlaces true linksFull true)
        (start linksFull))[(First.flatPlaces true linksFull true).length]?.getD []) :=
  endTests_of_test linksFull (First.flatPlaces true linksFull true) endOpen_both.2 lo N hI hV

end VerifiableInference.Desc.K13.Law
