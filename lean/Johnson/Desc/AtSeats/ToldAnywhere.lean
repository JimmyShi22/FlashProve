-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/AtSeats/ToldAnywhere.lean: PlanAt's FIELD told AT ANY PLACE OF THE FIRST CHAIN AT ONCE:
every tree of the two rounds that the file's data have at a place has the depth and the width that
the IOP as written in Lean declares at that tree's number. Where the first chain's sub-protocols
declare the written list osC (which follows from the test on the cut: oracles_of_cut,
Johnson/Desc/AtSeats/FromTheCut.lean), the declared side is closed, and ONE TEST BY LEAN's KERNEL
OVER THE 83 TREES ties it to the written table laidFull, at which the data's half ends.

  laid_told        THE CLOSED TEST: at each j below 83: laidFull[j] is (logLength, words) of osC[j].
  laid_told_rejects   it can fail: one tree's width turned; the list shifted by one.
  told_anywhere    G declares osC · the data's half at (ds, i₀, base) ⟹ told there. No word on which
                   sub-protocol stands at the place, on what it declares or on how many trees.
  ds₁_of_triple, trees_le_roots   two facts at letters: the written lists are never unfolded.
  dataHalf_writtenP   THE DATA's HALF AT writtenPFull's OWN LIST, AT EVERY PLACE: NO PREMISE: the
                   two counts of dataHalf_written are paid from t₁_written (FrameInScope.lean).
  told_written     so: told at every place of writtenPFull's list, under "G declares osC" alone.

What is not claimed. That G declares osC. Nothing on soundness.

-/
import Johnson.Desc.AtSeats.DataHalfWritten
import Johnson.Desc.AtSeats.FitsAtPlan
import Johnson.Desc.Sound.BaseOfBookFit
import Johnson.Top.H0.K2Hears.FrameInScope

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace HashBuild
open OnBytes OnBytes.Three OnBytes.Maker Johnson.G
open OnBytes.Params (Rounds)
open VerifiableInference.Desc (FileDescription Oracle oraclesOf osC oracleAt_first)

set_option maxRecDepth 1000000 in
/-- **The closed test.** -/
theorem laid_told : (decide (osC.length = 83) && (List.range 83).all fun j =>
    decide (laidFull[j]? = (osC[j]?).map fun o => (o.logLength, o.words))) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- Negative tests. -/
theorem laid_told_rejects :
    (((List.range 83).all fun j => decide (laidFull[j]? =
        ((osC.modify 40 fun o => { o with words := o.words + 1 })[j]?).map fun o =>
          (o.logLength, o.words))) ||
      ((List.range 83).all fun j => decide (laidFull[j]? =
        ((osC.drop 1)[j]?).map fun o => (o.logLength, o.words)))) = false := by
  decide +kernel

/-- **told, at any place.** -/
theorem told_anywhere {Xi : Type} (G : FileDescription Xi) (hO : oraclesOf G.first.blocksInOrder = osC)
    {ds : List RDT} {i₀ base : ℕ} (hD : DataHalf ds i₀ base) :
    ∀ d₁ d₂ : RDT, (ds.drop i₀).take 2 = [d₁, d₂] → ∀ n sh, treeShT [d₁, d₂] n = some sh →
      ∀ o, G.oracleAt (base + n) = some o → o.logLength = sh.a ∧ o.words = sh.W := by
  intro d₁ d₂ e n sh h o ho
  have hl := hD d₁ d₂ e n sh h
  obtain ⟨h83, hall⟩ := Bool.and_eq_true_iff.1 laid_told
  have hlen : osC.length = 83 := of_decide_eq_true h83
  have hj : base + n < 83 := by
    have := (List.getElem?_eq_some_iff.1 hl).1
    rwa [laid_83] at this
  rw [oracleAt_first G (by rw [hO, hlen]; exact hj), hO] at ho
  have k := of_decide_eq_true (List.all_eq_true.1 hall (base + n) (List.mem_range.2 hj))
  rw [ho, hl] at k
  have k' := Option.some.inj k
  exact ⟨(congrArg Prod.fst k').symm, (congrArg Prod.snd k').symm⟩

/-- The first chain's list of the data at a triple of lists of rounds. -/
theorem ds₁_of_triple (a : ℕ) (T : Rounds × Rounds × Rounds) :
    (WholeD.of a (wholeAt (some T))).ds₁ = (Whole.of T.1 T.2.1 T.2.2).stretch₁.map rdtOf := rfl

/-- The data's trees are at most the first list's roots. -/
theorem trees_le_roots (R₁ R₂ R₃ : Rounds) :
    (((Whole.of R₁ R₂ R₃).stretch₁.map rdtOf).map (·.trees.length)).sum ≤ rootsIn R₁ := by
  have h := VerifiableInference.Desc.Sound.data_trees 0 R₁ R₂ R₃
  have h' : ((Whole.of R₁ R₂ R₃).stretch₁.map rdtOf).map (·.trees.length) = _ := h
  rw [h', List.dropLast_eq_take]
  exact sum_take_le _ _

/-- **The data's half at the written data's own list, at every place.** -/
theorem dataHalf_writtenP (i₀ : ℕ) : DataHalf writtenPFull.ds₁ i₀
    ((writtenPFull.ds₁.take i₀).map (·.trees.length)).sum := by
  have e : writtenPFull.ds₁ =
      (Whole.of dryProofFull.1 dryProofFull.2.1 dryProofFull.2.2).stretch₁.map rdtOf :=
    ds₁_of_triple 32 dryProofFull
  have t : (writtenPFull.ds₁.map (·.trees.length)).sum = 83 :=
    VerifiableInference.Desc.First.K2.t₁_written
  rw [e] at t ⊢
  exact dataHalf_written (t ▸ trees_le_roots _ _ _) (Nat.le_of_eq t) i₀

/-- **told at every place of the written data's list.** -/
theorem told_written {Xi : Type} (G : FileDescription Xi) (hO : oraclesOf G.first.blocksInOrder = osC) (i₀ : ℕ) :
    ∀ d₁ d₂ : RDT, (writtenPFull.ds₁.drop i₀).take 2 = [d₁, d₂] → ∀ n sh,
      treeShT [d₁, d₂] n = some sh → ∀ o,
      G.oracleAt (((writtenPFull.ds₁.take i₀).map (·.trees.length)).sum + n) = some o →
      o.logLength = sh.a ∧ o.words = sh.W :=
  told_anywhere G hO (dataHalf_writtenP i₀)

end HashBuild
