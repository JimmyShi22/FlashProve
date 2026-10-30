-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K14/Sim/Book.lean: THE PREMISE OwnClear OF Honest/K14/Sim/Good.lean IS PAID at every book that the
frame's maker `bookWhole` returns at the proof file's IOP as written in Lean and the written list of the shared chain's sendings:
no entry spends a coin of the parts at "LIN point", "LOC", "LIN zeta" or "SPLIT". And the start of the coin that "SPLIT" spends.

  `noneSpent_of_spentBy`   the converse of the frame's `spentBy_of_noneSpent`
  `written_clear`  no entry of the written list names one of the four as its owner (an evaluation)
  `ownClear_of_whole`   **OwnClear at such a book**
  `split_entry_written`, `fold_entry_written`   the entries by which "SPLIT" and the fold are lent their coins: start and count

Limits. That `bookWhole` returns is a premise here. No
property of the protocol is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K14.Sim.Good
import Johnson.Desc.ProofFile.Honest.K14.SharedAheadAtHead
import Johnson.Desc.ProofFile.Honest.BookSharedLaw
import Johnson.Desc.ProofFile.Honest.Law.Rule.Tests

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K14
open VerifiableInference.Desc (Place Chain)
open ProofFile.Honest.Small (noneSpent)

/-- The converse of `spentBy_of_noneSpent`. -/
theorem noneSpent_of_spentBy {B : ProverCoinCounts} {o : Addr} (h : ∀ p, B.spentBy o p = []) :
    noneSpent B o = true := by
  unfold noneSpent
  refine List.all_eq_true.2 fun e he => ?_
  by_contra hc
  simp only [Bool.not_eq_true', Bool.not_eq_false, Bool.and_eq_true, Bool.not_eq_true] at hc
  have hc' : e.once = true ∧ (e.owner == o) = true := by simpa using hc
  have : e ∈ B.spentBy o e.spender := by
    unfold ProverCoinCounts.spentBy
    exact List.mem_filter.2 ⟨he, by simp [hc'.1, hc'.2]⟩
  rw [h] at this
  cases this

/-- No entry of the written list names one of the four as its owner. -/
theorem written_clear : ∀ i, (i = 1 ∨ i = 4 ∨ i = 7 ∨ i = 8) →
    writtenShort.all (fun e => e.owner != ⟨place i, 0⟩) = true := by
  rintro i (rfl | rfl | rfl | rfl) <;> decide

variable {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r₀ : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain P5J.TS ProofFile.Cl}
  {x₀ : VerifiableInference.Desc.First.Look.Place}

/-- **OwnClear at a book that `bookWhole` returns.** -/
theorem ownClear_of_whole (h : P5J.AtMgA OnBytes.secondHashFunction Z D r₀ Zp Np cF x₀)
    {p0 p2 : Johnson.G.ChainSends} {M : Merges} {B : ProverCoinCounts}
    (hB : bookWhole (P5J.F0T OnBytes.secondHashFunction Zp Np cF) p0 Johnson.G.proofSendsFull.2.1 p2 M = .ok B) :
    OwnClear B := by
  obtain ⟨l, hl', hf⟩ := bookWhole_spent_known_shared hB
  obtain rfl : l = writtenShort := Except.ok.inj (hl'.symm.trans (sharedAhead_at_head h))
  have hpl := ((VerifiableInference.Desc.FileDescription.planOk_ok _).1 h.laid.planOk).places
  have key : ∀ i, (i = 1 ∨ i = 4 ∨ i = 7 ∨ i = 8) → noneSpent B ⟨place i, 0⟩ = true := by
    intro i hi
    refine noneSpent_of_spentBy fun p => ?_
    rw [(hf ⟨place i, 0⟩ (fun q => absurd (chain_first hpl _ q) (by simp [place]))
      (fun q => absurd (chain_second hpl _ q) (by simp [place]))).1 p]
    unfold ProverCoinCounts.spentBy
    refine List.filter_eq_nil_iff.2 fun e he hc => ?_
    have h1 := List.all_eq_true.1 (written_clear i hi) e he
    simp only [Bool.and_eq_true, beq_iff_eq] at hc
    rw [hc.1.1] at h1
    simp at h1
  exact ⟨key 1 (by simp), key 4 (by simp), key 7 (by simp), key 8 (by simp)⟩

/-- **The coin that "SPLIT" spends**: at the written list its one entry is the 42,853rd coin of "send o_omega", from 0. -/
theorem split_entry_written :
    (writtenShort.filter fun e => e.once && e.spender == ⟨place 8, 0⟩).map
        (fun e => (e.owner, e.start, e.count)) = [(⟨sendPlace 5, 0⟩, ⟨0, 42853⟩, ⟨0, 1⟩)] := by
  decide

/-- **The coefficients that the first fold spends**: at the written list the entry starts at the coin 10,808 of "send o_u". -/
theorem fold_entry_written :
    (writtenShort.filter fun e => e.once && e.spender == ⟨⟨2, none, 9, .K12⟩, 0⟩).map
        (fun e => (e.owner, e.start, e.count)) = [(⟨sendPlace 2, 0⟩, ⟨0, 10808⟩, ⟨0, 15⟩)] := by
  decide

end ProofFile.Honest.K14

#print axioms ProofFile.Honest.K14.noneSpent_of_spentBy
#print axioms ProofFile.Honest.K14.written_clear
#print axioms ProofFile.Honest.K14.ownClear_of_whole
#print axioms ProofFile.Honest.K14.split_entry_written
#print axioms ProofFile.Honest.K14.fold_entry_written
