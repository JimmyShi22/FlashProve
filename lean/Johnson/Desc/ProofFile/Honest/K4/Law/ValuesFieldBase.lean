-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K4/Law/ValuesFieldBase.lean: CONDITIONAL on h and hA (the general statement on hM, hE and ho too), and on hB, which only
names the table's base and follows from h.

What is here. THE FIELD "layers" (`ValuesJ` at the twelve members 28 g + 4 of the feed-forward layers' own rounds, sub-protocol K4; Law/ValuesField.lean) WITH
ITS TWO PREMISES half AND hf PAID, at the threads' writers' one term for the first chain, `firstThread h parts w`
(Honest/Thread/TheFirstThread.lean), at the falls of that thread's own list, at EVERY J and Said. First general in the filling, with K4's lot among its
lots; then at the wider filling at the index of matrices, whose return is the base prover, with no premise but the head at the return, the return,
and hB.

  `k4_layers_field_first_thread`   general in the filling: half by `half_atPure_at` (Law/HalfAtPureBy.lean), hf by `hf_head` (Law/HalfHead.lean) at
      `k4_falls_first` (Law/TwoAtFirstThread.lean) and `k4Fall_mem_atPure` (Law/FillFalls.lean), each at the member's own `LaidK4` (`laid_at`)
  **`k4_layers_field_base`**   at the base prover: K4's lot by `k4_lot_at_widerFillAtCPUOWM` (Law/LotThrough.lean)

IT IS `ValuesJ`: ONE PREMISE OF THE RULE FOR `AcceptedJ` AND `NextJ`, NOT THESE TWO: the rule still wants that the run on shapes returns, the fit of what is played
(`FitsAt`, or the test `halved`), and in the gathering structure's form the other fields. THE MEMBER's TEST ON VALUES READS NO VALUE THAT K4's SIDE SENDS
(Law/ValuesAtMember.lean's head).

Limits. NO STAND OF THE THREAD BEYOND BORDER 0 IS KNOWN: where the thread does not stand in front of a member, where a fall of the list speaks there, or
where the side has not played, the statement is idle. h and hA: their payers are named in Law/TwoAtFirstThread.lean's head; at one triple of files both
are had together (`base_met_zFull`, Law/BaseMetAtFull.lean, no row). It stands over files that are no rows of laws.14, Law/TwoAtFirstThread.lean and what lies
beneath it among them, and so over comparisons by Lean's kernel that no independent checker has replayed (Law/HalfAtPureBy.lean; Law/LookJoinDear.lean).
THE FULL SIZE ALONE; the format's second hash function alone. Nothing on what any value is worth.
No property is claimed.
A LAW, NOT A PART: it rests on modules under Johnson/Goal/: no file that defines a part of the proof file's description may import this one.
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.ValuesAtHead
import Johnson.Desc.ProofFile.Honest.K4.Law.TwoAtFirstThread

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K4
open OnBytes OnBytes.Model
open OnBytes.Desc.First.K4 (Par)
open OnBytes.Desc.First.K4.Honest (K4Pub)
open VerifiableInference.Desc (Block)
open P5J (TS)
open ProofFile.Honest.K4.SeatedHead (LaidK4 laid_at)
open ProofFile.Honest.FirstThread (HeadAtReturn FirstThreadParts firstThread firstFalls)
open Johnson.AtFull.Shape (Tab.g Tab.vals firstZA)

variable {W₀ Rc Tr X₀ X' : Type} {files : VerifierAndGoals.PublicFiles} {A : OnlineProverWithDescription W₀ Rc Tr X₀ X'}
  (h : HeadAtReturn files A) (parts : FirstThreadParts A) (w : Local W₀ Rc ProofFile.Inst Tr)
  (Said : Nat → Coins A.B → Mid (Local W₀ Rc ProofFile.Inst Tr) X' → Prop)

/-- CONDITIONAL on h, hB, hA, hM, hE and ho. **THE FIELD "layers" AT THE FIRST THREAD, AT THE FALLS OF THAT THREAD's OWN LIST**, general in the filling. -/
theorem k4_layers_field_first_thread {Bs : ProofFile.PureBase}
    (hB : ProofFile.baseOf A.Z (ProofFile.pureSeat OnBytes.secondHashFunction A.Z) = .ok Bs) {P : OnlineProverParts W₀ Rc Tr X₀ X'}
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction files.pol files.lay files.KL P = .ok A)
    (cells : Tr → Cells) (weights : W₀ → Weights)
    (look : ProofFile.Pub → ProofFile.Ground → K4Pub → List Fmt.Drawn → Forest.Heard)
    {M : HLot (Local W₀ Rc ProofFile.Inst Tr) (Local W₀ Rc ProofFile.Inst Tr) X'} (hM : M ∈ P.lots)
    (hE : M.halves A.Z A.G = (k4HLot cells weights look).halves A.Z A.G)
    (ho : ∀ M' ∈ P.lots, (∀ y ∈ M'.halves A.Z A.G, y.place.kind ≠ .K4) ∨
      M'.halves A.Z A.G = (k4HLot cells weights look).halves A.Z A.G)
    (J : Nat → TS → Prop) :
    ∀ l, l < 24 → l % 2 = 0 →
      ValuesJ (firstThread h parts w) Said J (firstZA (Tab.g A.Z Bs.G₀) (Tab.vals A.Z Bs.G₀))
        (fallsBy (firstFalls A parts.numbers) h.firstChain.blocksInOrder) (14 * l + 3 + 1) := by
  intro l hl he
  obtain ⟨g, rfl⟩ : ∃ g, l = 2 * g := ⟨l / 2, by omega⟩
  obtain ⟨x, blk, Lh⟩ := laid_at h.head (show g < 12 by omega)
  have e : 14 * (2 * g) + 3 + 1 = 28 * g + 4 := by omega
  rw [e]
  exact valuesJ_of _ Said (k4_layers_values h.head A.H _ _ _ _ _ _ _ _ _ _ w hB Lh
    (half_atPure_at h.head Lh hA cells weights look hM hE ho)
    (hf_head Lh (k4_falls_first h parts hA _ (k4Fall_mem_atPure h.head Lh hA))))

end ProofFile.Honest.K4

namespace ProofFile.Honest.K4
open ProofFile.Honest.Term (matrixInput)
open ProofFile.Honest.FirstThread (HeadAtReturn FirstThreadParts firstThread firstFalls)
open Johnson.AtFull.Shape (Tab.g Tab.vals firstZA)
open P5J (TS)

variable {files : VerifierAndGoals.PublicFiles} {A : OnlineProverWithDescription AtPublicFiles.AtFiles.FullSizeMatrix IndexCommitterCoins Cells Unit Unit}
  (h : HeadAtReturn files A) (parts : FirstThreadParts A)
  (w : Local AtPublicFiles.AtFiles.FullSizeMatrix IndexCommitterCoins ProofFile.Inst Cells)
  (Said : Nat → Coins A.B → Mid (Local AtPublicFiles.AtFiles.FullSizeMatrix IndexCommitterCoins ProofFile.Inst Cells) Unit → Prop)

/-- CONDITIONAL on h, hB and hA. **THE FIELD "layers" AT THE BASE PROVER.** -/
theorem k4_layers_field_base {Bs : ProofFile.PureBase}
    (hB : ProofFile.baseOf A.Z (ProofFile.pureSeat OnBytes.secondHashFunction A.Z) = .ok Bs)
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction files.pol files.lay files.KL
      (onlineProverPartsInUse matrixInput OnBytes.secondHashFunction OnBytes.HonestTrace.Sz.ref openHonest) = .ok A)
    (J : Nat → TS → Prop) :
    ∀ l, l < 24 → l % 2 = 0 →
      ValuesJ (firstThread h parts w) Said J (firstZA (Tab.g A.Z Bs.G₀) (Tab.vals A.Z Bs.G₀))
        (fallsBy (firstFalls A parts.numbers) h.firstChain.blocksInOrder) (14 * l + 3 + 1) := by
  obtain ⟨⟨M, hM, hE⟩, ho⟩ := k4_lot_at_widerFillAtCPUOWM matrixInput OnBytes.secondHashFunction
    OnBytes.HonestTrace.Sz.ref openHonest A.Z A.G
  exact k4_layers_field_first_thread h parts w Said hB hA _ _ _ hM hE ho J

end ProofFile.Honest.K4

#print axioms ProofFile.Honest.K4.k4_layers_field_first_thread
#print axioms ProofFile.Honest.K4.k4_layers_field_base
