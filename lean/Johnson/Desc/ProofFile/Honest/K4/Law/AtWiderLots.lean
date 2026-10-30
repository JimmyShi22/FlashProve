-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/AtWiderLots.lean: CONDITIONAL.

What is here. THE FRAME's OWN LEMMA ON K4's ENTRY IN ITS FILLING, HANDED TO OUR STATEMENT THAT TAKES
ITS FORM. `widerFillOwn_k4` (Honest/AtPureWiderLots.lean) says: the lots of `widerFillOwn` hold a
member whose halves at a public part are those of `K4.k4HLot` at that part's reader of the index.
`half_atPure_by` (Law/HalfAtPureBy.lean) takes just that form (∃ M ∈ P.lots, …) and ends in half: at
the place of the member of the layers' own rounds (kind K4) the first chain of the prover that the
frame's maker `onlineProverFromPublicFiles` (Honest/AtPure.lean) returns holds K4's own half. What it is for: that the
two fit is held by Lean here, and by nothing else. half is the hypothesis of that name in
Law/PlaysFive.lean, Law/LookJoinDear.lean and Law/WoTopThr.lean. One statement with its proof: two
calls.

  `half_widerOwn`   **half at `widerFillOwn`, by the frame's own lemma.**

Limits. CONDITIONAL: on h · LaidK4 · hA (the maker returns at that filling: shown here of no files)
· ho (every other lot of the filling has no half at a place of the kind K4, or K4's halves: shown
here of none of the nine). The same end stands in Law/AtWiderAt.lean's proofs by
`k4Lot_mem_widerOwn` and unfolding: two ways to one end. Of h together with LaidK4 · hA · ho no
example is known to us. THE FULL SIZE ALONE, AND THE FORMAT's EARLIER HASH ALONE; that h holds of
any files is not shown here: the side library AtFullSide proves, with no hypothesis, that h has a
member at one place (AtFullSide.Top.headMember_zFull, AtFullSide/Top/HeadMemberAtFull.lean, whose
own Limits say what it is worth). Honest/AtPureWiderLots.lean and what it imports are no part of the
library yet. Beneath `half_atPure_by` stand comparisons by Lean's own kernel that no independent
checker has replayed (Law/HalfAtPure.lean's head names them). IT IS A LAW, NOT A PART: it rests on
modules under Johnson/Goal/: no file that defines a part may build on it; it states no goal. Nothing
on soundness, on completeness or on any other property.
No property is claimed.

-/
import Johnson.Desc.ProofFile.Honest.AtPureWiderLots
import Johnson.Desc.ProofFile.Honest.K4.Law.HalfAtPureBy

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K4
open OnBytes.Desc.First.K4 (Par)
open OnBytes.Desc.First.K4.Honest
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (Chain Block)
open P5J (AtMgA TS)
open ProofFile.Honest.K4.SeatedHead (LaidK4)

/-- CONDITIONAL: on h, Lh, hA and ho. **half AT `widerFillOwn`, BY THE FRAME's OWN LEMMA.** -/
theorem half_widerOwn {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
    {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl} {xh : VerifiableInference.Desc.First.Look.Place}
    (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh) {k m g : ℕ} {x : Bool × Par}
    {blk : Block TS ProofFile.Cl} (Lh : LaidK4 Zp cF k m g x blk) {W₀ X : Type} {own₀ : X}
    {L : LongLots W₀ X} {I : WiderIn W₀} {o : SecondHashFunctionArgument} {S : OnBytes.HonestTrace.Sz}
    {O : OnlineProverArguments} {A : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit X}
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL (widerFillOwn own₀ L I o S O) = .ok A)
    (ho : ∀ M' ∈ (widerFillOwn own₀ L I o S O).lots,
      (∀ y ∈ M'.halves A.Z A.G, y.place.kind ≠ .K4) ∨
      M'.halves A.Z A.G = (k4HLot id (I.weights A.Z) (fun _ _ => k4LookAt)).halves A.Z A.G) :
    A.H.first.find? (fun z => z.place == IM.k4Place g) =
      some (k4Half id (I.weights A.Z) k4Tokens (k4LookAt) (k4PubAt cF k x)) :=
  half_atPure_by h Lh hA id (I.weights A.Z) (fun _ _ => k4LookAt)
    (by
      obtain ⟨M, hm, e⟩ := widerFillOwn_k4 own₀ L I o S O
      exact ⟨M, hm, e A.Z A.G⟩) ho

end ProofFile.Honest.K4

#print axioms ProofFile.Honest.K4.half_widerOwn
