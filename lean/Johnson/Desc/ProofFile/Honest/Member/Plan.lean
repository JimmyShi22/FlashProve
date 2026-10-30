--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/Member/Plan.lean: the test on the plan, from the proof file's IOP down
to a lot's sub-protocol, by the place. Statements with their proofs.

Where the IOP passes its tests on the plan, every member of the first chain's flat list passes its
own (`IM.plan_flat`, Johnson/IMR/PlanAt.lean, over `planOk_blocks`, Johnson/Desc/PlanPasses.lean).
The library carries that down to the lot's sub-protocol by index (`plan_alone`, `plan_carried`,
`plan_joined`, PlanAt.lean). Here it is carried down for a member at the place, in the forms of
Johnson/Desc/ProofFile/Honest/Member/Statement.lean, whose head lists the member's test on the plan
under what it does not cover.
Main names:
  `AsFlat.planOk`: if m is x as `Chain.blocksInOrder` lays it and m passes its test on the plan, so does x:
    in either arm.
  `plan_at_place`: **at `onlineDescription`, where the IOP passes its tests on the plan: the lot's
    sub-protocol at any place of a kind at which a member stands passes its own.** No other
    premise on the place.
  `plan_at_alone`: the same under `AlonePlace`: a case of `plan_at_place`.
  `plan_at_first`: at a segment's first place, with the test on the plan of the segment's own row of
    `framesOf` beside it.
  `plan_of_own`: from a sub-protocol's `Block.retype` to the sub-protocol.

What is not claimed. That the IOP passes its tests on the plan at any three files: a premise. The
library concludes it from the three public files where `proofDataAndDecisionOfPublicFiles` returns (`laidPOf_ok`,
Johnson/Desc/Laid/ProofFullLaw.lean); its other laws on this IOP conclude it behind an acceptance,
which is of no use where the acceptance is what is to be shown. That a member stands at the place
(Johnson/Desc/ProofFile/Honest/Member/Stands.lean). The first chain's last sub-protocol, of the kind
`frame`, is served by no one name here: `IM.plan_flat`, `member_last`, `AsFlat.planOk`,
`IM.alone_planOk` and `plan_of_own`, in that order, give it. Nothing on soundness, completeness or
hiding.

-/
import Johnson.Desc.ProofFile.Honest.Member.AtLot
import Johnson.IMR.PlanAt
import Johnson.IMR.FirstSeats

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.AtPlace
open VerifiableInference.Desc (Block Chain FileDescription KindName Place)
open VerifiableInference.Desc.First (S)

/-- The test on the plan goes down through `Chain.blocksInOrder`'s layer, in either arm. -/
theorem AsFlat.planOk {σ C : Type} {x m : Block σ C} (h : AsFlat x m) (hp : m.planOk = true) :
    x.planOk = true := by
  rcases h with rfl | rfl
  · exact hp
  · have hp' : (x.planOk && x.hasNoClaimsAndNothingAfter) = true := hp
    exact (Bool.and_eq_true _ _ ▸ hp').1

variable {o : SecondHashFunctionArgument} {pol lay KL : ByteArray} {F : FileDescription Inst} {Z : Pub} {Bs : PureBase}
  {base : List (Block S Cl)} {c : Chain S Cl} {A : SharedSeat} {B : SecondSeat}

/-- Where the IOP passes its tests on the plan, the lot's sub-protocol at a place of `AlonePlace` at
which a member stands passes its own. `plan_at_place` says the same without the premise on the
place. -/
theorem plan_at_alone (O : IM.Open o pol lay KL F Z Bs base c A B) (hp : F.planOk = true)
    {L : Lot} (hL : L ∈ onlineFirstChainBlockTables Z) {b : Block S Cl} (hb : b ∈ L.blocks Bs.G₀)
    (hk : b.place.kind ≠ KindName.frame) (ha : AlonePlace Z b.place) {m : Block S Cl}
    (hm : m ∈ c.blocksInOrder) (hpl : m.place = b.place) : b.planOk = true := by
  obtain ⟨x, hF, hA⟩ := member_alone o pol lay KL F Z Bs base c A B O L hL b hb hk ha m hm hpl
  rw [← IM.alone_planOk hA]
  exact hF.planOk (IM.plan_flat O hp m hm)

/-- Where the IOP passes its tests on the plan, the lot's sub-protocol at a segment's first place at
which a member stands passes its own, and so does the segment's own row of `framesOf`. -/
theorem plan_at_first (O : IM.Open o pol lay KL F Z Bs base c A B) (hp : F.planOk = true)
    {l : Nat} {k : KindName} {L : Lot} (hL : L ∈ onlineFirstChainBlockTables Z) {b : Block S Cl}
    (hb : b ∈ L.blocks Bs.G₀) (hbp : b.place = ⟨1, some l, 1, k⟩) (hk : k ≠ KindName.frame)
    {m : Block S Cl} (hm : m ∈ c.blocksInOrder) (hpl : m.place = b.place) :
    b.planOk = true ∧
      ∃ fs f, Johnson.Desc.First.Walk.Seat.framesOf Z.p.built.links Z.first Z.p.X = .ok fs ∧
        fs[l]? = some f ∧ f.plan = true := by
  have hJ := member_first o pol lay KL F Z Bs base c A B O l k L hL b hb hbp hk m hm hpl
  obtain ⟨fs, f, hfs, hf, e⟩ := hJ.planOk
  have h := IM.plan_flat O hp m hm
  rw [e, Bool.and_eq_true] at h
  exact ⟨h.1, fs, f, hfs, hf, h.2⟩

/-- From the test on the plan of a sub-protocol's `Block.retype` to its own: the first half of
`IM.retype_planOk` (Johnson/IMR/SeatForm.lean). -/
theorem plan_of_own {C : Type} (x : Block S C) (h : (x.retype : Block S Cl).planOk = true) :
    x.planOk = true := (IM.retype_planOk x h).1

/-- **Where the IOP passes its tests on the plan, the lot's sub-protocol at any place of a kind at
which a member stands passes its own**: whether or not something is laid behind it
(`IM.laid_planOk`, Johnson/IMR/SeatForm.lean, at either form of `member_laid`). -/
theorem plan_at_place (O : IM.Open o pol lay KL F Z Bs base c A B) (hp : F.planOk = true)
    {L : Lot} (hL : L ∈ onlineFirstChainBlockTables Z) {b : Block S Cl} (hb : b ∈ L.blocks Bs.G₀)
    (hk : b.place.kind ≠ KindName.frame) {m : Block S Cl} (hm : m ∈ c.blocksInOrder)
    (hpl : m.place = b.place) : b.planOk = true := by
  obtain ⟨x, hF, p, _, _, h⟩ := member_laid Z (pureSeat o Z) Bs base c O.made O.sound O.places
    O.chain L hL b hb hk m hm hpl
  have hx := hF.planOk (IM.plan_flat O hp m hm)
  rcases h with h | ⟨fr, _, _, _, _, h⟩
  · exact IM.laid_planOk (Or.inl h) hx
  · exact IM.laid_planOk (Or.inr ⟨fr.2, h⟩) hx

end ProofFile.Honest.AtPlace

#print axioms ProofFile.Honest.AtPlace.AsFlat.planOk
#print axioms ProofFile.Honest.AtPlace.plan_at_alone
#print axioms ProofFile.Honest.AtPlace.plan_at_first
#print axioms ProofFile.Honest.AtPlace.plan_of_own
#print axioms ProofFile.Honest.AtPlace.plan_at_place
