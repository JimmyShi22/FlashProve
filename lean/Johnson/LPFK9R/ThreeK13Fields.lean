-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/LPFK9R/ThreeK13Fields.lean:
THE LIST OF FACTS ON REACHED STATES (Johnson/Desc/First/FoldFacts.lean):
ITS THREE FIELDS ON K13's ROWS ON THE TABLE (pileMasks · pileWithin · oneRow) IN THE FIELDS' OWN
LETTERS, ALL THREE AT ONE AND THE SAME Z A B c: the letters of "onlineDescription's value,
opened" (IM.Open), so that whoever joins them has no ∃ to unify.
  masks_reached     in scope: K13.pileMasksC at every state that the first chain's own
                    sub-protocols reach: Reach.fold (Johnson/Top/H0/Walk/Reach.lean), then
                    fold_masks (MasksByPlace.lean) at pileMasksC_atM3 (PileMasksFields.lean).
                    No test on the list of rounds is asked.
  within_reached    K13.pileWithinC and K13.oneRowC there: the road of descPure_reach_within
                    (Johnson/Desc/AtSeats/WithinSeat.lean) walked at the opened letters: reach_inv ·
                    seatKeeps_within · seatBack_within over open_flat (Johnson/IMR/OpenFlat.lean).
  pileMasks_field_at | pileWithin_field_at | oneRow_field_at
                    GENERAL IN Rch AND at_, ONE PREMISE hRch THAT
                    TIES Rch TO THE WRAPPED "reached"; THE LAST LINE IS THE FIELD's TYPE, SIGN
                    FOR SIGN.
  three_fields      the three as one conjunction.
  pileMasks_rchAt   the first in the form of tidy_field | pileWithin_field | oneRow_field
                    (∃ Z A B c …, at RchAt): beside the last two, to be taken as they lie (not in
                    this library). (Names here end in "_at": none stands twice where both are open.)
THE FENCE "failed = none" IS NOT SPENT.
Limits. Calls alone: no new law. Nothing on soundness.

-/
import Johnson.LPFK9R.MasksByPlace
import Johnson.Desc.K13.Law.PileMasksFields
import Johnson.Desc.AtSeats.FoldFactsPaid
import Johnson.IMR.OpenFlat
import Johnson.Top.H0.Walk.ReachAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LPFK9
open OnBytes OnBytes.Model
open VerifiableInference.Desc
open VerifiableInference.Desc.First
open VerifiableInference.Desc.Sound (below)
open VerifiableInference.Desc.K13.Law (WithinFact withinFact_start reach_inv)
open Johnson.Desc.First.Walk.Tied (Reach reach_raw RchAt rchAt_raw)
open ProofFile (Cl)
open Meaning.K2

section
variable {lay : ByteArray} {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub} {Bs : ProofFile.PureBase}
  {base : List (Block S Cl)} {c : Chain S Cl} {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- **IN SCOPE: "K13.pileMasks" accepts at every reached state of the first chain.** -/
theorem masks_reached {Pp : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} (hS : VerifierAndGoals.InScope Pp = true)
    (hR : VerifierAndGoals.readFiles Pp = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction Pp.pol lay Pp.KL F Z Bs base c A B) (k : ℕ) (a : ProofFile.InstPub × S)
    (h : Reach 0 c.blocksInOrder (ProofFile.startS Z) k a) : K13.pileMasksC a.2 = true := by
  obtain ⟨-, rs, cols, hf⟩ := h.fold
  exact fold_masks (fun _ _ _ _ _ q => VerifiableInference.Desc.K13.Law.pileMasksC_atM3 q) hS hR O
    a.1 0 (c.blocksInOrder.take k) (c.blocksInOrder.drop k) (List.take_append_drop k _).symm rs cols _ hf

/-- **"K13.pileWithin" and "K13.oneRow" accept there**, at the opened letters. -/
theorem within_reached {o : ProofFile.SecondHashFunctionArgument} {pol KL : ByteArray}
    (O : IM.Open o pol lay KL F Z Bs base c A B) (hp : ∀ b ∈ c.blocksInOrder, b.planOk = true) (k : ℕ)
    (a : ProofFile.InstPub × S) (h : Reach 0 c.blocksInOrder (ProofFile.startS Z) k a) : WithinFact a.2 :=
  reach_inv WithinFact
    (fun z => withinFact_start (startS_facts O.pub z).1 (startS_facts O.pub z).2.1
      (startS_facts O.pub z).2.2) hp
    (open_flat seatKeeps_within seatBack_within O trivial (fun _ _ _ => trivial)) h

variable {X : Type} (Rch : Nat → X → Prop) (at_ : X → ProofFile.InstPub × S)

/-- **FoldFacts' FIELD pileMasks.** -/
theorem pileMasks_field_at {Pp : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} (hS : VerifierAndGoals.InScope Pp = true)
    (hR : VerifierAndGoals.readFiles Pp = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction Pp.pol lay Pp.KL F Z Bs base c A B)
    (hRch : ∀ k a, Rch k a → Reach 0 (c.blocksInOrder.map below) (ProofFile.startS Z) k (at_ a)) :
    ∀ k a, Rch k a → (at_ a).2.failed = none → K13.pileMasksC (at_ a).2 = true :=
  fun k a h _ => masks_reached hS hR O k (at_ a) (reach_raw (hRch k a h))

/-- **FoldFacts' FIELD pileWithin.** -/
theorem pileWithin_field_at {o : ProofFile.SecondHashFunctionArgument} {pol KL : ByteArray}
    (O : IM.Open o pol lay KL F Z Bs base c A B) (hF : F.planOk = true)
    (hRch : ∀ k a, Rch k a → Reach 0 (c.blocksInOrder.map below) (ProofFile.startS Z) k (at_ a)) :
    ∀ k a, Rch k a → (at_ a).2.failed = none → K13.pileWithinC (at_ a).2 = true :=
  fun k a h _ => (within_reached O (flat_planOk O.desc hF) k (at_ a) (reach_raw (hRch k a h))).1

/-- **FoldFacts' FIELD oneRow.** -/
theorem oneRow_field_at {o : ProofFile.SecondHashFunctionArgument} {pol KL : ByteArray}
    (O : IM.Open o pol lay KL F Z Bs base c A B) (hF : F.planOk = true)
    (hRch : ∀ k a, Rch k a → Reach 0 (c.blocksInOrder.map below) (ProofFile.startS Z) k (at_ a)) :
    ∀ k a, Rch k a → (at_ a).2.failed = none → K13.oneRowC (at_ a).2 = true :=
  fun k a h _ => (within_reached O (flat_planOk O.desc hF) k (at_ a) (reach_raw (hRch k a h))).2

/-- **The three at once.** -/
theorem three_fields {Pp : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} (hS : VerifierAndGoals.InScope Pp = true)
    (hR : VerifierAndGoals.readFiles Pp = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction Pp.pol lay Pp.KL F Z Bs base c A B) (hF : F.planOk = true)
    (hRch : ∀ k a, Rch k a → Reach 0 (c.blocksInOrder.map below) (ProofFile.startS Z) k (at_ a)) :
    (∀ k a, Rch k a → (at_ a).2.failed = none → K13.pileMasksC (at_ a).2 = true) ∧
      (∀ k a, Rch k a → (at_ a).2.failed = none → K13.pileWithinC (at_ a).2 = true) ∧
      (∀ k a, Rch k a → (at_ a).2.failed = none → K13.oneRowC (at_ a).2 = true) :=
  ⟨pileMasks_field_at Rch at_ hS hR O hRch, pileWithin_field_at Rch at_ O hF hRch,
    oneRow_field_at Rch at_ O hF hRch⟩

end

/-- **pileMasks in the form of tidy_field.** -/
theorem pileMasks_rchAt {Pp : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray}
    {F : FileDescription ProofFile.Inst} (hS : VerifierAndGoals.InScope Pp = true) (hR : VerifierAndGoals.readFiles Pp = .ok pp)
    (h : ProofFile.onlineDescription OnBytes.secondHashFunction Pp.pol lay Pp.KL = .ok F) :
    ∃ (Z : ProofFile.Pub) (A : ProofFile.SharedSeat) (B : ProofFile.SecondSeat) (c : Chain S ProofFile.Cl),
      ProofFile.pureRoad.pub OnBytes.secondHashFunction Pp.pol lay Pp.KL = .ok Z ∧
      F = ProofFile.fileDescBy OnBytes.secondHashFunction ProofFile.pureRoad.links Z A B (fun s => s) (ProofFile.startS Z) c ∧
        ∀ (Str : Type) (k : ℕ) (a : (ProofFile.InstPub × S) × Str),
          RchAt (ProofFile.fileDescBy OnBytes.secondHashFunction ProofFile.pureRoad.links Z A B (fun s => s) (ProofFile.startS Z)
            c) k a →
          a.1.2.failed = none → K13.pileMasksC a.1.2 = true := by
  obtain ⟨Z, Bs, base, c, A, B, O⟩ := IM.seat_open h
  exact ⟨Z, A, B, c, O.pub, O.desc, fun _ n a hr _ => masks_reached hS hR O n a.1 (rchAt_raw hr)⟩

end LPFK9

#print axioms LPFK9.masks_reached
#print axioms LPFK9.within_reached
#print axioms LPFK9.pileMasks_field_at
#print axioms LPFK9.pileWithin_field_at
#print axioms LPFK9.oneRow_field_at
#print axioms LPFK9.three_fields
#print axioms LPFK9.pileMasks_rchAt
