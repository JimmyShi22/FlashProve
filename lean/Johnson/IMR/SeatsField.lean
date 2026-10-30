-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/IMR/SeatsField.lean: TWO FIELDS OF THE STRUCTURE FoldFacts
(Johnson/Desc/First/FoldFacts.lean), WHOLE, each statement ending in the field's own
type: «seatsCarried» at d.L := Ld and «msgShapes» at d.M := msgsOfChain Z.made.proof.1. A join of
laws that stand: no induction is typed here. Statements and proofs.

  fold_whole         a fold over the first k sub-protocols is a fold over the first min k 358
  start_of_noMark    in scope: where a fold from the start at z ends at a state without a mark, the
                     start at z bears no mark
  seatsCarried_field the field «seatsCarried», general in Rch and at_
  msgShapes_field    the field «msgShapes», general in Rch and at_

THE PREMISES IN FRONT, BY NAME, AND WHOSE EACH IS. hS · hR: the goals' scope; the public files are
read · O: the opening (Johnson/IMR/SeatOpen.lean: seat_open gives one wherever ProofFile.onlineDescription returns)
· hRch:
what is reached in Rch's sense is the end of a fold over the first k sub-protocols from the start at
the statement's own public part (the form in which Meaning.K2.groupIs_field asks it;
Reach.fold gives it) · hF : F.planOk = true: the tests on the plan of the IOP as written in Lean ·
hB : sendsAreB … = true: a closed test on the plan's list of rounds against the sendings of the
written list of places · hLd (at seatsCarried_field alone): laidAtCodes … = some Ld: what names Ld.
NONE OF THESE IS SHOWN HERE.
WHAT FALLS AGAINST seats_planOk | shapes_start. «The first state bears no mark»: from the field's
own fence: no mark at the border, so z's request has passed its test (Meaning.K2.reqOk_of_noMark,
Johnson/IMR/AtReach.lean), so the start is not the blank state (Meaning.K2.start_noMark,
Johnson/IMR/EndFive.lean) ·
«k ≤ 358»: beyond 358 the first k are the whole list (Meaning.K2.flat_358).
CALLED, NOT TYPED: seats_planOk · debts_final · hp_of_planOk (SendsFinal.lean) · k2Fences_paid
(Johnson/IMR/SendsFences.lean) · shapes_start (Johnson/IMR/ShapesJoin.lean) · shapeDebts_fenced
(Johnson/IMR/ShapesK2.lean) ·
k12_shape_debt (ShapesK12.lean) · blocksOk_of_planOk (PlanOkFlat.lean) · reach_of_fold
(Johnson/Top/H0/Walk/Reach.lean) · H2K.Made.p12OfMade_own (Johnson/Desc/K12/Law/OwnMaskAtLast.lean).
What is not claimed. The structure FoldFacts is not imported here: that each end is its field's type
is checked by Lean in Johnson/IMR/AtReachFits.lean. That the premises can be met together. THE
FOLD's ROUNDS
AND COLUMNS inside hRch are bound under «there are»: no conclusion names them. No soundness.

-/
import Johnson.IMR.SendsFinal
import Johnson.IMR.ShapesK2
import Johnson.IMR.ShapesK12
import Johnson.IMR.EndFive

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace IM

open VerifiableInference.Desc (Block Chain FileDescription Place OpenedColumn foldBlocks)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.K12.Door (snAt sendsAreB laidAtCodes msgsOfChain)
open Johnson.Desc.First.Walk.Tied (reach_of_fold)
open ProofFile (Cl)

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- In scope the first k sub-protocols are the first min k 358. -/
theorem fold_whole (hS : VerifierAndGoals.InScope P = true)
    (O : Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (k : ℕ) :
    c.blocksInOrder.take k = c.blocksInOrder.take (min k 358) := by
  have hlen := Meaning.K2.flat_358 hS O
  rcases Nat.le_total k 358 with h | h
  · rw [Nat.min_eq_left h]
  · rw [Nat.min_eq_right h, List.take_of_length_le (by omega), List.take_of_length_le (by omega)]

/-- **The fence shuts the blank start out.** -/
theorem start_of_noMark (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {k : ℕ} (hk : k ≤ 358)
    {z : ProofFile.InstPub} {s : S} {rs r : List Fmt.RoundView} {cols q : List OpenedColumn}
    (hf : foldBlocks 0 (c.blocksInOrder.take k) (ProofFile.startS Z z) rs cols = .ok (s, r, q))
    (hu : s.failed = none) : (ProofFile.startS Z z).failed = none := by
  have hlen := Meaning.K2.flat_358 hS O
  exact Meaning.K2.start_noMark O.pub
    (Meaning.K2.reqOk_of_noMark hS hR O (reach_of_fold k (by omega) s rs r cols q hf) hu)

/-- **Field seatsCarried, whole**, at d.L := Ld. -/
theorem seatsCarried_field (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {X : Type} (Rch : ℕ → X → Prop)
    (at_ : X → ProofFile.InstPub × S)
    (hRch : ∀ k a, Rch k a → ∃ rs cols r q,
      foldBlocks 0 (c.blocksInOrder.take k) (ProofFile.startS Z (at_ a).1) rs cols = .ok ((at_ a).2, r, q))
    (hF : F.planOk = true)
    (hB : sendsAreB Z.made.proof.1 358 (snAt Z Bs.G₀ placesW) = true)
    {Ld : VerifiableInference.Desc.K12.Door.Laid}
    (hLd : laidAtCodes Z.first.codes Z.made.proof.1 = some Ld) :
    ∀ k a, Rch k a → (at_ a).2.failed = none →
      VerifiableInference.Desc.K12.Door.atFirstSeats Ld (at_ a).2 = true := by
  intro k a hr hu
  obtain ⟨rs, cols, r, q, hf⟩ := hRch k a hr
  rw [fold_whole hS O k] at hf
  have hk : min k 358 ≤ 358 := Nat.min_le_right _ _
  exact (seats_planOk hS hR O (at_ a).1 hF (start_of_noMark hS hR O hk hf hu) hB hLd hk hf).1

/-- **Field msgShapes, whole**, at d.M := msgsOfChain Z.made.proof.1. -/
theorem msgShapes_field (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {X : Type} (Rch : ℕ → X → Prop)
    (at_ : X → ProofFile.InstPub × S)
    (hRch : ∀ k a, Rch k a → ∃ rs cols r q,
      foldBlocks 0 (c.blocksInOrder.take k) (ProofFile.startS Z (at_ a).1) rs cols = .ok ((at_ a).2, r, q))
    (hF : F.planOk = true)
    (hB : sendsAreB Z.made.proof.1 358 (snAt Z Bs.G₀ placesW) = true) :
    ∀ k a, Rch k a → (at_ a).2.failed = none →
      VerifiableInference.Desc.K12.Door.atFirstShapes (msgsOfChain Z.made.proof.1) (at_ a).2 =
        true := by
  intro k a hr hu
  obtain ⟨rs, cols, r, q, hf⟩ := hRch k a hr
  rw [fold_whole hS O k] at hf
  have hk : min k 358 ≤ 358 := Nat.min_le_right _ _
  have hpl := blocksOk_of_planOk O hF
  exact shapes_start hS hR O (at_ a).1 (debts_final hS hR O (at_ a).1 hpl)
    (shapeDebts_fenced hS hR O (k2Fences_paid hS hR O (at_ a).1)
      (k12_shape_debt (hp_of_planOk hS hR O hpl) (H2K.Made.p12OfMade_own _)))
    hB (start_of_noMark hS hR O hk hf hu) hk hf

end

end IM

#print axioms IM.fold_whole
#print axioms IM.start_of_noMark
#print axioms IM.seatsCarried_field
#print axioms IM.msgShapes_field
