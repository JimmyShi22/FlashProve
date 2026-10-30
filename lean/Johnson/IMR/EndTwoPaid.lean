-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/IMR/EndTwoPaid.lean: TWO TESTS ON THE VERIFIER's STATE AT WHATEVER IS
REACHED BY THE WRAPPED SUB-PROTOCOLS' STEPS, AT AN OPENING's LETTERS: the places of the list of
commitment trees are the listed seats (K12.Door.seatsCarriedB), and the statement's oracle
messages' shapes are the listed ones (K12.Door.msgShapesB). Used for
«the one fact on reached states that SH₃'s hR still asks»: its binder hEnd, at 358.

WHAT IS SAID.
  seatsEnd_paid    the first test, at every k (358 is an instance)
  shapesEnd_paid   the second, at every k
  hEnd_paid        **both at 358, in the asker's own letters but for its «h.typed z», which is not
                   asked here: it holds at every z**
HOW. Calls alone: IM.seatsCarried_field | IM.msgShapes_field (Johnson/IMR/SeatsField.lean) at Rch :=
that
very «reached» and at_ := id; reach_raw and Reach.fold carry «reached» to the fold's form;
atFirstSeats | atFirstShapes unfold to the two tests. The debts on the sendings (SendDebts) and on
the shapes (ShapeDebts) are paid inside these two theorems: nothing of them is asked here.

THE PREMISES IN FRONT, BY NAME: hS · hR (the goals' scope; the public files are read) · O (the
opening: free by seat_open) · hF (the IOP as written in Lean passes its tests on the plan) · hB (the
test sendsAreB on the planning program's notices: it follows from hF and PlanWritten.madeRow Z =
true by Johnson/IMR/FivePinned.lean's sends_pinned_paid) · hLd (laidAtCodes returns Ld: the first
and the
third theorem alone) · «reached» · THE FENCE «no mark», WHICH IS SPENT.
What is not claimed. That a state is reached; that the premises can be met together: NO MEMBER.
In that binder (Johnson/Desc/Last/FourAtRcEnd.lean, read) L and M are free letters, bound by its
premise PlanSits alone: that premise is then owed at Ld and msgsOfChain Z.made.proof.1: not shown
here. No soundness.

-/
import Johnson.IMR.SeatsField
import Johnson.Top.H0.Walk.Reach

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace IM

open VerifiableInference.Desc
open VerifiableInference.Desc.First
open VerifiableInference.Desc.K12.Door (laidAtCodes sendsAreB snAt msgsOfChain seatsCarriedB
  msgShapesB)
open ProofFile (Cl)
open Johnson.Desc.First.Walk.Tied (Reach reach_raw)

variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- What is reached by the wrapped sub-protocols' steps is the end of a fold over the first k. -/
theorem fold_of_wrapped : ∀ (k : ℕ) (a : ProofFile.InstPub × S),
    Reach 0 (c.blocksInOrder.map Sound.below) (ProofFile.startS Z) k a → ∃ rs cols r q,
      foldBlocks 0 (c.blocksInOrder.take k) (ProofFile.startS Z (id a).1) rs cols = .ok ((id a).2, r, q) :=
  fun _ _ h => let ⟨_, rs, cols, f⟩ := (reach_raw h).fold; ⟨rs, cols, [], [], f⟩

/-- **The places of the list of commitment trees are the listed seats**, at every reached state
without a mark. -/
theorem seatsEnd_paid (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (hF : F.planOk = true)
    (hB : sendsAreB Z.made.proof.1 358 (snAt Z Bs.G₀ placesW) = true)
    {Ld : VerifiableInference.Desc.K12.Door.Laid}
    (hLd : laidAtCodes Z.first.codes Z.made.proof.1 = some Ld) {k : ℕ} {z : ProofFile.InstPub} {s : S}
    (h : Reach 0 (c.blocksInOrder.map Sound.below) (ProofFile.startS Z) k (z, s)) (hu : s.failed = none) :
    seatsCarriedB Ld s.book = true :=
  seatsCarried_field hS hR O (fun k a => Reach 0 (c.blocksInOrder.map Sound.below) (ProofFile.startS Z) k a) id
    fold_of_wrapped hF hB hLd k (z, s) h hu

/-- **The statement's oracle messages' shapes are the listed ones**, at every reached state without
a mark. -/
theorem shapesEnd_paid (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (hF : F.planOk = true)
    (hB : sendsAreB Z.made.proof.1 358 (snAt Z Bs.G₀ placesW) = true) {k : ℕ} {z : ProofFile.InstPub}
    {s : S} (h : Reach 0 (c.blocksInOrder.map Sound.below) (ProofFile.startS Z) k (z, s))
    (hu : s.failed = none) : msgShapesB (msgsOfChain Z.made.proof.1) s.st = true :=
  msgShapes_field hS hR O (fun k a => Reach 0 (c.blocksInOrder.map Sound.below) (ProofFile.startS Z) k a) id
    fold_of_wrapped hF hB k (z, s) h hu

/-- **Both at the end of the first chain.** -/
theorem hEnd_paid (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (hF : F.planOk = true)
    (hB : sendsAreB Z.made.proof.1 358 (snAt Z Bs.G₀ placesW) = true)
    {Ld : VerifiableInference.Desc.K12.Door.Laid}
    (hLd : laidAtCodes Z.first.codes Z.made.proof.1 = some Ld) :
    ∀ z s, Reach 0 (c.blocksInOrder.map Sound.below) (ProofFile.startS Z) 358 (z, s) → s.failed = none →
      seatsCarriedB Ld s.book = true ∧ msgShapesB (msgsOfChain Z.made.proof.1) s.st = true :=
  fun _ _ h hu => ⟨seatsEnd_paid hS hR O hF hB hLd h hu, shapesEnd_paid hS hR O hF hB h hu⟩

end IM

#print axioms IM.fold_of_wrapped
#print axioms IM.seatsEnd_paid
#print axioms IM.shapesEnd_paid
#print axioms IM.hEnd_paid
