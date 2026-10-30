-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/IMR/FramePaid.lean: THE FIELD "frameIs" OF THE LIST OF FACTS ALONG THE
FOLD, UNDER THE FLAT LIST's OWN TESTS ALONE: Johnson/IMR/FrameJoin.lean's two theorems at
Johnson/IMR/ToldPaid.lean's
k1Told_paid and k2Told_paid.
  counts_paid: CountsBy c Z (cntOf N') at N' := N.withTold IM.placesW (Meaning.Carry.toldOf c.blocksInOrder).
  frameIs_paid: THE TOP: the field at ownAt and keptAt := the terms with code at Z.first.shape, THAT
    N', IM.linksW, IM.placesW and any built (these terms do not read built).
WHICH N A CALLER MUST LAY: the table of numbers that fills ownAt and keptAt must BE N.withTold
IM.placesW (toldOf c.blocksInOrder) for some N. At another table of numbers nothing is said here.
WHAT IS STILL PREMISED: blocksOk c.blocksInOrder = true: of every entry b of the flat list: b.planOk (its own
test on the list of rounds) and b.shaped. And, as everywhere: the goals' scope and our seats'
opening.
OBJECT: ProofFile.onlineDescription's value at OnBytes.secondHashFunction, in scope. USERS: whoever makes a value of the list
of facts along the fold.
Every theorem on states starts from the premise that a fold returns; no proof file is exhibited for
which one does. No soundness.
-/
import Johnson.IMR.FrameJoin
import Johnson.IMR.ToldPaid

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Meaning.K2

open OnBytes OnBytes.Model
open VerifiableInference.Desc
open VerifiableInference.Desc.First
open ProofFile (Cl)

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

theorem counts_paid (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    (hp : blocksOk c.blocksInOrder = true) (N : Numbers) :
    CountsBy c Z (cntOf (N.withTold IM.placesW (Meaning.Carry.toldOf c.blocksInOrder))) :=
  counts_told hS hR O Meaning.Carry.k1Told_paid Meaning.Carry.k2Told_paid hp N

/-- **THE FIELD "frameIs", UNDER THE FLAT LIST's OWN TESTS ALONE.** -/
theorem frameIs_paid (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    (hp : blocksOk c.blocksInOrder = true) (N : Numbers) (built : Array Stages.LinkH) {X : Type}
    (Rch : Nat → X → Prop) (at_ : X → ProofFile.InstPub × S)
    (hRch : ∀ k a, Rch k a → ∃ rs cols r q,
      foldBlocks 0 (c.blocksInOrder.take k) (ProofFile.startS Z (at_ a).1) rs cols = .ok ((at_ a).2, r, q)) :
    ∀ k a p m L, Rch k a → (at_ a).2.failed = none → IM.placesW[k]? = some p → p.link = some m →
      (at_ a).2.link? = some L →
      L.check.frame.moment = momentW (shiftW m) p.piece ∧
        L.check.frame.own = FillSent.ownAt Z.first.shape
          (N.withTold IM.placesW (Meaning.Carry.toldOf c.blocksInOrder)) IM.linksW IM.placesW built m
          (momentW (shiftW m) p.piece) ∧
        L.check.frame.keptBefore = FillSent.keptAt Z.first.shape
          (N.withTold IM.placesW (Meaning.Carry.toldOf c.blocksInOrder)) IM.linksW IM.placesW built m ∧
        (p.piece ≤ 11 + 2 * shiftW m →
          L.check.frame.link = m ∧ L.check.frame.next = .laterOrClose) :=
  frameIs_field0 hS hR O Meaning.Carry.k1Told_paid Meaning.Carry.k2Told_paid hp N built Rch at_ hRch

end

#print axioms counts_paid
#print axioms frameIs_paid

end Meaning.K2
