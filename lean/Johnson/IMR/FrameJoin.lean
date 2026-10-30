-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/IMR/FrameJoin.lean: THE ONE PREMISE OF Johnson/IMR/FrameClosed.lean's
frameIs_field1, CountsBy, JOINED TO THE COUNTS ALONG THE FOLD (Johnson/IMR/BookAtWhole.lean's
bookAt_whole, with Johnson/IMR/BorderW.lean's border_W for its premise on the borders).
  counts_told: CountsBy c Z (cntOf N') at N' := N.withTold IM.placesW (Meaning.Carry.toldOf c.blocksInOrder),
    at every table of numbers N.
  frameIs_field0: THE TOP: the field "frameIs" at ownAt and keptAt := the terms with code at
    Z.first.shape, THAT N', IM.linksW, IM.placesW and any built.
WHICH N A CALLER MUST LAY: the table of numbers that fills ownAt and keptAt must BE N.withTold
IM.placesW (toldOf c.blocksInOrder) for some N: its msgsAt are then the counts that the flat list's own
entries tell. At another table of numbers nothing is said here.
WHAT IS STILL PREMISED, each by name: K1Told and K2Told (two sentences on the texts of kinds K1 and
K2, with no state in them: the tenants that a sending's entry tells are as many as the messages that
it sends), and blocksOk c.blocksInOrder = true (every entry of the flat list passes its own test on the list
of rounds and is shaped).
OBJECT: ProofFile.onlineDescription's value at OnBytes.secondHashFunction, in scope. USERS: whoever makes a value of the list
of facts along the fold.
Every theorem on states starts from the premise that a fold returns; no proof file is exhibited for
which one does. No soundness.
-/
import Johnson.IMR.FrameClosed
import Johnson.IMR.BookAtWhole
import Johnson.IMR.BorderW

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

/-- **THE FIRST NAMED PREMISE, at the table of numbers that bears what the flat list's entries
tell.** -/
theorem counts_told (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (h1 : Meaning.Carry.K1Told)
    (hT : Meaning.Carry.K2Told) (hp : blocksOk c.blocksInOrder = true) (N : Numbers) :
    CountsBy c Z (cntOf (N.withTold IM.placesW (Meaning.Carry.toldOf c.blocksInOrder))) :=
  counts_of_bookAt fun p R C k r hk f =>
    Meaning.Carry.bookAt_whole hS hR O h1 hT N IM.placesW hk (IM.border_W k hk)
      (List.all_eq_true.2 fun b hb => List.all_eq_true.1 hp b (List.mem_of_mem_take hb)) p R C r f

/-- **THE FIELD "frameIs", UNDER K1Told, K2Told AND THE FLAT LIST's OWN TESTS.** -/
theorem frameIs_field0 (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (h1 : Meaning.Carry.K1Told)
    (hT : Meaning.Carry.K2Told) (hp : blocksOk c.blocksInOrder = true) (N : Numbers)
    (built : Array Stages.LinkH) {X : Type} (Rch : Nat → X → Prop) (at_ : X → ProofFile.InstPub × S)
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
  frameIs_field1 hS hR O _ built (counts_told hS hR O h1 hT hp N) Rch at_ hRch

end

#print axioms counts_told
#print axioms frameIs_field0

end Meaning.K2
