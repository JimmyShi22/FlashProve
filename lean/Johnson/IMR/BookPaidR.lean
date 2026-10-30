-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/IMR/BookPaidR.lean: THE TABLE OF JOINTS' PROMISE AT THE PROOF FILE, THE HALF THAT READS THE VERIFIER's STATE: Johnson/IMR/BookReach.lean's book_reached | book_all WITHOUT THE TWO SENTENCES ON THE PLAN's TEXTS: K1Told | K2Told ARE LAID IN: k1Told_paid | k2Told_paid (Johnson/IMR/ToldPaid.lean: over Johnson/Desc/K1/Law/ToldCounts.lean and Johnson/Top/H0/Tw/K2C/ToldTenants.lean), no premise. Compiled with the whole library.
  book_reached_paid   hB OF Johnson/IMR/HandsReach.lean's TOOLS, IN SCOPE, UNDER blocksOk c.blocksInOrder =
                      true ALONE.
  book_all_paid       the field «book» behind every accepting step from a reached state, at every row, under that alone.
  book_reached_planOk hB from F.planOk = true (Johnson/IMR/PlanOkFlat.lean).
ON WORDS: «the state» is the verifier's state; a «sub-protocol» is a block of the IOP as written in Lean.
What is not claimed. blocksOk c.blocksInOrder = true. That the table's real N is N.withTold placesW (toldOf c.blocksInOrder). No soundness.
-/
import Johnson.IMR.BookReach
import Johnson.IMR.PlanOkFlat
import Johnson.IMR.ToldPaid

set_option autoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace IM

open VerifiableInference.Desc (Block Chain FileDescription Place OpenedColumn)
open VerifiableInference.Desc.First (S Numbers bookAt)
open Johnson.Desc.First.Walk.Tied (Reach)
open ProofFile (Cl)

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub}
  {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl} {A : ProofFile.SharedSeat}
  {B : ProofFile.SecondSeat}

theorem book_reached_paid (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (N : Numbers)
    (hp : VerifiableInference.Desc.blocksOk c.blocksInOrder = true) (p : ProofFile.InstPub) :
    ∀ k s, Reach 0 c.blocksInOrder (ProofFile.startS Z) k (p, s) →
      bookAt (N.withTold placesW (Meaning.Carry.toldOf c.blocksInOrder)) placesW[k]? s = true :=
  book_reached hS hR O Meaning.Carry.k1Told_paid Meaning.Carry.k2Told_paid N hp p

theorem book_all_paid (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (N : Numbers)
    (hp : VerifiableInference.Desc.blocksOk c.blocksInOrder = true) (p : ProofFile.InstPub) {k : ℕ}
    {b : Block S Cl} (hb : c.blocksInOrder[k]? = some b) {s s' : S}
    (hf : RF 0 c.blocksInOrder (ProofFile.startS Z) p k s) (hy : Yes 0 b s s') :
    bookAt (N.withTold placesW (Meaning.Carry.toldOf c.blocksInOrder)) placesW[k + 1]? s' = true :=
  book_all hS hR O Meaning.Carry.k1Told_paid Meaning.Carry.k2Told_paid N hp p hb hf hy

/-- **hB FROM THE DESCRIPTION's OWN TESTS ON THE PLAN.** -/
theorem book_reached_planOk (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (N : Numbers)
    (hF : F.planOk = true) (p : ProofFile.InstPub) :
    ∀ k s, Reach 0 c.blocksInOrder (ProofFile.startS Z) k (p, s) →
      bookAt (N.withTold placesW (Meaning.Carry.toldOf c.blocksInOrder)) placesW[k]? s = true :=
  book_reached_paid hS hR O N (blocksOk_of_planOk O hF) p

end

end IM

#print axioms IM.book_reached_planOk
#print axioms IM.book_reached_paid
#print axioms IM.book_all_paid
