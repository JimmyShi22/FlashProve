-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/IMR/BookReach.lean: THE TABLE OF JOINTS' PROMISE AT THE PROOF FILE, THE HALF THAT READS THE
VERIFIER's STATE ALONE: «bookAt AT EVERY REACHED STATE» (the premise hB of
Johnson/IMR/HandsReach.lean's book_of_reach · HandsR.of_five · handsR_of_counts | _same and of
Johnson/IMR/HandsReachR.lean's two) IS PAID, IN THE GOALS'
SCOPE, AT THE WRITTEN LIST, AT THE NUMBERS N.withTold placesW (toldOf c.blocksInOrder) (toldOf: Meaning.Carry.toldOf l := l.map fun b => b.oracles.flatten, Johnson/IMR/BookAtCut.lean; whether the constant of that name in other files is the same text is not held here): BY bookAt_whole (Johnson/IMR/BookAtWhole.lean), Reach.fold (Johnson/Top/H0/Walk/Reach.lean) AND border_W (Johnson/IMR/BorderW.lean). SO THE FIELD «book» OF HandsR STANDS AT ALL 358 ROWS, AND EVERY SHARE's hT | hM FALL, AT THE FENCE «REACHED».
  book_reached      hB. PREMISES THAT STAY, ALL bookAt_whole's OWN: K1Told · K2Told (sentences on the plan's texts; said to be proved in K1's and K2's files; not joined) · blocksOk c.blocksInOrder = true (the description's own test on the plan).
  book_all          the field «book» at every row: behind every accepting step from a reached state.
ON WORDS: «the state» is the verifier's state; a «sub-protocol» is a block of the IOP as written in Lean.
What is not claimed. K1Told · K2Told · blocksOk. That the table's real N is N.withTold placesW (toldOf c.blocksInOrder) (the composed meaning's N: P5J.At.N, Johnson/P5J/LettersAt.lean). No soundness.
-/
import Johnson.IMR.HandsReachR
import Johnson.IMR.BorderW
import Johnson.IMR.PlacesScope
import Johnson.IMR.BookAtWhole

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

/-- **bookAt AT EVERY REACHED STATE.** -/
theorem book_reached (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (h1 : Meaning.Carry.K1Told)
    (hT : Meaning.Carry.K2Told) (N : Numbers)
    (hp : VerifiableInference.Desc.blocksOk c.blocksInOrder = true) (p : ProofFile.InstPub) :
    ∀ k s, Reach 0 c.blocksInOrder (ProofFile.startS Z) k (p, s) →
      bookAt (N.withTold placesW (Meaning.Carry.toldOf c.blocksInOrder)) placesW[k]? s =
        true := by
  intro k s h
  obtain ⟨hk, rs, cols, hf⟩ := h.fold
  have hlen : c.blocksInOrder.length = 358 := by
    rw [← List.length_map (f := (·.place)), places_scope hS hR O, places_len]
  rw [hlen] at hk
  have hpk : VerifiableInference.Desc.blocksOk (c.blocksInOrder.take k) = true :=
    List.all_eq_true.2 fun b hb => List.all_eq_true.1 hp b (List.mem_of_mem_take hb)
  exact Meaning.Carry.bookAt_whole hS hR O h1 hT N placesW hk (border_W k hk) hpk p rs cols _ hf

/-- **THE FIELD «book» AT EVERY ROW.** -/
theorem book_all (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (h1 : Meaning.Carry.K1Told)
    (hT : Meaning.Carry.K2Told) (N : Numbers)
    (hp : VerifiableInference.Desc.blocksOk c.blocksInOrder = true) (p : ProofFile.InstPub) {k : ℕ}
    {b : Block S Cl} (hb : c.blocksInOrder[k]? = some b) {s s' : S}
    (hf : RF 0 c.blocksInOrder (ProofFile.startS Z) p k s) (hy : Yes 0 b s s') :
    bookAt (N.withTold placesW (Meaning.Carry.toldOf c.blocksInOrder)) placesW[k + 1]? s' =
      true :=
  book_of_reach (book_reached hS hR O h1 hT N hp p) hb hf hy

end

end IM

#print axioms IM.book_reached
#print axioms IM.book_all
