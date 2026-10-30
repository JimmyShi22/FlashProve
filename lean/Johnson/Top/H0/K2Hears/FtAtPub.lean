-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/K2Hears/FtAtPub.lean: the code switch: the number `firstTree` in the numbers of a
place of the kind, as the proof file's description makes them (`P1K2.p2With`,
Johnson/Desc/ProofFile/Lot/K2OfPlan.lean), is 0: the number `ft` of the frame that the rule of
composition has for a file's first chain. Statements and proofs; no definition.

  `pubBy_par`         the field P of the public part Z is what the starts make of the first chain's
                      parameters
  `firstTree_of_pub`  where `ProofFile.pureRoad.pub o` returns Z: Z.P.firstTree = 0
  `p2With_fields`     a place's numbers: firstTree is Z's; read is that of `P1K2.numsAt`
  `ft_of_pub`         THE STATEMENT: p.firstTree = 0
Limits. Nothing says which frame a rule of composition has. No soundness is claimed.

-/
import Johnson.Desc.ProofFile.Lot.K2OfPlan
import Johnson.Desc.ProofFile.Law.MakerPublic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P1K2
open ProofFile (Pub Starts Spot pubBy)
open VerifiableInference.Desc.First.K2 (P2)

theorem pubBy_par
    {made : ByteArray → ByteArray → ByteArray → Except String Johnson.G.OfPlan.Made} {st : Starts}
    {pol lay KL : ByteArray} {Z : Pub} (h : pubBy made st pol lay KL = .ok Z) :
    Z.P = st.par Z.made.p.chains.proof.first := by
  unfold pubBy at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  repeat' split at h
  all_goals first | contradiction | (cases h; rfl)

/-- **At the proof file's description the first chain's first own tree has the number 0.** -/
theorem firstTree_of_pub {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray} {Z : Pub}
    (h : ProofFile.pureRoad.pub o pol lay KL = .ok Z) : Z.P.firstTree = 0 := by
  rw [pubBy_par (show pubBy (ProofFile.PlainG.madeOf o) ProofFile.plainStarts pol lay KL = .ok Z from h)]
  rfl

theorem p2With_fields {P : Prep} {Z : Pub} {sp : Spot} {p : P2} (h : p2With P Z sp = some p) :
    p.firstTree = Z.P.firstTree ∧ ∃ n, numsAt P sp.place.link = some n ∧ p.read = n.read := by
  unfold p2With at h
  obtain ⟨n, hn, rfl⟩ := Option.map_eq_some_iff.1 h
  exact ⟨rfl, n, hn, rfl⟩

/-- **The place's firstTree is 0.** -/
theorem ft_of_pub {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray} {Z : Pub}
    (h : ProofFile.pureRoad.pub o pol lay KL = .ok Z) {P : Prep} {sp : Spot} {p : P2}
    (hp : p2With P Z sp = some p) : p.firstTree = 0 :=
  (p2With_fields hp).1.trans (firstTree_of_pub h)

end P1K2

#print axioms P1K2.pubBy_par
#print axioms P1K2.firstTree_of_pub
#print axioms P1K2.p2With_fields
#print axioms P1K2.ft_of_pub
