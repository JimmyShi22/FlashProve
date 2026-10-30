-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P1K8R/ThirdTie.lean: AT EVERY STATE THAT THE FIRST CHAIN's OWN BLOCKS REACH IN FRONT OF A
SEGMENT's BATCHING THE DATA's THIRD ARRAY OF READS IS NUMBER 0, AND ARRAY 0, WHICH IS ALSO EVERY
ATTENTION PLAN's OWN NUMBER OF THAT ARRAY, IS APART THERE (LinkJoin.ApartAt,
Johnson/Desc/First/Link/Law/OkJoin.lean). UNDER THE SCOPE, THE FILES READ AND IM.Open. Lemmas; none
of the library's goals. No prover stands in them; nothing on completeness, soundness or hiding.

  `u2_of_units`, **`u2_at_batch`**   the third clause of `unitsLaid`
      (Johnson/Desc/K8/Honest/FallCount.lean); at all 25 segments, by `units_at_batch`
      (Johnson/P1K8R/UnitsAtBatch.lean), `units_at_batch_att`, `units_at_batch_head`
      (UnitsAtBatchAll.lean)
  `tree_of_laid`, **`apartAt_of_tests`**   no state stands in them: where the third array of reads
      is t, `apartB` (Johnson/Desc/K8/Honest/ApartOf.lean) and `piecesLaid` (PiecesLaid.lean) give
      LinkJoin.ApartAt at t: three of its clauses are `apartB`'s; every piece lies in the digits'
      array
  **`apartAt_zero`**, **`apartAt_iU3`**   so at a reached state, by `apart_at_batch`
      (Johnson/P1K8R/ApartAtBatch.lean) and `public_at_batch` (PublicAtBatch.lean); the second by
      P1K2.att_u3 (Johnson/P1K2R/K5RestScope.lean) besides
The like elsewhere: LinkJoin.StaticOk's field apart has it from closed clauses of a built segment
(Johnson/P1K8R/StaticAtBatch.lean carries these to a reached state); K9Asks has a test with code for
it (Johnson/Desc/First/Link/Law/K9AsksLaw.lean); on the number alone, at the blanked data and at the
states that the wrapped blocks reach: LinkJoin.hU_att (AttThirdVector.lean).
Limits. Nothing on whether any state is reached.
Terms: lean/GLOSSARY.md.

-/
import Johnson.P1K8R.UnitsAtBatch
import Johnson.P1K8R.UnitsAtBatchAll
import Johnson.P1K8R.ApartAtBatch
import Johnson.P1K8R.PublicAtBatch
import Johnson.P1K2R.K5RestScope
import Johnson.Desc.First.Link.Law.OkJoin

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P1K8
open OnBytes OnBytes.Model OnBytes.Model.HTailF2
open OnBytes.Model.Stages (LinkH)
open VerifiableInference VerifiableInference.Desc VerifiableInference.Desc.First
open VerifiableInference.Desc.First.K8.Honest
open Johnson.Desc.First.Walk.Tied (Reach)

/-- The test on the vectors of reads says which array the third is. -/
theorem u2_of_units {nU : Array Nat} {tl : HTailF2} {tU : Nat} (h : unitsLaid nU tl tU = true) :
    tl.ix.U.getD 2 none = some tU := by
  simp only [unitsLaid, Bool.and_eq_true, beq_iff_eq] at h
  exact h.1.1.1.1.1.2

/-- Where the two calls' pieces lie as the test says, each lies in the digits' array. -/
theorem tree_of_laid {tl : HTailF2} (h : piecesLaid tl = true) (k : Nat) (p : Piece)
    (hp : p ∈ (tl.zOf k).pieces.toList) : p.tree = tl.ix.ZZ := by
  simp only [piecesLaid, Bool.and_eq_true, beq_iff_eq] at h
  unfold HTailF2.zOf at hp
  split at hp
  · have hm : pieceKey p ∈ tl.z1.pieces.toList.map pieceKey := List.mem_map_of_mem hp
    rw [h.1] at hm
    obtain ⟨i, -, e⟩ := List.mem_map.1 hm
    exact (congrArg (·.1) e).symm
  · have hm : pieceKey p ∈ tl.z2.pieces.toList.map pieceKey := List.mem_map_of_mem hp
    rw [h.2] at hm
    obtain ⟨i, -, e⟩ := List.mem_map.1 hm
    exact (congrArg (·.1) e).symm

/-- **The third array of reads is apart (LinkJoin.ApartAt), from two tests on public numbers.** No
state stands in it. -/
theorem apartAt_of_tests {tl : HTailF2} {t : Nat} (hU : tl.ix.U.getD 2 none = some t)
    (hA : apartB tl = true) (hP : piecesLaid tl = true) : LinkJoin.ApartAt tl t := by
  obtain ⟨-, -, ⟨a1, a2⟩, a3⟩ := (apartB_iff tl).1 hA
  have e : (tl.ix.U.getD 2 none).getD 0 = t := by rw [hU]; rfl
  rw [e] at a1 a2
  refine ⟨2, by omega, hU, fun q => a1 q.symm, fun q => a2 q.symm, fun mu hm q => ?_,
    fun k p hp q => ?_⟩
  · have a4 := (a3 mu hm).2.2.2
    rw [e] at a4
    exact a4 q.symm
  · exact a1 ((tree_of_laid hP k p hp).symm.trans q).symm

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Claim)} {c : Chain S Claim}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- **At a state reached in front of a segment's batching the data's third array of reads is
number 0**, at all 25 segments. -/
theorem u2_at_batch (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {l : ℕ} (hl : l < 25)
    {z : ProofFile.InstPub} {s : S}
    (h : Reach 0 c.blocksInOrder (ProofFile.startS Z) (14 * l + (if l = 24 then 11 else 9)) (z, s)) :
    ∃ tl, s.tl? = some tl ∧ tl.ix.U.getD 2 none = some 0 := by
  by_cases h24 : l = 24
  · subst h24
    obtain ⟨X, tl, -, ht, hu⟩ := units_at_batch_head hS hR O h
    exact ⟨tl, ht, u2_of_units hu⟩
  · rw [if_neg h24] at h
    by_cases he : l % 2 = 0
    · obtain ⟨X, tl, -, ht, hu⟩ := units_at_batch hS hR O hl
        (by unfold IM.subAt; rw [if_neg h24, if_pos he]) h
      exact ⟨tl, ht, u2_of_units hu⟩
    · obtain ⟨X, tl, -, ht, hu⟩ := units_at_batch_att hS hR O hl
        (by unfold IM.subAt; rw [if_neg h24, if_neg he]) h
      exact ⟨tl, ht, u2_of_units hu⟩

/-- **THE THIRD TIE**: at such a state array 0 is apart from the digits', the planes', the symbols'
and the pieces' arrays, at the state's own data. -/
theorem apartAt_zero (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {l : ℕ} (hl : l < 25)
    {z : ProofFile.InstPub} {s : S}
    (h : Reach 0 c.blocksInOrder (ProofFile.startS Z) (14 * l + (if l = 24 then 11 else 9)) (z, s))
    {tl : HTailF2} (ht : s.tl? = some tl) : LinkJoin.ApartAt tl 0 := by
  obtain ⟨t1, h1, hu⟩ := u2_at_batch hS hR O hl h
  obtain ⟨t2, h2, ha, -⟩ := apart_at_batch hS hR O hl h
  obtain ⟨t3, h3, hp, -, -⟩ := public_at_batch hS hR O hl h
  obtain rfl : tl = t1 := Option.some.inj (ht.symm.trans h1)
  obtain rfl : tl = t2 := Option.some.inj (ht.symm.trans h2)
  obtain rfl : tl = t3 := Option.some.inj (ht.symm.trans h3)
  exact apartAt_of_tests hu ha hp

/-- **The like at an attention plan's own number of that array**, which is 0. -/
theorem apartAt_iU3 (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {l : ℕ} (hl : l < 25)
    {z : ProofFile.InstPub} {s : S}
    (h : Reach 0 c.blocksInOrder (ProofFile.startS Z) (14 * l + (if l = 24 then 11 else 9)) (z, s))
    {tl : HTailF2} (ht : s.tl? = some tl) {g : ℕ} {Ap : Attention.Plan}
    (hA : Bs.G₀.W.A[g]? = some Ap) : LinkJoin.ApartAt tl Ap.iU3 := by
  rw [(P1K2.att_u3 O.public hA).1]
  exact apartAt_zero hS hR O hl h ht

end

end P1K8

#print axioms P1K8.u2_of_units
#print axioms P1K8.tree_of_laid
#print axioms P1K8.apartAt_of_tests
#print axioms P1K8.u2_at_batch
#print axioms P1K8.apartAt_zero
#print axioms P1K8.apartAt_iU3
