-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/Thread/NoK14K15.lean: no sub-protocol of the first chain at the full
size is of the kind K14 or K15. The definition `fHead` (FHead.lean) has the clause "True" at these
two kinds. This file shows that these two arms are met at no number of the chain, so that they make
no clause of `keeps` empty. No definition.

  1  `places_no_k14_k15`   a test on the written list of the 358 places: none has the kind K14 or
     K15. The statement has no free variable. It is decided by the kernel's evaluation
     (`decide +kernel`), so it is counted apart from the other lemmas
  2  `places_no_k14_k15_control`   the test can fail: with K13 in the place of K14 it fails
  3  `head_no_k14_k15`   under the library's hypothesis `AtMgA`: no sub-protocol of the chain's flat
     list has a place of the kind K14 or K15

Limits.
  * Full size only, and lemma 3 only at the hash function `secondHashFunction` (FirstAt.lean says which that
    is).
  * The lemmas prove no property of a prover or a protocol.
-/
import Johnson.P5J.MgAtAll
import Johnson.P5J.PlacesPaid

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.FirstThread
open VerifiableInference.Desc (Chain KindName)
open VerifiableInference.Desc.First (blockPlaces)
open OnBytes.Maker (WholeD)
open P5J (AtMgA TS)

set_option maxRecDepth 1000000 in
/-- No place of the written list has the kind K14 or K15. -/
theorem places_no_k14_k15 :
    (P5J.At.ps.all fun p => p.kind != KindName.K14 && p.kind != KindName.K15) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- A control: with K13 in the place of K14 the same test fails. -/
theorem places_no_k14_k15_control :
    (P5J.At.ps.all fun p => p.kind != KindName.K13 && p.kind != KindName.K15) = false := by
  decide +kernel

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- Under `AtMgA` no sub-protocol of the first chain has a place of the kind K14 or K15. -/
theorem head_no_k14_k15 (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) :
    ∀ blk ∈ cF.blocksInOrder, blk.place.kind ≠ KindName.K14 ∧ blk.place.kind ≠ KindName.K15 := by
  intro blk hb
  have e : blockPlaces cF.blocksInOrder = P5J.At.ps := P5J.At.places_paid h.scope h.reads h.laid
  have hm : blk.place ∈ P5J.At.ps := by
    rw [← e]
    unfold blockPlaces
    exact List.mem_map.2 ⟨blk, hb, rfl⟩
  have t := List.all_eq_true.1 places_no_k14_k15 _ hm
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at t
  exact t

end ProofFile.Honest.FirstThread

#print axioms ProofFile.Honest.FirstThread.places_no_k14_k15
#print axioms ProofFile.Honest.FirstThread.places_no_k14_k15_control
#print axioms ProofFile.Honest.FirstThread.head_no_k14_k15
