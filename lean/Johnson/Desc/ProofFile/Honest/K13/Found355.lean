-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K13/Found355.lean: kind K13, the members' batching: UNDER THE
LIBRARY's HEAD h (`P5J.AtMgA`: a hypothesis, which has a member: `headMember_zFull`,
AtFullSide/Top/HeadMemberAtFull.lean; the full size, the format's second hash function): AT THE PLACE OF
NUMBER 355 OF THE FIRST CHAIN's FLAT LIST THE KIND's LOT HAS, IN ITS OWN LIST OF HALVES, THE KIND's
HALF. AT THE LOT's OWN LIST: NO PROVER AND NO FILLING IS NAMED. Three statements under h, three
closed tests without a premise, with their proofs; no definition. NO PROPERTY IS CLAIMED.

Main names. `k13_found_355`: **under h, at every reader weights, filler pile and ground G: where
number 355 of cF.blocksInOrder is blk, `find?` at blk's place in `(k13Lot weights pile).halves Zp G` returns
`proverSideOfClaimCombination weights (pile Zp G) (whereOf Zp)`**: it says which half. `k13Keep_found_355`: the same of
`k13LotKeep weights pile get set` (KeepJob.lean of this folder) and `k13HalfKeep`, at every get and
set. `k13_found`: under h: at EVERY number b: where number b is blk and blk's place has the kind
K13, `find?` in `k13Lot`'s list returns some half; its "there is" is fixed by the equation that
follows it.

The three closed tests, on the library's written list of the first chain's places (`P5J.At.ps`,
Johnson/P5J/LettersAt.lean), each evaluated by Lean's kernel (`decide +kernel`). `ps_K13_one`: every
place of the kind K13 on the list is ⟨1, none, 3, .K13⟩. Two controls: `ps_K13_some`: the list has a
place of that kind, so the first test is not passed for want of a case; `ps_K13_control`: the same
test at piece 4 returns false.

How. Under h the places of cF.blocksInOrder are the written list (`P5J.At.places_paid`,
Johnson/P5J/PlacesPaid.lean). Number 355: `m3_member_place` (FromThreadAt.lean of this folder). The
lot's list at the kind's place: `k13Lot_find`, `k13Place_whereOf` (LotKind.lean), which ask no
premise; `k13LotKeep_halves` (LotKeepKind.lean).

Limits. CONDITIONAL ON h. WHICH HALF STANDS IN A LIST: nothing on whether it plays or is accepted,
on a run or a thread. That a prover's list of halves (`Prover.first`) holds this lot's halves, at
any filling, is not said. `k13_found` has no sister at the kept lot here. The closed tests are
evaluations by the kernel: no independent checker has replayed them. Of the three statements under h
the third does not call the first. Nothing outside this file calls these statements.

What is not claimed. It is none of the library's goals. Nothing on soundness, completeness, hiding
or binding.
-/
import Johnson.Desc.ProofFile.Honest.K13.LotKind
import Johnson.Desc.ProofFile.Honest.K13.LotKeepKind
import Johnson.Desc.ProofFile.Honest.K13.FromThreadAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K13
open VerifiableInference.Desc (Block Chain Place)
open VerifiableInference.Desc.First (blockPlaces)
open VerifiableInference.Desc.K13 (whereOf)
open OnBytes.Maker (WholeD)
open P5J (AtMgA TS)

set_option maxRecDepth 100000 in
/-- **A closed test on the written list of places**: every place of the kind K13 on it is the kind's
place. -/
theorem ps_K13_one :
    (P5J.At.ps.all fun p => p.kind != .K13 || p == ⟨1, none, 3, .K13⟩) = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- A control: the test is not passed for nothing: the list has a place of the kind K13. -/
theorem ps_K13_some : (P5J.At.ps.any fun p => p.kind == .K13) = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- A control: the like test at another piece's number fails. -/
theorem ps_K13_control :
    (P5J.At.ps.all fun p => p.kind != .K13 || p == ⟨1, none, 4, .K13⟩) = false := by decide +kernel

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {xh : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh) {W₀ Rc Tr X : Type}

include h in
/-- **AT NUMBER 355 THE LOT's OWN LIST HAS THE KIND's HALF**: under h; it says which half. -/
theorem k13_found_355 (weights : W₀ → Weights) (pile : ProofFile.Pub → ProofFile.Ground → PileOf ProofFile.Inst)
    (G : ProofFile.Ground) :
    ∀ blk, cF.blocksInOrder[355]? = some blk →
      ((k13Lot (Rc := Rc) (Tr := Tr) (X := X) weights pile).halves Zp G).find?
          (fun y => y.place == blk.place) =
        some (proverSideOfClaimCombination weights (pile Zp G) (whereOf Zp)) := by
  intro blk hb
  rw [m3_member_place h hb, ← k13Place_whereOf Zp]
  exact k13Lot_find weights pile Zp G

include h in
/-- The same at the lot's kept form: under h. -/
theorem k13Keep_found_355 (weights : W₀ → Weights) (pile : ProofFile.Pub → ProofFile.Ground → PileOf ProofFile.Inst)
    (get : X → Option K13Kept) (set : X → Option K13Kept → X) (G : ProofFile.Ground) :
    ∀ blk, cF.blocksInOrder[355]? = some blk →
      ((k13LotKeep (Rc := Rc) (Tr := Tr) weights pile get set).halves Zp G).find?
          (fun y => y.place == blk.place) =
        some (k13HalfKeep weights (pile Zp G) get set (whereOf Zp)) := by
  intro blk hb
  rw [m3_member_place h hb, k13LotKeep_halves]
  exact List.find?_cons_of_pos (by simp [k13HalfKeep, k13Place_whereOf])

include h in
/-- **AT EVERY NUMBER WHOSE PLACE HAS THE KIND K13 THE LOT's OWN LIST HAS A HALF**: under h. -/
theorem k13_found (weights : W₀ → Weights) (pile : ProofFile.Pub → ProofFile.Ground → PileOf ProofFile.Inst)
    (G : ProofFile.Ground) :
    ∀ b : ℕ, ∀ blk, cF.blocksInOrder[b]? = some blk → blk.place.kind = .K13 →
      ∃ g, ((k13Lot (Rc := Rc) (Tr := Tr) (X := X) weights pile).halves Zp G).find?
        (fun y => y.place == blk.place) = some g := by
  intro b blk hb hk
  have e := P5J.At.places_paid h.scope h.reads h.laid
  have hm : blk.place ∈ P5J.At.ps := by
    rw [← e]
    exact List.mem_map.2 ⟨blk, List.mem_of_getElem? hb, rfl⟩
  have q := List.all_eq_true.1 ps_K13_one _ hm
  rw [hk] at q
  have hp : blk.place = ⟨1, none, 3, .K13⟩ := by simpa using q
  refine ⟨proverSideOfClaimCombination weights (pile Zp G) (whereOf Zp), ?_⟩
  rw [hp, ← k13Place_whereOf Zp]
  exact k13Lot_find weights pile Zp G

end ProofFile.Honest.K13

#print axioms ProofFile.Honest.K13.ps_K13_one
#print axioms ProofFile.Honest.K13.ps_K13_some
#print axioms ProofFile.Honest.K13.ps_K13_control
#print axioms ProofFile.Honest.K13.k13_found_355
#print axioms ProofFile.Honest.K13.k13Keep_found_355
#print axioms ProofFile.Honest.K13.k13_found
