-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P5J/L0/PlanFourAtJoin.lean: FOUR OF THE TESTS ON THE PLAN THAT THE LAST TABLE's LAW ASKS
(`LLT25.PlanCore₃`: nodup · fence · oneTable · planShapes), EACH IN THE FIELD's OWN TEXT AT THE
JOIN's OWN TERMS, FROM THE HEAD `AtMg` (Johnson/P5J/AtMg.lean, when the entry tests had 13 rows).

  `nodup_at_join`: no two of mine have one number: the list of mine's seats is written
    (`IM.Seats.mineSeats_at_join`), `At.arr Zp` is `arrOf` at the written seats of all three chains
    (`P5T.seats_in_scope`), and there the three numbers part: a closed fact, by the kernel
    (`arr_apart_written`; `arr_can_meet`: the negative test).
  `fence_at_join`: mine lie in trees in front of the last chain's third sub-protocol: the three
    seats' trees are 1, 82 and 84; the base is 83 + 11 (`AtMg.trees_at`).
  `oneTable_at_join`: whoever of mine sits at Omega's seat has rows of one kind alone:
    `LLT25.oneTable_of_one` at the two fields oneSeat and omegaSeat (other files' theorems from
    the head) and a closed fact on the written sizes' shape for Omega (`oneTable_sized`).
  `planShapes_at_head`: AT Ld := `LFull`: `ToldDesc.planShapes_of_cut` at `AtMg.cut_written`.
  `indexNeW_at_head`: and the structure's fifteenth field: the two elder seats are apart.
  `nodupB_at_join` · `fenceB_at_join` · `oneTableAllB_at_join` · `planShapesB_at_head`: the same
    four as "the named test with code says true" (Johnson/LLT25R/PlanLeftTests.lean;
    Johnson/ToldDescR/BookAtW.lean).
Limits. That a head can be had at given public files is not said here. planShapes stands at
Ld := `LFull` alone. Of seats and placeB nothing is said. The full size alone. Nothing on soundness.
On hiding nothing.

-/
import Johnson.IMR.SeatsAtHead
import Johnson.LLT25R.MineThree
import Johnson.ToldDescR.PlanShapesOfCut

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace P5J.L0
open OnBytes OnBytes.Maker OnBytes.Slice
open VerifiableInference.OnPublicFiles.Last (baseTwoAt)
open VerifiableInference.Desc (Chain)
open VerifiableInference.Desc.Sound (Mem seatOf numOf Fenced)
open VerifiableInference.Desc.K13.Law (LFull)
open LLT25 (FL seatK c0 c1 baseTwo_pure oneTable_of_one)
open LLT25.PlanB (oneSeat_of omegaSeat_of nodupB fenceB oneTableAllB)
open ToldDesc (p14At)
open IM.Seats (mineA mineSeats_at_join oneSeat_at_join omegaSeat_at_join)

variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}

set_option maxRecDepth 1000000 in
/-- At the written seats of all three chains the three seats' numbers part. -/
theorem arr_apart_written : (([(1, 0), (82, 0), (84, 0)] : List (ℕ × ℕ)).map fun s =>
    P5T.arrOf P5T.seatsAllFull s.1 s.2).Nodup := by decide +kernel

set_option maxRecDepth 1000000 in
/-- The negative test: two seats beyond the list have one number. -/
theorem arr_can_meet : ¬ (([(1, 0), (1000, 0), (1001, 0)] : List (ℕ × ℕ)).map fun s =>
    P5T.arrOf P5T.seatsAllFull s.1 s.2).Nodup := by decide +kernel

/-- `At.arr` under the head. -/
theorem arr_at_head (h : AtMg o Z D r Zp Np cF) : At.arr Zp = P5T.arrOf P5T.seatsAllFull := by
  show P5T.arrOf (P5T.planSeatsAll Zp Zp.D) = _
  rw [(P5T.seats_in_scope h.scope h.laid.pub h.made_accepts
    (LPFD.Full.laidPOf_of h.laid.value h.laid.planOk h.laid.data h.laid.asks)).2.1]

/-- **THE FIELD nodup.** -/
theorem nodup_at_join (h : AtMg o Z D r Zp Np cF) :
    ((mineA o Z Zp Np cF).map (numOf (At.arr Zp))).Nodup := by
  have e : (mineA o Z Zp Np cF).map (numOf (At.arr Zp)) =
      ((mineA o Z Zp Np cF).map seatOf).map fun s => At.arr Zp s.1 s.2 := by
    rw [List.map_map]
    rfl
  rw [e, mineSeats_at_join h, arr_at_head h]
  exact arr_apart_written

/-- **THE FIELD fence.** -/
theorem fence_at_join (h : AtMg o Z D r Zp Np cF) :
    Fenced (baseTwoAt (FL o ProofFile.pureRoad.links Zp (seatK Zp Np) Np cF) (D.at frS.P.T.a) (c0 Zp)
      (c1 Np)) (mineA o Z Zp Np cF) := by
  rw [baseTwo_pure, h.trees_at.1, h.trees_at.2]
  intro x hx
  have m : seatOf x ∈ ([(1, 0), (82, 0), (84, 0)] : List (ℕ × ℕ)) :=
    mineSeats_at_join h ▸ List.mem_map_of_mem hx
  have b : (seatOf x).1 ≤ 84 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at m
    rcases m with m | m | m <;> rw [m] <;> decide
  exact Nat.lt_of_le_of_lt b (by decide)

set_option maxRecDepth 1000000 in
/-- At the written sizes. -/
theorem oneTable_sized : ToldDesc.oneTableB VerifiableInference.PlanWritten.proofSizedFull.codes
    VerifiableInference.PlanWritten.proofSizedFull.batch.shape.omega = true := by decide +kernel

/-- **THE FIELD oneTable.** -/
theorem oneTable_at_join (h : AtMg o Z D r Zp Np cF) :
    ∀ x ∈ mineA o Z Zp Np cF, seatOf x = ((D.at frS.P.T.a).t₁ + 1, 0) →
      ToldDesc.OneTable (p14At Zp).codes (x.1.l.get x.2).1 := by
  have hs : Zp.p.chains.made.sized.proof = VerifiableInference.PlanWritten.proofSizedFull :=
    VerifiableInference.PlanWritten.sized_in_scope h.scope h.laid.pub
      (VerifiableInference.PlanWritten.sized_of_made h.made_accepts)
  have hT : ToldDesc.OneTable (p14At Zp).codes (p14At Zp).S.omega := by
    show ToldDesc.OneTable Zp.p.chains.made.sized.proof.codes
      Zp.p.chains.made.sized.proof.batch.shape.omega
    rw [hs]
    exact (ToldDesc.oneTable_iff _ _).1 oneTable_sized
  exact oneTable_of_one (oneSeat_of (oneSeat_at_join h)) (omegaSeat_of (omegaSeat_at_join h)) hT

/-- **THE FIELD planShapes, at the written list.** -/
theorem planShapes_at_head (h : AtMg o Z D r Zp Np cF) :
    ToldDesc.PlanShapes (F0T o Zp Np cF) LFull 0 ((At.N Zp cF).treesAt none) :=
  ToldDesc.planShapes_of_cut _ h.cut_written _

/-- **THE FIELD indexNeW**: the two elder seats are apart: (1, 0) and (82, 0) (`AtMg.seats_at`). -/
theorem indexNeW_at_head (h : AtMg o Z D r Zp Np cF) :
    (LLT25.vAt Zp (At.N Zp cF)).index ≠ (LLT25.vAt Zp (At.N Zp cF)).w := by
  show (At.N Zp cF).index ≠ (At.N Zp cF).w
  rw [h.seats_at.1, h.seats_at.2]
  decide

/-! ### The same four as named tests with code -/

theorem nodupB_at_join (h : AtMg o Z D r Zp Np cF) :
    nodupB (At.arr Zp) (mineA o Z Zp Np cF) = true := decide_eq_true (nodup_at_join h)

theorem fenceB_at_join (h : AtMg o Z D r Zp Np cF) :
    fenceB ((D.at frS.P.T.a).t₁ + (D.at frS.P.T.a).t₂) (mineA o Z Zp Np cF) = true := by
  have F := fence_at_join h
  rw [baseTwo_pure] at F
  exact List.all_eq_true.2 fun x hx => decide_eq_true (F x hx)

theorem oneTableAllB_at_join (h : AtMg o Z D r Zp Np cF) :
    oneTableAllB (p14At Zp).codes (mineA o Z Zp Np cF) ((D.at frS.P.T.a).t₁ + 1, 0) = true := by
  refine List.all_eq_true.2 fun x hx => ?_
  by_cases e : seatOf x = ((D.at frS.P.T.a).t₁ + 1, 0)
  · rw [(ToldDesc.oneTable_iff _ _).2 (oneTable_at_join h x hx e), Bool.or_true]
  · rw [decide_eq_false e]
    rfl

theorem planShapesB_at_head (h : AtMg o Z D r Zp Np cF) :
    ToldDesc.planShapesB (F0T o Zp Np cF) LFull 0 ((At.N Zp cF).treesAt none) = true :=
  (ToldDesc.planShapes_iff _ _ _ _).2 (planShapes_at_head h)

end P5J.L0

#print axioms P5J.L0.indexNeW_at_head
#print axioms P5J.L0.nodupB_at_join
#print axioms P5J.L0.fenceB_at_join
#print axioms P5J.L0.oneTableAllB_at_join
#print axioms P5J.L0.planShapesB_at_head
#print axioms P5J.L0.arr_apart_written
#print axioms P5J.L0.arr_can_meet
#print axioms P5J.L0.arr_at_head
#print axioms P5J.L0.nodup_at_join
#print axioms P5J.L0.fence_at_join
#print axioms P5J.L0.oneTable_sized
#print axioms P5J.L0.oneTable_at_join
#print axioms P5J.L0.planShapes_at_head
