-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/- Johnson/Desc/First/Att/Door/Law/K5HeadPaid.lean: kind K5 (an attention segment's own rounds): TWO OF THE THREE CONDITIONS THAT THE KIND's NAMED CONDITION ASKS ONCE FOR A HEAD (K5LeftOfCond.lean: K5CondsHead: fence · oneShape) ARE THEOREMS FROM THE HEAD.


Compiled with the whole library.
(Where this and lean/THEOREM.md differ, the page holds.)


Why. Both are named conditions on public data that no test of the verifier asks. Files below Johnson/P5T/ prove, in scope and where the value is laid: the table's test on the fence accepts (Johnson/P5T/FenceAtMg.lean: AtMg.fence); the first chain's seats off the plan are the written ones (Johnson/P5T/CoreAtMg.lean: AtMg.seats); and, by an evaluation in Lean's kernel, no two written seats stand at one tree and tenant (Johnson/P5T/PlanSeatsFull.lean: seatsAllFull_apart).
fence is the first, after one definition is unfolded. oneShape ("any two members at one seat have one shape", K5MemOfSome.lean) follows from the other two: by the make each member's shape and seat are those of a seat off the plan (Johnson/P5T/MembersByMake.lean: plain_membersR); two seats at one tree and tenant are one seat.

Main names:
  `fence_head`: the field fence, in its own text, under the head AtMg.
  `member_is_seat`, `oneShapeB_of_apart`: general in the seats, the radii and the number of sendings.
  `psFull_apart`: the first chain's written seats are pairwise apart: the left part of seatsAllFull_apart.
  **`oneShape_head`**: oneShapeB (At.ms Zp lay) = true under the head AtMg, at every lay.
  **`oneShape_field`**, `fence_field`: the two fields' own texts under the head AtMgA.
Is it empty here? Implications from the head; a member of the head is proved at `storedPublicFiles` and `zGap`
alone (at secondHashFunction; side library AtFullSide/Top/).
Limits. The third condition for a head (pads) is not touched.
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.Door.Law.K5MemOfSome
import Johnson.P5T.CoreAtMg
import Johnson.P5J.PlanOk
import Johnson.P5J.MgAtAll

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace H2K5.Door
open VerifiableInference.Desc (Chain)
open VerifiableInference.Desc.First (fenceFit)
open VerifiableInference.Desc.Sound (Mem seatOf msOf)
open OnBytes.Maker (WholeD)
open P5T (PSeat memberListsR plain_membersR psFull seatsAllFull seatsAllFull_apart)
open P5J (AtMg AtMgA TS)

/-- By the make, a member's shape and seat are those of a seat off the plan. -/
theorem member_is_seat (n : ℕ) (rad : ℕ → ℕ → ℕ) (ps : List PSeat) (y : Mem) (hy : y ∈ msOf (memberListsR n rad ps)) :
    ∃ p ∈ ps, (y.1.l.get y.2).1 = p.shape ∧ seatOf y = (p.j, p.t) := by
  have h1 : ((y.1.l.get y.2).1, seatOf y) ∈ (msOf (memberListsR n rad ps)).map (fun x => ((x.1.l.get x.2).1, seatOf x)) :=
    List.mem_map.2 ⟨y, hy, rfl⟩
  rw [plain_membersR] at h1
  obtain ⟨k, _, h2⟩ := List.mem_flatMap.1 h1
  obtain ⟨p, hp, e⟩ := List.mem_map.1 h2
  exact ⟨p, (List.mem_filter.1 hp).1, (congrArg Prod.fst e).symm, (congrArg Prod.snd e).symm⟩

/-- **Where the seats are pairwise apart, one seat bears one shape.** -/
theorem oneShapeB_of_apart (n : ℕ) (rad : ℕ → ℕ → ℕ) (ps : List PSeat) (hn : (ps.map fun p => (p.j, p.t)).Nodup) :
    oneShapeB (msOf (memberListsR n rad ps)) = true := by
  unfold oneShapeB
  refine List.all_eq_true.2 fun y hy => List.all_eq_true.2 fun y' hy' => ?_
  by_cases e : seatOf y = seatOf y'
  · obtain ⟨p, hp, a1, a2⟩ := member_is_seat n rad ps y hy
    obtain ⟨p', hp', b1, b2⟩ := member_is_seat n rad ps y' hy'
    have hpp : p = p' := List.inj_on_of_nodup_map hn hp hp' (a2.symm.trans (e.trans b2))
    subst hpp
    rw [a1, b1, decide_eq_true rfl, Bool.or_true]
  · rw [decide_eq_false e]
    rfl

/-- The first chain's written seats are pairwise apart. -/
theorem psFull_apart : (psFull.map fun p => (p.j, p.t)).Nodup := by
  have h := seatsAllFull_apart
  unfold seatsAllFull at h
  rw [List.map_append, List.map_append] at h
  exact (List.nodup_append.1 (List.nodup_append.1 h).1).1

section
variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}

/-- The field fence, in its own text. -/
theorem fence_head (h : AtMg o Z D r Zp Np cF) : fenceFit (P5J.At.N Zp cF) P5J.At.links P5J.At.ps = true := h.fence

/-- **One seat bears one shape, from the head.** -/
theorem oneShape_head (h : AtMg o Z D r Zp Np cF) (lay : ByteArray) : oneShapeB (P5J.At.ms Zp lay) = true := by
  have e : P5J.At.pseats Zp = psFull := h.seats
  rw [P5J.At.ms_is]
  unfold P5J.At.members
  rw [e]
  exact oneShapeB_of_apart _ _ _ psFull_apart

end

section
variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}
  {x : VerifiableInference.Desc.First.Look.Place} (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)

include h in
/-- K5CondsHead's field fence. -/
theorem fence_field : fenceFit (P5J.At.N Zp cF) P5J.At.links P5J.At.ps = true := fence_head h.toAtMg

/-- K5CondsHead's field oneShape. -/
theorem oneShape_field : oneShapeB h.𝔇.ms = true := oneShape_head h.toAtMg Z.lay

end

end H2K5.Door

#print axioms H2K5.Door.member_is_seat
#print axioms H2K5.Door.oneShapeB_of_apart
#print axioms H2K5.Door.psFull_apart
#print axioms H2K5.Door.fence_head
#print axioms H2K5.Door.oneShape_head
#print axioms H2K5.Door.fence_field
#print axioms H2K5.Door.oneShape_field
