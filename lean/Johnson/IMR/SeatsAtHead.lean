-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/IMR/SeatsAtHead.lean: SIX OF THE NAMED TESTS OF THE LAST TABLE's PREMISE hP
(LLT25.PlanOk₃) SAY TRUE UNDER THE ONE HEAD P5J.AtMg, at the join's own letters: someW, someI,
mineW, mineI, omegaSeat, oneSeat, in the names of Johnson/LLT25R/PlanLeftTests.lean (someB, mineAtB,
omegaSeatB, oneSeatB). Statements and proofs.



  pairW_written · pairI_written   closed facts, by the kernel: among the written entries with a
                      sample one has W's shape and the seat (82, 0); one has the index masks'
                      message's shape and the seat (1, 0). pair_can_fail: none has W's shape and
                      the seat (81, 0)
  member_at_head      under the head, a pair (shape, seat) of the written entries with a sample is
                      a member's of the first table's list (P5T.memsSame_atR: no premise)
  **someW_at_head · someI_at_head · mineW_at_head · mineI_at_head**   ms₂ and Ns stay letters
  planA · nsA · mineA   the shared table's plan, its numbers and what is mine, at the join's terms
  **omegaSeat_at_join**   the second of the shared table's three members sits at (t₁ + 1, 0) and has
                      the plan's shape for Omega
  seats_written_at_head   the first table's members' seats are a written LIST: an equation of lists
                      (P5T.plain_membersR), not of membership alone
  tenants_written_at_head   the shared table's three tenants at the join are the written ones
  mineSeats_written   a closed fact, by the kernel: at the written values what is mine has the
                      seats [(1, 0), (82, 0), (84, 0)]. mineSeats_can_fail: with 81 trees in front
                      a seat would stand twice
  **mineSeats_at_join · oneSeat_at_join**

CALLED, NOT TYPED ANEW: P5J.AtMg.seats (the first chain's entries with their seats are the written
ones: Johnson/P5T/CoreAtMg.lean) and P5J.AtMg.pins (madeRow at the head's own public part:
Johnson/P5T/FenceAtMg.lean); seats_at (W at (82, 0), the index masks' message at
(1, 0)), omega_at, first_told (Johnson/P5J/NumbersAtHead.lean) and trees_at
(Johnson/HB/LLHARD/HeadFacts.lean).
KIN. tenants_written_at_head goes the road of omega_at (the same three rewritings) and
says it of all three tenants; omega_at with omega_written follows from it.
THE HEAD. It stands over the entry tests' list of thirteen rows: over the list that went before it
AtMg.pins cannot be had.
NOT HERE: oneOmega, the seventh on seats: Johnson/IMR/OneOmegaAtHead.lean has it, from the head too.

What is not claimed. That a head can be had at any public files. The full size alone. Nothing on
radii. No member. No soundness.

-/
import Johnson.IMR.SampleAtW
import Johnson.LLT25R.PlanLeftTests
import Johnson.LLT25R.LastAt
import Johnson.P5T.CoreAtMg
import Johnson.P5T.MembersByMake
import Johnson.P5J.NumbersAtHead
import Johnson.Desc.K14.Law.SharedConstAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace IM.Seats

open OnBytes
open VerifiableInference.Desc (Chain)
open VerifiableInference.Desc.Sound (Mem seatOf)
open VerifiableInference.Desc.Shared (NumbersS)
open OnBytes.Maker (WholeD)
open LLT25 (vAt mineOf mem_mineOf)
open LLT25.PlanB (someB mineAtB omegaSeatB oneSeatB)
open ToldDesc (p14At)
open _root_.Desc.K14.Law.Fence (msSh numbersSh sendingO tenantSh)
open _root_.Desc.K14.Law (layUFull layOFull)
open _root_.Desc.K14.Law (Sh.planAt Sh.ms Sh.t₁ Sh.layU Sh.layO)
open P5J

variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}

set_option maxRecDepth 1000000 in
theorem pairW_written : (shW, ((82, 0) : ℕ × ℕ)) ∈
    (P5T.psFull.filter (·.smpd)).map fun p => (p.shape, p.seat) := by decide +kernel

set_option maxRecDepth 1000000 in
theorem pairI_written : (shI, ((1, 0) : ℕ × ℕ)) ∈
    (P5T.psFull.filter (·.smpd)).map fun p => (p.shape, p.seat) := by decide +kernel

set_option maxRecDepth 1000000 in
/-- The closed fact can fail. -/
theorem pair_can_fail : (shW, ((81, 0) : ℕ × ℕ)) ∉
    (P5T.psFull.filter (·.smpd)).map fun p => (p.shape, p.seat) := by decide +kernel

/-- A written pair is a member's. -/
theorem member_at_head (h : AtMg o Z D r Zp Np cF) {sh : OracleShape} {t : ℕ × ℕ}
    (hc : (sh, t) ∈ (P5T.psFull.filter (·.smpd)).map fun p => (p.shape, p.seat)) :
    ∃ x ∈ At.ms Zp Z.lay, (x.1.l.get x.2).1 = sh ∧ seatOf x = t := by
  rw [← h.seats] at hc
  obtain ⟨x, hx, e⟩ := List.mem_map.1 ((P5T.memsSame_atR Zp (At.rad Zp Z.lay) (sh, t)).2 hc)
  exact ⟨x, hx, congrArg Prod.fst e, congrArg Prod.snd e⟩

/-- **someW.** -/
theorem someW_at_head (h : AtMg o Z D r Zp Np cF) :
    someB (At.ms Zp Z.lay) (At.N Zp cF).w = true := by
  obtain ⟨x, hx, -, e⟩ := member_at_head h pairW_written
  exact List.any_eq_true.2 ⟨x, hx, decide_eq_true (e.trans h.seats_at.1.symm)⟩

/-- **someI.** -/
theorem someI_at_head (h : AtMg o Z D r Zp Np cF) :
    someB (At.ms Zp Z.lay) (At.N Zp cF).index = true := by
  obtain ⟨x, hx, -, e⟩ := member_at_head h pairI_written
  exact List.any_eq_true.2 ⟨x, hx, decide_eq_true (e.trans h.seats_at.2.symm)⟩

/-- **mineW.** -/
theorem mineW_at_head (h : AtMg o Z D r Zp Np cF) (ms₂ : List Mem) (Ns : NumbersS) :
    mineAtB (mineOf (At.ms Zp Z.lay) ms₂ (At.N Zp cF) Ns) (vAt Zp (At.N Zp cF)).w
      (vAt Zp (At.N Zp cF)).wShape = true := by
  obtain ⟨x, hx, es, e⟩ := member_at_head h pairW_written
  have e' : seatOf x = (At.N Zp cF).w := e.trans h.seats_at.1.symm
  refine List.any_eq_true.2 ⟨x, mem_mineOf.2 (.inl ⟨hx, .inl e'⟩), ?_⟩
  rw [Bool.and_eq_true]
  exact ⟨decide_eq_true e', decide_eq_true (es.trans (p14_w h.pins.1).symm)⟩

/-- **mineI.** -/
theorem mineI_at_head (h : AtMg o Z D r Zp Np cF) (ms₂ : List Mem) (Ns : NumbersS) :
    mineAtB (mineOf (At.ms Zp Z.lay) ms₂ (At.N Zp cF) Ns) (vAt Zp (At.N Zp cF)).index
      (vAt Zp (At.N Zp cF)).indexShape = true := by
  obtain ⟨x, hx, es, e⟩ := member_at_head h pairI_written
  have e' : seatOf x = (At.N Zp cF).index := e.trans h.seats_at.2.symm
  refine List.any_eq_true.2 ⟨x, mem_mineOf.2 (.inl ⟨hx, .inr e'⟩), ?_⟩
  rw [Bool.and_eq_true]
  exact ⟨decide_eq_true e', decide_eq_true (es.trans (index_shape h.pins.1).symm)⟩

/-! ### Omega's seat, at the join's own terms -/

/-- The shared table's plan at the head's letters. -/
abbrev planA (o : ProofFile.SecondHashFunctionArgument) (Zp : ProofFile.Pub) (Np : H2U.Places4) (cF : Chain TS ProofFile.Cl) :=
  Sh.planAt Zp Np (F0T o Zp Np cF)

/-- The shared table's numbers at the join. -/
abbrev nsA (o : ProofFile.SecondHashFunctionArgument) (Zp : ProofFile.Pub) (Np : H2U.Places4) (cF : Chain TS ProofFile.Cl) :
    NumbersS :=
  numbersSh (Sh.t₁ (planA o Zp Np cF)) (Sh.layU (planA o Zp Np cF)) (Sh.layO (planA o Zp Np cF))
    (0, 0) (0, 0)

/-- What is mine at the join. -/
abbrev mineA (o : ProofFile.SecondHashFunctionArgument) (Z : VerifierAndGoals.PublicFiles) (Zp : ProofFile.Pub) (Np : H2U.Places4)
    (cF : Chain TS ProofFile.Cl) : List Mem :=
  mineOf (At.ms Zp Z.lay) (Sh.ms (planA o Zp Np cF)) (At.N Zp cF) (nsA o Zp Np cF)

/-- **omegaSeat**, at the join's own terms. -/
theorem omegaSeat_at_join (h : AtMg o Z D r Zp Np cF) :
    omegaSeatB (mineA o Z Zp Np cF) ((D.at OnBytes.Slice.frS.P.T.a).t₁ + 1, 0)
      (p14At Zp).S.omega = true := by
  have hx : (⟨sendingO (planA o Zp Np cF).Q.S ((planA o Zp Np cF).rad5 0)
      ((planA o Zp Np cF).rad5 1) (Sh.t₁ (planA o Zp Np cF)) (Sh.layU (planA o Zp Np cF))
      (Sh.layO (planA o Zp Np cF)), ⟨0, Nat.two_pos⟩⟩ : Mem) ∈ Sh.ms (planA o Zp Np cF) :=
    List.mem_cons_of_mem _ List.mem_cons_self
  refine List.any_eq_true.2 ⟨_, mem_mineOf.2 (.inr ⟨hx, rfl⟩), ?_⟩
  rw [Bool.and_eq_true]
  refine ⟨decide_eq_true ?_, decide_eq_true rfl⟩
  rw [h.trees_at.1]
  exact h.omega_at

/-! ### No two of mine have one seat -/

/-- The seats of the first table's members, at the written entries. -/
def seatsW : List (ℕ × ℕ) :=
  ((List.range Johnson.G.proofSendsFull.1.sends.length).flatMap fun k =>
    (P5T.mineAt P5T.psFull k).map fun p => (p.shape, p.seat)).map Prod.snd

/-- The seats of what is mine, at the written values. -/
def mineSeatsW : List (ℕ × ℕ) :=
  (seatsW.filter fun s => decide (s = (82, 0)) || decide (s = (1, 0))) ++
    [tenantSh 83 layUFull layOFull .oU, tenantSh 83 layUFull layOFull .oOmega,
      tenantSh 83 layUFull layOFull .oSp].filter fun s =>
        decide (s = tenantSh 83 layUFull layOFull .oOmega)

set_option maxRecDepth 1000000 in
/-- A closed fact, by the kernel: they are three, and which. -/
theorem mineSeats_written : mineSeatsW = [(1, 0), (82, 0), (84, 0)] := by decide +kernel

set_option maxRecDepth 1000000 in
/-- The closed fact can fail: with 81 trees in front Omega would sit at W's seat: a seat twice. -/
theorem mineSeats_can_fail :
    ¬ ((seatsW.filter fun s => decide (s = (82, 0)) || decide (s = (1, 0))) ++
      [tenantSh 81 layUFull layOFull .oOmega]).Nodup := by decide +kernel

/-- The first table's members' seats are the written list: an equation of lists
(P5T.plain_membersR), not of membership alone. -/
theorem seats_written_at_head (h : AtMg o Z D r Zp Np cF) :
    (At.ms Zp Z.lay).map seatOf = seatsW := by
  have a := congrArg (List.map Prod.snd) (P5T.plain_membersR Zp.made.proof.1.sends.length
    (At.rad Zp Z.lay) (P5T.planSeats Zp Zp.D.1))
  rw [List.map_map] at a
  have b : ((List.range Zp.made.proof.1.sends.length).flatMap fun k =>
      (P5T.mineAt (P5T.planSeats Zp Zp.D.1) k).map fun p => (p.shape, p.seat)).map Prod.snd =
      seatsW := by
    rw [h.seats, (pins h.pins.1).2.2.2.2]
    rfl
  exact a.trans b

/-- The shared table's three tenants at the join are the written ones. -/
theorem tenants_written_at_head (h : AtMg o Z D r Zp Np cF) :
    tenantSh (Sh.t₁ (planA o Zp Np cF)) (Sh.layU (planA o Zp Np cF)) (Sh.layO (planA o Zp Np cF)) =
      tenantSh 83 layUFull layOFull := by
  have hs : Zp.p.chains.made.sized.proof = VerifiableInference.PlanWritten.proofSizedFull :=
    (pins h.pins.1).1
  show tenantSh (VerifiableInference.Desc.oraclesOf (F0T o Zp Np cF).first.blocksInOrder).length
    ((layTrees Zp.p.chains.made.sized.proof.codes
      ((_root_.Desc.K14.withU Zp.p.chains.made.sized.proof.batch.shape).getD #[])).getD default)
    ((layTrees Zp.p.chains.made.sized.proof.codes
      (_root_.Desc.K14.withOmega Zp.p.chains.made.sized.proof.batch.shape)).getD default) = _
  rw [hs, h.first_told, VerifiableInference.PlanWritten.codes_written]
  rfl

/-- **The seats of what is mine at the join, as a list: three, and which.** -/
theorem mineSeats_at_join (h : AtMg o Z D r Zp Np cF) :
    (mineA o Z Zp Np cF).map seatOf = [(1, 0), (82, 0), (84, 0)] := by
  refine Eq.trans ?_ mineSeats_written
  show (((At.ms Zp Z.lay).filter ((fun s => decide (s = (At.N Zp cF).w) ||
      decide (s = (At.N Zp cF).index)) ∘ seatOf)) ++
    ((Sh.ms (planA o Zp Np cF)).filter ((fun s => decide (s = tenantSh (Sh.t₁ (planA o Zp Np cF))
      (Sh.layU (planA o Zp Np cF)) (Sh.layO (planA o Zp Np cF)) .oOmega)) ∘ seatOf))).map seatOf = _
  rw [List.map_append, ← List.filter_map, ← List.filter_map, seats_written_at_head h,
    h.seats_at.1, h.seats_at.2]
  show _ ++ ([tenantSh (Sh.t₁ (planA o Zp Np cF)) (Sh.layU (planA o Zp Np cF))
      (Sh.layO (planA o Zp Np cF)) .oU,
    tenantSh (Sh.t₁ (planA o Zp Np cF)) (Sh.layU (planA o Zp Np cF))
      (Sh.layO (planA o Zp Np cF)) .oOmega,
    tenantSh (Sh.t₁ (planA o Zp Np cF)) (Sh.layU (planA o Zp Np cF))
      (Sh.layO (planA o Zp Np cF)) .oSp].filter _) = _
  rw [tenants_written_at_head h]
  rfl

/-- **oneSeat**, at the join's own terms. -/
theorem oneSeat_at_join (h : AtMg o Z D r Zp Np cF) : oneSeatB (mineA o Z Zp Np cF) = true := by
  apply decide_eq_true
  rw [mineSeats_at_join h]
  decide

end IM.Seats

#print axioms IM.Seats.pairW_written
#print axioms IM.Seats.pairI_written
#print axioms IM.Seats.pair_can_fail
#print axioms IM.Seats.member_at_head
#print axioms IM.Seats.someW_at_head
#print axioms IM.Seats.someI_at_head
#print axioms IM.Seats.mineW_at_head
#print axioms IM.Seats.mineI_at_head
#print axioms IM.Seats.omegaSeat_at_join
#print axioms IM.Seats.mineSeats_written
#print axioms IM.Seats.mineSeats_can_fail
#print axioms IM.Seats.seats_written_at_head
#print axioms IM.Seats.tenants_written_at_head
#print axioms IM.Seats.mineSeats_at_join
#print axioms IM.Seats.oneSeat_at_join
