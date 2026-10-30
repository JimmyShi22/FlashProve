-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K13/PileLengthReach.lean: THE PILE's LENGTH AT EVERY REACHED STATE OF
THE FIRST CHAIN OF THE PROOF FILE's IOP AS WRITTEN IN LEAN, UP TO THE BORDER 355: IT IS THE
LIBRARY's OWN COUNT `P1L20.takenAt`. One definition with code, and statements with their proofs. It
stands on ClearedBySort.lean and PileAtFlat.lean of this folder and the library alone.

One induction along the library's `Reach` (Johnson/Top/H0/Walk/Reach.lean). A step: `stepYes_decide`
(Johnson/Top/H0/Walk/ReachInv.lean) to the decision; at one of the 25 numbers of a "cleared":
`cleared_by_sort` (ClearedBySort.lean): one row is laid at the rows' end, or, at an attention's
segment, the rows stay; at every other number: `flat_stays` (PileAtFlat.lean): the rows stay;
`flat_notAtEnd` (ClearedBySort.lean): the state does not come to the chain's end, so the rows on the
table are the field `out.pending` (the library's `rows_of_not_mem`); the count: the library's
`P1L20.taken_step` (Johnson/P1L20R/RoomFold.lean). The start: the library's `startS_facts`
(Johnson/Desc/AtSeats/StatementSeat.lean). Nothing under Johnson/Desc/ProofFile/Honest/ but these
two files is spent.
Under: In the goals' scope (`VerifierAndGoals.InScope`, `VerifierAndGoals.readFiles`), under the opening of the proof
file's IOP (`IM.Open`: its letters Z, Bs, c are what is public, the blank ground's holder, the first
chain).
Main names:
  `siteC k`: a test with code: k is 28 g + 14 for a g < 12, or 352. By the kernel:
    `isTake_eq_siteC`: below 355 it is the library's `P1L20.isTake` · `siteC_cleared`: at the number
    of segment l's "cleared" it says whether l is even · `siteC_only_cleared`: below 355 it is true
    at such numbers alone.
  `pile_length_reach_flat`: **where every sub-protocol of the chain's list passes its own test on
    the plan: at every state reached at a border k ≤ 355 from the IOP's own start: the state does
    not stand at the chain's end, and its pile has `P1L20.takenAt` k rows.**
  `pile_length_reach`: the same from F.planOk = true (by the library's `IM.plan_flat`,
    Johnson/IMR/PlanAt.lean).
  `takenAt_zero`, `takenAt_355`: by the kernel: `P1L20.takenAt` 0 = 0; `P1L20.takenAt` 355 = 13. Kin
    in the library: `P1L20.taken_three` (RoomFold.lean).

What is not claimed. That a state is reached at any border. That the premise on the plan holds at
any public files. What the rows are. Nothing from the border 356 on. Nothing on soundness,
completeness or hiding.

-/
import Johnson.Desc.ProofFile.Honest.K13.ClearedBySort
import Johnson.P1L20R.RoomFold
import Johnson.IMR.PlanAt
import Johnson.Desc.AtSeats.StatementSeat

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K13

open OnBytes OnBytes.Model
open VerifiableInference.Desc (Block Chain FileDescription)
open VerifiableInference.Desc.First (S)
open Johnson.Desc.First.Walk.Tied (Reach stepYes_decide)
open Meaning.K2 (rows_of_not_mem startS_facts)
open ProofFile (Cl)

/-- k is the number of a sub-protocol that lays a site's row. A test with code. -/
def siteC (k : Nat) : Bool := ((List.range 12).any fun g => 28 * g + 14 == k) || k == 352

set_option maxRecDepth 1000000 in
theorem isTake_eq_siteC_full :
    ((List.range 355).all fun k => P1L20.isTake k == siteC k) = true := by decide +kernel

/-- Below 355 the test is the library's own. -/
theorem isTake_eq_siteC {k : Nat} (hk : k < 355) : P1L20.isTake k = siteC k :=
  eq_of_beq (List.all_eq_true.1 isTake_eq_siteC_full k (List.mem_range.2 hk))

theorem siteC_cleared_full : ((List.range 25).all fun l =>
    siteC (14 * l + IM.nAt l + 7) == decide (l % 2 = 0)) = true := by decide +kernel

/-- At the number of segment l's "cleared" the test says whether l is even. -/
theorem siteC_cleared {l : Nat} (hl : l < 25) :
    siteC (14 * l + IM.nAt l + 7) = decide (l % 2 = 0) :=
  eq_of_beq (List.all_eq_true.1 siteC_cleared_full l (List.mem_range.2 hl))

set_option maxRecDepth 1000000 in
theorem siteC_only_cleared_full : ((List.range 355).all fun k =>
    !siteC k || (List.range 25).any fun l => 14 * l + IM.nAt l + 7 == k) = true := by
  decide +kernel

/-- Below 355 the test returns true at the numbers of a "cleared" alone. -/
theorem siteC_only_cleared {k : Nat} (hk : k < 355) (h : siteC k = true) :
    ∃ l < 25, k = 14 * l + IM.nAt l + 7 := by
  have q := List.all_eq_true.1 siteC_only_cleared_full k (List.mem_range.2 hk)
  rw [h] at q
  obtain ⟨l, hl, e⟩ : ∃ x < 25, 14 * x + IM.nAt x + 7 = k := by simpa using q
  exact ⟨l, hl, e.symm⟩

theorem takenAt_zero : P1L20.takenAt 0 = 0 := by decide +kernel

theorem takenAt_355 : P1L20.takenAt 355 = 13 := by decide +kernel

variable {Pp : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- **THE PILE's LENGTH AT EVERY REACHED STATE UP TO THE BORDER 355**, where every sub-protocol of
the chain's list passes its own test on the plan. -/
theorem pile_length_reach_flat (hS : VerifierAndGoals.InScope Pp = true) (hR : VerifierAndGoals.readFiles Pp = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction Pp.pol lay Pp.KL F Z Bs base c A B)
    (hp : ∀ b ∈ c.blocksInOrder, b.planOk = true) {k : Nat} {a : ProofFile.InstPub × S}
    (h : Reach 0 c.blocksInOrder (ProofFile.startS Z) k a) (hk : k ≤ 355) :
    NotAtEnd a.2 ∧ a.2.out.pending.length = P1L20.takenAt k := by
  induction h with
  | zero z =>
    refine ⟨fun a e => ?_, ?_⟩
    · rw [(startS_facts O.pub z).2.2] at e
      cases e
    · show (ProofFile.startS Z z).out.pending.length = _
      rw [(startS_facts O.pub z).1, takenAt_zero]
      rfl
  | succ hr hb hy ih =>
    rename_i k z s s' b
    obtain ⟨hs, hlen⟩ := ih (by omega)
    have hs0 : NotAtEnd s := hs
    have hlen0 : s.out.pending.length = P1L20.takenAt k := hlen
    obtain ⟨rs, gs, hd⟩ := stepYes_decide hy
    have hs' : NotAtEnd s' := flat_notAtEnd hS hR O k b hb (by omega) s s' rs gs hd hs0
    refine ⟨hs', ?_⟩
    show s'.out.pending.length = _
    rw [P1L20.taken_step (by omega), isTake_eq_siteC (by omega), ← hlen0,
      ← rows_of_not_mem hs', ← rows_of_not_mem hs0]
    by_cases hc : ∃ l < 25, k = 14 * l + IM.nAt l + 7
    · obtain ⟨l, hl, rfl⟩ := hc
      rw [siteC_cleared hl]
      obtain ⟨_, _, q⟩ := cleared_by_sort hS hR O hp l hl b hb
      rcases q with ⟨rfl, hq⟩ | ⟨he, _, hq⟩ | ⟨ho, hq⟩
      · obtain ⟨r, _, hrow⟩ := hq s s' rs gs hd
        rw [hrow, List.length_append]
        rfl
      · obtain ⟨r, _, hrow⟩ := hq s s' rs gs hd
        rw [hrow, List.length_append, decide_eq_true he]
        rfl
      · rw [hq s s' rs gs hd, decide_eq_false (by omega)]
        rfl
    · have hno : siteC k = false := by
        cases hq : siteC k with
        | false => rfl
        | true => exact absurd (siteC_only_cleared (by omega) hq) hc
      rw [hno, (flat_stays hS hR O k b hb (by omega) (fun l hl e => hc ⟨l, hl, e⟩) s s' rs gs
        hd).1]
      rfl

/-- **The same, where the IOP passes its own tests on the plan.** -/
theorem pile_length_reach (hS : VerifierAndGoals.InScope Pp = true) (hR : VerifierAndGoals.readFiles Pp = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction Pp.pol lay Pp.KL F Z Bs base c A B) (hp : F.planOk = true)
    {k : Nat} {a : ProofFile.InstPub × S}
    (h : Johnson.Desc.First.Walk.Tied.Reach 0 c.blocksInOrder (ProofFile.startS Z) k a) (hk : k ≤ 355) :
    NotAtEnd a.2 ∧ a.2.out.pending.length = P1L20.takenAt k :=
  pile_length_reach_flat hS hR O (IM.plan_flat O hp) h hk

end ProofFile.Honest.K13

#print axioms ProofFile.Honest.K13.isTake_eq_siteC_full
#print axioms ProofFile.Honest.K13.isTake_eq_siteC
#print axioms ProofFile.Honest.K13.siteC_cleared_full
#print axioms ProofFile.Honest.K13.siteC_cleared
#print axioms ProofFile.Honest.K13.siteC_only_cleared_full
#print axioms ProofFile.Honest.K13.siteC_only_cleared
#print axioms ProofFile.Honest.K13.takenAt_zero
#print axioms ProofFile.Honest.K13.takenAt_355
#print axioms ProofFile.Honest.K13.pile_length_reach_flat
#print axioms ProofFile.Honest.K13.pile_length_reach
