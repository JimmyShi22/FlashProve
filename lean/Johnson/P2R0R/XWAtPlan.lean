-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P2R0R/XWAtPlan.lean: TWO PREMISES OF ROW 0's LAW OF THE LAST TABLE
(Johnson/Flat/Last/RowZeroAtZ.lean: hseat · hsh) AT "THE FIRST MEMBER OF A
LIST THAT SITS AT W's SEAT, BY find?, ELSE A DEFAULT": the text of the shared table's constant's
Sh.xW (Johnson/Desc/K14/Law/SharedConst.lean). STATED AND PROVED. "The two equations off find?".

The term is named here (seatedFirst), so that this file
stands over the last table's files alone; that Sh.xW is that term stands in P2R0R/XWAtSh.lean.
  getD_find: what find? returns, where some member of the list passes the test, is a member of the
      list and passes the test: the default is not reached.
  seatedFirst ms w d · seatedFirst_sits: where a member of ms sits at w: seatedFirst ms w d is a
      member of ms and sits there.
  **seatedFirst_at_plan**: FROM THE LAST TABLE's TESTS ON THE PLAN (LLT25R/LastOwedCore.lean:
      PlanOk₃, at V := vAt Z N₁: own3_at_end's premise hP): (a) hseat's form: seatedFirst ms₁ N₁.w d
      sits at N₁.w; (b) its shape is (p14At Z).S.w. By someW (a member sits there) · mineW (one of
      mine has W's seat and shape) · oneSeat (no two of mine have one seat).
  hsh_at_plan: hsh's form, from (b) and one equation on the letter Pw: Pw.lin.w = (p14At Z).S.w
      (at Pw := K13.whereOf Z that is Johnson/P2R0R/SizedIsRead.lean's hSZ_of, at the field w).
Why oneSeat. find? takes the FIRST member at the seat: that SOME member there has W's shape does not
give the first one's shape.
Limits. Whoever calls it lays the constant's ms₁ | N₁ and the law's 𝔇.N | 𝔇.P13 at one term each:
that is not said here. NO EXAMPLE IN LEAN shows PlanOk₃ met; as reported, not shown here, someW ·
mineW · oneSeat are among the tests that files of evaluations, not named here, have evaluated at
both real sizes. Nothing on soundness or on hiding.

-/
import Johnson.LLT25R.LastV

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace P2R0
open OnBytes OnBytes.Maker
open VerifiableInference.Desc (Chain FileDescription)
open VerifiableInference.Desc.Sound (Mem seatOf)
open VerifiableInference.Desc.Shared (NumbersS)
open VerifiableInference.Desc.First (S ModelPart Numbers)
open ProofFile (SecondHashFunctionArgument LinksBy Cl)
open ToldDesc (p14At)
open LLT25

/-- What find? returns, where some member passes the test: a member that passes it. -/
theorem getD_find {α : Type} (l : List α) (p : α → Bool) (d : α) (h : ∃ m ∈ l, p m = true) :
    (l.find? p).getD d ∈ l ∧ p ((l.find? p).getD d) = true := by
  obtain ⟨m, hm, hp⟩ := h
  cases hf : l.find? p with
  | none => exact absurd hp (List.find?_eq_none.1 hf m hm)
  | some x => exact ⟨List.mem_of_find?_eq_some hf, List.find?_some hf⟩

/-- The first member of ms that sits at w; d where there is none. -/
def seatedFirst (ms : List Mem) (w : ℕ × ℕ) (d : Mem) : Mem :=
  (ms.find? fun m => decide (m.1.seat m.2 = w)).getD d

/-- **Where a member of the list sits at w, seatedFirst is such a member.** -/
theorem seatedFirst_sits (ms : List Mem) (w : ℕ × ℕ) (d : Mem) (h : ∃ m ∈ ms, m.1.seat m.2 = w) :
    seatedFirst ms w d ∈ ms ∧ (seatedFirst ms w d).1.seat (seatedFirst ms w d).2 = w := by
  obtain ⟨m, hm, hs⟩ := h
  have k := getD_find ms (fun m => decide (m.1.seat m.2 = w)) d ⟨m, hm, decide_eq_true hs⟩
  exact ⟨k.1, of_decide_eq_true k.2⟩

variable {o : SecondHashFunctionArgument} {mk : LinksBy} {Z : ProofFile.Pub} {N : H2U.Places4} {c : Chain S Cl}
  {D : WholeD} {Xi' : Type} {G : FileDescription Xi'} {arr : ℕ → ℕ → ℕ} {dB : RDT} {dt : List RDT}
  {ms₁ ms₂ : List Mem} {N₁ : Numbers} {Ns : NumbersS} {links : List ModelPart}
  {ps : List VerifiableInference.Desc.Place} {r : Fmt.M1.Stage → ℕ} {n₁ ft nΩ : ℕ}
  {Ld : VerifiableInference.Desc.K12.Door.Laid}

/-- **hseat's form, and the shape, from the last table's tests on the plan.** -/
theorem seatedFirst_at_plan
    (hP : PlanOk₃ o mk Z N c D G arr dB dt ms₁ ms₂ N₁ Ns links ps r n₁ ft nΩ (vAt Z N₁) Ld)
    (d : Mem) :
    (seatedFirst ms₁ N₁.w d).1.seat (seatedFirst ms₁ N₁.w d).2 = N₁.w ∧
      ((seatedFirst ms₁ N₁.w d).1.l.get (seatedFirst ms₁ N₁.w d).2).1 = (p14At Z).S.w := by
  obtain ⟨m, hm, hs⟩ := hP.someW
  have hs' : m.1.seat m.2 = N₁.w := hs
  obtain ⟨hx, hw⟩ := seatedFirst_sits ms₁ N₁.w d ⟨m, hm, hs'⟩
  have hmine : seatedFirst ms₁ N₁.w d ∈ mineOf ms₁ ms₂ N₁ Ns :=
    mem_mineOf.2 (Or.inl ⟨hx, Or.inl hw⟩)
  obtain ⟨x, hxm, hxs, hxsh⟩ := hP.mineW
  have hxs' : seatOf x = N₁.w := hxs
  have e : seatedFirst ms₁ N₁.w d = x :=
    hP.oneSeat _ hmine x hxm ((show seatOf (seatedFirst ms₁ N₁.w d) = N₁.w from hw).trans hxs'.symm)
  refine ⟨hw, ?_⟩
  rw [e]
  exact hxsh

/-- **hsh's form.** -/
theorem hsh_at_plan
    (hP : PlanOk₃ o mk Z N c D G arr dB dt ms₁ ms₂ N₁ Ns links ps r n₁ ft nΩ (vAt Z N₁) Ld)
    (d : Mem) (Pw : VerifiableInference.Desc.K13.Where) (hPw : Pw.lin.w = (p14At Z).S.w) :
    Pw.lin.w = ((seatedFirst ms₁ N₁.w d).1.l.get (seatedFirst ms₁ N₁.w d).2).1 :=
  hPw.trans (seatedFirst_at_plan hP d).2.symm

end P2R0

#print axioms P2R0.getD_find
#print axioms P2R0.seatedFirst_sits
#print axioms P2R0.seatedFirst_at_plan
#print axioms P2R0.hsh_at_plan
