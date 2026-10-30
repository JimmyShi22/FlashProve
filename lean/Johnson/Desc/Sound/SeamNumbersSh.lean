-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Sound/SeamNumbersSh.lean: **THE PREMISES ON MEMBERS AND NUMBERS AT THE SHARED CHAIN's TWO PROXIMITY TESTS, AT THE FILLING ms := msSh · N.tenant := tenantSh (SharedMembers.lean): THE PART THAT IS COUNTING ALONE.** Definitions with code; statements and proofs.
  memSh m          the member of msSh that is the message m.   memSh_mem · memSh_sits · memSh_entry (its entry: the plan's shape with the letter's radius): by make.
  **uniq_sh**      a member of msSh that sits at m's tenant IS memSh m (where the layouts are the planner's: tenants_apart).   memSh_ne: two messages, two members.
  huniq_nine | huniq_ten    tupleNine_members' | tupleTen_members' premise huniq (SeamLast.lean), to the letter.
  **hN_sh**        ((mineS N ms true k).map (numOf arr)).Nodup at EVERY k: nine_paid's | ten_paid's hN.
  **hap_nine | hap_ten**   apartAt N arr true 9 (.msg .oSp) · (.msg .oOmega) · apartAt N arr true 10 (.msg .oOmega).
UNDER: the two layouts are layTrees' · N.tenant = tenantSh lo layU layO · harr: the plan's letter arr gives the three tenants three numbers.
NOT HERE: SentBefore (the trees' numbers against the pieces' bases: it wants the data).
Limits. It closes no row. NO SOUNDNESS.

-/
import Johnson.Desc.Sound.SharedMembers
import Johnson.Desc.Sound.BordersSharedFill

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Law.Fence
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Maker
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.Shared

section
variable (S : LinShape) (rU rO rSp lo : ℕ) (layU layO : TreeLay)

/-- The member that is the message m. -/
def memSh : Msg2 → Mem
  | .oU => ⟨sendingU S rU lo layU layO, ⟨0, Nat.one_pos⟩⟩
  | .oOmega => ⟨sendingO S rO rSp lo layU layO, ⟨0, Nat.two_pos⟩⟩
  | .oSp => ⟨sendingO S rO rSp lo layU layO, ⟨1, Nat.one_lt_two⟩⟩

theorem memSh_mem (m : Msg2) : memSh S rU rO rSp lo layU layO m ∈ msSh S rU rO rSp lo layU layO := by
  rw [msSh_all]
  cases m <;> simp [memSh]

theorem memSh_seat (m : Msg2) : (memSh S rU rO rSp lo layU layO m).1.seat
    (memSh S rU rO rSp lo layU layO m).2 = tenantSh lo layU layO m := by
  cases m <;> rfl

theorem memSh_sits (m : Msg2) : SitsAt (memSh S rU rO rSp lo layU layO m)
    (tenantSh lo layU layO m).1 (tenantSh lo layU layO m).2 := memSh_seat S rU rO rSp lo layU layO m

/-- Its entry: the plan's shape with the letter's radius. -/
theorem memSh_entry :
    (memSh S rU rO rSp lo layU layO .oU).1.l.get (memSh S rU rO rSp lo layU layO .oU).2 =
        (S.fold.u, rU) ∧
      (memSh S rU rO rSp lo layU layO .oOmega).1.l.get (memSh S rU rO rSp lo layU layO .oOmega).2 =
        (S.omega, rO) ∧
      (memSh S rU rO rSp lo layU layO .oSp).1.l.get (memSh S rU rO rSp lo layU layO .oSp).2 =
        (S.sharedSplit, rSp) := ⟨rfl, rfl, rfl⟩

/-- Every member of the list is one of the three. -/
theorem msSh_memSh (z : Mem) (hz : z ∈ msSh S rU rO rSp lo layU layO) :
    ∃ m, z = memSh S rU rO rSp lo layU layO m := by
  rw [msSh_all] at hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with rfl | rfl | rfl
  · exact ⟨.oU, rfl⟩
  · exact ⟨.oOmega, rfl⟩
  · exact ⟨.oSp, rfl⟩

variable (codes : Codes) (sentU sentO : Array OracleNotice)
  (hlU : layTrees codes sentU = some layU) (hlO : layTrees codes sentO = some layO)
  (hU : 0 < sentU.size) (hO : 1 < sentO.size)
include hlU hlO hU hO

/-- **Who sits at m's tenant is memSh m.** -/
theorem uniq_sh (m : Msg2) (z : Mem) (hz : z ∈ msSh S rU rO rSp lo layU layO)
    (hs : SitsAt z (tenantSh lo layU layO m).1 (tenantSh lo layU layO m).2) :
    z = memSh S rU rO rSp lo layU layO m := by
  obtain ⟨m', rfl⟩ := msSh_memSh S rU rO rSp lo layU layO z hz
  have e : tenantSh lo layU layO m' = tenantSh lo layU layO m :=
    (memSh_seat S rU rO rSp lo layU layO m').symm.trans hs
  rw [tenants_apart codes sentU sentO layU layO hlU hlO hU hO lo m' m e]

/-- Two messages, two members. -/
theorem memSh_ne (m m' : Msg2) (h : m ≠ m') :
    memSh S rU rO rSp lo layU layO m ≠ memSh S rU rO rSp lo layU layO m' := by
  intro e
  apply h
  apply tenants_apart codes sentU sentO layU layO hlU hlO hU hO lo m m'
  rw [← memSh_seat S rU rO rSp lo layU layO m, ← memSh_seat S rU rO rSp lo layU layO m', e]

variable (N : NumbersS) (hN : N.tenant = tenantSh lo layU layO)
include hN

/-- tupleNine_members' huniq. -/
theorem huniq_nine : ∀ z ∈ msSh S rU rO rSp lo layU layO,
    SitsAt z (N.tenant .oU).1 (N.tenant .oU).2 ∨ SitsAt z (N.tenant .oSp).1 (N.tenant .oSp).2 →
    z = memSh S rU rO rSp lo layU layO .oU ∨ z = memSh S rU rO rSp lo layU layO .oSp := by
  intro z hz h
  rw [hN] at h
  exact h.imp (uniq_sh S rU rO rSp lo layU layO codes sentU sentO hlU hlO hU hO _ z hz)
    (uniq_sh S rU rO rSp lo layU layO codes sentU sentO hlU hlO hU hO _ z hz)

/-- tupleTen_members' huniq: the data's first member is o_omega, its second o_sp. -/
theorem huniq_ten : ∀ z ∈ msSh S rU rO rSp lo layU layO,
    SitsAt z (N.tenant .oSp).1 (N.tenant .oSp).2 ∨
      SitsAt z (N.tenant .oOmega).1 (N.tenant .oOmega).2 →
    z = memSh S rU rO rSp lo layU layO .oOmega ∨ z = memSh S rU rO rSp lo layU layO .oSp := by
  intro z hz h
  rw [hN] at h
  exact h.symm.imp (uniq_sh S rU rO rSp lo layU layO codes sentU sentO hlU hlO hU hO _ z hz)
    (uniq_sh S rU rO rSp lo layU layO codes sentU sentO hlU hlO hU hO _ z hz)

variable (arr : ℕ → ℕ → ℕ)
  (harr : ∀ m m' : Msg2, arr (tenantSh lo layU layO m).1 (tenantSh lo layU layO m).2 =
    arr (tenantSh lo layU layO m').1 (tenantSh lo layU layO m').2 → m = m')
include harr

omit hlU hlO hU hO hN in
/-- **hN, at every block.** -/
theorem hN_sh (k : ℕ) :
    ((mineS N (msSh S rU rO rSp lo layU layO) true k).map (numOf arr)).Nodup := by
  have hall : ((msSh S rU rO rSp lo layU layO).map (numOf arr)).Nodup := by
    rw [msSh_all]
    have a1 : ¬ arr (tenantSh lo layU layO .oU).1 (tenantSh lo layU layO .oU).2 =
        arr (tenantSh lo layU layO .oOmega).1 (tenantSh lo layU layO .oOmega).2 :=
      fun e => absurd (harr .oU .oOmega e) (by decide)
    have a2 : ¬ arr (tenantSh lo layU layO .oU).1 (tenantSh lo layU layO .oU).2 =
        arr (tenantSh lo layU layO .oSp).1 (tenantSh lo layU layO .oSp).2 :=
      fun e => absurd (harr .oU .oSp e) (by decide)
    have a3 : ¬ arr (tenantSh lo layU layO .oOmega).1 (tenantSh lo layU layO .oOmega).2 =
        arr (tenantSh lo layU layO .oSp).1 (tenantSh lo layU layO .oSp).2 :=
      fun e => absurd (harr .oOmega .oSp e) (by decide)
    show [arr (tenantSh lo layU layO .oU).1 (tenantSh lo layU layO .oU).2,
      arr (tenantSh lo layU layO .oOmega).1 (tenantSh lo layU layO .oOmega).2,
      arr (tenantSh lo layU layO .oSp).1 (tenantSh lo layU layO .oSp).2].Nodup
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
      List.nodup_nil, and_true, not_false_eq_true]
    exact ⟨⟨a1, a2⟩, a3⟩
  exact hall.sublist (List.Sublist.map _ List.filter_sublist)

/-- One message apart from another, as the table's test wants it. -/
theorem apart_pair (m m' : Msg2) (h : m ≠ m') :
    (numOfComp N arr (.msg m) != some (arr (N.tenant m').1 (N.tenant m').2) &&
      seatOfComp N (.msg m) != some (N.tenant m')) = true := by
  rw [Bool.and_eq_true, bne_iff_ne, bne_iff_ne]
  refine ⟨fun e => h ?_, fun e => h ?_⟩
  · have e' := Option.some.inj e
    rw [hN] at e'
    exact harr m m' e'
  · have e' := Option.some.inj e
    rw [hN] at e'
    exact tenants_apart codes sentU sentO layU layO hlU hlO hU hO lo m m' e'

/-- **The tests on the plan's numbers at block 9.** -/
theorem hap_nine : apartAt N arr true 9 (.msg .oSp) = true ∧ apartAt N arr true 9 (.msg .oOmega) = true := by
  have hl : laysAtS true 9 = [.msg .oU] := by decide
  unfold apartAt
  rw [hl]
  simp only [List.all_cons, List.all_nil, Bool.and_true]
  exact ⟨apart_pair lo layU layO codes sentU sentO hlU hlO hU hO N hN arr harr .oSp .oU (by decide),
    apart_pair lo layU layO codes sentU sentO hlU hlO hU hO N hN arr harr .oOmega .oU (by decide)⟩

/-- **At block 10.** -/
theorem hap_ten : apartAt N arr true 10 (.msg .oOmega) = true := by
  have hl : laysAtS true 10 = [.msg .oSp] := by decide
  unfold apartAt
  rw [hl]
  simp only [List.all_cons, List.all_nil, Bool.and_true]
  exact apart_pair lo layU layO codes sentU sentO hlU hlO hU hO N hN arr harr .oOmega .oSp (by decide)

end

end Desc.K14.Law.Fence

#print axioms Desc.K14.Law.Fence.uniq_sh
#print axioms Desc.K14.Law.Fence.memSh_ne
#print axioms Desc.K14.Law.Fence.huniq_nine
#print axioms Desc.K14.Law.Fence.huniq_ten
#print axioms Desc.K14.Law.Fence.hN_sh
#print axioms Desc.K14.Law.Fence.hap_nine
#print axioms Desc.K14.Law.Fence.hap_ten
