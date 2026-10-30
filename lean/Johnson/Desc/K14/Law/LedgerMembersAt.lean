-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K14/Law/LedgerMembersAt.lean: THE MEMBERS AT THE TWO SENDINGS, AT THE FILLING.
share_seamed (Johnson/Desc/K14/Law/LedgerSeamRow.lean) asks, at each of the shared chain's two
sendings, a member for every message of the sending (memK2, memK5), a list of the new sampled
members (new2, new5), and four premises on them: entry, all, hno, hnew. HERE they are laid and paid
at the filling of the members (ms := msSh, oNo := oNoSh sentU.size,
N.tenant := tenantSh: Johnson/Desc/Sound/SharedMembers.lean, SeamNumbersSh.lean), its three radii
laid as K1's places' own (rad2 0, rad5 0, rad5 1).

  mask_unsampled  of "send o_u" only the first message is sampled: the fresh mask is announced with
                  no sample.
  memK2, new2, entry_two, all_two, hno_two, hnew_two   at "send o_u": o_u's member; for the mask,
                  which nobody samples, a member made for its entry.
  memK5, new5, entry_five, all_five, hno_five, hnew_five   at "send o_omega": o_omega's and o_sp's
                  members.
WHAT STAYS. hUw, hS, hm (the plan: the sending's messages) · hlU, hlO (the two layouts) · hN (the
table's tenants are tenantSh's) · hkU, hk, hkS (the three are sampled: by PlanShapes under Q.S.ok).
What is not claimed. No soundness; no level. NO MEMBER OF THE PROMISE IS SHOWN.

-/
import Johnson.Desc.K14.Law.LedgerSeamRow
import Johnson.Desc.K14.Law.LedgerNew
import Johnson.Desc.K14.Law.PlanShapes
import Johnson.Desc.Sound.SeamNumbersSh

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Law
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Maker
open VerifiableInference.Desc.K1 (shapesOf shapeAt sampledAt)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.Shared
open Desc.K14.Law.Fence

variable (Q : P14) (sentU : Array OracleNotice) (layU layO : TreeLay) (lo : ℕ) (rad2 rad5 : ℕ → ℕ)

/-- **Of "send o_u" only the first message is sampled.** -/
theorem mask_unsampled (hUw : withU Q.S = some sentU) (k : Fin (shapesOf (parU Q sentU)).length)
    (hk : sampledAt (parU Q sentU) k) : k.val = 0 := by
  by_contra h0
  obtain ⟨rest, hr, rfl⟩ := withU_cut hUw
  obtain ⟨kv, hkv⟩ := k
  have h0 : kv ≠ 0 := h0
  have hlen := hkv
  rw [show shapesOf (parU Q (#[(⟨Q.S.fold.u, Q.S.fold.leafClass⟩ : OracleNotice)] ++ rest)) = _ from
    shapes_parK1 Q _ _ _] at hlen
  unfold linWithU at hr
  by_cases hm : Q.S.masksAhead = true
  · simp only [hm, if_true] at hr
    cases hn : linMaskNotice Q.S.testU Q.S.fold.leafClass with
    | none => simp [hn] at hr
    | some nt =>
      simp [hn] at hr
      subst hr
      unfold linMaskNotice at hn
      obtain ⟨s, _, rfl⟩ := Option.map_eq_some_iff.1 hn
      have hk1 : kv = 1 := by
        simp at hlen
        omega
      have e : (shapesOf (parU Q (#[(⟨Q.S.fold.u, Q.S.fold.leafClass⟩ : OracleNotice)] ++
          #[foldMaskNotice { ioppFoldShape s {} with maskLeafClass := Q.S.fold.leafClass }])))[kv]?
              =
          some (foldMaskNotice
            { ioppFoldShape s {} with maskLeafClass := Q.S.fold.leafClass }).shape := by
        rw [show shapesOf (parU Q _) = _ from shapes_parK1 Q _ _ _, hk1]
        rfl
      exact ((sampled_of e).1 hk) rfl
  · simp [hm] at hr
    subst hr
    simp at hlen
    omega

/-! ## At "send o_u" -/

/-- A member for each message of "send o_u": o_u's; for the mask, which nobody samples, one made for
its entry, at o_u's seat. -/
def memK2 (k : Fin (shapesOf (parU Q sentU)).length) : Mem :=
  if k.val = 0 then (memSh Q.S (rad2 0) (rad5 0) (rad5 1) lo layU layO .oU)
  else ⟨⟨[(shapeAt (parU Q sentU) k, rad2 k.val)], fun _ => tenantSh lo layU layO .oU⟩,
    ⟨0, Nat.one_pos⟩⟩

/-- The new sampled members of "send o_u". -/
def new2 : List Mem := [(memSh Q.S (rad2 0) (rad5 0) (rad5 1) lo layU layO .oU)]

theorem entry_two (hUw : withU Q.S = some sentU) (k : Fin (shapesOf (parU Q sentU)).length) :
    (memK2 Q sentU layU layO lo rad2 rad5 k).1.l.get (memK2 Q sentU layU layO lo rad2 rad5 k).2 =
      (shapeAt (parU Q sentU) k, rad2 k.val) := by
  unfold memK2
  by_cases h : k.val = 0
  · rw [if_pos h]
    obtain ⟨kv, hkv⟩ := k
    obtain rfl : kv = 0 := h
    rw [show shapeAt (parU Q sentU) ⟨0, hkv⟩ = Q.S.fold.u from shapeAtU Q sentU hUw hkv]
    rfl
  · rw [if_neg h]
    rfl

theorem all_two (hU0 : 0 < (shapesOf (parU Q sentU)).length)
    (hkU : sampledAt (parU Q sentU) ⟨0, hU0⟩) :
    ∀ x ∈ new2 Q layU layO lo rad2 rad5, ∃ k, sampledAt (parU Q sentU) k ∧
      memK2 Q sentU layU layO lo rad2 rad5 k = x := by
  intro x hx
  obtain rfl : x = _ := List.mem_singleton.1 hx
  exact ⟨⟨0, hU0⟩, hkU, if_pos rfl⟩

theorem hno_two (hUw : withU Q.S = some sentU) (k : Fin (shapesOf (parU Q sentU)).length)
    (hk : sampledAt (parU Q sentU) k) :
    oNoSh sentU.size (memK2 Q sentU layU layO lo rad2 rad5 k) = 0 + k.val := by
  have h := mask_unsampled Q sentU hUw k hk
  unfold memK2
  rw [if_pos h, h]
  rfl

theorem hnew_two (N : NumbersS) (hN : N.tenant = tenantSh lo layU layO)
    (hlU : layTrees Q.codes sentU = some layU)
    (hlO : layTrees Q.codes (withOmega Q.S) = some layO) (hU : 0 < sentU.size)
    (hO : 1 < (withOmega Q.S).size) :
    ∀ x ∈ (msSh Q.S (rad2 0) (rad5 0) (rad5 1) lo layU layO), SitsAt x (N.tenant .oU).1 (N.tenant
        .oU).2 →
      x ∈ new2 Q layU layO lo rad2 rad5 := by
  intro x hx hs
  rw [hN] at hs
  exact List.mem_singleton.2 (uniq_sh Q.S (rad2 0) (rad5 0) (rad5 1) lo layU layO Q.codes sentU
    (withOmega Q.S) hlU hlO hU hO .oU x hx hs)

/-! ## At "send o_omega" -/

/-- A member for each message of "send o_omega". -/
def memK5 (k : Fin (shapesOf (parO Q)).length) : Mem :=
  if k.val = 0 then (memSh Q.S (rad2 0) (rad5 0) (rad5 1) lo layU layO .oOmega) else (memSh Q.S
      (rad2 0) (rad5 0) (rad5 1) lo layU layO .oSp)

/-- The new sampled members of "send o_omega". -/
def new5 : List Mem := [(memSh Q.S (rad2 0) (rad5 0) (rad5 1) lo layU layO .oOmega), (memSh Q.S
    (rad2 0) (rad5 0) (rad5 1) lo layU layO .oSp)]

theorem entry_five (hS : Q.S.sharedSplitNeeded = true) (k : Fin (shapesOf (parO Q)).length) :
    (memK5 Q layU layO lo rad2 rad5 k).1.l.get (memK5 Q layU layO lo rad2 rad5 k).2 =
      (shapeAt (parO Q) k, rad5 k.val) := by
  have hlen : (shapesOf (parO Q)).length = 2 := by
    rw [(lengths Q #[]).2, sizeOmega Q.S hS]
  unfold memK5
  obtain ⟨kv, hkv⟩ := k
  by_cases h : kv = 0
  · subst h
    rw [if_pos rfl, shape_omega Q hkv]
    rfl
  · obtain rfl : kv = 1 := by omega
    rw [if_neg Nat.one_ne_zero, shape_split Q hS hkv]
    rfl

theorem all_five (h0 : 0 < (shapesOf (parO Q)).length) (hk : sampledAt (parO Q) ⟨0, h0⟩)
    (h1 : 1 < (shapesOf (parO Q)).length) (hkS : sampledAt (parO Q) ⟨1, h1⟩) :
    ∀ x ∈ new5 Q layU layO lo rad2 rad5, ∃ k, sampledAt (parO Q) k ∧
      memK5 Q layU layO lo rad2 rad5 k = x := by
  intro x hx
  rcases List.mem_cons.1 hx with rfl | hx
  · exact ⟨⟨0, h0⟩, hk, if_pos rfl⟩
  · obtain rfl : x = _ := List.mem_singleton.1 hx
    exact ⟨⟨1, h1⟩, hkS, if_neg Nat.one_ne_zero⟩

theorem hno_five (hS : Q.S.sharedSplitNeeded = true) (k : Fin (shapesOf (parO Q)).length) :
    oNoSh sentU.size (memK5 Q layU layO lo rad2 rad5 k) = sentU.size + k.val := by
  have hlen : (shapesOf (parO Q)).length = 2 := by
    rw [(lengths Q #[]).2, sizeOmega Q.S hS]
  unfold memK5
  obtain ⟨kv, hkv⟩ := k
  by_cases h : kv = 0
  · subst h
    rw [if_pos rfl]
    rfl
  · obtain rfl : kv = 1 := by omega
    rw [if_neg Nat.one_ne_zero]
    rfl

theorem hnew_five (N : NumbersS) (hN : N.tenant = tenantSh lo layU layO)
    (hlU : layTrees Q.codes sentU = some layU)
    (hlO : layTrees Q.codes (withOmega Q.S) = some layO) (hU : 0 < sentU.size)
    (hO : 1 < (withOmega Q.S).size) :
    ∀ m, m = Msg2.oOmega ∨ m = .oSp → ∀ x ∈ (msSh Q.S (rad2 0) (rad5 0) (rad5 1) lo layU layO),
      SitsAt x (N.tenant m).1 (N.tenant m).2 → x ∈ new5 Q layU layO lo rad2 rad5 := by
  intro m hm x hx hs
  rw [hN] at hs
  have e := uniq_sh Q.S (rad2 0) (rad5 0) (rad5 1) lo layU layO Q.codes sentU (withOmega Q.S) hlU
      hlO
    hU hO m x hx hs
  rcases hm with rfl | rfl
  · exact e ▸ List.mem_cons_self
  · exact e ▸ List.mem_cons_of_mem _ List.mem_cons_self

end Desc.K14.Law

#print axioms Desc.K14.Law.entry_two
#print axioms Desc.K14.Law.all_two
#print axioms Desc.K14.Law.hno_two
#print axioms Desc.K14.Law.hnew_two
#print axioms Desc.K14.Law.entry_five
#print axioms Desc.K14.Law.all_five
#print axioms Desc.K14.Law.hno_five
#print axioms Desc.K14.Law.hnew_five
#print axioms Desc.K14.Law.mask_unsampled
