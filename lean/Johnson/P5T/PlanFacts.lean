-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P5T/PlanFacts.lean: TWO FACTS ON THE LIST OF SEATS `planSeats` (Johnson/P5T/PlanSeats.lean),
BY ITS MAKE. Theorems, proved. No test is needed for either.

(1) THE KEY (0, l, k) NUMBERS A LINK's ORACLE MESSAGES AS THE LAYOUT DOES. An array of the layout
names its oracle message by `ReqArray.message`: "which of its link's oracle messages holds it, from
0" (OnBytes/Params/Items.lean): the place in `(S.link[l]).messages`.
  `rolesOf_own`: a role "own k" among the roles of "link l, moment m" comes of the message at place
    k of that very list, and that message's moment is m.
  `planSeats_own`: a seat of `planSeats Z dl` whose segment is (l, m) and whose role is "own k" HAS
    THE KEY (0, l, k), AND k IS THE PLACE, IN `(Z.first.shape.link[l]).messages`, OF A MESSAGE OF
    THE MOMENT m.
(2) ABOVE A BOUND THE GROUPS ARE EMPTY.
  `segOf_lt`: a label is read back as a link's number below the bound that the reader is given.
  `planSeats_seg`: a seat of `planSeats Z dl` has a segment's number of at most g, g := the LENGTH
    OF THE LIST OF THE REQUEST's GROUPS, `(OnBytes.reqGroups Z.first.shape).toList.length`.
  `group_beyond`: for every k ABOVE g: `(numbersOf (planSeats Z dl)).group k = []`. g IS NOT THE
    LAST GROUP's NUMBER: the list has one group for each link and one for the last test
    (OnBytes/Iop/Req.lean), so its members bear the numbers 0 … g - 1; `planSeats` hands its reader
    of labels the bound g + 1: so BY THE MAKE ALONE THE NUMBER g ITSELF IS LEFT OPEN.
  `segsBelowB ps n` (a Bool) and `group_beyond_of`: the sharp form, at any list ps and any n: where
    no seat of ps has a segment's number above n: for every k above n the group is empty.
Limits. (1) speaks of the seats with the role "own": a kept copy's key (0, l, k) is laid off the
group's own list of born messages: not treated. That the seat's shape is that message's is a test
(`rolesFit`). Nothing on soundness.

-/
import Johnson.P5T.NumbersOf

set_option autoImplicit false
set_option relaxedAutoImplicit false

open VerifiableInference.Desc VerifiableInference.Desc.First

namespace P5T

theorem rolesOf_own (S : OnBytes.Params.ReqShape) (groups : List OnBytes.ReqGroup) (l m k : Nat)
    (h : Role.own k ∈ rolesOf S groups l m) :
    ∃ M, ((S.link[l]?).bind fun L => L.messages[k]?) = some M ∧ M.moment = m := by
  have key : Role.own k ∈ ((((S.link[l]?).map (·.messages)).getD []).zipIdx.filter
      fun x => x.1.moment == m).map fun x => Role.own x.2 := by
    unfold rolesOf at h
    by_cases hm : (m != 0) = true
    · simpa only [hm, if_true] using h
    · simp only [hm, Bool.false_eq_true, if_false, List.mem_append, List.mem_map,
        List.mem_singleton, reduceCtorEq, and_false, exists_false, or_false, false_or] at h
      rcases h with h | h
      · rcases h with h | h
        · split at h <;> simp at h
        · exact List.mem_map.2 h
      · split at h <;> simp at h
  obtain ⟨x, hx, e⟩ := List.mem_map.1 key
  obtain ⟨hx1, hx2⟩ := List.mem_filter.1 hx
  have ek : x.2 = k := by
    injection e
  have hz := List.mem_zipIdx' hx1
  cases hl : S.link[l]? with
  | none =>
    rw [hl] at hx1
    simp at hx1
  | some L =>
    rw [hl] at hx1
    have hg : L.messages[x.2]? = some x.1 := by
      have := List.mem_zipIdx_iff_getElem?.1 hx1
      simpa using this
    exact ⟨x.1, by rw [Option.bind_some, ← ek]; exact hg, by simpa using hx2⟩

theorem segOf_lt (groups moments : Nat) (label : String) (l m : Nat)
    (h : segOf groups moments label = some (l, m)) : l < groups := by
  unfold segOf at h
  obtain ⟨a, ha, h1⟩ := List.exists_of_findSome?_eq_some h
  obtain ⟨b, -, h2⟩ := List.exists_of_findSome?_eq_some h1
  split at h2
  · injection h2 with e
    injection e with e1 _
    rw [← e1]
    exact List.mem_range.1 ha
  · cases h2

/-- What a seat of the list is made of. -/
theorem planSeats_mem (Z : ProofFile.Pub) (dl : List Fmt.DeclaredRound) (p : PSeat)
    (hp : p ∈ planSeats Z dl) :
    ∃ (label : String) (i : Nat),
      p.seg = segOf ((OnBytes.reqGroups Z.first.shape).toList.length + 1) 16 label ∧
      p.role = (match segOf ((OnBytes.reqGroups Z.first.shape).toList.length + 1) 16 label with
        | some (l, m) => rolesOf Z.first.shape (OnBytes.reqGroups Z.first.shape).toList l m
        | none => []).getD i .other := by
  unfold planSeats at hp
  obtain ⟨s, -, hs⟩ := List.mem_flatMap.1 hp
  split at hs
  · cases hs
  · obtain ⟨i, -, rfl⟩ := List.mem_map.1 hs
    exact ⟨s.1.label, i, rfl, rfl⟩

theorem planSeats_seg (Z : ProofFile.Pub) (dl : List Fmt.DeclaredRound) (p : PSeat)
    (hp : p ∈ planSeats Z dl) (l m : Nat) (hs : p.seg = some (l, m)) :
    l ≤ (OnBytes.reqGroups Z.first.shape).toList.length := by
  obtain ⟨label, i, e1, -⟩ := planSeats_mem Z dl p hp
  exact Nat.lt_succ_iff.1 (segOf_lt _ _ label l m (e1.symm.trans hs))

/-- **The key numbers a link's messages as the layout does.** -/
theorem planSeats_own (Z : ProofFile.Pub) (dl : List Fmt.DeclaredRound) (p : PSeat)
    (hp : p ∈ planSeats Z dl) (l m k : Nat) (hs : p.seg = some (l, m)) (hr : p.role = .own k) :
    keyOf p = (0, l, k) ∧
      ∃ M, ((Z.first.shape.link[l]?).bind fun L => L.messages[k]?) = some M ∧ M.moment = m := by
  refine ⟨by unfold keyOf; rw [hs, hr], ?_⟩
  obtain ⟨label, i, e1, e2⟩ := planSeats_mem Z dl p hp
  rw [← e1, hs] at e2
  have hmem : Role.own k ∈
      rolesOf Z.first.shape (OnBytes.reqGroups Z.first.shape).toList l m := by
    have e3 := hr.symm.trans e2
    rw [List.getD_eq_getElem?_getD] at e3
    cases hg : (rolesOf Z.first.shape (OnBytes.reqGroups Z.first.shape).toList l m)[i]? with
    | none =>
      rw [hg] at e3
      cases e3
    | some r =>
      rw [hg] at e3
      have e4 : r = Role.own k := e3.symm
      rw [← e4]
      exact List.mem_of_getElem? hg
  exact rolesOf_own _ _ l m k hmem

/-- No seat of the list has a segment's number above n. -/
def segsBelowB (ps : List PSeat) (n : Nat) : Bool :=
  ps.all fun p =>
    match p.seg with
    | some (l, _) => decide (l ≤ n)
    | none => true

/-- **Above n the groups are empty**, where the test accepts. -/
theorem group_beyond_of (ps : List PSeat) (n : Nat) (h : segsBelowB ps n = true) (k : Nat)
    (hk : n < k) : (numbersOf ps).group k = [] := by
  have h0 : ∀ t, (numbersOf ps).sent k t = [] := by
    intro t
    show (ps.filter fun p => p.seg == some (k, t) && p.smpd && !p.isStart).map (·.seat) = []
    rw [List.map_eq_nil_iff, List.filter_eq_nil_iff]
    intro p hp hc
    simp only [Bool.and_eq_true, beq_iff_eq] at hc
    have h1 := List.all_eq_true.1 h p hp
    rw [hc.1.1] at h1
    have h2 : k ≤ n := of_decide_eq_true h1
    omega
  unfold Numbers.group
  rw [h0, h0, h0]
  rfl

/-- **Above the length of the list of the request's groups the groups are empty**, by the make. -/
theorem group_beyond (Z : ProofFile.Pub) (dl : List Fmt.DeclaredRound) (k : Nat)
    (hk : (OnBytes.reqGroups Z.first.shape).toList.length < k) :
    (numbersOf (planSeats Z dl)).group k = [] := by
  have h0 : ∀ t, (numbersOf (planSeats Z dl)).sent k t = [] := by
    intro t
    show ((planSeats Z dl).filter fun p => p.seg == some (k, t) && p.smpd && !p.isStart).map
      (·.seat) = []
    rw [List.map_eq_nil_iff, List.filter_eq_nil_iff]
    intro p hp hc
    simp only [Bool.and_eq_true, beq_iff_eq] at hc
    have := planSeats_seg Z dl p hp k t hc.1.1
    omega
  unfold Numbers.group
  rw [h0, h0, h0]
  rfl

end P5T

#print axioms P5T.rolesOf_own
#print axioms P5T.planSeats_own
#print axioms P5T.planSeats_seg
#print axioms P5T.group_beyond
#print axioms P5T.group_beyond_of
