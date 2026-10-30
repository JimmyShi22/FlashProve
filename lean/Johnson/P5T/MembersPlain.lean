-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P5T/MembersPlain.lean: TWO TESTS ON THE TYPED ORACLE MESSAGES' LISTS (`seatsFitB`,
Johnson/Desc/PlanMem.lean; `groupsAreMembers`, Johnson/Desc/First/BordersPlan.lean) RESTATED OVER
THE FIRST CHAIN's ENTRIES (`planSeats`, Johnson/P5T/PlanSeats.lean) ALONE. Two definitions with
code, five theorems.

Why. `memberLists` (MemberLists.lean) takes the shapes, with the radii, from the sendings'
rows, whose maker reads layout.txt and the planner's calls; the (tree, tenant)s from `planSeats`.
The two tests read of a list's entry its shapes and its (tree, tenant)s: NO RADIUS. Restated over
`planSeats` they read the public part's sendings and declared rounds alone (and, the first, the IOP
as written in Lean).
  `seatsFitP F cs ps`: no entry with a sample has a fault at its (tree, tenant).
  `groupsP N n ps`: every (tree, tenant) of every group, the index masks' and W's is an entry's with
    a sample.
  `all_congr_mem`, `fit_of_sending`: steps.
  `seatsFitB_plain`: where `membersFault` finds nothing and `sendsBelowB` accepts
    (Johnson/P5T/MemsSame.lean): seatsFitB F cs (memberLists rows ps) = seatsFitP F cs ps.
  `mem_allSeats`, `groups_plain`: where `sendsBelowB` accepts:
    groupsAreMembers N n (memberLists rows ps) = groupsP N n ps.
SO, FOR THESE TWO TESTS, WHAT STILL READS THE ROWS IS `membersFault` AND `sendsBelowB`.

Limits. Equations of tests: nothing on whether a test accepts. Other tests on the typed oracle
messages are not restated here. Nothing on the radii. Nothing on soundness.

-/
import Johnson.P5T.MemsSame
import Johnson.Desc.First.BordersPlan

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P5T
open VerifiableInference.Desc (FileDescription seatFaultAt seatsFitB allSeats)
open VerifiableInference.Desc.First (Numbers groupsAreMembers)

/-- No entry with a sample has a fault at its (tree, tenant). -/
def seatsFitP {Xi : Type} (F : FileDescription Xi) (cs : OnBytes.Codes) (ps : List PSeat) : Bool :=
  (ps.filter (·.smpd)).all fun p => (seatFaultAt F cs "" p.shape p.seat.1 p.seat.2).isNone

/-- Every (tree, tenant) of every group, the index masks' and W's is an entry's with a sample. -/
def groupsP (N : Numbers) (n : Nat) (ps : List PSeat) : Bool :=
  ((List.range (n + 1)).flatMap N.group ++ [N.index, N.w]).all
    ((ps.filter (·.smpd)).map (·.seat)).contains

/-- Two tests that agree at every member of a list agree on the list. -/
theorem all_congr_mem {α : Type} (l : List α) (f g : α → Bool) (h : ∀ a ∈ l, f a = g a) :
    l.all f = l.all g := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.all_cons, List.all_cons, h a (List.mem_cons_self ..),
      ih fun x hx => h x (List.mem_cons_of_mem _ hx)]

/-- One sending. -/
theorem fit_of_sending (ok : OnBytes.OracleShape → Nat × Nat → Bool)
    (mine : List PSeat) : ∀ (l : List (OnBytes.OracleShape × Nat)),
    mine.map (·.shape) = l.map (·.1) →
    (l.length == (mine.map (·.seat)).length && (List.range l.length).all fun i =>
      ok (l.getD i default).1 ((mine.map (·.seat)).getD i (0, 0))) =
      mine.all fun p => ok p.shape p.seat := by
  induction mine with
  | nil =>
    intro l h
    cases l with
    | nil => rfl
    | cons a l => simp at h
  | cons p mine ih =>
    intro l h
    cases l with
    | nil => simp at h
    | cons a l =>
      simp only [List.map_cons, List.cons.injEq] at h
      have ih' := ih l h.2
      simp only [List.map_cons, List.length_cons, List.all_cons, List.range_succ_eq_map,
        List.all_map, List.getD_cons_zero, ← h.1]
      rw [← ih']
      simp only [Function.comp_def, List.getD_cons_succ]
      cases ok p.shape p.seat <;> simp

theorem seatsFitB_plain {Xi : Type} (F : FileDescription Xi) (cs : OnBytes.Codes)
    (rows : List Johnson.G.SendRow) (ps : List PSeat)
    (ha : (membersFault rows ps).isEmpty = true) (hb : sendsBelowB rows ps = true) :
    seatsFitB F cs (memberLists rows ps) = seatsFitP F cs ps := by
  have hs := shapes_of_noFault rows ps (List.isEmpty_iff.1 ha)
  have e : seatsFitB F cs (memberLists rows ps) = (firstRows rows).zipIdx.all fun r =>
      (ps.filter fun p => p.send == r.2 && p.smpd).all fun p =>
        (seatFaultAt F cs "" p.shape p.seat.1 p.seat.2).isNone := by
    unfold seatsFitB memberLists
    rw [List.all_map]
    refine all_congr_mem _ _ _ fun r hr => ?_
    exact fit_of_sending (fun sh s => (seatFaultAt F cs "" sh s.1 s.2).isNone) _ _ (hs r hr)
  rw [e, Bool.eq_iff_iff]
  unfold seatsFitP
  simp only [List.all_eq_true, List.mem_filter]
  constructor
  · intro h p ⟨hp, hsm⟩
    have hlt : p.send < (firstRows rows).length := by
      have := List.all_eq_true.1 hb p hp
      simpa [hsm] using this
    exact h ((firstRows rows)[p.send], p.send) (List.mem_zipIdx_iff_getElem?.2 (by simp [hlt])) p
      ⟨hp, by simp [hsm]⟩
  · intro h r _ p ⟨hp, hq⟩
    exact h p ⟨hp, (Bool.and_eq_true_iff.1 hq).2⟩

theorem mem_allSeats (rows : List Johnson.G.SendRow) (ps : List PSeat)
    (hb : sendsBelowB rows ps = true) (s : Nat × Nat) :
    s ∈ allSeats (memberLists rows ps) ↔ s ∈ (ps.filter (·.smpd)).map (·.seat) := by
  unfold allSeats memberLists
  rw [List.mem_flatMap]
  constructor
  · rintro ⟨x, hx, hs⟩
    obtain ⟨r, _, rfl⟩ := List.mem_map.1 hx
    have hs' : s ∈ (ps.filter fun p => p.send == r.2 && p.smpd).map (·.seat) := hs
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hs'
    have hp' := List.mem_filter.1 hp
    exact List.mem_map.2 ⟨p, List.mem_filter.2 ⟨hp'.1, (Bool.and_eq_true_iff.1 hp'.2).2⟩, rfl⟩
  · intro hs
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hs
    have hp' := List.mem_filter.1 hp
    have hsm : p.smpd = true := hp'.2
    have hlt : p.send < (firstRows rows).length := by
      have := List.all_eq_true.1 hb p hp'.1
      simpa [hsm] using this
    refine ⟨_, List.mem_map.2 ⟨((firstRows rows)[p.send], p.send),
      List.mem_zipIdx_iff_getElem?.2 (by simp [hlt]), rfl⟩, ?_⟩
    show p.seat ∈ (ps.filter fun q => q.send == p.send && q.smpd).map (·.seat)
    exact List.mem_map.2 ⟨p, List.mem_filter.2 ⟨hp'.1, by simp [hsm]⟩, rfl⟩

theorem groups_plain (N : Numbers) (n : Nat) (rows : List Johnson.G.SendRow) (ps : List PSeat)
    (hb : sendsBelowB rows ps = true) :
    groupsAreMembers N n (memberLists rows ps) = groupsP N n ps := by
  unfold groupsAreMembers groupsP
  refine all_congr_mem _ _ _ fun s _ => ?_
  rw [Bool.eq_iff_iff, List.contains_iff_mem, List.contains_iff_mem]
  exact mem_allSeats rows ps hb s

end P5T

#print axioms P5T.all_congr_mem
#print axioms P5T.fit_of_sending
#print axioms P5T.seatsFitB_plain
#print axioms P5T.mem_allSeats
#print axioms P5T.groups_plain
