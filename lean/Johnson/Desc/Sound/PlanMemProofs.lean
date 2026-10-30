-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Sound/PlanMemProofs.lean: WHAT A YES OF THE PLAIN TESTS ON THE MEMBERS' LISTS GIVES:
the premises on the plan's side of the law on committed words (WordsLaw.lean), as theorems.
  `Sending.ofLists`, `sendsOf L`, `msOf L`: the members (`Mem`, World.lean) of plain lists
    (`MemberLists`, Johnson/Desc/PlanMem.lean).
  `seat_of_noFault` (proved): where the plain `seatFaultAt` (Johnson/Desc/SeatAt.lean) finds no
    fault, the seven clauses of `SeatFits` (MsgSig.lean) hold, in the library's own terms (`aOf`,
    `cMain`).
  `seatsFit_of_B` (proved): a yes of `seatsFitB` gives `SeatsFit cs G (msOf L)`; `seatsFit_sub`: and
    of any of these members.
  `meets_of_B` (proved): a yes of the library's `allMeet` (Johnson/Pack/Check.lean) at each entry
    gives the library's `MeetsAt` at every member, at its radius: the premise of the library's lemma
    on a sending.
  `padB_of_key`, `inMsg_of_key`, `padSame_sound` (proved): a yes of `padSame`: two members with one
    number have their pads at one place and one range: what makes "alike outside their pads"
    (`AgreeOff`, World.lean) one notion, and a copy's message outside its pad its original's.
  `seat_mem` (proved): a member's seat stands in `allSeats L`, where the entry has as many seats as
    shapes.
Limits. THE YES ITSELF IS A PREMISE: at a real plan it is known by an evaluation, which is evidence
and no proof. That the lists are the plan's is said by nothing here. Nothing on soundness.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Sound.MeaningSig
import Johnson.Desc.PlanMem
import Johnson.Pack.Check

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace VerifiableInference.Desc.Sound
open Cb Johnson.Pack OnBytes.Slice

/-- A sending off two plain lists. Beyond the seats' list: (0, 0). -/
def Sending.ofLists (l : List (OnBytes.OracleShape × ℕ)) (seats : List (ℕ × ℕ)) : Sending :=
  ⟨l, fun i => seats.getD i.val (0, 0)⟩

/-- The sendings of plain lists. -/
def sendsOf (L : MemberLists) : List Sending := L.map fun x => Sending.ofLists x.1 x.2

/-- **The members of plain lists.** -/
def msOf (L : MemberLists) : List Mem := membersOf (sendsOf L)

theorem true_of_ite_nil {α : Type} {c : Bool} {x : α}
    (h : (if c = true then ([] : List α) else [x]) = []) : c = true := by
  by_cases hc : c = true
  · exact hc
  · rw [if_neg hc] at h
    cases h

theorem nil_of_ite_none {α β : Type} {l : List α} {x : β}
    (h : (if l.isEmpty = true then (none : Option β) else some x) = none) : l = [] := by
  by_cases hc : l.isEmpty = true
  · exact List.isEmpty_iff.1 hc
  · rw [if_neg hc] at h
    cases h

/-- **Where the plain test finds no fault, the seven clauses hold.** -/
theorem seat_of_noFault {Xi : Type} (G : FileDescription Xi) (cs : OnBytes.Codes) (tag : String)
    (s : OnBytes.OracleShape) (j t : ℕ) (h : seatFaultAt G cs tag s j t = none) :
    ∃ o n, G.oracleAt j = some o ∧ o.tenants[t]? = some n ∧ o.logLength = aOf cs s ∧
      n.main = s.mainRows * s.mainDeg ∧ n.mask = s.maskRows * 3 ∧
      (s.mainRows = 0 ∨ (cMain cs s).a = aOf cs s) ∧
      (o.tenants.map fun t => t.main + t.mask).sum = o.words ∧
      (s.mainDeg = 1 ∨ s.mainDeg = 3) := by
  unfold seatFaultAt at h
  split at h
  · cases h
  · rename_i o ho
    split at h
    · cases h
    · rename_i n hn
      dsimp only at h
      have hb := nil_of_ite_none h
      simp only [List.append_eq_nil_iff] at hb
      obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := hb
      have e1 := beq_iff_eq.1 (true_of_ite_nil h1)
      have e2 := beq_iff_eq.1 (true_of_ite_nil h2)
      have e3 := beq_iff_eq.1 (true_of_ite_nil h3)
      have e4 := true_of_ite_nil h4
      have e5 := beq_iff_eq.1 (true_of_ite_nil h5)
      have e6 := true_of_ite_nil h6
      rw [Bool.or_eq_true, beq_iff_eq, beq_iff_eq] at e4 e6
      exact ⟨o, n, ho, hn, e1, e2, e3, e4, e5, e6⟩

/-- A member of plain lists comes of an entry. -/
theorem mem_msOf (L : MemberLists) (x : Mem) (hx : x ∈ msOf L) :
    ∃ p ∈ L, x.1 = Sending.ofLists p.1 p.2 := by
  unfold msOf membersOf sendsOf at hx
  obtain ⟨s, hs, hx⟩ := List.mem_flatMap.1 hx
  obtain ⟨i, -, rfl⟩ := List.mem_map.1 hx
  obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hs
  exact ⟨p, hp, rfl⟩

/-- **A yes of the plain test gives that the seats fit.** -/
theorem seatsFit_of_B {Xi : Type} (G : FileDescription Xi) (cs : OnBytes.Codes) (L : MemberLists)
    (h : seatsFitB G cs L = true) : SeatsFit cs G (msOf L) := by
  intro x hx
  obtain ⟨p, hp, e⟩ := mem_msOf L x hx
  rw [e]
  intro k
  have h1 := List.all_eq_true.1 h p hp
  rw [Bool.and_eq_true] at h1
  have h2 := List.all_eq_true.1 h1.2 k.val (List.mem_range.2 k.isLt)
  rw [Option.isNone_iff_eq_none] at h2
  have e1 : p.1.getD k.val default = p.1.get k := List.getD_eq_getElem _ _ k.isLt
  rw [e1] at h2
  exact seat_of_noFault G cs "" _ _ _ h2

/-- And of any of these members. -/
theorem seatsFit_sub {Xi : Type} (G : FileDescription Xi) (cs : OnBytes.Codes) (ms mine : List Mem)
    (h : SeatsFit cs G ms) (hs : ∀ x ∈ mine, x ∈ ms) : SeatsFit cs G mine :=
  fun x hx => h x (hs x hx)

/-- **A yes of the library's test at each entry gives the library's `MeetsAt` at every member.** -/
theorem meets_of_B (cs : OnBytes.Codes) (L : MemberLists)
    (h : (L.all fun x => allMeet cs x.1) = true) (x : Mem) (hx : x ∈ msOf L) :
    MeetsAt cs (x.1.l.get x.2).1 (x.1.l.get x.2).2 (dOf cs (x.1.l.get x.2).1)
      (lOf cs (x.1.l.get x.2).1 (x.1.l.get x.2).2) := by
  obtain ⟨p, hp, e⟩ := mem_msOf L x hx
  obtain ⟨s, i⟩ := x
  simp only at e
  subst e
  exact allMeet_sound cs p.1 (List.all_eq_true.1 h p hp) i

/-- The test on a pad's place reads the shape through `padKey` alone. -/
theorem padB_of_key (cs : OnBytes.Codes) (s s' : OnBytes.OracleShape)
    (h : padKey cs s = padKey cs s') : padB cs s = padB cs s' := by
  unfold padKey at h
  simp only [Prod.mk.injEq] at h
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  funext mask row place
  unfold padB
  rw [h1, h2, h3, h4, h5]

/-- And so do a message's ranges. -/
theorem inMsg_of_key (cs : OnBytes.Codes) (s s' : OnBytes.OracleShape)
    (h : padKey cs s = padKey cs s') : InMsg cs s = InMsg cs s' := by
  unfold padKey at h
  simp only [Prod.mk.injEq] at h
  obtain ⟨h1, h2, -, h4, h5⟩ := h
  have h4' : (pMain cs s).ell = (pMain cs s').ell := h4
  have h5' : (pMask cs s).ell = (pMask cs s').ell := h5
  funext mask row place
  unfold InMsg
  rw [h1, h2, h4', h5']

/-- A member of plain lists, with its index. -/
theorem mem_msOf' (L : MemberLists) (x : Mem) (hx : x ∈ msOf L) :
    ∃ p ∈ L, ∃ i : Fin p.1.length, x = ⟨Sending.ofLists p.1 p.2, i⟩ := by
  unfold msOf membersOf sendsOf at hx
  obtain ⟨s, hs, hx⟩ := List.mem_flatMap.1 hx
  obtain ⟨i, -, rfl⟩ := List.mem_map.1 hx
  obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hs
  exact ⟨p, hp, i, rfl⟩

/-- **A yes of `padSame`: two members with one number have their pads at one place, and one range.**
-/
theorem padSame_sound (cs : OnBytes.Codes) (L : MemberLists) (arr : ℕ → ℕ → ℕ)
    (h : padSame cs L arr = true) (x x' : Mem) (hx : x ∈ msOf L) (hx' : x' ∈ msOf L)
    (hn : numOf arr x = numOf arr x') :
    padB cs (x.1.l.get x.2).1 = padB cs (x'.1.l.get x'.2).1 ∧
      InMsg cs (x.1.l.get x.2).1 = InMsg cs (x'.1.l.get x'.2).1 := by
  obtain ⟨p, hp, i, rfl⟩ := mem_msOf' L x hx
  obtain ⟨p', hp', i', rfl⟩ := mem_msOf' L x' hx'
  have t := List.all_eq_true.1 (List.all_eq_true.1 (List.all_eq_true.1 (List.all_eq_true.1 h p hp)
    i.val (List.mem_range.2 i.isLt)) p' hp') i'.val (List.mem_range.2 i'.isLt)
  rw [Bool.or_eq_true, bne_iff_ne, beq_iff_eq] at t
  have e1 : p.1.getD i.val default = p.1.get i := List.getD_eq_getElem _ _ i.isLt
  have e2 : p'.1.getD i'.val default = p'.1.get i' := List.getD_eq_getElem _ _ i'.isLt
  rw [e1, e2] at t
  have k : padKey cs (p.1.get i).1 = padKey cs (p'.1.get i').1 := t.resolve_left fun c => c hn
  exact ⟨padB_of_key cs _ _ k, inMsg_of_key cs _ _ k⟩

/-- A member's seat stands among all seats. -/
theorem seat_mem {Xi : Type} (G : FileDescription Xi) (cs : OnBytes.Codes) (L : MemberLists)
    (h : seatsFitB G cs L = true) (x : Mem) (hx : x ∈ msOf L) : x.1.seat x.2 ∈ allSeats L := by
  obtain ⟨p, hp, e⟩ := mem_msOf L x hx
  obtain ⟨s, i⟩ := x
  simp only at e
  subst e
  have h1 := List.all_eq_true.1 h p hp
  rw [Bool.and_eq_true, beq_iff_eq] at h1
  have hi : i.val < p.2.length := h1.1 ▸ i.isLt
  refine List.mem_flatMap.2 ⟨p, hp, ?_⟩
  show p.2.getD i.val (0, 0) ∈ p.2
  rw [List.getD_eq_getElem _ _ hi]
  exact List.getElem_mem hi

end VerifiableInference.Desc.Sound
