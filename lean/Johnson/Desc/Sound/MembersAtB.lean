-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Sound/MembersAtB.lean: A TEST WITH CODE ON PLAIN LISTS: WHOEVER OF THE TABLE's MEMBERS
SITS AT ONE OF SOME LISTED TENANTS IS, BY PLACE, THE MEMBER OF A TYPED LIST. Definitions, and
theorems with their proofs. No kind of sub-protocol is named but in section 4.

The table of joints quantifies over "every member of ms that sits at tenant t of tree j"
(`pinJT`, `noCollJT`, `shownJT`: Johnson/Desc/Sound/MeaningSig.lean). A kind's law speaks of the
members of its own typed list. Where ms is made of plain lists (`msOf L`,
Johnson/Desc/Sound/PlanMemProofs.lean), that the two are the same members is a fact on public lists.

Main names:
  `pairOf x`, `pairsOf L`, `pairs_eq`: a member's entry (shape, radius) and seat; these pairs off
    the plain lists, with code; the members of `msOf L` have just these pairs, in order.
  `sitsB L qs es`: THE TEST: at each place a of the list of tenants qs: some pair of L has the seat
    qs[a], and every pair of L with that seat has the entry es[a].
  `sits_of_B`: what it gives where it passes, in terms of `msOf L` and `SitsAt`.
  `seatsByPlace qs`: the seats of a typed list by place: member i sits at qs[i].
  `alike_of_B`: so each member of `msOf L` that sits at a tenant of qs is `Alike`
    (Johnson/Desc/Sound/PinMove.lean) to a member of the typed list es with the seats
    `seatsByPlace qs`.
  `each_of_B`: member by member, where there are as many tenants as typed members: whoever sits at
    the typed member i's seat is `Alike` to that member; the seats are just the listed tenants.
  `onceB L qs`, `nodup_of_B`: no two members of `msOf L` sit at one tenant of qs: the members picked
    by their seats have different seats.
  `mem_filter_of_sits`: a member that sits at a tenant of qs is one of those picked.
  `mineAt_K2`, `laysTok_K2`, `minePadAt_K2`: at a place of the kind K2 the table's extractor lays no
    member's message and no token, and the pads of the members at `N.keptOf` of the segment in
    front.
  `MembersTry`: made-up lists: `sitsB` passes once and fails twice; `onceB` passes once and fails
    once.
Limits. The test's value at a real plan is not shown here. That the plain lists are the plan's is
said by nothing here. Nothing on soundness. On hiding nothing.

-/
import Johnson.Desc.Sound.PlanMemProofs
import Johnson.Desc.Sound.PinMove
import Johnson.Desc.Sound.BordersFill

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Sound
open OnBytes (OracleShape)
open VerifiableInference.Desc.First (ModelPart Numbers laysSeats laysPads laysTok rowOf)

/-! ## 1 The members as plain pairs -/

/-- A member's entry (shape and radius) and its seat. -/
def pairOf (x : Mem) : (OracleShape × ℕ) × (ℕ × ℕ) := (x.1.l.get x.2, x.1.seat x.2)

/-- The same pairs off the plain lists, with code. -/
def pairsOf (L : MemberLists) : List ((OracleShape × ℕ) × (ℕ × ℕ)) :=
  L.flatMap fun e => (List.finRange e.1.length).map fun i => (e.1.get i, e.2.getD i.val (0, 0))

/-- **The members of plain lists have just these pairs, in order.** -/
theorem pairs_eq (L : MemberLists) : (msOf L).map pairOf = pairsOf L := by
  unfold msOf membersOf sendsOf pairsOf
  rw [List.flatMap_map, List.map_flatMap]
  refine List.flatMap_congr fun e _ => ?_
  rw [List.map_map]
  rfl

theorem pair_mem {L : MemberLists} {x : Mem} (hx : x ∈ msOf L) : pairOf x ∈ pairsOf L := by
  rw [← pairs_eq]
  exact List.mem_map_of_mem hx

theorem mem_of_pair {L : MemberLists} {p : (OracleShape × ℕ) × (ℕ × ℕ)} (hp : p ∈ pairsOf L) :
    ∃ x ∈ msOf L, pairOf x = p := by
  rw [← pairs_eq] at hp
  exact List.mem_map.1 hp

/-! ## 2 The test -/

/-- **THE TEST.** qs: tenants (tree, tenant); es: a typed list's entries. By place. -/
def sitsB (L : MemberLists) (qs : List (ℕ × ℕ)) (es : List (OracleShape × ℕ)) : Bool :=
  decide (qs.length ≤ es.length) &&
    (qs.zip es).all fun qe =>
      ((pairsOf L).any fun p => p.2 == qe.1) && (pairsOf L).all fun p => p.2 != qe.1 || p.1 == qe.2

/-- **What it gives where it passes.** -/
theorem sits_of_B {L : MemberLists} {qs : List (ℕ × ℕ)} {es : List (OracleShape × ℕ)}
    (h : sitsB L qs es = true) (a : ℕ) (q : ℕ × ℕ) (hq : qs[a]? = some q) :
    ∃ e, es[a]? = some e ∧ (∃ x ∈ msOf L, SitsAt x q.1 q.2) ∧
      ∀ x ∈ msOf L, SitsAt x q.1 q.2 → x.1.l.get x.2 = e := by
  unfold sitsB at h
  rw [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨hl, hall⟩ := h
  have ha : a < qs.length := (List.getElem?_eq_some_iff.1 hq).1
  have ha' : a < es.length := Nat.lt_of_lt_of_le ha hl
  have hz : (qs.zip es)[a]? = some (q, es[a]) := by
    rw [List.getElem?_zip_eq_some]
    exact ⟨hq, List.getElem?_eq_getElem ha'⟩
  have h1 := List.all_eq_true.1 hall _ (List.mem_of_getElem? hz)
  rw [Bool.and_eq_true] at h1
  refine ⟨es[a], List.getElem?_eq_getElem ha', ?_, fun x hx hs => ?_⟩
  · obtain ⟨p, hp, e⟩ := List.any_eq_true.1 h1.1
    obtain ⟨x, hx, rfl⟩ := mem_of_pair hp
    exact ⟨x, hx, beq_iff_eq.1 e⟩
  · have h2 := List.all_eq_true.1 h1.2 _ (pair_mem hx)
    rw [Bool.or_eq_true, bne_iff_ne, beq_iff_eq] at h2
    rcases h2 with h2 | h2
    · exact absurd hs h2
    · exact h2

/-- The seats of a typed list by place: member i sits at the i-th of the listed tenants. -/
def seatsByPlace (qs : List (ℕ × ℕ)) (n : ℕ) : Fin n → ℕ × ℕ := fun i => qs.getD i.val (0, 0)

/-- **Each member that sits at a listed tenant is alike to a member of the typed list**, whose seats
are the listed tenants by place; and some member sits there. -/
theorem alike_of_B {L : MemberLists} {qs : List (ℕ × ℕ)} {es : List (OracleShape × ℕ)}
    (h : sitsB L qs es = true) :
    ∀ q ∈ qs, (∃ x ∈ msOf L, SitsAt x q.1 q.2) ∧
      ∀ x ∈ msOf L, SitsAt x q.1 q.2 →
        ∃ i : Fin es.length, Alike x ⟨⟨es, seatsByPlace qs es.length⟩, i⟩ := by
  intro q hq
  obtain ⟨a, ha⟩ := List.getElem?_of_mem hq
  obtain ⟨e, he, h1, h2⟩ := sits_of_B h a q ha
  refine ⟨h1, fun x hx hs => ?_⟩
  obtain ⟨ha', e'⟩ := List.getElem?_eq_some_iff.1 he
  refine ⟨⟨a, ha'⟩, ?_, ?_⟩
  · rw [h2 x hx hs]
    exact e'.symm
  · show x.1.seat x.2 = qs.getD a (0, 0)
    rw [List.getD_eq_getElem?_getD, ha]
    exact hs

/-- **Member by member**: where the test passes and there are as many tenants as typed members:
every member of `msOf L` that sits at the seat of the typed member i is alike to THAT member; the
typed members' seats are just the listed tenants; and at each of these a member of `msOf L` sits. -/
theorem each_of_B {L : MemberLists} {qs : List (ℕ × ℕ)} {es : List (OracleShape × ℕ)}
    (h : sitsB L qs es = true) (hl : qs.length = es.length) :
    (∀ i : Fin es.length, ∀ x ∈ msOf L,
      SitsAt x (seatsByPlace qs es.length i).1 (seatsByPlace qs es.length i).2 →
        Alike x ⟨⟨es, seatsByPlace qs es.length⟩, i⟩) ∧
      (∀ q ∈ qs, ∃ i : Fin es.length, seatsByPlace qs es.length i = q) ∧
      (∀ i : Fin es.length, seatsByPlace qs es.length i ∈ qs) ∧
      ∀ q ∈ qs, ∃ x ∈ msOf L, SitsAt x q.1 q.2 := by
  have hat : ∀ i : Fin es.length, qs[i.val]? = some (seatsByPlace qs es.length i) := by
    intro i
    have hi : i.val < qs.length := by
      rw [hl]
      exact i.isLt
    show qs[i.val]? = some (qs.getD i.val (0, 0))
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
    rfl
  refine ⟨fun i x hx hs => ?_, fun q hq => ?_, fun i => List.mem_of_getElem? (hat i),
    fun q hq => (alike_of_B h q hq).1⟩
  · obtain ⟨e, he, -, h2⟩ := sits_of_B h i.val _ (hat i)
    refine ⟨?_, hs⟩
    rw [h2 x hx hs]
    rw [List.getElem?_eq_getElem i.isLt] at he
    exact (Option.some.inj he).symm
  · obtain ⟨a, ha⟩ := List.getElem?_of_mem hq
    have ha' : a < es.length := by
      rw [← hl]
      exact (List.getElem?_eq_some_iff.1 ha).1
    exact ⟨⟨a, ha'⟩, Option.some.inj ((hat ⟨a, ha'⟩).symm.trans ha)⟩

/-! ## 3 The members picked by their seats -/

/-- No two pairs of L have one seat among the listed tenants. -/
def onceB (L : MemberLists) (qs : List (ℕ × ℕ)) : Bool :=
  decide (((pairsOf L).map (·.2)).filter fun s => qs.contains s).Nodup

/-- **The members picked by their seats have different seats.** -/
theorem nodup_of_B {L : MemberLists} {qs : List (ℕ × ℕ)} (h : onceB L qs = true) :
    (((msOf L).filter fun x => qs.contains (x.1.seat x.2)).map seatOf).Nodup := by
  unfold onceB at h
  rw [decide_eq_true_eq, ← pairs_eq, List.map_map] at h
  have e : ((msOf L).filter fun x => qs.contains (x.1.seat x.2)).map seatOf =
      ((msOf L).map ((·.2) ∘ pairOf)).filter fun s => qs.contains s := by
    rw [List.filter_map]
    rfl
  rw [e]
  exact h

/-- A member that sits at a listed tenant is one of those picked. -/
theorem mem_filter_of_sits {ms : List Mem} {qs : List (ℕ × ℕ)} {x : Mem} (hx : x ∈ ms)
    {q : ℕ × ℕ} (hq : q ∈ qs) (hs : SitsAt x q.1 q.2) :
    x ∈ ms.filter fun x => qs.contains (x.1.seat x.2) := by
  rw [List.mem_filter]
  refine ⟨hx, ?_⟩
  rw [show x.1.seat x.2 = q from hs]
  exact List.contains_iff_mem.2 hq

/-! ## 4 What the table's extractor lays at a place of the kind K2 -/

/-- It lays no member's message. -/
theorem mineAt_K2 (ms : List Mem) (N : Numbers) (links : List ModelPart) (p : Place)
    (hk : p.kind = .K2) : mineAt ms N links p = [] := by
  have e : laysSeats N links p = [] := by
    unfold laysSeats
    rw [hk]
    split <;> rfl
  unfold mineAt
  rw [e]
  exact List.filter_eq_nil_iff.2 fun _ _ => by simp

/-- It lays no token. -/
theorem laysTok_K2 (links : List ModelPart) (p : Place) (hk : p.kind = .K2) :
    laysTok links p = false := by
  unfold laysTok
  rw [hk]
  exact Bool.and_false _

/-- It lays the pads of the members that sit at the tenants which the segment in front keeps. -/
theorem minePadAt_K2 (ms : List Mem) (N : Numbers) (links : List ModelPart) (p : Place)
    (hk : p.kind = .K2) (hl : (rowOf links p).lays = true) :
    minePadAt ms N links p =
      ms.filter fun x => (N.keptOf (p.link.getD links.length - 1)).contains (x.1.seat x.2) := by
  have e : laysPads N links p = N.keptOf (p.link.getD links.length - 1) := by
    unfold laysPads
    rw [hk, hl]
    rfl
  unfold minePadAt
  rw [e]

/-! ## 5 A try, at made-up lists -/

namespace MembersTry

def shA : OracleShape := { code := 0, mainRows := 1 }
def shB : OracleShape := { code := 0, mainRows := 2 }
/-- Two sendings: one member at (0, 0); two at (1, 0) and (1, 1). -/
def L0 : MemberLists := [([(shA, 3)], [(0, 0)]), ([(shB, 5), (shA, 3)], [(1, 0), (1, 1)])]

/-- The test passes at the second sending's own list. -/
theorem passes : sitsB L0 [(1, 0), (1, 1)] [(shB, 5), (shA, 3)] = true := by decide
/-- It fails where the typed list has another radius at a place. -/
theorem fails_entry : sitsB L0 [(1, 0), (1, 1)] [(shB, 5), (shA, 4)] = false := by decide
/-- It fails at a tenant at which no member sits. -/
theorem fails_empty : sitsB L0 [(2, 0)] [(shA, 3)] = false := by decide
theorem once : onceB L0 [(1, 0), (1, 1)] = true := by decide
/-- Two members at one tenant: the second test fails. -/
theorem once_fails : onceB (([(shA, 3)], [(1, 0)]) :: L0) [(1, 0)] = false := by decide

end MembersTry

end VerifiableInference.Desc.Sound

#print axioms VerifiableInference.Desc.Sound.pairs_eq
#print axioms VerifiableInference.Desc.Sound.sits_of_B
#print axioms VerifiableInference.Desc.Sound.alike_of_B
#print axioms VerifiableInference.Desc.Sound.each_of_B
#print axioms VerifiableInference.Desc.Sound.nodup_of_B
#print axioms VerifiableInference.Desc.Sound.mem_filter_of_sits
#print axioms VerifiableInference.Desc.Sound.mineAt_K2
#print axioms VerifiableInference.Desc.Sound.laysTok_K2
#print axioms VerifiableInference.Desc.Sound.minePadAt_K2
#print axioms VerifiableInference.Desc.Sound.MembersTry.passes
#print axioms VerifiableInference.Desc.Sound.MembersTry.fails_entry
#print axioms VerifiableInference.Desc.Sound.MembersTry.once_fails
