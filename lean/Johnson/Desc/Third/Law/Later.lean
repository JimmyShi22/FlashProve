-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Third/Law/Later.lean: relations between two statements, "the second is a later state of
the first", and that four functions of the plain ground keep them. Definitions of Prop and theorems.

Why. A chain's end asks only that every group bears the mark "a test has begun" and that every
sampled message names such a group. That says something of the claims laid earlier only if no block
on the way drops a claim, writes the mark itself, lays something on a group behind its mark, or
writes a group's number into a message's list without making the message a member.

Main names:
  `Later T T'`: the codes are the same; every group of T stands at its number in T' with the same
    codes, no member gone, a mark kept; as long as it bears no mark in T' its open rows are T's, in
    order, with more behind; if it bore the mark in T it has the same members and rows (`frozen`).
    Every message of T stands at its number with the same shape; once sampled it stays so with the
    same sample rows and pad; no group is gone from its list.
  `NoNewMark T T'`: a group that bears the mark in T' stood in T and bore it there.
  `Linked T`: a message that names a group is a member of it.
  `Carries T T'`: Later, NoNewMark, and Linked is kept. Reflexive and transitive.
  `carries_adoptP`, `carries_elsewhereP`, `carries_joinP`, `carries_addRowP`: the four functions
    that K14's second part calls. Three of the proofs read a clause of the function's own test ("not
    sampled here"; "no test has begun", twice).

Whose. The general tool on the plain ground's functions (Grows, NoNewMark, Linked, Frozen in
VerifiableInference.Desc) is in other files. These relations are for the last chain's own blocks;
Later says more than Grows (rows, sample rows, pads).

Limits. Invariants: a block that says yes to all and hands the record on meets them, and so does one
that says no to all. Nothing on what a mark or a row means. Nothing on soundness or on hiding.
-/
import Johnson.Desc.First.Base.Ground

set_option autoImplicit false
set_option relaxedAutoImplicit false

open OnBytes OnBytes.Slice
open Desc.Plain (DState)

namespace VerifiableInference.Desc.Later

/-! ## 1 The relations -/

/-- A group, later. -/
structure GroupLater (G G' : Group) : Prop where
  code : G'.code = G.code
  maskCode : G'.maskCode = G.maskCode
  /-- no member has gone -/
  members : ∀ o, o ∈ G.members → o ∈ G'.members
  /-- a mark stays -/
  mark : G.inRun = true → G'.inRun = true
  /-- as long as there is no mark: the open rows, in order, with more behind -/
  rows : G'.inRun = false → ∃ more : List Row, G'.rows.toList = G.rows.toList ++ more
  /-- behind the mark nothing comes -/
  frozen : G.inRun = true → G'.members = G.members ∧ G'.rows = G.rows

/-- An oracle message, later. -/
structure OracleLater (x x' : Oracle) : Prop where
  shape : x'.shape = x.shape
  /-- once sampled: it stays so, with the same sample rows and pad -/
  sampled : x.sampled = true → x'.sampled = true ∧ x'.sampleRows = x.sampleRows ∧ x'.pad = x.pad
  /-- no group has gone from its list -/
  groups : ∀ g, g ∈ x.groups → g ∈ x'.groups
  spent : x.spentAsMask = true → x'.spentAsMask = true

/-- **A statement, later.** -/
structure Later (T T' : Statement) : Prop where
  codes : T'.codes = T.codes
  groups : ∀ (i : Nat) (G : Group), T.groups[i]? = some G →
    ∃ G', T'.groups[i]? = some G' ∧ GroupLater G G'
  oracles : ∀ (i : Nat) (x : Oracle), T.oracles[i]? = some x →
    ∃ x', T'.oracles[i]? = some x' ∧ OracleLater x x'

/-- **No mark has been written.** -/
def NoNewMark (T T' : Statement) : Prop :=
  ∀ (i : Nat) (G' : Group), T'.groups[i]? = some G' → G'.inRun = true →
    ∃ G, T.groups[i]? = some G ∧ G.inRun = true

/-- Both. -/
def Lays (T T' : Statement) : Prop := Later T T' ∧ NoNewMark T T'

/-- **A message that names a group is a member of it.** -/
def Linked (T : Statement) : Prop :=
  ∀ (o : Nat) (x : Oracle) (g : Nat), T.oracles[o]? = some x → g ∈ x.groups →
    ∃ G, T.groups[g]? = some G ∧ o ∈ G.members

/-- Lays, and Linked is kept. -/
def Carries (T T' : Statement) : Prop := Lays T T' ∧ (Linked T → Linked T')

theorem GroupLater.refl (G : Group) : GroupLater G G :=
  ⟨rfl, rfl, fun _ h => h, fun h => h, fun _ => ⟨[], (List.append_nil _).symm⟩, fun _ => ⟨rfl, rfl⟩⟩

theorem GroupLater.trans {A B C : Group} (h1 : GroupLater A B) (h2 : GroupLater B C) :
    GroupLater A C :=
  ⟨h2.code.trans h1.code, h2.maskCode.trans h1.maskCode, fun o h => h2.members o (h1.members o h),
    fun h => h2.mark (h1.mark h), fun hC => by
      have hB : B.inRun = false := by
        cases hb : B.inRun with
        | false => rfl
        | true =>
          have t := h2.mark hb
          rw [hC] at t
          cases t
      obtain ⟨m1, e1⟩ := h1.rows hB
      obtain ⟨m2, e2⟩ := h2.rows hC
      exact ⟨m1 ++ m2, by rw [e2, e1, List.append_assoc]⟩,
    fun hA => by
      obtain ⟨a1, a2⟩ := h1.frozen hA
      obtain ⟨b1, b2⟩ := h2.frozen (h1.mark hA)
      exact ⟨b1.trans a1, b2.trans a2⟩⟩

theorem OracleLater.refl (x : Oracle) : OracleLater x x :=
  ⟨rfl, fun h => ⟨h, rfl, rfl⟩, fun _ h => h, fun h => h⟩

theorem OracleLater.trans {x y z : Oracle} (h1 : OracleLater x y) (h2 : OracleLater y z) :
    OracleLater x z :=
  ⟨h2.shape.trans h1.shape, fun h => by
      obtain ⟨a1, a2, a3⟩ := h1.sampled h
      obtain ⟨b1, b2, b3⟩ := h2.sampled a1
      exact ⟨b1, b2.trans a2, b3.trans a3⟩,
    fun g h => h2.groups g (h1.groups g h), fun h => h2.spent (h1.spent h)⟩

theorem Later.refl (T : Statement) : Later T T :=
  ⟨rfl, fun _ G h => ⟨G, h, GroupLater.refl G⟩, fun _ x h => ⟨x, h, OracleLater.refl x⟩⟩

theorem Later.trans {A B C : Statement} (h1 : Later A B) (h2 : Later B C) : Later A C :=
  ⟨h2.codes.trans h1.codes, fun i G h => by
      obtain ⟨G1, g1, e1⟩ := h1.groups i G h
      obtain ⟨G2, g2, e2⟩ := h2.groups i G1 g1
      exact ⟨G2, g2, e1.trans e2⟩,
    fun i x h => by
      obtain ⟨x1, g1, e1⟩ := h1.oracles i x h
      obtain ⟨x2, g2, e2⟩ := h2.oracles i x1 g1
      exact ⟨x2, g2, e1.trans e2⟩⟩

theorem NoNewMark.refl (T : Statement) : NoNewMark T T := fun _ G' h hm => ⟨G', h, hm⟩

theorem NoNewMark.trans {A B C : Statement} (h1 : NoNewMark A B) (h2 : NoNewMark B C) :
    NoNewMark A C := fun i G' h hm => by
  obtain ⟨G1, g1, m1⟩ := h2 i G' h hm
  exact h1 i G1 g1 m1

theorem Lays.refl (T : Statement) : Lays T T := ⟨Later.refl T, NoNewMark.refl T⟩

theorem Lays.trans {A B C : Statement} (h1 : Lays A B) (h2 : Lays B C) : Lays A C :=
  ⟨h1.1.trans h2.1, h1.2.trans h2.2⟩

theorem Carries.refl (T : Statement) : Carries T T := ⟨Lays.refl T, fun h => h⟩

theorem Carries.trans {A B C : Statement} (h1 : Carries A B) (h2 : Carries B C) : Carries A C :=
  ⟨h1.1.trans h2.1, fun h => h2.2 (h1.2 h)⟩

/-! ## 2 Changes of a statement -/

/-- One oracle message is changed, to a later one. -/
theorem lays_modifyOracle (T : Statement) (o : Nat) (f : Oracle → Oracle)
    (hf : ∀ x, T.oracles[o]? = some x → OracleLater x (f x)) :
    Lays T { T with oracles := T.oracles.modify o f } :=
  ⟨⟨rfl, fun _ G h => ⟨G, h, GroupLater.refl G⟩, fun i x h => by
      by_cases e : o = i
      · subst e
        exact ⟨f x, by simp [Array.getElem?_modify, h], hf x h⟩
      · exact ⟨x, by simp [Array.getElem?_modify, e, h], OracleLater.refl x⟩⟩,
    fun _ G' h hm => ⟨G', h, hm⟩⟩

/-- One group is changed, to a later one with the same mark. -/
theorem lays_modifyGroup (T : Statement) (g : Nat) (f : Group → Group)
    (hf : ∀ G, T.groups[g]? = some G → GroupLater G (f G)) (hm : ∀ G, (f G).inRun = G.inRun) :
    Lays T { T with groups := T.groups.modify g f } :=
  ⟨⟨rfl, fun i G h => by
      by_cases e : g = i
      · subst e
        exact ⟨f G, by simp [Array.getElem?_modify, h], hf G h⟩
      · exact ⟨G, by simp [Array.getElem?_modify, e, h], GroupLater.refl G⟩,
    fun _ x h => ⟨x, h, OracleLater.refl x⟩⟩,
    fun i G' h hr => by
      have h' : (T.groups.modify g f)[i]? = some G' := h
      rw [Array.getElem?_modify] at h'
      by_cases e : g = i
      · rw [if_pos e] at h'
        cases hx : T.groups[i]? with
        | none =>
          rw [hx] at h'
          cases h'
        | some G =>
          rw [hx] at h'
          have e' : f G = G' := Option.some.inj h'
          refine ⟨G, rfl, ?_⟩
          rw [← hm G, e']
          exact hr
      · rw [if_neg e] at h'
        exact ⟨G', h', hr⟩⟩

/-- New oracle messages at the end. -/
theorem lays_stSent (T : Statement) (sent : Array OracleNotice) : Lays T (stSent T sent) :=
  ⟨⟨rfl, fun _ G h => ⟨G, h, GroupLater.refl G⟩, fun _ x h =>
      ⟨x, (Array.getElem?_append_left (Array.getElem?_eq_some_iff.1 h).1).trans h,
        OracleLater.refl x⟩⟩,
    fun _ G' h hm => ⟨G', h, hm⟩⟩

/-- What was in an array is in it behind an insertion. -/
theorem mem_insertIdxIfInBounds {α : Type} (xs : Array α) (k : Nat) (a b : α) (h : b ∈ xs) :
    b ∈ xs.insertIdxIfInBounds k a := by
  unfold Array.insertIdxIfInBounds
  split
  · exact Array.mem_insertIdx.2 (Or.inr h)
  · exact h

/-- What is inserted within the bounds is in the array. -/
theorem self_mem_insertIdxIfInBounds {α : Type} (xs : Array α) (k : Nat) (a : α)
    (hk : k ≤ xs.size) : a ∈ xs.insertIdxIfInBounds k a := by
  unfold Array.insertIdxIfInBounds
  split
  · exact Array.mem_insertIdx.2 (Or.inl rfl)
  · rename_i hn
    exact absurd hk hn

theorem size_filter_le' {α : Type} (xs : Array α) (p : α → Bool) :
    (xs.filter p).size ≤ xs.size := by
  first
    | exact Array.size_filter_le
    | exact Array.size_filter_le _ _
    | simp [Array.size_filter_le]
    | grind

/-- An entry of an array of which one entry is changed: it is what stood there, or that changed. -/
theorem of_modify {α : Type} (xs : Array α) (k : Nat) (f : α → α) (i : Nat) (a' : α)
    (h : (xs.modify k f)[i]? = some a') :
    ∃ a, xs[i]? = some a ∧ ((k = i ∧ a' = f a) ∨ (k ≠ i ∧ a' = a)) := by
  rw [Array.getElem?_modify] at h
  by_cases e : k = i
  · rw [if_pos e] at h
    cases hx : xs[i]? with
    | none =>
      rw [hx] at h
      cases h
    | some a =>
      rw [hx] at h
      exact ⟨a, rfl, Or.inl ⟨e, (Option.some.inj h).symm⟩⟩
  · rw [if_neg e] at h
    exact ⟨a', h, Or.inr ⟨e, rfl⟩⟩

/-! ### Linked -/

/-- One group is changed and loses no member: Linked stays. -/
theorem linked_modifyGroup (T : Statement) (k : Nat) (f : Group → Group)
    (hf : ∀ (G : Group) (a : Nat), a ∈ G.members → a ∈ (f G).members) (h : Linked T) :
    Linked { T with groups := T.groups.modify k f } := by
  intro o x g hx hg
  obtain ⟨G, hG, ho⟩ := h o x g hx hg
  by_cases e : k = g
  · subst e
    exact ⟨f G, by simp [Array.getElem?_modify, hG], hf G o ho⟩
  · exact ⟨G, by simp [Array.getElem?_modify, e, hG], ho⟩

/-- One message is changed and keeps its list of groups: Linked stays. -/
theorem linked_modifyOracle (T : Statement) (k : Nat) (f : Oracle → Oracle)
    (hf : ∀ x : Oracle, (f x).groups = x.groups) (h : Linked T) :
    Linked { T with oracles := T.oracles.modify k f } := by
  intro o x' g hx hg
  obtain ⟨x, hx0, hc⟩ := of_modify T.oracles k f o x' hx
  rcases hc with ⟨_, e⟩ | ⟨_, e⟩
  · rw [e, hf x] at hg
    exact h o x g hx0 hg
  · rw [e] at hg
    exact h o x g hx0 hg

/-- A message notes a group of which it is a member: Linked stays. -/
theorem linked_noted (T : Statement) (o g : Nat) (h : Linked T)
    (hn : ∃ G, T.groups[g]? = some G ∧ o ∈ G.members) :
    Linked { T with
      oracles := T.oracles.modify o fun x => { x with groups := x.groups ++ [g] } } := by
  intro i x' g' hx hg
  obtain ⟨x, hx0, hc⟩ := of_modify T.oracles o _ i x' hx
  rcases hc with ⟨ei, e⟩ | ⟨_, e⟩
  · rw [e] at hg
    have hg' : g' ∈ x.groups ++ [g] := hg
    rcases List.mem_append.1 hg' with hq | hq
    · exact h i x g' hx0 hq
    · have eg : g' = g := by
        rcases List.mem_cons.1 hq with hq | hq
        · exact hq
        · cases hq
      rw [eg, ← ei]
      exact hn
  · rw [e] at hg
    exact h i x g' hx0 hg

/-- New messages come with an empty list: Linked stays. -/
theorem linked_stSent (T : Statement) (sent : Array OracleNotice) (h : Linked T) :
    Linked (stSent T sent) := by
  intro o x g hx hg
  have hx' : (T.oracles ++ sent.map fun n => ({ shape := n.shape } : Oracle))[o]? = some x := hx
  by_cases ho : o < T.oracles.size
  · rw [Array.getElem?_append_left ho] at hx'
    exact h o x g hx' hg
  · rw [Array.getElem?_append_right (Nat.le_of_not_lt ho), Array.getElem?_map] at hx'
    cases hs : sent[o - T.oracles.size]? with
    | none =>
      rw [hs] at hx'
      cases hx'
    | some n =>
      rw [hs] at hx'
      have e : ({ shape := n.shape } : Oracle) = x := Option.some.inj hx'
      rw [← e] at hg
      have hg' : g ∈ ([] : List Nat) := hg
      cases hg'

/-! ### The changes that K14's second part makes -/

theorem carries_stSent (T : Statement) (sent : Array OracleNotice) : Carries T (stSent T sent) :=
  ⟨lays_stSent T sent, linked_stSent T sent⟩

/-- What withMessageInGroup does to the group: G: the group in front. -/
abbrev joinG (G : Group) (o : Nat) (kept : Bool) : Group → Group := fun G' => { G' with
  members := G'.members.insertIdxIfInBounds (G.members.filter (· < o)).size o
  kept := G'.kept.insertIdxIfInBounds (G.members.filter (· < o)).size kept }

/-- An oracle message joins a group THAT IS THERE AND BEARS NO MARK. -/
theorem carries_joined (T : Statement) (g o : Nat) (kept : Bool) (G : Group)
    (hG : T.groups[g]? = some G) (hr : G.inRun = false) : Carries T (withMessageInGroup T g o kept G) := by
  have hl1 : Lays T { T with groups := T.groups.modify g (joinG G o kept) } :=
    lays_modifyGroup T g (joinG G o kept)
      (fun G' hG' => by
        have e : G = G' := Option.some.inj (hG.symm.trans hG')
        subst e
        exact ⟨rfl, rfl, fun a h => mem_insertIdxIfInBounds _ _ _ _ h, fun h => h,
          fun _ => ⟨[], (List.append_nil _).symm⟩,
          fun h => (by rw [hr] at h; cases h)⟩)
      (fun _ => rfl)
  have hl2 := lays_modifyOracle { T with groups := T.groups.modify g (joinG G o kept) } o
    (fun x => { x with groups := x.groups ++ [g] })
    (fun x _ => ⟨rfl, fun h => ⟨h, rfl, rfl⟩, fun _ h => List.mem_append_left _ h, fun h => h⟩)
  refine ⟨hl1.trans hl2, fun h => ?_⟩
  have hk : Linked { T with groups := T.groups.modify g (joinG G o kept) } :=
    linked_modifyGroup T g (joinG G o kept)
      (fun G' a ha => mem_insertIdxIfInBounds _ _ _ _ ha) h
  exact linked_noted { T with groups := T.groups.modify g (joinG G o kept) } o g hk
    ⟨joinG G o kept G, by simp [Array.getElem?_modify, hG],
      self_mem_insertIdxIfInBounds _ _ _ (size_filter_le' _ _)⟩

/-- One more open row, ON A GROUP THAT BEARS NO MARK. -/
theorem carries_withRow (T : Statement) (g : Nat) (row : Row)
    (hr : ∀ G : Group, T.groups[g]? = some G → G.inRun = false) : Carries T (withRow T g row) :=
  ⟨lays_modifyGroup T g (fun G => { G with rows := G.rows.push row })
      (fun G hG => ⟨rfl, rfl, fun _ h => h, fun h => h, fun _ => ⟨[row], by first | simp | rfl⟩,
        fun h => (by rw [hr G hG] at h; cases h)⟩) (fun _ => rfl),
    linked_modifyGroup T g _ (fun _ _ ha => ha)⟩

/-! ## 3 The plain ground's four functions that K14's second part calls -/

open VerifiableInference.Desc.Ground (adoptP adoptL elsewhereP elsewhereL joinP joinL addRowP rowL)

variable {L : Type}

/-- All clauses of a test that passes hold. -/
theorem ok_mem {l : Ground.Clauses} (h : Ground.ok l = true) : ∀ c ∈ l, c.2 = true := by
  unfold Ground.ok at h
  exact fun c hc => List.all_eq_true.1 h c hc

theorem false_of_not {b : Bool} (h : (!b) = true) : b = false := by
  cases b with
  | false => rfl
  | true => cases h

/-- adoptP's yes: the statement has the new messages at its end; their numbers are the next ones. -/
theorem adoptP_inv (d : DState L) (sent : Array OracleNotice) (given : Array (Nat × Fmt.Src))
    (a : Array Nat × DState L) (h : adoptP d sent given = some a) :
    a.2.st = stSent d.st sent ∧ a.1 = (Array.range sent.size).map (· + d.st.oracles.size) := by
  unfold adoptP at h
  split at h
  · obtain ⟨lay, -, e⟩ := Option.map_eq_some_iff.1 h
    subst e
    exact ⟨rfl, rfl⟩
  · cases h

/-- elsewhereP's yes: the message there; the change here; the test has passed. -/
theorem elsewhereP_inv (d d' : DState L) (mine : Nat) (other : Statement) (theirs : Nat)
    (h : elsewhereP d mine other theirs = some d') :
    ∃ y, other.oracles[theirs]? = some y ∧
      d'.st = { d.st with oracles := d.st.oracles.modify mine fun x =>
        { x with sampled := true, sampleRows := y.sampleRows.map (·.renamed mine),
                 pad := y.pad } } ∧
      Ground.ok (elsewhereL d.st mine other theirs) = true := by
  unfold elsewhereP at h
  split at h
  · rename_i hok
    cases hy : other.oracles[theirs]? with
    | none =>
      rw [hy] at h
      cases h
    | some y =>
      rw [hy] at h
      have e := Option.some.inj h
      subst e
      exact ⟨y, rfl, rfl, hok⟩
  · cases h

/-- joinP's yes: the group in front, WHICH BEARS NO MARK; the change. -/
theorem joinP_inv (d d' : DState L) (g o : Nat) (kept : Bool) (h : joinP d g o kept = some d') :
    ∃ G, d.st.groups[g]? = some G ∧ G.inRun = false ∧ d'.st = withMessageInGroup d.st g o kept G := by
  unfold joinP at h
  split at h
  · rename_i hok
    cases hG : d.st.groups[g]? with
    | none =>
      rw [hG] at h
      cases h
    | some G =>
      rw [hG] at h
      have e := Option.some.inj h
      subst e
      have t := ok_mem hok _
        (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))
      rw [hG] at t
      have t' : (!G.inRun) = true := t
      exact ⟨G, rfl, false_of_not t', rfl⟩
  · cases h

/-- addRowP's yes: the group, if it is there, BEARS NO MARK; the row is no sample row; the change.
-/
theorem addRowP_inv (d d' : DState L) (g : Nat) (row : Row) (h : addRowP d g row = some d') :
    (∀ G : Group, d.st.groups[g]? = some G → G.inRun = false) ∧ (row.kind != .sample) = true ∧
      d'.st = withRow d.st g row := by
  unfold addRowP at h
  split at h
  · rename_i hok
    have e := Option.some.inj h
    subst e
    refine ⟨fun G hG => ?_, ok_mem hok _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))), rfl⟩
    have t := ok_mem hok _ (List.Mem.tail _ (List.Mem.head _))
    rw [hG] at t
    have t' : (!G.inRun) = true := t
    exact false_of_not t'
  · cases h

theorem carries_adoptP (d : DState L) (sent : Array OracleNotice) (given : Array (Nat × Fmt.Src))
    (a : Array Nat × DState L) (h : adoptP d sent given = some a) : Carries d.st a.2.st := by
  rw [(adoptP_inv d sent given a h).1]
  exact carries_stSent d.st sent

/-- The message that is marked as sampled elsewhere WAS NOT SAMPLED HERE: so no sample row is
overwritten. -/
theorem carries_elsewhereP (d d' : DState L) (mine : Nat) (other : Statement) (theirs : Nat)
    (h : elsewhereP d mine other theirs = some d') : Carries d.st d'.st := by
  obtain ⟨y, _, e, hok⟩ := elsewhereP_inv d d' mine other theirs h
  rw [e]
  refine ⟨lays_modifyOracle d.st mine _ ?_, linked_modifyOracle d.st mine _ (fun _ => rfl)⟩
  intro x hx
  have t := ok_mem hok _
    (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))
  rw [hx] at t
  have t' : (!x.sampled) = true := t
  have hs : x.sampled = false := false_of_not t'
  exact ⟨rfl, fun hq => (by rw [hs] at hq; cases hq), fun _ hg => hg, fun hq => hq⟩

theorem carries_joinP (d d' : DState L) (g o : Nat) (kept : Bool) (h : joinP d g o kept = some d') :
    Carries d.st d'.st := by
  obtain ⟨G, hG, hr, e⟩ := joinP_inv d d' g o kept h
  rw [e]
  exact carries_joined d.st g o kept G hG hr

theorem carries_addRowP (d d' : DState L) (g : Nat) (row : Row) (h : addRowP d g row = some d') :
    Carries d.st d'.st := by
  obtain ⟨hr, _, e⟩ := addRowP_inv d d' g row h
  rw [e]
  exact carries_withRow d.st g row hr

end VerifiableInference.Desc.Later

#print axioms VerifiableInference.Desc.Later.Carries.trans
#print axioms VerifiableInference.Desc.Later.carries_adoptP
#print axioms VerifiableInference.Desc.Later.carries_elsewhereP
#print axioms VerifiableInference.Desc.Later.carries_joinP
#print axioms VerifiableInference.Desc.Later.carries_addRowP
