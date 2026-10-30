-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K12/SeatLaws.lean: the proximity test (the kind K12): what a yes holds at the two ends
that the kind's files' laws on the parts do not reach: THE SEAT at the first chain's finish
(AtFinish.lean), and THE FRONT (Join.lean's frontJ over Johnson/Desc/K12/Front.lean). Theorems; no
code.

  inside_ok · enterFinish_ok · leaveFinish_ok   the door.
  atFinish_ok   **a yes of the test at the first chain's finish gives a yes of the kind's block over
                its own record, at the record that the door lays**, and says what is laid back: so
                a law on the block over its own record is carried to the chain's state.
  step_inside · atFinish_planOk · atFinish_step   THE SAME OF `Block.step`, of which the kind's law
                speaks: the seat's step asks the inner block's own two tests on form, of the same
                rounds and columns.
  refuse_ok · forM_ok · openClaimsE_ok · frontE_ok   the front says yes JUST WHERE every one of its
                named clauses on the schedule holds, the group is there, and every one of the
                clauses on a claim holds of every claim that lies open on the group.
  block_front_holds   the like of the kind's block's own yes (by `k12_ok`).
  frontJ_ok · front_holds   the front's part: nothing has passed yet; all these clauses hold; the
                record is handed on unturned.
  front_group · front_members_there · front_mask_there · front_in_step · front_trees   single
                clauses read off: that the group, its members, the mask's message, their places in
                the book and these places' trees ARE THERE. Nothing holds them against the place's
                numbers.
The names stand in a namespace of their own (Seat), beside the kind's files' laws on the parts.
Nothing on what the clauses mean. Nothing on soundness.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.K12.AtFinish
import Johnson.Desc.K12.FrameLaws

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K12.Seat
open OnBytes OnBytes.Params
open VerifiableInference.Desc VerifiableInference.Desc.K12 VerifiableInference.Desc.Ground
open VerifiableInference.Desc.First (S)

theorem bind_ok {α β : Type} (x : Except String α) (f : α → Except String β) (b : β) :
    (x >>= f) = .ok b ↔ ∃ a, x = .ok a ∧ f a = .ok b := by
  cases x with
  | error e => simp [bind, Except.bind]
  | ok a => simp [bind, Except.bind]

theorem ebind_ok {α β : Type} (x : Except String α) (f : α → Except String β) (b : β) :
    x.bind f = .ok b ↔ ∃ a, x = .ok a ∧ f a = .ok b := by
  cases x with
  | error e => simp [Except.bind]
  | ok a => simp [Except.bind]

theorem need_ok (name : String) (b : Bool) (u : Unit) : need name b = .ok u ↔ b = true := by
  cases b <;> simp [need]

theorem pure_ok {α : Type} (a b : α) : (pure a : Except String α) = .ok b ↔ a = b := by
  simp [pure, Except.pure]

/-- A list of named clauses refuses nothing just where all hold. -/
theorem refuse_ok (l : Clauses) (u : Unit) : Ground.refuse l = .ok u ↔ ∀ c ∈ l, c.2 = true := by
  unfold Ground.refuse
  split
  · rename_i c hc
    have hm := List.mem_of_find?_eq_some hc
    have hf := List.find?_some hc
    constructor
    · intro h; cases h
    · intro h
      have := h c hm
      simp [this] at hf
  · rename_i hn
    simp only [List.find?_eq_none] at hn
    constructor
    · intro _ c hc
      simpa using hn c hc
    · intro _; rfl

/-- A test asked of every member of a list says yes just where it says yes of each. -/
theorem forM_ok {α : Type} (l : List α) (f : α → Except String Unit) :
    l.forM f = .ok () ↔ ∀ a ∈ l, f a = .ok () := by
  induction l with
  | nil => simp [pure, Except.pure]
  | cons a l ih =>
    have e : (a :: l).forM f = (f a >>= fun _ => l.forM f) := rfl
    rw [e, bind_ok]
    simp only [List.mem_cons, forall_eq_or_imp, ih]
    constructor
    · rintro ⟨_, h1, h2⟩
      exact ⟨h1, h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨(), h1, h2⟩

theorem openClaimsE_ok (St : Statement) (g : Nat) :
    openClaimsE St g = .ok () ↔
      ∃ G, St.groups[g]? = some G ∧ ∀ row ∈ G.rows.toList, ∀ c ∈ rowL St g row, c.2 = true := by
  unfold openClaimsE
  split
  · rename_i hn
    simp [hn]
  · rename_i G hG
    simp only [hG, Option.some.injEq, exists_eq_left', forM_ok, refuse_ok]

/-- **The front says yes just where all its clauses hold.** -/
theorem frontE_ok (St : Statement) (B : TreeBook) (g : Nat) (mask : Option Nat) :
    frontE St B g mask = .ok () ↔
      (∀ c ∈ frontL St B g mask, c.2 = true) ∧
        ∃ G, St.groups[g]? = some G ∧
          ∀ row ∈ G.rows.toList, ∀ c ∈ rowL St g row, c.2 = true := by
  simp only [frontE, bind_ok, refuse_ok, openClaimsE_ok]
  constructor
  · rintro ⟨_, h1, h2⟩
    exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨(), h1, h2⟩

theorem frontJ_ok (p : P12) (t t' : T12) (rs : List Fmt.RoundView)
    (gs : List (List (Nat × List UInt64))) (h : (frontJ p).decide t rs gs = .ok t') :
    t.pass = .nothing ∧ frontE t.st t.book t.g t.mask = .ok () ∧ t' = t := by
  simp only [frontJ] at h
  split at h
  · rename_i hp
    simp only [bind_ok, pure_ok] at h
    obtain ⟨_, hf, rfl⟩ := h
    exact ⟨hp, hf, rfl⟩
  · simp [wrongForm] at h

/-- The front's part, with its clauses read off. -/
theorem front_holds (p : P12) (t t' : T12) (rs : List Fmt.RoundView)
    (gs : List (List (Nat × List UInt64))) (h : (frontJ p).decide t rs gs = .ok t') :
    t' = t ∧ t.pass = .nothing ∧ (∀ c ∈ frontL t.st t.book t.g t.mask, c.2 = true) ∧
      ∃ G, t.st.groups[t.g]? = some G ∧
        ∀ row ∈ G.rows.toList, ∀ c ∈ rowL t.st t.g row, c.2 = true := by
  obtain ⟨hp, hf, he⟩ := frontJ_ok p t t' rs gs h
  obtain ⟨h1, h2⟩ := (frontE_ok _ _ _ _).1 hf
  exact ⟨he, hp, h1, h2⟩

/-- A yes of the riding parts' front holds `frontJ`'s own yes at the same record. The riding front
may ask more, in front of it and behind it (in JoinGuarded.lean:
the count of roots; the public test at the record's codes): nothing of that is read off here. The
proof has two arms.
As reported, not shown here, `frontK_ok` says the like, with what the two further tests say. -/
theorem frontP5_ok (p : P12) (t t' : T12) (rs : List Fmt.RoundView)
    (gs : List (List (Nat × List UInt64))) (h : (guardedProximityTestParts.front p).decide t rs gs = .ok t') :
    (frontJ p).decide t rs gs = .ok t' := by
  first
    | exact h
    | (simp only [guardedProximityTestParts, bind_ok, need_ok, pure_ok] at h
       obtain ⟨_, _, t₁, h1, _, _, rfl⟩ := h
       exact h1)

/-- **Of the block's own yes**: where the kind's block says yes, nothing had passed at its front,
and all the front's clauses hold of the record that it was handed. -/
theorem block_front_holds (p : P12) (t t' : T12) (rs : List Fmt.RoundView)
    (gs : List (List (Nat × List UInt64)))
    (h : (proximityTestKind guardedProximityTestParts p : Block T12 Unit).decide t rs gs = .ok t') :
    t.pass = .nothing ∧ (∀ c ∈ frontL t.st t.book t.g t.mask, c.2 = true) ∧
      ∃ G, t.st.groups[t.g]? = some G ∧
        ∀ row ∈ G.rows.toList, ∀ c ∈ rowL t.st t.g row, c.2 = true := by
  obtain ⟨_, _, _, t₀, _, _, _, h0, _⟩ := k12_ok guardedProximityTestParts p t t' rs gs h
  obtain ⟨_, hp, h1, h2⟩ := front_holds p t t₀ [] [] (frontP5_ok p t t₀ [] [] h0)
  exact ⟨hp, h1, h2⟩

/-! ## Single clauses of the front, read off by name

Each from "every clause of the front's list holds" (`frontE_ok`, `front_holds`). THEY SAY THAT A
THING IS THERE; NONE HOLDS A SHAPE, A PLACE OR A TREE AGAINST THE NUMBERS OF THE TEST's PLACE: by
their types the front's two lists are made of the record, the book, the group's number and the
mask's alone: no number of the place goes in. -/

section clauses
variable {St : Statement} {B : TreeBook} {g : Nat} {mask : Option Nat}

/-- The group under test is there. -/
theorem front_group (h : ∀ c ∈ frontL St B g mask, c.2 = true) : ∃ G, St.groups[g]? = some G := by
  have := h ("front: the group is there", (St.groups[g]?).isSome) (by simp [frontL])
  exact Option.isSome_iff_exists.1 this

/-- Every member of the group is a message of the record. -/
theorem front_members_there (h : ∀ c ∈ frontL St B g mask, c.2 = true) {G : Group}
    (hG : St.groups[g]? = some G) : ∀ o ∈ G.members, ∃ y, St.oracles[o]? = some y := by
  have := h ("front: every member is there",
    on (St.groups[g]?) fun G => G.members.all fun o => (St.oracles[o]?).isSome) (by simp [frontL])
  simp only [on, hG, Option.map_some, Option.getD_some, Array.all_eq_true_iff_forall_mem] at this
  exact fun o ho => Option.isSome_iff_exists.1 (this o ho)

/-- The message that holds the first fold's mask, if one is handed in, is one of the record's. -/
theorem front_mask_there (h : ∀ c ∈ frontL St B g mask, c.2 = true) {m : Nat}
    (hm : mask = some m) : ∃ y, St.oracles[m]? = some y := by
  have := h ("front: the mask's message is there",
    mask.isNone || (mask.bind fun m => St.oracles[m]?).isSome) (by simp [frontL])
  subst hm
  simpa [Option.isSome_iff_exists] using this

/-- The record and the book of trees know as many messages. -/
theorem front_in_step (h : ∀ c ∈ frontL St B g mask, c.2 = true) :
    St.oracles.size = B.place.size := by
  have := h ("front: statement and book are in step", St.oracles.size == B.place.size)
    (by simp [frontL])
  simpa using this

/-- Every member, and the mask's message, has a place in the book, and the tree of that place is in
the book. -/
theorem front_trees (h : ∀ c ∈ frontL St B g mask, c.2 = true) {G : Group}
    (hG : St.groups[g]? = some G) :
    ∀ o ∈ G.members.toList ++ mask.toList,
      ∃ p t, B.place[o]? = some p ∧ B.trees[p.1]? = some t := by
  have := h ("front: each tree is in the book",
    on (St.groups[g]?) fun G => (G.members.toList ++ mask.toList).all fun o =>
      ((B.place[o]?).bind fun p => B.trees[p.1]?).isSome) (by simp [frontL])
  simp only [on, hG, Option.map_some, Option.getD_some, List.all_eq_true] at this
  intro o ho
  obtain ⟨t, ht⟩ := Option.isSome_iff_exists.1 (this o ho)
  obtain ⟨p, hp, hpt⟩ := Option.bind_eq_some_iff.1 ht
  exact ⟨p, t, hp, hpt⟩

end clauses

/-- A block whose record is born and dies inside it says yes just where the door lets in, the inner
block says yes, and the way out does. -/
theorem inside_ok {S' T' Cl' : Type} (enter : S' → Except String T') (b : Block T' Cl')
    (leave : S' → T' → Except String S') (s s' : S') (rs : List Fmt.RoundView)
    (gs : List (List (Nat × List UInt64))) :
    (b.inside enter leave).decide s rs gs = .ok s' ↔
      ∃ t t', enter s = .ok t ∧ b.decide t rs gs = .ok t' ∧ leave s t' = .ok s' := by
  simp only [Block.inside, ebind_ok]
  constructor
  · rintro ⟨t, he, t', hb, hl⟩
    exact ⟨t, t', he, hb, hl⟩
  · rintro ⟨t, t', he, hb, hl⟩
    exact ⟨t, he, t', hb, hl⟩

theorem enterFinish_ok (s : S) (t : T12) (h : enterFinish s = .ok t) :
    ∃ o, s.here = .fin o ∧ s.noneWaits = true ∧ s.failed.isNone = true ∧
      t = { st := s.st, book := s.book, roots := s.roots, g := o.fr.group, pass := .nothing
            mask := o.mask } := by
  simp only [enterFinish] at h
  split at h
  · rename_i o ho
    simp only [bind_ok, need_ok, pure_ok] at h
    obtain ⟨_, h1, _, h2, rfl⟩ := h
    exact ⟨o, ho, h1, h2, rfl⟩
  · simp at h

theorem leaveFinish_ok (s s' : S) (t : T12) :
    leaveFinish s t = .ok s' ↔ s' = { s with st := t.st, book := t.book, roots := t.roots } := by
  simp [leaveFinish, eq_comm]

/-- **A yes of the test at the first chain's finish**: the chain stands at its finish, no count of
claims waits, no test is marked; the kind's block says yes from the record that the door lays; and
of the chain's state only the running record, the book and the count of roots turn. -/
theorem atFinish_ok (p : P12) (s s' : S) (rs : List Fmt.RoundView)
    (gs : List (List (Nat × List UInt64))) (h : (atFinish p).decide s rs gs = .ok s') :
    ∃ o t', s.here = .fin o ∧ s.noneWaits = true ∧ s.failed.isNone = true ∧
      (proximityTestKind guardedProximityTestParts p : Block T12 Unit).decide
        { st := s.st, book := s.book, roots := s.roots, g := o.fr.group, pass := .nothing
          mask := o.mask } rs gs = .ok t' ∧
      s' = { s with st := t'.st, book := t'.book, roots := t'.roots } := by
  obtain ⟨t, t', he, hb, hl⟩ := (inside_ok _ _ _ _ _ _ _).1 h
  obtain ⟨o, ho, h1, h2, rfl⟩ := enterFinish_ok s t he
  exact ⟨o, t', ho, h1, h2, hb, (leaveFinish_ok _ _ _).1 hl⟩

/-! ## The same of the block as a step

The kind's law speaks of `Block.step`, which asks the rounds' and the columns' form before the
decision. A block laid by `Block.inside` states the inner block's very rounds: so its step asks the
same two tests, of the same rounds and columns, and takes as many columns. -/

/-- **The step of a block whose record is born and dies inside it** says yes just where the door
lets in, the inner block's STEP says yes on the same rounds and columns, taking as many columns,
and the way out does. -/
theorem step_inside {S' T' Cl' : Type} (firstTree : Nat) (enter : S' → Except String T')
    (b : Block T' Cl') (leave : S' → T' → Except String S') (s s' : S') (rs : List Fmt.RoundView)
    (cols : List OpenedColumn) (k : Nat) :
    (b.inside enter leave).step firstTree s rs cols = .ok (s', k) ↔
      ∃ t t', enter s = .ok t ∧ b.step firstTree t rs cols = .ok (t', k) ∧
        leave s t' = .ok s' := by
  simp only [Block.step, Block.inside, bind_ok, ebind_ok, need_ok, pure_ok, Prod.mk.injEq]
  constructor
  · rintro ⟨_, h1, _, h2, x, ⟨t, he, t', hb, hl⟩, rfl, hk⟩
    exact ⟨t, t', he, ⟨(), h1, (), h2, t', hb, rfl, hk⟩, hl⟩
  · rintro ⟨t, t', he, ⟨_, h1, _, h2, x, hb, rfl, hk⟩, hl⟩
    exact ⟨(), h1, (), h2, s', ⟨t, he, x, hb, hl⟩, rfl, hk⟩

/-- Where the seat's test on the plan says yes, so does the kind's block's. -/
theorem atFinish_planOk (p : P12) (h : (atFinish p).planOk = true) :
    (proximityTestKind guardedProximityTestParts p : Block T12 Unit).planOk = true := by
  simp only [atFinish, Block.inside, Bool.and_eq_true] at h
  exact h.1.1

/-- **A yes of the test's STEP at the first chain's finish** gives a yes of the kind's block's step
over its own record, at the record that the door lays, on the same rounds and columns, taking as
many columns; and says what is laid back. -/
theorem atFinish_step (p : P12) (firstTree : Nat) (s s' : S) (rs : List Fmt.RoundView) (cols : List OpenedColumn)
    (k : Nat) (h : (atFinish p).step firstTree s rs cols = .ok (s', k)) :
    ∃ o t', s.here = .fin o ∧ s.noneWaits = true ∧ s.failed.isNone = true ∧
      (proximityTestKind guardedProximityTestParts p : Block T12 Unit).step firstTree
        { st := s.st, book := s.book, roots := s.roots, g := o.fr.group, pass := .nothing
          mask := o.mask } rs cols = .ok (t', k) ∧
      s' = { s with st := t'.st, book := t'.book, roots := t'.roots } := by
  obtain ⟨t, t', he, hb, hl⟩ := (step_inside _ _ _ _ _ _ _ _ _).1 h
  obtain ⟨o, ho, h1, h2, rfl⟩ := enterFinish_ok s t he
  exact ⟨o, t', ho, h1, h2, hb, (leaveFinish_ok _ _ _).1 hl⟩

end VerifiableInference.Desc.K12.Seat
