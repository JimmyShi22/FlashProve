-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Flat/DryRel.lean: two routines compared in a dry run.

A description of a protocol has one list of rounds for all instances, and the rounds are made by a
dry run of a block that knows the instance. To show that the rounds do not hang on the instance, two
runs are compared: the same text at two instances, from one dry context. This file has the relation
and the laws by which it passes through the ways in which a routine is put together.

The relation. For two blocks (`Blk`, OnBytes/Iop/Ground.lean) and a relation R on values, `relB R b
b'`: from every dry context both fail, or both return, with values in R and THE SAME CONTEXT LEFT.
The channel's notes of the rounds are a part of the context, so the two dry runs then state the same
rounds (`relB_dryRun`). For routines in a state above (`SubM`, `LinkM`) a relation on the states is
chosen: from states in it, the values are in R and the states left are in it again. `Cmp m` holds
such a relation for a monad m with its three laws; `Cmp.blk` is that of blocks, `Cmp.state S c` that
of a state above, under the relation S on states.

What makes it cheap. Where every chosen relation on states is equality (`Cmp.Same`), a routine is
in relation with itself, whatever its text (`Cmp.bind_same`): nothing is asked of it but that it
leaves the two flags of a run as they are (`Over.K`, OnBytes/Flat/LinksKeepsBase.lean).

Main definitions: `All2` (two lists, member by member), `Res`, `relB`, `Cmp`, `Cmp.blk`,
`Cmp.state`, `Cmp.Same`.
Main theorems: `relB_bind`, `same_blk`, `same_state`, `Cmp.bind_same`, `Cmp.map`, `Cmp.lift`,
`Cmp.run`; the calls that a dry run skips (`relB_test`, `relB_check`, `relB_note`, `relB_noteBy`,
`relB_onView`, `relB_getOnView`, `relB_testOnView`, `relB_checkOnView`); `relB_dryRun`.

Not claimed: anything on a run on a view. Two failures are in relation whatever their names. For
proofs only; no module of the program imports this file.


-/
import OnBytes.Flat.LinksKeepsBase

set_option autoImplicit false

namespace OnBytes.Flat

/-! ## Two lists, member by member -/

/-- Two lists have as many members, and these are in the relation R, each with its like. -/
inductive All2 {α β : Type} (R : α → β → Prop) : List α → List β → Prop
  | nil : All2 R [] []
  | cons {a : α} {b : β} {l : List α} {l' : List β} :
    R a b → All2 R l l' → All2 R (a :: l) (b :: l')

theorem All2.length {α β : Type} {R : α → β → Prop} {l : List α} {l' : List β} (h : All2 R l l') :
    l.length = l'.length := by
  induction h with
  | nil => rfl
  | cons _ _ ih => simp [ih]

theorem All2.append {α β : Type} {R : α → β → Prop} {l₁ l₂ : List α} {l₁' l₂' : List β}
    (h₁ : All2 R l₁ l₁') (h₂ : All2 R l₂ l₂') : All2 R (l₁ ++ l₂) (l₁' ++ l₂') := by
  induction h₁ with
  | nil => exact h₂
  | cons h _ ih => exact .cons h ih

theorem All2.refl {α : Type} {R : α → α → Prop} (h : ∀ a, R a a) : ∀ l : List α, All2 R l l
  | [] => .nil
  | a :: l => .cons (h a) (All2.refl h l)

/-- What is read of each member is the same. -/
theorem All2.map_eq {α β γ : Type} {R : α → β → Prop} {f : α → γ} {g : β → γ}
    (h : ∀ a b, R a b → f a = g b) {l : List α} {l' : List β} (hl : All2 R l l') :
    l.map f = l'.map g := by
  induction hl with
  | nil => rfl
  | cons h0 _ ih => simp [h _ _ h0, ih]

/-! ## Two blocks -/

/-- Two results of blocks: both are failures, or both are values in R with one context left. -/
def Res {α : Type} (R : α → α → Prop) :
    Except Failure (α × Ctx) → Except Failure (α × Ctx) → Prop
  | .ok x, .ok x' => R x.1 x'.1 ∧ x.2 = x'.2
  | .error _, .error _ => True
  | _, _ => False

/-- Two blocks: from every dry context their results are so. -/
def relB {α : Type} (R : α → α → Prop) (b b' : Blk α) : Prop :=
  ∀ c, c.Dry → Res R (b c) (b' c)

theorem relB_pure {α : Type} {R : α → α → Prop} {a a' : α} (h : R a a') :
    relB R (pure a) (pure a') := fun _ _ => ⟨h, rfl⟩

theorem relB_bind {α β : Type} {S : α → α → Prop} {R : β → β → Prop} {x x' : Blk α}
    {f f' : α → Blk β} (hk : Blk.Keeps x) (hx : relB S x x')
    (hf : ∀ a a', S a a' → relB R (f a) (f' a')) : relB R (x >>= f) (x' >>= f') := by
  intro c hc
  have h := hx c hc
  cases h1 : x c with
  | error e =>
    cases h2 : x' c with
    | error e' =>
      rw [Blk.bind_error h1, Blk.bind_error h2]
      trivial
    | ok r' =>
      rw [h1, h2] at h
      exact h.elim
  | ok r =>
    cases h2 : x' c with
    | error e' =>
      rw [h1, h2] at h
      exact h.elim
    | ok r' =>
      obtain ⟨a, d⟩ := r
      obtain ⟨a', d'⟩ := r'
      rw [h1, h2] at h
      obtain ⟨ha, hd⟩ := h
      have hd' : d = d' := hd
      subst hd'
      rw [Blk.bind_ok h1, Blk.bind_ok h2]
      have k := hk c a d h1
      exact hf a a' ha d ⟨k.1.trans hc.1, k.2.trans hc.2⟩

theorem relB_mono {α : Type} {R R' : α → α → Prop} {x x' : Blk α}
    (h : ∀ a a', R a a' → R' a a') (hx : relB R x x') : relB R' x x' := by
  intro c hc
  have h0 := hx c hc
  revert h0
  cases x c <;> cases x' c <;> intro h0
  · trivial
  · exact h0.elim
  · exact h0.elim
  · exact ⟨h _ _ h0.1, h0.2⟩

theorem relB_refl {α : Type} (x : Blk α) : relB Eq x x := by
  intro c _
  cases x c
  · trivial
  · exact ⟨rfl, rfl⟩

/-- Two blocks that give the same result at every dry context. -/
theorem relB_of_dryEq {α : Type} {x x' : Blk α} (h : Blk.DryEq x x') : relB Eq x x' := by
  intro c hc
  rw [h c hc]
  exact relB_refl x' c hc

/-! ## A relation for each layer -/

/-- How two routines of the monad m are compared, with the laws of a returned value, of one routine
after another, and of a wider relation on values. -/
structure Cmp (m : Type → Type) [Monad m] [Over m] where
  /-- the relation, at a relation on values -/
  Rel : {α : Type} → (α → α → Prop) → m α → m α → Prop
  pure' : ∀ {α : Type} {R : α → α → Prop} {a a' : α}, R a a' → Rel R (pure a) (pure a')
  bind' : ∀ {α β : Type} {S : α → α → Prop} {R : β → β → Prop} {x x' : m α} {f f' : α → m β},
    Over.K x → Rel S x x' → (∀ a a', S a a' → Rel R (f a) (f' a')) → Rel R (x >>= f) (x' >>= f')
  mono' : ∀ {α : Type} {R R' : α → α → Prop} {x x' : m α},
    (∀ a a', R a a' → R' a a') → Rel R x x' → Rel R' x x'

/-- Blocks. -/
def Cmp.blk : Cmp Blk where
  Rel := relB
  pure' := relB_pure
  bind' := relB_bind
  mono' := relB_mono

/-- A state above, under the relation S on states. -/
def Cmp.state {σ : Type} {m : Type → Type} [Monad m] [Over m] (S : σ → σ → Prop) (c : Cmp m) :
    Cmp (StateT σ m) where
  Rel R x x' := ∀ s s', S s s' → c.Rel (fun p p' => R p.1 p'.1 ∧ S p.2 p'.2) (x s) (x' s')
  pure' h _ _ hs := c.pure' ⟨h, hs⟩
  bind' {_ _ _ _ x x' f f'} hk hx hf s s' hs := by
    show c.Rel _ (x s >>= fun p => f p.1 p.2) (x' s' >>= fun p => f' p.1 p.2)
    exact c.bind' (hk s) (hx s s' hs) fun p p' h => hf p.1 p'.1 h.1 p.2 p'.2 h.2
  mono' h hx s s' hs := c.mono' (fun _ _ k => ⟨h _ _ k.1, k.2⟩) (hx s s' hs)

section laws

variable {m : Type → Type} [Monad m] [Over m] {α β σ : Type}

/-- Every routine is in relation with itself, with equal values. -/
def Cmp.Same (c : Cmp m) : Prop := ∀ {α : Type} (x : m α), c.Rel Eq x x

theorem same_blk : Cmp.blk.Same := fun x => relB_refl x

theorem same_state {c : Cmp m} (h : c.Same) : (Cmp.state (σ := σ) Eq c).Same := by
  intro α x s s' hs
  subst hs
  exact c.mono' (fun p p' e => by subst e; exact ⟨rfl, rfl⟩) (h (x s))

/-- **After one and the same routine**: two continuations, at one value. -/
theorem Cmp.bind_same (c : Cmp m) (hs : c.Same) {R : β → β → Prop} {x : m α} {f f' : α → m β}
    (hk : Over.K x) (hf : ∀ a, c.Rel R (f a) (f' a)) : c.Rel R (x >>= f) (x >>= f') :=
  c.bind' hk (hs x) fun a a' e => by subst e; exact hf a

/-- One and the same routine, at a relation that holds of every value with itself. -/
theorem Cmp.refl (c : Cmp m) (hs : c.Same) {R : α → α → Prop} (hR : ∀ a, R a a) (x : m α) :
    c.Rel R x x := c.mono' (fun a a' e => by subst e; exact hR a) (hs x)

theorem Cmp.map [LawfulMonad m] (c : Cmp m) {S : α → α → Prop} {R : β → β → Prop} {x x' : m α}
    {f f' : α → β} (hk : Over.K x) (hx : c.Rel S x x') (hf : ∀ a a', S a a' → R (f a) (f' a')) :
    c.Rel R (f <$> x) (f' <$> x') := by
  rw [← bind_pure_comp, ← bind_pure_comp]
  exact c.bind' hk hx fun a a' h => c.pure' (hf a a' h)

theorem Cmp.ite (c : Cmp m) {R : α → α → Prop} {p : Prop} [Decidable p] {x x' y y' : m α}
    (hx : c.Rel R x x') (hy : c.Rel R y y') :
    c.Rel R (if p then x else y) (if p then x' else y') := by
  split
  · exact hx
  · exact hy

/-- A routine of the layer below, run in the layer above. -/
theorem Cmp.lift (c : Cmp m) (S : σ → σ → Prop) {R : α → α → Prop} {x x' : m α} (hk : Over.K x)
    (hx : c.Rel R x x') :
    (Cmp.state S c).Rel R (StateT.lift x : StateT σ m α) (StateT.lift x') :=
  fun _ _ hs => c.bind' hk hx fun _ _ h => c.pure' ⟨h, hs⟩

/-- A routine of the layer above, run from two states. -/
theorem Cmp.run (c : Cmp m) (S : σ → σ → Prop) {R : α → α → Prop} {x x' : StateT σ m α}
    (hx : (Cmp.state S c).Rel R x x') {s s' : σ} (hs : S s s') :
    c.Rel (fun p p' => R p.1 p'.1 ∧ S p.2 p'.2) (StateT.run x s) (StateT.run x' s') := hx s s' hs

end laws

/-! ## The calls that a dry run skips -/

theorem relB_test (b b' : Bool) (name : String) : relB Eq (Blk.test b name) (Blk.test b' name) := by
  intro c hc
  unfold Blk.test
  simp only [hc.1, Bool.or_true, if_true]
  exact ⟨rfl, rfl⟩

theorem relB_check (name : String) (b b' : Bool) :
    relB Eq (Blk.check name b) (Blk.check name b') := by
  intro c hc
  unfold Blk.check
  simp only [hc.1, Bool.or_true, Bool.true_or, if_true]
  exact ⟨rfl, rfl⟩

theorem relB_note (w : String) (v v' : E) : relB Eq (Blk.note w v) (Blk.note w v') := by
  intro c hc
  unfold Blk.note
  simp only [hc.2, Bool.false_eq_true, if_false]
  exact ⟨rfl, rfl⟩

theorem relB_noteBy (w : String) (v v' : Unit → E) :
    relB Eq (Blk.noteBy w v) (Blk.noteBy w v') := by
  intro c hc
  unfold Blk.noteBy
  simp only [hc.2, Bool.false_eq_true, if_false]
  exact ⟨rfl, rfl⟩

theorem relB_onView {α : Type} (d : α) (f f' : Unit → α) :
    relB Eq (Blk.onView d f) (Blk.onView d f') := by
  intro c hc
  unfold Blk.onView
  simp only [hc.1, if_true]
  exact ⟨rfl, rfl⟩

theorem relB_getOnView {α : Type} (d : α) (f f' : Unit → Option α) (name : String) :
    relB Eq (Blk.getOnView d f name) (Blk.getOnView d f' name) := by
  intro c hc
  unfold Blk.getOnView
  simp only [hc.1, if_true]
  exact ⟨rfl, rfl⟩

theorem relB_testOnView (f f' : Unit → Bool) (name : String) :
    relB Eq (Blk.testOnView f name) (Blk.testOnView f' name) := by
  intro c hc
  unfold Blk.testOnView
  simp only [hc.1, Bool.true_or, if_true]
  exact ⟨rfl, rfl⟩

theorem relB_checkOnView (name : String) (f f' : Unit → Bool) :
    relB Eq (Blk.checkOnView name f) (Blk.checkOnView name f') := by
  intro c hc
  unfold Blk.checkOnView
  simp only [hc.1, Bool.true_or, if_true]
  exact ⟨rfl, rfl⟩

/-! ## The dry runs -/

/-- **Two blocks in relation have dry runs that both fail, or both return, with the same rounds and
with values in the relation.** -/
theorem relB_dryRun {α : Type} {R : α → α → Prop} {b b' : Blk α} (h : relB R b b') (s : Start) :
    match b.dryRun s, b'.dryRun s with
    | none, none => True
    | some x, some x' => x.1 = x'.1 ∧ R x.2 x'.2
    | _, _ => False := by
  unfold Blk.dryRun Blk.dryRunNamed Blk.runNamed
  by_cases hl : s.st.codes.lengthsOk = true
  · simp only [hl, if_true]
    have h0 := h { ch := { dry := true, entries := s.entries, samples := s.samples,
                           firstTree := s.firstTree, left := [], opened := [] },
                   st := s.st, book := s.book, keepNotes := false } ⟨rfl, rfl⟩
    revert h0
    generalize b _ = r
    generalize b' _ = r'
    intro h0
    cases r with
    | error e =>
      cases r' with
      | error e' => trivial
      | ok x' => exact h0.elim
    | ok x =>
      cases r' with
      | error e' => exact h0.elim
      | ok x' =>
        obtain ⟨a, d⟩ := x
        obtain ⟨a', d'⟩ := x'
        obtain ⟨ha, hd⟩ := h0
        have hd' : d = d' := hd
        subst hd'
        dsimp only
        by_cases hq : (d.ch.entries.isEmpty && d.ch.items.isEmpty && d.ch.settled) = true
        · rw [if_pos hq, if_pos hq]
          exact ⟨rfl, ha⟩
        · rw [if_neg hq, if_neg hq]
          trivial
  · simp only [hl, Bool.false_eq_true, if_false]
    trivial

end OnBytes.Flat
