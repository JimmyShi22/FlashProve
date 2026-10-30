-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Ends/FoChan.lean.
Three words on what a block of the byte-level verifier does to the channel's two marks, with their
rules and the ground's blocks.

A run of the byte-level verifier keeps, in the channel's state, whether the run is the dry one
(`dry`) and which message of the prover is open (`cur`). A run that is not the dry one is on a view.
A context on a view with no message open is `Clean` (PscView.lean).

 * `Dry b`: a run of b on a view that returns is still on the view.
 * `Calm b`: it leaves `dry` and `cur` as they were.
 * `Shut b`: from a context on a view it leaves a context on a view with no message open.
 * The rules: `pure`, `bind`, a loop over a list, a loop over an array; a block that is `Dry` and
   then one that is `Shut`; a block that is `Shut` and then one that is `Calm`.
 * The ground's blocks (OnBytes/Iop/Ground.lean), each by its body: those that read or turn the
   statement, the book, the notes, the count of roots or the openings are `Calm`; `Blk.item`, which
   receives an item, is `Dry`; `Blk.close` is `Shut`, and so `Dry`. The blocks made of these two
   stand in OnBytes/Tie/Pv/Lookup/Ends/FoShut.lean.
All three words speak of runs that return alone: a block that never returns has all three.

Not claimed: anything on soundness, completeness or hiding.

-/
import OnBytes.Tie.Pv.Psc.PscView
import OnBytes.Iop.Ground

set_option autoImplicit false

namespace Fo
open OnBytes OnBytes.PscRun

section
variable {α β σ : Type}

/-- A run on a view that returns is still on the view. -/
structure Dry (b : Blk α) : Prop where
  out : ∀ c a c', b c = .ok (a, c') → c.ch.dry = false → c'.ch.dry = false

/-- A run that returns leaves the mark of the dry run and the open message as they were. -/
structure Calm (b : Blk α) : Prop where
  out : ∀ c a c', b c = .ok (a, c') → c'.ch.dry = c.ch.dry ∧ c'.ch.cur = c.ch.cur

/-- A run on a view that returns leaves no message open. -/
structure Shut (b : Blk α) : Prop where
  out : ∀ c a c', b c = .ok (a, c') → c.ch.dry = false → Clean c'

theorem Calm.dry {b : Blk α} (h : Calm b) : Dry b :=
  ⟨fun c a c' e hd => (h.out c a c' e).1.trans hd⟩

theorem Shut.dry {b : Blk α} (h : Shut b) : Dry b := ⟨fun c a c' e hd => (h.out c a c' e hd).1⟩

theorem Calm.pure (a : α) : Calm (pure a : Blk α) := ⟨fun c x c' h => by
  obtain ⟨_, rfl⟩ := Prod.mk.inj ((pureB_ok a c (x, c')).1 h)
  exact ⟨rfl, rfl⟩⟩

theorem Dry.pure (a : α) : Dry (pure a : Blk α) := (Calm.pure a).dry

theorem Calm.bind {x : Blk α} {f : α → Blk β} (hx : Calm x) (hf : ∀ a, Calm (f a)) :
    Calm (x >>= f) := ⟨fun c b c' h => by
  obtain ⟨a, c1, h1, h2⟩ := (bindB_ok x f c (b, c')).1 h
  exact ⟨((hf a).out c1 b c' h2).1.trans (hx.out c a c1 h1).1,
    ((hf a).out c1 b c' h2).2.trans (hx.out c a c1 h1).2⟩⟩

theorem Dry.bind {x : Blk α} {f : α → Blk β} (hx : Dry x) (hf : ∀ a, Dry (f a)) :
    Dry (x >>= f) := ⟨fun c b c' h hd => by
  obtain ⟨a, c1, h1, h2⟩ := (bindB_ok x f c (b, c')).1 h
  exact (hf a).out c1 b c' h2 (hx.out c a c1 h1 hd)⟩

/-- First a block that keeps the run on its view, then one that leaves no message open. -/
theorem Shut.after {x : Blk α} {f : α → Blk β} (hx : Dry x) (hf : ∀ a, Shut (f a)) :
    Shut (x >>= f) := ⟨fun c b c' h hd => by
  obtain ⟨a, c1, h1, h2⟩ := (bindB_ok x f c (b, c')).1 h
  exact (hf a).out c1 b c' h2 (hx.out c a c1 h1 hd)⟩

/-- First a block that leaves no message open, then one that leaves the marks alone. -/
theorem Shut.before {x : Blk α} {f : α → Blk β} (hx : Shut x) (hf : ∀ a, Calm (f a)) :
    Shut (x >>= f) := ⟨fun c b c' h hd => by
  obtain ⟨a, c1, h1, h2⟩ := (bindB_ok x f c (b, c')).1 h
  obtain ⟨e1, e2⟩ := (hf a).out c1 b c' h2
  obtain ⟨k1, k2⟩ := hx.out c a c1 h1 hd
  exact ⟨e1.trans k1, e2.trans k2⟩⟩

/-- From a clean context a calm block leaves a clean one. -/
theorem Calm.clean {b : Blk α} (h : Calm b) {c c' : Ctx} {a : α} (e : b c = .ok (a, c'))
    (hc : Clean c) : Clean c' :=
  ⟨(h.out c a c' e).1.trans hc.1, (h.out c a c' e).2.trans hc.2⟩

theorem Calm.loop (f : β → σ → Blk (ForInStep σ)) (hf : ∀ a s, Calm (f a s)) :
    ∀ (l : List β) (s : σ), Calm (forIn l s f)
  | [], s => by
    rw [List.forIn_nil]
    exact Calm.pure s
  | a :: l, s => by
    rw [List.forIn_cons]
    refine Calm.bind (hf a s) fun r => ?_
    cases r with
    | done t => exact Calm.pure t
    | yield t => exact Calm.loop f hf l t

theorem Dry.loop (f : β → σ → Blk (ForInStep σ)) (hf : ∀ a s, Dry (f a s)) :
    ∀ (l : List β) (s : σ), Dry (forIn l s f)
  | [], s => by
    rw [List.forIn_nil]
    exact Dry.pure s
  | a :: l, s => by
    rw [List.forIn_cons]
    refine Dry.bind (hf a s) fun r => ?_
    cases r with
    | done t => exact Dry.pure t
    | yield t => exact Dry.loop f hf l t

theorem Calm.loopA (f : β → σ → Blk (ForInStep σ)) (hf : ∀ a s, Calm (f a s)) (l : Array β)
    (s : σ) : Calm (forIn l s f) := by
  rw [← Array.forIn_toList]
  exact Calm.loop f hf _ s

theorem Dry.loopA (f : β → σ → Blk (ForInStep σ)) (hf : ∀ a s, Dry (f a s)) (l : Array β)
    (s : σ) : Dry (forIn l s f) := by
  rw [← Array.forIn_toList]
  exact Dry.loop f hf _ s

theorem Calm.forM (f : β → Blk PUnit) (hf : ∀ a, Calm (f a)) : ∀ l : List β, Calm (l.forM f)
  | [] => Calm.pure _
  | a :: l => Calm.bind (hf a) fun _ => Calm.forM f hf l

end

/-! ### the ground's blocks -/
section
variable {α : Type}

/-- For a block written as a function of the context that hands the channel's state on. -/
macro "calm_body" : tactic =>
  `(tactic| (refine ⟨?_⟩; intro c a c' h; try dsimp only at h
             (repeat' split at h) <;> cases h <;> exact ⟨rfl, rfl⟩))

theorem calm_fail (name : String) : Calm (Blk.fail name : Blk α) := by
  refine ⟨?_⟩
  intro c a c' h
  cases h
theorem calm_must (b : Bool) (name : String) : Calm (Blk.must b name) := by
  unfold Blk.must; calm_body
theorem calm_test (b : Bool) (name : String) : Calm (Blk.test b name) := by
  unfold Blk.test; calm_body
theorem calm_check (name : String) (b : Bool) : Calm (Blk.check name b) := by
  unfold Blk.check; calm_body
theorem calm_onView (d : α) (f : Unit → α) : Calm (Blk.onView d f) := by
  unfold Blk.onView; calm_body
theorem calm_getOnView (d : α) (f : Unit → Option α) (name : String) :
    Calm (Blk.getOnView d f name) := by
  unfold Blk.getOnView; calm_body
theorem calm_testOnView (f : Unit → Bool) (name : String) : Calm (Blk.testOnView f name) := by
  unfold Blk.testOnView; calm_body
theorem calm_checkOnView (name : String) (f : Unit → Bool) : Calm (Blk.checkOnView name f) := by
  unfold Blk.checkOnView; calm_body
theorem calm_get (x : Option α) (name : String) : Calm (Blk.get x name) := by
  unfold Blk.get; calm_body
theorem calm_isDry : Calm Blk.isDry := by unfold Blk.isDry; calm_body
theorem calm_samples : Calm Blk.samples := by unfold Blk.samples; calm_body
theorem calm_firstTree : Calm Blk.firstTree := by unfold Blk.firstTree; calm_body
theorem calm_lastEntry : Calm Blk.lastEntry := by unfold Blk.lastEntry; calm_body
theorem calm_statement : Calm Blk.statement := by unfold Blk.statement; calm_body
theorem calm_setStatement (S : Statement) : Calm (Blk.setStatement S) := by
  unfold Blk.setStatement; calm_body
theorem calm_theBook : Calm Blk.theBook := by unfold Blk.theBook; calm_body
theorem calm_setBook (B : TreeBook) : Calm (Blk.setBook B) := by unfold Blk.setBook; calm_body
theorem calm_onOracle (o : Nat) (f : Oracle → Oracle) : Calm (Blk.onOracle o f) := by
  unfold Blk.onOracle; calm_body
theorem calm_onGroup (g : Nat) (f : Group → Group) : Calm (Blk.onGroup g f) := by
  unfold Blk.onGroup; calm_body
theorem calm_requireRows (rows : Nat) : Calm (Blk.requireRows rows) := by
  unfold Blk.requireRows; calm_body
theorem calm_takeColumns (t : Tree) (xs : Array Nat) : Calm (Blk.takeColumns t xs) := by
  unfold Blk.takeColumns; calm_body

theorem calm_note (what : String) (v : E) : Calm (Blk.note what v) := by
  refine ⟨?_⟩
  intro c a c' h
  unfold Blk.note at h
  cases h
  constructor <;> split <;> rfl
theorem calm_noteBy (what : String) (v : Unit → E) : Calm (Blk.noteBy what v) := by
  refine ⟨?_⟩
  intro c a c' h
  unfold Blk.noteBy at h
  cases h
  constructor <;> split <;> rfl
theorem calm_recvRoot : Calm Blk.recvRoot := by
  refine ⟨?_⟩
  intro c a c' h
  unfold Blk.recvRoot at h
  cases h
  constructor <;> (dsimp only; split <;> rfl)

theorem dry_item (i : Fmt.Item) (d : Fmt.ItemValue) : Dry (Blk.item i d) := ⟨fun c a c' h hd => by
        obtain ⟨_, _, _, _, _, e, _⟩ := item_view i d a c c' hd h
        exact e⟩

theorem shut_close (name : String) (kind : Fmt.Kind) (nz : Nat) :
    Shut (Blk.close name kind nz) := ⟨fun c a c' h hd => by
  obtain ⟨_, _, _, _, _, _, _, _, e, _⟩ := close_view name kind nz a c c' hd h
  exact e⟩

end
end Fo
