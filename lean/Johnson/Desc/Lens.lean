-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Lens.lean: a part of a chain's carried state, and the one wrapper by which a step that
is typed at a part's state becomes a step at the whole state.

The steps of a chain's decision are written by many hands, each at the state that its routine reads
and writes. The fold of a chain threads one carried state S. A lens says where a part P lies in S:
how it is read (`get`) and how it is laid back (`set`). `Lens.lift` turns a step at P into a step at
S: it reads the part, runs the step on this stretch's rounds and the opened columns, and lays the
new part back; it refuses exactly where the step refuses, and takes the columns that the step takes.

Main names:
  `Lens S P`, `Lens.Lawful`: get and set; the laws: get after set, set after get, set after set.
  `Lens.lift`: the wrapper.
  `Lens.liftWith`: the same for a step that also reads, and does not write, something else of S.
  `Lens.id`, `Lens.comp`, `Lens.pair`: the whole state; a part of a part; two parts as one part:
    `pair` takes a proof that they do not overlap (`Lens.Apart`).
  `Part S P`, `Part.Lawful`, `Part.Apart`, `Part.lift`, `Part.liftWith`, `Part.ofLens`, `Part.comp`,
    `Part.pair`, `Part.liftRow`: the same for a part that is there at some states alone (a link's
    own part): `get?` may say that there is none; the wrapper then refuses.
  `Step.quiet`, `Step.quietE`: a function on a state that takes no round and no column, as a step:
    it refuses a stretch that is not empty. `Step.nest`: a table of rows as one step.
Main theorems: `lift_none`, `lift_some`: where the wrapper refuses and what it returns; `get_lift`:
the part behind the wrapped step is the part behind the step; `lift_keeps`: a part that lies apart
is not touched; `lift_id`, `lift_comp`: the wrapper goes along `id` and `comp`; `lawful_id`,
`lawful_comp`, `lawful_pair`. For a part: `Part.lift_absent`, `Part.lift_at`, `Part.lift_none`,
`Part.lift_eq_some`, `Part.get_lift`, `Part.lift_keeps`, `Part.liftWith_absent`, `Part.liftWith_at`,
`Part.lawful_ofLens`, `Part.lift_ofLens`.
Limits: general; no field of any state is named here. It imports Johnson/Desc/Step.lean alone
(`OpenedColumn`, `Step`, `Row`, `stepAll`), which imports Fmt/View.lean alone.

This file does not count as written independently of ArkLib: AI systems that had seen ArkLib's
source wrote it, and ArkLib has a file of the same name and idea,
ArkLib/OracleReduction/LiftContext/Lens.lean (Apache-2.0; commit 2817d8c7). The two files have three
declared names in common (`Lens`, `id`, `lift`).

-/
import Johnson.Desc.Step

set_option autoImplicit false

namespace VerifiableInference.Desc

/-- Where a part P lies in a state S. -/
structure Lens (S P : Type) where
  /-- reads the part -/
  get : S → P
  /-- lays a part back -/
  set : S → P → S

namespace Lens

variable {S P Q R : Type}

/-- The laws of a lens. -/
structure Lawful (l : Lens S P) : Prop where
  /-- what was laid is what is read -/
  get_set : ∀ s p, l.get (l.set s p) = p
  /-- to lay back what was read changes nothing -/
  set_get : ∀ s, l.set s (l.get s) = s
  /-- the later laying wins -/
  set_set : ∀ s p q, l.set (l.set s p) q = l.set s q

/-- Two parts do not overlap: to lay the one does not change the other, and the order of two layings
does not matter. -/
structure Apart (l : Lens S P) (m : Lens S Q) : Prop where
  get_left : ∀ s q, l.get (m.set s q) = l.get s
  get_right : ∀ s p, m.get (l.set s p) = m.get s
  swap : ∀ s p q, m.set (l.set s p) q = l.set (m.set s q) p

/-- **The wrapper**: a step at a part's state as a step at the whole state. -/
def lift (l : Lens S P) (f : Step P) : Step S := fun s rounds cols =>
  (f (l.get s) rounds cols).map fun x => (l.set s x.1, x.2)

/-- The wrapper for a step that also reads something else of the state, which it does not write. -/
def liftWith (l : Lens S P) (read : S → R) (f : R → Step P) : Step S := fun s rounds cols =>
  l.lift (f (read s)) s rounds cols

/-- The whole state as a part. -/
protected def id : Lens S S := ⟨fun s => s, fun _ s => s⟩

/-- A part of a part. -/
def comp (l : Lens S P) (m : Lens P Q) : Lens S Q :=
  ⟨fun s => m.get (l.get s), fun s q => l.set s (m.set (l.get s) q)⟩

/-- Two parts that do not overlap, as one. The proof costs nothing at the run; without it the second
laying would win where the two overlap, and what a step returned for the first would be lost. -/
def pair (l : Lens S P) (m : Lens S Q) (_ : l.Apart m) : Lens S (P × Q) :=
  ⟨fun s => (l.get s, m.get s), fun s x => m.set (l.set s x.1) x.2⟩

/-! ## What the wrapper does -/

/-- The wrapper refuses exactly where the step refuses. -/
theorem lift_none (l : Lens S P) (f : Step P) (s : S) (rounds : List Fmt.RoundView) (cols : List OpenedColumn) :
    l.lift f s rounds cols = none ↔ f (l.get s) rounds cols = none := by
  unfold lift
  cases f (l.get s) rounds cols <;> simp

/-- What the wrapper returns. -/
theorem lift_some (l : Lens S P) (f : Step P) (s : S) (rounds : List Fmt.RoundView) (cols : List OpenedColumn)
    (p : P) (k : Nat) (h : f (l.get s) rounds cols = some (p, k)) :
    l.lift f s rounds cols = some (l.set s p, k) := by
  unfold lift
  rw [h]
  rfl

/-- Whatever the wrapper returns comes of the step. -/
theorem lift_eq_some (l : Lens S P) (f : Step P) (s t : S) (rounds : List Fmt.RoundView)
    (cols : List OpenedColumn) (k : Nat) (h : l.lift f s rounds cols = some (t, k)) :
    ∃ p, f (l.get s) rounds cols = some (p, k) ∧ t = l.set s p := by
  unfold lift at h
  cases e : f (l.get s) rounds cols with
  | none => rw [e] at h; cases h
  | some x =>
    rw [e] at h
    cases h
    exact ⟨x.1, rfl, rfl⟩

/-- The part behind the wrapped step is the part behind the step. -/
theorem get_lift (l : Lens S P) (hl : l.Lawful) (f : Step P) (s t : S) (rounds : List Fmt.RoundView)
    (cols : List OpenedColumn) (k : Nat) (h : l.lift f s rounds cols = some (t, k)) :
    f (l.get s) rounds cols = some (l.get t, k) := by
  obtain ⟨p, hp, rfl⟩ := lift_eq_some l f s t rounds cols k h
  rw [hl.get_set]
  exact hp

/-- A part that lies apart is not touched. -/
theorem lift_keeps (l : Lens S P) (m : Lens S Q) (ha : l.Apart m) (f : Step P) (s t : S)
    (rounds : List Fmt.RoundView) (cols : List OpenedColumn) (k : Nat)
    (h : l.lift f s rounds cols = some (t, k)) : m.get t = m.get s := by
  obtain ⟨p, _, rfl⟩ := lift_eq_some l f s t rounds cols k h
  exact ha.get_right s p

/-- At the whole state the wrapper does nothing. -/
theorem lift_id (f : Step S) : (Lens.id : Lens S S).lift f = f := by
  funext s rounds cols
  unfold lift Lens.id
  cases f s rounds cols <;> rfl

/-- The wrapper along a part of a part. -/
theorem lift_comp (l : Lens S P) (m : Lens P Q) (f : Step Q) :
    (l.comp m).lift f = l.lift (m.lift f) := by
  funext s rounds cols
  unfold lift comp
  cases f (m.get (l.get s)) rounds cols <;> rfl

/-! ## The laws go along -/

theorem lawful_id : (Lens.id : Lens S S).Lawful :=
  ⟨fun _ _ => rfl, fun _ => rfl, fun _ _ _ => rfl⟩

theorem lawful_comp (l : Lens S P) (m : Lens P Q) (hl : l.Lawful) (hm : m.Lawful) :
    (l.comp m).Lawful where
  get_set := fun s q => by
    show m.get (l.get (l.set s (m.set (l.get s) q))) = q
    rw [hl.get_set, hm.get_set]
  set_get := fun s => by
    show l.set s (m.set (l.get s) (m.get (l.get s))) = s
    rw [hm.set_get, hl.set_get]
  set_set := fun s p q => by
    show l.set (l.set s (m.set (l.get s) p)) (m.set (l.get (l.set s (m.set (l.get s) p))) q) =
      l.set s (m.set (l.get s) q)
    rw [hl.get_set, hm.set_set, hl.set_set]

theorem lawful_pair (l : Lens S P) (m : Lens S Q) (hl : l.Lawful) (hm : m.Lawful)
    (ha : l.Apart m) : (l.pair m ha).Lawful where
  get_set := fun s x => by
    show (l.get (m.set (l.set s x.1) x.2), m.get (m.set (l.set s x.1) x.2)) = x
    rw [ha.get_left, hl.get_set, hm.get_set]
  set_get := fun s => by
    show m.set (l.set s (l.get s)) (m.get s) = s
    rw [hl.set_get, hm.set_get]
  set_set := fun s x y => by
    show m.set (l.set (m.set (l.set s x.1) x.2) y.1) y.2 = m.set (l.set s y.1) y.2
    rw [← ha.swap (l.set s x.1) y.1 x.2, hl.set_set, hm.set_set]

end Lens

/-! ## A part that is there at some states alone -/

/-- Where a part P lies in a state S, if it is there: a chain's state holds a link's own part only
while the chain stands inside such a link. That to lay a part where there is none changes nothing
is a law (`Lawful.set_none`), no fact of this record. -/
structure Part (S P : Type) where
  /-- reads the part, if it is there -/
  get? : S → Option P
  /-- lays a part back -/
  set : S → P → S

namespace Part

variable {S P Q R : Type}

/-- The laws of a part. -/
structure Lawful (l : Part S P) : Prop where
  /-- where there is a part, what was laid is what is read -/
  get_set : ∀ s p q, l.get? s = some q → l.get? (l.set s p) = some p
  /-- to lay back what was read changes nothing -/
  set_get : ∀ s p, l.get? s = some p → l.set s p = s
  /-- the later laying wins -/
  set_set : ∀ s p q, l.set (l.set s p) q = l.set s q
  /-- where there is no part, a laying changes nothing -/
  set_none : ∀ s p, l.get? s = none → l.set s p = s

/-- Two parts do not overlap. -/
structure Apart (l : Part S P) (m : Part S Q) : Prop where
  get_left : ∀ s q, l.get? (m.set s q) = l.get? s
  get_right : ∀ s p, m.get? (l.set s p) = m.get? s
  swap : ∀ s p q, m.set (l.set s p) q = l.set (m.set s q) p

/-- **The wrapper at a part that may not be there**: it refuses where the part is not there. -/
def lift (l : Part S P) (f : Step P) : Step S := fun s rounds cols =>
  (l.get? s).bind fun p => (f p rounds cols).map fun x => (l.set s x.1, x.2)

/-- The same for a step that also reads something else of the state, which it does not write; it
refuses where that is not there. -/
def liftWith (l : Part S P) (read : S → Option R) (f : R → Step P) : Step S := fun s rounds cols =>
  match read s with
  | none => none
  | some r => l.lift (f r) s rounds cols

/-- A lens as a part that is always there. -/
def ofLens (l : Lens S P) : Part S P := ⟨fun s => some (l.get s), l.set⟩

/-- A part of a part. -/
def comp (l : Part S P) (m : Part P Q) : Part S Q :=
  ⟨fun s => (l.get? s).bind m.get?,
   fun s q => match l.get? s with
     | none => s
     | some p => l.set s (m.set p q)⟩

/-- Two parts that do not overlap, as one: there where both are. -/
def pair (l : Part S P) (m : Part S Q) (_ : l.Apart m) : Part S (P × Q) :=
  ⟨fun s => (l.get? s).bind fun p => (m.get? s).map fun q => (p, q),
   fun s x => m.set (l.set s x.1) x.2⟩

/-- The wrapper refuses where the part is not there. -/
theorem lift_absent (l : Part S P) (f : Step P) (s : S) (rounds : List Fmt.RoundView) (cols : List OpenedColumn)
    (h : l.get? s = none) : l.lift f s rounds cols = none := by
  unfold lift
  rw [h]
  rfl

/-- Where the part is there, the wrapper is the step at it, the new part laid back. -/
theorem lift_at (l : Part S P) (f : Step P) (s : S) (p : P) (rounds : List Fmt.RoundView)
    (cols : List OpenedColumn) (h : l.get? s = some p) :
    l.lift f s rounds cols = (f p rounds cols).map fun x => (l.set s x.1, x.2) := by
  unfold lift
  rw [h]
  rfl

/-- Where the part is there, the wrapper refuses exactly where the step refuses. -/
theorem lift_none (l : Part S P) (f : Step P) (s : S) (p : P) (rounds : List Fmt.RoundView)
    (cols : List OpenedColumn) (h : l.get? s = some p) :
    l.lift f s rounds cols = none ↔ f p rounds cols = none := by
  rw [lift_at l f s p rounds cols h]
  cases f p rounds cols <;> simp

/-- Whatever the wrapper returns comes of the step at the part that was there. -/
theorem lift_eq_some (l : Part S P) (f : Step P) (s t : S) (rounds : List Fmt.RoundView)
    (cols : List OpenedColumn) (k : Nat) (h : l.lift f s rounds cols = some (t, k)) :
    ∃ p p', l.get? s = some p ∧ f p rounds cols = some (p', k) ∧ t = l.set s p' := by
  cases e : l.get? s with
  | none => rw [lift_absent l f s rounds cols e] at h; cases h
  | some p =>
    rw [lift_at l f s p rounds cols e] at h
    cases e' : f p rounds cols with
    | none => rw [e'] at h; cases h
    | some x =>
      rw [e'] at h
      cases h
      exact ⟨p, x.1, rfl, e', rfl⟩

/-- The part behind the wrapped step is the part behind the step. -/
theorem get_lift (l : Part S P) (hl : l.Lawful) (f : Step P) (s t : S) (rounds : List Fmt.RoundView)
    (cols : List OpenedColumn) (k : Nat) (h : l.lift f s rounds cols = some (t, k)) :
    ∃ p p', l.get? s = some p ∧ f p rounds cols = some (p', k) ∧ l.get? t = some p' := by
  obtain ⟨p, p', h1, h2, rfl⟩ := lift_eq_some l f s t rounds cols k h
  exact ⟨p, p', h1, h2, hl.get_set s p' p h1⟩

/-- A part that lies apart is not touched. -/
theorem lift_keeps (l : Part S P) (m : Part S Q) (ha : l.Apart m) (f : Step P) (s t : S)
    (rounds : List Fmt.RoundView) (cols : List OpenedColumn) (k : Nat)
    (h : l.lift f s rounds cols = some (t, k)) : m.get? t = m.get? s := by
  obtain ⟨_, p', _, _, rfl⟩ := lift_eq_some l f s t rounds cols k h
  exact ha.get_right s p'

/-- Where what it reads is not there, `liftWith` refuses. -/
theorem liftWith_absent (l : Part S P) (read : S → Option R) (f : R → Step P) (s : S)
    (rounds : List Fmt.RoundView) (cols : List OpenedColumn) (h : read s = none) :
    l.liftWith read f s rounds cols = none := by
  unfold liftWith
  rw [h]

/-- Where it is there, `liftWith` is `lift` of the step at what was read. -/
theorem liftWith_at (l : Part S P) (read : S → Option R) (f : R → Step P) (s : S) (r : R)
    (rounds : List Fmt.RoundView) (cols : List OpenedColumn) (h : read s = some r) :
    l.liftWith read f s rounds cols = l.lift (f r) s rounds cols := by
  unfold liftWith
  rw [h]

/-- A row of a table at a part's state as a row at the whole state. -/
def liftRow (l : Part S P) (r : Row P) : Row S := ⟨r.name, r.take, l.lift r.step⟩

/-- A lawful lens is a lawful part. -/
theorem lawful_ofLens (l : Lens S P) (hl : l.Lawful) : (ofLens l).Lawful :=
  ⟨fun s p _ _ => congrArg some (hl.get_set s p),
   fun s p h => by
     have e : l.get s = p := Option.some.inj h
     show l.set s p = s
     rw [← e, hl.set_get],
   fun s p q => hl.set_set s p q,
   fun _ _ h => by cases h⟩

/-- At a lens the two wrappers are one. -/
theorem lift_ofLens (l : Lens S P) (f : Step P) : (ofLens l).lift f = l.lift f := rfl

end Part

namespace Step

variable {S α : Type}

/-- A function on a state that takes no round and no column, as a step. It refuses a stretch that is
not empty. -/
def quiet (f : S → Option S) : Step S := fun s rounds _ =>
  if rounds.isEmpty then (f s).map fun t => (t, 0) else none

/-- The same for a function that refuses under a name; the name is dropped. -/
def quietE (f : S → Except String S) : Step S := quiet fun s => (f s).toOption

/-- A table as one step: it refuses where a row refuses or a round of the stretch is left over, and
says how many columns its rows took. -/
def nest (tbl : List (Row S)) : Step S := fun s rounds cols =>
  match stepAll tbl s rounds cols with
  | .ok (t, [], left) => some (t, cols.length - left.length)
  | _ => none

/-- A quiet step takes no column. -/
theorem quiet_takes (f : S → Option S) (s t : S) (rounds : List Fmt.RoundView) (cols : List OpenedColumn) (k : Nat)
    (h : quiet f s rounds cols = some (t, k)) : rounds = [] ∧ k = 0 ∧ f s = some t := by
  unfold quiet at h
  cases rounds with
  | cons r l => simp at h
  | nil =>
    cases e : f s with
    | none => simp [e] at h
    | some u =>
      simp [e] at h
      exact ⟨rfl, h.2.symm, by rw [h.1]⟩

end Step

end VerifiableInference.Desc

#print axioms VerifiableInference.Desc.Lens.get_lift
#print axioms VerifiableInference.Desc.Lens.lift_keeps
#print axioms VerifiableInference.Desc.Lens.lift_comp
#print axioms VerifiableInference.Desc.Lens.lawful_pair
#print axioms VerifiableInference.Desc.Step.quiet_takes
#print axioms VerifiableInference.Desc.Part.get_lift
#print axioms VerifiableInference.Desc.Part.lawful_ofLens
#print axioms VerifiableInference.Desc.Part.lift_keeps
#print axioms VerifiableInference.Desc.Part.liftWith_at
