-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Tie/Pv/Psc/Run/PscKit.lean: laws on successful runs of the sub-proofs' monad SubM, and that
the model's calls on the channel, where they succeed, are successes of the block's own calls.

The files of this folder follow the sumcheck routines of OnBytes/Model/Psc.lean on a run. This file
is their kit. No routine of OnBytes/Model/Psc.lean occurs in it.

Main names:
  `bind_ok`, `lift_ok`, `liftY_ok`, `pure_ok`, `must_ok`, `mustAs_ok`, `getS_ok`, `take_ok`,
    `change_ok`, `takeSlots_ok`: what a success of a bind, a lifted call, pure, must, mustAs, get,
    take, change and takeSlots says.
  `trRead_recvEs`, `closeAs_close`, `trAnswer_closeOne`, `trAnswerNotZero_closeOne`,
    `trEmpty_closeEmpty`: a success of a call of OnBytes/Model/Rounds.lean is a success of the
    matching call of OnBytes/Iop/Ground.lean, from the same context to the same context.
  `hearOne_of`: elements received, and then a round closed for one element, are a success of
    hearOne (OnBytes/Iop/Psc.lean).
Limits: one direction only, since closeAs tests more than close does. No law has a hypothesis on
whether the channel is a view or the dry run: each holds in both. Nothing is said on hiding.
-/
import OnBytes.Model.Tsc
import OnBytes.Iop.GroundLaws

namespace OnBytes.Model.Road

/-! ## Runs of SubM -/

theorem bind_ok {α β : Type} (x : SubM α) (f : α → SubM β) (F : Fork) (c : Ctx) (r :
    (β × Fork) × Ctx) :
    (x >>= f) F c = .ok r ↔ ∃ a F1 c1, x F c = .ok ((a, F1), c1) ∧ f a F1 c1 = .ok r := by
  show (StateT.bind x f) F c = .ok r ↔ _
  simp only [StateT.bind]
  show (StateT.bind (x F) _) c = .ok r ↔ _
  simp only [StateT.bind]
  show Except.bind (x F c) _ = .ok r ↔ _
  cases h : x F c with
  | error e => simp [Except.bind]
  | ok v =>
    obtain ⟨⟨a, F1⟩, c1⟩ := v
    simp only [Except.bind, Except.ok.injEq, Prod.mk.injEq]
    constructor
    · intro k; exact ⟨a, F1, c1, ⟨⟨rfl, rfl⟩, rfl⟩, k⟩
    · rintro ⟨_, _, _, ⟨⟨rfl, rfl⟩, rfl⟩, k⟩; exact k

theorem lift_ok {α : Type} (b : Blk α) (F G : Fork) (c c' : Ctx) (a : α) :
    (liftM b : SubM α) F c = .ok ((a, G), c') ↔ b c = .ok (a, c') ∧ G = F := by
  show (StateT.lift b : SubM α) F c = .ok ((a, G), c') ↔ _
  simp only [StateT.lift]
  show (StateT.bind b _) c = .ok ((a, G), c') ↔ _
  simp only [StateT.bind]
  show Except.bind (b c) _ = .ok ((a, G), c') ↔ _
  cases h : b c with
  | error e => simp [Except.bind]
  | ok v =>
    obtain ⟨a1, c1⟩ := v
    simp only [Except.bind]
    show (Except.ok ((a1, F), c1) : Except Failure _) = .ok ((a, G), c') ↔ _
    simp only [Except.ok.injEq, Prod.mk.injEq]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨⟨h1, h3⟩, h2.symm⟩
    · rintro ⟨⟨h1, h3⟩, h2⟩; exact ⟨⟨h1, h2.symm⟩, h3⟩

theorem mustAs_ok (name : String) (b : Bool) (c c' : Ctx) (u : Unit) :
    mustAs name b c = .ok (u, c') ↔ b = true ∧ c' = c := by
  unfold mustAs
  cases b with
  | true => simp [pure, StateT.pure, Except.pure, eq_comm]
  | false => simp [refuse, Blk.fail]

/-- A lifted call, with Blk.Yields. -/
theorem liftY_ok {α : Type} (b : Blk α) (F G : Fork) (c c' : Ctx) (a : α) :
    (StateT.lift b : SubM α) F c = .ok ((a, G), c') ↔ b.Yields c a c' ∧ G = F := by
  rw [Blk.yields_iff]; exact lift_ok b F G c c' a

theorem pure_ok {α : Type} (a x : α) (F G : Fork) (c c' : Ctx) :
    (pure a : SubM α) F c = .ok ((x, G), c') ↔ x = a ∧ G = F ∧ c' = c := by
  show (Except.ok ((a, F), c) : Except Failure _) = .ok ((x, G), c') ↔ _
  simp only [Except.ok.injEq, Prod.mk.injEq]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨h1.symm, h2.symm, h3.symm⟩
  · rintro ⟨h1, h2, h3⟩; exact ⟨⟨h1.symm, h2.symm⟩, h3.symm⟩

theorem must_ok (b : Bool) (F G : Fork) (c c' : Ctx) (u : Unit) :
    SubM.must b F c = .ok ((u, G), c') ↔ b = true ∧ G = F ∧ c' = c := by
  unfold SubM.must
  rw [liftY_ok, Blk.yields_must]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨h1, h3, h2⟩
  · rintro ⟨h1, h3, h2⟩; exact ⟨⟨h1, h2⟩, h3⟩

theorem getS_ok {α : Type} (x : Option α) (F G : Fork) (c c' : Ctx) (a : α) :
    SubM.get x F c = .ok ((a, G), c') ↔ x = some a ∧ G = F ∧ c' = c := by
  unfold SubM.get
  rw [liftY_ok, Blk.yields_get]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨h1, h3, h2⟩
  · rintro ⟨h1, h3, h2⟩; exact ⟨⟨h1, h2⟩, h3⟩

theorem take_ok {α : Type} (f : Fork → Option (α × Fork)) (F G : Fork) (c c' : Ctx) (a : α) :
    SubM.take f F c = .ok ((a, G), c') ↔ f F = some (a, G) ∧ c' = c := by
  simp only [SubM.take]
  cases f F with
  | none => simp [liftOption_none]
  | some y => simp [liftOption_some, eq_comm, Prod.ext_iff, and_assoc]

theorem change_ok (f : Fork → Option Fork) (F G : Fork) (c c' : Ctx) (u : Unit) :
    SubM.change f F c = .ok ((u, G), c') ↔ f F = some G ∧ c' = c := by
  simp only [SubM.change]
  cases f F with
  | none => simp [liftOption_none]
  | some y => simp [liftOption_some, eq_comm]

theorem takeSlots_ok (n : Nat) (F G : Fork) (c c' : Ctx) (j : Nat) :
    SubM.takeSlots n F c = .ok ((j, G), c') ↔
      j = F.next ∧ G = { F with next := F.next + n } ∧ c' = c := by
  unfold SubM.takeSlots
  rw [take_ok]
  simp only [Option.some.injEq, Prod.mk.injEq]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨h1.symm, h2.symm, h3⟩
  · rintro ⟨h1, h2, h3⟩; exact ⟨⟨h1.symm, h2.symm⟩, h3⟩

/-! ## The model's calls on the channel are the block's -/

theorem trReadLoop_eq : ∀ (n : Nat) (a : Array E), trReadLoop n a = Blk.recvEsInto n a
  | 0, _ => rfl
  | n + 1, a => by
    simp only [trReadLoop, Blk.recvEsInto]
    congr 1
    funext x
    exact trReadLoop_eq n (a.push x)

/-- trRead hears what recvEs hears. -/
theorem trRead_recvEs (n : Nat) (a : Array E) (c c' : Ctx) (h : (trRead n).Yields c a c') :
    (Blk.recvEs n).Yields c a.toList c' := by
  unfold trRead at h
  rw [trReadLoop_eq] at h
  unfold Blk.recvEs
  exact (Blk.yields_bind _ _ _ _ _).2 ⟨a, c', h, (Blk.yields_pure _ _ _ _).2 ⟨rfl, rfl⟩⟩

theorem lastEntry_inv (e : Fmt.Entry) (c c' : Ctx) (h : Blk.lastEntry.Yields c e c') : c' = c := by
  rw [Blk.yields_iff] at h
  unfold Blk.lastEntry at h
  split at h
  · exact (congrArg Prod.snd (Except.ok.inj h)).symm
  · cases h

/-- closeAs closes the round as close does; its further tests change nothing. -/
theorem closeAs_close (name : String) (kind : Fmt.Kind) (elems nz entries : Nat) (d : Fmt.Drawn)
    (c c' : Ctx) (h : (closeAs name kind elems nz entries).Yields c d c') :
    (Blk.close name kind nz).Yields c d c' := by
  unfold closeAs at h
  obtain ⟨_, c1, h1, k1⟩ := (Blk.yields_bind _ _ _ _ _).1 h
  obtain ⟨_, e1⟩ := (Blk.yields_must _ _ _).1 h1
  obtain ⟨d1, c2, h2, k2⟩ := (Blk.yields_bind _ _ _ _ _).1 k1
  obtain ⟨e, c3, h3, k3⟩ := (Blk.yields_bind _ _ _ _ _).1 k2
  have e3 := lastEntry_inv e _ _ h3
  obtain ⟨_, c4, h4, k4⟩ := (Blk.yields_bind _ _ _ _ _).1 k3
  obtain ⟨_, e4⟩ := (Blk.yields_must _ _ _).1 h4
  obtain ⟨e5, e6⟩ := (Blk.yields_pure _ _ _ _).1 k4
  rw [e5, e6, e4, e3, ← e1]
  exact h2

theorem oneOf_closeOne (name : String) (kind : Fmt.Kind) (nz : Nat) (d : Fmt.Drawn) (x : E)
    (c c1 c' : Ctx) (h1 : (Blk.close name kind nz).Yields c d c1) (h2 : (oneOf d).Yields c1 x c') :
    (Blk.closeOne name kind nz).Yields c x c' := by
  unfold Blk.closeOne
  refine (Blk.yields_bind _ _ _ _ _).2 ⟨d, c1, h1, ?_⟩
  unfold oneOf at h2
  cases hel : d.elems with
  | nil => rw [hel] at h2; rw [Blk.yields_iff] at h2; cases h2
  | cons a l =>
    cases l with
    | nil => rw [hel] at h2; exact h2
    | cons a' l' => rw [hel] at h2; rw [Blk.yields_iff] at h2; cases h2

/-- trAnswer closes a round for one element as closeOne does. -/
theorem trAnswer_closeOne (r : RoundName) (x : E) (c c' : Ctx) (h : (trAnswer r).Yields c x c') :
    (Blk.closeOne r.name (if r == .pscEpsilon then .join else .elems) 0).Yields c x c' := by
  unfold trAnswer at h
  obtain ⟨_, c1, h1, k1⟩ := (Blk.yields_bind _ _ _ _ _).1 h
  obtain ⟨_, e1⟩ := (mustAs_ok _ _ _ _ _).1 ((Blk.yields_iff _ _ _ _).1 h1)
  obtain ⟨d, c2, h2, k2⟩ := (Blk.yields_bind _ _ _ _ _).1 k1
  rw [e1] at h2
  exact oneOf_closeOne _ _ _ d x _ c2 _ (closeAs_close _ _ _ _ _ _ _ _ h2) k2

theorem trAnswerNotZero_closeOne (r : RoundName) (x : E) (c c' : Ctx)
    (h : (trAnswerNotZero r).Yields c x c') : (Blk.closeOne r.name .elems 1).Yields c x c' := by
  unfold trAnswerNotZero at h
  obtain ⟨_, c1, h1, k1⟩ := (Blk.yields_bind _ _ _ _ _).1 h
  obtain ⟨_, e1⟩ := (mustAs_ok _ _ _ _ _).1 ((Blk.yields_iff _ _ _ _).1 h1)
  obtain ⟨d, c2, h2, k2⟩ := (Blk.yields_bind _ _ _ _ _).1 k1
  rw [e1] at h2
  exact oneOf_closeOne _ _ _ d x _ c2 _ (closeAs_close _ _ _ _ _ _ _ _ h2) k2

theorem trEmpty_closeEmpty (r : RoundName) (c c' : Ctx) (h : (trEmpty r).Yields c () c') :
    (Blk.closeEmpty r.name).Yields c () c' := by
  unfold trEmpty at h
  obtain ⟨d, c2, h2, k2⟩ := (Blk.yields_bind _ _ _ _ _).1 h
  unfold Blk.closeEmpty
  exact (Blk.yields_bind _ _ _ _ _).2 ⟨d, c2, closeAs_close _ _ _ _ _ _ _ _ h2, k2⟩

/-- Received, then closed for one element: the block's hearOne. -/
theorem hearOne_of (name : String) (kind : Fmt.Kind) (n nz : Nat) (q : List E) (g : E)
    (c c1 c' : Ctx) (h1 : (Blk.recvEs n).Yields c q c1)
    (h2 : (Blk.closeOne name kind nz).Yields c1 g c') :
    (OnBytes.Psc.hearOne name kind n nz).Yields c (q, g) c' := by
  unfold OnBytes.Psc.hearOne
  exact (Blk.yields_bind _ _ _ _ _).2 ⟨q, c1, h1,
    (Blk.yields_bind _ _ _ _ _).2 ⟨g, c', h2, (Blk.yields_pure _ _ _ _).2 ⟨rfl, rfl⟩⟩⟩

end OnBytes.Model.Road
