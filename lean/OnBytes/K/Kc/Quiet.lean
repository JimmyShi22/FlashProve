-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/K/Kc/Quiet.lean: routines of a sub-proof's check that do not touch the channel, as functions
on the ledger alone.

Many routines of the check of a sub-proof receive nothing and draw nothing: they make forms, add
claims to the sub-proof's one equation, and test public numbers. Such a routine still has the type
of one that runs in a context (OnBytes/Iop/Ground.lean). This file says what "does not touch" means,
gives the rules by which it passes through a routine's text, and takes the context away.

 'QuietB b', for a block b, and 'Quiet m', for a routine m of a sub-proof: in runs on a view, a run
   that succeeds leaves the context as it was but for the intermediate values that are kept
   (`Blk.SameButNotes`), and from every other context of a run on a view the same routine, from the
   same state, succeeds with the same value and the same new state.
 'still m': the function on the ledger alone: the routine m itself, run from one fixed empty context
   of a run on a view (`viewCtx`), with that context dropped from what it returns. Its type is
   Fork → Option (α × Fork): no block, no context. No text is written twice: the function IS the
   program's routine.
 `still_iff`: for a quiet routine, a run on a view from F and ANY context succeeds with a and G
   exactly if 'still m F = some (a, G)'. BOTH DIRECTIONS.
 `Sim.of_quiet`: the same in the form of OnBytes/K/Kc/Laws.lean, so that quiet routines and
   routines that read rounds can be chained.

The rules: `QuietB.of_iff`; instances for pure, bind, if, must, get, fail, the named conditions, a
kept value; for a block as a routine, the steps on the state, reading the state, a function applied
to a value; `qbS`, `quiet_foldlM`, `quiet_forInS`, `quiet_forInA`, `quiet_forInR`, `quiet_forMA`,
`quiet_forML`, `quiet_mapMA` for loops.

Not claimed. Nothing on the dry run. Nothing on soundness. The program does not import this file.
-/
import OnBytes.K.Kc.HearProved

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.K.Kc

open OnBytes.Model (Fork SubM)

variable {α β γ σ : Type}

/-! ## The two notions -/

theorem sameButNotes_refl (c : Ctx) : Blk.SameButNotes c c := ⟨rfl, rfl, rfl, rfl⟩

theorem sameButNotes_trans {a b c : Ctx} (h1 : Blk.SameButNotes a b) (h2 : Blk.SameButNotes b c) :
    Blk.SameButNotes a c :=
  ⟨h2.ch.trans h1.ch, h2.st.trans h1.st, h2.book.trans h1.book, h2.failed.trans h1.failed⟩

/-- The block does not touch the channel, the statement or the book, and does not depend on the
context, in runs on a view. -/
class QuietB (b : Blk α) : Prop where
  quiet : ∀ (c c' d : Ctx) (x : α), c.ch.dry = false → c'.ch.dry = false → b.Yields c x d →
    Blk.SameButNotes c d ∧ ∃ d', b.Yields c' x d'

/-- The same for a routine of a sub-proof, from every state. -/
class Quiet (m : SubM α) : Prop where
  quiet : ∀ F : Fork, QuietB (m F)

/-- A block that leaves the context and whose success is a condition on its value alone. -/
theorem QuietB.of_iff {b : Blk α} (P : α → Prop)
    (h : ∀ (c d : Ctx) (x : α), c.ch.dry = false → (b.Yields c x d ↔ P x ∧ d = c)) : QuietB b :=
  ⟨fun c c' d x hd hd' r => by
    obtain ⟨p, rfl⟩ := (h c d x hd).mp r
    exact ⟨sameButNotes_refl _, c', (h c' c' x hd').mpr ⟨p, rfl⟩⟩⟩

/-! ## Blocks -/

instance quietB_pure (a : α) : QuietB (pure a : Blk α) :=
  QuietB.of_iff (fun x => x = a) fun c d x _ => Blk.yields_pure a x c d

instance quietB_bind (b1 : Blk α) (b2 : α → Blk β) [QuietB b1] [∀ a, QuietB (b2 a)] :
    QuietB (b1 >>= b2) :=
  ⟨fun c c' d y hd hd' r => by
    obtain ⟨x, c1, h1, h2⟩ := (Blk.yields_bind _ _ _ _ _).mp r
    obtain ⟨s1, d1, k1⟩ := QuietB.quiet c c' c1 x hd hd' h1
    have s1' := (QuietB.quiet c' c d1 x hd' hd k1).1
    have e1 : c1.ch.dry = false := by
      rw [s1.ch]
      exact hd
    have e1' : d1.ch.dry = false := by
      rw [s1'.ch]
      exact hd'
    obtain ⟨s2, d2, k2⟩ := QuietB.quiet c1 d1 d y e1 e1' h2
    exact ⟨sameButNotes_trans s1 s2, d2, (Blk.yields_bind _ _ _ _ _).mpr ⟨x, d1, k1, k2⟩⟩⟩

instance quietB_ite (p : Prop) [Decidable p] (a b : Blk α) [QuietB a] [QuietB b] :
    QuietB (if p then a else b) := by
  split <;> infer_instance

instance quietB_must (b : Bool) : QuietB (Blk.must b) :=
  QuietB.of_iff (fun _ => b = true) fun c d _ _ => Blk.yields_must b c d

instance quietB_get (x : Option α) : QuietB (Blk.get x) :=
  QuietB.of_iff (fun a => x = some a) fun c d a _ => Blk.yields_get x a c d

instance quietB_fail (n : String) : QuietB (Blk.fail n : Blk α) :=
  ⟨fun c _ d x _ _ r => by
    have k : (Except.error { name := n } : Except Failure (α × Ctx)) = .ok (x, d) :=
      (Blk.yields_iff _ _ _ _).mp r
    cases k⟩

instance quietB_refuse (n : String) : QuietB (Model.refuse n : Blk α) := by
  unfold Model.refuse
  infer_instance

instance quietB_mustAs (n : String) (b : Bool) : QuietB (Model.mustAs n b) := by
  unfold Model.mustAs
  infer_instance

instance quietB_isDry : QuietB Blk.isDry :=
  QuietB.of_iff (fun b => b = false) fun c d b hd => by
    rw [Slice.yields_isDry, hd]

instance quietB_testAs (n : String) (b : Bool) : QuietB (Model.testAs n b) := by
  unfold Model.testAs
  infer_instance

instance quietB_held (x : Except String α) : QuietB (Model.Head.held x) := by
  unfold Model.Head.held
  split <;> infer_instance

instance quietB_getAs (n : String) (x : Option α) : QuietB (Model.Head.getAs n x) := by
  unfold Model.Head.getAs
  split <;> infer_instance

instance quietB_note (w : String) (v : E) : QuietB (Blk.note w v) :=
  ⟨fun c _ d _ _ _ r =>
    ⟨Blk.yields_note w v c d r, _, (Blk.yields_iff _ _ _ _).mpr rfl⟩⟩

/-! ## Routines -/

instance quiet_pure (a : α) : Quiet (pure a : SubM α) :=
  ⟨fun F => (inferInstance : QuietB (pure (a, F) : Blk (α × Fork)))⟩

instance quiet_bind (m : SubM α) (f : α → SubM β) [Quiet m] [∀ a, Quiet (f a)] :
    Quiet (m >>= f) :=
  ⟨fun F => by
    haveI := Quiet.quiet (m := m) F
    haveI : ∀ p : α × Fork, QuietB (f p.1 p.2) := fun p => Quiet.quiet (m := f p.1) p.2
    exact (inferInstance : QuietB (m F >>= fun p => f p.1 p.2))⟩

/-- One routine after another, with the facts on the parts given by hand. -/
theorem qbS {m : SubM α} {f : α → SubM β} (hm : Quiet m) (hf : ∀ a, Quiet (f a)) :
    Quiet (m >>= f) :=
  @quiet_bind α β m f hm hf

instance quiet_ite (p : Prop) [Decidable p] (a b : SubM α) [Quiet a] [Quiet b] :
    Quiet (if p then a else b) := by
  split <;> infer_instance

instance quiet_lift (b : Blk α) [QuietB b] : Quiet (StateT.lift b : SubM α) :=
  ⟨fun F => (inferInstance : QuietB (b >>= fun y => pure (y, F)))⟩

instance quiet_liftM (b : Blk α) [QuietB b] : Quiet (liftM b : SubM α) :=
  quiet_lift b

instance quiet_change (f : Fork → Option Fork) : Quiet (SubM.change f) :=
  ⟨fun F => QuietB.of_iff (fun x => f F = some x.2) fun c d x _ => by
    obtain ⟨u, G⟩ := x
    cases u
    exact sub_change f F G c d⟩

instance quiet_take (f : Fork → Option (α × Fork)) : Quiet (SubM.take f) :=
  ⟨fun F => QuietB.of_iff (fun x => f F = some x) fun c d x _ => by
    obtain ⟨a, G⟩ := x
    exact sub_take f F G c d a⟩

instance quiet_ask (f : Fork → Option α) : Quiet (SubM.ask f) :=
  ⟨fun F => QuietB.of_iff (fun x => f F = some x.1 ∧ x.2 = F) fun c d x _ => by
    obtain ⟨a, G⟩ := x
    show (SubM.ask f F).Yields c (a, G) d ↔ (f F = some a ∧ G = F) ∧ d = c
    rw [sub_ask, and_assoc]⟩

instance quiet_must (b : Bool) : Quiet (SubM.must b) := by
  unfold SubM.must
  infer_instance

instance quiet_get (x : Option α) : Quiet (SubM.get x) := by
  unfold SubM.get
  infer_instance

instance quiet_getS : Quiet (get : SubM Fork) :=
  ⟨fun F => (inferInstance : QuietB (pure (F, F) : Blk (Fork × Fork)))⟩

instance quiet_modify (f : Fork → Fork) : Quiet (modify f : SubM PUnit) :=
  ⟨fun F => (inferInstance : QuietB (pure (PUnit.unit, f F) : Blk (PUnit × Fork)))⟩

instance quiet_map (g : α → β) (m : SubM α) [Quiet m] : Quiet (g <$> m) := by
  rw [map_eq_pure_bind]
  infer_instance

instance quiet_slot : Quiet SubM.slot := by
  unfold SubM.slot
  infer_instance

instance quiet_shown (j : Nat) : Quiet (SubM.shown j) := by
  unfold SubM.shown
  infer_instance

instance quiet_publicPart (a : Model.Aff) : Quiet (SubM.publicPart a) := by
  unfold SubM.publicPart
  infer_instance

instance quiet_noteH (w : String) (v : E) : Quiet (Model.Head.noteH w v) := by
  unfold Model.Head.noteH
  infer_instance

/-! ## Loops -/

theorem quiet_foldlM (f : σ → β → SubM σ) (hf : ∀ s a, Quiet (f s a)) :
    ∀ (l : List β) (s : σ), Quiet (l.foldlM f s)
  | [], s => by
    rw [List.foldlM_nil]
    infer_instance
  | a :: l, s => by
    rw [List.foldlM_cons]
    haveI := hf s a
    haveI := fun s' => quiet_foldlM f hf l s'
    infer_instance

instance quiet_fold (f : σ → β → SubM σ) [hf : ∀ s a, Quiet (f s a)] (l : List β) (s : σ) :
    Quiet (l.foldlM f s) := quiet_foldlM f hf l s

theorem quiet_forInS (f : γ → σ → SubM (ForInStep σ)) (hf : ∀ x s, Quiet (f x s)) :
    ∀ (l : List γ) (s : σ), Quiet (forIn l s f)
  | [], s => by
    rw [List.forIn_nil]
    infer_instance
  | x :: l, s => by
    rw [List.forIn_cons]
    refine qbS (hf x s) fun r => ?_
    cases r with
    | done b => exact quiet_pure b
    | yield b => exact quiet_forInS f hf l b

theorem quiet_forInA (f : γ → σ → SubM (ForInStep σ)) (hf : ∀ x s, Quiet (f x s)) (l : Array γ)
    (s : σ) : Quiet (forIn l s f) := by
  rw [← Array.forIn_toList]
  exact quiet_forInS f hf l.toList s

/-- The numbers of the loop "for x in [0:n]". -/
theorem range_list (n : Nat) :
    List.range' ([:n] : Std.Legacy.Range).start ([:n] : Std.Legacy.Range).size
      ([:n] : Std.Legacy.Range).step = List.range' 0 n := by
  simp [Std.Legacy.Range.size]

theorem quiet_forInR (n : Nat) (s : σ) (f : Nat → σ → SubM (ForInStep σ))
    (hf : ∀ x s, Quiet (f x s)) : Quiet (forIn [:n] s f) := by
  have e : forIn [:n] s f = forIn (List.range' 0 n) s f := by
    rw [Std.Legacy.Range.forIn_eq_forIn_range', range_list]
  rw [e]
  exact quiet_forInS f hf _ _

theorem quiet_forMA (f : γ → SubM PUnit) (hf : ∀ x, Quiet (f x)) (l : Array γ) :
    Quiet (l.forM f) := by
  unfold Array.forM
  rw [← Array.foldlM_toList]
  exact quiet_foldlM _ (fun _ x => hf x) _ _

theorem quiet_forML (f : γ → SubM PUnit) (hf : ∀ x, Quiet (f x)) : ∀ l : List γ, Quiet (l.forM f)
  | [] => by
    have e : ([] : List γ).forM f = pure PUnit.unit := rfl
    rw [e]
    infer_instance
  | x :: l => by
    have e : (x :: l).forM f = (f x >>= fun _ => l.forM f) := rfl
    rw [e]
    haveI := hf x
    haveI := quiet_forML f hf l
    infer_instance

theorem quiet_mapMA (f : γ → SubM β) (hf : ∀ x, Quiet (f x)) (l : Array γ) :
    Quiet (l.mapM f) := by
  rw [Array.mapM_eq_foldlM, ← Array.foldlM_toList]
  refine quiet_foldlM _ (fun s x => ?_) _ _
  haveI := hf x
  infer_instance

/-! ## The context taken away -/

/-- An empty context of a run on a view. -/
def viewCtx : Ctx := { ch := { dry := false, entries := [] } }

/-- The routine as a function on the ledger alone: run from `viewCtx`, the context dropped. -/
def still (m : SubM α) (F : Fork) : Option (α × Fork) := ((m F).outcome viewCtx).map (·.1)

/-- **A quiet routine is its function on the ledger**: in a run on a view, from any context. -/
theorem still_iff (m : SubM α) [Quiet m] (F G : Fork) (C : Ctx) (a : α) (hd : C.ch.dry = false) :
    (∃ D, (m F).Yields C (a, G) D) ↔ still m F = some (a, G) := by
  haveI := Quiet.quiet (m := m) F
  constructor
  · rintro ⟨D, r⟩
    obtain ⟨_, d, k⟩ := QuietB.quiet C viewCtx D (a, G) hd rfl r
    have k' : (m F).outcome viewCtx = some ((a, G), d) := k
    unfold still
    rw [k']
    rfl
  · intro e
    unfold still at e
    cases ho : (m F).outcome viewCtx with
    | none =>
      rw [ho] at e
      cases e
    | some y =>
      rw [ho] at e
      obtain ⟨x, d⟩ := y
      have ex : x = (a, G) := Option.some.inj e
      subst ex
      exact (QuietB.quiet viewCtx C d (a, G) rfl hd ho).2

/-- What a quiet routine leaves of the context: all but the kept values. -/
theorem still_same (m : SubM α) [Quiet m] {F G : Fork} {C D : Ctx} {a : α}
    (hd : C.ch.dry = false) (r : (m F).Yields C (a, G) D) : Blk.SameButNotes C D := by
  haveI := Quiet.quiet (m := m) F
  exact (QuietB.quiet C C D (a, G) hd hd r).1

/-- A function on the ledger alone as a function on a ledger and a tape. -/
def Fl.ofStill (g : Fork → Option (α × Fork)) : Fl α := fun F t => (g F).map fun x => (x.1, x.2, t)

/-- A quiet routine in the form of OnBytes/K/Kc/Laws.lean. -/
theorem Sim.of_quiet (m : SubM α) [Quiet m] : Sim m (Fl.ofStill (still m)) := by
  intro F G C D a hd r
  have s := still_same m hd r
  have e := (still_iff m F G C a hd).mp ⟨D, r⟩
  refine ⟨?_, Left.of_same hd s⟩
  unfold Fl.ofStill tape
  rw [e, s.ch]
  rfl

end OnBytes.K.Kc
