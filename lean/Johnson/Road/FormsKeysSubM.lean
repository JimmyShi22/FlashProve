-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/FormsKeysSubM.lean: laws on a run of a routine of a sub-proof.

A routine of a sub-proof (SubM in OnBytes/Model/Hide.lean) takes a state (Fork) and gives a block
(Blk in OnBytes/Iop/Ground.lean), which takes a context and returns a value, a state and a context,
or fails. The verifier's checks are written in do-notation over such routines. To say what a check
has done when it has returned, one has to take its text apart step by step. This file holds the laws
for that: one for each way in which the text of OnBytes/Model/Layer.lean puts routines together, and
one for each small routine that reads no message.

The form is that of the verifier's laws on blocks (OnBytes/Iop/GroundLaws.lean): a law speaks of a
run that returns, (m F).Yields c (a, G) c': the routine m, from the state F and the context c,
returns the value a and leaves the state G and the context c'. runs_iff turns that into the equation
m F c = .ok ((a, G), c'), in which SubM.lin_run (OnBytes/Model/HideLaws.lean) and
t2Lin_total (OnBytes/Model/TreesLaws.lean) are written. Nothing is said where a routine fails.

Main theorems: runs_iff; sub_pure, sub_bind, sub_seq, sub_lift; sub_get, sub_form, sub_must,
sub_mustAs, sub_note, sub_change, sub_ask, sub_take, sub_lin; sub_forIn (a loop over a list),
sub_forM (one call for each entry of an array), sub_mapM_list; link_sub.

What is compared with what: the verifier's text with itself.

What is not here: the routines that read a message or draw (read, point, batch, answer); Blk.check
and Blk.test. No theorem says that a routine returns. The program does not import this file.
-/
import OnBytes.Model.Layer
import OnBytes.Model.HideLaws
import OnBytes.Iop.GroundLaws

set_option autoImplicit false

namespace OnBytes.Road

open OnBytes.Model (Fork SubM LinkM LinkCtx Aff)

variable {α β : Type}

/-- A run that returns, as an equation. -/
theorem runs_iff (m : SubM α) (F G : Fork) (c c' : Ctx) (a : α) :
    (m F).Yields c (a, G) c' ↔ m F c = .ok ((a, G), c') :=
  Blk.yields_iff _ _ _ _

/-! ## How routines are put together -/

/-- A routine that only returns a value. -/
theorem sub_pure (a x : α) (F G : Fork) (c c' : Ctx) :
    ((pure a : SubM α) F).Yields c (x, G) c' ↔ x = a ∧ G = F ∧ c' = c := by
  show (pure (a, F) : Blk (α × Fork)).Yields c (x, G) c' ↔ _
  rw [Blk.yields_pure]
  constructor
  · rintro ⟨h1, h2⟩
    cases h1
    exact ⟨rfl, rfl, h2⟩
  · rintro ⟨rfl, rfl, rfl⟩
    exact ⟨rfl, rfl⟩

/-- Two routines, one after the other: a run of the whole is a run of the first followed by a run of
the second from where the first ended. -/
theorem sub_bind (m : SubM α) (k : α → SubM β) (F G : Fork) (c c' : Ctx) (b : β) :
    ((m >>= k) F).Yields c (b, G) c' ↔
      ∃ (a : α) (F1 : Fork) (c1 : Ctx),
        (m F).Yields c (a, F1) c1 ∧ (k a F1).Yields c1 (b, G) c' := by
  show ((m F >>= fun p => k p.1 p.2 : Blk (β × Fork))).Yields c (b, G) c' ↔ _
  rw [Blk.yields_bind]
  constructor
  · rintro ⟨⟨a, F1⟩, c1, h1, h2⟩
    exact ⟨a, F1, c1, h1, h2⟩
  · rintro ⟨a, F1, c1, h1, h2⟩
    exact ⟨(a, F1), c1, h1, h2⟩

/-- The same where the first routine returns no value. -/
theorem sub_seq (m : SubM Unit) (k : SubM β) (F G : Fork) (c c' : Ctx) (b : β) :
    ((do m; k) F).Yields c (b, G) c' ↔
      ∃ (F1 : Fork) (c1 : Ctx), (m F).Yields c ((), F1) c1 ∧ (k F1).Yields c1 (b, G) c' := by
  rw [sub_bind]
  constructor
  · rintro ⟨_, F1, c1, h1, h2⟩
    exact ⟨F1, c1, h1, h2⟩
  · rintro ⟨F1, c1, h1, h2⟩
    exact ⟨(), F1, c1, h1, h2⟩

/-- A block as a routine: it runs, and the state stays as it was. -/
theorem sub_lift (x : Blk α) (F G : Fork) (c c' : Ctx) (a : α) :
    ((StateT.lift x : SubM α) F).Yields c (a, G) c' ↔ x.Yields c a c' ∧ G = F := by
  show ((x >>= fun y => pure (y, F) : Blk (α × Fork))).Yields c (a, G) c' ↔ _
  rw [Blk.yields_bind]
  constructor
  · rintro ⟨y, c1, h1, h2⟩
    obtain ⟨e1, e2⟩ := (Blk.yields_pure _ _ _ _).mp h2
    cases e1
    subst e2
    exact ⟨h1, rfl⟩
  · rintro ⟨h1, rfl⟩
    exact ⟨a, c', h1, (Blk.yields_pure _ _ _ _).mpr ⟨rfl, rfl⟩⟩

/-! ## The small routines that read no message -/

/-- SubM.get: the value was there; nothing has turned. -/
theorem sub_get (x : Option α) (F G : Fork) (c c' : Ctx) (a : α) :
    (SubM.get x F).Yields c (a, G) c' ↔ x = some a ∧ G = F ∧ c' = c := by
  unfold SubM.get
  rw [sub_lift, Blk.yields_get]
  tauto

/-- The same under the name that OnBytes/Model/Layer.lean gives it. -/
theorem sub_form (x : Option α) (F G : Fork) (c c' : Ctx) (a : α) :
    (Model.Layer.form x F).Yields c (a, G) c' ↔ x = some a ∧ G = F ∧ c' = c :=
  sub_get x F G c c' a

/-- SubM.must: the condition held; nothing has turned. -/
theorem sub_must (b : Bool) (F G : Fork) (c c' : Ctx) :
    (SubM.must b F).Yields c ((), G) c' ↔ b = true ∧ G = F ∧ c' = c := by
  unfold SubM.must
  rw [sub_lift, Blk.yields_must]
  tauto

/-- mustAs inside a routine, as do-notation lifts it: the condition held; nothing has turned. -/
theorem sub_mustAs (n : String) (b : Bool) (F G : Fork) (c c' : Ctx) :
    ((monadLift (Model.mustAs n b) : SubM Unit) F).Yields c ((), G) c' ↔
      b = true ∧ G = F ∧ c' = c := by
  show ((StateT.lift (Model.mustAs n b) : SubM Unit) F).Yields c ((), G) c' ↔ _
  rw [sub_lift, Blk.yields_iff]
  cases b with
  | false =>
    constructor
    · rintro ⟨h, -⟩
      cases h
    · rintro ⟨h, -, -⟩
      cases h
  | true =>
    constructor
    · rintro ⟨h, e⟩
      cases h
      exact ⟨rfl, e, rfl⟩
    · rintro ⟨-, e, rfl⟩
      exact ⟨rfl, e⟩

/-- A note leaves the state as it was and, of the context, the channel, the statement, the book and
the record of a failed test. -/
theorem sub_note {w : String} {x : E} {F G : Fork} {c c' : Ctx}
    (h : (Model.Layer.note w x F).Yields c ((), G) c') : G = F ∧ Blk.SameButNotes c c' := by
  have h' : ((StateT.lift (Blk.note ("layer: " ++ w) x) : SubM Unit) F).Yields c ((), G) c' := h
  obtain ⟨h1, h2⟩ := (sub_lift _ _ _ _ _ _).mp h'
  exact ⟨h2, Blk.yields_note _ _ _ _ h1⟩

/-- SubM.change: the step has returned the new state; the context has not turned. -/
theorem sub_change (f : Fork → Option Fork) (F G : Fork) (c c' : Ctx) :
    (SubM.change f F).Yields c ((), G) c' ↔ f F = some G ∧ c' = c := by
  rw [runs_iff]
  simp only [SubM.change]
  cases f F with
  | none => simp [liftOption_none]
  | some H => simp [liftOption_some, eq_comm]

/-- SubM.ask: the function has returned the value; nothing has turned. -/
theorem sub_ask (f : Fork → Option α) (F G : Fork) (c c' : Ctx) (a : α) :
    (SubM.ask f F).Yields c (a, G) c' ↔ f F = some a ∧ G = F ∧ c' = c := by
  rw [runs_iff]
  simp only [SubM.ask]
  cases f F with
  | none => simp [liftOption_none]
  | some y => simp [liftOption_some, eq_comm, and_assoc]

/-- SubM.take: the step has returned the value and the new state; the context has not turned. -/
theorem sub_take (f : Fork → Option (α × Fork)) (F G : Fork) (c c' : Ctx) (a : α) :
    (SubM.take f F).Yields c (a, G) c' ↔ f F = some (a, G) ∧ c' = c := by
  rw [runs_iff]
  simp only [SubM.take]
  cases f F with
  | none => simp [liftOption_none]
  | some y => simp [liftOption_some, eq_comm]

/-- SubM.lin: SubM.lin_run (OnBytes/Model/HideLaws.lean) in this file's form. -/
theorem sub_lin (f : Aff) (F G : Fork) (c c' : Ctx) :
    (SubM.lin f F).Yields c ((), G) c' ↔ F.lin f = some G ∧ c' = c := by
  rw [runs_iff]
  exact SubM.lin_run f F G c c'

/-! ## Loops -/

/-- A loop over a list that carries no value, with any step: what holds of no member and the state
and context at the start, and is kept by each run of the step, holds of the whole list and the state
and context at the end. Asked of a run of the step: that it goes on to the next member. The step may
use where in the list it stands. The text "for a in l do ..." of a routine is such a loop; its step
is the body followed by "go on", with the body's own steps in between. -/
theorem sub_forIn (f : α → PUnit → SubM (ForInStep PUnit)) (l0 : List α)
    (I : List α → Fork → Ctx → Prop)
    (step : ∀ pre a rest, l0 = pre ++ a :: rest → ∀ F c s G c', I pre F c →
      (f a PUnit.unit F).Yields c (s, G) c' →
        s = ForInStep.yield PUnit.unit ∧ I (pre ++ [a]) G c') :
    ∀ (l pre : List α) (F G : Fork) (c c' : Ctx), l0 = pre ++ l → I pre F c →
      ((forIn l PUnit.unit f : SubM PUnit) F).Yields c (PUnit.unit, G) c' → I l0 G c'
  | [], pre, F, G, c, c', e, hI, h => by
    rw [List.forIn_nil] at h
    obtain ⟨-, e1, e2⟩ := (sub_pure _ _ _ _ _ _).mp h
    rw [e, List.append_nil, e1, e2]
    exact hI
  | a :: l, pre, F, G, c, c', e, hI, h => by
    rw [List.forIn_cons] at h
    obtain ⟨s, F1, c1, h1, h2⟩ := (sub_bind _ _ _ _ _ _ _).mp h
    obtain ⟨es, hI'⟩ := step pre a l e F c s F1 c1 hI h1
    rw [es] at h2
    exact sub_forIn f l0 I step l (pre ++ [a]) F1 G c1 c' (by rw [e]; simp) hI' h2

/-- One call for each entry of an array, in the entries' order: the same law. -/
theorem sub_forM (body : α → SubM Unit) (as : Array α) (I : List α → Fork → Ctx → Prop)
    (step : ∀ pre a rest, as.toList = pre ++ a :: rest → ∀ F c G c', I pre F c →
      (body a F).Yields c ((), G) c' → I (pre ++ [a]) G c')
    {F G : Fork} {c c' : Ctx} (hI : I [] F c)
    (h : ((as.forM body : SubM Unit) F).Yields c ((), G) c') : I as.toList G c' := by
  have key : ∀ (l pre : List α) (F G : Fork) (c c' : Ctx), as.toList = pre ++ l → I pre F c →
      ((l.foldlM (fun (_ : Unit) a => body a) () : SubM Unit) F).Yields c ((), G) c' →
        I as.toList G c' := by
    intro l
    induction l with
    | nil =>
      intro pre F G c c' e hI h
      rw [List.foldlM_nil] at h
      obtain ⟨-, e1, e2⟩ := (sub_pure _ _ _ _ _ _).mp h
      rw [e, List.append_nil, e1, e2]
      exact hI
    | cons a l ih =>
      intro pre F G c c' e hI h
      rw [List.foldlM_cons] at h
      obtain ⟨_, F1, c1, h1, h2⟩ := (sub_bind _ _ _ _ _ _ _).mp h
      exact ih (pre ++ [a]) F1 G c1 c' (by rw [e]; simp) (step pre a l e F c F1 c1 hI h1) h2
  unfold Array.forM at h
  rw [← Array.foldlM_toList] at h
  exact key as.toList [] F G c c' rfl hI h

/-- A routine that is called on each member of a list and leaves state and context as they were: so
does the whole, and the results are as many as the members, each the routine's on its member. -/
theorem sub_mapM_list (f : α → SubM β) (P : α → β → Prop)
    (hf : ∀ a F c b G c', (f a F).Yields c (b, G) c' → G = F ∧ c' = c ∧ P a b) :
    ∀ (l : List α) (F G : Fork) (c c' : Ctx) (r : List β),
      ((l.mapM f : SubM (List β)) F).Yields c (r, G) c' → G = F ∧ c' = c ∧ List.Forall₂ P l r
  | [], F, G, c, c', r, h => by
    rw [List.mapM_nil] at h
    obtain ⟨e0, e1, e2⟩ := (sub_pure _ _ _ _ _ _).mp h
    rw [e0]
    exact ⟨e1, e2, List.Forall₂.nil⟩
  | a :: l, F, G, c, c', r, h => by
    rw [List.mapM_cons] at h
    obtain ⟨b, F1, c1, h1, h2⟩ := (sub_bind _ _ _ _ _ _ _).mp h
    obtain ⟨bs, F2, c2, h3, h4⟩ := (sub_bind _ _ _ _ _ _ _).mp h2
    obtain ⟨e0, e1, e2⟩ := (sub_pure _ _ _ _ _ _).mp h4
    obtain ⟨f1, f2, p1⟩ := hf a F c b F1 c1 h1
    obtain ⟨g1, g2, p2⟩ := sub_mapM_list f P hf l F1 F2 c1 c2 bs h3
    rw [e0]
    exact ⟨by rw [e1, g1, f1], by rw [e2, g2, f2], List.Forall₂.cons p1 p2⟩

/-! ## A routine inside a link -/

/-- LinkM.sub: the routine has run; what the link holds has not turned. -/
theorem link_sub (x : SubM α) (L L' : LinkCtx) (F G : Fork) (c c' : Ctx) (a : α) :
    (LinkM.sub x L F).Yields c ((a, L'), G) c' ↔ (x F).Yields c (a, G) c' ∧ L' = L := by
  unfold LinkM.sub
  rw [sub_bind]
  constructor
  · rintro ⟨b, F1, c1, h1, h2⟩
    obtain ⟨e1, rfl, rfl⟩ := (sub_pure _ _ _ _ _ _).mp h2
    cases e1
    exact ⟨h1, rfl⟩
  · rintro ⟨h1, rfl⟩
    exact ⟨a, G, c', h1, (sub_pure _ _ _ _ _ _).mpr ⟨rfl, rfl, rfl⟩⟩

#print axioms sub_bind
#print axioms sub_lift
#print axioms sub_mustAs
#print axioms sub_note
#print axioms sub_forIn
#print axioms sub_mapM_list
#print axioms sub_forM
#print axioms link_sub

end OnBytes.Road
