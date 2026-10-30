-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/HeadView.lean: a run on a view stays a run on a view, through the routine that hears
the output head's messages; and what that routine returns on a view.

Johnson/Road/HeadPoint.lean gathers in the record HeardFits what is used of what the routine hear
returns. One of the tests behind it is a test on values, which the dry run skips, and it runs after
the lookup's routine Forest.pad. This file shows that Forest.pad, run from a view's context, leaves
a view's context, so that the test counts, and concludes the record. It shows the same of all other
routines under hear, and the length of a point that is drawn on a view.

How. Routine by routine. At the bottom stand the laws on the channel's calls in a run on a view
(OnBytes/Iop/GroundLaws.lean: recvE_inv, close_inv). A routine that is made of steps which keep a
view keeps it. The two properties are classes, so that Lean finds the fact on each step by itself.

Main definitions: KeepsViewB (a block), KeepsView (a routine of a sub-proof).
Main theorems: view_step, view_end, view_ite, view_ite2 (how a routine is walked); keeps_foldlM;
instances, each a named theorem, for the calls and routines that the lookup uses, up to keeps_pad,
and for the routines of the head's messages, up to keeps_hear; closeAs_elems, trPoint_size,
point_size, PV_size (a point that was drawn on a view has the length that was asked);
heardFits_of_view: what hear returns in a run on a view, with no further hypothesis.

What is not claimed. Nothing on the dry run: whether a dry run stays dry is not looked at. Nothing
on what the routines show. That a routine succeeds is a hypothesis throughout. The program does not
import this file.
-/
import Johnson.Road.HeadPoint
import OnBytes.Slice.BlkBegin

set_option autoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.Hd.View

open OnBytes.Model (Reading Fork SubM)

/-- The block, run from a view's context, leaves a view's context. -/
class KeepsViewB {α : Type} (b : Blk α) : Prop where
  keep : ∀ c x c', c.ch.dry = false → b.Yields c x c' → c'.ch.dry = false

/-- The routine, run from a view's context, leaves a view's context. -/
class KeepsView {α : Type} (m : SubM α) : Prop where
  keep : ∀ F C a G D, C.ch.dry = false → Ok m F C a G D → D.ch.dry = false

section Blocks
variable {α β : Type}

/-- A block that only returns a value. -/
instance keepsB_pure (a : α) : KeepsViewB (pure a : Blk α) :=
  ⟨fun c x c' hd h => by
    obtain ⟨-, e⟩ := (Blk.yields_pure _ _ _ _).1 h
    rw [e]
    exact hd⟩

/-- One block after another, if each keeps a view. -/
instance keepsB_bind (b1 : Blk α) (b2 : α → Blk β) [KeepsViewB b1] [∀ a, KeepsViewB (b2 a)] :
    KeepsViewB (b1 >>= b2) :=
  ⟨fun c y c2 hd h => by
    obtain ⟨x, c1, h1, h2⟩ := (Blk.yields_bind _ _ _ _ _).1 h
    exact KeepsViewB.keep _ _ _ (KeepsViewB.keep _ _ _ hd h1) h2⟩

/-- A choice between two blocks that keep a view. -/
instance keepsB_ite (p : Prop) [Decidable p] (a b : Blk α) [KeepsViewB a] [KeepsViewB b] :
    KeepsViewB (if p then a else b) := by
  split <;> infer_instance

/-- Blk.must keeps a view. -/
instance keepsB_must (b : Bool) : KeepsViewB (Blk.must b) :=
  ⟨fun c x c' hd h => by
    obtain ⟨-, e⟩ := (Blk.yields_must b c c').1 h
    rw [e]
    exact hd⟩

/-- Blk.get keeps a view. -/
instance keepsB_get (x : Option α) : KeepsViewB (Blk.get x) :=
  ⟨fun c a c' hd h => by
    obtain ⟨-, e⟩ := (Blk.yields_get x a c c').1 h
    rw [e]
    exact hd⟩

/-- A block that fails leaves nothing. -/
instance keepsB_fail (n : String) : KeepsViewB (Blk.fail n : Blk α) :=
  ⟨fun c x c' _ h => by
    have k : (Except.error { name := n } : Except Failure (α × Ctx)) = .ok (x, c') :=
      (Blk.yields_iff _ _ _ _).1 h
    cases k⟩

/-- mustAs keeps a view. -/
instance keepsB_mustAs (n : String) (b : Bool) : KeepsViewB (Model.mustAs n b) :=
  ⟨fun c x c' hd h => by
    obtain ⟨-, e⟩ := (mustAs_ok n b c c' x).1 ((Blk.yields_iff _ _ _ _).1 h)
    rw [e]
    exact hd⟩

/-- Receiving an element: by the law recvE_inv. -/
instance keepsB_recvE : KeepsViewB Blk.recvE :=
  ⟨fun c x c' hd h => by
    obtain ⟨_, _, _, _, _, _, s⟩ := Blk.recvE_inv x c c' hd h
    rw [s.dry]
    exact hd⟩

/-- Closing a round: by the law close_inv. -/
instance keepsB_close (name : String) (kind : Fmt.Kind) (nz : ℕ) :
    KeepsViewB (Blk.close name kind nz) :=
  ⟨fun c d c' hd h => by
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, k, _⟩ :=
      Blk.close_inv name kind nz d c c' hd h
    exact k⟩

/-- Blk.lastEntry keeps a view. -/
instance keepsB_lastEntry : KeepsViewB Blk.lastEntry :=
  ⟨fun c e c' hd h => by
    obtain ⟨-, k⟩ := (Slice.yields_lastEntry e c c').1 h
    rw [k]
    exact hd⟩

/-- closeAs keeps a view. -/
instance keepsB_closeAs (name : String) (kind : Fmt.Kind) (a b c : ℕ) :
    KeepsViewB (Model.closeAs name kind a b c) := by
  unfold Model.closeAs
  infer_instance

/-- oneOf keeps a view. -/
instance keepsB_oneOf (d : Fmt.Drawn) : KeepsViewB (Model.oneOf d) := by
  unfold Model.oneOf
  split <;> infer_instance

/-- noBatching keeps a view. -/
instance keepsB_noBatching (r : Model.RoundName) : KeepsViewB (Model.noBatching r) := by
  unfold Model.noBatching
  infer_instance

/-- trReadLoop keeps a view. -/
theorem keepsB_trReadLoop : ∀ (n : ℕ) (a : Array E), KeepsViewB (Model.trReadLoop n a)
  | 0, a => by
    unfold Model.trReadLoop
    infer_instance
  | n + 1, a => by
    unfold Model.trReadLoop
    haveI := fun a => keepsB_trReadLoop n a
    infer_instance

/-- trRead keeps a view. -/
instance keepsB_trRead (n : ℕ) : KeepsViewB (Model.trRead n) := keepsB_trReadLoop n _

/-- trSum keeps a view. -/
instance keepsB_trSum : KeepsViewB Model.trSum := keepsB_recvE

/-- trAnswer keeps a view. -/
instance keepsB_trAnswer (r : Model.RoundName) : KeepsViewB (Model.trAnswer r) := by
  unfold Model.trAnswer
  infer_instance

/-- trAnswerNotZero keeps a view. -/
instance keepsB_trAnswerNotZero (r : Model.RoundName) :
    KeepsViewB (Model.trAnswerNotZero r) := by
  unfold Model.trAnswerNotZero
  infer_instance

/-- trEmpty keeps a view. -/
instance keepsB_trEmpty (r : Model.RoundName) : KeepsViewB (Model.trEmpty r) := by
  unfold Model.trEmpty
  infer_instance

/-- trPoint keeps a view. -/
instance keepsB_trPoint (r : Model.RoundName) (n : ℕ) : KeepsViewB (Model.trPoint r n) := by
  unfold Model.trPoint
  infer_instance

/-- roundDraw keeps a view. -/
instance keepsB_roundDraw : KeepsViewB Model.roundDraw := keepsB_trAnswer _

end Blocks

section Routines
variable {α β : Type}

/-- A routine that only returns a value. -/
instance keeps_pure (a : α) : KeepsView (pure a : SubM α) :=
  ⟨fun F C b G D hd h => by
    obtain ⟨-, -, e⟩ := pure_ok h
    rw [e]
    exact hd⟩

/-- One routine after another, if each keeps a view. -/
instance keeps_bind (m : SubM α) (f : α → SubM β) [KeepsView m] [∀ a, KeepsView (f a)] :
    KeepsView (m >>= f) :=
  ⟨fun F C b G D hd h => by
    obtain ⟨a, F1, C1, h1, h2⟩ := bind_ok h
    exact KeepsView.keep _ _ _ _ _ (KeepsView.keep _ _ _ _ _ hd h1) h2⟩

/-- A choice between two routines that keep a view. -/
instance keeps_ite (p : Prop) [Decidable p] (a b : SubM α) [KeepsView a] [KeepsView b] :
    KeepsView (if p then a else b) := by
  split <;> infer_instance

/-- A block that keeps a view, run inside a routine. -/
instance keeps_liftM (b : Blk α) [KeepsViewB b] : KeepsView (liftM b : SubM α) :=
  ⟨fun F C a G D hd h =>
    KeepsViewB.keep C a D hd ((Blk.yields_iff _ _ _ _).2 ((ok_lift b F G C D a).1 h).1)⟩

/-- The same, where the block is lifted by StateT.lift. -/
instance keeps_lift (b : Blk α) [KeepsViewB b] : KeepsView (StateT.lift b : SubM α) :=
  ⟨fun F C a G D hd h =>
    KeepsViewB.keep C a D hd ((Blk.yields_iff _ _ _ _).2 ((ok_lift b F G C D a).1 h).1)⟩

/-- A step on the state does not touch the context. -/
instance keeps_change (f : Fork → Option Fork) : KeepsView (SubM.change f) :=
  ⟨fun F C a G D hd h => by
    have h' : (liftM ((f F).map fun H => (((), H), C)) :
        Except Failure ((Unit × Fork) × Ctx)) = .ok ((a, G), D) := h
    cases hf : f F with
    | none =>
      rw [hf] at h'
      cases h'
    | some H =>
      rw [hf] at h'
      cases h'
      exact hd⟩

/-- A step on the state that returns a value does not touch the context. -/
instance keeps_take (f : Fork → Option (α × Fork)) : KeepsView (SubM.take f) :=
  ⟨fun F C a G D hd h => by
    have h' : (liftM ((f F).map fun x => (x, C)) :
        Except Failure ((α × Fork) × Ctx)) = .ok ((a, G), D) := h
    cases hf : f F with
    | none =>
      rw [hf] at h'
      cases h'
    | some H =>
      rw [hf] at h'
      cases h'
      exact hd⟩

/-- Reading a value off the state does not touch the context. -/
instance keeps_ask (f : Fork → Option α) : KeepsView (SubM.ask f) :=
  ⟨fun F C a G D hd h => by
    have h' : (liftM ((f F).map fun x => ((x, F), C)) :
        Except Failure ((α × Fork) × Ctx)) = .ok ((a, G), D) := h
    cases hf : f F with
    | none =>
      rw [hf] at h'
      cases h'
    | some H =>
      rw [hf] at h'
      cases h'
      exact hd⟩

/-- SubM.must keeps a view. -/
instance keeps_must (b : Bool) : KeepsView (SubM.must b) := by
  unfold SubM.must
  infer_instance

/-- SubM.get keeps a view. -/
instance keeps_get (x : Option α) : KeepsView (SubM.get x) := by
  unfold SubM.get
  infer_instance

/-- SubM.read keeps a view. -/
instance keeps_read (n : ℕ) : KeepsView (SubM.read n) := by
  unfold SubM.read
  infer_instance

/-- SubM.readSum keeps a view. -/
instance keeps_readSum : KeepsView SubM.readSum := by
  unfold SubM.readSum
  infer_instance

/-- SubM.answer keeps a view. -/
instance keeps_answer (r : Model.RoundName) : KeepsView (SubM.answer r) := by
  unfold SubM.answer
  infer_instance

/-- SubM.point keeps a view. -/
instance keeps_point (r : Model.RoundName) (n : ℕ) : KeepsView (SubM.point r n) := by
  unfold SubM.point
  infer_instance

/-- SubM.empty keeps a view. -/
instance keeps_empty (r : Model.RoundName) : KeepsView (SubM.empty r) := by
  unfold SubM.empty
  infer_instance

/-- SubM.slots keeps a view. -/
instance keeps_slots (n : ℕ) : KeepsView (SubM.slots n) := by
  unfold SubM.slots
  infer_instance

/-- SubM.slot keeps a view. -/
instance keeps_slot : KeepsView SubM.slot := by
  unfold SubM.slot
  infer_instance

/-- SubM.takeSlots keeps a view. -/
instance keeps_takeSlots (n : ℕ) : KeepsView (SubM.takeSlots n) := by
  unfold SubM.takeSlots
  infer_instance

/-- SubM.shown keeps a view. -/
instance keeps_shown (j : ℕ) : KeepsView (SubM.shown j) := by
  unfold SubM.shown
  infer_instance

/-- SubM.publicPart keeps a view. -/
instance keeps_publicPart (a : Model.Aff) : KeepsView (SubM.publicPart a) := by
  unfold SubM.publicPart
  infer_instance

/-- SubM.owe keeps a view. -/
instance keeps_owe (w : String) : KeepsView (SubM.owe w) := by
  unfold SubM.owe
  infer_instance

/-- A fold over a list, if every step keeps the view. -/
theorem keeps_foldlM {σ : Type} (f : σ → β → SubM σ) (hf : ∀ s a, KeepsView (f s a)) :
    ∀ (l : List β) (s : σ), KeepsView (l.foldlM f s)
  | [], s => by
    rw [List.foldlM_nil]
    infer_instance
  | a :: l, s => by
    rw [List.foldlM_cons]
    haveI := hf s a
    haveI := fun s' => keeps_foldlM f hf l s'
    infer_instance

/-- The same as an instance. -/
instance keeps_fold {σ : Type} (f : σ → β → SubM σ) [hf : ∀ s a, KeepsView (f s a)] (l : List β)
    (s : σ) : KeepsView (l.foldlM f s) := keeps_foldlM f hf l s

/-- One step of a routine on a view, and what follows it. -/
theorem view_step {m : SubM α} [KeepsView m] {f : α → SubM β} {F G : Fork} {C D : Ctx} {b : β}
    (hd : C.ch.dry = false) (h : Ok (m >>= f) F C b G D) :
    ∃ a F1 C1, C1.ch.dry = false ∧ Ok (f a) F1 C1 b G D := by
  obtain ⟨a, F1, C1, h1, h2⟩ := bind_ok h
  exact ⟨a, F1, C1, KeepsView.keep _ _ _ _ _ hd h1, h2⟩

/-- A routine's last step on a view: it returns a value. -/
theorem view_end {a b : α} {F G : Fork} {C D : Ctx} (hd : C.ch.dry = false)
    (h : Ok (pure a : SubM α) F C b G D) : D.ch.dry = false :=
  KeepsView.keep _ _ _ _ _ hd h

/-- Either of two steps, chosen by a condition, and one continuation. -/
theorem view_ite {p : Prop} [Decidable p] {x x' : SubM α} [KeepsView x] [KeepsView x']
    {jp : α → SubM β} {F G : Fork} {C D : Ctx} {b : β} (hd : C.ch.dry = false)
    (h : Ok (if p then x >>= jp else x' >>= jp) F C b G D) :
    ∃ a F1 C1, C1.ch.dry = false ∧ Ok (jp a) F1 C1 b G D := by
  by_cases hp : p
  · rw [if_pos hp] at h
    exact view_step hd h
  · rw [if_neg hp] at h
    exact view_step hd h

/-- The same where the first branch has two steps. -/
theorem view_ite2 {γ : Type} {p : Prop} [Decidable p] {x : SubM γ} [KeepsView x]
    {g : γ → SubM α} [∀ c, KeepsView (g c)] {x' : SubM α} [KeepsView x'] {jp : α → SubM β}
    {F G : Fork} {C D : Ctx} {b : β} (hd : C.ch.dry = false)
    (h : Ok (if p then x >>= fun c => g c >>= jp else x' >>= jp) F C b G D) :
    ∃ a F1 C1, C1.ch.dry = false ∧ Ok (jp a) F1 C1 b G D := by
  by_cases hp : p
  · rw [if_pos hp] at h
    obtain ⟨c, _, _, hd, h⟩ := view_step hd h
    exact view_step hd h
  · rw [if_neg hp] at h
    exact view_step hd h

end Routines

/-- pscBeginAt keeps a view. -/
instance keeps_pscBeginAt (t : E) : KeepsView (Model.pscBeginAt t) := by
  unfold Model.pscBeginAt
  infer_instance

/-- pscBegin keeps a view. -/
instance keeps_pscBegin (C : Model.Aff) : KeepsView (Model.pscBegin C) := by
  unfold Model.pscBegin
  infer_instance

/-- pscRound keeps a view, if the block that draws its challenge does. -/
instance keeps_pscRound (p : Model.Psc) (w : OnBytes.Psc.Weight) (draw : Blk E)
    [KeepsViewB draw] : KeepsView (Model.pscRound p w draw) :=
  ⟨fun F C a G D hd h => by
    unfold Model.pscRound at h
    obtain ⟨_, _, _, hd, h⟩ := view_step hd h
    obtain ⟨_, _, _, hd, h⟩ := view_step hd h
    obtain ⟨_, _, _, hd, h⟩ := view_step hd h
    obtain ⟨_, _, _, hd, h⟩ := view_step hd h
    obtain ⟨_, _, _, hd, h⟩ := view_step hd h
    exact view_end hd h⟩

/-- roundIn keeps a view. -/
instance keeps_roundIn (form : Model.RoundForm) (p : Model.Psc) (z : E) (degree : ℕ) :
    KeepsView (Model.roundIn form p z degree) := by
  unfold Model.roundIn
  infer_instance

/-- pscEnds keeps a view. -/
instance keeps_pscEnds (p : Model.Psc) (dY n : ℕ) : KeepsView (Model.pscEnds p dY n) :=
  ⟨fun F C a G D hd h => by
    unfold Model.pscEnds at h
    obtain ⟨_, _, _, hd, h⟩ := view_step hd h
    obtain ⟨⟨beta, p'⟩, _, _, hd, h⟩ := view_step hd h
    obtain ⟨_, _, _, hd, h⟩ := view_step hd h
    obtain ⟨_, _, _, hd, h⟩ := view_step hd h
    obtain ⟨_, _, _, hd, h⟩ := view_step hd h
    obtain ⟨_, _, _, hd, h⟩ := view_step hd h
    obtain ⟨_, _, _, hd, h⟩ := view_step hd h
    exact view_end hd h⟩

/-- pscRow keeps a view. -/
instance keeps_pscRow (p : Model.Psc) (S0 : E) (kept : Model.Aff) :
    KeepsView (Model.pscRow p S0 kept) := by
  unfold Model.pscRow
  infer_instance

/-- levelRounds keeps a view. -/
theorem keeps_levelRounds (mu : ℕ) (rho : Array E) : ∀ (order : List ℕ) (r : Array E)
    (p : Model.Psc), KeepsView (Model.levelRounds mu rho order r p)
  | [], r, p => by
    unfold Model.levelRounds
    infer_instance
  | v :: order, r, p =>
    ⟨fun F C a G D hd h => by
      unfold Model.levelRounds at h
      obtain ⟨_, _, _, hd, h⟩ := view_step hd h
      obtain ⟨⟨x, p'⟩, _, _, hd, h⟩ := view_step hd h
      exact (keeps_levelRounds mu rho order _ _).keep _ _ _ _ _ hd h⟩

/-- The same as an instance. -/
instance keeps_levelRounds' (mu : ℕ) (rho : Array E) (order : List ℕ) (r : Array E)
    (p : Model.Psc) : KeepsView (Model.levelRounds mu rho order r p) :=
  keeps_levelRounds mu rho order r p

/-- levelIn keeps a view. -/
instance keeps_levelIn (mu : ℕ) (rho : Array E) (C : Model.Aff) (order : List ℕ) :
    KeepsView (Model.levelIn mu rho C order) :=
  ⟨fun F C0 a G D hd h => by
    unfold Model.levelIn at h
    obtain ⟨_, _, _, hd, h⟩ := view_step hd h
    obtain ⟨_, _, _, hd, h⟩ := view_step hd h
    obtain ⟨⟨r, p⟩, _, _, hd, h⟩ := view_step hd h
    obtain ⟨⟨sL, p'⟩, _, _, hd, h⟩ := view_step hd h
    obtain ⟨_, _, _, hd, h⟩ := view_step hd h
    obtain ⟨_, _, _, hd, h⟩ := view_step hd h
    obtain ⟨_, _, _, hd, h⟩ := view_step hd h
    obtain ⟨⟨row, p''⟩, _, _, hd, h⟩ := view_step hd h
    exact view_end hd h⟩

/-- roundsIn keeps a view. -/
instance keeps_roundsIn (form : Model.RoundForm) (p : Model.Psc) (zs : List (E × ℕ)) :
    KeepsView (Model.roundsIn form p zs) := by
  unfold Model.roundsIn
  exact keeps_foldlM _ (fun s z =>
    ⟨fun F C a G D hd h => by
      obtain ⟨⟨r, q⟩, _, _, hd, h⟩ := view_step hd h
      exact view_end hd h⟩) _ _

/-- Forest.draws keeps a view. -/
instance keeps_draws (h0 : Model.Forest.Shape) : KeepsView (Model.Forest.draws h0) :=
  ⟨fun F C a G D hd h => by
    unfold Model.Forest.draws at h
    obtain ⟨_, _, _, hd, h⟩ := view_ite hd h
    obtain ⟨_, _, _, hd, h⟩ := view_step hd h
    exact view_end hd h⟩

/-- Forest.tieStep keeps a view. -/
instance keeps_tieStep (a : E) (s : Model.Forest.TieStep) (j : ℕ) :
    KeepsView (Model.Forest.tieStep a s j) :=
  ⟨fun F C x G D hd h => by
    unfold Model.Forest.tieStep at h
    obtain ⟨_, _, _, hd, h⟩ := view_step hd h
    obtain ⟨⟨first, p⟩, _, _, hd, h⟩ := view_step hd h
    obtain ⟨_, _, _, hd, h⟩ := view_step hd h
    obtain ⟨_, _, _, hd, h⟩ := view_step hd h
    obtain ⟨_, _, _, hd, h⟩ := view_ite2 hd h
    obtain ⟨⟨row, p'⟩, _, _, hd, h⟩ := view_step hd h
    exact view_end hd h⟩

/-- Forest.tie keeps a view. -/
instance keeps_tie (a : E) : KeepsView (Model.Forest.tie a) :=
  ⟨fun F C x G D hd h => by
    unfold Model.Forest.tie at h
    obtain ⟨_, _, _, hd, h⟩ := view_step hd h
    obtain ⟨_, _, _, hd, h⟩ := view_step hd h
    exact view_end hd h⟩

/-- Forest.level keeps a view. -/
instance keeps_level (s : Model.Forest.Descent) (mu : ℕ) (order : List ℕ) :
    KeepsView (Model.Forest.level s mu order) :=
  ⟨fun F C x G D hd h => by
    unfold Model.Forest.level at h
    obtain ⟨_, _, _, hd, h⟩ := view_step hd h
    exact view_end hd h⟩

/-- **The lookup's routine keeps a run on a view a run on a view.** -/
instance keeps_pad (calls : Array Model.Call) (pub : Array ℕ) (lid : ℕ) :
    KeepsView (Model.Forest.pad calls pub lid) :=
  ⟨fun F C g G D hd h => by
    unfold Model.Forest.pad at h
    obtain ⟨h0, _, _, hd, h⟩ := view_step hd h
    obtain ⟨_, _, _, hd, h⟩ := view_step hd h
    obtain ⟨slot0, _, _, hd, h⟩ := view_step hd h
    obtain ⟨o1, _, _, hd, h⟩ := view_step hd h
    obtain ⟨o2, _, _, hd, h⟩ := view_step hd h
    obtain ⟨o3, _, _, hd, h⟩ := view_step hd h
    obtain ⟨⟨theta, alpha, a⟩, _, _, hd, h⟩ := view_step hd h
    obtain ⟨t, _, _, hd, h⟩ := view_step hd h
    obtain ⟨keys, _, _, hd, h⟩ := view_step hd h
    obtain ⟨table, _, _, hd, h⟩ := view_step hd h
    obtain ⟨_, _, _, hd, h⟩ := view_step hd h
    obtain ⟨leaves, _, _, hd, h⟩ := view_step hd h
    obtain ⟨⟨zb0, leaves'⟩, _, _, hd, h⟩ := view_step hd h
    obtain ⟨r5, _, _, hd, h⟩ := view_step hd h
    obtain ⟨bits, _, _, hd, h⟩ := view_step hd h
    obtain ⟨⟨zb1, bits'⟩, _, _, hd, h⟩ := view_step hd h
    obtain ⟨⟨sBit, bits''⟩, _, _, hd, h⟩ := view_step hd h
    obtain ⟨vBit, _, _, hd, h⟩ := view_step hd h
    obtain ⟨⟨bitsRow, p'⟩, _, _, hd, h⟩ := view_step hd h
    obtain ⟨s, _, _, hd, h⟩ := view_step hd h
    obtain ⟨_, _, _, hd, h⟩ := view_step hd h
    obtain ⟨_, _, _, hd, h⟩ := view_step hd h
    obtain ⟨_, _, _, hd, h⟩ := view_step hd h
    exact view_end hd h⟩

/-! ## The routines of the head's messages -/

/-- testAs keeps a view. -/
instance keepsB_testAs (n : String) (b : Bool) : KeepsViewB (Model.testAs n b) :=
  ⟨fun c x c' hd h => by
    obtain ⟨-, e⟩ := testAs_view n b c c' x hd ((Blk.yields_iff _ _ _ _).1 h)
    rw [e]
    exact hd⟩

/-- Head.held keeps a view. -/
instance keepsB_held {α : Type} (x : Except String α) : KeepsViewB (Model.Head.held x) :=
  ⟨fun c a c' hd h => by
    obtain ⟨-, e⟩ := (held_ok x c c' a).1 ((Blk.yields_iff _ _ _ _).1 h)
    rw [e]
    exact hd⟩

/-- Head.getAs keeps a view. -/
instance keepsB_getAs {α : Type} (n : String) (x : Option α) :
    KeepsViewB (Model.Head.getAs n x) :=
  ⟨fun c a c' hd h => by
    obtain ⟨-, e⟩ := (getAs_ok n x c c' a).1 ((Blk.yields_iff _ _ _ _).1 h)
    rw [e]
    exact hd⟩

/-- Blk.note keeps a view. -/
instance keepsB_note (w : String) (v : E) : KeepsViewB (Blk.note w v) :=
  ⟨fun c x c' hd h => by
    have s := Blk.yields_note w v c c' h
    rw [s.ch]
    exact hd⟩

/-- Blk.requireRows keeps a view. -/
instance keepsB_requireRows (rows : ℕ) : KeepsViewB (Blk.requireRows rows) :=
  ⟨fun c x c' hd h => by
    obtain ⟨_, _, _, e⟩ := Slice.requireRows_inv rows c c' hd h
    rw [e]
    exact hd⟩

/-- trBatchOpen keeps a view. -/
instance keepsB_trBatchOpen : KeepsViewB Model.trBatchOpen := by
  unfold Model.trBatchOpen
  infer_instance

/-- trBatchRows keeps a view. -/
instance keepsB_trBatchRows (rows : ℕ) : KeepsViewB (Model.trBatchRows rows) :=
  keepsB_requireRows rows

/-- trBatch keeps a view. -/
instance keepsB_trBatch (rows : ℕ) : KeepsViewB (Model.trBatch rows) := by
  unfold Model.trBatch
  infer_instance

/-- SubM.batch keeps a view. -/
instance keeps_batch (rows : ℕ) : KeepsView (SubM.batch rows) := by
  unfold SubM.batch
  infer_instance

/-- SubM.claimsIn keeps a view. -/
instance keeps_claimsIn (n : ℕ) : KeepsView (SubM.claimsIn n) := by
  unfold SubM.claimsIn
  infer_instance

/-- Head.noteH keeps a view. -/
instance keeps_noteH (w : String) (v : E) : KeepsView (Model.Head.noteH w v) := by
  unfold Model.Head.noteH
  infer_instance

/-- Head.replyToken keeps a view. -/
instance keeps_replyToken (plain : Array E) (V : ℕ) :
    KeepsView (Model.Head.replyToken plain V) :=
  ⟨fun F C a G D hd h => by
    unfold Model.Head.replyToken at h
    obtain ⟨_, _, _, hd, h⟩ := view_step hd h
    obtain ⟨_, _, _, hd, h⟩ := view_step hd h
    exact view_end hd h⟩

/-- Head.mergedPoint keeps a view. -/
instance keeps_mergedPoint (h0 : Model.Head.Shape) (g1 : Model.Forest.Heard) :
    KeepsView (Model.Head.mergedPoint h0 g1) := by
  unfold Model.Head.mergedPoint
  infer_instance

/-- tscLoop keeps a view. -/
theorem keeps_tscLoop : ∀ (zs : List E) (r : Array E) (p : Model.Psc),
    KeepsView (Model.tscLoop zs r p)
  | [], r, p => by
    unfold Model.tscLoop
    infer_instance
  | z :: zs, r, p =>
    ⟨fun F C a G D hd h => by
      unfold Model.tscLoop at h
      obtain ⟨⟨x, p'⟩, _, _, hd, h⟩ := view_step hd h
      exact (keeps_tscLoop zs _ _).keep _ _ _ _ _ hd h⟩

/-- The same as an instance. -/
instance keeps_tscLoop' (zs : List E) (r : Array E) (p : Model.Psc) :
    KeepsView (Model.tscLoop zs r p) := keeps_tscLoop zs r p

/-- tscRounds keeps a view. -/
instance keeps_tscRounds (P : Array E) (lt : ℕ) : KeepsView (Model.tscRounds P lt) :=
  ⟨fun F C a G D hd h => by
    unfold Model.tscRounds at h
    obtain ⟨_, _, _, hd, h⟩ := view_step hd h
    obtain ⟨_, _, _, hd, h⟩ := view_step hd h
    obtain ⟨_, _, _, hd, h⟩ := view_step hd h
    obtain ⟨⟨r, p⟩, _, _, hd, h⟩ := view_step hd h
    exact view_end hd h⟩

/-- tscIn keeps a view. -/
instance keeps_tscIn (P : Array E) (lt shown dY : ℕ) : KeepsView (Model.tscIn P lt shown dY) :=
  ⟨fun F C a G D hd h => by
    unfold Model.tscIn at h
    obtain ⟨_, _, _, hd, h⟩ := view_step hd h
    obtain ⟨⟨sEnd, p⟩, _, _, hd, h⟩ := view_step hd h
    exact view_end hd h⟩

/-- Head.hearSquares keeps a view. -/
instance keeps_hearSquares (h0 : Model.Head.Shape) (PV : Array E) :
    KeepsView (Model.Head.hearSquares h0 PV) :=
  ⟨fun F C a G D hd h => by
    unfold Model.Head.hearSquares at h
    obtain ⟨_, _, _, hd, h⟩ := view_step hd h
    obtain ⟨_, _, _, hd, h⟩ := view_step hd h
    obtain ⟨_, _, _, hd, h⟩ := view_step hd h
    exact view_end hd h⟩

/-- Head.shownRun keeps a view. -/
instance keeps_shownRun (first n : ℕ) : KeepsView (Model.Head.shownRun first n) := by
  unfold Model.Head.shownRun
  exact keeps_foldlM _ (fun a j =>
    ⟨fun F C x G D hd h => by
      obtain ⟨_, _, _, hd, h⟩ := view_step hd h
      exact view_end hd h⟩) _ _

/-- Head.hearProducts keeps a view. -/
instance keeps_hearProducts (h0 : Model.Head.Shape) (PV : Array E) :
    KeepsView (Model.Head.hearProducts h0 PV) :=
  ⟨fun F C a G D hd h => by
    unfold Model.Head.hearProducts at h
    obtain ⟨_, _, _, hd, h⟩ := view_step hd h
    obtain ⟨_, _, _, hd, h⟩ := view_step hd h
    obtain ⟨_, _, _, hd, h⟩ := view_step hd h
    obtain ⟨_, _, _, hd, h⟩ := view_step hd h
    obtain ⟨⟨row, p⟩, _, _, hd, h⟩ := view_step hd h
    exact view_end hd h⟩

/-- Head.hearStream keeps a view. -/
instance keeps_hearStream (h0 : Model.Head.Shape) (zt : Array E) :
    KeepsView (Model.Head.hearStream h0 zt) :=
  ⟨fun F C a G D hd h => by
    unfold Model.Head.hearStream at h
    obtain ⟨_, _, _, hd, h⟩ := view_step hd h
    obtain ⟨_, _, _, hd, h⟩ := view_step hd h
    obtain ⟨_, _, _, hd, h⟩ := view_step hd h
    obtain ⟨⟨row, p⟩, _, _, hd, h⟩ := view_step hd h
    exact view_end hd h⟩

/-- Head.channelRounds keeps a view. -/
theorem keeps_channelRounds : ∀ (n : ℕ) (r : Array E) (p : Model.Psc),
    KeepsView (Model.Head.channelRounds n r p)
  | 0, r, p => by
    unfold Model.Head.channelRounds
    infer_instance
  | n + 1, r, p =>
    ⟨fun F C a G D hd h => by
      unfold Model.Head.channelRounds at h
      obtain ⟨⟨x, p'⟩, _, _, hd, h⟩ := view_step hd h
      exact (keeps_channelRounds n _ _).keep _ _ _ _ _ hd h⟩

/-- The same as an instance. -/
instance keeps_channelRounds' (n : ℕ) (r : Array E) (p : Model.Psc) :
    KeepsView (Model.Head.channelRounds n r p) := keeps_channelRounds n r p

/-- Head.hearLogits keeps a view. -/
instance keeps_hearLogits (h0 : Model.Head.Shape) (lam : ℕ) (zt : Array E) :
    KeepsView (Model.Head.hearLogits h0 lam zt) :=
  ⟨fun F C a G D hd h => by
    unfold Model.Head.hearLogits at h
    obtain ⟨_, _, _, hd, h⟩ := view_step hd h
    obtain ⟨⟨r, p⟩, _, _, hd, h⟩ := view_step hd h
    obtain ⟨⟨sEnd, p'⟩, _, _, hd, h⟩ := view_step hd h
    obtain ⟨_, _, _, hd, h⟩ := view_step hd h
    obtain ⟨_, _, _, hd, h⟩ := view_step hd h
    obtain ⟨⟨row, p''⟩, _, _, hd, h⟩ := view_step hd h
    exact view_end hd h⟩

/-- **The routine that hears the head's messages keeps a run on a view a run on a view.** -/
instance keeps_hear (h0 : Model.Head.Shape) (L : Model.Head.HL) (hp : Model.Head.HPlanH2)
    (cov : Model.Head.Covered) (plain : Array E) :
    KeepsView (Model.Head.hear h0 L hp cov plain) :=
  ⟨fun F C a G D hd h => by
    unfold Model.Head.hear at h
    obtain ⟨_, _, _, hd, h⟩ := view_step hd h
    obtain ⟨_, _, _, hd, h⟩ := view_step hd h
    obtain ⟨_, _, _, hd, h⟩ := view_step hd h
    obtain ⟨_, _, _, hd, h⟩ := view_step hd h
    obtain ⟨_, _, _, hd, h⟩ := view_step hd h
    obtain ⟨⟨sW, gp, wpl⟩, _, _, hd, h⟩ := view_step hd h
    obtain ⟨⟨sPv, omV, tV⟩, _, _, hd, h⟩ := view_step hd h
    obtain ⟨_, _, _, hd, h⟩ := view_step hd h
    obtain ⟨_, _, _, hd, h⟩ := view_step hd h
    obtain ⟨_, _, _, hd, h⟩ := view_step hd h
    obtain ⟨⟨tH, rs⟩, _, _, hd, h⟩ := view_step hd h
    obtain ⟨_, _, _, hd, h⟩ := view_step hd h
    obtain ⟨_, _, _, hd, h⟩ := view_step hd h
    obtain ⟨_, _, _, hd, h⟩ := view_step hd h
    obtain ⟨_, _, _, hd, h⟩ := view_step hd h
    obtain ⟨_, _, _, hd, h⟩ := view_step hd h
    obtain ⟨_, _, _, hd, h⟩ := view_step hd h
    obtain ⟨_, _, _, hd, h⟩ := view_step hd h
    obtain ⟨_, _, _, hd, h⟩ := view_step hd h
    obtain ⟨_, _, _, hd, h⟩ := view_step hd h
    obtain ⟨_, _, _, hd, h⟩ := view_step hd h
    obtain ⟨_, _, _, hd, h⟩ := view_step hd h
    obtain ⟨_, _, _, hd, h⟩ := view_step hd h
    exact view_end hd h⟩

/-! ## The length of a drawn point -/

/-- On a view, a round that closeAs has closed has drawn as many elements as the call asked. -/
theorem closeAs_elems {name : String} {kind : Fmt.Kind} {a b c : ℕ} {d : Fmt.Drawn} {C D : Ctx}
    (hd : C.ch.dry = false) (h : (Model.closeAs name kind a b c).Yields C d D) :
    d.elems.length = a := by
  unfold Model.closeAs at h
  obtain ⟨_, c1, h1, h⟩ := (Blk.yields_bind _ _ _ _ _).1 h
  obtain ⟨-, e1⟩ := (Blk.yields_must _ _ _).1 h1
  obtain ⟨d', c2, h2, h⟩ := (Blk.yields_bind _ _ _ _ _).1 h
  obtain ⟨e, c3, h3, h⟩ := (Blk.yields_bind _ _ _ _ _).1 h
  obtain ⟨_, c4, h4, h⟩ := (Blk.yields_bind _ _ _ _ _).1 h
  obtain ⟨ed, -⟩ := (Blk.yields_pure _ _ _ _).1 h
  rw [e1] at h2
  obtain ⟨e0, _, _, _, _, _, _, _, _, _, k7, _, _, _, _, k12, _⟩ :=
    Blk.close_inv _ _ _ _ _ _ hd h2
  obtain ⟨k, -⟩ := (Slice.yields_lastEntry _ _ _).1 h3
  rw [k12] at k
  have ee : e0 = e := Option.some.inj k
  have kb := ((Blk.yields_must _ _ _).1 h4).1
  have ka : e.drawE = a := eq_of_beq (and_true_split (and_true_split kb).1).1
  rw [ed, k7, ee, ka]

/-- On a view, the point that trPoint returns has as many coordinates as were asked. -/
theorem trPoint_size {r : Model.RoundName} {n : ℕ} {v : Array E} {C D : Ctx}
    (hd : C.ch.dry = false) (h : (Model.trPoint r n).Yields C v D) : v.size = n := by
  unfold Model.trPoint at h
  obtain ⟨_, c1, h1, h⟩ := (Blk.yields_bind _ _ _ _ _).1 h
  have hd1 : c1.ch.dry = false := KeepsViewB.keep _ _ _ hd h1
  obtain ⟨d, c2, h2, h⟩ := (Blk.yields_bind _ _ _ _ _).1 h
  obtain ⟨e, -⟩ := (Blk.yields_pure _ _ _ _).1 h
  rw [e]
  simpa using closeAs_elems hd1 h2

/-- The same for the routine of a sub-proof. -/
theorem point_size {r : Model.RoundName} {n : ℕ} {v : Array E} {F G : Fork} {C D : Ctx}
    (hd : C.ch.dry = false) (h : Ok (SubM.point r n) F C v G D) : v.size = n :=
  trPoint_size hd ((Blk.yields_iff _ _ _ _).2 ((ok_lift (Model.trPoint r n) F G C D v).1 h).1)

/-- **The norm's point over the positions has lt coordinates**, in a run on a view. -/
theorem PV_size {h : Model.Head.Shape} {L : Model.Head.HL} {hp : Model.Head.HPlanH2}
    {cov : Model.Head.Covered} {plain : Array E} {x : Model.Head.Heard} {F G : Fork} {C D : Ctx}
    (hd : C.ch.dry = false) (hx : Ok (Model.Head.hear h L hp cov plain) F C x G D) :
    x.PV.size = h.lt := by
  obtain ⟨yTok, F1, C1, F2, C2, g1, F3, C3, Zl, F4, C4, PV, F5, C5, sW, gp, wpl, F6, C6, sPv, omV,
    tV, F7, C7, qN, qH, tN, F8, C8, tH, rs, F9, C9, k1, k2, k3, k4, k5, -, -, -, -, -, -, -,
    rfl⟩ := hear_steps hx
  have hd1 : C1.ch.dry = false := KeepsView.keep _ _ _ _ _ hd k1
  have hd2 : C2.ch.dry = false := KeepsView.keep _ _ _ _ _ hd1 k2
  have hd3 : C3.ch.dry = false := KeepsView.keep _ _ _ _ _ hd2 k3
  have hd4 : C4.ch.dry = false := KeepsView.keep _ _ _ _ _ hd3 k4
  exact point_size hd4 k5

/-- **What hear returns in a run on a view.** -/
theorem heardFits_of_view {h : Model.Head.Shape} {L : Model.Head.HL} {hp : Model.Head.HPlanH2}
    {cov : Model.Head.Covered} {plain : Array E} {x : Model.Head.Heard} {F G : Fork} {C D : Ctx}
    (hd : C.ch.dry = false) (hx : Ok (Model.Head.hear h L hp cov plain) F C x G D) :
    HeardFits h L cov x := by
  obtain ⟨yTok, F1, C1, F2, C2, g1, F3, C3, Zl, F4, C4, PV, F5, C5, sW, gp, wpl, F6, C6, sPv, omV,
    tV, F7, C7, qN, qH, tN, F8, C8, tH, rs, F9, C9, k1, k2, k3, k4, -, -, -, hqN, hqH, -, -, -,
    rfl⟩ := hear_steps hx
  obtain ⟨hy, -, e1⟩ := replyToken_ok hd k1
  have hd1 : C1.ch.dry = false := by rw [e1]; exact hd
  have hd2 : C2.ch.dry = false := KeepsView.keep _ _ _ _ _ hd1 k2
  have hd3 : C3.ch.dry = false := KeepsView.keep _ _ _ _ _ hd2 k3
  obtain ⟨m1, m2⟩ := mergedPoint_ok hd3 k4
  exact ⟨⟨yTok, hy, rfl⟩, pad_ok k3, m1, m2, hqN, hqH⟩

#print axioms keeps_pad
#print axioms keeps_hear
#print axioms PV_size
#print axioms heardFits_of_view

end OnBytes.Road.Hd.View
