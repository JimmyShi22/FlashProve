-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/HeadKeeps.lean: the routines that receive the messages of the output head's sub-proof
keep the state's shape.

Johnson/Road/HeadWalk.lean shows that the routines which add the sub-proof's claims run from states
with one coefficient for each slot and with one number of columns for each array, if the first of
them does. This file shows the same for the routines that run before them and receive the prover's
messages: the lookup's routine Forest.pad, the sumchecks, hear, the merge's messages, and the draw
of the smallness test's matrix.

How. Routine by routine. A block that is lifted into a routine does not see the state. Of the steps
on the state these routines use five: setting up the slots, taking slots, putting hidden values
under slots, noting an owed claim, and reading. Each keeps the shape. A routine that is made of
steps which keep it keeps it. The property is a class, so that Lean finds the fact on each step by
itself.

Main definitions: KeepsS (the class form of Walk.Keeps).
Main theorems: ok_take, ok_ask; st_step, st_end, st_ite, st_ite2 (how a routine is walked);
keeps_foldlM; instances, each a named theorem, for the steps and routines up to keeps_pad,
keeps_hear, keeps_wsForkEnd and keeps_drawMatrixF.

What is not claimed. Nothing on what the routines show, on the context, or on the values that are
received. That a routine succeeds is a hypothesis throughout. The program does not import this file.
-/
import Johnson.Road.HeadWalk

set_option autoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.Hd.Parts

open OnBytes.Model (Fork SubM)

/-- From a state with one coefficient for each slot, the routine, if it succeeds, leaves a state
with one coefficient for each slot in which every array has as many columns as before. -/
class KeepsS {α : Type} (m : SubM α) : Prop where
  keep : ∀ F C a G D, F.LS.size = F.ns → Ok m F C a G D → Walk.Kept F G

section Routines
variable {α β : Type}

/-- A step on the state that may refuse and that returns a value. -/
theorem ok_take (f : Fork → Option (α × Fork)) (F G : Fork) (C D : Ctx) (a : α) :
    Ok (SubM.take f) F C a G D ↔ f F = some (a, G) ∧ D = C := by
  unfold Ok
  simp only [SubM.take]
  cases f F with
  | none => simp [liftOption_none]
  | some H => simp [liftOption_some, eq_comm]

/-- A value that is read off the state by a function that may refuse. -/
theorem ok_ask (f : Fork → Option α) (F G : Fork) (C D : Ctx) (a : α) :
    Ok (SubM.ask f) F C a G D ↔ f F = some a ∧ G = F ∧ D = C := by
  unfold Ok
  simp only [SubM.ask]
  cases f F with
  | none => simp [liftOption_none]
  | some y => simp [liftOption_some, eq_comm, and_assoc]

/-- A routine that leaves the state. -/
theorem keeps_of_stay {m : SubM α} (h : ∀ F C a G D, Ok m F C a G D → G = F) : KeepsS m :=
  ⟨Walk.keeps_of_leaves h⟩

/-- A routine that only returns a value. -/
instance keeps_pure (a : α) : KeepsS (pure a : SubM α) := ⟨Walk.keeps_pure a⟩

/-- One routine after another, if each keeps the state. -/
instance keeps_bind (m : SubM α) (f : α → SubM β) [hm : KeepsS m] [hf : ∀ a, KeepsS (f a)] :
    KeepsS (m >>= f) := ⟨Walk.keeps_bind hm.keep fun a => (hf a).keep⟩

/-- A choice between two routines that keep the state. -/
instance keeps_ite (p : Prop) [Decidable p] (a b : SubM α) [KeepsS a] [KeepsS b] :
    KeepsS (if p then a else b) := by
  split <;> infer_instance

/-- A block that is run inside a routine does not see the state. -/
instance keeps_liftM (b : Blk α) : KeepsS (liftM b : SubM α) := ⟨Walk.keeps_lift b⟩

/-- The same, where the block is lifted by StateT.lift. -/
instance keeps_lift (b : Blk α) : KeepsS (StateT.lift b : SubM α) := ⟨Walk.keeps_slift b⟩

/-- Reading a value off the state. -/
instance keeps_ask (f : Fork → Option α) : KeepsS (SubM.ask f) :=
  keeps_of_stay fun F C a G D h => ((ok_ask f F G C D a).mp h).2.1

/-- Putting a run of hidden values under slots. -/
instance keeps_hideRun (first : ℕ) (v : Array E) (k : E) :
    KeepsS (SubM.change fun F => F.hideRun first v k) := ⟨Walk.keeps_hideRun first v k⟩

/-- SubM.must keeps the state. -/
instance keeps_must (b : Bool) : KeepsS (SubM.must b) := by
  unfold SubM.must
  infer_instance

/-- SubM.get keeps the state. -/
instance keeps_get (x : Option α) : KeepsS (SubM.get x) := by
  unfold SubM.get
  infer_instance

/-- SubM.read keeps the state. -/
instance keeps_read (n : ℕ) : KeepsS (SubM.read n) := by
  unfold SubM.read
  infer_instance

/-- SubM.readSum keeps the state. -/
instance keeps_readSum : KeepsS SubM.readSum := by
  unfold SubM.readSum
  infer_instance

/-- SubM.answer keeps the state. -/
instance keeps_answer (r : Model.RoundName) : KeepsS (SubM.answer r) := by
  unfold SubM.answer
  infer_instance

/-- SubM.point keeps the state. -/
instance keeps_point (r : Model.RoundName) (n : ℕ) : KeepsS (SubM.point r n) := by
  unfold SubM.point
  infer_instance

/-- SubM.empty keeps the state. -/
instance keeps_empty (r : Model.RoundName) : KeepsS (SubM.empty r) := by
  unfold SubM.empty
  infer_instance

/-- SubM.trits keeps the state. -/
instance keeps_trits (a b : ℕ) : KeepsS (SubM.trits a b) := by
  unfold SubM.trits
  infer_instance

/-- SubM.batchOpen keeps the state. -/
instance keeps_batchOpen : KeepsS SubM.batchOpen := by
  unfold SubM.batchOpen
  infer_instance

/-- Setting up the slots: there is one coefficient for each, and the arrays stay. -/
instance keeps_slots (n : ℕ) : KeepsS (SubM.slots n) :=
  ⟨fun F C a G D _ h => by
    unfold SubM.slots at h
    rw [Walk.ok_change] at h
    have e : F.slots n = G := Option.some.inj h.1
    rw [← e]
    exact ⟨Fork.slots_sized F n, fun _ => rfl⟩⟩

/-- SubM.slot keeps the state. -/
instance keeps_slot : KeepsS SubM.slot := by
  unfold SubM.slot
  infer_instance

/-- Taking slots moves the number of the next free slot alone. -/
instance keeps_takeSlots (n : ℕ) : KeepsS (SubM.takeSlots n) :=
  ⟨fun F C a G D hs h => by
    unfold SubM.takeSlots at h
    rw [ok_take] at h
    have e : (F.next, { F with next := F.next + n }) = (a, G) := Option.some.inj h.1
    have e2 : { F with next := F.next + n } = G := congrArg Prod.snd e
    rw [← e2]
    exact ⟨hs, fun _ => rfl⟩⟩

/-- SubM.shown keeps the state. -/
instance keeps_shown (j : ℕ) : KeepsS (SubM.shown j) := by
  unfold SubM.shown
  infer_instance

/-- SubM.publicPart keeps the state. -/
instance keeps_publicPart (a : Model.Aff) : KeepsS (SubM.publicPart a) := by
  unfold SubM.publicPart
  infer_instance

/-- Noting an owed claim changes the list of owed claims alone. -/
instance keeps_owe (w : String) : KeepsS (SubM.owe w) :=
  ⟨fun F C a G D hs h => by
    unfold SubM.owe at h
    rw [ok_take] at h
    have e : F.owe w = (a, G) := Option.some.inj h.1
    have e2 : (F.owe w).2 = G := congrArg Prod.snd e
    rw [← e2]
    exact ⟨hs, fun _ => rfl⟩⟩

/-- A fold over a list, if every step keeps the state. -/
theorem keeps_foldlM {σ : Type} (f : σ → β → SubM σ) (hf : ∀ s a, KeepsS (f s a)) :
    ∀ (l : List β) (s : σ), KeepsS (l.foldlM f s)
  | [], s => by
    rw [List.foldlM_nil]
    infer_instance
  | a :: l, s => by
    rw [List.foldlM_cons]
    haveI := hf s a
    haveI := fun s' => keeps_foldlM f hf l s'
    infer_instance

/-- The same as an instance. -/
instance keeps_fold {σ : Type} (f : σ → β → SubM σ) [hf : ∀ s a, KeepsS (f s a)] (l : List β)
    (s : σ) : KeepsS (l.foldlM f s) := keeps_foldlM f hf l s

/-- One step of a routine, and what follows it. -/
theorem st_step {m : SubM α} [KeepsS m] {f : α → SubM β} {F0 F G : Fork} {C D : Ctx} {b : β}
    (hd : Walk.Kept F0 F) (h : Ok (m >>= f) F C b G D) :
    ∃ a F1 C1, Walk.Kept F0 F1 ∧ Ok (f a) F1 C1 b G D := by
  rw [ok_bind] at h
  obtain ⟨a, F1, C1, h1, h2⟩ := h
  exact ⟨a, F1, C1, hd.trans (KeepsS.keep _ _ _ _ _ hd.1 h1), h2⟩

/-- The end of a routine. -/
theorem st_end {a b : α} {F0 F G : Fork} {C D : Ctx} (hd : Walk.Kept F0 F)
    (h : Ok (pure a : SubM α) F C b G D) : Walk.Kept F0 G := by
  rw [ok_pure] at h
  rw [h.2.1]
  exact hd

/-- A choice between two routines, each followed by the same routine. -/
theorem st_ite {p : Prop} [Decidable p] {x x' : SubM α} [KeepsS x] [KeepsS x']
    {jp : α → SubM β} {F0 F G : Fork} {C D : Ctx} {b : β} (hd : Walk.Kept F0 F)
    (h : Ok (if p then x >>= jp else x' >>= jp) F C b G D) :
    ∃ a F1 C1, Walk.Kept F0 F1 ∧ Ok (jp a) F1 C1 b G D := by
  split at h
  · exact st_step hd h
  · exact st_step hd h

/-- The same, where the first of the two has two steps. -/
theorem st_ite2 {γ : Type} {p : Prop} [Decidable p] {x : SubM γ} [KeepsS x]
    {g : γ → SubM α} [∀ c, KeepsS (g c)] {x' : SubM α} [KeepsS x'] {jp : α → SubM β}
    {F0 F G : Fork} {C D : Ctx} {b : β} (hd : Walk.Kept F0 F)
    (h : Ok (if p then x >>= fun c => g c >>= jp else x' >>= jp) F C b G D) :
    ∃ a F1 C1, Walk.Kept F0 F1 ∧ Ok (jp a) F1 C1 b G D := by
  split at h
  · obtain ⟨c, F1, C1, hd1, h1⟩ := st_step hd h
    exact st_step hd1 h1
  · exact st_step hd h

end Routines

/-- pscBeginAt keeps the state. -/
instance keeps_pscBeginAt (t : E) : KeepsS (Model.pscBeginAt t) := by
  unfold Model.pscBeginAt
  infer_instance

/-- pscBegin keeps the state. -/
instance keeps_pscBegin (C : Model.Aff) : KeepsS (Model.pscBegin C) := by
  unfold Model.pscBegin
  infer_instance

/-- pscRound keeps the state. -/
instance keeps_pscRound (p : Model.Psc) (w : OnBytes.Psc.Weight) (draw : Blk E) :
    KeepsS (Model.pscRound p w draw) :=
  ⟨fun F C a G D hs h => by
    have hd := Walk.Kept.refl hs
    unfold Model.pscRound at h
    obtain ⟨_, _, _, hd, h⟩ := st_step hd h
    obtain ⟨_, _, _, hd, h⟩ := st_step hd h
    obtain ⟨_, _, _, hd, h⟩ := st_step hd h
    obtain ⟨_, _, _, hd, h⟩ := st_step hd h
    obtain ⟨_, _, _, hd, h⟩ := st_step hd h
    exact st_end hd h⟩

/-- roundIn keeps the state. -/
instance keeps_roundIn (form : Model.RoundForm) (p : Model.Psc) (z : E) (degree : ℕ) :
    KeepsS (Model.roundIn form p z degree) := by
  unfold Model.roundIn
  infer_instance

/-- pscEnds keeps the state. -/
instance keeps_pscEnds (p : Model.Psc) (dY n : ℕ) : KeepsS (Model.pscEnds p dY n) :=
  ⟨fun F C a G D hs h => by
    have hd := Walk.Kept.refl hs
    unfold Model.pscEnds at h
    obtain ⟨_, _, _, hd, h⟩ := st_step hd h
    obtain ⟨⟨beta, p'⟩, _, _, hd, h⟩ := st_step hd h
    obtain ⟨_, _, _, hd, h⟩ := st_step hd h
    obtain ⟨_, _, _, hd, h⟩ := st_step hd h
    obtain ⟨_, _, _, hd, h⟩ := st_step hd h
    obtain ⟨_, _, _, hd, h⟩ := st_step hd h
    obtain ⟨_, _, _, hd, h⟩ := st_step hd h
    exact st_end hd h⟩

/-- pscRow keeps the state. -/
instance keeps_pscRow (p : Model.Psc) (S0 : E) (kept : Model.Aff) :
    KeepsS (Model.pscRow p S0 kept) := by
  unfold Model.pscRow
  infer_instance

/-- levelRounds keeps the state. -/
theorem keeps_levelRounds (mu : ℕ) (rho : Array E) : ∀ (order : List ℕ) (r : Array E)
    (p : Model.Psc), KeepsS (Model.levelRounds mu rho order r p)
  | [], r, p => by
    unfold Model.levelRounds
    infer_instance
  | v :: order, r, p =>
    ⟨fun F C a G D hs h => by
      have hd := Walk.Kept.refl hs
      unfold Model.levelRounds at h
      obtain ⟨_, _, _, hd, h⟩ := st_step hd h
      obtain ⟨⟨x, p'⟩, _, _, hd, h⟩ := st_step hd h
      exact hd.trans ((keeps_levelRounds mu rho order _ _).keep _ _ _ _ _ hd.1 h)⟩

/-- The same as an instance. -/
instance keeps_levelRounds' (mu : ℕ) (rho : Array E) (order : List ℕ) (r : Array E)
    (p : Model.Psc) : KeepsS (Model.levelRounds mu rho order r p) :=
  keeps_levelRounds mu rho order r p

/-- levelIn keeps the state. -/
instance keeps_levelIn (mu : ℕ) (rho : Array E) (C : Model.Aff) (order : List ℕ) :
    KeepsS (Model.levelIn mu rho C order) :=
  ⟨fun F C0 a G D hs h => by
    have hd := Walk.Kept.refl hs
    unfold Model.levelIn at h
    obtain ⟨_, _, _, hd, h⟩ := st_step hd h
    obtain ⟨_, _, _, hd, h⟩ := st_step hd h
    obtain ⟨⟨r, p⟩, _, _, hd, h⟩ := st_step hd h
    obtain ⟨⟨sL, p'⟩, _, _, hd, h⟩ := st_step hd h
    obtain ⟨_, _, _, hd, h⟩ := st_step hd h
    obtain ⟨_, _, _, hd, h⟩ := st_step hd h
    obtain ⟨_, _, _, hd, h⟩ := st_step hd h
    obtain ⟨⟨row, p''⟩, _, _, hd, h⟩ := st_step hd h
    exact st_end hd h⟩

/-- roundsIn keeps the state. -/
instance keeps_roundsIn (form : Model.RoundForm) (p : Model.Psc) (zs : List (E × ℕ)) :
    KeepsS (Model.roundsIn form p zs) := by
  unfold Model.roundsIn
  exact keeps_foldlM _ (fun s z =>
    ⟨fun F C a G D hs h => by
      have hd := Walk.Kept.refl hs
      obtain ⟨⟨r, q⟩, _, _, hd, h⟩ := st_step hd h
      exact st_end hd h⟩) _ _

/-- Forest.draws keeps the state. -/
instance keeps_draws (h0 : Model.Forest.Shape) : KeepsS (Model.Forest.draws h0) :=
  ⟨fun F C a G D hs h => by
    have hd := Walk.Kept.refl hs
    unfold Model.Forest.draws at h
    obtain ⟨_, _, _, hd, h⟩ := st_ite hd h
    obtain ⟨_, _, _, hd, h⟩ := st_step hd h
    exact st_end hd h⟩

/-- Forest.tieStep keeps the state. -/
instance keeps_tieStep (a : E) (s : Model.Forest.TieStep) (j : ℕ) :
    KeepsS (Model.Forest.tieStep a s j) :=
  ⟨fun F C x G D hs h => by
    have hd := Walk.Kept.refl hs
    unfold Model.Forest.tieStep at h
    obtain ⟨_, _, _, hd, h⟩ := st_step hd h
    obtain ⟨⟨first, p⟩, _, _, hd, h⟩ := st_step hd h
    obtain ⟨_, _, _, hd, h⟩ := st_step hd h
    obtain ⟨_, _, _, hd, h⟩ := st_step hd h
    obtain ⟨_, _, _, hd, h⟩ := st_ite2 hd h
    obtain ⟨⟨row, p'⟩, _, _, hd, h⟩ := st_step hd h
    exact st_end hd h⟩

/-- Forest.tie keeps the state. -/
instance keeps_tie (a : E) : KeepsS (Model.Forest.tie a) :=
  ⟨fun F C x G D hs h => by
    have hd := Walk.Kept.refl hs
    unfold Model.Forest.tie at h
    obtain ⟨_, _, _, hd, h⟩ := st_step hd h
    obtain ⟨_, _, _, hd, h⟩ := st_step hd h
    exact st_end hd h⟩

/-- Forest.level keeps the state. -/
instance keeps_level (s : Model.Forest.Descent) (mu : ℕ) (order : List ℕ) :
    KeepsS (Model.Forest.level s mu order) :=
  ⟨fun F C x G D hs h => by
    have hd := Walk.Kept.refl hs
    unfold Model.Forest.level at h
    obtain ⟨_, _, _, hd, h⟩ := st_step hd h
    exact st_end hd h⟩

/-- The lookup's routine keeps the state. -/
instance keeps_pad (calls : Array Model.Call) (pub : Array ℕ) (lid : ℕ) :
    KeepsS (Model.Forest.pad calls pub lid) :=
  ⟨fun F C g G D hs h => by
    have hd := Walk.Kept.refl hs
    unfold Model.Forest.pad at h
    obtain ⟨h0, _, _, hd, h⟩ := st_step hd h
    obtain ⟨_, _, _, hd, h⟩ := st_step hd h
    obtain ⟨slot0, _, _, hd, h⟩ := st_step hd h
    obtain ⟨o1, _, _, hd, h⟩ := st_step hd h
    obtain ⟨o2, _, _, hd, h⟩ := st_step hd h
    obtain ⟨o3, _, _, hd, h⟩ := st_step hd h
    obtain ⟨⟨theta, alpha, a⟩, _, _, hd, h⟩ := st_step hd h
    obtain ⟨t, _, _, hd, h⟩ := st_step hd h
    obtain ⟨keys, _, _, hd, h⟩ := st_step hd h
    obtain ⟨table, _, _, hd, h⟩ := st_step hd h
    obtain ⟨_, _, _, hd, h⟩ := st_step hd h
    obtain ⟨leaves, _, _, hd, h⟩ := st_step hd h
    obtain ⟨⟨zb0, leaves'⟩, _, _, hd, h⟩ := st_step hd h
    obtain ⟨r5, _, _, hd, h⟩ := st_step hd h
    obtain ⟨bits, _, _, hd, h⟩ := st_step hd h
    obtain ⟨⟨zb1, bits'⟩, _, _, hd, h⟩ := st_step hd h
    obtain ⟨⟨sBit, bits''⟩, _, _, hd, h⟩ := st_step hd h
    obtain ⟨vBit, _, _, hd, h⟩ := st_step hd h
    obtain ⟨⟨bitsRow, p'⟩, _, _, hd, h⟩ := st_step hd h
    obtain ⟨s, _, _, hd, h⟩ := st_step hd h
    obtain ⟨_, _, _, hd, h⟩ := st_step hd h
    obtain ⟨_, _, _, hd, h⟩ := st_step hd h
    obtain ⟨_, _, _, hd, h⟩ := st_step hd h
    exact st_end hd h⟩

/-! ## The routines of the head's messages -/

/-- SubM.batch keeps the state. -/
instance keeps_batch (rows : ℕ) : KeepsS (SubM.batch rows) := by
  unfold SubM.batch
  infer_instance

/-- SubM.claimsIn keeps the state. -/
instance keeps_claimsIn (n : ℕ) : KeepsS (SubM.claimsIn n) := by
  unfold SubM.claimsIn
  infer_instance

/-- Head.noteH keeps the state. -/
instance keeps_noteH (w : String) (v : E) : KeepsS (Model.Head.noteH w v) := by
  unfold Model.Head.noteH
  infer_instance

/-- Head.replyToken keeps the state. -/
instance keeps_replyToken (plain : Array E) (V : ℕ) :
    KeepsS (Model.Head.replyToken plain V) :=
  ⟨fun F C a G D hs h => by
    have hd := Walk.Kept.refl hs
    unfold Model.Head.replyToken at h
    obtain ⟨_, _, _, hd, h⟩ := st_step hd h
    obtain ⟨_, _, _, hd, h⟩ := st_step hd h
    exact st_end hd h⟩

/-- Head.mergedPoint keeps the state. -/
instance keeps_mergedPoint (h0 : Model.Head.Shape) (g1 : Model.Forest.Heard) :
    KeepsS (Model.Head.mergedPoint h0 g1) := by
  unfold Model.Head.mergedPoint
  infer_instance

/-- tscLoop keeps the state. -/
theorem keeps_tscLoop : ∀ (zs : List E) (r : Array E) (p : Model.Psc),
    KeepsS (Model.tscLoop zs r p)
  | [], r, p => by
    unfold Model.tscLoop
    infer_instance
  | z :: zs, r, p =>
    ⟨fun F C a G D hs h => by
      have hd := Walk.Kept.refl hs
      unfold Model.tscLoop at h
      obtain ⟨⟨x, p'⟩, _, _, hd, h⟩ := st_step hd h
      exact hd.trans ((keeps_tscLoop zs _ _).keep _ _ _ _ _ hd.1 h)⟩

/-- The same as an instance. -/
instance keeps_tscLoop' (zs : List E) (r : Array E) (p : Model.Psc) :
    KeepsS (Model.tscLoop zs r p) := keeps_tscLoop zs r p

/-- tscRounds keeps the state. -/
instance keeps_tscRounds (P : Array E) (lt : ℕ) : KeepsS (Model.tscRounds P lt) :=
  ⟨fun F C a G D hs h => by
    have hd := Walk.Kept.refl hs
    unfold Model.tscRounds at h
    obtain ⟨_, _, _, hd, h⟩ := st_step hd h
    obtain ⟨_, _, _, hd, h⟩ := st_step hd h
    obtain ⟨_, _, _, hd, h⟩ := st_step hd h
    obtain ⟨⟨r, p⟩, _, _, hd, h⟩ := st_step hd h
    exact st_end hd h⟩

/-- tscIn keeps the state. -/
instance keeps_tscIn (P : Array E) (lt shown dY : ℕ) : KeepsS (Model.tscIn P lt shown dY) :=
  ⟨fun F C a G D hs h => by
    have hd := Walk.Kept.refl hs
    unfold Model.tscIn at h
    obtain ⟨_, _, _, hd, h⟩ := st_step hd h
    obtain ⟨⟨sEnd, p⟩, _, _, hd, h⟩ := st_step hd h
    exact st_end hd h⟩

/-- Head.hearSquares keeps the state. -/
instance keeps_hearSquares (h0 : Model.Head.Shape) (PV : Array E) :
    KeepsS (Model.Head.hearSquares h0 PV) :=
  ⟨fun F C a G D hs h => by
    have hd := Walk.Kept.refl hs
    unfold Model.Head.hearSquares at h
    obtain ⟨_, _, _, hd, h⟩ := st_step hd h
    obtain ⟨_, _, _, hd, h⟩ := st_step hd h
    obtain ⟨_, _, _, hd, h⟩ := st_step hd h
    exact st_end hd h⟩

/-- Head.shownRun keeps the state. -/
instance keeps_shownRun (first n : ℕ) : KeepsS (Model.Head.shownRun first n) := by
  unfold Model.Head.shownRun
  exact keeps_foldlM _ (fun a j =>
    ⟨fun F C x G D hs h => by
      have hd := Walk.Kept.refl hs
      obtain ⟨_, _, _, hd, h⟩ := st_step hd h
      exact st_end hd h⟩) _ _

/-- Head.hearProducts keeps the state. -/
instance keeps_hearProducts (h0 : Model.Head.Shape) (PV : Array E) :
    KeepsS (Model.Head.hearProducts h0 PV) :=
  ⟨fun F C a G D hs h => by
    have hd := Walk.Kept.refl hs
    unfold Model.Head.hearProducts at h
    obtain ⟨_, _, _, hd, h⟩ := st_step hd h
    obtain ⟨_, _, _, hd, h⟩ := st_step hd h
    obtain ⟨_, _, _, hd, h⟩ := st_step hd h
    obtain ⟨_, _, _, hd, h⟩ := st_step hd h
    obtain ⟨⟨row, p⟩, _, _, hd, h⟩ := st_step hd h
    exact st_end hd h⟩

/-- Head.hearStream keeps the state. -/
instance keeps_hearStream (h0 : Model.Head.Shape) (zt : Array E) :
    KeepsS (Model.Head.hearStream h0 zt) :=
  ⟨fun F C a G D hs h => by
    have hd := Walk.Kept.refl hs
    unfold Model.Head.hearStream at h
    obtain ⟨_, _, _, hd, h⟩ := st_step hd h
    obtain ⟨_, _, _, hd, h⟩ := st_step hd h
    obtain ⟨_, _, _, hd, h⟩ := st_step hd h
    obtain ⟨⟨row, p⟩, _, _, hd, h⟩ := st_step hd h
    exact st_end hd h⟩

/-- Head.channelRounds keeps the state. -/
theorem keeps_channelRounds : ∀ (n : ℕ) (r : Array E) (p : Model.Psc),
    KeepsS (Model.Head.channelRounds n r p)
  | 0, r, p => by
    unfold Model.Head.channelRounds
    infer_instance
  | n + 1, r, p =>
    ⟨fun F C a G D hs h => by
      have hd := Walk.Kept.refl hs
      unfold Model.Head.channelRounds at h
      obtain ⟨⟨x, p'⟩, _, _, hd, h⟩ := st_step hd h
      exact hd.trans ((keeps_channelRounds n _ _).keep _ _ _ _ _ hd.1 h)⟩

/-- The same as an instance. -/
instance keeps_channelRounds' (n : ℕ) (r : Array E) (p : Model.Psc) :
    KeepsS (Model.Head.channelRounds n r p) := keeps_channelRounds n r p

/-- Head.hearLogits keeps the state. -/
instance keeps_hearLogits (h0 : Model.Head.Shape) (lam : ℕ) (zt : Array E) :
    KeepsS (Model.Head.hearLogits h0 lam zt) :=
  ⟨fun F C a G D hs h => by
    have hd := Walk.Kept.refl hs
    unfold Model.Head.hearLogits at h
    obtain ⟨_, _, _, hd, h⟩ := st_step hd h
    obtain ⟨⟨r, p⟩, _, _, hd, h⟩ := st_step hd h
    obtain ⟨⟨sEnd, p'⟩, _, _, hd, h⟩ := st_step hd h
    obtain ⟨_, _, _, hd, h⟩ := st_step hd h
    obtain ⟨_, _, _, hd, h⟩ := st_step hd h
    obtain ⟨⟨row, p''⟩, _, _, hd, h⟩ := st_step hd h
    exact st_end hd h⟩

/-- The routine that hears the head's messages keeps the state. -/
instance keeps_hear (h0 : Model.Head.Shape) (L : Model.Head.HL) (hp : Model.Head.HPlanH2)
    (cov : Model.Head.Covered) (plain : Array E) :
    KeepsS (Model.Head.hear h0 L hp cov plain) :=
  ⟨fun F C a G D hs h => by
    have hd := Walk.Kept.refl hs
    unfold Model.Head.hear at h
    obtain ⟨_, _, _, hd, h⟩ := st_step hd h
    obtain ⟨_, _, _, hd, h⟩ := st_step hd h
    obtain ⟨_, _, _, hd, h⟩ := st_step hd h
    obtain ⟨_, _, _, hd, h⟩ := st_step hd h
    obtain ⟨_, _, _, hd, h⟩ := st_step hd h
    obtain ⟨⟨sW, gp, wpl⟩, _, _, hd, h⟩ := st_step hd h
    obtain ⟨⟨sPv, omV, tV⟩, _, _, hd, h⟩ := st_step hd h
    obtain ⟨_, _, _, hd, h⟩ := st_step hd h
    obtain ⟨_, _, _, hd, h⟩ := st_step hd h
    obtain ⟨_, _, _, hd, h⟩ := st_step hd h
    obtain ⟨⟨tH, rs⟩, _, _, hd, h⟩ := st_step hd h
    obtain ⟨_, _, _, hd, h⟩ := st_step hd h
    obtain ⟨_, _, _, hd, h⟩ := st_step hd h
    obtain ⟨_, _, _, hd, h⟩ := st_step hd h
    obtain ⟨_, _, _, hd, h⟩ := st_step hd h
    obtain ⟨_, _, _, hd, h⟩ := st_step hd h
    obtain ⟨_, _, _, hd, h⟩ := st_step hd h
    obtain ⟨_, _, _, hd, h⟩ := st_step hd h
    obtain ⟨_, _, _, hd, h⟩ := st_step hd h
    obtain ⟨_, _, _, hd, h⟩ := st_step hd h
    obtain ⟨_, _, _, hd, h⟩ := st_step hd h
    obtain ⟨_, _, _, hd, h⟩ := st_step hd h
    obtain ⟨_, _, _, hd, h⟩ := st_step hd h
    exact st_end hd h⟩

/-! ## The merge's messages -/

/-- wsForkRounds keeps the state. -/
theorem keeps_wsForkRounds : ∀ (n : ℕ) (rm : Array E) (p : Model.Psc),
    KeepsS (Model.wsForkRounds n rm p)
  | 0, rm, p => by
    unfold Model.wsForkRounds
    infer_instance
  | n + 1, rm, p =>
    ⟨fun F C a G D hs h => by
      have hd := Walk.Kept.refl hs
      unfold Model.wsForkRounds at h
      obtain ⟨⟨x, p'⟩, _, _, hd, h⟩ := st_step hd h
      exact hd.trans ((keeps_wsForkRounds n _ _).keep _ _ _ _ _ hd.1 h)⟩

/-- The same as an instance. -/
instance keeps_wsForkRounds' (n : ℕ) (rm : Array E) (p : Model.Psc) :
    KeepsS (Model.wsForkRounds n rm p) := keeps_wsForkRounds n rm p

/-- wsForkMerge keeps the state. -/
instance keeps_wsForkMerge (lk : ℕ) (sv : Array ℕ) : KeepsS (Model.wsForkMerge lk sv) :=
  ⟨fun F C a G D hs h => by
    have hd := Walk.Kept.refl hs
    unfold Model.wsForkMerge at h
    obtain ⟨_, _, _, hd, h⟩ := st_step hd h
    obtain ⟨_, _, _, hd, h⟩ := st_step hd h
    obtain ⟨⟨rm, p⟩, _, _, hd, h⟩ := st_step hd h
    obtain ⟨⟨sFv, p'⟩, _, _, hd, h⟩ := st_step hd h
    obtain ⟨_, _, _, hd, h⟩ := st_step hd h
    exact st_end hd h⟩

/-- wsForkEnd keeps the state. -/
instance keeps_wsForkEnd (lay : Model.WsLay) (cl : Array Model.WsClaim) (sv : Array ℕ) :
    KeepsS (Model.wsForkEnd lay cl sv) :=
  ⟨fun F C a G D hs h => by
    have hd := Walk.Kept.refl hs
    unfold Model.wsForkEnd at h
    obtain ⟨_, _, _, hd, h⟩ := st_step hd h
    obtain ⟨_, _, _, hd, h⟩ := st_step hd h
    obtain ⟨_, _, _, hd, h⟩ := st_step hd h
    obtain ⟨⟨o, rho⟩, _, _, hd, h⟩ := st_step hd h
    exact st_end hd h⟩

/-- The draw of the smallness test's matrix keeps the state. -/
instance keeps_drawMatrixF (tl : Model.HTailF2) : KeepsS tl.drawMatrixF :=
  ⟨fun F C a G D hs h => by
    have hd := Walk.Kept.refl hs
    unfold Model.HTailF2.drawMatrixF at h
    obtain ⟨_, _, _, hd, h⟩ := st_step hd h
    obtain ⟨_, _, _, hd, h⟩ := st_step hd h
    exact st_end hd h⟩

#print axioms keeps_pad
#print axioms keeps_hear
#print axioms keeps_wsForkEnd
#print axioms keeps_drawMatrixF

end OnBytes.Road.Hd.Parts
