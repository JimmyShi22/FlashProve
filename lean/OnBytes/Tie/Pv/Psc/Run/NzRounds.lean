-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Tie/Pv/Psc/Run/NzRounds.lean: the routines on the channel of a model's sub-proof keep the
property `NzCtx` of OnBytes/Tie/Pv/Psc/Run/NzCtx.lean.

Main names:
  `keeps_same`: a block that leaves the plan's unused entries, the view's rounds that are not yet
    closed, and the kind of run as they were keeps `NzCtx`.
  `keeps_must`, `keeps_mustAs`, `keeps_get`, `keeps_lastEntry`, `keeps_requireRows`,
    `keeps_closeAs`, `keeps_oneOf`: calls of OnBytes/Iop/Ground.lean, OnBytes/Model/Frame.lean and
    OnBytes/Model/Rounds.lean.
  `keeps_trRead`, `keeps_trSum`, `keeps_trAnswer`, `keeps_trAnswerNotZero`, `keeps_trTrits`,
    `keeps_trEmpty`, `keeps_trPoint`, `keeps_trBatchOpen`, `keeps_trBatchRows`, `keeps_trBatch`: the
    ten routines of OnBytes/Model/Rounds.lean.
  `KeepsS`: a routine of a sub-proof (SubM) keeps `NzCtx`. `keepsS_pure`, `keepsS_bind`,
    `keepsS_lift`, `keepsS_ask`, `keepsS_take`, `keepsS_change`: the ways in which such routines are
    made.

Limits: as in OnBytes/Tie/Pv/Psc/Run/NzCtx.lean. Routines that are not named are not treated; they
follow where they are made of these by bind.
-/
import OnBytes.Tie.Pv.Psc.Run.NzCtx

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Model.Road

variable {K : Type} [CommRing K] (ρ : Reading K)

theorem keeps_same {α : Type} (b : Blk α)
    (H : ∀ c a c', b.Yields c a c' → c'.ch.entries = c.ch.entries ∧
      c'.ch.pending = c.ch.pending ∧ c'.ch.dry = c.ch.dry) : Keeps ρ b := fun c a c' h y => by
  obtain ⟨e1, e2, e3⟩ := H c a c' y
  refine ⟨e3.trans h.1, fun k e r he hr => ?_⟩
  rw [e1] at he
  rw [e2] at hr
  exact h.2 k e r he hr

theorem keeps_must (b : Bool) : Keeps ρ (Blk.must b) := keeps_same ρ _ fun c _ c' y => by
  obtain ⟨_, rfl⟩ := (Blk.yields_must b c c').1 y
  exact ⟨rfl, rfl, rfl⟩

theorem keeps_mustAs (name : String) (b : Bool) : Keeps ρ (mustAs name b) :=
  keeps_same ρ _ fun c u c' y => by
    obtain ⟨_, rfl⟩ := (mustAs_ok name b c c' u).1 ((Blk.yields_iff _ _ _ _).1 y)
    exact ⟨rfl, rfl, rfl⟩

theorem keeps_get {α : Type} (x : Option α) : Keeps ρ (Blk.get x) :=
  keeps_same ρ _ fun c a c' y => by
    obtain ⟨_, rfl⟩ := (Blk.yields_get x a c c').1 y
    exact ⟨rfl, rfl, rfl⟩

theorem keeps_fail {α : Type} (name : String) : Keeps ρ (Blk.fail name : Blk α) :=
  fun c a c' _ y => by
    rw [Blk.yields_iff] at y
    cases y

theorem keeps_lastEntry : Keeps ρ Blk.lastEntry := keeps_same ρ _ fun c a c' y => by
  rw [Blk.yields_iff] at y
  unfold Blk.lastEntry at y
  cases hl : c.ch.last with
  | none => simp [hl] at y
  | some e =>
    simp only [hl, Except.ok.injEq, Prod.mk.injEq] at y
    obtain ⟨_, rfl⟩ := y
    exact ⟨rfl, rfl, rfl⟩

theorem keeps_requireRows (rows : Nat) : Keeps ρ (Blk.requireRows rows) :=
  keeps_same ρ _ fun c a c' y => by
    rw [Blk.yields_iff] at y
    unfold Blk.requireRows at y
    cases hl : c.ch.last with
    | none => simp [hl] at y
    | some e =>
      simp only [hl] at y
      split at y
      · simp only [Except.ok.injEq, Prod.mk.injEq] at y
        obtain ⟨_, rfl⟩ := y
        exact ⟨rfl, rfl, rfl⟩
      · cases y

theorem keeps_closeAs (name : String) (kind : Fmt.Kind) (elems notZero entries : Nat) :
    Keeps ρ (closeAs name kind elems notZero entries) :=
  keeps_bind ρ _ _ (keeps_must ρ _) fun _ =>
    keeps_bind ρ _ _ (keeps_close ρ name kind notZero) fun d =>
      keeps_bind ρ _ _ (keeps_lastEntry ρ) fun _ =>
        keeps_bind ρ _ _ (keeps_must ρ _) fun _ => keeps_pure ρ d

theorem keeps_oneOf (d : Fmt.Drawn) : Keeps ρ (oneOf d) := by
  unfold oneOf
  split
  · exact keeps_pure ρ _
  · exact keeps_fail ρ _

theorem keeps_noBatching (r : RoundName) : Keeps ρ (noBatching r) := keeps_mustAs ρ _ _

theorem keeps_trReadLoop : ∀ (n : Nat) (a : Array E), Keeps ρ (trReadLoop n a)
  | 0, a => keeps_pure ρ a
  | n + 1, a => keeps_bind ρ _ _ (keeps_recvE ρ) fun x => keeps_trReadLoop n (a.push x)

theorem keeps_trRead (n : Nat) : Keeps ρ (trRead n) := keeps_trReadLoop ρ n _

theorem keeps_trSum : Keeps ρ trSum := keeps_recvE ρ

theorem keeps_trAnswer (r : RoundName) : Keeps ρ (trAnswer r) :=
  keeps_bind ρ _ _ (keeps_noBatching ρ r) fun _ =>
    keeps_bind ρ _ _ (keeps_closeAs ρ _ _ _ _ _) fun d => keeps_oneOf ρ d

theorem keeps_trAnswerNotZero (r : RoundName) : Keeps ρ (trAnswerNotZero r) :=
  keeps_bind ρ _ _ (keeps_noBatching ρ r) fun _ =>
    keeps_bind ρ _ _ (keeps_closeAs ρ _ _ _ _ _) fun d => keeps_oneOf ρ d

theorem keeps_trTrits (columns combinations : Nat) : Keeps ρ (trTrits columns combinations) :=
  keeps_bind ρ _ _ (keeps_must ρ _) fun _ =>
    keeps_bind ρ _ _ (keeps_closeAs ρ _ _ _ _ _) fun _ => keeps_pure ρ _

theorem keeps_trEmpty (r : RoundName) : Keeps ρ (trEmpty r) :=
  keeps_bind ρ _ _ (keeps_closeAs ρ _ _ _ _ _) fun _ => keeps_pure ρ ()

theorem keeps_trPoint (r : RoundName) (n : Nat) : Keeps ρ (trPoint r n) :=
  keeps_bind ρ _ _ (keeps_noBatching ρ r) fun _ =>
    keeps_bind ρ _ _ (keeps_closeAs ρ _ _ _ _ _) fun _ => keeps_pure ρ _

theorem keeps_trBatchOpen : Keeps ρ trBatchOpen :=
  keeps_bind ρ _ _ (keeps_closeAs ρ _ _ _ _ _) fun d => keeps_oneOf ρ d

theorem keeps_trBatchRows (rows : Nat) : Keeps ρ (trBatchRows rows) := keeps_requireRows ρ rows

theorem keeps_trBatch (rows : Nat) : Keeps ρ (trBatch rows) :=
  keeps_bind ρ _ _ (keeps_mustAs ρ _ _) fun _ =>
    keeps_bind ρ _ _ (keeps_trBatchOpen ρ) fun _ =>
      keeps_bind ρ _ _ (keeps_trBatchRows ρ rows) fun _ => keeps_pure ρ _

/-! ## Routines of a sub-proof -/

/-- A routine of a sub-proof keeps `NzCtx`. -/
def KeepsS {α : Type} (x : SubM α) : Prop :=
  ∀ F c a G c', NzCtx ρ c → x F c = .ok ((a, G), c') → NzCtx ρ c'

theorem keepsS_pure {α : Type} (a : α) : KeepsS ρ (pure a : SubM α) := fun F c x G c' h y => by
  obtain ⟨_, _, rfl⟩ := (pure_ok _ _ _ _ _ _).1 y
  exact h

theorem keepsS_bind {α β : Type} (x : SubM α) (f : α → SubM β) (hx : KeepsS ρ x)
    (hf : ∀ a, KeepsS ρ (f a)) : KeepsS ρ (x >>= f) := fun F c b G c' h y => by
  obtain ⟨a, F1, c1, y1, y2⟩ := (bind_ok _ _ _ _ _).1 y
  exact hf a F1 c1 b G c' (hx F c a F1 c1 h y1) y2

theorem keepsS_lift {α : Type} (b : Blk α) (hb : Keeps ρ b) :
    KeepsS ρ (StateT.lift b : SubM α) := fun F c a G c' h y =>
  hb c a c' h ((liftY_ok b F G c c' a).1 y).1

theorem keepsS_ask {α : Type} (f : Fork → Option α) : KeepsS ρ (SubM.ask f) :=
  fun F c a G c' h y => by
    obtain ⟨_, _, rfl⟩ := (ask_ok f F G c c' a).1 y
    exact h

theorem keepsS_take {α : Type} (f : Fork → Option (α × Fork)) : KeepsS ρ (SubM.take f) :=
  fun F c a G c' h y => by
    obtain ⟨_, rfl⟩ := (take_ok f F G c c' a).1 y
    exact h

theorem keepsS_change (f : Fork → Option Fork) : KeepsS ρ (SubM.change f) :=
  fun F c u G c' h y => by
    obtain ⟨_, rfl⟩ := (change_ok f F G c c' u).1 y
    exact h

end OnBytes.Model.Road

#print axioms OnBytes.Model.Road.keeps_trBatch
#print axioms OnBytes.Model.Road.keepsS_lift
