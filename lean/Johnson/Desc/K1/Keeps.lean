-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K1/Keeps.lean: kind K1 writes the statement through the ground's plain functions
alone, and never begins a proximity test: so its own blocks keep EVERY relation R on statements that
these functions keep (Johnson/Desc/GroundKeeps.lean: GroundKeeps R): among them "a statement only
grows" and "no new mark". Theorems.

  laid_keeps, decideSend_keeps   the sending's decision: the messages are received, the sampled ones
                       admitted.
  joinAll_keeps, joinOwnP_keeps  a segment's own messages join its group.
  sendOwn_keeps        a sending by itself.
  laterOwn_keeps, commitStep_keeps, commitOwn_keeps   a segment's later moment.
The names stand in the namespace K1.Rel: the kind's law on one property, "the statement is in
order", has theorems of the same names in K1.
What is not claimed. Which relations are such is Johnson/Desc/GroundKeeps.lean's matter. The first
segment's opening and the three blocks at the first chain's record: Johnson/Desc/K1/KeepsAtS.lean.

-/
import Johnson.Desc.K1.OwnLaws
import Johnson.Desc.GroundKeeps
import Johnson.Desc.BlockKeeps

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K1.Rel
open OnBytes OnBytes.Params OnBytes.Model Desc.Plain
open VerifiableInference.Desc.First.Send (joinOwnP joinAll)
open VerifiableInference.Desc.Ground (GroundKeeps By)
open VerifiableInference.Desc.Keeps (Decides)

variable {L Cl : Type} {R : Statement → Statement → Prop}

/-- The sample rows are laid, message by message. -/
theorem laid_keeps (H : GroundKeeps R) (codes : Codes) (seeds : List (List E × E)) (l : List
    (Nat × OracleShape))
    (ys : List E) (d d' : DState L) (h : Laid codes seeds l ys d d') : R d.st d'.st := by
  induction h with
  | done d => exact H.refl _
  | pass o s l ys d d' h0 h ih => exact ih
  | lay o s l ys d d₁ d' h0 hs hy ha h ih => exact H.trans (H.admit _ _ _ _ ha) ih

/-- The sending's decision. -/
theorem decideSend_keeps (H : GroundKeeps R) (P : Par) (owed : Option Nat) (d : DState L)
    (rs : List Fmt.RoundView)
    (y : Array Nat × DState L) (h : decideSend P owed d rs = .ok y) : R d.st y.2.st := by
  unfold decideSend at h
  split at h
  · obtain ⟨_, _, h⟩ := (bind_ok _ _ _).1 h
    obtain ⟨_, _, h⟩ := (bind_ok _ _ _).1 h
    obtain ⟨_, _, h⟩ := (bind_ok _ _ _).1 h
    obtain ⟨_, _, h⟩ := (bind_ok _ _ _).1 h
    obtain ⟨x, h5, h⟩ := (bind_ok _ _ _).1 h
    obtain ⟨_, _, h⟩ := (bind_ok _ _ _).1 h
    obtain ⟨_, _, h⟩ := (bind_ok _ _ _).1 h
    obtain ⟨e, h8, h⟩ := (bind_ok _ _ _).1 h
    have hp : (x.1, e) = y := by simpa [pure, Except.pure] using h
    subst hp
    exact H.trans (H.recv _ d x.2 _ x.1 ((named_ok _ _ _).1 h5))
      (laid_keeps H _ _ _ _ _ _ (layRows_ok _ _ _ _ _ _ h8))
  · cases h

/-- Messages join a group, one behind the other. -/
theorem joinAll_keeps (H : GroundKeeps R) (p : GPar) (g : Nat) (l : List (ReqMessage × Nat)) : ∀
    (d d' : DState L),
    joinAll groundG p g l d = some d' → R d.st d'.st := by
  induction l with
  | nil =>
    intro d d' h
    cases h
    exact H.refl _
  | cons x l ih =>
    intro d d' h
    cases hj : (groundG (L := L)).join p d g x.2 (decide (0 < x.1.life)) with
    | none => simp [joinAll, hj] at h
    | some e =>
      simp only [joinAll, hj, Option.bind_some] at h
      exact H.trans (H.join d e g x.2 _ hj) (ih e d' h)

/-- The messages sent join the segment's group. -/
theorem joinOwnP_keeps (H : GroundKeeps R) (p : GPar) (d : DState L) (f : ReqFrame)
    (sent : List ReqMessage)
    (ids : Array Nat) (y : ReqFrame × DState L) (h : joinOwnP groundG p d f sent ids = some y) :
    R d.st y.2.st := by
  unfold joinOwnP at h
  split at h
  · cases hj : joinAll groundG p f.group (zipT sent ids.toList) d with
    | none => simp [hj] at h
    | some e =>
      simp only [hj, Option.map_some, Option.some.injEq] at h
      subst h
      exact joinAll_keeps H _ _ _ _ _ hj
  · cases h

/-- A sending by itself. -/
theorem sendOwn_keeps (H : GroundKeeps R) (P : Par) :
    Decides (By R fun s : Owing (DState (Array Nat)) => s.held.st) (sendOwn (Cl := Cl) P) := by
  intro s rs _ s' h
  obtain ⟨x, h1, h2⟩ := Keeps.emap_ok (x := decideSend P s.owed s.held rs) h
  subst h2
  exact decideSend_keeps H _ _ _ _ _ h1

/-- A later moment's sending with its joining. -/
theorem laterOwn_keeps (H : GroundKeeps R) (P : Par) (owed : Option Nat) (c : ChainCheck)
    (w : DState Unit)
    (rs : List Fmt.RoundView) (y : ChainCheck × DState Unit) (h : laterOwn P owed c w rs = .ok y) :
    R w.st y.2.st := by
  unfold laterOwn at h
  dsimp only at h
  split at h
  · cases h
  · split at h
    · cases h
    · split at h
      · cases h
      · cases hd : decideSend P owed w rs with
        | error e => simp [hd] at h
        | ok x =>
          simp only [hd] at h
          split at h
          · cases h
          · rename_i z hz
            cases h
            exact H.trans (decideSend_keeps H _ _ _ _ _ hd) (joinOwnP_keeps H _ _ _ _ _ _ hz)

/-- A commitment's frame changes what the sending carries by the sending alone. -/
theorem commitStep_keeps {W : Type} (st : W → Statement) (send : L3.Send W)
    (hs : ∀ c w rs y, send c w rs = .ok y → R (st w) (st y.2)) (trees : List Nat)
    (s s' : L3.St W) (rs : List Fmt.RoundView) (h : L3.commitStep send trees s rs = .ok s') :
    R (st s.w) (st s'.w) := by
  unfold L3.commitStep at h
  obtain ⟨_, _, h⟩ := (bind_ok _ _ _).1 h
  obtain ⟨⟨check, w⟩, h1, h⟩ := (bind_ok _ _ _).1 h
  dsimp only at h
  obtain ⟨⟨L', F'⟩, _, h⟩ := (bind_ok _ _ _).1 h
  cases h
  exact hs _ _ _ _ h1

/-- A segment's later moment. -/
theorem commitOwn_keeps (H : GroundKeeps R) (P : Par) (link moment : Nat) (arrays : Option
    (List Nat)) :
    Decides (By R fun s : Owing (L3.St (DState Unit)) => s.held.w.st)
      (commitOwn (Cl := Cl) P link moment arrays) := by
  intro s rs _ s' h
  simp only [commitOwn] at h
  split at h
  · split at h
    · cases h
    · obtain ⟨x, h1, h2⟩ := Keeps.emap_ok h
      subst h2
      exact commitStep_keeps (fun w : DState Unit => w.st) _
        (fun c w rs y hy => laterOwn_keeps H P s.owed c w rs y hy) _ _ _ _ h1
  · cases h

end VerifiableInference.Desc.K1.Rel
