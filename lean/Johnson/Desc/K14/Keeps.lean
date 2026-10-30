-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K14/Keeps.lean: a sending, and the eight functions of the page of the linear claim's
shared rounds, write the statement through the ground's plain functions alone, and never begin a
proximity test: so they keep EVERY relation R on statements that these functions keep
(Johnson/Desc/GroundKeeps.lean: GroundKeeps R): among them "a statement only grows" and "no new
mark". Theorems.

  sampleLoop_keeps, sendP_keeps   a sending, at the description's value of the ground functions.
  linPoint · behindU · laysRec · loc · behindOmega · joins · linZeta · split: each name with _keeps
  behind it.
What is not claimed. These are the page's functions: the blocks that call them are another file's.

-/
import Johnson.Desc.K14.Text
import Johnson.Desc.GroundKeeps

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.Plain
open OnBytes OnBytes.Params VerifiableInference.Desc VerifiableInference.Desc.Ground

variable {L : Type} {R : Statement → Statement → Prop}

/-- A bind of Option that returns: both halves return. -/
theorem obind_ok {α β : Type} {x : Option α} {f : α → Option β} {b : β}
    (h : (x >>= f) = some b) : ∃ a, x = some a ∧ f a = some b := by
  cases x with
  | none => cases h
  | some a => exact ⟨a, rfl, h⟩

/-- Message by message: each is admitted. -/
theorem sampleLoop_keeps (H : GroundKeeps R) (p : GPar) (codes : Codes) (seeds : List SampleSeed)
    (l : List (Nat × OracleShape)) : ∀ (ys : List E) (d : DState L) (y : DState L × List E),
    sampleLoop groundG p codes seeds l ys d = some y → R d.st y.1.st := by
  induction l with
  | nil =>
    intro ys d y h
    simp only [sampleLoop, Option.some.injEq] at h
    subst h
    exact H.refl _
  | cons a l ih =>
    intro ys d y h
    obtain ⟨o, s⟩ := a
    cases hr : rowsFor codes s o seeds (List.range s.answers) ys #[] with
    | none => simp [sampleLoop, hr] at h
    | some x =>
      obtain ⟨rows, ys'⟩ := x
      cases ha : (groundG (L := L)).admit p d o rows with
      | none => simp [sampleLoop, hr, ha] at h
      | some d₁ =>
        simp only [sampleLoop, hr, ha] at h
        exact H.trans (H.admit d d₁ o rows ha) (ih _ _ _ h)

/-- A sending: the messages are received; those with answers are admitted. -/
theorem sendP_keeps (H : GroundKeeps R) (p : GPar) (own : Bool) (d : DState L)
    (sent : Array OracleNotice)
    (r₁ r₂ : Fmt.RoundView) (y : Array Nat × List E × List E × Nat × DState L)
    (h : sendP groundG p own d sent r₁ r₂ = some y) : R d.st y.2.2.2.2.st := by
  unfold sendP at h
  obtain ⟨⟨ids, d₁⟩, h1, h⟩ := obind_ok h
  dsimp only at h
  obtain ⟨shapes, _, h⟩ := obind_ok h
  obtain ⟨seeds, _, h⟩ := obind_ok h
  obtain ⟨an, _, h⟩ := obind_ok h
  split at h
  · obtain ⟨⟨d₂, left⟩, h2, h⟩ := obind_ok h
    dsimp only at h
    split at h
    · cases h
      exact H.trans (H.recv p.firstTree d d₁ sent ids h1) (sampleLoop_keeps H _ _ _ _ _ _ _ h2)
    · cases h
  · cases h

end Desc.Plain

namespace Desc.K14
open OnBytes OnBytes.Params Desc.Plain VerifiableInference.Desc VerifiableInference.Desc.Ground

variable {R : Statement → Statement → Prop}

/-- The shared point: the two groups are opened. -/
theorem linPoint_keeps (H : GroundKeeps R) (p : Par) (d d' : St) (rs : List Fmt.RoundView)
    (h : linPoint p d rs = some d') :
    R d.st d'.st := by
  unfold linPoint at h
  split at h
  · obtain ⟨_, _, h⟩ := obind_ok h
    obtain ⟨⟨gU, d₁⟩, h1, h⟩ := obind_ok h
    dsimp only at h
    split at h
    · obtain ⟨y, h2, h⟩ := obind_ok h
      cases h
      exact H.trans (H.newGroup d d₁ _ _ gU h1) (H.newGroup d₁ y.2 _ _ y.1 h2)
    · obtain ⟨y, h2, h⟩ := obind_ok h
      cases h2
      cases h
      exact H.newGroup d d₁ _ _ gU h1
  · cases h

/-- Behind the folded row's sending: the statement is left as it is. -/
theorem behindU_keeps (H : GroundKeeps R) (p : Par) (d d' : St) (ids : Array Nat)
    (h : behindU p d ids = some d') : R d.st d'.st := by
  unfold behindU at h
  split at h <;>
    (obtain ⟨_, _, h⟩ := obind_ok h
     obtain ⟨_, _, h⟩ := obind_ok h
     cases h
     exact H.refl _)

/-- The folded row joins its group; the record's rows are laid. -/
theorem laysRec_keeps (H : GroundKeeps R) (p : Par) (d d' : St) (rs : List Fmt.RoundView)
    (h : laysRec p d rs = some d') :
    R d.st d'.st := by
  unfold laysRec at h
  dsimp only at h
  obtain ⟨_, _, h⟩ := obind_ok h
  obtain ⟨d₁, h1, h⟩ := obind_ok h
  obtain ⟨rows, _, h⟩ := obind_ok h
  exact H.trans (H.join _ _ _ _ _ h1) (H.addRows _ _ _ _ h)

/-- The rows at the locations drawn are laid. -/
theorem loc_keeps (H : GroundKeeps R) (p : Par) (d d' : St) (rs : List Fmt.RoundView)
    (gs : List (List (Nat × List UInt64)))
    (h : loc p d rs gs = some d') : R d.st d'.st := by
  unfold loc at h
  split at h
  · dsimp only at h
    obtain ⟨rows, _, h⟩ := obind_ok h
    exact H.addRows _ _ _ _ h
  · cases h

/-- Behind Omega's sending: the statement is left as it is. -/
theorem behindOmega_keeps (H : GroundKeeps R) (p : Par) (d d' : St) (ids : Array Nat)
    (h : behindOmega p d ids = some d') : R d.st d'.st := by
  unfold behindOmega at h
  split at h <;>
    (obtain ⟨_, _, h⟩ := obind_ok h
     obtain ⟨_, _, h⟩ := obind_ok h
     cases h
     exact H.refl _)

/-- Omega and the split's message join their groups. -/
theorem joins_keeps (H : GroundKeeps R) (p : Par) (d d' : St) (rs : List Fmt.RoundView)
    (h : joins p d rs = some d') :
    R d.st d'.st := by
  unfold joins at h
  dsimp only at h
  obtain ⟨_, _, h⟩ := obind_ok h
  obtain ⟨d₁, h1, h⟩ := obind_ok h
  split at h
  · obtain ⟨d₂, h2, h⟩ := obind_ok h
    exact H.trans (H.trans (H.join _ _ _ _ _ h1) (H.join _ _ _ _ _ h2)) (H.join _ _ _ _ _ h)
  · cases h
    exact H.join _ _ _ _ _ h1

/-- The second point: the statement is left as it is. -/
theorem linZeta_keeps (H : GroundKeeps R) (d d' : St) (rs : List Fmt.RoundView)
    (h : linZeta d rs = some d') :
    R d.st d'.st := by
  unfold linZeta at h
  split at h
  · cases h; exact H.refl _
  · cases h

/-- The split: an entry of a mask is taken; two rows are laid. -/
theorem split_keeps (H : GroundKeeps R) (p : Par) (d d' : St) (rs : List Fmt.RoundView)
    (h : split p d rs = some d') :
    R d.st d'.st := by
  unfold split at h
  dsimp only at h
  obtain ⟨row, _, h⟩ := obind_ok h
  split at h
  · exact H.addRow _ _ _ _ h
  · split at h
    · obtain ⟨mu, _, h⟩ := obind_ok h
      obtain ⟨G, _, h⟩ := obind_ok h
      obtain ⟨_, _, h⟩ := obind_ok h
      obtain ⟨⟨kappa, d₁⟩, h1, h⟩ := obind_ok h
      dsimp only at h
      obtain ⟨d₂, h2, h⟩ := obind_ok h
      exact H.trans (H.trans (H.takeMask _ _ _ _ h1) (H.addRow _ _ _ _ h2)) (H.addRow _ _ _ _ h)
    · obtain ⟨mu, hm, h⟩ := obind_ok h
      cases hm
  · cases h

end Desc.K14
