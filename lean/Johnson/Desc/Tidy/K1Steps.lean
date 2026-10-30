-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Tidy/K1Steps.lean: the sending kind's three blocks at the first chain's record keep
every relation on statements that the eight plain functions which ask nothing of their caller keep
(`GroundQuiet`, Johnson/Desc/GroundQuiet.lean) and that the admitting of a sample keeps where the
rows handed in are on the message (`AdmitOn`, Johnson/Desc/K1/Quiet.lean): where the block's test on
the plan passes, at a yes on rounds that fit. Statements with their proofs.

Johnson/Desc/K1/Keeps.lean and Johnson/Desc/K1/KeepsAtS.lean have the same of every `GroundKeeps`,
which asks the admitting without its condition. "A quiet step" (`Quiet`,
Johnson/Desc/Means/Walk.lean) is no such relation: it has the admitting under the condition alone.
Johnson/Desc/K1/Quiet.lean has the sending's own decision (`decideSend_rel`, `sendOwn_rel`); here
are the joinings, the later moment, the opening, and the three blocks at the record.
Main names:
  `joinAll_rel`, `joinOwnP_rel`, `laterOwn_rel`, `commitOwn_rel`, `firstOwn_rel`.
  `sendAtS_fits`, `commitAtS_fits`, `firstAtS_fits`: **the three blocks**: `Fits (By R ·.st)`
    (Johnson/Desc/Tidy/Fits.lean: at a yes of the decision on rounds that fit); `…_steps`: so
    `Steps`.
  `sendAtS_quiet`, `commitAtS_quiet`, `firstAtS_quiet`: so each is a quiet step.

What is not claimed. That a plan passes the blocks' tests. Nothing on soundness.

-/
import Johnson.Desc.K1.Quiet
import Johnson.Desc.K1.KeepsAtS
import Johnson.Desc.Tidy.Fits

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K1
open OnBytes OnBytes.Params OnBytes.Model Desc.Plain
open OnBytes.Slice
open VerifiableInference.Desc.Ground (GroundQuiet By)
open VerifiableInference.Desc.Keeps (Steps Fits steps_of_fits)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.Send (joinOwnP joinAll)
open VerifiableInference.Desc.K1.Rel (putLink_st putFork_st)

variable {L Cl : Type} {R : Statement → Statement → Prop}

/-- Messages join a group, one behind the other. -/
theorem joinAll_rel (H : GroundQuiet R) (p : GPar) (g : Nat) (l : List (ReqMessage × Nat)) :
    ∀ (d d' : DState L), joinAll groundG p g l d = some d' → R d.st d'.st := by
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
theorem joinOwnP_rel (H : GroundQuiet R) (p : GPar) (d : DState L) (f : ReqFrame)
    (sent : List ReqMessage) (ids : Array Nat) (y : ReqFrame × DState L)
    (h : joinOwnP groundG p d f sent ids = some y) : R d.st y.2.st := by
  unfold joinOwnP at h
  split at h
  · cases hj : joinAll groundG p f.group (zipT sent ids.toList) d with
    | none => simp [hj] at h
    | some e =>
      simp only [hj, Option.map_some, Option.some.injEq] at h
      subst h
      exact joinAll_rel H _ _ _ _ _ hj
  · cases h

/-- A later moment's sending with its joining. -/
theorem laterOwn_rel (H : GroundQuiet R) (hA : AdmitOn R) (P : Par) (hB : planOkOwn P = true)
    (owed : Option Nat) (c : ChainCheck) (w : DState Unit) (r₁ r₂ : Fmt.RoundView)
    (hfit : roundsFit (rounds P) [r₁, r₂] = true) (y : ChainCheck × DState Unit)
    (h : laterOwn P owed c w [r₁, r₂] = .ok y) : R w.st y.2.st := by
  unfold laterOwn at h
  dsimp only at h
  split at h
  · cases h
  · split at h
    · cases h
    · split at h
      · cases h
      · cases hd : decideSend P owed w [r₁, r₂] with
        | error e => simp [hd] at h
        | ok x =>
          simp only [hd] at h
          split at h
          · cases h
          · rename_i z hz
            cases h
            exact H.trans (decideSend_rel H hA P owed w x.2 r₁ r₂ x.1 hB hfit hd)
              (joinOwnP_rel H _ _ _ _ _ _ hz)

/-- **A segment's later moment**, at rounds that fit and a plan that passes. -/
theorem commitOwn_rel (H : GroundQuiet R) (hA : AdmitOn R) (P : Par) (hB : planOkOwn P = true)
    (link moment : Nat) (arrays : Option (List Nat)) (s s' : Owing (L3.St (DState Unit)))
    (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64)))
    (hfit : roundsFit (rounds P) rs = true)
    (h : (commitOwn (Cl := Cl) P link moment arrays).decide s (rs.map noDigest) gs = .ok s') :
    R s.held.w.st s'.held.w.st := by
  obtain ⟨r₁, r₂, rfl⟩ := fit_two _ _ rs hfit
  simp only [commitOwn] at h
  split at h
  · split at h
    · cases h
    · obtain ⟨x, h1, h2⟩ := Keeps.emap_ok h
      subst h2
      unfold L3.commitStep at h1
      obtain ⟨_, _, h1⟩ := (bind_ok _ _ _).1 h1
      obtain ⟨⟨check, w⟩, h3, h1⟩ := (bind_ok _ _ _).1 h1
      dsimp only at h1
      obtain ⟨⟨L', F'⟩, _, h1⟩ := (bind_ok _ _ _).1 h1
      cases h1
      exact laterOwn_rel H hA P hB s.owed _ _ (noDigest r₁) (noDigest r₂) hfit _ h3
  · cases h

/-- **The first segment's opening**, at rounds that fit and a plan that passes. -/
theorem firstOwn_rel (H : GroundQuiet R) (hA : AdmitOn R) (P : Par) (hB : planOkOwn P = true)
    (owed : Option Nat) (c : ChainCheck) (d : DState Unit) (r₁ r₂ : Fmt.RoundView)
    (hfit : roundsFit (rounds P) [r₁, r₂] = true) (y : ChainCheck × DState Unit)
    (h : firstOwn P owed c d [r₁, r₂] = .ok y) : R d.st y.2.st := by
  unfold firstOwn at h
  dsimp only at h
  obtain ⟨_, _, h⟩ := (bind_ok _ _ _).1 h
  obtain ⟨_, _, h⟩ := (bind_ok _ _ _).1 h
  obtain ⟨_, _, h⟩ := (bind_ok _ _ _).1 h
  obtain ⟨_, _, h⟩ := (bind_ok _ _ _).1 h
  obtain ⟨_, _, h⟩ := (bind_ok _ _ _).1 h
  obtain ⟨_, _, h⟩ := (bind_ok _ _ _).1 h
  obtain ⟨⟨g, d₁⟩, h1, h⟩ := (bind_ok _ _ _).1 h
  dsimp only at h
  obtain ⟨_, _, h⟩ := (bind_ok _ _ _).1 h
  obtain ⟨⟨ids, d₂⟩, h2, h⟩ := (bind_ok _ _ _).1 h
  dsimp only at h
  obtain ⟨_, _, h⟩ := (bind_ok _ _ _).1 h
  obtain ⟨_, _, h⟩ := (bind_ok _ _ _).1 h
  obtain ⟨⟨f₂, d₃⟩, h3, h⟩ := (bind_ok _ _ _).1 h
  cases h
  exact H.trans (H.trans (H.newGroup d d₁ _ _ g ((named_ok _ _ _).1 h1))
    (decideSend_rel H hA P owed d₁ d₂ r₁ r₂ ids hB hfit h2))
    (joinOwnP_rel H _ _ _ _ _ _ ((named_ok _ _ _).1 h3))

/-! ## At the first chain's record -/

/-- **W's sending, at the first chain's record.** -/
theorem sendAtS_fits (H : GroundQuiet R) (hA : AdmitOn R) (P : Par) :
    Fits (By R fun s : S => s.st) (sendAtS (Cl := Cl) P) := by
  intro hp s rs gs s' hfit h
  have hB : planOkOwn P = true := hp
  have hfit' : roundsFit (rounds P) rs = true := hfit
  simp only [sendAtS] at h
  split at h
  · split at h
    · obtain ⟨y, h1, h2⟩ := Keeps.emap_ok h
      subst h2
      exact sendOwn_rel (Cl := Cl) H hA P hB _ _ rs _ hfit' h1
    · cases h
  · cases h

/-- **A segment's later moment, at the first chain's record.** -/
theorem commitAtS_fits (H : GroundQuiet R) (hA : AdmitOn R) (P : Par) (link moment : Nat)
    (arrays : Option (List Nat)) :
    Fits (By R fun s : S => s.st) (commitAtS (Cl := Cl) P link moment arrays) := by
  intro hp s rs gs s' hfit h
  have hp' : (planOkOwn P && arrays.isSome) = true := hp
  have hB : planOkOwn P = true := (Bool.and_eq_true _ _ ▸ hp').1
  have hfit' : roundsFit (rounds P) rs = true := hfit
  simp only [commitAtS] at h
  split at h
  · obtain ⟨y, h1, h2⟩ := Keeps.emap_ok h
    subst h2
    show R s.st (((laid s y.held.w).putLink y.held.L).putFork y.held.F).st
    rw [putFork_st, putLink_st]
    exact commitOwn_rel (Cl := Cl) H hA P hB link moment arrays _ _ rs _ hfit' h1
  · cases h

/-- **The first segment's opening, at the first chain's record.** -/
theorem firstAtS_fits (H : GroundQuiet R) (hA : AdmitOn R) (q : Params.First) (gp : GPar) :
    Fits (By R fun s : S => s.st) (firstSegmentOpening (Cl := Cl) q gp) := by
  intro hp s rs gs s' hfit h
  simp only [firstSegmentOpening, Bool.and_eq_true] at hp hfit h
  obtain ⟨r₁, r₂, rfl⟩ := fit_two _ _ rs hfit
  obtain ⟨_, _, h⟩ := (bind_ok _ _ _).1 h
  obtain ⟨⟨c, d⟩, h1, h⟩ := (bind_ok _ _ _).1 h
  cases h
  exact firstOwn_rel H hA _ hp.1 _ _ _ (noDigest r₁) (noDigest r₂) hfit _ h1

theorem sendAtS_steps (H : GroundQuiet R) (hA : AdmitOn R) (P : Par) :
    Steps (By R fun s : S => s.st) (sendAtS (Cl := Cl) P) := steps_of_fits (sendAtS_fits H hA P)

theorem commitAtS_steps (H : GroundQuiet R) (hA : AdmitOn R) (P : Par) (link moment : Nat)
    (arrays : Option (List Nat)) :
    Steps (By R fun s : S => s.st) (commitAtS (Cl := Cl) P link moment arrays) :=
  steps_of_fits (commitAtS_fits H hA P link moment arrays)

theorem firstAtS_steps (H : GroundQuiet R) (hA : AdmitOn R) (q : Params.First) (gp : GPar) :
    Steps (By R fun s : S => s.st) (firstSegmentOpening (Cl := Cl) q gp) :=
  steps_of_fits (firstAtS_fits H hA q gp)

/-! ## Quiet steps -/

variable {K : Type} [CommRing K] (ρ : OnBytes.Model.Reading K)

theorem sendAtS_quiet (P : Par) :
    Steps (By (Means.Quiet ρ) fun s : S => s.st) (sendAtS (Cl := Cl) P) :=
  sendAtS_steps (Means.groundQuiet_quiet ρ) (admitOn_quiet ρ) P

theorem commitAtS_quiet (P : Par) (link moment : Nat) (arrays : Option (List Nat)) :
    Steps (By (Means.Quiet ρ) fun s : S => s.st) (commitAtS (Cl := Cl) P link moment arrays) :=
  commitAtS_steps (Means.groundQuiet_quiet ρ) (admitOn_quiet ρ) P link moment arrays

theorem firstAtS_quiet (q : Params.First) (gp : GPar) :
    Steps (By (Means.Quiet ρ) fun s : S => s.st) (firstSegmentOpening (Cl := Cl) q gp) :=
  firstAtS_steps (Means.groundQuiet_quiet ρ) (admitOn_quiet ρ) q gp

end VerifiableInference.Desc.K1
