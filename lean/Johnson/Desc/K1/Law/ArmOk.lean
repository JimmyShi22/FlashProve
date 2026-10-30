-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K1/Law/ArmOk.lean: a guard that makes any sentence on the
verifier's state, wanted in front of a link's reads alone, free of the border and riding over K1's fifty
later places for nothing.
WHY. The binder hArm of K01_law's fifty later places binds every state inside the promise; several of
what the three sorts' halves of the exchange still ask are facts that only a state which the verifier reaches
meets. Such a fact reaches the tie through the wider promise alone (`mw1`'s letter xb): one Bool at both
borders of all fifty places, which must ride over each place's accept.
OBJECT: `blkL Z G l d X arrs` (LaterOne.lean); the open link's frame's field `moment`.
USER: the top of K01_law's fifty later places (its premise hxb and its letter xb);
Johnson/Desc/K1/Law/ArmAtReads.lean.
LETTERS: J (any sentence on the state); Z, G, l, d, X, arrs; x, x'.
  `AtMoment1 s`      the open link's frame announces its second commitment (moment 1)
  `ArmOk J s`        AtMoment1 s → J s
  `armOk_idle`       where the open link's frame stands at another moment, or no link is open: ArmOk J
  `commitAtS_moment` an accept of a later commitment at moment m: in front the frame stands at m (the
                   sub-protocol's own test, Johnson/Desc/K1/Own.lean)
  `LaterMoment`, `laterMoment_blkL`   in front of the place (l, d) the frame stands at `momL d` (1 at the
                   reads, 2 at the digits), behind at one more
  `atMoment1_of_yes` **in front of an accept at a link's reads: AtMoment1**
  `armOk_later`      **behind an accept at any of the fifty: ArmOk J, whatever J is** (the guard is false)
So along the states that the verifier reaches ArmOk J is owed at one border a link alone: in front of the
reads; at the other three borders of a link's two later places it is idle.
What is not claimed. J at any state. Nothing on soundness.

-/
import Johnson.Desc.K1.Law.LookAtLater
import Johnson.Desc.K1.Law.APileOf
import Johnson.Desc.K1.Law.FrameAtLater

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K1
open OnBytes OnBytes.Params OnBytes.Model
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Keeps (Decides)
open OnBytes.Model.Stages (LinkH)

variable {Cl Pp : Type}

/-- The open link's frame announces its second commitment. -/
def AtMoment1 (s : S) : Prop := ∃ L, s.link? = some L ∧ L.check.frame.moment = 1

/-- **J, where the state stands in front of its link's second commitment.** -/
def ArmOk (J : S → Prop) (s : S) : Prop := AtMoment1 s → J s

/-- Where the frame stands at another moment, or no link is open, the sentence is idle. -/
theorem armOk_idle (J : S → Prop) (s : S)
    (h : ∀ L, s.link? = some L → L.check.frame.moment ≠ 1) : ArmOk J s :=
  fun ⟨L, a, e⟩ => absurd e (h L a)

/-- An accept of a later commitment at moment m: in front the frame stands at m. -/
theorem commitAtS_moment (P : Par) (link moment : Nat) (arrays : Option (List Nat)) (s s' : S)
    (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64)))
    (h : (commitAtS P link moment arrays : Block S Cl).decide s rs gs = .ok s') :
    ∃ L, s.link? = some L ∧ L.check.frame.moment = moment := by
  unfold commitAtS at h
  dsimp only at h
  split at h
  · rename_i L F tl hL _ _
    obtain ⟨y, hy, rfl⟩ := (map_ok _ _ _).1 h
    simp only [commitOwn] at hy
    split at hy
    · rename_i hc
      simp only [Bool.and_eq_true, beq_iff_eq] at hc
      exact ⟨L, hL, hc.1.2⟩
    · cases hy
  · cases h

/-- An accept of B on two rounds: the frame stands at m in front and at m + 1 behind. -/
def LaterMoment (m : ℕ) (B : Block S Cl) : Prop :=
  ∀ (s s' : S) rs gs, rs.length = 2 → B.decide s rs gs = .ok s' →
    ∃ L L', s.link? = some L ∧ s'.link? = some L' ∧ L.check.frame.moment = m ∧
      L'.check.frame.moment = m + 1

theorem laterMoment_commitAtS (P : Par) (link moment : Nat) (arrays : Option (List Nat)) :
    LaterMoment moment (commitAtS P link moment arrays : Block S Cl) := by
  intro s s' rs gs h2 h
  obtain ⟨L₀, a₀, em⟩ := commitAtS_moment P link moment arrays s s' rs gs h
  obtain ⟨r₁, r₂, rfl⟩ := List.length_eq_two.1 h2
  obtain ⟨L, L', a, b, e, _⟩ := commitAtS_frame P link moment arrays s s' r₁ r₂ gs h
  obtain rfl : L₀ = L := Option.some.inj (a₀.symm.trans a)
  exact ⟨L₀, L', a, b, em, by rw [e, ← em]⟩

theorem laterMoment_laterAt (q : Params.First) (gp : _root_.Desc.Plain.GPar)
    (link piece moment : Nat) (arrays : Option (List Nat)) :
    LaterMoment moment (laterAt q gp link piece moment arrays : Block S Cl) :=
  laterMoment_commitAtS _ _ _ _

theorem laterMoment_joined (P : Par) (link moment : Nat) (arrays : Option (List Nat)) (nm : String)
    (q : Block S Cl) (hq : Decides LookSame q) :
    LaterMoment moment (Block.andThen nm (commitAtS P link moment arrays) q) := by
  intro s s' rs gs h2 h
  obtain ⟨r₁, r₂, rfl⟩ := List.length_eq_two.1 h2
  obtain ⟨s₁, gs₁, rs₂, gs₂, h1, h3⟩ := joined_yes P link moment arrays nm q s s' r₁ r₂ gs h
  obtain ⟨L, L', a, b, e1, e2⟩ := laterMoment_commitAtS P link moment arrays s s₁ _ gs₁ rfl h1
  exact ⟨L, L', a, (hq _ _ _ _ h3).link.trans b, e1, e2⟩

theorem laterMoment_k1Reads (Z : ProofFile.Pub) (G : ProofFile.Ground) (l : Nat) (X : LinkH) (pr : Nat)
    (reads : Option (List Nat)) : LaterMoment 1 (IM.k1Reads Z G l X pr reads) :=
  laterMoment_joined _ _ _ _ _ _ (lookSame_k1Quiet G l X)

theorem laterMoment_blkL (Z : ProofFile.Pub) (G : ProofFile.Ground) (l : ℕ) (d : Bool) (X : LinkH)
    (arrs : Option (List ℕ)) : LaterMoment (momL d) (blkL Z G l d X arrs) := by
  cases d with
  | true => exact laterMoment_laterAt _ _ _ _ _ _
  | false => exact laterMoment_k1Reads _ _ _ _ _ _

/-- **In front of an accept at a link's reads the frame stands at moment 1.** -/
theorem atMoment1_of_yes (Z : ProofFile.Pub) (G : ProofFile.Ground) (l : ℕ) (X : LinkH)
    (arrs : Option (List ℕ)) (x x' : Pp × S) (hy : YesOf (blkL Z G l false X arrs) x x') :
    AtMoment1 x.2 := by
  obtain ⟨_, rs, gs, hfit, hd⟩ := hy
  have hlen : (rs.map noDigest).length = 2 := by
    rw [List.length_map, Keeps.fit_length _ _ hfit, rounds_blkL]
  obtain ⟨L, _, a, _, e, _⟩ := laterMoment_blkL Z G l false X arrs _ _ _ gs hlen hd
  exact ⟨L, a, e⟩

/-- **Behind an accept at any of the fifty later places ArmOk J holds, whatever J is.** -/
theorem armOk_later (J : S → Prop) (Z : ProofFile.Pub) (G : ProofFile.Ground) (l : ℕ) (d : Bool) (X : LinkH)
    (arrs : Option (List ℕ)) (x x' : Pp × S) (hy : YesOf (blkL Z G l d X arrs) x x') :
    ArmOk J x'.2 := by
  obtain ⟨_, rs, gs, hfit, hd⟩ := hy
  have hlen : (rs.map noDigest).length = 2 := by
    rw [List.length_map, Keeps.fit_length _ _ hfit, rounds_blkL]
  obtain ⟨_, L', _, b, _, e⟩ := laterMoment_blkL Z G l d X arrs _ _ _ gs hlen hd
  rintro ⟨L₂, b₂, e₂⟩
  obtain rfl : L' = L₂ := Option.some.inj (b.symm.trans b₂)
  rw [e] at e₂
  cases d <;> cases e₂

end VerifiableInference.Desc.K1

#print axioms VerifiableInference.Desc.K1.armOk_idle
#print axioms VerifiableInference.Desc.K1.commitAtS_moment
#print axioms VerifiableInference.Desc.K1.laterMoment_blkL
#print axioms VerifiableInference.Desc.K1.atMoment1_of_yes
#print axioms VerifiableInference.Desc.K1.armOk_later
