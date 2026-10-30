-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K1/Law/CallsI.lean: K01_law: THE BINDER hIo OF hOrder_of (Johnson/Desc/K1/Law/CallsO.lean) («what "in order" says beside inOrderK13 rides over a later sending's accept»), PAID WHERE io0 IS A TEST ON THE PUBLIC PART AND groupAllB: io0 a = (ioP a.1 && groupAllB N a.2): the public part is left by the
accept (YesOf's first clause); groupAllB rides: the open link's frame's group is left (LaterGroup, Johnson/Desc/K1/Law/GroupIsAt.lean) and so is the open link's number (StepL.link).
  stepL_blkL · groupAll_later · hIo_of · ioLive_of
Nothing on soundness.
-/
import Johnson.Desc.K1.Law.CallsG

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K1
open OnBytes OnBytes.Params OnBytes.Model Desc.Plain
open OnBytes.Maker
open VerifiableInference.Desc.First (S Numbers)
open OnBytes.Model.Stages (LinkH)
open IM (k1Ix k1Reads)

variable {Pp : Type}

/-- An accept of the place's sub-protocol on two rounds is a step of the sort StepL, at the group that the open link's frame names. -/
theorem stepL_blkL (Z : ProofFile.Pub) (G : ProofFile.Ground) (l : ℕ) (d : Bool) (X : LinkH)
    (arrs : Option (List ℕ)) (s s' : S) (r₁ r₂ : Fmt.RoundView) (gs : List (List (Nat × List UInt64)))
    (h : (blkL Z G l d X arrs).decide s [r₁, r₂] gs = .ok s') (g : ℕ)
    (hg : ∀ L, s.link? = some L → L.check.frame.group = g) (z : Pp) :
    StepL (parL Z G l d) g (z, s) (z, s') := by
  cases d with
  | true => exact stepL_commitAtS _ _ _ _ s s' r₁ r₂ gs h g hg z
  | false => exact stepL_k1Reads Z G l X _ arrs s s' r₁ r₂ gs h g hg z

/-- **groupAllB rides.** -/
theorem groupAll_later (N : Numbers) (Z : ProofFile.Pub) (G : ProofFile.Ground) (l : ℕ) (d : Bool) (X : LinkH)
    (arrs : Option (List ℕ)) (x x' : Pp × S) (hy : YesOf (blkL Z G l d X arrs) x x')
    (h0 : groupAllB N x.2 = true) : groupAllB N x'.2 = true := by
  obtain ⟨_, rs, gs, hfit, hd⟩ := hy
  have h2 : (rs.map noDigest).length = 2 := by
    rw [List.length_map, K13.Law.roundsFit_length _ _ hfit, two_blkL]
  obtain ⟨r₁, r₂, e⟩ := List.length_eq_two.1 h2
  have hG := laterGroup_blkL Z G l d X arrs _ _ _ _ h2 hd
  rw [e] at hd
  unfold groupAllB at h0 ⊢
  cases hL' : x'.2.link? with
  | none => rfl
  | some L' =>
    cases hL : x.2.link? with
    | none =>
      unfold groupOf at hG
      rw [hL', hL] at hG
      cases hG
    | some L =>
      have hst := stepL_blkL Z G l d X arrs x.2 x'.2 r₁ r₂ gs hd L.check.frame.group
        (fun L₀ h₀ => by rw [hL] at h₀; cases h₀; rfl) x.1
      obtain ⟨L₁, h₁, e₁⟩ := hst.link L' hL'
      have h₁' : x.2.link? = some L₁ := h₁
      rw [hL] at h₁'
      cases h₁'
      unfold groupOf at hG
      rw [hL', hL, Option.map_some, Option.map_some] at hG
      rw [hL, Option.all_some] at h0
      rw [Option.all_some, Option.some.inj hG, e₁]
      exact h0

/-! ## The open link's frame's shape rides (after LaterGroup, Johnson/Desc/K1/Law/GroupIsAt.lean) -/

/-- The shape that the open link's frame names; nothing where no link is open. -/
def shapeOfL (s : S) : Option Params.ReqShape := s.link?.map fun L => L.check.frame.shape

/-- An accept of B on two rounds leaves it. -/
def LaterShape {Cl : Type} (B : Block S Cl) : Prop :=
  ∀ s s' rs gs, rs.length = 2 → B.decide s rs gs = .ok s' → shapeOfL s' = shapeOfL s

theorem laterShape_commitAtS {Cl : Type} (P : Par) (link moment : Nat) (arrays : Option (List Nat)) :
    LaterShape (commitAtS P link moment arrays : Block S Cl) := by
  intro s s' rs gs h2 h
  obtain ⟨r₁, r₂, rfl⟩ := List.length_eq_two.1 h2
  obtain ⟨L, L', hL, hL', hfr, _⟩ := commitAtS_frame P link moment arrays s s' r₁ r₂ gs h
  unfold shapeOfL
  rw [hL, hL', Option.map_some, Option.map_some, hfr]

theorem laterShape_joined {Cl : Type} (P : Par) (link moment : Nat) (arrays : Option (List Nat))
    (nm : String) (q : Block S Cl) (hq : QuietP q) :
    LaterShape (Block.andThen nm (commitAtS P link moment arrays) q) := by
  intro s s' rs gs h2 h
  obtain ⟨r₁, r₂, rfl⟩ := List.length_eq_two.1 h2
  obtain ⟨s₁, gs₁, rs₂, gs₂, h1, h3⟩ := joined_yes P link moment arrays nm q s s' r₁ r₂ gs h
  have e : shapeOfL s' = shapeOfL s₁ := by
    unfold shapeOfL
    rw [(hq _ _ _ _ h3).2.2.2.1]
  exact e.trans (laterShape_commitAtS P link moment arrays s s₁ _ gs₁ rfl h1)

theorem laterShape_blkL (Z : ProofFile.Pub) (G : ProofFile.Ground) (l : ℕ) (d : Bool) (X : LinkH)
    (arrs : Option (List ℕ)) : LaterShape (blkL Z G l d X arrs) := by
  cases d with
  | true => exact laterShape_commitAtS _ _ _ _
  | false => exact laterShape_joined _ _ _ _ _ _ (quietP_orLoud _ _ _ G l X _)

/-- **liveShapeB rides.** -/
theorem liveShape_later (sh : Params.ReqShape) (Z : ProofFile.Pub) (G : ProofFile.Ground) (l : ℕ) (d : Bool)
    (X : LinkH) (arrs : Option (List ℕ)) (x x' : Pp × S) (hy : YesOf (blkL Z G l d X arrs) x x')
    (h0 : liveShapeB sh x.2 = true) : liveShapeB sh x'.2 = true := by
  obtain ⟨_, rs, gs, hfit, hd⟩ := hy
  have h2 : (rs.map noDigest).length = 2 := by
    rw [List.length_map, K13.Law.roundsFit_length _ _ hfit, two_blkL]
  have hG := laterShape_blkL Z G l d X arrs _ _ _ _ h2 hd
  unfold liveShapeB at h0 ⊢
  unfold shapeOfL at hG
  cases hL' : x'.2.link? with
  | none => rfl
  | some L' =>
    cases hL : x.2.link? with
    | none =>
      rw [hL', hL] at hG
      cases hG
    | some L =>
      rw [hL', hL, Option.map_some, Option.map_some] at hG
      rw [hL, Option.all_some] at h0
      rw [Option.all_some, Option.some.inj hG]
      exact h0

/-- **liveB rides.** -/
theorem live_later (N : Numbers) (sh : Params.ReqShape) (Z : ProofFile.Pub) (G : ProofFile.Ground) (l : ℕ)
    (d : Bool) (X : LinkH) (arrs : Option (List ℕ)) (x x' : Pp × S)
    (hy : YesOf (blkL Z G l d X arrs) x x') (h0 : liveB N sh x.2 = true) :
    liveB N sh x'.2 = true := by
  unfold liveB at h0 ⊢
  rw [Bool.and_eq_true] at h0 ⊢
  exact ⟨groupAll_later N Z G l d X arrs x x' hy h0.1, liveShape_later sh Z G l d X arrs x x' hy h0.2⟩

/-- **hIo, to the binder's letter.** -/
theorem hIo_of (N : Numbers) (sh : Params.ReqShape) (xb : S → Bool) (io0 : Pp × S → Bool)
    (ioP : Pp → Bool) (h : ∀ a, io0 a = (ioP a.1 && liveX N sh xb a.2)) (Z : ProofFile.Pub)
    (G : ProofFile.Ground) (l : ℕ) (d : Bool) (X : LinkH) (arrs : Option (List ℕ))
    (hx : ∀ x x' : Pp × S, YesOf (blkL Z G l d X arrs) x x' → xb x.2 = true → xb x'.2 = true)
    (x x' : Pp × S) (hy : YesOf (blkL Z G l d X arrs) x x') (h0 : io0 x = true) :
    io0 x' = true := by
  rw [h, Bool.and_eq_true] at h0 ⊢
  obtain ⟨a0, a1⟩ := h0
  unfold liveX at a1 ⊢
  rw [Bool.and_eq_true] at a1 ⊢
  exact ⟨by rw [hy.1]; exact a0, live_later N sh Z G l d X arrs x x' hy a1.1, hx x x' hy a1.2⟩

/-- LaidK1's field ioLive, there. -/
theorem ioLive_of (N : Numbers) (sh : Params.ReqShape) (xb : S → Bool) (io0 : Pp × S → Bool)
    (ioP : Pp → Bool) (h : ∀ a, io0 a = (ioP a.1 && liveX N sh xb a.2)) (a : Pp × S)
    (h0 : io0 a = true) : liveB N sh a.2 = true := by
  rw [h, Bool.and_eq_true] at h0
  have a1 := h0.2
  unfold liveX at a1
  rw [Bool.and_eq_true] at a1
  exact a1.1

end VerifiableInference.Desc.K1

#print axioms VerifiableInference.Desc.K1.groupAll_later
#print axioms VerifiableInference.Desc.K1.live_later
#print axioms VerifiableInference.Desc.K1.hIo_of
