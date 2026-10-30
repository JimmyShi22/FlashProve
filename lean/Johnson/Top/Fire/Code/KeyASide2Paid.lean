-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/Fire/Code/KeyASide2Paid.lean: THE SHARED CHAIN's FOLD (KeyASide2AtFk.lean) WITH THE TWO
STEPS STRUCK THAT LEAVE THE STATE: 0 → 1 (the chain's front) AND 11 → 12 (the chain's end): CALLS OF
front₂_same | chainEnd_same (Johnson/RunOne/KeyKeepsAt23.lean) AND shared_flat (KeyCut23.lean).
  tests₂_01 | tests₂_1112   PROVED: at ONE state Tests₂ passes from 0 to 1 and from
                            11 to 12: the book-keeping is an equation; the open pins from 3 on
                            are the same list; the clauses under «2 ≤ k» … are idle | carried
  front_at | end_at         PROVED: which block stands at shared.blocksInOrder[0] | [11] (the second under
    ONE
                            PUBLIC PREMISE: the shared chain has twelve blocks: in scope
                            lengths_in_scope, KeyRoundsAtSeat.lean)
  g0_paid | g11_paid        PROVED: the two steps in StepInvP's form
  Left₂                   A NAMED PREMISE: WHAT IS LEFT: THE START AND TEN STEPS, EACH WITH A WORD
                            ON WHERE IT STANDS, AT Tests₂ ALONE (no letter H: for one, use Gaps₂)
  gaps₂_of_left             PROVED: Left₂ gives Gaps₂ at H := fun _ _ => True
  aSide₂_of_left            PROVED: k ≤ 12: the fold under Left₂
OBJECT · USER · LETTERS: as KeyASide2AtFk.lean.
AN IMPLICATION: ELEVEN OF ITS THIRTEEN LEGS ARE STILL PREMISES HERE: IT SAYS LITTLE OF THE SHARED
CHAIN UNTIL THEY ARE PAID. OF THE TEN STEPS EIGHT ARE TYPED ON THE STATE ALONE (tests₂_12 …
tests₂_89, Johnson/RunOne/KeyTestsStep.lean) AND WANT A BRIDGE FROM THE BLOCK's YES; g9 | g10 ARE OTHER FILES'.
(Where this and lean/THEOREM.md differ, the page holds.) THE START
  (s0) IS TYPED IN PARTS (aSide_at_all · e18_at_end ·
shape₂_first · codes_of_last). IN SCOPE, AT atSix · off₂N, ALL THIRTEEN ARE PAID: KeyASide2All.lean.
Nothing on soundness.
-/
import Johnson.Top.Fire.Code.KeyASide2AtFk
import Johnson.RunOne.KeyKeepsAt23

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LPFD
open OnBytes OnBytes.Params OnBytes.Maker
open VerifiableInference.Desc VerifiableInference.Desc.Key VerifiableInference.Desc.Sound
open VerifiableInference.Desc.Plain
open VerifiableInference.Desc.Key (FirstState Claim Xi)
open Johnson.RunOne.KeyRows1 (plan₁)
open Johnson.RunOne.KeyRows23

section
variable (at_ : Where) (S : LinShape) (K₁ : KPlan) (a : ℕ) (last₁ : FirstState → Bool)
  (off₂ : ℕ → ℕ)

/-- At one state: from border 0 to border 1. -/
theorem tests₂_01 (z : P₂ × St₂) (T : Tests₂ at_ S K₁ a last₁ off₂ 0 z) :
    Tests₂ at_ S K₁ a last₁ off₂ 1 z :=
  { shape := T.shape, last := T.last, eval := T.eval, placed₁ := T.placed₁, order₁ := T.order₁
    key := T.key, codes := T.codes, lay := fun h => absurd h (by decide)
    placed := by
      have e : (pinned (open₂ 1)).filter (3 ≤ ·) = (pinned (open₂ 0)).filter (3 ≤ ·) := by decide
      rw [e]
      exact T.placed
    order := T.order, linOk := fun h => absurd h (by decide)
    seatU := fun h => absurd h (by decide), seatOmega := fun h => absurd h (by decide)
    fits := T.fits, mask₁ := T.mask₁, maskU := fun h => absurd h (by decide) }

/-- At one state: from border 11 to border 12. -/
theorem tests₂_1112 (z : P₂ × St₂) (T : Tests₂ at_ S K₁ a last₁ off₂ 11 z) :
    Tests₂ at_ S K₁ a last₁ off₂ 12 z :=
  { shape := T.shape, last := T.last, eval := T.eval, placed₁ := T.placed₁, order₁ := T.order₁
    key := T.key, codes := T.codes, lay := fun _ => T.lay (by decide)
    placed := by
      have e : (pinned (open₂ 12)).filter (3 ≤ ·) = (pinned (open₂ 11)).filter (3 ≤ ·) := by decide
      rw [e]
      exact T.placed
    order := T.order, linOk := fun _ => T.linOk (by decide)
    seatU := fun _ => T.seatU (by decide), seatOmega := fun _ => T.seatOmega (by decide)
    fits := T.fits, mask₁ := T.mask₁, maskU := fun _ => T.maskU (by decide) }

end

section
variable (X : Source) (N : H2U.PlaceNums) (P : LaterPlaces) (D : WholeD) (at_ : Where)
  (off₂ : ℕ → ℕ)

/-- The block at the shared chain's place 0 is the front's. -/
theorem front_at (b : Block St₂ Claim) (hb : (Fk X N P).shared.blocksInOrder[0]? = some b) :
    b = front₂ X := by
  rw [show (Fk X N P).shared.blocksInOrder = _ from shared_flat X N P] at hb
  exact (Option.some.inj hb).symm

/-- The block at place 11 is the chain's end, where the chain has twelve blocks. -/
theorem end_at (hlen : (Fk X N P).shared.blocksInOrder.length = 12) (b : Block St₂ Claim)
    (hb : (Fk X N P).shared.blocksInOrder[11]? = some b) :
    b = seat (VerifiableInference.Desc.K12.Seat.last (inFront₂ X P)) := by
  have h12 : (front₂ X :: (inFront₂ X P ++
      [VerifiableInference.Desc.K12.Seat.last (inFront₂ X P)]).map seat).length = 12 := by
    rw [← shared_flat X N P]
    exact hlen
  rw [show (Fk X N P).shared.blocksInOrder = _ from shared_flat X N P] at hb
  have hl : (inFront₂ X P).length = 10 := by
    simp only [List.length_cons, List.length_map, List.length_append, List.length_nil] at h12
    omega
  have h2 : ((inFront₂ X P ++ [VerifiableInference.Desc.K12.Seat.last (inFront₂ X P)]).map
      seat)[10]? = some b := hb
  rw [List.getElem?_map, List.getElem?_append_right (by rw [hl]), hl] at h2
  exact (Option.some.inj h2).symm

/-- **0 → 1.** -/
theorem g0_paid (b : Block St₂ Claim) (hb : (Fk X N P).shared.blocksInOrder[0]? = some b) :
    StepInvP b (T₂ X at_ off₂ 0) (T₂ X at_ off₂ 1) := by
  obtain rfl := front_at X N P b hb
  intro p s s' rs gs _ hy T
  obtain rfl := front₂_same X s _ gs s' hy
  exact tests₂_01 at_ _ _ _ _ off₂ _ T

/-- **11 → 12.** -/
theorem g11_paid (hlen : (Fk X N P).shared.blocksInOrder.length = 12) (b : Block St₂ Claim)
    (hb : (Fk X N P).shared.blocksInOrder[11]? = some b) :
    StepInvP b (T₂ X at_ off₂ 11) (T₂ X at_ off₂ 12) := by
  obtain rfl := end_at X N P hlen b hb
  intro p s s' rs gs _ hy T
  obtain rfl := chainEnd_same (Cl := Unit) 2 11 true ((inFront₂ X P).flatMap (·.rounds))
    (fun d : St₂ => ChainEnd.untestedL d.st) s (rs.map noDigest) gs s' hy
  exact tests₂_1112 at_ _ _ _ _ off₂ _ T

/-- **What is left: the start and ten steps** (where each stands: the file's head). -/
structure Left₂ : Prop where
  /-- the start -/
  s0 : ∀ a, st₂ (Fk X N P) D a → a.1.1.key.fits (shapeAt X).fold.index = true → T₂ X at_ off₂ 0 a
  /-- 1 → 2 -/
  g1 : ∀ b, (Fk X N P).shared.blocksInOrder[1]? = some b →
    StepInvP b (T₂ X at_ off₂ 1) (T₂ X at_ off₂ 2)
  /-- 2 → 3 -/
  g2 : ∀ b, (Fk X N P).shared.blocksInOrder[2]? = some b →
    StepInvP b (T₂ X at_ off₂ 2) (T₂ X at_ off₂ 3)
  /-- 3 → 4 -/
  g3 : ∀ b, (Fk X N P).shared.blocksInOrder[3]? = some b →
    StepInvP b (T₂ X at_ off₂ 3) (T₂ X at_ off₂ 4)
  /-- 4 → 5 -/
  g4 : ∀ b, (Fk X N P).shared.blocksInOrder[4]? = some b →
    StepInvP b (T₂ X at_ off₂ 4) (T₂ X at_ off₂ 5)
  /-- 5 → 6 -/
  g5 : ∀ b, (Fk X N P).shared.blocksInOrder[5]? = some b →
    StepInvP b (T₂ X at_ off₂ 5) (T₂ X at_ off₂ 6)
  /-- 6 → 7 -/
  g6 : ∀ b, (Fk X N P).shared.blocksInOrder[6]? = some b →
    StepInvP b (T₂ X at_ off₂ 6) (T₂ X at_ off₂ 7)
  /-- 7 → 8 -/
  g7 : ∀ b, (Fk X N P).shared.blocksInOrder[7]? = some b →
    StepInvP b (T₂ X at_ off₂ 7) (T₂ X at_ off₂ 8)
  /-- 8 → 9 -/
  g8 : ∀ b, (Fk X N P).shared.blocksInOrder[8]? = some b →
    StepInvP b (T₂ X at_ off₂ 8) (T₂ X at_ off₂ 9)
  /-- 9 → 10: the proximity test of G_u -/
  g9 : ∀ b, (Fk X N P).shared.blocksInOrder[9]? = some b →
    StepInvP b (T₂ X at_ off₂ 9) (T₂ X at_ off₂ 10)
  /-- 10 → 11: the proximity test of G_omega -/
  g10 : ∀ b, (Fk X N P).shared.blocksInOrder[10]? = some b →
    StepInvP b (T₂ X at_ off₂ 10) (T₂ X at_ off₂ 11)

/-- A step at Tests₂ alone is a step of the fold's invariant at the idle letter. -/
theorem plainStep₂ (k : ℕ) (b : Block St₂ Claim)
    (h : StepInvP b (T₂ X at_ off₂ k) (T₂ X at_ off₂ (k + 1))) :
    StepInvP b (T₂H X at_ off₂ (fun _ _ => True) k) (T₂H X at_ off₂ (fun _ _ => True) (k + 1)) :=
  fun p s s' rs gs hf hy hA => ⟨h p s s' rs gs hf hy hA.1, trivial⟩

theorem gaps₂_of_left (hlen : (Fk X N P).shared.blocksInOrder.length = 12) (L : Left₂ X N P D at_ off₂) :
    Gaps₂ X N P D at_ off₂ (fun _ _ => True) where
  s0 := fun a ha hf => ⟨L.s0 a ha hf, trivial⟩
  g0 := fun b hb => plainStep₂ X at_ off₂ 0 b (g0_paid X N P at_ off₂ b hb)
  g1 := fun b hb => plainStep₂ X at_ off₂ 1 b (L.g1 b hb)
  g2 := fun b hb => plainStep₂ X at_ off₂ 2 b (L.g2 b hb)
  g3 := fun b hb => plainStep₂ X at_ off₂ 3 b (L.g3 b hb)
  g4 := fun b hb => plainStep₂ X at_ off₂ 4 b (L.g4 b hb)
  g5 := fun b hb => plainStep₂ X at_ off₂ 5 b (L.g5 b hb)
  g6 := fun b hb => plainStep₂ X at_ off₂ 6 b (L.g6 b hb)
  g7 := fun b hb => plainStep₂ X at_ off₂ 7 b (L.g7 b hb)
  g8 := fun b hb => plainStep₂ X at_ off₂ 8 b (L.g8 b hb)
  g9 := fun b hb => plainStep₂ X at_ off₂ 9 b (L.g9 b hb)
  g10 := fun b hb => plainStep₂ X at_ off₂ 10 b (L.g10 b hb)
  g11 := fun b hb => plainStep₂ X at_ off₂ 11 b (g11_paid X N P at_ off₂ hlen b hb)

/-- **The fold, under what is left.** -/
theorem aSide₂_of_left (hlen : (Fk X N P).shared.blocksInOrder.length = 12) (L : Left₂ X N P D at_ off₂)
    (k : ℕ) (a : P₂ × St₂) (hk : k ≤ 12) (hist : Hist₂ (Fk X N P) D k a)
    (hfit : a.1.1.key.fits (shapeAt X).fold.index = true) : T₂ X at_ off₂ k a :=
  aSide₂_of_hist X N P D at_ off₂ _ (gaps₂_of_left X N P D at_ off₂ hlen L) k a hk hist hfit

end

end LPFD

#print axioms LPFD.tests₂_01
#print axioms LPFD.tests₂_1112
#print axioms LPFD.front_at
#print axioms LPFD.end_at
#print axioms LPFD.g0_paid
#print axioms LPFD.g11_paid
#print axioms LPFD.gaps₂_of_left
#print axioms LPFD.aSide₂_of_left
