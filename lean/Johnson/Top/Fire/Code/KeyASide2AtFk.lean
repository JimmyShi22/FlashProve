-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/Fire/Code/KeyASide2AtFk.lean: THE SHARED CHAIN's STATE's SIDE OF THE
PROMISE FROM THE HISTORY: THE FOLD, WITH EVERY STEP A NAMED FIELD. The sibling of
KeyASideAtFk.lean (chain 1: Gaps · aSide_of_hist). THE INVARIANT IS Tests₂
(Johnson/RunOne/KeyOn2Parts.lean: sixteen fields on the verifier's state): NO SECOND ONE IS
  DECLARED.
  T₂ X at_ off₂ k z   Tests₂ AT THE TABLES' OWN LETTERS (those of On₂, RunOne/KeyRowsAtFk.lean)
  Gaps₂ … H         A NAMED PREMISE: THE START AND THE TWELVE STEPS, EACH WITH A WORD ON WHERE IT
                      STANDS. HERE EVEN THE STEPS TYPED ELSEWHERE ARE FIELDS: each says so: they are
                      struck by calls in KeyASide2Paid.lean | KeyASide2Start.lean; what then stays: g2 · g5 · g9 · g10. (Where
                      this and lean/THEOREM.md differ, the page holds.)
                      H : ℕ → P₂ × St₂ → Prop IS A LETTER: what a step's proof wants of the state in
                      front beside Tests₂ (as at chain 1: KeyASideAtFk.lean's H₀ | H₁): at
                      H := fun _ _ => True it asks nothing.
  aSide₂_of_hist      PROVED: k ≤ 12, UNDER Gaps₂ AND ONE TEST ON THE INSTANCE (fits): at every
    state
                      that is reached at border k of the shared chain: T₂ … k
OBJECT: Tests₂ at Hist₂ (Fk X N P) D k a · USER: KeyASide2Paid.lean; meant: on₂_of_tests
(chain 2's members) · row 3.2's guard's last debt (shape₂ … 12 and placed of the handed shared
state) · LETTERS: X N P D · at_ · off₂ · H.
AN IMPLICATION: EMPTY WHERE NOTHING IS REACHED. THE STRINGS' SIDE (Strings₂) IS NOT HERE.
Nothing on soundness.
-/
import Johnson.Top.Fire.Code.ReachedInvPair
import Johnson.RunOne.KeyOn2Parts
import Johnson.RunOne.KeyRowsAtFk

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
variable (X : Source) (N : H2U.PlaceNums) (P : LaterPlaces) (D : WholeD) (at_ : Where)
  (off₂ : ℕ → ℕ)

/-- Tests₂ at the tables' own letters. -/
abbrev T₂ (k : ℕ) (z : P₂ × St₂) : Prop :=
  Tests₂ at_ (shapeAt X) (plan₁ (oneAt X)) (oneAt X).given.plan.samples (last₁At (oneAt X)) off₂ k z

/-- The fold's invariant at border k: Tests₂ and the letter. -/
abbrev T₂H (H : ℕ → P₂ × St₂ → Prop) (k : ℕ) (z : P₂ × St₂) : Prop := T₂ X at_ off₂ k z ∧ H k z

/-- **The start and the twelve steps, each with a word on where it stands.** -/
structure Gaps₂ (H : ℕ → P₂ × St₂ → Prop) : Prop where
  /-- THE START: other files' (last · placed₁ · order₁: ASide … 19; shape: shape₂_first; with
  eval · mask₁ at chain 1's end) (aSide_at_all · e18_at_end) (Where
  this and lean/THEOREM.md differ, the page holds.) -/
  s0 : ∀ a, st₂ (Fk X N P) D a → a.1.1.key.fits (shapeAt X).fold.index = true →
    T₂H X at_ off₂ H 0 a
  /-- 0 → 1: other files' (row 2.0: the same state; shape₂_01 is an equation): TYPED IN PARTS: to be
  struck by a call -/
  g0 : ∀ b, (Fk X N P).shared.blocksInOrder[0]? = some b →
    StepInvP b (T₂H X at_ off₂ H 0) (T₂H X at_ off₂ H 1)
  /-- 1 → 2: other files' (LIN point: PointLaid · shape₂_12 · free₂_12): TYPED, the fields beside
  shape inside free₂_12 -/
  g1 : ∀ b, (Fk X N P).shared.blocksInOrder[1]? = some b →
    StepInvP b (T₂H X at_ off₂ H 1) (T₂H X at_ off₂ H 2)
  /-- 2 → 3: other files': the sending of o_u with its mask (sure22) (Where
  this and lean/THEOREM.md differ, the page holds.) -/
  g2 : ∀ b, (Fk X N P).shared.blocksInOrder[2]? = some b →
    StepInvP b (T₂H X at_ off₂ H 2) (T₂H X at_ off₂ H 3)
  /-- 3 → 4: other files' (RecLaid · shape₂_34 · free₂_34): TYPED, as g1 -/
  g3 : ∀ b, (Fk X N P).shared.blocksInOrder[3]? = some b →
    StepInvP b (T₂H X at_ off₂ H 3) (T₂H X at_ off₂ H 4)
  /-- 4 → 5: other files' (LOC: LocLaid · shape₂_45 · free₂_45): TYPED, as g1 -/
  g4 : ∀ b, (Fk X N P).shared.blocksInOrder[4]? = some b →
    StepInvP b (T₂H X at_ off₂ H 4) (T₂H X at_ off₂ H 5)
  /-- 5 → 6: other files': the sending of Omega with the split (sure25) (Where
  this and lean/THEOREM.md differ, the page holds.) -/
  g5 : ∀ b, (Fk X N P).shared.blocksInOrder[5]? = some b →
    StepInvP b (T₂H X at_ off₂ H 5) (T₂H X at_ off₂ H 6)
  /-- 6 → 7: other files' (Joined · shape₂_67 · free₂_67): TYPED, as g1 -/
  g6 : ∀ b, (Fk X N P).shared.blocksInOrder[6]? = some b →
    StepInvP b (T₂H X at_ off₂ H 6) (T₂H X at_ off₂ H 7)
  /-- 7 → 8: other files' (LIN zeta: ZetaLaid · shape₂_78 · free₂_78): TYPED, as g1 -/
  g7 : ∀ b, (Fk X N P).shared.blocksInOrder[7]? = some b →
    StepInvP b (T₂H X at_ off₂ H 7) (T₂H X at_ off₂ H 8)
  /-- 8 → 9: other files' (SplitLaid · shape₂_89 · free₂_89): TYPED, as g1 -/
  g8 : ∀ b, (Fk X N P).shared.blocksInOrder[8]? = some b →
    StepInvP b (T₂H X at_ off₂ H 8) (T₂H X at_ off₂ H 9)
  /-- 9 → 10: other files': the proximity test of G_u (Where
  this and lean/THEOREM.md differ, the page holds.) -/
  g9 : ∀ b, (Fk X N P).shared.blocksInOrder[9]? = some b →
    StepInvP b (T₂H X at_ off₂ H 9) (T₂H X at_ off₂ H 10)
  /-- 10 → 11: other files': the proximity test of G_omega (Where
  this and lean/THEOREM.md differ, the page holds.) -/
  g10 : ∀ b, (Fk X N P).shared.blocksInOrder[10]? = some b →
    StepInvP b (T₂H X at_ off₂ H 10) (T₂H X at_ off₂ H 11)
  /-- 11 → 12: other files' (row 2.11: the same state; shape₂_1112 is an equation): TYPED IN PARTS:
  as g0 -/
  g11 : ∀ b, (Fk X N P).shared.blocksInOrder[11]? = some b →
    StepInvP b (T₂H X at_ off₂ H 11) (T₂H X at_ off₂ H 12)

/-- **All twelve, under the named steps.** -/
theorem aSide₂_of_hist (H : ℕ → P₂ × St₂ → Prop) (G : Gaps₂ X N P D at_ off₂ H) (k : ℕ)
    (a : P₂ × St₂) (hk : k ≤ 12) (hist : Hist₂ (Fk X N P) D k a)
    (hfit : a.1.1.key.fits (shapeAt X).fold.index = true) : T₂ X at_ off₂ k a := by
  refine (reached_held_invP _ (Fk X N P).shared.blocksInOrder (st₂ (Fk X N P) D)
    (fun k z => z.1.1.key.fits (shapeAt X).fold.index = true → T₂H X at_ off₂ H k z) 12
    (fun a ha => G.s0 a ha) (fun j hj b hb => ?_) k a hk hist hfit).1
  refine stepP_imp b (fun p : P₂ => p.1.key.fits (shapeAt X).fold.index = true) _ _ ?_
  match j, hj with
  | 0, _ => exact G.g0 b hb
  | 1, _ => exact G.g1 b hb
  | 2, _ => exact G.g2 b hb
  | 3, _ => exact G.g3 b hb
  | 4, _ => exact G.g4 b hb
  | 5, _ => exact G.g5 b hb
  | 6, _ => exact G.g6 b hb
  | 7, _ => exact G.g7 b hb
  | 8, _ => exact G.g8 b hb
  | 9, _ => exact G.g9 b hb
  | 10, _ => exact G.g10 b hb
  | 11, _ => exact G.g11 b hb
  | n + 12, h12 => exact absurd h12 (by omega)

end

end LPFD

#print axioms LPFD.aSide₂_of_hist
