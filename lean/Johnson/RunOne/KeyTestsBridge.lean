-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/RunOne/KeyTestsBridge.lean: THE KEY FILE, THE SHARED CHAIN: SIX BRIDGES: FROM THE ACCEPTING DECISION OF THE DESCRIPTION's OWN BLOCK NUMBER k (k = 1 · 3 · 4 · 6 · 7 · 8) TO «THE FACTS ON THE VERIFIER's STATE ALONE GO ON FROM BORDER k TO k + 1», IN THE PAIR FORM THAT THE FOLD OVER THE HISTORY ASKS (StepInvP, Johnson/Top/Fire/Code/ReachedInvPair.lean).
OBJECT. ∀ b, (descriptionFromSource X N P).shared.blocksInOrder[k]? = some b → StepInvP b (TestsAt at_ off₂ X k) (TestsAt at_ off₂ X (k + 1)); TestsAt at_ off₂ X k z := Tests₂ (Johnson/RunOne/KeyOn2Parts.lean) at the tables' own letters at the description: shapeAt X · plan₁ (oneAt X) · the plan's samples · last₁At (oneAt X).
HOW. CALLS ALONE, three a bridge: which of the kind's eight blocks stands at that place · that block's accepting decision gives the step's relation on the two states · the relation carries Tests₂ (tests₂_kk', Johnson/RunOne/KeyTestsStep.lean). At 1 · 4 · 7: shared_k with point_ | loc_ | zeta_at_blocks, which spend that the rounds fit the declared rounds; at 3 · 6 · 8: recLaid_ | joined_ | splitLaid_at_desc.
IN FRONT. The kind's eight blocks by name (h); at 1 · 6 · 8: the shape splits (hS). Both are public, on the plan. NOTHING OF THE STATE IN FRONT BUT Tests₂ IS ASKED.
That (p14At X P).par.S, (p14At X P).S and shapeAt X are one term is Lean's own check here.
Limits. Nothing on the strings' side. The steps 2 and 5 (the two sendings) and 0 · 9 · 10 · 11 are not here. No member is shown. Nothing on soundness.

-/
import Johnson.RunOne.KeyTestsStep
import Johnson.RunOne.KeyBridges23
import Johnson.RunOne.KeyRowsAtFk
import Johnson.Top.Fire.Code.ReachedInvPair

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.RunOne.KeyRows23
open OnBytes OnBytes.Params
open VerifiableInference.Desc VerifiableInference.Desc.Key
open VerifiableInference.Desc.Key (FirstState)
open Desc.Plain (Par)
open VerifiableInference.Desc.Plain (held_decide)
open VerifiableInference.Desc.Sound (held)
open Johnson.RunOne.KeyRows1 (plan₁)

/-- The facts on the verifier's state alone, at border k, at the tables' own letters at the description. -/
abbrev TestsAt (at_ : Where) (off₂ : Nat → Nat) (X : Source) (k : Nat) (z : P₂ × St₂) : Prop :=
  Tests₂ at_ (shapeAt X) (plan₁ (oneAt X)) (oneAt X).given.plan.samples (last₁At (oneAt X)) off₂ k z

section
variable (at_ : Where) (off₂ : Nat → Nat) (X : Source) (N : H2U.PlaceNums) (P : LaterPlaces)
  (b1 b2 b3 b4 b5 b6 b7 b8 : Block _root_.Desc.K14.St Unit)
  (h : _root_.Desc.K14.blocks (p14At X P) = some [b1, b2, b3, b4, b5, b6, b7, b8])
include h

theorem bridge₂_1 (hS : (p14At X P).S.sharedSplitNeeded = true) :
    ∀ b, (descriptionFromSource X N P).shared.blocksInOrder[1]? = some b → LPFD.StepInvP b (TestsAt at_ off₂ X 1) (TestsAt at_ off₂ X 2) := by
  intro b hb z d d' rs gs hf hd T
  have e : b = seat b1 := Option.some.inj (hb.symm.trans (shared_1 X N P b1 b2 b3 b4 b5 b6 b7 b8 h))
  subst e
  obtain ⟨r, L, hl⟩ := point_at_blocks _ b1 b2 b3 b4 b5 b6 b7 b8 h hS d rs gs d' hf hd
  exact tests₂_12 at_ (p14At X P).par (plan₁ (oneAt X)) (oneAt X).given.plan.samples (last₁At (oneAt X)) off₂ z d d' L hl T

theorem bridge₂_3 :
    ∀ b, (descriptionFromSource X N P).shared.blocksInOrder[3]? = some b → LPFD.StepInvP b (TestsAt at_ off₂ X 3) (TestsAt at_ off₂ X 4) := by
  intro b hb z d d' rs gs hf hd T
  obtain ⟨GU, rows, L⟩ := recLaid_at_desc X N P b1 b2 b3 b4 b5 b6 b7 b8 h b hb d _ gs d' hd
  exact tests₂_34 at_ (p14At X P).par (plan₁ (oneAt X)) (oneAt X).given.plan.samples (last₁At (oneAt X)) off₂ z d d' L T

theorem bridge₂_4 :
    ∀ b, (descriptionFromSource X N P).shared.blocksInOrder[4]? = some b → LPFD.StepInvP b (TestsAt at_ off₂ X 4) (TestsAt at_ off₂ X 5) := by
  intro b hb z d d' rs gs hf hd T
  have e : b = seat b4 := Option.some.inj (hb.symm.trans (shared_4 X N P b1 b2 b3 b4 b5 b6 b7 b8 h))
  subst e
  obtain ⟨r, GU, rows, L, hl⟩ := loc_at_blocks _ b1 b2 b3 b4 b5 b6 b7 b8 h d rs gs d' hf hd
  exact tests₂_45 at_ (p14At X P).par (plan₁ (oneAt X)) (oneAt X).given.plan.samples (last₁At (oneAt X)) off₂ z d d' L hl T

theorem bridge₂_6 (hS : (p14At X P).S.sharedSplitNeeded = true) :
    ∀ b, (descriptionFromSource X N P).shared.blocksInOrder[6]? = some b → LPFD.StepInvP b (TestsAt at_ off₂ X 6) (TestsAt at_ off₂ X 7) := by
  intro b hb z d d' rs gs hf hd T
  obtain ⟨GU, GO, J⟩ := joined_at_desc X N P b1 b2 b3 b4 b5 b6 b7 b8 h hS b hb d _ gs d' hd
  exact tests₂_67 at_ (p14At X P).S (plan₁ (oneAt X)) (oneAt X).given.plan.samples (last₁At (oneAt X)) off₂ z d d' J T

theorem bridge₂_7 :
    ∀ b, (descriptionFromSource X N P).shared.blocksInOrder[7]? = some b → LPFD.StepInvP b (TestsAt at_ off₂ X 7) (TestsAt at_ off₂ X 8) := by
  intro b hb z d d' rs gs hf hd T
  have e : b = seat b7 := Option.some.inj (hb.symm.trans (shared_7 X N P b1 b2 b3 b4 b5 b6 b7 b8 h))
  subst e
  obtain ⟨r, L, hl⟩ := zeta_at_blocks _ b1 b2 b3 b4 b5 b6 b7 b8 h d rs gs d' hf hd
  exact tests₂_78 at_ (p14At X P).S (plan₁ (oneAt X)) (oneAt X).given.plan.samples (last₁At (oneAt X)) off₂ z d d' L hl T

theorem bridge₂_8 (hS : (p14At X P).S.sharedSplitNeeded = true) :
    ∀ b, (descriptionFromSource X N P).shared.blocksInOrder[8]? = some b → LPFD.StepInvP b (TestsAt at_ off₂ X 8) (TestsAt at_ off₂ X 9) := by
  intro b hb z d d' rs gs hf hd T
  obtain ⟨GU, GO, x, l, n, row, mu, L⟩ := splitLaid_at_desc X N P b1 b2 b3 b4 b5 b6 b7 b8 h hS b hb d _ gs d' hd
  exact tests₂_89 at_ (p14At X P).S (plan₁ (oneAt X)) (oneAt X).given.plan.samples (last₁At (oneAt X)) off₂ z d d' L T

end

end Johnson.RunOne.KeyRows23

#print axioms Johnson.RunOne.KeyRows23.bridge₂_1
#print axioms Johnson.RunOne.KeyRows23.bridge₂_3
#print axioms Johnson.RunOne.KeyRows23.bridge₂_4
#print axioms Johnson.RunOne.KeyRows23.bridge₂_6
#print axioms Johnson.RunOne.KeyRows23.bridge₂_7
#print axioms Johnson.RunOne.KeyRows23.bridge₂_8
