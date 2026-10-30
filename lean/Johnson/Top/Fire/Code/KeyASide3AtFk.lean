-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/Fire/Code/KeyASide3AtFk.lean: THE KEY FILE's LAST CHAIN: THE VERIFIER's STATE's SIDE OF
THE INVARIANT FROM THE HISTORY: at every state that is reached at border k ≤ 4 of the last chain:
Tests₃ (Johnson/RunOne/KeyOn3Parts.lean) at the tables' own letters, those of On₃
(Johnson/RunOne/KeyRowsAtFk.lean). The sibling of KeyASideAtFk.lean (chain 1) and KeyASide2AtFk.lean
(the shared chain); the rule is reached_held_invP (ReachedInvPair.lean).
  T₃ X P at_ off₂ off₃ k z   Tests₃ at On₃'s letters
  T₃L …                      the fold's invariant: T₃, and the codes' lengths are in order at the
                             state's codes (the start's own test asks it; every step keeps the
                             codes; the own proximity test's step spends it)
  start₃_paid                PROVED: the start, from the shared chain's Tests₂ at its last border
  step₃_01 … step₃_34        PROVED: the four steps, each at the sub-protocol that second_flat
                             (KeyCut23.lean) names, from its acceptance alone
  aSide₃_of_hist             PROVED: k ≤ 4: NO STEP IS LEFT AS A NAMED PREMISE
PREMISES: hf: the test on the plan that ties the chains · ha1: one answer to a sample · hA | hoff:
on the letters at_ · off₂ · off₃ (public; no state) · hfit: a test on the instance: the key fits the
shape · h12: THE SHARED CHAIN's STATE's SIDE AT ITS LAST BORDER, at every state reached there:
another file's theorem: LAID IN BY A CALL in KeyASide3All.lean.
OBJECT: Tests₃ at Hist₃ (Fk X N P) D k a · USER: none yet; meant: on₃_of_parts (chain 3's members);
row 3.2's caller · LETTERS: X N P D · at_ · off₂ · off₃.
AN IMPLICATION: EMPTY WHERE NOTHING IS REACHED. THE ORACLE STRINGS' SIDE (Strings₃) IS NOT HERE.
Nothing on soundness.
-/
import Johnson.Top.Fire.Code.KeyASide2AtFk
import Johnson.RunOne.KeyTests3Steps
import Johnson.RunOne.KeyKeepsAt23
import Johnson.RunOne.KeyBridges23
import Johnson.RunOne.Law.K12Shape32
import Johnson.RunOne.Law.K12Order
import Johnson.RunOne.Law.K12FwdAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LPFD
open OnBytes OnBytes.Params OnBytes.Maker
open VerifiableInference.Desc VerifiableInference.Desc.Key VerifiableInference.Desc.Sound
open VerifiableInference.Desc.Plain
open VerifiableInference.Desc.Key (FirstState Claim Xi)
open VerifiableInference.Desc.K12 (T12 P12 proximityTestKind guardedProximityTestParts)
open H2K.JointK (Blk' Gs)
open Johnson.RunOne.KeyRows1 (plan₁)
open Johnson.RunOne.KeyRows23
open Johnson.RunOne.Law.K12Shape32 (own_yes shapeB₃_2_3)
open Johnson.RunOne.Law.K12Order (k12_inOrder)
open Johnson.RunOne.Law.K12FwdAt (asks_W stages_W p12At_nums)
open Johnson.RunOne.Law.RngAsked (asksPlan_ok)

section
variable (X : Source) (N : H2U.PlaceNums) (P : LaterPlaces) (D : WholeD) (at_ : Where)
  (off₂ off₃ : ℕ → ℕ)

/-- Tests₃ at the tables' own letters. -/
abbrev T₃ (k : ℕ) (z : P₃ × St₃) : Prop :=
  Tests₃ at_ (shapeAt X) (plan₁ (oneAt X)) (oneAt X).given.plan.samples [0] (srcOk (ownTest P))
    off₂ off₃ ((oneAt X).ranges.stages.length + 2) k z

/-- The fold's invariant at border k. -/
abbrev T₃L (k : ℕ) (z : P₃ × St₃) : Prop :=
  T₃ X P at_ off₂ off₃ k z ∧ z.2.st.codes.lengthsOk = true

/-- **The start.** -/
theorem start₃_paid (hoff : ∀ k ∈ [0, 2], off₃ (at_ k).1 = (at_ k).1)
    (h12 : ∀ a₂ : P₂ × St₂, Hist₂ (Fk X N P) D (Fk X N P).shared.blocksInOrder.length a₂ →
      a₂.1.1.key.fits (shapeAt X).fold.index = true → T₂ X at_ off₂ 12 a₂) :
    ∀ a, st₃ (Fk X N P) D a → a.1.1.key.fits (shapeAt X).fold.index = true →
      T₃L X P at_ off₂ off₃ 0 a := by
  intro a ha hfit
  obtain ⟨hH, hst⟩ := ha
  exact tests₃_start at_ (shapeAt X) (plan₁ (oneAt X)) (oneAt X).given.plan.samples [0]
    (last₁At (oneAt X)) (srcOk (ownTest P)) off₂ off₃ ((oneAt X).ranges.stages.length + 2)
    (codesAt X) (fun x s₁ s₂ => (Fk X N P).start₃ x s₁ s₂) (starts_fkD X N P)
    (last₁_gives (oneAt X)) hoff a.1.1 a.1.2.1 a.1.2.2 a.2
    (Johnson.RunOne.KeyRows23.ok_of_toOption hst) (h12 _ hH hfit)

/-- **0 → 1**: the shared rounds' kind's second part. -/
theorem step₃_01 (hA : AtOk at_ off₂ off₃ ((oneAt X).ranges.stages.length + 2))
    (b : Block St₃ Claim) (hb : (Fk X N P).second.blocksInOrder[0]? = some b) :
    StepInvP (P := P₃) b (T₃L X P at_ off₂ off₃ 0) (T₃L X P at_ off₂ off₃ 1) := by
  intro p s s' rs gs _ hy T
  obtain ⟨bd, yO, G, dot, L⟩ := laid_at_desc X N P b hb s _ gs s' hy
  refine ⟨tests₃_01 at_ (plan₁ (oneAt X)) (oneAt X).given.plan.samples [0] (srcOk (ownTest P))
    off₂ off₃ ((oneAt X).ranges.stages.length + 2) p s s' L hA T.1, ?_⟩
  show s'.st.codes.lengthsOk = true
  rw [L.codes]
  exact T.2

/-- **1 → 2**: the taken trees' sources. -/
theorem step₃_12 (b : Block St₃ Claim) (hb : (Fk X N P).second.blocksInOrder[1]? = some b) :
    StepInvP (P := P₃) b (T₃L X P at_ off₂ off₃ 1) (T₃L X P at_ off₂ off₃ 2) := by
  obtain ⟨f, hfl, -⟩ := second_flat X N P
  rw [show (Fk X N P).second.blocksInOrder = _ from hfl] at hb
  obtain rfl := Option.some.inj hb
  intro p s s' rs gs _ hy T
  have hy' : (VerifiableInference.Desc.Third.takenSources (ownTest P) : Block St₃ Unit).decide s
      (rs.map noDigest) gs = .ok s' := hy
  obtain rfl := sources_same (ownTest P) s _ gs s' hy'
  exact ⟨tests₃_12 at_ _ _ _ _ _ off₂ off₃ _ (p, s') (sources_yes (ownTest P) s' _ gs s' hy') T.1,
    T.2⟩

/-- **2 → 3**: the own proximity test. -/
theorem step₃_23 (hf : (descriptionFromSource X N P).fileOk = true) (ha1 : (oneAt X).given.plan.samples = 1)
    (b : Block St₃ Claim) (hb : (Fk X N P).second.blocksInOrder[2]? = some b) :
    StepInvP (P := P₃) b (T₃L X P at_ off₂ off₃ 2) (T₃L X P at_ off₂ off₃ 3) := by
  obtain ⟨f, hfl, -⟩ := second_flat X N P
  rw [show (Fk X N P).second.blocksInOrder = _ from hfl] at hb
  obtain rfl := Option.some.inj hb
  intro p s s' rs gs _ hy T
  have hy' : (K12.Seat.onOwn (proximityTestKind guardedProximityTestParts (H2U.proximityTestParametersAt ⟨3, none, 2, .K12⟩ P.W) : Blk')).decide s
      (rs.map noDigest) gs = .ok s' := hy
  obtain ⟨he, ha, _, _⟩ := asksPlan_ok (asks_W X N P hf)
  have en := p12At_nums _ _ he
  have hsh := shapeB₃_2_3 (shapeAt X) (plan₁ (oneAt X)) (oneAt X).given.plan.samples [0]
    (srcOk (ownTest P)) ((oneAt X).ranges.stages.length + 2) _ he ha s s' _ gs hy'
    (by rw [en]; exact stages_W X N P hf) ha1 T.1.shape
  obtain ⟨tE, hk, rfl⟩ := own_yes _ s s' _ gs hy'
  have K1 := H2K.Out.k12_out _ he ha _ tE _ gs hk
  refine ⟨tests₃_23 at_ _ _ _ _ _ off₂ off₃ _ (p, s) tE hsh K1.book
    (k12_inOrder _ _ tE _ gs hk T.2) T.1, ?_⟩
  show tE.st.codes.lengthsOk = true
  rw [K1.codes]
  exact T.2

/-- **3 → 4**: the chain's end. -/
theorem step₃_34 (b : Block St₃ Claim) (hb : (Fk X N P).second.blocksInOrder[3]? = some b) :
    StepInvP (P := P₃) b (T₃L X P at_ off₂ off₃ 3) (T₃L X P at_ off₂ off₃ 4) := by
  obtain ⟨f, hfl, -⟩ := second_flat X N P
  rw [show (Fk X N P).second.blocksInOrder = _ from hfl] at hb
  obtain rfl := Option.some.inj hb
  intro p s s' rs gs _ hy T
  have hy' : (end₃At X P).decide s (rs.map noDigest) gs = .ok s' := hy
  have hfin := end₃_yes _ s _ gs s' hy'
  obtain rfl := chainEnd_same (Cl := Unit) 3 3 false _ (fun d : St₃ => ChainEnd.untestedL d.st) s
    _ gs s' hy'
  exact ⟨tests₃_34 at_ _ _ _ _ _ off₂ off₃ _ (p, s') hfin T.1, T.2⟩

/-- **All four borders behind the start, with no step left.** -/
theorem aSide₃_of_hist (hf : (descriptionFromSource X N P).fileOk = true)
    (ha1 : (oneAt X).given.plan.samples = 1)
    (hA : AtOk at_ off₂ off₃ ((oneAt X).ranges.stages.length + 2))
    (hoff : ∀ k ∈ [0, 2], off₃ (at_ k).1 = (at_ k).1)
    (h12 : ∀ a₂ : P₂ × St₂, Hist₂ (Fk X N P) D (Fk X N P).shared.blocksInOrder.length a₂ →
      a₂.1.1.key.fits (shapeAt X).fold.index = true → T₂ X at_ off₂ 12 a₂)
    (k : ℕ) (a : P₃ × St₃) (hk : k ≤ 4) (hist : Hist₃ (Fk X N P) D k a)
    (hfit : a.1.1.key.fits (shapeAt X).fold.index = true) :
    T₃ X P at_ off₂ off₃ k a ∧ a.2.st.codes.lengthsOk = true := by
  refine reached_held_invP _ (Fk X N P).second.blocksInOrder (st₃ (Fk X N P) D)
    (fun k z => z.1.1.key.fits (shapeAt X).fold.index = true → T₃L X P at_ off₂ off₃ k z) 4
    (start₃_paid X N P D at_ off₂ off₃ hoff h12) (fun j hj b hb => ?_) k a hk hist hfit
  refine stepP_imp b (fun p : P₃ => p.1.key.fits (shapeAt X).fold.index = true) _ _ ?_
  match j, hj with
  | 0, _ => exact step₃_01 X N P at_ off₂ off₃ hA b hb
  | 1, _ => exact step₃_12 X N P at_ off₂ off₃ b hb
  | 2, _ => exact step₃_23 X N P at_ off₂ off₃ hf ha1 b hb
  | 3, _ => exact step₃_34 X N P at_ off₂ off₃ b hb
  | n + 4, h4 => exact absurd h4 (by omega)

end

end LPFD

#print axioms LPFD.start₃_paid
#print axioms LPFD.step₃_01
#print axioms LPFD.step₃_12
#print axioms LPFD.step₃_23
#print axioms LPFD.step₃_34
#print axioms LPFD.aSide₃_of_hist
