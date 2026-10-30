-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/Fire/Code/KeyASide2Start.lean: THE SHARED CHAIN's FOLD (KeyASide2AtFk.lean |
  KeyASide2Paid.lean): THE START's LEG (s0) STRUCK BY CALLS, IN SCOPE, AT THE TABLES' atSix: at
  every state at which the shared chain starts Tests₂ holds at border 0.
  tests₂_start   PROVED: at ((x, s), start₂ x): from ASide … 19 s · «the row (Eval) is
    there» · «the mask lies beside W» · three public facts (the shape's form · the one-time plan's
    shape and codes are the sized key's) · fits: field by field as seam₁On
    (RunOne/KeySeam1.lean) has them, WITHOUT THE STRINGS: last: t1_of_aSide | n₁_two · placed₁ |
    order₁: ASide's · codes: codes_of_last · shape: shape₂_first · order: Means.InOrder.start
  s0_made      PROVED: Left₂'s s0 AT atSix: from InScope · the five equations of the seat · planOk
    · wantedOk: by aSide_at_made | e18_at_made (KeyASideAll.lean) at chain 1's end
  Four₂        A NAMED PREMISE: THE FOUR STEPS THAT ARE LEFT, EACH WITH A WORD ON WHERE IT STANDS:
    g2 | g5 (the two sendings: step₂_2 | step₂_5) · g9 | g10
    (the two proximity tests: other files') (Where
    this and lean/THEOREM.md differ, the page holds.)
  aSide₂_made  PROVED: k ≤ 12: THE FOLD IN SCOPE, UNDER Four₂ AND fits: NINE OF THIRTEEN LEGS
    PAID: s0 (here) · g0 | g11 (KeyASide2Paid.lean) · g1 · g3 · g4 · g6 · g7 · g8:
    gap₂_k (Gaps2InScope.lean) over tests₂_kk' (Johnson/RunOne/KeyTestsStep.lean)
OBJECT · USER: as KeyASide2AtFk.lean · LETTERS: off₂; in front: none but the seat's.
AN IMPLICATION: FOUR OF THIRTEEN LEGS ARE A PREMISE (Four₂). UP TO BORDER 2 NOTHING IS LEFT
  (aSide₂_two). EMPTY WHERE NOTHING IS REACHED. Nothing on soundness.
-/
import Johnson.Top.Fire.Code.KeyASide2Paid
import Johnson.Top.Fire.Code.KeyASideAll
import Johnson.Top.Fire.Code.KeyRoundsAtSeat
import Johnson.Top.Fire.Code.Gaps2InScope

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 40000

noncomputable section

open scoped ENNReal

namespace LPFD
open VerifiableInference VerifiableInference.OnPublicFiles
open Rom ZKCP Hiop Prob Cb Cb.Ood OnBytes.Flat OnBytes.Slice OnBytes.Maker OnBytes.RunA
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms
open TypedOracleCompiler.Joined
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run _root_.Run.PQ OnBytes
open VerifiableInference.Desc VerifiableInference.Desc.Sound VerifiableInference.Desc.Plain
open VerifiableInference.Desc.Key
open VerifiableInference.Desc.Key (Xi)
open VerifiableInference.Desc.Key (FirstState)
open Johnson.RunOne.KeyRows23 (BaseSt AtFk Fk fr₁ fr₂ fr₃ On₁ Cl₁ On₂ Cl₂ On₃ Cl₃ oneAt St₂ St₃
    seam₁_at_fk seam₂_at_fk ends_at_fk)
open Johnson.RunOne.KeyRows1 (FirstLetters firstOn_of firstClaim_of CollCell ReadsL open₁)
open Johnson.RunOne.KeyRows23 (CellOnly inFront₂ front₂ seat open₃)

open OnBytes.Params (OneTime Setting)
open Johnson.RunOne.KeyRows1
open Johnson.RunOne.KeyRows23 (CellOnly)

open Johnson.RunOne.Law.AtFreeCfg (ReadOf)
open Johnson.RunOne.Law.KeyInScope (five_in_scope)
open Johnson.RunOne.KeyRows23 (atSix)

open Johnson.RunOne.Law.StepSideGaps (gaps_of)
open Johnson.RunOne.Law.StepSideAtFk (H₀ H₁)

open Johnson.RunOne.KeyRows23

section
variable (X : Source) (N : H2U.PlaceNums) (P : LaterPlaces) (at_ : Where) (off₂ : ℕ → ℕ)

/-- **At the shared chain's start**, without the strings. -/
theorem tests₂_start (hform : LKFU.Shape23.formOk (shapeAt X) = true) (hlin : (oneAt X).lin =
    shapeAt X) (hcodes : (oneAt X).codes = codesAt X)
    (x₀ x₁ : Lookup) (hl : lookupsOf (oneAt X) = [x₀, x₁]) (x : Xi) (s : FirstState) (A : ASide
        (oneAt X) at_ 19 s)
    (he : EvalIs (oneAt X).lin s) (hmk : ∀ o, (plan₁ (oneAt X)).orc 2 = some o → MaskWith (fun i =>
        s.d.book.place[i]?) o (o + 1))
    (hfit : x.key.fits (shapeAt X).fold.index = true) : T₂ X at_ off₂ 0 ((x, s), (Fk X N P).start₂
        x) :=
  have h19 : shape₁ (plan₁ (oneAt X)) (readers₁ (oneAt X)) (book₁ (oneAt X)) (n₁ (oneAt X)) (slots₁
      (oneAt X)) 19 s = true :=
    t1_of_aSide X at_ x₀ x₁ hl 19 s A
  { shape := shape₂_first (shapeAt X) _ (codesAt X) x.key hform
    last := by
      have h := h19
      unfold last₁At
      rw [n₁_two (oneAt X) x₀ x₁ hl] at h ⊢
      exact h
    eval := hlin ▸ he
    placed₁ := by
      have e : pinned (open₁ 2 19) = [0, 2] := by decide
      rw [← e]
      exact A.2.1
    order₁ := A.2.2.1
    key := rfl
    codes := by
      show codesAt X = s.d.st.codes
      rw [codes_of_last (oneAt X) 19 s h19, hcodes]
    lay := fun h => absurd h (by decide)
    placed := by
      have e : (pinned (open₂ 0)).filter (3 ≤ ·) = [] := by decide
      rw [e]
      intro k hk
      cases hk
    order := Means.InOrder.start (codesAt X)
    linOk := fun h => absurd h (by decide)
    seatU := fun h => absurd h (by decide)
    seatOmega := fun h => absurd h (by decide)
    fits := hfit
    mask₁ := hmk
    maskU := fun h => absurd h (by decide) }

end

section
variable (X : Source) (N : H2U.PlaceNums) (P : LaterPlaces)
    (c₁ : Block (Fk X N P).S₁ (Fk X N P).Cl) (k₁ : List (Block (Fk X N P).S₁ (Fk X N P).Cl))
variable {Zp : VerifierAndGoals.PublicFiles} {X₀ : OnBytes.Model.Verify.Public} {cfg : ByteArray}
    {m : Johnson.G.OfPlan.Made}
variable (D : WholeD) (off₂ : ℕ → ℕ)

/-- **The start's leg, in scope.** -/
theorem s0_made (q₁ : (Fk X N P).first.blocksInOrder = c₁ :: k₁)
    (hZ : VerifierAndGoals.InScope Zp = true) (hP : ReadOf Zp.pol X₀) (hm : madeAt X₀ Zp.lay cfg = .ok m) (hX
        : sourceOf m = .ok X) (hp : (Fk X N P).planOk = true)
    (hw : (Fk X N P).wantedOk = true) (hN : rangesNumbers m = .ok N) (a : P₂ × St₂) (ha : st₂ (Fk X
        N P) D a)
    (hfit : a.1.1.key.fits (shapeAt X).fold.index = true) : T₂ X atSix off₂ 0 a := by
  obtain ⟨h19, e⟩ : Hist₁ (Fk X N P) D (Fk X N P).first.blocksInOrder.length a.1 ∧ a.2 = (Fk X N P).start₂
      a.1.1 := ha
  rw [(lengths_in_scope hZ hP hm hX hp hw).1] at h19
  obtain ⟨x₀, x₁, hl⟩ := hl_in_scope hZ hP hm hX hp
  have A := aSide_at_made X N P c₁ k₁ D q₁ hZ hP hm hX hp hN 19 a.1 (Nat.le_refl 19) h19
  have E := (e18_at_made X N P c₁ k₁ D q₁ hZ hP hm hX hp hN).2 a.1 h19
  have hfo := fileOk_of_planOk' _ hp
  obtain ⟨e1, e2⟩ := pubsOf_k m X hX
  have t := tests₂_start X N P atSix off₂ (form_of_fileOk X N P hfo) (lin_of_fileOk X N P hfo)
    (codes_of_front X N P (by rw [e2, e1]) (front_of_planOk X N P hp) hfo) x₀ x₁ hl a.1.1 a.1.2 A
        E.1 E.2.2 hfit
  rw [← e] at t
  exact t

/-- **The four steps that are left** (where each stands: the file's head). -/
structure Four₂ : Prop where
  /-- 2 → 3: the sending of o_u with its mask -/
  g2 : ∀ b, (Fk X N P).shared.blocksInOrder[2]? = some b → StepInvP b (T₂ X atSix off₂ 2) (T₂ X atSix off₂ 3)
  /-- 5 → 6: the sending of Omega with the split -/
  g5 : ∀ b, (Fk X N P).shared.blocksInOrder[5]? = some b → StepInvP b (T₂ X atSix off₂ 5) (T₂ X atSix off₂ 6)
  /-- 9 → 10: the proximity test of G_u -/
  g9 : ∀ b, (Fk X N P).shared.blocksInOrder[9]? = some b → StepInvP b (T₂ X atSix off₂ 9) (T₂ X atSix off₂
               10)
  /-- 10 → 11: the proximity test of G_omega -/
  g10 : ∀ b, (Fk X N P).shared.blocksInOrder[10]? = some b → StepInvP b (T₂ X atSix off₂ 10) (T₂ X atSix off₂
               11)

/-- **The fold in scope, under the four.** -/
theorem aSide₂_made (q₁ : (Fk X N P).first.blocksInOrder = c₁ :: k₁)
    (hZ : VerifierAndGoals.InScope Zp = true) (hP : ReadOf Zp.pol X₀) (hm : madeAt X₀ Zp.lay cfg = .ok m) (hX
        : sourceOf m = .ok X) (hp : (Fk X N P).planOk = true)
    (hw : (Fk X N P).wantedOk = true) (hN : rangesNumbers m = .ok N)
    (G : Four₂ X N P off₂)
    (k : ℕ) (a : P₂ × St₂) (hk : k ≤ 12) (hist : Hist₂ (Fk X N P) D k a)
    (hfit : a.1.1.key.fits (shapeAt X).fold.index = true) : T₂ X atSix off₂ k a :=
  aSide₂_of_left X N P D atSix off₂ (lengths_in_scope hZ hP hm hX hp hw).2.1
    { s0 := fun a ha hf => s0_made X N P c₁ k₁ D off₂ q₁ hZ hP hm hX hp hw hN a ha hf
      g1 := gap₂_1 atSix off₂ hZ hP hm hX hp, g2 := G.g2, g3 := gap₂_3 atSix off₂ hp
      g4 := gap₂_4 atSix off₂ hp, g5 := G.g5, g6 := gap₂_6 atSix off₂ hZ hP hm hX hp
      g7 := gap₂_7 atSix off₂ hp, g8 := gap₂_8 atSix off₂ hZ hP hm hX hp, g9 := G.g9
      g10 := G.g10 } k a hk hist hfit

/-- **Borders 0 … 2: nothing is left**: from the history, the seat's facts and fits alone. -/
theorem aSide₂_two (q₁ : (Fk X N P).first.blocksInOrder = c₁ :: k₁)
    (hZ : VerifierAndGoals.InScope Zp = true) (hP : ReadOf Zp.pol X₀) (hm : madeAt X₀ Zp.lay cfg = .ok m) (hX
        : sourceOf m = .ok X) (hp : (Fk X N P).planOk = true)
    (hw : (Fk X N P).wantedOk = true) (hN : rangesNumbers m = .ok N)
    (k : ℕ) (a : P₂ × St₂) (hk : k ≤ 2) (hist : Hist₂ (Fk X N P) D k a)
    (hfit : a.1.1.key.fits (shapeAt X).fold.index = true) : T₂ X atSix off₂ k a := by
  refine reached_held_invP _ (Fk X N P).shared.blocksInOrder (st₂ (Fk X N P) D)
    (fun k z => z.1.1.key.fits (shapeAt X).fold.index = true → T₂ X atSix off₂ k z) 2
    (fun a ha hf => s0_made X N P c₁ k₁ D off₂ q₁ hZ hP hm hX hp hw hN a ha hf) (fun j hj b hb =>
        ?_) k a hk hist hfit
  refine stepP_imp b (fun p : P₂ => p.1.key.fits (shapeAt X).fold.index = true) _ _ ?_
  match j, hj with
  | 0, _ => exact g0_paid X N P atSix off₂ b hb
  | 1, _ => exact gap₂_1 atSix off₂ hZ hP hm hX hp b hb
  | n + 2, h2 => exact absurd h2 (by omega)

end

end LPFD

#print axioms LPFD.tests₂_start
#print axioms LPFD.s0_made
#print axioms LPFD.aSide₂_made
#print axioms LPFD.aSide₂_two
#print axioms LPFD.aSide_at_made
#print axioms LPFD.e18_at_made
#print axioms LPFD.gap₂_1
#print axioms LPFD.gap₂_3
#print axioms LPFD.gap₂_4
#print axioms LPFD.gap₂_6
#print axioms LPFD.gap₂_7
#print axioms LPFD.gap₂_8
