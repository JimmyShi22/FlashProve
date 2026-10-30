-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/Fire/Code/KeyASide2All.lean: THE SHARED CHAIN's STATE's SIDE OF THE PROMISE FROM THE
  HISTORY, IN SCOPE, AT EVERY BORDER: ALL THIRTEEN LEGS PAID: NO PREMISE ON A STEP IS LEFT.
  step₂_2 | step₂_5 (Johnson/RunOne/KeyRow22AtSeat.lean: the two sendings) CALLED; WHAT THEY LEAVE
  IN FRONT IS PAID HERE: the two tests with code on the plan (plan22B | plan25B) BY LEAN's KERNEL AT
  THE WRITTEN KEY's SHAPE AND CODES.
  plan25_full | plan22_full       KERNEL FACTS: the two tests say yes at keyFull's shape and
    codes, at one answer to a sample · plan25_full_no | plan22_full_no: CHECKS THAT THEY CAN FAIL:
    at two answers both say no
  plan_at                         a sub-protocol that the description seats in the shared chain
    passes its own test on the plan, under planOk
  codes14_in_scope                K14's parameters' codes at the seat are the written key's
  two₂_made                       PROVED: KeyASide2Two.lean's Two₂ at off₂N, from the scope's five
    equations and planOk
  aSide₂_at_all                PROVED: k ≤ 12 · Hist₂ (Fk X N P) D k a · fits ⊢
    Tests₂ at the tables' letters (atSix · off₂N) at border k: FROM THE SEAT's FACTS ALONE. The
    sibling of aSide_at_all (KeyASideAll.lean: chain 1).
  guard_32_at_all              PROVED: row 3.2's guard at public numbers (KeyOmegaPublic.lean)
    WITH NO PREMISE ON A STEP: Hist₃ (Fk X N P) D 2 a · fits · Seat.enterOwn a.2 = .ok t ⊢ BookOrdW
    (stages + 2) 1 t.book ∧ t.book.trees.size = stages + 2 + 1 ∧ t.roots = 0
WHOSE LEGS: s0 · g0 · g11
  · g1 · g3 · g4 · g6 · g7 · g8: bridges over tests₂_kk' · g2 · g5: other files' · g9 · g10: Johnson/RunOne/Law/StepSide2.lean's. All but g2 · g5 come by KeyASide2Two.lean and the files below it.
OBJECT: Tests₂ at Hist₂ (Fk X N P) D k a · USER: on₂_of_tests (Johnson/RunOne/KeyOn2Tests.lean: chain 2's members) ·
  row 3.2's payers · LETTERS: none in front but the seat's.
THE STATE's SIDE ALONE: THE STRINGS' SIDE (Strings₂) IS NOT HERE. NO MEMBER IS SHOWN: EMPTY WHERE
  NOTHING IS REACHED. fits IS A TEST ON THE INSTANCE. Nothing on soundness.
-/
import Johnson.Top.Fire.Code.KeyASide2Two
import Johnson.RunOne.KeyRow22AtSeat

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
open VerifiableInference.Desc.K12 (T12)
open Lk6.AtPlan (keyFull)

/-- **The second sending's test on the plan, at the written key.** -/
theorem plan25_full : plan25B keyFull.once.shape 1 keyFull.codes = true := by decide +kernel

/-- A test that it can fail. -/
theorem plan25_full_no : plan25B keyFull.once.shape 2 keyFull.codes = false := by decide +kernel

/-- **The first sending's, at whatever withU says there.** -/
theorem plan22_full : ((_root_.Desc.K14.withU keyFull.once.shape).all fun s => plan22B
    keyFull.once.shape 1 keyFull.codes s) = true := by decide +kernel

/-- A test that it can fail; and withU says something there. -/
theorem plan22_full_no : ((_root_.Desc.K14.withU keyFull.once.shape).any fun s => !plan22B
    keyFull.once.shape 2 keyFull.codes s) = true := by decide +kernel

section
variable (X : Source) (N : H2U.PlaceNums) (P : LaterPlaces)

/-- A seated sub-protocol of the shared chain passes its own test on the plan. -/
theorem plan_at (hp : (Fk X N P).planOk = true) (k : ℕ) (b : Block St₂ Unit) (hb : (Fk X N
    P).shared.blocksInOrder[k]? = some (seat b)) : b.planOk = true := by
  have h := List.all_eq_true.1 (shared_blocksOk X N P hp) (seat b) (List.mem_of_getElem? hb)
  have h1 : (seat b : Block St₂ Key.Claim).planOk = true := (Bool.and_eq_true_iff.1 h).1
  have h2 : ((Block.retype b : Block St₂ Key.Claim).planOk && (Block.retype b : Block St₂
      Key.Claim).hasNoClaimsAndNothingAfter) = true := h1
  have h3 : (b.planOk && b.claims.isEmpty) = true := (Bool.and_eq_true_iff.1 h2).1
  exact (Bool.and_eq_true_iff.1 h3).1

variable (c₁ : Block (Fk X N P).S₁ (Fk X N P).Cl) (k₁ : List (Block (Fk X N P).S₁ (Fk X N P).Cl))
variable {Zp : VerifierAndGoals.PublicFiles} {X₀ : OnBytes.Model.Verify.Public} {cfg : ByteArray}
    {m : Johnson.G.OfPlan.Made}
variable (D : WholeD)

theorem codes14_in_scope (hZ : VerifierAndGoals.InScope Zp = true) (hP : ReadOf Zp.pol X₀) (hm : madeAt X₀
    Zp.lay cfg = .ok m) (hX : sourceOf m = .ok X)
    (hp : (Fk X N P).planOk = true) : (p14At X P).codes = keyFull.codes := by
  obtain ⟨e1, e2⟩ := pubsOf_k m X hX
  have hc : (oneAt X).codes = codesAt X :=
    codes_of_front X N P (by rw [e2, e1]) (front_of_planOk X N P hp) (fileOk_of_planOk' _ hp)
  exact (show (p14At X P).codes = codesAt X from rfl).trans (hc.symm.trans (five_in_scope hZ hP hm
      hX hp).2.2.2.2)

/-- **The two sendings' steps, in scope.** -/
theorem two₂_made (hZ : VerifierAndGoals.InScope Zp = true) (hP : ReadOf Zp.pol X₀) (hm : madeAt X₀ Zp.lay cfg
    = .ok m) (hX : sourceOf m = .ok X)
    (hp : (Fk X N P).planOk = true) : Two₂ X N P off₂N := by
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, h8⟩ := eight_said X N P hp
  have eS : (p14At X P).S = keyFull.once.shape := shape_full hZ hP hm hX hp
  have eC := codes14_in_scope X N P hZ hP hm hX hp
  have ea : (oneAt X).given.plan.samples = 1 := Johnson.RunOne.KeySendGood.samples_in_scope hZ hP hm
      hX hp
  have hM : (p14At X P).S.masksAhead = true := masks_of_form _ (form_of_fileOk X N P
      (fileOk_of_planOk' _ hp))
  have p2 : b2.planOk = true := plan_at X N P hp 2 b2 (shared_2 X N P b1 b2 b3 b4 b5 b6 b7 b8 h8)
  have p5 : b5.planOk = true := plan_at X N P hp 5 b5 (shared_5 X N P b1 b2 b3 b4 b5 b6 b7 b8 h8)
  refine ⟨fun b hb => ?_, fun b hb => ?_⟩
  · exact step₂_2 X N P b1 b2 b3 b4 b5 b6 b7 b8 h8 atSix (plan₁ (oneAt X)) (oneAt
      X).given.plan.samples (last₁At (oneAt X)) off₂N hM p2
      (fun sentU hU => by
        rw [eS] at hU ⊢
        rw [eC, ea]
        have h := plan22_full
        rw [hU] at h
        exact h) rfl b hb
  · exact step₂_5 X N P b1 b2 b3 b4 b5 b6 b7 b8 h8 atSix (plan₁ (oneAt X)) (oneAt
      X).given.plan.samples (last₁At (oneAt X)) off₂N p5
      (by rw [eS, eC, ea]; exact plan25_full) rfl rfl b hb

/-- **The shared chain's state's side at every border, from the history and the seat's facts
alone.** -/
theorem aSide₂_at_all (q₁ : (Fk X N P).first.blocksInOrder = c₁ :: k₁)
    (hZ : VerifierAndGoals.InScope Zp = true) (hP : ReadOf Zp.pol X₀) (hm : madeAt X₀ Zp.lay cfg = .ok m) (hX
        : sourceOf m = .ok X) (hL : laterPlaces m = .ok P)
    (hp : (Fk X N P).planOk = true) (hw : (Fk X N P).wantedOk = true) (hN : rangesNumbers m = .ok N)
    (k : ℕ) (a : P₂ × St₂) (hk : k ≤ 12) (hist : Hist₂ (Fk X N P) D k a)
    (hfit : a.1.1.key.fits (shapeAt X).fold.index = true) : T₂ X atSix off₂N k a :=
  aSide₂_two_left X N P c₁ k₁ D off₂N q₁ hZ hP hm hX hL hp hw hN (two₂_made X N P hZ hP hm hX hp) k
      a hk hist hfit

/-- **Row 3.2's guard at public numbers, from the history and the seat's facts alone.** -/
theorem guard_32_at_all (q₁ : (Fk X N P).first.blocksInOrder = c₁ :: k₁)
    (hZ : VerifierAndGoals.InScope Zp = true) (hP : ReadOf Zp.pol X₀) (hm : madeAt X₀ Zp.lay cfg = .ok m) (hX
        : sourceOf m = .ok X) (hL : laterPlaces m = .ok P)
    (hp : (Fk X N P).planOk = true) (hw : (Fk X N P).wantedOk = true) (hN : rangesNumbers m = .ok N)
    (a : (Xi × FirstState × St₂) × St₃) (h : Hist₃ (Fk X N P) D 2 a) (hfit : a.1.1.key.fits (shapeAt
        X).fold.index = true)
    (t : T12) (ht : VerifiableInference.Desc.K12.Seat.enterOwn a.2 = .ok t) :
    H2K.First.BookOrdW ((oneAt X).ranges.stages.length + 2) 1 t.book ∧ t.book.trees.size = (oneAt
        X).ranges.stages.length + 2 + 1 ∧ t.roots = 0 :=
  guard_32_two X N P c₁ k₁ D q₁ hZ hP hm hX hL hp hw hN (two₂_made X N P hZ hP hm hX hp) a h hfit t
      ht

end

end LPFD

#print axioms LPFD.plan25_full
#print axioms LPFD.plan25_full_no
#print axioms LPFD.plan22_full
#print axioms LPFD.plan22_full_no
#print axioms LPFD.plan_at
#print axioms LPFD.codes14_in_scope
#print axioms LPFD.two₂_made
#print axioms LPFD.aSide₂_at_all
#print axioms LPFD.guard_32_at_all
#print axioms Johnson.RunOne.KeyRows23.step₂_2
#print axioms Johnson.RunOne.KeyRows23.step₂_5
