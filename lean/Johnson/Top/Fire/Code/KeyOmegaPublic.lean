-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/Fire/Code/KeyOmegaPublic.lean: THE KEY FILE's LAST CHAIN, ROW 3.2 (the own proximity
  test): THE GUARD's LAST DEBT: guard_32_made (KeyASideAll.lean) ends «there are q and tO:
  the handed shared chain's book places its message oOmega at q, tO is its tree number q.1, and the
  book behind the door is in order BY THE ORDER at (the first chain's roots, tO.number)»: HERE:
  tO.number IS A PUBLIC NUMBER, AND WHICH: UNDER Four₂ (KeyASide2Start.lean).
  omega_of_tests   PROVED: general in the letters: from Tests₂ at border 12: its
    book-keeping's tenth clause (oOmega = 2) · its last clause (the book is in order: the tree at
    the place z bears z) · placed at the tables' message 4 (the plan's oracle 2 sits where at_ 4
    says, through off₂): tO.number = ω FOR THE ω WITH (at_ 4).1 = off₂ ω, where off₂ takes that
    value once
  guard_32_public PROVED: IN SCOPE, AT atSix AND off₂N, UNDER Four₂ AND fits: Hist₃ (Fk X N P) D 2
    a → ∀ t, Seat.enterOwn a.2 = .ok t → BookOrdW (stages + 2) 1 t.book ∧ t.book.trees.size = stages
    + 2 + 1 ∧ t.roots = 0: NO «THERE IS», NO NUMBER READ OFF A STATE: R₁ by
    roots_of_aSide19; ω = 1: Omega's tree is the shared chain's second (atSix 4 = (7, 0) = (off₂N 1,
    0))
OBJECT: the guard of the law at row 3.2 · USER: row 3.2's payers · LETTERS:
  none in front but the seat's.
WHAT «THE PUBLIC ω» IS IN K12's LAW (its takenOrderB π R₁ ω) WAS NOT HELD AT ITS TEXT: HERE ω IS
  THE NUMBER THAT THE SHARED CHAIN's OWN BOOK GIVES Omega's TREE (counted from 0 in that chain): 1.
  IF THE LAW's ω IS COUNTED OTHERWISE THE CALLER MUST SAY SO.
AN IMPLICATION: IT STANDS UNDER Four₂: FOUR STEPS OF THE SHARED CHAIN THAT ARE NOT PAID (g2 | g5:
  other files' · g9 | g10: other files'). (Where
  this and lean/THEOREM.md differ, the page holds.) EMPTY WHERE NOTHING IS REACHED. Nothing on soundness.

-/
import Johnson.Top.Fire.Code.KeyASide2Start
import Johnson.Top.Fire.Code.KeyAtOff

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

section
variable (at_ : Where) (S : OnBytes.Params.LinShape) (K₁ : KPlan) (a : ℕ) (last₁ : FirstState →
    Bool) (off₂ : ℕ → ℕ)

/-- **Which number Omega's tree bears in the shared chain's book at its end.** -/
theorem omega_of_tests (z : P₂ × St₂) (T : Tests₂ at_ S K₁ a last₁ off₂ 12 z) (ω : ℕ) (at4 : (at_
    4).1 = off₂ ω)
    (hinj : ∀ t, off₂ t = off₂ ω → t = ω) (q : ℕ × ℕ) (tO : OnBytes.Tree)
    (hq : z.2.book.place[z.2.loc.oOmega]? = some q) (ht : z.2.book.trees[q.1]? = some tO) :
        tO.number = ω := by
  have hs := T.shape
  simp only [LKFU.Shape23.ok, LKFU.Shape23.shape₂, List.all_cons, List.all_nil, Bool.and_true,
      Bool.and_eq_true] at hs
  obtain ⟨-, -, -, -, -, -, -, -, -, c10, -, -, -, -, -, -, -, c18⟩ := hs
  have n10 : z.2.loc.oOmega = 2 ∧ z.2.loc.oSp = 3 := by simpa using c10
  have hB : BookStep 0 z.2.book z.2.roots := (bookStep_iff 0 _ _).1 c18
  obtain ⟨o, t, ho, hpl, hat⟩ := T.placed 4 (by decide)
  have o2 : 2 = o := Option.some.inj ho
  subst o2
  rw [n10.1] at hq
  have e : q = t := Option.some.inj (hq.symm.trans hpl)
  have hn : tO.number = 0 + q.1 := hB.2 q.1 tO ht
  have h1 : off₂ q.1 = off₂ ω := by
    rw [e]
    exact (congrArg Prod.fst hat).symm.trans at4
  rw [hn, Nat.zero_add]
  exact hinj q.1 h1

end

section
variable (X : Source) (N : H2U.PlaceNums) (P : LaterPlaces)
    (c₁ : Block (Fk X N P).S₁ (Fk X N P).Cl) (k₁ : List (Block (Fk X N P).S₁ (Fk X N P).Cl))
variable {Zp : VerifierAndGoals.PublicFiles} {X₀ : OnBytes.Model.Verify.Public} {cfg : ByteArray}
    {m : Johnson.G.OfPlan.Made}
variable (D : WholeD)

/-- **Row 3.2's guard at public numbers, under the four.** -/
theorem guard_32_public (q₁ : (Fk X N P).first.blocksInOrder = c₁ :: k₁)
    (hZ : VerifierAndGoals.InScope Zp = true) (hP : ReadOf Zp.pol X₀) (hm : madeAt X₀ Zp.lay cfg = .ok m) (hX
        : sourceOf m = .ok X) (hp : (Fk X N P).planOk = true)
    (hw : (Fk X N P).wantedOk = true) (hN : rangesNumbers m = .ok N) (G : Four₂ X N P off₂N)
    (a : (Xi × FirstState × St₂) × St₃) (h : Hist₃ (Fk X N P) D 2 a) (hfit : a.1.1.key.fits (shapeAt
        X).fold.index = true)
    (t : T12) (ht : VerifiableInference.Desc.K12.Seat.enterOwn a.2 = .ok t) :
    H2K.First.BookOrdW ((oneAt X).ranges.stages.length + 2) 1 t.book ∧ t.book.trees.size = (oneAt
        X).ranges.stages.length + 2 + 1 ∧ t.roots = 0 := by
  obtain ⟨q, tO, h1, h2, h3, h4, h5⟩ := guard_32_made X N P c₁ k₁ D q₁ hZ hP hm hX hp hN a h t ht
  have H2 := hist₃_handed (Fk X N P) D 2 a h
  rw [(lengths_in_scope hZ hP hm hX hp hw).2.1] at H2
  have T := aSide₂_made X N P c₁ k₁ D off₂N q₁ hZ hP hm hX hp hw hN G 12 _ (Nat.le_refl 12) H2 hfit
  have hω : tO.number = 1 := omega_of_tests atSix _ _ _ _ off₂N _ T 1 rfl
    (fun t ht => by unfold off₂N at ht; omega) q tO h1 h2
  have H1 := hist₂_handed (Fk X N P) D 12 _ H2
  rw [(lengths_in_scope hZ hP hm hX hp hw).1] at H1
  have hr : a.1.2.1.d.roots = (oneAt X).ranges.stages.length + 2 :=
    roots_of_aSide19 (oneAt X) atSix _ (aSide_at_made X N P c₁ k₁ D q₁ hZ hP hm hX hp hN 19 _
        (Nat.le_refl 19) H1)
  rw [hω, hr] at h3
  rw [hr] at h4
  exact ⟨h3, h4, h5⟩

end

end LPFD

#print axioms LPFD.omega_of_tests
#print axioms LPFD.guard_32_public
#print axioms LPFD.guard_32_made
#print axioms LPFD.aSide₂_made
#print axioms LPFD.roots_of_aSide19
