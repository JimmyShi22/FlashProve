-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/Fire/Code/KeyGuard32Free.lean: THE KEY FILE, ROW 3.2: guard_32_at_all (Top/Fire/Code/KeyASide2All.lean) WITH ITS LAST PREMISE ON THE INSTANCE, hfit, PAID OFF THE PROMISE IN FRONT: THE CALL THAT SHOWS THAT fits_of_freeAt₃ (KeyAt32Letters.lean) HAS hfit's VERY FORM.
OBJECT: BookOrdW ‹public numbers› behind row 3.2's door · USER: pays_32's caller at the name · LETTERS: B · coll · y.
  guard_32_free   PROVED: the seat's facts · Hist₃ (Fk X N P) D 2 a · FreeAt B.h₃ coll a y (Free₃'s first field) where B.recOf = recBack ⟹ ∀ t, Seat.enterOwn a.2 = .ok t → BookOrdW (stages + 2) 1 t.book ∧ t.book.trees.size = stages + 2 + 1 ∧ t.roots = 0: NO PREMISE ON THE INSTANCE OR ON A VERIFIER's STATE BESIDE THE WOVEN PROMISE's OWN TWO HALVES.
AN IMPLICATION: EMPTY WHERE NOTHING IS REACHED. Nothing on soundness.
-/
import Johnson.Top.Fire.Code.KeyASide2All
import Johnson.Top.Fire.Code.KeyAt32Letters

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

section
variable (X : Source) (N : H2U.PlaceNums) (P : LaterPlaces)
variable (c₁ : Block (Fk X N P).S₁ (Fk X N P).Cl) (k₁ : List (Block (Fk X N P).S₁ (Fk X N P).Cl))
variable {Zp : VerifierAndGoals.PublicFiles} {X₀ : OnBytes.Model.Verify.Public} {cfg : ByteArray} {m : Johnson.G.OfPlan.Made}
variable (D : WholeD)

theorem guard_32_free {Cells M Smp : Type} (B : BaseSt Cells M Smp RecFull) (hB : B.recOf = recBack) (coll : Strs → RecFull → Prop)
    (q₁ : (Fk X N P).first.blocksInOrder = c₁ :: k₁)
    (hZ : VerifierAndGoals.InScope Zp = true) (hP : ReadOf Zp.pol X₀) (hm : madeAt X₀ Zp.lay cfg = .ok m) (hX : sourceOf m = .ok X) (hL : laterPlaces m = .ok P)
    (hp : (Fk X N P).planOk = true) (hw : (Fk X N P).wantedOk = true) (hN : rangesNumbers m = .ok N)
    (a : (Xi × FirstState × St₂) × St₃) (y : Strs) (h : Hist₃ (Fk X N P) D 2 a) (hfree : FreeAt B.h₃ coll a y)
    (t : T12) (ht : VerifiableInference.Desc.K12.Seat.enterOwn a.2 = .ok t) :
    H2K.First.BookOrdW ((oneAt X).ranges.stages.length + 2) 1 t.book ∧ t.book.trees.size = (oneAt X).ranges.stages.length + 2 + 1 ∧ t.roots = 0 :=
  guard_32_at_all X N P c₁ k₁ D q₁ hZ hP hm hX hL hp hw hN a h (fits_of_freeAt₃ B hZ hP hm hX hp hB coll a y hfree) t ht

end

end LPFD

#print axioms LPFD.guard_32_free
