-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Top/Fire/Code/KeyNoCollAtWords.lean: at the full size: AT A STORED TABLE OF CODE WORDS THE EVENT «the out-of-domain (OOD) sample does not single one table out» IS FALSE AT EVERY SEED, AT THE FULL SIZE's DECODER AND IN OUR TABLES' WRITTEN LETTER.
Main names.
  `dist_DN`: the full size's code has distance 2 ^ 32 - (44040191 + 402653184) + 1: `hasDist_genOf` (OnBytes/Slice/CodeFacts.lean), called · `eM_lt`: the radius is below it [by evaluation of two numerals].
  `notColl_words`: ¬ DN.coll y ρ wherever DN.tab y is a table of code words: `not_coll_words` (OnBytes/K/Oracle/Decodes.lean), called at DN.
  `notCollN_words`: the same of `collN` (KeyAtName.lean) at a boundary's strings · `dcdN_words`: and there the written decoder returns that table's message at its own OOD sample (`dcd_words`, OnBytes/K/Oracle/Decodes.lean).
OBJECT: `DecR.coll` | `DecR.dcd` at the full size's decoder · USER: KeyMemberAtSeat.lean (the stored side of a member of a border's promise) · LETTERS: none.
Limits. AT CODE WORDS ALONE: of a table that is no table of code words nothing is said: there the event's chance is another row's. No hash stands here: the seed is any seed. Nothing on soundness.

-/
import Johnson.Top.Fire.Code.KeyAtName
import OnBytes.K.Oracle.Decodes
import OnBytes.Slice.CodeFacts

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
open Johnson.RunOne.KeyRows23 (BaseSt AtFk Fk fr₁ fr₂ fr₃ On₁ Cl₁ On₂ Cl₂ On₃ Cl₃ oneAt St₂ St₃ seam₁_at_fk seam₂_at_fk ends_at_fk)
open Johnson.RunOne.KeyRows1 (FirstLetters firstOn_of firstClaim_of CollCell ReadsL open₁)
open Johnson.RunOne.KeyRows23 (CellOnly inFront₂ front₂ seat open₃)
open Johnson.RunOne.KeyRows23 (p14At shared_flat names_blocks fileOk_all bareB)
open Lk6.AtPlan (keyFull)
open Johnson.RunOne.Law.AtFreeCfg (ReadOf)
open Johnson.RunOne.Law.KeyInScope (five_in_scope shared_lin_in_scope)


theorem dist_DN : Blocks.HasDist DN.ix.G (2 ^ 32 - (44040191 + 402653184) + 1) :=
  OnBytes.Slice.hasDist_genOf frS.P.T (by decide) (by decide)

theorem eM_lt : DN.eM < 2 ^ 32 - (44040191 + 402653184) + 1 := by decide

/-- **A table of code words has no collision at any seed.** -/
theorem notColl_words (y : DN.toDec.Pos → SgX) (M : DN.ix.Row → DN.toDec.Co → GE)
    (hf : ∀ r x, DN.tab y r x = DN.ix.G.mulVec (M r) x) (ρ : DN.Z.D) : ¬ DN.coll y ρ :=
  OnBytes.K.Oracle.not_coll_words DN dist_DN eM_lt y M hf ρ

/-- **The same of our tables' written letter, at a boundary's strings.** -/
theorem notCollN_words (D : WholeD) (y : (oneExternalString (2 ^ (D.at frS.P.T.a).a) SgX).Str) (M : DN.ix.Row → DN.toDec.Co → GE)
    (hf : ∀ r x, DN.tab y r x = DN.ix.G.mulVec (M r) x) (r : RecFull) :
    ¬ collN (strsOf (fr₁ (D.at frS.P.T.a)) ((y, fun _ => []) : (EAll (D.at frS.P.T.a) (allOf (D.at frS.P.T.a))).Str)) r := by
  unfold collN
  rw [yOf_cell]
  exact notColl_words y M hf r.1

/-- **And there the written decoder returns that table's message, at its own OOD sample.** -/
theorem dcdN_words (D : WholeD) (y : (oneExternalString (2 ^ (D.at frS.P.T.a).a) SgX).Str) (M : DN.ix.Row → DN.toDec.Co → GE)
    (hf : ∀ r x, DN.tab y r x = DN.ix.G.mulVec (M r) x) (ρ : DN.Z.D) :
    decN (strsOf (fr₁ (D.at frS.P.T.a)) ((y, fun _ => []) : (EAll (D.at frS.P.T.a) (allOf (D.at frS.P.T.a))).Str)).cell
      (ρ, DN.ix.ZR.val ρ (DN.ix.view M)) = some (DN.ix.view M) := by
  unfold decN
  rw [yOf_cell]
  exact OnBytes.K.Oracle.dcd_words DN dist_DN eM_lt y M hf ρ

end LPFD

#print axioms LPFD.dist_DN
#print axioms LPFD.eM_lt
#print axioms LPFD.notColl_words
#print axioms LPFD.notCollN_words
#print axioms LPFD.dcdN_words
