-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Top/Fire/Code/The35.lean (CARRIED BY A PROGRAM AND TABLES OF THIS PROJECT: the description is `Key.descriptionFromSource X N P`, the instance `Key.keyInstanceOfOutOfDomainSample`; THE FENCE OVER THE SCOPE (a statement over the goals' scope and the term from it to what the top asks) IS NOT IN THIS FILE; THE TABLES ARE THE WOVEN ONES: `On₁'` | `On₂'` | `On₃'`, KeyTablesR.lean: the tables' own promises AND «this record was reached»: so a law may spend the history; every field is the easier to pay: `KeepsAt.reached`): at the full size: ON THE PLAIN ROAD: AT THE KEY FILE's OWN DESCRIPTION `Key.descriptionFromSource X N P` AND THE TABLES OF KeyTablesR.lean: WHAT IS LEFT, AS ONE DEFINITION WHOSE FIELDS ARE THE 35 BLOCKS BY NUMBER: so that each kind's law has a named field to fill, and «proved» in this project's lists can be checked by Lean.
Main names.
  `The35`: 35 fields `r1_0 … r1_18 · r2_0 … r2_11 · r3_0 … r3_3`: field rj_i: `KeepsAt` (RowPieces.lean) at the i-th piece of chain j of the maker's own cut: «between the borders i and i + 1 of these tables, WITH THE HISTORY WOVEN IN, the promise is kept, and true behind gives true in front», at that piece's own errors.
  `The21`: the 21 of them that no theorem fills here. (Where
  this and lean/THEOREM.md differ, the page holds.)
  `the35_of_21`: **THE TERM THAT FILLS FOURTEEN**: 1.2 · 1.3 · 1.6 · 1.7 · 1.8 · 1.9 · 1.12 · 1.13 · 1.14 · 1.18 (ten: Johnson/RunOne/KeyTenAt.lean) and 2.0 · 2.11 · 3.1 · 3.3 (four: Johnson/RunOne/KeyKeeps23.lean), CALLED AT THE MAKER's OWN PIECES AT THE TABLES' OWN PROMISES AND LIFTED BY `KeepsAt.reached`, from `The21` and named facts: PUBLIC: the plan's lookups are a list of two (hl) · the shape has a message with W (hw) · ten blocks stand between the shared chain's front and its end (hin) · ON THE LETTERS: the collision and «not bad» read the stored table's cells alone (`CellOnly`) · the first reading reads no ledger · the pinned trees lie below the pieces' bases (hb₁: at all 19 pieces of the first chain · hb₂₀ · hb₂₁₁ · hb₃₁).
  `keyDebtCap_of_21`: FROM THE 21, THE NAMED FACTS, THE DATA AND «the pieces' errors are the cap» TO `KeyDebtCap (Key.descriptionFromSource X N P) VerifiableInference.Desc.Key.keyInstanceOfOutOfDomainSample A E DK file`: one chain of terms.
  `keyDebt_of_21`: the same at the payer's own errors, each piece's at most 2⁻¹ ^ 128: to `KeyDebt … (2⁻¹ ^ 128) …`.
  `rowsOwed_of_35`: `The35` with `AtFk` · `FirstLetters` · the three heads · hl · hw · hin gives the frame's `RowsOwed` AT THE WOVEN TABLES: THE THREE LENGTHS ARE PAID HERE (`flat_length`, Johnson/RunOne/KeyTenAt.lean · `shared_flat` · `second_length`, Johnson/RunOne/KeyCut23.lean); the seams, the end and the first boundary are theorems of Johnson/RunOne/KeyRowsAtFk.lean and KeyFirst.lean at the tables' own promises; the history rides (`rowsOwed_woven`, RowsWoven.lean).
Limits. A joining: of the 35 laws this file calls fourteen, all book-keeping blocks without a draw; the 21 that are left hold every block that draws: all the weight. Where the weight lies: a field alone is worth nothing: at errors as large as a round's number of challenges every field holds for nothing; and at the cap too all 35 hold for nothing where the promises hold nowhere (coll := «always»; a base whose recOf is none; an X with other than two lookups): what bars that is `FirstLetters` alone. The weight is «`The21` and `AtCap` and `FirstLetters` and `AtFk`, at one set of letters» (asked over the goals' scope by The21AtD.lean). This file does not show that it can be met at these tables. The 21, the fields 2.9 · 2.10 · 3.2 among them, are paid at the seat's written terms, in scope, where protocolDataWellFormed says yes: Johnson/Goal/Conditions/KeyOpenHolds.lean, whose head says what that is worth. (Where
this and lean/THEOREM.md differ, the page holds.) These tables take the plain Member | PIN | NoColl | hasSmp (Johnson/Desc/Msg.lean) by name, at a letter G. What is shown of these four in the abstract (fillG at one tenant, Johnson/Desc/Key/KeyFill.lean; famG over a family of seats, KeyFillFam.lean, KeyFillOracles.lean), and what is not: The21AtD.lean's head, Limits. This file shows no member. That F_K's honest run lays such strings and record is no theorem. Where no member is shown at F_K's own letters, a law or field at these tables that has PIN as an item or NoColl in its promise may be true and empty at the real protocol, and by itself closes nothing. Of this file alone: «fourteen of 35 laws are proved» is true only with «none of them draws, and at letters of which no member is shown here»; the 21 are not all that is left of the key file's hypothesis; a field filled is not a row paid at the cap. Nothing on soundness.

-/
import Johnson.Top.Fire.Code.KeyLeadsRamp
import Johnson.Desc.Key.Slot
import Johnson.Top.Fire.Code.KeyTablesR
import Johnson.RunOne.KeyFirst
import Johnson.RunOne.KeyTenAt
import Johnson.RunOne.KeyKeepsAt23

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

/-- Book-keeping on a list: a head, ten mapped members, one mapped last. -/
theorem at_eleven {α β : Type} (f : α → β) (a : β) (l : List α) (z : α) (h : l.length = 10) : (a :: (l ++ [z]).map f)[11]? = some (f z) := by
  have e : (a :: (l ++ [z]).map f)[11]? = ((l ++ [z]).map f)[10]? := List.getElem?_cons_succ
  rw [e, List.getElem?_map, ← h, List.getElem?_concat_length]
  rfl

theorem len_twelve {α β : Type} (f : α → β) (a : β) (l : List α) (z : α) (h : l.length = 10) : (a :: (l ++ [z]).map f).length = 12 := by
  simp [h]

section
variable {Cells M Smp Rec : Type} (X : Source) (N : H2U.PlaceNums) (P : LaterPlaces)
    {Xr : Type} (A : (frS.toDecR frZ 402653181).Claims Xr) (E : Coding A) (DK : WholeD) {W : Type}
    (c₁ : Block (Fk X N P).S₁ (Fk X N P).Cl) (k₁ : List (Block (Fk X N P).S₁ (Fk X N P).Cl)) (c₂ : Block (Fk X N P).S₂ (Fk X N P).Cl)
    (k₂ : List (Block (Fk X N P).S₂ (Fk X N P).Cl)) (c₃ : Block (Fk X N P).S₃ (Fk X N P).Cl) (k₃ : List (Block (Fk X N P).S₃ (Fk X N P).Cl))
    (rest₁ : (i : ℕ) → (ds : List RDT) → Rest (ckP .two)
      (frameAt (DK.at frS.P.T.a) (allOf (DK.at frS.P.T.a)) (DK.at frS.P.T.a).key₁ 0) ((Fk X N P).XiPub × (Fk X N P).S₁) W ds)
    (rest₂ : (i : ℕ) → (ds : List RDT) → Rest (ckP .two)
      (frameAt (DK.at frS.P.T.a) (allOf (DK.at frS.P.T.a)) (DK.at frS.P.T.a).key₂ 0) (((Fk X N P).XiPub × (Fk X N P).S₁) × (Fk X N P).S₂) W ds)
    (rest₃ : (i : ℕ) → (ds : List RDT) → Rest (ckP .two)
      (frameAt (DK.at frS.P.T.a) (allOf (DK.at frS.P.T.a)) (DK.at frS.P.T.a).key₃ (Fk X N P).lastChainFirstTreeNumber)
      (((Fk X N P).XiPub × (Fk X N P).S₁ × (Fk X N P).S₂) × (Fk X N P).S₃) W ds)
    (dW wEnd : W)
    (B : BaseSt Cells M Smp Rec) (at_ : Where) (R : KRead Cells M) (enc : (ℕ → OnBytes.E) → ℕ → OnBytes.E) (rad : ℕ)
    (coll : Strs → Rec → Prop) (off₂ off₃ : ℕ → ℕ)

/-- **What is left at the tables of KeyTablesR.lean: one law a block, by the block's number.** -/
structure The35 : Prop where
  /-- 1.0: idx.1.send -/
  r1_0 : KeepsAt (On₁' X N P (DK.at frS.P.T.a) B at_ R coll) (Cl₁ X N P (DK.at frS.P.T.a) B at_ R) ((atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).p₁ :: (atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).l₁) 0
  /-- 1.1: msg.1.send -/
  r1_1 : KeepsAt (On₁' X N P (DK.at frS.P.T.a) B at_ R coll) (Cl₁ X N P (DK.at frS.P.T.a) B at_ R) ((atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).p₁ :: (atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).l₁) 1
  /-- 1.2: look0: laid -/
  r1_2 : KeepsAt (On₁' X N P (DK.at frS.P.T.a) B at_ R coll) (Cl₁ X N P (DK.at frS.P.T.a) B at_ R) ((atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).p₁ :: (atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).l₁) 2
  /-- 1.3: look0.1.caller -/
  r1_3 : KeepsAt (On₁' X N P (DK.at frS.P.T.a) B at_ R coll) (Cl₁ X N P (DK.at frS.P.T.a) B at_ R) ((atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).p₁ :: (atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).l₁) 3
  /-- 1.4: look0.2 (K3) -/
  r1_4 : KeepsAt (On₁' X N P (DK.at frS.P.T.a) B at_ R coll) (Cl₁ X N P (DK.at frS.P.T.a) B at_ R) ((atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).p₁ :: (atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).l₁) 4
  /-- 1.5: look0.3.layer -/
  r1_5 : KeepsAt (On₁' X N P (DK.at frS.P.T.a) B at_ R coll) (Cl₁ X N P (DK.at frS.P.T.a) B at_ R) ((atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).p₁ :: (atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).l₁) 5
  /-- 1.6: look0: behind the batching -/
  r1_6 : KeepsAt (On₁' X N P (DK.at frS.P.T.a) B at_ R coll) (Cl₁ X N P (DK.at frS.P.T.a) B at_ R) ((atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).p₁ :: (atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).l₁) 6
  /-- 1.7: look0: cleared -/
  r1_7 : KeepsAt (On₁' X N P (DK.at frS.P.T.a) B at_ R coll) (Cl₁ X N P (DK.at frS.P.T.a) B at_ R) ((atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).p₁ :: (atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).l₁) 7
  /-- 1.8: look1: laid -/
  r1_8 : KeepsAt (On₁' X N P (DK.at frS.P.T.a) B at_ R coll) (Cl₁ X N P (DK.at frS.P.T.a) B at_ R) ((atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).p₁ :: (atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).l₁) 8
  /-- 1.9: look1.1.caller -/
  r1_9 : KeepsAt (On₁' X N P (DK.at frS.P.T.a) B at_ R coll) (Cl₁ X N P (DK.at frS.P.T.a) B at_ R) ((atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).p₁ :: (atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).l₁) 9
  /-- 1.10: look1.2 (K3) -/
  r1_10 : KeepsAt (On₁' X N P (DK.at frS.P.T.a) B at_ R coll) (Cl₁ X N P (DK.at frS.P.T.a) B at_ R) ((atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).p₁ :: (atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).l₁) 10
  /-- 1.11: look1.3.layer -/
  r1_11 : KeepsAt (On₁' X N P (DK.at frS.P.T.a) B at_ R coll) (Cl₁ X N P (DK.at frS.P.T.a) B at_ R) ((atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).p₁ :: (atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).l₁) 11
  /-- 1.12: look1: behind the batching -/
  r1_12 : KeepsAt (On₁' X N P (DK.at frS.P.T.a) B at_ R coll) (Cl₁ X N P (DK.at frS.P.T.a) B at_ R) ((atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).p₁ :: (atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).l₁) 12
  /-- 1.13: look1: cleared -/
  r1_13 : KeepsAt (On₁' X N P (DK.at frS.P.T.a) B at_ R coll) (Cl₁ X N P (DK.at frS.P.T.a) B at_ R) ((atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).p₁ :: (atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).l₁) 13
  /-- 1.14: rng.0.rows -/
  r1_14 : KeepsAt (On₁' X N P (DK.at frS.P.T.a) B at_ R coll) (Cl₁ X N P (DK.at frS.P.T.a) B at_ R) ((atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).p₁ :: (atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).l₁) 14
  /-- 1.15: rng (K12) -/
  r1_15 : KeepsAt (On₁' X N P (DK.at frS.P.T.a) B at_ R coll) (Cl₁ X N P (DK.at frS.P.T.a) B at_ R) ((atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).p₁ :: (atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).l₁) 15
  /-- 1.16: batt.1.batt (K13) -/
  r1_16 : KeepsAt (On₁' X N P (DK.at frS.P.T.a) B at_ R coll) (Cl₁ X N P (DK.at frS.P.T.a) B at_ R) ((atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).p₁ :: (atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).l₁) 16
  /-- 1.17: w.1.send -/
  r1_17 : KeepsAt (On₁' X N P (DK.at frS.P.T.a) B at_ R coll) (Cl₁ X N P (DK.at frS.P.T.a) B at_ R) ((atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).p₁ :: (atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).l₁) 17
  /-- 1.18: seal -/
  r1_18 : KeepsAt (On₁' X N P (DK.at frS.P.T.a) B at_ R coll) (Cl₁ X N P (DK.at frS.P.T.a) B at_ R) ((atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).p₁ :: (atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).l₁) 18
  /-- 2.0: the shared chain's front -/
  r2_0 : KeepsAt (On₂' X N P (DK.at frS.P.T.a) B at_ R enc rad coll off₂) (Cl₂ X N P (DK.at frS.P.T.a) B at_ R enc rad) ((atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).p₂ :: (atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).l₂) 0
  /-- 2.1: LIN point -/
  r2_1 : KeepsAt (On₂' X N P (DK.at frS.P.T.a) B at_ R enc rad coll off₂) (Cl₂ X N P (DK.at frS.P.T.a) B at_ R enc rad) ((atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).p₂ :: (atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).l₂) 1
  /-- 2.2: send o_u -/
  r2_2 : KeepsAt (On₂' X N P (DK.at frS.P.T.a) B at_ R enc rad coll off₂) (Cl₂ X N P (DK.at frS.P.T.a) B at_ R enc rad) ((atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).p₂ :: (atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).l₂) 2
  /-- 2.3: (rec_gamma) -/
  r2_3 : KeepsAt (On₂' X N P (DK.at frS.P.T.a) B at_ R enc rad coll off₂) (Cl₂ X N P (DK.at frS.P.T.a) B at_ R enc rad) ((atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).p₂ :: (atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).l₂) 3
  /-- 2.4: LOC -/
  r2_4 : KeepsAt (On₂' X N P (DK.at frS.P.T.a) B at_ R enc rad coll off₂) (Cl₂ X N P (DK.at frS.P.T.a) B at_ R enc rad) ((atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).p₂ :: (atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).l₂) 4
  /-- 2.5: send o_omega -/
  r2_5 : KeepsAt (On₂' X N P (DK.at frS.P.T.a) B at_ R enc rad coll off₂) (Cl₂ X N P (DK.at frS.P.T.a) B at_ R enc rad) ((atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).p₂ :: (atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).l₂) 5
  /-- 2.6: joins -/
  r2_6 : KeepsAt (On₂' X N P (DK.at frS.P.T.a) B at_ R enc rad coll off₂) (Cl₂ X N P (DK.at frS.P.T.a) B at_ R enc rad) ((atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).p₂ :: (atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).l₂) 6
  /-- 2.7: LIN zeta -/
  r2_7 : KeepsAt (On₂' X N P (DK.at frS.P.T.a) B at_ R enc rad coll off₂) (Cl₂ X N P (DK.at frS.P.T.a) B at_ R enc rad) ((atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).p₂ :: (atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).l₂) 7
  /-- 2.8: SPLIT -/
  r2_8 : KeepsAt (On₂' X N P (DK.at frS.P.T.a) B at_ R enc rad coll off₂) (Cl₂ X N P (DK.at frS.P.T.a) B at_ R enc rad) ((atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).p₂ :: (atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).l₂) 8
  /-- 2.9: the proximity test (chain 2, piece 9) -/
  r2_9 : KeepsAt (On₂' X N P (DK.at frS.P.T.a) B at_ R enc rad coll off₂) (Cl₂ X N P (DK.at frS.P.T.a) B at_ R enc rad) ((atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).p₂ :: (atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).l₂) 9
  /-- 2.10: the proximity test (chain 2, piece 10) -/
  r2_10 : KeepsAt (On₂' X N P (DK.at frS.P.T.a) B at_ R enc rad coll off₂) (Cl₂ X N P (DK.at frS.P.T.a) B at_ R enc rad) ((atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).p₂ :: (atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).l₂) 10
  /-- 2.11: the end of chain 2 -/
  r2_11 : KeepsAt (On₂' X N P (DK.at frS.P.T.a) B at_ R enc rad coll off₂) (Cl₂ X N P (DK.at frS.P.T.a) B at_ R enc rad) ((atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).p₂ :: (atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).l₂) 11
  /-- 3.0: K14, second part -/
  r3_0 : KeepsAt (On₃' X N P (DK.at frS.P.T.a) B at_ R coll off₂ off₃) (Cl₃ X N P (DK.at frS.P.T.a) B at_ R) ((atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).p₃ :: (atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).l₃) 0
  /-- 3.1: the taken trees' sources -/
  r3_1 : KeepsAt (On₃' X N P (DK.at frS.P.T.a) B at_ R coll off₂ off₃) (Cl₃ X N P (DK.at frS.P.T.a) B at_ R) ((atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).p₃ :: (atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).l₃) 1
  /-- 3.2: the proximity test (chain 3, piece 2) -/
  r3_2 : KeepsAt (On₃' X N P (DK.at frS.P.T.a) B at_ R coll off₂ off₃) (Cl₃ X N P (DK.at frS.P.T.a) B at_ R) ((atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).p₃ :: (atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).l₃) 2
  /-- 3.3: the end of chain 3 -/
  r3_3 : KeepsAt (On₃' X N P (DK.at frS.P.T.a) B at_ R coll off₂ off₃) (Cl₃ X N P (DK.at frS.P.T.a) B at_ R) ((atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).p₃ :: (atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).l₃) 3

/-- **The 21 that `the35_of_21` does not fill.** -/
structure The21 : Prop where
  /-- 1.0: idx.1.send -/
  r1_0 : KeepsAt (On₁' X N P (DK.at frS.P.T.a) B at_ R coll) (Cl₁ X N P (DK.at frS.P.T.a) B at_ R) ((atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).p₁ :: (atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).l₁) 0
  /-- 1.1: msg.1.send -/
  r1_1 : KeepsAt (On₁' X N P (DK.at frS.P.T.a) B at_ R coll) (Cl₁ X N P (DK.at frS.P.T.a) B at_ R) ((atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).p₁ :: (atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).l₁) 1
  /-- 1.4: look0.2 (K3) -/
  r1_4 : KeepsAt (On₁' X N P (DK.at frS.P.T.a) B at_ R coll) (Cl₁ X N P (DK.at frS.P.T.a) B at_ R) ((atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).p₁ :: (atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).l₁) 4
  /-- 1.5: look0.3.layer -/
  r1_5 : KeepsAt (On₁' X N P (DK.at frS.P.T.a) B at_ R coll) (Cl₁ X N P (DK.at frS.P.T.a) B at_ R) ((atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).p₁ :: (atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).l₁) 5
  /-- 1.10: look1.2 (K3) -/
  r1_10 : KeepsAt (On₁' X N P (DK.at frS.P.T.a) B at_ R coll) (Cl₁ X N P (DK.at frS.P.T.a) B at_ R) ((atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).p₁ :: (atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).l₁) 10
  /-- 1.11: look1.3.layer -/
  r1_11 : KeepsAt (On₁' X N P (DK.at frS.P.T.a) B at_ R coll) (Cl₁ X N P (DK.at frS.P.T.a) B at_ R) ((atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).p₁ :: (atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).l₁) 11
  /-- 1.15: rng (K12) -/
  r1_15 : KeepsAt (On₁' X N P (DK.at frS.P.T.a) B at_ R coll) (Cl₁ X N P (DK.at frS.P.T.a) B at_ R) ((atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).p₁ :: (atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).l₁) 15
  /-- 1.16: batt.1.batt (K13) -/
  r1_16 : KeepsAt (On₁' X N P (DK.at frS.P.T.a) B at_ R coll) (Cl₁ X N P (DK.at frS.P.T.a) B at_ R) ((atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).p₁ :: (atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).l₁) 16
  /-- 1.17: w.1.send -/
  r1_17 : KeepsAt (On₁' X N P (DK.at frS.P.T.a) B at_ R coll) (Cl₁ X N P (DK.at frS.P.T.a) B at_ R) ((atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).p₁ :: (atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).l₁) 17
  /-- 2.1: LIN point -/
  r2_1 : KeepsAt (On₂' X N P (DK.at frS.P.T.a) B at_ R enc rad coll off₂) (Cl₂ X N P (DK.at frS.P.T.a) B at_ R enc rad) ((atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).p₂ :: (atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).l₂) 1
  /-- 2.2: send o_u -/
  r2_2 : KeepsAt (On₂' X N P (DK.at frS.P.T.a) B at_ R enc rad coll off₂) (Cl₂ X N P (DK.at frS.P.T.a) B at_ R enc rad) ((atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).p₂ :: (atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).l₂) 2
  /-- 2.3: (rec_gamma) -/
  r2_3 : KeepsAt (On₂' X N P (DK.at frS.P.T.a) B at_ R enc rad coll off₂) (Cl₂ X N P (DK.at frS.P.T.a) B at_ R enc rad) ((atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).p₂ :: (atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).l₂) 3
  /-- 2.4: LOC -/
  r2_4 : KeepsAt (On₂' X N P (DK.at frS.P.T.a) B at_ R enc rad coll off₂) (Cl₂ X N P (DK.at frS.P.T.a) B at_ R enc rad) ((atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).p₂ :: (atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).l₂) 4
  /-- 2.5: send o_omega -/
  r2_5 : KeepsAt (On₂' X N P (DK.at frS.P.T.a) B at_ R enc rad coll off₂) (Cl₂ X N P (DK.at frS.P.T.a) B at_ R enc rad) ((atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).p₂ :: (atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).l₂) 5
  /-- 2.6: joins -/
  r2_6 : KeepsAt (On₂' X N P (DK.at frS.P.T.a) B at_ R enc rad coll off₂) (Cl₂ X N P (DK.at frS.P.T.a) B at_ R enc rad) ((atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).p₂ :: (atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).l₂) 6
  /-- 2.7: LIN zeta -/
  r2_7 : KeepsAt (On₂' X N P (DK.at frS.P.T.a) B at_ R enc rad coll off₂) (Cl₂ X N P (DK.at frS.P.T.a) B at_ R enc rad) ((atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).p₂ :: (atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).l₂) 7
  /-- 2.8: SPLIT -/
  r2_8 : KeepsAt (On₂' X N P (DK.at frS.P.T.a) B at_ R enc rad coll off₂) (Cl₂ X N P (DK.at frS.P.T.a) B at_ R enc rad) ((atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).p₂ :: (atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).l₂) 8
  /-- 2.9: the proximity test (chain 2, piece 9) -/
  r2_9 : KeepsAt (On₂' X N P (DK.at frS.P.T.a) B at_ R enc rad coll off₂) (Cl₂ X N P (DK.at frS.P.T.a) B at_ R enc rad) ((atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).p₂ :: (atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).l₂) 9
  /-- 2.10: the proximity test (chain 2, piece 10) -/
  r2_10 : KeepsAt (On₂' X N P (DK.at frS.P.T.a) B at_ R enc rad coll off₂) (Cl₂ X N P (DK.at frS.P.T.a) B at_ R enc rad) ((atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).p₂ :: (atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).l₂) 10
  /-- 3.0: K14, second part -/
  r3_0 : KeepsAt (On₃' X N P (DK.at frS.P.T.a) B at_ R coll off₂ off₃) (Cl₃ X N P (DK.at frS.P.T.a) B at_ R) ((atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).p₃ :: (atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).l₃) 0
  /-- 3.2: the proximity test (chain 3, piece 2) -/
  r3_2 : KeepsAt (On₃' X N P (DK.at frS.P.T.a) B at_ R coll off₂ off₃) (Cl₃ X N P (DK.at frS.P.T.a) B at_ R) ((atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).p₃ :: (atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).l₃) 2

set_option maxHeartbeats 4000000 in
/-- **The term that fills fourteen.** -/
theorem the35_of_21 (H : The21 X N P DK c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd B at_ R enc rad coll off₂ off₃)
    (q₁ : (Fk X N P).first.blocksInOrder = c₁ :: k₁) (q₂ : (Fk X N P).shared.blocksInOrder = c₂ :: k₂) (q₃ : (Fk X N P).second.blocksInOrder = c₃ :: k₃)
    (x₀ x₁ : Lookup) (hl : lookupsOf (oneAt X) = [x₀, x₁])
    (bw : Block FirstState Claim)
    (hw : sendW (oneAt X) pieces (rootsBefore X.Y.D.1 (batchRound X.Y.D.1))
      (groupsTold X.Y.told.1 (rootsBefore X.Y.D.1 (lastSendRound X.Y.D.1)) (rootsAt X.Y.D.1 (lastSendRound X.Y.D.1))) = some bw)
    (hin : (inFront₂ X P).length = 10)
    (hc : CellOnly coll) (hG : ReadsL B.h₁)
    (hb₁ : ∀ n p, ((atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).p₁ :: (atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).l₁)[n]? = some p → ∀ j ∈ pinned (open₁ 2 n), (at_ j).1 < p.base)
    (hb₂₀ : ∀ p, ((atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).p₂ :: (atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).l₂)[0]? = some p → ∀ j ∈ pinned seam, (at_ j).1 < p.base)
    (hb₂₁₁ : ∀ p, ((atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).p₂ :: (atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).l₂)[11]? = some p → ∀ j ∈ pinned end₂, (at_ j).1 < p.base)
    (hb₃₁ : ∀ p, ((atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).p₃ :: (atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).l₃)[1]? = some p → ∀ j ∈ pinned (open₃ 1), (at_ j).1 < p.base) :
    The35 X N P DK c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd B at_ R enc rad coll off₂ off₃ :=
  have hcoll : CollCell coll := fun y y' r e => (hc y y' r e).1
  { H with
    r1_2 := KeepsAt.reached _ _ (rowBlocksF₁ q₁ 2) (show KeepsAt (On₁ X N P (DK.at frS.P.T.a) B at_ R coll) (Cl₁ X N P (DK.at frS.P.T.a) B at_ R) ((atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).p₁ :: (atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).l₁) 2 from fun p hp => by
      have hbp := hb₁ 2 p hp
      obtain ⟨b, base, ds, back, hb, rfl⟩ := rowGet₁ (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd 2 p hp
      rw [← q₁] at hb
      exact Johnson.RunOne.KeyRows1.at_laid0 (Fk X N P) (fr₁ (DK.at frS.P.T.a)) B.h₁ at_ (oneAt X) R coll X.Y.D.1 X.Y.told.1 X.set N x₀ x₁ hl b hb _ rfl hbp hcoll)
    r1_3 := KeepsAt.reached _ _ (rowBlocksF₁ q₁ 3) (show KeepsAt (On₁ X N P (DK.at frS.P.T.a) B at_ R coll) (Cl₁ X N P (DK.at frS.P.T.a) B at_ R) ((atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).p₁ :: (atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).l₁) 3 from fun p hp => by
      have hbp := hb₁ 3 p hp
      obtain ⟨b, base, ds, back, hb, rfl⟩ := rowGet₁ (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd 3 p hp
      rw [← q₁] at hb
      exact Johnson.RunOne.KeyRows1.at_caller0 (Fk X N P) (fr₁ (DK.at frS.P.T.a)) B.h₁ at_ (oneAt X) R coll X.Y.D.1 X.Y.told.1 X.set N x₀ x₁ hl b hb _ rfl hbp hcoll hG)
    r1_6 := KeepsAt.reached _ _ (rowBlocksF₁ q₁ 6) (show KeepsAt (On₁ X N P (DK.at frS.P.T.a) B at_ R coll) (Cl₁ X N P (DK.at frS.P.T.a) B at_ R) ((atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).p₁ :: (atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).l₁) 6 from fun p hp => by
      have hbp := hb₁ 6 p hp
      obtain ⟨b, base, ds, back, hb, rfl⟩ := rowGet₁ (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd 6 p hp
      rw [← q₁] at hb
      exact Johnson.RunOne.KeyRows1.at_behind0 (Fk X N P) (fr₁ (DK.at frS.P.T.a)) B.h₁ at_ (oneAt X) R coll X.Y.D.1 X.Y.told.1 X.set N x₀ x₁ hl b hb _ rfl hbp hcoll)
    r1_7 := KeepsAt.reached _ _ (rowBlocksF₁ q₁ 7) (show KeepsAt (On₁ X N P (DK.at frS.P.T.a) B at_ R coll) (Cl₁ X N P (DK.at frS.P.T.a) B at_ R) ((atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).p₁ :: (atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).l₁) 7 from fun p hp => by
      have hbp := hb₁ 7 p hp
      obtain ⟨b, base, ds, back, hb, rfl⟩ := rowGet₁ (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd 7 p hp
      rw [← q₁] at hb
      exact Johnson.RunOne.KeyRows1.at_cleared0 (Fk X N P) (fr₁ (DK.at frS.P.T.a)) B.h₁ at_ (oneAt X) R coll X.Y.D.1 X.Y.told.1 X.set N x₀ x₁ hl b hb _ rfl hbp hcoll hG)
    r1_8 := KeepsAt.reached _ _ (rowBlocksF₁ q₁ 8) (show KeepsAt (On₁ X N P (DK.at frS.P.T.a) B at_ R coll) (Cl₁ X N P (DK.at frS.P.T.a) B at_ R) ((atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).p₁ :: (atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).l₁) 8 from fun p hp => by
      have hbp := hb₁ 8 p hp
      obtain ⟨b, base, ds, back, hb, rfl⟩ := rowGet₁ (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd 8 p hp
      rw [← q₁] at hb
      exact Johnson.RunOne.KeyRows1.at_laid1 (Fk X N P) (fr₁ (DK.at frS.P.T.a)) B.h₁ at_ (oneAt X) R coll X.Y.D.1 X.Y.told.1 X.set N x₀ x₁ hl b hb _ rfl hbp hcoll)
    r1_9 := KeepsAt.reached _ _ (rowBlocksF₁ q₁ 9) (show KeepsAt (On₁ X N P (DK.at frS.P.T.a) B at_ R coll) (Cl₁ X N P (DK.at frS.P.T.a) B at_ R) ((atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).p₁ :: (atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).l₁) 9 from fun p hp => by
      have hbp := hb₁ 9 p hp
      obtain ⟨b, base, ds, back, hb, rfl⟩ := rowGet₁ (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd 9 p hp
      rw [← q₁] at hb
      exact Johnson.RunOne.KeyRows1.at_caller1 (Fk X N P) (fr₁ (DK.at frS.P.T.a)) B.h₁ at_ (oneAt X) R coll X.Y.D.1 X.Y.told.1 X.set N x₀ x₁ hl b hb _ rfl hbp hcoll hG)
    r1_12 := KeepsAt.reached _ _ (rowBlocksF₁ q₁ 12) (show KeepsAt (On₁ X N P (DK.at frS.P.T.a) B at_ R coll) (Cl₁ X N P (DK.at frS.P.T.a) B at_ R) ((atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).p₁ :: (atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).l₁) 12 from fun p hp => by
      have hbp := hb₁ 12 p hp
      obtain ⟨b, base, ds, back, hb, rfl⟩ := rowGet₁ (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd 12 p hp
      rw [← q₁] at hb
      exact Johnson.RunOne.KeyRows1.at_behind1 (Fk X N P) (fr₁ (DK.at frS.P.T.a)) B.h₁ at_ (oneAt X) R coll X.Y.D.1 X.Y.told.1 X.set N x₀ x₁ hl b hb _ rfl hbp hcoll)
    r1_13 := KeepsAt.reached _ _ (rowBlocksF₁ q₁ 13) (show KeepsAt (On₁ X N P (DK.at frS.P.T.a) B at_ R coll) (Cl₁ X N P (DK.at frS.P.T.a) B at_ R) ((atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).p₁ :: (atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).l₁) 13 from fun p hp => by
      have hbp := hb₁ 13 p hp
      obtain ⟨b, base, ds, back, hb, rfl⟩ := rowGet₁ (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd 13 p hp
      rw [← q₁] at hb
      exact Johnson.RunOne.KeyRows1.at_cleared1 (Fk X N P) (fr₁ (DK.at frS.P.T.a)) B.h₁ at_ (oneAt X) R coll X.Y.D.1 X.Y.told.1 X.set N x₀ x₁ hl b hb _ rfl hbp hcoll hG)
    r1_14 := KeepsAt.reached _ _ (rowBlocksF₁ q₁ 14) (show KeepsAt (On₁ X N P (DK.at frS.P.T.a) B at_ R coll) (Cl₁ X N P (DK.at frS.P.T.a) B at_ R) ((atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).p₁ :: (atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).l₁) 14 from fun p hp => by
      have hbp := hb₁ 14 p hp
      obtain ⟨b, base, ds, back, hb, rfl⟩ := rowGet₁ (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd 14 p hp
      rw [← q₁] at hb
      exact Johnson.RunOne.KeyRows1.at_rngRows (Fk X N P) (fr₁ (DK.at frS.P.T.a)) B.h₁ at_ (oneAt X) R coll X.Y.D.1 X.Y.told.1 X.set N x₀ x₁ hl b hb _ rfl hbp hcoll hG)
    r1_18 := KeepsAt.reached _ _ (rowBlocksF₁ q₁ 18) (show KeepsAt (On₁ X N P (DK.at frS.P.T.a) B at_ R coll) (Cl₁ X N P (DK.at frS.P.T.a) B at_ R) ((atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).p₁ :: (atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).l₁) 18 from fun p hp => by
      have hbp := hb₁ 18 p hp
      obtain ⟨b, base, ds, back, hb, rfl⟩ := rowGet₁ (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd 18 p hp
      rw [← q₁] at hb
      exact Johnson.RunOne.KeyRows1.at_seal (Fk X N P) (fr₁ (DK.at frS.P.T.a)) B.h₁ at_ (oneAt X) R coll X.Y.D.1 X.Y.told.1 X.set N x₀ x₁ hl bw hw b hb _ rfl hbp hcoll)
    r2_0 := KeepsAt.reached _ _ (rowBlocksF₂ q₂ 0) (show KeepsAt (On₂ X N P (DK.at frS.P.T.a) B at_ R enc rad coll off₂) (Cl₂ X N P (DK.at frS.P.T.a) B at_ R enc rad) ((atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).p₂ :: (atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).l₂) 0 from fun p hp => by
      have hbp := hb₂₀ p hp
      obtain ⟨b, base, ds, back, hb, rfl⟩ := rowGet₂ (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd 0 p hp
      rw [← q₂, Johnson.RunOne.KeyRows23.shared_flat] at hb
      obtain rfl : front₂ X = b := Option.some.inj (List.getElem?_cons_zero.symm.trans hb)
      apply Johnson.RunOne.KeyRows23.front₂_keeps <;> assumption)
    r2_11 := KeepsAt.reached _ _ (rowBlocksF₂ q₂ 11) (show KeepsAt (On₂ X N P (DK.at frS.P.T.a) B at_ R enc rad coll off₂) (Cl₂ X N P (DK.at frS.P.T.a) B at_ R enc rad) ((atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).p₂ :: (atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).l₂) 11 from fun p hp => by
      have hbp := hb₂₁₁ p hp
      obtain ⟨b, base, ds, back, hb, rfl⟩ := rowGet₂ (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd 11 p hp
      have e := q₂.symm.trans (Johnson.RunOne.KeyRows23.shared_flat X N P)
      obtain rfl := Option.some.inj ((at_eleven seat (front₂ X) (inFront₂ X P) _ hin).symm.trans ((congrArg (fun l => l[11]?) e).symm.trans hb))
      apply Johnson.RunOne.KeyRows23.end₂_keeps <;> assumption)
    r3_1 := KeepsAt.reached _ _ (rowBlocksF₃ q₃ 1) (show KeepsAt (On₃ X N P (DK.at frS.P.T.a) B at_ R coll off₂ off₃) (Cl₃ X N P (DK.at frS.P.T.a) B at_ R) ((atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).p₃ :: (atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).l₃) 1 from fun p hp => by
      have hbp := hb₃₁ p hp
      obtain ⟨b, base, ds, back, hb, rfl⟩ := rowGet₃ (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd 1 p hp
      obtain ⟨f, hf, -⟩ := Johnson.RunOne.KeyRows23.second_flat X N P
      rw [← q₃, hf] at hb
      obtain rfl := Option.some.inj hb
      apply Johnson.RunOne.KeyRows23.sources₃_keeps <;> assumption)
    r3_3 := KeepsAt.reached _ _ (rowBlocksF₃ q₃ 3) (show KeepsAt (On₃ X N P (DK.at frS.P.T.a) B at_ R coll off₂ off₃) (Cl₃ X N P (DK.at frS.P.T.a) B at_ R) ((atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).p₃ :: (atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).l₃) 3 from fun p hp => by
      obtain ⟨b, base, ds, back, hb, rfl⟩ := rowGet₃ (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd 3 p hp
      obtain ⟨f, hf, -⟩ := Johnson.RunOne.KeyRows23.second_flat X N P
      rw [← q₃, hf] at hb
      obtain rfl := Option.some.inj hb
      apply Johnson.RunOne.KeyRows23.end₃_keeps
      assumption) }

set_option maxHeartbeats 4000000 in
/-- **The 35, with the facts on the letters and three public facts, give the frame's `RowsOwed` AT THE WOVEN TABLES**: the three lengths are paid here; the two seams, the end and the first boundary's two facts are theorems of Johnson/RunOne/KeyRowsAtFk.lean and Johnson/RunOne/KeyFirst.lean at the tables' own promises; the history rides (`rowsOwed_woven`). -/
theorem rowsOwed_of_35 [Inhabited Cells] [Inhabited M] (ρ : RecFull → Rec) (cellsOf : (lettersAt A (relationsAndEncodingOfClaims A E)).conf.Msg → Cells)
    (H : The35 X N P DK c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd B at_ R enc rad coll off₂ off₃)
    (atFk : AtFk X B at_ R off₃)
    (first : FirstLetters (fr₁ (DK.at frS.P.T.a)) B.h₁ at_ (oneAt X) R coll VerifiableInference.Desc.Key.keyInstanceOfOutOfDomainSample (Fk X N P).start₁
      (fun y : (oneExternalString (2 ^ (DK.at frS.P.T.a).a) SgX).Str => ((y, fun _ => []) : (EAll (DK.at frS.P.T.a) (allOf (DK.at frS.P.T.a))).Str)) ρ
      (fun y r => (lettersAt A (relationsAndEncodingOfClaims A E)).conf.coll y r.1) (fun y r => (lettersAt A (relationsAndEncodingOfClaims A E)).conf.dcd y r) (lettersAt A (relationsAndEncodingOfClaims A E)).conf.held cellsOf)
    (q₁ : (Fk X N P).first.blocksInOrder = c₁ :: k₁) (q₂ : (Fk X N P).shared.blocksInOrder = c₂ :: k₂) (q₃ : (Fk X N P).second.blocksInOrder = c₃ :: k₃)
    (x₀ x₁ : Lookup) (hl : lookupsOf (oneAt X) = [x₀, x₁])
    (bw : Block FirstState Claim)
    (hw : sendW (oneAt X) pieces (rootsBefore X.Y.D.1 (batchRound X.Y.D.1))
      (groupsTold X.Y.told.1 (rootsBefore X.Y.D.1 (lastSendRound X.Y.D.1)) (rootsAt X.Y.D.1 (lastSendRound X.Y.D.1))) = some bw)
    (hin : (inFront₂ X P).length = 10) :
    RowsOwed (Fk X N P) VerifiableInference.Desc.Key.keyInstanceOfOutOfDomainSample A E DK c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd
      (On₁' X N P (DK.at frS.P.T.a) B at_ R coll) (Cl₁ X N P (DK.at frS.P.T.a) B at_ R) (On₂' X N P (DK.at frS.P.T.a) B at_ R enc rad coll off₂) (Cl₂ X N P (DK.at frS.P.T.a) B at_ R enc rad) (On₃' X N P (DK.at frS.P.T.a) B at_ R coll off₂ off₃) (Cl₃ X N P (DK.at frS.P.T.a) B at_ R) := by
  have n₁ : k₁.length = 18 := by
    have e := Johnson.RunOne.KeyRows1.flat_length (oneAt X) X.Y.D.1 X.Y.told.1 X.set N x₀ x₁ hl bw hw
    have e' : (Fk X N P).first.blocksInOrder.length = 19 := e
    rw [q₁, List.length_cons] at e'
    omega
  have n₂ : k₂.length = 11 := by
    have e := q₂.symm.trans (Johnson.RunOne.KeyRows23.shared_flat X N P)
    have e12 : k₂.length + 1 = 12 := (congrArg List.length e).trans (len_twelve seat (front₂ X) (inFront₂ X P) _ hin)
    omega
  have n₃ : k₃.length = 3 := by
    have e := Johnson.RunOne.KeyRows23.second_length X N P
    rw [q₃, List.length_cons] at e
    omega
  have S : SeamsOwed (Fk X N P) VerifiableInference.Desc.Key.keyInstanceOfOutOfDomainSample A E DK c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd
      (On₁ X N P (DK.at frS.P.T.a) B at_ R coll) (Cl₁ X N P (DK.at frS.P.T.a) B at_ R) (On₂ X N P (DK.at frS.P.T.a) B at_ R enc rad coll off₂) (Cl₂ X N P (DK.at frS.P.T.a) B at_ R enc rad) (On₃ X N P (DK.at frS.P.T.a) B at_ R coll off₂ off₃) (Cl₃ X N P (DK.at frS.P.T.a) B at_ R) :=
    { seam₁ := by
        rw [rowLen₁, n₁]
        exact fun b h => seam₁_at_fk X N P (DK.at frS.P.T.a) B at_ R enc rad coll off₂ off₃ atFk b h
      seam₂ := by
        rw [rowLen₂, n₂]
        exact fun b h => seam₂_at_fk X N P (DK.at frS.P.T.a) B at_ R enc rad coll off₂ off₃ atFk b h
      ends := by
        rw [rowLen₃, n₃]
        exact fun b h => ends_at_fk X N P (DK.at frS.P.T.a) B at_ R coll off₂ off₃ b h
      firstOn := fun rec y _ hc _ => firstOn_of first rec y hc
      firstClaim := fun rec y _ hc hL => by
        have h := firstClaim_of first rec y hL
        unfold Hiop.ConfigurationWithOutOfDomainSample.D
        rw [if_neg hc]
        exact Option.isSome_iff_ne_none.mp h }
  exact rowsOwed_woven S q₁ q₂
    (eachKeeps_of_at (fun n => match n with
      | 0 => H.r1_0
      | 1 => H.r1_1
      | 2 => H.r1_2
      | 3 => H.r1_3
      | 4 => H.r1_4
      | 5 => H.r1_5
      | 6 => H.r1_6
      | 7 => H.r1_7
      | 8 => H.r1_8
      | 9 => H.r1_9
      | 10 => H.r1_10
      | 11 => H.r1_11
      | 12 => H.r1_12
      | 13 => H.r1_13
      | 14 => H.r1_14
      | 15 => H.r1_15
      | 16 => H.r1_16
      | 17 => H.r1_17
      | 18 => H.r1_18
      | m + 19 => fun p hp => nomatch (rowNone₁ (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd (m + 19) (by omega)).symm.trans hp))
    (eachKeeps_of_at (fun n => match n with
      | 0 => H.r2_0
      | 1 => H.r2_1
      | 2 => H.r2_2
      | 3 => H.r2_3
      | 4 => H.r2_4
      | 5 => H.r2_5
      | 6 => H.r2_6
      | 7 => H.r2_7
      | 8 => H.r2_8
      | 9 => H.r2_9
      | 10 => H.r2_10
      | 11 => H.r2_11
      | m + 12 => fun p hp => nomatch (rowNone₂ (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd (m + 12) (by omega)).symm.trans hp))
    (eachKeeps_of_at (fun n => match n with
      | 0 => H.r3_0
      | 1 => H.r3_1
      | 2 => H.r3_2
      | 3 => H.r3_3
      | m + 4 => fun p hp => nomatch (rowNone₃ (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd (m + 4) (by omega)).symm.trans hp))

set_option maxHeartbeats 4000000 in
/-- **FROM THE 21 TO THE DEBT AT THE CAP, AT THE KEY FILE's OWN DESCRIPTION**: one chain of terms: `the35_of_21` · `rowsOwed_of_35`. -/
theorem keyDebtCap_of_21 [Inhabited Cells] [Inhabited M] (file : String) (ρ : RecFull → Rec) (cellsOf : (lettersAt A (relationsAndEncodingOfClaims A E)).conf.Msg → Cells)
    (H : The21 X N P DK c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd B at_ R enc rad coll off₂ off₃)
    (atFk : AtFk X B at_ R off₃)
    (first : FirstLetters (fr₁ (DK.at frS.P.T.a)) B.h₁ at_ (oneAt X) R coll VerifiableInference.Desc.Key.keyInstanceOfOutOfDomainSample (Fk X N P).start₁
      (fun y : (oneExternalString (2 ^ (DK.at frS.P.T.a).a) SgX).Str => ((y, fun _ => []) : (EAll (DK.at frS.P.T.a) (allOf (DK.at frS.P.T.a))).Str)) ρ
      (fun y r => (lettersAt A (relationsAndEncodingOfClaims A E)).conf.coll y r.1) (fun y r => (lettersAt A (relationsAndEncodingOfClaims A E)).conf.dcd y r) (lettersAt A (relationsAndEncodingOfClaims A E)).conf.held cellsOf)
    (q₁ : (Fk X N P).first.blocksInOrder = c₁ :: k₁) (q₂ : (Fk X N P).shared.blocksInOrder = c₂ :: k₂) (q₃ : (Fk X N P).second.blocksInOrder = c₃ :: k₃)
    (x₀ x₁ : Lookup) (hl : lookupsOf (oneAt X) = [x₀, x₁])
    (bw : Block FirstState Claim)
    (hw : sendW (oneAt X) pieces (rootsBefore X.Y.D.1 (batchRound X.Y.D.1))
      (groupsTold X.Y.told.1 (rootsBefore X.Y.D.1 (lastSendRound X.Y.D.1)) (rootsAt X.Y.D.1 (lastSendRound X.Y.D.1))) = some bw)
    (hin : (inFront₂ X P).length = 10)
    (hc : CellOnly coll) (hG : ReadsL B.h₁)
    (hb₁ : ∀ n p, ((atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).p₁ :: (atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).l₁)[n]? = some p → ∀ j ∈ pinned (open₁ 2 n), (at_ j).1 < p.base)
    (hb₂₀ : ∀ p, ((atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).p₂ :: (atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).l₂)[0]? = some p → ∀ j ∈ pinned seam, (at_ j).1 < p.base)
    (hb₂₁₁ : ∀ p, ((atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).p₂ :: (atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).l₂)[11]? = some p → ∀ j ∈ pinned end₂, (at_ j).1 < p.base)
    (hb₃₁ : ∀ p, ((atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).p₃ :: (atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).l₃)[1]? = some p → ∀ j ∈ pinned (open₃ 1), (at_ j).1 < p.base)
    (data : (Fk X N P).data file = .ok (DK.at frS.P.T.a))
    (a₁ : AtCap rest₁) (a₂ : AtCap rest₂) (a₃ : AtCap rest₃)
    (dS : ((Fk X N P).XiPub × (Fk X N P).S₁) × (EAll (DK.at frS.P.T.a) (allOf (DK.at frS.P.T.a))).Str) :
    KeyDebtCap (Fk X N P) VerifiableInference.Desc.Key.keyInstanceOfOutOfDomainSample A E DK file :=
  ⟨W, c₁, k₁, c₂, k₂, c₃, k₃, rest₁, rest₂, rest₃, dW, wEnd, dS, _, _, _, _, _, _, data, q₁, q₂, q₃,
    rowsOwed_of_35 X N P A E DK c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd B at_ R enc rad coll off₂ off₃ ρ cellsOf
      (the35_of_21 X N P DK c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd B at_ R enc rad coll off₂ off₃ H q₁ q₂ q₃ x₀ x₁ hl bw hw hin hc hG hb₁ hb₂₀ hb₂₁₁ hb₃₁)
      atFk first q₁ q₂ q₃ x₀ x₁ hl bw hw hin,
    a₁, a₂, a₃⟩

set_option maxHeartbeats 4000000 in
/-- **THE SAME AT THE PAYER's OWN ERRORS**, each piece's at most 2⁻¹ ^ 128: to `KeyDebt … (2⁻¹ ^ 128) …`, from which the ramp (KeyLeadsRamp.lean: `keyLeadsBelow_of_debt` · `keyLeadsCap_of_below`) goes on to the cap. -/
theorem keyDebt_of_21 [Inhabited Cells] [Inhabited M] (file : String) (ρ : RecFull → Rec) (cellsOf : (lettersAt A (relationsAndEncodingOfClaims A E)).conf.Msg → Cells)
    (H : The21 X N P DK c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd B at_ R enc rad coll off₂ off₃)
    (atFk : AtFk X B at_ R off₃)
    (first : FirstLetters (fr₁ (DK.at frS.P.T.a)) B.h₁ at_ (oneAt X) R coll VerifiableInference.Desc.Key.keyInstanceOfOutOfDomainSample (Fk X N P).start₁
      (fun y : (oneExternalString (2 ^ (DK.at frS.P.T.a).a) SgX).Str => ((y, fun _ => []) : (EAll (DK.at frS.P.T.a) (allOf (DK.at frS.P.T.a))).Str)) ρ
      (fun y r => (lettersAt A (relationsAndEncodingOfClaims A E)).conf.coll y r.1) (fun y r => (lettersAt A (relationsAndEncodingOfClaims A E)).conf.dcd y r) (lettersAt A (relationsAndEncodingOfClaims A E)).conf.held cellsOf)
    (q₁ : (Fk X N P).first.blocksInOrder = c₁ :: k₁) (q₂ : (Fk X N P).shared.blocksInOrder = c₂ :: k₂) (q₃ : (Fk X N P).second.blocksInOrder = c₃ :: k₃)
    (x₀ x₁ : Lookup) (hl : lookupsOf (oneAt X) = [x₀, x₁])
    (bw : Block FirstState Claim)
    (hw : sendW (oneAt X) pieces (rootsBefore X.Y.D.1 (batchRound X.Y.D.1))
      (groupsTold X.Y.told.1 (rootsBefore X.Y.D.1 (lastSendRound X.Y.D.1)) (rootsAt X.Y.D.1 (lastSendRound X.Y.D.1))) = some bw)
    (hin : (inFront₂ X P).length = 10)
    (hc : CellOnly coll) (hG : ReadsL B.h₁)
    (hb₁ : ∀ n p, ((atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).p₁ :: (atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).l₁)[n]? = some p → ∀ j ∈ pinned (open₁ 2 n), (at_ j).1 < p.base)
    (hb₂₀ : ∀ p, ((atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).p₂ :: (atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).l₂)[0]? = some p → ∀ j ∈ pinned seam, (at_ j).1 < p.base)
    (hb₂₁₁ : ∀ p, ((atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).p₂ :: (atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).l₂)[11]? = some p → ∀ j ∈ pinned end₂, (at_ j).1 < p.base)
    (hb₃₁ : ∀ p, ((atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).p₃ :: (atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).l₃)[1]? = some p → ∀ j ∈ pinned (open₃ 1), (at_ j).1 < p.base)
    (data : (Fk X N P).data file = .ok (DK.at frS.P.T.a)) (sealed : (Fk X N P).sealLast = true)
    (b₁ : EachBelow ((2 : ℝ≥0∞)⁻¹ ^ 128) ((atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).p₁ :: (atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).l₁)) (b₂ : EachBelow ((2 : ℝ≥0∞)⁻¹ ^ 128) ((atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).p₂ :: (atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).l₂)) (b₃ : EachBelow ((2 : ℝ≥0∞)⁻¹ ^ 128) ((atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).p₃ :: (atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).l₃))
    (dS : ((Fk X N P).XiPub × (Fk X N P).S₁) × (EAll (DK.at frS.P.T.a) (allOf (DK.at frS.P.T.a))).Str) :
    KeyDebt (Fk X N P) VerifiableInference.Desc.Key.keyInstanceOfOutOfDomainSample A E DK ((2 : ℝ≥0∞)⁻¹ ^ 128) file :=
  ⟨W, c₁, k₁, c₂, k₂, c₃, k₃, rest₁, rest₂, rest₃, dW, wEnd, dS, _, _, _, _, _, _, data, sealed, q₁, q₂, q₃,
    rowsOwed_of_35 X N P A E DK c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd B at_ R enc rad coll off₂ off₃ ρ cellsOf
      (the35_of_21 X N P DK c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd B at_ R enc rad coll off₂ off₃ H q₁ q₂ q₃ x₀ x₁ hl bw hw hin hc hG hb₁ hb₂₀ hb₂₁₁ hb₃₁)
      atFk first q₁ q₂ q₃ x₀ x₁ hl bw hw hin,
    b₁, b₂, b₃⟩

end

end LPFD

#print axioms LPFD.keyDebt_of_21
#print axioms LPFD.keyDebtCap_of_21
#print axioms LPFD.The35
#print axioms LPFD.The21
#print axioms LPFD.the35_of_21
#print axioms LPFD.rowsOwed_of_35
