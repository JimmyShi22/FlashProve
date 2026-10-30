-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Top/Fire/Code/TheRest.lean: THE KEY FILE's DEBT, WITH THE ROWS THAT ARE LAID IN AS A LIST: so that each new row is one line, not a new structure.
Main names.
  `Row`: the 21 rows of `The21` (The35.lean), by their fields' names.
  `lawAt … r`: row r's law: EACH TEXT TAKEN FROM `The21`'s FIELD BY PROGRAM, sign for sign; at the same letters.
  `the21_iff`: `The21 … ↔ ∀ r, lawAt … r`: nothing is lost or added.
  `TheRest … paid`: the laws of the rows that are NOT in the list `paid`.
  `the21_of_rest`: the rest, and the laws of the rows in the list, give `The21` · `rest_nil`: at the empty list the rest is all 21 · `rest_mono`: a longer list owes less.
OBJECT: `The21` · USER: KeyAtRest.lean · LETTERS: all of `The21`'s, and the list.
Limits. A re-cut of a structure. NO LAW IS PAID HERE. A list with every row in it owes nothing: the worth lies in who pays the listed rows. Nothing on soundness.

-/
import Johnson.Top.Fire.Code.The35

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 40000

noncomputable section

open scoped ENNReal

namespace LPFD
open scoped ENNReal
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

/-- The 21 rows, by `The21`'s fields' names. -/
inductive Row where
  | r1_0
  | r1_1
  | r1_4
  | r1_5
  | r1_10
  | r1_11
  | r1_15
  | r1_16
  | r1_17
  | r2_1
  | r2_2
  | r2_3
  | r2_4
  | r2_5
  | r2_6
  | r2_7
  | r2_8
  | r2_9
  | r2_10
  | r3_0
  | r3_2
  deriving DecidableEq, Repr

/-- All of them, in `The21`'s order. -/
def Row.all : List Row := [.r1_0, .r1_1, .r1_4, .r1_5, .r1_10, .r1_11, .r1_15, .r1_16, .r1_17, .r2_1, .r2_2, .r2_3, .r2_4, .r2_5, .r2_6, .r2_7, .r2_8, .r2_9, .r2_10, .r3_0, .r3_2]

theorem Row.mem_all (r : Row) : r ∈ Row.all := by cases r <;> decide

section
variable {Cells M Smp Rec : Type} (X : Source) (N : H2U.PlaceNums) (P : LaterPlaces)
    (DK : WholeD) {W : Type}
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


/-- **Row r's law.** -/
def lawAt : Row → Prop
  | .r1_0 => KeepsAt (On₁' X N P (DK.at frS.P.T.a) B at_ R coll) (Cl₁ X N P (DK.at frS.P.T.a) B at_ R) ((atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).p₁ :: (atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).l₁) 0
  | .r1_1 => KeepsAt (On₁' X N P (DK.at frS.P.T.a) B at_ R coll) (Cl₁ X N P (DK.at frS.P.T.a) B at_ R) ((atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).p₁ :: (atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).l₁) 1
  | .r1_4 => KeepsAt (On₁' X N P (DK.at frS.P.T.a) B at_ R coll) (Cl₁ X N P (DK.at frS.P.T.a) B at_ R) ((atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).p₁ :: (atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).l₁) 4
  | .r1_5 => KeepsAt (On₁' X N P (DK.at frS.P.T.a) B at_ R coll) (Cl₁ X N P (DK.at frS.P.T.a) B at_ R) ((atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).p₁ :: (atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).l₁) 5
  | .r1_10 => KeepsAt (On₁' X N P (DK.at frS.P.T.a) B at_ R coll) (Cl₁ X N P (DK.at frS.P.T.a) B at_ R) ((atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).p₁ :: (atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).l₁) 10
  | .r1_11 => KeepsAt (On₁' X N P (DK.at frS.P.T.a) B at_ R coll) (Cl₁ X N P (DK.at frS.P.T.a) B at_ R) ((atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).p₁ :: (atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).l₁) 11
  | .r1_15 => KeepsAt (On₁' X N P (DK.at frS.P.T.a) B at_ R coll) (Cl₁ X N P (DK.at frS.P.T.a) B at_ R) ((atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).p₁ :: (atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).l₁) 15
  | .r1_16 => KeepsAt (On₁' X N P (DK.at frS.P.T.a) B at_ R coll) (Cl₁ X N P (DK.at frS.P.T.a) B at_ R) ((atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).p₁ :: (atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).l₁) 16
  | .r1_17 => KeepsAt (On₁' X N P (DK.at frS.P.T.a) B at_ R coll) (Cl₁ X N P (DK.at frS.P.T.a) B at_ R) ((atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).p₁ :: (atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).l₁) 17
  | .r2_1 => KeepsAt (On₂' X N P (DK.at frS.P.T.a) B at_ R enc rad coll off₂) (Cl₂ X N P (DK.at frS.P.T.a) B at_ R enc rad) ((atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).p₂ :: (atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).l₂) 1
  | .r2_2 => KeepsAt (On₂' X N P (DK.at frS.P.T.a) B at_ R enc rad coll off₂) (Cl₂ X N P (DK.at frS.P.T.a) B at_ R enc rad) ((atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).p₂ :: (atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).l₂) 2
  | .r2_3 => KeepsAt (On₂' X N P (DK.at frS.P.T.a) B at_ R enc rad coll off₂) (Cl₂ X N P (DK.at frS.P.T.a) B at_ R enc rad) ((atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).p₂ :: (atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).l₂) 3
  | .r2_4 => KeepsAt (On₂' X N P (DK.at frS.P.T.a) B at_ R enc rad coll off₂) (Cl₂ X N P (DK.at frS.P.T.a) B at_ R enc rad) ((atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).p₂ :: (atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).l₂) 4
  | .r2_5 => KeepsAt (On₂' X N P (DK.at frS.P.T.a) B at_ R enc rad coll off₂) (Cl₂ X N P (DK.at frS.P.T.a) B at_ R enc rad) ((atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).p₂ :: (atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).l₂) 5
  | .r2_6 => KeepsAt (On₂' X N P (DK.at frS.P.T.a) B at_ R enc rad coll off₂) (Cl₂ X N P (DK.at frS.P.T.a) B at_ R enc rad) ((atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).p₂ :: (atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).l₂) 6
  | .r2_7 => KeepsAt (On₂' X N P (DK.at frS.P.T.a) B at_ R enc rad coll off₂) (Cl₂ X N P (DK.at frS.P.T.a) B at_ R enc rad) ((atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).p₂ :: (atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).l₂) 7
  | .r2_8 => KeepsAt (On₂' X N P (DK.at frS.P.T.a) B at_ R enc rad coll off₂) (Cl₂ X N P (DK.at frS.P.T.a) B at_ R enc rad) ((atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).p₂ :: (atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).l₂) 8
  | .r2_9 => KeepsAt (On₂' X N P (DK.at frS.P.T.a) B at_ R enc rad coll off₂) (Cl₂ X N P (DK.at frS.P.T.a) B at_ R enc rad) ((atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).p₂ :: (atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).l₂) 9
  | .r2_10 => KeepsAt (On₂' X N P (DK.at frS.P.T.a) B at_ R enc rad coll off₂) (Cl₂ X N P (DK.at frS.P.T.a) B at_ R enc rad) ((atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).p₂ :: (atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).l₂) 10
  | .r3_0 => KeepsAt (On₃' X N P (DK.at frS.P.T.a) B at_ R coll off₂ off₃) (Cl₃ X N P (DK.at frS.P.T.a) B at_ R) ((atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).p₃ :: (atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).l₃) 0
  | .r3_2 => KeepsAt (On₃' X N P (DK.at frS.P.T.a) B at_ R coll off₂ off₃) (Cl₃ X N P (DK.at frS.P.T.a) B at_ R) ((atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).p₃ :: (atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).l₃) 2

/-- **The 21 are these, row by row.** -/
theorem the21_iff : The21 X N P DK c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd B at_ R enc rad coll off₂ off₃ ↔
    ∀ r, lawAt X N P DK c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd B at_ R enc rad coll off₂ off₃ r :=
  ⟨fun H r => by
    cases r
    · exact H.r1_0
    · exact H.r1_1
    · exact H.r1_4
    · exact H.r1_5
    · exact H.r1_10
    · exact H.r1_11
    · exact H.r1_15
    · exact H.r1_16
    · exact H.r1_17
    · exact H.r2_1
    · exact H.r2_2
    · exact H.r2_3
    · exact H.r2_4
    · exact H.r2_5
    · exact H.r2_6
    · exact H.r2_7
    · exact H.r2_8
    · exact H.r2_9
    · exact H.r2_10
    · exact H.r3_0
    · exact H.r3_2,
   fun h => { r1_0 := h .r1_0, r1_1 := h .r1_1, r1_4 := h .r1_4, r1_5 := h .r1_5, r1_10 := h .r1_10, r1_11 := h .r1_11, r1_15 := h .r1_15, r1_16 := h .r1_16, r1_17 := h .r1_17, r2_1 := h .r2_1, r2_2 := h .r2_2, r2_3 := h .r2_3, r2_4 := h .r2_4, r2_5 := h .r2_5, r2_6 := h .r2_6, r2_7 := h .r2_7, r2_8 := h .r2_8, r2_9 := h .r2_9, r2_10 := h .r2_10, r3_0 := h .r3_0, r3_2 := h .r3_2 }⟩

/-- **What is owed when the rows of the list are laid in.** -/
def TheRest (paid : List Row) : Prop :=
  ∀ r, r ∉ paid → lawAt X N P DK c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd B at_ R enc rad coll off₂ off₃ r

variable {X N P DK c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd B at_ R enc rad coll off₂ off₃}

/-- **The rest, and the laws of the rows in the list, give the 21.** -/
theorem the21_of_rest (paid : List Row)
    (hp : ∀ r ∈ paid, lawAt X N P DK c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd B at_ R enc rad coll off₂ off₃ r)
    (h : TheRest X N P DK c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd B at_ R enc rad coll off₂ off₃ paid) :
    The21 X N P DK c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd B at_ R enc rad coll off₂ off₃ :=
  (the21_iff X N P DK c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd B at_ R enc rad coll off₂ off₃).2 fun r =>
    if hr : r ∈ paid then hp r hr else h r hr

/-- At the empty list the rest is all 21. -/
theorem rest_nil : TheRest X N P DK c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd B at_ R enc rad coll off₂ off₃ [] ↔
    The21 X N P DK c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd B at_ R enc rad coll off₂ off₃ :=
  ⟨fun h => the21_of_rest [] (fun _ hr => nomatch hr) h,
   fun H r _ => (the21_iff X N P DK c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd B at_ R enc rad coll off₂ off₃).1 H r⟩

/-- A longer list owes less. -/
theorem rest_mono {paid paid' : List Row} (hs : paid ⊆ paid')
    (h : TheRest X N P DK c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd B at_ R enc rad coll off₂ off₃ paid) :
    TheRest X N P DK c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd B at_ R enc rad coll off₂ off₃ paid' :=
  fun r hr => h r fun hr' => hr (hs hr')

end

end LPFD

#print axioms LPFD.Row.mem_all
#print axioms LPFD.lawAt
#print axioms LPFD.the21_iff
#print axioms LPFD.TheRest
#print axioms LPFD.the21_of_rest
#print axioms LPFD.rest_nil
#print axioms LPFD.rest_mono
