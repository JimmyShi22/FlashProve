-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Top/Fire/Code/BasesOk.lean, adapted by a program of this project that is not in this repository: at the full size: AT THE KEY FILE's OWN DESCRIPTION: «THE PINNED TREES LIE BELOW THE PIECES' BASES» AS ONE TEST WITH CODE: four of the premises that stand beside the 21 laws (The35.lean: hb₁ · hb₂₀ · hb₂₁₁ · hb₃₁) become one evaluation.
Main names.
  `basesOk at_ F D`: a Bool: at every border n of the first chain every message whose pin is open there has its tree's number below the n-th piece's base · at the shared chain's front those of the first seam's open pins lie below the chain's first tree `D.t₁` · at its end (piece 11) those open behind it · at the last chain's piece 1 those open there. The bases are `baseOf` (RowBase.lean): computed off the description's blocks' declared rounds and the data's trees.
  `basesOk_eq`: IT IS THE TEST ON NUMBERS ALONE `basesOkN` (BaseNums.lean, a light file that can be evaluated in any build) at the description's blocks' numbers of declared rounds and our tables' lists of open pins.
  `basesAll` · `basesAll_eq` · `bases_of_all` · `four_of_all`: THE SAME AT EVERY BORDER OF THE THREE CHAINS (19 · 12 · 4): a ride of the first test showed that it is not tight at the messages that the shared chain sends (it asked that chain's pins at two borders alone): the wide test's yes gives the premise at every piece, and so the four.
  `seatsApart_of_arrOk`: the tables' tie `ArrOk G at_ l` gives the public test `seatsApartN at_ l` (BaseNums.lean): WHAT REFUSES «message 4's seat one tree higher» (that is message 5's seat; one block sends both trees, so the bases cannot part them).
  `bases_of_ok`: **ITS YES, WITH THE THREE HEADS, GIVES THE FOUR PREMISES**, in `the35_of_21`'s own words.
THE CONTROL, FOR WHOEVER EVALUATES: `at_` turned at one open message to a tree that is sent later (its number + the file's number of trees): the test must say no; and at the honest `at_` with the tightest pin's tree + 1.
Limits. That it says yes at the release's data and our tables' `at_` IS NOT SHOWN HERE: it is to be evaluated. It reads `at_`, a letter of the tables. Nothing on soundness.

-/
import Johnson.Top.Fire.Code.The35
import Johnson.Top.Fire.Code.RowBase
import Johnson.Top.Fire.Code.BaseNums

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 40000

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
open Johnson.RunOne.KeyRows23 (CellOnly inFront₂ front₂ seat open₂ open₃)

/-- **The pinned trees lie below the pieces' bases: a test with code.** -/
def basesOk {XI : Type} (at_ : Where) (F : FileDescription XI) (D : WholeD) : Bool :=
  ((List.range F.first.blocksInOrder.length).all fun n => (pinned (open₁ 2 n)).all fun j => decide ((at_ j).1 < baseOf 0 D.ds₁ F.first.blocksInOrder n)) &&
  ((pinned seam).all fun j => decide ((at_ j).1 < baseOf D.t₁ D.ds₂ F.shared.blocksInOrder 0)) &&
  ((pinned end₂).all fun j => decide ((at_ j).1 < baseOf D.t₁ D.ds₂ F.shared.blocksInOrder 11)) &&
  ((pinned (open₃ 1)).all fun j => decide ((at_ j).1 < baseOf (D.t₁ + D.t₂) D.ds₃ F.second.blocksInOrder 1))

/-- The bases off the blocks are the bases off their numbers of declared rounds. -/
theorem cutBase_eq_baseN {S Cl : Type} : ∀ (l : List (Block S Cl)) (n base : ℕ) (ds : List RDT) (b : Block S Cl),
    cutBase base ds b l n = baseN base ds ((b :: l).map (·.rounds.length)) n
  | [], 0, _, _, _ => rfl
  | [], _ + 1, _, _, _ => rfl
  | _ :: _, 0, _, _, _ => rfl
  | c :: l, n + 1, base, ds, b => cutBase_eq_baseN l n (base + nTrees (ds.take b.rounds.length)) (ds.drop b.rounds.length) c

theorem baseOf_eq_baseN {S Cl : Type} (base : ℕ) (ds : List RDT) : ∀ (bs : List (Block S Cl)) (n : ℕ),
    baseOf base ds bs n = baseN base ds (bs.map (·.rounds.length)) n
  | [], 0 => rfl
  | [], _ + 1 => rfl
  | b :: l, n => cutBase_eq_baseN l n base ds b

/-- **The test at a description IS the test on numbers**, at its blocks' numbers of declared rounds and our tables' lists of open pins. -/
theorem basesOk_eq {XI : Type} (at_ : Where) (F : FileDescription XI) (D : WholeD) :
    basesOk at_ F D = basesOkN at_ (fun n => pinned (open₁ 2 n)) (pinned seam) (pinned end₂) (pinned (open₃ 1))
      (F.first.blocksInOrder.map (·.rounds.length)) (F.shared.blocksInOrder.map (·.rounds.length)) (F.second.blocksInOrder.map (·.rounds.length)) D := by
  unfold basesOk basesOkN
  simp only [baseOf_eq_baseN, List.length_map]

/-- **The pinned trees lie below the pieces' bases, AT EVERY BORDER OF THE THREE CHAINS.** -/
def basesAll {XI : Type} (at_ : Where) (F : FileDescription XI) (D : WholeD) : Bool :=
  ((List.range F.first.blocksInOrder.length).all fun n => (pinned (open₁ 2 n)).all fun j => decide ((at_ j).1 < baseOf 0 D.ds₁ F.first.blocksInOrder n)) &&
  ((List.range F.shared.blocksInOrder.length).all fun n => (pinned (open₂ n)).all fun j => decide ((at_ j).1 < baseOf D.t₁ D.ds₂ F.shared.blocksInOrder n)) &&
  ((List.range F.second.blocksInOrder.length).all fun n => (pinned (open₃ n)).all fun j => decide ((at_ j).1 < baseOf (D.t₁ + D.t₂) D.ds₃ F.second.blocksInOrder n))

theorem basesAll_eq {XI : Type} (at_ : Where) (F : FileDescription XI) (D : WholeD) :
    basesAll at_ F D = basesAllN at_ (fun n => pinned (open₁ 2 n)) (fun n => pinned (open₂ n)) (fun n => pinned (open₃ n))
      (F.first.blocksInOrder.map (·.rounds.length)) (F.shared.blocksInOrder.map (·.rounds.length)) (F.second.blocksInOrder.map (·.rounds.length)) D := by
  unfold basesAll basesAllN
  simp only [baseOf_eq_baseN, List.length_map]

/-- **The tables' tie «the seat at_ k is message k's» keeps the seats apart**: so where the test says no, no reading letter meets the tie. -/
theorem seatsApart_of_arrOk {A Cells M Smp Rec : Type} (G : Reading A Cells M Smp Rec) (at_ : Where) (l : List ℕ) (hl : l.Nodup)
    (h : ArrOk G at_ l) : seatsApartN at_ l = true := by
  unfold seatsApartN
  refine decide_eq_true (List.Nodup.map_on (fun x hx y hy e => ?_) hl)
  rw [← h x hx, ← h y hy, e]

/-- What is open in front of the shared chain's first block is the first seam's list; in front of its last block the pins are those behind it. -/
theorem open₂_zero : open₂ 0 = seam := rfl
theorem pinned_open₂_last : pinned (open₂ 11) = pinned end₂ := by decide

section
variable (X : Source) (N : H2U.PlaceNums) (P : LaterPlaces)
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
    (at_ : Where)

/-- **Its yes gives the four.** -/
theorem bases_of_ok (h : basesOk at_ (Fk X N P) (DK.at frS.P.T.a) = true)
    (q₁ : (Fk X N P).first.blocksInOrder = c₁ :: k₁) (q₂ : (Fk X N P).shared.blocksInOrder = c₂ :: k₂) (q₃ : (Fk X N P).second.blocksInOrder = c₃ :: k₃) :
    (∀ n p, ((atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).p₁ :: (atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).l₁)[n]? = some p → ∀ j ∈ pinned (open₁ 2 n), (at_ j).1 < p.base) ∧
    (∀ p, ((atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).p₂ :: (atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).l₂)[0]? = some p → ∀ j ∈ pinned seam, (at_ j).1 < p.base) ∧
    (∀ p, ((atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).p₂ :: (atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).l₂)[11]? = some p → ∀ j ∈ pinned end₂, (at_ j).1 < p.base) ∧
    (∀ p, ((atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).p₃ :: (atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).l₃)[1]? = some p → ∀ j ∈ pinned (open₃ 1), (at_ j).1 < p.base) := by
  unfold basesOk at h
  simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, List.mem_range] at h
  obtain ⟨⟨⟨h₁, h₂⟩, h₃⟩, h₄⟩ := h
  refine ⟨fun n p hp j hj => ?_, fun p hp j hj => ?_, fun p hp j hj => ?_, fun p hp j hj => ?_⟩
  · rw [base_at₁ (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd q₁ n p hp]
    refine h₁ n ?_ j hj
    have hn : n < ((atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).p₁ :: (atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).l₁).length := (List.getElem?_eq_some_iff.1 hp).1
    rw [List.length_cons, rowLen₁] at hn
    rw [q₁, List.length_cons]
    exact hn
  · rw [base_at₂ (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd q₂ 0 p hp]
    exact h₂ j hj
  · rw [base_at₂ (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd q₂ 11 p hp]
    exact h₃ j hj
  · rw [base_at₃ (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd q₃ 1 p hp]
    exact h₄ j hj

/-- **Its yes gives the premise at every piece of the three rows.** -/
theorem bases_of_all (h : basesAll at_ (Fk X N P) (DK.at frS.P.T.a) = true)
    (q₁ : (Fk X N P).first.blocksInOrder = c₁ :: k₁) (q₂ : (Fk X N P).shared.blocksInOrder = c₂ :: k₂) (q₃ : (Fk X N P).second.blocksInOrder = c₃ :: k₃) :
    (∀ n p, ((atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).p₁ :: (atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).l₁)[n]? = some p → ∀ j ∈ pinned (open₁ 2 n), (at_ j).1 < p.base) ∧
    (∀ n p, ((atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).p₂ :: (atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).l₂)[n]? = some p → ∀ j ∈ pinned (open₂ n), (at_ j).1 < p.base) ∧
    (∀ n p, ((atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).p₃ :: (atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).l₃)[n]? = some p → ∀ j ∈ pinned (open₃ n), (at_ j).1 < p.base) := by
  unfold basesAll at h
  simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, List.mem_range] at h
  obtain ⟨⟨h₁, h₂⟩, h₃⟩ := h
  refine ⟨fun n p hp j hj => ?_, fun n p hp j hj => ?_, fun n p hp j hj => ?_⟩
  · rw [base_at₁ (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd q₁ n p hp]
    refine h₁ n ?_ j hj
    have hn : n < ((atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).p₁ :: (atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).l₁).length := (List.getElem?_eq_some_iff.1 hp).1
    rw [List.length_cons, rowLen₁] at hn
    rw [q₁, List.length_cons]
    exact hn
  · rw [base_at₂ (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd q₂ n p hp]
    refine h₂ n ?_ j hj
    have hn : n < ((atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).p₂ :: (atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).l₂).length := (List.getElem?_eq_some_iff.1 hp).1
    rw [List.length_cons, rowLen₂] at hn
    rw [q₂, List.length_cons]
    exact hn
  · rw [base_at₃ (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd q₃ n p hp]
    refine h₃ n ?_ j hj
    have hn : n < ((atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).p₃ :: (atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).l₃).length := (List.getElem?_eq_some_iff.1 hp).1
    rw [List.length_cons, rowLen₃] at hn
    rw [q₃, List.length_cons]
    exact hn

/-- **So the four premises of `the35_of_21`.** -/
theorem four_of_all (h : basesAll at_ (Fk X N P) (DK.at frS.P.T.a) = true)
    (q₁ : (Fk X N P).first.blocksInOrder = c₁ :: k₁) (q₂ : (Fk X N P).shared.blocksInOrder = c₂ :: k₂) (q₃ : (Fk X N P).second.blocksInOrder = c₃ :: k₃) :
    (∀ n p, ((atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).p₁ :: (atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).l₁)[n]? = some p → ∀ j ∈ pinned (open₁ 2 n), (at_ j).1 < p.base) ∧
    (∀ p, ((atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).p₂ :: (atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).l₂)[0]? = some p → ∀ j ∈ pinned seam, (at_ j).1 < p.base) ∧
    (∀ p, ((atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).p₂ :: (atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).l₂)[11]? = some p → ∀ j ∈ pinned end₂, (at_ j).1 < p.base) ∧
    (∀ p, ((atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).p₃ :: (atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).l₃)[1]? = some p → ∀ j ∈ pinned (open₃ 1), (at_ j).1 < p.base) := by
  obtain ⟨a₁, a₂, a₃⟩ := bases_of_all X N P DK c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd at_ h q₁ q₂ q₃
  exact ⟨a₁, fun p hp j hj => a₂ 0 p hp j (open₂_zero ▸ hj), fun p hp j hj => a₂ 11 p hp j (pinned_open₂_last ▸ hj), fun p hp => a₃ 1 p hp⟩

end

end LPFD

#print axioms LPFD.seatsApart_of_arrOk
#print axioms LPFD.basesAll
#print axioms LPFD.basesAll_eq
#print axioms LPFD.bases_of_all
#print axioms LPFD.four_of_all
#print axioms LPFD.basesOk
#print axioms LPFD.basesOk_eq
#print axioms LPFD.bases_of_ok
