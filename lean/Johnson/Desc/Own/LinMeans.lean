--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Own/LinMeans.lean: WHAT EACH TEST OF Johnson/Desc/Own/Lin.lean CHECKS, AS A STATEMENT
IN Prop, PROVED AGAINST ITS TEXT. Theorems. No block imports this file.

WHAT THESE STATEMENTS ARE, SAID PLAINLY: THE BOOLEAN TEXTS SPELT AGAIN IN Prop, CONNECTIVE FOR
CONNECTIVE. They are true and proved, and but for twoPower_exp and the two on room they add no
meaning that the text did not show: a bound is a bound. They are the tie for whoever spends a
clause.

  TwoPower n · twoPower_iff · twoPower_exp (a yes gives an exponent a with n = 2 ^ a)
  lengthsFit_iff · ShapeSound · shapeSound_iff · CodeFits · codeFits_iff · IndexFits ·
  indexFits_iff · FoldShapeFits · foldeqShapeFits_iff · FoldFits · foldFits_iff · SplitMessageFits ·
  splitMessageFits_iff · VectorMessageFits · vectorMessageFits_iff · LinShapeFits ·
  linShapeFits_iff · LinFits · linFits_iff
  TWO THAT SAY MORE THAN THE TEXT, out of Johnson/Desc/Own/RoomMeans.lean's le_roomOf:
  omega_has_room · w_has_room: linFits' yes gives: o_omega (W) can hold a vector in its layout
  (roomCan), the matrix's rows (2 ^ kCol entries) are at most the places of its real rows, and no
  place of its sample's pad in the main table is among them.
What is not claimed. That these statements are what the protocol needs: whether the tests ask enough
is not said here. Fmt.saltLenOK, the format's, is left as it is. Nothing on soundness.

-/
import Johnson.Desc.Own.Lin
import Johnson.Desc.Own.RoomMeans

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Own
open OnBytes OnBytes.Params

/-- n is not 0, and is 2 to the least exponent that reaches it. -/
def TwoPower (n : Nat) : Prop := n ≠ 0 ∧ 2 ^ ceilLog2 n = n

theorem twoPower_iff (n : Nat) : twoPower n = true ↔ TwoPower n := by
  unfold twoPower TwoPower
  simp only [Bool.and_eq_true, bne_iff_ne, beq_iff_eq]

theorem twoPower_exp (n : Nat) (h : twoPower n = true) : ∃ a, n = 2 ^ a :=
  ⟨ceilLog2 n, ((twoPower_iff n).1 h).2.symm⟩

theorem lengthsFit_iff (c : Codes) : lengthsFit c = true ↔
    (∀ x ∈ c.base, TwoPower x.ell) ∧ ∀ x ∈ c.mask, TwoPower x.ell := by
  unfold lengthsFit
  simp only [Bool.and_eq_true, Array.all_eq_true_iff_forall_mem, twoPower_iff]

/-- It has rows; it names a code for the rows that it has; its main rows are over one of the two
fields. -/
def ShapeSound (s : OracleShape) : Prop :=
  (s.mainRows ≠ 0 ∨ s.maskRows ≠ 0) ∧ (s.mainRows = 0 ∨ s.code ≠ noId) ∧
    (s.maskRows = 0 ∨ s.maskCode ≠ noId) ∧ (s.mainRows = 0 ∨ s.mainDeg = 1 ∨ s.mainDeg = 3)

theorem shapeSound_iff (s : OracleShape) : shapeSound s = true ↔ ShapeSound s := by
  unfold shapeSound ShapeSound
  simp only [Bool.and_eq_true, Bool.not_eq_true', Bool.and_eq_false_iff, beq_eq_false_iff_ne,
    bne_eq_false_iff_eq, and_assoc, or_assoc]

/-- Three numbers describe a code. -/
def CodeFits (c : Code) : Prop :=
  1 ≤ c.logN ∧ c.logN ≤ mostLogN ∧ 1 ≤ c.ell ∧ c.ell ≤ 2 ^ c.logN ∧ c.r ≤ 2 ^ c.logN ∧
    c.dim ≤ 2 ^ c.logN ∧ c.dim ≤ 2 ^ min c.logN 32

theorem codeFits_iff (c : Code) : codeFits c = true ↔ CodeFits c := by
  unfold codeFits CodeFits
  simp only [Bool.and_eq_true, decide_eq_true_eq, and_assoc]

/-- A stored table's shape. -/
def IndexFits (s : IndexShape) : Prop :=
  CodeFits s.code ∧ s.v ≤ 40 ∧ s.pads < s.code.ell ∧ Fmt.saltLenOK s.saltBytes = true

theorem indexFits_iff (s : IndexShape) : indexFits s = true ↔ IndexFits s := by
  unfold indexFits IndexFits
  simp only [Bool.and_eq_true, decide_eq_true_eq, codeFits_iff, and_assoc]

/-- The fold's shape by itself. -/
def FoldShapeFits (S : FoldeqShape) : Prop :=
  IndexFits S.index ∧ ShapeSound S.u ∧ 0 < S.u.mainRows ∧ S.u.mainDeg = 3 ∧ 1 ≤ S.u.answers ∧
    1 ≤ S.columns

theorem foldeqShapeFits_iff (S : FoldeqShape) : foldeqShapeFits S = true ↔ FoldShapeFits S := by
  unfold foldeqShapeFits FoldShapeFits
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, indexFits_iff, shapeSound_iff,
    and_assoc]

/-- The fold's shape with the codes that it names. -/
def FoldFits (codes : Codes) (S : FoldeqShape) : Prop :=
  FoldShapeFits S ∧ S.u.code < codes.base.size ∧ S.entries ≤ roomOf codes S.u S.rowsHigh

theorem foldFits_iff (codes : Codes) (S : FoldeqShape) :
    foldFits codes S = true ↔ FoldFits codes S := by
  unfold foldFits FoldFits
  simp only [Bool.and_eq_true, decide_eq_true_eq, foldeqShapeFits_iff, and_assoc]

/-- A split's message: mask rows alone, sampled, under that mask code. -/
def SplitMessageFits (o : OracleShape) (maskCode : Nat) : Prop :=
  o.mainRows = 0 ∧ o.maskRows ≠ 0 ∧ 1 ≤ o.answers ∧ o.maskCode = maskCode

theorem splitMessageFits_iff (o : OracleShape) (maskCode : Nat) :
    splitMessageFits o maskCode = true ↔ SplitMessageFits o maskCode := by
  unfold splitMessageFits SplitMessageFits
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, bne_iff_ne, and_assoc]

/-- o_omega or W: sound; main rows over the large field; sampled. -/
def VectorMessageFits (o : OracleShape) : Prop :=
  ShapeSound o ∧ o.mainRows ≠ 0 ∧ o.mainDeg = 3 ∧ 1 ≤ o.answers

theorem vectorMessageFits_iff (o : OracleShape) :
    vectorMessageFits o = true ↔ VectorMessageFits o := by
  unfold vectorMessageFits VectorMessageFits
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, bne_iff_ne, shapeSound_iff,
    and_assoc]

/-- The linear part's shape by itself: fifteen clauses. -/
def LinShapeFits (S : LinShape) : Prop :=
  FoldShapeFits S.fold ∧ 1 ≤ S.matrixRows ∧ S.kLo ≤ 30 ∧ S.kRow ≤ 30 ∧ S.kCol ≤ 60 ∧
  S.matrixRows * 2 ^ S.kLo ≤ S.fold.index.plain ∧
  VectorMessageFits S.omega ∧ VectorMessageFits S.w ∧
  (S.fold.u.maskRows = 0 ∨ S.fold.u.maskCode = S.sharedMaskCode) ∧
  (S.w.maskRows = 0 ∨ S.w.maskCode = S.ownMaskCode) ∧
  S.omega.maskRows = 0 ∧
  (S.sharedSplitNeeded = false ∨ S.omegaLeafClass ≠ S.sharedSplitLeafClass) ∧
  (S.ownSplitNeeded = false ∨ S.wLeafClass ≠ S.ownSplitLeafClass) ∧
  (S.sharedSplitNeeded = false ∨ SplitMessageFits S.sharedSplit S.sharedMaskCode) ∧
  (S.ownSplitNeeded = false ∨ SplitMessageFits S.ownSplit S.ownMaskCode)

theorem linShapeFits_iff (S : LinShape) : linShapeFits S = true ↔ LinShapeFits S := by
  unfold linShapeFits LinShapeFits
  simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true', decide_eq_true_eq, beq_iff_eq,
    bne_iff_ne, foldeqShapeFits_iff, vectorMessageFits_iff, splitMessageFits_iff, and_assoc]

/-- The linear part's shape with the codes that it names. -/
def LinFits (codes : Codes) (S : LinShape) : Prop :=
  LinShapeFits S ∧ FoldFits codes S.fold ∧ S.omega.code < codes.base.size ∧
  S.w.code < codes.base.size ∧ S.sharedMaskCode < codes.mask.size ∧
  S.ownMaskCode < codes.mask.size ∧ S.matrixRows ≤ roomOf codes S.omega S.omegaRowsHigh ∧
  2 ^ S.kCol ≤ roomOf codes S.w S.wRowsHigh

theorem linFits_iff (codes : Codes) (S : LinShape) : linFits codes S = true ↔ LinFits codes S := by
  unfold linFits LinFits
  simp only [Bool.and_eq_true, decide_eq_true_eq, linShapeFits_iff, foldFits_iff, and_assoc]

/-- linFits' yes: the matrix's rows have room in o_omega, in words of places. -/
theorem omega_has_room (codes : Codes) (S : LinShape) (h : linFits codes S = true) :
    roomCan codes S.omega S.omegaRowsHigh = true ∧
    S.matrixRows ≤ S.omega.mainRows * 2 ^ (vectorLay codes S.omega S.omegaRowsHigh).placeBits ∧
    ∀ p ∈ (if S.omega.answers == 0 then [] else (padMade codes S.omega).getD []),
      p.part = .main →
        S.matrixRows ≤ (vectorLay codes S.omega S.omegaRowsHigh).entryAt p.index := by
  obtain ⟨hs, _, _, _, _, _, hr, _⟩ := (linFits_iff codes S).1 h
  exact (le_roomOf codes S.omega S.omegaRowsHigh S.matrixRows hs.2.1).1 hr

/-- linFits' yes: 2 ^ kCol entries have room in W, in words of places. -/
theorem w_has_room (codes : Codes) (S : LinShape) (h : linFits codes S = true) :
    roomCan codes S.w S.wRowsHigh = true ∧
    2 ^ S.kCol ≤ S.w.mainRows * 2 ^ (vectorLay codes S.w S.wRowsHigh).placeBits ∧
    ∀ p ∈ (if S.w.answers == 0 then [] else (padMade codes S.w).getD []),
      p.part = .main → 2 ^ S.kCol ≤ (vectorLay codes S.w S.wRowsHigh).entryAt p.index := by
  obtain ⟨_, _, _, _, _, _, _, hr⟩ := (linFits_iff codes S).1 h
  exact (le_roomOf codes S.w S.wRowsHigh (2 ^ S.kCol) (Nat.pow_pos (by decide))).1 hr

end VerifiableInference.Desc.Own
