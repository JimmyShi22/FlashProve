-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K12/Part4/PiecesOfAMember.lean: A PROXIMITY TEST ON A GROUP OF SEVERAL
MEMBERS (the kind K12): a stretch of a tree's column, as the test's job reads it off the first
stage's tables, is the list of the written symbols of ONE MEMBER's OWN ROWS. General in the number
of members and in which member it is.

WHAT IT IS NOT.
  * It says nothing of who sent the rows, of coins, of a book, of a run or of a thread. A member's
    rows are four lists of lists of words here, and nothing ties them to a sender's.
  * That the member's block lies within the stage's table, and that no earlier member's block covers
    one of its rows, are premises. They are public; they are shown at no place here.
  * That the state's tables are read off the stage's lists is a premise (two equations for each
    piece).
  * It is no statement on a tree's depth.
  * Nothing on completeness, soundness or what a proof hides.

WORDS. The first stage of a proximity test has a main table and a mask table. Each member of the
group under test owns a block of rows in each (MemShape, K12/RunLay.lean); layFirst lays the
members' rows into the stage's lists; where two blocks cover one row, the earlier member's wins. A
piece (Piece) is a stretch of a tree's column: one member's main rows, one member's mask rows, or
the first fold's fresh table. symG is a code word's symbol at a position
(Johnson/Prover/Link/Base.lean); lst reads a list of words as field elements, 0 beyond its end.

WHAT IT IS. No definition; five theorems.

  firstCoveringBlock    of a list of blocks, the search for the first that covers a row finds the
                        block number j, where that block covers the row and no earlier one does
  rowOfAMember          so the stage's row there is that block's own row
  mainPieceOfAMember    **member number j's main rows**: the job's stretch is the list of the
                        symbols of that member's own main rows and tails; one word a symbol where
                        the member's rows are over the base field, else three
  maskPieceOfAMember    **member number j's mask rows**: the same for its mask rows and tails
  freshPieceOfTheState  **the fresh table**: the job's stretch is the list of the symbols of the
                        state's fresh table and its tails, whatever the members are

KIN. main_piece, mask_piece, fresh_piece (K12/TreeIsColumn.lean) say the like at two members, at
member 0's main rows and member 1's mask rows, against one kind of sender's rows. These are general
in the member and stop at the member's own lists.

CALLED. maskWords, freshWords (K12/TreeIsColumn.lean); split_idx (K12/RunJobLaw.lean); getD_range,
sg_k (K12/RunByTab.lean); symG_congr (Johnson/Prover/Link/Base.lean).
-/
import Johnson.Desc.ProofFile.Honest.K12.TreeIsColumnAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.Part4
open OnBytes.Slice (ofE lst)
open Johnson.Prover.Link (PS symG symG_congr mainSym)
open Fmt.M1 (Stage)
open Fmt.M1.Own (PSt words)
open H2K.Pub (sgOf)
open ProofFile.Honest.K12.Light

/-! ## 1 The first block that covers a row -/

/-- **The search for the first block that covers row b finds block number j**, where that block
covers b and no earlier block does. -/
theorem firstCoveringBlock (b : ℕ) (B : RowBlock) (covers : B.first ≤ b ∧ b < B.first + B.count) :
    ∀ (blocks : List RowBlock) (j : ℕ), blocks[j]? = some B →
      (∀ i < j, ∀ other, blocks[i]? = some other →
        ¬ (other.first ≤ b ∧ b < other.first + other.count)) →
      (blocks.findSome? fun A =>
        if A.first ≤ b ∧ b < A.first + A.count then some (A.rows.getD (b - A.first) [])
        else none) = some (B.rows.getD (b - B.first) [])
  | [], _, isThere, _ => by simp at isThere
  | A :: rest, 0, isThere, _ => by
    have same : A = B := by simpa using isThere
    subst same
    simp only [List.findSome?_cons, if_pos covers]
  | A :: rest, j + 1, isThere, clear => by
    have notFirst := clear 0 (Nat.succ_pos j) A rfl
    simp only [List.findSome?_cons, if_neg notFirst]
    exact firstCoveringBlock b B covers rest j (by simpa using isThere) fun i below other isOther =>
      clear (i + 1) (Nat.succ_lt_succ below) other (by simpa using isOther)

/-- **So the stage's row b is that block's own row.** -/
theorem rowOfAMember (n len b : ℕ) (blocks : List RowBlock) (j : ℕ) (B : RowBlock) (inTable : b < n)
    (isThere : blocks[j]? = some B)
    (clear : ∀ i < j, ∀ other, blocks[i]? = some other →
      ¬ (other.first ≤ b ∧ b < other.first + other.count))
    (covers : B.first ≤ b ∧ b < B.first + B.count) :
    (layRows n len blocks).getD b [] = B.rows.getD (b - B.first) [] := by
  have found := firstCoveringBlock b B covers blocks j isThere clear
  unfold layRows
  rw [getD_range n _ _ b inTable]
  exact congrArg (fun answer => answer.getD (List.replicate len Fmt.Fld.zeroE)) found

/-! ## 2 The three sorts of piece -/

variable (s : Stage) (members : List (MemShape × PSt)) (j : ℕ) (m : MemShape) (q : PSt)
  (isMember : members[j]? = some (m, q)) (P : PS)

include isMember in
/-- **Member number j's main rows.** room: its block lies within the stage's main table. clear: no
earlier member's block covers one of its rows. table, tails: the state's main table and tails are
read off the stage's lists. -/
theorem mainPieceOfAMember (stage : s.h ≤ s.k) (room : m.mainFirst + m.mainRows ≤ 2 ^ s.k)
    (clear : ∀ i < j, ∀ other, members[i]? = some other → ∀ r < m.mainRows,
      ¬ (other.1.mainFirst ≤ m.mainFirst + r ∧
        m.mainFirst + r < other.1.mainFirst + other.1.mainRows))
    (table : P.tabM = (readPS s (layFirst s members)).tabM)
    (tails : P.tM = (readPS s (layFirst s members)).tM) (x : ℕ) :
    wordsAt (symOf s P x) (selsOf s (members.map (·.1)) (.main j)) =
      (List.range m.mainRows).flatMap fun r =>
        if m.base then [(ofE (symG s.C x (lst (q.M.getD r [])) (lst (q.Rh.getD r [])))).1]
        else words (ofE (symG s.C x (lst (q.M.getD r [])) (lst (q.Rh.getD r [])))) := by
  have shape : (members.map (·.1))[j]? = some m :=
    List.getElem?_map.trans (congrArg (Option.map (·.1)) isMember)
  have rows : selsOf s (members.map (·.1)) (.main j) =
      (List.range m.mainRows).map fun r => ⟨.main, m.mainFirst + r, m.base⟩ := by
    simp only [selsOf, shape]
  unfold wordsAt
  rw [rows, List.flatMap_map]
  refine congrArg List.flatten (List.map_congr_left fun r isRow => ?_)
  have below : r < m.mainRows := List.mem_range.1 isRow
  have inTable : m.mainFirst + r < 2 ^ s.k := by omega
  have covers : m.mainFirst ≤ m.mainFirst + r ∧ m.mainFirst + r < m.mainFirst + m.mainRows := by
    omega
  have symbol : symOf s P x ⟨.main, m.mainFirst + r, m.base⟩ =
      ofE (symG s.C x (lst (q.M.getD r [])) (lst (q.Rh.getD r []))) := by
    show (if m.mainFirst + r < 2 ^ s.k then
      ofE (mainSym (sgOf s) P.tabM P.tM x (m.mainFirst + r)) else Fmt.Fld.zeroE) = _
    rw [if_pos inTable]
    show ofE (symG s.C x
      (fun i => P.tabM (m.mainFirst + r + 2 ^ ((sgOf s).h + (sgOf s).g) * i))
      (P.tM (m.mainFirst + r))) = _
    rw [sg_k stage]
    refine congrArg ofE (symG_congr _ x _ _ _ _ (fun i _ => ?_) fun t _ => ?_)
    · rw [table]
      show lst ((layRows (2 ^ s.k) s.C.l
        (members.map fun y => ⟨y.1.mainFirst, y.1.mainRows, y.2.M⟩)).getD
          ((m.mainFirst + r + 2 ^ s.k * i) % 2 ^ s.k) [])
        ((m.mainFirst + r + 2 ^ s.k * i) / 2 ^ s.k) = _
      rw [(split_idx s.k _ i inTable).1, (split_idx s.k _ i inTable).2,
        rowOfAMember _ _ _ _ j ⟨m.mainFirst, m.mainRows, q.M⟩ inTable
          (List.getElem?_map.trans (congrArg (Option.map _) isMember))
          (fun i' before other isOther => by
            obtain ⟨y, isY, rfl⟩ := Option.map_eq_some_iff.1 (List.getElem?_map.symm.trans isOther)
            exact clear i' before y isY r below) covers]
      show lst (q.M.getD (m.mainFirst + r - m.mainFirst) []) i = _
      rw [Nat.add_sub_cancel_left]
    · rw [tails]
      show lst ((layRows (2 ^ s.k) s.C.r
        (members.map fun y => ⟨y.1.mainFirst, y.1.mainRows, y.2.Rh⟩)).getD
          (m.mainFirst + r) []) t = _
      rw [rowOfAMember _ _ _ _ j ⟨m.mainFirst, m.mainRows, q.Rh⟩ inTable
          (List.getElem?_map.trans (congrArg (Option.map _) isMember))
          (fun i' before other isOther => by
            obtain ⟨y, isY, rfl⟩ := Option.map_eq_some_iff.1 (List.getElem?_map.symm.trans isOther)
            exact clear i' before y isY r below) covers]
      show lst (q.Rh.getD (m.mainFirst + r - m.mainFirst) []) t = _
      rw [Nat.add_sub_cancel_left]
  show (if m.base then [(symOf s P x ⟨.main, m.mainFirst + r, m.base⟩).1]
    else words (symOf s P x ⟨.main, m.mainFirst + r, m.base⟩)) = _
  rw [symbol]

include isMember in
/-- **Member number j's mask rows.** room: its block lies within the stage's mask table. clear: no
earlier member's block covers one of its rows. table, tails: the state's mask table and tails are
read off the stage's lists. -/
theorem maskPieceOfAMember (room : m.maskFirst + m.maskRows ≤ 2 ^ s.h)
    (clear : ∀ i < j, ∀ other, members[i]? = some other → ∀ r < m.maskRows,
      ¬ (other.1.maskFirst ≤ m.maskFirst + r ∧
        m.maskFirst + r < other.1.maskFirst + other.1.maskRows))
    (table : P.tabZ = (readPS s (layFirst s members)).tabZ)
    (tails : P.tZ = (readPS s (layFirst s members)).tZ) (x : ℕ) :
    wordsAt (symOf s P x) (selsOf s (members.map (·.1)) (.mask j)) =
      (List.range m.maskRows).flatMap fun r =>
        words (ofE (symG s.Z (x % 2 ^ s.Z.a) (lst (q.W.getD r [])) (lst (q.Sg.getD r [])))) := by
  have shape : (members.map (·.1))[j]? = some m :=
    List.getElem?_map.trans (congrArg (Option.map (·.1)) isMember)
  have rows : selsOf s (members.map (·.1)) (.mask j) =
      (List.range m.maskRows).map fun r => ⟨.mask, m.maskFirst + r, false⟩ := by
    simp only [selsOf, shape]
  rw [rows, Light.maskWords s P x _ _ room]
  refine congrArg List.flatten (List.map_congr_left fun r isRow => ?_)
  have below : r < m.maskRows := List.mem_range.1 isRow
  have inTable : m.maskFirst + r < 2 ^ s.h := by omega
  have covers : m.maskFirst ≤ m.maskFirst + r ∧ m.maskFirst + r < m.maskFirst + m.maskRows := by
    omega
  refine congrArg (fun y => words (ofE y)) (symG_congr _ _ _ _ _ _ (fun i _ => ?_) fun t _ => ?_)
  · rw [table]
    show lst ((layRows (2 ^ s.h) s.Z.l
      (members.map fun y => ⟨y.1.maskFirst, y.1.maskRows, y.2.W⟩)).getD
        ((m.maskFirst + r + 2 ^ s.h * i) % 2 ^ s.h) [])
      ((m.maskFirst + r + 2 ^ s.h * i) / 2 ^ s.h) = _
    rw [(split_idx s.h _ i inTable).1, (split_idx s.h _ i inTable).2,
      rowOfAMember _ _ _ _ j ⟨m.maskFirst, m.maskRows, q.W⟩ inTable
        (List.getElem?_map.trans (congrArg (Option.map _) isMember))
        (fun i' before other isOther => by
          obtain ⟨y, isY, rfl⟩ := Option.map_eq_some_iff.1 (List.getElem?_map.symm.trans isOther)
          exact clear i' before y isY r below) covers]
    show lst (q.W.getD (m.maskFirst + r - m.maskFirst) []) i = _
    rw [Nat.add_sub_cancel_left]
  · rw [tails]
    show lst ((layRows (2 ^ s.h) s.Z.r
      (members.map fun y => ⟨y.1.maskFirst, y.1.maskRows, y.2.Sg⟩)).getD
        (m.maskFirst + r) []) t = _
    rw [rowOfAMember _ _ _ _ j ⟨m.maskFirst, m.maskRows, q.Sg⟩ inTable
        (List.getElem?_map.trans (congrArg (Option.map _) isMember))
        (fun i' before other isOther => by
          obtain ⟨y, isY, rfl⟩ := Option.map_eq_some_iff.1 (List.getElem?_map.symm.trans isOther)
          exact clear i' before y isY r below) covers]
    show lst (q.Sg.getD (m.maskFirst + r - m.maskFirst) []) t = _
    rw [Nat.add_sub_cancel_left]

/-- **The fresh table.** Whatever the members' shapes are. No premise. -/
theorem freshPieceOfTheState (shapes : List MemShape) (x : ℕ) :
    wordsAt (symOf s P x) (selsOf s shapes .fresh) =
      (List.range (2 ^ s.h)).flatMap fun r =>
        words (ofE (symG s.Z (x % 2 ^ s.Z.a) (P.fM r) (P.fT r))) :=
  Light.freshWords s P x

end ProofFile.Honest.K12.Part4

#print axioms ProofFile.Honest.K12.Part4.firstCoveringBlock
#print axioms ProofFile.Honest.K12.Part4.rowOfAMember
#print axioms ProofFile.Honest.K12.Part4.mainPieceOfAMember
#print axioms ProofFile.Honest.K12.Part4.maskPieceOfAMember
#print axioms ProofFile.Honest.K12.Part4.freshPieceOfTheState
