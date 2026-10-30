-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K12/Part4/ColumnsOfSentMembers.lean: THE LAST CHAIN's PROXIMITY TEST
(the kind K12, the place W): AT A JOB ON THREE MEMBERS OF WHICH THE FIRST TWO ARE MESSAGES OF
SENDINGS OF THE KIND K1, THE COLUMNS OF THE JOB's TREES 0 AND 1 ARE THE SENDERS' OWN WRITTEN
SYMBOLS, at any rows V that agree with the members' rows.

WHAT IT IS NOT.
  * NO COIN, NO BOOK, NO RUN, NO THREAD. That the rows which a member computes at the stretch that
    the frame carries are the sender's rows at its own coins is a PREMISE here (memberRows); so is
    that the test's fresh table and its tails are the second sending's last message's mask rows
    (freshTable, freshTails).
  * It does not say what a sender's table is, nor that a thread's table shows these symbols: that
    is the sending's authors' half.
  * The public facts (each block lies within the stage's table; the codes are the stage's; the main
    rows' degree is 1 or 3; no earlier member's block covers a row) are premises, gathered in two
    structures. They are shown at no place here.
  * It is no statement on a tree's depth.
  * Nothing on completeness, soundness or what a proof hides.

WORDS. As in K12/Part4/PiecesOfAMember.lean. A sending of the kind K1 has public numbers P (K1.Par);
shapeAt P k is the shape of its message number k; Rows is what a caller gives of one message: every
row and every row's tail; mainSyms P V k x and maskSyms P V k x are the written symbols of message
k's main and mask rows at the position x (Johnson/Prover/Send/Core.lean): of these a sender's
written column is made. memK1 makes a member of such a message (K12/AtProof/JobW.lean).

WHAT IT IS. Two definitions, which are premises' forms; eight theorems.

  MaskBlockFits, MainBlockFits   a message's block of mask (main) rows, laid from a first row on,
                          lies within the stage's table, and its code is the stage's
  entryOfTheTable         a tabulated list of rows, read back, gives the entry
  symbolOverTheBaseField  a symbol of rows over the base field, computed in the extension field, is
                          the symbol computed in the base field
  maskSymbolsOfSentRows   the symbols of a message's tabulated mask rows are maskSyms
  mainSymbolsOfSentRows   the symbols of its tabulated main rows are mainSyms: one word a symbol at
                          degree 1, three at degree 3
  freshSymbolsOfSentRows  the symbols of a fresh table that agrees with a message's mask rows are
                          that message's maskSyms
  tablesOfThreeMembers    the first state's four tables are read off the three members' lists
  firstTreeIsTheSenders   **tree 0, where it is member 0's mask rows: its column is maskSyms of the
                          first sending's message**
  secondTreeIsTheSenders  **tree 1, where it is member 1's main rows, its mask rows and the fresh
                          table: its column is mainSyms ++ maskSyms of the second sending's message,
                          ++ maskSyms of the message that is the fresh table**

CALLED. mainPieceOfAMember, maskPieceOfAMember, freshPieceOfTheState (PiecesOfAMember.lean);
column_three, rows_three (K12/AtFile/WJointTree.lean); wordsAt_append (K12/TreeIsColumnAt.lean);
flatMap_congr' (K12/TreesSentBeforeTestFromSentTable.lean); symG_congr (Johnson/Prover/Link/Base.lean).
-/
import Johnson.Desc.ProofFile.Honest.K12.Part4.PiecesOfAMember
import Johnson.Desc.ProofFile.Honest.K12.AtFile.WJointTree
import Johnson.Desc.ProofFile.Honest.K12.AtProof.JobW
import Johnson.Desc.ProofFile.Honest.K12.TreesSentBeforeTestFromSentTable

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.Part4
open OnBytes.Slice (GE GF ofE ofF toE_ofE lst codeOf)
open Johnson.Prover.Link (PS symG symG_congr words3)
open Johnson.Prover.Send (Rows shapeAt mainSyms maskSyms symF)
open Fmt.M1 (Stage)
open Fmt.M1.Own (PSt words)
open VerifiableInference.Desc (K1.Par)
open ProofFile.Honest.K12.Light
open ProofFile.Honest.K12.AtProof (tabG psOfRows memShape memK1 csAt)

/-! ## 1 From lists of words to the sender's written symbols -/

/-- A message's block of mask rows, laid from the row first on, lies within the stage's mask table,
and its mask code is the stage's. -/
structure MaskBlockFits (s : Stage) (P : K1.Par) (k first : ℕ) : Prop where
  room : first + (shapeAt P k).maskRows ≤ 2 ^ s.h
  code : codeOf (P.codes.mask.getD (shapeAt P k).maskCode default) = s.Z

/-- The same for its main rows; and their degree is 1 or 3. -/
structure MainBlockFits (s : Stage) (P : K1.Par) (k first : ℕ) : Prop where
  stage : s.h ≤ s.k
  room : first + (shapeAt P k).mainRows ≤ 2 ^ s.k
  code : codeOf (P.codes.base.getD (shapeAt P k).code default) = s.C
  degree : (shapeAt P k).mainDeg = 1 ∨ (shapeAt P k).mainDeg = 3

/-- **A tabulated list of rows, read back, gives the entry.** -/
theorem entryOfTheTable (rows places : ℕ) (f : ℕ → ℕ → GE) (r j : ℕ) (isRow : r < rows)
    (isPlace : j < places) : lst ((tabG rows places f).getD r []) j = f r j := by
  unfold tabG
  rw [Light.getD_range rows _ _ r isRow, Light.lst_range places _ j isPlace, toE_ofE]

/-- **A symbol of rows over the base field, computed in the extension field, is the symbol computed
in the base field.** -/
theorem symbolOverTheBaseField (C : Fmt.M1.Code) (x : ℕ) (m r : ℕ → GF) :
    symG C x (fun j => algebraMap GF GE (m j)) (fun q => algebraMap GF GE (r q)) =
      algebraMap GF GE (symF C x m r) := by
  unfold symG symF
  simp only [map_add, map_sum, map_mul]

/-- **The symbols of a message's tabulated mask rows are the sender's written symbols.** -/
theorem maskSymbolsOfSentRows (P : K1.Par) (V : ℕ → Rows) (k x : ℕ) (Z : Fmt.M1.Code)
    (code : codeOf (P.codes.mask.getD (shapeAt P k).maskCode default) = Z) :
    ((List.range (shapeAt P k).maskRows).flatMap fun r =>
      words (ofE (symG Z (x % 2 ^ Z.a) (lst ((psOfRows P k (V k)).W.getD r []))
        (lst ((psOfRows P k (V k)).Sg.getD r []))))) = maskSyms P V k x := by
  subst code
  unfold maskSyms
  refine flatMap_congr' _ fun r isRow => ?_
  have below : r < (shapeAt P k).maskRows := List.mem_range.1 isRow
  exact congrArg (fun y => words (ofE y)) (symG_congr _ _ _ _ _ _
    (fun j isPlace => entryOfTheTable _ _ _ r j below isPlace)
    fun q isPlace => entryOfTheTable _ _ _ r q below isPlace)

/-- **The symbols of a message's tabulated main rows are the sender's written symbols**: one word a
symbol at degree 1, three at degree 3. -/
theorem mainSymbolsOfSentRows (P : K1.Par) (V : ℕ → Rows) (k x : ℕ) (C : Fmt.M1.Code)
    (code : codeOf (P.codes.base.getD (shapeAt P k).code default) = C)
    (degree : (shapeAt P k).mainDeg = 1 ∨ (shapeAt P k).mainDeg = 3) :
    ((List.range (shapeAt P k).mainRows).flatMap fun r =>
      if (shapeAt P k).mainDeg == 1 then
        [(ofE (symG C x (lst ((psOfRows P k (V k)).M.getD r []))
          (lst ((psOfRows P k (V k)).Rh.getD r [])))).1]
      else words (ofE (symG C x (lst ((psOfRows P k (V k)).M.getD r []))
          (lst ((psOfRows P k (V k)).Rh.getD r []))))) = mainSyms P V k x := by
  subst code
  unfold mainSyms
  refine flatMap_congr' _ fun r isRow => ?_
  have below : r < (shapeAt P k).mainRows := List.mem_range.1 isRow
  have symbol : symG (codeOf (P.codes.base.getD (shapeAt P k).code default)) x
      (lst ((psOfRows P k (V k)).M.getD r [])) (lst ((psOfRows P k (V k)).Rh.getD r [])) =
      symG (codeOf (P.codes.base.getD (shapeAt P k).code default)) x
        ((V k).main ((shapeAt P k).mainDeg == 3) r) ((V k).mainTl ((shapeAt P k).mainDeg == 3) r) :=
    symG_congr _ _ _ _ _ _ (fun j isPlace => entryOfTheTable _ _ _ r j below isPlace)
      fun q isPlace => entryOfTheTable _ _ _ r q below isPlace
  rw [symbol]
  rcases degree with one | three
  · rw [one]
    show [(ofE (symG _ x (fun j => algebraMap GF GE ((V k).mainF r j))
      fun q => algebraMap GF GE ((V k).mainTlF r q))).1] = [ofF (symF _ x _ _)]
    rw [symbolOverTheBaseField]
    rfl
  · rw [three]
    rfl

/-- **The symbols of a fresh table that agrees with a message's mask rows are that message's written
symbols.** fM, fT: the fresh table and its tails. -/
theorem freshSymbolsOfSentRows (P : K1.Par) (V : ℕ → Rows) (k x : ℕ) (s : Stage)
    (fM fT : ℕ → ℕ → GE) (rows : (shapeAt P k).maskRows = 2 ^ s.h)
    (code : codeOf (P.codes.mask.getD (shapeAt P k).maskCode default) = s.Z)
    (freshTable : ∀ r < 2 ^ s.h, ∀ j < s.Z.l, fM r j = (V k).mask r j)
    (freshTails : ∀ r < 2 ^ s.h, ∀ q < s.Z.r, fT r q = (V k).maskTl r q) :
    ((List.range (2 ^ s.h)).flatMap fun r =>
      words (ofE (symG s.Z (x % 2 ^ s.Z.a) (fM r) (fT r)))) = maskSyms P V k x := by
  show _ = (List.range (shapeAt P k).maskRows).flatMap fun r =>
    words3 (ofE (symG (codeOf (P.codes.mask.getD (shapeAt P k).maskCode default))
      (x % 2 ^ (codeOf (P.codes.mask.getD (shapeAt P k).maskCode default)).a) ((V k).mask r)
      ((V k).maskTl r)))
  rw [rows, code]
  refine flatMap_congr' _ fun r isRow => ?_
  have below : r < 2 ^ s.h := List.mem_range.1 isRow
  exact congrArg (fun y => words (ofE y)) (symG_congr _ _ _ _ _ _
    (fun j isPlace => freshTable r below j isPlace) fun q isPlace => freshTails r below q isPlace)

/-! ## 2 At a job on three members -/

variable {W X : Type} (B : ManyJob W X) (mA mB mC : Mem W X) (members : B.mems = [mA, mB, mC])
  (w : W) (fr : Front X) (C : TestCoins)

include members in
/-- **The first state's four tables are read off the three members' lists.** -/
theorem tablesOfThreeMembers :
    (B.toRun.toTest.first w fr C).tabM = (readPS B.s₀ (layFirst B.s₀
        [(mA.shape, mA.rows w fr (C.mem 0)), (mB.shape, mB.rows w fr (C.mem 1)),
          (mC.shape, mC.rows w fr (C.mem 2))])).tabM ∧
      (B.toRun.toTest.first w fr C).tM = (readPS B.s₀ (layFirst B.s₀
        [(mA.shape, mA.rows w fr (C.mem 0)), (mB.shape, mB.rows w fr (C.mem 1)),
          (mC.shape, mC.rows w fr (C.mem 2))])).tM ∧
      (B.toRun.toTest.first w fr C).tabZ = (readPS B.s₀ (layFirst B.s₀
        [(mA.shape, mA.rows w fr (C.mem 0)), (mB.shape, mB.rows w fr (C.mem 1)),
          (mC.shape, mC.rows w fr (C.mem 2))])).tabZ ∧
      (B.toRun.toTest.first w fr C).tZ = (readPS B.s₀ (layFirst B.s₀
        [(mA.shape, mA.rows w fr (C.mem 0)), (mB.shape, mB.rows w fr (C.mem 1)),
          (mC.shape, mC.rows w fr (C.mem 2))])).tZ := by
  rw [← rows_three B mA mB mC members w fr C.mem]
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- **Tree 0, where it is member 0's mask rows: its column is the first sending's message's written
mask symbols.** J, lift, sender, k, firstRows: the member, as memK1 makes it. V: any rows that agree
with the member's at message k (memberRows: a premise). fits: public. -/
theorem firstTreeIsTheSenders {Wd : Type} (J : K1.SendJob Wd X) (lift : W → Wd) (sender : Addr)
    (k : ℕ) (firstRows : Option ℕ × Option ℕ)
    (members : B.mems = [memK1 J lift sender k firstRows, mB, mC]) {depth : ℕ}
    (tree : B.trees[0]? = some (depth, [.mask 0]))
    (fits : MaskBlockFits B.s₀ J.P k (firstRows.2.getD 0)) (V : ℕ → Rows)
    (memberRows : K1.rowsR J.P J.ride (J.data (lift w) fr)
      (csAt _ (K1.startR J.P J.ride k) (C.mem 0)) k = V k) (x : ℕ) :
    ((B.toRun.toTest.trees₀ w fr C.mem (B.toRun.toTest.first w fr C)).getD 0
        (0, fun _ => [])).2 x = maskSyms J.P V k x := by
  obtain ⟨-, -, table, tails⟩ := tablesOfThreeMembers B _ mB mC members w fr C
  rw [column_three B _ mB mC members w fr C.mem _ 0 depth [.mask 0] tree x]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
  rw [← maskSymbolsOfSentRows J.P V k x B.s₀.Z fits.code, ← memberRows]
  exact maskPieceOfAMember B.s₀ [((memK1 J lift sender k firstRows).shape,
      (memK1 J lift sender k firstRows).rows w fr (C.mem 0)), (mB.shape, mB.rows w fr (C.mem 1)),
      (mC.shape, mC.rows w fr (C.mem 2))] 0 _ _ rfl _ fits.room
    (fun i before => absurd before (Nat.not_lt_zero i)) table tails x

/-- **Tree 1, where it is member 1's main rows, its mask rows and the fresh table: its column is the
second sending's written symbols.** J, lift, sender, firstRows: member 1, message 0 of its sending,
as memK1 makes it. freshMessage: the number of the message that is the fresh table. V: any rows that
agree with the member's at message 0 (memberRows) and with the test's fresh table at freshMessage
(freshTable, freshTails): premises. The other premises are public. -/
theorem secondTreeIsTheSenders {Wd : Type} (J : K1.SendJob Wd X) (lift : W → Wd) (sender : Addr)
    (firstRows : Option ℕ × Option ℕ)
    (members : B.mems = [mA, memK1 J lift sender 0 firstRows, mC]) {depth : ℕ}
    (tree : B.trees[1]? = some (depth, [.main 1, .mask 1, .fresh]))
    (fitsMain : MainBlockFits B.s₀ J.P 0 (firstRows.1.getD 0))
    (fitsMask : MaskBlockFits B.s₀ J.P 0 (firstRows.2.getD 0))
    (clearMain : ∀ r < (shapeAt J.P 0).mainRows, ¬ (mA.shape.mainFirst ≤ firstRows.1.getD 0 + r ∧
      firstRows.1.getD 0 + r < mA.shape.mainFirst + mA.shape.mainRows))
    (clearMask : ∀ r < (shapeAt J.P 0).maskRows, ¬ (mA.shape.maskFirst ≤ firstRows.2.getD 0 + r ∧
      firstRows.2.getD 0 + r < mA.shape.maskFirst + mA.shape.maskRows))
    (freshMessage : ℕ) (freshRows : (shapeAt J.P freshMessage).maskRows = 2 ^ B.s₀.h)
    (freshCode : codeOf (J.P.codes.mask.getD (shapeAt J.P freshMessage).maskCode default) =
      B.s₀.Z) (V : ℕ → Rows)
    (memberRows : K1.rowsR J.P J.ride (J.data (lift w) fr)
      (csAt _ (K1.startR J.P J.ride 0) (C.mem 1)) 0 = V 0)
    (freshTable : ∀ r < 2 ^ B.s₀.h, ∀ j < B.s₀.Z.l,
      (B.toRun.toTest.first w fr C).fM r j = (V freshMessage).mask r j)
    (freshTails : ∀ r < 2 ^ B.s₀.h, ∀ q < B.s₀.Z.r,
      (B.toRun.toTest.first w fr C).fT r q = (V freshMessage).maskTl r q) (x : ℕ) :
    ((B.toRun.toTest.trees₀ w fr C.mem (B.toRun.toTest.first w fr C)).getD 1
        (0, fun _ => [])).2 x =
      mainSyms J.P V 0 x ++ maskSyms J.P V 0 x ++ maskSyms J.P V freshMessage x := by
  obtain ⟨mainTable, mainTails, maskTable, maskTails⟩ :=
    tablesOfThreeMembers B mA _ mC members w fr C
  have onlyFirst : ∀ {p : MemShape × PSt → Prop}, p (mA.shape, mA.rows w fr (C.mem 0)) →
      ∀ i < 1, ∀ other, [(mA.shape, mA.rows w fr (C.mem 0)),
        ((memK1 J lift sender 0 firstRows).shape,
          (memK1 J lift sender 0 firstRows).rows w fr (C.mem 1)),
        (mC.shape, mC.rows w fr (C.mem 2))][i]? = some other → p other := by
    intro p holds i before other isOther
    obtain rfl : i = 0 := Nat.lt_one_iff.1 before
    obtain rfl : _ = other := Option.some.inj isOther
    exact holds
  rw [column_three B mA _ mC members w fr C.mem _ 1 depth [.main 1, .mask 1, .fresh] tree x]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
  rw [wordsAt_append, wordsAt_append, ← List.append_assoc,
    ← mainSymbolsOfSentRows J.P V 0 x B.s₀.C fitsMain.code fitsMain.degree,
    ← maskSymbolsOfSentRows J.P V 0 x B.s₀.Z fitsMask.code,
    ← freshSymbolsOfSentRows J.P V freshMessage x B.s₀ _ _ freshRows freshCode freshTable
      freshTails, ← memberRows]
  refine congrArg₂ (· ++ ·) (congrArg₂ (· ++ ·) ?_ ?_) ?_
  · exact mainPieceOfAMember B.s₀ [(mA.shape, mA.rows w fr (C.mem 0)),
      ((memK1 J lift sender 0 firstRows).shape,
        (memK1 J lift sender 0 firstRows).rows w fr (C.mem 1)),
      (mC.shape, mC.rows w fr (C.mem 2))] 1 _ _ rfl _ fitsMain.stage fitsMain.room
      (onlyFirst (p := fun other => ∀ r < (shapeAt J.P 0).mainRows,
        ¬ (other.1.mainFirst ≤ firstRows.1.getD 0 + r ∧
          firstRows.1.getD 0 + r < other.1.mainFirst + other.1.mainRows)) clearMain)
      mainTable mainTails x
  · exact maskPieceOfAMember B.s₀ [(mA.shape, mA.rows w fr (C.mem 0)),
      ((memK1 J lift sender 0 firstRows).shape,
        (memK1 J lift sender 0 firstRows).rows w fr (C.mem 1)),
      (mC.shape, mC.rows w fr (C.mem 2))] 1 _ _ rfl _ fitsMask.room
      (onlyFirst (p := fun other => ∀ r < (shapeAt J.P 0).maskRows,
        ¬ (other.1.maskFirst ≤ firstRows.2.getD 0 + r ∧
          firstRows.2.getD 0 + r < other.1.maskFirst + other.1.maskRows)) clearMask)
      maskTable maskTails x
  · exact freshPieceOfTheState B.s₀ _ _ x

end ProofFile.Honest.K12.Part4

#print axioms ProofFile.Honest.K12.Part4.entryOfTheTable
#print axioms ProofFile.Honest.K12.Part4.symbolOverTheBaseField
#print axioms ProofFile.Honest.K12.Part4.maskSymbolsOfSentRows
#print axioms ProofFile.Honest.K12.Part4.mainSymbolsOfSentRows
#print axioms ProofFile.Honest.K12.Part4.freshSymbolsOfSentRows
#print axioms ProofFile.Honest.K12.Part4.tablesOfThreeMembers
#print axioms ProofFile.Honest.K12.Part4.firstTreeIsTheSenders
#print axioms ProofFile.Honest.K12.Part4.secondTreeIsTheSenders
