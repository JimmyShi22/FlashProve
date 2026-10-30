-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/WordsOfMember.lean

OF WHAT KIND IT IS. With `cuts_atU` (CutOfBookAt.lean) in front, these two become a tie between what
one part is handed of a run's values and what another part is handed of them. By themselves they
name no run and no book: `SameCut` is a premise.

The words that a proximity test's job makes of its own rows at a member which is a message of one of
the shared chain's two sendings are that sender's coded table, read. Two theorems.

  `member_rows`: a member's own rows are its sender's, entry by entry, read.
  `wordsAt_member`: at a statement: `wordsAt` (Johnson/Desc/K12/Honest/LaidState.lean) at
      `plainMany` (ManyFits.lean) is the reading of the shared rounds' authors' `wordsOf`
      (Honest/K14/Sendings.lean) at the sender's rows.

What for. The field tie of `LeftAt` (OnFreeTAtHeadULeft.lean): those authors' `rowsU_read` and
`rowsO_read` (Honest/K14/SendingsRows.lean) end in the same reading of the same table.

By what. `entries_same`, `mem_main`, `mem_mask` (TreeIsColumnAt.lean); `lst_tabE`
(TreeIsColumn.lean); `rowBits_shape` (PubNear.lean); the library's `tableSize_main`,
`tableSize_mask` (Johnson/RunOne/Law/FrontSteps.lean).

Beside it. `held_wordsAt` (E2E/KeyHeldWords.lean) ties the library's `held` to `wordsAt` under two
premises at every row and place, without a bound: a `ManyJob`'s lists read 0 beyond their ends; that
the other side is 0 there is not known to us, so these two premises are not had for such lists.
`words_coded` (SaysAtTest.lean) reads `wordsAt` at `plainMany` as a coded table of the job's own.

Limits.
- A message that is laid of a vector and coins alone (hs). A fold's fresh table, the second message
  of "send o_u", is outside both laws; it is no member of the group under test, and `wordsAt` does
  not read it.
- hl and hz (a code's message length is the power of two that its logarithm says) are premises, each
  asked only where its table has a row: at the typed sizes o_u names no mask code and o_sp no base
  code, by an evaluation of Lean's that no file keeps, and the default code that is then read does
  not meet the equation. To ask both outright instead: true, and of no use at
  these two messages.
- hv (the member's vector is the sender's) and `SameCut` are premises.
- It moves no count. Nothing on completeness, on soundness or on what a view shows.
Terms: RunBySpec.lean.
-/
import Johnson.Desc.ProofFile.Honest.K12.TreeIsColumnAt
import Johnson.Desc.ProofFile.Honest.K12.PubNear
import Johnson.Desc.ProofFile.Honest.K12.ManyFits
import Johnson.RunOne.Law.FrontSteps

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.Light
open OnBytes (Statement GroupLayout Oracle ceilLog2)
open OnBytes.Slice (rdE ofE readE lst)
open OnBytes.Means (realRows tableSize)
open ProofFile.Honest (Addr State Front)
open ProofFile.Honest.K12 (TestCoins)
open ProofFile.Honest.K14 (SendJob jobU jobOmega laid Ask sendingsFit)

/-- **A member's own rows are its sender's, entry by entry, read.** J: one of the shared
chain's two sendings at the plan Q; k: one of its messages, laid of a vector and coins. The member
that `memOfSending` (JobShared.lean) makes of that message, at values c that are the sender's own,
cut from the message's offset on (`SameCut`, TreeIsColumnAt.lean), and at the sender's vector (hv):
at every real row and every place below the code's message length, the entry of the member's list,
read, is the sender's laid entry, read: in the main table and in the mask table. No run, no
statement of the verifier's and no book is named; t is the state as the sender's part is handed it.
-/
theorem member_rows {W X : Type} (Q : Desc.K14.P14) (hQ : sendingsFit Q = true) (J : SendJob)
    (hJ : J.Q = (jobU ⟨Q, 0⟩).Q ∧ J.sort = (jobU ⟨Q, 0⟩).sort ∨
      J.Q = (jobOmega ⟨Q, 0⟩).Q ∧ J.sort = (jobOmega ⟨Q, 0⟩).sort)
    (k : ℕ) (hk : k < J.Q.sent.size) (high : Bool) (hs : J.sort k = .plain high) (at_ : Addr)
    (fs : Option ℕ × Option ℕ) (ask : W → Ask) (v? : Option (W → Front X → ℕ → OnBytes.E)) (w : W)
    (fr : Front X) (t : State Ask Unit) (hv : vecAt J k ask v? w fr = J.data t k)
    (cs : Array OnBytes.E) (c : Stretch) (same : SameCut J k cs c) :
    (∀ r < (shapeAt J k).mainRows, ∀ j < (J.Q.codes.base.getD (shapeAt J k).code default).ell,
      lst (((memOfSending J at_ k fs ask v?).rows w fr c).M.getD r []) j =
        readE ((J.rows t cs k).main r j)) ∧
    ∀ r < (shapeAt J k).maskRows, ∀ j < (J.Q.codes.mask.getD (shapeAt J k).maskCode default).ell,
      lst (((memOfSending J at_ k fs ask v?).rows w fr c).W.getD r []) j =
        readE ((J.rows t cs k).mask r j) := by
  have hrows : (memOfSending J at_ k fs ask v?).rows w fr c =
      rowsOfLaid J.Q.codes (shapeAt J k) (laid J.Q.codes (shapeAt J k) (vecAt J k ask v? w fr)
        (fun i => OnBytes.E.ofTriple (ofE (c.e i))) (J.sort k)) := by
    cases v? <;> rfl
  rw [hrows, hv]
  refine ⟨fun r hr j hj => ?_, fun r hr j hj => ?_⟩
  · have e := entries_same Q hQ J hJ k hk high hs (J.data t k) cs c same (.main r j)
      (mem_main hr hj)
    show lst ((tabE (shapeAt J k).mainRows (J.Q.codes.base.getD (shapeAt J k).code default).ell
      _).getD r []) j = _
    rw [lst_tabE _ _ _ r j hr hj]
    exact e
  · have e := entries_same Q hQ J hJ k hk high hs (J.data t k) cs c same (.mask r j)
      (mem_mask hr hj)
    show lst ((tabE (shapeAt J k).maskRows
      (J.Q.codes.mask.getD (shapeAt J k).maskCode default).ell _).getD r []) j = _
    rw [lst_tabE _ _ _ r j hr hj]
    exact e

/-- **At a statement: the words that a job's own rows make at a member are the sender's coded
table, read.** Under `member_rows`' premises at the job's member number n and its values `C.mem n`:
where the layout finds the message o at n, the statement holds at o a message of that shape under
the sending's codes, and, of each of its two tables that has a row, the code's message length is the
power of two that its logarithm says: at every index below the table's size. -/
theorem wordsAt_member {W X : Type} (Q : Desc.K14.P14) (hQ : sendingsFit Q = true) (J : SendJob)
    (hJ : J.Q = (jobU ⟨Q, 0⟩).Q ∧ J.sort = (jobU ⟨Q, 0⟩).sort ∨
      J.Q = (jobOmega ⟨Q, 0⟩).Q ∧ J.sort = (jobOmega ⟨Q, 0⟩).sort)
    (k : ℕ) (hk : k < J.Q.sent.size) (high : Bool) (hs : J.sort k = .plain high) (at_ : Addr)
    (fs : Option ℕ × Option ℕ) (ask : W → Ask) (v? : Option (W → Front X → ℕ → OnBytes.E)) (w : W)
    (fr : Front X) (t : State Ask Unit) (hv : vecAt J k ask v? w fr = J.data t k)
    (cs : Array OnBytes.E) (A : ManyJob W X) (n : ℕ)
    (hn : A.mems[n]? = some (memOfSending J at_ k fs ask v?)) (C : TestCoins)
    (same : SameCut J k cs (C.mem n)) (S : Statement) (L : GroupLayout) (o : ℕ)
    (hf : L.find o = some n) (y : Oracle) (hy : S.oracles[o]? = some y)
    (hsh : y.shape = shapeAt J k) (hc : S.codes = J.Q.codes)
    (hl : 0 < (shapeAt J k).mainRows → (J.Q.codes.base.getD (shapeAt J k).code default).ell =
      2 ^ (J.Q.codes.base.getD (shapeAt J k).code default).logEll)
    (hz : 0 < (shapeAt J k).maskRows →
      (J.Q.codes.mask.getD (shapeAt J k).maskCode default).ell =
        2 ^ (J.Q.codes.mask.getD (shapeAt J k).maskCode default).logEll)
    (pt : OnBytes.Part) (i : ℕ) (hi : i < tableSize S o pt) :
    ProofFile.Honest.K12.wordsAt S L (plainMany A w fr C) o pt i =
      rdE.val (ProofFile.Honest.K14.wordsOf J.Q.sent (J.rows t cs) k pt i) := by
  obtain ⟨hM, hZ⟩ := member_rows Q hQ J hJ k hk high hs at_ fs ask v? w fr t hv cs (C.mem n) same
  have hg : (S.oracles.getD o default) = y := by
    rw [Array.getD_eq_getD_getElem?, hy]
    rfl
  have hrb : ∀ p, S.rowBits o p = ceilLog2 ((shapeAt J k).rows p) := fun p => by
    rw [rowBits_shape, hg, hsh]
  have hrr : ∀ p, realRows S o p = (shapeAt J k).rows p := fun p => by
    unfold realRows
    rw [hy]
    show y.shape.rows p = _
    rw [hsh]
  have hmr : memRows A w fr C n = (memOfSending J at_ k fs ask v?).rows w fr (C.mem n) := by
    unfold memRows
    rw [hn]
  unfold ProofFile.Honest.K12.wordsAt ProofFile.Honest.K14.wordsOf
  rw [hf]
  cases pt with
  | main =>
    show (if i % 2 ^ S.rowBits o .main < realRows S o .main then
      lst ((memRows A w fr C n).M.getD (i % 2 ^ S.rowBits o .main) []) (i / 2 ^ S.rowBits o .main)
      else 0) = rdE.val (if i % 2 ^ ceilLog2 (shapeAt J k).mainRows < (shapeAt J k).mainRows then
        (J.rows t cs k).main (i % 2 ^ ceilLog2 (shapeAt J k).mainRows)
          (i / 2 ^ ceilLog2 (shapeAt J k).mainRows) else OnBytes.zeroE)
    rw [hrb, hrr, hmr]
    show (if i % 2 ^ ceilLog2 (shapeAt J k).mainRows < (shapeAt J k).mainRows then _ else 0) = _
    split
    · rename_i hlt
      have hpos : 0 < y.shape.mainRows := by
        rw [hsh]
        exact Nat.lt_of_le_of_lt (Nat.zero_le _) hlt
      rw [Johnson.RunOne.Law.FrontSteps.tableSize_main hy hpos, hc, hsh, Nat.pow_add,
        ← hl (Nat.lt_of_le_of_lt (Nat.zero_le _) hlt)] at hi
      exact hM _ hlt _ (Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact hi))
    · exact rdE.zero.symm
  | mask =>
    show (if i % 2 ^ S.rowBits o .mask < realRows S o .mask then
      lst ((memRows A w fr C n).W.getD (i % 2 ^ S.rowBits o .mask) []) (i / 2 ^ S.rowBits o .mask)
      else 0) = rdE.val (if i % 2 ^ ceilLog2 (shapeAt J k).maskRows < (shapeAt J k).maskRows then
        (J.rows t cs k).mask (i % 2 ^ ceilLog2 (shapeAt J k).maskRows)
          (i / 2 ^ ceilLog2 (shapeAt J k).maskRows) else OnBytes.zeroE)
    rw [hrb, hrr, hmr]
    show (if i % 2 ^ ceilLog2 (shapeAt J k).maskRows < (shapeAt J k).maskRows then _ else 0) = _
    split
    · rename_i hlt
      have hpos : 0 < y.shape.maskRows := by
        rw [hsh]
        exact Nat.lt_of_le_of_lt (Nat.zero_le _) hlt
      rw [Johnson.RunOne.Law.FrontSteps.tableSize_mask hy hpos, hc, hsh, Nat.pow_add,
        ← hz (Nat.lt_of_le_of_lt (Nat.zero_le _) hlt)] at hi
      exact hZ _ hlt _ (Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact hi))
    · exact rdE.zero.symm

end ProofFile.Honest.K12.Light

#print axioms ProofFile.Honest.K12.Light.member_rows
#print axioms ProofFile.Honest.K12.Light.wordsAt_member
