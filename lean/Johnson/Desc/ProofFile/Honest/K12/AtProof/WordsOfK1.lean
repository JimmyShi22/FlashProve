-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K12/AtProof/WordsOfK1.lean: the words that a proximity test's job makes
of its own rows, at a member made of a message of kind K1: the sender's table of that message, by
index. The twin of wordsAt_member (K12/WordsOfMember.lean), which stands at the shared chain's two
sendings. Together they give the value side of the tie at the last chain's test: its first two
members here, Omega's there.

  lst_tabG         an entry of a message's rows, as lists of words
  wordsAt_memK1    wordsAt at plainMany, at a member memK1: Rows.word of the member's rows

Limits.
- hl, hz: each code's message length is the power of two that its logarithm says, where its table has
  a row: premises, as at wordsAt_member.
- That the member's stretch reads the sender's own coins and its front the sender's: wMember_rows,
  members_held.
- What the witness's words are is the thread's letter: not here.
- Nothing on completeness, soundness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K12.AtProof.WMemberSent
import Johnson.Desc.ProofFile.Honest.K12.WordsOfMember

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.AtProof
open OnBytes (Statement GroupLayout Oracle ceilLog2)
open OnBytes.Slice (lst toE_ofE GE)
open OnBytes.Means (realRows tableSize)
open ProofFile.Honest (Addr Front)
open ProofFile.Honest.K12 (TestCoins)
open ProofFile.Honest.K12.Light (ManyJob plainMany memRows rowBits_shape)
open Johnson.Prover.Send (Rows shapeAt)

variable {W X : Type}

/-- **An entry of a message's rows, as lists of words.** -/
theorem lst_tabG (r n : Nat) (f : Nat → Nat → GE) (i j : Nat) (hi : i < r) (hj : j < n) :
    lst ((tabG r n f).getD i []) j = f i j := by
  unfold tabG
  rw [ProofFile.Honest.K12.Light.getD_range r _ _ i hi, ProofFile.Honest.K12.Light.lst_range n _ j hj, toE_ofE]

/-- **The words at a member of kind K1 are the member's rows' table, by index.** -/
theorem wordsAt_memK1 {Wd : Type} (J : K1.SendJob Wd X) (lift : W → Wd) (at_ : Addr) (k : Nat)
    (fs : Option Nat × Option Nat) (A : ManyJob W X) (n : Nat)
    (hn : A.mems[n]? = some (memK1 J lift at_ k fs)) (w : W) (fr : Front X) (C : TestCoins)
    (S : Statement) (L : GroupLayout) (o : Nat) (hf : L.find o = some n) (y : Oracle)
    (hy : S.oracles[o]? = some y) (hsh : y.shape = shapeAt J.P k) (hc : S.codes = J.P.codes)
    (hl : 0 < (shapeAt J.P k).mainRows → (J.P.codes.base.getD (shapeAt J.P k).code default).ell =
      2 ^ (J.P.codes.base.getD (shapeAt J.P k).code default).logEll)
    (hz : 0 < (shapeAt J.P k).maskRows →
      (J.P.codes.mask.getD (shapeAt J.P k).maskCode default).ell =
        2 ^ (J.P.codes.mask.getD (shapeAt J.P k).maskCode default).logEll)
    (pt : OnBytes.Part) (i : Nat) (hi : i < tableSize S o pt) :
    ProofFile.Honest.K12.wordsAt S L (plainMany A w fr C) o pt i =
      (K1.rowsR J.P J.ride (J.data (lift w) fr)
        (csAt _ (K1.startR J.P J.ride k) (C.mem n)) k).word (shapeAt J.P k) pt i := by
  have hg : (S.oracles.getD o default) = y := by
    rw [Array.getD_eq_getD_getElem?, hy]
    rfl
  have hrb : ∀ p, S.rowBits o p = ceilLog2 ((shapeAt J.P k).rows p) := fun p => by
    rw [rowBits_shape, hg, hsh]
  have hrr : ∀ p, realRows S o p = (shapeAt J.P k).rows p := fun p => by
    unfold realRows
    rw [hy]
    show y.shape.rows p = _
    rw [hsh]
  have hmr : memRows A w fr C n = psOfRows J.P k (K1.rowsR J.P J.ride (J.data (lift w) fr)
      (csAt _ (K1.startR J.P J.ride k) (C.mem n)) k) := by
    unfold memRows
    rw [hn]
    rfl
  unfold ProofFile.Honest.K12.wordsAt
  rw [hf]
  cases pt with
  | main =>
    show (if i % 2 ^ S.rowBits o .main < realRows S o .main then
      lst ((memRows A w fr C n).M.getD (i % 2 ^ S.rowBits o .main) []) (i / 2 ^ S.rowBits o .main)
      else 0) = (if i % 2 ^ ceilLog2 (shapeAt J.P k).mainRows < (shapeAt J.P k).mainRows then
        (K1.rowsR J.P J.ride (J.data (lift w) fr) (csAt _ (K1.startR J.P J.ride k) (C.mem n)) k).main
          ((shapeAt J.P k).mainDeg == 3) (i % 2 ^ ceilLog2 (shapeAt J.P k).mainRows)
          (i / 2 ^ ceilLog2 (shapeAt J.P k).mainRows) else 0)
    rw [hrb, hrr, hmr]
    show (if i % 2 ^ ceilLog2 (shapeAt J.P k).mainRows < (shapeAt J.P k).mainRows then _ else 0) = _
    split
    · rename_i hlt
      have hpos : 0 < y.shape.mainRows := by
        rw [hsh]
        exact Nat.lt_of_le_of_lt (Nat.zero_le _) hlt
      rw [Johnson.RunOne.Law.FrontSteps.tableSize_main hy hpos, hc, hsh, Nat.pow_add,
        ← hl (Nat.lt_of_le_of_lt (Nat.zero_le _) hlt)] at hi
      exact lst_tabG _ _ _ _ _ hlt (Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact hi))
    · rfl
  | mask =>
    show (if i % 2 ^ S.rowBits o .mask < realRows S o .mask then
      lst ((memRows A w fr C n).W.getD (i % 2 ^ S.rowBits o .mask) []) (i / 2 ^ S.rowBits o .mask)
      else 0) = (if i % 2 ^ ceilLog2 (shapeAt J.P k).maskRows < (shapeAt J.P k).maskRows then
        (K1.rowsR J.P J.ride (J.data (lift w) fr) (csAt _ (K1.startR J.P J.ride k) (C.mem n)) k).mask
          (i % 2 ^ ceilLog2 (shapeAt J.P k).maskRows)
          (i / 2 ^ ceilLog2 (shapeAt J.P k).maskRows) else 0)
    rw [hrb, hrr, hmr]
    show (if i % 2 ^ ceilLog2 (shapeAt J.P k).maskRows < (shapeAt J.P k).maskRows then _ else 0) = _
    split
    · rename_i hlt
      have hpos : 0 < y.shape.maskRows := by
        rw [hsh]
        exact Nat.lt_of_le_of_lt (Nat.zero_le _) hlt
      rw [Johnson.RunOne.Law.FrontSteps.tableSize_mask hy hpos, hc, hsh, Nat.pow_add,
        ← hz (Nat.lt_of_le_of_lt (Nat.zero_le _) hlt)] at hi
      exact lst_tabG _ _ _ _ _ hlt (Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact hi))
    · rfl

end ProofFile.Honest.K12.AtProof

#print axioms ProofFile.Honest.K12.AtProof.lst_tabG
#print axioms ProofFile.Honest.K12.AtProof.wordsAt_memK1
