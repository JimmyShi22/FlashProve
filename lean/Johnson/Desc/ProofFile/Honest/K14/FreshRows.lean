-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K14/FreshRows.lean: kind K14: WHICH COIN STANDS WHERE IN THE ROWS THAT
THE PART AT "send o_omega" MAKES (Honest/K14/Sendings.lean: laid, SendJob.rows, at jobOmega), where
the shape splits and o_sp has no main row, one mask row of n + 1 entries and one out-of-domain (OOD)
answer (SpShape, Johnson/Desc/K14/Honest/FreshAtChain.lean).

  omega_sent, omega_shape0, omega_shape1   the sending's two notices, written out
  spFirstCoin_eq  o_sp's first coin comes after o_omega's coins
  due_sp, takes_omega   o_sp's own count; **the part's count**: o_omega's coins, n + 1 entries, the
                  tail's r entries; all of the extension field
  sp_mask_coin, sp_tail_coin   entry j of o_sp's mask row is the part's coin number
                  spFirstCoin + j; entry q of its tail the coin number spFirstCoin + (n + 1) + q
  sp_row_read, sp_tail_read    **BELOW n + 1, AND BELOW r, these, read, are the row and the tail of
                  the library's statement on o_sp** (maskRowOf, maskTailOf:
                  Johnson/Desc/K14/Honest/FreshAt.lean) at the four into which coinsFour
                  (Honest/K14/FreshCoins.lean) cuts the part's coins
  sp_sym_read     so the symbol of o_sp's row at a position is the library's symbol at that row and
                  tail
  laid_main_congr, laid_tail_congr   a message without a mask row, at one vector: OF THE COINS its
                  main rows, at every place, and its main rows' tails, where they are read, read the
                  message's own alone
  omega_rows_congr   **so, at one state, of the part's coins o_omega's rows read those below
                  spFirstCoin alone**

What is assumed. The shape splits; SpShape; for o_omega: no mask row (hz: what the closing statement
reads off the test sendingsFit: omega_noMask, Honest/K14/FreshShows.lean).
What is not claimed. Nothing on how coins are sampled. Nothing on columns or answers. Nothing on any
property.
-/
import Johnson.Desc.ProofFile.Honest.K14.FreshDefs
import Johnson.Desc.ProofFile.Honest.K14.FreshCoins
import Johnson.Desc.K14.Honest.FreshAtChain

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K14
open OnBytes (E zeroE Codes OracleShape OracleNotice)
open OnBytes.Slice (readE rdE rdE_val)
open Desc.K14.Honest (SpShape maskRowOf maskTailOf)

variable (A : SendPub)

/-- The sending's two notices. -/
theorem omega_sent (hs : A.P.S.sharedSplitNeeded = true) :
    (jobOmega A).Q.sent = #[⟨A.P.S.omega, A.P.S.omegaLeafClass⟩,
      ⟨A.P.S.sharedSplit, A.P.S.sharedSplitLeafClass⟩] := by
  have e : (jobOmega A).Q.sent = Desc.K14.withOmega A.P.S := Desc.K14.Law.parK1_sent A.P 5 _ _
  rw [e, Desc.K14.Law.withOmega_split hs]

/-- Message number 0 has o_omega's shape. -/
theorem omega_shape0 (hs : A.P.S.sharedSplitNeeded = true) :
    ((jobOmega A).Q.sent.getD 0 default).shape = A.P.S.omega := by
  rw [omega_sent A hs]
  rfl

/-- Message number 1 has o_sp's shape. -/
theorem omega_shape1 (hs : A.P.S.sharedSplitNeeded = true) :
    ((jobOmega A).Q.sent.getD 1 default).shape = A.P.S.sharedSplit := by
  rw [omega_sent A hs]
  rfl

/-- o_sp's first coin comes after o_omega's coins. -/
theorem spFirstCoin_eq (hs : A.P.S.sharedSplitNeeded = true) :
    spFirstCoin A = dueOf A.P.codes A.P.S.omega (.plain A.P.S.omegaRowsHigh) := by
  unfold spFirstCoin offsetOf
  rw [omega_sent A hs]
  exact Nat.zero_add _

/-- o_sp's own count. -/
theorem due_sp {n : Nat} (H : SpShape A.P.codes A.P.S n) (high : Bool) :
    dueOf A.P.codes A.P.S.sharedSplit (.plain high) = n + 1 + (spMaskCode A).r := by
  have hl : (A.P.codes.mask.getD A.P.S.sharedSplit.maskCode default).ell = n + 1 := H.length
  show A.P.S.sharedSplit.mainRows * _ +
    (if A.P.S.sharedSplit.maskRows == 0 then A.P.S.sharedSplit.answers else 0) +
    A.P.S.sharedSplit.maskRows * (A.P.codes.mask.getD A.P.S.sharedSplit.maskCode default).ell +
    A.P.S.sharedSplit.maskRows * (spMaskCode A).r = _
  rw [H.noMain, H.oneRow, hl, if_neg (by decide), Nat.zero_mul, Nat.one_mul, Nat.one_mul]
  omega

/-- **The part's count.** -/
theorem takes_omega {n : Nat} (hs : A.P.S.sharedSplitNeeded = true)
    (H : SpShape A.P.codes A.P.S n) :
    (sendingPart (jobOmega A)).takes = ⟨0, spFirstCoin A + (n + 1) + (spMaskCode A).r⟩ := by
  show takesOf (jobOmega A).Q.codes (jobOmega A).Q.sent (jobOmega A).sort = _
  have e : offsetOf (jobOmega A).Q.codes (jobOmega A).Q.sent (jobOmega A).sort
      (jobOmega A).Q.sent.size = 0 + dueOf A.P.codes A.P.S.omega (.plain A.P.S.omegaRowsHigh) +
        dueOf A.P.codes A.P.S.sharedSplit (.plain A.P.S.omegaRowsHigh) := by
    unfold offsetOf
    rw [omega_sent A hs]
    rfl
  unfold takesOf
  rw [e, spFirstCoin_eq A hs, due_sp A H]
  congr 1
  omega

/-- Entry j of o_sp's mask row is the part's coin number spFirstCoin + j. -/
theorem sp_mask_coin {n : Nat} (hs : A.P.S.sharedSplitNeeded = true)
    (H : SpShape A.P.codes A.P.S n) (t : State Ask Unit) (cs : Array E) (j : Nat) :
    ((jobOmega A).rows t cs 1).mask 0 j = cs.getD (spFirstCoin A + j) zeroE := by
  unfold SendJob.rows
  rw [omega_shape1 A hs]
  show cs.getD (spFirstCoin A + (A.P.S.sharedSplit.mainRows * _ +
    (if A.P.S.sharedSplit.maskRows == 0 then A.P.S.sharedSplit.answers else 0) +
    j * A.P.S.sharedSplit.maskRows + 0)) zeroE = _
  rw [H.noMain, H.oneRow]
  simp

/-- Entry q of o_sp's tail is the part's coin number spFirstCoin + (n + 1) + q. -/
theorem sp_tail_coin {n : Nat} (hs : A.P.S.sharedSplitNeeded = true)
    (H : SpShape A.P.codes A.P.S n) (t : State Ask Unit) (cs : Array E) (q : Nat) :
    ((jobOmega A).rows t cs 1).maskTail 0 q = cs.getD (spFirstCoin A + (n + 1) + q) zeroE := by
  have hl : (A.P.codes.mask.getD A.P.S.sharedSplit.maskCode default).ell = n + 1 := H.length
  unfold SendJob.rows
  rw [omega_shape1 A hs]
  show cs.getD (spFirstCoin A + (A.P.S.sharedSplit.mainRows * _ +
    (if A.P.S.sharedSplit.maskRows == 0 then A.P.S.sharedSplit.answers else 0) +
    A.P.S.sharedSplit.maskRows *
      (A.P.codes.mask.getD A.P.S.sharedSplit.maskCode default).ell + 0 * _ + q)) zeroE = _
  rw [H.noMain, H.oneRow, hl]
  congr 1
  simp
  omega

/-- **o_sp's mask row, read, below n + 1**: the library's row at the four into which coinsFour cuts
the coins. -/
theorem sp_row_read {n : Nat} (hs : A.P.S.sharedSplitNeeded = true)
    (H : SpShape A.P.codes A.P.S n) (t : State Ask Unit) {d : Due} (hf : d.f = 0)
    (he : d.e = spFirstCoin A + (n + 1) + (spMaskCode A).r) (c : Cs d) (j : Nat) (hj : j < n + 1) :
    readE (((jobOmega A).rows t (coinsE c).toArray 1).mask 0 j) =
      maskRowOf n (coinsFour (spFirstCoin A) n (spMaskCode A).r hf he c).1.2.1
        (coinsFour (spFirstCoin A) n (spMaskCode A).r hf he c).1.2.2 j := by
  rw [sp_mask_coin A hs H, ← rdE_val, coin_read c _ (by omega)]
  unfold maskRowOf
  by_cases h : j < n
  · rw [dif_pos h]
    rfl
  · rw [dif_neg h]
    exact congrArg c.e (Fin.ext (by show spFirstCoin A + j = spFirstCoin A + n; omega))

/-- **o_sp's tail, read, below r**: the library's tail. -/
theorem sp_tail_read {n : Nat} (hs : A.P.S.sharedSplitNeeded = true)
    (H : SpShape A.P.codes A.P.S n) (t : State Ask Unit) {d : Due} (hf : d.f = 0)
    (he : d.e = spFirstCoin A + (n + 1) + (spMaskCode A).r) (c : Cs d) (q : Nat)
    (hq : q < (spMaskCode A).r) :
    readE (((jobOmega A).rows t (coinsE c).toArray 1).maskTail 0 q) =
      maskTailOf (spMaskCode A).r (coinsFour (spFirstCoin A) n (spMaskCode A).r hf he c).1.1
        q := by
  rw [sp_tail_coin A hs H, ← rdE_val, coin_read c _ (by omega)]
  unfold maskTailOf
  rw [dif_pos hq]
  rfl

/-- **The symbol of o_sp's row at a position**, of the rows as the part lays them and read: the
library's symbol at the row and the tail of its statement on o_sp. -/
theorem sp_sym_read {n : Nat} (hs : A.P.S.sharedSplitNeeded = true)
    (H : SpShape A.P.codes A.P.S n) (t : State Ask Unit) {d : Due} (hf : d.f = 0)
    (he : d.e = spFirstCoin A + (n + 1) + (spMaskCode A).r) (c : Cs d) (y : Nat) :
    Johnson.Prover.Link.symG (OnBytes.Slice.codeOf (spMaskCode A)) y
        (fun j => readE (((jobOmega A).rows t (coinsE c).toArray 1).mask 0 j))
        (fun q => readE (((jobOmega A).rows t (coinsE c).toArray 1).maskTail 0 q)) =
      Johnson.Prover.Link.symG (Desc.K14.Honest.spSymCode A.P.codes A.P.S) y
        (maskRowOf n (coinsFour (spFirstCoin A) n (spMaskCode A).r hf he c).1.2.1
          (coinsFour (spFirstCoin A) n (spMaskCode A).r hf he c).1.2.2)
        (maskTailOf (Desc.K14.Honest.spSymCode A.P.codes A.P.S).r
          (coinsFour (spFirstCoin A) n (spMaskCode A).r hf he c).1.1) :=
  Johnson.Prover.Link.symG_congr _ y _ _ _ _
    (fun j hj => sp_row_read A hs H t hf he c j (by
      have hl : (Desc.K14.Honest.spSymCode A.P.codes A.P.S).l = n + 1 := H.length
      exact hl ▸ hj))
    fun q hq => sp_tail_read A hs H t hf he c q hq

/-- A message without a mask row, at one vector v: of the coins its main rows read the message's own
alone, at every place. -/
theorem laid_main_congr (codes : Codes) (s : OracleShape) (v cs cs' : Nat → E) (high : Bool)
    (hz : s.maskRows = 0) (h : ∀ i, i < dueOf codes s (.plain high) → cs i = cs' i) (r j : Nat) :
    (laid codes s v cs (.plain high)).main r j = (laid codes s v cs' (.plain high)).main r j := by
  show (if _ then cs _ else _) = (if _ then cs' _ else _)
  split_ifs with hc
  · simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hc
    refine h _ ?_
    show _ < s.mainRows * _ + (if s.maskRows == 0 then s.answers else 0) + s.maskRows * _ +
      s.maskRows * _
    rw [hz, if_pos (by decide)]
    omega
  · rfl

/-- A message's main rows' tails, where they are read, read the message's own coins alone. -/
theorem laid_tail_congr (codes : Codes) (s : OracleShape) (v cs cs' : Nat → E) (high : Bool)
    (h : ∀ i, i < dueOf codes s (.plain high) → cs i = cs' i) (r q : Nat) (hr : r < s.mainRows)
    (hq : q < (codes.base.getD s.code default).r) :
    (laid codes s v cs (.plain high)).mainTail r q =
      (laid codes s v cs' (.plain high)).mainTail r q := by
  show cs _ = cs' _
  refine h _ ?_
  have h1 : r * (codes.base.getD s.code default).r + q <
      s.mainRows * (codes.base.getD s.code default).r :=
    Nat.lt_of_lt_of_le (by rw [Nat.succ_mul]; omega) (Nat.mul_le_mul_right _ hr)
  simp only [dueOf]
  omega

/-- **At one state, of the part's coins o_omega's rows read those below spFirstCoin alone.** -/
theorem omega_rows_congr (hs : A.P.S.sharedSplitNeeded = true) (hz : A.P.S.omega.maskRows = 0)
    (t : State Ask Unit) (cs cs' : Array E)
    (h : ∀ i, i < spFirstCoin A → cs.getD i zeroE = cs'.getD i zeroE) :
    (∀ r j, ((jobOmega A).rows t cs 0).main r j = ((jobOmega A).rows t cs' 0).main r j) ∧
      ∀ r q, r < A.P.S.omega.mainRows → q < (A.P.codes.base.getD A.P.S.omega.code default).r →
        ((jobOmega A).rows t cs 0).mainTail r q = ((jobOmega A).rows t cs' 0).mainTail r q := by
  have h' : ∀ i, i < dueOf A.P.codes A.P.S.omega (.plain A.P.S.omegaRowsHigh) →
      cs.getD (offsetOf (jobOmega A).Q.codes (jobOmega A).Q.sent (jobOmega A).sort 0 + i) zeroE =
        cs'.getD (offsetOf (jobOmega A).Q.codes (jobOmega A).Q.sent (jobOmega A).sort 0 + i)
          zeroE := fun i hi => by
    have e : offsetOf (jobOmega A).Q.codes (jobOmega A).Q.sent (jobOmega A).sort 0 = 0 := by
      simp [offsetOf]
    rw [e, Nat.zero_add]
    exact h i (by rw [spFirstCoin_eq A hs]; exact hi)
  unfold SendJob.rows
  rw [omega_shape0 A hs]
  exact ⟨fun r j => laid_main_congr A.P.codes A.P.S.omega _ _ _ _ hz h' r j,
    fun r q hr hq => laid_tail_congr A.P.codes A.P.S.omega _ _ _ _ h' r q hr hq⟩

end ProofFile.Honest.K14

#print axioms ProofFile.Honest.K14.omega_sent
#print axioms ProofFile.Honest.K14.omega_shape0
#print axioms ProofFile.Honest.K14.omega_shape1
#print axioms ProofFile.Honest.K14.spFirstCoin_eq
#print axioms ProofFile.Honest.K14.due_sp
#print axioms ProofFile.Honest.K14.takes_omega
#print axioms ProofFile.Honest.K14.sp_mask_coin
#print axioms ProofFile.Honest.K14.sp_tail_coin
#print axioms ProofFile.Honest.K14.sp_row_read
#print axioms ProofFile.Honest.K14.sp_tail_read
#print axioms ProofFile.Honest.K14.sp_sym_read
#print axioms ProofFile.Honest.K14.laid_main_congr
#print axioms ProofFile.Honest.K14.laid_tail_congr
#print axioms ProofFile.Honest.K14.omega_rows_congr
