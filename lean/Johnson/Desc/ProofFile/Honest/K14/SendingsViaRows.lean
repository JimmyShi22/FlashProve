-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K14/SendingsViaRows.lean: the two texts of a sending lay the same
entries in the two tables OF TWO SORTS OF MESSAGE, both laid plainly (MsgSort.plain): a message that
carries a vector over the extension field, with no mask row, at least one OOD answer and no more
answers than the code's message length (main_same, word_main_same); and a message of mask rows alone
on which no table rides (mask_same, word_mask_same). There the rows that the shared sending's part
lays (rowsR, Honest/K1/Coins.lean) of a vector's data and its coins are, entry by entry below the
rows' number and the code's message length, what this kind's own text lays (laid,
Honest/K14/Sendings.lean) of the same vector and the same coins, read in the field; by index: below
the tables' sizes, where the code's message length is a power of two. Nine statements with their
proofs; no definition.

  val_coinsE      a part's coin by number, as the program's element, reads as the coin (ce)
  pad_count       the pad's count at a message that carries a vector and has no mask row: the number
                  of its OOD answers
  main_same       a message that carries a vector and has no mask row: its main rows' entries
  mask_same       a message of mask rows alone on which no table rides: its mask rows' entries
  word_main_same, word_mask_same, word_none_same, word_noMain_same   so the two tables by index,
                  below their sizes
  start_one       where message number 1's coins begin: at the same number in both texts, where
                  there is a message number 0, it carries a vector and has no mask row, and no table
                  rides on it

What is assumed. The message's coins in the two texts are the same by number: cs i reads as the coin
number (startR P ride k).e + i. The data is vectorData (Honest/K14/SendingsVia.lean) of the vector.
On the shape: for a vector's message: entries of the extension field, no mask row, an OOD answer, no
more answers than the code's message length; for a message of mask rows alone: no main row. For the
tables by index: the code's message length is a power of two.
What is not claimed. Nothing on tails or on a riding table: Honest/K14/SendingsViaHolds.lean. That a
number lies below a part's count: val_coinsE holds beyond the count too (0 = 0); that the two texts
take as many coins: Honest/K14/SendingsViaCounts.lean. Nothing on a verifier's decision, on
soundness or on hiding.
Nearest kin: below the count val_coinsE says what coin_read (Honest/K14/FreshCoins.lean) says.
-/
import Johnson.Desc.ProofFile.Honest.K14.SendingsVia
import Johnson.Desc.ProofFile.Honest.K14.Sendings
import Johnson.Desc.ProofFile.Honest.Sum
import Johnson.Desc.ProofFile.Honest.K1.CoinLaw
import Johnson.Desc.ProofFile.Honest.K1.MaskLaw
import Johnson.Desc.ProofFile.Honest.K1.DataLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K14
open OnBytes (E zeroE Codes OracleShape OracleNotice ceilLog2)
open OnBytes.Slice (GE GF rdE rdE_val readE readE_ofTriple toE toE_ofE ofE)
open VerifiableInference.Desc (K1.Par K1.Msg.of)
open Johnson.Prover.Send (Rows shapeAt)
open ProofFile.Honest.K1 (Ride rowsR startR dueR ce)

/-- A part's coin by number, as the program's element, reads as the coin; beyond the count both
sides are 0. -/
theorem val_coinsE {d : Due} (c : Cs d) (j : Nat) :
    rdE.val ((coinsE c).toArray.getD j zeroE) = ce c j := by
  unfold coinsE ce
  by_cases h : j < d.e
  · rw [dif_pos h]
    simp [Array.getD_eq_getD_getElem?, h, rdE_val, readE_ofTriple, toE_ofE]
  · rw [dif_neg h]
    simp [Array.getD_eq_getD_getElem?, h, rdE.zero]

variable (P : K1.Par) (ride : Nat → Option Ride)
  (data : Nat → Nat → Nat → Option (GF ⊕ GE)) (c : Cs (dueR P ride)) (k : Nat)

/-- The pad's count at a message that carries a vector and has no mask row, where it has an OOD
answer: the number of its OOD answers. -/
theorem pad_count (codes : Codes) (s : OracleShape) (R : Option Ride) (h3 : s.mainDeg = 3)
    (hz : s.maskRows = 0) (ha : s.answers ≠ 0) :
    (ProofFile.Honest.K1.stepsOf codes s R).pad = s.answers := by
  simp [ProofFile.Honest.K1.stepsOf, h3, hz, ha]

/-- **The main rows' entries of a message that carries a vector and has no mask row are the same in
the two texts**, below the rows' number (hr) and the code's message length (hj): where the entries
are of the extension field, the message has an OOD answer and no more answers than that length, the
data is vectorData of the vector (hdata), and the coins are the same by number (hcs). -/
theorem main_same (high : Bool) (v cs : Nat → E) (h3 : (shapeAt P k).mainDeg = 3)
    (hz : (shapeAt P k).maskRows = 0) (ha : (shapeAt P k).answers ≠ 0)
    (hlen : (shapeAt P k).answers ≤ (P.codes.base.getD (shapeAt P k).code default).ell)
    (hdata : ∀ r j, data k r j = vectorData P.codes (shapeAt P k) high v r j)
    (hcs : ∀ i, rdE.val (cs i) = ce c ((startR P ride k).e + i)) (r j : Nat)
    (hr : r < (shapeAt P k).mainRows)
    (hj : j < (P.codes.base.getD (shapeAt P k).code default).ell) :
    (rowsR P ride data c k).mainE r j =
      rdE.val ((laid P.codes (shapeAt P k) v cs (.plain high)).main r j) := by
  have h3b : ((shapeAt P k).mainDeg == 3) = true := by rw [h3]; rfl
  have hpad := pad_count P.codes (shapeAt P k) (ride k) h3 hz ha
  by_cases hp : r + 1 = (shapeAt P k).mainRows ∧
      (P.codes.base.getD (shapeAt P k).code default).ell - (shapeAt P k).answers ≤ j
  · -- a place of the pad
    obtain ⟨hp1, hp2⟩ := hp
    have e := ProofFile.Honest.K1.pad_coin_e P ride data c k
      (j - ((P.codes.base.getD (shapeAt P k).code default).ell - (shapeAt P k).answers)) h3b ha
      (by omega) (by rw [hpad]; exact hlen) (by rw [hpad]; omega)
    rw [hpad] at e
    have er : (shapeAt P k).mainRows - 1 = r := by omega
    have ej : (P.codes.base.getD (shapeAt P k).code default).ell - (shapeAt P k).answers +
        (j - ((P.codes.base.getD (shapeAt P k).code default).ell - (shapeAt P k).answers)) = j := by
      omega
    rw [er, ej] at e
    rw [e]
    have hc : ((shapeAt P k).maskRows == 0 && r + 1 == (shapeAt P k).mainRows &&
        decide ((P.codes.base.getD (shapeAt P k).code default).ell - (shapeAt P k).answers ≤ j) &&
        decide (j < (P.codes.base.getD (shapeAt P k).code default).ell)) = true := by
      rw [hz, hp1, decide_eq_true hp2, decide_eq_true hj, beq_self_eq_true, beq_self_eq_true]
      rfl
    show _ = rdE.val (if _ then cs _ else _)
    rw [if_pos hc, hcs]
    rfl
  · -- a place of the vector
    have hno : (r, j) ∉ padInMain (P.codes.base.getD (shapeAt P k).code default).ell
        (shapeAt P k) := by
      unfold padInMain
      have hm : (shapeAt P k).mainRows ≠ 0 := by omega
      simp only [hz, h3b, bne_self_eq_false, beq_eq_false_iff_ne.2 hm, Bool.or_self,
        Bool.false_eq_true, if_false, if_true, Nat.one_mul, List.mem_map, List.mem_range,
        Prod.mk.injEq, not_exists, not_and]
      intro i hi h1 h2
      exact hp ⟨by omega, by omega⟩
    rw [ProofFile.Honest.K1.main_data_e P ride data c k r j h3b hr hj ha hno, hdata r j]
    have hc : (viaPad P.codes (shapeAt P k) r j) = false := by
      unfold viaPad
      by_contra hh
      have hh' := eq_true_of_ne_false hh
      simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hh'
      exact hp ⟨hh'.1.1.2, hh'.1.2⟩
    have hc2 : ((shapeAt P k).maskRows == 0 && r + 1 == (shapeAt P k).mainRows &&
        decide ((P.codes.base.getD (shapeAt P k).code default).ell - (shapeAt P k).answers ≤ j) &&
        decide (j < (P.codes.base.getD (shapeAt P k).code default).ell)) = false := hc
    unfold vectorData
    rw [hc, decide_eq_false (Nat.not_le.2 hr), decide_eq_false (Nat.not_le.2 hj)]
    show toE _ = rdE.val (if _ then _ else v _)
    rw [hc2]
    rfl

/-- **The mask rows' entries of a message of mask rows alone, on which no table rides, are the same
in the two texts**, below the rows' number (hr) and the mask code's message length (hj), where the
coins are the same by number (hcs). -/
theorem mask_same (high : Bool) (v cs : Nat → E) (hm : (shapeAt P k).mainRows = 0)
    (hz : (shapeAt P k).maskRows ≠ 0) (hride : ride k = none)
    (hcs : ∀ i, rdE.val (cs i) = ce c ((startR P ride k).e + i)) (r j : Nat)
    (hr : r < (shapeAt P k).maskRows)
    (hj : j < (P.codes.mask.getD (shapeAt P k).maskCode default).ell) :
    (rowsR P ride data c k).mask r j =
      rdE.val ((laid P.codes (shapeAt P k) v cs (.plain high)).mask r j) := by
  rw [ProofFile.Honest.K1.mask_coin P ride data c k r j hride hr hj]
  have hzb : ((shapeAt P k).maskRows == 0) = false := beq_eq_false_iff_ne.2 hz
  show _ = rdE.val (cs ((shapeAt P k).mainRows * _ +
    (if (shapeAt P k).maskRows == 0 then _ else 0) + j * (shapeAt P k).maskRows + r))
  rw [hcs, hm, hzb]
  have hs : ProofFile.Honest.K1.maskStart P ride k = (startR P ride k).e := by
    simp [ProofFile.Honest.K1.maskStart, ProofFile.Honest.K1.Steps.main, ProofFile.Honest.K1.stepsOf, hm, hz]
  rw [hs]
  congr 1
  simp [Nat.add_assoc]

/-- **The main table by index**, below its size: under main_same's premises, and where the code's
message length is a power of two (h2). -/
theorem word_main_same (L : Nat → Laid) (high : Bool) (v cs : Nat → E)
    (hL : L k = laid P.codes (shapeAt P k) v cs (.plain high))
    (h3 : (shapeAt P k).mainDeg = 3) (hz : (shapeAt P k).maskRows = 0)
    (ha : (shapeAt P k).answers ≠ 0)
    (hlen : (shapeAt P k).answers ≤ (P.codes.base.getD (shapeAt P k).code default).ell)
    (h2 : 2 ^ (P.codes.base.getD (shapeAt P k).code default).logEll =
      (P.codes.base.getD (shapeAt P k).code default).ell)
    (hdata : ∀ r j, data k r j = vectorData P.codes (shapeAt P k) high v r j)
    (hcs : ∀ i, rdE.val (cs i) = ce c ((startR P ride k).e + i)) (i : Nat)
    (hi : i < (K1.Msg.of P.codes (shapeAt P k)).size .main) :
    (rowsR P ride data c k).word (shapeAt P k) .main i = rdE.val (wordsOf P.sent L k .main i) := by
  show (if i % 2 ^ ceilLog2 (shapeAt P k).mainRows < (shapeAt P k).mainRows then
      (rowsR P ride data c k).main ((shapeAt P k).mainDeg == 3)
        (i % 2 ^ ceilLog2 (shapeAt P k).mainRows) (i / 2 ^ ceilLog2 (shapeAt P k).mainRows)
      else 0) =
    rdE.val (if i % 2 ^ ceilLog2 (shapeAt P k).mainRows < (shapeAt P k).mainRows then
      (L k).main (i % 2 ^ ceilLog2 (shapeAt P k).mainRows)
        (i / 2 ^ ceilLog2 (shapeAt P k).mainRows) else zeroE)
  by_cases hr : i % 2 ^ ceilLog2 (shapeAt P k).mainRows < (shapeAt P k).mainRows
  · rw [if_pos hr, if_pos hr, hL]
    have hj : i / 2 ^ ceilLog2 (shapeAt P k).mainRows <
        (P.codes.base.getD (shapeAt P k).code default).ell := by
      have hK : ((shapeAt P k).mainRows != 0) = true := bne_iff_ne.2 (by omega)
      have hK' : ((shapeAt P k).mainRows == 0) = false := beq_eq_false_iff_ne.2 (by omega)
      have hs : (K1.Msg.of P.codes (shapeAt P k)).size .main =
          2 ^ ceilLog2 (shapeAt P k).mainRows *
            2 ^ (P.codes.base.getD (shapeAt P k).code default).logEll := by
        rw [← Nat.pow_add]
        show (if ((shapeAt P k).mainRows != 0) = true then
          2 ^ (if ((shapeAt P k).mainRows == 0) = true then 0 else
            ceilLog2 (shapeAt P k).mainRows +
              (P.codes.base.getD (shapeAt P k).code default).logEll) else 0) = _
        rw [if_pos hK, hK', if_neg Bool.false_ne_true]
      rw [hs, h2] at hi
      exact Nat.div_lt_of_lt_mul hi
    rw [← main_same P ride data c k high v cs h3 hz ha hlen hdata hcs _ _ hr hj]
    unfold Rows.main
    rw [h3]
    rfl
  · rw [if_neg hr, if_neg hr, rdE.zero]

/-- **The mask table by index**, below its size: where the message has no main row, no table rides
on it, the coins are the same by number, and the mask code's message length is a power of two
(h2). -/
theorem word_mask_same (L : Nat → Laid) (high : Bool) (v cs : Nat → E)
    (hL : L k = laid P.codes (shapeAt P k) v cs (.plain high))
    (hm : (shapeAt P k).mainRows = 0) (hride : ride k = none)
    (h2 : 2 ^ (P.codes.mask.getD (shapeAt P k).maskCode default).logEll =
      (P.codes.mask.getD (shapeAt P k).maskCode default).ell)
    (hcs : ∀ i, rdE.val (cs i) = ce c ((startR P ride k).e + i)) (i : Nat)
    (hi : i < (K1.Msg.of P.codes (shapeAt P k)).size .mask) :
    (rowsR P ride data c k).word (shapeAt P k) .mask i = rdE.val (wordsOf P.sent L k .mask i) := by
  show (if i % 2 ^ ceilLog2 (shapeAt P k).maskRows < (shapeAt P k).maskRows then
      (rowsR P ride data c k).mask (i % 2 ^ ceilLog2 (shapeAt P k).maskRows)
        (i / 2 ^ ceilLog2 (shapeAt P k).maskRows) else 0) =
    rdE.val (if i % 2 ^ ceilLog2 (shapeAt P k).maskRows < (shapeAt P k).maskRows then
      (L k).mask (i % 2 ^ ceilLog2 (shapeAt P k).maskRows)
        (i / 2 ^ ceilLog2 (shapeAt P k).maskRows) else zeroE)
  by_cases hr : i % 2 ^ ceilLog2 (shapeAt P k).maskRows < (shapeAt P k).maskRows
  · rw [if_pos hr, if_pos hr, hL]
    have hz : (shapeAt P k).maskRows ≠ 0 := by omega
    have hj : i / 2 ^ ceilLog2 (shapeAt P k).maskRows <
        (P.codes.mask.getD (shapeAt P k).maskCode default).ell := by
      have hK : ((shapeAt P k).maskRows != 0) = true := bne_iff_ne.2 hz
      have hK' : ((shapeAt P k).maskRows == 0) = false := beq_eq_false_iff_ne.2 hz
      have hs : (K1.Msg.of P.codes (shapeAt P k)).size .mask =
          2 ^ ceilLog2 (shapeAt P k).maskRows *
            2 ^ (P.codes.mask.getD (shapeAt P k).maskCode default).logEll := by
        rw [← Nat.pow_add]
        show (if ((shapeAt P k).maskRows != 0) = true then
          2 ^ (if ((shapeAt P k).maskRows == 0) = true then 0 else
            ceilLog2 (shapeAt P k).maskRows +
              (P.codes.mask.getD (shapeAt P k).maskCode default).logEll) else 0) = _
        rw [if_pos hK, hK', if_neg Bool.false_ne_true]
      rw [hs, h2] at hi
      exact Nat.div_lt_of_lt_mul hi
    exact mask_same P ride data c k high v cs hm hz hride hcs _ _ hr hj
  · rw [if_neg hr, if_neg hr, rdE.zero]

/-- A table of a message without such rows holds 0 in both texts. -/
theorem word_none_same (L : Nat → Laid) (i : Nat) (hz : (shapeAt P k).maskRows = 0) :
    (rowsR P ride data c k).word (shapeAt P k) .mask i = rdE.val (wordsOf P.sent L k .mask i) := by
  show (if i % 2 ^ ceilLog2 (shapeAt P k).maskRows < (shapeAt P k).maskRows then _ else 0) =
    rdE.val (if i % 2 ^ ceilLog2 (shapeAt P k).maskRows < (shapeAt P k).maskRows then _
      else zeroE)
  rw [hz, if_neg (Nat.not_lt_zero _), if_neg (Nat.not_lt_zero _), rdE.zero]

@[inherit_doc word_none_same]
theorem word_noMain_same (L : Nat → Laid) (i : Nat) (hm : (shapeAt P k).mainRows = 0) :
    (rowsR P ride data c k).word (shapeAt P k) .main i = rdE.val (wordsOf P.sent L k .main i) := by
  show (if i % 2 ^ ceilLog2 (shapeAt P k).mainRows < (shapeAt P k).mainRows then _ else 0) =
    rdE.val (if i % 2 ^ ceilLog2 (shapeAt P k).mainRows < (shapeAt P k).mainRows then _
      else zeroE)
  rw [hm, if_neg (Nat.not_lt_zero _), if_neg (Nat.not_lt_zero _), rdE.zero]

/-- **Where message number 1's coins begin**, behind a message number 0 (there is one: h0) that is
laid plainly, carries a vector over the extension field, has no mask row and has an OOD answer, and
on which no table rides (hr0): at the same number in both texts. -/
theorem start_one (sort : Nat → MsgSort) (high : Bool) (h0 : 0 < P.sent.size)
    (hs : sort 0 = .plain high) (hr0 : ride 0 = none) (h3 : (shapeAt P 0).mainDeg = 3)
    (hz : (shapeAt P 0).maskRows = 0) (ha : (shapeAt P 0).answers ≠ 0) :
    (startR P ride 1).e = offsetOf P.codes P.sent sort 1 := by
  have e1 : (startR P ride 1) =
      (⟨0, 0⟩ : Due).plus (ProofFile.Honest.K1.dueMsg P.codes (shapeAt P 0) (ride 0)) := rfl
  have e2 : offsetOf P.codes P.sent sort 1 = 0 + dueOf P.codes (shapeAt P 0) (sort 0) := by
    unfold offsetOf
    have ht : P.sent.toList.take 1 = [P.sent.getD 0 default] := by
      rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem h0, Option.getD_some]
      cases hl : P.sent.toList with
      | nil =>
        have hn : P.sent.toList.length = 0 := by rw [hl]; rfl
        rw [Array.length_toList] at hn
        omega
      | cons a l =>
        have : P.sent[0] = a := by
          rw [← Array.getElem_toList]
          simp [hl]
        rw [this]
        rfl
    rw [ht]
    rfl
  rw [e1, e2, hs]
  simp [ProofFile.Honest.K1.dueMsg, ProofFile.Honest.K1.Steps.main, ProofFile.Honest.K1.stepsOf, dueOf, h3, hz, ha,
    hr0]

end ProofFile.Honest.K14

#print axioms ProofFile.Honest.K14.val_coinsE
#print axioms ProofFile.Honest.K14.pad_count
#print axioms ProofFile.Honest.K14.main_same
#print axioms ProofFile.Honest.K14.mask_same
#print axioms ProofFile.Honest.K14.word_main_same
#print axioms ProofFile.Honest.K14.word_mask_same
#print axioms ProofFile.Honest.K14.word_none_same
#print axioms ProofFile.Honest.K14.word_noMain_same
#print axioms ProofFile.Honest.K14.start_one
