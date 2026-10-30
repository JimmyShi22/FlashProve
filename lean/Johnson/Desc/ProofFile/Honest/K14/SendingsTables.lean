-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K14/SendingsTables.lean: the tables that the two sendings' parts lay
with code (Honest/K14/Sendings.lean: laid, wordsOf), read into the library's field, are the tables
of Johnson/Desc/K14/Honest/SendMoves.lean (vecRows, coinRows) as the shared sending's core holds
them (Johnson/Prover/Send/Core.lean: Rows.word): entry by entry, at every index; for a main table
under the four premises on the message's shape that are named below. So, for the two tables of a
message laid of a vector and coins, it is said of every index which datum or which coin stands
there. OF A FOLD's FRESH TABLE LESS IS SAID: readFresh is defined as the reading of the mask rows
and tails that the part's own text lays there (laid at .fresh k h), so word_fresh_reads says only
that wordsOf and Rows.word cut an index into row and place alike, and that this table does not hang
on the vector; its entries are named by the part's own text, not by coin: which coin stands at an
entry is not said (it lies inside Fmt.M1.FoldOwn.freshRow, which laid calls). Two definitions with
code, and six statements with their proofs.

  split_unique    a row's number and a place are read off an index
  padCoin_ownPad  at the index of (row r, place j) of a message without a mask row: the pad's random
                  value number j - (ell - answers) if r is the last main row and j one of the last
                  places of the row, as many as there are OOD answers; nothing elsewhere
  readCoins       a message's coins, read, in the form of MsgCoins: which number stands for what
  laid_main_reads the main rows, read
  word_main_reads, word_mask_reads   the two tables of a message laid of a vector and coins, read,
                  at every index
  readFresh       the mask rows and tails that laid lays at a fold's fresh table, read, in the form
                  of MsgCoins; its fields tail and pad are 0
  word_fresh_reads   the mask table of a fold's fresh table, read: coinRows at the packed entries,
                  which are readFresh's, so the part's own

What is assumed, as premises. For the main table: the message has no mask row, has a main row, its
main rows are over the extension field, and its OOD answers are at most the code's message length.
Met by a default value in silence, and shut out by no premise: a code is read by
`codes.base.getD s.code default` or `codes.mask.getD s.maskCode default`: at a code's number beyond
its array it is the default code; a message's shape is read by `sent.getD k default`: at a number k
beyond the sending the statements speak of the default notice's shape.
What is not claimed. Every equation is between readings, not between the program's words. Nothing on
the columns or on the OOD answers. Nothing on a decision of the verifier, on how the coins are
distributed, on soundness or on hiding.
-/
import Johnson.Desc.ProofFile.Honest.K14.Sendings
import Johnson.Desc.K14.Honest.SendHeld

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K14
open OnBytes (E zeroE Codes OracleShape OracleNotice PadPlace vectorLay ceilLog2 thetaE)
open OnBytes.Slice (rdE)
open Desc.K14.Honest (MsgCoins ownPadPlaces padCoin vecMain vecRows coinRows padCoin_none
  ownPadPlaces_main)
open Johnson.Prover.Send (Rows)

/-- A row's number and a place are read off an index. -/
theorem split_unique (M r r' j j' : Nat) (hr : r < M) (hr' : r' < M)
    (h : r + j * M = r' + j' * M) : r = r' ∧ j = j' := by
  have h1 : (r + j * M) % M = (r' + j' * M) % M := by rw [h]
  rw [Nat.add_mul_mod_self_right, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hr,
    Nat.mod_eq_of_lt hr'] at h1
  subst h1
  exact ⟨rfl, Nat.eq_of_mul_eq_mul_right (Nat.lt_of_le_of_lt (Nat.zero_le _) hr)
    (Nat.add_left_cancel h)⟩

/-- **Where the pad stands in the main table of a message without a mask row**, which has a main
row, main rows over the extension field, and at most as many OOD answers as the code's message
length; at a row's number r below the rows' number rounded up to a power of two. The code is
`codes.base.getD s.code default`: the default code at a number beyond the array. -/
theorem padCoin_ownPad (codes : Codes) (s : OracleShape) (hz : s.maskRows = 0)
    (hm : 0 < s.mainRows) (hdeg : s.mainDeg = 3)
    (hlen : s.answers ≤ (codes.base.getD s.code default).ell) (pad : Nat → Cb.Gl.E) (r j : Nat)
    (hr : r < 2 ^ ceilLog2 s.mainRows) :
    padCoin (ownPadPlaces codes s) pad (r + j * 2 ^ ceilLog2 s.mainRows) =
      if r + 1 = s.mainRows ∧ (codes.base.getD s.code default).ell - s.answers ≤ j ∧
          j < (codes.base.getD s.code default).ell then
        some (pad (j - ((codes.base.getD s.code default).ell - s.answers))) else none := by
  have hP := ownPadPlaces_main codes s hz hm hdeg hlen
  have hlast : s.mainRows - 1 < 2 ^ ceilLog2 s.mainRows :=
    Nat.lt_of_lt_of_le (by omega) (VerifiableInference.Desc.Own.le_pow_ceil s.mainRows)
  by_cases c : r + 1 = s.mainRows ∧ (codes.base.getD s.code default).ell - s.answers ≤ j ∧
      j < (codes.base.getD s.code default).ell
  · rw [if_pos c]
    obtain ⟨c1, c2, c3⟩ := c
    have hi : j - ((codes.base.getD s.code default).ell - s.answers) < s.answers := by omega
    have hmem : (⟨.main, (s.mainRows - 1) + ((codes.base.getD s.code default).ell - s.answers +
        (j - ((codes.base.getD s.code default).ell - s.answers))) * 2 ^ ceilLog2 s.mainRows,
        j - ((codes.base.getD s.code default).ell - s.answers), thetaE 0⟩ : PadPlace) ∈
        ownPadPlaces codes s := by
      rw [hP]
      exact List.mem_map.2 ⟨_, List.mem_range.2 hi, rfl⟩
    have ht : r + j * 2 ^ ceilLog2 s.mainRows = (s.mainRows - 1) +
        ((codes.base.getD s.code default).ell - s.answers +
          (j - ((codes.base.getD s.code default).ell - s.answers))) * 2 ^ ceilLog2 s.mainRows := by
      have e1 : r = s.mainRows - 1 := by omega
      have e2 : (codes.base.getD s.code default).ell - s.answers +
          (j - ((codes.base.getD s.code default).ell - s.answers)) = j := by omega
      rw [e1, e2]
    cases e : (ownPadPlaces codes s).find?
        (fun q => q.part == .main && q.index == r + j * 2 ^ ceilLog2 s.mainRows) with
    | none =>
      have h := List.find?_eq_none.1 e _ hmem
      simp only [beq_self_eq_true, Bool.true_and, beq_iff_eq] at h
      exact absurd ht.symm h
    | some q =>
      have hq := List.find?_some e
      simp only [Bool.and_eq_true, beq_iff_eq] at hq
      have hq' := List.mem_of_find?_eq_some e
      rw [hP] at hq'
      obtain ⟨k, _, rfl⟩ := List.mem_map.1 hq'
      have hk := (split_unique _ _ _ _ _ hlast hlast (hq.2.trans ht)).2
      unfold padCoin
      rw [e, Option.map_some]
      show some (pad k) = _
      have : k = j - ((codes.base.getD s.code default).ell - s.answers) := by omega
      rw [this]
  · rw [if_neg c]
    refine padCoin_none _ _ _ fun p hp _ heq => c ?_
    rw [hP] at hp
    obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hp
    obtain ⟨e1, e2⟩ := split_unique _ _ _ _ _ hr hlast heq
    have hk' := List.mem_range.1 hk
    exact ⟨by omega, by omega, by omega⟩

/-- **A message's coins, read**, in the form of MsgCoins: of a message laid of a vector and coins.
cs: the message's coins, numbered from 0. The two codes are read with `getD … default`: at a code's
number beyond its array the default code's lengths are taken, in silence. -/
def readCoins (codes : Codes) (s : OracleShape) (cs : Nat → E) : MsgCoins :=
  let c := codes.base.getD s.code default
  let z := codes.mask.getD s.maskCode default
  let atPad := s.mainRows * c.r
  let atMask := atPad + (if s.maskRows == 0 then s.answers else 0)
  let atTail := atMask + s.maskRows * z.ell
  { tail := fun r t => rdE.val (cs (r * c.r + t))
    pad := fun i => rdE.val (cs (atPad + i))
    mask := fun r j => rdE.val (cs (atMask + j * s.maskRows + r))
    maskTail := fun r t => rdE.val (cs (atTail + r * z.r + t)) }

/-- The main rows of a message without a mask row, read; under the premises of padCoin_ownPad, with
the same default for the code. -/
theorem laid_main_reads (codes : Codes) (s : OracleShape) (high : Bool) (v cs : Nat → E)
    (hz : s.maskRows = 0) (hm : 0 < s.mainRows) (hdeg : s.mainDeg = 3)
    (hlen : s.answers ≤ (codes.base.getD s.code default).ell) (r j : Nat)
    (hr : r < 2 ^ ceilLog2 s.mainRows) :
    rdE.val ((laid codes s v cs (.plain high)).main r j) =
      vecMain (vectorLay codes s high) (ownPadPlaces codes s) (fun k => rdE.val (v k))
        (readCoins codes s cs).pad r j := by
  have hp := padCoin_ownPad codes s hz hm hdeg hlen (readCoins codes s cs).pad r j hr
  unfold vecMain
  rw [show (vectorLay codes s high).rowBits = ceilLog2 s.mainRows from rfl, hp]
  by_cases c : r + 1 = s.mainRows ∧ (codes.base.getD s.code default).ell - s.answers ≤ j ∧
      j < (codes.base.getD s.code default).ell
  · have hb : (s.maskRows == 0 && r + 1 == s.mainRows &&
        decide ((codes.base.getD s.code default).ell - s.answers ≤ j) &&
        decide (j < (codes.base.getD s.code default).ell)) = true := by
      simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq]
      exact ⟨⟨⟨hz, c.1⟩, c.2.1⟩, c.2.2⟩
    rw [if_pos c, Option.getD_some]
    show rdE.val (if _ then _ else _) = _
    rw [if_pos hb]
    rfl
  · have hb : ¬ (s.maskRows == 0 && r + 1 == s.mainRows &&
        decide ((codes.base.getD s.code default).ell - s.answers ≤ j) &&
        decide (j < (codes.base.getD s.code default).ell)) = true := by
      intro h
      simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
      exact c ⟨h.1.1.2, h.1.2, h.2⟩
    rw [if_neg c, Option.getD_none]
    show rdE.val (if _ then _ else _) = _
    rw [if_neg hb]
    rfl

/-- **The main table of a message laid of a vector and coins, read, at every index**, where the
message has no mask row, has a main row, has main rows over the extension field, and has at most as
many OOD answers as the code's message length. L, sent, k: the sending's rows, its notices, and the
message's number in it. The shape is `(sent.getD k default).shape`: at a k beyond the sending it is
the default notice's. -/
theorem word_main_reads (codes : Codes) (sent : Array OracleNotice) (L : Nat → Laid) (k : Nat)
    (high : Bool) (v cs : Nat → E)
    (hL : L k = laid codes (sent.getD k default).shape v cs (.plain high))
    (hz : (sent.getD k default).shape.maskRows = 0) (hm : 0 < (sent.getD k default).shape.mainRows)
    (hdeg : (sent.getD k default).shape.mainDeg = 3)
    (hlen : (sent.getD k default).shape.answers ≤
      (codes.base.getD (sent.getD k default).shape.code default).ell) (i : Nat) :
    rdE.val (wordsOf sent L k .main i) =
      (vecRows codes (sent.getD k default).shape high (fun n => rdE.val (v n))
        (readCoins codes (sent.getD k default).shape cs)).word (sent.getD k default).shape .main
        i := by
  have hd : ((sent.getD k default).shape.mainDeg == 3) = true := by
    rw [hdeg]
    rfl
  have hpos : 0 < 2 ^ ceilLog2 (sent.getD k default).shape.mainRows := Nat.two_pow_pos _
  show rdE.val (if _ then _ else _) = (if _ then _ else _)
  by_cases c : i % 2 ^ ceilLog2 (sent.getD k default).shape.mainRows <
      (sent.getD k default).shape.mainRows
  · have c' : i % 2 ^ VerifiableInference.Desc.K1.clog (sent.getD k default).shape.mainRows <
        (sent.getD k default).shape.mainRows := c
    rw [if_pos c, if_pos c', hL,
      laid_main_reads codes _ high v cs hz hm hdeg hlen _ _ (Nat.mod_lt _ hpos)]
    unfold Rows.main
    rw [if_pos hd]
    rfl
  · have c' : ¬ i % 2 ^ VerifiableInference.Desc.K1.clog (sent.getD k default).shape.mainRows <
        (sent.getD k default).shape.mainRows := c
    rw [if_neg c, if_neg c', rdE.zero]

/-- **The mask table of a message laid of a vector and coins, read, at every index**, and at every
`data`: the mask table does not hang on the vector. At a k beyond the sending the shape is the
default notice's. -/
theorem word_mask_reads (codes : Codes) (sent : Array OracleNotice) (L : Nat → Laid) (k : Nat)
    (high : Bool) (v cs : Nat → E) (data : Nat → Cb.Gl.E)
    (hL : L k = laid codes (sent.getD k default).shape v cs (.plain high)) (i : Nat) :
    rdE.val (wordsOf sent L k .mask i) =
      (vecRows codes (sent.getD k default).shape high data
        (readCoins codes (sent.getD k default).shape cs)).word (sent.getD k default).shape .mask
        i := by
  show rdE.val (if _ then _ else _) = (if _ then _ else _)
  by_cases c : i % 2 ^ ceilLog2 (sent.getD k default).shape.maskRows <
      (sent.getD k default).shape.maskRows
  · have c' : i % 2 ^ VerifiableInference.Desc.K1.clog (sent.getD k default).shape.maskRows <
        (sent.getD k default).shape.maskRows := c
    rw [if_pos c, if_pos c', hL]
    rfl
  · have c' : ¬ i % 2 ^ VerifiableInference.Desc.K1.clog (sent.getD k default).shape.maskRows <
        (sent.getD k default).shape.maskRows := c
    rw [if_neg c, if_neg c', rdE.zero]

/-- The entries and tails of a fold's fresh table, read, in the form of MsgCoins: by definition the
reading of the mask rows and tails that `laid` itself lays at `.fresh k h`, the packing included.
The fields tail and pad are 0. -/
def readFresh (codes : Codes) (s : OracleShape) (cs : Nat → E) (k h : Nat) : MsgCoins :=
  { tail := fun _ _ => 0, pad := fun _ => 0
    mask := fun r j => rdE.val ((laid codes s (fun _ => zeroE) cs (.fresh k h)).mask r j)
    maskTail := fun r t => rdE.val ((laid codes s (fun _ => zeroE) cs (.fresh k h)).maskTail r t) }

/-- **The mask table of a fold's fresh table, read, at every index**: it is coinRows at readFresh,
which is the part's own rows, read. So what is said is that the two texts cut an index into row and
place alike and that the table does not hang on v; which coin stands at an entry is not said. At an
n beyond the sending the shape is the default notice's. -/
theorem word_fresh_reads (codes : Codes) (sent : Array OracleNotice) (L : Nat → Laid) (n : Nat)
    (v cs : Nat → E) (k h : Nat)
    (hL : L n = laid codes (sent.getD n default).shape v cs (.fresh k h)) (i : Nat) :
    rdE.val (wordsOf sent L n .mask i) =
      (coinRows (readFresh codes (sent.getD n default).shape cs k h)).word
        (sent.getD n default).shape .mask i := by
  show rdE.val (if _ then _ else _) = (if _ then _ else _)
  by_cases c : i % 2 ^ ceilLog2 (sent.getD n default).shape.maskRows <
      (sent.getD n default).shape.maskRows
  · have c' : i % 2 ^ VerifiableInference.Desc.K1.clog (sent.getD n default).shape.maskRows <
        (sent.getD n default).shape.maskRows := c
    rw [if_pos c, if_pos c', hL]
    rfl
  · have c' : ¬ i % 2 ^ VerifiableInference.Desc.K1.clog (sent.getD n default).shape.maskRows <
        (sent.getD n default).shape.maskRows := c
    rw [if_neg c, if_neg c', rdE.zero]

end ProofFile.Honest.K14

#print axioms ProofFile.Honest.K14.split_unique
#print axioms ProofFile.Honest.K14.padCoin_ownPad
#print axioms ProofFile.Honest.K14.laid_main_reads
#print axioms ProofFile.Honest.K14.word_main_reads
#print axioms ProofFile.Honest.K14.word_mask_reads
#print axioms ProofFile.Honest.K14.word_fresh_reads
