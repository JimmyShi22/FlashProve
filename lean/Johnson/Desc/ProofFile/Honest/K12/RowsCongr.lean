-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/RowsCongr.lean: a sending's rows of one message read, of the
part's coins, that message's own stretch alone. `rowsR`
(Johnson/Desc/ProofFile/Honest/K1/Coins.lean) makes message number k's rows of the caller's data and
the part's whole purse; here: two purses that agree on the message's stretch (from `startR` on,
`dueMsg` coins of each field) give the same rows, as functions. So the rows that a proximity test's
job makes anew of a carried stretch (`OneSent.mem`, JobOne.lean in this folder) are the sender's
own, where that stretch is the sender's purse cut at the message. In Lean the statement on two
purses is `rowsR_congr`, general in the sending's public numbers P, in ride, in the caller's data,
in the two purses and in the message's number k. The statement on the job's rows is `mem_is_sent`,
at message number 0, general in Q, w, S and c; `same_one` (SameAtOne.lean in this folder) calls it.
Theorems with their proofs; no definition.

In the list: a sending is a sub-protocol of the kind K1. P (`K1.Par`, Johnson/Desc/K1/Send.lean)
holds its public numbers, and `shapeAt P k` (Johnson/Prover/Send/Core.lean) is the shape of its
message number k. `Rows` (Core.lean) is what a sending's caller supplies for one oracle message, six
functions: its main rows and their tails, each over the extension field and over the base field, its
mask rows and their tails. ride gives, at a message's number, the two numbers of a table that rides
in that message (`Ride`), or none. A part (`Part`, in the frame,
Johnson/Desc/ProofFile/Honest/Frame.lean) is the prover's side of a stretch of a sub-protocol's
rounds. Coins (`Cs d`, the frame) are elements of the base field and of the extension field, as many
as the count d states (`Due`: fields `f` and `e`). The part's purse is here a value c of
`Cs (dueR P ride)`, coins of the whole sending's count; the word does not mean the frame's type
`Purse`. `cf c i` and `ce c i` are its coins number i of the two fields, 0 beyond the count. Message
number k's stretch of a purse is, in each field, the `dueMsg P.codes (shapeAt P k) (ride k)` coins
from number `startR P ride k` on. `Ride`, `dueR`, `cf`, `ce`, `dueMsg` and `startR` are in
K1/Coins.lean. A stretch S (`Stretch`, Coins.lean in this folder) is a run of coins, read by number
(`S.f i`, `S.e i`), and `csOfStretch d S` (JobOne.lean) are the coins of the count d read off it. A
job (`TestJob`, Test.lean in this folder) is what a caller supplies for its proximity test; its
members are the oracle messages of the group under test. Q (`OneSent`, JobOne.lean) is what
`jobOne` (JobOne.lean) takes of a sending; that job's one member is the sending's message 0. w is
the prover's input. The member's rows are `Q.mem w S`: `rowsR` at `Q.P`, `Q.ride`, `Q.data w`,
message number 0 and the coins `csOfStretch _ S`. The sender's purse is c, and the sender's rows of
message 0 are `rowsR Q.P Q.ride (Q.data w) c 0`.

  `rowsR_congr`: under hf and he below, `rowsR P ride data c k` is `rowsR P ride data c' k`
  `mem_is_sent`: the sender's purse agrees with the stretch on message 0's coins ⟹ the sender's
    rows of message 0 are the job's member's rows. In Lean, under hf and he below:
    `rowsR Q.P Q.ride (Q.data w) c 0` is `Q.mem w S`
  `cf_stretch`, `ce_stretch`: a purse made of a stretch holds the stretch's coins. In Lean: at i
    below the count d of the field, coin number i of `csOfStretch d S` is the value of S at i
  `rows_ext`: two values of `Rows` whose six fields are equal are equal
  `rowIdx_lt`: r < R and q < Q give r * Q + q < R * Q

By what. `rowsR_congr` unfolds `rowsR`, `dueMsg` and `stepsOf` (K1/Coins.lean) and compares the six
fields one by one (`rows_ext`). In each field, every number at which a coin is read is the stretch's
start plus a number below the message's count, by `rowIdx_lt` and arithmetic. `mem_is_sent` is
`rowsR_congr` at k = 0 and c' = `csOfStretch _ S`, with `cf_stretch` and `ce_stretch`.

Hypotheses. Of `rowsR_congr`. hf: at every i below the `f` of message k's count, `cf c` and `cf c'`
agree at `(startR P ride k).f + i`. he: the same for `ce` and `e`. Of `mem_is_sent`. hf: at every i
below the `f` of message 0's count, `cf c i` is `S.f i`. he: the same for `ce`, `e` and `S.e`.

Limits.
- That a carried stretch holds the sender's coins is asked: a matter of the book. In Lean these are
  the hypotheses hf and he of `mem_is_sent`. They are proved nowhere in this file; c and S are free
  parameters, and no book (`ProverCoinCounts`, the frame) occurs in it.
- `mem_is_sent` is stated at message number 0 only.
- No hypothesis says that message 0's count lies within the whole sending's count. At a number
  beyond the latter `cf` and `ce` give 0: hf and he then say that the value of S is 0, and a row
  that reads there reads, on both sides of `mem_is_sent`, a 0 in a coin's place.
- `rowsR_congr` bounds what the rows depend on. It does not say that any coin of the stretch is
  read, or at how many entries one is read.
- The option `maxHeartbeats` is raised to 1000000 for the whole file.
- Nothing on completeness, on soundness or on what is hidden.
-/
import Johnson.Desc.ProofFile.Honest.K12.JobOne

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace ProofFile.Honest.K12
open OnBytes OnBytes.Slice Cb
open VerifiableInference.Desc
open Johnson.Prover.Send (Rows shapeAt)
open ProofFile.Honest.K1 (Ride rowsR dueR dueMsg startR cf ce)

theorem rowIdx_lt {r q R Q : ℕ} (hr : r < R) (hq : q < Q) : r * Q + q < R * Q :=
  calc r * Q + q < r * Q + Q := Nat.add_lt_add_left hq _
    _ = (r + 1) * Q := (Nat.succ_mul r Q).symm
    _ ≤ R * Q := Nat.mul_le_mul_right Q hr

/-- Two values of `Rows` whose six fields are equal are equal. -/
theorem rows_ext (A B : Rows) (h1 : A.mainE = B.mainE) (h2 : A.mainF = B.mainF)
    (h3 : A.mainTlE = B.mainTlE) (h4 : A.mainTlF = B.mainTlF) (h5 : A.mask = B.mask)
    (h6 : A.maskTl = B.maskTl) : A = B := by
  cases A
  cases B
  simp only at h1 h2 h3 h4 h5 h6
  subst h1 h2 h3 h4 h5 h6
  rfl

section
variable (P : K1.Par) (ride : ℕ → Option Ride) (data : ℕ → ℕ → ℕ → Option (GF ⊕ GE))
  (c c' : Cs (dueR P ride)) (k : ℕ)

/-- **A message's rows read its own stretch alone.** c, c': two purses. hf, he: they agree, in each
field, on the coins of message number k. -/
theorem rowsR_congr
    (hf : ∀ i, i < (dueMsg P.codes (shapeAt P k) (ride k)).f →
      cf c ((startR P ride k).f + i) = cf c' ((startR P ride k).f + i))
    (he : ∀ i, i < (dueMsg P.codes (shapeAt P k) (ride k)).e →
      ce c ((startR P ride k).e + i) = ce c' ((startR P ride k).e + i)) :
    rowsR P ride data c k = rowsR P ride data c' k := by
  -- names for the shape s, the two codes C and Z, and the message's five counts n
  generalize hs : shapeAt P k = s at hf he
  generalize hC : P.codes.base.getD s.code default = C
  generalize hZ : P.codes.mask.getD s.maskCode default = Z
  have hn : K1.stepsOf P.codes s (ride k) =
      { tails := s.mainRows * C.r
        word := if s.mainRows != 0 && s.answers == 0 then s.mainRows * C.ell else 0
        pad := if s.maskRows == 0 && s.answers != 0 then
          (if s.mainDeg == 3 then 1 else 3) * s.answers else 0
        mask := ((ride k).map (·.count)).getD (s.maskRows * Z.ell)
        maskTails := s.maskRows * Z.r } := by
    unfold K1.stepsOf
    rw [hC, hZ]
  generalize hN : K1.stepsOf P.codes s (ride k) = n at hn
  have hdue : dueMsg P.codes s (ride k) =
      if s.mainDeg == 3 then ⟨0, n.main + n.mask + n.maskTails⟩
      else ⟨n.main, n.mask + n.maskTails⟩ := by
    unfold dueMsg
    rw [hN]
  rw [hdue] at hf he
  have htl : n.tails = s.mainRows * C.r := by rw [hn]
  have hmt : n.maskTails = s.maskRows * Z.r := by rw [hn]
  have hmain : n.main = n.tails + n.word + n.pad := rfl
  -- the number i of a coin in a main row's message is below `n.main`
  have hcoin : ∀ r j i, r < s.mainRows → j < C.ell →
      (if n.word != 0 then (if j < C.ell then some (n.tails + r * C.ell + j) else none)
        else ((if n.pad != 0 && r + 1 == s.mainRows && decide (C.ell - n.pad ≤ j) &&
          decide (j < C.ell) then some (j - (C.ell - n.pad)) else none).map (n.tails + ·))) =
        some i → i < n.main := by
    intro r j i hr hj h
    by_cases hw : (n.word != 0) = true
    · rw [if_pos hw, if_pos hj] at h
      obtain rfl := Option.some.inj h
      have hw' : n.word = s.mainRows * C.ell := by
        have e : n.word = if s.mainRows != 0 && s.answers == 0 then s.mainRows * C.ell else 0 := by
          rw [hn]
        split at e
        · exact e
        · rw [e] at hw
          simp at hw
      have := rowIdx_lt hr hj
      omega
    · rw [if_neg hw] at h
      split at h
      · rename_i hp
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hp
        have h' : n.tails + (j - (C.ell - n.pad)) = i := Option.some.inj h
        have h1 := hp.1.2
        omega
      · cases h
  -- he and hf, restated over the ranges of numbers at which the rows read
  have hE : ∀ i, i < (if (s.mainDeg == 3) = true then n.main else 0) + n.mask + n.maskTails →
      ce c ((startR P ride k).e + i) = ce c' ((startR P ride k).e + i) := by
    intro i hi
    refine he i ?_
    by_cases ho : (s.mainDeg == 3) = true
    · rw [if_pos ho] at hi ⊢
      exact hi
    · rw [if_neg ho] at hi ⊢
      show i < n.mask + n.maskTails
      omega
  have hF : (s.mainDeg == 3) = false → ∀ i, i < n.main →
      cf c ((startR P ride k).f + i) = cf c' ((startR P ride k).f + i) := by
    intro ho i hi
    refine hf i ?_
    rw [if_neg (by rw [ho]; exact Bool.false_ne_true)]
    exact hi
  refine rows_ext _ _ ?_ ?_ ?_ ?_ ?_ ?_
  · funext r j
    simp only [rowsR, hs, hC, hZ, hN]
    split
    · rfl
    · rename_i hg
      simp only [Bool.or_eq_true, decide_eq_true_eq, not_or, Nat.not_le, Bool.not_eq_true',
        Bool.not_eq_false] at hg
      split
      · rename_i i hi
        refine hE i ?_
        rw [if_pos hg.1.1]
        have := hcoin r j i hg.1.2 hg.2 hi
        omega
      · rfl
  · funext r j
    simp only [rowsR, hs, hC, hZ, hN]
    split
    · rfl
    · rename_i hg
      simp only [Bool.or_eq_true, decide_eq_true_eq, not_or, Nat.not_le, Bool.not_eq_true] at hg
      split
      · rename_i i hi
        exact hF hg.1.1 i (hcoin r j i hg.1.2 hg.2 hi)
      · rfl
  · funext r q
    simp only [rowsR, hs, hC, hZ, hN]
    split
    · rename_i hg
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hg
      have := rowIdx_lt hg.1.2 hg.2
      rw [Nat.add_assoc]
      refine hE _ ?_
      rw [if_pos hg.1.1]
      omega
    · rfl
  · funext r q
    simp only [rowsR, hs, hC, hZ, hN]
    split
    · rename_i hg
      simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at hg
      have := rowIdx_lt hg.1.2 hg.2
      rw [Nat.add_assoc]
      exact hF hg.1.1 _ (by omega)
    · rfl
  · funext r j
    simp only [rowsR, hs, hC, hZ, hN]
    cases hR : ride k with
    | some R =>
      have hm : n.mask = R.count := by rw [hn, hR]; rfl
      simp only
      split
      · congr 1
        funext i
        split
        · rename_i hi
          rw [Nat.add_assoc]
          exact hE _ (by omega)
        · rfl
      · rfl
    | none =>
      have hm : n.mask = s.maskRows * Z.ell := by rw [hn, hR]; rfl
      simp only
      split
      · rename_i hg
        have := rowIdx_lt hg.2 hg.1
        rw [Nat.add_assoc, Nat.add_assoc]
        exact hE _ (by rw [hm, Nat.mul_comm s.maskRows]; omega)
      · rfl
  · funext r q
    simp only [rowsR, hs, hC, hZ, hN]
    split
    · rename_i hg
      have := rowIdx_lt hg.1 hg.2
      rw [Nat.add_assoc, Nat.add_assoc, Nat.add_assoc]
      exact hE _ (by omega)
    · rfl

end

theorem cf_stretch (d : Due) (S : Stretch) (i : ℕ) (h : i < d.f) :
    cf (csOfStretch d S) i = S.f i := by
  unfold cf
  rw [dif_pos h]
  rfl

theorem ce_stretch (d : Due) (S : Stretch) (i : ℕ) (h : i < d.e) :
    ce (csOfStretch d S) i = S.e i := by
  unfold ce
  rw [dif_pos h]
  rfl

/-- **The job's member's rows are the sender's rows of message 0**, where the sender's purse agrees
with the stretch on that message's coins. c: the sender's purse. S: the stretch. -/
theorem mem_is_sent {W : Type} (Q : OneSent W) (w : W) (S : Stretch) (c : Cs (dueR Q.P Q.ride))
    (hf : ∀ i, i < (dueMsg Q.P.codes (shapeAt Q.P 0) (Q.ride 0)).f → cf c i = S.f i)
    (he : ∀ i, i < (dueMsg Q.P.codes (shapeAt Q.P 0) (Q.ride 0)).e → ce c i = S.e i) :
    rowsR Q.P Q.ride (Q.data w) c 0 = Q.mem w S := by
  refine rowsR_congr Q.P Q.ride (Q.data w) c (csOfStretch _ S) 0 (fun i hi => ?_) fun i hi => ?_
  · show cf c (0 + i) = cf (csOfStretch _ S) (0 + i)
    rw [Nat.zero_add]
    by_cases h : i < (dueR Q.P Q.ride).f
    · rw [cf_stretch _ S i h, hf i hi]
    · unfold cf
      rw [dif_neg h, dif_neg h]
  · show ce c (0 + i) = ce (csOfStretch _ S) (0 + i)
    rw [Nat.zero_add]
    by_cases h : i < (dueR Q.P Q.ride).e
    · rw [ce_stretch _ S i h, he i hi]
    · unfold ce
      rw [dif_neg h, dif_neg h]

end ProofFile.Honest.K12

#print axioms ProofFile.Honest.K12.mem_is_sent
#print axioms ProofFile.Honest.K12.rowIdx_lt
#print axioms ProofFile.Honest.K12.rows_ext
#print axioms ProofFile.Honest.K12.rowsR_congr
#print axioms ProofFile.Honest.K12.cf_stretch
#print axioms ProofFile.Honest.K12.ce_stretch
