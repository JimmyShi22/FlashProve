-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K6/GoodRounds.lean: the rounds that the tests `goodK6` and `goodK6Nz`
(Honest/K6/Good.lean) read, by number, and what the plan's entries say of these rounds. Definitions
with code, statements and proofs, and tests; general in the place's public numbers.

Why. Whoever holds a share against the test "`goodK6` says no" counts, round by round, how many
challenges show the one bad value. For that the test has to be an "or" over named rounds, each of
which draws one element. This file says so much and no more.

  `goodRounds p`    the numbers of the 4 lt + 2 lPd + 2 rounds whose first drawn element `goodK6`
                    reads, rising
  `nzRounds p`      the numbers of the four rounds in the further variable
  `goodRounds_length`, `goodRounds_rise`, `goodRounds_nodup`   as many as `goodK6Events` says;
                    rising; so no number twice
  `goodK6_iff`, `goodK6_no_iff`   **`goodK6` says no just if at one of these rounds the first drawn
                    element is 0**
  `goodK6Nz_iff`    the like for the four
  `headDrawsAt p r` how many elements the declared round number r draws, and how many of them by the
                    rule that never gives 0
  `goodRounds_draw` **each round of `goodRounds` draws just one element, and not by that rule**
  `nzRounds_draw`   **each of the four draws just one element, by that rule**

Limits. "Is 0" compares words (Good.lean's Limits). `elemOf` yields 0 too where the list does not
hold the round, or the round draws nothing: so the tests say no at a SHORT list as well: whoever
counts by `goodK6_no_iff` needs lists of the full length. That number r of the list `own` is the
draw of the declared round number r is Good.lean's convention (own: from the sub-protocol's first
round on), no theorem here. NOTHING ON A SPACE OF CHALLENGES, on how a challenge is drawn or shown,
or on any share: that a round whose entry bears the flag never shows 0 is not said here. The
declared rounds are `Head.Par.rounds` (Johnson/Desc/Kinds/HeadKind.lean); that a description seats
them at a place is not said here. Nothing on `linkedK6`.
Nothing on any property.

-/
import Johnson.Desc.ProofFile.Honest.K6.Good
import Johnson.Desc.Kinds.HeadKind

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K6
open OnBytes (E isZeroE)
open VerifiableInference.Desc.Kinds (Round Head.Par drawPoint.rounds sendThenBatch.rounds
  level.rounds sumcheck.rounds)

/-! ## 1 The rounds that the tests read, by number -/

/-- **The numbers of the rounds whose first drawn element `goodK6` reads**, rising: the variables'
rounds of the first and of the second sumcheck; the first round and the variables' rounds of the
third and of the fourth. -/
def goodRounds (p : Head.Par) : List Nat :=
  (List.range (headLPd p + headLt p)).map (headInFront p 2 + 1 + ·) ++
    (List.range (headLt p)).map (headInFront p 5 + 1 + ·) ++
    (List.range (headLt p + 1)).map (headInFront p 6 + ·) ++
    (List.range (headLPd p + headLt p + 1)).map (headInFront p 7 + ·)

/-- The numbers of the four rounds in the further variable, which `goodK6Nz` reads. -/
def nzRounds (p : Head.Par) : List Nat :=
  [headInFront p 2 + 1 + (headLPd p + headLt p), headInFront p 5 + 1 + headLt p,
    headInFront p 6 + 1 + headLt p, headInFront p 7 + 1 + (headLPd p + headLt p)]

theorem headInFront_at (p : Head.Par) :
    headInFront p 2 = 2 ∧ headInFront p 5 = headLPd p + headLt p + 7 ∧
    headInFront p 6 = headLPd p + 2 * headLt p + 10 ∧
    headInFront p 7 = headLPd p + 3 * headLt p + 13 := by
  have e2 : headInFront p 2 = 0 + 1 + 1 := rfl
  have e5 : headInFront p 5 = 0 + 1 + 1 + (headLPd p + headLt p + 3) + 1 + 1 := rfl
  have e6 : headInFront p 6 = 0 + 1 + 1 + (headLPd p + headLt p + 3) + 1 + 1 + (headLt p + 3) := rfl
  have e7 : headInFront p 7 =
      0 + 1 + 1 + (headLPd p + headLt p + 3) + 1 + 1 + (headLt p + 3) + (headLt p + 3) := rfl
  exact ⟨by omega, by omega, by omega, by omega⟩

/-- As many as the count of events says. -/
theorem goodRounds_length (p : Head.Par) : (goodRounds p).length = goodK6Events p := by
  unfold goodRounds goodK6Events
  simp only [List.length_append, List.length_map, List.length_range]
  omega

theorem mem_goodRounds (p : Head.Par) (r : Nat) : r ∈ goodRounds p ↔
    (∃ j, j < headLPd p + headLt p ∧ r = headInFront p 2 + 1 + j) ∨
    (∃ j, j < headLt p ∧ r = headInFront p 5 + 1 + j) ∨
    (∃ j, j < headLt p + 1 ∧ r = headInFront p 6 + j) ∨
    (∃ j, j < headLPd p + headLt p + 1 ∧ r = headInFront p 7 + j) := by
  unfold goodRounds
  simp only [List.mem_append, List.mem_map, List.mem_range, or_assoc, eq_comm]

/-- **They rise: so no number stands twice.** -/
theorem goodRounds_rise (p : Head.Par) : (goodRounds p).Pairwise (· < ·) := by
  obtain ⟨f2, f5, f6, f7⟩ := headInFront_at p
  have up : ∀ (n a : Nat), ((List.range n).map (a + ·)).Pairwise (· < ·) := fun n a => by
    rw [List.pairwise_map]
    exact List.pairwise_lt_range.imp fun h => by omega
  unfold goodRounds
  simp only [List.pairwise_append, List.mem_append, List.mem_map, List.mem_range]
  refine ⟨⟨⟨up _ _, up _ _, ?_⟩, up _ _, ?_⟩, up _ _, ?_⟩
  · rintro a ⟨i, hi, rfl⟩ b ⟨j, hj, rfl⟩
    omega
  · rintro a (⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩) b ⟨j, hj, rfl⟩ <;> omega
  · rintro a ((⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩) | ⟨i, hi, rfl⟩) b ⟨j, hj, rfl⟩ <;> omega

theorem goodRounds_nodup (p : Head.Par) : (goodRounds p).Nodup :=
  (goodRounds_rise p).imp fun h => Nat.ne_of_lt h

/-! ## 2 The tests, in these rounds -/

theorem headAll_zipIdx {α : Type} (ok : α → Bool) : ∀ (l : List α) (k : Nat),
    (l.zipIdx k).all (fun x => ok x.1) = l.all ok
  | [], _ => rfl
  | a :: l, k => by
    rw [List.zipIdx_cons, List.all_cons, List.all_cons, headAll_zipIdx ok l (k + 1)]

theorem headClausesOn_all (what ask : String) (ok : E → Bool)
    (z : VerifiableInference.Desc.Kinds.Point) :
    (headClausesOn what ask ok z).all (·.2) = z.toList.all ok := by
  unfold headClausesOn
  rw [List.all_map]
  exact headAll_zipIdx ok z.toList 0

theorem headSumR_all (p : Head.Par) (i n : Nat) (own : List Fmt.Drawn) :
    (headSumR p i n own).toList.all (!isZeroE ·) = true ↔
      ∀ j, j < n → isZeroE (elemOf own (headInFront p i + 1 + j)) = false := by
  unfold headSumR
  simp only [List.all_eq_true, List.mem_map, List.mem_range, Bool.not_eq_true']
  constructor
  · intro h j hj
    exact h _ ⟨j, hj, rfl⟩
  · rintro h x ⟨j, hj, rfl⟩
    exact h j hj

/-- **`goodK6` says yes just if at none of these rounds the first drawn element is 0.** -/
theorem goodK6_iff (p : Head.Par) (own : List Fmt.Drawn) :
    goodK6 p own = true ↔ ∀ r ∈ goodRounds p, isZeroE (elemOf own r) = false := by
  unfold goodK6 goodK6Clauses
  simp only [List.all_append, Bool.and_eq_true, headClausesOn_all, List.all_cons, List.all_nil,
    Bool.and_true, headSumR_all, Bool.not_eq_true']
  constructor
  · rintro ⟨⟨⟨⟨a2, a5⟩, a6⟩, a7⟩, e6, e7⟩ r hr
    rcases (mem_goodRounds p r).1 hr with ⟨j, hj, rfl⟩ | ⟨j, hj, rfl⟩ | ⟨j, hj, rfl⟩ | ⟨j, hj, rfl⟩
    · exact a2 j hj
    · exact a5 j hj
    · cases j with
      | zero => exact e6
      | succ j =>
        rw [show headInFront p 6 + (j + 1) = headInFront p 6 + 1 + j by omega]
        exact a6 j (by omega)
    · cases j with
      | zero => exact e7
      | succ j =>
        rw [show headInFront p 7 + (j + 1) = headInFront p 7 + 1 + j by omega]
        exact a7 j (by omega)
  · intro h
    refine ⟨⟨⟨⟨fun j hj => ?_, fun j hj => ?_⟩, fun j hj => ?_⟩, fun j hj => ?_⟩, ?_, ?_⟩
    · exact h _ ((mem_goodRounds p _).2 (Or.inl ⟨j, hj, rfl⟩))
    · exact h _ ((mem_goodRounds p _).2 (Or.inr (Or.inl ⟨j, hj, rfl⟩)))
    · exact h _ ((mem_goodRounds p _).2 (Or.inr (Or.inr (Or.inl ⟨j + 1, by omega, by omega⟩))))
    · exact h _ ((mem_goodRounds p _).2 (Or.inr (Or.inr (Or.inr ⟨j + 1, by omega, by omega⟩))))
    · exact h _ ((mem_goodRounds p _).2 (Or.inr (Or.inr (Or.inl ⟨0, by omega, rfl⟩))))
    · exact h _ ((mem_goodRounds p _).2 (Or.inr (Or.inr (Or.inr ⟨0, by omega, rfl⟩))))

/-- **It says no just if at one of them the first drawn element is 0.** -/
theorem goodK6_no_iff (p : Head.Par) (own : List Fmt.Drawn) :
    goodK6 p own = false ↔ ∃ r ∈ goodRounds p, isZeroE (elemOf own r) = true := by
  constructor
  · intro h
    refine Classical.byContradiction fun hn => ?_
    have hy : goodK6 p own = true := (goodK6_iff p own).2 fun r hr => by
      cases hz : isZeroE (elemOf own r) with
      | false => rfl
      | true => exact absurd ⟨r, hr, hz⟩ hn
    rw [hy] at h
    cases h
  · rintro ⟨r, hr, hz⟩
    cases hg : goodK6 p own with
    | false => rfl
    | true =>
      rw [(goodK6_iff p own).1 hg r hr] at hz
      cases hz

/-- `goodK6Nz` says yes just if at none of the four rounds in the further variable the first drawn
element is 0. -/
theorem goodK6Nz_iff (p : Head.Par) (own : List Fmt.Drawn) :
    goodK6Nz p own = true ↔ ∀ r ∈ nzRounds p, isZeroE (elemOf own r) = false := by
  unfold goodK6Nz goodK6NzClauses nzRounds
  simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true, Bool.not_eq_true',
    List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]

/-! ## 3 What the plan's entries say of these rounds -/

/-- The sub-protocol's rounds as data, of the two logarithms. -/
def headRoundsOf (lt lPd : Nat) : List Round :=
  drawPoint.rounds lt ++ (sendThenBatch.rounds 9 9 ++ (level.rounds (lPd + lt) ++
    (sendThenBatch.rounds 7 7 ++ (sumcheck.rounds lt 4 ++ (sumcheck.rounds lt 2 ++
      sumcheck.rounds (lt + lPd) 2)))))

/-- The declared rounds are these, each with its entry. -/
theorem headRounds_are (p : Head.Par) : p.rounds =
    (headRoundsOf (headLt p) (headLPd p)).map fun r => { entry := r.entry p.work } := by
  show (drawPoint.rounds (headLt p) ++ sendThenBatch.rounds 9 9 ++ [] ++
    level.rounds (0 + headLPd p + headLt p) ++ sendThenBatch.rounds 7 7 ++
    sumcheck.rounds (headLt p) 4 ++ sumcheck.rounds (headLt p) 2 ++
    sumcheck.rounds (headLt p + headLPd p) 2).map
      (fun (r : Round) => ({ entry := r.entry p.work } : Fmt.DeclaredRound)) = _
  unfold headRoundsOf
  rw [Nat.zero_add]
  simp only [List.append_assoc, List.append_nil]

/-- How many elements a declared round draws, and how many of them by the rule that never gives 0.
-/
def headDrawsAt (p : Head.Par) (r : Nat) : Option (Nat × Nat) :=
  (p.rounds[r]?).map fun d => (d.entry.drawE, d.entry.drawNZ)

theorem headMid_at {α : Type} (A S B : List α) (k : Nat) (hk : k < S.length) :
    (A ++ (S ++ B))[A.length + k]? = S[k]? := by
  rw [List.getElem?_append_right (by omega), Nat.add_sub_cancel_left,
    List.getElem?_append_left hk]

theorem headRun_var {α : Type} (e v y : α) (m : Nat) (tl : List α) (j : Nat) (hj : j < m) :
    (e :: List.replicate m v ++ (y :: tl))[j + 1]? = some v := by
  show (List.replicate m v ++ (y :: tl))[j]? = some v
  rw [List.getElem?_append_left (by simpa using hj)]
  simp [hj]

theorem headRun_last {α : Type} (e v y : α) (m : Nat) (tl : List α) :
    (e :: List.replicate m v ++ (y :: tl))[m + 1]? = some y := by
  show (List.replicate m v ++ (y :: tl))[m]? = some y
  rw [List.getElem?_append_right (by simp)]
  simp

/-- A stretch "first round, m rounds alike, one more, a tail" inside a list: its first round, the m,
and the one more, by number. -/
theorem headStretch_at {α : Type} (A B : List α) (e v y : α) (m : Nat) (tl : List α) :
    (A ++ ((e :: List.replicate m v ++ (y :: tl)) ++ B))[A.length + 0]? = some e ∧
    (∀ j, j < m →
      (A ++ ((e :: List.replicate m v ++ (y :: tl)) ++ B))[A.length + (j + 1)]? = some v) ∧
    (A ++ ((e :: List.replicate m v ++ (y :: tl)) ++ B))[A.length + (m + 1)]? = some y := by
  have hl : (e :: List.replicate m v ++ (y :: tl)).length = m + 2 + tl.length := by
    simp
    omega
  refine ⟨?_, fun j hj => ?_, ?_⟩
  · rw [headMid_at _ _ _ 0 (by omega)]
    rfl
  · rw [headMid_at _ _ _ (j + 1) (by omega)]
    exact headRun_var e v y m tl j hj
  · rw [headMid_at _ _ _ (m + 1) (by omega)]
    exact headRun_last e v y m tl

theorem headLevel_length (m : Nat) : (level.rounds m).length = m + 4 := by
  simp [level.rounds]

theorem headSumcheck_length (m e : Nat) : (sumcheck.rounds m e).length = m + 3 := by
  simp [sumcheck.rounds]

/-- A variable's round, the round in the further variable, and the first round of a sumcheck that
sends its claimed sum, as data. -/
def headVarRound : Round := ⟨"PSC round", 2, 1, false, 0⟩
@[inherit_doc headVarRound] def headLastRound : Round := ⟨"PSC Y", 2, 1, true, 0⟩
@[inherit_doc headVarRound] def headFirstRound : Round := ⟨"PSC epsilon", 2, 1, false, 0⟩

/-- The first sumcheck's rounds in the list. -/
theorem headRounds_at2 (a c : Nat) :
    (∀ j, j < c + a → (headRoundsOf a c)[2 + 1 + j]? = some headVarRound) ∧
    (headRoundsOf a c)[2 + 1 + (c + a)]? = some headLastRound := by
  have D : headRoundsOf a c = (drawPoint.rounds a ++ sendThenBatch.rounds 9 9) ++
      (level.rounds (c + a) ++ (sendThenBatch.rounds 7 7 ++ (sumcheck.rounds a 4 ++
        (sumcheck.rounds a 2 ++ sumcheck.rounds (a + c) 2)))) := by
    unfold headRoundsOf
    simp only [List.append_assoc]
  have S := headStretch_at (drawPoint.rounds a ++ sendThenBatch.rounds 9 9)
    (sendThenBatch.rounds 7 7 ++ (sumcheck.rounds a 4 ++
      (sumcheck.rounds a 2 ++ sumcheck.rounds (a + c) 2)))
    ⟨"PSC epsilon", 1, 1, false, 0⟩ headVarRound headLastRound (c + a)
    [⟨"PSC values", 2, 0, false, 0⟩, ⟨"LINE", 0, 1, false, 0⟩]
  have hA : (drawPoint.rounds a ++ sendThenBatch.rounds 9 9).length = 2 := rfl
  rw [hA] at S
  rw [D]
  refine ⟨fun j hj => ?_, ?_⟩
  · rw [show 2 + 1 + j = 2 + (j + 1) by omega]
    exact S.2.1 j hj
  · rw [show 2 + 1 + (c + a) = 2 + (c + a + 1) by omega]
    exact S.2.2

/-- A later sumcheck's rounds in a list, behind f rounds. -/
theorem headRounds_sum (A B : List Round) (m e f : Nat) (hA : A.length = f) :
    (A ++ (sumcheck.rounds m e ++ B))[f]? = some headFirstRound ∧
    (∀ j, j < m → (A ++ (sumcheck.rounds m e ++ B))[f + 1 + j]? = some headVarRound) ∧
    (A ++ (sumcheck.rounds m e ++ B))[f + 1 + m]? = some headLastRound := by
  have S := headStretch_at A B headFirstRound headVarRound headLastRound m
    [⟨"PSC values", e, 0, false, 0⟩]
  rw [hA] at S
  refine ⟨S.1, fun j hj => ?_, ?_⟩
  · rw [show f + 1 + j = f + (j + 1) by omega]
    exact S.2.1 j hj
  · rw [show f + 1 + m = f + (m + 1) by omega]
    exact S.2.2

theorem headDrawsAt_eq (p : Head.Par) (r : Nat) : headDrawsAt p r =
    ((headRoundsOf (headLt p) (headLPd p))[r]?).map fun x =>
      (x.drawn, if x.notZero then 1 else 0) := by
  unfold headDrawsAt
  rw [headRounds_are, List.getElem?_map, Option.map_map]
  rfl

/-- The three later sumchecks' rounds in the list. -/
theorem headRounds_at567 (a c : Nat) :
    ((∀ j, j < a → (headRoundsOf a c)[c + a + 7 + 1 + j]? = some headVarRound) ∧
      (headRoundsOf a c)[c + a + 7 + 1 + a]? = some headLastRound) ∧
    ((headRoundsOf a c)[c + 2 * a + 10]? = some headFirstRound ∧
      (∀ j, j < a → (headRoundsOf a c)[c + 2 * a + 10 + 1 + j]? = some headVarRound) ∧
      (headRoundsOf a c)[c + 2 * a + 10 + 1 + a]? = some headLastRound) ∧
    ((headRoundsOf a c)[c + 3 * a + 13]? = some headFirstRound ∧
      (∀ j, j < a + c → (headRoundsOf a c)[c + 3 * a + 13 + 1 + j]? = some headVarRound) ∧
      (headRoundsOf a c)[c + 3 * a + 13 + 1 + (a + c)]? = some headLastRound) := by
  have D5 : headRoundsOf a c = (drawPoint.rounds a ++ (sendThenBatch.rounds 9 9 ++
      (level.rounds (c + a) ++ sendThenBatch.rounds 7 7))) ++
      (sumcheck.rounds a 4 ++ (sumcheck.rounds a 2 ++ sumcheck.rounds (a + c) 2)) := by
    unfold headRoundsOf
    simp only [List.append_assoc]
  have D6 : headRoundsOf a c = (drawPoint.rounds a ++ (sendThenBatch.rounds 9 9 ++
      (level.rounds (c + a) ++ (sendThenBatch.rounds 7 7 ++ sumcheck.rounds a 4)))) ++
      (sumcheck.rounds a 2 ++ sumcheck.rounds (a + c) 2) := by
    unfold headRoundsOf
    simp only [List.append_assoc]
  have D7 : headRoundsOf a c = (drawPoint.rounds a ++ (sendThenBatch.rounds 9 9 ++
      (level.rounds (c + a) ++ (sendThenBatch.rounds 7 7 ++ (sumcheck.rounds a 4 ++
        sumcheck.rounds a 2))))) ++ (sumcheck.rounds (a + c) 2 ++ []) := by
    unfold headRoundsOf
    simp only [List.append_assoc, List.append_nil]
  have o1 : (drawPoint.rounds a).length = 1 := rfl
  have o2 : (sendThenBatch.rounds 9 9).length = 1 := rfl
  have o3 : (sendThenBatch.rounds 7 7).length = 1 := rfl
  have S5 := headRounds_sum (drawPoint.rounds a ++ (sendThenBatch.rounds 9 9 ++
      (level.rounds (c + a) ++ sendThenBatch.rounds 7 7)))
    (sumcheck.rounds a 2 ++ sumcheck.rounds (a + c) 2) a 4 (c + a + 7)
    (by simp only [List.length_append, o1, o2, o3, headLevel_length]; omega)
  have S6 := headRounds_sum (drawPoint.rounds a ++ (sendThenBatch.rounds 9 9 ++
      (level.rounds (c + a) ++ (sendThenBatch.rounds 7 7 ++ sumcheck.rounds a 4))))
    (sumcheck.rounds (a + c) 2) a 2 (c + 2 * a + 10)
    (by simp only [List.length_append, o1, o2, o3, headLevel_length, headSumcheck_length]; omega)
  have S7 := headRounds_sum (drawPoint.rounds a ++ (sendThenBatch.rounds 9 9 ++
      (level.rounds (c + a) ++ (sendThenBatch.rounds 7 7 ++ (sumcheck.rounds a 4 ++
        sumcheck.rounds a 2))))) [] (a + c) 2 (c + 3 * a + 13)
    (by simp only [List.length_append, o1, o2, o3, headLevel_length, headSumcheck_length]; omega)
  rw [← D5] at S5
  rw [← D6] at S6
  rw [← D7] at S7
  exact ⟨S5.2, S6, S7⟩

/-- **EACH ROUND THAT `goodK6` READS DRAWS JUST ONE ELEMENT, AND NOT BY THE RULE THAT NEVER GIVES
0.** -/
theorem goodRounds_draw (p : Head.Par) : ∀ r ∈ goodRounds p, headDrawsAt p r = some (1, 0) := by
  obtain ⟨f2, f5, f6, f7⟩ := headInFront_at p
  obtain ⟨v2, _⟩ := headRounds_at2 (headLt p) (headLPd p)
  obtain ⟨⟨v5, _⟩, ⟨e6, v6, _⟩, e7, v7, _⟩ := headRounds_at567 (headLt p) (headLPd p)
  intro r hr
  rw [headDrawsAt_eq]
  rcases (mem_goodRounds p r).1 hr with ⟨j, hj, rfl⟩ | ⟨j, hj, rfl⟩ | ⟨j, hj, rfl⟩ | ⟨j, hj, rfl⟩
  · rw [f2, v2 j hj]
    rfl
  · rw [f5, v5 j hj]
    rfl
  · rw [f6]
    cases j with
    | zero =>
      rw [Nat.add_zero, e6]
      rfl
    | succ j =>
      rw [show headLPd p + 2 * headLt p + 10 + (j + 1) = headLPd p + 2 * headLt p + 10 + 1 + j by
        omega, v6 j (by omega)]
      rfl
  · rw [f7]
    cases j with
    | zero =>
      rw [Nat.add_zero, e7]
      rfl
    | succ j =>
      rw [show headLPd p + 3 * headLt p + 13 + (j + 1) = headLPd p + 3 * headLt p + 13 + 1 + j by
        omega, v7 j (by omega)]
      rfl

/-- **EACH OF THE FOUR ROUNDS THAT `goodK6Nz` READS DRAWS JUST ONE ELEMENT, BY THE RULE THAT NEVER
GIVES 0.** -/
theorem nzRounds_draw (p : Head.Par) : ∀ r ∈ nzRounds p, headDrawsAt p r = some (1, 1) := by
  obtain ⟨f2, f5, f6, f7⟩ := headInFront_at p
  obtain ⟨_, y2⟩ := headRounds_at2 (headLt p) (headLPd p)
  obtain ⟨⟨_, y5⟩, ⟨_, _, y6⟩, _, _, y7⟩ := headRounds_at567 (headLt p) (headLPd p)
  intro r hr
  rw [headDrawsAt_eq]
  unfold nzRounds at hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · rw [f2, y2]
    rfl
  · rw [f5, y5]
    rfl
  · rw [f6, y6]
    rfl
  · rw [f7, Nat.add_comm (headLPd p) (headLt p), y7]
    rfl

/-! ## 4 Tests at three sizes -/

/-- Public numbers for the tests: the logarithms of the numbers of positions and of features in a
block, the number of features. All else is 0 or a stand-in. -/
def goodRoundsPar (lt ls d : Nat) : Head.Par :=
  { sizes := { lt, ls, d, MF := 0, KF := 0, epsF := 0, V := 5, sh := 7, F := 24 }
    policy := ⟨0, 0, 0⟩, sT := 0, floor := 0, work := 0, before := [] }

-- the small size, written out: 30 rounds; 16 are read by the first test, 4 by the second
#guard goodRounds (goodRoundsPar 2 1 6) ==
  [3, 4, 5, 6, 7, 13, 14, 17, 18, 19, 22, 23, 24, 25, 26, 27]
#guard nzRounds (goodRoundsPar 2 1 6) == [8, 15, 20, 28]
#guard (goodRoundsPar 2 1 6).rounds.length == 30
-- at three sizes: the counts; every named round lies among the declared rounds; the names
#guard [goodRoundsPar 2 1 6, goodRoundsPar 6 1 500, goodRoundsPar 10 1 5120].map
  (fun p => ((goodRounds p).length, p.rounds.length)) == [(16, 30), (44, 58), (68, 82)]
#guard [goodRoundsPar 2 1 6, goodRoundsPar 6 1 500, goodRoundsPar 10 1 5120].all fun p =>
  (goodRounds p).all (fun r => (p.rounds[r]?).any fun d =>
    d.entry.name == "PSC round" || d.entry.name == "PSC epsilon") &&
  (nzRounds p).all fun r => (p.rounds[r]?).any fun d => d.entry.name == "PSC Y"
-- NO OTHER ROUND BEARS THE FLAG; and the rounds that draw one element without it and are read by
-- neither test are five: the two batching rounds, the first rounds of the first two sumchecks, and
-- the round that ends the first
#guard [goodRoundsPar 2 1 6, goodRoundsPar 6 1 500, goodRoundsPar 10 1 5120].all fun p =>
  (List.range p.rounds.length).filter (fun r => headDrawsAt p r == some (1, 1)) == nzRounds p &&
  ((List.range p.rounds.length).filter fun r =>
    headDrawsAt p r == some (1, 0) && !(goodRounds p).contains r).length == 5

#print axioms headInFront_at
#print axioms goodRounds_length
#print axioms mem_goodRounds
#print axioms goodRounds_rise
#print axioms goodRounds_nodup
#print axioms headAll_zipIdx
#print axioms headClausesOn_all
#print axioms headSumR_all
#print axioms goodK6_iff
#print axioms goodK6_no_iff
#print axioms goodK6Nz_iff
#print axioms headRounds_are
#print axioms headMid_at
#print axioms headRun_var
#print axioms headRun_last
#print axioms headStretch_at
#print axioms headLevel_length
#print axioms headSumcheck_length
#print axioms headRounds_at2
#print axioms headRounds_sum
#print axioms headDrawsAt_eq
#print axioms headRounds_at567
#print axioms goodRounds_draw
#print axioms nzRounds_draw

end ProofFile.Honest.K6
