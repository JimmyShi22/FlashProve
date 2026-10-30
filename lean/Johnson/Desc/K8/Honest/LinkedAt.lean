-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K8/Honest/LinkedAt.lean: WHAT THE TIES AND READS OF THE LIST "K8.equations" LAY ON ONE
ENTRY OF THE TWO LAST VIRTUAL ROWS OF THE DIGITS' ARRAY (THE READS' ROW, THE TIES' ROW); AND THAT
ENTRY's WEIGHT AS TERMS IN THE BATCHING ELEMENT. Definitions with code, statements and proofs. On
the list's own text and plain data: no block, no prover. Lemmas; none of the library's goals.

ZZ: the digits' array. mz: the rows of cells of all matrices. A column x < 2 mz of either row stands
for a digit (low: x < mz; high: the others) of a row of cells.
  `runSum_at`   a run's sum in the world in which one entry is 1: the weight at that entry, where
      the run covers it
  `readCoefE tl y x`   WITH CODE: what the read y (a table and one of its segments) lays on column x
      of the reads' row: the table's weight at x's place in the segment, where the low digits'
      window covers x, and 2^10 times it where the high digits' window does; **`read_at_row`**: it
      is the read's bracket where that entry is 1, less the bracket where all is 0
  `stepTerms c e st s l`   one term for each member of l: number q has the exponent e + (s + q) * st
      and the coefficient c of the member; `stepTerms_sum`, `stepTerms_mem`, `stepTerms_nodup`,
      `stepTerms_has`
  **`reads_at_row`**   ZZ is no matrix's array of symbols and not what a read's vector's array reads
      as: the ties' and reads' terms where column x of the reads' row is 1, less those where all is
      0: one term a read, each under its own power
  `readsTerms`, **`readsTerms_ok`**, **`readsTerms_live`**   with the plain claims' terms: the
      exponents differ and are at most d; where some read's `readCoefE` at x is not the word 0, a
      coefficient is not 0
  **`tie_at_row`**   the powers laid; the shape's rows at most 3 mS: a tie's bracket where column x
      of the ties' row is 1, less the bracket where all is 0: (2^20)^(i % 3) * theta^(stepF * (i /
      3)) where the low window covers x at i, and 2^10 times the like at the high window
By: Powered.wl_val (OnBytes/Tie/Pv/Tail/EndClosed.lean) · tieLeft_some (EndLoopsB.lean) ·
highDigit_val (EndClaims.lean) · okE_add (Johnson/Top/H/P1Tie/Words.lean) · `tieBracket_off`,
`readBracket_off`, `plainTerms_ok` (WeightAt.lean).
Limits: identities at one value of the element. Nothing on which columns a list's reads cover.
Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.K8.Honest.TiesAt
import Johnson.Desc.K8.Honest.CoefCode

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K8.Honest
open OnBytes OnBytes.Model OnBytes.Model.HTailF2
open VerifiableInference.Desc VerifiableInference.Desc.First.TailClaims
open VerifiableInference.Desc.First.TailClaims.Law
open OnBytes.Tie.Pv.Tail.Port

/-- A run's sum in the world in which one entry is 1. -/
theorem runSum_at (a : Nat → Cb.Gl.E) (t r x c n : Nat) :
    runSum (fun j => a j * (oneAt t r x).entry t r (c + j)) n 0 =
      if c ≤ x ∧ x < c + n then a (x - c) else 0 := by
  by_cases h : c ≤ x ∧ x < c + n
  · rw [if_pos h, runSum_pick _ n (x - c) (by omega) (fun d _ hne => by
      show a d * (if t = t ∧ r = r ∧ c + d = x then (1 : Cb.Gl.E) else 0) = 0
      rw [if_neg (fun e => hne (by have := e.2.2; omega)), mul_zero])]
    show a (x - c) * (if t = t ∧ r = r ∧ c + (x - c) = x then (1 : Cb.Gl.E) else 0) = a (x - c)
    rw [if_pos ⟨rfl, rfl, by omega⟩, mul_one]
  · rw [if_neg h, runSum_eq_sum]
    refine Finset.sum_eq_zero fun d hd => ?_
    show a (0 + d) * (if t = t ∧ r = r ∧ c + (0 + d) = x then (1 : Cb.Gl.E) else 0) = 0
    rw [if_neg (fun e => h (by
      have := e.2.2
      have := Finset.mem_range.1 hd
      omega)), mul_zero]

/-- What a read lays on column x of the reads' row, with code. -/
def readCoefE (tl : HTailF2) (y : HFun × Nat) (x : Nat) : E :=
  addE
    (if (tl.zzCol y.1.mat 0 (y.2 * y.1.len)).getD 0 ≤ x ∧
        x < (tl.zzCol y.1.mat 0 (y.2 * y.1.len)).getD 0 + y.1.len then
      y.1.phi.getD (x - (tl.zzCol y.1.mat 0 (y.2 * y.1.len)).getD 0) zeroE else zeroE)
    (highDigit
      (if (tl.zzCol y.1.mat 1 (y.2 * y.1.len)).getD 0 ≤ x ∧
          x < (tl.zzCol y.1.mat 1 (y.2 * y.1.len)).getD 0 + y.1.len then
        y.1.phi.getD (x - (tl.zzCol y.1.mat 1 (y.2 * y.1.len)).getD 0) zeroE else zeroE))

/-- **A read's bracket at a column of the reads' row.** -/
theorem read_at_row (tl : HTailF2) (F0 : Fork) (y : HFun × Nat) (x : Nat)
    (hU : (tl.ix.U.getD y.1.tree none).getD 0 ≠ tl.ix.ZZ) :
    readBracket Reading.gl (oneAt tl.ix.ZZ tl.zzRowReads x) tl F0 y -
        readBracket Reading.gl allZero tl F0 y = Reading.gl.val (readCoefE tl y x) := by
  unfold readBracket readCoefE
  simp only [entry_off tl.ix.ZZ tl.zzRowReads x _ hU, entry_zero, mul_zero, runSum_zero]
  rw [runSum_at, runSum_at, Reading.gl.add, highDigit_val Reading.gl]
  split_ifs <;> (try simp only [Reading.gl.zero]) <;> ring

/-- One term for each member of a list, the exponents a step apart. -/
def stepTerms {α : Type} (c : α → Cb.Gl.E) (e st : Nat) : Nat → List α → List (ℕ × Cb.Gl.E)
  | _, [] => []
  | s, y :: l => (e + s * st, c y) :: stepTerms c e st (s + 1) l

theorem stepTerms_sum {α : Type} (c : α → Cb.Gl.E) (e st : Nat) (X : Cb.Gl.E) :
    ∀ (l : List α) (s : Nat),
      sumFrom (fun q y => X ^ (e + q * st) * c y) s l = K9L.termsSum (stepTerms c e st s l) X
  | [], _ => by simp [sumFrom, stepTerms, K9L.termsSum]
  | y :: l, s => by
    have ih := stepTerms_sum c e st X l (s + 1)
    simp only [sumFrom, stepTerms, K9L.termsSum, List.map_cons, List.sum_cons] at ih ⊢
    rw [ih]

theorem stepTerms_mem {α : Type} (c : α → Cb.Gl.E) (e st : Nat) :
    ∀ (l : List α) (s : Nat) (z : ℕ × Cb.Gl.E), z ∈ stepTerms c e st s l →
      ∃ q, s ≤ q ∧ q < s + l.length ∧ z.1 = e + q * st
  | [], _, _, h => nomatch h
  | y :: l, s, z, h => by
    rcases List.mem_cons.1 h with rfl | h
    · exact ⟨s, Nat.le_refl _, by simp, rfl⟩
    · obtain ⟨q, h1, h2, h3⟩ := stepTerms_mem c e st l (s + 1) z h
      exact ⟨q, by omega, by simp only [List.length_cons]; omega, h3⟩

theorem stepTerms_nodup {α : Type} (c : α → Cb.Gl.E) (e st : Nat) (hst : 0 < st) :
    ∀ (l : List α) (s : Nat), ((stepTerms c e st s l).map (·.1)).Nodup
  | [], _ => List.nodup_nil
  | y :: l, s => by
    simp only [stepTerms, List.map_cons, List.nodup_cons]
    refine ⟨fun h => ?_, stepTerms_nodup c e st hst l (s + 1)⟩
    obtain ⟨z, hz, ez⟩ := List.mem_map.1 h
    obtain ⟨q, h1, -, h3⟩ := stepTerms_mem c e st l (s + 1) z hz
    rw [h3] at ez
    have h4 : (s + 1) * st ≤ q * st := Nat.mul_le_mul_right _ h1
    have h5 : (s + 1) * st = s * st + st := Nat.succ_mul _ _
    omega

theorem stepTerms_has {α : Type} (c : α → Cb.Gl.E) (e st : Nat) :
    ∀ (l : List α) (s : Nat) (y : α), y ∈ l → ∃ z ∈ stepTerms c e st s l, z.2 = c y
  | [], _, _, h => nomatch h
  | y' :: l, s, y, h => by
    rcases List.mem_cons.1 h with rfl | h
    · exact ⟨_, List.mem_cons_self, rfl⟩
    · obtain ⟨z, hz, e'⟩ := stepTerms_has c e st l (s + 1) y h
      exact ⟨z, List.mem_cons_of_mem _ hz, e'⟩

/-- **What the ties and reads lay on a column of the reads' row.** -/
theorem reads_at_row (tl : HTailF2) (F0 : Fork) (funs : Array HFun) (x : Nat)
    (hg : ∀ mu, mu < tl.NM → tl.gtTree.getD mu 0 ≠ tl.ix.ZZ)
    (hU0 : (tl.ix.U.getD 0 none).getD 0 ≠ tl.ix.ZZ)
    (hU2 : (tl.ix.U.getD 2 none).getD 0 ≠ tl.ix.ZZ) :
    (((List.range tl.NM).map
          (tieTerm Reading.gl (oneAt tl.ix.ZZ tl.zzRowReads x) tl F0)).sum +
        sumFrom (readTerm Reading.gl (oneAt tl.ix.ZZ tl.zzRowReads x) tl F0) 0
          (readsList tl funs)) -
      (((List.range tl.NM).map (tieTerm Reading.gl allZero tl F0)).sum +
        sumFrom (readTerm Reading.gl allZero tl F0) 0 (readsList tl funs)) =
      K9L.termsSum (stepTerms (fun y => Reading.gl.val (readCoefE tl y x))
        (F0.planClaimsF + tl.eqFirst.getD tl.NM 0) tl.stepF 0 (readsList tl funs))
        (Reading.gl.val F0.theta) := by
  have ht : (List.range tl.NM).map (tieTerm Reading.gl (oneAt tl.ix.ZZ tl.zzRowReads x) tl F0) =
      (List.range tl.NM).map (tieTerm Reading.gl allZero tl F0) :=
    List.map_congr_left fun mu hmu => by
      unfold tieTerm
      rw [tieBracket_off tl mu _ _ x
        (fun h => by
          have h2 : 2 * tl.zzBlocks + 1 = 2 * tl.zzBlocks := h.2
          omega)
        (fun h => hg mu (List.mem_range.1 hmu) h.1)]
  have hr : sumFrom (readTerm Reading.gl (oneAt tl.ix.ZZ tl.zzRowReads x) tl F0) 0
        (readsList tl funs) -
      sumFrom (readTerm Reading.gl allZero tl F0) 0 (readsList tl funs) =
      sumFrom (fun q y => Reading.gl.val F0.theta ^
          (F0.planClaimsF + tl.eqFirst.getD tl.NM 0 + q * tl.stepF) *
        Reading.gl.val (readCoefE tl y x)) 0 (readsList tl funs) := by
    rw [sumFrom_sub]
    refine sumFrom_congr _ _ _ _ fun j z hz => ?_
    have hU : (tl.ix.U.getD z.1.tree none).getD 0 ≠ tl.ix.ZZ := by
      rcases tree_of_mem tl funs z hz with e | e
      · rw [e]
        exact hU0
      · rw [e]
        exact hU2
    unfold readTerm
    rw [← mul_sub, read_at_row tl F0 z x hU, Nat.add_assoc]
  rw [ht, ← stepTerms_sum]
  linear_combination hr

/-- The terms of the weight of column x of the reads' row. -/
def readsTerms (a : Nat → Cb.Gl.E) (tl : HTailF2) (funs : Array HFun) (n nf nb x : Nat) :
    List (ℕ × Cb.Gl.E) :=
  plainTerms a nf nb (tl.NM + (readsList tl funs).length) ++
    stepTerms (fun y => Reading.gl.val (readCoefE tl y x)) (n + firstOf tl tl.NM) tl.stepF 0
      (readsList tl funs)

theorem stepF_pos (tl : HTailF2) : 0 < tl.stepF := Nat.pos_of_ne_zero (by
  unfold HTailF2.stepF
  positivity)

/-- The plain claims' exponents lie below the plan's number. -/
theorem plainTerms_lt (a : Nat → Cb.Gl.E) (nf nb m n : Nat) (hcl : nf + (4 + m) + nb ≤ n) :
    ∀ y ∈ plainTerms a nf nb m, y.1 < n := by
  intro y hy
  unfold plainTerms at hy
  rcases List.mem_append.1 hy with hy | hy
  · have b1 := fromOn_mem _ _ _ y hy
    omega
  · have b1 := fromOn_mem _ _ _ y hy
    omega

/-- **The exponents differ from each other and are at most d.** -/
theorem readsTerms_ok (a : Nat → Cb.Gl.E) (tl : HTailF2) (funs : Array HFun) (n nf nb x d : Nat)
    (hcl : nf + (4 + (tl.NM + (readsList tl funs).length)) + nb ≤ n)
    (hd : n + (firstOf tl tl.NM + (readsList tl funs).length * tl.stepF) ≤ d + 1) :
    K9L.TermsOk (readsTerms a tl funs n nf nb x) d := by
  obtain ⟨p1, p2⟩ := plainTerms_ok a nf nb (tl.NM + (readsList tl funs).length) d (by omega)
  have pb := plainTerms_lt a nf nb _ n hcl
  have hst := stepF_pos tl
  refine ⟨?_, ?_⟩
  · unfold readsTerms
    rw [List.map_append, List.nodup_append]
    refine ⟨p1, stepTerms_nodup _ _ _ hst _ _, ?_⟩
    intro u hu v hv
    obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hu
    obtain ⟨z, hz, rfl⟩ := List.mem_map.1 hv
    have b1 := pb y hy
    obtain ⟨q, -, -, h3⟩ := stepTerms_mem _ _ _ _ _ z hz
    omega
  · intro y hy
    unfold readsTerms at hy
    rcases List.mem_append.1 hy with hy | hy
    · exact p2 y hy
    · obtain ⟨q, -, h2, h3⟩ := stepTerms_mem _ _ _ _ _ y hy
      have h4 : (q + 1) * tl.stepF ≤ (readsList tl funs).length * tl.stepF :=
        Nat.mul_le_mul_right _ (by omega)
      have h5 : (q + 1) * tl.stepF = q * tl.stepF + tl.stepF := Nat.succ_mul _ _
      omega

/-- **Where a read's weight at the column is not the word 0, a coefficient is not 0.** -/
theorem readsTerms_live (a : Nat → Cb.Gl.E) (tl : HTailF2) (funs : Array HFun) (n nf nb x : Nat)
    (h : ((readsList tl funs).any fun y => !isZeroE (readCoefE tl y x)) = true) :
    ∃ y ∈ readsTerms a tl funs n nf nb x, y.2 ≠ 0 := by
  obtain ⟨y, hy, hne⟩ := List.any_eq_true.1 h
  obtain ⟨z, hz, ez⟩ := stepTerms_has (fun y => Reading.gl.val (readCoefE tl y x))
    (n + firstOf tl tl.NM) tl.stepF (readsList tl funs) 0 y hy
  refine ⟨z, List.mem_append_right _ hz, ?_⟩
  rw [ez]
  intro h0
  have h1 : isZeroE (readCoefE tl y x) = true :=
    (OnBytes.Slice.isZeroE_iff _ (Part.MaskedSum.okE_add _ _)).2 h0
  rw [h1] at hne
  cases hne

/-- **A tie's bracket at a column of the ties' row.** -/
theorem tie_at_row (tl : HTailF2) (θ : E) (hP : Powered tl θ) (mu x : Nat) (hmu : mu < tl.NM)
    (hm : (tl.shp.getD mu {}).m ≤ 3 * (tl.shp.getD mu {}).mS)
    (hg : tl.gtTree.getD mu 0 ≠ tl.ix.ZZ) :
    tieBracket Reading.gl (oneAt tl.ix.ZZ tl.zzRowTies x) tl mu -
        tieBracket Reading.gl allZero tl mu =
      (if (tl.zzCol mu 0 0).getD 0 ≤ x ∧ x < (tl.zzCol mu 0 0).getD 0 + (tl.shp.getD mu {}).m then
          ((2 : Cb.Gl.E) ^ 20) ^ ((x - (tl.zzCol mu 0 0).getD 0) % 3) *
            Reading.gl.val θ ^ (tl.stepF * ((x - (tl.zzCol mu 0 0).getD 0) / 3)) else 0) +
        (2 : Cb.Gl.E) ^ 10 *
          (if (tl.zzCol mu 1 0).getD 0 ≤ x ∧
              x < (tl.zzCol mu 1 0).getD 0 + (tl.shp.getD mu {}).m then
            ((2 : Cb.Gl.E) ^ 20) ^ ((x - (tl.zzCol mu 1 0).getD 0) % 3) *
              Reading.gl.val θ ^ (tl.stepF * ((x - (tl.zzCol mu 1 0).getD 0) / 3)) else 0) := by
  obtain ⟨wl, hwl⟩ := hP.tieLeft_some mu hmu
  have hv := hP.wl_val Reading.gl mu hmu (hP.lt_shp mu hmu) hm wl hwl
  unfold tieBracket
  rw [hwl]
  simp only [Option.getD_some, entry_off tl.ix.ZZ tl.zzRowTies x _ hg, entry_zero, mul_zero,
    runSum_zero]
  rw [runSum_at, runSum_at]
  split_ifs with h0 h1 h1
  · rw [hv _ (by omega), hv _ (by omega)]
    ring
  · rw [hv _ (by omega)]
    ring
  · rw [hv _ (by omega)]
    ring
  · ring

end VerifiableInference.Desc.First.K8.Honest

#print axioms VerifiableInference.Desc.First.K8.Honest.runSum_at
#print axioms VerifiableInference.Desc.First.K8.Honest.read_at_row
#print axioms VerifiableInference.Desc.First.K8.Honest.stepTerms_sum
#print axioms VerifiableInference.Desc.First.K8.Honest.stepTerms_nodup
#print axioms VerifiableInference.Desc.First.K8.Honest.reads_at_row
#print axioms VerifiableInference.Desc.First.K8.Honest.readsTerms_ok
#print axioms VerifiableInference.Desc.First.K8.Honest.readsTerms_live
#print axioms VerifiableInference.Desc.First.K8.Honest.tie_at_row
