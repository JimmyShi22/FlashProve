-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K8/Honest/ReadAgainVal.lean: THE SMALLNESS TEST: THE VALUE OF EACH ENTRY OF THE
VERIFIER's SECOND COMPUTATION OF THE COLUMN WEIGHTS OF THE READS' ROW (`readWeightsAgain`,
OnBytes/Model/Tail.lean), AS A WRITTEN SUM OVER THE READS IN THE ORDER IN WHICH THEY ARE LAID (the
library's `readsList`): one term a read: a power of the batching element, a step apart from read to
read, times what the read lays on the column. And each entry is a word below the prime. Level by
level over the five folds of Johnson/Desc/K8/Honest/ReadAgainFold.lean. Lemmas on the verifier's own
text; none of the library's goals.

  `colAt base n phi x`   what a stretch of n columns from base on, filled with phi, has at column x
  `segAt mz base n phi x`   a segment's two stretches: the low digits', and 2 ^ 10 times the high
                   digits'
  `readLays tl F x before q y`   what read number q lays on column x, the matrix's first column
                   being `before`: θ ^ (planClaims + firstAgain NM + q * pow2Again tau) * segAt
                   tl.mz (before + sg * len) len phi x
  `rowsBefore tl n`   the rows of the matrices in front of matrix number n: the second computation's
                   own count
  `val_modify`   · `fold_j` · `fold_sg` · `fold_fn` · `fold_un` · `fold_mu` the levels: an adding at
                   one place · the rows of cells of a segment · the segments of a table · the tables
                   of a vector on a matrix · the vectors on a matrix · the matrices
  **`readAgain_sum`**   x < 2 * tl.mz ⊢ the value of entry x = the sum over readsList tl tl.funs,
                   from number 0, of readLays tl F x (rowsBefore tl ‹the read's matrix›)
  `AllOk w`   every entry of w, and what stands for an entry outside, is a word below the prime
  **`readAgain_ok`**   AllOk (tl.readWeightsAgain F), with no premise
Limits. THE MATRICES' FIRST COLUMNS ARE THE SECOND COMPUTATION's OWN (counted afresh): that they are
the plan's is not said here. Nothing on the first computation. Outside the array (x at or beyond 2 *
tl.mz) nothing is said of the value.
Nothing is claimed on completeness, soundness or hiding.

-/
import Johnson.Desc.K8.Honest.ReadAgainFold
import Johnson.Desc.First.Batch.Law.Stages
import OnBytes.Tie.Pv.Lookup.Ends.FoNatVal
import OnBytes.Tie.Pv.Tail.EndLoopsB
import Johnson.Top.H.P1Tie.Words

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K8.Honest
open OnBytes OnBytes.Model OnBytes.Model.HTailF2
open OnBytes.Tie.Pv.Tail.Port (readsList segsOf)
open VerifiableInference.Desc.K9L (sumFrom_append sumFrom_map)

local notation "K" => Cb.Gl.E
local notation "val" => Reading.gl.val

/-- What a stretch of n columns from base on, filled with phi, has at column x. -/
noncomputable def colAt (base n : Nat) (phi : Array E) (x : Nat) : K :=
  if base ≤ x ∧ x < base + n then val (phi.getD (x - base) zeroE) else 0

theorem colAt_zero (base : Nat) (phi : Array E) (x : Nat) : colAt base 0 phi x = 0 := by
  unfold colAt
  rw [if_neg (by omega)]

theorem colAt_succ (base n : Nat) (phi : Array E) (x : Nat) :
    colAt base (n + 1) phi x =
      colAt base n phi x + if base + n = x then val (phi.getD n zeroE) else 0 := by
  unfold colAt
  by_cases h : base + n = x
  · subst h
    rw [if_pos (by omega), if_neg (by omega), if_pos rfl, zero_add, Nat.add_sub_cancel_left]
  · rw [if_neg h, add_zero]
    by_cases h2 : base ≤ x ∧ x < base + n
    · rw [if_pos (by omega), if_pos h2]
    · rw [if_neg (by omega), if_neg h2]

/-- A segment's two stretches. -/
noncomputable def segAt (mz base n : Nat) (phi : Array E) (x : Nat) : K :=
  colAt base n phi x + ((2 ^ t2D0 : Nat) : K) * colAt (mz + base) n phi x

/-- An entry behind an adding at one place. -/
theorem val_modify (w : Array E) (i x : Nat) (v : E) (hx : x < w.size) :
    val ((w.modify i fun y => addE y v).getD x zeroE) =
      val (w.getD x zeroE) + if i = x then val v else 0 := by
  have h1 : (w.modify i fun y => addE y v).getD x zeroE =
      if i = x then addE (w.getD x zeroE) v else w.getD x zeroE := by
    have e : w[x]? = some w[x] := Array.getElem?_eq_getElem hx
    simp only [Array.getD_eq_getD_getElem?, Array.getElem?_modify, e]
    split <;> rfl
  rw [h1]
  split
  · rw [Reading.gl.add]
  · rw [add_zero]

theorem size_jStep (mz base : Nat) (kr : E) (phi w : Array E) (j : Nat) :
    (jStep mz base kr phi w j).size = w.size := by
  unfold jStep
  rw [Array.size_modify, Array.size_modify]

/-- **The rows of cells of a segment.** -/
theorem fold_j (mz base : Nat) (kr : E) (phi : Array E) (x : Nat) : ∀ (n : Nat) (w : Array E),
    x < w.size →
      ((List.range n).foldl (jStep mz base kr phi) w).size = w.size ∧
        val (((List.range n).foldl (jStep mz base kr phi) w).getD x zeroE) =
          val (w.getD x zeroE) + val kr * segAt mz base n phi x
  | 0, w, _ => by
    refine ⟨rfl, ?_⟩
    unfold segAt
    rw [colAt_zero, colAt_zero]
    simp
  | n + 1, w, hx => by
    obtain ⟨s1, v1⟩ := fold_j mz base kr phi x n w hx
    rw [List.range_succ, List.foldl_append]
    generalize (List.range n).foldl (jStep mz base kr phi) w = W at s1 v1 ⊢
    refine ⟨by
      show (jStep mz base kr phi W n).size = _
      rw [size_jStep, s1], ?_⟩
    show val ((jStep mz base kr phi W n).getD x zeroE) = _
    unfold jStep
    rw [val_modify _ _ _ _ (by rw [Array.size_modify, s1]; exact hx),
      val_modify _ _ _ _ (by rw [s1]; exact hx), v1, Fo.scaleNat_val Reading.gl, Reading.gl.mul]
    unfold segAt
    rw [colAt_succ, colAt_succ, Nat.add_assoc mz base n]
    split_ifs <;> ring

/-- What read number q lays on column x, the matrix's first column being `before`. -/
noncomputable def readLays (tl : HTailF2) (F : Fork) (x before q : Nat) (y : HFun × Nat) : K :=
  val F.theta ^ (F.planClaimsF + tl.firstAgain tl.NM + q * pow2Again tl.tau) *
    segAt tl.mz (before + y.2 * y.1.len) y.1.len y.1.phi x

/-- **The segments of a table.** -/
theorem fold_sg (tl : HTailF2) (F : Fork) (before : Nat) (Fn : HFun) (x : Nat) :
    ∀ (n q0 : Nat) (kr : E) (w : Array E), x < w.size →
      val kr = val F.theta ^ (F.planClaimsF + tl.firstAgain tl.NM + q0 * pow2Again tl.tau) →
      ((List.range n).foldl (sgStep tl.mz before (powE F.theta (pow2Again tl.tau)) Fn)
          ⟨kr, w⟩).snd.size = w.size ∧
        val ((List.range n).foldl (sgStep tl.mz before (powE F.theta (pow2Again tl.tau)) Fn)
          ⟨kr, w⟩).fst =
          val F.theta ^ (F.planClaimsF + tl.firstAgain tl.NM + (q0 + n) * pow2Again tl.tau) ∧
        val (((List.range n).foldl (sgStep tl.mz before (powE F.theta (pow2Again tl.tau)) Fn)
          ⟨kr, w⟩).snd.getD x zeroE) =
          val (w.getD x zeroE) +
            sumFrom (fun q sg => readLays tl F x before q (Fn, sg)) q0 (List.range n)
  | 0, q0, kr, w, _, hk => by
    refine ⟨rfl, ?_, ?_⟩
    · show val kr = _
      rw [hk, Nat.add_zero]
    · show val (w.getD x zeroE) = _
      simp [sumFrom]
  | n + 1, q0, kr, w, hx, hk => by
    obtain ⟨s1, k1, v1⟩ := fold_sg tl F before Fn x n q0 kr w hx hk
    rw [List.range_succ, List.foldl_append]
    obtain ⟨s2, v2⟩ := fold_j tl.mz (before + n * Fn.len)
      ((List.range n).foldl (sgStep tl.mz before (powE F.theta (pow2Again tl.tau)) Fn)
        ⟨kr, w⟩).fst Fn.phi x Fn.len
      ((List.range n).foldl (sgStep tl.mz before (powE F.theta (pow2Again tl.tau)) Fn)
        ⟨kr, w⟩).snd (by rw [s1]; exact hx)
    refine ⟨s2.trans s1, ?_, ?_⟩
    · show val (mulE _ (powE F.theta (pow2Again tl.tau))) = _
      rw [Reading.gl.mul, Reading.gl.pow, k1, ← pow_add]
      congr 1
      ring
    · refine v2.trans ?_
      rw [v1, k1, sumFrom_append, List.length_range]
      simp only [sumFrom, readLays]
      ring

/-- **The tables of a vector of reads on a matrix.** -/
theorem fold_fn (tl : HTailF2) (F : Fork) (mu un before x : Nat) :
    ∀ (l : List HFun) (q : Nat) (w : Array E), x < w.size →
      (l.foldl (fnStep tl F mu un before) ⟨q, w⟩).snd.size = w.size ∧
        (l.foldl (fnStep tl F mu un before) ⟨q, w⟩).fst =
          q + (l.flatMap (segsOf tl mu un)).length ∧
        val ((l.foldl (fnStep tl F mu un before) ⟨q, w⟩).snd.getD x zeroE) =
          val (w.getD x zeroE) + sumFrom (readLays tl F x before) q (l.flatMap (segsOf tl mu un))
  | [], q, w, _ => by
    refine ⟨rfl, rfl, ?_⟩
    show val (w.getD x zeroE) = _
    simp [sumFrom]
  | Fn :: l, q, w, hx => by
    rw [List.foldl_cons, List.flatMap_cons]
    by_cases hc : (Fn.mat == mu && Fn.tree == un) = true
    · obtain ⟨s1, -, v1⟩ := fold_sg tl F before Fn x ((tl.mats.getD mu {}).m / Fn.len) q
        (powE F.theta (F.planClaimsF + tl.firstAgain tl.NM + q * pow2Again tl.tau)) w hx
        (Reading.gl.pow _ _)
      have e1 : fnStep tl F mu un before ⟨q, w⟩ Fn =
          ⟨q + (tl.mats.getD mu {}).m / Fn.len,
            ((List.range ((tl.mats.getD mu {}).m / Fn.len)).foldl
              (sgStep tl.mz before (powE F.theta (pow2Again tl.tau)) Fn)
              ⟨powE F.theta (F.planClaimsF + tl.firstAgain tl.NM + q * pow2Again tl.tau),
                w⟩).snd⟩ := by
        unfold fnStep
        rw [if_pos hc]
      have e2 : segsOf tl mu un Fn =
          (List.range ((tl.mats.getD mu {}).m / Fn.len)).map fun sg => (Fn, sg) := by
        unfold segsOf
        rw [if_pos hc]
      obtain ⟨s3, q3, v3⟩ := fold_fn tl F mu un before x l _ _ (by rw [s1]; exact hx)
      rw [e1, e2]
      refine ⟨s3.trans s1, ?_, ?_⟩
      · rw [q3, List.length_append, List.length_map, List.length_range]
        omega
      · rw [v3, v1, sumFrom_append, sumFrom_map, List.length_map, List.length_range]
        ring
    · have e1 : fnStep tl F mu un before ⟨q, w⟩ Fn = ⟨q, w⟩ := by
        unfold fnStep
        rw [if_neg hc]
      have e2 : segsOf tl mu un Fn = [] := by
        unfold segsOf
        rw [if_neg hc]
      rw [e1, e2, List.nil_append]
      exact fold_fn tl F mu un before x l q w hx

/-- **The vectors of reads on a matrix.** -/
theorem fold_un (tl : HTailF2) (F : Fork) (mu before x : Nat) :
    ∀ (us : List Nat) (q : Nat) (w : Array E), x < w.size →
      (us.foldl (unStep tl F mu before) ⟨q, w⟩).snd.size = w.size ∧
        (us.foldl (unStep tl F mu before) ⟨q, w⟩).fst =
          q + (us.flatMap fun un => tl.funs.toList.flatMap (segsOf tl mu un)).length ∧
        val ((us.foldl (unStep tl F mu before) ⟨q, w⟩).snd.getD x zeroE) =
          val (w.getD x zeroE) + sumFrom (readLays tl F x before) q
            (us.flatMap fun un => tl.funs.toList.flatMap (segsOf tl mu un))
  | [], q, w, _ => by
    refine ⟨rfl, rfl, ?_⟩
    show val (w.getD x zeroE) = _
    simp [sumFrom]
  | un :: us, q, w, hx => by
    rw [List.foldl_cons, List.flatMap_cons]
    obtain ⟨s1, q1, v1⟩ := fold_fn tl F mu un before x tl.funs.toList q w hx
    have e1 : unStep tl F mu before ⟨q, w⟩ un =
        tl.funs.toList.foldl (fnStep tl F mu un before) ⟨q, w⟩ := rfl
    obtain ⟨s3, q3, v3⟩ := fold_un tl F mu before x us
      (tl.funs.toList.foldl (fnStep tl F mu un before) ⟨q, w⟩).fst
      (tl.funs.toList.foldl (fnStep tl F mu un before) ⟨q, w⟩).snd (by rw [s1]; exact hx)
    rw [e1]
    refine ⟨s3.trans s1, ?_, ?_⟩
    · refine q3.trans ?_
      rw [q1, List.length_append]
      omega
    · refine v3.trans ?_
      rw [v1, q1, sumFrom_append]
      ring

/-- The rows of the matrices in front of matrix number n: the second computation's own count. -/
def rowsBefore (tl : HTailF2) (n : Nat) : Nat :=
  (List.range n).foldl (fun a nu => a + (tl.mats.getD nu {}).m) 0

theorem rowsBefore_succ (tl : HTailF2) (n : Nat) :
    rowsBefore tl (n + 1) = rowsBefore tl n + (tl.mats.getD n {}).m := by
  unfold rowsBefore
  rw [List.range_succ, List.foldl_append]
  rfl

/-- A read of matrix mu's lists lies on matrix mu. -/
theorem mat_of_mem (tl : HTailF2) (mu : Nat) (us : List Nat) (l : List HFun) (y : HFun × Nat)
    (h : y ∈ us.flatMap fun un => l.flatMap (segsOf tl mu un)) : y.1.mat = mu := by
  obtain ⟨un, -, h⟩ := List.mem_flatMap.1 h
  obtain ⟨Fn, -, h⟩ := List.mem_flatMap.1 h
  unfold segsOf at h
  split at h
  · rename_i hc
    obtain ⟨sg, -, rfl⟩ := List.mem_map.1 h
    simp only [Bool.and_eq_true, beq_iff_eq] at hc
    exact hc.1
  · exact absurd h (List.not_mem_nil)

/-- **The matrices.** -/
theorem fold_mu (tl : HTailF2) (F : Fork) (x : Nat) (w : Array E) (hx : x < w.size) :
    ∀ n : Nat,
      ((List.range n).foldl (muStep tl F) ⟨0, 0, w⟩).fst = rowsBefore tl n ∧
        ((List.range n).foldl (muStep tl F) ⟨0, 0, w⟩).snd.snd.size = w.size ∧
        ((List.range n).foldl (muStep tl F) ⟨0, 0, w⟩).snd.fst =
          ((List.range n).flatMap fun mu =>
            [0, 2].flatMap fun un => tl.funs.toList.flatMap (segsOf tl mu un)).length ∧
        val (((List.range n).foldl (muStep tl F) ⟨0, 0, w⟩).snd.snd.getD x zeroE) =
          val (w.getD x zeroE) +
            sumFrom (fun q y => readLays tl F x (rowsBefore tl y.1.mat) q y) 0
              ((List.range n).flatMap fun mu =>
                [0, 2].flatMap fun un => tl.funs.toList.flatMap (segsOf tl mu un))
  | 0 => by
    refine ⟨rfl, rfl, rfl, ?_⟩
    show val (w.getD x zeroE) = _
    simp [sumFrom]
  | n + 1 => by
    obtain ⟨b1, s1, q1, v1⟩ := fold_mu tl F x w hx n
    rw [List.range_succ, List.foldl_append, List.flatMap_append]
    obtain ⟨s2, q2, v2⟩ := fold_un tl F n ((List.range n).foldl (muStep tl F) ⟨0, 0, w⟩).fst x
      [0, 2] ((List.range n).foldl (muStep tl F) ⟨0, 0, w⟩).snd.fst
      ((List.range n).foldl (muStep tl F) ⟨0, 0, w⟩).snd.snd (by rw [s1]; exact hx)
    refine ⟨?_, s2.trans s1, ?_, ?_⟩
    · show _ + (tl.mats.getD n {}).m = _
      rw [b1, rowsBefore_succ]
    · refine q2.trans ?_
      rw [q1, List.length_append]
      simp
    · refine v2.trans ?_
      rw [v1, q1, b1, sumFrom_append, Nat.zero_add]
      simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
      rw [add_assoc]
      congr 1
      congr 1
      refine OnBytes.Tie.Pv.Tail.Port.sumFrom_congr _ _ _ _ fun q y hy => ?_
      rw [mat_of_mem tl n [0, 2] tl.funs.toList y (by
        simpa only [List.flatMap_cons, List.flatMap_nil, List.append_nil] using hy)]

/-- **The value of an entry of the second computation.** -/
theorem readAgain_sum (tl : HTailF2) (F : Fork) (x : Nat) (hx : x < 2 * tl.mz) :
    val ((tl.readWeightsAgain F).getD x zeroE) =
      sumFrom (fun q y => readLays tl F x (rowsBefore tl y.1.mat) q y) 0
        (readsList tl tl.funs) := by
  obtain ⟨-, -, -, v⟩ := fold_mu tl F x (Array.replicate (2 * tl.mz) zeroE)
    (by rw [Array.size_replicate]; exact hx) tl.NM
  rw [readAgain_fold, v]
  have e0 : (Array.replicate (2 * tl.mz) zeroE).getD x zeroE = zeroE := by
    simp [Array.getD, hx]
  rw [e0, Reading.gl.zero, zero_add]
  rfl

/-! ## Each entry is a word below the prime -/

/-- Every entry, and what stands for an entry outside, is a word below the prime. -/
def AllOk (w : Array E) : Prop := ∀ x : Nat, OnBytes.okE (w.getD x zeroE) = true

theorem allOk_modify (w : Array E) (i : Nat) (v : E) (h : AllOk w) :
    AllOk (w.modify i fun y => addE y v) := by
  intro x
  have hx := h x
  rw [Array.getD_eq_getD_getElem?] at hx ⊢
  rw [Array.getElem?_modify]
  split
  · cases e : w[x]? with
    | none =>
      rw [e] at hx
      exact hx
    | some a => exact Part.MaskedSum.okE_add _ _
  · exact hx

theorem foldl_keeps {α β : Type} (P : β → Prop) (f : β → α → β) (h : ∀ b a, P b → P (f b a)) :
    ∀ (l : List α) (b : β), P b → P (l.foldl f b)
  | [], _, hb => hb
  | a :: l, b, hb => foldl_keeps P f h l (f b a) (h b a hb)

theorem allOk_j (mz base : Nat) (kr : E) (phi w : Array E) (j : Nat) (h : AllOk w) :
    AllOk (jStep mz base kr phi w j) := by
  unfold jStep
  exact allOk_modify _ _ _ (allOk_modify _ _ _ h)

theorem allOk_sg (mz before : Nat) (byStep : E) (Fn : HFun) (s : MProd E (Array E)) (sg : Nat)
    (h : AllOk s.snd) : AllOk (sgStep mz before byStep Fn s sg).snd :=
  foldl_keeps AllOk (jStep mz (before + sg * Fn.len) s.fst Fn.phi)
    (fun w j hw => allOk_j mz (before + sg * Fn.len) s.fst Fn.phi w j hw) (List.range Fn.len)
    s.snd h

theorem allOk_fn (tl : HTailF2) (F : Fork) (mu un before : Nat) (s : MProd Nat (Array E))
    (Fn : HFun) (h : AllOk s.snd) : AllOk (fnStep tl F mu un before s Fn).snd := by
  unfold fnStep
  split
  · exact foldl_keeps (fun r : MProd E (Array E) => AllOk r.snd)
      (sgStep tl.mz before (powE F.theta (pow2Again tl.tau)) Fn)
      (fun r sg hr => allOk_sg tl.mz before (powE F.theta (pow2Again tl.tau)) Fn r sg hr)
      (List.range ((tl.mats.getD mu {}).m / Fn.len))
      ⟨powE F.theta (F.planClaimsF + tl.firstAgain tl.NM + s.fst * pow2Again tl.tau), s.snd⟩ h
  · exact h

theorem allOk_un (tl : HTailF2) (F : Fork) (mu before : Nat) (s : MProd Nat (Array E))
    (un : Nat) (h : AllOk s.snd) : AllOk (unStep tl F mu before s un).snd :=
  foldl_keeps (fun r : MProd Nat (Array E) => AllOk r.snd) (fnStep tl F mu un before)
    (fun r Fn hr => allOk_fn tl F mu un before r Fn hr) tl.funs.toList ⟨s.fst, s.snd⟩ h

theorem allOk_mu (tl : HTailF2) (F : Fork) (s : MProd Nat (MProd Nat (Array E))) (mu : Nat)
    (h : AllOk s.snd.snd) : AllOk (muStep tl F s mu).snd.snd :=
  foldl_keeps (fun r : MProd Nat (Array E) => AllOk r.snd) (unStep tl F mu s.fst)
    (fun r un hr => allOk_un tl F mu s.fst r un hr) [0, 2] ⟨s.snd.fst, s.snd.snd⟩ h

/-- **Each entry of the second computation is a word below the prime.** -/
theorem readAgain_ok (tl : HTailF2) (F : Fork) : AllOk (tl.readWeightsAgain F) := by
  rw [readAgain_fold]
  refine foldl_keeps (fun r : MProd Nat (MProd Nat (Array E)) => AllOk r.snd.snd) (muStep tl F)
    (fun r mu hr => allOk_mu tl F r mu hr) (List.range tl.NM)
    ⟨0, 0, Array.replicate (2 * tl.mz) zeroE⟩ ?_
  · intro x
    have e0 : (Array.replicate (2 * tl.mz) zeroE).getD x zeroE = zeroE := by
      rw [Array.getD_eq_getD_getElem?, Array.getElem?_replicate]
      split <;> rfl
    show OnBytes.okE ((Array.replicate (2 * tl.mz) zeroE).getD x zeroE) = true
    rw [e0]
    rfl

end VerifiableInference.Desc.First.K8.Honest

#print axioms VerifiableInference.Desc.First.K8.Honest.colAt_zero
#print axioms VerifiableInference.Desc.First.K8.Honest.colAt_succ
#print axioms VerifiableInference.Desc.First.K8.Honest.val_modify
#print axioms VerifiableInference.Desc.First.K8.Honest.size_jStep
#print axioms VerifiableInference.Desc.First.K8.Honest.fold_j
#print axioms VerifiableInference.Desc.First.K8.Honest.fold_sg
#print axioms VerifiableInference.Desc.First.K8.Honest.fold_fn
#print axioms VerifiableInference.Desc.First.K8.Honest.fold_un
#print axioms VerifiableInference.Desc.First.K8.Honest.rowsBefore_succ
#print axioms VerifiableInference.Desc.First.K8.Honest.mat_of_mem
#print axioms VerifiableInference.Desc.First.K8.Honest.fold_mu
#print axioms VerifiableInference.Desc.First.K8.Honest.readAgain_sum
#print axioms VerifiableInference.Desc.First.K8.Honest.allOk_modify
#print axioms VerifiableInference.Desc.First.K8.Honest.foldl_keeps
#print axioms VerifiableInference.Desc.First.K8.Honest.allOk_j
#print axioms VerifiableInference.Desc.First.K8.Honest.allOk_sg
#print axioms VerifiableInference.Desc.First.K8.Honest.allOk_fn
#print axioms VerifiableInference.Desc.First.K8.Honest.allOk_un
#print axioms VerifiableInference.Desc.First.K8.Honest.allOk_mu
#print axioms VerifiableInference.Desc.First.K8.Honest.readAgain_ok
