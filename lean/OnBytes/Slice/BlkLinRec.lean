-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/BlkLinRec.lean: the row of a stored table's record on the folded row, in closed form.

Where tables have a record, the block that folds a stored table's rows puts aside one plain row for
each seed of the record (OnBytes/Iop/Foldeq.lean: foldeqJoined, foldeqRecordRow): all rows' answers
under that seed, folded. This file reads that row as coefficients on entries, at every index
(LinF.rec, read_recordRow). On the entries of the folded message before the pads it has the weights
of the seed's point; on the three pads of its own answer the seed's factor times 1, X, X^2; on the
pads of the other answers 0; and beyond the message 0. Its target is the sum of the rows' answers
under the weights of the fold's point.

The program makes the row of a tensor cut at the message's length, and mends it at each pad by a
coefficient on a single entry: the closed form has the same two parts.

Main definitions: `LinF.padList`, `LinF.rec`.
Main theorems: `foldl_pairs`, `coefAt_unitFold`, `unitFold_keeps`, `readE_maddFold`,
`read_recordRow`.

Not claimed. Nothing on a run. Nothing on what a record is good for.

-/
import OnBytes.Slice.BlkLinRead
import OnBytes.Slice.BlkTensCut

set_option autoImplicit false

namespace OnBytes.Slice
open Prob Cb
open OnBytes.Params (FoldeqShape)

/-- A loop inside a loop, as one loop over the pairs. -/
theorem foldl_pairs {β : Type} (g : β → ℕ → ℕ → β) (m : List ℕ) : ∀ (l : List ℕ) (b : β),
    l.foldl (fun r a => m.foldl (fun r t => g r a t) r) b =
      (l.flatMap fun a => m.map fun t => (a, t)).foldl (fun r q => g r q.1 q.2) b
  | [], _ => rfl
  | a :: l, b => by
    rw [List.foldl_cons, List.flatMap_cons, List.foldl_append, List.foldl_map, foldl_pairs g m l]

/-- **Coefficients on single entries, added one after the other.** -/
theorem coefAt_unitFold {α : Type} (o : ℕ) (part : Part) (f : α → ℕ) (c : α → E) :
    ∀ (l : List α) (r : Row) (o' : ℕ) (part' : Part) (i : ℕ),
    coefAt (l.foldl (fun r q => r.addUnit o part (f q) (c q)) r) o' part' i =
      coefAt r o' part' i +
        (l.map fun q => if o == o' && part == part' && f q == i then readE (c q) else 0).sum
  | [], r, o', part', i => by simp
  | q :: l, r, o', part', i => by
    rw [List.foldl_cons, coefAt_unitFold o part f c l, coefAt_addUnit, List.map_cons, List.sum_cons,
      add_assoc]

/-- They leave the row's kind and target. -/
theorem unitFold_keeps {α : Type} (o : ℕ) (part : Part) (f : α → ℕ) (c : α → E) :
    ∀ (l : List α) (r : Row),
    (l.foldl (fun r q => r.addUnit o part (f q) (c q)) r).kind = r.kind ∧
      (l.foldl (fun r q => r.addUnit o part (f q) (c q)) r).target = r.target
  | [], _ => ⟨rfl, rfl⟩
  | q :: l, r => unitFold_keeps o part f c l (r.addUnit o part (f q) (c q))

/-- A sum of products, made one after the other. -/
theorem readE_maddFold (a b : ℕ → E) : ∀ (l : List ℕ) (t : E),
    readE (l.foldl (fun t r => maddE t (a r) (b r)) t) =
      readE t + (l.map fun r => readE (a r) * readE (b r)).sum
  | [], t => by simp
  | r :: l, t => by
    rw [List.foldl_cons, readE_maddFold a b l, readE_maddE, List.map_cons, List.sum_cons, add_assoc]

namespace LinF

/-- The pads of a row's message: the number of the answer, and the coordinate. -/
def padList (answers : ℕ) : List (ℕ × ℕ) :=
  (List.range answers).flatMap fun a => (List.range 3).map fun t => (a, t)

/-- **The row of the record's answer number i, folded.** The folded row lies in the main table of
the oracle message u, laid by lay. ell: the length of a row's message; its last 3 · answers entries
are pads. z, beta: the seed's point and factor. -/
def rec (lay : VectorLay) (u ell answers : ℕ) (z : List GE) (beta : GE) (i : ℕ) (target : GE) :
    RowF where
  coef o part idx :=
    (if u == o && Part.main == part then
        laid lay (fun e => if e < ell then eqW z.length (fun t => z.getD t 0) e else 0) idx
      else 0) +
      ((padList answers).map fun q =>
        if u == o && Part.main == part && lay.index (ell - 3 * answers + 3 * q.1 + q.2) == idx then
          (if q.1 == i then beta * readE (thetaE q.2) else 0) -
            eqW z.length (fun t => z.getD t 0) (ell - 3 * answers + 3 * q.1 + q.2)
        else 0).sum
  target := target

end LinF

/-- **The program's row of the record's answer number i, read.** -/
theorem read_recordRow (S : FoldeqShape) (seed : SampleSeed) (record : Array E) (i : ℕ)
    (eqGamma : Array E) (u : FoldedRow) (r : Row) (hb : S.index.cubeBits ≤ u.lay.bits)
    (hell : S.index.code.ell ≤ 2 ^ S.index.cubeBits)
    (h : foldeqRecordRow S seed record i eqGamma u = some r) :
    r.kind = .plain ∧
      readRow r = LinF.rec u.lay u.oracle S.index.code.ell S.index.answers (seed.z.map readE)
        (readE seed.beta) i
        ((List.range S.index.rows).map fun j => readE (eqGamma.getD j zeroE) *
          readE (record.getD (j * S.index.answers + i) zeroE)).sum := by
  unfold foldeqRecordRow at h
  by_cases hg : (seed.z.length == S.index.cubeBits &&
      record.size == S.index.rows * S.index.answers) = true
  · simp only [hg, guard, if_true, Option.bind_eq_bind, Option.pure_def, Option.bind_some] at h
    obtain ⟨cut, hcut, hr⟩ := Option.bind_eq_some_iff.1 h
    obtain rfl := Option.some.inj hr
    have hz : seed.z.length = S.index.cubeBits := by
      simp only [Bool.and_eq_true, beq_iff_eq] at hg
      exact hg.1
    have hfold := foldl_pairs (fun (r : Row) a t =>
      r.addUnit u.oracle .main (u.lay.index (S.index.padPlace a t))
        (subE (if a == i then mulE seed.beta (thetaE t) else zeroE)
          ((Tensor.eq seed.z).entry (S.index.padPlace a t)))) (List.range 3)
      (List.range S.index.answers) (u.addAll {} cut)
    have hkeep := unitFold_keeps u.oracle .main
      (fun q : ℕ × ℕ => u.lay.index (S.index.padPlace q.1 q.2))
      (fun q => subE (if q.1 == i then mulE seed.beta (thetaE q.2) else zeroE)
        ((Tensor.eq seed.z).entry (S.index.padPlace q.1 q.2)))
      (LinF.padList S.index.answers) (u.addAll {} cut)
    have hw : ∀ e, readE ((Tensor.eq seed.z).entry e) =
        eqW (seed.z.map readE).length (fun t => (seed.z.map readE).getD t 0) e := fun e => by
      rw [readE_eqList, readE_one, one_mul]
    refine ⟨?_, ?_⟩
    · show (List.foldl _ (u.addAll {} cut) (List.range S.index.answers)).kind = _
      rw [hfold]
      exact hkeep.1.trans (addLaid_keeps u.oracle u.lay cut {}).2
    · unfold readRow LinF.rec
      refine congrArg₂ RowF.mk (funext fun o => funext fun part => funext fun idx => ?_) ?_
      · show coefAt (List.foldl _ (u.addAll {} cut) (List.range S.index.answers)) o part idx = _
        rw [hfold]
        refine (coefAt_unitFold u.oracle .main
          (fun q : ℕ × ℕ => u.lay.index (S.index.padPlace q.1 q.2))
          (fun q => subE (if q.1 == i then mulE seed.beta (thetaE q.2) else zeroE)
            ((Tensor.eq seed.z).entry (S.index.padPlace q.1 q.2)))
          (LinF.padList S.index.answers) (u.addAll {} cut) o part idx).trans ?_
        refine congrArg₂ (· + ·) ?_ (congrArg List.sum (List.map_congr_left fun q _ => ?_))
        · show coefAt (addLaid {} u.oracle u.lay cut) o part idx = _
          rw [coefAt_addLaid, coefAt_empty, zero_add]
          split
          · have hsh := tensorBelow_shape_at (Tensor.eq seed.z) rfl 0 S.index.cubeBits
              S.index.code.ell cut hcut
            rw [sum_onTable u.lay S.index.cubeBits cut
              (fun w hw' => ⟨((hsh w hw').1).trans ((vars_eqTensor _ _).trans hz), (hsh w hw').2⟩)
              hb idx]
            unfold laid
            have hs := sum_tensorBelow_at rdE (Tensor.eq seed.z) rfl 0 S.index.cubeBits
              S.index.code.ell cut hcut (u.lay.entryAt (idx % 2 ^ u.lay.bits))
            simp only [rdE_val, pow_zero, Nat.div_one] at hs
            beta_reduce
            rw [hs]
            by_cases h1 : u.lay.entryAt (idx % 2 ^ u.lay.bits) < 2 ^ S.index.cubeBits
            · rw [if_pos h1, Nat.mod_eq_of_lt h1, hw]
            · rw [if_neg h1, if_neg fun h2 => h1 (lt_of_lt_of_le h2 hell)]
          · rfl
        · show (if _ then readE (subE _ _) else 0) = _
          have hp : S.index.padPlace q.1 q.2 =
              S.index.code.ell - 3 * S.index.answers + 3 * q.1 + q.2 := rfl
          rw [readE_sub, hw, hp]
          by_cases hq : (q.1 == i) = true
          · simp only [hq, if_true, readE_mul]
          · simp only [hq, Bool.false_eq_true, if_false, readE_zero]
      · show readE (List.foldl _ zeroE (List.range S.index.rows)) = _
        rw [readE_maddFold (fun j => eqGamma.getD j zeroE)
          (fun j => record.getD (j * S.index.answers + i) zeroE), readE_zero, zero_add]
  · simp [hg, guard] at h

end OnBytes.Slice
