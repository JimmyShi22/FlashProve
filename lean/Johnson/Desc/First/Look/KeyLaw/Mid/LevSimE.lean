-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Look/KeyLaw/Mid/LevSimE.lean: the table's tree in the course over the field
(`cTable`, Course.lean) goes with `A.tableRun L` (LevRunD.lean), between the relations `Sim` at the
seams 4 and 5 (Relation.lean). The course is our text of the program's lookup, over the field. That
the program's run, read in the field, is this course is not shown here.

Main names:
  `rdRow_nil`, `rows_read` a row without terms on the table of bits is read by `rd0`.
  `ownN_sum` the number of mask entries of n levels, as a sum over a range.
  `table_goes` the field `table` of `Sims`.
Limits: D.S = A.toPub; 1 ≤ d; `PlAt` at each of the d levels (the orders and places are the
course's).

-/
import Johnson.Desc.First.Look.KeyLaw.Mid.LevSimD

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Lk6.Mid
open Lk6.PortSim
open OnBytes OnBytes.Slice Flat Lev

variable (A : Dat GE) (sl : Slot → A.J)

theorem rdRow_nil (r : RowF) (h : r.maps = []) : rdRow A sl r = rd0 sl r := by
  unfold rdRow rd0
  rw [h]
  refine congrArg (fun c => (⟨c, r.target⟩ : Cb.LdLkp.Row GE A.J)) (funext fun j => ?_)
  show rdMF sl r.masks j + 0 = _
  rw [add_zero]

theorem rows_read (old new : List RowF) (hn : ∀ r ∈ new, r.maps = []) :
    (old ++ new).map (rdRow A sl) = old.map (rdRow A sl) ++ new.map (rd0 sl) := by
  rw [List.map_append]
  exact congrArg (old.map (rdRow A sl) ++ ·)
    (List.map_congr_left fun r hr => rdRow_nil A sl r (hn r hr))

theorem ownN_sum (g : ℕ) : ∀ n, ownN g n = ((List.range n).map fun l => 2 * (g + l) + 5).sum
  | 0 => rfl
  | n + 1 => by
    rw [List.range_succ, List.map_append, List.sum_append, ← ownN_sum g n]
    show ownN g n + (2 * (g + n) + 5) = ownN g n + (2 * (g + n) + 5 + 0)
    rw [Nat.add_zero]

/-- **The table's tree.** -/
theorem table_goes (L : LevPl A) (D : Dt) (st : A.St) (own idx : ℕ) (hS : D.S = A.toPub)
    (hd : 1 ≤ A.d)
    (hp : ∀ l < A.d, PlAt sl D (A.tabD L) false l (own + ownAt A.toPub 4 + ownN A.mu l)
      (idx + idxAt A.toPub 4)) :
    Goes (Sim A sl st own idx 4) (Sim A sl st own idx 5) (cTable D) (A.tableRun L)
      (fmT A.mu (A.d - 1)) := by
  intro s x hs hf
  obtain ⟨n, hn⟩ : ∃ n, A.d = n + 1 := ⟨A.d - 1, by omega⟩
  have hn' : A.d - 1 = n := by omega
  rw [hn', fmT_eq] at hf ⊢
  obtain ⟨ht1, ht2, ht3⟩ := hs.top (by omega) (by omega)
  have hlen : s.top.point.length = A.mu + 0 := ht2
  have hrel : RelC sl s.top (A.tabIn x).2 :=
    ⟨List.ext_getElem (by
        show (List.ofFn fun i : Fin (A.mu + 0) => x.pt i).length = _
        rw [List.length_ofFn, hlen]) fun i _ h2 => by
        show (List.ofFn fun i : Fin (A.mu + 0) => x.pt i)[i] = _
        rw [List.getElem_ofFn, ht3 i h2, List.getD_eq_getElem _ _ h2],
      by
        show x.top.mf = _
        rw [ht1]
        rfl,
      by
        show x.top.tg = _
        rw [ht1]
        rfl⟩
  have r := tree_goes sl D (A.tabD L) s.top (A.tabIn x).2 s hrel false n
    (fun l hl => by
      rw [hs.own, hs.idx]
      exact hp l (by omega))
    (by
      rw [hs.own, hs.idx]
      exact hp n (by omega)) hf
  have eC : cTable D s =
      { (cLevels D false A.mu (n + 1) 0 s.top s).2 with
        top := (cLevels D false A.mu (n + 1) 0 s.top s).1 } := by
    unfold cTable
    rw [hS]
    show ({ (cLevels D false A.mu A.d 0 s.top s).2 with
      top := (cLevels D false A.mu A.d 0 s.top s).1 } : Cs) = _
    rw [hn]
  have eR : A.tableRun L x (s.rounds.take (fmN A.mu (n + 1)).length) =
      A.tabBack (x, stepsN (A.tabD L) (n + 1) (A.tabIn x).2
        (s.rounds.take (fmN A.mu (n + 1)).length)) := by
    unfold Dat.tableRun
    rw [hn']
    exact congrArg A.tabBack (treeStep_eq (A.tabD L) x (A.tabIn x).2 n _)
  rw [eC, eR]
  generalize cLevels D false A.mu (n + 1) 0 s.top s = cs at r
  generalize stepsN (A.tabD L) (n + 1) (A.tabIn x).2 (s.rounds.take (fmN A.mu (n + 1)).length) =
    a' at r
  obtain ⟨r1, r2, r3⟩ := r
  obtain ⟨new, hnew, e1, e2⟩ := r3.rows
  refine ⟨⟨hs.st, ?_, ?_, ?_, ?_, fun h => absurd h (by decide), fun h => absurd h (by decide),
    fun _ h => absurd h (by decide), fun _ _ => ⟨?_, ?_, ?_⟩, fun _ i hi => ?_,
    fun h => absurd h (by decide)⟩, r3.rounds⟩
  · show x.al = cs.2.alpha
    rw [r3.same.alpha]
    exact hs.al
  · show x.rows ++ a'.rows = cs.2.rows.map (rdRow A sl)
    rw [e1, e2, rows_read A sl _ _ hnew, hs.rows]
    rfl
  · show cs.2.own = own + ownAt A.toPub 5
    have e5 : ownAt A.toPub 5 =
        ownAt A.toPub 4 + ((List.range A.d).map fun l => 2 * (A.mu + l) + 5).sum := by
      simp only [ownAt]
    rw [r3.own, hs.own, e5, ← ownN_sum, hn, if_neg (by decide), Nat.add_assoc]
    rfl
  · show cs.2.idx = idx + idxAt A.toPub 5
    rw [r3.idx, hs.idx]
    rfl
  · show (⟨a'.mf, a'.tg⟩ : SCl GE A.J) = rdS A sl cs.1
    rw [r1.mf, r1.tg]
    rfl
  · show cs.1.point.length = A.mu + A.d
    rw [r2, hn]
    rfl
  · intro t ht
    show (if t < A.mu + (A.d - 1 + 1) then a'.pt.getD t 0 else 0) = cs.1.point.getD t 0
    have ht' : t < cs.1.point.length := ht
    rw [r2] at ht'
    rw [if_pos (by omega), r1.pt]
  · show x.cls i = rdCl A sl cs.2.alpha (A.v i) (cs.2.leaves i)
    rw [r3.same.alpha, r3.same.leaves]
    exact hs.cls (by omega) i hi

end Lk6.Mid

#print axioms Lk6.Mid.table_goes
