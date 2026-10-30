-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Fmt/M2BatchEq.lean: the second toy (a test protocol, a chain of three links): the closing that the
decision runs (`batch`) equals its meaning (`batchLit`: every row written out), at the blocks of
Fmt/M2All.lean and the draws' rows `drawL` (Fmt/M2Loc.lean), under conditions on sizes.

Theorems. Core Lean. Many statements of this library are written twice: a definition in the
namespace `Spec` states a proposition, and a theorem of the same name outside that namespace proves
it (lean/GLOSSARY.md).

A row is a linear claim: vectors of coefficients, called forms, on tables, with a target value. At
the closing of a group the verifier draws one element theta and sums all open rows of the group
under its powers. A draw is a position that the verifier has drawn; `drawL` makes the rows of one
draw. A block is the function of one step of the protocol. The frame is the decision's pass through
the rounds of the chain of links (`decBy`, `goLinks`, Fmt/M2Dec.lean). What waits from the former
link is the record `Wait` (Fmt/M2Dec.lean). The head of Fmt/M2Loc.lean says what the switch between
two links, the carrying message and the kept message sent anew are.
`batch` (Fmt/M2Dec.lean), which the decision runs, batches the open rows of a group member by
member, lets a block add the draws' rows onto the sum so far without writing them out, and lays the
result into the group's table once. The meaning (Fmt/M2Close.lean: batchLit) writes every row out on
the group's tables, in the text's order, and sums them under the powers of the batching element.
Here, under the conditions below: the two give the same row, or both none.

Main names:
  `Spec.batch_none`, `batch_none`: the case in which nothing waits (the first link): for a list of
    rows that is not empty, `batch` = `batchLit`, whatever the blocks.
  `Spec.batch_some`, `batch_some`: the case in which something waits: at the blocks of
    Fmt/M2All.lean (`blocks`) and the draws' rows `drawL`, `batch` = `batchLit` under four
    conditions on sizes:
      the group has a member;
      a kept row has its three pad places (3 ≤ l);
      the sum of the rows in front of the draws (`frontSum`) has on the carrying message a form
        of 2 l entries,
      and on the kept message sent anew one of l entries (none if nothing was kept).
    The last two are equations between numbers, to be evaluated at given data. The last three are
    hypotheses of `sumDrawsFrom_eq` (Fmt/M2LocEq.lean).
  `condAt`, `batchC`, `Spec.batchC_lit`, `batchC_lit`: the conditions as a test that can be run; the
    closing that refuses where the test fails; where it gives a row, `batch` (the fast closing) and
    the meaning give that row.
  `rel_draws`: under the hypotheses of its statement, a row of a switch touches the group's first
    two members alone, and a step with the empty form leaves a sum as it is. The arithmetic is on
    words: a sum or a product is reduced modulo p, an input need not be. But every entry of a sum is
    the output of an addition, so its words are below p (`Can`, Fmt/M1CsEq.lean).
  `toK_congr`: the row on the group reads only the target and the forms of the group's own members.

Limits: this file does not say that the conditions on the sums' sizes hold at every view (not here:
Fmt/M2DecEq.lean; there: where the frame's test on sizes has passed). It does not say that
`batchLit` is what the programs (the C++ implementation that comes with this Lean code) compute. It
says nothing on soundness.

Terms: lean/GLOSSARY.md.
-/
import Fmt.M2CloseEq
import Fmt.M2LocEq
import Fmt.M2All

set_option autoImplicit false

namespace Fmt.M2.BatchEq
open Fmt.M1 Fmt.M1.CsEq Fmt.M2.CloseEq Fmt.M2.LocEq

/-! ## The entries of a sum have their words below p; a step with the empty form -/

theorem can_axpy (f : Fld) (u : Array E) (s : E) (v : Array E) : Can f (axpy f u s v).toList := by
  rw [axpy_stepL]
  exact can_stepL f _ s _

theorem axpy_empty (f : Fld) (a : Array E) (s : E) (h : Can f a.toList) : axpy f a s #[] = a := by
  rw [axpy_stepL]
  show (stepL f a.toList s []).toArray = a
  rw [step_nil f _ s h]

/-- all forms of a row have their words below p -/
def Hc (f : Fld) (M : MRow) : Prop :=
  (∀ j, Can f (M.main.getD j #[]).toList) ∧ ∀ j, Can f (M.mask.getD j #[]).toList

theorem hc_step (f : Fld) (x : E) (s : MRow × E) (R : MRow) : Hc f (stM f x s R).1 :=
  ⟨fun j => by
    show Can f ((axpyL f s.1.main s.2 R.main).getD j #[]).toList
    rw [axpyL_getD]
    exact can_axpy f _ _ _,
   fun j => by
    show Can f ((axpyL f s.1.mask s.2 R.mask).getD j #[]).toList
    rw [axpyL_getD]
    exact can_axpy f _ _ _⟩

theorem hc_fold (f : Fld) (x : E) :
    ∀ (rows : List MRow) (s : MRow × E), Hc f s.1 → Hc f (rows.foldl (stM f x) s).1
  | [], _, h => h
  | R :: rows, s, _ => hc_fold f x rows (stM f x s R) (hc_step f x s R)

theorem hc_start (f : Fld) : Hc f ⟨[], [], Fld.zeroE⟩ := ⟨fun _ => can_nil f, fun _ => can_nil f⟩

/-! ## The meaning's nested fold is the fold over the flat list -/

def stL (f : Fld) (theta : E) (s : LRow × E) (r : LRow) : LRow × E :=
  (s.1.add f s.2 r, f.mulE s.2 theta)

/-- one draw of the literal sum -/
def stX (f : Fld) (C Z : Code) (kept : Bool) (S : KSRow) (theta : E) (col : Nat → Option KCol)
    (acc : Option (LRow × E)) (x : Nat) : Option (LRow × E) :=
  match acc, col x with
  | some a, some cl => some ((drawL f C Z kept S x cl).foldl (stL f theta) a)
  | _, _ => none

theorem lit_fold (f : Fld) (C Z : Code) (kept : Bool) (S : KSRow) (theta : E) (start : LRow)
    (first : E) (xs : List Nat) (col : Nat → Option KCol) :
    sumDrawsFromLit f C Z kept S theta start first xs col =
      xs.foldl (stX f C Z kept S theta col) (some (start, first)) := rfl

theorem fold_none (f : Fld) (C Z : Code) (kept : Bool) (S : KSRow)
    (theta : E) (col : Nat → Option KCol) :
    ∀ xs : List Nat, xs.foldl (stX f C Z kept S theta col) none = none
  | [] => rfl
  | _ :: xs => fold_none f C Z kept S theta col xs

theorem lit_flat (P : Par) (kept : Bool) (S : KSRow) (theta : E) (col : Nat → Option KCol) :
    ∀ (xs : List Nat) (a : LRow × E), xs.foldl (stX P.fld P.C P.Z kept S theta col) (some a) =
      (drawsLit drawL P kept S col xs).map fun ds => ds.foldl (stL P.fld theta) a
  | [], _ => rfl
  | x :: xs, a => by
      show xs.foldl (stX P.fld P.C P.Z kept S theta col)
          (stX P.fld P.C P.Z kept S theta col (some a) x) = _
      unfold drawsLit stX
      cases hc : col x with
      | none =>
          show xs.foldl (stX P.fld P.C P.Z kept S theta col) none = _
          rw [fold_none]
          rfl
      | some cl =>
          show xs.foldl (stX P.fld P.C P.Z kept S theta col)
              (some ((drawL P.fld P.C P.Z kept S x cl).foldl (stL P.fld theta) a)) = _
          rw [lit_flat P kept S theta col xs]
          cases drawsLit drawL P kept S col xs with
          | none => rfl
          | some rest =>
              show some (rest.foldl (stL P.fld theta) _) =
                some ((drawL P.fld P.C P.Z kept S x cl ++ rest).foldl (stL P.fld theta) a)
              rw [List.foldl_append]

/-! ## A switch's row touches the first two members alone -/

theorem toM_main (n : Nat) (R : LRow) (j : Nat) :
    (R.toM n).main.getD j #[] =
      if j < n then (if j == 0 then R.g else if j == 1 then R.p else #[]) else #[] := by
  show ((List.range n).map fun j => if j == 0 then R.g else if j == 1 then R.p else #[]).getD
      j #[] = _
  rw [List.getD_eq_getElem?_getD, List.getElem?_map]
  by_cases h : j < n
  · rw [List.getElem?_range h, if_pos h]
    rfl
  · rw [List.getElem?_eq_none (by rw [List.length_range]; omega), if_neg h]
    rfl

/-- what the two folds over a switch's rows have in common -/
structure Rel (n : Nat) (M0 : MRow) (sM : MRow × E) (sL : LRow × E) : Prop where
  pw   : sM.2 = sL.2
  t    : sM.1.t = sL.1.t
  g    : sM.1.main.getD 0 #[] = sL.1.g
  p    : 1 < n → sM.1.main.getD 1 #[] = sL.1.p
  rest : ∀ j, 2 ≤ j → sM.1.main.getD j #[] = M0.main.getD j #[]
  mask : ∀ j, sM.1.mask.getD j #[] = M0.mask.getD j #[]

theorem rel_step (f : Fld) (theta : E) (n : Nat) (hn : 0 < n) (M0 : MRow) (h0 : Hc f M0)
    (sM : MRow × E) (sL : LRow × E) (h : Rel n M0 sM sL) (r : LRow) :
    Rel n M0 (stM f theta sM (r.toM n)) (stL f theta sL r) where
  pw := by
    show f.mulE sM.2 theta = f.mulE sL.2 theta
    rw [h.pw]
  t := by
    show f.addE sM.1.t (f.mulE sM.2 r.t) = f.addE sL.1.t (f.mulE sL.2 r.t)
    rw [h.t, h.pw]
  g := by
    show (axpyL f sM.1.main sM.2 (r.toM n).main).getD 0 #[] = axpy f sL.1.g sL.2 r.g
    rw [axpyL_getD, toM_main, if_pos hn, h.g, h.pw]
    rfl
  p := fun h1 => by
    show (axpyL f sM.1.main sM.2 (r.toM n).main).getD 1 #[] = axpy f sL.1.p sL.2 r.p
    rw [axpyL_getD, toM_main, if_pos h1, h.p h1, h.pw]
    rfl
  rest := fun j hj => by
    show (axpyL f sM.1.main sM.2 (r.toM n).main).getD j #[] = _
    have e : (r.toM n).main.getD j #[] = #[] := by
      rw [toM_main]
      by_cases hjn : j < n
      · rw [if_pos hjn]
        have a0 : (j == 0) = false := by simp; omega
        have a1 : (j == 1) = false := by simp; omega
        simp [a0, a1]
      · rw [if_neg hjn]
    rw [axpyL_getD, e, h.rest j hj, axpy_empty f _ _ (h0.1 j)]
  mask := fun j => by
    show (axpyL f sM.1.mask sM.2 []).getD j #[] = _
    rw [axpyL_getD, h.mask j]
    show axpy f _ _ #[] = _
    exact axpy_empty f _ _ (h0.2 j)

theorem rel_draws (f : Fld) (theta : E) (n : Nat) (hn : 0 < n) (M0 : MRow) (h0 : Hc f M0) :
    ∀ (ds : List LRow) (sM : MRow × E) (sL : LRow × E), Rel n M0 sM sL →
      Rel n M0 ((ds.map (·.toM n)).foldl (stM f theta) sM) (ds.foldl (stL f theta) sL)
  | [], _, _, h => h
  | r :: ds, sM, sL, h =>
    rel_draws f theta n hn M0 h0 ds _ _ (rel_step f theta n hn M0 h0 sM sL h r)

/-! ## The row on the group reads the target and the forms of the group's own members alone -/

theorem pickRow_lt :
    ∀ (L : List (Option Nat × Nat)) (r j0 j st b : Nat),
      pickRow L r j0 = some (j, st, b) → j < j0 + L.length
  | [], _, _, _, _, _, h => by cases h
  | (some s, c) :: xs, r, j0, j, st, b, h => by
      unfold pickRow at h
      by_cases hc : (s ≤ r && r < s + 2 ^ c) = true
      · rw [if_pos hc] at h
        have e : j0 = j := congrArg (·.1) (Option.some.inj h)
        simp only [List.length_cons]
        omega
      · rw [if_neg hc] at h
        have := pickRow_lt xs r (j0 + 1) j st b h
        simp only [List.length_cons]
        omega
  | (none, c) :: xs, r, j0, j, st, b, h => by
      unfold pickRow at h
      have := pickRow_lt xs r (j0 + 1) j st b h
      simp only [List.length_cons]
      omega

theorem keptFrom_lt : ∀ (ms : List Mem) (j0 j : Nat), keptFrom ms j0 = some j → j < j0 + ms.length
  | [], _, _, h => by cases h
  | m :: ms, j0, j, h => by
      unfold keptFrom at h
      by_cases hk : m.kept = true
      · rw [if_pos hk] at h
        have e : j0 = j := Option.some.inj h
        simp only [List.length_cons]
        omega
      · rw [if_neg hk] at h
        have := keptFrom_lt ms (j0 + 1) j h
        simp only [List.length_cons]
        omega

theorem layAll_congr (w n : Nat) (L : List (Option Nat × Nat)) (A B : List (Array E))
    (h : ∀ j, j < L.length → A.getD j #[] = B.getD j #[]) :
    layAll w n L A = layAll w n L B := by
  apply ext_ent
  · rw [size_layAll, size_layAll]
  · intro i hi
    rw [size_layAll] at hi
    rw [ent_layAll _ _ _ _ i hi, ent_layAll _ _ _ _ i hi]
    cases hp : pickRow L (i % 2 ^ w) 0 with
    | none => rfl
    | some x =>
        obtain ⟨j, st, b⟩ := x
        show ent (A.getD j #[]) _ = ent (B.getD j #[]) _
        rw [h j (by have := pickRow_lt L _ 0 j st b hp; omega)]

theorem toK_congr (ms : List Mem) (l lz : Nat) (A B : MRow)
    (hm : ∀ j, j < ms.length → A.main.getD j #[] = B.main.getD j #[])
    (hk : ∀ j, j < ms.length → A.mask.getD j #[] = B.mask.getD j #[]) (ht : A.t = B.t) :
    toK ms l lz A = toK ms l lz B := by
  unfold toK
  rw [layAll_congr _ _ _ A.main B.main
        (fun j hj => hm j (by simp only [List.length_zip, List.length_map] at hj; omega)),
    layAll_congr _ _ _ A.mask B.mask
      (fun j hj => hk j (by simp only [List.length_zip, List.length_map] at hj; omega)), ht]
  cases hi : keptIdx ms with
  | none => rfl
  | some j =>
      have := keptFrom_lt ms 0 j hi
      simp only [hm j (by omega)]

/-- The list that `batch` puts together after the draws, member by member. -/
theorem put_getD (n : Nat) (g p : Array E) (M : List (Array E)) (j : Nat) (hj : j < n) :
    ((g :: p :: M.drop 2).take n).getD j #[] =
      if j = 0 then g else if j = 1 then p else M.getD j #[] := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_take_of_lt hj]
  match j with
  | 0 => rfl
  | 1 => rfl
  | j + 2 =>
      show ((M.drop 2)[j]?).getD #[] = M.getD (j + 2) #[]
      rw [List.getElem?_drop, List.getD_eq_getElem?_getD, Nat.add_comm 2 j]

/-! ## The two theorems (`batch_none`, `batch_some`), and the closing that tests their conditions
(`batchC`, `batchC_lit`) -/

def Spec.batch_none : Prop :=
  ∀ (B : Blocks) (dl : DrawL) (P : Par) (V : M1.View) (m : Nat) (plain : List MRow) (theta : E),
    plain ≠ [] → batch B P V m none plain theta = batchLit B dl P V m none plain theta

theorem batch_none : Spec.batch_none := by
  intro B dl P V m plain theta h
  show some (toK (memsOf P.links m) P.C.l P.Z.l (sumM P.fld theta plain)) =
    some (sumK P.fld theta (plain.map (toK (memsOf P.links m) P.C.l P.Z.l)))
  rw [toK_sumM P.fld theta _ _ _ plain h]

/-- The core of `batch_some`, on plain arguments. F: the rows of the switch in front (not empty:
`hF`); plain: the link's own rows; M: their sum. -/
theorem core (P : Par) (kept : Bool) (S : KSRow) (theta : E) (col : Nat → Option KCol)
    (xs : List Nat) (ms : List Mem) (l lz : Nat) (F : List LRow) (plain : List MRow) (M : MRow × E)
    (hM : M = sumMFrom P.fld theta Fld.oneE (F.map (·.toM ms.length) ++ plain))
    (hF : F ≠ []) (hn : 0 < ms.length) (h3 : kept = true → 3 ≤ P.C.l)
    (hg : (M.1.main.getD 0 #[]).size = 2 * P.C.l)
    (hp : (M.1.main.getD 1 #[]).size = (if kept then P.C.l else 0)) :
    (match sumDrawsFrom P.fld P.C P.Z kept S theta ⟨M.1.main.getD 0 #[], M.1.main.getD 1 #[], M.1.t⟩ M.2 xs col with
      | some (D, _) =>
        some (toK ms l lz ⟨(D.g :: D.p :: M.1.main.drop 2).take ms.length, M.1.mask, D.t⟩)
      | none => none) =
    ((drawsLit drawL P kept S col xs).map fun ds =>
      F.map (fun R => toK ms l lz (R.toM ms.length)) ++ (plain.map (toK ms l lz) ++ ds.map fun R => toK ms l lz (R.toM ms.length))).map (sumK P.fld theta) := by
  have hcM : Hc P.fld M.1 := by
    rw [hM, sumMFrom_fold]
    exact hc_fold _ _ _ _ (hc_start _)
  have e1 := sumDrawsFrom_eq P.fld P.C P.Z kept S theta
    ⟨M.1.main.getD 0 #[], M.1.main.getD 1 #[], M.1.t⟩ M.2 xs col h3 hg hp (hcM.1 0) (hcM.1 1)
  rw [e1, lit_fold, lit_flat]
  cases drawsLit drawL P kept S col xs with
  | none => rfl
  | some ds =>
      have rel := rel_draws P.fld theta ms.length hn M.1 hcM ds M
        (⟨M.1.main.getD 0 #[], M.1.main.getD 1 #[], M.1.t⟩, M.2)
        ⟨rfl, rfl, rfl, fun _ => rfl, fun _ _ => rfl, fun _ => rfl⟩
      show (match some
        (ds.foldl (stL P.fld theta) (⟨M.1.main.getD 0 #[], M.1.main.getD 1 #[], M.1.t⟩, M.2)) with
          | some (D, _) =>
            some (toK ms l lz ⟨(D.g :: D.p :: M.1.main.drop 2).take ms.length, M.1.mask, D.t⟩)
          | none => none) =
        some (sumK P.fld theta
            (F.map (fun R => toK ms l lz (R.toM ms.length)) ++
              (plain.map (toK ms l lz) ++ ds.map fun R => toK ms l lz (R.toM ms.length))))
      generalize ds.foldl (stL P.fld theta)
          (⟨M.1.main.getD 0 #[], M.1.main.getD 1 #[], M.1.t⟩, M.2) = r at rel ⊢
      obtain ⟨D, pw⟩ := r
      show some (toK ms l lz ⟨(D.g :: D.p :: M.1.main.drop 2).take ms.length, M.1.mask, D.t⟩) =
        some (sumK P.fld theta
            (F.map (fun R => toK ms l lz (R.toM ms.length)) ++
              (plain.map (toK ms l lz) ++ ds.map fun R => toK ms l lz (R.toM ms.length))))
      have el : F.map (fun R => toK ms l lz (R.toM ms.length)) ++
            (plain.map (toK ms l lz) ++ ds.map fun R => toK ms l lz (R.toM ms.length)) =
          ((F.map (·.toM ms.length) ++ plain) ++ ds.map (·.toM ms.length)).map (toK ms l lz) := by
        simp only [List.map_append, List.map_map, List.append_assoc]
        rfl
      have ne : (F.map (·.toM ms.length) ++ plain) ++ ds.map (·.toM ms.length) ≠ [] := by
        cases F with
        | nil => exact absurd rfl hF
        | cons a F => simp
      have es : sumM P.fld theta ((F.map (·.toM ms.length) ++ plain) ++ ds.map (·.toM ms.length)) =
          ((ds.map (·.toM ms.length)).foldl (stM P.fld theta) M).1 := by
        unfold sumM
        rw [hM, sumMFrom_fold, sumMFrom_fold, List.foldl_append]
      rw [el, ← toK_sumM P.fld theta _ _ _ _ ne, es]
      congr 1
      apply toK_congr
      · intro j hj
        show ((D.g :: D.p :: M.1.main.drop 2).take ms.length).getD j #[] = _
        rw [put_getD _ _ _ _ j hj]
        by_cases h0 : j = 0
        · subst h0
          rw [if_pos rfl]
          exact rel.g.symm
        · rw [if_neg h0]
          by_cases h1 : j = 1
          · subst h1
            rw [if_pos rfl]
            exact (rel.p hj).symm
          · rw [if_neg h1]
            exact (rel.rest j (by omega)).symm
      · intro j _
        exact (rel.mask j).symm
      · exact rel.t.symm

/-- the sum of the rows in front of the draws -/
def frontSum (P : Par) (m : Nat) (w : Wait) (plain : List MRow) (theta : E) : MRow × E :=
  sumMFrom P.fld theta Fld.oneE
    ((frontRows blocks P (decide (m - 1 < P.links)) w).map (·.toM (memsOf P.links m).length) ++
      plain)

def Spec.batch_some : Prop :=
  ∀ (P : Par) (V : M1.View) (m : Nat) (w : Wait) (plain : List MRow) (theta : E), 0 <
      (memsOf P.links m).length →
    (decide (m - 1 < P.links) = true → 3 ≤ P.C.l) →
    ((frontSum P m w plain theta).1.main.getD 0 #[]).size = 2 * P.C.l →
    ((frontSum P m w plain theta).1.main.getD 1 #[]).size =
      (if decide (m - 1 < P.links) then P.C.l else 0) →
    batch blocks P V m (some w) plain theta = batchLit blocks drawL P V m (some w) plain theta

/-- Proves `Spec.batch_some`: where something waits, under the four conditions on sizes of its
statement, the closing that the decision runs is its meaning. -/
theorem batch_some : Spec.batch_some := by
  intro P V m w plain theta hn h3 hg hp
  exact core P (decide (m - 1 < P.links)) w.S theta
    (fun x => (colAt V (m - 2) x).bind (groupCol (memsOf P.links (m - 1)) 1)) w.xs
    (memsOf P.links m) P.C.l P.Z.l (frontRows blocks P (decide (m - 1 < P.links)) w) plain
    (frontSum P m w plain theta) rfl (by unfold frontRows; simp) hn h3 hg hp

/-- The two theorems' conditions, as a test. -/
def condAt (P : Par) (m : Nat) (wait : Option Wait) (plain : List MRow) (theta : E) : Bool :=
  match wait with
  | none => !plain.isEmpty
  | some w =>
    decide (0 < (memsOf P.links m).length) && (!decide (m - 1 < P.links) || decide (3 ≤ P.C.l)) &&
    ((frontSum P m w plain theta).1.main.getD 0 #[]).size == 2 * P.C.l &&
    ((frontSum P m w plain theta).1.main.getD 1 #[]).size ==
      (if decide (m - 1 < P.links) then P.C.l else 0)

/-- The closing, refused where the conditions fail: so a run that is accepted with it has met them
at every closing. -/
def batchC (P : Par) (V : M1.View) : Batch := fun m wait plain theta =>
  if condAt P m wait plain theta then batch blocks P V m wait plain theta else none

def Spec.batchC_lit : Prop :=
  ∀ (P : Par) (V : M1.View) (m : Nat) (wait : Option Wait)
      (plain : List MRow) (theta : E) (R : KRow),
    batchC P V m wait plain theta = some R →
    batch blocks P V m wait plain theta = some R ∧
    batchLit blocks drawL P V m wait plain theta = some R

/-- Proves `Spec.batchC_lit`: where the tested closing gives a row, the fast closing and the meaning
give that row. -/
theorem batchC_lit : Spec.batchC_lit := by
  intro P V m wait plain theta R h
  unfold batchC at h
  by_cases hc : condAt P m wait plain theta = true
  · rw [if_pos hc] at h
    refine ⟨h, ?_⟩
    cases wait with
    | none =>
        rw [← batch_none blocks drawL P V m plain theta (by
          intro e
          rw [e] at hc
          cases hc)]
        exact h
    | some w =>
        unfold condAt at hc
        simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true', decide_eq_true_eq,
          decide_eq_false_iff_not, beq_iff_eq] at hc
        rw [← batch_some P V m w plain theta hc.1.1.1 (fun hk => by
          rcases hc.1.1.2 with h1 | h1
          · exact absurd (of_decide_eq_true hk) h1
          · exact h1) hc.1.2 (by
            rw [hc.2]
            by_cases hk : m - 1 < P.links
            · simp [hk]
            · simp [hk])]
        exact h
  · rw [if_neg hc] at h
    cases h

end Fmt.M2.BatchEq
