-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Tail/ClosedRec.lean: the closed record of a smallness test: the record at which the
theorems on the link of a sub-proof (InSubLay.lean, InSubAll.lean) are meant.

The record tl : OnBytes.Model.HTailF2 that a plan makes has no table and no first columns: the field
funs is written by `closeFuns` and the field cfFirst by `drawMatrixF` (OnBytes/Model/Tail.lean),
both in a run. At such a record the sizes `sizeOf tl` (SizeOf.lean) have no table, and the premises
`SameShapes` and "cfFirst holds the running sums of the matrices' columns" of `link_at_lay` cannot
be met at a real sub-proof. The theorems are meant at the record with the tables' public shapes
(matrix, length, first entry) and the running sums laid in. Here that record is a definition,
`closedAt tl sh`, for a written list sh of shapes; the tables of a statement are `funsOf sh phi`:
these shapes with the statement's weights; and the premises on public data are paid by construction
or gathered in one Bool.

Main names (namespace OnBytes.Tie.Pv.Tail.Closed):
  `firstCols`: the running sums of the matrices' columns, by the term of `drawMatrixF`.
  `tabFun`, `funsL`, `funsOf`: a table of a given shape with given weights, in the third vector; the
    tables of a list of shapes, table number n with the weights phi n.
  `closedAt tl sh`: tl with the list of tables closed, the tables of the shapes sh without weights,
    and `firstCols`.
  `closed_tabs`: the tables of `sizeOf (closedAt tl sh)` are sh. `closed_same`, `closed_tree`,
    `closed_first`: `SameShapes`, "every table in the third vector" and the premise on cfFirst hold
    by construction.
  `closed_run`: the record that a run has behind `closeFuns` at tables funs and behind the drawing
    of the matrix is `closedAt` with funs and the drawn entries laid in, whatever sh.
  `shapesOf`, `closedAt_close`, `funsOf_self`: the shapes of a list of tables; the record that
    `closeFuns` returns at tables funs agrees with `closedAt` at their shapes but for the tables'
    weights and cfFirst; tables in the third vector are `funsOf` of their shapes and their weights.
    `sizeOf_same`, `sizeOf_closed`: a record with the same matrices, number of combinations and
    shapes has the closed record's sizes.
  `apartTest`, `apart_of_test`: a Bool on the sizes (the places of two tables do not meet) gives
    `Apart` (Cb/Pv/Tail/PlacesOne.lean).
  `readsNo`, `topClosed`, `reads_length`, `topOf_closed`: the number of reads and the number of
    indices as functions of tl and sh alone; at every statement's record the number of indices
    (`topOf`) is `topClosed tl sh`.
  `ClosedOK`, `closedTest`, `closedOK_of_test`: the premises on public data that are left, at the
    closed record, and one Bool that gives them.
Limits: tl and sh are letters. tl may be any record, a record that is closed already among them:
`closedAt` lays funs, funClosed and cfFirst anew and keeps all else. That sh is the list of shapes
of the tables which the verifier's run closes at a given sub-proof is not said (`closed_run` has the
run's own tables; `funsOf_self` and `sizeOf_closed` tie them to sh := their shapes). `apartTest`
asks more than `Apart`: it also refuses tables without a place that lie inside another. `closedTest`
is a Bool on public numbers: that it is true at a given sub-proof is a run, no proof term. That pc
and pc + `topClosed` are a plan's numbers is not said.

-/
import Cb.Pv.Tail.PlacesOne
import OnBytes.Tie.Pv.Tail.InSubAll

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Tie.Pv.Tail.Closed
open OnBytes OnBytes.Model OnBytes.DgP OnBytes.Tie.Pv.Tail OnBytes.Tie.Pv.Tail.Port Cb.Pv.Tail Cb.Fo

/-- The running sums of the matrices' columns; a last entry holds their count. -/
def firstCols (tl : HTailF2) : Array Nat :=
  tl.mats.foldl (fun a M => a.push (a.getD (a.size - 1) 0 + M.k)) #[0]

/-- A table of a given shape with given weights, in the third vector. -/
def tabFun (t : Tab) (phi : Array E) : HFun :=
  { mat := t.mat, len := t.len, phi := phi, tree := 2, start := t.start }

/-- The tables of a list of shapes: table number n has the weights phi n. -/
def funsL : List Tab → (ℕ → Array E) → List HFun
  | [], _ => []
  | t :: l, phi => tabFun t (phi 0) :: funsL l fun n => phi (n + 1)

/-- The same as an array. -/
def funsOf (sh : List Tab) (phi : ℕ → Array E) : Array HFun := (funsL sh phi).toArray

/-- The closed record. -/
def closedAt (tl : HTailF2) (sh : List Tab) : HTailF2 :=
  { tl with funClosed := true, funs := funsOf sh fun _ => #[], cfFirst := firstCols tl }

theorem funsL_shapes : ∀ (sh : List Tab) (phi : ℕ → Array E),
    ((funsL sh phi).map fun Fn : HFun => (⟨Fn.mat, Fn.len, Fn.start⟩ : Tab)) = sh
  | [], _ => rfl
  | t :: l, phi => by
    show (⟨t.mat, t.len, t.start⟩ : Tab) :: _ = t :: l
    rw [funsL_shapes l]

theorem funsL_tree : ∀ (sh : List Tab) (phi : ℕ → Array E), ∀ Fn ∈ funsL sh phi, Fn.tree = 2
  | [], _, _, h => absurd h List.not_mem_nil
  | t :: l, phi, Fn, h => by
    rcases List.mem_cons.1 h with rfl | h
    · rfl
    · exact funsL_tree l _ Fn h

/-- The tables of the closed record's sizes are the written shapes. -/
theorem closed_tabs (tl : HTailF2) (sh : List Tab) : (sizeOf (closedAt tl sh)).tabs = sh :=
  funsL_shapes sh _

/-- The tables of a statement have the closed record's shapes. -/
theorem closed_same (tl : HTailF2) (sh : List Tab) (phi : ℕ → Array E) :
    SameShapes (closedAt tl sh) (funsOf sh phi) :=
  (funsL_shapes sh phi).trans (funsL_shapes sh _).symm

/-- Every table of a statement is in the third vector. -/
theorem closed_tree (sh : List Tab) (phi : ℕ → Array E) :
    ∀ Fn ∈ (funsOf sh phi).toList, Fn.tree = 2 := funsL_tree sh phi

/-- The closed record's first columns are the running sums. -/
theorem closed_first (tl : HTailF2) (sh : List Tab) :
    (closedAt tl sh).cfFirst =
      (closedAt tl sh).mats.foldl (fun a M => a.push (a.getD (a.size - 1) 0 + M.k)) #[0] := rfl

/-- The record of a run behind the closing of the tables and the drawing of the matrix. -/
theorem closed_run (tl tl₁ : HTailF2) (funs : Array HFun) (sh : List Tab) (cf : Array Int)
    (h : tl.closeFuns funs = some tl₁) :
    { tl₁ with cfF := cf, cfFirst := firstCols tl₁ } =
      { closedAt tl sh with funs := funs, cfF := cf } := by
  unfold HTailF2.closeFuns at h
  split at h
  · exact absurd h (by simp)
  · obtain rfl := Option.some.inj h
    rfl

/-- The public shapes of a list of tables. -/
def shapesOf (funs : Array HFun) : List Tab :=
  funs.toList.map fun Fn : HFun => (⟨Fn.mat, Fn.len, Fn.start⟩ : Tab)

/-- The record that the verifier's own routine closes at tables funs agrees with the closed record
at their shapes but for the tables' weights and the first columns. -/
theorem closedAt_close (tl tl₁ : HTailF2) (funs : Array HFun)
    (h : tl.closeFuns funs = some tl₁) :
    closedAt tl (shapesOf funs) =
      { tl₁ with funs := funsOf (shapesOf funs) fun _ => #[], cfFirst := firstCols tl₁ } := by
  unfold HTailF2.closeFuns at h
  split at h
  · exact absurd h (by simp)
  · obtain rfl := Option.some.inj h
    rfl

theorem funsL_self : ∀ l : List HFun, (∀ Fn ∈ l, Fn.tree = 2) →
    funsL (l.map fun Fn : HFun => (⟨Fn.mat, Fn.len, Fn.start⟩ : Tab))
      (fun n => (l.getD n {}).phi) = l
  | [], _ => rfl
  | Fn :: l, h => by
    have h2 : Fn.tree = 2 := h Fn List.mem_cons_self
    show tabFun ⟨Fn.mat, Fn.len, Fn.start⟩ Fn.phi :: funsL _ (fun n => (l.getD n {}).phi) = Fn :: l
    rw [funsL_self l fun G hG => h G (List.mem_cons_of_mem _ hG)]
    congr 1
    unfold tabFun
    rw [← h2]

/-- Tables in the third vector are the tables of their shapes with their weights. -/
theorem funsOf_self (funs : Array HFun) (h : ∀ Fn ∈ funs.toList, Fn.tree = 2) :
    funsOf (shapesOf funs) (fun n => (funs.toList.getD n {}).phi) = funs := by
  unfold funsOf shapesOf
  rw [funsL_self funs.toList h]

/-- The sizes read the number of matrices, the matrices, the number of combinations and the tables'
shapes alone. -/
theorem sizeOf_same (c c' : HTailF2) (h1 : c'.NM = c.NM) (h2 : c'.mats = c.mats)
    (h3 : c'.tau = c.tau) (h4 : shapesOf c'.funs = shapesOf c.funs) : sizeOf c' = sizeOf c := by
  unfold shapesOf at h4
  unfold sizeOf
  rw [h1, h2, h3, h4]

/-- The sizes of a record that has the closed record's matrices and tables of the shapes sh. -/
theorem sizeOf_closed (tl c' : HTailF2) (sh : List Tab) (h1 : c'.NM = tl.NM)
    (h2 : c'.mats = tl.mats) (h3 : c'.tau = tl.tau) (h4 : shapesOf c'.funs = sh) :
    sizeOf c' = sizeOf (closedAt tl sh) :=
  sizeOf_same (closedAt tl sh) c' h1 h2 h3 (h4.trans (funsL_shapes sh _).symm)

/-- The places of two tables do not meet: a test on the sizes. -/
def apartTest (t : TSize) : Bool :=
  decide (∀ n, n < t.tabs.length → ∀ n', n' < t.tabs.length → n ≠ n' →
    (t.tabs.getD n ⟨0, 0, 0⟩).start + t.k (t.tabs.getD n ⟨0, 0, 0⟩).mat *
        (t.m (t.tabs.getD n ⟨0, 0, 0⟩).mat / (t.tabs.getD n ⟨0, 0, 0⟩).len) ≤
      (t.tabs.getD n' ⟨0, 0, 0⟩).start ∨
    (t.tabs.getD n' ⟨0, 0, 0⟩).start + t.k (t.tabs.getD n' ⟨0, 0, 0⟩).mat *
        (t.m (t.tabs.getD n' ⟨0, 0, 0⟩).mat / (t.tabs.getD n' ⟨0, 0, 0⟩).len) ≤
      (t.tabs.getD n ⟨0, 0, 0⟩).start)

theorem getD_of_some {l : List Tab} {n : ℕ} {T : Tab} (h : l[n]? = some T) :
    n < l.length ∧ l.getD n ⟨0, 0, 0⟩ = T := by
  obtain ⟨hn, e⟩ := List.getElem?_eq_some_iff.1 h
  refine ⟨hn, ?_⟩
  rw [List.getD_eq_getElem?_getD, h]
  rfl

theorem below_of {c k S sg : ℕ} (hc : c < k) (hs : sg < S) : c * S + sg < k * S := by
  have h := Nat.mul_le_mul_right S (Nat.succ_le_of_lt hc)
  rw [Nat.succ_mul] at h
  omega

/-- No two of table, column and segment stand at one place, from the test. -/
theorem apart_of_test {t : TSize} (h : apartTest t = true) : Apart t := by
  have ht := of_decide_eq_true h
  intro n T c sg n' T' c' sg' h1 _ h3 h4 h1' _ h3' h4' e
  obtain ⟨l1, g1⟩ := getD_of_some h1
  obtain ⟨l2, g2⟩ := getD_of_some h1'
  by_cases hn : n = n'
  · subst hn
    obtain rfl : T = T' := Option.some.inj (h1.symm.trans h1')
    have hS : 0 < t.m T.mat / T.len := lt_of_le_of_lt (Nat.zero_le _) h4
    have d1 : (sg + c * (t.m T.mat / T.len)) / (t.m T.mat / T.len) = c := by
      rw [Nat.add_mul_div_right _ _ hS, Nat.div_eq_of_lt h4, Nat.zero_add]
    have d2 : (sg' + c' * (t.m T.mat / T.len)) / (t.m T.mat / T.len) = c' := by
      rw [Nat.add_mul_div_right _ _ hS, Nat.div_eq_of_lt h4', Nat.zero_add]
    have e' : sg + c * (t.m T.mat / T.len) = sg' + c' * (t.m T.mat / T.len) := by omega
    have hc : c = c' := by rw [← d1, e', d2]
    subst hc
    exact ⟨rfl, rfl, by omega⟩
  · have b1 := below_of h3 h4
    have b2 := below_of h3' h4'
    have d := ht n l1 n' l2 hn
    rw [g1, g2] at d
    rcases d with d | d <;> omega

/-- The number of segments of a table of shape t on matrix mu and vector un. -/
def segNo (tl : HTailF2) (mu un : ℕ) (t : Tab) : ℕ :=
  if (t.mat == mu && (2 : ℕ) == un) = true then (tl.mats.getD mu {}).m / t.len else 0

/-- The number of reads, from the shapes. -/
def readsNo (tl : HTailF2) (sh : List Tab) : ℕ :=
  ((List.range tl.NM).map fun mu => ([0, 2].map fun un => (sh.map (segNo tl mu un)).sum).sum).sum

theorem segs_length (tl : HTailF2) (mu un : ℕ) (t : Tab) (phi : Array E) :
    (segsOf tl mu un (tabFun t phi)).length = segNo tl mu un t := by
  unfold segsOf segNo tabFun
  split
  · rw [List.length_map, List.length_range]
  · rfl

theorem segsL_length (tl : HTailF2) (mu un : ℕ) : ∀ (sh : List Tab) (phi : ℕ → Array E),
    ((funsL sh phi).map fun Fn => (segsOf tl mu un Fn).length) = sh.map (segNo tl mu un)
  | [], _ => rfl
  | t :: l, phi => by
    show (segsOf tl mu un (tabFun t (phi 0))).length :: _ = segNo tl mu un t :: _
    rw [segs_length, segsL_length tl mu un l]

/-- The number of reads hangs on the shapes alone. -/
theorem reads_length (tl : HTailF2) (sh : List Tab) (phi : ℕ → Array E) :
    (readsList tl (funsOf sh phi)).length = readsNo tl sh := by
  unfold readsList readsNo
  rw [List.length_flatMap]
  refine congrArg List.sum (List.map_congr_left fun mu _ => ?_)
  rw [List.length_flatMap]
  refine congrArg List.sum (List.map_congr_left fun un _ => ?_)
  rw [List.length_flatMap]
  exact congrArg List.sum (segsL_length tl mu un sh phi)

/-- The number of indices, from the record and the shapes. -/
def topClosed (tl : HTailF2) (sh : List Tab) : ℕ :=
  firstOf tl tl.NM + readsNo tl sh * tl.stepF

/-- At every statement's record the number of indices is that number. -/
theorem topOf_closed (tl : HTailF2) (sh : List Tab) (phi : ℕ → Array E)
    (β : Dr (sizeOf (closedAt tl sh)).size) :
    topOf (recLay (closedAt tl sh) (funsOf sh phi) β)
      (recLay (closedAt tl sh) (funsOf sh phi) β).funs = topClosed tl sh := by
  show firstOf tl tl.NM + (readsList tl (funsOf sh phi)).length * tl.stepF = _
  rw [reads_length]
  rfl

/-- The premises on public data that are left, at a record c. -/
structure ClosedOK (c : HTailF2) (n a pc : ℕ) : Prop where
  nums : FoNums.ok c.f9 = true
  shape : shapeTest2 c Cb.Gl.p = true
  cols : colsTest c = true
  nm : c.NM = c.mats.size
  fit : Fits c
  sym : ∀ mu, mu < c.NM → (c.shp.getD mu {}).mS = Alg.symRows (c.shp.getD mu {}).m
  apart : Apart (sizeOf c)
  na : n ≤ a
  apc : a + (1 + Fo.nRows c.f9) ≤ pc

/-- One Bool for them, at the closed record. -/
def closedTest (tl : HTailF2) (sh : List Tab) (n a pc : ℕ) : Bool :=
  FoNums.ok (closedAt tl sh).f9 && shapeTest2 (closedAt tl sh) Cb.Gl.p &&
  colsTest (closedAt tl sh) && decide ((closedAt tl sh).NM = (closedAt tl sh).mats.size) &&
  decide (∀ mu, mu < (closedAt tl sh).NM →
    ((closedAt tl sh).shp.getD mu {}).m = ((closedAt tl sh).mats.getD mu {}).m ∧
      ((closedAt tl sh).shp.getD mu {}).k = ((closedAt tl sh).mats.getD mu {}).k) &&
  decide (∀ mu, mu < (closedAt tl sh).NM →
    ((closedAt tl sh).shp.getD mu {}).mS = Alg.symRows ((closedAt tl sh).shp.getD mu {}).m) &&
  apartTest (sizeOf (closedAt tl sh)) && decide (n ≤ a) &&
  decide (a + (1 + Fo.nRows (closedAt tl sh).f9) ≤ pc)

theorem closedOK_of_test {tl : HTailF2} {sh : List Tab} {n a pc : ℕ}
    (h : closedTest tl sh n a pc = true) : ClosedOK (closedAt tl sh) n a pc := by
  simp only [closedTest, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, apart_of_test h7, h8, h9⟩

end OnBytes.Tie.Pv.Tail.Closed

#print axioms OnBytes.Tie.Pv.Tail.Closed.closed_tabs
#print axioms OnBytes.Tie.Pv.Tail.Closed.closed_same
#print axioms OnBytes.Tie.Pv.Tail.Closed.closed_tree
#print axioms OnBytes.Tie.Pv.Tail.Closed.closed_first
#print axioms OnBytes.Tie.Pv.Tail.Closed.closed_run
#print axioms OnBytes.Tie.Pv.Tail.Closed.closedAt_close
#print axioms OnBytes.Tie.Pv.Tail.Closed.funsOf_self
#print axioms OnBytes.Tie.Pv.Tail.Closed.sizeOf_closed
#print axioms OnBytes.Tie.Pv.Tail.Closed.apart_of_test
#print axioms OnBytes.Tie.Pv.Tail.Closed.reads_length
#print axioms OnBytes.Tie.Pv.Tail.Closed.topOf_closed
#print axioms OnBytes.Tie.Pv.Tail.Closed.closedOK_of_test
