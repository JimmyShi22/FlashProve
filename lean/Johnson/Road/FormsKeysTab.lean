-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/FormsKeysTab.lean: the order of the entries inside a family of tables of the reads: the
numbering that the verifier's forms use against the numbering of its smallness test.

The forms of a layer sub-proof name an entry of the reads as "entry e of the family that begins at
tb" (Env.U3at in OnBytes/Model/LayerForms.lean). The smallness test names it as "column c, run sg of
the rows of the table Fn" (HTailF2.tabAt in OnBytes/Model/Tail.lean). This file shows that the two
meet: entry e is part e / n / k, column e / n mod k, run e mod n, where a part has k columns and a
column n runs.

What is compared with what. Two texts of the verifier with each other: layParts, layTables and U3at
(OnBytes/Model/LayerForms.lean) with tabAt (OnBytes/Model/Tail.lean) and tailsOf
(OnBytes/Model/LayerPlan.lean). firstM, rowsM, colsM, partsM and fcM are definitions of
Johnson/Road/FormsKeysMat.lean from the verifier's layout, for a matrix given by its number mat: 0
af, 1 ad, 2 ar, 3 qa, 4 the stream that comes in, 5 the stream that goes out. Laid1 is a definition
of Johnson/Road/FormsKeysHolds.lean. The library is not mentioned.

Main theorems.
 - layParts_eq: the parts of a family whose parts have one size, in closed form.
 - tails_sizes, tails_pair: in the verifier's list of matrices, part p of each of the six matrices
   stands at the number firstM + p and has rowsM rows and colsM columns; the length of the list.
 - entry_split, entry_join: an entry below parts k n and a triple (part, column, run) in range
   determine each other. entry_tabAt, tailAt_inv: the place that tabAt has for such a triple.
 - U3at_entry: what a form that U3at returns is worth, and that its entry is below the family's
   length. layTables_len: the family's length.
 - laid1_family: one family meets Laid1. laid1_of_run: the six families at the lookup's point meet
   it, in the forms in which summed_of_holds asks for it.
 - weighedOf_spec', inside_of_layout: what the marks of a call's columns say
   (Johnson/Road/FormsKeysRun8.lean), from the placing rule instead of the layers' parity.

The hypotheses of laid1_of_run, and where they are met. The verifier's lines hy, hg, hrd, hl, ht,
hp, hzt, hfun return together at made-up numbers: the guard on runR8 hR8 in
Johnson/Road/FormsKeysRun8.lean, a run, with the sizes matsR as here. The switches there: a theorem
(switchesR8). htm and hNM, that the matrices of the smallness test's list have the rows and columns
of the list of tailsOf and that NM is the list's length: met by the record that orderTab builds. For
the records that the verifier's own plans build they are theorems: plan_sizes,
Johnson/Road/FormsKeysPlan.lean.
The guard of this file is a run on the same made-up numbers: for every family of tables, those on
the matrix of counts too, the places of tabAt in the nesting part, column, run are the family's
entries in their order; with runs and columns swapped they are not.

What is not claimed. Nothing is said of what an entry holds: see Johnson/Road/FormsKeysHolds.lean.
That the array and the number of columns under which the forms name a place (iU3, K3) are those of
the smallness test is not looked at. The families at other points than the lookup's are covered by
laid1_family, not by laid1_of_run. The program does not import this file.
-/
import Johnson.Road.FormsKeysHolds
import Johnson.Road.FormsKeysAddr
import Johnson.Road.FormsKeysRun8
import OnBytes.Model.LayerPlan

set_option autoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road

open Finset
open OnBytes.Model (Reading World Aff Seg CallD HFun HTailF2 TMat Tail place topBit lastOf eqTab
  longPhi Level)
open OnBytes.Model.Layer (Env Lay Shape Reads Heard TableAsk TableAt layParts layTables tableAsks
  tailsOf matIx layout readsOf pointsOf funsOf)

/-! ## The parts of a family -/

/-- One step of layParts. -/
theorem layParts_succ (mats : Array (ℕ × ℕ)) (a : TableAsk) (n p : ℕ) :
    layParts mats a (n + 1) p =
      ((a.M0 + (a.parts - (n + 1)), p) ::
        (layParts mats a n (p + (mats.getD (a.M0 + (a.parts - (n + 1))) (0, 0)).2 *
          ((mats.getD (a.M0 + (a.parts - (n + 1))) (0, 0)).1 / a.L))).1,
       (layParts mats a n (p + (mats.getD (a.M0 + (a.parts - (n + 1))) (0, 0)).2 *
          ((mats.getD (a.M0 + (a.parts - (n + 1))) (0, 0)).1 / a.L))).2) := rfl

/-- The last n parts of a family whose parts all have m rows and k columns, laid from entry b on. -/
theorem layParts_run (mats : Array (ℕ × ℕ)) (a : TableAsk) (m k : ℕ)
    (hm : ∀ p, p < a.parts → mats.getD (a.M0 + p) (0, 0) = (m, k)) :
    ∀ (n b : ℕ), n ≤ a.parts → layParts mats a n b =
      ((List.range n).map fun i => (a.M0 + (a.parts - n + i), b + i * (k * (m / a.L))),
        b + n * (k * (m / a.L)))
  | 0, b, _ => by
    show ([], b) = _
    simp
  | n + 1, b, hn => by
    rw [layParts_succ, hm (a.parts - (n + 1)) (by omega),
      layParts_run mats a m k hm n _ (by omega)]
    show ((a.M0 + (a.parts - (n + 1)), b) :: (List.range n).map (fun i =>
        (a.M0 + (a.parts - n + i), b + k * (m / a.L) + i * (k * (m / a.L)))),
      b + k * (m / a.L) + n * (k * (m / a.L))) = _
    generalize k * (m / a.L) = w
    rw [List.range_succ_eq_map, List.map_cons, List.map_map]
    refine Prod.ext ?_ ?_
    · show _ :: _ = _ :: _
      congr 1
      · simp
      · refine List.map_congr_left fun i _ => ?_
        show (a.M0 + (a.parts - n + i), b + w + i * w) =
          (a.M0 + (a.parts - (n + 1) + (i + 1)), b + (i + 1) * w)
        rw [Nat.succ_mul]
        congr 1 <;> omega
    · show b + w + n * w = b + (n + 1) * w
      rw [Nat.succ_mul]
      omega

/-- The parts of a family whose parts all have m rows and k columns: part p is the matrix M0 + p of
the list, its table begins p k (m / L) entries behind the family's first entry b, and the first free
entry lies parts k (m / L) entries behind b. -/
theorem layParts_eq (mats : Array (ℕ × ℕ)) (a : TableAsk) (m k : ℕ)
    (hm : ∀ p, p < a.parts → mats.getD (a.M0 + p) (0, 0) = (m, k)) (b : ℕ) :
    layParts mats a a.parts b =
      ((List.range a.parts).map fun p => (a.M0 + p, b + p * (k * (m / a.L))),
        b + a.parts * (k * (m / a.L))) := by
  rw [layParts_run mats a m k hm a.parts b (Nat.le_refl _)]
  simp only [Nat.sub_self, Nat.zero_add]

/-! ## The list of matrices -/

/-- The names and sizes from which tailsOf makes the list of matrices. -/
def asksTab (y : Lay) : List (String × ℕ × ℕ) :=
  ((List.range (y.parts.getD 0 0)).map fun p =>
    ("af" ++ toString p, y.mrow.getD 0 0, y.kcol.getD 0 0)) ++
  ((List.range (y.parts.getD 1 0)).map fun p =>
    ("ad" ++ toString p, y.mrow.getD 1 0, y.kcol.getD 1 0)) ++
  [("ar", y.mrow.getD 2 0, y.kcol.getD 2 0), ("b", 2 ^ y.h.lmb, y.kbm),
   ("qa", y.mrow.getD 3 0, y.kcol.getD 3 0), ("xbO", y.mxb, y.kxb), ("xbI", y.mxb, y.kxb)]

/-- The matrix that tailsOf makes in group g from a name with sizes and its number in the list. -/
def tmatTab (y : Lay) (g : ℕ) (x : (String × ℕ × ℕ) × ℕ) : TMat :=
  let own : TMat := { name := x.1.1, m := x.1.2.1, k := x.1.2.2, aId := (1 + g) * 256 + x.2 }
  if x.2 == (matIx y).iXI && g != 0 then
    { own with kind := 1, foreign := some 0, aId := g * 256 + (matIx y).iXO }
  else own

/-- tailsOf, in these words. -/
theorem tailsOf_eq (y : Lay) : tailsOf y = (Array.range y.NGr).map fun g =>
    ({ mats := ((asksTab y).zipIdx.map (tmatTab y g)).toArray } : Tail) := rfl

/-- The matrix has the rows and columns that stand beside its name. -/
theorem tmatTab_size (y : Lay) (g : ℕ) (x : (String × ℕ × ℕ) × ℕ) :
    ((tmatTab y g x).m, (tmatTab y g x).k) = x.1.2 := by
  unfold tmatTab
  dsimp only
  split <;> rfl

/-- The rows and columns of the matrices of the list, in its order. -/
def sizesTab (y : Lay) : List (ℕ × ℕ) :=
  List.replicate (y.parts.getD 0 0) (y.mrow.getD 0 0, y.kcol.getD 0 0) ++
  List.replicate (y.parts.getD 1 0) (y.mrow.getD 1 0, y.kcol.getD 1 0) ++
  [(y.mrow.getD 2 0, y.kcol.getD 2 0), (2 ^ y.h.lmb, y.kbm), (y.mrow.getD 3 0, y.kcol.getD 3 0),
   (y.mxb, y.kxb), (y.mxb, y.kxb)]

/-- A list made from the first n numbers by a function with one value. -/
theorem map_range_const {α : Type} (n : ℕ) (f : ℕ → α) (c : α) (h : ∀ i, f i = c) :
    (List.range n).map f = List.replicate n c := by
  rw [List.eq_replicate_iff]
  refine ⟨by simp, fun b hb => ?_⟩
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp hb
  exact h i

/-- The sizes in asksTab are sizesTab. -/
theorem asksTab_sizes (y : Lay) : (asksTab y).map (·.2) = sizesTab y := by
  have e0 := map_range_const (y.parts.getD 0 0) ((fun x : String × ℕ × ℕ => x.2) ∘ fun p =>
    ("af" ++ toString p, y.mrow.getD 0 0, y.kcol.getD 0 0)) (y.mrow.getD 0 0, y.kcol.getD 0 0)
    (fun _ => rfl)
  have e1 := map_range_const (y.parts.getD 1 0) ((fun x : String × ℕ × ℕ => x.2) ∘ fun p =>
    ("ad" ++ toString p, y.mrow.getD 1 0, y.kcol.getD 1 0)) (y.mrow.getD 1 0, y.kcol.getD 1 0)
    (fun _ => rfl)
  unfold asksTab sizesTab
  rw [List.map_append, List.map_append, List.map_map, List.map_map, e0, e1]
  rfl

/-- Member g of an array made from the first n numbers. -/
theorem getD_range_map {α : Type} (f : ℕ → α) (n g : ℕ) (d : α) (hg : g < n) :
    ((Array.range n).map f).getD g d = f g := by
  simp [Array.getD, hg]

/-- The rows and columns of the matrices of group g, as the check of a layer sub-proof takes them
from tailsOf, are sizesTab. -/
theorem tails_pairs (y : Lay) {g : ℕ} (hg : g < y.NGr) :
    (((tailsOf y).getD g {}).mats.map fun M => (M.m, M.k)) = (sizesTab y).toArray := by
  rw [tailsOf_eq, getD_range_map _ _ _ _ hg]
  show (((asksTab y).zipIdx.map (tmatTab y g)).toArray.map fun M => (M.m, M.k)) = _
  rw [List.map_toArray, List.map_map, ← asksTab_sizes]
  have e : ((fun M : TMat => (M.m, M.k)) ∘ tmatTab y g) =
      ((·.2) : String × ℕ × ℕ → ℕ × ℕ) ∘ Prod.fst := funext fun x => tmatTab_size y g x
  rw [e, ← List.map_map, List.zipIdx_map_fst]

/-- Members of a list of a copies of x, b copies of y and a list t. -/
theorem getD_three {α : Type} (a b : ℕ) (x y : α) (t : List α) (d : α) :
    (∀ p, p < a → (List.replicate a x ++ List.replicate b y ++ t).getD p d = x) ∧
    (∀ p, p < b → (List.replicate a x ++ List.replicate b y ++ t).getD (a + p) d = y) ∧
    ∀ j, (List.replicate a x ++ List.replicate b y ++ t).getD (a + b + j) d = t.getD j d := by
  refine ⟨fun p hp => ?_, fun p hp => ?_, fun j => ?_⟩
  · rw [List.getD_eq_getElem?_getD, List.append_assoc,
      List.getElem?_append_left (by simpa using hp)]
    simp [hp]
  · rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by simp; omega),
      List.getElem?_append_right (by simp)]
    simp [hp]
  · rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp)]
    simp

/-- The list has the parts of af, the parts of ad and five more matrices. -/
theorem sizesTab_length (y : Lay) :
    (sizesTab y).length = y.parts.getD 0 0 + y.parts.getD 1 0 + 5 := by
  unfold sizesTab
  rw [List.length_append, List.length_append, List.length_replicate, List.length_replicate]
  rfl

/-- Part p of the matrix with the number mat stands in the list at the number firstM + p, and
has rowsM rows and colsM columns. -/
theorem sizesTab_at (y : Lay) {mat p : ℕ} (hmat : mat ≤ 5) (hp : p < partsM y mat) :
    firstM y mat + p < (sizesTab y).length ∧
      (sizesTab y).getD (firstM y mat + p) (0, 0) = (rowsM y mat, colsM y mat) := by
  obtain ⟨t1, t2, t3⟩ := getD_three (y.parts.getD 0 0) (y.parts.getD 1 0)
    (y.mrow.getD 0 0, y.kcol.getD 0 0) (y.mrow.getD 1 0, y.kcol.getD 1 0)
    [(y.mrow.getD 2 0, y.kcol.getD 2 0), (2 ^ y.h.lmb, y.kbm), (y.mrow.getD 3 0, y.kcol.getD 3 0),
     (y.mxb, y.kxb), (y.mxb, y.kxb)] (0, 0)
  rw [sizesTab_length]
  interval_cases mat
  · have hp' : p < y.parts.getD 0 0 := hp
    have e : firstM y 0 + p = p := Nat.zero_add p
    rw [e]
    exact ⟨by omega, t1 p hp'⟩
  · have hp' : p < y.parts.getD 1 0 := hp
    have e : firstM y 1 + p = y.parts.getD 0 0 + p := rfl
    rw [e]
    exact ⟨by omega, t2 p hp'⟩
  · have hp' : p < 1 := hp
    obtain rfl : p = 0 := by omega
    have e : firstM y 2 + 0 = y.parts.getD 0 0 + y.parts.getD 1 0 + 0 := rfl
    rw [e]
    exact ⟨by omega, t3 0⟩
  · have hp' : p < 1 := hp
    obtain rfl : p = 0 := by omega
    have e : firstM y 3 + 0 = y.parts.getD 0 0 + y.parts.getD 1 0 + 2 := rfl
    rw [e]
    exact ⟨by omega, t3 2⟩
  · have hp' : p < 1 := hp
    obtain rfl : p = 0 := by omega
    have e : firstM y 4 + 0 = y.parts.getD 0 0 + y.parts.getD 1 0 + 4 := rfl
    rw [e]
    exact ⟨by omega, t3 4⟩
  · have hp' : p < 1 := hp
    obtain rfl : p = 0 := by omega
    have e : firstM y 5 + 0 = y.parts.getD 0 0 + y.parts.getD 1 0 + 3 := rfl
    rw [e]
    exact ⟨by omega, t3 3⟩

/-- The rows and columns of a member of a list of matrices. -/
theorem getD_map_sizes (ms : Array TMat) {i : ℕ} (hi : i < ms.size) :
    (ms.map fun M => (M.m, M.k)).getD i (0, 0) = ((ms.getD i {}).m, (ms.getD i {}).k) := by
  simp [Array.getD, hi]

/-- The sizes of the matrices in the verifier's list. In every group g of the layout the list has
the parts of af, the parts of ad and five more matrices; and for each of the six numbers mat and
each part p, the matrix with the number firstM + p has rowsM rows and colsM columns. -/
theorem tails_sizes (y : Lay) {g : ℕ} (hg : g < y.NGr) :
    ((tailsOf y).getD g {}).mats.size = y.parts.getD 0 0 + y.parts.getD 1 0 + 5 ∧
    ∀ mat p, mat ≤ 5 → p < partsM y mat →
      firstM y mat + p < ((tailsOf y).getD g {}).mats.size ∧
      (((tailsOf y).getD g {}).mats.getD (firstM y mat + p) {}).m = rowsM y mat ∧
      (((tailsOf y).getD g {}).mats.getD (firstM y mat + p) {}).k = colsM y mat := by
  have P := tails_pairs y hg
  have hsz : ((tailsOf y).getD g {}).mats.size = (sizesTab y).length := by
    have := congrArg Array.size P
    simpa using this
  refine ⟨hsz.trans (sizesTab_length y), fun mat p hmat hp => ?_⟩
  obtain ⟨h1, h2⟩ := sizesTab_at y hmat hp
  have hi : firstM y mat + p < ((tailsOf y).getD g {}).mats.size := by rw [hsz]; exact h1
  have e : ((((tailsOf y).getD g {}).mats.map fun M => (M.m, M.k)).getD (firstM y mat + p) (0, 0)) =
      (rowsM y mat, colsM y mat) := by
    rw [P, ← h2]
    simp [Array.getD, List.getD_eq_getElem?_getD, h1]
  rw [getD_map_sizes _ hi] at e
  exact ⟨hi, congrArg Prod.fst e, congrArg Prod.snd e⟩

/-! ## An entry of a family: part, column, run of rows -/

/-- An entry e of a family of parts tables, each of k columns with n runs of rows, taken apart: the
part e / n / k, the column e / n mod k, the run e mod n. -/
theorem entry_split {parts k n e : ℕ} (he : e < parts * (k * n)) :
    e / n / k < parts ∧ e / n % k < k ∧ e % n < n ∧
      e = (e / n / k * k + e / n % k) * n + e % n := by
  have hn : 0 < n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h
      simp at he
    · exact h
  have hk : 0 < k := by
    rcases Nat.eq_zero_or_pos k with h | h
    · subst h
      simp at he
    · exact h
  have h1 : e / n < k * parts := by
    refine Nat.div_lt_of_lt_mul ?_
    calc e < parts * (k * n) := he
      _ = n * (k * parts) := by ring
  refine ⟨Nat.div_lt_of_lt_mul h1, Nat.mod_lt _ hk, Nat.mod_lt _ hn, ?_⟩
  rw [Nat.div_add_mod', Nat.div_add_mod']

/-- Every part p, column c and run s in range is hit by an entry of the family, (p k + c) n + s, and
entry_split takes that entry apart into p, c and s. By the last clause of entry_split no other entry
is taken apart so. -/
theorem entry_join {parts k n p c s : ℕ} (hp : p < parts) (hc : c < k) (hs : s < n) :
    (p * k + c) * n + s < parts * (k * n) ∧ ((p * k + c) * n + s) / n / k = p ∧
      ((p * k + c) * n + s) / n % k = c ∧ ((p * k + c) * n + s) % n = s := by
  obtain ⟨e1, e2, e3, e4⟩ := split_entry (p := p) hc hs
  refine ⟨?_, by rw [e1, e3], by rw [e1, e4], e2⟩
  have h1 : p * k + c + 1 ≤ parts * k := by
    have h2 := Nat.mul_le_mul_right k (Nat.succ_le_of_lt hp)
    rw [Nat.succ_mul] at h2
    omega
  have h3 := Nat.mul_le_mul_right n h1
  rw [Nat.succ_mul] at h3
  calc (p * k + c) * n + s < (p * k + c) * n + n := by omega
    _ ≤ parts * k * n := h3
    _ = parts * (k * n) := by ring

/-- Where the smallness test has the entry for column c and run sg of a table. -/
theorem tailAt_some (tl : HTailF2) (Fn : HFun) {c sg : ℕ} (h1 : Fn.mat < tl.NM) (h2 : Fn.len ≠ 0)
    (h3 : c < (tl.mats.getD Fn.mat {}).k) (h4 : sg < (tl.mats.getD Fn.mat {}).m / Fn.len) :
    tl.tabAt Fn c sg = some (Fn.start + c * ((tl.mats.getD Fn.mat {}).m / Fn.len) + sg) := by
  have a : (decide (Fn.mat < tl.NM) && Fn.len != 0) = true := by simp [h1, h2]
  have b : (decide (c < (tl.mats.getD Fn.mat {}).k) &&
      decide (sg < (tl.mats.getD Fn.mat {}).m / Fn.len)) = true := by
    rw [Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq]
    exact ⟨h3, h4⟩
  unfold HTailF2.tabAt
  rw [if_pos a]
  show (if (decide (c < (tl.mats.getD Fn.mat {}).k) &&
      decide (sg < (tl.mats.getD Fn.mat {}).m / Fn.len)) = true then _ else none) = _
  rw [if_pos b]

/-- The smallness test has an entry only for a column and a run of the table's matrix. -/
theorem tailAt_inv (tl : HTailF2) (Fn : HFun) {c sg pos : ℕ} (h : tl.tabAt Fn c sg = some pos) :
    Fn.mat < tl.NM ∧ Fn.len ≠ 0 ∧ c < (tl.mats.getD Fn.mat {}).k ∧
      sg < (tl.mats.getD Fn.mat {}).m / Fn.len ∧
      pos = Fn.start + c * ((tl.mats.getD Fn.mat {}).m / Fn.len) + sg := by
  unfold HTailF2.tabAt at h
  by_cases a : (decide (Fn.mat < tl.NM) && Fn.len != 0) = true
  · rw [if_pos a] at h
    have h' : (if (decide (c < (tl.mats.getD Fn.mat {}).k) &&
        decide (sg < (tl.mats.getD Fn.mat {}).m / Fn.len)) = true then
          some (Fn.start + c * ((tl.mats.getD Fn.mat {}).m / Fn.len) + sg) else none) =
        some pos := h
    by_cases b : (decide (c < (tl.mats.getD Fn.mat {}).k) &&
        decide (sg < (tl.mats.getD Fn.mat {}).m / Fn.len)) = true
    · rw [if_pos b] at h'
      simp only [Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq] at a b
      exact ⟨a.1, a.2, b.1, b.2, (Option.some.inj h').symm⟩
    · rw [if_neg b] at h'
      cases h'
  · rw [if_neg a] at h
    cases h

/-- Entry e of a family against the smallness test's own numbering. The family begins at entry b;
its parts are the matrices M0, M0 + 1 and so on of the smallness test's list, each of m rows and k
columns; its tables have runs of L rows. The table of the part e / n / k, which begins
(e / n / k) (k n) entries behind b, has the place b + e for its column e / n mod k and its run
e mod n, where n = m / L. -/
theorem entry_tabAt (tl : HTailF2) {M0 parts m k L b e : ℕ} (phi : Array E)
    (he : e < parts * (k * (m / L)))
    (htl : ∀ p, p < parts → M0 + p < tl.NM ∧ (tl.mats.getD (M0 + p) {}).m = m ∧
      (tl.mats.getD (M0 + p) {}).k = k) :
    tl.tabAt { mat := M0 + e / (m / L) / k, len := L, phi := phi, tree := 2,
               start := b + e / (m / L) / k * (k * (m / L)) } (e / (m / L) % k) (e % (m / L)) =
      some (b + e) := by
  obtain ⟨hp, hc, hs, hsum⟩ := entry_split he
  obtain ⟨t1, t2, t3⟩ := htl _ hp
  have hL : L ≠ 0 := by
    intro h0
    subst h0
    simp at hs
  rw [tailAt_some tl _ t1 hL (by rw [t3]; exact hc) (by rw [t2]; exact hs)]
  show some (b + e / (m / L) / k * (k * (m / L)) +
    e / (m / L) % k * ((tl.mats.getD (M0 + e / (m / L) / k) {}).m / L) + e % (m / L)) = _
  rw [t2]
  congr 1
  generalize m / L = n at hsum ⊢
  generalize e / n / k = p at hsum ⊢
  generalize e / n % k = c at hsum ⊢
  generalize e % n = s at hsum ⊢
  rw [hsum]
  ring

/-! ## The forms' own name of an entry -/

section Value

variable {K : Type} [Field K] (ρ : Reading K) (W : World K)

/-- What U3at returns. If it returns a form for entry e of the family that begins at tb, then a
family x of the list begins at tb, it is the first such in the list, e is below its length, and the
form is worth the hidden value at the place tb + e of the array of reads. -/
theorem U3at_entry {v : Env} {tb e : ℕ} {a : Aff} (h : v.U3at tb e = some a) :
    ∃ x, v.tab.find? (fun x => x.first == tb) = some x ∧ e < x.len ∧
      a.value ρ W = W.entry v.iU3 ((tb + e) / v.K3) ((tb + e) % v.K3) := by
  unfold Env.U3at at h
  cases hx : v.tab.find? (fun x => x.first == tb) with
  | none =>
    rw [hx] at h
    cases h
  | some x =>
    rw [hx] at h
    have h' : (if (decide (e < x.len) && v.K3 != 0 && decide ((tb + e) / v.K3 < 2 ^ 32)) = true then
        some (Aff.ent v.iU3 ((tb + e) / v.K3) ((tb + e) % v.K3)) else none) = some a := h
    by_cases hc : (decide (e < x.len) && v.K3 != 0 && decide ((tb + e) / v.K3 < 2 ^ 32)) = true
    · rw [if_pos hc] at h'
      have ha := Option.some.inj h'
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
      refine ⟨x, rfl, hc.1.1, ?_⟩
      rw [← ha, Aff.value_ent]
    · rw [if_neg hc] at h'
      cases h'

end Value

/-- Beside each family's place layTables returns the family that was asked for and the first entries
of its parts' tables, laid from the family's first entry on; and the family ends where its last part
ends. -/
theorem layTables_len (mats : Array (ℕ × ℕ)) : ∀ (asks : List TableAsk) (p : ℕ)
    (r : List TableAt × List (TableAsk × List (ℕ × ℕ)) × ℕ), layTables mats asks p = some r →
    ∀ x ∈ r.1, ∃ q ∈ asks, x.name = q.name ∧
      x.first + x.len = (layParts mats q q.parts x.first).2
  | [], p, r, h, x, hx => by
    have e : r = ([], [], p) := by simpa [layTables] using h.symm
    subst e
    simp at hx
  | a :: rest, p, r, h, x, hx => by
    have hle := layParts_le mats a a.parts p
    have h' : (if ((layParts mats a a.parts p).2 == p) = true then none else
        (layTables mats rest (layParts mats a a.parts p).2).map fun r =>
          ((⟨a.name, p, (layParts mats a a.parts p).2 - p⟩ : TableAt) :: r.1,
            (a, (layParts mats a a.parts p).1) :: r.2.1, r.2.2)) = some r := h
    by_cases hq : ((layParts mats a a.parts p).2 == p) = true
    · rw [if_pos hq] at h'
      cases h'
    · rw [if_neg hq] at h'
      obtain ⟨r', h1, h2⟩ := map_some h'
      subst h2
      rcases List.mem_cons.mp hx with e | hx
      · subst e
        refine ⟨a, List.mem_cons_self, rfl, ?_⟩
        show p + ((layParts mats a a.parts p).2 - p) = (layParts mats a a.parts p).2
        omega
      · obtain ⟨q, q1, q2, q3⟩ := layTables_len mats rest _ r' h1 x hx
        exact ⟨q, List.mem_cons_of_mem _ q1, q2, q3⟩

/-! ## One family -/

section Family

variable {K : Type} [Field K] {ρ : Reading K} {W : World K}

/-- One family of the verifier's tables meets the record Laid1. Asked: layTables has laid the
families asks from entry 0 on, and the environment's list of places is its result; the family q is
the only one of asks with the name n, and is found under that name at entry tb; its first part is
the first part of the matrix with the number mat; each of its parts has rowsM rows and colsM
columns, in the sizes from which the tables were laid (hsz) and in the smallness test's list (htl);
each of its parts has its table, with the weights phi, in the list funs (hf). -/
theorem laid1_family {v : Env} {tl : HTailF2} {funs : Array HFun} {mats : Array (ℕ × ℕ)}
    {asks : List TableAsk} {r : List TableAt × List (TableAsk × List (ℕ × ℕ)) × ℕ}
    (hl : layTables mats asks 0 = some r) (ht : v.tab = r.1) {n : String} {tb : ℕ}
    (hn : v.tabAt n = some tb) {q : TableAsk}
    (huniq : ∀ q' ∈ asks, q'.name = n → q' = q) {mat : ℕ} (hM0 : q.M0 = firstM v.y mat)
    (hsz : ∀ p, p < q.parts → mats.getD (q.M0 + p) (0, 0) = (rowsM v.y mat, colsM v.y mat))
    (htl : ∀ p, p < q.parts → q.M0 + p < tl.NM ∧ (tl.mats.getD (q.M0 + p) {}).m = rowsM v.y mat ∧
      (tl.mats.getD (q.M0 + p) {}).k = colsM v.y mat) {phi : Array E}
    (hf : ∀ m ∈ (layParts mats q q.parts tb).1,
      ({ mat := m.1, len := q.L, phi := phi, tree := 2, start := m.2 } : HFun) ∈ funs) :
    Laid1 ρ W v tl funs tb mat q.L (rowsM v.y mat / q.L) phi := by
  intro e a h
  obtain ⟨x, hx, hlen, hval⟩ := U3at_entry ρ W h
  -- the family that begins at tb is the one found under the name n
  obtain ⟨hc, -⟩ := layTables_chain mats asks 0 r hl
  rw [← ht] at hc
  obtain ⟨x', hx'm, hx'n, hx'f⟩ := tabAt_mem hn
  have e1 := chain_first v.tab 0 hc x' hx'm
  rw [hx'f, hx] at e1
  have e2 : x = x' := Option.some.inj e1
  subst e2
  -- its length
  obtain ⟨q', q1, q2, q3⟩ := layTables_len mats asks 0 r hl x (by rw [← ht]; exact hx'm)
  have e3 : q' = q := huniq q' q1 (q2.symm.trans hx'n)
  subst e3
  rw [hx'f, layParts_eq mats q' _ _ hsz] at q3
  have he : e < q'.parts * (colsM v.y mat * (rowsM v.y mat / q'.L)) := by
    have q3' : tb + x.len = tb + q'.parts * (colsM v.y mat * (rowsM v.y mat / q'.L)) := q3
    omega
  obtain ⟨hp, hcc, hs, hsum⟩ := entry_split he
  refine ⟨_, _, _, tb + e / (rowsM v.y mat / q'.L) / colsM v.y mat *
    (colsM v.y mat * (rowsM v.y mat / q'.L)), hcc, hs, hsum, hval, ?_, ?_⟩
  · rw [← hM0]
    refine hf (_, _) ?_
    rw [layParts_eq mats q' _ _ hsz]
    exact List.mem_map.mpr ⟨_, List.mem_range.mpr hp, rfl⟩
  · rw [← hM0]
    exact entry_tabAt tl phi he htl

end Family

/-! ## The six families of the lookup's point -/

/-- The numbers of the six families: each is asked for under its name with the first part and the
number of parts of its matrix, and with runs of 2^la rows (a long table) or T rows (a short one). -/
theorem six_numbers (y : Lay) (rd : Reads) (g : ℕ) (hAF : "Z" ∈ rd.rdAF) (hQA : "Z" ∈ rd.rdQA)
    (hXI : "Z" ∈ rd.rdXI) (hXO : "Z" ∈ rd.rdXO) (hAD : "zt" ∈ rd.rdAD) (hAR : "zt" ∈ rd.rdAR) :
    (∃ a ∈ tableAsks y rd g, a.name = "af" ++ "@" ++ "Z" ∧ a.M0 = firstM y 0 ∧
      a.parts = partsM y 0 ∧ a.L = 2 ^ y.h.la) ∧
    (∃ a ∈ tableAsks y rd g, a.name = "qa" ++ "@" ++ "Z" ∧ a.M0 = firstM y 3 ∧
      a.parts = partsM y 3 ∧ a.L = 2 ^ y.h.la) ∧
    (∃ a ∈ tableAsks y rd g, a.name = "xbI" ++ "@" ++ "Z" ∧ a.M0 = firstM y 4 ∧
      a.parts = partsM y 4 ∧ a.L = 2 ^ y.h.la) ∧
    (∃ a ∈ tableAsks y rd g, a.name = "xbO" ++ "@" ++ "Z" ∧ a.M0 = firstM y 5 ∧
      a.parts = partsM y 5 ∧ a.L = 2 ^ y.h.la) ∧
    (∃ a ∈ tableAsks y rd g, a.name = "ad" ++ "@" ++ "zt" ∧ a.M0 = firstM y 1 ∧
      a.parts = partsM y 1 ∧ a.L = y.T) ∧
    (∃ a ∈ tableAsks y rd g, a.name = "ar" ++ "@" ++ "zt" ∧ a.M0 = firstM y 2 ∧
      a.parts = partsM y 2 ∧ a.L = y.T) := by
  have m : ∀ (f : String → TableAsk) (p : String) (l : List String), p ∈ l → f p ∈ l.map f :=
    fun f p l h => List.mem_map.mpr ⟨p, h, rfl⟩
  exact
   ⟨⟨_, List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
      (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
        (List.mem_append_left _ (List.mem_append_left _ (m _ _ _ hAF)))))))), rfl, rfl, rfl, rfl⟩,
    ⟨_, List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
      (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
        (List.mem_append_left _ (List.mem_append_right _ (m _ _ _ hQA)))))))), rfl, rfl, rfl, rfl⟩,
    ⟨_, List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
      (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
        (List.mem_append_right _ (m _ _ _ hXI))))))), rfl, rfl, rfl, rfl⟩,
    ⟨_, List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
      (List.mem_append_left _ (List.mem_append_right _ (m _ _ _ hXO))))), rfl, rfl, rfl, rfl⟩,
    ⟨_, List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
      (List.mem_append_right _ (m _ _ _ hAD)))), rfl, rfl, rfl, rfl⟩,
    ⟨_, List.mem_append_left _ (List.mem_append_left _
      (List.mem_append_right _ (m _ _ _ hAR))), rfl, rfl, rfl, rfl⟩⟩

/-- The sizes from which the check of a layer sub-proof lays its tables: part p of the matrix with
the number mat has rowsM rows and colsM columns. -/
theorem tails_pair (y : Lay) {g : ℕ} (hg : g < y.NGr) {mat p : ℕ} (hmat : mat ≤ 5)
    (hp : p < partsM y mat) :
    (matsR y g).getD (firstM y mat + p) (0, 0) = (rowsM y mat, colsM y mat) := by
  obtain ⟨h1, h2⟩ := sizesTab_at y hmat hp
  unfold matsR
  rw [tails_pairs y hg, ← h2]
  simp [Array.getD, List.getD_eq_getElem?_getD, h1]

/-- The matrices af, qa and the two of the stream have 2^lm rows with la ≤ lm. -/
theorem rows_of_laid2 {y : Lay} (L2 : Laid2 y) :
    ∀ mat ∈ [0, 3, 4, 5], ∃ lm, y.h.la ≤ lm ∧ rowsM y mat = 2 ^ lm := by
  intro mat hm
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl
  · exact ⟨_, L2.la_af, L2.mrow0⟩
  · exact ⟨_, L2.la_q, L2.mrow3⟩
  · exact ⟨_, L2.la_x, L2.mxb⟩
  · exact ⟨_, L2.la_x, L2.mxb⟩

section Run

variable {K : Type} [Field K] {h : Shape} {pc : List (List String)} {v : Env} {rd : Reads}
  {r : List TableAt × List (TableAsk × List (ℕ × ℕ)) × ℕ}

/-- The six families of the verifier's own run meet the record Laid1, in the forms in which
summed_of_holds (Johnson/Road/FormsKeysHolds.lean) asks for it. Asked: the verifier's lines that
make the layout, the reads, the tables' places (laid from the sizes of the matrices of tailsOf), the
points and the list of tables; the switches; and that the matrices of the smallness test's list have
the rows and columns of the list of tailsOf, with NM the list's length (htm, hNM). -/
theorem laid1_of_run (ρ : Reading K) (W : World K) (hy : layout h pc = .ok v.y) (S : Switches h)
    (hg : v.g < v.y.NGr) (hrd : readsOf v.y = .ok rd)
    (hl : layTables (matsR v.y v.g) (tableAsks v.y rd v.g) 0 = some r) (ht : v.tab = r.1)
    {tl : HTailF2} (htm : (tl.mats.map fun M => (M.m, M.k)) = matsR v.y v.g)
    (hNM : tl.NM = tl.mats.size) {H : Heard} {hd : Level} {hd2 : Option Level}
    {pts : List (String × Array E)}
    {funs : Array HFun} (hp : pointsOf v.y H hd hd2 = some pts)
    (hzt : lastOf H.fo.zx v.y.h.lt = .ok H.ztF) (hfun : funsOf v.y H.fo pts r.2.1 = some funs) :
    ∃ Z, lastOf H.fo.zx v.y.h.la = .ok Z ∧ v.y.T = 2 ^ H.ztF.size ∧
      (∀ p ∈ [("af" ++ "@" ++ "Z", 0), ("qa" ++ "@" ++ "Z", 3), ("xbI" ++ "@" ++ "Z", 4),
        ("xbO" ++ "@" ++ "Z", 5)], ∀ tb, v.tabAt p.1 = some tb → ∃ n,
          fcM v.y p.2 = n * 2 ^ v.y.ls ∧
          Laid1 ρ W v tl funs tb p.2 (2 ^ v.y.ls * v.y.T) n (longPhi Z v.y.ls H.ztF.size)) ∧
      (∀ p ∈ [("ad" ++ "@" ++ "zt", 1), ("ar" ++ "@" ++ "zt", 2)], ∀ tb,
        v.tabAt p.1 = some tb →
          Laid1 ρ W v tl funs tb p.2 v.y.T (fcM v.y p.2) (eqTab H.ztF)) := by
  have A := admitted_of_layout hy S.p3
  have hT := (laid2_of_layout hy).T
  have hrows := rows_of_laid2 (laid2_of_layout hy)
  have hla : v.y.h.la = v.y.ls + v.y.h.lt := by
    rw [A.shape]
    exact A.la
  obtain ⟨p1, p2, p3, p4, p5, p6⟩ := points_of_layout hy S hrd
  obtain ⟨Z, hZ, -, hst, -, TL, TS, -⟩ := tables_of_run ρ hy S hrd hl ht hp hzt hfun
  obtain ⟨-, hT5⟩ := tails_sizes v.y hg
  obtain ⟨n0, n3, n4, n5, n1, n2⟩ := six_numbers v.y rd v.g p1 p2 p3 p4 p5 p6
  have step : ∀ (n : String) (mat L : ℕ) (phi : Array E), mat ≤ 5 →
      (∃ a ∈ tableAsks v.y rd v.g, a.name = n ∧ a.M0 = firstM v.y mat ∧
        a.parts = partsM v.y mat ∧ a.L = L) →
      (∃ b a, v.tabAt n = some b ∧ a ∈ tableAsks v.y rd v.g ∧ a.name = n ∧
        ∀ m ∈ (layParts (matsR v.y v.g) a a.parts b).1,
          ({ mat := m.1, len := a.L, phi := phi, tree := 2, start := m.2 } : HFun) ∈ funs) →
      ∀ tb, v.tabAt n = some tb → Laid1 ρ W v tl funs tb mat L (rowsM v.y mat / L) phi := by
    intro n mat L phi hmat ⟨a, ha, an, aM, ap, aL⟩ ⟨b, a', hb, ha', an', hf⟩ tb htb
    have eb : b = tb := Option.some.inj (hb.symm.trans htb)
    subst eb
    have ea : a' = a := ask_of_name hrd ha' ha (an'.trans an.symm)
    subst ea
    rw [← aL]
    refine laid1_family hl ht hb (fun q' hq' e => ask_of_name hrd hq' ha' (e.trans an'.symm)) aM
      (fun p hp => ?_) (fun p hp => ?_) hf
    · rw [ap] at hp
      rw [aM]
      exact tails_pair v.y hg hmat hp
    · rw [ap] at hp
      rw [aM]
      obtain ⟨hi, -, -⟩ := hT5 mat p hmat hp
      have hsz : tl.mats.size = ((tailsOf v.y).getD v.g {}).mats.size := by
        have h1 := congrArg Array.size htm
        simpa [matsR] using h1
      have hi' : firstM v.y mat + p < tl.mats.size := by
        rw [hsz]
        exact hi
      have e := getD_map_sizes tl.mats hi'
      rw [htm, tails_pair v.y hg hmat hp] at e
      exact ⟨by rw [hNM]; exact hi', (congrArg Prod.fst e).symm, (congrArg Prod.snd e).symm⟩
  have long : ∀ (n : String) (mat : ℕ), mat ≤ 5 → mat ∈ [0, 3, 4, 5] →
      (∃ a ∈ tableAsks v.y rd v.g, a.name = n ∧ a.M0 = firstM v.y mat ∧
        a.parts = partsM v.y mat ∧ a.L = 2 ^ v.y.h.la) →
      n ∈ ["af" ++ "@" ++ "Z", "qa" ++ "@" ++ "Z", "xbI" ++ "@" ++ "Z", "xbO" ++ "@" ++ "Z"] →
      ∀ tb, v.tabAt n = some tb → ∃ k, fcM v.y mat = k * 2 ^ v.y.ls ∧
        Laid1 ρ W v tl funs tb mat (2 ^ v.y.ls * v.y.T) k (longPhi Z v.y.ls H.ztF.size) := by
    intro n mat hmat hm4 hnum hn tb htb
    obtain ⟨lm, hle, hrow⟩ := hrows mat hm4
    have e1 : 2 ^ v.y.ls * v.y.T = 2 ^ v.y.h.la := by rw [hT, ← Nat.pow_add, ← hla]
    have e2 : 2 ^ (lm - v.y.h.la) = rowsM v.y mat / 2 ^ v.y.h.la := by
      rw [hrow, Nat.pow_div hle (by norm_num)]
    refine ⟨2 ^ (lm - v.y.h.la), ?_, ?_⟩
    · unfold fcM
      rw [hrow, hT, Nat.pow_div (by omega) (by norm_num), ← Nat.pow_add]
      congr 1
      omega
    · rw [e1, e2, hst]
      exact step n mat _ _ hmat hnum (TL n hn) tb htb
  refine ⟨Z, hZ, by rw [hst]; exact hT, fun p hp => ?_, fun p hp => ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl
    · exact long _ 0 (by omega) (by simp) n0 (by simp)
    · exact long _ 3 (by omega) (by simp) n3 (by simp)
    · exact long _ 4 (by omega) (by simp) n4 (by simp)
    · exact long _ 5 (by omega) (by simp) n5 (by simp)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl
    · exact step _ 1 _ _ (by omega) n1 (TS _ (by simp))
    · exact step _ 2 _ _ (by omega) n2 (TS _ (by simp))

end Run

/-! ## The marks of a call, from "every listed column is one of the call's" -/

/-- What the marks say, as weighedOf_spec of Johnson/Road/FormsKeysRun8.lean says it, with another
second hypothesis: every column that a segment of the call lists is below J (hin). -/
theorem weighedOf_spec' {v : Env} {c : CallD} {w : Array Bool} (h : v.weighedOf c = some w)
    (hin : ∀ s ∈ c.segs, ∀ j ∈ s.pos.toList, j < c.J) :
    w.size = v.y.Lam * c.J ∧ ∀ lam, lam < v.y.Lam →
      (∀ j ∈ colsOn v c lam, j < c.J) ∧ (colsOn v c lam).Nodup ∧
        ∀ j, j < c.J → (w.getD (lam * c.J + j) true = true ↔ j ∈ colsOn v c lam) := by
  rw [weighedOf_eq] at h
  obtain ⟨a, -, n, d⟩ := marks_spec _ _ _ h
  rw [Array.size_replicate] at a
  have below : ∀ lam, ∀ j ∈ colsOn v c lam, j < c.J := by
    intro lam j hj
    obtain ⟨s, hs, -, hp⟩ := mem_colsOn.mp hj
    exact hin s hs j hp
  refine ⟨a, fun lam hlam => ⟨below lam, ?_, fun j hj => ?_⟩⟩
  · exact List.Nodup.of_map _ ((List.nodup_flatMap.mp n).1 lam (List.mem_range.mpr hlam))
  · have hlt : lam * c.J + j < v.y.Lam * c.J := by
      have h2 := Nat.mul_le_mul_right c.J (Nat.succ_le_of_lt hlam)
      rw [Nat.succ_mul] at h2
      omega
    have h0 : (Array.replicate (v.y.Lam * c.J) false).getD (lam * c.J + j) true = false := by
      simp [Array.getD, hlt]
    rw [d, h0]
    constructor
    · rintro (h1 | h1)
      · cases h1
      · obtain ⟨lam', -, j', hj', e⟩ := mem_marksOn.mp h1
        obtain ⟨e1, e2⟩ := layer_column (below lam' j' hj') hj e
        subst e1
        subst e2
        exact hj'
    · exact fun h1 => Or.inr (mem_marksOn.mpr ⟨lam, hlam, j, h1, rfl⟩)

/-- In every call of a layout that the verifier has returned for a shape with the switches, every
column that a segment lists is one of the call's. It follows from the placing rule; which layers
have routed experts plays no part. -/
theorem inside_of_layout {h : Shape} {pc : List (List String)} {y : Lay}
    (hy : layout h pc = .ok y) (S : Switches h) :
    ∀ cd ∈ y.calls, ∀ s ∈ cd.segs, ∀ j ∈ s.pos.toList, j < cd.J := by
  intro cd hcd s hs j hj
  have A := admitted_of_layout hy S.p3
  obtain ⟨fam, -, hn, -, -, -⟩ := segs_of_admitted A S cd hcd s hs
  have hlt : s.n < 2 ^ (topBit + 1) := by
    rw [hn]
    exact len_lt A fam
  obtain ⟨cl, taken, -, -, hc⟩ := A.calls
  rw [hc] at hcd
  obtain ⟨c0, -, rfl⟩ := List.mem_map.mp (List.mem_toArray.mp hcd)
  have Al := place_aligned _ _ _ _ 0 s hs (by simp) hlt
  obtain ⟨x, hx, e⟩ := List.getElem_of_mem hj
  have hx' : x < s.pos.size := by simpa using hx
  have hi := Al.inside x (by rw [← Al.size]; exact hx')
  have e' : s.pos[x] = j := by simpa using e
  have e2 : s.pos.getD x 0 = j := by
    rw [← e']
    simp [Array.getD, hx']
  rw [e2] at hi
  exact hi

/-! ## A run on made-up numbers -/

/-- For each group of layers: whether for every family of tables the places that the smallness test
has for the family's parts, columns and runs of rows, in that nesting, are the family's entries in
their order, from its first to its last. swap: a control, with the runs outside the columns. Refuses
where the verifier's functions refuse. -/
def orderTab (h : Shape) (pc : List (List String)) (swap : Bool) : Except String (List Bool) := do
  let y ← layout h pc
  let rd ← readsOf y
  (List.range y.NGr).mapM fun g =>
    let ms := ((tailsOf y).getD g {}).mats
    let tl : HTailF2 := { NM := ms.size, mats := ms }
    match layTables (matsR y g) (tableAsks y rd g) 0 with
    | none => throw "no tables"
    | some r => pure ((r.1.zip r.2.1).all fun x =>
      let L := x.2.1.L
      let at' (ps : ℕ × ℕ) (c sg : ℕ) := tl.tabAt { mat := ps.1, len := L, start := ps.2 } c sg
      (x.2.2.flatMap fun ps =>
        let M := ms.getD ps.1 {}
        if swap then
          (List.range (M.m / L)).flatMap fun sg => (List.range M.k).map fun c => at' ps c sg
        else (List.range M.k).flatMap fun c => (List.range (M.m / L)).map fun sg => at' ps c sg) ==
      (List.range x.1.len).map fun e => some (x.1.first + e))

/- the order of the entries, in both groups; and the control -/
#guard (match orderTab hR8 pcR8 false, orderTab hR8 pcR8 true with
  | .ok a, .ok b => a == [true, true] && b == [false, false]
  | _, _ => false)

#print axioms layParts_eq
#print axioms tails_sizes
#print axioms entry_split
#print axioms entry_join
#print axioms entry_tabAt
#print axioms tailAt_inv
#print axioms U3at_entry
#print axioms layTables_len
#print axioms laid1_family
#print axioms laid1_of_run
#print axioms weighedOf_spec'
#print axioms inside_of_layout

end OnBytes.Road
