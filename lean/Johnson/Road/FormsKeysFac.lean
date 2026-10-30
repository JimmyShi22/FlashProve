-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/FormsKeysFac.lean: the two halves in which the verifier settles a factor of a weight
claim multiply to what the factor weighs an index with, at the cell that the layout gives the index;
and so what the verifier's settling of a whole claim is worth on a matrix W, any function, which
stands where the committed matrix of weights would stand.

A claim on the matrix W (OnBytes/Model/Weights.lean) has one factor for each index group of its
unit. The verifier never writes the sum that the claim speaks of. It evaluates each factor on the
group's column bits (WsFac.onColumns, wsEpsT) and writes out what is left on the rows
(WsFac.onRows, WsRowFac.table, wsGamma). Johnson/Road/FormsKeysWm.lean writes the sum (claimVal),
with facAt of Johnson/Road/FormsKeysPan.lean for what a factor weighs an index with and cellOf for
the cell of a digit. This file shows that the two agree.

What is compared with what: the verifier's own functions onColumns, onRows, table, wsEpsT, wsRowPart
and wsGamma with definitions of these files: facAt, splitG, cellOf, claimVal, and two of this file,
colHalf and rowHalf, which say in the field what each half means. The library is not mentioned, but
for its kernel eqN, in which facAt is written.

Main definitions: colHalf, rowHalf; joinG; gamOf; colRel.
Main theorems.
 - onColumns_at: at coordinates that spell a number c on the group's column bits, onColumns reads as
   colHalf at c. table_at, table_size: the table on the rows reads as rowHalf, and has one member
   for each value that the group leaves to the rows.
 - fac_split: at every index below R the product of the two halves, at the two parts into which
   splitG cuts the index, is facAt.
 - splitG_inj: no two indices have the same two parts. split_onto: a column part below 2^t and a row
   part below what is left to the rows are the parts of an index below R, or weigh 0.
 - fac_sum: summing over column parts and row parts is summing over indices.
 - cells_sum: the same for a list of groups, by induction.
 - claim_cells: the sum over all columns C and all rows y of the unit of wsGamma[y] times wsEpsT at
   the point that spells C times W (off + y) C is wgt ka claimVal. claim_cells_layout: the same on a
   layout that wsLayOf returns.

The hypotheses, and where they are met. GrpOK, Runs, UnitOK (Johnson/Road/FormsKeysWOk.lean): for
every unit of a layout that the verifier builds, a theorem: unitOK_of_layout
(Johnson/Road/FormsKeysWLay.lean). That wsLayOf returns, that the layout has the claim's unit, and
that the claim passes wsClaimShape, which says that each factor fits its group: run together at
made-up numbers, on the verifier's own list of weight claims, in Johnson/Road/FormsKeysRunW.lean
(its point W5). That the reading takes numerals to numbers (Numerals): a theorem for the reading in
the library's field (gl_numerals, Johnson/Road/FormsKeysKit.lean).
The same file runs, in the program's own field and at made-up numbers: what fac_split says, at the
parts that the library's split gives an index (W3); where the two factors of the left side of
claim_cells are not 0, for claims that weigh one tuple alone (W2); and that left side whole, at
ka = wgt = 1 on a made-up W, against the library's formulas (W4).

What is not claimed. Every statement is an identity; no challenge's distribution is used. Only
points of zeros and ones are put on the columns: what wsEpsT is worth at another point is not said.
Which coordinate of such a point goes with which column bit is set by the definition bitsOf, after
the way wsEpsT reads a point: coordinate i with bit lk - 1 - i. No theorem here ties that order to
the way the committed table is opened.
That cellOf is the library's place of a weight's digit is the matter of another file. Nothing ties W
to a commitment. The program does not import this file.
-/
import Johnson.Road.FormsKeysWLay
import Johnson.Road.FormsKeysPoint
import OnBytes.Iop.RowLaws

set_option autoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road

open Finset
open OnBytes.Model (Reading WsGrp WsUnit WsLay WsFac WsRowFac WsClaim WsRecClaim wsOuter wsDot wsEq1
  wsEpsT wsRowPart wsGamma wsDigits wsSecondDigit wsClaimShape eqTab clog2 WsShape wsLayOf)

/-! ## All products of two vectors -/

/-- Pushing the images of a list's members onto an array appends them. -/
theorem push_fold (f : E → E) : ∀ (l : List E) (out : Array E),
    (l.foldl (fun o y => o.push (f y)) out).toList = out.toList ++ l.map f
  | [], out => by simp
  | y :: l, out => by
    rw [List.foldl_cons, push_fold f l]
    simp

/-- wsOuter as a list: for each member of a, in order, its products with the members of b. -/
theorem wsOuter_toList (a b : Array E) :
    (wsOuter a b).toList = a.toList.flatMap fun x => b.toList.map fun y => mulE x y := by
  have H : ∀ (l : List E) (out : Array E),
      (l.foldl (fun out x => b.foldl (fun o y => o.push (mulE x y)) out) out).toList =
        out.toList ++ l.flatMap fun x => b.toList.map fun y => mulE x y := by
    intro l
    induction l with
    | nil =>
      intro out
      simp
    | cons x l ih =>
      intro out
      rw [List.foldl_cons, ih, ← Array.foldl_toList, push_fold, List.flatMap_cons,
        List.append_assoc]
  unfold wsOuter
  rw [← Array.foldl_toList, H]
  simp

/-- Lists of one length laid end to end. -/
theorem flatMap_length {α β : Type} (g : α → List β) (n : ℕ) :
    ∀ l : List α, (∀ a ∈ l, (g a).length = n) → (l.flatMap g).length = l.length * n
  | [], _ => by simp
  | x :: l, h => by
    rw [List.flatMap_cons, List.length_append, h x List.mem_cons_self,
      flatMap_length g n l (fun a ha => h a (List.mem_cons_of_mem _ ha)), List.length_cons,
      Nat.succ_mul]
    omega

/-- wsOuter has one member for each pair. -/
theorem wsOuter_size (a b : Array E) : (wsOuter a b).size = a.size * b.size := by
  have h := flatMap_length (fun x => b.toList.map fun y => mulE x y) b.size a.toList
    (by intro x _; simp)
  rw [← wsOuter_toList] at h
  simpa using h

/-- The member of wsOuter at the index i |b| + q is a[i] b[q]. -/
theorem wsOuter_getD (a b : Array E) {i q : ℕ} (hi : i < a.size) (hq : q < b.size) :
    (wsOuter a b).getD (i * b.size + q) zeroE = mulE (a.getD i zeroE) (b.getD q zeroE) := by
  have h2 := flatMap_getElem? (fun x => b.toList.map fun y => mulE x y) b.size a.toList
    (by intro x _; simp) i q (a.getD i zeroE) (by simp [Array.getD, hi]) hq
  rw [← wsOuter_toList] at h2
  rw [Array.getD_eq_getD_getElem?, ← Array.getElem?_toList, h2]
  simp [Array.getD, hq]

section Values

variable {K : Type} [Field K] (ρ : Reading K)

/-- A sum over the members of wsOuter is a sum over the pairs. -/
theorem sum_wsOuter (a b : Array E) (H : ℕ → K) :
    ∑ y ∈ range (wsOuter a b).size, ρ.val ((wsOuter a b).getD y zeroE) * H y =
      ∑ i ∈ range a.size, ∑ q ∈ range b.size,
        ρ.val (a.getD i zeroE) * ρ.val (b.getD q zeroE) * H (i * b.size + q) := by
  rw [wsOuter_size, sum_blocks]
  refine sum_congr rfl fun i hi => sum_congr rfl fun q hq => ?_
  rw [wsOuter_getD a b (mem_range.mp hi) (mem_range.mp hq), ρ.mul]

/-! ## Products and sums that the verifier folds -/

/-- A product folded over the first n numbers. -/
theorem foldl_mul_range (h : ℕ → E) (p0 : E) : ∀ n : ℕ,
    ρ.val ((List.range n).foldl (fun p i => mulE p (h i)) p0) =
      ρ.val p0 * ∏ i ∈ range n, ρ.val (h i)
  | 0 => by simp
  | n + 1 => by
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, ρ.mul,
      foldl_mul_range h p0 n, Finset.prod_range_succ, mul_assoc]

/-- A product folded over a list. -/
theorem foldl_mul_list {α : Type} (h : α → E) : ∀ (l : List α) (p0 : E),
    ρ.val (l.foldl (fun p y => mulE p (h y)) p0) = ρ.val p0 * (l.map fun y => ρ.val (h y)).prod
  | [], p0 => by simp
  | y :: l, p0 => by
    rw [List.foldl_cons, foldl_mul_list h l, ρ.mul, List.map_cons, List.prod_cons, mul_assoc]

/-- wsDot reads as the sum of the products. -/
theorem wsDot_value (n : ℕ) (a b : Array E) :
    ρ.val (wsDot n a b) = ∑ i ∈ range n, ρ.val (a.getD i zeroE) * ρ.val (b.getD i zeroE) := by
  unfold wsDot
  induction n with
  | zero => simp [ρ.zero]
  | succ n ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, maddE_val, ih,
      Finset.sum_range_succ]

/-- wsEq1 at a coordinate that is 1 or 0. -/
theorem wsEq1_bit (p : E) (b : Bool) :
    ρ.val (wsEq1 p (if b then oneE else zeroE)) = if b then ρ.val p else 1 - ρ.val p := by
  unfold wsEq1
  cases b
  · simp [ρ.add, ρ.mul, ρ.sub, ρ.one, ρ.zero]
  · simp [ρ.add, ρ.mul, ρ.sub, ρ.one]

/-! ## The kernel eq -/

/-- The kernel, with the bits of the index counted from the lowest. -/
theorem eqN_low_bits (t off : ℕ) (a : ℕ → K) (c : ℕ) :
    Blocks.eqN t off a c = ∏ i ∈ range t,
      (if c.testBit i then a (off + (t - 1 - i)) else 1 - a (off + (t - 1 - i))) := by
  unfold Blocks.eqN
  refine (Finset.prod_range_reflect _ t).symm.trans (prod_congr rfl fun j hj => ?_)
  have hj' : j < t := mem_range.mp hj
  have e : t - 1 - (t - 1 - j) = j := by omega
  simp only [e]

/-- The kernel at a point of zeros and ones that spells the number c: 1 at c, 0 at every other index
below 2^t. -/
theorem eqN_bool (t off : ℕ) (a : ℕ → K) {c i : ℕ} (hc : c < 2 ^ t) (hi : i < 2 ^ t)
    (ha : ∀ s, s < t → a (off + s) = if c.testBit (t - 1 - s) then 1 else 0) :
    Blocks.eqN t off a i = if i = c then 1 else 0 := by
  unfold Blocks.eqN
  by_cases h : i = c
  · subst h
    rw [if_pos rfl]
    refine prod_eq_one fun s hs => ?_
    rw [ha s (mem_range.mp hs)]
    cases i.testBit (t - 1 - s) <;> simp
  · rw [if_neg h]
    obtain ⟨j, hj⟩ : ∃ j, i.testBit j ≠ c.testBit j := by
      by_contra hn
      exact h (Nat.eq_of_testBit_eq fun j => by_contra fun hj => hn ⟨j, hj⟩)
    have hjt : j < t := by
      by_contra hge
      have hp : 2 ^ t ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) (by omega)
      exact hj ((Nat.testBit_lt_two_pow (lt_of_lt_of_le hi hp)).trans
        (Nat.testBit_lt_two_pow (lt_of_lt_of_le hc hp)).symm)
    refine prod_eq_zero (mem_range.mpr (show t - 1 - j < t by omega)) ?_
    rw [ha _ (by omega), show t - 1 - (t - 1 - j) = j by omega]
    cases h1 : i.testBit j <;> cases h2 : c.testBit j <;> simp_all

end Values

/-! ## Lists -/

/-- A filter that keeps every member. -/
theorem filterMap_all {α β : Type} {f : α → Option β} {g : α → β} :
    ∀ l : List α, (∀ a ∈ l, f a = some (g a)) → l.filterMap f = l.map g
  | [], _ => rfl
  | x :: l, h => by
    rw [List.filterMap_cons, h x List.mem_cons_self, List.map_cons,
      filterMap_all l fun a ha => h a (List.mem_cons_of_mem _ ha)]

/-- A filter that keeps no member. -/
theorem filterMap_none {α β : Type} {f : α → Option β} :
    ∀ l : List α, (∀ a ∈ l, f a = none) → l.filterMap f = []
  | [], _ => rfl
  | x :: l, h => by
    rw [List.filterMap_cons, h x List.mem_cons_self,
      filterMap_none l fun a ha => h a (List.mem_cons_of_mem _ ha)]

/-- Quotient and remainder of i B + q for q below B. -/
theorem div_mod_block {B i q : ℕ} (hq : q < B) : (i * B + q) / B = i ∧ (i * B + q) % B = q := by
  have hB : 0 < B := by omega
  constructor
  · rw [Nat.mul_comm, Nat.mul_add_div hB, Nat.div_eq_of_lt hq, Nat.add_zero]
  · rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt hq]

/-! ## The two halves of a factor -/

/-- The first of the coordinates of a factor's point that belong to the bits which the group gives
to the columns. -/
def takenOff (g : WsGrp) : ℕ := if g.high then 0 else g.z - g.t

/-- The first of the coordinates that belong to the bits which are left to the rows. -/
def leftOff (g : WsGrp) : ℕ := if g.high then g.t else 0

section Halves

variable {K : Type} [Field K] (ρ : Reading K)

/-- What a factor weighs the column part c of an index with. Class 'E': the equality weight, at c,
of the t coordinates of the bits that go to the columns. Class 'A', taken: the element that is
written out for c, and 0 from R on. Class 'A', not taken: 1. -/
def colHalf (x : WsFac) (g : WsGrp) (c : ℕ) : K :=
  if g.cls == 'E' then Blocks.eqN g.t (takenOff g) (pt ρ x.pt) c
  else if g.aTaken then (if c < g.R then ρ.val (x.AV.getD c zeroE) else 0)
  else 1

/-- What a factor weighs the row part r of an index with. Class 'E': r is hi 2^(z - t) + lo'; the
element for hi times the equality weight, at lo', of the z - t coordinates of the bits that are left
to the rows. Class 'A', taken: 1. Class 'A', not taken: the element that is written out for r. -/
def rowHalf (x : WsFac) (g : WsGrp) (r : ℕ) : K :=
  if g.cls == 'E' then
    ρ.val (x.HV.getD (r / 2 ^ (g.z - g.t)) zeroE) *
      Blocks.eqN (g.z - g.t) (leftOff g) (pt ρ x.pt) (r % 2 ^ (g.z - g.t))
  else if g.aTaken then 1
  else ρ.val (x.AV.getD r zeroE)

/-- The verifier's column half. If the coordinates of the group's column bits are zeros and ones
that spell the number c below 2^t, the lowest bit at the group's first column bit, then what
onColumns returns reads as colHalf at c. -/
theorem onColumns_at {x : WsFac} {g : WsGrp} (hg : GrpOK g) {X : ℕ → E} {c : ℕ}
    (hc : c < 2 ^ g.t)
    (hX : ∀ i, i < g.t → X (g.cb0 + i) = if c.testBit i then oneE else zeroE) :
    ρ.val (x.onColumns g X) = colHalf ρ x g c := by
  rcases hg with ⟨hcls, -, ht, -⟩ | ⟨hcls, ht, -⟩
  · have hE : (g.cls == 'E') = true := by rw [hcls]; rfl
    unfold WsFac.onColumns colHalf
    rw [if_pos hE, if_pos hE, foldl_mul_range, ρ.one, one_mul, eqN_low_bits]
    refine prod_congr rfl fun i hi => ?_
    have hi' : i < g.t := mem_range.mp hi
    have e : g.z - 1 - g.takenAt i = takenOff g + (g.t - 1 - i) := by
      unfold WsGrp.takenAt takenOff
      split <;> omega
    rw [hX i hi', wsEq1_bit, e]
    rfl
  · have hE : (g.cls == 'E') = false := by rw [hcls]; rfl
    unfold WsFac.onColumns colHalf
    simp only [hE, Bool.false_eq_true, ↓reduceIte]
    by_cases h0 : 0 < g.t
    · have hA : g.aTaken = true := by
        unfold WsGrp.aTaken
        rw [hcls]
        simp [h0]
      have htR : g.t = clog2 g.R := by
        rcases ht with h | h
        · exact h
        · omega
      have hR : g.R ≤ 2 ^ g.t := by
        rw [htR]
        exact le_two_pow_ceilLog2 g.R
      simp only [hA, ↓reduceIte]
      rw [wsDot_value]
      have hs : (Array.ofFn (n := g.t) fun s => X (g.cb0 + g.t - 1 - s.val)).size = g.t := by simp
      have hterm : ∀ i ∈ range g.R, ρ.val (x.AV.getD i zeroE) *
          ρ.val ((eqTab (Array.ofFn (n := g.t) fun s => X (g.cb0 + g.t - 1 - s.val))).getD i
            zeroE) = if i = c then ρ.val (x.AV.getD i zeroE) else 0 := by
        intro i hi
        have hi2 : i < 2 ^ g.t := lt_of_lt_of_le (mem_range.mp hi) hR
        rw [eqTab_value ρ _ i (by rw [hs]; exact hi2), hs, eqN_bool g.t 0 _ hc hi2 ?_]
        · by_cases hic : i = c
          · rw [if_pos hic, if_pos hic, mul_one]
          · rw [if_neg hic, if_neg hic, mul_zero]
        · intro s hs'
          have e1 : g.cb0 + g.t - 1 - s = g.cb0 + (g.t - 1 - s) := by omega
          have e2 : pt ρ (Array.ofFn (n := g.t) fun s => X (g.cb0 + g.t - 1 - s.val)) (0 + s) =
              ρ.val (X (g.cb0 + g.t - 1 - s)) := by
            simp [pt, Array.getD, hs']
          rw [e2, e1, hX _ (by omega)]
          cases c.testBit (g.t - 1 - s)
          · simp [ρ.zero]
          · simp [ρ.one]
      rw [sum_congr rfl hterm, Finset.sum_ite_eq']
      simp only [mem_range]
    · have hA : g.aTaken = false := by
        unfold WsGrp.aTaken
        simp [h0]
      simp only [hA, Bool.false_eq_true, ↓reduceIte]
      exact ρ.one

/-- The coordinates that a factor of class 'E' leaves to the rows: the z - t coordinates of its
point from leftOff on. -/
theorem rows_point (x : WsFac) (g : WsGrp) (ht : g.t ≤ g.z) :
    ((List.range g.z).filterMap fun i =>
      if g.takenBit (g.z - 1 - i) then none else some (x.pt.getD i zeroE)) =
      (List.range (g.z - g.t)).map fun k => x.pt.getD (leftOff g + k) zeroE := by
  by_cases hh : g.high = true
  · have hr : List.range g.z = List.range g.t ++ (List.range (g.z - g.t)).map (g.t + ·) := by
      rw [← List.range_add]
      congr 1
      omega
    rw [hr, List.filterMap_append, filterMap_none, List.nil_append,
      filterMap_all (g := fun i => x.pt.getD i zeroE), List.map_map]
    · unfold leftOff
      rw [if_pos hh]
      rfl
    · intro a ha
      obtain ⟨k, hk, rfl⟩ := List.mem_map.mp ha
      have hk' := List.mem_range.mp hk
      have hb : g.takenBit (g.z - 1 - (g.t + k)) = false := by
        unfold WsGrp.takenBit
        rw [if_pos hh]
        simp
        omega
      rw [hb]
      rfl
    · intro a ha
      have ha' := List.mem_range.mp ha
      have hb : g.takenBit (g.z - 1 - a) = true := by
        unfold WsGrp.takenBit
        rw [if_pos hh]
        simp
        omega
      rw [hb]
      rfl
  · have hr : List.range g.z =
        List.range (g.z - g.t) ++ (List.range g.t).map (g.z - g.t + ·) := by
      rw [← List.range_add]
      congr 1
      omega
    rw [hr, List.filterMap_append, filterMap_all (g := fun i => x.pt.getD i zeroE),
      filterMap_none, List.append_nil]
    · unfold leftOff
      rw [if_neg hh]
      simp
    · intro a ha
      obtain ⟨k, hk, rfl⟩ := List.mem_map.mp ha
      have hk' := List.mem_range.mp hk
      have hb : g.takenBit (g.z - 1 - (g.z - g.t + k)) = true := by
        unfold WsGrp.takenBit
        rw [if_neg hh]
        simp
        omega
      rw [hb]
      rfl
    · intro a ha
      have ha' := List.mem_range.mp ha
      have hb : g.takenBit (g.z - 1 - a) = false := by
        unfold WsGrp.takenBit
        rw [if_neg hh]
        simp
        omega
      rw [hb]
      rfl

/-- The table of a factor of class 'E' on the rows. -/
theorem table_E (x : WsFac) (g : WsGrp) (hE : (g.cls == 'E') = true) (ht : g.t ≤ g.z) :
    (x.onRows g).table g = wsOuter x.HV
      (eqTab ((List.range (g.z - g.t)).map fun k => x.pt.getD (leftOff g + k) zeroE).toArray) := by
  unfold WsFac.onRows WsRowFac.table
  rw [if_pos hE, if_pos hE]
  show wsOuter x.HV (eqTab ((List.range g.z).filterMap fun i =>
      if g.takenBit (g.z - 1 - i) then none else some (x.pt.getD i zeroE)).toArray) = _
  rw [rows_point x g ht]

/-- What a group of class 'E' leaves to the rows. -/
theorem left_E {g : WsGrp} (hR : g.R = g.o * 2 ^ g.z) (ht : g.t ≤ g.z)
    (hl : g.left = g.R / 2 ^ g.t) : g.left = g.o * 2 ^ (g.z - g.t) := by
  have e : g.o * 2 ^ g.z = g.o * 2 ^ (g.z - g.t) * 2 ^ g.t := by
    rw [Nat.mul_assoc, ← Nat.pow_add, Nat.sub_add_cancel ht]
  rw [hl, hR, e, Nat.mul_div_cancel _ (Nat.pow_pos (by norm_num))]

/-- The verifier's table of a factor on the rows has one member for each value that the group leaves
to the rows. -/
theorem table_size {x : WsFac} {g : WsGrp} (hg : GrpOK g) (hfit : x.fits g = true) :
    ((x.onRows g).table g).size = g.left := by
  rcases hg with ⟨hcls, hR, ht, hl⟩ | ⟨hcls, ht, hl⟩
  · have hE : (g.cls == 'E') = true := by rw [hcls]; rfl
    unfold WsFac.fits at hfit
    rw [if_pos hE] at hfit
    simp only [Bool.and_eq_true, beq_iff_eq] at hfit
    rw [table_E x g hE ht, wsOuter_size, eqTab_size, hfit.1.1, left_E hR ht hl]
    simp
  · have hE : (g.cls == 'E') = false := by rw [hcls]; rfl
    unfold WsFac.fits at hfit
    rw [if_neg (by rw [hE]; simp)] at hfit
    simp only [Bool.and_eq_true, beq_iff_eq] at hfit
    unfold WsFac.onRows WsRowFac.table
    simp only [hE, Bool.false_eq_true, ↓reduceIte]
    by_cases h0 : 0 < g.t
    · have hA : g.aTaken = true := by
        unfold WsGrp.aTaken
        rw [hcls]
        simp [h0]
      simp only [hA, ↓reduceIte]
      rw [hl, if_pos h0]
      rfl
    · have hA : g.aTaken = false := by
        unfold WsGrp.aTaken
        simp [h0]
      simp only [hA, Bool.false_eq_true, ↓reduceIte]
      rw [hl, if_neg h0]
      exact hfit.1.1

/-- The verifier's row half: the member r of the table of a factor on the rows reads as rowHalf
at r, for r below what the group leaves to the rows. -/
theorem table_at {x : WsFac} {g : WsGrp} (hg : GrpOK g) (hfit : x.fits g = true) {r : ℕ}
    (hr : r < g.left) :
    ρ.val (((x.onRows g).table g).getD r zeroE) = rowHalf ρ x g r := by
  rcases hg with ⟨hcls, hR, ht, hl⟩ | ⟨hcls, ht, hl⟩
  · have hE : (g.cls == 'E') = true := by rw [hcls]; rfl
    unfold WsFac.fits at hfit
    rw [if_pos hE] at hfit
    simp only [Bool.and_eq_true, beq_iff_eq] at hfit
    have hps : (((List.range (g.z - g.t)).map fun k =>
        x.pt.getD (leftOff g + k) zeroE).toArray).size = g.z - g.t := by simp
    have hts := eqTab_size (((List.range (g.z - g.t)).map fun k =>
        x.pt.getD (leftOff g + k) zeroE).toArray)
    rw [hps] at hts
    have hpos : 0 < 2 ^ (g.z - g.t) := Nat.pow_pos (by norm_num)
    have hq : r % 2 ^ (g.z - g.t) < 2 ^ (g.z - g.t) := Nat.mod_lt _ hpos
    have hi : r / 2 ^ (g.z - g.t) < x.HV.size := by
      rw [hfit.1.1]
      refine Nat.div_lt_of_lt_mul ?_
      rw [Nat.mul_comm, ← left_E hR ht hl]
      exact hr
    have e : r = r / 2 ^ (g.z - g.t) * (eqTab (((List.range (g.z - g.t)).map fun k =>
        x.pt.getD (leftOff g + k) zeroE).toArray)).size + r % 2 ^ (g.z - g.t) := by
      rw [hts, Nat.div_add_mod']
    unfold rowHalf
    rw [if_pos hE, table_E x g hE ht]
    conv_lhs => rw [e]
    rw [wsOuter_getD _ _ hi (by rw [hts]; exact hq), ρ.mul,
      eqTab_value ρ _ _ (by rw [hps]; exact hq), hps,
      ← eqN_shift' (g.z - g.t) (leftOff g) (pt ρ x.pt)]
    congr 1
    refine eqN_congr' (K := K) _ 0 (fun j hj => ?_) _
    simp [pt, Array.getD, hj]
  · have hE : (g.cls == 'E') = false := by rw [hcls]; rfl
    unfold WsFac.onRows WsRowFac.table rowHalf
    simp only [hE, Bool.false_eq_true, ↓reduceIte]
    by_cases h0 : 0 < g.t
    · have hA : g.aTaken = true := by
        unfold WsGrp.aTaken
        rw [hcls]
        simp [h0]
      rw [hl, if_pos h0] at hr
      obtain rfl : r = 0 := by omega
      simp only [hA, ↓reduceIte]
      exact ρ.one
    · have hA : g.aTaken = false := by
        unfold WsGrp.aTaken
        simp [h0]
      simp only [hA, Bool.false_eq_true, ↓reduceIte]

end Halves

/-! ## A factor is the product of its two halves -/

/-- The index of a group of class 'E' that is made of hi, of the bits l that are left to the rows
and of the bits c that go to the columns. -/
def joinG (g : WsGrp) (hi l c : ℕ) : ℕ :=
  if g.high then (hi * 2 ^ g.t + c) * 2 ^ (g.z - g.t) + l
  else (hi * 2 ^ (g.z - g.t) + l) * 2 ^ g.t + c

/-- Every number is such an index. -/
theorem joinG_surj (g : WsGrp) (v : ℕ) :
    ∃ hi l c, l < 2 ^ (g.z - g.t) ∧ c < 2 ^ g.t ∧ v = joinG g hi l c := by
  have hA : 0 < 2 ^ (g.z - g.t) := Nat.pow_pos (by norm_num)
  have hB : 0 < 2 ^ g.t := Nat.pow_pos (by norm_num)
  unfold joinG
  by_cases hh : g.high = true
  · refine ⟨v / 2 ^ (g.z - g.t) / 2 ^ g.t, v % 2 ^ (g.z - g.t), v / 2 ^ (g.z - g.t) % 2 ^ g.t,
      Nat.mod_lt _ hA, Nat.mod_lt _ hB, ?_⟩
    rw [if_pos hh, Nat.div_add_mod', Nat.div_add_mod']
  · refine ⟨v / 2 ^ g.t / 2 ^ (g.z - g.t), v / 2 ^ g.t % 2 ^ (g.z - g.t), v % 2 ^ g.t,
      Nat.mod_lt _ hA, Nat.mod_lt _ hB, ?_⟩
    rw [if_neg hh, Nat.div_add_mod', Nat.div_add_mod']

/-- Class 'E': splitG takes the index joinG hi l c apart into the column part c and the row part
hi 2^(z - t) + l; and the index lies below (hi + 1) 2^z. -/
theorem joinG_split {g : WsGrp} (hE : (g.cls == 'E') = true) (ht : g.t ≤ g.z) (hi : ℕ) {l c : ℕ}
    (hl : l < 2 ^ (g.z - g.t)) (hc : c < 2 ^ g.t) :
    splitG g (joinG g hi l c) = (c, hi * 2 ^ (g.z - g.t) + l) ∧
      joinG g hi l c < (hi + 1) * 2 ^ g.z := by
  have hz : 2 ^ g.z = 2 ^ (g.z - g.t) * 2 ^ g.t := by
    rw [← Nat.pow_add, Nat.sub_add_cancel ht]
  unfold splitG joinG
  rw [if_pos hE]
  by_cases hh : g.high = true
  · rw [if_pos hh, if_pos hh]
    have hlo : c * 2 ^ (g.z - g.t) + l < 2 ^ g.z := by
      have h1 := Nat.mul_le_mul_right (2 ^ (g.z - g.t)) (Nat.succ_le_of_lt hc)
      rw [Nat.succ_mul] at h1
      rw [hz, Nat.mul_comm (2 ^ (g.z - g.t))]
      omega
    have ev : (hi * 2 ^ g.t + c) * 2 ^ (g.z - g.t) + l =
        hi * 2 ^ g.z + (c * 2 ^ (g.z - g.t) + l) := by
      rw [hz]
      ring
    obtain ⟨a1, a2⟩ := div_mod_block (i := hi * 2 ^ g.t + c) hl
    obtain ⟨-, b2⟩ := div_mod_block (i := hi) hc
    obtain ⟨c1, -⟩ := div_mod_block (i := hi) hlo
    refine ⟨by rw [a1, a2, b2, ev, c1], ?_⟩
    rw [ev, Nat.succ_mul]
    omega
  · rw [if_neg hh, if_neg hh]
    have hlo : l * 2 ^ g.t + c < 2 ^ g.z := by
      have h1 := Nat.mul_le_mul_right (2 ^ g.t) (Nat.succ_le_of_lt hl)
      rw [Nat.succ_mul] at h1
      rw [hz]
      omega
    have ev : (hi * 2 ^ (g.z - g.t) + l) * 2 ^ g.t + c = hi * 2 ^ g.z + (l * 2 ^ g.t + c) := by
      rw [hz]
      ring
    obtain ⟨a1, a2⟩ := div_mod_block (i := hi * 2 ^ (g.z - g.t) + l) hc
    refine ⟨by rw [a1, a2], ?_⟩
    rw [ev, Nat.succ_mul]
    omega

/-- No two indices have the same two parts. -/
theorem splitG_inj {g : WsGrp} (hg : GrpOK g) {v v' : ℕ} (h : splitG g v = splitG g v') :
    v = v' := by
  rcases hg with ⟨hcls, -, ht, -⟩ | ⟨hcls, -, -⟩
  · have hE : (g.cls == 'E') = true := by rw [hcls]; rfl
    obtain ⟨hi, l, c, hl, hc, rfl⟩ := joinG_surj g v
    obtain ⟨hi', l', c', hl', hc', rfl⟩ := joinG_surj g v'
    rw [(joinG_split hE ht hi hl hc).1, (joinG_split hE ht hi' hl' hc').1] at h
    have h1 : c = c' := congrArg Prod.fst h
    have h2 : hi * 2 ^ (g.z - g.t) + l = hi' * 2 ^ (g.z - g.t) + l' := congrArg Prod.snd h
    have e1 : hi = hi' := by
      rw [← (div_mod_block (i := hi) hl).1, h2, (div_mod_block (i := hi') hl').1]
    have e2 : l = l' := by
      rw [← (div_mod_block (i := hi) hl).2, h2, (div_mod_block (i := hi') hl').2]
    rw [h1, e1, e2]
  · have hE : (g.cls == 'E') = false := by rw [hcls]; rfl
    unfold splitG at h
    simp only [hE, Bool.false_eq_true, ↓reduceIte] at h
    by_cases hA : g.aTaken = true
    · simp only [hA, ↓reduceIte] at h
      exact congrArg Prod.fst h
    · simp only [hA, Bool.false_eq_true, ↓reduceIte] at h
      exact congrArg Prod.snd h

section Split

variable {K : Type} [Field K] (ρ : Reading K)

/-- Class 'E': splitG takes the index joinG hi l c apart into the column part c and the row part
hi 2^(z - t) + l, and the factor weighs the index with the product of its two halves at these. -/
theorem joinG_spec (x : WsFac) {g : WsGrp} (hE : (g.cls == 'E') = true) (ht : g.t ≤ g.z)
    (hi : ℕ) {l c : ℕ} (hl : l < 2 ^ (g.z - g.t)) (hc : c < 2 ^ g.t) :
    splitG g (joinG g hi l c) = (c, hi * 2 ^ (g.z - g.t) + l) ∧
      facAt ρ x g (joinG g hi l c) =
        colHalf ρ x g c * rowHalf ρ x g (hi * 2 ^ (g.z - g.t) + l) := by
  have hz : 2 ^ g.z = 2 ^ (g.z - g.t) * 2 ^ g.t := by
    rw [← Nat.pow_add, Nat.sub_add_cancel ht]
  obtain ⟨r1, r2⟩ := div_mod_block (i := hi) hl
  unfold splitG facAt colHalf rowHalf joinG takenOff leftOff
  rw [if_pos hE, if_pos hE, if_pos hE, if_pos hE, r1, r2]
  by_cases hh : g.high = true
  · rw [if_pos hh, if_pos hh, if_pos hh, if_pos hh]
    have hlo : c * 2 ^ (g.z - g.t) + l < 2 ^ g.z := by
      have h1 := Nat.mul_le_mul_right (2 ^ (g.z - g.t)) (Nat.succ_le_of_lt hc)
      rw [Nat.succ_mul] at h1
      rw [hz, Nat.mul_comm (2 ^ (g.z - g.t))]
      omega
    have ev : (hi * 2 ^ g.t + c) * 2 ^ (g.z - g.t) + l =
        hi * 2 ^ g.z + (c * 2 ^ (g.z - g.t) + l) := by
      rw [hz]
      ring
    obtain ⟨a1, a2⟩ := div_mod_block (i := hi * 2 ^ g.t + c) hl
    obtain ⟨b1, b2⟩ := div_mod_block (i := hi) hc
    obtain ⟨c1, c2⟩ := div_mod_block (i := hi) hlo
    refine ⟨?_, ?_⟩
    · rw [a1, a2, b2, ev, c1]
    · have ez : g.z = g.t + (g.z - g.t) := by omega
      have e2 : Blocks.eqN g.z 0 (pt ρ x.pt) (c * 2 ^ (g.z - g.t) + l) =
          Blocks.eqN g.t 0 (pt ρ x.pt) c * Blocks.eqN (g.z - g.t) g.t (pt ρ x.pt) l := by
        have h3 := Blocks.eqN_append' g.t (g.z - g.t) 0 (pt ρ x.pt) c hl
        rw [← ez, Nat.zero_add] at h3
        exact h3
      rw [ev, c1, c2, e2]
      ring
  · rw [if_neg hh, if_neg hh, if_neg hh, if_neg hh]
    have hlo : l * 2 ^ g.t + c < 2 ^ g.z := by
      have h1 := Nat.mul_le_mul_right (2 ^ g.t) (Nat.succ_le_of_lt hl)
      rw [Nat.succ_mul] at h1
      rw [hz]
      omega
    have ev : (hi * 2 ^ (g.z - g.t) + l) * 2 ^ g.t + c = hi * 2 ^ g.z + (l * 2 ^ g.t + c) := by
      rw [hz]
      ring
    obtain ⟨a1, a2⟩ := div_mod_block (i := hi * 2 ^ (g.z - g.t) + l) hc
    obtain ⟨c1, c2⟩ := div_mod_block (i := hi) hlo
    refine ⟨?_, ?_⟩
    · rw [a1, a2]
    · have ez : g.z = g.z - g.t + g.t := by omega
      have e2 : Blocks.eqN g.z 0 (pt ρ x.pt) (l * 2 ^ g.t + c) =
          Blocks.eqN (g.z - g.t) 0 (pt ρ x.pt) l * Blocks.eqN g.t (g.z - g.t) (pt ρ x.pt) c := by
        have h3 := Blocks.eqN_append' (g.z - g.t) g.t 0 (pt ρ x.pt) l hc
        rw [← ez, Nat.zero_add] at h3
        exact h3
      rw [ev, c1, c2, e2]
      ring

/-- A factor is the product of its two halves: at every index v below R, what the factor weighs v
with is its column half at the column part of v times its row half at the row part of v. -/
theorem fac_split (x : WsFac) {g : WsGrp} (hg : GrpOK g) {v : ℕ} (hv : v < g.R) :
    colHalf ρ x g (splitG g v).1 * rowHalf ρ x g (splitG g v).2 = facAt ρ x g v := by
  rcases hg with ⟨hcls, -, ht, -⟩ | ⟨hcls, -, -⟩
  · have hE : (g.cls == 'E') = true := by rw [hcls]; rfl
    obtain ⟨hi, l, c, hl, hc, rfl⟩ := joinG_surj g v
    obtain ⟨s1, s2⟩ := joinG_spec ρ x hE ht hi hl hc
    rw [s1, s2]
  · have hE : (g.cls == 'E') = false := by rw [hcls]; rfl
    unfold splitG facAt colHalf rowHalf
    simp only [hE, Bool.false_eq_true, ↓reduceIte]
    by_cases hA : g.aTaken = true
    · simp only [hA, ↓reduceIte, hv, mul_one]
    · simp only [hA, Bool.false_eq_true, ↓reduceIte, one_mul]

/-- A column part c below 2^t and a row part r below what the group leaves to the rows are the two
parts of an index below R, or the two halves weigh them with 0. -/
theorem split_onto (x : WsFac) {g : WsGrp} (hg : GrpOK g) {c r : ℕ} (hc : c < 2 ^ g.t)
    (hr : r < g.left) :
    (∃ v, v < g.R ∧ splitG g v = (c, r)) ∨ colHalf ρ x g c * rowHalf ρ x g r = 0 := by
  rcases hg with ⟨hcls, hR, ht, hl⟩ | ⟨hcls, ht, hl⟩
  · have hE : (g.cls == 'E') = true := by rw [hcls]; rfl
    have hpos : 0 < 2 ^ (g.z - g.t) := Nat.pow_pos (by norm_num)
    obtain ⟨s1, s2⟩ := joinG_split hE ht (r / 2 ^ (g.z - g.t)) (Nat.mod_lt r hpos) hc
    have hi : r / 2 ^ (g.z - g.t) < g.o := by
      refine Nat.div_lt_of_lt_mul ?_
      rw [Nat.mul_comm, ← left_E hR ht hl]
      exact hr
    refine Or.inl ⟨joinG g (r / 2 ^ (g.z - g.t)) (r % 2 ^ (g.z - g.t)) c, ?_, ?_⟩
    · rw [hR]
      exact lt_of_lt_of_le s2 (Nat.mul_le_mul_right _ hi)
    · rw [s1, Nat.div_add_mod']
  · have hE : (g.cls == 'E') = false := by rw [hcls]; rfl
    by_cases h0 : 0 < g.t
    · have hA : g.aTaken = true := by
        unfold WsGrp.aTaken
        rw [hcls]
        simp [h0]
      rw [hl, if_pos h0] at hr
      obtain rfl : r = 0 := by omega
      by_cases hcR : c < g.R
      · refine Or.inl ⟨c, hcR, ?_⟩
        unfold splitG
        simp only [hE, hA, Bool.false_eq_true, ↓reduceIte]
      · refine Or.inr ?_
        unfold colHalf
        simp only [hE, hA, hcR, Bool.false_eq_true, ↓reduceIte, zero_mul]
    · have hA : g.aTaken = false := by
        unfold WsGrp.aTaken
        simp [h0]
      have ht0 : g.t = 0 := by omega
      rw [ht0, pow_zero] at hc
      obtain rfl : c = 0 := by omega
      rw [hl, if_neg h0] at hr
      refine Or.inl ⟨r, hr, ?_⟩
      unfold splitG
      simp only [hE, hA, Bool.false_eq_true, ↓reduceIte]

/-- Summing over column parts and row parts is summing over indices. For every F: the sum over all
c below 2^t and all r below what the group leaves to the rows of the two halves times F c r is the
sum over the indices v below R of what the factor weighs v with, times F at the two parts of v. -/
theorem fac_sum (x : WsFac) {g : WsGrp} (hg : GrpOK g) (F : ℕ → ℕ → K) :
    ∑ c ∈ range (2 ^ g.t), ∑ r ∈ range g.left, colHalf ρ x g c * rowHalf ρ x g r * F c r =
      ∑ v ∈ range g.R, facAt ρ x g v * F (splitG g v).1 (splitG g v).2 := by
  rcases hg with ⟨hcls, hR, ht, hl⟩ | ⟨hcls, ht, hl⟩
  · have hE : (g.cls == 'E') = true := by rw [hcls]; rfl
    have hz : 2 ^ g.z = 2 ^ (g.z - g.t) * 2 ^ g.t := by
      rw [← Nat.pow_add, Nat.sub_add_cancel ht]
    rw [Finset.sum_comm, left_E hR ht hl, sum_blocks]
    by_cases hh : g.high = true
    · have hR' : g.R = g.o * 2 ^ g.t * 2 ^ (g.z - g.t) := by
        rw [hR, hz]
        ring
      rw [hR', sum_blocks, sum_blocks]
      refine sum_congr rfl fun hi _ => ?_
      rw [Finset.sum_comm]
      refine sum_congr rfl fun c hc => sum_congr rfl fun l hl' => ?_
      obtain ⟨s1, s2⟩ := joinG_spec ρ x hE ht hi (mem_range.mp hl') (mem_range.mp hc)
      unfold joinG at s1 s2
      rw [if_pos hh] at s1 s2
      rw [s1, s2]
    · have hR' : g.R = g.o * 2 ^ (g.z - g.t) * 2 ^ g.t := by
        rw [hR, hz]
        ring
      rw [hR', sum_blocks, sum_blocks]
      refine sum_congr rfl fun hi _ => sum_congr rfl fun l hl' => sum_congr rfl fun c hc => ?_
      obtain ⟨s1, s2⟩ := joinG_spec ρ x hE ht hi (mem_range.mp hl') (mem_range.mp hc)
      unfold joinG at s1 s2
      rw [if_neg hh] at s1 s2
      rw [s1, s2]
  · have hE : (g.cls == 'E') = false := by rw [hcls]; rfl
    unfold splitG facAt colHalf rowHalf
    simp only [hE, Bool.false_eq_true, ↓reduceIte]
    by_cases h0 : 0 < g.t
    · have hA : g.aTaken = true := by
        unfold WsGrp.aTaken
        rw [hcls]
        simp [h0]
      have htR : g.t = clog2 g.R := by
        rcases ht with h | h
        · exact h
        · omega
      have hR : g.R ≤ 2 ^ g.t := by
        rw [htR]
        exact le_two_pow_ceilLog2 g.R
      rw [hl, if_pos h0]
      simp only [hA, ↓reduceIte, Finset.sum_range_one, mul_one]
      rw [← Finset.sum_subset (range_subset_range.mpr hR)]
      · exact sum_congr rfl fun v hv => by rw [if_pos (mem_range.mp hv)]
      · intro v _ hv
        rw [if_neg (fun h => hv (mem_range.mpr h)), zero_mul]
    · have hA : g.aTaken = false := by
        unfold WsGrp.aTaken
        simp [h0]
      have ht0 : g.t = 0 := by omega
      rw [hl, if_neg h0, ht0]
      simp only [hA, Bool.false_eq_true, ↓reduceIte, pow_zero, Finset.sum_range_one, one_mul]

end Split

/-! ## A claim's coefficients on the rows of its unit -/

/-- The coefficients that wsGamma makes from the vector d of the digits' scalars: for the last pair
of a factor and its group first, all products with the factor's table on the rows. -/
def gamOf (l : List (WsFac × WsGrp)) (d : Array E) : Array E :=
  l.foldr (fun y v => wsOuter v ((y.1.onRows y.2).table y.2)) d

/-- Images of the pairs of two lists, paired again with the second list. -/
theorem zip_map_zip {α β γ : Type} (h : α × β → γ) : ∀ (f : List α) (g : List β),
    ((f.zip g).map h).zip g = (f.zip g).map fun y => (h y, y.2)
  | [], _ => by simp
  | _ :: _, [] => by simp
  | a :: f, b :: g => by simp [zip_map_zip h f g]

/-- wsGamma on what wsRowPart leaves of a claim. -/
theorem wsGamma_eq {lay : WsLay} {c : WsClaim} {u : WsUnit} (hu : lay.U[c.ui]? = some u)
    (ka wgt : E) :
    wsGamma u (wsRowPart lay c ka) wgt =
      gamOf (c.f.zip u.g) (wsDigits u.nlw (mulE wgt ka)).toArray := by
  have e : wsRowPart lay c ka =
      { ui := c.ui, ka := ka, f := (c.f.zip u.g).map fun y => y.1.onRows y.2 } := by
    unfold wsRowPart
    rw [hu]
  rw [e]
  unfold wsGamma gamOf
  show ((((c.f.zip u.g).map fun y => y.1.onRows y.2).zip u.g).reverse.foldl
    (fun v y => wsOuter v (y.1.table y.2)) (wsDigits u.nlw (mulE wgt ka)).toArray) = _
  rw [zip_map_zip, List.foldl_reverse, List.foldr_map]

/-- The number of these coefficients: one for each digit and each tuple of what the groups leave to
the rows. -/
theorem gamOf_size : ∀ (l : List (WsFac × WsGrp)),
    (∀ y ∈ l, GrpOK y.2 ∧ y.1.fits y.2 = true) → ∀ d : Array E,
    (gamOf l d).size = d.size * (l.map (·.2.left)).prod
  | [], _, d => by simp [gamOf]
  | (x, g) :: rest, hok, d => by
    obtain ⟨hg, hfit⟩ := hok (x, g) List.mem_cons_self
    show (wsOuter (gamOf rest d) ((x.onRows g).table g)).size = _
    rw [wsOuter_size, table_size hg hfit,
      gamOf_size rest (fun y hy => hok y (List.mem_cons_of_mem _ hy)) d, List.map_cons,
      List.prod_cons]
    ring

/-- The digits' scalars are as many as the digits. -/
theorem wsDigits_length : ∀ (n : ℕ) (s : E), (wsDigits n s).length = n
  | 0, _ => rfl
  | n + 1, s => by
    show (wsDigits n _).length + 1 = n + 1
    rw [wsDigits_length n]

/-! ## The column, counted from the groups' own bits -/

/-- The column as colIn gives it, if the first group's first column bit counts as bit 0 and each
group's bits follow those of the group before. -/
def colRel : List (WsGrp × ℕ) → ℕ
  | [] => 0
  | (g, v) :: rest => colRel rest * 2 ^ g.t + (splitG g v).1

/-- For groups whose column bits follow each other from bit cb on, colIn is colRel, moved up by cb
bits. -/
theorem colIn_rel : ∀ (gs : List WsGrp) (cb : ℕ), Runs gs cb → ∀ idx : List ℕ,
    colIn (gs.zip idx) = 2 ^ cb * colRel (gs.zip idx)
  | [], _, _, _ => by simp [colIn, colRel]
  | _ :: _, _, _, [] => by simp [colIn, colRel]
  | g :: gs, cb, h, v :: idx => by
    show (splitG g v).1 * 2 ^ g.cb0 + colIn (gs.zip idx) =
      2 ^ cb * (colRel (gs.zip idx) * 2 ^ g.t + (splitG g v).1)
    rw [h.1, colIn_rel gs (cb + g.t) h.2 idx, Nat.pow_add]
    ring

/-- A bit of a number that is made of lo below 2^cb, of c below 2^t above it, and of more above. -/
theorem testBit_block {lo cb C2 t c i : ℕ} (hlo : lo < 2 ^ cb) (hc : c < 2 ^ t) (hi : i < t) :
    (lo + 2 ^ cb * (C2 * 2 ^ t + c)).testBit (cb + i) = c.testBit i := by
  rw [Nat.add_comm lo, Nat.testBit_two_pow_mul_add _ hlo, if_neg (by omega),
    Nat.add_sub_cancel_left, Nat.mul_comm C2, Nat.testBit_two_pow_mul_add _ hc, if_pos hi]

section Cells

variable {K : Type} [Field K] (ρ : Reading K)

/-- A common factor of all terms of sumIdx. -/
theorem sumIdx_mul (a : K) : ∀ (l : List (WsFac × WsGrp)) (F : List ℕ → K),
    sumIdx ρ l (fun idx => a * F idx) = a * sumIdx ρ l F
  | [], _ => rfl
  | (x, g) :: rest, F => by
    show ∑ v ∈ range g.R, facAt ρ x g v * sumIdx ρ rest (fun idx => a * F (v :: idx)) =
      a * ∑ v ∈ range g.R, facAt ρ x g v * sumIdx ρ rest fun idx => F (v :: idx)
    rw [Finset.mul_sum]
    refine sum_congr rfl fun v _ => ?_
    rw [sumIdx_mul a rest]
    ring

/-- The heart of the matter, by induction on the groups. l: factors with their groups, whose column
bits follow each other from bit cb on and end at or before bit lk. XX C: coordinates that spell the
number C of a column on the bits below lk. d: any vector in the place of the digits' scalars. lo:
any bits below cb. For every G: the sum over the numbers C that the groups' bits can spell and over
the rows y of the coefficient on row y, times the product of the factors' column halves at the
column lo + 2^cb C, times G C y, is the sum over all tuples of indices of what the factors weigh
them with, times the sum over the members of d of the member times G at the tuple's column and
row. -/
theorem cells_sum (lk : ℕ) (XX : ℕ → ℕ → E)
    (hXX : ∀ C b, b < lk → XX C b = if C.testBit b then oneE else zeroE) :
    ∀ (l : List (WsFac × WsGrp)) (cb : ℕ), (∀ y ∈ l, GrpOK y.2 ∧ y.1.fits y.2 = true) →
      Runs (l.map (·.2)) cb → cb + (l.map (·.2.t)).sum ≤ lk →
      ∀ (d : Array E) (G : ℕ → ℕ → K) (lo : ℕ), lo < 2 ^ cb →
      ∑ C ∈ range (2 ^ (l.map (·.2.t)).sum), ∑ y ∈ range (gamOf l d).size,
        ρ.val ((gamOf l d).getD y zeroE) *
          ((l.map fun p => ρ.val (p.1.onColumns p.2 (XX (lo + 2 ^ cb * C)))).prod * G C y) =
      sumIdx ρ l fun idx => ∑ q ∈ range d.size, ρ.val (d.getD q zeroE) *
        G (colRel ((l.map (·.2)).zip idx)) (rowIn ((l.map (·.2)).zip idx) q)
  | [], cb, _, _, _, d, G, lo, _ => by
    simp [gamOf, sumIdx, colRel, rowIn]
  | (x, g) :: rest, cb, hok, hr, hle, d, G, lo, hlo => by
    obtain ⟨hg, hfit⟩ := hok (x, g) List.mem_cons_self
    have hok' : ∀ y ∈ rest, GrpOK y.2 ∧ y.1.fits y.2 = true :=
      fun y hy => hok y (List.mem_cons_of_mem _ hy)
    have hcb : g.cb0 = cb := hr.1
    have hr' : Runs (rest.map (·.2)) (cb + g.t) := hr.2
    have hsum : (((x, g) :: rest).map (·.2.t)).sum = (rest.map (·.2.t)).sum + g.t := by
      rw [List.map_cons, List.sum_cons, Nat.add_comm]
    have hle' : cb + g.t + (rest.map (·.2.t)).sum ≤ lk := by
      rw [hsum] at hle
      omega
    have hbit : ∀ i, i < g.t → cb + i < lk := by
      intro i hi
      omega
    have hsz := table_size hg hfit
    have IH := cells_sum lk XX hXX rest (cb + g.t) hok' hr' hle' d
    -- what stands under the two halves, before and after the induction hypothesis
    let inner : ℕ → ℕ → K := fun c r =>
      ∑ C2 ∈ range (2 ^ (rest.map (·.2.t)).sum), ∑ y' ∈ range (gamOf rest d).size,
        ρ.val ((gamOf rest d).getD y' zeroE) *
          ((rest.map fun p => ρ.val (p.1.onColumns p.2
            (XX (lo + 2 ^ cb * c + 2 ^ (cb + g.t) * C2)))).prod *
            G (C2 * 2 ^ g.t + c) (y' * g.left + r))
    let F : ℕ → ℕ → K := fun c r =>
      sumIdx ρ rest fun idx => ∑ q ∈ range d.size, ρ.val (d.getD q zeroE) *
        G (colRel ((rest.map (·.2)).zip idx) * 2 ^ g.t + c)
          (rowIn ((rest.map (·.2)).zip idx) q * g.left + r)
    have step2 : ∀ c ∈ range (2 ^ g.t), ∀ r, inner c r = F c r := by
      intro c hc r
      have hc' : c < 2 ^ g.t := mem_range.mp hc
      have hlo' : lo + 2 ^ cb * c < 2 ^ (cb + g.t) := by
        have h1 := Nat.mul_le_mul_left (2 ^ cb) (Nat.succ_le_of_lt hc')
        rw [Nat.mul_succ] at h1
        rw [Nat.pow_add]
        omega
      exact IH (fun C2 y' => G (C2 * 2 ^ g.t + c) (y' * g.left + r)) (lo + 2 ^ cb * c) hlo'
    have step1 : ∑ C ∈ range (2 ^ (((x, g) :: rest).map (·.2.t)).sum),
        ∑ y ∈ range (gamOf ((x, g) :: rest) d).size,
          ρ.val ((gamOf ((x, g) :: rest) d).getD y zeroE) *
            ((((x, g) :: rest).map fun p =>
              ρ.val (p.1.onColumns p.2 (XX (lo + 2 ^ cb * C)))).prod * G C y) =
        ∑ c ∈ range (2 ^ g.t), ∑ r ∈ range g.left,
          colHalf ρ x g c * rowHalf ρ x g r * inner c r := by
      rw [hsum, Nat.pow_add, sum_blocks, Finset.sum_comm]
      refine sum_congr rfl fun c hc => ?_
      have hc' : c < 2 ^ g.t := mem_range.mp hc
      calc ∑ C2 ∈ range (2 ^ (rest.map (·.2.t)).sum),
            ∑ y ∈ range (gamOf ((x, g) :: rest) d).size,
              ρ.val ((gamOf ((x, g) :: rest) d).getD y zeroE) *
                ((((x, g) :: rest).map fun p => ρ.val (p.1.onColumns p.2
                  (XX (lo + 2 ^ cb * (C2 * 2 ^ g.t + c))))).prod * G (C2 * 2 ^ g.t + c) y)
          = ∑ C2 ∈ range (2 ^ (rest.map (·.2.t)).sum), ∑ y' ∈ range (gamOf rest d).size,
              ∑ r ∈ range g.left, colHalf ρ x g c * rowHalf ρ x g r *
                (ρ.val ((gamOf rest d).getD y' zeroE) *
                  ((rest.map fun p => ρ.val (p.1.onColumns p.2
                    (XX (lo + 2 ^ cb * c + 2 ^ (cb + g.t) * C2)))).prod *
                    G (C2 * 2 ^ g.t + c) (y' * g.left + r))) := by
            refine sum_congr rfl fun C2 _ => ?_
            show ∑ y ∈ range (wsOuter (gamOf rest d) ((x.onRows g).table g)).size,
              ρ.val ((wsOuter (gamOf rest d) ((x.onRows g).table g)).getD y zeroE) * _ = _
            rw [sum_wsOuter, hsz]
            refine sum_congr rfl fun y' _ => sum_congr rfl fun r hr2 => ?_
            have e1 : ρ.val (x.onColumns g (XX (lo + 2 ^ cb * (C2 * 2 ^ g.t + c)))) =
                colHalf ρ x g c := by
              refine onColumns_at ρ hg hc' fun i hi => ?_
              rw [hcb, hXX _ _ (hbit i hi), testBit_block hlo hc' hi]
            have e2 : lo + 2 ^ cb * (C2 * 2 ^ g.t + c) =
                lo + 2 ^ cb * c + 2 ^ (cb + g.t) * C2 := by
              rw [Nat.pow_add]
              ring
            rw [List.map_cons, List.prod_cons, e1, table_at ρ hg hfit (mem_range.mp hr2), e2]
            ring
        _ = ∑ C2 ∈ range (2 ^ (rest.map (·.2.t)).sum), ∑ r ∈ range g.left,
              ∑ y' ∈ range (gamOf rest d).size, colHalf ρ x g c * rowHalf ρ x g r *
                (ρ.val ((gamOf rest d).getD y' zeroE) *
                  ((rest.map fun p => ρ.val (p.1.onColumns p.2
                    (XX (lo + 2 ^ cb * c + 2 ^ (cb + g.t) * C2)))).prod *
                    G (C2 * 2 ^ g.t + c) (y' * g.left + r))) :=
            sum_congr rfl fun _ _ => Finset.sum_comm
        _ = ∑ r ∈ range g.left, ∑ C2 ∈ range (2 ^ (rest.map (·.2.t)).sum),
              ∑ y' ∈ range (gamOf rest d).size, colHalf ρ x g c * rowHalf ρ x g r *
                (ρ.val ((gamOf rest d).getD y' zeroE) *
                  ((rest.map fun p => ρ.val (p.1.onColumns p.2
                    (XX (lo + 2 ^ cb * c + 2 ^ (cb + g.t) * C2)))).prod *
                    G (C2 * 2 ^ g.t + c) (y' * g.left + r))) := Finset.sum_comm
        _ = ∑ r ∈ range g.left, colHalf ρ x g c * rowHalf ρ x g r * inner c r := by
            refine sum_congr rfl fun r _ => ?_
            show _ = colHalf ρ x g c * rowHalf ρ x g r * ∑ C2 ∈ _, ∑ y' ∈ _, _
            rw [Finset.mul_sum]
            exact sum_congr rfl fun _ _ => (Finset.mul_sum _ _ _).symm
    calc _ = ∑ c ∈ range (2 ^ g.t), ∑ r ∈ range g.left,
          colHalf ρ x g c * rowHalf ρ x g r * inner c r := step1
      _ = ∑ c ∈ range (2 ^ g.t), ∑ r ∈ range g.left,
          colHalf ρ x g c * rowHalf ρ x g r * F c r :=
        sum_congr rfl fun c hc => sum_congr rfl fun r _ => by rw [step2 c hc r]
      _ = ∑ v ∈ range g.R, facAt ρ x g v * F (splitG g v).1 (splitG g v).2 := fac_sum ρ x hg F
      _ = _ := rfl

end Cells

/-! ## What a claim says, from the verifier's two halves -/

/-- The base of the digits is the word of the number 256. -/
theorem second_digit : Model.fOfNat 256 = wsSecondDigit := by decide

/-- A member of a list that is read as an array. -/
theorem toArray_getD (l : List E) (i : ℕ) : l.toArray.getD i zeroE = l.getD i zeroE := by
  simp [Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD]

/-- The coordinate of column bit b in the point that spells the number C of a column. -/
theorem bitsOf_at {lk C b : ℕ} (hb : b < lk) :
    (bitsOf lk C).getD (lk - 1 - b) zeroE = if C.testBit b then oneE else zeroE := by
  have h1 : lk - 1 - b < lk := by omega
  have e : lk - 1 - (lk - 1 - b) = b := by omega
  simp [bitsOf, Array.getD, h1, e]

section Claim

variable {K : Type} [Field K] (ρ : Reading K)

variable {ρ} in
/-- The scalar of digit q reads as 256^q times the first. -/
theorem wsDigits_value (hρ : Numerals ρ) : ∀ (n : ℕ) (s : E) (q : ℕ), q < n →
    ρ.val ((wsDigits n s).getD q zeroE) = (256 : K) ^ q * ρ.val s
  | 0, _, q, h => absurd h (Nat.not_lt_zero q)
  | n + 1, s, 0, _ => by simp [wsDigits]
  | n + 1, s, q + 1, h => by
    have e1 : (wsDigits (n + 1) s).getD (q + 1) zeroE =
        (wsDigits n (scaleE wsSecondDigit s)).getD q zeroE := by simp [wsDigits]
    have e2 : scaleE wsSecondDigit s = Model.scaleNat s 256 := by
      unfold Model.scaleNat
      rw [second_digit]
    rw [e1, wsDigits_value hρ n _ q (by omega), e2, hρ.scaleNat, pow_succ]
    push_cast
    ring

/-- The factors 1 - X b for the column bits from ncb on, at a point that spells C below 2^lk: their
product is 1 if C is below 2^ncb, and 0 otherwise. -/
theorem tail_bits {lk ncb C : ℕ} (hC : C < 2 ^ lk) (X : ℕ → E)
    (hX : ∀ b, b < lk → X b = if C.testBit b then oneE else zeroE) :
    ∏ i ∈ range (lk - ncb), (1 - ρ.val (X (ncb + i))) = if C < 2 ^ ncb then 1 else 0 := by
  by_cases h : C < 2 ^ ncb
  · rw [if_pos h]
    refine prod_eq_one fun i hi => ?_
    have hi' := mem_range.mp hi
    have hb : C.testBit (ncb + i) = false :=
      Nat.testBit_lt_two_pow (lt_of_lt_of_le h (Nat.pow_le_pow_right (by norm_num) (by omega)))
    rw [hX _ (by omega), hb]
    simp [ρ.zero]
  · rw [if_neg h]
    obtain ⟨j, hj1, hj2⟩ : ∃ j, ncb ≤ j ∧ C.testBit j = true := by
      by_contra hn
      refine h (Nat.lt_pow_two_of_testBit C fun i hi => ?_)
      cases hb : C.testBit i
      · rfl
      · exact absurd ⟨i, hi, hb⟩ hn
    have hjl : j < lk := by
      by_contra hge
      have h2 := Nat.testBit_lt_two_pow
        (lt_of_lt_of_le hC (Nat.pow_le_pow_right (by norm_num) (by omega : lk ≤ j)))
      rw [h2] at hj2
      cases hj2
    refine prod_eq_zero (mem_range.mpr (show j - ncb < lk - ncb by omega)) ?_
    rw [show ncb + (j - ncb) = j by omega, hX j hjl, hj2]
    simp [ρ.one]

/-- wsEpsT reads as the product of the factors' values on their column bits, times 1 - X b for each
column bit b that no group of the unit takes. -/
theorem wsEpsT_value {lay : WsLay} {c : WsClaim} {u : WsUnit} (hu : lay.U[c.ui]? = some u)
    (rm : Array E) :
    ρ.val (wsEpsT lay c rm) =
      ((c.f.zip u.g).map fun y =>
        ρ.val (y.1.onColumns y.2 fun b => rm.getD (lay.lk - 1 - b) zeroE)).prod *
      ∏ i ∈ range (lay.lk - u.ncb), (1 - ρ.val (rm.getD (lay.lk - 1 - (u.ncb + i)) zeroE)) := by
  unfold wsEpsT
  rw [hu]
  show ρ.val ((List.range (lay.lk - u.ncb)).foldl
    (fun p i => mulE p (subE oneE (rm.getD (lay.lk - 1 - (u.ncb + i)) zeroE)))
    ((c.f.zip u.g).foldl
      (fun p y => mulE p (y.1.onColumns y.2 fun b => rm.getD (lay.lk - 1 - b) zeroE)) oneE)) = _
  rw [foldl_mul_range, foldl_mul_list, ρ.one, one_mul]
  congr 1
  exact prod_congr rfl fun i _ => by rw [ρ.sub, ρ.one]

/-- What passing wsClaimShape says. -/
theorem shape_of_claim {lay : WsLay} {c : WsClaim} {u : WsUnit} (hu : lay.U[c.ui]? = some u)
    (hs : wsClaimShape lay c = .ok ()) :
    c.f.length = u.g.length ∧ ∀ y ∈ c.f.zip u.g, y.1.fits y.2 = true := by
  unfold wsClaimShape at hs
  rw [hu] at hs
  have hs2 : (if (c.f.length == u.g.length && ((c.f.zip u.g).all fun y => y.1.fits y.2)) = true
      then (pure () : Except String Unit) else throw "internal-claim-factors") = .ok () := hs
  by_cases hc : (c.f.length == u.g.length && ((c.f.zip u.g).all fun y => y.1.fits y.2)) = true
  · simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at hc
    exact hc
  · rw [if_neg hc] at hs2
    cases hs2

variable {ρ} in
/-- What the verifier's settling of a claim is worth on the matrix W. For a claim that passes
wsClaimShape, on a unit as the layout leaves it: the sum, over all columns C of W and all rows y of
the unit, of the claim's coefficient on the row (wsGamma of what wsRowPart leaves, under the scalars
ka and wgt), times the value of the claim's factors on the columns at the point that spells C
(wsEpsT), times the entry of W in row u.off + y and column C, is wgt ka times the sum that the claim
speaks of (claimVal). -/
theorem claim_cells (hρ : Numerals ρ) {lay : WsLay} {c : WsClaim} {u : WsUnit}
    (hu : lay.U[c.ui]? = some u) (hs : wsClaimShape lay c = .ok ()) (U : UnitOK lay.lk u)
    (W : Wm K) (ka wgt : E) :
    ∑ C ∈ range (2 ^ lay.lk), ∑ y ∈ range u.rows,
      ρ.val ((wsGamma u (wsRowPart lay c ka) wgt).getD y zeroE) *
        ρ.val (wsEpsT lay c (bitsOf lay.lk C)) * W (u.off + y) C =
      ρ.val wgt * ρ.val ka * claimVal ρ lay W c := by
  obtain ⟨hlen, hfits⟩ := shape_of_claim hu hs
  have hmap : (c.f.zip u.g).map (·.2) = u.g := List.map_snd_zip (by omega)
  have hok : ∀ y ∈ c.f.zip u.g, GrpOK y.2 ∧ y.1.fits y.2 = true := fun y hy =>
    ⟨U.grp y.2 (by
      have h1 : y.2 ∈ (c.f.zip u.g).map (·.2) := List.mem_map_of_mem hy
      rw [hmap] at h1
      exact h1), hfits y hy⟩
  have htsum : ((c.f.zip u.g).map (·.2.t)).sum = u.ncb := by
    have h1 : (((c.f.zip u.g).map (·.2)).map (·.t)).sum = (u.g.map (·.t)).sum := by rw [hmap]
    rw [U.ncb, ← h1, List.map_map]
    rfl
  have hleft : ((c.f.zip u.g).map (·.2.left)).prod = (u.g.map (·.left)).prod := by
    have h1 : (((c.f.zip u.g).map (·.2)).map (·.left)).prod = (u.g.map (·.left)).prod := by
      rw [hmap]
    rw [← h1, List.map_map]
    rfl
  have hds : (wsDigits u.nlw (mulE wgt ka)).toArray.size = u.nlw := by
    simp [wsDigits_length]
  have hgs : (gamOf (c.f.zip u.g) (wsDigits u.nlw (mulE wgt ka)).toArray).size = u.rows := by
    rw [gamOf_size _ hok, hds, hleft, U.rows]
  have key := cells_sum ρ lay.lk (fun C b => (bitsOf lay.lk C).getD (lay.lk - 1 - b) zeroE)
    (fun C b hb => bitsOf_at hb) (c.f.zip u.g) 0 hok (by rw [hmap]; exact U.runs)
    (by rw [htsum, Nat.zero_add]; exact U.le) (wsDigits u.nlw (mulE wgt ka)).toArray
    (fun C y => W (u.off + y) C) 0 (by simp)
  rw [htsum, hgs, hds, hmap] at key
  simp only [pow_zero, one_mul, Nat.zero_add] at key
  -- the left side: the columns from 2^ncb on weigh nothing
  have hle2 : 2 ^ u.ncb ≤ 2 ^ lay.lk := Nat.pow_le_pow_right (by norm_num) U.le
  rw [wsGamma_eq hu, ← Finset.sum_subset (range_subset_range.mpr hle2)]
  · -- the right side
    have hR : ρ.val wgt * ρ.val ka * claimVal ρ lay W c =
        sumIdx ρ (c.f.zip u.g) fun idx => ∑ q ∈ range u.nlw,
          ρ.val ((wsDigits u.nlw (mulE wgt ka)).toArray.getD q zeroE) *
            W (u.off + rowIn (u.g.zip idx) q) (colRel (u.g.zip idx)) := by
      unfold claimVal
      rw [hu]
      show ρ.val wgt * ρ.val ka * sumIdx ρ (c.f.zip u.g) (wgtOf u W) = _
      rw [← sumIdx_mul]
      congr 1
      funext idx
      unfold wgtOf cellOf
      rw [Finset.mul_sum]
      refine sum_congr rfl fun q hq => ?_
      have h0 := colIn_rel u.g 0 U.runs idx
      rw [pow_zero, one_mul] at h0
      rw [toArray_getD, wsDigits_value hρ _ _ _ (mem_range.mp hq), ρ.mul]
      show _ * (_ * W (u.off + rowIn (u.g.zip idx) q) (colIn (u.g.zip idx))) = _
      rw [h0]
      ring
    rw [hR, ← key]
    refine sum_congr rfl fun C hC => sum_congr rfl fun y _ => ?_
    have hC' : C < 2 ^ u.ncb := mem_range.mp hC
    rw [wsEpsT_value ρ hu, tail_bits ρ (lt_of_lt_of_le hC' hle2)
      (fun b => (bitsOf lay.lk C).getD (lay.lk - 1 - b) zeroE) (fun b hb => bitsOf_at hb),
      if_pos hC']
    ring
  · intro C hC hC2
    have hC' : C < 2 ^ lay.lk := mem_range.mp hC
    have hn : ¬ C < 2 ^ u.ncb := fun h => hC2 (mem_range.mpr h)
    refine sum_eq_zero fun y _ => ?_
    rw [wsEpsT_value ρ hu, tail_bits ρ hC'
      (fun b => (bitsOf lay.lk C).getD (lay.lk - 1 - b) zeroE) (fun b hb => bitsOf_at hb),
      if_neg hn]
    ring

variable {ρ} in
/-- The same on a layout that the verifier builds: the unit's properties follow from "wsLayOf
returns" (unitOK_of_layout, Johnson/Road/FormsKeysWLay.lean). -/
theorem claim_cells_layout (hρ : Numerals ρ) {s : WsShape} {p3 : Bool} {lk : ℕ} {lay : WsLay}
    (hl : wsLayOf s p3 lk = .ok lay) {c : WsClaim} {u : WsUnit} (hu : lay.U[c.ui]? = some u)
    (hs : wsClaimShape lay c = .ok ()) (W : Wm K) (ka wgt : E) :
    ∑ C ∈ range (2 ^ lay.lk), ∑ y ∈ range u.rows,
      ρ.val ((wsGamma u (wsRowPart lay c ka) wgt).getD y zeroE) *
        ρ.val (wsEpsT lay c (bitsOf lay.lk C)) * W (u.off + y) C =
      ρ.val wgt * ρ.val ka * claimVal ρ lay W c := by
  obtain ⟨hlk, hU⟩ := unitOK_of_layout hl
  have hm : u ∈ lay.U := Array.mem_of_getElem? hu
  exact claim_cells hρ hu hs (by rw [hlk]; exact (hU u hm).1) W ka wgt

end Claim

#print axioms onColumns_at
#print axioms table_at
#print axioms fac_split
#print axioms splitG_inj
#print axioms split_onto
#print axioms fac_sum
#print axioms cells_sum
#print axioms claim_cells
#print axioms claim_cells_layout

end OnBytes.Road
