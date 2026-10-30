-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/C/Weights.lean: CONDITIONAL.

Not shown here. That the honest side's list of points is a part of the verifier's (PtsPart), and
that the verifier's function phiOf returns: hypotheses. Nothing on places or on cells. No example
is known. No property is claimed.

THE HONEST SIDE's WEIGHTS OF A FAMILY OF TABLES ARE THE VERIFIER's, IN BOTH CASES. The honest side
of the sub-protocol K4 takes a family's weights from the verifier's own function, or, where the
token coordinates of the family's point are zeros and ones, lists the few rows that have a weight
(wtsOf, fewOf: Johnson/Desc/K4/Honest/Cells.lean). Here: wherever its test wtsFit is true, the sum
that it makes of any words under its weights is, read in the field, the sum under the verifier's
weights (phiOf, OnBytes/Model/Layer.lean).

  Named, AskOk, ask_ok   a family of the verifier's list has no named point, or no name of the three
                 on the matrix of the lookup's planes.
  phiOf_at       the verifier's weights of a family with NONE of the three names (Named), at a point
                 that is found.
  phiOf_fo       these weights do not read what the lookup has sampled.
  phiOf_part     what phiOf returns at a part of a list it returns at the list.
  length_flatMap_const, blockRows_size, longPhi_size   sizes.
  sum_few, sum_zipIdx   two sums over lists.
  few_sum        the sum over the few rows.
  corner_long, corner_short   the sum under the verifier's weights at such a point.
  entrySum, fewAt, entrySum_few, entrySum_whole, whole_sum   the sum that the honest side makes,
                 in either case.
  entry_sum      it is the sum under the verifier's weights.
-/
import Johnson.Road.K4.C.Cells
import Johnson.Road.K4.C.Fold
import Johnson.Road.K4.C.Corner
import Johnson.Road.FormsKeysPoint
import OnBytes.Tie.Pv.Lookup.Ends.FoReadsLayer

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Road.K4.C
open Finset
open OnBytes OnBytes.Model OnBytes.Road
open OnBytes.Model.Layer (Lay Reads TableAsk tableAsks phiOf)
open OnBytes.Desc.First.K4.Honest (cornerOf fewOf wtsOf wtsFit)

/-- The family's name is NONE of the three on the matrix of the lookup's planes ("b-bits-0",
"b-bits-1", "b-pin"). -/
def Named (a : TableAsk) : Prop :=
  (a.name == "b-bits-0") = false ∧ (a.name == "b-bits-1") = false ∧ (a.name == "b-pin") = false

/-- The family has no named point, or no name of these three. -/
def AskOk (a : TableAsk) : Prop := a.point.isEmpty = true ∨ Named a

/-- Every family of the verifier's list is so. -/
theorem ask_ok {y : Lay} {rd : Reads} {g : ℕ} {a : TableAsk} (h : a ∈ tableAsks y rd g) :
    AskOk a := by
  rw [Fo.tableAsks_eq] at h
  rcases List.mem_append.mp h with h | h
  · exact Or.inr ⟨beq_eq_false_iff_ne.mpr (Fo.ask_ne h _ (by decide)),
      beq_eq_false_iff_ne.mpr (Fo.ask_ne h _ (by decide)),
      beq_eq_false_iff_ne.mpr (Fo.ask_ne h _ (by decide))⟩
  · left
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl <;> rfl

/-- The verifier's weights of a family with none of the three names, at a point that is found. -/
theorem phiOf_at {y : Lay} {fo : Forest.Heard} {pts : List (String × Array E)} {a : TableAsk}
    (hn : Named a) {p : String × Array E} (hf : (pts.find? fun q => q.1 == a.point) = some p)
    (hs : p.2.size = if a.lng then y.h.la else y.h.lt) :
    phiOf y fo pts a = some (if a.lng then longPhi p.2 y.ls y.h.lt else eqTab p.2) := by
  unfold phiOf
  rw [hn.1, hn.2.1, hn.2.2, hf]
  simp [hs]

/-- The weights of a family with none of the three names do not read what the lookup has sampled.
-/
theorem phiOf_fo {y : Lay} (fo fo' : Forest.Heard) {pts : List (String × Array E)} {a : TableAsk}
    (hn : Named a) : phiOf y fo pts a = phiOf y fo' pts a := by
  unfold phiOf
  rw [hn.1, hn.2.1, hn.2.2]
  rfl

/-- What phiOf returns at a part of a list it returns at the list. -/
theorem phiOf_part {y : Lay} {fo : Forest.Heard} {pt pts : List (String × Array E)}
    (hp : PtsPart pt pts) {a : TableAsk} {phi : Array E} (h : phiOf y fo pt a = some phi) :
    phiOf y fo pts a = some phi := by
  unfold phiOf at h ⊢
  by_cases c0 : (a.name == "b-bits-0") = true
  · rw [if_pos c0] at h ⊢
    exact h
  rw [if_neg c0] at h ⊢
  by_cases c1 : (a.name == "b-bits-1") = true
  · rw [if_pos c1] at h ⊢
    exact h
  rw [if_neg c1] at h ⊢
  by_cases c2 : (a.name == "b-pin") = true
  · rw [if_pos c2] at h ⊢
    exact h
  rw [if_neg c2] at h ⊢
  cases hq : (pt.find? fun q => q.1 == a.point) with
  | none =>
    rw [hq] at h
    cases h
  | some q =>
    rw [hq] at h
    rw [hp _ _ hq]
    exact h

/-! ## Sizes -/

/-- The length of a list that is made of one list of n members for each member of l. -/
theorem length_flatMap_const {α β : Type} (g : α → List β) (n : ℕ) : ∀ l : List α,
    (∀ a ∈ l, (g a).length = n) → (l.flatMap g).length = l.length * n
  | [], _ => by simp
  | x :: l, h => by
    rw [List.flatMap_cons, List.length_append, h x List.mem_cons_self,
      length_flatMap_const g n l fun a ha => h a (List.mem_cons_of_mem _ ha), List.length_cons,
      Nat.succ_mul, Nat.add_comm]

/-- A block's weights are as many as the two tables' sizes multiplied. -/
theorem blockRows_size (low tok : Array E) : (blockRows low tok).size = low.size * tok.size := by
  have h1 : (blockRows low tok).toList =
      low.toList.flatMap fun a => tok.toList.map fun b => mulE a b := by
    simp [blockRows, Array.toList_flatMap]
  rw [← Array.length_toList, h1,
    length_flatMap_const _ tok.size low.toList (by intro a _; simp), Array.length_toList]

/-- A long table's weights at a point of ls + lt coordinates. -/
theorem longPhi_size {p : Array E} {ls lt : ℕ} (hs : p.size = ls + lt) :
    (longPhi p ls lt).size = 2 ^ (ls + lt) := by
  unfold longPhi
  rw [blockRows_size, eqTab_size, eqTab_size, Array.size_extract, Array.size_extract, pow_add]
  congr 2 <;> omega

/-! ## Two sums over lists -/

/-- The rows that are left out have the weight 0. -/
theorem sum_few (lt t : ℕ) (Y : ℕ → Cb.Gl.E) : ∀ l : List (E × ℕ),
    ((l.filterMap fun x => if x.1 == zeroE then none else some (x.2 * 2 ^ lt + t, x.1)).map
      fun y => Y y.1 * Reading.gl.val y.2).sum =
      (l.map fun x => Y (x.2 * 2 ^ lt + t) * Reading.gl.val x.1).sum
  | [] => rfl
  | x :: l => by
    by_cases c : (x.1 == zeroE) = true
    · rw [List.filterMap_cons_none (by rw [if_pos c]), sum_few lt t Y l, List.map_cons,
        List.sum_cons, eq_of_beq c, Reading.gl.zero, mul_zero, zero_add]
    · rw [List.filterMap_cons_some (b := (x.2 * 2 ^ lt + t, x.1)) (by rw [if_neg c]),
        List.map_cons, List.sum_cons, sum_few lt t Y l, List.map_cons, List.sum_cons]

/-- A sum over a list with its members' numbers. -/
theorem sum_zipIdx (Y : ℕ → Cb.Gl.E) : ∀ (l : List E) (k : ℕ),
    ((l.zipIdx k).map fun x => Y x.2 * Reading.gl.val x.1).sum =
      ∑ r ∈ range l.length, Y (k + r) * Reading.gl.val (l.getD r zeroE)
  | [], _ => by simp
  | a :: l, k => by
    rw [List.zipIdx_cons, List.map_cons, List.sum_cons, sum_zipIdx Y l (k + 1), List.length_cons,
      Finset.sum_range_succ', List.getD_cons_zero, Nat.add_zero, add_comm]
    congr 1
    refine sum_congr rfl fun r _ => ?_
    rw [List.getD_cons_succ, show k + 1 + r = k + (r + 1) by omega]

/-- **The sum over the few rows.** -/
theorem few_sum {lng : Bool} {ls lt : ℕ} {p : Array E} {rows : Array (ℕ × E)}
    (h : fewOf lng ls lt p = some rows) (X : ℕ → F) :
    ∃ t, cornerOf (p.extract (if lng then ls else 0) ((if lng then ls else 0) + lt)) = some t ∧
      Reading.gl.val (rows.foldl (fun s x => maddS s (X x.1) x.2) zeroE) =
        ∑ r ∈ range (eqTab (p.extract 0 (if lng then ls else 0))).size,
          Reading.gl.val (ofF (X (r * 2 ^ lt + t))) *
            Reading.gl.val ((eqTab (p.extract 0 (if lng then ls else 0))).getD r zeroE) := by
  unfold fewOf at h
  obtain ⟨t, ht, rfl⟩ := Option.map_eq_some_iff.mp h
  refine ⟨t, ht, ?_⟩
  rw [← Array.foldl_toList, List.toList_toArray,
    gl_foldl_maddS (fun x : ℕ × E => X x.1) (fun x => x.2), Reading.gl.zero, zero_add,
    sum_few lt t (fun i => Reading.gl.val (ofF (X i))),
    sum_zipIdx (fun r => Reading.gl.val (ofF (X (r * 2 ^ lt + t)))), Array.length_toList]
  refine sum_congr rfl fun r _ => ?_
  rw [Nat.zero_add, Array.getD_eq_getD_getElem?, ← Array.getElem?_toList,
    ← List.getD_eq_getElem?_getD]

/-! ## The verifier's weights at a point whose token coordinates are zeros and ones -/

/-- A long table. -/
theorem corner_long {p : Array E} {ls lt t : ℕ} (hs : p.size = ls + lt)
    (ht : cornerOf (p.extract ls (ls + lt)) = some t) (Y : ℕ → Cb.Gl.E) :
    ∑ j ∈ range (2 ^ (ls + lt)), Reading.gl.val ((longPhi p ls lt).getD j zeroE) * Y j =
      ∑ r ∈ range (eqTab (p.extract 0 ls)).size,
        Y (r * 2 ^ lt + t) * Reading.gl.val ((eqTab (p.extract 0 ls)).getD r zeroE) := by
  have s1 : (p.extract 0 ls).size = ls := by
    rw [Array.size_extract]
    omega
  have s2 : (p.extract ls (ls + lt)).size = lt := by
    rw [Array.size_extract]
    omega
  have t1 := eqTab_size (p.extract 0 ls)
  have t2 := eqTab_size (p.extract ls (ls + lt))
  rw [s1] at t1
  rw [s2] at t2
  have htl := (corner_pt ht).1
  rw [s2] at htl
  rw [pow_add, Alg.sum_range_mul_add, t1]
  refine sum_congr rfl fun r hr => ?_
  have hin : ∀ i ∈ range (2 ^ lt),
      Reading.gl.val ((longPhi p ls lt).getD (r * 2 ^ lt + i) zeroE) * Y (r * 2 ^ lt + i) =
        if i = t then Y (r * 2 ^ lt + i) *
          Reading.gl.val ((eqTab (p.extract 0 ls)).getD r zeroE) else 0 := by
    intro i hi
    have e : (longPhi p ls lt).getD (r * 2 ^ lt + i) zeroE =
        mulE ((eqTab (p.extract 0 ls)).getD r zeroE)
          ((eqTab (p.extract ls (ls + lt))).getD i zeroE) := by
      have := blockRows_getD (eqTab (p.extract 0 ls)) (eqTab (p.extract ls (ls + lt)))
        (r := r) (i := i) (by rw [t1]; exact mem_range.mp hr) (by rw [t2]; exact mem_range.mp hi)
      rw [t2] at this
      exact this
    rw [e, Reading.gl.mul, eqTab_corner ht (by rw [s2]; exact mem_range.mp hi)]
    by_cases c : i = t
    · rw [if_pos c, if_pos c]
      ring
    · rw [if_neg c, if_neg c]
      ring
  rw [sum_congr rfl hin, Finset.sum_ite_eq', if_pos (mem_range.mpr htl)]

/-- A short table. -/
theorem corner_short {p : Array E} {lt t : ℕ} (hs : p.size = lt)
    (ht : cornerOf (p.extract 0 (0 + lt)) = some t) (Y : ℕ → Cb.Gl.E) :
    ∑ j ∈ range (2 ^ lt), Reading.gl.val ((eqTab p).getD j zeroE) * Y j =
      ∑ r ∈ range (eqTab (p.extract 0 0)).size,
        Y (r * 2 ^ lt + t) * Reading.gl.val ((eqTab (p.extract 0 0)).getD r zeroE) := by
  have e1 : p.extract 0 (0 + lt) = p := by rw [Nat.zero_add, ← hs, Array.extract_size]
  rw [e1] at ht
  have e0 : p.extract 0 0 = #[] := by simp
  have e2 : eqTab (#[] : Array E) = #[oneE] := rfl
  have htl := (corner_pt ht).1
  rw [hs] at htl
  have hin : ∀ i ∈ range (2 ^ lt), Reading.gl.val ((eqTab p).getD i zeroE) * Y i =
      if i = t then Y i else 0 := by
    intro i hi
    rw [eqTab_corner ht (by rw [hs]; exact mem_range.mp hi)]
    by_cases c : i = t
    · rw [if_pos c, if_pos c, one_mul]
    · rw [if_neg c, if_neg c, zero_mul]
  rw [sum_congr rfl hin, Finset.sum_ite_eq', if_pos (mem_range.mpr htl), e0, e2]
  show Y t = ∑ r ∈ range 1, Y (r * 2 ^ lt + t) * Reading.gl.val ((#[oneE] : Array E).getD r zeroE)
  rw [Finset.sum_range_one, Nat.zero_mul, Nat.zero_add]
  show Y t = Y t * Reading.gl.val oneE
  rw [Reading.gl.one, mul_one]

/-! ## The sum that the honest side makes -/

/-- The sum of the words X r under a family's weights, in either case: famEntry's text
(Johnson/Desc/K4/Honest/Cells.lean). L: the number of rows of a run. -/
def entrySum (L : ℕ) (wts : OnBytes.Desc.First.K4.Honest.Wts) (X : ℕ → F) : E :=
  match wts with
  | .few rows => rows.foldl (fun s x => maddS s (X x.1) x.2) zeroE
  | .whole phi =>
    match phi.get with
    | none => zeroE
    | some phi => (List.range L).foldl (fun s r => maddS s (X r) (phi.getD r zeroE)) zeroE

/-- The few rows, where wtsOf lists them. -/
def fewAt (y : Lay) (pt : List (String × Array E)) (a : TableAsk) : Option (Array (ℕ × E)) :=
  if a.point.isEmpty then none
  else (pt.find? fun p => p.1 == a.point).bind fun p =>
    if p.2.size == (if a.lng then y.h.la else y.h.lt) then fewOf a.lng y.ls y.h.lt p.2 else none

/-- The sum where wtsOf lists the few rows. -/
theorem entrySum_few {y : Lay} {fo : Forest.Heard} {pt : List (String × Array E)} {a : TableAsk}
    {rows : Array (ℕ × E)} (h : fewAt y pt a = some rows) (X : ℕ → F) :
    entrySum a.L (wtsOf y fo pt a) X = rows.foldl (fun s x => maddS s (X x.1) x.2) zeroE := by
  have e : wtsOf y fo pt a = (match fewAt y pt a with
      | some rows => OnBytes.Desc.First.K4.Honest.Wts.few rows
      | none => OnBytes.Desc.First.K4.Honest.Wts.whole (Thunk.mk fun _ =>
          (phiOf y fo pt a).bind fun phi => if phi.size == a.L then some phi else none)) := rfl
  rw [e, h]
  rfl

/-- The sum where wtsOf takes the verifier's own weights. -/
theorem entrySum_whole {y : Lay} {fo : Forest.Heard} {pt : List (String × Array E)} {a : TableAsk}
    {phi : Array E} (h : fewAt y pt a = none) (hphi : phiOf y fo pt a = some phi)
    (hs : phi.size = a.L) (X : ℕ → F) :
    entrySum a.L (wtsOf y fo pt a) X =
      (List.range a.L).foldl (fun s r => maddS s (X r) (phi.getD r zeroE)) zeroE := by
  have e : wtsOf y fo pt a = (match fewAt y pt a with
      | some rows => OnBytes.Desc.First.K4.Honest.Wts.few rows
      | none => OnBytes.Desc.First.K4.Honest.Wts.whole (Thunk.mk fun _ =>
          (phiOf y fo pt a).bind fun phi => if phi.size == a.L then some phi else none)) := rfl
  rw [e, h]
  show (match (phiOf y fo pt a).bind fun phi => if phi.size == a.L then some phi else none with
    | none => zeroE
    | some phi => (List.range a.L).foldl (fun s r => maddS s (X r) (phi.getD r zeroE)) zeroE) = _
  rw [hphi]
  show (match (if (phi.size == a.L) = true then some phi else none) with
    | none => zeroE
    | some phi => (List.range a.L).foldl (fun s r => maddS s (X r) (phi.getD r zeroE)) zeroE) = _
  rw [if_pos (by rw [hs]; exact beq_self_eq_true _)]

/-- The whole weights' loop, read in the field. -/
theorem whole_sum (L : ℕ) (phi : Array E) (X : ℕ → F) :
    Reading.gl.val ((List.range L).foldl (fun s r => maddS s (X r) (phi.getD r zeroE)) zeroE) =
      ∑ j ∈ range L, Reading.gl.val (phi.getD j zeroE) * Reading.gl.val (ofF (X j)) := by
  rw [gl_foldl_maddS (fun r => X r) (fun r => phi.getD r zeroE), Reading.gl.zero, zero_add,
    list_range_sum]
  exact sum_congr rfl fun j _ => mul_comm _ _

/-- **The sum that the honest side makes is the sum under the verifier's weights.** -/
theorem entry_sum {y : Lay} {fo : Forest.Heard} {pt pts : List (String × Array E)} {a : TableAsk}
    {phi : Array E} (hok : AskOk a) (hfit : wtsFit y fo pt a = true)
    (hphi : phiOf y fo pts a = some phi) (hp : PtsPart pt pts) (X : ℕ → F) :
    Reading.gl.val (entrySum a.L (wtsOf y fo pt a) X) =
      ∑ j ∈ range a.L, Reading.gl.val (phi.getD j zeroE) * Reading.gl.val (ofF (X j)) := by
  unfold wtsFit at hfit
  by_cases he : a.point.isEmpty = true
  · rw [if_pos he] at hfit
    have hfew : fewAt y pt a = none := by
      unfold fewAt
      rw [if_pos he]
    cases hq : phiOf y fo pt a with
    | none =>
      rw [hq] at hfit
      cases hfit
    | some phi0 =>
      rw [hq] at hfit
      have hs : phi0.size = a.L := eq_of_beq hfit
      obtain rfl : phi0 = phi := Option.some.inj ((phiOf_part hp hq).symm.trans hphi)
      rw [entrySum_whole hfew hq hs, whole_sum]
  · rw [if_neg he] at hfit
    have hn : Named a := hok.resolve_left he
    cases hq : (pt.find? fun p => p.1 == a.point) with
    | none =>
      rw [hq] at hfit
      cases hfit
    | some p =>
      rw [hq] at hfit
      have hfit' : (if a.lng = true then
          p.2.size == y.h.la && y.ls + y.h.lt == y.h.la && a.L == 2 ^ y.h.la
          else p.2.size == y.h.lt && a.L == 2 ^ y.h.lt) = true := hfit
      cases hl : a.lng with
      | true =>
        rw [hl, if_pos rfl] at hfit'
        simp only [Bool.and_eq_true, beq_iff_eq] at hfit'
        obtain ⟨⟨z1, z2⟩, z3⟩ := hfit'
        have hz : p.2.size = y.ls + y.h.lt := by omega
        have hph : phiOf y fo pt a = some (longPhi p.2 y.ls y.h.lt) := by
          rw [phiOf_at hn hq (by rw [hl, if_pos rfl]; exact z1), hl, if_pos rfl]
        obtain rfl : longPhi p.2 y.ls y.h.lt = phi :=
          Option.some.inj ((phiOf_part hp hph).symm.trans hphi)
        have hfa : fewAt y pt a = fewOf true y.ls y.h.lt p.2 := by
          unfold fewAt
          rw [if_neg he, hq, hl]
          show (if (p.2.size == (if true = true then y.h.la else y.h.lt)) = true then _ else _) = _
          rw [if_pos rfl, if_pos (by rw [z1]; exact beq_self_eq_true _)]
        cases hw : fewOf true y.ls y.h.lt p.2 with
        | none =>
          rw [entrySum_whole (hfa.trans hw) hph (by rw [longPhi_size hz, z2, z3]), whole_sum]
        | some rows =>
          obtain ⟨t, ht, e⟩ := few_sum hw X
          rw [if_pos rfl] at ht e
          rw [entrySum_few (hfa.trans hw), e, z3, ← z2,
            corner_long hz ht fun j => Reading.gl.val (ofF (X j))]
      | false =>
        rw [hl, if_neg Bool.false_ne_true] at hfit'
        simp only [Bool.and_eq_true, beq_iff_eq] at hfit'
        obtain ⟨z1, z3⟩ := hfit'
        have hph : phiOf y fo pt a = some (eqTab p.2) := by
          rw [phiOf_at hn hq (by rw [hl, if_neg Bool.false_ne_true]; exact z1), hl,
            if_neg Bool.false_ne_true]
        obtain rfl : eqTab p.2 = phi := Option.some.inj ((phiOf_part hp hph).symm.trans hphi)
        have hfa : fewAt y pt a = fewOf false y.ls y.h.lt p.2 := by
          unfold fewAt
          rw [if_neg he, hq, hl]
          show (if (p.2.size == (if false = true then y.h.la else y.h.lt)) = true then _ else _) = _
          rw [if_neg Bool.false_ne_true, if_pos (by rw [z1]; exact beq_self_eq_true _)]
        cases hw : fewOf false y.ls y.h.lt p.2 with
        | none =>
          rw [entrySum_whole (hfa.trans hw) hph (by rw [eqTab_size, z1, z3]), whole_sum]
        | some rows =>
          obtain ⟨t, ht, e⟩ := few_sum hw X
          rw [if_neg Bool.false_ne_true] at ht e
          rw [entrySum_few (hfa.trans hw), e, z3,
            corner_short z1 ht fun j => Reading.gl.val (ofF (X j))]

end OnBytes.Road.K4.C

#print axioms OnBytes.Road.K4.C.ask_ok
#print axioms OnBytes.Road.K4.C.phiOf_at
#print axioms OnBytes.Road.K4.C.phiOf_fo
#print axioms OnBytes.Road.K4.C.phiOf_part
#print axioms OnBytes.Road.K4.C.length_flatMap_const
#print axioms OnBytes.Road.K4.C.blockRows_size
#print axioms OnBytes.Road.K4.C.longPhi_size
#print axioms OnBytes.Road.K4.C.sum_few
#print axioms OnBytes.Road.K4.C.sum_zipIdx
#print axioms OnBytes.Road.K4.C.few_sum
#print axioms OnBytes.Road.K4.C.corner_long
#print axioms OnBytes.Road.K4.C.corner_short
#print axioms OnBytes.Road.K4.C.entrySum_few
#print axioms OnBytes.Road.K4.C.entrySum_whole
#print axioms OnBytes.Road.K4.C.whole_sum
#print axioms OnBytes.Road.K4.C.entry_sum
