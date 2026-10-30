-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Road/FormsKeysRun8.lean: the verifier's placement of a lookup call's segments beside the
library's index map, run at the library's eight calls on made-up numbers; and what the verifier's
marks of a call's columns say, as theorems.

Two parts, of two kinds of evidence.

Part 1 is a run. A line "#guard" is evaluated when this file is compiled, by Lean's interpreter, and
the compilation fails if the value is not true. It is no theorem: nothing that only a guard shows
can be used in a proof, and it says nothing of other numbers.
Compared, the verifier's function with the library's object, at the shape hR8 (the shape hR of
Johnson/Road/FormsKeysRun.lean with the numbers of trees that eight calls have), the eight lines of
calls pcR8 and the library's sizes dimOf hR8:
 1. the written lines pcR8 name the segments of the library's calls (fams), in its order; the kinds
    of tables in these lines are written after the library's lut by reading; no guard compares the
    words, but point 10 compares the tables that the kinds select with the library's, row by row,
 2. layout returns, and call c of the layout has the names (fams c).map segName,
 3. for every family s and every x below its length, the column that the layout's segment lists
    for its entry x is the library's pos s x,
 4. for every call the logarithm of the number of columns is the library's lJ; here the least
    number of columns that the shape asks for, 2^4, is below every call's own number,
 5. for every call, layer of a group and column: the verifier's rule CallD.padding says what the
    library's isPad says, and weighedOf marks the column exactly if isPad is false,
 6. a control, the shape hR8c, which asks for at least 2^6 columns: layout returns, points 2, 3 and
    5 hold (5 for all columns of the verifier's call), and in the calls 6 and 7 the verifier has
    2^6 columns where the library has 2^5 (floorR8 is false for these two calls alone),
 7. the placement alone (place, without a layout) at five made-up sets of sizes, among them lengths
    that are no powers of two, lengths 1 and lengths 0: points 2 to 5 without the marks.
Run besides, in the verifier's own words, in both groups of layers of hR8 and of hR8c:
 8. with a point for each call that is made from one point inside a tree and one over the trees'
    numbers as the lookup makes it (lookR8), the tests on the calls' points pass that the theorem
    joinPart_of_run (Johnson/Road/FormsKeysPoint.lean) has as its hypotheses
    hZ, hzt, hm, ha, hpt, and line, weighedOf and joinPart return for every call at these points,
 9. pointsOf returns 10 points and funsOf a table for each part of each family, the hypotheses hp
    and hfun of tables_of_run in the same file.
Compared besides, the verifier's tables with the library's, at hR8:
 10. for every call the verifier's padding key, which is row t0 of the table in the call's record,
    is the number (lut tb c).pad of the library, also as a word of the base field (padWordsR8), the
    two tables have equally many rows, and they agree in every row. This is run at two values of
    tb, the library's table functions. tbR8 is written from the verifier's own two tables of the
    gate; there the rows that hang on tb (all of call 6, the lower half of call 5) agree by the way
    tbR8 is written, and only their form is compared. tbRef is the library's reference data; there
    the verifier's computed tables are compared with the library's data, at the step 2^-8 and the
    clamp 4095 of hR8, with the gate's clamp. The padding keys of the calls 0 to 5 and 7 do not
    hang on tb; that of call 6 is the verifier's exactly if tb.SILU (2^15) = 0.

The hypotheses of joinPart_keyVec (Johnson/Road/FormsKeysKV.lean). The guard
on runR8 hR8 runs together, in one environment for each of the two groups and for all eight calls:
hy, hs, hg, hrd, hl, ht; hZ, hzt, hm, ha, hpt with NC = 8; hcq, hq, hq'; hn; hfl; hw; hf at alpha =
5 and theta = 9, with the marks of hw. Theorems: S (switchesR8), Zd at dimOf (sized_dimOf). hpad is
run as an equality of two numbers and of two words of the base field (point 10), not of their
readings in a field; at call 6 it holds exactly if tb.SILU (2^15) = 0, a condition on tb. Not run:
T, the truth of the tables in a world, and hρ.

Part 2 is proved, for any call and any environment; the library is not mentioned in it.
Main definitions: colsOn (the columns that the segments which exist on a layer list), marksOn.
Main theorems: marks_spec (the invariant of marking), weighedOf_eq, weighedOf_spec, weighedOf_apart,
padJ_unlisted. Compared: the verifier's weighedOf and markColumns with colsOn, which this file
defines from the verifier's lists Seg.pos.
The hypotheses. That weighedOf returns marks: met at the numbers of part 1 (point 5), by a run.
That every segment exists on the last layer of the group (hlast): concluded by last_of_layout from
"layout returns" (a run: point 2) and the switches (a theorem: switchesR8). From "weighedOf returns"
alone the statement does not follow: weighedOf tests an index lam J + p against the size Lam J of
the array alone, so a segment that is absent from the last layer could list a column p at or above J
and mark a column of a later layer. The last guard shows such a call, written by hand.
This is no gap of the verifier. No call of a layout that it returns lists such a column: the placing
rule puts every column below J (inside_of_layout, Johnson/Road/FormsKeysTab.lean,
under the switches). That file has the same statement from "every listed
column is below J" (weighedOf_spec'), and the theorem on a layout's calls, callFits_of_layout
(Johnson/Road/FormsKeysKV.lean), goes by it and not by hlast.

What is made up: as in Johnson/Road/FormsKeysRun.lean; also the names of the calls, the sets of
sizes of point 7 and all elements of the field. hR8 is not a shape that the verifier has admitted:
the tests that are not run there are not run here.

What is not claimed. No theorem here compares the verifier's placement or tables with the library's.
Nothing is said of the trees, or of what the forms of the segments are worth. No proof
is made or checked. The program does not import this file.

Files named above that a package may lack. Johnson/Road/FormsKeysPoint.lean,
Johnson/Road/FormsKeysKV.lean and Johnson/Road/FormsKeysTab.lean
are in the library's full tree; a package that is cut to what its front
theorems need may not hold them. Where they lack, what this comment says of their theorems
(joinPart_of_run, tables_of_run, joinPart_keyVec, inside_of_layout, weighedOf_spec',
callFits_of_layout), and with it the paragraph "This is no gap of the verifier", cannot be checked
there.

-/
import Johnson.Road.FormsKeysRun
import Inst.Model.TablesRef

set_option autoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road

open Finset
open OnBytes.Model (Reading Seg CallD place lastOf Level eqTab)
open OnBytes.Model.Layer (Env Lay Shape Scales Reads Heard layout scalesOf scalesHeld readsOf
  tableAsks layTables pointsOf funsOf)
open Inst.Model (Tables tbRef)
open Inst.Model.FFSeg (Dim Fam fams call ord len isExp isPad used lut)

/-! ## The made-up numbers -/

/-- Eight lines of calls: the names of the calls are made up; the kinds and the segments are written
after the library's list of calls. -/
def pcR8 : List (List String) :=
  [["c0", "R16", "G", "U"],
   ["c1", "R16", "N1", "N1H", "N2", "N2H", "O", "D", "V"],
   ["c2", "R16", "QK", "QKH", "XR", "LR", "LT", "DD"],
   ["c3", "R8", "GH", "UH", "OH", "DH", "VH", "ROW", "LH", "SEL", "L3", "G0"],
   ["c4", "FC", "CN1", "CN2", "CQK", "CV", "CLR"],
   ["c5", "FS", "MR", "CG"],
   ["c6", "FL", "F"],
   ["c7", "R16", "UT"]]

/-- The shape hR with the numbers of trees that the eight calls have. The least logarithm of a
call's number of keys is 10, so a call has at least 2^4 columns. -/
def hR8 : Shape := { hR with iota := #[1, 1, 1, 4, 1, 1, 0, 0] }

/-- The same shape with 12 as the least logarithm of a call's number of keys, so that a call has at
least 2^6 columns, and the numbers of trees that follow from it. -/
def hR8c : Shape := { hR with nmin := 12, iota := #[0, 0, 0, 3, 0, 0, 0, 0] }

/-- Sizes of the library with made-up lengths of the families. -/
def dimR (d nq nkv ch f nexp : ℕ) : Dim :=
  let P := (dimOf hR).P
  { dimOf hR with P := { P with d := d, nq := nq, nkv := nkv, ch := ch, f := f, nexp := nexp } }

/-- The verifier's placement of the library's eight calls at the library's lengths, with at least
2^fl columns. -/
def placedR (D : Dim) (fl : ℕ) : Array CallD :=
  ((List.finRange 8).map fun c =>
    place "" "" ((fams c).map fun s => (segName s, len D s, isExp s)) fl).toArray

/-! ## What is compared -/

/-- True if there are eight calls and call c has the segments of the library's call c, by name and
in order. -/
def namesR8 (calls : Array CallD) : Bool :=
  calls.size == 8 && (List.finRange 8).all fun c =>
    (calls[c.val]!.segs.map fun s : Seg => s.name) == (fams c).map segName

/-- True if for every family s the segment at the family's place in its call has the family's name
and length, and lists for every x below the length the column that the library's index map gives. -/
def columnsR8 (D : Dim) (calls : Array CallD) : Bool :=
  famsR.all fun s =>
    let g := calls[(call s).val]!.segs[ord s]!
    g.name == segName s && g.n == len D s && g.pos.size == len D s &&
      (List.range (len D s)).all fun x => g.pos[x]! == Inst.Model.FFSeg.pos D s x

/-- For each call the logarithm of the number of columns: the verifier's, the library's. -/
def logsR8 (D : Dim) (calls : Array CallD) : List (ℕ × ℕ) :=
  (List.finRange 8).map fun c => (calls[c.val]!.lJ, Inst.Model.FFSeg.lJ D c)

/-- For each call: whether the least logarithm of the number of columns that the shape asks for,
nmin - ll - lt, is at most the library's logarithm. -/
def floorR8 (h : Shape) (D : Dim) : List Bool :=
  (List.finRange 8).map fun c => decide (h.nmin - h.ll - h.lt ≤ Nat.clog 2 (used D c))

/-- The library's table functions, written from the verifier's two tables of the gate: SILU is the
verifier's word less 4096, and SIGM at ι is the verifier's word of table FS at ι - 2^14. The three
functions that no table of a layer's lookup reads are 0. -/
def tbR8 (y : Lay) : Tables :=
  ⟨fun ι => (y.silu.getD ι.toNat 0 : ℤ) - 4096, fun ι => (y.fs.getD (ι - 2 ^ 14).toNat 0 : ℤ),
    fun _ => 0, fun _ _ _ => 0, fun _ _ _ => 0⟩

/-- For each call the padding key: the verifier's, which is the row t0 of the table in the call's
record, and the library's. -/
def padKeysR8 (y : Lay) (tb : Tables) : List (ℤ × ℤ) :=
  (List.finRange 8).map fun c =>
    let k := y.cl.getD c.val {}
    (((k.tauAt k.t0).toNat : ℤ), (lut tb c).pad)

/-- True if for every call the library's padding key is not negative and the verifier's padding key,
as a word of the base field, is the residue of the library's. -/
def padWordsR8 (y : Lay) (tb : Tables) : Bool :=
  (List.finRange 8).all fun c =>
    let k := y.cl.getD c.val {}
    decide (0 ≤ (lut tb c).pad) && k.tauAt k.t0 == Model.fOfNat (lut tb c).pad.toNat

/-- For each call: whether the verifier's table has as many rows as the library's, and the number of
rows in which the two tables differ. -/
def tablesR8 (y : Lay) (tb : Tables) : List (Bool × ℕ) :=
  (List.finRange 8).map fun c =>
    let k := y.cl.getD c.val {}
    (2 ^ k.k == (lut tb c).rows,
      ((List.range (lut tb c).rows).filter fun t =>
        ((k.tauAt t).toNat : ℤ) != (lut tb c).row t).length)

/-- The library's word on padding, evaluated once: for each call c, at the place lam J + j, whether
the library calls column j padding in layer lam. J: the number of columns of the verifier's call. -/
def libPadR8 (D : Dim) (Lam : ℕ) (calls : Array CallD) : Array (Array Bool) :=
  ((List.finRange 8).map fun c =>
    let J := calls[c.val]!.J
    (Array.range (Lam * J)).map fun i => isPad D c (i / J) (i % J)).toArray

/-- True if for every call, every one of Lam layers and every column of the verifier's call the
verifier's rule for padding says what the library's says. pad: libPadR8. -/
def paddingR8 (pad : Array (Array Bool)) (Lam : ℕ) (calls : Array CallD) : Bool :=
  (List.range 8).all fun c =>
    let cd := calls[c]!
    cd.J == 2 ^ cd.lJ && (pad[c]!).size == Lam * cd.J &&
      (List.range Lam).all fun lam => (List.range cd.J).all fun j =>
        cd.padding lam j == (pad[c]!)[lam * cd.J + j]!

/-- True if for every call weighedOf returns marks, one for each layer and column, and a column is
marked on a layer exactly if the library does not call it padding there. pad: libPadR8. -/
def marksR8 (pad : Array (Array Bool)) (v : Env) : Bool :=
  (List.range 8).all fun c =>
    match v.weighedOf v.y.calls[c]! with
    | none => false
    | some w => w == (pad[c]!).map (!·)

/-- What the lookup leaves, as far as the points and the tables' weights read it: a point inside a
tree, a point over the trees' numbers, and each call's point made from them as the lookup makes it
(Forest.pad in OnBytes/Model/Look.lean); two points at which the planes are read. -/
def lookR8 (y : Lay) : Model.Forest.Heard :=
  let zx := elemsR 2000 y.fo.dT
  let zy := elemsR 2100 y.fo.rK
  { shape := y.fo, leaves := {}, zx := zx, zy := zy,
    zk := (Array.range y.fo.NC).map fun c =>
      zy.extract (y.fo.rK - y.fo.iota.getD c 0) zy.size ++ zx,
    zb0 := elemsR 2200 (y.fo.kT + y.fo.cK + 5), zb1 := elemsR 2300 (y.fo.kT + y.fo.cK + 5),
    e := elemsR 2400 y.fo.NC, alpha := Model.ofNat 5, theta := Model.ofNat 9 }

/-- What the verifier holds after the messages of the norms and of the two token sumchecks, as far
as the points read it. Each point has the length that hearNorms and hearTerms
(OnBytes/Model/Layer.lean) give it; the slots and the batching powers, which no point reads, are
empty. -/
def heardR8 (y : Lay) (rd : Reads) (g : ℕ) : Heard :=
  let fo := lookR8 y
  { fo := fo, PV := elemsR 2500 y.h.lt,
    ZE := if g == 0 then elemsR 2600 (y.ls + y.h.lt) else #[],
    tkh := if g == 0 then elemsR 2700 (y.lPd - y.ls) else #[],
    ztF := (lastOf fo.zx y.h.lt).toOption.getD #[], sW := 0, gp := #[],
    wpl := { r := elemsR 2800 rd.muV }, sPv := 0, omV := #[], tV := { r := elemsR 2900 y.h.lt },
    tT := some { r := elemsR 3000 y.h.lt } }

/-- The tests on the calls' points, in the verifier's words: the last la coordinates of the
lookup's point are taken, its last lt are the token point, the last la of every call's point are
taken and equal those of the lookup's point, and each of the eight points has the length that the
call's record says. -/
def testsR8 (v : Env) (H : Heard) : Bool :=
  match lastOf H.fo.zx v.y.h.la, lastOf H.fo.zx v.y.h.lt,
    v.zk.mapM (fun z => (lastOf z v.y.h.la).toOption) with
  | .ok Z, .ok zt, some ends =>
    zt == H.ztF && ends.all (· == Z) && v.zk.size == 8 &&
      (List.range 8).all fun c => (v.zk.getD c #[]).size == ((v.y.cl[c]?).map (·.n)).getD 0
  | _, _, _ => false

/-- What is compared at a shape. First, for the layout's calls: namesR8, columnsR8, logsR8, floorR8,
paddingR8. Then for each group of layers: marksR8; testsR8; the two numbers of linesR and joinsR, at
the points of lookR8; the number of points that pointsOf returns and the number of tables that
funsOf returns (0 if it returns none). Refuses where the verifier's functions refuse. -/
def runR8 (h : Shape) : Except String
    ((Bool × Bool × List (ℕ × ℕ) × List Bool × Bool) ×
      List (Bool × Bool × (ℕ × ℕ) × Bool × ℕ × ℕ)) := do
  let y ← layout h pcR8
  let sc ← scalesOf h klR
  scalesHeld h sc
  let rd ← readsOf y
  let D := dimOf h
  let pad := libPadR8 D y.Lam y.calls
  let r ← (List.range y.NGr).mapM fun g =>
    match layTables (matsR y g) (tableAsks y rd g) 0 with
    | none => throw "no tables"
    | some r =>
      let H := heardR8 y rd g
      let v : Env := { y, sc, g, iU3 := 0, K3 := 16, tab := r.1, zk := H.fo.zk }
      let pts := pointsOf y H { r := elemsR 3100 rd.muH } (some { r := elemsR 3200 rd.muH2 })
      let funs := pts.bind fun p => funsOf y H.fo p r.2.1
      pure (marksR8 pad v, testsR8 v H, linesR v, joinsR v,
        (pts.map (·.length)).getD 0, (funs.map (·.size)).getD 0)
  pure ((namesR8 y.calls, columnsR8 D y.calls, logsR8 D y.calls, floorR8 h D,
    paddingR8 pad y.Lam y.calls), r)

/-- The placement alone, at the library's lengths for the sizes D and no least number of columns,
on two layers: namesR8, columnsR8, that the two logarithms are equal for every call, paddingR8. -/
def placeR8 (D : Dim) : Bool :=
  let calls := placedR D 0
  namesR8 calls && columnsR8 D calls && (logsR8 D calls).all (fun p => p.1 == p.2) &&
    paddingR8 (libPadR8 D 2 calls) 2 calls

/-! ## The run -/

/- the written lines are the library's calls -/
#guard (pcR8.map fun l => l.drop 2) == (List.finRange 8).map fun c => (fams c).map segName

/-- The two shapes have the switches and digit forms for which the library has keys. -/
theorem switchesR8 : Switches hR8 ∧ Switches hR8c :=
  ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩,
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩⟩

/- 2 to 5, 8, 9: at least 2^4 columns -/
#guard (match runR8 hR8 with
  | .ok r => r ==
    ((true, true, [(6, 6), (6, 6), (6, 6), (9, 9), (6, 6), (6, 6), (5, 5), (5, 5)],
        [true, true, true, true, true, true, true, true], true),
      [(true, true, (118, 118), true, 10, 28), (true, true, (118, 118), true, 10, 27)])
  | .error _ => false)

/- 6: the control, at least 2^6 columns -/
#guard (match runR8 hR8c with
  | .ok r => r ==
    ((true, true, [(6, 6), (6, 6), (6, 6), (9, 9), (6, 6), (6, 6), (6, 5), (6, 5)],
        [true, true, true, true, true, true, false, false], true),
      [(true, true, (118, 118), true, 10, 28), (true, true, (118, 118), true, 10, 27)])
  | .error _ => false)

/- 7: the placement alone, at lengths that no shape need have -/
#guard [dimR 13 3 2 5 37 6, dimR 1 1 1 1 1 1, dimR 0 0 0 0 0 0, dimR 21 7 1 3 64 3,
    dimR 31 2 1 9 33 5].all placeR8

/- 10: the padding keys and the tables -/
#guard (match layout hR8 pcR8 with
  | .ok y =>
    let keys : List (ℤ × ℤ) :=
      ([0, 0, 0, 0, 2 ^ 15 + 2 ^ 39, 2 ^ 15 + 2 ^ 28 + 2 ^ 40, 2 ^ 15 + 2 ^ 40, 0] : List ℤ).map
        fun k => (k, k)
    padKeysR8 y (tbR8 y) == keys && padKeysR8 y tbRef == keys &&
      padWordsR8 y (tbR8 y) && padWordsR8 y tbRef &&
      tablesR8 y (tbR8 y) == List.replicate 8 (true, 0) &&
      tablesR8 y tbRef == List.replicate 8 (true, 0)
  | .error _ => false)

/-! ## Marking: the invariant -/

/-- One step of markColumns, at the index i of the array of marks: refuses an index that is marked
already or lies outside the array, else marks it. -/
def markAt (w : Array Bool) (i : ℕ) : Option (Array Bool) :=
  if w.getD i true then none else some (w.setIfInBounds i true)

/-- After the index i has been marked, the marked indices are the earlier ones and i. An index
outside the array counts as marked. -/
theorem getD_marked (w : Array Bool) (i k : ℕ) :
    (w.setIfInBounds i true).getD k true = true ↔ w.getD k true = true ∨ k = i := by
  rw [Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?, Array.getElem?_setIfInBounds]
  by_cases h : i = k
  · subst h
    by_cases h2 : i < w.size
    · simp [h2]
    · simp [h2]
  · rw [if_neg h]
    constructor
    · exact Or.inl
    · rintro (h1 | h1)
      · exact h1
      · exact absurd h1.symm h

/-- An index that does not count as marked lies inside the array. -/
theorem lt_of_unmarked {w : Array Bool} {i : ℕ} (h : w.getD i true = false) : i < w.size := by
  by_contra hn
  have e : w.getD i true = true := by simp [Array.getD, hn]
  rw [e] at h
  cases h

/-- The invariant of marking. If all indices of a list have been marked one after the other and no
step has refused, then the array has kept its size, none of the indices was marked before, no index
stands twice in the list, and the marked indices are the earlier ones and those of the list. -/
theorem marks_spec : ∀ (l : List ℕ) (w w' : Array Bool), l.foldlM markAt w = some w' →
    w'.size = w.size ∧ (∀ i ∈ l, w.getD i true = false) ∧ l.Nodup ∧
      ∀ k, w'.getD k true = true ↔ w.getD k true = true ∨ k ∈ l
  | [], w, w', h => by
    have e : w = w' := by simpa using h
    subst e
    simp
  | i :: l, w, w', h => by
    rw [List.foldlM_cons] at h
    obtain ⟨w1, h1, h2⟩ := bind_some h
    unfold markAt at h1
    by_cases hi : w.getD i true = true
    · rw [if_pos hi] at h1
      cases h1
    · rw [if_neg hi] at h1
      cases h1
      obtain ⟨a, b, c, d⟩ := marks_spec l _ w' h2
      refine ⟨by rw [a, Array.size_setIfInBounds], ?_, ?_, ?_⟩
      · intro j hj
        rcases List.mem_cons.mp hj with rfl | hj
        · exact Bool.not_eq_true _ ▸ hi
        · have hb := b j hj
          by_contra hc
          rw [(getD_marked w i j).mpr (Or.inl (by simpa using hc))] at hb
          cases hb
      · refine List.nodup_cons.mpr ⟨fun hm => ?_, c⟩
        have hb := b i hm
        rw [(getD_marked w i i).mpr (Or.inr rfl)] at hb
        cases hb
      · intro k
        rw [d k, getD_marked, List.mem_cons, or_assoc]

/-! ## Folds -/

/-- Two folds of steps that may refuse are equal if their steps are. -/
theorem foldlM_steps {α β : Type} {f g : β → α → Option β} (h : ∀ b a, f b a = g b a)
    (l : List α) (b : β) : l.foldlM f b = l.foldlM g b := by
  have e : f = g := funext fun b => funext (h b)
  rw [e]

/-- A fold over lists laid end to end is the fold of the folds over the lists. -/
theorem foldlM_flat {α β γ : Type} (f : β → γ → Option β) (g : α → List γ) :
    ∀ (l : List α) (b : β), (l.flatMap g).foldlM f b = l.foldlM (fun b x => (g x).foldlM f b) b
  | [], b => by simp
  | x :: l, b => by
    have ih := foldlM_flat f g l
    rw [List.flatMap_cons, List.foldlM_append, List.foldlM_cons]
    simp only [ih]

/-- In lists laid end to end without a repeat, a member stands in one list only, and at one place
of it. -/
theorem flat_place {α β : Type} {f : α → List β} {l : List α} (hn : (l.flatMap f).Nodup)
    {a a' x x' : ℕ} {s s' : α} {b : β} (ha : l[a]? = some s) (ha' : l[a']? = some s')
    (hx : (f s)[x]? = some b) (hx' : (f s')[x']? = some b) : a = a' ∧ x = x' := by
  obtain ⟨h1, h2⟩ := List.nodup_flatMap.mp hn
  obtain ⟨la, ea⟩ := List.getElem?_eq_some_iff.mp ha
  obtain ⟨la', ea'⟩ := List.getElem?_eq_some_iff.mp ha'
  have hb := List.mem_of_getElem? hx
  have hb' := List.mem_of_getElem? hx'
  rcases Nat.lt_trichotomy a a' with h | h | h
  · have hd : List.Disjoint (f l[a]) (f l[a']) := List.pairwise_iff_getElem.mp h2 a a' la la' h
    rw [ea, ea'] at hd
    exact (hd hb hb').elim
  · subst h
    have es : s = s' := Option.some.inj (ha.symm.trans ha')
    subst es
    obtain ⟨lx, ex⟩ := List.getElem?_eq_some_iff.mp hx
    obtain ⟨lx', ex'⟩ := List.getElem?_eq_some_iff.mp hx'
    exact ⟨rfl, (List.Nodup.getElem_inj_iff (h1 s (List.mem_of_getElem? ha))).mp
      (ex.trans ex'.symm)⟩
  · have hd : List.Disjoint (f l[a']) (f l[a]) := List.pairwise_iff_getElem.mp h2 a' a la' la h
    rw [ea, ea'] at hd
    exact (hd hb' hb).elim

/-- A number is a J + x with x below J in at most one way. -/
theorem layer_column {J a b x y : ℕ} (hx : x < J) (hy : y < J) (h : a * J + x = b * J + y) :
    a = b ∧ x = y := by
  rcases Nat.lt_trichotomy a b with h1 | h1 | h1
  · have h2 := Nat.mul_le_mul_right J (Nat.succ_le_of_lt h1)
    rw [Nat.succ_mul] at h2
    omega
  · subst h1
    exact ⟨rfl, by omega⟩
  · have h2 := Nat.mul_le_mul_right J (Nat.succ_le_of_lt h1)
    rw [Nat.succ_mul] at h2
    omega

/-! ## The marks of a call -/

/-- The columns that the segments of call c which exist on layer lam list, segment after segment in
the order of the call's line, each segment's in the order of its entries. -/
def colsOn (v : Env) (c : CallD) (lam : ℕ) : List ℕ :=
  c.segs.flatMap fun s => if s.moe && !v.isMoe lam then [] else s.pos.toList

/-- The indices that weighedOf marks, in its order. -/
def marksOn (v : Env) (c : CallD) : List ℕ :=
  (List.range v.y.Lam).flatMap fun lam => (colsOn v c lam).map (lam * c.J + ·)

/-- A column is among colsOn exactly if some segment that exists on the layer lists it. -/
theorem mem_colsOn {v : Env} {c : CallD} {lam j : ℕ} :
    j ∈ colsOn v c lam ↔ ∃ s ∈ c.segs, (s.moe && !v.isMoe lam) = false ∧ j ∈ s.pos.toList := by
  unfold colsOn
  rw [List.mem_flatMap]
  constructor
  · rintro ⟨s, hs, hj⟩
    by_cases hb : (s.moe && !v.isMoe lam) = true
    · rw [if_pos hb] at hj
      cases hj
    · rw [if_neg hb] at hj
      exact ⟨s, hs, Bool.not_eq_true _ ▸ hb, hj⟩
  · rintro ⟨s, hs, hb, hj⟩
    refine ⟨s, hs, ?_⟩
    rw [hb]
    exact hj

/-- An index is among marksOn exactly if it is lam J + j for a layer lam of the group and a column j
among colsOn on that layer. -/
theorem mem_marksOn {v : Env} {c : CallD} {i : ℕ} :
    i ∈ marksOn v c ↔ ∃ lam, lam < v.y.Lam ∧ ∃ j ∈ colsOn v c lam, lam * c.J + j = i := by
  unfold marksOn
  simp only [List.mem_flatMap, List.mem_range, List.mem_map]

/-- markColumns marks the indices lam J + p for the columns p of the segment, in their order. -/
theorem markColumns_eq (J lam : ℕ) (s : Seg) (w : Array Bool) :
    Env.markColumns J lam s w = (s.pos.toList.map (lam * J + ·)).foldlM markAt w := by
  unfold Env.markColumns
  rw [← Array.foldlM_toList, List.foldlM_map]
  rfl

/-- weighedOf marks the indices marksOn, one after the other, in an array of Lam J places. -/
theorem weighedOf_eq (v : Env) (c : CallD) :
    v.weighedOf c = (marksOn v c).foldlM markAt (Array.replicate (v.y.Lam * c.J) false) := by
  unfold Env.weighedOf marksOn
  rw [foldlM_flat]
  refine foldlM_steps (fun w lam => ?_) _ _
  unfold colsOn
  rw [List.map_flatMap, foldlM_flat]
  refine foldlM_steps (fun w s => ?_) _ _
  by_cases hb : (s.moe && !v.isMoe lam) = true
  · rw [if_pos hb, if_pos hb]
    rfl
  · rw [if_neg hb, if_neg hb, markColumns_eq]

/-- What the marks say. Asked: weighedOf has returned the marks w; and every segment of the call
exists on the last layer of the group (hlast). Then w has Lam J places, and on every layer lam of
the group: every column that a segment which exists on lam lists is below J; these columns, taken
segment after segment and entry after entry, are all different; and a column j below J is marked at
the place lam J + j exactly if a segment that exists on lam lists it. -/
theorem weighedOf_spec {v : Env} {c : CallD} {w : Array Bool} (h : v.weighedOf c = some w)
    (hlast : ∀ s ∈ c.segs, (s.moe && !v.isMoe (v.y.Lam - 1)) = false) :
    w.size = v.y.Lam * c.J ∧ ∀ lam, lam < v.y.Lam →
      (∀ j ∈ colsOn v c lam, j < c.J) ∧ (colsOn v c lam).Nodup ∧
        ∀ j, j < c.J → (w.getD (lam * c.J + j) true = true ↔ j ∈ colsOn v c lam) := by
  rw [weighedOf_eq] at h
  obtain ⟨a, b, n, d⟩ := marks_spec _ _ _ h
  rw [Array.size_replicate] at a
  have below : ∀ lam, lam < v.y.Lam → ∀ j ∈ colsOn v c lam, j < c.J := by
    intro lam hlam j hj
    obtain ⟨s, hs, -, hp⟩ := mem_colsOn.mp hj
    have hj' : j ∈ colsOn v c (v.y.Lam - 1) := mem_colsOn.mpr ⟨s, hs, hlast s hs, hp⟩
    have hi := lt_of_unmarked (b _ (mem_marksOn.mpr ⟨v.y.Lam - 1, by omega, j, hj', rfl⟩))
    rw [Array.size_replicate] at hi
    obtain ⟨k, hk⟩ : ∃ k, v.y.Lam = k + 1 := ⟨v.y.Lam - 1, by omega⟩
    rw [hk, Nat.add_sub_cancel, Nat.succ_mul] at hi
    omega
  refine ⟨a, fun lam hlam => ⟨below lam hlam, ?_, fun j hj => ?_⟩⟩
  · exact List.Nodup.of_map _ ((List.nodup_flatMap.mp n).1 lam (List.mem_range.mpr hlam))
  · have hin : lam * c.J + j < v.y.Lam * c.J := by
      have h2 := Nat.mul_le_mul_right c.J (Nat.succ_le_of_lt hlam)
      rw [Nat.succ_mul] at h2
      omega
    have h0 : (Array.replicate (v.y.Lam * c.J) false).getD (lam * c.J + j) true = false := by
      simp [Array.getD, hin]
    rw [d, h0]
    constructor
    · rintro (h1 | h1)
      · cases h1
      · obtain ⟨lam', hl', j', hj', e⟩ := mem_marksOn.mp h1
        obtain ⟨e1, e2⟩ := layer_column (below lam' hl' j' hj') hj e
        subst e1
        subst e2
        exact hj'
    · exact fun h1 => Or.inr (mem_marksOn.mpr ⟨lam, hlam, j, h1, rfl⟩)

/-- Apart, by places. On a layer of the group, two entries of segments that exist there have one
column only if they are one entry of one segment. a, a': the segments' numbers in the call's line;
x, x': the entries' numbers. This needs no word on the last layer. -/
theorem weighedOf_apart {v : Env} {c : CallD} {w : Array Bool} (h : v.weighedOf c = some w)
    {lam : ℕ} (hlam : lam < v.y.Lam) {a a' x x' j : ℕ} {s s' : Seg} (ha : c.segs[a]? = some s)
    (ha' : c.segs[a']? = some s') (hs : (s.moe && !v.isMoe lam) = false)
    (hs' : (s'.moe && !v.isMoe lam) = false) (hx : s.pos[x]? = some j)
    (hx' : s'.pos[x']? = some j) : a = a' ∧ x = x' := by
  rw [weighedOf_eq] at h
  obtain ⟨-, -, n, -⟩ := marks_spec _ _ _ h
  have n1 : (colsOn v c lam).Nodup :=
    List.Nodup.of_map _ ((List.nodup_flatMap.mp n).1 lam (List.mem_range.mpr hlam))
  refine flat_place n1 ha ha' (b := j) ?_ ?_
  · rw [hs]
    simpa using hx
  · rw [hs']
    simpa using hx'

/-- In a layout with routed experts the last layer of a group has them. -/
theorem isMoe_last {v : Env} (L : Laid v.y) (hp : v.y.h.p3 = true) :
    v.isMoe (v.y.Lam - 1) = true := by
  have h1 : (2 ^ v.y.h.ll - 1) % 2 = 1 := by
    obtain ⟨k, hk⟩ : ∃ k, v.y.h.ll = k + 1 := ⟨v.y.h.ll - 1, by have := L.ll; omega⟩
    have h2 : 0 < 2 ^ k := Nat.pow_pos (by omega)
    rw [hk, Nat.pow_succ]
    omega
  unfold Env.isMoe
  rw [hp, L.Lam, h1]
  rfl

/-- The hypothesis of weighedOf_spec on the last layer holds in every layout that the verifier has
returned for a shape with the switches. -/
theorem last_of_layout {h : Shape} {pc : List (List String)} {v : Env}
    (hy : layout h pc = .ok v.y) (S : Switches h) (c : CallD) :
    ∀ s ∈ c.segs, (s.moe && !v.isMoe (v.y.Lam - 1)) = false := by
  intro s _
  have A := admitted_of_layout hy S.p3
  rw [isMoe_last A.laid (by rw [A.shape]; exact S.p3)]
  simp

/-- A call of two columns whose one segment exists only on layers with routed experts and lists
column 3. -/
def callOutR8 : CallD :=
  { name := "", kind := "", segs := [{ name := "", n := 1, pos := #[3], moe := true }], J := 2,
    lJ := 1, used := #[] }

/-- An environment with three layers in a group, of which only the middle one has routed experts. No
layout of the verifier has three layers in a group. All that weighedOf does not read is empty. -/
def envOutR8 : Env where
  y := { h := hR8, Lam := 3 }
  sc := ⟨#[], 13, 8⟩
  g := 0
  iU3 := 0
  K3 := 16
  tab := []
  zk := #[]

/- Why weighedOf_spec asks that every segment exists on the last layer: weighedOf returns marks for
callOutR8 in envOutR8, the listed column is not below J, and column 1 of the last layer is marked,
where no segment exists. -/
#guard envOutR8.weighedOf callOutR8 == some #[false, false, false, false, false, true]

section Padding

variable {K : Type} [Field K] (ρ : Reading K)

/-- The weight of the padding's columns, by the columns themselves: for each layer its weight times
the sum of the weights of the columns below J that no segment which exists on that layer lists. The
hypotheses are those of weighedOf_spec. -/
theorem padJ_unlisted {v : Env} {c : CallD} {w : Array Bool} (h : v.weighedOf c = some w)
    (hlast : ∀ s ∈ c.segs, (s.moe && !v.isMoe (v.y.Lam - 1)) = false) (q : ℕ) :
    padJ ρ v q c w = ∑ lam ∈ range v.y.Lam, ρ.val (elJ v q lam) *
      ∑ j ∈ (range c.J).filter (fun j => j ∉ colsOn v c lam),
        ρ.val ((eqTab (v.zj q c.lJ)).getD j zeroE) := by
  obtain ⟨-, H⟩ := weighedOf_spec h hlast
  unfold padJ
  rw [list_range_sum]
  refine Finset.sum_congr rfl fun lam hlam => ?_
  obtain ⟨-, -, m⟩ := H lam (Finset.mem_range.mp hlam)
  rw [list_range_sum, Finset.sum_filter]
  congr 1
  refine Finset.sum_congr rfl fun j hj => ?_
  have mj := m j (Finset.mem_range.mp hj)
  by_cases hm : j ∈ colsOn v c lam
  · rw [if_pos (mj.mpr hm), if_neg (not_not.mpr hm)]
  · rw [if_neg (fun e => hm (mj.mp e)), if_pos hm]

end Padding

#print axioms switchesR8
#print axioms marks_spec
#print axioms weighedOf_eq
#print axioms weighedOf_spec
#print axioms weighedOf_apart
#print axioms last_of_layout
#print axioms padJ_unlisted

end OnBytes.Road
