-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/FormsKeysKV.lean: one call's factor in the lookup's join, and the library's key vector.

For a call of the verifier's layout whose line names the families of the library's call cc, in the
library's order, the value of the verifier's joinPart is
  alpha - q theta - (the multilinear extension of the library's key vector keyVec cc at the call's
  own point) + TS + the matrix products,
where TS and the matrix products are the parts of that extension that come from the products in the
keys, at that point (TSP, ACCP of Johnson/Road/FormsKeysFree.lean). They stand inside the extension
and are added back. So the statement says of the key vector: its padding, its columns, its weights
and the affine parts of its keys. Of the products in the keys it says nothing: it holds for all
weights w, every L0 and, but for the padding key, every tb.

What is compared with what: the verifier's joinPart, on the verifier's own layout, marks and points,
with the library's keyVec.

The parts: Johnson/Road/FormsKeysPoint.lean (the call's point; the lines' worth),
Johnson/Road/FormsKeysPos.lean (the verifier's rule for the columns is the library's pos; the number
of columns), Johnson/Road/FormsKeysRun8.lean and Johnson/Road/FormsKeysTab.lean (what the verifier's
marks say; every column that the placing rule gives is one of the call's),
Johnson/Road/FormsKeysKF.lean (the call in the library's quantities),
Johnson/Road/FormsKeysVec.lean (the extension of the key vector, on the library's side alone).

Main definitions: famS.
Main theorems: callFits_of_layout, lJ_of_call, hpad_of_word, joinPart_keyVec.

Hypotheses of joinPart_keyVec that no theorem concludes: that layout, scalesHeld, readsOf and
layTables return; the switches; that the six families of tables are true in the world at hand; the
verifier's run-time tests on the points, in their own words; that cd is call number q (hcq); that
the call's line is the library's (hn); that the verifier's least number of columns does
not pass the library's number (hfl: it hangs on a line of the parameter file); that the verifier's
padding key is the library's (hpad: hpad_of_word brings it down to an equation of two words; no
theorem compares the two texts' tables); that joinPart and weighedOf return.
Johnson/Road/FormsKeysRun8.lean runs these together on made-up numbers, but for the truth of the
tables of reads; hpad it runs as numbers and as words. Johnson/Road/FormsKeysRunK.lean runs them on
the two examples' own files: at the small one hfl fails for four calls; at the large one joinPart is
not run. That call number q has the table of the
library's call cc is asked in hpad alone, for one row; q need not be cc.

What is not claimed: see Johnson/Road/FormsKeysKit.lean. How the call's point is cut out of the
point of the whole lookup, the calls' weights and the trees are not looked at. A parameter file that
divides the segments into calls otherwise than the library is outside this file. The program does
not import this file.
-/
import Johnson.Road.FormsKeysPoint
import Johnson.Road.FormsKeysPos
import Johnson.Road.FormsKeysTab
import Johnson.Road.FormsKeysKF
import Johnson.Road.FormsKeysVec

set_option autoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road

open Finset
open OnBytes.Model (Reading World Aff Seg CallD lastOf place topBit)
open OnBytes.Model.Layer (Env Lay Shape Reads TableAsk TableAt layout scalesHeld readsOf layTables
  tableAsks)
open Inst.Model (Scl Tables)
open Inst.Model.FFSeg (Dim Fam LW len fams famsIn used lJ aC keyVec lut)

/-- The family of a segment, by its name; G if the name is no family's. -/
def famS (g : Seg) : Fam := (famOf g.name).getD .G

variable {h : Shape} {pc : List (List String)} {v : Env}

/-- A call of the verifier's layout whose line names the families of the library's call cc, in the
library's order, is that call, in the sense of the record CallFits, and each of its segments holds
its family, in the sense of SegFits. Asked beside: the switches; sizes that agree with the shape;
the verifier's least logarithm of the number of columns, nmin - ll - lt, is at most the library's
logarithm; weighedOf has returned the marks. -/
theorem callFits_of_layout (hy : layout h pc = .ok v.y) (S : Switches h) {D : Dim} (Z : Sized h D)
    {cd : CallD} (hcd : cd ∈ v.y.calls) {cc : Fin 8}
    (hn : cd.segs.map (·.name) = (fams cc).map segName)
    (hfl : h.nmin - h.ll - h.lt ≤ Nat.clog 2 (used D cc)) {weighed : Array Bool}
    (hw : v.weighedOf cd = some weighed) :
    CallFits v D cd weighed cc famS ∧ ∀ s ∈ cd.segs, SegFits v D cd.lJ s (famS s) := by
  have A := admitted_of_layout hy S.p3
  have HS : ∀ s ∈ cd.segs, SegFits v D cd.lJ s (famS s) := by
    intro s hs
    obtain ⟨fam, a1, a2, a3, a4, a5⟩ := segs_of_layout hy S cd hcd s hs
    have e : famS s = fam := by
      unfold famS
      rw [a1, famOf_segName]
      rfl
    rw [e]
    exact ⟨a1, a2.trans (Z.len_eq fam).symm, a3, a4, a5⟩
  have hfam : cd.segs.map famS = fams cc := by
    have e1 : cd.segs.map famS = (cd.segs.map (·.name)).map fun n => (famOf n).getD .G := by
      rw [List.map_map]
      rfl
    rw [e1, hn, List.map_map]
    conv_rhs => rw [← List.map_id (fams cc)]
    refine List.map_congr_left fun s _ => ?_
    show (famOf (segName s)).getD .G = s
    rw [famOf_segName]
    rfl
  have hlt : ∀ s ∈ fams cc, len D s < 2 ^ (topBit + 1) := fun s _ => by
    rw [Z.len_eq s]
    exact len_lt A s
  obtain ⟨hsize, hmarks⟩ := weighedOf_spec' hw (inside_of_layout hy S cd hcd)
  obtain ⟨cl, taken, -, -, h3⟩ := A.calls
  rw [h3] at hcd
  obtain ⟨c0, -, rfl⟩ := List.mem_map.mp (List.mem_toArray.mp hcd)
  have hlen := fun g hg => (HS g hg).n
  have hl := lengths_of_segs D cc c0.1 c0.2.1 c0.2.2 _ famS hfam hlen
  refine ⟨⟨hfam, pos_eq_segs D cc c0.1 c0.2.1 c0.2.2 _ famS hfam hlen hlt,
    lJ_eq D cc c0.1 c0.2.1 c0.2.2 _ hl hlt hfl, place_J _ _ _ _, ?_, ?_⟩, HS⟩
  · intro lam j hlam hj
    rw [(hmarks lam hlam).2.2 j hj, mem_colsOn]
    constructor
    · rintro ⟨s, hs, he, hm⟩
      obtain ⟨x, hx, e⟩ := List.getElem_of_mem hm
      have hx' : x < s.pos.size := by simpa using hx
      refine ⟨s, hs, he, x, hx', ?_⟩
      rw [Array.getD, dif_pos hx']
      simpa using e
    · rintro ⟨s, hs, he, x, hx, e⟩
      refine ⟨s, hs, he, ?_⟩
      rw [Array.getD, dif_pos hx] at e
      rw [← e]
      simp
  · rw [A.shape]
    exact Z.lL.symm

/-- The verifier's logarithm of the number of columns of such a call, without a hypothesis on the
least number: it is the larger of the library's and nmin - ll - lt. -/
theorem lJ_of_call (hy : layout h pc = .ok v.y) (S : Switches h) {D : Dim} (Z : Sized h D)
    {cd : CallD} (hcd : cd ∈ v.y.calls) {cc : Fin 8}
    (hn : cd.segs.map (·.name) = (fams cc).map segName) :
    cd.lJ = max (lJ D cc) (h.nmin - h.ll - h.lt) := by
  have A := admitted_of_layout hy S.p3
  have hlen : ∀ s ∈ cd.segs, s.n = len D (famS s) := by
    intro s hs
    obtain ⟨fam, a1, a2, -, -, -⟩ := segs_of_layout hy S cd hcd s hs
    have e : famS s = fam := by
      unfold famS
      rw [a1, famOf_segName]
      rfl
    rw [e]
    exact a2.trans (Z.len_eq fam).symm
  have hfam : cd.segs.map famS = fams cc := by
    have e1 : cd.segs.map famS = (cd.segs.map (·.name)).map fun n => (famOf n).getD .G := by
      rw [List.map_map]
      rfl
    rw [e1, hn, List.map_map]
    conv_rhs => rw [← List.map_id (fams cc)]
    refine List.map_congr_left fun s _ => ?_
    show (famOf (segName s)).getD .G = s
    rw [famOf_segName]
    rfl
  have hlt : ∀ s ∈ fams cc, len D s < 2 ^ (topBit + 1) := fun s _ => by
    rw [Z.len_eq s]
    exact len_lt A s
  obtain ⟨cl, taken, -, -, h3⟩ := A.calls
  rw [h3] at hcd
  obtain ⟨c0, -, rfl⟩ := List.mem_map.mp (List.mem_toArray.mp hcd)
  exact lJ_max D cc c0.1 c0.2.1 c0.2.2 _
    (lengths_of_segs D cc c0.1 c0.2.1 c0.2.2 _ famS hfam hlen) hlt

/-- The hypothesis hpad of joinPart_keyVec, from an equation of two words: if the verifier's padding
key is the word of the number n, it reads as n. -/
theorem hpad_of_word {K : Type} [Field K] {ρ : Reading K} (hρ : Numerals ρ) {x : F} {n : ℕ}
    (h : x = Model.fOfNat n) : ρ.val (ofF x) = ((n : ℤ) : K) := by
  rw [h]
  show ρ.val (Model.ofNat n) = _
  rw [hρ.ofNat]
  push_cast
  rfl

section Run

variable {K : Type} [Field K] {rd : Reads} {mats : Array (ℕ × ℕ)}
  {r : List TableAt × List (TableAsk × List (ℕ × ℕ)) × ℕ}

/-- One call's factor in the lookup's join against the library's key vector. On the verifier's own
layout, scales and tables (the seven lines), at the verifier's own points (its lines and run-time
tests hZ, hzt, hm, ha, hpt), in any world in which the six families of tables are true there: if
call number q of the layout names the families of the library's call cc in the library's order (hn),
the least number of columns does not bite (hfl), the marks are weighedOf's (hw) and the padding key
is the library's (hpad), then the form that joinPart returns is worth alpha - q theta, less the
multilinear extension of the library's key vector of call cc at the point of call q, plus TSP and
the sums ACCP at that point. For all tb, L0 and w: TSP and ACCP stand inside the extension and are
added back, so the right side does not hang on w or L0. The seven lines: hy, S, hs, hg, hrd, hl,
ht. -/
theorem joinPart_keyVec (hy : layout h pc = .ok v.y) (S : Switches h)
    (hs : scalesHeld h v.sc = .ok ()) (hg : v.g < v.y.NGr) (hrd : readsOf v.y = .ok rd)
    (hl : layTables mats (tableAsks v.y rd v.g) 0 = some r) (ht : v.tab = r.1)
    {ρ : Reading K} (hρ : Numerals ρ) {D : Dim} (Zd : Sized h D) {W : World K}
    {zx Z zt : Array E} {ends : Array (Array E)}
    (hZ : lastOf zx v.y.h.la = .ok Z) (hzt : lastOf zx v.y.h.lt = .ok zt)
    (hm : v.zk.mapM (fun z => (lastOf z v.y.h.la).toOption) = some ends)
    (ha : ends.all (· == Z) = true) {NC : ℕ}
    (hpt : ((List.range NC).all fun c =>
      (v.zk.getD c #[]).size == ((v.y.cl[c]?).map (·.n)).getD 0) = true)
    (c : Cells K) (T : TrueAt ρ W v h.lt c (pt ρ Z) (pt ρ zt)) (tb : Tables) (L0 : ℕ)
    (w : ℕ → LW K) (alpha theta : E) (q : ℕ) (cd : CallD) (hcq : v.y.calls[q]? = some cd)
    (hq : q < NC) (hq' : q < v.zk.size) {cc : Fin 8}
    (hn : cd.segs.map (·.name) = (fams cc).map segName)
    (hfl : h.nmin - h.ll - h.lt ≤ Nat.clog 2 (used D cc)) {weighed : Array Bool}
    (hw : v.weighedOf cd = some weighed)
    (hpad : ρ.val (ofF ((v.y.cl.getD q {}).tauAt (v.y.cl.getD q {}).t0)) =
      (((lut tb cc).pad : ℤ) : K))
    {f : Aff} (hf : v.joinPart alpha theta q cd weighed = some f) :
    f.value ρ W = ρ.val alpha - (q : K) * ρ.val theta -
      Blocks.ext (aC D cc) (keyVec (scl := sclOf h v.sc v.g v.y.Lam) D (cellsOf D c) tb L0 w cc)
        (pt ρ (v.zk.getD q #[])) +
      TSP (scl := sclOf h v.sc v.g v.y.Lam) D (cellsOf D c) tb L0 w cc (pt ρ (v.zk.getD q #[])) +
      ∑ l ∈ range D.nl, elP D (pt ρ (v.zk.getD q #[])) l *
        ((famsIn cc l).map fun s =>
          ACCP (scl := sclOf h v.sc v.g v.y.Lam) D (cellsOf D c) w (pt ρ (v.zk.getD q #[])) s
            l).sum := by
  letI : Scl := sclOf h v.sc v.g v.y.Lam
  have A := admitted_of_layout hy S.p3
  have hcd : cd ∈ v.y.calls := Array.mem_of_getElem? hcq
  obtain ⟨C, HS⟩ := callFits_of_layout hy S Zd hcd hn hfl hw
  obtain ⟨k2, ku, -⟩ := joinPart_of_run hy S hs hg hrd hl ht hρ Zd hZ hzt hm ha hpt c T tb L0 w
    alpha theta q cd hcq hq hq' weighed hf
  have hsz := size_of_test hy hpt hq hcq
  have F := fits_of_layout_true hy S hs hg hrd hl ht hρ Zd c (pt ρ Z) (pt ρ zt) T
  have hu : ∀ j, j < D.lT → pt ρ zt j = pt ρ (v.zk.getD q #[]) (D.lL + lJ D cc + j) := by
    intro j hj
    have e := ku j (by rw [A.shape, ← Zd.lT]; exact hj)
    rw [C.ll, C.lJ] at e
    exact e
  rw [ext_keyVec_KFP]
  exact F.joinPart_KF tb L0 w alpha theta q cd weighed cc famS C HS (by omega)
    (lJ_of_layout hy cd hcd) k2 hu hpad hf

end Run

#print axioms callFits_of_layout
#print axioms lJ_of_call
#print axioms hpad_of_word
#print axioms joinPart_keyVec

end OnBytes.Road
