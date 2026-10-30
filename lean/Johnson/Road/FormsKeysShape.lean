-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/FormsKeysShape.lean: the lookup's own numbers of a layer sub-proof: its calls, their
number, and the depth of a tree.

Two matters.

1. The test on the calls' points. When the verifier runs the lookup it tests that the point of each
call has as many coordinates as the call's record says (internal-forest-point in Forest.pad,
OnBytes/Model/Look.lean). By the text of Forest.pad and of its caller hearLook
(OnBytes/Model/Layer.lean), which no theorem here unfolds, that test reads the records and their
number in what Forest.shape returns on the layout's records y.cl and the shape's cap lidb.
joinPart_keyVec (Johnson/Road/FormsKeysKV.lean) has the test written on the layout's records, with
any number NC of calls, and two hypotheses q < NC and q < zk.size beside it. Here the test is taken
in the verifier's own letters, and the two hypotheses are concluded.
 - shape_calls: Forest.shape returns the calls that it was given, and their number.
 - shape_of_layout: for a layout that layout returns, Forest.shape returns on y.cl and lidb, and
   y.fo is what it returns, but for the field pub. So the hypothesis hs0 below can be met.
 - fo_of_layout: y.fo.calls = y.cl, y.fo.NC = y.cl.size = y.calls.size.
 - test_of_port: the verifier's test gives the test on the layout's records.
 - point_there: a call's point is there, since the test gives it at least one coordinate.
 - joinPart_keyVec': joinPart_keyVec with these.

2. The depth of a tree. The library's Dk D is the least of D.cap and the calls' numbers of
coordinates aC D c; the verifier's fo.dT is the least of lidb and the records' n.
 - Dk_of_layout: Dk D = y.fo.dT, for sizes that agree with the shape and have cap = lidb, and a
   layout with eight calls, each with the line of the library's call of its number, in which the
   verifier's least number of columns does not pass the library's.

What is compared with what. Matter 1: the verifier's functions with themselves (Forest.shape,
layout); joinPart_keyVec' as joinPart_keyVec. Matter 2: the verifier's fo.dT against the library's
Dk.

Hypotheses that no theorem concludes: those of joinPart_keyVec but hq and hq'. For Dk_of_layout:
that layout returns; the switches; the eight lines and the eight bounds (H). The "#guard" at the end
evaluates both depths on the made-up shape hR8 of Johnson/Road/FormsKeysRun8.lean, whose guards run
the lines and the bounds.

What is not claimed. That the array zk of an environment is the one that Forest.pad makes is not
shown: the test is a hypothesis on v.zk. The trees' numbers, first trees and prefixes are not
compared with the library's. The program does not import this file.
-/
import Johnson.Road.FormsKeysKV
import Johnson.Road.FormsKeysCap

set_option autoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road

open Finset
open OnBytes.Model (Reading World Aff Seg CallD Call lastOf)
open OnBytes.Model.Layer (Env Lay Shape Reads TableAsk TableAt layout layoutLook scalesHeld readsOf
  layTables tableAsks)
open Inst.Model (Scl Tables)
open Inst.Model.FFSeg (Dim Fam LW fams famsIn used lJ aC Dk keyVec lut)

/-! ## What Forest.shape returns -/

/-- Forest.shape returns the calls that it was given, and their number. -/
theorem shape_calls {calls : Array Call} {lid : ℕ} {fo : Model.Forest.Shape}
    (h : Model.Forest.shape calls lid = .ok fo) : fo.calls = calls ∧ fo.NC = calls.size := by
  unfold Model.Forest.shape at h
  obtain ⟨-, -, h⟩ := ok_of_bind h
  obtain ⟨-, h⟩ := ok_of_jp h
  obtain ⟨-, h⟩ := ok_of_jp h
  obtain ⟨-, h⟩ := ok_of_jp h
  obtain ⟨-, h⟩ := ok_of_jp h
  obtain ⟨-, h⟩ := ok_of_jp h
  obtain ⟨r, -, h⟩ := ok_of_bind h
  obtain ⟨callOf, first, free⟩ := r
  obtain ⟨-, h⟩ := ok_of_jp h
  have e := (Except.ok.inj h).symm
  subst e
  exact ⟨rfl, rfl⟩

/-- The second half of the layout holds what Forest.shape returns on the calls' records and the
shape's cap, with the field pub filled in. -/
theorem look_fo {y y' : Lay} (hy : layoutLook y = .ok y') :
    ∃ s0 pub, Model.Forest.shape y'.cl y'.h.lidb = .ok s0 ∧ y'.fo = { s0 with pub := pub } := by
  unfold layoutLook at hy
  obtain ⟨u, hu, hy⟩ := ok_of_bind hy
  obtain ⟨fo, hfo, hy⟩ := ok_of_bind hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨kbm, -, hy⟩ := ok_of_bind hy
  obtain ⟨-, -, hy⟩ := ok_of_bind hy
  obtain ⟨pub, -, hy⟩ := ok_of_bind hy
  obtain ⟨-, -, hy⟩ := ok_of_bind hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  cases hy
  exact ⟨fo, pub, hfo, rfl⟩

/-- For a layout that the verifier returns, Forest.shape returns on the layout's records of the
calls and the shape's cap, and the layout's numbers of the lookup are what it returns, but for the
field pub. -/
theorem shape_of_layout {h : Shape} {pc : List (List String)} {y : Lay}
    (hy : layout h pc = .ok y) :
    ∃ s0 pub, Model.Forest.shape y.cl y.h.lidb = .ok s0 ∧ y.fo = { s0 with pub := pub } := by
  unfold layout at hy
  obtain ⟨y0, -, h1⟩ := ok_of_bind hy
  exact look_fo h1

/-- The layout's numbers of the lookup hold the layout's records of the calls, and their number,
which is the number of the layout's calls. -/
theorem fo_of_layout {h : Shape} {pc : List (List String)} {y : Lay}
    (hy : layout h pc = .ok y) :
    y.fo.calls = y.cl ∧ y.fo.NC = y.cl.size ∧ y.cl.size = y.calls.size := by
  obtain ⟨s0, pub, hs, e⟩ := shape_of_layout hy
  obtain ⟨a, b⟩ := shape_calls hs
  refine ⟨by rw [e]; exact a, by rw [e]; exact b, ?_⟩
  rw [cl_of_layout hy]
  simp

/-! ## The test on the calls' points -/

/-- The verifier's test on the calls' points, in its own letters, on numbers s0 that Forest.shape
has returned for the layout's records, is the test on the layout's records, for as many calls as the
layout has. -/
theorem test_of_port {h : Shape} {pc : List (List String)} {v : Env} (hy : layout h pc = .ok v.y)
    {s0 : Model.Forest.Shape} (hs0 : Model.Forest.shape v.y.cl v.y.h.lidb = .ok s0)
    (hpt : ((List.range s0.NC).all fun c =>
      (v.zk.getD c #[]).size == ((s0.calls[c]?).map (·.n)).getD 0) = true) :
    ((List.range v.y.calls.size).all fun c =>
      (v.zk.getD c #[]).size == ((v.y.cl[c]?).map (·.n)).getD 0) = true := by
  obtain ⟨a, b⟩ := shape_calls hs0
  rw [a, b, (fo_of_layout hy).2.2] at hpt
  exact hpt

/-- A call's point is there: the test gives it ll + lJ + lt coordinates, and ll is at least 1, while
a point that is not there reads as the empty one. -/
theorem point_there {h : Shape} {pc : List (List String)} {v : Env} (hy : layout h pc = .ok v.y)
    (hp3 : h.p3 = true) {NC q : ℕ} {cd : CallD}
    (hpt : ((List.range NC).all fun c =>
      (v.zk.getD c #[]).size == ((v.y.cl[c]?).map (·.n)).getD 0) = true)
    (hq : q < NC) (hcq : v.y.calls[q]? = some cd) : q < v.zk.size := by
  have hsz := size_of_test hy hpt hq hcq
  have hll := (admitted_of_layout hy hp3).laid.ll
  by_contra hc
  have e : v.zk.getD q #[] = #[] := by
    rw [Array.getD, dif_neg hc]
  rw [e] at hsz
  have e0 : (#[] : Array E).size = 0 := rfl
  omega

/-- A number under which the layout has a call is below the number of its calls. -/
theorem lt_of_call {y : Lay} {q : ℕ} {cd : CallD} (hcq : y.calls[q]? = some cd) :
    q < y.calls.size := by
  by_contra hc
  have e : y.calls[q]? = none := Array.getElem?_eq_none (Nat.not_lt.mp hc)
  rw [e] at hcq
  cases hcq

section Run

variable {h : Shape} {pc : List (List String)} {v : Env} {K : Type} [Field K] {rd : Reads}
  {mats : Array (ℕ × ℕ)} {r : List TableAt × List (TableAsk × List (ℕ × ℕ)) × ℕ}

/-- joinPart_keyVec with the test on the calls' points in the verifier's own letters: on the numbers
s0 that Forest.shape returns for the layout's records and the shape's cap (hs0, hpt). That q is
below the number of calls and that the point of call q is there are no hypotheses any more. All else
is as in joinPart_keyVec. -/
theorem joinPart_keyVec' (hy : layout h pc = .ok v.y) (S : Switches h)
    (hs : scalesHeld h v.sc = .ok ()) (hg : v.g < v.y.NGr) (hrd : readsOf v.y = .ok rd)
    (hl : layTables mats (tableAsks v.y rd v.g) 0 = some r) (ht : v.tab = r.1)
    {ρ : Reading K} (hρ : Numerals ρ) {D : Dim} (Zd : Sized h D) {W : World K}
    {zx Z zt : Array E} {ends : Array (Array E)}
    (hZ : lastOf zx v.y.h.la = .ok Z) (hzt : lastOf zx v.y.h.lt = .ok zt)
    (hm : v.zk.mapM (fun z => (lastOf z v.y.h.la).toOption) = some ends)
    (ha : ends.all (· == Z) = true) {s0 : Model.Forest.Shape}
    (hs0 : Model.Forest.shape v.y.cl v.y.h.lidb = .ok s0)
    (hpt : ((List.range s0.NC).all fun c =>
      (v.zk.getD c #[]).size == ((s0.calls[c]?).map (·.n)).getD 0) = true)
    (c : Cells K) (T : TrueAt ρ W v h.lt c (pt ρ Z) (pt ρ zt)) (tb : Tables) (L0 : ℕ)
    (w : ℕ → LW K) (alpha theta : E) (q : ℕ) (cd : CallD) (hcq : v.y.calls[q]? = some cd)
    {cc : Fin 8} (hn : cd.segs.map (·.name) = (fams cc).map segName)
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
  have hpt' := test_of_port hy hs0 hpt
  have hq := lt_of_call hcq
  exact joinPart_keyVec hy S hs hg hrd hl ht hρ Zd hZ hzt hm ha hpt' c T tb L0 w alpha theta q cd
    hcq hq (point_there hy S.p3 hpt' hq hcq) hn hfl hw hpad hf

end Run

/-! ## The depth of a tree -/

/-- The least value over an array of eight records is the least value over the eight numbers. -/
theorem fold_eight (A : Array Call) (f : Fin 8 → ℕ) (a : ℕ) (hs : A.size = 8)
    (hf : ∀ c : Fin 8, (A[c.val]?).map (·.n) = some (f c)) :
    A.foldl (fun m c => min m c.n) a = (List.finRange 8).foldl (fun m c => min m (f c)) a := by
  obtain ⟨l⟩ := A
  rcases l with _ | ⟨a0, _ | ⟨a1, _ | ⟨a2, _ | ⟨a3, _ | ⟨a4, _ | ⟨a5, _ | ⟨a6, _ | ⟨a7, _ |
    ⟨a8, l⟩⟩⟩⟩⟩⟩⟩⟩⟩
  all_goals try (exfalso; simp at hs; done)
  have h0 : a0.n = f 0 := Option.some.inj (hf 0)
  have h1 : a1.n = f 1 := Option.some.inj (hf 1)
  have h2 : a2.n = f 2 := Option.some.inj (hf 2)
  have h3 : a3.n = f 3 := Option.some.inj (hf 3)
  have h4 : a4.n = f 4 := Option.some.inj (hf 4)
  have h5 : a5.n = f 5 := Option.some.inj (hf 5)
  have h6 : a6.n = f 6 := Option.some.inj (hf 6)
  have h7 : a7.n = f 7 := Option.some.inj (hf 7)
  have e8 : List.finRange 8 = [0, 1, 2, 3, 4, 5, 6, 7] := by decide
  rw [← Array.foldl_toList, e8]
  show List.foldl (fun m c => min m c.n) a [a0, a1, a2, a3, a4, a5, a6, a7] = _
  simp only [List.foldl_cons, List.foldl_nil, h0, h1, h2, h3, h4, h5, h6, h7]

/-- The library's depth of a tree is the verifier's. For sizes that agree with the shape and have
the verifier's cap, and a layout with eight calls, where call number cc has the line of the
library's call cc and the verifier's least logarithm of the number of columns, nmin - ll - lt, is at
most the library's logarithm (H). -/
theorem Dk_of_layout {h : Shape} {pc : List (List String)} {v : Env} (hy : layout h pc = .ok v.y)
    (S : Switches h) {D : Dim} (Z : Sized h D) (hc : D.cap = h.lidb) (h8 : v.y.calls.size = 8)
    (H : ∀ cc : Fin 8, ∃ cd, v.y.calls[cc.val]? = some cd ∧
      cd.segs.map (·.name) = (fams cc).map segName ∧
      h.nmin - h.ll - h.lt ≤ Nat.clog 2 (used D cc)) :
    Dk D = v.y.fo.dT := by
  obtain ⟨-, -, e⟩ := dT_of_layout hy
  have hsh := (admitted_of_layout hy S.p3).shape
  rw [e]
  unfold Inst.Model.FFSeg.Dk
  rw [hc]
  symm
  refine fold_eight v.y.cl (aC D) h.lidb (by rw [(fo_of_layout hy).2.2, h8]) fun cc => ?_
  obtain ⟨cd, hcq, hn, hfl⟩ := H cc
  have hfl' : h.nmin - h.ll - h.lt ≤ lJ D cc := hfl
  have h2 : v.y.cl[cc.val]? = some (v.y.callRecord cc.val cd) := by
    rw [cl_of_layout hy]
    simp [hcq]
  rw [h2]
  show some (v.y.h.ll + cd.lJ + v.y.h.lt) = some (D.lL + lJ D cc + D.lT)
  rw [lJ_of_call hy S Z (Array.mem_of_getElem? hcq) hn, hsh, Z.lL, Z.lT, Nat.max_eq_left hfl']

/-! ## A run on made-up numbers -/

/- on the shape hR8 with its eight calls, at the sizes dimC hR8: the layout has eight calls and
eight records, and its numbers of the lookup hold as many; the eight lines are the library's and the
eight bounds hold (the hypothesis H of Dk_of_layout); the library's depth of a tree is the
verifier's -/
#guard (match layout hR8 pcR8 with
  | .ok y => y.calls.size == 8 && y.cl.size == 8 && y.fo.NC == 8 && y.fo.calls.size == 8 &&
      namesR8 y.calls && (floorR8 hR8 (dimC hR8)).all id && Dk (dimC hR8) == y.fo.dT
  | .error _ => false)

#print axioms shape_calls
#print axioms shape_of_layout
#print axioms fo_of_layout
#print axioms test_of_port
#print axioms point_there
#print axioms joinPart_keyVec'
#print axioms Dk_of_layout

end OnBytes.Road
