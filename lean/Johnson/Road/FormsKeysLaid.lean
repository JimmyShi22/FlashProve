-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Road/FormsKeysLaid.lean: what the verifier's own tests give: the plain facts on a layout's
numbers, the range of the norms' shifts, and the segments of the lookup's calls.

Johnson/Road/FormsKeysFits.lean proves the record Fits from a few records of hypotheses, and
Johnson/Road/FormsKeysCall.lean asks five things of every segment of a call.
This file proves, from the verifier's own functions:
 - the record Laid, plain facts on the numbers of a layout, of every layout that the function layout
   returns for a shape with routed experts (laid_of_layout), and that each of its calls has at least
   as many columns as a block has features (lJ_of_layout),
 - that the norms' shifts are at least 17 on every layer of the model, if the test scalesHeld has
   passed (K_of_scalesHeld), and so at least 16 on the layers of every group (K_on_group, K_of_env),
 - under the switches for which the library has keys: every segment of every call of such a layout
   has the name, the length and the layers of one of the library's families, one column for each
   entry, and, if the family is read by blocks, columns that are aligned on blocks (segs_of_layout).
   This says that every segment is a family. It does not say that every family has a segment; for
   that, segmentList_has says that every family's name is in the verifier's list of segments, and
   the record Admitted keeps the layout's test that every segment of the list has been taken.

How. layoutBase is one long block of tests, each of which refuses or goes on. If the block returns a
layout, every test has gone on, and the layout is the record that the block's last line writes out.
The record Admitted gathers what is used of that. layoutLook changes three fields that Admitted does
not read. A call's segments are taken from the list segmentList by name, so each has a member's
length; under the switches each member of that list is one of the library's families.

Main definitions: Admitted, segsRef.
Main theorems: admitted_of_base, look_keeps, admitted_of_layout, laid_of_layout, cl_of_layout,
lJ_of_layout;
K_of_scalesHeld, K_on_group, K_of_env; segmentList_ref, segmentList_has, takeCalls_mem,
segs_of_admitted, segs_of_layout.

What is not claimed: see Johnson/Road/FormsKeysKit.lean. Nothing is said on a shape without routed
experts. That each family has a segment in some call is shown in Johnson/Road/FormsKeysAdmit.lean,
not here. That no two segments share a column is not shown of the layout;
that two segments which exist on one layer share none there follows from a test that the verifier
makes when it runs (Johnson/Road/FormsKeysRun8.lean). What the calls' kinds of tables are is not
shown. The program does not import this file.

Files named above that a package may lack. Johnson/Road/FormsKeysCall.lean,
Johnson/Road/FormsKeysAdmit.lean and Johnson/Road/FormsKeysRun8.lean are in
the library's full tree and are not imported by this file; a package that is cut to what its front
theorems need may not hold them. Where they lack, what this comment says of them cannot be checked
there.

-/
import Johnson.Road.FormsKeysFits
import Johnson.Road.FormsKeysPlace

set_option autoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road

open OnBytes.Model (refuseIf Seg CallD SegAsk topBit place)
open OnBytes.Model.Layer (Env Lay Shape Scales layout layoutBase layoutLook scalesHeld scalesHeldAt
  segmentList takeSegments takeCalls)
open Inst.Model.FFSeg (Fam len isExp)

/-! ## A block of tests that returns a value -/

/-- If a step and what follows it return a value, the step has returned one, and what follows
returns the value from it. -/
theorem ok_of_bind {α β : Type} {x : Except String α} {f : α → Except String β} {y : β}
    (h : (x >>= f) = .ok y) : ∃ a, x = .ok a ∧ f a = .ok y := by
  cases x with
  | error e => cases h
  | ok a => exact ⟨a, rfl, h⟩

/-- A test that goes on has found its condition false. -/
theorem false_of_refuseIf {b : Bool} {n : String} {a : Unit} (h : refuseIf b n = .ok a) :
    b = false := by
  cases b with
  | false => rfl
  | true => cases h

/-- If a test and what follows it return a value, the test's condition is false, and what follows
returns the value. -/
theorem ok_of_refuse {β : Type} {b : Bool} {n : String} {f : Unit → Except String β} {y : β}
    (h : (refuseIf b n >>= f) = .ok y) : b = false ∧ f () = .ok y := by
  obtain ⟨a, h1, h2⟩ := ok_of_bind h
  exact ⟨false_of_refuseIf h1, h2⟩

/-- If "one condition or the other" is false, both are. -/
theorem or_false_split {a b : Bool} (h : (a || b) = false) : a = false ∧ b = false := by
  cases a <;> cases b <;> first | exact ⟨rfl, rfl⟩ | cases h

/-- The test "the remainder is not 0", found false. -/
theorem dvd_of_bne {a s : ℕ} (h : (a % s != 0) = false) : s ∣ a :=
  Nat.dvd_of_mod_eq_zero (by simpa using h)

/-- The test "above the bound", found false. -/
theorem le_of_gt_false {a b : ℕ} (h : decide (a > b) = false) : a ≤ b :=
  Nat.not_lt.mp (of_decide_eq_false h)

/-! ## The layout -/

/-- What is used of a layout that the verifier has admitted for the shape h. -/
structure Admitted (h : Shape) (y : Lay) : Prop where
  /-- the layout holds its shape -/
  shape : y.h = h
  /-- the plain facts on its numbers -/
  laid : Laid y
  /-- the rows of a block: the bits of a feature in its block, then those of a token -/
  la : h.la = y.ls + h.lt
  /-- the groups of layers -/
  NGr : y.NGr = h.L / 2 ^ h.ll
  /-- the layers are whole groups -/
  whole : h.L % 2 ^ h.ll = 0
  /-- the bounds on the widths -/
  d20 : h.d ≤ 2 ^ 20
  f20 : h.f ≤ 2 ^ 20
  /-- the query heads fill the model's width -/
  Hd : h.H * h.dh = h.d
  /-- there is a query head, and at most 64 heads -/
  H0 : h.H ≠ 0
  heads : h.H + h.Gk ≤ 64
  /-- the bound on the experts -/
  NE : h.NE ≤ 4096
  /-- the calls are placed from what takeCalls has taken from the list of segments, and every
  segment of the list has been taken -/
  calls : ∃ cl taken,
    takeCalls (segmentList h (h.H * h.dh + h.Gk * h.dh) (h.Gk * h.dh)) cl [] [] = .ok taken ∧
    ((segmentList h (h.H * h.dh + h.Gk * h.dh) (h.Gk * h.dh)).any
      fun s => !taken.2.contains s.1) = false ∧
    y.calls = (taken.1.map fun c => place c.1 c.2.1 c.2.2 (h.nmin - h.ll - h.lt)).toArray

/-- The first half of the layout, for a shape with routed experts. -/
theorem admitted_of_base {h : Shape} {pc : List (List String)} {y : Lay}
    (hy : layoutBase h pc = .ok y) (hp3 : h.p3 = true) : Admitted h y := by
  unfold layoutBase at hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨e2, hy⟩ := ok_of_refuse hy
  obtain ⟨e3, hy⟩ := ok_of_refuse hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨-, -, hy⟩ := ok_of_bind hy
  obtain ⟨e6, hy⟩ := ok_of_refuse hy
  obtain ⟨e7, hy⟩ := ok_of_refuse hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨e9, hy⟩ := ok_of_refuse hy
  obtain ⟨e10, hy⟩ := ok_of_refuse hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨e18, hy⟩ := ok_of_refuse hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨-, -, hy⟩ := ok_of_bind hy
  obtain ⟨-, -, hy⟩ := ok_of_bind hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨taken, ht, hy⟩ := ok_of_bind hy
  obtain ⟨e29, hy⟩ := ok_of_refuse hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  generalize Model.Layer.gateTables h.eg h.smax h.p3 h.gcl = gt at hy
  obtain ⟨silu, fs⟩ := gt
  cases hy
  -- the test on the shape's words
  have a1 := or_false_split e2
  have a2 := or_false_split a1.1
  have a3 := or_false_split a2.1
  have a4 := a1.2
  rw [hp3, Bool.true_and] at a4
  have a5 := or_false_split a3.1
  have a6 := or_false_split a5.1
  have a7 := or_false_split a6.1
  have a8 := or_false_split a7.1
  have ll : 1 ≤ h.ll := Nat.not_lt.mp (of_decide_eq_false a8.2)
  have ffe : h.f = 2 * h.fe := by simpa using (or_false_split (or_false_split a4).1).2
  -- the test on the rows of a block
  have la : h.la = h.la - h.lt + h.lt := by
    have k := of_decide_eq_false (or_false_split e6).1
    omega
  -- the test on whole blocks
  have b1 := or_false_split e7
  have b2 := or_false_split b1.1
  have b3 := b1.2
  rw [hp3, Bool.true_and] at b3
  -- the test on the heads
  have c1 := or_false_split e9
  have c2 := or_false_split c1.1
  have c3 := or_false_split c2.1
  have c4 := or_false_split c3.1
  have c5 := or_false_split c4.1
  have c6 := or_false_split c5.1
  have Hd : h.H * h.dh = h.d := by simpa using c2.2
  have H0 : h.H ≠ 0 := by simpa using c6.1
  -- the test on the experts
  have d1 := e18
  rw [hp3, Bool.true_and] at d1
  have bd : 2 ^ (h.la - h.lt) ∣ h.d := dvd_of_bne b2.1
  have bdq : 2 ^ (h.la - h.lt) ∣ h.H * h.dh := by rw [Hd]; exact bd
  exact {
    shape := rfl
    laid := {
      S2 := rfl
      ll := ll
      Lam := rfl
      LamM := rfl
      NW := rfl
      NN := rfl
      dq := rfl
      dkv := rfl
      nqk := rfl
      bd := bd
      bf := dvd_of_bne b2.2
      bfe := dvd_of_bne b3
      bdq := bdq
      bdkv := dvd_of_bne (or_false_split e10).1
      ffe := ffe
      ten := rfl
      xb := rfl }
    la := la
    NGr := rfl
    whole := by simpa using (or_false_split e3).2
    d20 := le_of_gt_false a3.2
    f20 := le_of_gt_false a2.2
    Hd := Hd
    H0 := H0
    heads := le_of_gt_false c1.2
    NE := le_of_gt_false (or_false_split (or_false_split d1).1).2
    calls := ⟨_, taken, ht, e29, rfl⟩ }

/-- The second half of the layout changes three fields: the calls' records, which it makes from the
calls, the lookup's numbers and the columns of the matrix of counts. Its first step, the tests on
the size of each call, has refused nothing. -/
theorem look_keeps {y y' : Lay} (hy : layoutLook y = .ok y') :
    (∃ u, (y.calls.zip (y.calls.mapIdx fun q cd => y.callRecord q cd)).forM
      (fun x => y.callHeld x.1 x.2) = .ok u) ∧
    ∃ fo kbm, y' = { y with
      cl := y.calls.mapIdx fun q cd => y.callRecord q cd, fo := fo, kbm := kbm } := by
  unfold layoutLook at hy
  obtain ⟨u, hu, hy⟩ := ok_of_bind hy
  refine ⟨⟨u, hu⟩, ?_⟩
  obtain ⟨fo, -, hy⟩ := ok_of_bind hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨kbm, -, hy⟩ := ok_of_bind hy
  obtain ⟨-, -, hy⟩ := ok_of_bind hy
  obtain ⟨pub, -, hy⟩ := ok_of_bind hy
  obtain ⟨-, -, hy⟩ := ok_of_bind hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  cases hy
  exact ⟨_, _, rfl⟩

/-- Every layout that the verifier returns for a shape with routed experts is admitted. -/
theorem admitted_of_layout {h : Shape} {pc : List (List String)} {y : Lay}
    (hy : layout h pc = .ok y) (hp3 : h.p3 = true) : Admitted h y := by
  unfold layout at hy
  obtain ⟨y0, h0, h1⟩ := ok_of_bind hy
  have A := admitted_of_base h0 hp3
  have L := A.laid
  obtain ⟨-, fo, kbm, rfl⟩ := look_keeps h1
  exact {
    shape := A.shape
    laid := {
      S2 := L.S2
      ll := L.ll
      Lam := L.Lam
      LamM := L.LamM
      NW := L.NW
      NN := L.NN
      dq := L.dq
      dkv := L.dkv
      nqk := L.nqk
      bd := L.bd
      bf := L.bf
      bfe := L.bfe
      bdq := L.bdq
      bdkv := L.bdkv
      ffe := L.ffe
      ten := L.ten
      xb := L.xb }
    la := A.la
    NGr := A.NGr
    whole := A.whole
    d20 := A.d20
    f20 := A.f20
    Hd := A.Hd
    H0 := A.H0
    heads := A.heads
    NE := A.NE
    calls := A.calls }

/-- Every layout that the verifier returns for a shape with routed experts has the shape it was made
for and the plain facts of the record Laid. -/
theorem laid_of_layout {h : Shape} {pc : List (List String)} {y : Lay}
    (hy : layout h pc = .ok y) (hp3 : h.p3 = true) : y.h = h ∧ Laid y :=
  ⟨(admitted_of_layout hy hp3).shape, (admitted_of_layout hy hp3).laid⟩

/-- The calls' records of a layout that the verifier returns are made from its calls. -/
theorem cl_of_layout {h : Shape} {pc : List (List String)} {y : Lay}
    (hy : layout h pc = .ok y) : y.cl = y.calls.mapIdx fun q cd => y.callRecord q cd := by
  unfold layout at hy
  obtain ⟨y0, -, h1⟩ := ok_of_bind hy
  obtain ⟨-, fo, kbm, rfl⟩ := look_keeps h1
  rfl

/-! ## The calls' numbers of columns -/

/-- If a test is run over a list by a fold and nothing is refused, no member is refused. -/
theorem foldlM_ok {α : Type} (f : α → Except String PUnit.{1}) :
    ∀ (l : List α) (u r : PUnit.{1}), l.foldlM (fun _ a => f a) u = .ok r →
      ∀ a ∈ l, f a = .ok PUnit.unit
  | [], _, _, _, _, ha => by cases ha
  | x :: l, u, r, h, a, ha => by
    rw [List.foldlM_cons] at h
    obtain ⟨u', h1, h2⟩ := ok_of_bind h
    rcases List.mem_cons.mp ha with e | hl
    · subst e
      exact h1
    · exact foldlM_ok f l u' r h2 a hl

/-- The same for an array. -/
theorem array_forM_ok {α : Type} (f : α → Except String PUnit.{1}) (xs : Array α) {u : PUnit.{1}}
    (h : xs.forM f = .ok u) : ∀ a ∈ xs, f a = .ok PUnit.unit := by
  intro a ha
  unfold Array.forM at h
  rw [← Array.foldlM_toList] at h
  exact foldlM_ok f xs.toList _ _ h a (Array.mem_def.mp ha)

/-- The tests on the size of one call ask that the call has at least as many columns as a block has
features. -/
theorem lJ_of_callHeld {y : Lay} {cd : CallD} {c : Model.Call} (h : y.callHeld cd c = .ok ()) :
    y.ls ≤ cd.lJ := by
  unfold Lay.callHeld at h
  obtain ⟨-, h⟩ := ok_of_refuse h
  obtain ⟨-, h⟩ := ok_of_refuse h
  exact Nat.not_lt.mp (of_decide_eq_false (or_false_split (false_of_refuseIf h)).2)

/-- Every call of a layout that the verifier returns has at least as many columns as a block has
features. -/
theorem lJ_of_layout {h : Shape} {pc : List (List String)} {y : Lay}
    (hy : layout h pc = .ok y) : ∀ cd ∈ y.calls, y.ls ≤ cd.lJ := by
  unfold layout at hy
  obtain ⟨y0, -, h1⟩ := ok_of_bind hy
  obtain ⟨⟨u, hu⟩, fo, kbm, rfl⟩ := look_keeps h1
  intro cd hcd
  have hcd' : cd ∈ y0.calls := hcd
  obtain ⟨i, hi, rfl⟩ := Array.getElem_of_mem hcd'
  have hz : i < (y0.calls.zip (y0.calls.mapIdx fun q cd => y0.callRecord q cd)).size := by
    simp [hi]
  have hm := array_forM_ok _ _ hu _ (Array.getElem_mem hz)
  rw [Array.getElem_zip] at hm
  exact lJ_of_callHeld hm

/-! ## The scales -/

/-- If a test is run over a list and nothing is refused, no member is refused. -/
theorem forM_ok {α : Type} (f : α → Except String PUnit.{1}) :
    ∀ (l : List α), l.forM f = .ok PUnit.unit → ∀ a ∈ l, f a = .ok PUnit.unit
  | [], _, _, ha => by cases ha
  | x :: l, h, a, ha => by
    have h' : (f x >>= fun _ => l.forM f) = .ok PUnit.unit := h
    obtain ⟨u, h1, h2⟩ := ok_of_bind h'
    rcases List.mem_cons.mp ha with e | hl
    · subst e
      exact h1
    · exact forM_ok f l h2 a hl

/-- The tests on the record of one layer ask that the two norms' shifts are at least 17. -/
theorem K_of_heldAt {h : Shape} {s : Scales} {l : ℕ} (hy : scalesHeldAt h s l = .ok ()) :
    17 ≤ s.kl l Model.Layer.LK1 ∧ 17 ≤ s.kl l Model.Layer.LK2 := by
  unfold scalesHeldAt at hy
  obtain ⟨-, -, hy⟩ := ok_of_bind hy
  obtain ⟨-, -, hy⟩ := ok_of_bind hy
  obtain ⟨-, -, hy⟩ := ok_of_bind hy
  obtain ⟨-, -, hy⟩ := ok_of_bind hy
  obtain ⟨-, -, hy⟩ := ok_of_bind hy
  obtain ⟨-, -, hy⟩ := ok_of_bind hy
  obtain ⟨-, -, hy⟩ := ok_of_bind hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨r, eF, -⟩ := ok_of_bind hy
  simp only [List.forIn_cons, List.forIn_nil] at eF
  obtain ⟨x1, g1, eF⟩ := ok_of_bind eF
  obtain ⟨t1, g1⟩ := ok_of_refuse g1
  cases g1
  obtain ⟨x2, g2, -⟩ := ok_of_bind eF
  obtain ⟨t2, -⟩ := ok_of_refuse g2
  have k1 := of_decide_eq_false (or_false_split (or_false_split t1).1).2
  have k2 := of_decide_eq_false (or_false_split (or_false_split t2).1).2
  exact ⟨by omega, by omega⟩

/-- If the tests on the file of scales have passed, the two norms' shifts are at least 17 on every
layer of the model. Nothing is said of a layer's number from L on: there the file has no record. -/
theorem K_of_scalesHeld {h : Shape} {sc : Scales} (hs : scalesHeld h sc = .ok ()) :
    ∀ l, l < h.L → 17 ≤ sc.kl l Model.Layer.LK1 ∧ 17 ≤ sc.kl l Model.Layer.LK2 := by
  intro l hl
  exact K_of_heldAt (forM_ok (scalesHeldAt h sc) (List.range h.L) hs l (List.mem_range.mpr hl))

/-- Layer lam of group g is a layer of the model. -/
theorem group_lt {P Q L g lam : ℕ} (e : L = P * Q) (hg : g < Q) (hl : lam < P) :
    g * P + lam < L := by
  subst e
  have h1 : P * (g + 1) ≤ P * Q := Nat.mul_le_mul_left P hg
  have h2 : P * (g + 1) = g * P + P := by ring
  omega

/-- On the layers of a group of an admitted layout the two norms' shifts are at least 16. -/
theorem K_on_group {h : Shape} {y : Lay} {sc : Scales} (A : Admitted h y)
    (hs : scalesHeld h sc = .ok ()) {g : ℕ} (hg : g < y.NGr) :
    ∀ lam, lam < 2 ^ h.ll → 16 ≤ sc.kl (g * y.Lam + lam) Model.Layer.LK1 ∧
      16 ≤ sc.kl (g * y.Lam + lam) Model.Layer.LK2 := by
  intro lam hl
  have e : h.L = 2 ^ h.ll * (h.L / 2 ^ h.ll) :=
    (Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero A.whole)).symm
  have hLam : y.Lam = 2 ^ h.ll := by rw [A.laid.Lam, A.shape]
  rw [A.NGr] at hg
  rw [hLam]
  obtain ⟨k1, k2⟩ := K_of_scalesHeld hs _ (group_lt e hg hl)
  exact ⟨by omega, by omega⟩

/-- The same in the words in which fits_of_laid asks it. -/
theorem K_of_env (v : Env) {h : Shape} (A : Admitted h v.y) (hs : scalesHeld h v.sc = .ok ())
    (hg : v.g < v.y.NGr) :
    ∀ lam, lam < 2 ^ v.y.h.ll → 16 ≤ v.sc.kl (v.lay lam) Model.Layer.LK1 ∧
      16 ≤ v.sc.kl (v.lay lam) Model.Layer.LK2 := by
  intro lam hl
  rw [A.shape] at hl
  exact K_on_group A hs hg lam hl

/-! ## The segments -/

/-- The verifier's list of segments under the switches: name, kind of table, length, and whether the
segment exists only on layers with routed experts. -/
def segsRef (h : Shape) : List (String × String × ℕ × Bool) :=
  [("G", "R16", h.f, false), ("U", "R16", h.f, false), ("UT", "R16", h.f, false),
   ("QK", "R16", h.H * h.dh + h.Gk * h.dh, false), ("QKH", "R16", h.H * h.dh + h.Gk * h.dh, false),
   ("N1", "R16", h.d, false), ("N1H", "R16", h.d, false), ("N2", "R16", h.d, false),
   ("N2H", "R16", h.d, false), ("O", "R16", h.d, false), ("D", "R16", h.d, false),
   ("V", "R16", h.Gk * h.dh, false), ("XR", "R16", h.d, true), ("LR", "R16", h.NE, true),
   ("LT", "R16", h.NE, true), ("DD", "R16", h.NE, true), ("GH", "R8", h.f, false),
   ("UH", "R8", h.f, false), ("OH", "R8", h.d, false), ("DH", "R8", h.d, false),
   ("VH", "R8", h.Gk * h.dh, false), ("ROW", "R8", 198, false), ("LH", "R8", h.NE, true),
   ("SEL", "R8", h.NE, true), ("L3", "R8", h.NE, true), ("G0", "R8", h.f, false),
   ("CN1", "FC", h.d, false), ("CN2", "FC", h.d, false),
   ("CQK", "FC", h.H * h.dh + h.Gk * h.dh, false), ("CV", "FC", h.Gk * h.dh, false),
   ("CLR", "FC", h.NE, true), ("MR", "FS", 1, true), ("CG", "FS", h.f, false),
   ("F", "FL", h.f, false)]

/-- Under the switches the verifier's list of segments is that list. -/
theorem segmentList_ref (h : Shape) (S : Switches h) :
    segmentList h (h.H * h.dh + h.Gk * h.dh) (h.Gk * h.dh) = segsRef h := by
  unfold segmentList segsRef
  rw [S.p3, S.gcl, S.rcl, S.xl, S.hq, S.hv, S.ho, S.hgD, S.huD, S.hdD, S.hr]
  rfl

/-- Under the switches every member of the verifier's list of segments is one of the library's
families: it has the family's name and length, and exists on the family's layers. -/
theorem segmentList_fam (h : Shape) (S : Switches h) (q : String × String × ℕ × Bool)
    (hq : q ∈ segmentList h (h.H * h.dh + h.Gk * h.dh) (h.Gk * h.dh)) :
    ∃ fam, q.1 = segName fam ∧ q.2.2.1 = len (dimOf h) fam ∧ q.2.2.2 = isExp fam := by
  rw [segmentList_ref h S] at hq
  unfold segsRef at hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    | rfl | rfl | rfl | rfl
  exacts [⟨.G, rfl, rfl, rfl⟩, ⟨.U, rfl, rfl, rfl⟩, ⟨.UT, rfl, rfl, rfl⟩, ⟨.QK, rfl, rfl, rfl⟩,
    ⟨.QKH, rfl, rfl, rfl⟩, ⟨.N1, rfl, rfl, rfl⟩, ⟨.N1H, rfl, rfl, rfl⟩, ⟨.N2, rfl, rfl, rfl⟩,
    ⟨.N2H, rfl, rfl, rfl⟩, ⟨.O, rfl, rfl, rfl⟩, ⟨.D, rfl, rfl, rfl⟩, ⟨.V, rfl, rfl, rfl⟩,
    ⟨.XR, rfl, rfl, rfl⟩, ⟨.LR, rfl, rfl, rfl⟩, ⟨.LT, rfl, rfl, rfl⟩, ⟨.DD, rfl, rfl, rfl⟩,
    ⟨.GH, rfl, rfl, rfl⟩, ⟨.UH, rfl, rfl, rfl⟩, ⟨.OH, rfl, rfl, rfl⟩, ⟨.DH, rfl, rfl, rfl⟩,
    ⟨.VH, rfl, rfl, rfl⟩, ⟨.ROW, rfl, rfl, rfl⟩, ⟨.LH, rfl, rfl, rfl⟩, ⟨.SEL, rfl, rfl, rfl⟩,
    ⟨.L3, rfl, rfl, rfl⟩, ⟨.G0, rfl, rfl, rfl⟩, ⟨.CN1, rfl, rfl, rfl⟩, ⟨.CN2, rfl, rfl, rfl⟩,
    ⟨.CQK, rfl, rfl, rfl⟩, ⟨.CV, rfl, rfl, rfl⟩, ⟨.CLR, rfl, rfl, rfl⟩, ⟨.MR, rfl, rfl, rfl⟩,
    ⟨.CG, rfl, rfl, rfl⟩, ⟨.F, rfl, rfl, rfl⟩]

/-- Under the switches every family's name is the name of a member of the verifier's list of
segments. -/
theorem segmentList_has (h : Shape) (S : Switches h) (fam : Fam) :
    ∃ q ∈ segmentList h (h.H * h.dh + h.Gk * h.dh) (h.Gk * h.dh), q.1 = segName fam := by
  rw [segmentList_ref h S]
  have hm : segName fam ∈ (segsRef h).map (·.1) := by
    cases fam <;> simp [segsRef, segName]
  obtain ⟨q, hq, e⟩ := List.mem_map.mp hm
  exact ⟨q, hq, e⟩

/-- Every segment that one line of the calls takes is a member of the list of segments. -/
theorem takeSegments_mem (sd : List (String × String × ℕ × Bool)) (kind : String) :
    ∀ (ns seen : List String) (r : List SegAsk × List String),
      takeSegments sd kind ns seen = .ok r →
      ∀ a ∈ r.1, ∃ s ∈ sd, a = (s.1, s.2.2.1, s.2.2.2)
  | [], _, _, h, _, ha => by
    cases h
    cases ha
  | n :: ns, seen, r, h, a, ha => by
    rw [takeSegments] at h
    cases hf : sd.find? (fun s => s.1 == n) with
    | none =>
      rw [hf] at h
      cases h
    | some s =>
      rw [hf] at h
      obtain ⟨-, h⟩ := ok_of_refuse h
      obtain ⟨r', h1, h2⟩ := ok_of_bind h
      cases h2
      rcases List.mem_cons.mp ha with e | ha'
      · exact ⟨s, List.mem_of_find?_eq_some hf, e⟩
      · exact takeSegments_mem sd kind ns (n :: seen) r' h1 a ha'

/-- Every segment of every call that the lines of the calls give is a member of the list of
segments. -/
theorem takeCalls_mem (sd : List (String × String × ℕ × Bool)) :
    ∀ (lines : List (List String)) (names seen : List String)
      (r : List (String × String × List SegAsk) × List String),
      takeCalls sd lines names seen = .ok r →
      ∀ c ∈ r.1, ∀ a ∈ c.2.2, ∃ s ∈ sd, a = (s.1, s.2.2.1, s.2.2.2)
  | [], _, _, _, h, _, hc => by
    cases h
    cases hc
  | ln :: rest, names, seen, r, h, c, hc => by
    rcases ln with _ | ⟨name, _ | ⟨kind, _ | ⟨s, more⟩⟩⟩
    · cases h
    · cases h
    · cases h
    · have h : (do
          refuseIf (names.contains name) "policy-call-list"
          refuseIf (["V", "a", "b", "E"].contains name) "policy-call-list"
          let a ← takeSegments sd kind (s :: more) seen
          let r ← takeCalls sd rest (name :: names) a.2
          pure ((name, kind, a.1) :: r.1, r.2)) = .ok r := h
      obtain ⟨-, h⟩ := ok_of_refuse h
      obtain ⟨-, h⟩ := ok_of_refuse h
      obtain ⟨a', h1, h⟩ := ok_of_bind h
      obtain ⟨r', h2, h⟩ := ok_of_bind h
      cases h
      rcases List.mem_cons.mp hc with e | hc'
      · subst e
        exact fun a ha => takeSegments_mem sd kind (s :: more) seen a' h1 a ha
      · exact takeCalls_mem sd rest (name :: names) a'.2 r' h2 c hc'

/-- A placed segment has the name, the length and the layers of one of the segments that were to be
placed. -/
theorem place_segs (name kind : String) (asks : List SegAsk) (floorLg : ℕ) (s : Seg)
    (hs : s ∈ (place name kind asks floorLg).segs) :
    ∃ a ∈ asks, s.name = a.1 ∧ s.n = a.2.1 ∧ s.moe = a.2.2 := by
  have hs' : s ∈ asks.zipIdx.map fun x =>
      ({ name := x.1.1, n := x.1.2.1,
         pos := Model.columnsOf (Model.piecesBelow (asks.map (·.2.1)) (topBit + 1) 0).1 x.2 x.1.2.1,
         moe := x.1.2.2 } : Seg) := hs
  obtain ⟨⟨a, i⟩, hx, rfl⟩ := List.mem_map.mp hs'
  exact ⟨a, (mem_zipIdx_getD (fun x : SegAsk => x.2.1) asks 0 a i hx).1, rfl, rfl, rfl⟩

/-- The length of every family is below the bound of the placing rule. -/
theorem len_lt {h : Shape} {y : Lay} (A : Admitted h y) (fam : Fam) :
    len (dimOf h) fam < 2 ^ (topBit + 1) := by
  have t : (2 : ℕ) ^ (topBit + 1) = 2 ^ 41 := rfl
  rw [t]
  have hd := A.d20
  have hf := A.f20
  have hn := A.NE
  have hq : h.H * h.dh ≤ 2 ^ 20 := by rw [A.Hd]; exact hd
  have h1 : 1 ≤ h.H := Nat.pos_of_ne_zero A.H0
  have hdh : h.dh ≤ 2 ^ 20 := by
    have e : 1 * h.dh ≤ h.H * h.dh := Nat.mul_le_mul_right h.dh h1
    omega
  have hG : h.Gk ≤ 64 := by have := A.heads; omega
  have hkv : h.Gk * h.dh ≤ 64 * 2 ^ 20 := Nat.mul_le_mul hG hdh
  have lf : h.f < 2 ^ 41 := by omega
  have ld : h.d < 2 ^ 41 := by omega
  have lkv : h.Gk * h.dh < 2 ^ 41 := by omega
  have lqk : h.H * h.dh + h.Gk * h.dh < 2 ^ 41 := by omega
  have ln : h.NE < 2 ^ 41 := by omega
  cases fam <;> first
    | exact lf | exact ld | exact lkv | exact lqk | exact ln
    | exact (by norm_num : (2 * 99 : ℕ) < 2 ^ 41) | exact (by norm_num : (1 : ℕ) < 2 ^ 41)

/-- The length of a family that is read by blocks is a whole number of blocks. -/
theorem len_dvd {h : Shape} {y : Lay} (A : Admitted h y) (fam : Fam) (hb : byBlocks fam = true) :
    2 ^ y.ls ∣ len (dimOf h) fam := by
  have L := A.laid
  have e := A.shape
  subst e
  rw [← L.S2]
  have hqk : y.S2 ∣ y.h.H * y.h.dh + y.h.Gk * y.h.dh := Nat.dvd_add L.bdq L.bdkv
  cases fam <;> first
    | exact L.bf | exact L.bd | exact L.bdkv | exact hqk | exact absurd hb (by decide)

/-- Under the switches, every segment of every call of an admitted layout holds one of the library's
families: it has the family's name, length and layers, one column for each entry, and, if the family
is read by blocks, columns that are aligned on blocks. These are the five fields of the record
SegFits of Johnson/Road/FormsKeysCall.lean. -/
theorem segs_of_admitted {h : Shape} {y : Lay} (A : Admitted h y) (S : Switches h) :
    ∀ cd ∈ y.calls, ∀ s ∈ cd.segs, ∃ fam, s.name = segName fam ∧ s.n = len (dimOf h) fam ∧
      s.moe = isExp fam ∧ s.pos.size = s.n ∧ (byBlocks fam = true → Aligned s y.ls cd.lJ) := by
  intro cd hcd s hs
  obtain ⟨cl, taken, ht, -, hc⟩ := A.calls
  rw [hc] at hcd
  have hcd' : cd ∈ taken.1.map fun c => place c.1 c.2.1 c.2.2 (h.nmin - h.ll - h.lt) :=
    Array.mem_def.mp hcd
  obtain ⟨c, hcm, rfl⟩ := List.mem_map.mp hcd'
  obtain ⟨a, ha, e1, e2, e3⟩ := place_segs _ _ _ _ s hs
  obtain ⟨q, hq, rfl⟩ := takeCalls_mem _ cl [] [] taken ht c hcm a ha
  obtain ⟨fam, f1, f2, f3⟩ := segmentList_fam h S q hq
  have hn : s.n = len (dimOf h) fam := e2.trans f2
  have hlt : s.n < 2 ^ (topBit + 1) := by rw [hn]; exact len_lt A fam
  refine ⟨fam, e1.trans f1, hn, e3.trans f3,
    (place_aligned _ _ _ _ 0 s hs (by simp) hlt).size, fun hb => ?_⟩
  refine place_aligned _ _ _ _ y.ls s hs ?_ hlt
  rw [hn]
  exact len_dvd A fam hb

/-- The same of every layout that the verifier returns. -/
theorem segs_of_layout {h : Shape} {pc : List (List String)} {y : Lay}
    (hy : layout h pc = .ok y) (S : Switches h) :
    ∀ cd ∈ y.calls, ∀ s ∈ cd.segs, ∃ fam, s.name = segName fam ∧ s.n = len (dimOf h) fam ∧
      s.moe = isExp fam ∧ s.pos.size = s.n ∧ (byBlocks fam = true → Aligned s y.ls cd.lJ) :=
  segs_of_admitted (admitted_of_layout hy S.p3) S

#print axioms laid_of_layout
#print axioms cl_of_layout
#print axioms lJ_of_layout
#print axioms K_of_scalesHeld
#print axioms K_of_env
#print axioms segs_of_layout
#print axioms segmentList_has

end OnBytes.Road
