-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/FormsKeysCap.lean: a tree of the lookup may hold as many keys as there are positions,
for every layout that the verifier returns.

Johnson/Road/FormsKeysVec.lean shows that the library's quantity KF of a lookup call is the
multilinear extension of the call's key vector at the library's point of the call, for sizes D with
D.lT ≤ D.cap. The sizes dimOf h of Johnson/Road/FormsKeysFits.lean have cap = 0. The record Sized
leaves cap free. This file shows that sizes which agree with the shape and take the verifier's cap
on a tree's depth, lidb, for the library's cap meet the hypothesis, whenever layout returns a layout
for the shape.

Main theorems.
 - shape_dT: the depth of a tree that Forest.shape returns is the least of the cap and the calls'
   logarithms of their numbers of keys, as its text says.
 - dT_of_layout: in a layout that layout returns, la ≤ fo.dT ≤ lidb, and fo.dT is that least value
   over the layout's own records of the calls.
 - cap_of_layout: lt ≤ lidb.
 - hcap_of_layout: D.lT ≤ D.cap for all sizes D with Sized h D and D.cap = h.lidb; sized_dimC: the
   sizes dimC h are such sizes.
 - ext_keyVec_KF_of_layout, KFP_eq_KF_of_layout: two theorems of FormsKeysVec.lean at such sizes.

What is compared with what. shape_dT, dT_of_layout, cap_of_layout: the verifier's functions with
themselves. The last two theorems are on objects of the library, at sizes that are tied to the
verifier's shape by Sized and by cap = lidb.

What is not claimed. That the library's depth of a tree Dk D is the verifier's fo.dT is not shown
here: both are written as the least of a cap and the calls' sizes, but the calls' sizes are not
compared here; Johnson/Road/FormsKeysShape.lean shows it for a layout whose calls are the library's.
That layout returns for some shape is no theorem: the "#guard" at the end evaluates layout on the
made-up shape hR8 of Johnson/Road/FormsKeysRun8.lean and tests the three inequalities there. The
program does not import this file.
-/
import Johnson.Road.FormsKeysAddr
import Johnson.Road.FormsKeysVec
import Johnson.Road.FormsKeysRun8

set_option autoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road

open OnBytes.Model (refuseIf Call)
open OnBytes.Model.Layer (Lay Shape layout layoutBase layoutLook)
open Inst.Model (Scl Tables)
open Inst.Model.FFSeg (Dim Cell LW aC keyVec zc KF)

/-! ## The depth of a tree -/

/-- A least value that a fold computes from a start is at most the start. -/
theorem foldl_min_le_start (calls : Array Call) (lid : ℕ) :
    calls.foldl (fun m c => min m c.n) lid ≤ lid :=
  Array.foldl_induction (motive := fun _ m => m ≤ lid) (Nat.le_refl _)
    fun _ _ hb => Nat.le_trans (Nat.min_le_left _ _) hb

/-- If "refuse under a condition, then go on" returns a value, the condition is false and what
follows returns the value. -/
theorem ok_of_jp {c : Prop} [Decidable c] {e : String} {β : Type}
    {jp : PUnit.{1} → Except String β} {y : β}
    (h : (if c then (throw e >>= jp) else (pure PUnit.unit >>= jp)) = .ok y) :
    ¬ c ∧ jp PUnit.unit = .ok y := by
  by_cases hc : c
  · rw [if_pos hc] at h
    have h' : (Except.error e : Except String β) = .ok y := h
    cases h'
  · rw [if_neg hc] at h
    exact ⟨hc, h⟩

/-- The depth of a tree that Forest.shape returns: the least of the cap and the calls' logarithms of
their numbers of keys. -/
theorem shape_dT {calls : Array Call} {lid : ℕ} {fo : Model.Forest.Shape}
    (h : Model.Forest.shape calls lid = .ok fo) :
    fo.dT = calls.foldl (fun m c => min m c.n) lid := by
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
  rfl

/-- The second half of the layout has taken the lookup's numbers from Forest.shape, on the calls'
records and the shape's cap, and has found a tree at least as deep as a block is high. It keeps the
depth. -/
theorem look_dT {y y' : Lay} (hy : layoutLook y = .ok y') :
    ∃ fo0, Model.Forest.shape (y.calls.mapIdx fun q cd => y.callRecord q cd) y.h.lidb = .ok fo0 ∧
      y.h.la ≤ fo0.dT ∧ y'.fo.dT = fo0.dT := by
  unfold layoutLook at hy
  obtain ⟨u, hu, hy⟩ := ok_of_bind hy
  obtain ⟨fo, hfo, hy⟩ := ok_of_bind hy
  obtain ⟨e, hy⟩ := ok_of_refuse hy
  obtain ⟨kbm, -, hy⟩ := ok_of_bind hy
  obtain ⟨-, -, hy⟩ := ok_of_bind hy
  obtain ⟨pub, -, hy⟩ := ok_of_bind hy
  obtain ⟨-, -, hy⟩ := ok_of_bind hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  cases hy
  exact ⟨fo, hfo, Nat.not_lt.mp (of_decide_eq_false e), rfl⟩

/-- The first half of the layout keeps the shape, whatever the profile. -/
theorem base_shape {h : Shape} {pc : List (List String)} {y : Lay}
    (hy : layoutBase h pc = .ok y) : y.h = h := by
  unfold layoutBase at hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨-, -, hy⟩ := ok_of_bind hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨-, -, hy⟩ := ok_of_bind hy
  obtain ⟨-, -, hy⟩ := ok_of_bind hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨taken, -, hy⟩ := ok_of_bind hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  generalize Model.Layer.gateTables h.eg h.smax h.p3 h.gcl = gt at hy
  obtain ⟨silu, fs⟩ := gt
  cases hy
  rfl

/-- The layout keeps the shape, whatever the profile. -/
theorem layout_shape {h : Shape} {pc : List (List String)} {y : Lay}
    (hy : layout h pc = .ok y) : y.h = h := by
  unfold layout at hy
  obtain ⟨y0, h0, h1⟩ := ok_of_bind hy
  have e := base_shape h0
  obtain ⟨-, fo, kbm, rfl⟩ := look_keeps h1
  exact e

/-- In a layout that the verifier returns a tree is at least as deep as a block is high and at most
as deep as the cap, and its depth is the least of the cap and the logarithms of the numbers of keys
in the layout's records of the calls. -/
theorem dT_of_layout {h : Shape} {pc : List (List String)} {y : Lay}
    (hy : layout h pc = .ok y) :
    h.la ≤ y.fo.dT ∧ y.fo.dT ≤ h.lidb ∧ y.fo.dT = y.cl.foldl (fun m c => min m c.n) h.lidb := by
  unfold layout at hy
  obtain ⟨y0, h0, h1⟩ := ok_of_bind hy
  have e0 := base_shape h0
  obtain ⟨fo0, hfo, hla, hd⟩ := look_dT h1
  have hdT := shape_dT hfo
  obtain ⟨-, fo, kbm, rfl⟩ := look_keeps h1
  rw [e0] at hla hdT
  refine ⟨by rw [hd]; exact hla, ?_, hd.trans hdT⟩
  rw [hd, hdT]
  exact foldl_min_le_start _ _

/-- For every layout that the verifier returns, the cap on a tree's depth is at least the logarithm
of the number of positions. -/
theorem cap_of_layout {h : Shape} {pc : List (List String)} {y : Lay}
    (hy : layout h pc = .ok y) : h.lt ≤ h.lidb := by
  obtain ⟨a, b, -⟩ := dT_of_layout hy
  have c := (laid2_of_layout hy).lt_la
  rw [layout_shape hy] at c
  omega

/-! ## Sizes of the library with the verifier's cap -/

/-- The sizes dimA h with the verifier's cap on a tree's depth for the library's. -/
def dimC (h : Shape) : Dim := { dimA h with cap := h.lidb }

/-- They agree with the shape, and their cap is the verifier's. -/
theorem sized_dimC (h : Shape) : Sized h (dimC h) ∧ (dimC h).cap = h.lidb :=
  ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl⟩

section AtLayout

variable {h : Shape} {pc : List (List String)} {y : Lay} (hy : layout h pc = .ok y) {D : Dim}
  (Z : Sized h D) (hc : D.cap = h.lidb)

include hy Z hc in
/-- Sizes that agree with the shape and have the verifier's cap meet the hypothesis of the theorems
of Johnson/Road/FormsKeysVec.lean at the library's own point. -/
theorem hcap_of_layout : D.lT ≤ D.cap := by
  rw [Z.lT, hc]
  exact cap_of_layout hy

variable {K : Type} [Field K] [scl : Scl] (t : Cell → K) (tb : Tables) (L0 : ℕ) (w : ℕ → LW K)

include hy Z hc in
/-- At such sizes the library's KF of call c is the multilinear extension of the library's key
vector of the call at the library's point of the call. -/
theorem ext_keyVec_KF_of_layout (z : ℕ → K) (c : Fin 8) :
    Blocks.ext (aC D c) (keyVec D t tb L0 w c) (zc D z c) = KF D t tb L0 w z c :=
  ext_keyVec_KF D t tb L0 w (hcap_of_layout hy Z hc) z c

include hy Z hc in
/-- At such sizes KFP at a point that agrees with the library's point of the call on its aC D c
coordinates is the library's KF. -/
theorem KFP_eq_KF_of_layout {z ζ : ℕ → K} {c : Fin 8} (hz : ∀ j < aC D c, ζ j = zc D z c j) :
    KFP D t tb L0 w c ζ = KF D t tb L0 w z c :=
  KFP_eq_KF D t tb L0 w (hcap_of_layout hy Z hc) hz

end AtLayout

/-! ## A run on made-up numbers -/

/- on the shape hR8 with its eight calls: layout returns, and lt ≤ la ≤ the depth of a tree ≤ the
cap -/
#guard (match layout hR8 pcR8 with
  | .ok y => hR8.lt ≤ hR8.la && hR8.la ≤ y.fo.dT && y.fo.dT ≤ hR8.lidb && hR8.lt ≤ hR8.lidb
  | .error _ => false)

#print axioms shape_dT
#print axioms dT_of_layout
#print axioms cap_of_layout
#print axioms sized_dimC
#print axioms hcap_of_layout
#print axioms ext_keyVec_KF_of_layout
#print axioms KFP_eq_KF_of_layout

end OnBytes.Road
