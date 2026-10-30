-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/HeadCols.lean: the form of a lookup call's key vector is worth the multilinear
extension of one function on the call's columns and the positions.

A lookup call of the output head's sub-proof has 2^lJ columns. Each segment of the call lists one
column for each of its entries; the other columns hold the padding key. The verifier marks the
listed columns and refuses if a column is listed twice or lies outside the call (markColumns in
OnBytes/Model/HeadForms.lean). This file shows that the marks cut the columns in two: a sum over all
columns is the sum over the columns without a mark plus the sums over the segments' entries. With
Johnson/Road/HeadCall.lean it follows that the call's form is worth the extension, at the call's key
point, of any function that has a segment's keys in the segment's columns and the padding key in the
columns without a mark.

Main definitions: markedSum; KeyFn (what is asked of the function).
Main theorems: marked_step, fold_marks, markColumns_sum, marks_sum, cols_split; ext_cols (an
extension over columns and positions, column by column); call_cols; keyForm_ext.

What is not claimed. That a function with the property KeyFn exists is not shown here. What the
forms of the segments are worth is a hypothesis. Nothing is said about what a lookup shows. The
program does not import this file.
-/
import Johnson.Road.HeadCall

set_option autoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.Hd

open Finset
open OnBytes.Model (Reading World Aff Fork SubM)

section Marks

variable {K : Type} [Field K]

/-- The sum of F over the columns below J that bear a mark other than 0. -/
def markedSum (w : Array ℕ) (J : ℕ) (F : ℕ → K) : K :=
  ∑ j ∈ range J, if w.getD j 0 = 0 then 0 else F j

/-- Writing at one index leaves the others. -/
theorem getD_set_ne (a : Array ℕ) {i j : ℕ} (h : i ≠ j) (x : ℕ) :
    (a.setIfInBounds i x).getD j 0 = a.getD j 0 := by
  simp [Array.getD_eq_getD_getElem?, h]

/-- What has been written at an index within the array is read there. -/
theorem getD_set_self (a : Array ℕ) {i : ℕ} (h : i < a.size) (x : ℕ) :
    (a.setIfInBounds i x).getD i 0 = x := by
  simp [Array.getD_eq_getD_getElem?, h]

/-- Marking a column that had no mark adds the column's term. -/
theorem marked_step {w : Array ℕ} {J p m : ℕ} (hs : w.size = J) (hp : p < w.size)
    (h0 : w.getD p 1 = 0) (hm : m ≠ 0) (F : ℕ → K) :
    (w.set! p m).size = J ∧ markedSum (w.set! p m) J F = markedSum w J F + F p := by
  rw [Array.set!_eq_setIfInBounds]
  refine ⟨by rw [Array.size_setIfInBounds]; exact hs, ?_⟩
  have h00 : w.getD p 0 = 0 := by simpa [Array.getD, hp] using h0
  have e : ∀ j, (if (w.setIfInBounds p m).getD j 0 = 0 then (0 : K) else F j) =
      (if w.getD j 0 = 0 then 0 else F j) + if j = p then F p else 0 := by
    intro j
    by_cases hj : j = p
    · subst hj
      rw [getD_set_self w hp m, if_neg hm, if_pos h00, if_pos rfl, zero_add]
    · rw [getD_set_ne w (fun h => hj h.symm) m, if_neg hj, add_zero]
  unfold markedSum
  rw [sum_congr rfl fun j _ => e j, sum_add_distrib]
  congr 1
  have s := Finset.sum_ite_eq' (range J) p fun _ => F p
  rw [s, if_pos (mem_range.mpr (hs ▸ hp))]

/-- Marking the columns pos 0, ..., pos (n - 1) one after the other, each with a mark other than 0:
if no step refuses, all these columns lie below J and their terms are added. -/
theorem fold_marks (J : ℕ) (pos mk : ℕ → ℕ) (hmk : ∀ x, mk x ≠ 0) (F : ℕ → K) :
    ∀ (n : ℕ) (w w' : Array ℕ), w.size = J →
      (List.range n).foldlM (fun w x =>
        if pos x < w.size && w.getD (pos x) 1 == 0 then some (w.set! (pos x) (mk x)) else none)
        w = some w' →
      w'.size = J ∧ markedSum w' J F = markedSum w J F + ∑ x ∈ range n, F (pos x) ∧
        ∀ x, x < n → pos x < J
  | 0, w, w', hs, h => by
    have e : w = w' := by simpa using h
    subst e
    exact ⟨hs, by simp, fun x hx => absurd hx (Nat.not_lt_zero x)⟩
  | n + 1, w, w', hs, h => by
    rw [List.range_succ, List.foldlM_append] at h
    obtain ⟨w1, h1, h2⟩ := bind_some h
    obtain ⟨s1, m1, p1⟩ := fold_marks J pos mk hmk F n w w1 hs h1
    rw [List.foldlM_cons] at h2
    obtain ⟨w2, h3, h4⟩ := bind_some h2
    have e2 : w2 = w' := by simpa using h4
    subst e2
    by_cases hc : (pos n < w1.size && w1.getD (pos n) 1 == 0) = true
    · rw [if_pos hc] at h3
      have e3 := Option.some.inj h3
      subst e3
      have hc' := (Bool.and_eq_true _ _ ▸ hc)
      have c1 : pos n < w1.size := of_decide_eq_true hc'.1
      have c2 : w1.getD (pos n) 1 = 0 := beq_iff_eq.mp hc'.2
      obtain ⟨s2, m2⟩ := marked_step s1 c1 c2 (hmk n) F
      refine ⟨s2, ?_, ?_⟩
      · rw [m2, m1, Finset.sum_range_succ, add_assoc]
      · intro x hx
        rcases Nat.lt_succ_iff_lt_or_eq.mp hx with h5 | h5
        · exact p1 x h5
        · rw [h5, ← s1]
          exact c1
    · rw [if_neg hc] at h3
      cases h3

/-- The columns of one segment. -/
theorem markColumns_sum {R : Model.Head.Run} {w w' : Array ℕ} {g : Model.Seg} {J : ℕ}
    (hs : w.size = J) (h : Model.Head.markColumns R w g = some w') (F : ℕ → K) :
    w'.size = J ∧
      markedSum w' J F = markedSum w J F + ∑ x ∈ range g.n, F (g.pos.getD x 0) ∧
      ∀ x, x < g.n → g.pos.getD x 0 < J :=
  fold_marks J (fun x => g.pos.getD x 0)
    (fun x => if Model.Head.perEntry g.name && Model.Head.firstEntry R.L g.name + x ≥ R.h.V
      then 2 else 1)
    (fun x => by dsimp only; split <;> decide) F g.n w w' hs h

/-- The columns of the segments of a list. -/
theorem marks_sum {R : Model.Head.Run} {J : ℕ} (F : ℕ → K) :
    ∀ (l : List Model.Seg) (w w' : Array ℕ), w.size = J →
      l.foldlM (fun w g => Model.Head.markColumns R w g) w = some w' →
      w'.size = J ∧
        markedSum w' J F = markedSum w J F +
          (l.map fun g => ∑ x ∈ range g.n, F (g.pos.getD x 0)).sum ∧
        ∀ g ∈ l, ∀ x, x < g.n → g.pos.getD x 0 < J
  | [], w, w', hs, h => by
    have e : w = w' := by simpa using h
    subst e
    exact ⟨hs, by simp, fun g hg => absurd hg (List.not_mem_nil)⟩
  | g :: l, w, w', hs, h => by
    rw [List.foldlM_cons] at h
    obtain ⟨w1, h1, h2⟩ := bind_some h
    obtain ⟨s1, m1, p1⟩ := markColumns_sum hs h1 F
    obtain ⟨s2, m2, p2⟩ := marks_sum F l w1 w' s1 h2
    refine ⟨s2, ?_, ?_⟩
    · rw [m2, m1, List.map_cons, List.sum_cons, add_assoc]
    · intro g' hg'
      rcases List.mem_cons.mp hg' with rfl | h3
      · exact p1
      · exact p2 g' h3

/-- The marks cut the columns in two: a sum over all columns of a call is the sum over the columns
without a mark plus the sums over the entries of the segments. -/
theorem cols_split {R : Model.Head.Run} {J : ℕ} {l : List Model.Seg} {w : Array ℕ}
    (h : l.foldlM (fun w g => Model.Head.markColumns R w g) (Array.replicate J 0) = some w)
    (F : ℕ → K) :
    ∑ j ∈ range J, F j = (∑ j ∈ range J, if w.getD j 0 = 0 then F j else 0) +
      (l.map fun g => ∑ x ∈ range g.n, F (g.pos.getD x 0)).sum := by
  obtain ⟨_, m, _⟩ := marks_sum (J := J) F l (Array.replicate J 0) w (by simp) h
  have z : markedSum (Array.replicate J 0) J F = 0 := by
    unfold markedSum
    refine sum_eq_zero fun j hj => ?_
    have e : (Array.replicate J 0).getD j 0 = 0 := by
      simp [Array.getD, mem_range.mp hj]
    rw [if_pos e]
  rw [z, zero_add] at m
  rw [← m]
  unfold markedSum
  rw [← sum_add_distrib]
  refine sum_congr rfl fun j _ => ?_
  split
  · rw [add_zero]
  · rw [zero_add]

end Marks

section Ext

variable {K : Type} [Field K]

/-- An extension over 2^lJ columns and 2^lt positions, column by column. The index of column j and
position i is j 2^lt + i; the point has the columns' coordinates first. -/
theorem ext_cols (lJ lt : ℕ) (f : ℕ → ℕ → K) (p : ℕ → K) :
    Blocks.ext (lJ + lt) (fun X => f (X / 2 ^ lt) (X % 2 ^ lt)) p =
      ∑ j ∈ range (2 ^ lJ), Blocks.eqN lJ 0 p j * Blocks.ext lt (f j) fun k => p (lJ + k) := by
  unfold Blocks.ext
  rw [pow_add, sum_blocks]
  refine sum_congr rfl fun j _ => ?_
  rw [mul_sum]
  refine sum_congr rfl fun i hi => ?_
  have hi' : i < 2 ^ lt := mem_range.mp hi
  have hpos : 0 < 2 ^ lt := by positivity
  have d1 : (j * 2 ^ lt + i) / 2 ^ lt = j := by
    rw [Nat.mul_comm, Nat.mul_add_div hpos, Nat.div_eq_of_lt hi', Nat.add_zero]
  have d2 : (j * 2 ^ lt + i) % 2 ^ lt = i := by
    rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt hi']
  beta_reduce
  rw [d1, d2, Blocks.eqN_append' lJ lt 0 p j hi', Nat.zero_add, eqN_shift' lt lJ p i]
  ring

variable {ρ : Reading K} {W : World K}

/-- What is asked of a function f on columns and positions, for the call with the segments l, the
marks w and J columns: in the column of entry x of a segment it has that segment's keys kv at x, and
in a column without a mark it is the padding key. -/
structure KeyFn (l : List Model.Seg) (w : Array ℕ) (J : ℕ) (kv : String → ℕ → ℕ → K) (pad : K)
    (f : ℕ → ℕ → K) : Prop where
  seg : ∀ g ∈ l, ∀ x, x < g.n → f (g.pos.getD x 0) = kv g.name x
  pad : ∀ j, j < J → w.getD j 0 = 0 → f j = fun _ => pad

/-- The padding's part and the segments' parts make up the sum over all columns. e: the weights of
the columns. -/
theorem call_cols {R : Model.Head.Run} {J lt : ℕ} {l : List Model.Seg} {w : Array ℕ}
    (h : l.foldlM (fun w g => Model.Head.markColumns R w g) (Array.replicate J 0) = some w)
    {kv : String → ℕ → ℕ → K} {pad : K} {f : ℕ → ℕ → K} (Kf : KeyFn l w J kv pad f)
    (e : Array E) (u : ℕ → K) :
    pad * padSum ρ e w J +
        (l.map fun g => wsum (fun x => ρ.val (e.getD (g.pos.getD x 0) zeroE)) lt u g.n
          (kv g.name)).sum =
      ∑ j ∈ range J, ρ.val (e.getD j zeroE) * Blocks.ext lt (f j) u := by
  rw [cols_split h fun j => ρ.val (e.getD j zeroE) * Blocks.ext lt (f j) u]
  congr 1
  · unfold padSum
    rw [mul_sum]
    refine sum_congr rfl fun j hj => ?_
    split
    · rename_i h0
      rw [Kf.pad j (mem_range.mp hj) h0, Blocks.ext_const, mul_comm]
    · rw [mul_zero]
  · refine congrArg List.sum (List.map_congr_left fun g hg => ?_)
    unfold wsum
    exact sum_congr rfl fun x hx => by rw [Kf.seg g hg x (mem_range.mp hx)]

/-- The weight of an entry of a segment is the weight of the entry's column. -/
theorem ewFrom_getD (e : Array E) (g : Model.Seg) {x : ℕ} (hx : x < g.pos.size) :
    (Model.Layer.Env.ewFrom e g).getD x zeroE = e.getD (g.pos.getD x 0) zeroE := by
  unfold Model.Layer.Env.ewFrom
  exact getD_map_lt _ _ hx zeroE 0

/-- The form of call number q's key vector against one function on columns and positions. p: the
call's key point, the columns' coordinates first. kv: the keys of each segment. dl g: what the form
of the segment g is worth beyond the weighted extensions of its keys. If f has the segments' keys in
their columns and the padding key in the columns without a mark, the call's form is worth the
extension of f at p, plus the first slot of a sumcheck in the call with the segment NF, plus the
dl g. -/
theorem keyForm_ext {R : Model.Head.Run} {q : ℕ} {laid : Array ℕ} {F G : Fork} {C D : Ctx}
    {x : Aff × Array ℕ} (kv : String → ℕ → ℕ → K) (dl : Model.Seg → K) {f : ℕ → ℕ → K}
    {p : ℕ → K} (hJ : (R.L.calls.getD q default).J = 2 ^ (R.L.calls.getD q default).lJ)
    (hz : (Model.Head.zjOf R.L R.x.g1 q).size = (R.L.calls.getD q default).lJ)
    (hp : ∀ k, k < (R.L.calls.getD q default).lJ → pt ρ (Model.Head.zjOf R.L R.x.g1 q) k = p k)
    (hLine : ∀ g ∈ (R.L.calls.getD q default).segs, ∀ a G' D',
      Ok (Model.Head.LINE R g.name) F C a G' D' → G' = F ∧ D' = C ∧ a.value ρ W =
        wsum (fun y => ρ.val ((Model.eqTab (Model.Head.zjOf R.L R.x.g1 q)).getD
          (g.pos.getD y 0) zeroE)) R.h.lt (fun k => p ((R.L.calls.getD q default).lJ + k)) g.n
          (kv g.name) + dl g)
    (Kf : ∀ w, (R.L.calls.getD q default).segs.foldlM
        (fun w g => Model.Head.markColumns R w g)
        (Array.replicate (R.L.calls.getD q default).J 0) = some w →
      KeyFn (R.L.calls.getD q default).segs w (R.L.calls.getD q default).J kv
        (ρ.val (ofF ((R.L.cl.getD q default).tauAt (R.L.cl.getD q default).t0))) f)
    (h : Ok (Model.Head.keyForm R q laid) F C x G D) :
    G = F ∧ D = C ∧ x.1.value ρ W =
      Blocks.ext ((R.L.calls.getD q default).lJ + R.h.lt)
          (fun X => f (X / 2 ^ R.h.lt) (X % 2 ^ R.h.lt)) p +
        (if q = R.x.qN then W.slot R.x.tN.sCl else 0) +
        ((R.L.calls.getD q default).segs.map dl).sum := by
  obtain ⟨e1, e2, w, hw, hv⟩ := keyForm_value _ hLine h
  refine ⟨e1, e2, ?_⟩
  have s1 : ((R.L.calls.getD q default).segs.map fun g =>
      wsum (fun y => ρ.val ((Model.eqTab (Model.Head.zjOf R.L R.x.g1 q)).getD
        (g.pos.getD y 0) zeroE)) R.h.lt (fun k => p ((R.L.calls.getD q default).lJ + k)) g.n
        (kv g.name) + dl g).sum =
      ((R.L.calls.getD q default).segs.map fun g =>
        wsum (fun y => ρ.val ((Model.eqTab (Model.Head.zjOf R.L R.x.g1 q)).getD
          (g.pos.getD y 0) zeroE)) R.h.lt (fun k => p ((R.L.calls.getD q default).lJ + k)) g.n
          (kv g.name)).sum + ((R.L.calls.getD q default).segs.map dl).sum :=
    List.sum_map_add
  have s2 := call_cols (ρ := ρ) (lt := R.h.lt) hw (Kf w hw)
    (Model.eqTab (Model.Head.zjOf R.L R.x.g1 q))
    (fun k => p ((R.L.calls.getD q default).lJ + k))
  have s3 : ∑ j ∈ range (R.L.calls.getD q default).J,
      ρ.val ((Model.eqTab (Model.Head.zjOf R.L R.x.g1 q)).getD j zeroE) *
        Blocks.ext R.h.lt (f j) (fun k => p ((R.L.calls.getD q default).lJ + k)) =
      Blocks.ext ((R.L.calls.getD q default).lJ + R.h.lt)
        (fun X => f (X / 2 ^ R.h.lt) (X % 2 ^ R.h.lt)) p := by
    rw [ext_cols, hJ]
    refine sum_congr rfl fun j hj => ?_
    have hj' : j < 2 ^ (Model.Head.zjOf R.L R.x.g1 q).size := by
      rw [hz]
      exact mem_range.mp hj
    have e3 : Blocks.eqN (R.L.calls.getD q default).lJ 0
        (pt ρ (Model.Head.zjOf R.L R.x.g1 q)) j =
        Blocks.eqN (R.L.calls.getD q default).lJ 0 p j :=
      eqN_congr' _ 0 (fun k hk => by rw [Nat.zero_add]; exact hp k hk) j
    rw [eqTab_value ρ _ j hj', hz, e3]
  rw [hv, s1, ← s3, ← s2]
  ring

end Ext

#print axioms cols_split
#print axioms ext_cols
#print axioms call_cols
#print axioms keyForm_ext

end OnBytes.Road.Hd
