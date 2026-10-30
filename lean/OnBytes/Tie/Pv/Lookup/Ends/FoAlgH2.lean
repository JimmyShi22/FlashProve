-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Ends/FoAlgH2.lean.
The head's key forms: the affine part of the named proposition, cut down to one law a segment.

Fo.AlgHAff (OnBytes/Tie/Pv/Lookup/Forest/FoAlgH.lean) speaks of a call's whole key form and whole
key vector. This file cuts both by the call's columns. What is left to show speaks of one segment's
form (Head.LINE) alone.

Defines:
  LayH R q: facts on the layout and on the lookup's record at call q: each segment lists as many
    columns as it has entries; the call has 2^lJ columns; its point has lJ + lt coordinates; the
    padding row of the lookup's shape is the layout's; one segment of the call with HD0, and none
    of another call, bears that name.
  LineLaw: the value of a segment's form is the sum over the segment's entries of the weight of the
    entry's column times the extension, over the positions, of the affine part of the entry's keys;
    plus, at HD0, 2^lPd / 2^(sh + 15) times what stands under the slot of the logits' sumcheck.
  AlgLine: A CLOSED PROPOSITION, NOT PROVED HERE: LineLaw, under the law of the reads, for every
    record made as the head's check makes it and every run of Head.LINE that returns.
States:
  extL_split, extL_const, ext_cols: the extension of a call's key vector, column by column.
  padW_val, lines_val: the values of the padding's weight and of the sum of the segments' forms.
  algHAff_at: at one record: one law a segment, and LayH at every call, give the affine part.
  algHAff_of_lines: AlgLine, and LayH at every record made so, give AlgHAff.
Not claimed: anything on soundness, completeness or hiding. Nor are AlgLine and LayH claimed.

-/
import OnBytes.Tie.Pv.Lookup.Forest.FoAlgH
import OnBytes.Tie.Pv.Lookup.Ends.FoCols

set_option autoImplicit false

namespace Fo
open TwV Finset OnBytes OnBytes.Model OnBytes.Ends OnBytes.Ends.H

section
variable {K : Type} [CommRing K]

/-- The extension at a point in two parts: the top part chooses a block. -/
theorem extL_split (g : ℕ → K) (zj zt : List K) :
    extL g (zj ++ zt) = ∑ j ∈ range (2 ^ zj.length),
      eqN zj.reverse j * extL (fun t => g (j * 2 ^ zt.length + t)) zt := by
  unfold extL
  simp only [lsum]
  have h := eqN_split zt.reverse zj.reverse fun i j => g (j * 2 ^ zt.length + i)
  simp only [List.length_reverse] at h
  rw [List.reverse_append, List.length_append, Nat.add_comm zj.length]
  have e : ∀ r ∈ range (2 ^ (zt.length + zj.length)),
      eqN (zt.reverse ++ zj.reverse) r * g r = eqN (zt.reverse ++ zj.reverse) r *
        g (r / 2 ^ zt.length * 2 ^ zt.length + r % 2 ^ zt.length) := by
    intro r _
    rw [Nat.div_add_mod']
  rw [Finset.sum_congr rfl e, h]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by ring

theorem extL_const (k : K) (z : List K) : extL (fun _ => k) z = k := by
  unfold extL
  rw [lsum, ← Finset.sum_mul]
  have := eqN_total z.reverse
  rw [List.length_reverse] at this
  rw [this, one_mul]

end

section
variable {K : Type} [Field K]

/-- The extension of a call's key vector, column by column. -/
theorem ext_cols (P : PubH) (f : String → ℕ → ℕ → K) (q : ℕ) (zj zt : List K)
    (hT : P.h.T = 2 ^ zt.length) :
    extL (kvOf P f q) (zj ++ zt) = ∑ j ∈ range (2 ^ zj.length), eqN zj.reverse j *
      colTerm (fun sn x => extL (f sn x) zt) (tauN P.L.fs q (t0N P.L.fs q) : K)
        (colH P.L q j) := by
  rw [extL_split]
  refine Finset.sum_congr rfl fun j _ => ?_
  congr 1
  have hpos : 0 < 2 ^ zt.length := Nat.pow_pos (by decide)
  have hk : ∀ t, t < 2 ^ zt.length → kvOf P f q (j * 2 ^ zt.length + t) =
      match colH P.L q j with
      | some (sn, x) => f sn x t
      | none => (tauN P.L.fs q (t0N P.L.fs q) : K) := by
    intro t ht
    have e1 : (j * 2 ^ zt.length + t) / 2 ^ zt.length = j := by
      rw [Nat.mul_comm, Nat.mul_add_div hpos, Nat.div_eq_of_lt ht, Nat.add_zero]
    have e2 : (j * 2 ^ zt.length + t) % 2 ^ zt.length = t := by
      rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt ht]
    unfold kvOf
    rw [hT, e1, e2]
    rcases colH P.L q j with _ | ⟨sn, x⟩ <;> rfl
  have hx : extL (fun t => kvOf P f q (j * 2 ^ zt.length + t)) zt =
      extL (fun t => match colH P.L q j with
        | some (sn, x) => f sn x t
        | none => (tauN P.L.fs q (t0N P.L.fs q) : K)) zt := by
    unfold extL
    refine congrArg List.sum (List.map_congr_left fun t ht => ?_)
    show _ * kvOf P f q (j * 2 ^ zt.length + t) = _
    rw [hk t (List.mem_range.mp ht)]
  rw [hx]
  cases hc : colH P.L q j with
  | none => exact extL_const _ zt
  | some sx => rfl

end

section
variable {K : Type} [CommRing K] (ρ : Reading K)

/-- The value of the weight of the columns that no segment lists. -/
theorem padW_val (e : Array E) (w : Array ℕ) (J : ℕ) :
    ρ.val (padWOf e w J) =
      ∑ j ∈ range J, (if mk0 w j = 0 then ρ.val (e.getD j zeroE) else 0) := by
  unfold padWOf
  rw [← List.range_eq_range']
  have key : ∀ (n : ℕ), ρ.val ((List.range n).foldl
      (fun p j => if w.getD j 0 == 0 then addE p (e.getD j zeroE) else p) zeroE) =
      ∑ j ∈ range n, (if mk0 w j = 0 then ρ.val (e.getD j zeroE) else 0) := by
    intro n
    induction n with
    | zero => simpa using ρ.zero
    | succ n ih =>
      rw [List.range_succ, List.foldl_append, Finset.sum_range_succ, ← ih]
      show ρ.val (if w.getD n 0 == 0 then addE _ (e.getD n zeroE) else _) = _
      unfold mk0
      by_cases h : w.getD n 0 = 0
      · rw [if_pos (by simpa using h), if_pos h, ρ.add]
      · rw [if_neg (by simpa using h), if_neg h, add_zero]
  exact key J

/-- The value of a sum of forms. -/
theorem lines_val (W : World K) : ∀ (ls : List Aff) (a : Aff),
    (ls.foldl (· + ·) a).value ρ W = a.value ρ W + (ls.map fun x => x.value ρ W).sum
  | [], a => by simp
  | x :: ls, a => by
    rw [List.foldl_cons, lines_val W ls, Aff.value_add, List.map_cons, List.sum_cons, add_assoc]


theorem forall2_sum {α β : Type} (r : α → β → Prop) (f : α → K) (g : β → K) :
    ∀ (l : List α) (l' : List β), (∀ a ∈ l, ∀ b, r a b → g b = f a) → List.Forall₂ r l l' →
      (l'.map g).sum = (l.map f).sum
  | _, _, _, .nil => rfl
  | a :: l, b :: l', h, .cons h1 h2 => by
    rw [List.map_cons, List.map_cons, List.sum_cons, List.sum_cons,
      h a List.mem_cons_self b h1,
      forall2_sum r f g l l' (fun a' ha' => h a' (List.mem_cons_of_mem _ ha')) h2]

end

/-- Facts on the layout and on the lookup's record, at call q. -/
structure LayH (R : Head.Run) (q : ℕ) : Prop where
  size : ∀ g ∈ (R.L.calls.getD q default).segs, g.pos.size = g.n
  cols : (R.L.calls.getD q default).J = 2 ^ (R.L.calls.getD q default).lJ
  point : (R.x.g1.zk.getD q #[]).size = (R.L.calls.getD q default).lJ + R.h.lt
  pad : tauN R.L.fs q (t0N R.L.fs q) =
    ((R.L.cl.getD q default).tauAt (R.L.cl.getD q default).t0).toNat
  hd0 : ((R.L.calls.getD q default).segs.map fun g => if g.name = "HD0" then 1 else 0).sum =
    if q = R.x.qH then 1 else 0

/-- The law of one segment's form. -/
def LineLaw (R : Head.Run) (lay : WsLay) (W : World Cb.Gl.E) (cell : NameH → Cb.Gl.E) (q : ℕ)
    (g : Seg) (a : Aff) : Prop :=
  a.value Reading.gl W =
    ((List.range g.n).map fun x =>
      Reading.gl.val ((eqTab (Head.zjOf R.L R.x.g1 q)).getD (g.pos.getD x 0) zeroE) *
        extL (affH (pubH R lay) cell g.name x) (rdA Reading.gl (Head.ztOf R.h R.L R.x.g1 q))).sum +
      (if g.name = "HD0" then iw (pubH R lay) * 2 ^ R.h.lPd * W.slot R.x.tH.sCl else 0)

/-- One law a segment, at one record. -/
def AlgLineAt (R : Head.Run) (lay : WsLay) : Prop :=
  ∀ q < R.x.g1.shape.NC,
    ∀ g ∈ (R.L.calls.getD q default).segs, ∀ (F : Fork) (c : Ctx) (a : Aff),
      Head.LINE R g.name F c = .ok ((a, F), c) →
      ∀ (W : World Cb.Gl.E) (cell : NameH → Cb.Gl.E),
        ReadsAll Reading.gl R.hp.tl.mats (funsH R) W.entry R.iU3 (colsOf F R.iU3)
          (fun m r c => cell (.cell m r c)) →
        LineLaw R lay W cell q g a

/-- **One law a segment, as one closed proposition.** -/
def AlgLine : Prop := ∀ (R : Head.Run) (lay : WsLay), MadeH R → AlgLineAt R lay

theorem rdA_cut (ρ : Reading Cb.Gl.E) (z : Array E) (a b : ℕ) (hz : z.size = a + b) :
    rdA ρ z = rdA ρ (z.extract 0 a) ++ rdA ρ (z.extract a (a + b)) := by
  have e1 := rdL_extract ρ z 0 a
  have e2 := rdL_extract ρ z a (a + b)
  have hl : (rdL ρ z).length = a + b := by rw [rdL_length, hz]
  show rdL ρ z = rdL ρ (z.extract 0 a) ++ rdL ρ (z.extract a (a + b))
  rw [e1, e2]
  unfold exL
  rw [List.drop_zero, Nat.sub_zero, Nat.add_sub_cancel_left,
    List.take_of_length_le (l := (rdL ρ z).drop a) (by rw [List.length_drop, hl]; omega),
    List.take_append_drop]

/-- The affine part falls to one law a segment, at one record. -/
theorem algHAff_at {R : Head.Run} {lay : WsLay} (hA : AlgLineAt R lay)
    (hL : ∀ q < R.x.g1.shape.NC, LayH R q) : AlgHAffAt R lay := by
  intro q laid laid' F G c c' v hq hk W cell hU
  obtain ⟨ls, weighed, b1, b2, rfl⟩ := keyForm_ok R q laid laid' F G c c' v hk
  have Y := hL q hq
  -- the point, in two parts
  have hz : zkH Reading.gl R q = rdA Reading.gl (Head.zjOf R.L R.x.g1 q) ++
      rdA Reading.gl (Head.ztOf R.h R.L R.x.g1 q) := rdA_cut _ _ _ _ Y.point
  have hzj : (rdA Reading.gl (Head.zjOf R.L R.x.g1 q)).length =
      (R.L.calls.getD q default).lJ := by
    show (rdL Reading.gl _).length = _
    rw [rdL_length]
    unfold Head.zjOf
    rw [Array.size_extract, Y.point]
    omega
  have hzt : (rdA Reading.gl (Head.ztOf R.h R.L R.x.g1 q)).length = R.h.lt := by
    show (rdL Reading.gl _).length = _
    rw [rdL_length]
    unfold Head.ztOf
    dsimp only
    rw [Array.size_extract, Y.point]
    omega
  rw [hz, ext_cols (pubH R lay) _ q _ _ (by rw [hzt]; rfl), hzj, ← Y.cols]
  -- the weights of the columns
  have hE : ∀ j ∈ range (R.L.calls.getD q default).J,
      eqN (rdA Reading.gl (Head.zjOf R.L R.x.g1 q)).reverse j =
        Reading.gl.val ((eqTab (Head.zjOf R.L R.x.g1 q)).getD j zeroE) := by
    intro j hj
    rw [rdL_getD, eqTab_val, eqTabK_get]
    have : j < 2 ^ (rdL Reading.gl (Head.zjOf R.L R.x.g1 q)).length := by
      have h1 : (rdL Reading.gl (Head.zjOf R.L R.x.g1 q)).length = _ := hzj
      rw [h1, ← Y.cols]
      exact mem_range.mp hj
    rw [if_pos this]
    rfl
  have hC := cols_sum R
    (fun j => Reading.gl.val ((eqTab (Head.zjOf R.L R.x.g1 q)).getD j zeroE))
    (fun sn x => extL (affH (pubH R lay) cell sn x)
      (rdA Reading.gl (Head.ztOf R.h R.L R.x.g1 q)))
    (tauN R.L.fs q (t0N R.L.fs q) : Cb.Gl.E) _ _ weighed Y.size b2
  rw [Array.size_replicate] at hC
  have hS : ∀ j ∈ range (R.L.calls.getD q default).J,
      eqN (rdA Reading.gl (Head.zjOf R.L R.x.g1 q)).reverse j *
        colTerm (fun sn x => extL (affH (pubH R lay) cell sn x)
          (rdA Reading.gl (Head.ztOf R.h R.L R.x.g1 q)))
          (tauN (pubH R lay).L.fs q (t0N (pubH R lay).L.fs q) : Cb.Gl.E)
          (colH (pubH R lay).L q j) =
      if mk0 (Array.replicate (R.L.calls.getD q default).J 0) j = 0 then
        (fun j => Reading.gl.val ((eqTab (Head.zjOf R.L R.x.g1 q)).getD j zeroE)) j *
          colTerm (fun sn x => extL (affH (pubH R lay) cell sn x)
          (rdA Reading.gl (Head.ztOf R.h R.L R.x.g1 q)))
            (tauN R.L.fs q (t0N R.L.fs q) : Cb.Gl.E) (colL (R.L.calls.getD q default).segs j)
      else 0 := by
    intro j hj
    have h0 : mk0 (Array.replicate (R.L.calls.getD q default).J 0) j = 0 := by
      unfold mk0
      rw [Array.getD_eq_getD_getElem?, Array.getElem?_replicate]
      split <;> rfl
    rw [if_pos h0, hE j hj]
    rfl
  rw [Finset.sum_congr rfl hS, hC]
  -- the segments' forms
  have hLs : (ls.map fun x => x.value Reading.gl W).sum =
      ((R.L.calls.getD q default).segs.map fun g =>
        ((List.range g.n).map fun x =>
          Reading.gl.val ((eqTab (Head.zjOf R.L R.x.g1 q)).getD (g.pos.getD x 0) zeroE) *
            extL (affH (pubH R lay) cell g.name x)
              (rdA Reading.gl (Head.ztOf R.h R.L R.x.g1 q))).sum +
          (if g.name = "HD0" then iw (pubH R lay) * 2 ^ R.h.lPd * W.slot R.x.tH.sCl
            else 0)).sum :=
    forall2_sum _ _ _ _ _ (fun g hg a ha => hA q hq g hg F c a ha W cell hU) b1
  have hH : ((R.L.calls.getD q default).segs.map fun g =>
      (if g.name = "HD0" then iw (pubH R lay) * 2 ^ R.h.lPd * W.slot R.x.tH.sCl
        else (0 : Cb.Gl.E))).sum =
      if q = R.x.qH then iw (pubH R lay) * 2 ^ R.h.lPd * W.slot R.x.tH.sCl else 0 := by
    have e : ∀ l : List Seg, (l.map fun g =>
        (if g.name = "HD0" then iw (pubH R lay) * 2 ^ R.h.lPd * W.slot R.x.tH.sCl
          else (0 : Cb.Gl.E))).sum =
        ((l.map fun g => if g.name = "HD0" then 1 else 0).sum : ℕ) *
          (iw (pubH R lay) * 2 ^ R.h.lPd * W.slot R.x.tH.sCl) := by
      intro l
      induction l with
      | nil => simp
      | cons g l ih =>
        rw [List.map_cons, List.sum_cons, ih, List.map_cons, List.sum_cons, Nat.cast_add, add_mul]
        congr 1
        split <;> simp
    rw [e, Y.hd0]
    split <;> simp
  have hpad : Reading.gl.val (scaleE ((R.L.cl.getD q default).tauAt (R.L.cl.getD q default).t0)
      (padWOf (eqTab (Head.zjOf R.L R.x.g1 q)) weighed (R.L.calls.getD q default).J)) =
      (tauN R.L.fs q (t0N R.L.fs q) : Cb.Gl.E) *
        ∑ j ∈ range (R.L.calls.getD q default).J, (if mk0 weighed j = 0 then
          Reading.gl.val ((eqTab (Head.zjOf R.L R.x.g1 q)).getD j zeroE) else 0) := by
    rw [scale_val, padW_val, Y.pad]
  rw [Aff.value_add, lines_val, Aff.value_empty, zero_add, hLs, List.sum_map_add, hH]
  beta_reduce
  by_cases h1 : q = R.x.qN
  · rw [if_pos (by simpa using h1), if_pos h1, Aff.value_add, Aff.value_ofConst, hpad]
    show _ + (Aff.slot R.x.tN.sCl).value Reading.gl W + _ = _
    rw [Aff.value_slot]
    ring
  · rw [if_neg (by simpa using h1), if_neg h1, Aff.value_ofConst, hpad]
    ring

/-- The affine part falls to one law a segment. -/
theorem algHAff_of_lines (hA : AlgLine) (hL : ∀ R, MadeH R → ∀ q < R.x.g1.shape.NC, LayH R q) :
    AlgHAff := fun R lay hR => algHAff_at (hA R lay hR) (hL R hR)

end Fo
