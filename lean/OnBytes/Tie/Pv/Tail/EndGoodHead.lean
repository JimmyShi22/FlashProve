-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Tail/EndGoodHead.lean: the own claims of the head's sub-proof (`Head.walk`,
OnBytes/Model/Head.lean) are added by the steps of OnBytes/Tie/Pv/Led/LedAdds.lean, and every form
among them names entries of the vector of the tables alone.

Definitions, and theorems with their proofs, each by a walk through a routine's text (`walkH`,
OnBytes/Tie/Pv/Tail/EndGoodHear.lean).

Main names: the instances of `HasGood` for the head's records that hold forms;
  `pq_bind3`, `pq_map`: «x, then f» where x returns three values; a function applied to what a
    routine returns; `walkJ`: the walk with them;
  `pq_` and a routine's name; `good_` and a function's name;
  `head_hear_good`: what `Head.hear` returns is good, for every array;
  `head_walk_adds`: a run of `Head.walk` holds a run of objectsF; before it and after it the
    sub-proof's own claims are added by a walk, every entry of every form in array Rn.iU3, if the
    records Rn and wo are good;
  `head_adds`: the same from the runs of the hearing, of the merge's messages and of `Head.walk`,
    with the two lists of forms.

Limits: those of OnBytes/Tie/Pv/Tail/EndGood.lean. Nothing on the claims of the smallness test
between the two lists.


-/
import OnBytes.Tie.Pv.Tail.EndGoodHear
import OnBytes.Tie.Pv.Tail.EndHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Tie.Pv.Tail.Forms
open OnBytes OnBytes.Model OnBytes.Tie.Pv.Tail

variable {t0 : Nat}

/-! ## The head's records that hold forms -/

/-- What is asked of a value of this type. -/
instance : HasGood Tsc := ⟨fun t r => HasGood.good t r.p ∧ HasGood.good t r.rowU⟩

/-- The record's field `p`. -/
instance good_Tsc_p (r : Tsc) [h : Good t0 r] : Good t0 r.p := ⟨h.out.1⟩

/-- The record's field `rowU`. -/
instance good_Tsc_rowU (r : Tsc) [h : Good t0 r] : Good t0 r.rowU := ⟨h.out.2⟩

/-- What is asked of a value of this type. -/
instance : HasGood WsMerged := ⟨fun t r => HasGood.good t r.p⟩

/-- The record's field `p`. -/
instance good_WsMerged_p (r : WsMerged) [h : Good t0 r] : Good t0 r.p := ⟨h.out⟩

/-- What is asked of a value of this type. -/
instance : HasGood WsForkOut := ⟨fun t r => HasGood.good t r.toWsMerged⟩

/-- The record's field `toWsMerged`. -/
instance good_WsForkOut_toWsMerged (r : WsForkOut) [h : Good t0 r] : Good t0 r.toWsMerged := ⟨h.out⟩

/-- What is asked of a value of this type. -/
instance : HasGood Head.Heard :=
  ⟨fun t r => HasGood.good t r.g1 ∧ HasGood.good t r.wpl ∧ HasGood.good t r.tV ∧
    HasGood.good t r.tN ∧ HasGood.good t r.tH⟩

/-- The record's field `g1`. -/
instance good_HHeard_g1 (r : Head.Heard) [h : Good t0 r] : Good t0 r.g1 := ⟨h.out.1⟩

/-- The record's field `wpl`. -/
instance good_HHeard_wpl (r : Head.Heard) [h : Good t0 r] : Good t0 r.wpl := ⟨h.out.2.1⟩

/-- The record's field `tV`. -/
instance good_HHeard_tV (r : Head.Heard) [h : Good t0 r] : Good t0 r.tV := ⟨h.out.2.2.1⟩

/-- The record's field `tN`. -/
instance good_HHeard_tN (r : Head.Heard) [h : Good t0 r] : Good t0 r.tN := ⟨h.out.2.2.2.1⟩

/-- The record's field `tH`. -/
instance good_HHeard_tH (r : Head.Heard) [h : Good t0 r] : Good t0 r.tH := ⟨h.out.2.2.2.2⟩

/-- What is asked of a value of this type. -/
instance : HasGood Head.Run := ⟨fun t r => HasGood.good t r.x⟩

/-- The record's field `x`. -/
instance good_HRun_x (r : Head.Run) [h : Good t0 r] : Good t0 r.x := ⟨h.out⟩

/-- What is asked of a value of this type. -/
instance : HasGood Head.RowAH :=
  ⟨fun t r => HasGood.good t r.Dg ∧ HasGood.good t r.V ∧ HasGood.good t r.c ∧ HasGood.good t r.s0 ∧
    HasGood.good t r.sig ∧ HasGood.good t r.l1 ∧ HasGood.good t r.h1 ∧ HasGood.good t r.Rlo ∧
    HasGood.good t r.Rhi ∧ HasGood.good t r.R ∧ HasGood.good t r.p1 ∧ HasGood.good t r.rr ∧
    HasGood.good t r.rq⟩

/-- The record's field `Dg`. -/
instance good_RowAH_Dg (r : Head.RowAH) [h : Good t0 r] : Good t0 r.Dg := ⟨h.out.1⟩

/-- The record's field `V`. -/
instance good_RowAH_V (r : Head.RowAH) [h : Good t0 r] : Good t0 r.V := ⟨h.out.2.1⟩

/-- The record's field `c`. -/
instance good_RowAH_c (r : Head.RowAH) [h : Good t0 r] : Good t0 r.c := ⟨h.out.2.2.1⟩

/-- The record's field `s0`. -/
instance good_RowAH_s0 (r : Head.RowAH) [h : Good t0 r] : Good t0 r.s0 := ⟨h.out.2.2.2.1⟩

/-- The record's field `sig`. -/
instance good_RowAH_sig (r : Head.RowAH) [h : Good t0 r] : Good t0 r.sig := ⟨h.out.2.2.2.2.1⟩

/-- The record's field `l1`. -/
instance good_RowAH_l1 (r : Head.RowAH) [h : Good t0 r] : Good t0 r.l1 := ⟨h.out.2.2.2.2.2.1⟩

/-- The record's field `h1`. -/
instance good_RowAH_h1 (r : Head.RowAH) [h : Good t0 r] : Good t0 r.h1 := ⟨h.out.2.2.2.2.2.2.1⟩

/-- The record's field `Rlo`. -/
instance good_RowAH_Rlo (r : Head.RowAH) [h : Good t0 r] : Good t0 r.Rlo := ⟨h.out.2.2.2.2.2.2.2.1⟩

/-- The record's field `Rhi`. -/
instance good_RowAH_Rhi (r : Head.RowAH)
    [h : Good t0 r] : Good t0 r.Rhi := ⟨h.out.2.2.2.2.2.2.2.2.1⟩

/-- The record's field `R`. -/
instance good_RowAH_R (r : Head.RowAH) [h : Good t0 r] : Good t0 r.R := ⟨h.out.2.2.2.2.2.2.2.2.2.1⟩

/-- The record's field `p1`. -/
instance good_RowAH_p1 (r : Head.RowAH)
    [h : Good t0 r] : Good t0 r.p1 := ⟨h.out.2.2.2.2.2.2.2.2.2.2.1⟩

/-- The record's field `rr`. -/
instance good_RowAH_rr (r : Head.RowAH)
    [h : Good t0 r] : Good t0 r.rr := ⟨h.out.2.2.2.2.2.2.2.2.2.2.2.1⟩

/-- The record's field `rq`. -/
instance good_RowAH_rq (r : Head.RowAH)
    [h : Good t0 r] : Good t0 r.rq := ⟨h.out.2.2.2.2.2.2.2.2.2.2.2.2⟩

/-- What is asked of a value of this type. -/
instance : HasGood
    (Row5 Aff) :=
  ⟨fun t r => HasGood.good t r.Dg ∧ HasGood.good t r.c ∧ HasGood.good t r.Vlo ∧
    HasGood.good t r.Vhi ∧ HasGood.good t r.a ∧ HasGood.good t r.b ∧ HasGood.good t r.sig ∧
    HasGood.good t r.s0 ∧ HasGood.good t r.l1 ∧ HasGood.good t r.h1 ∧ HasGood.good t r.Blo ∧
    HasGood.good t r.Bhi ∧ HasGood.good t r.kap ∧ HasGood.good t r.Rlo ∧ HasGood.good t r.Rhi ∧
    HasGood.good t r.R ∧ HasGood.good t r.q1 ∧ HasGood.good t r.rr ∧ HasGood.good t r.rq⟩

/-- The record's field `Dg`. -/
instance good_Row5_Dg (r : (Row5 Aff)) [h : Good t0 r] : Good t0 r.Dg := ⟨h.out.1⟩

/-- The record's field `c`. -/
instance good_Row5_c (r : (Row5 Aff)) [h : Good t0 r] : Good t0 r.c := ⟨h.out.2.1⟩

/-- The record's field `Vlo`. -/
instance good_Row5_Vlo (r : (Row5 Aff)) [h : Good t0 r] : Good t0 r.Vlo := ⟨h.out.2.2.1⟩

/-- The record's field `Vhi`. -/
instance good_Row5_Vhi (r : (Row5 Aff)) [h : Good t0 r] : Good t0 r.Vhi := ⟨h.out.2.2.2.1⟩

/-- The record's field `a`. -/
instance good_Row5_a (r : (Row5 Aff)) [h : Good t0 r] : Good t0 r.a := ⟨h.out.2.2.2.2.1⟩

/-- The record's field `b`. -/
instance good_Row5_b (r : (Row5 Aff)) [h : Good t0 r] : Good t0 r.b := ⟨h.out.2.2.2.2.2.1⟩

/-- The record's field `sig`. -/
instance good_Row5_sig (r : (Row5 Aff)) [h : Good t0 r] : Good t0 r.sig := ⟨h.out.2.2.2.2.2.2.1⟩

/-- The record's field `s0`. -/
instance good_Row5_s0 (r : (Row5 Aff)) [h : Good t0 r] : Good t0 r.s0 := ⟨h.out.2.2.2.2.2.2.2.1⟩

/-- The record's field `l1`. -/
instance good_Row5_l1 (r : (Row5 Aff)) [h : Good t0 r] : Good t0 r.l1 := ⟨h.out.2.2.2.2.2.2.2.2.1⟩

/-- The record's field `h1`. -/
instance good_Row5_h1 (r : (Row5 Aff)) [h : Good t0 r] : Good t0 r.h1 := ⟨h.out.2.2.2.2.2.2.2.2.2.1⟩

/-- The record's field `Blo`. -/
instance good_Row5_Blo (r : (Row5 Aff))
    [h : Good t0 r] : Good t0 r.Blo := ⟨h.out.2.2.2.2.2.2.2.2.2.2.1⟩

/-- The record's field `Bhi`. -/
instance good_Row5_Bhi (r : (Row5 Aff))
    [h : Good t0 r] : Good t0 r.Bhi := ⟨h.out.2.2.2.2.2.2.2.2.2.2.2.1⟩

/-- The record's field `kap`. -/
instance good_Row5_kap (r : (Row5 Aff))
    [h : Good t0 r] : Good t0 r.kap := ⟨h.out.2.2.2.2.2.2.2.2.2.2.2.2.1⟩

/-- The record's field `Rlo`. -/
instance good_Row5_Rlo (r : (Row5 Aff))
    [h : Good t0 r] : Good t0 r.Rlo := ⟨h.out.2.2.2.2.2.2.2.2.2.2.2.2.2.1⟩

/-- The record's field `Rhi`. -/
instance good_Row5_Rhi (r : (Row5 Aff))
    [h : Good t0 r] : Good t0 r.Rhi := ⟨h.out.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1⟩

/-- The record's field `R`. -/
instance good_Row5_R (r : (Row5 Aff))
    [h : Good t0 r] : Good t0 r.R := ⟨h.out.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1⟩

/-- The record's field `q1`. -/
instance good_Row5_q1 (r : (Row5 Aff))
    [h : Good t0 r] : Good t0 r.q1 := ⟨h.out.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1⟩

/-- The record's field `rr`. -/
instance good_Row5_rr (r : (Row5 Aff))
    [h : Good t0 r] : Good t0 r.rr := ⟨h.out.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1⟩

/-- The record's field `rq`. -/
instance good_Row5_rq (r : (Row5 Aff))
    [h : Good t0 r] : Good t0 r.rq := ⟨h.out.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2⟩

/-! ## Further laws -/

/-- «x, then f», where x returns three values. -/
theorem pq_bind3 {α β γ δ : Type} [HasGood α] [HasGood β] [HasGood γ] [HasGood δ]
    {x : SubM (α × β × γ)} {f : α × β × γ → SubM δ} (hx : PresQ t0 x)
    (hf : ∀ a b c, Good t0 a → Good t0 b → Good t0 c → PresQ t0 (f (a, b, c))) :
    PresQ t0 (x >>= f) :=
  pq_bind hx fun p hp => hf p.1 p.2.1 p.2.2 ⟨hp.out.1⟩ ⟨hp.out.2.1⟩ ⟨hp.out.2.2⟩

/-- A function applied to what a routine returns. -/
theorem pq_map {α β : Type} [HasGood α] [HasGood β] (g : α → β) {x : SubM α} (hx : PresQ t0 x)
    (hg : ∀ a, Good t0 a → Good t0 (g a)) : PresQ t0 (g <$> x) := by
  rw [map_eq_pure_bind]
  exact pq_bind hx fun a ha => @pq_pure _ _ _ _ (hg a ha)

/-- An array given by a function. -/
instance good_ofFn {α : Type} [HasGood α] {n : Nat} (f : Fin n → α) [h : ∀ i, Good t0 (f i)] :
    Good t0 (Array.ofFn f) :=
  ⟨fun y hy => by
    have h2 : y ∈ Array.ofFn f := by simpa using hy
    obtain ⟨i, rfl⟩ := Array.mem_ofFn.1 h2
    exact (h i).out⟩

/-- An array's image under a function with good values. -/
instance good_mapArr {α β : Type} [HasGood β] (f : α → β) (a : Array α) [h : ∀ x, Good t0 (f x)] :
    Good t0 (a.map f) :=
  ⟨fun y hy => by
    have h2 : y ∈ a.map f := by simpa using hy
    obtain ⟨x, -, rfl⟩ := Array.mem_map.1 h2
    exact (h x).out⟩

/-- The ledger's constant, as a form. -/
instance good_ledC (v : E) : Good t0 (LedK.c v : Aff) := good_ofConst v

/-- The ledger's sum, of forms. -/
instance good_ledAdd (a b : Aff) [Good t0 a] [Good t0 b] : Good t0 (LedK.add a b) := good_add a b

/-- The ledger's difference, of forms. -/
instance good_ledSub (a b : Aff) [Good t0 a] [Good t0 b] : Good t0 (LedK.sub a b) := good_sub a b

/-- The ledger's multiple, of a form. -/
instance good_ledMul (a : Aff) (k : E) [Good t0 a] : Good t0 (LedK.mul a k) := good_scale a k

/-- One step of the walk, with the laws above. -/
macro "walkJ_step" : tactic => `(tactic| first
  | exact inferInstance | refine pq_bind3 ?_ ?_ | refine pq_map _ ?_ ?_ | refine @pq_lin _ _ ?_
  | walkH_step)

/-- The walk, with the laws above. -/
macro "walkJ" : tactic => `(tactic| repeat' walkJ_step)

/-! ## Functions that return forms -/

open OnBytes.Model in
/-- `ledDig` returns a good value. -/
instance good_Model_ledDig (Dg : Array Aff) (first n : Nat) [Good t0 Dg] :
    Good t0 (OnBytes.Model.ledDig Dg first n) := by
  unfold OnBytes.Model.ledDig
  walkJ

/-! ### The ledger's row of nineteen fields, field by field -/

section
variable (cell : Nat → Aff) [∀ j, Good t0 (cell j)]

/-- The field `Dg` of `row5 cell` is good. -/
theorem good_row5_Dg : Good t0 (row5 cell).Dg := by
  show Good t0 (Array.ofFn (n := 99) fun j => LedK.add (cell j.val) (LedK.c (ofNat 128)))
  infer_instance

/-- The field `c` of `row5 cell` is good. -/
theorem good_row5_c : Good t0 (row5 cell).c := by
  have := good_row5_Dg (t0 := t0) cell
  show Good t0 (Array.ofFn (n := 10) fun s =>
    if s.val == 0 then (LedK.c zeroE : Aff)
    else if s.val == 9 then ((row5 cell).Dg.getD 9 (LedK.c zeroE))
    else LedK.sub (ledDig (row5 cell).Dg (10 + 6 * (s.val - 1)) 6) (LedK.c (ofNat (2 ^ 47))))
  infer_instance

/-- The field `Vlo` of `row5 cell` is good. -/
theorem good_row5_Vlo : Good t0 (row5 cell).Vlo := by
  have := good_row5_Dg (t0 := t0) cell
  show Good t0 (ledDig (row5 cell).Dg 0 6)
  infer_instance

/-- The field `Vhi` of `row5 cell` is good. -/
theorem good_row5_Vhi : Good t0 (row5 cell).Vhi := by
  have := good_row5_Dg (t0 := t0) cell
  show Good t0 (ledDig (row5 cell).Dg 6 4)
  infer_instance

/-- The field `a` of `row5 cell` is good. -/
theorem good_row5_a : Good t0 (row5 cell).a := by
  have := good_row5_Dg (t0 := t0) cell
  show Good t0 (LedK.add (LedK.add (LedK.add
    (LedK.mul ((row5 cell).Dg.getD 58 (LedK.c zeroE)) (ofNat 2))
    ((row5 cell).Dg.getD 59 (LedK.c zeroE)))
    (LedK.mul ((row5 cell).Dg.getD 60 (LedK.c zeroE)) (ofNat 256)))
    (LedK.mul ((row5 cell).Dg.getD 61 (LedK.c zeroE)) (ofNat 65536)))
  infer_instance

/-- The field `b` of `row5 cell` is good. -/
theorem good_row5_b : Good t0 (row5 cell).b := by
  have := good_row5_Dg (t0 := t0) cell
  show Good t0 (LedK.add ((row5 cell).Dg.getD 62 (LedK.c zeroE))
    (LedK.mul ((row5 cell).Dg.getD 63 (LedK.c zeroE)) (ofNat 256)))
  infer_instance

/-- The field `sig` of `row5 cell` is good. -/
theorem good_row5_sig : Good t0 (row5 cell).sig := by
  have := good_row5_Dg (t0 := t0) cell
  have := good_row5_a (t0 := t0) cell
  have := good_row5_b (t0 := t0) cell
  show Good t0 (LedK.add (row5 cell).a (LedK.mul (row5 cell).b (ofNat (2 ^ 24))))
  infer_instance

/-- The field `s0` of `row5 cell` is good. -/
theorem good_row5_s0 : Good t0 (row5 cell).s0 := by
  unfold row5
  dsimp only
  infer_instance

/-- The field `l1` of `row5 cell` is good. -/
theorem good_row5_l1 : Good t0 (row5 cell).l1 := by
  have := good_row5_Dg (t0 := t0) cell
  show Good t0 (ledDig (row5 cell).Dg 64 5)
  infer_instance

/-- The field `h1` of `row5 cell` is good. -/
theorem good_row5_h1 : Good t0 (row5 cell).h1 := by
  have := good_row5_Dg (t0 := t0) cell
  show Good t0 (ledDig (row5 cell).Dg 69 5)
  infer_instance

/-- The field `Blo` of `row5 cell` is good. -/
theorem good_row5_Blo : Good t0 (row5 cell).Blo := by
  have := good_row5_Dg (t0 := t0) cell
  show Good t0 (ledDig (row5 cell).Dg 74 3)
  infer_instance

/-- The field `Bhi` of `row5 cell` is good. -/
theorem good_row5_Bhi : Good t0 (row5 cell).Bhi := by
  have := good_row5_Dg (t0 := t0) cell
  show Good t0 (ledDig (row5 cell).Dg 77 2)
  infer_instance

/-- The field `kap` of `row5 cell` is good. -/
theorem good_row5_kap : Good t0 (row5 cell).kap := by
  have := good_row5_Dg (t0 := t0) cell
  show Good t0 (LedK.sub ((row5 cell).Dg.getD 79 (LedK.c zeroE)) (LedK.c (ofNat 4)))
  infer_instance

/-- The field `Rlo` of `row5 cell` is good. -/
theorem good_row5_Rlo : Good t0 (row5 cell).Rlo := by
  have := good_row5_Dg (t0 := t0) cell
  show Good t0 (ledDig (row5 cell).Dg 80 3)
  infer_instance

/-- The field `Rhi` of `row5 cell` is good. -/
theorem good_row5_Rhi : Good t0 (row5 cell).Rhi := by
  have := good_row5_Dg (t0 := t0) cell
  show Good t0 (ledDig (row5 cell).Dg 83 3)
  infer_instance

/-- The field `R` of `row5 cell` is good. -/
theorem good_row5_R : Good t0 (row5 cell).R := by
  have := good_row5_Dg (t0 := t0) cell
  have := good_row5_Rlo (t0 := t0) cell
  have := good_row5_Rhi (t0 := t0) cell
  show Good t0 (LedK.add (row5 cell).Rlo (LedK.mul (row5 cell).Rhi (ofNat (2 ^ 24))))
  infer_instance

/-- The field `q1` of `row5 cell` is good. -/
theorem good_row5_q1 : Good t0 (row5 cell).q1 := by
  have := good_row5_Dg (t0 := t0) cell
  show Good t0 (ledDig (row5 cell).Dg 86 3)
  infer_instance

/-- The field `rr` of `row5 cell` is good. -/
theorem good_row5_rr : Good t0 (row5 cell).rr := by
  have := good_row5_Dg (t0 := t0) cell
  show Good t0 (ledDig (row5 cell).Dg 89 5)
  infer_instance

/-- The field `rq` of `row5 cell` is good. -/
theorem good_row5_rq : Good t0 (row5 cell).rq := by
  have := good_row5_Dg (t0 := t0) cell
  show Good t0 (ledDig (row5 cell).Dg 94 5)
  infer_instance

/-- `row5` returns a good value. -/
instance good_Model_row5 : Good t0 (row5 cell) :=
  ⟨⟨(good_row5_Dg cell).out, (good_row5_c cell).out, (good_row5_Vlo cell).out,
    (good_row5_Vhi cell).out, (good_row5_a cell).out, (good_row5_b cell).out,
    (good_row5_sig cell).out, (good_row5_s0 cell).out, (good_row5_l1 cell).out,
    (good_row5_h1 cell).out, (good_row5_Blo cell).out, (good_row5_Bhi cell).out,
    (good_row5_kap cell).out, (good_row5_Rlo cell).out, (good_row5_Rhi cell).out,
    (good_row5_R cell).out, (good_row5_q1 cell).out, (good_row5_rr cell).out,
    (good_row5_rq cell).out⟩⟩

end

open OnBytes.Model in
/-- `ledCarry5` returns a good value. -/
instance good_Model_ledCarry5 (r : Row5 Aff) (s : Nat) (Ws : Aff) [Good t0 r] [Good t0 Ws] :
    Good t0 (OnBytes.Model.ledCarry5 r s Ws) := by
  unfold OnBytes.Model.ledCarry5
  walkJ

open OnBytes.Model in
/-- `ledLines5` returns a good value. -/
instance good_Model_ledLines5 (r : Row5 Aff) (P : Array Aff) (eps : E) (two : Aff) [Good t0 r]
    [Good t0 P] [Good t0 two] :
    Good t0 (OnBytes.Model.ledLines5 r P eps two) := by
  unfold OnBytes.Model.ledLines5
  walkJ

open OnBytes.Model.Head in
/-- `Head.digits` returns a good value. -/
instance good_Model_Head_digits (Dg : Array Aff) (a n : Nat) [Good t0 Dg] :
    Good t0 (OnBytes.Model.Head.digits Dg a n) := by
  unfold OnBytes.Model.Head.digits
  walkJ

open OnBytes.Model in
/-- `wsForkStart` returns a good value. -/
instance good_Model_wsForkStart (sv : Array Nat) (rho : Array E) :
    Good t0 (OnBytes.Model.wsForkStart sv rho) := by
  unfold OnBytes.Model.wsForkStart
  walkJ

/-! ## OnBytes/Model/Psc.lean, Tsc.lean, Merge.lean -/

open OnBytes.Model in
/-- `layerObject`: its forms and what it returns are good. -/
instance pq_Model_layerObject (o : Level) [Good t0 o] :
    PresQ t0 (OnBytes.Model.layerObject o) := by
  unfold OnBytes.Model.layerObject
  walkJ

open OnBytes.Model in
/-- `tscLoop`: its forms and what it returns are good. -/
instance pq_Model_tscLoop :
    ∀ (zs : List E) (r : Array E) (p : Psc) [Good t0 p], PresQ t0 (OnBytes.Model.tscLoop zs r p)
  | [], r, p, _ => by
    unfold OnBytes.Model.tscLoop
    walkJ
  | z :: zs, r, p, _ => by
    have := pq_Model_tscLoop zs
    unfold OnBytes.Model.tscLoop
    walkJ

open OnBytes.Model in
/-- `tscRounds`: its forms and what it returns are good. -/
instance pq_Model_tscRounds (P : Array E) (lt : Nat) [Good t0 P] [Good t0 lt] :
    PresQ t0 (OnBytes.Model.tscRounds P lt) := by
  unfold OnBytes.Model.tscRounds
  walkJ

open OnBytes.Model in
/-- `tscIn`: its forms and what it returns are good. -/
instance pq_Model_tscIn (P : Array E) (lt shown degreeInY : Nat) [Good t0 P] [Good t0 lt]
    [Good t0 shown] [Good t0 degreeInY] :
    PresQ t0 (OnBytes.Model.tscIn P lt shown degreeInY) := by
  unfold OnBytes.Model.tscIn
  walkJ

open OnBytes.Model in
/-- `wsForkRounds`: its forms and what it returns are good. -/
instance pq_Model_wsForkRounds :
    ∀ (n : Nat) (rm : Array E) (p : Psc) [Good t0 p], PresQ t0 (OnBytes.Model.wsForkRounds n rm p)
  | 0, rm, p, _ => by
    unfold OnBytes.Model.wsForkRounds
    walkJ
  | n + 1, rm, p, _ => by
    have := pq_Model_wsForkRounds n
    unfold OnBytes.Model.wsForkRounds
    walkJ

open OnBytes.Model in
/-- `wsForkMerge`: its forms and what it returns are good. -/
instance pq_Model_wsForkMerge (lk : Nat) (sv : Array Nat) [Good t0 lk] [Good t0 sv] :
    PresQ t0 (OnBytes.Model.wsForkMerge lk sv) := by
  unfold OnBytes.Model.wsForkMerge
  walkJ

open OnBytes.Model in
/-- `wsForkLin`: its forms and what it returns are good. -/
instance pq_Model_wsForkLin (o : WsMerged) [Good t0 o] :
    PresQ t0 (OnBytes.Model.wsForkLin o) := by
  unfold OnBytes.Model.wsForkLin
  walkJ

open OnBytes.Model in
/-- `wsForkEnd`: its forms and what it returns are good. -/
instance pq_Model_wsForkEnd (lay : WsLay) (cl : Array WsClaim) (sv : Array Nat) [Good t0 lay]
    [Good t0 cl] [Good t0 sv] :
    PresQ t0 (OnBytes.Model.wsForkEnd lay cl sv) := by
  unfold OnBytes.Model.wsForkEnd
  walkJ

/-! ## OnBytes/Model/HeadHeard.lean -/

open OnBytes.Model.Head in
/-- `Head.noteH`: its forms and what it returns are good. -/
instance pq_Model_Head_noteH (what : String) (value : E) [Good t0 what] [Good t0 value] :
    PresQ t0 (OnBytes.Model.Head.noteH what value) := by
  unfold OnBytes.Model.Head.noteH
  walkJ

open OnBytes.Model.Head in
/-- `Head.replyToken`: its forms and what it returns are good. -/
instance pq_Model_Head_replyToken (plain : Array E) (V : Nat) [Good t0 plain] [Good t0 V] :
    PresQ t0 (OnBytes.Model.Head.replyToken plain V) := by
  unfold OnBytes.Model.Head.replyToken
  walkJ

open OnBytes.Model.Head in
/-- `Head.mergedPoint`: its forms and what it returns are good. -/
instance pq_Model_Head_mergedPoint (h : Shape) (g1 : Forest.Heard) [Good t0 h] [Good t0 g1] :
    PresQ t0 (OnBytes.Model.Head.mergedPoint h g1) := by
  unfold OnBytes.Model.Head.mergedPoint
  walkJ

open OnBytes.Model.Head in
/-- `Head.hearSquares`: its forms and what it returns are good. -/
instance pq_Model_Head_hearSquares (h : Shape) (PV : Array E) [Good t0 h] [Good t0 PV] :
    PresQ t0 (OnBytes.Model.Head.hearSquares h PV) := by
  unfold OnBytes.Model.Head.hearSquares
  walkJ

open OnBytes.Model.Head in
/-- `Head.shownRun`: its forms and what it returns are good. -/
instance pq_Model_Head_shownRun (first n : Nat) [Good t0 first] [Good t0 n] :
    PresQ t0 (OnBytes.Model.Head.shownRun first n) := by
  unfold OnBytes.Model.Head.shownRun
  walkJ

open OnBytes.Model.Head in
/-- `Head.hearProducts`: its forms and what it returns are good. -/
instance pq_Model_Head_hearProducts (h : Shape) (PV : Array E) [Good t0 h] [Good t0 PV] :
    PresQ t0 (OnBytes.Model.Head.hearProducts h PV) := by
  unfold OnBytes.Model.Head.hearProducts
  walkJ

open OnBytes.Model.Head in
/-- `Head.hearStream`: its forms and what it returns are good. -/
instance pq_Model_Head_hearStream (h : Shape) (zt : Array E) [Good t0 h] [Good t0 zt] :
    PresQ t0 (OnBytes.Model.Head.hearStream h zt) := by
  unfold OnBytes.Model.Head.hearStream
  walkJ

open OnBytes.Model.Head in
/-- `Head.channelRounds`: its forms and what it returns are good. -/
instance pq_Model_Head_channelRounds :
    ∀ (n : Nat) (r : Array E) (p : Psc) [Good t0 p],
      PresQ t0 (OnBytes.Model.Head.channelRounds n r p)
  | 0, r, p, _ => by
    unfold OnBytes.Model.Head.channelRounds
    walkJ
  | n + 1, r, p, _ => by
    have := pq_Model_Head_channelRounds n
    unfold OnBytes.Model.Head.channelRounds
    walkJ

open OnBytes.Model.Head in
/-- `Head.hearLogits`: its forms and what it returns are good. -/
instance pq_Model_Head_hearLogits (h : Shape) (lam : Nat) (zt : Array E) [Good t0 h] [Good t0 lam]
    [Good t0 zt] :
    PresQ t0 (OnBytes.Model.Head.hearLogits h lam zt) := by
  unfold OnBytes.Model.Head.hearLogits
  walkJ

/-! ## OnBytes/Model/HeadTables.lean, HeadForms.lean, Head.lean -/

open OnBytes.Model.Head in
/-- `Head.tabAt`: its forms and what it returns are good. -/
instance pq_Model_Head_tabAt (Rn : OnBytes.Model.Head.Run) (n : String) [Good Rn.iU3 Rn]
    [Good Rn.iU3 n] :
    PresQ Rn.iU3 (OnBytes.Model.Head.tabAt Rn n) := by
  unfold OnBytes.Model.Head.tabAt
  walkJ

open OnBytes.Model.Head in
/-- `Head.U3at`: its forms and what it returns are good. -/
instance pq_Model_Head_U3at (Rn : OnBytes.Model.Head.Run) (t i : Nat) [Good Rn.iU3 Rn]
    [Good Rn.iU3 t] [Good Rn.iU3 i] :
    PresQ Rn.iU3 (OnBytes.Model.Head.U3at Rn t i) := by
  unfold OnBytes.Model.Head.U3at
  walkJ

open OnBytes.Model.Head in
/-- `Head.segOf`: its forms and what it returns are good. -/
instance pq_Model_Head_segOf (Rn : OnBytes.Model.Head.Run) (sn : String) [Good Rn.iU3 Rn]
    [Good Rn.iU3 sn] :
    PresQ Rn.iU3 (OnBytes.Model.Head.segOf Rn sn) := by
  unfold OnBytes.Model.Head.segOf
  walkJ

open OnBytes.Model.Head in
/-- `Head.ewOf`: its forms and what it returns are good. -/
instance pq_Model_Head_ewOf (Rn : OnBytes.Model.Head.Run) (sn : String) [Good Rn.iU3 Rn]
    [Good Rn.iU3 sn] :
    PresQ Rn.iU3 (OnBytes.Model.Head.ewOf Rn sn) := by
  unfold OnBytes.Model.Head.ewOf
  walkJ

open OnBytes.Model.Head in
/-- `Head.ewh`: its forms and what it returns are good. -/
instance pq_Model_Head_ewh (Rn : OnBytes.Model.Head.Run) (sn : String) [Good Rn.iU3 Rn]
    [Good Rn.iU3 sn] :
    PresQ Rn.iU3 (OnBytes.Model.Head.ewh Rn sn) := by
  unfold OnBytes.Model.Head.ewh
  walkJ

open OnBytes.Model.Head in
/-- `Head.Sl`: its forms and what it returns are good. -/
instance pq_Model_Head_Sl (Rn : OnBytes.Model.Head.Run) (sn : String) (OFF nl J : Nat)
    [Good Rn.iU3 Rn] [Good Rn.iU3 sn] [Good Rn.iU3 OFF] [Good Rn.iU3 nl] [Good Rn.iU3 J] :
    PresQ Rn.iU3 (OnBytes.Model.Head.Sl Rn sn OFF nl J) := by
  unfold OnBytes.Model.Head.Sl
  walkJ

open OnBytes.Model.Head in
/-- `Head.xbA`: its forms and what it returns are good. -/
instance pq_Model_Head_xbA (Rn : OnBytes.Model.Head.Run) (t kh : Nat) [Good Rn.iU3 Rn]
    [Good Rn.iU3 t] [Good Rn.iU3 kh] :
    PresQ Rn.iU3 (OnBytes.Model.Head.xbA Rn t kh) := by
  unfold OnBytes.Model.Head.xbA
  walkJ

open OnBytes.Model.Head in
/-- `Head.sh2`: its forms and what it returns are good. -/
instance pq_Model_Head_sh2 (Rn : OnBytes.Model.Head.Run) (t j : Nat) [Good Rn.iU3 Rn]
    [Good Rn.iU3 t] [Good Rn.iU3 j] :
    PresQ Rn.iU3 (OnBytes.Model.Head.sh2 Rn t j) := by
  unfold OnBytes.Model.Head.sh2
  walkJ

open OnBytes.Model.Head in
/-- `Head.rowAt`: its forms and what it returns are good. -/
instance pq_Model_Head_rowAt (Rn : OnBytes.Model.Head.Run) (P : String) [Good Rn.iU3 Rn]
    [Good Rn.iU3 P] :
    PresQ Rn.iU3 (OnBytes.Model.Head.rowAt Rn P) := by
  unfold OnBytes.Model.Head.rowAt
  walkJ

open OnBytes.Model.Head in
/-- `Head.row5At`: its forms and what it returns are good. -/
instance pq_Model_Head_row5At (Rn : OnBytes.Model.Head.Run) (P : String) [Good Rn.iU3 Rn]
    [Good Rn.iU3 P] :
    PresQ Rn.iU3 (OnBytes.Model.Head.row5At Rn P) := by
  unfold OnBytes.Model.Head.row5At
  walkJ

open OnBytes.Model.Head in
/-- `Head.gapAt`: its forms and what it returns are good. -/
instance pq_Model_Head_gapAt (Rn : OnBytes.Model.Head.Run) (P : String) (i : Nat) (wsum : E)
    [Good Rn.iU3 Rn] [Good Rn.iU3 P] [Good Rn.iU3 i] [Good Rn.iU3 wsum] :
    PresQ Rn.iU3 (OnBytes.Model.Head.gapAt Rn P i wsum) := by
  unfold OnBytes.Model.Head.gapAt
  walkJ

open OnBytes.Model.Head in
/-- `Head.ztSeg`: its forms and what it returns are good. -/
instance pq_Model_Head_ztSeg (Rn : OnBytes.Model.Head.Run) (sn : String) [Good Rn.iU3 Rn]
    [Good Rn.iU3 sn] :
    PresQ Rn.iU3 (OnBytes.Model.Head.ztSeg Rn sn) := by
  unfold OnBytes.Model.Head.ztSeg
  walkJ

open OnBytes.Model.Head in
/-- `Head.middleDigit`: its forms and what it returns are good. -/
instance pq_Model_Head_middleDigit (Rn : OnBytes.Model.Head.Run) (sn : String) (wR : E)
    [Good Rn.iU3 Rn] [Good Rn.iU3 sn] [Good Rn.iU3 wR] :
    PresQ Rn.iU3 (OnBytes.Model.Head.middleDigit Rn sn wR) := by
  unfold OnBytes.Model.Head.middleDigit
  walkJ

open OnBytes.Model.Head in
/-- `Head.lowDigit`: its forms and what it returns are good. -/
instance pq_Model_Head_lowDigit (Rn : OnBytes.Model.Head.Run) (sn : String) (wR : E)
    [Good Rn.iU3 Rn] [Good Rn.iU3 sn] [Good Rn.iU3 wR] :
    PresQ Rn.iU3 (OnBytes.Model.Head.lowDigit Rn sn wR) := by
  unfold OnBytes.Model.Head.lowDigit
  walkJ

open OnBytes.Model.Head in
/-- `Head.LINE`: its forms and what it returns are good. -/
instance pq_Model_Head_LINE (Rn : OnBytes.Model.Head.Run) (sn : String) [Good Rn.iU3 Rn]
    [Good Rn.iU3 sn] :
    PresQ Rn.iU3 (OnBytes.Model.Head.LINE Rn sn) := by
  unfold OnBytes.Model.Head.LINE
  walkJ

open OnBytes.Model.Head in
/-- `Head.keyForm`: its forms and what it returns are good. -/
instance pq_Model_Head_keyForm (Rn : OnBytes.Model.Head.Run) (q : Nat) (laid : Array Nat)
    [Good Rn.iU3 Rn] [Good Rn.iU3 q] [Good Rn.iU3 laid] :
    PresQ Rn.iU3 (OnBytes.Model.Head.keyForm Rn q laid) := by
  unfold OnBytes.Model.Head.keyForm
  walkJ

open OnBytes.Model.Head in
/-- `Head.claimSquares`: its forms and what it returns are good. -/
instance pq_Model_Head_claimSquares (Rn : OnBytes.Model.Head.Run) [Good Rn.iU3 Rn] :
    PresQ Rn.iU3 (OnBytes.Model.Head.claimSquares Rn) := by
  unfold OnBytes.Model.Head.claimSquares
  walkJ

open OnBytes.Model.Head in
/-- `Head.claimLedger5`: its forms and what it returns are good. -/
instance pq_Model_Head_claimLedger5 (Rn : OnBytes.Model.Head.Run) [Good Rn.iU3 Rn] :
    PresQ Rn.iU3 (OnBytes.Model.Head.claimLedger5 Rn) := by
  unfold OnBytes.Model.Head.claimLedger5
  walkJ

open OnBytes.Model.Head in
/-- `Head.claimLedger4`: its forms and what it returns are good. -/
instance pq_Model_Head_claimLedger4 (Rn : OnBytes.Model.Head.Run) [Good Rn.iU3 Rn] :
    PresQ Rn.iU3 (OnBytes.Model.Head.claimLedger4 Rn) := by
  unfold OnBytes.Model.Head.claimLedger4
  walkJ

open OnBytes.Model.Head in
/-- `Head.claimLedger`: its forms and what it returns are good. -/
instance pq_Model_Head_claimLedger (Rn : OnBytes.Model.Head.Run) [Good Rn.iU3 Rn] :
    PresQ Rn.iU3 (OnBytes.Model.Head.claimLedger Rn) := by
  unfold OnBytes.Model.Head.claimLedger
  walkJ

open OnBytes.Model.Head in
/-- `Head.claimStream`: its forms and what it returns are good. -/
instance pq_Model_Head_claimStream (Rn : OnBytes.Model.Head.Run) [Good Rn.iU3 Rn] :
    PresQ Rn.iU3 (OnBytes.Model.Head.claimStream Rn) := by
  unfold OnBytes.Model.Head.claimStream
  walkJ

open OnBytes.Model.Head in
/-- `Head.claimJoin`: its forms and what it returns are good. -/
instance pq_Model_Head_claimJoin (Rn : OnBytes.Model.Head.Run) [Good Rn.iU3 Rn] :
    PresQ Rn.iU3 (OnBytes.Model.Head.claimJoin Rn) := by
  unfold OnBytes.Model.Head.claimJoin
  walkJ

open OnBytes.Model.Head in
/-- `Head.claimPolicy`: its forms and what it returns are good. -/
instance pq_Model_Head_claimPolicy (Rn : OnBytes.Model.Head.Run) [Good Rn.iU3 Rn] :
    PresQ Rn.iU3 (OnBytes.Model.Head.claimPolicy Rn) := by
  unfold OnBytes.Model.Head.claimPolicy
  walkJ

open OnBytes.Model.Head in
/-- `Head.claimPlanes`: its forms and what it returns are good. -/
instance pq_Model_Head_claimPlanes (Rn : OnBytes.Model.Head.Run) [Good Rn.iU3 Rn] :
    PresQ Rn.iU3 (OnBytes.Model.Head.claimPlanes Rn) := by
  unfold OnBytes.Model.Head.claimPlanes
  walkJ

open OnBytes.Model.Head in
/-- `Head.claimLogits`: its forms and what it returns are good. -/
instance pq_Model_Head_claimLogits (Rn : OnBytes.Model.Head.Run) [Good Rn.iU3 Rn] :
    PresQ Rn.iU3 (OnBytes.Model.Head.claimLogits Rn) := by
  unfold OnBytes.Model.Head.claimLogits
  walkJ

open OnBytes.Model.Head in
/-- `Head.noteConstant`: its forms and what it returns are good. -/
instance pq_Model_Head_noteConstant (group : String) [Good t0 group] :
    PresQ t0 (OnBytes.Model.Head.noteConstant group) := by
  unfold OnBytes.Model.Head.noteConstant
  walkJ

/-! ## The runs -/

/-- What `Head.hear` returns is good, for every array. Its second step sets the number of slots,
which is no step of a walk; so the law is said of the value alone. -/
theorem head_hear_good (hS : Head.Shape) (Lh : Head.HL) (hp : Head.HPlanH2) (cov : Head.Covered)
    (plain : Array E) (x : Head.Heard) (F G : Fork) (c c' : Ctx)
    (hr : Head.hear hS Lh hp cov plain F c = .ok ((x, G), c')) : Good t0 x := by
  unfold Head.hear at hr
  obtain ⟨_, _, _, -, hr⟩ := (Port.bind_ok _ _ _ _ _).1 hr
  obtain ⟨_, _, _, -, hr⟩ := (Port.bind_ok _ _ _ _ _).1 hr
  exact ⟨(PresQ.out (t0 := t0) (self := by walkJ) _ _ _ _ _ hr).2⟩

/-- A run of «x, then f» in a routine that also calls the chain, where x is a lifted routine of the
sub-proof: f has run from a state that a walk reaches. -/
theorem peelQ {α β : Type} [HasGood α] {x : SubM α} {f : α → LinkM β} (hx : PresQ t0 x)
    {L : LinkCtx} {F : Fork} {c : Ctx} {r : ((β × LinkCtx) × Fork) × Ctx}
    (h : ((liftM x : LinkM α) >>= f) L F c = .ok r) :
    ∃ a L1 F1 c1, AddsIn t0 F F1 ∧ f a L1 F1 c1 = .ok r := by
  obtain ⟨a, L1, F1, c1, h1, h2⟩ := (bindL_ok _ _ _ _ _ _).1 h
  obtain ⟨h1, -⟩ := Walk.liftSubL_ok _ _ _ _ _ _ _ _ h1
  exact ⟨a, L1, F1, c1, (hx.out _ _ _ _ _ h1).1, h2⟩

/-- A run of `Head.walk` holds a run of objectsF; before it and after it the sub-proof's own claims
are added by a walk, and every entry of every form among them lies in array Rn.iU3. -/
theorem head_walk_adds (Rn : Head.Run) (tl tl' : HTailF2) (wo : WsForkOut) (L L' : LinkCtx)
    (F G' : Fork) (c c' : Ctx) [Good Rn.iU3 Rn] [Good Rn.iU3 wo]
    (h : Head.walk Rn tl wo L F c = .ok (((tl', L'), G'), c')) :
    ∃ F7 c7 G c9, AddsIn Rn.iU3 F F7 ∧ tl.objectsF Rn.t.funs F7 c7 = .ok ((tl', G), c9) ∧
      AddsIn Rn.iU3 G G' := by
  unfold Head.walk at h
  obtain ⟨_, _, _, _, k1, h⟩ := peelQ (t0 := Rn.iU3) inferInstance h
  obtain ⟨_, _, _, _, k2, h⟩ := peelQ (t0 := Rn.iU3) inferInstance h
  obtain ⟨_, _, _, _, k3, h⟩ := peelQ (t0 := Rn.iU3) inferInstance h
  obtain ⟨_, _, _, _, k4, h⟩ := peelQ (t0 := Rn.iU3) inferInstance h
  obtain ⟨_, _, _, _, k5, h⟩ := peelQ (t0 := Rn.iU3) inferInstance h
  obtain ⟨_, _, _, _, k6, h⟩ := peelQ (t0 := Rn.iU3) inferInstance h
  obtain ⟨_, _, _, _, k7, h⟩ := peelQ (t0 := Rn.iU3) inferInstance h
  obtain ⟨_, _, _, _, k8, h⟩ := peelQ (t0 := Rn.iU3) inferInstance h
  obtain ⟨_, _, _, _, k9, h⟩ := peelQ (t0 := Rn.iU3) inferInstance h
  obtain ⟨_, _, _, _, k10, h⟩ := peelQ (t0 := Rn.iU3) inferInstance h
  obtain ⟨_, _, _, _, k11, h⟩ := peelQ (t0 := Rn.iU3) inferInstance h
  obtain ⟨_, _, _, _, k12, h⟩ := peelQ (t0 := Rn.iU3) inferInstance h
  obtain ⟨_, _, _, _, k13, h⟩ := peelQ (t0 := Rn.iU3) inferInstance h
  obtain ⟨_, _, _, _, k14, h⟩ := peelQ (t0 := Rn.iU3) inferInstance h
  obtain ⟨tl1, L15, G, c15, ho, h⟩ := (bindL_ok _ _ _ _ _ _).1 h
  obtain ⟨ho, -⟩ := Walk.liftSubL_ok _ _ _ _ _ _ _ _ ho
  obtain ⟨_, _, _, _, k15, h⟩ := peelQ (t0 := Rn.iU3) inferInstance h
  obtain ⟨_, _, _, _, k16, h⟩ := peelQ (t0 := Rn.iU3) inferInstance h
  obtain ⟨_, _, _, _, k17, h⟩ := peelQ (t0 := Rn.iU3) inferInstance h
  obtain ⟨_, _, _, _, k18, h⟩ := peelQ (t0 := Rn.iU3) inferInstance h
  obtain ⟨_, _, _, _, k19, h⟩ := peelQ (t0 := Rn.iU3) inferInstance h
  obtain ⟨rfl, -, rfl, -⟩ := (pureL_ok _ _ _ _ _ _ _ _).1 h
  exact ⟨_, _, _, _,
    (((((((((((((k1.trans k2).trans k3).trans k4).trans k5).trans k6).trans k7).trans k8).trans
    k9).trans k10).trans k11).trans k12).trans k13).trans k14), ho,
    ((((k15.trans k16).trans k17).trans k18).trans k19)⟩

/-- The own claims of the head's sub-proof, from the runs of the hearing, of the merge's messages
and of `Head.walk`. -/
theorem head_adds (hS : Head.Shape) (Lh : Head.HL) (hp : Head.HPlanH2) (cov : Head.Covered)
    (plain : Array E) (wsLay : WsLay) (cl : Array WsClaim) (sv : Array Nat) (Rn : Head.Run)
    (tl tl' : HTailF2) (wo : WsForkOut) (L L' : LinkCtx) (F1 F2 F4 F5 F G' : Fork)
    (c1 c2 c4 c5 c c' : Ctx)
    (hh : Head.hear hS Lh hp cov plain F1 c1 = .ok ((Rn.x, F2), c2))
    (hwe : wsForkEnd wsLay cl sv F4 c4 = .ok ((wo, F5), c5))
    (h : Head.walk Rn tl wo L F c = .ok (((tl', L'), G'), c')) :
    ∃ F7 c7 G c9 l1 l3, OnBytes.Road.Rows.Adds F l1 F7 ∧
      (∀ a ∈ l1, ∀ e ∈ a.ents.toList, e.tree = Rn.iU3) ∧
      tl.objectsF Rn.t.funs F7 c7 = .ok ((tl', G), c9) ∧ OnBytes.Road.Rows.Adds G l3 G' ∧
      ∀ a ∈ l3, ∀ e ∈ a.ents.toList, e.tree = Rn.iU3 := by
  have hR : Good Rn.iU3 Rn := ⟨(head_hear_good hS Lh hp cov plain Rn.x F1 F2 c1 c2 hh).out⟩
  have hw : Good Rn.iU3 wo :=
    ⟨((inferInstance : PresQ Rn.iU3 (wsForkEnd wsLay cl sv)).out F4 c4 wo F5 c5 hwe).2⟩
  obtain ⟨F7, c7, G, c9, ⟨l1, a1, q1⟩, ho, ⟨l3, a3, q3⟩⟩ :=
    head_walk_adds Rn tl tl' wo L L' F G' c c' h
  exact ⟨F7, c7, G, c9, l1, l3, a1, q1, ho, a3, q3⟩

end OnBytes.Tie.Pv.Tail.Forms

#print axioms OnBytes.Tie.Pv.Tail.Forms.head_hear_good
#print axioms OnBytes.Tie.Pv.Tail.Forms.head_walk_adds
#print axioms OnBytes.Tie.Pv.Tail.Forms.head_adds
