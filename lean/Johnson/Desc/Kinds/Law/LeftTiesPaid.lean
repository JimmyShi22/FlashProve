-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/LeftTiesPaid.lean: LeftTies (Law/WeightTwinAt.lean: "the two ties that are
left" between the output head's claim on the weights and the claim that the plain text weightsClaim
makes), PAID FROM PUBLIC FACTS ON THE LAYOUT: (a) the program's weight of entry v of the segment
"HD0" reads as the text's ew .marginTop v, at every v < V; (b) so the two sums over the vocabulary.
Statements and proofs.

  ew_twin          (a) at one point on the columns and one column: by the law of fromLookup
                   (HeadInLaw.lean: LettersOk.column), Law/Columns.lean's columns_law (a column lies
                   below the number of columns) and Law/WeightTwin.lean's rd_eq_eqTab.
  wx_twin          (b) from (a): by LettersOk.wx and sumE_value'.
  leftTies_of_columns   at the seat: from three public facts: the logarithm of call 0's number of
                   columns is the text's; the segment's columns below V are the text's; it has at
                   least V entries.
  place_size, leftTies_of_place   the last two paid by Law/PlaceColumn.lean where call 0 is placed
                   by the layout's own rule at segments of the text's three lengths.

WHAT IT IS NOT. Implications. THAT THE LAYOUT's CALL NUMBER 0 IS SO PLACED, THAT ITS THIRD SEGMENT
IS THE ONE NAMED "HD0", AND THAT THE TWO LOGARITHMS ARE ONE ARE PREMISES HERE: facts in the goals'
scope (Goal/Meaning/HeadColsScope.lean has calls_six and cols_in_scope): that cone is
not imported. Nothing on soundness.
LETTERS. No letter stands under "there is".

-/
import Mathlib
import Johnson.Desc.Kinds.Law.WeightTwinAt
import Johnson.Desc.Kinds.Law.Columns
import Johnson.Desc.Kinds.Law.PlaceColumn

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

namespace VerifiableInference.Desc.Kinds.Head.Law

open OnBytes (E zeroE)
open OnBytes.Model (Reading eqTab)
open Norm (lt ls d)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.K11Caller (ewAt)

section Letters
variable [Sizes]

/-- **The program's weight of entry v of the segment is the text's**, at one point on the columns
and one column. -/
theorem ew_twin (floor : Nat) (zx : Point) (zk : Nat → Point) (hL : LettersOk floor zk
    (fromLookup floor zx zk)) (hP : PointsOk floor zx zk) (hlen : ∀ k, lenOf k < 2 ^ 41)
    (zj : Array E) (hz : zj = onColumns floor zk (.inr .marginTop)) (pos : Array Nat) (v : Nat)
    (hv : v < JV) (hs : v < pos.size) (hp : pos.getD v 0 = columnOf (.inr .marginTop) v) :
    rd ((pos.map fun p => (eqTab zj).getD p zeroE).getD v zeroE) =
      rd ((fromLookup floor zx zk).head.ew .marginTop v) := by
  have e1 : (pos.map fun p => (eqTab zj).getD p zeroE).getD v zeroE =
      (eqTab zj).getD (pos.getD v 0) zeroE := by
    simp [Array.getD, hs]
  have e2 := hL.column (.inr .marginTop) v hv
  have e2' : (fromLookup floor zx zk).head.ew .marginTop v =
      eq (onColumns floor zk (.inr .marginTop)) (columnOf (.inr .marginTop) v) := e2
  have hsz : (onColumns floor zk (.inr .marginTop)).size =
      lJ floor (keysOf (.inr .marginTop)) :=
    Came.size_extract0 (hP 0 _ rfl).1
  have hcol : columnOf (.inr .marginTop) v < 2 ^ (onColumns floor zk (.inr .marginTop)).size := by
    rw [hsz]
    have h1 := (Came.columns_law ((keysOf (.inr .marginTop)).map lenOf) (fun n hn => by
      obtain ⟨k, _, rfl⟩ := List.mem_map.1 hn
      exact hlen k)).1 2 v hv
    have h2 := Came.le_two_pow_clog2 ((keysOf (.inr .marginTop)).map lenOf).sum
    have h3 : 2 ^ clog2 ((keysOf (.inr .marginTop)).map lenOf).sum ≤
        2 ^ lJ floor (keysOf (.inr .marginTop)) :=
      Nat.pow_le_pow_right (by norm_num) (le_max_left _ _)
    exact lt_of_lt_of_le h1 (le_trans h2 h3)
  rw [e1, e2', hp, hz]
  exact (rd_eq_eqTab _ _ hcol).symm

/-- **And so the two sums over the vocabulary.** -/
theorem wx_twin (floor : Nat) (zx : Point) (zk : Nat → Point) (hL : LettersOk floor zk
    (fromLookup floor zx zk)) (ew : Array E) (hs : V ≤ ew.size) (hVJ : V ≤ JV)
    (h : ∀ v, v < V → rd (ew.getD v zeroE) = rd ((fromLookup floor zx zk).head.ew .marginTop v)) :
    rd (OnBytes.Model.sumE (ew.extract 0 V)) =
      rd ((fromLookup floor zx zk).head.wx .marginTop) := by
  have e1 : rd (OnBytes.Model.sumE (ew.extract 0 V)) = _ :=
    OnBytes.Road.Hd.sumE_value' Reading.gl (ew.extract 0 V)
  have hsz : (ew.extract 0 V).size = V := by
    rw [Array.size_extract]
    omega
  rw [e1, hsz, hL.wx .marginTop, rd_sumTo]
  have e2 : (Finset.range (len .marginTop)).sum (fun x => rd (if first .marginTop + x < V then
      (fromLookup floor zx zk).head.ew .marginTop x else 0)) =
      (Finset.range (len .marginTop)).sum fun x => if x < V then
        rd ((fromLookup floor zx zk).head.ew .marginTop x) else 0 := by
    refine Finset.sum_congr rfl fun x _ => ?_
    have e0 : first .marginTop + x = x := Nat.zero_add x
    rw [e0]
    split
    · rfl
    · exact rd_zero
  rw [e2, Came.sum_cut (show V ≤ len .marginTop from hVJ)]
  refine Finset.sum_congr rfl fun v hv => ?_
  have hv' := Finset.mem_range.1 hv
  rw [← h v hv']
  congr 1
  simp [Array.getD, hv', hsz, Nat.lt_of_lt_of_le hv' hs]

end Letters

/-- **LeftTies, PAID**, from three public facts on the layout's call number 0 and its segment: the
logarithm of its number of columns is the text's; the segment's columns below V are the text's; it
has at least V entries. s: a verifier's state at which the kind's letters are given; gk: what the
lookup heard there; x: a stored hearing that hands gk through. -/
theorem leftTies_of_columns (W : OnBytes.Model.Verify.Public) {s : S} {g : Given}
    {gk : OnBytes.Model.Forest.Heard} (cov : OnBytes.Model.Head.Covered)
    (x : OnBytes.Model.Head.Heard) (t : OnBytes.Model.Head.Tables) (sg : OnBytes.Model.Seg)
    (hg : given (parOf W.hS (workOf W)) (seatAt W.hS (readsOf W)) s = .ok g)
    (hgk : s.lookHeard? = some gk) (hx : x.g1 = gk)
    (hplan : (parOf W.hS (workOf W)).ok = true)
    (hlJ : (W.HLy.calls.getD 0 default).lJ =
      @lJ (sizesOf W.hS) (parOf W.hS (workOf W)).floor (callKeys 0))
    (hpos : ∀ v, v < W.hS.V → sg.pos.getD v 0 = @columnOf (sizesOf W.hS) (.inr .marginTop) v)
    (hsz : W.hS.V ≤ sg.pos.size) :
    LeftTies W g cov x t (ewAt (runAt W cov x t) 0 sg) := by
  obtain ⟨z0, y, hz0, _, _, rfl⟩ := Came.given_ok _ _ _ _ hg
  obtain ⟨z, hz, hP, _, _, _, hL⟩ :=
    Came.given_letters _ _ _ _ hg (parOf W.hS (workOf W)).sT hplan
  obtain rfl : z0 = z := Option.some.inj (hz0.symm.trans hz)
  have hzz : z0 = (gk.zx, fun c => gk.zk.getD c #[]) := by
    have h0 : s.lookHeard?.map (fun g => (g.zx, fun c => g.zk.getD c #[])) = some z0 := hz0
    rw [hgk] at h0
    exact (Option.some.inj h0).symm
  subst hzz
  letI : Sizes := sizesOf W.hS
  letI : Policy := (parOf W.hS (workOf W)).policy
  letI : Request := (seatAt W.hS (readsOf W)).request s
  letI : Token := ⟨y⟩
  have hlen : ∀ k, lenOf k < 2 ^ 41 := Came.lens_small (sT := (parOf W.hS (workOf W)).sT) hplan
  have hzj : OnBytes.Model.Head.zjOf W.HLy x.g1 0 =
      onColumns (parOf W.hS (workOf W)).floor (fun c => gk.zk.getD c #[]) (.inr .marginTop) := by
    unfold OnBytes.Model.Head.zjOf onColumns
    rw [hx, hlJ]
    rfl
  have ha : ∀ v, v < V → rd ((ewAt (runAt W cov x t) 0 sg).getD v zeroE) =
      rd ((fromLookup (parOf W.hS (workOf W)).floor gk.zx
        fun c => gk.zk.getD c #[]).head.ew .marginTop v) := fun v hv =>
    ew_twin _ _ _ hL hP hlen _ hzj sg.pos v (Nat.lt_of_lt_of_le hv V_le_JV)
      (Nat.lt_of_lt_of_le hv hsz) (hpos v hv)
  refine ⟨ha, ?_⟩
  exact wx_twin _ _ _ hL _ (by
    show V ≤ (sg.pos.map _).size
    rw [Array.size_map]
    exact hsz) V_le_JV ha

/-- A placed segment has at least as many columns as entries. -/
theorem place_size (name kind : String) (asks : List OnBytes.Model.SegAsk) (fl a : Nat)
    (ha : a < asks.length) : (asks.map (·.2.1)).getD a 0 ≤
      ((OnBytes.Model.place name kind asks fl).segs.getD a default).pos.size := by
  rw [OnBytes.Road.place_columns name kind asks fl a ha]
  unfold OnBytes.Model.columnsOf
  simp only [Array.size_append, Array.size_replicate]
  omega

/-- **LeftTies, PAID, WHERE THE LAYOUT's CALL NUMBER 0 IS PLACED BY THE LAYOUT's OWN RULE** at three
segments of the text's three lengths (d, d, JV): at its third segment. -/
theorem leftTies_of_place (W : OnBytes.Model.Verify.Public) {s : S} {g : Given}
    {gk : OnBytes.Model.Forest.Heard} (cov : OnBytes.Model.Head.Covered)
    (x : OnBytes.Model.Head.Heard) (t : OnBytes.Model.Head.Tables)
    (hg : given (parOf W.hS (workOf W)) (seatAt W.hS (readsOf W)) s = .ok g)
    (hgk : s.lookHeard? = some gk) (hx : x.g1 = gk)
    (hplan : (parOf W.hS (workOf W)).ok = true)
    (hlJ : (W.HLy.calls.getD 0 default).lJ =
      @lJ (sizesOf W.hS) (parOf W.hS (workOf W)).floor (callKeys 0))
    (name kind : String) (asks : List OnBytes.Model.SegAsk) (fl : Nat)
    (hcall : W.HLy.calls.getD 0 default = OnBytes.Model.place name kind asks fl)
    (hasks : asks.map (·.2.1) = (keysOf (.inr .marginTop)).map (@lenOf (sizesOf W.hS))) :
    LeftTies W g cov x t
      (ewAt (runAt W cov x t) 0 ((W.HLy.calls.getD 0 default).segs.getD 2 default)) := by
  obtain ⟨_, y, _, _, _, _⟩ := Came.given_ok _ _ _ _ hg
  letI : Sizes := sizesOf W.hS
  letI : Policy := (parOf W.hS (workOf W)).policy
  letI : Request := (seatAt W.hS (readsOf W)).request s
  letI : Token := ⟨y⟩
  have hlen : ∀ k, lenOf k < 2 ^ 41 := Came.lens_small (sT := (parOf W.hS (workOf W)).sT) hplan
  have h3 : 2 < asks.length := by
    have := congrArg List.length hasks
    rw [List.length_map, List.length_map] at this
    rw [this]
    decide
  have hn : (asks.map (·.2.1)).getD 2 0 = JV := by
    rw [hasks]
    rfl
  refine leftTies_of_columns W cov x t _ hg hgk hx hplan hlJ (fun v hv => ?_) ?_
  · rw [hcall, place_column name kind asks fl 2 v h3 (fun n hn' => by
      rw [hasks] at hn'
      obtain ⟨k, _, rfl⟩ := List.mem_map.1 hn'
      exact hlen k) (by rw [hn]; exact Nat.lt_of_lt_of_le hv V_le_JV), hasks]
    rfl
  · rw [hcall]
    refine le_trans ?_ (place_size name kind asks fl 2 h3)
    rw [hn]
    exact V_le_JV

end VerifiableInference.Desc.Kinds.Head.Law

#print axioms VerifiableInference.Desc.Kinds.Head.Law.leftTies_of_place
#print axioms VerifiableInference.Desc.Kinds.Head.Law.leftTies_of_columns
