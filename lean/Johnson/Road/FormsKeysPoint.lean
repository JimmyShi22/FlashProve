-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/FormsKeysPoint.lean: one point serves all calls of the lookup, and the names Z and zt
stand for it.

The record Fits (Johnson/Road/FormsKeysKit.lean) speaks of a point (low | u): the tables found under
"…@Z" are true at (low | u), those under "…@zt" at u. The theorem on a call's factor in the lookup's
join (joinPart_of_layout, Johnson/Road/FormsKeysAdmit.lean) asks two things of the call's own point.
This file ties these points to the verifier's. Let zx be the lookup's point, Z its last la
coordinates and zt its last lt, as the verifier takes them. With low := the coordinates of Z and
u := those of zt:
 - zt is Z without its first ls coordinates, so Z is (low | u) (token_point);
 - if the verifier's test that the last la coordinates of every call's point equal Z has passed, and
   a call's point has the length that another test asks (size_of_test), the two hypotheses on that
   call's point hold, for all calls with this one low, and the last lt coordinates of each call's
   point are zt (ends_all, call_point, call_token, calls_share; joinPart_of_run, in any world with
   true tables);
 - in the verifier's list of points by name, "Z" is Z and "zt" is zt (pointsOf_names);
 - no two families of tables have one name (names_nodup), so a family is known by its name, and the
   families with the four names "…@Z" and the two names "…@zt" get from the verifier the weights of
   a long table at Z and the equality weights of zt (weights_of_names);
 - these weights, read in the field, are eq(low, r) eq(u, i) at the row of (r, i), and eq(u, i)
   (longPhi_value, eqTab_value), so LongTrue and ShortTrue at this point say that an entry is the
   sum of its cells under the verifier's own weights (longTrue_iff_phi, shortTrue_iff_phi);
 - each part of a family that layTables has laid has a table with these weights and its own first
   entry in the verifier's list of tables (layTables_laid, funsOf_mem);
 - all of this together, from the verifier's lines alone (tables_of_run, with trueAt_iff_summed).

Main definitions: longNames, shortNames, allNames, SummedAt.

What is not claimed. The verifier's tests on the points are hypotheses here, in its own words; that
a run which ends well has passed them is not derived from the run, nor that the lookup's own list of
calls is the layout's. What the smallness test does with the list of tables is not looked at, nor in
which order the entries of one part's table stand for columns and blocks of rows: that entry number
b of a family belongs to block b of its matrix stays the reading of LongTrue. See also
Johnson/Road/FormsKeysKit.lean. The program does not import this file.
-/
import Johnson.Road.FormsKeysAdmit
import Johnson.Road.FormsKeysPan
import OnBytes.Model.Layer

set_option autoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road

open Finset
open OnBytes.Model (Reading World Aff Seg CallD lastOf cutLast eqTab longPhi blockRows Level HFun)
open OnBytes.Model.Layer (Env Lay Shape Heard Reads TableAsk TableAt pointsOf phiOf funsOf readsOf
  tableAsks layTables layParts layout scalesHeld)
open Inst.Model (Scl Tables)
open Inst.Model.FFSeg (Dim Fam LW lin len)

variable {K : Type} [Field K] (ρ : Reading K)

/-! ## The last coordinates of a point -/

omit [Field K] in
/-- What lastOf returns: the point has at least k coordinates, and the result is its last k. -/
theorem lastOf_ok {z Z : Array E} {k : ℕ} (h : lastOf z k = .ok Z) :
    k ≤ z.size ∧ Z = z.extract (z.size - k) z.size := by
  have h' : (do
      pure (← (if k > z.size then Except.error "plan-tensor-layout"
        else Except.ok (z.extract 0 (z.size - k), z.extract (z.size - k) z.size) :
          Except String (Array E × Array E))).2) = Except.ok Z := h
  by_cases hk : k > z.size
  · rw [if_pos hk] at h'
    cases h'
  · rw [if_neg hk] at h'
    exact ⟨by omega, (Except.ok.inj h').symm⟩

omit [Field K] in
/-- An entry of a stretch of an array. -/
theorem getD_extract {α : Type} (z : Array α) {a b j : ℕ} (hb : b ≤ z.size) (hj : a + j < b)
    (d : α) : (z.extract a b).getD j d = z.getD (a + j) d := by
  have h1 : j < min b z.size - a := by omega
  have h2 : a + j < z.size := by omega
  simp [Array.getD, h1, h2]

omit [Field K] in
/-- The last k coordinates are k. -/
theorem size_last {z Z : Array E} {k : ℕ} (h : lastOf z k = .ok Z) : Z.size = k := by
  obtain ⟨hk, rfl⟩ := lastOf_ok h
  rw [Array.size_extract]
  omega

/-- Coordinate j of the last k coordinates of a point. -/
theorem pt_last {z Z : Array E} {k : ℕ} (h : lastOf z k = .ok Z) {j : ℕ} (hj : j < k) :
    pt ρ Z j = pt ρ z (z.size - k + j) := by
  obtain ⟨hk, rfl⟩ := lastOf_ok h
  unfold pt
  rw [getD_extract z (Nat.le_refl _) (by omega)]

/-! ## The point of a call -/

/-- The point of call q, which has 2^lJ columns, against the lookup's point. Asked: the call's point
has the ll coordinates of the layer, the lJ of the column and the lt of the token; its last la
coordinates are Z; a block's row has the ls low bits of a feature and the lt bits of a token; a call
has at least 2^ls columns. Then the point is long enough for the layer and the column, and the last
ls coordinates of the column are the first ls of Z. -/
theorem call_point (v : Env) {q lJ : ℕ} {Z : Array E}
    (hn : (v.zk.getD q #[]).size = v.y.h.ll + lJ + v.y.h.lt)
    (hend : lastOf (v.zk.getD q #[]) v.y.h.la = .ok Z) (hla : v.y.h.la = v.y.ls + v.y.h.lt)
    (hls : v.y.ls ≤ lJ) :
    v.y.h.ll + lJ ≤ (v.zk.getD q #[]).size ∧
      ∀ j, j < v.y.ls → pt ρ Z j = pt ρ (v.zj q lJ) (lJ - v.y.ls + j) := by
  refine ⟨by omega, fun j hj => ?_⟩
  rw [pt_last ρ hend (by omega)]
  unfold pt Env.zj
  rw [getD_extract _ (by omega) (by omega)]
  have e : (v.zk.getD q #[]).size - v.y.h.la + j = v.y.h.ll + (lJ - v.y.ls + j) := by omega
  rw [e]

/-- The token point against the lookup's point: if Z is the last la = ls + lt coordinates of a point
and zt its last lt, then zt is Z without its first ls coordinates. -/
theorem token_point {zx Z zt : Array E} {la ls lt : ℕ} (hZ : lastOf zx la = .ok Z)
    (hzt : lastOf zx lt = .ok zt) (hla : la = ls + lt) :
    ∀ j, j < lt → pt ρ zt j = pt ρ Z (ls + j) := by
  intro j hj
  obtain ⟨hk, _⟩ := lastOf_ok hZ
  rw [pt_last ρ hzt hj, pt_last ρ hZ (by omega)]
  have e : zx.size - lt + j = zx.size - la + (ls + j) := by omega
  rw [e]

/-- The token part of a call's point. Under the hypotheses of call_point, if zt is Z without its
first ls coordinates, the last lt coordinates of the call's point are zt. -/
theorem call_token (v : Env) {q lJ : ℕ} {Z zt : Array E}
    (hn : (v.zk.getD q #[]).size = v.y.h.ll + lJ + v.y.h.lt)
    (hend : lastOf (v.zk.getD q #[]) v.y.h.la = .ok Z) (hla : v.y.h.la = v.y.ls + v.y.h.lt)
    (hls : v.y.ls ≤ lJ) (hu : ∀ j, j < v.y.h.lt → pt ρ zt j = pt ρ Z (v.y.ls + j)) :
    ∀ j, j < v.y.h.lt → pt ρ zt j = pt ρ (v.zk.getD q #[]) (v.y.h.ll + lJ + j) := by
  intro j hj
  rw [hu j hj, pt_last ρ hend (by omega)]
  have e : (v.zk.getD q #[]).size - v.y.h.la + (v.y.ls + j) = v.y.h.ll + lJ + j := by omega
  rw [e]

/-! ## The test that the verifier runs on the calls' points -/

omit [Field K] in
/-- The verifier takes the last la coordinates of every call's point and tests that each result
equals Z. If it has taken them all and the test has passed, the last la coordinates of every call's
point are Z. -/
theorem ends_all {zk ends : Array (Array E)} {la : ℕ} {Z : Array E}
    (hm : zk.mapM (fun z => (lastOf z la).toOption) = some ends)
    (ha : ends.all (· == Z) = true) : ∀ q, q < zk.size → lastOf (zk.getD q #[]) la = .ok Z := by
  intro q hq
  rw [Array.mapM_eq_mapM_toList] at hm
  obtain ⟨l, hl, rfl⟩ := map_some hm
  obtain ⟨_, hi⟩ := list_mapM_some _ _ _ hl
  have hz : zk.toList[q]? = some (zk.getD q #[]) := by simp [Array.getD, hq]
  obtain ⟨b, hb, hf⟩ := hi q _ hz
  have hbm : b ∈ l := List.mem_of_getElem? hb
  have hbZ : b = Z := by
    have h1 : ∀ x ∈ l, (x == Z) = true := by simpa using ha
    exact eq_of_beq (h1 b hbm)
  subst hbZ
  cases hx : lastOf (zk.getD q #[]) la with
  | error e => rw [hx] at hf; cases hf
  | ok a =>
    rw [hx] at hf
    have : a = b := Option.some.inj hf
    rw [this]

/-! ## The names Z and zt -/

omit [Field K] in
/-- A value that is kept when a refusal's name is dropped was returned. -/
theorem ok_of_toOption {α : Type} {x : Except String α} {a : α} (h : x.toOption = some a) :
    x = .ok a := by
  cases x with
  | error e => cases h
  | ok b =>
    have e : b = a := Option.some.inj h
    rw [e]

omit [Field K] in
/-- In the verifier's list of points by name, Z is the last la coordinates of the lookup's point,
and zt is the token point that the verifier has kept. -/
theorem pointsOf_names {y : Lay} {H : Heard} {hd : Level} {hd2 : Option Level}
    {pts : List (String × Array E)} (h : pointsOf y H hd hd2 = some pts) :
    ∃ Z, lastOf H.fo.zx y.h.la = .ok Z ∧ pts.find? (fun p => p.1 == "Z") = some ("Z", Z) ∧
      pts.find? (fun p => p.1 == "zt") = some ("zt", H.ztF) := by
  unfold pointsOf at h
  obtain ⟨Z, hZ, h⟩ := bind_some h
  cases hd2 with
  | none =>
    obtain ⟨routed, _, h⟩ := bind_some h
    obtain ⟨a, _, h⟩ := bind_some h
    obtain ⟨b, _, h⟩ := bind_some h
    have e := Option.some.inj h
    subst e
    exact ⟨Z, ok_of_toOption hZ, rfl, rfl⟩
  | some o =>
    obtain ⟨routed, _, h⟩ := bind_some h
    obtain ⟨a, _, h⟩ := bind_some h
    obtain ⟨b, _, h⟩ := bind_some h
    have e := Option.some.inj h
    subst e
    exact ⟨Z, ok_of_toOption hZ, rfl, rfl⟩

/-! ## The weights of a table at these points -/

omit [Field K] in
/-- Entry r n + i of a list that is made of one list of n members for each member of l. -/
theorem flatMap_getElem? {α β : Type} (g : α → List β) (n : ℕ) : ∀ (l : List α),
    (∀ a ∈ l, (g a).length = n) → ∀ (r i : ℕ) (a : α), l[r]? = some a → i < n →
    (l.flatMap g)[r * n + i]? = (g a)[i]?
  | [], _, r, i, a, h, _ => by simp at h
  | x :: l, hl, 0, i, a, h, hi => by
    have e : x = a := by simpa using h
    subst e
    rw [List.flatMap_cons, Nat.zero_mul, Nat.zero_add,
      List.getElem?_append_left (by rw [hl x List.mem_cons_self]; exact hi)]
  | x :: l, hl, r + 1, i, a, h, hi => by
    have h' : l[r]? = some a := by simpa using h
    have e : (r + 1) * n + i = (g x).length + (r * n + i) := by
      rw [hl x List.mem_cons_self]
      ring
    rw [List.flatMap_cons, e, List.getElem?_append_right (Nat.le_add_right _ _),
      Nat.add_sub_cancel_left]
    exact flatMap_getElem? g n l (fun a ha => hl a (List.mem_cons_of_mem _ ha)) r i a h' hi

omit [Field K] in
/-- The weight of the row of (r, i) in a block: low[r] tok[i]. -/
theorem blockRows_getD (low tok : Array E) {r i : ℕ} (hr : r < low.size) (hi : i < tok.size) :
    (blockRows low tok).getD (r * tok.size + i) zeroE =
      mulE (low.getD r zeroE) (tok.getD i zeroE) := by
  have h1 : (blockRows low tok).toList =
      low.toList.flatMap fun a => tok.toList.map fun b => mulE a b := by
    simp [blockRows, Array.toList_flatMap]
  have h2 := flatMap_getElem? (fun a => tok.toList.map fun b => mulE a b) tok.size low.toList
    (by intro a _; simp) r i (low.getD r zeroE) (by simp [Array.getD, hr]) hi
  rw [← h1] at h2
  rw [Array.getD_eq_getD_getElem?, ← Array.getElem?_toList, h2]
  simp [Array.getD, hi]

/-- The weights of a long table at a point Z of ls + lt coordinates: the row of the feature with the
low bits r and of the token i has the equality weight of the first ls coordinates at r times that of
the last lt at i. -/
theorem longPhi_value {Z : Array E} {ls lt : ℕ} (hs : Z.size = ls + lt) {r i : ℕ}
    (hr : r < 2 ^ ls) (hi : i < 2 ^ lt) :
    ρ.val ((longPhi Z ls lt).getD (r * 2 ^ lt + i) zeroE) =
      Blocks.eqN ls 0 (pt ρ Z) r * Blocks.eqN lt 0 (fun j => pt ρ Z (ls + j)) i := by
  unfold longPhi
  have s1 : (Z.extract 0 ls).size = ls := by
    rw [Array.size_extract]
    omega
  have s2 : (Z.extract ls (ls + lt)).size = lt := by
    rw [Array.size_extract]
    omega
  have t1 := eqTab_size (Z.extract 0 ls)
  have t2 := eqTab_size (Z.extract ls (ls + lt))
  rw [s1] at t1
  rw [s2] at t2
  have e : r * 2 ^ lt + i = r * (eqTab (Z.extract ls (ls + lt))).size + i := by rw [t2]
  rw [e, blockRows_getD _ _ (by rw [t1]; exact hr) (by rw [t2]; exact hi), ρ.mul,
    eqTab_value ρ _ _ (by rw [s1]; exact hr), eqTab_value ρ _ _ (by rw [s2]; exact hi), s1, s2]
  congr 1
  · refine eqN_congr' ls 0 (fun j hj => ?_) r
    unfold pt
    rw [Nat.zero_add, getD_extract Z (by omega) (by omega), Nat.zero_add]
  · refine eqN_congr' lt 0 (fun j hj => ?_) i
    show pt ρ (Z.extract ls (ls + lt)) (0 + j) = pt ρ Z (ls + (0 + j))
    unfold pt
    rw [Nat.zero_add, getD_extract Z (by omega) (by omega)]

/-- What an entry of a long table stands for (longAt in Johnson/Road/FormsKeysWorld.lean), at the
point whose feature part is the first ls coordinates of Z and whose token part is the last lt: the
sum of the block's cells under the weights that the verifier makes from Z. -/
theorem longAt_phi {Z : Array E} {ls lt : ℕ} (hs : Z.size = ls + lt) (c : Cells K) (mat b : ℕ) :
    longAt ls lt c (pt ρ Z) (fun j => pt ρ Z (ls + j)) mat b =
      ∑ r ∈ range (2 ^ ls), ∑ i ∈ range (2 ^ lt),
        ρ.val ((longPhi Z ls lt).getD (r * 2 ^ lt + i) zeroE) * c mat (b * 2 ^ ls + r) i := by
  unfold longAt Blocks.ext
  refine sum_congr rfl fun r hr => ?_
  rw [mul_sum]
  refine sum_congr rfl fun i hi => ?_
  rw [longPhi_value ρ hs (mem_range.mp hr) (mem_range.mp hi)]
  ring

/-- What an entry of a short table stands for (shortAt), at the point zt: the sum of the feature's
cells under the weights that the verifier makes from zt. -/
theorem shortAt_phi (zt : Array E) (c : Cells K) (mat φ : ℕ) :
    shortAt zt.size c (pt ρ zt) mat φ =
      ∑ i ∈ range (2 ^ zt.size), ρ.val ((eqTab zt).getD i zeroE) * c mat φ i := by
  unfold shortAt Blocks.ext
  refine sum_congr rfl fun i hi => ?_
  rw [eqTab_value ρ zt i (mem_range.mp hi)]

omit [Field K] in
/-- The weights that the verifier gives to a long family whose point has the name Z. -/
theorem phiOf_long {y : Lay} {fo : Model.Forest.Heard} {pts : List (String × Array E)}
    {a : TableAsk} {Z : Array E} (h0 : (a.name == "b-bits-0") = false)
    (h1 : (a.name == "b-bits-1") = false) (h2 : (a.name == "b-pin") = false)
    (hp : a.point = "Z") (hl : a.lng = true)
    (hf : pts.find? (fun p => p.1 == "Z") = some ("Z", Z)) (hs : Z.size = y.h.la) :
    phiOf y fo pts a = some (longPhi Z y.ls y.h.lt) := by
  unfold phiOf
  rw [h0, h1, h2, hp, hf, hl]
  simp [hs]

omit [Field K] in
/-- The weights that the verifier gives to a short family whose point has the name zt. -/
theorem phiOf_short {y : Lay} {fo : Model.Forest.Heard} {pts : List (String × Array E)}
    {a : TableAsk} {zt : Array E} (h0 : (a.name == "b-bits-0") = false)
    (h1 : (a.name == "b-bits-1") = false) (h2 : (a.name == "b-pin") = false)
    (hp : a.point = "zt") (hl : a.lng = false)
    (hf : pts.find? (fun p => p.1 == "zt") = some ("zt", zt)) (hs : zt.size = y.h.lt) :
    phiOf y fo pts a = some (eqTab zt) := by
  unfold phiOf
  rw [h0, h1, h2, hp, hf, hl]
  simp [hs]

/-! ## No two families have one name -/

omit [Field K] in
/-- A list that is there or not is a part of the list. -/
theorem ite_sublist {α : Type} (c : Prop) [Decidable c] (l : List α) :
    (if c then l else []).Sublist l := by
  split_ifs
  · exact List.Sublist.refl _
  · exact List.nil_sublist _

/-- All names of points of long tables. -/
def longNames : List String := ["Z"] ++ ["Z_V"] ++ ["Y"] ++ (["Z_a"] ++ ["Z_b"])

/-- All names of points of short tables. -/
def shortNames : List String := ["zt"] ++ ["P_V", "r_tV"] ++ ["rt"]

omit [Field K] in
/-- Each list of points that readsOf returns is a part of the list of all names of its kind, in that
list's order. -/
theorem readsOf_sublist {y : Lay} {rd : Reads} (h : readsOf y = .ok rd) :
    rd.rdAF.Sublist longNames ∧ rd.rdQA.Sublist longNames ∧ rd.rdXI.Sublist longNames ∧
    rd.rdXO.Sublist longNames ∧ rd.rdAD.Sublist shortNames ∧ rd.rdAR.Sublist shortNames ∧
    rd.rdQS.Sublist shortNames := by
  unfold readsOf at h
  have h2 := refuse_bind h
  have e := (Except.ok.inj h2).symm
  subst e
  have L : ∀ (a b c d e : Prop) [Decidable a] [Decidable b] [Decidable c] [Decidable d]
      [Decidable e], ((if a then ["Z"] else []) ++ (if b then ["Z_V"] else []) ++
        (if c then ["Y"] else []) ++
        (if d then ["Z_a"] ++ (if e then ["Z_b"] else []) else [])).Sublist longNames := by
    intro a b c d e _ _ _ _ _
    exact (((ite_sublist a _).append (ite_sublist b _)).append (ite_sublist c _)).append
      ((ite_sublist d _).trans ((List.Sublist.refl _).append (ite_sublist e _)))
  have S : ∀ (a b c : Prop) [Decidable a] [Decidable b] [Decidable c],
      ((if a then ["zt"] else []) ++ (if b then ["P_V", "r_tV"] else []) ++
        (if c then ["rt"] else [])).Sublist shortNames := by
    intro a b c _ _ _
    exact ((ite_sublist a _).append (ite_sublist b _)).append (ite_sublist c _)
  exact ⟨L _ _ _ _ _, L _ _ _ _ _, L _ _ _ _ _, L _ _ _ _ _, S _ _ _, S _ _ _, S _ _ _⟩

/-- All names that a family of tables can have. -/
def allNames : List String :=
  longNames.map (fun n => "af" ++ "@" ++ n) ++ longNames.map (fun n => "qa" ++ "@" ++ n) ++
  longNames.map (fun n => "xbI" ++ "@" ++ n) ++ ["xbI" ++ "@" ++ "Z_E"] ++
  longNames.map (fun n => "xbO" ++ "@" ++ n) ++ shortNames.map (fun n => "ad" ++ "@" ++ n) ++
  shortNames.map (fun n => "ar" ++ "@" ++ n) ++ shortNames.map (fun n => "qa" ++ "@" ++ n) ++
  ["b-bits-0", "b-bits-1", "b-pin"]

omit [Field K] in
/-- These names differ from one another. -/
theorem allNames_nodup : allNames.Nodup := by
  simp [allNames, longNames, shortNames]

omit [Field K] in
/-- With the points that readsOf returns, no two families of a group have one name. -/
theorem names_nodup {y : Lay} {rd : Reads} (h : readsOf y = .ok rd) (g : ℕ) :
    ((tableAsks y rd g).map (·.name)).Nodup := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := readsOf_sublist h
  refine List.Nodup.sublist ?_ allNames_nodup
  rw [tableAsks_names]
  exact ((((((((h1.map _).append (h2.map _)).append (h3.map _)).append
    (ite_sublist _ _)).append (h4.map _)).append (h5.map _)).append (h6.map _)).append
    ((ite_sublist _ _).trans (h7.map _))).append (List.Sublist.refl _)

omit [Field K] in
/-- The families that are asked for the six matrices at the lookup's point: each has the name that
the forms read, the point's name, and the kind of table. -/
theorem six_asks (y : Lay) (rd : Reads) (g : ℕ) (hAF : "Z" ∈ rd.rdAF) (hQA : "Z" ∈ rd.rdQA)
    (hXI : "Z" ∈ rd.rdXI) (hXO : "Z" ∈ rd.rdXO) (hAD : "zt" ∈ rd.rdAD) (hAR : "zt" ∈ rd.rdAR) :
    (∀ n ∈ ["af" ++ "@" ++ "Z", "qa" ++ "@" ++ "Z", "xbI" ++ "@" ++ "Z", "xbO" ++ "@" ++ "Z"],
      ∃ a ∈ tableAsks y rd g, a.name = n ∧ a.point = "Z" ∧ a.lng = true) ∧
    (∀ n ∈ ["ad" ++ "@" ++ "zt", "ar" ++ "@" ++ "zt"],
      ∃ a ∈ tableAsks y rd g, a.name = n ∧ a.point = "zt" ∧ a.lng = false) := by
  have m : ∀ (f : String → TableAsk) (p : String) (l : List String), p ∈ l → f p ∈ l.map f :=
    fun f p l h => List.mem_map.mpr ⟨p, h, rfl⟩
  have a1 : ∃ a ∈ tableAsks y rd g, a.name = "af" ++ "@" ++ "Z" ∧ a.point = "Z" ∧ a.lng = true :=
    ⟨_, List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
      (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
        (List.mem_append_left _ (List.mem_append_left _ (m _ _ _ hAF)))))))), rfl, rfl, rfl⟩
  have a2 : ∃ a ∈ tableAsks y rd g, a.name = "qa" ++ "@" ++ "Z" ∧ a.point = "Z" ∧ a.lng = true :=
    ⟨_, List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
      (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
        (List.mem_append_left _ (List.mem_append_right _ (m _ _ _ hQA)))))))), rfl, rfl, rfl⟩
  have a3 : ∃ a ∈ tableAsks y rd g, a.name = "xbI" ++ "@" ++ "Z" ∧ a.point = "Z" ∧ a.lng = true :=
    ⟨_, List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
      (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
        (List.mem_append_right _ (m _ _ _ hXI))))))), rfl, rfl, rfl⟩
  have a4 : ∃ a ∈ tableAsks y rd g, a.name = "xbO" ++ "@" ++ "Z" ∧ a.point = "Z" ∧ a.lng = true :=
    ⟨_, List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
      (List.mem_append_left _ (List.mem_append_right _ (m _ _ _ hXO))))), rfl, rfl, rfl⟩
  have a5 : ∃ a ∈ tableAsks y rd g, a.name = "ad" ++ "@" ++ "zt" ∧ a.point = "zt" ∧
      a.lng = false :=
    ⟨_, List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
      (List.mem_append_right _ (m _ _ _ hAD)))), rfl, rfl, rfl⟩
  have a6 : ∃ a ∈ tableAsks y rd g, a.name = "ar" ++ "@" ++ "zt" ∧ a.point = "zt" ∧
      a.lng = false :=
    ⟨_, List.mem_append_left _ (List.mem_append_left _
      (List.mem_append_right _ (m _ _ _ hAR))), rfl, rfl, rfl⟩
  refine ⟨fun n hn => ?_, fun n hn => ?_⟩
  · rcases List.mem_cons.mp hn with e | hn
    · rw [e]; exact a1
    rcases List.mem_cons.mp hn with e | hn
    · rw [e]; exact a2
    rcases List.mem_cons.mp hn with e | hn
    · rw [e]; exact a3
    rcases List.mem_cons.mp hn with e | hn
    · rw [e]; exact a4
    · simp at hn
  · rcases List.mem_cons.mp hn with e | hn
    · rw [e]; exact a5
    rcases List.mem_cons.mp hn with e | hn
    · rw [e]; exact a6
    · simp at hn

/-! ## The weights of the six families -/

omit [Field K] in
/-- With the points that readsOf returns, a family is known by its name. -/
theorem ask_of_name {y : Lay} {rd : Reads} (hrd : readsOf y = .ok rd) {g : ℕ} {a a' : TableAsk}
    (ha : a ∈ tableAsks y rd g) (ha' : a' ∈ tableAsks y rd g) (e : a.name = a'.name) : a = a' :=
  List.inj_on_of_nodup_map (names_nodup hrd g) ha ha' e

omit [Field K] in
/-- None of the six names is a name of a table on the matrix of counts. -/
theorem six_not_b : ∀ n ∈ ["af" ++ "@" ++ "Z", "qa" ++ "@" ++ "Z", "xbI" ++ "@" ++ "Z",
    "xbO" ++ "@" ++ "Z", "ad" ++ "@" ++ "zt", "ar" ++ "@" ++ "zt"],
    (n == "b-bits-0") = false ∧ (n == "b-bits-1") = false ∧ (n == "b-pin") = false := by
  simp

omit [Field K] in
/-- The names Z and zt, tied to the points. Whatever family of the group has one of the four names
…@Z gets, from the verifier's phiOf, the weights of a long table at Z, the last la coordinates of
the lookup's point. Whatever family has one of the two names …@zt gets the equality weights of the
token point. hzt: the line of the verifier that makes the token point. -/
theorem weights_of_names {y : Lay} {rd : Reads} (hrd : readsOf y = .ok rd) (g : ℕ)
    (hAF : "Z" ∈ rd.rdAF) (hQA : "Z" ∈ rd.rdQA) (hXI : "Z" ∈ rd.rdXI) (hXO : "Z" ∈ rd.rdXO)
    (hAD : "zt" ∈ rd.rdAD) (hAR : "zt" ∈ rd.rdAR) {H : Heard} {hd : Level} {hd2 : Option Level}
    {pts : List (String × Array E)} (hp : pointsOf y H hd hd2 = some pts)
    (hzt : lastOf H.fo.zx y.h.lt = .ok H.ztF) :
    ∃ Z, lastOf H.fo.zx y.h.la = .ok Z ∧
      (∀ a ∈ tableAsks y rd g, a.name ∈ ["af" ++ "@" ++ "Z", "qa" ++ "@" ++ "Z",
          "xbI" ++ "@" ++ "Z", "xbO" ++ "@" ++ "Z"] →
        phiOf y H.fo pts a = some (longPhi Z y.ls y.h.lt)) ∧
      (∀ a ∈ tableAsks y rd g, a.name ∈ ["ad" ++ "@" ++ "zt", "ar" ++ "@" ++ "zt"] →
        phiOf y H.fo pts a = some (eqTab H.ztF)) := by
  obtain ⟨Z, hZ, f1, f2⟩ := pointsOf_names hp
  obtain ⟨A, B⟩ := six_asks y rd g hAF hQA hXI hXO hAD hAR
  refine ⟨Z, hZ, fun a ha hn => ?_, fun a ha hn => ?_⟩
  · obtain ⟨a', ha', e1, e2, e3⟩ := A _ hn
    have e : a = a' := ask_of_name hrd ha ha' e1.symm
    subst e
    obtain ⟨b0, b1, b2⟩ := six_not_b a.name (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hn ⊢
      tauto)
    exact phiOf_long b0 b1 b2 e2 e3 f1 (size_last hZ)
  · obtain ⟨a', ha', e1, e2, e3⟩ := B _ hn
    have e : a = a' := ask_of_name hrd ha ha' e1.symm
    subst e
    obtain ⟨b0, b1, b2⟩ := six_not_b a.name (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hn ⊢
      tauto)
    exact phiOf_short b0 b1 b2 e2 e3 f2 (size_last hzt)

/-! ## From a family's place to its tables -/

omit [Field K] in
/-- Beside each family's place layTables returns the family that was asked for and the first entries
of its parts' tables, laid from the family's first entry on. -/
theorem layTables_laid (mats : Array (ℕ × ℕ)) : ∀ (asks : List TableAsk) (p : ℕ)
    (r : List TableAt × List (TableAsk × List (ℕ × ℕ)) × ℕ), layTables mats asks p = some r →
    ∀ x ∈ r.1, ∃ q ∈ r.2.1, q.1 ∈ asks ∧ x.name = q.1.name ∧
      q.2 = (layParts mats q.1 q.1.parts x.first).1
  | [], p, r, h, x, hx => by
    have e : r = ([], [], p) := by simpa [layTables] using h.symm
    subst e
    simp at hx
  | a :: rest, p, r, h, x, hx => by
    have h' : (if ((layParts mats a a.parts p).2 == p) = true then none else
        (layTables mats rest (layParts mats a a.parts p).2).map fun r =>
          ((⟨a.name, p, (layParts mats a a.parts p).2 - p⟩ : TableAt) :: r.1,
            (a, (layParts mats a a.parts p).1) :: r.2.1, r.2.2)) = some r := h
    by_cases hq : ((layParts mats a a.parts p).2 == p) = true
    · rw [if_pos hq] at h'
      cases h'
    · rw [if_neg hq] at h'
      obtain ⟨r', h1, h2⟩ := map_some h'
      subst h2
      rcases List.mem_cons.mp hx with e | hx
      · subst e
        exact ⟨(a, (layParts mats a a.parts p).1), List.mem_cons_self, List.mem_cons_self, rfl,
          rfl⟩
      · obtain ⟨q, q1, q2, q3, q4⟩ := layTables_laid mats rest _ r' h1 x hx
        exact ⟨q, List.mem_cons_of_mem _ q1, List.mem_cons_of_mem _ q2, q3, q4⟩

omit [Field K] in
/-- Every part of every family that was laid has its table in the verifier's list of tables, with
the family's weights and the part's first entry. -/
theorem funsOf_mem {y : Lay} {fo : Model.Forest.Heard} {pts : List (String × Array E)}
    {laid : List (TableAsk × List (ℕ × ℕ))} {funs : Array HFun}
    (h : funsOf y fo pts laid = some funs) {q : TableAsk × List (ℕ × ℕ)} (hq : q ∈ laid) :
    ∃ phi, phiOf y fo pts q.1 = some phi ∧ ∀ m ∈ q.2,
      ({ mat := m.1, len := q.1.L, phi := phi, tree := 2, start := m.2 } : HFun) ∈ funs := by
  unfold funsOf at h
  obtain ⟨l, hl, h⟩ := bind_some h
  have e := Option.some.inj h
  subst e
  obtain ⟨_, hi⟩ := list_mapM_some _ _ _ hl
  obtain ⟨i, hi'⟩ := List.getElem?_of_mem hq
  obtain ⟨b, hb, hf⟩ := hi i q hi'
  obtain ⟨phi, hphi, hf⟩ := bind_some hf
  have e := Option.some.inj hf
  subst e
  refine ⟨phi, hphi, fun m hm => ?_⟩
  have h1 : ({ mat := m.1, len := q.1.L, phi := phi, tree := 2, start := m.2 } : HFun) ∈
      l.flatten :=
    List.mem_flatten.mpr ⟨_, List.mem_of_getElem? hb, List.mem_map.mpr ⟨m, hm, rfl⟩⟩
  simpa using h1

/-! ## What the record's true tables say, in the verifier's weights -/

/-- What an entry of a long table stands for, at the point (first ls coordinates of Z | u), where u
agrees with the last lt coordinates of Z. -/
theorem longAt_phi' {Z : Array E} {ls lt : ℕ} (hs : Z.size = ls + lt) {u : ℕ → K}
    (hu : ∀ j, j < lt → u j = pt ρ Z (ls + j)) (c : Cells K) (mat b : ℕ) :
    longAt ls lt c (pt ρ Z) u mat b =
      ∑ r ∈ range (2 ^ ls), ∑ i ∈ range (2 ^ lt),
        ρ.val ((longPhi Z ls lt).getD (r * 2 ^ lt + i) zeroE) * c mat (b * 2 ^ ls + r) i := by
  rw [← longAt_phi ρ hs]
  unfold longAt Blocks.ext
  refine sum_congr rfl fun r _ => ?_
  congr 1
  refine sum_congr rfl fun i _ => ?_
  congr 1
  refine eqN_congr' lt 0 (fun j hj => ?_) i
  show u (0 + j) = pt ρ Z (ls + (0 + j))
  rw [Nat.zero_add]
  exact hu j hj

/-- LongTrue at the point (first ls coordinates of Z | zt) says: every entry that the verifier can
name holds the cells of its block, summed under the weights that the verifier makes from Z. -/
theorem longTrue_iff_phi (W : World K) (v : Env) (tb mat lt : ℕ) (c : Cells K) {Z : Array E}
    (hs : Z.size = v.y.ls + lt) {u : ℕ → K} (hu : ∀ j, j < lt → u j = pt ρ Z (v.y.ls + j)) :
    LongTrue ρ W v tb mat v.y.ls lt c (pt ρ Z) u ↔
      ∀ b a, v.U3at tb b = some a → a.value ρ W =
        ∑ r ∈ range (2 ^ v.y.ls), ∑ i ∈ range (2 ^ lt),
          ρ.val ((longPhi Z v.y.ls lt).getD (r * 2 ^ lt + i) zeroE) *
            c mat (b * 2 ^ v.y.ls + r) i := by
  have e := fun b => longAt_phi' ρ hs hu c mat b
  constructor
  · intro H b a h
    rw [← e b]
    exact H b a h
  · intro H b a h
    have h1 := H b a h
    rw [← e b] at h1
    exact h1

/-- ShortTrue at the point zt says: every entry that the verifier can name holds its feature's
cells, summed under the equality weights that the verifier makes from zt. -/
theorem shortTrue_iff_phi (W : World K) (v : Env) (tb mat : ℕ) (c : Cells K) (zt : Array E) :
    ShortTrue ρ W v tb mat zt.size c (pt ρ zt) ↔
      ∀ φ a, v.U3at tb φ = some a → a.value ρ W =
        ∑ i ∈ range (2 ^ zt.size), ρ.val ((eqTab zt).getD i zeroE) * c mat φ i := by
  have e := fun φ => shortAt_phi ρ zt c mat φ
  constructor
  · intro H φ a h
    rw [← e φ]
    exact H φ a h
  · intro H φ a h
    have h1 := H φ a h
    rw [← e φ] at h1
    exact h1

/-- The entries of the six families are sums of cells under the verifier's own weights: those of the
four families at Z under the weights of a long table at Z, those of the two families at zt under the
equality weights of zt. Beside each name stands the number of its matrix. -/
def SummedAt (W : World K) (v : Env) (c : Cells K) (Z zt : Array E) : Prop :=
  (∀ p ∈ [("af" ++ "@" ++ "Z", 0), ("qa" ++ "@" ++ "Z", 3), ("xbI" ++ "@" ++ "Z", 4),
      ("xbO" ++ "@" ++ "Z", 5)], ∀ tb, v.tabAt p.1 = some tb → ∀ b a, v.U3at tb b = some a →
    a.value ρ W = ∑ r ∈ range (2 ^ v.y.ls), ∑ i ∈ range (2 ^ zt.size),
      ρ.val ((longPhi Z v.y.ls zt.size).getD (r * 2 ^ zt.size + i) zeroE) *
        c p.2 (b * 2 ^ v.y.ls + r) i) ∧
  (∀ p ∈ [("ad" ++ "@" ++ "zt", 1), ("ar" ++ "@" ++ "zt", 2)], ∀ tb, v.tabAt p.1 = some tb →
    ∀ φ a, v.U3at tb φ = some a →
      a.value ρ W = ∑ i ∈ range (2 ^ zt.size), ρ.val ((eqTab zt).getD i zeroE) * c p.2 φ i)

/-- The one hypothesis on the world, TrueAt, at the point (first ls coordinates of Z | zt), says
that the entries of the six families are sums of cells under the verifier's own weights. -/
theorem trueAt_iff_summed (W : World K) (v : Env) (c : Cells K) {Z zt : Array E}
    (hs : Z.size = v.y.ls + zt.size)
    (hu : ∀ j, j < zt.size → pt ρ zt j = pt ρ Z (v.y.ls + j)) :
    TrueAt ρ W v zt.size c (pt ρ Z) (pt ρ zt) ↔ SummedAt ρ W v c Z zt := by
  have L := fun tb mat => longTrue_iff_phi ρ W v tb mat zt.size c hs hu
  have Sh := fun tb mat => shortTrue_iff_phi ρ W v tb mat c zt
  constructor
  · intro T
    refine ⟨fun p hp tb htb => ?_, fun p hp tb htb => ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl
      · exact (L tb 0).mp (T.af tb htb)
      · exact (L tb 3).mp (T.qa tb htb)
      · exact (L tb 4).mp (T.xi tb htb)
      · exact (L tb 5).mp (T.xo tb htb)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl
      · exact (Sh tb 1).mp (T.ad tb htb)
      · exact (Sh tb 2).mp (T.ar tb htb)
  · intro ⟨A, B⟩
    exact
      { af := fun b hb => (L b 0).mpr (A ("af" ++ "@" ++ "Z", 0) (by simp) b hb)
        qa := fun b hb => (L b 3).mpr (A ("qa" ++ "@" ++ "Z", 3) (by simp) b hb)
        xi := fun b hb => (L b 4).mpr (A ("xbI" ++ "@" ++ "Z", 4) (by simp) b hb)
        xo := fun b hb => (L b 5).mpr (A ("xbO" ++ "@" ++ "Z", 5) (by simp) b hb)
        ad := fun b hb => (Sh b 1).mpr (B ("ad" ++ "@" ++ "zt", 1) (by simp) b hb)
        ar := fun b hb => (Sh b 2).mpr (B ("ar" ++ "@" ++ "zt", 2) (by simp) b hb) }

/-! ## One point for all calls -/

/-- One point serves all calls. zx: the lookup's point. Asked, in the verifier's own words: Z is the
last la coordinates of zx and zt its last lt; the last la coordinates of every call's point have
been taken, and the test that each equals Z has passed. Also: la = ls + lt. Then zt is Z without its
first ls coordinates; and for every call q whose point has ll + lJ + lt coordinates, with ls ≤ lJ,
the two hypotheses of joinPart_of_layout hold with low := the coordinates of Z. -/
theorem calls_share (v : Env) {zx Z zt : Array E} {ends : Array (Array E)}
    (hZ : lastOf zx v.y.h.la = .ok Z) (hzt : lastOf zx v.y.h.lt = .ok zt)
    (hm : v.zk.mapM (fun z => (lastOf z v.y.h.la).toOption) = some ends)
    (ha : ends.all (· == Z) = true) (hla : v.y.h.la = v.y.ls + v.y.h.lt) :
    (∀ j, j < v.y.h.lt → pt ρ zt j = pt ρ Z (v.y.ls + j)) ∧
      ∀ q lJ, q < v.zk.size → (v.zk.getD q #[]).size = v.y.h.ll + lJ + v.y.h.lt → v.y.ls ≤ lJ →
        v.y.h.ll + lJ ≤ (v.zk.getD q #[]).size ∧
          ∀ j, j < v.y.ls → pt ρ Z j = pt ρ (v.zj q lJ) (lJ - v.y.ls + j) :=
  ⟨token_point ρ hZ hzt hla,
    fun q _ hq hn hls => call_point ρ v hn (ends_all hm ha q hq) hla hls⟩

/-! ## A call's factor, with the verifier's point -/

omit [Field K] in
/-- The length of a call's point. The lookup tests that the point of each of its NC calls has as
many coordinates as the call's record says (hpt, with the layout's records). For call number q of a
layout that the verifier has returned the record says ll + lJ + lt. -/
theorem size_of_test {h : Shape} {pc : List (List String)} {v : Env} (hy : layout h pc = .ok v.y)
    {NC q : ℕ} {cd : CallD}
    (hpt : ((List.range NC).all fun c =>
      (v.zk.getD c #[]).size == ((v.y.cl[c]?).map (·.n)).getD 0) = true)
    (hq : q < NC) (hcq : v.y.calls[q]? = some cd) :
    (v.zk.getD q #[]).size = v.y.h.ll + cd.lJ + v.y.h.lt := by
  have h1 : ((v.zk.getD q #[]).size == ((v.y.cl[q]?).map (·.n)).getD 0) = true :=
    List.all_eq_true.mp hpt q (List.mem_range.mpr hq)
  have h2 : v.y.cl[q]? = some (v.y.callRecord q cd) := by
    rw [cl_of_layout hy]
    simp [hcq]
  rw [h2] at h1
  have h3 : (v.zk.getD q #[]).size = (v.y.callRecord q cd).n := by simpa using h1
  rw [h3]
  rfl

section Lines

variable {h : Shape} {pc : List (List String)} {v : Env} {rd : Reads} {mats : Array (ℕ × ℕ)}
  {r : List TableAt × List (TableAsk × List (ℕ × ℕ)) × ℕ}
  (hy : layout h pc = .ok v.y) (S : Switches h) (hs : scalesHeld h v.sc = .ok ())
  (hg : v.g < v.y.NGr) (hrd : readsOf v.y = .ok rd)
  (hl : layTables mats (tableAsks v.y rd v.g) 0 = some r) (ht : v.tab = r.1)

include hy S hs hg hrd hl ht in
/-- What one call's factor in the lookup's join is worth, at the verifier's own point, in any world
with true tables: the theorem joinPart_of_layout_true with low := the coordinates of Z and u :=
those of zt. In place of its two hypotheses on the call's point stand the verifier's lines and
tests: those of calls_share (hZ, hzt, hm, ha) and that of size_of_test (hpt); and that cd is call
number q of the layout, with a point of its own (hcq, hq, hq'). The first two parts of the
conclusion say that the last ls + lt coordinates of this call's point are (low | u): the last ls
coordinates of the column are the first ls of Z, and the coordinates of the token are zt. -/
theorem joinPart_of_run {ρ : Reading K} (hρ : Numerals ρ) {D : Dim} (Zd : Sized h D) {W : World K}
    {zx Z zt : Array E} {ends : Array (Array E)}
    (hZ : lastOf zx v.y.h.la = .ok Z) (hzt : lastOf zx v.y.h.lt = .ok zt)
    (hm : v.zk.mapM (fun z => (lastOf z v.y.h.la).toOption) = some ends)
    (ha : ends.all (· == Z) = true) {NC : ℕ}
    (hpt : ((List.range NC).all fun c =>
      (v.zk.getD c #[]).size == ((v.y.cl[c]?).map (·.n)).getD 0) = true)
    (c : Cells K) (T : TrueAt ρ W v h.lt c (pt ρ Z) (pt ρ zt)) (tb : Tables) (L0 : ℕ)
    (w : ℕ → LW K) (alpha theta : E) (q : ℕ) (cd : CallD) (hcq : v.y.calls[q]? = some cd)
    (hq : q < NC) (hq' : q < v.zk.size) (weighed : Array Bool) {f : Aff}
    (hf : v.joinPart alpha theta q cd weighed = some f) :
    (∀ j, j < v.y.ls → pt ρ Z j = pt ρ (v.zj q cd.lJ) (cd.lJ - v.y.ls + j)) ∧
    (∀ j, j < v.y.h.lt → pt ρ zt j = pt ρ (v.zk.getD q #[]) (v.y.h.ll + cd.lJ + j)) ∧
    ∃ fam : Seg → Fam, (∀ s ∈ cd.segs, SegFits v D cd.lJ s (fam s)) ∧
      f.value ρ W = ρ.val alpha - (q : K) * ρ.val theta -
        ρ.val (ofF ((v.y.cl.getD q {}).tauAt (v.y.cl.getD q {}).t0)) * padJ ρ v q cd weighed -
        (cd.segs.map fun s => ((List.range v.y.Lam).map fun lam =>
          if (s.moe && !v.isMoe lam) = true then 0
          else ρ.val (elJ v q lam) * ∑ x ∈ range (len D (fam s)),
            ρ.val ((ewJ v q cd s).getD x zeroE) *
              Blocks.ext D.lT (fun i => lin (scl := sclOf h v.sc v.g v.y.Lam) D (cellsOf D c)
                tb L0 w (fam s) lam x i) (pt ρ zt)).sum).sum := by
  have A := admitted_of_layout hy S.p3
  have hla : v.y.h.la = v.y.ls + v.y.h.lt := by
    rw [A.shape]
    exact A.la
  have hcd : cd ∈ v.y.calls := Array.mem_of_getElem? hcq
  have hn := size_of_test hy hpt hq hcq
  have hls := lJ_of_layout hy cd hcd
  obtain ⟨hu, hall⟩ := calls_share ρ v hZ hzt hm ha hla
  obtain ⟨k1, k2⟩ := hall q cd.lJ hq' hn hls
  exact ⟨k2, call_token ρ v hn (ends_all hm ha q hq') hla hls hu,
    joinPart_of_layout_true hy S hs hg hrd hl ht hρ Zd c _ _ T tb L0 w alpha theta q cd hcd weighed
      k1 k2 hf⟩

omit [Field K] in
/-- A family that is found under a name is a member of the verifier's list with that name, and what
is found is its first entry. -/
theorem tabAt_mem {v : Env} {n : String} {b : ℕ} (h : v.tabAt n = some b) :
    ∃ x ∈ v.tab, x.name = n ∧ x.first = b := by
  unfold Env.tabAt at h
  obtain ⟨x, hx, hxf⟩ := map_some h
  exact ⟨x, List.mem_of_find?_eq_some hx, by simpa using List.find?_some hx, hxf⟩

include hy S hrd hl ht in
/-- The names, the points, the weights and the tables, together. From the verifier's lines: Z is the
last la coordinates of the lookup's point, with ls + lt coordinates, and the token point is Z
without its first ls. Each of the four names …@Z is found; the family that was asked for under it
has, for each of its parts, laid from the entry that was found, a table in the verifier's list of
tables with the weights of a long table at Z. The like holds of the two names …@zt with the equality
weights of the token point. And in any world the hypothesis TrueAt at this point says that the
entries of the six families are sums of cells under these weights. hp, hzt, hfun: the verifier's
lines that make the list of points, the token point and the list of tables. -/
theorem tables_of_run {H : Heard} {hd : Level} {hd2 : Option Level}
    {pts : List (String × Array E)} {funs : Array HFun} (hp : pointsOf v.y H hd hd2 = some pts)
    (hzt : lastOf H.fo.zx v.y.h.lt = .ok H.ztF) (hfun : funsOf v.y H.fo pts r.2.1 = some funs) :
    ∃ Z, lastOf H.fo.zx v.y.h.la = .ok Z ∧ Z.size = v.y.ls + v.y.h.lt ∧
      H.ztF.size = v.y.h.lt ∧ (∀ j, j < v.y.h.lt → pt ρ H.ztF j = pt ρ Z (v.y.ls + j)) ∧
      (∀ n ∈ ["af" ++ "@" ++ "Z", "qa" ++ "@" ++ "Z", "xbI" ++ "@" ++ "Z", "xbO" ++ "@" ++ "Z"],
        ∃ b a, v.tabAt n = some b ∧ a ∈ tableAsks v.y rd v.g ∧ a.name = n ∧
          ∀ m ∈ (layParts mats a a.parts b).1,
            ({ mat := m.1, len := a.L, phi := longPhi Z v.y.ls v.y.h.lt, tree := 2,
               start := m.2 } : HFun) ∈ funs) ∧
      (∀ n ∈ ["ad" ++ "@" ++ "zt", "ar" ++ "@" ++ "zt"],
        ∃ b a, v.tabAt n = some b ∧ a ∈ tableAsks v.y rd v.g ∧ a.name = n ∧
          ∀ m ∈ (layParts mats a a.parts b).1,
            ({ mat := m.1, len := a.L, phi := eqTab H.ztF, tree := 2, start := m.2 } : HFun) ∈
              funs) ∧
      ∀ (W : World K) (c : Cells K),
        TrueAt ρ W v v.y.h.lt c (pt ρ Z) (pt ρ H.ztF) ↔ SummedAt ρ W v c Z H.ztF := by
  have A := admitted_of_layout hy S.p3
  have hla : v.y.h.la = v.y.ls + v.y.h.lt := by
    rw [A.shape]
    exact A.la
  obtain ⟨p1, p2, p3, p4, p5, p6⟩ := points_of_layout hy S hrd
  obtain ⟨Z, hZ, wl, ws⟩ := weights_of_names hrd v.g p1 p2 p3 p4 p5 p6 hp hzt
  have Fd := found_of_layout hy S hrd hl ht
  have hsz : Z.size = v.y.ls + v.y.h.lt := by rw [size_last hZ, hla]
  have hst : H.ztF.size = v.y.h.lt := size_last hzt
  have hu := token_point ρ hZ hzt hla
  have part : ∀ (n : String) (phi : Array E), (∃ b, v.tabAt n = some b) →
      (∀ a ∈ tableAsks v.y rd v.g, a.name = n → phiOf v.y H.fo pts a = some phi) →
      ∃ b a, v.tabAt n = some b ∧ a ∈ tableAsks v.y rd v.g ∧ a.name = n ∧
        ∀ m ∈ (layParts mats a a.parts b).1,
          ({ mat := m.1, len := a.L, phi := phi, tree := 2, start := m.2 } : HFun) ∈ funs := by
    intro n phi ⟨b, hb⟩ hw
    obtain ⟨x, hx, hxn, hxf⟩ := tabAt_mem hb
    rw [ht] at hx
    obtain ⟨q, q1, q2, q3, q4⟩ := layTables_laid mats _ 0 r hl x hx
    obtain ⟨phi', hphi, hmem⟩ := funsOf_mem hfun q1
    have hqn : q.1.name = n := q3.symm.trans hxn
    have e : phi' = phi := Option.some.inj (hphi.symm.trans (hw q.1 q2 hqn))
    subst e
    refine ⟨b, q.1, hb, q2, hqn, fun m hm => ?_⟩
    rw [← hxf, ← q4] at hm
    exact hmem m hm
  refine ⟨Z, hZ, hsz, hst, hu, fun n hn => ?_, fun n hn => ?_, fun W c => ?_⟩
  · refine part n _ ?_ (fun a ha e => wl a ha (by rw [e]; exact hn))
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
    rcases hn with rfl | rfl | rfl | rfl
    · exact Fd.af
    · exact Fd.qa
    · exact Fd.xi
    · exact Fd.xo
  · refine part n _ ?_ (fun a ha e => ws a ha (by rw [e]; exact hn))
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
    rcases hn with rfl | rfl
    · exact Fd.ad
    · exact Fd.ar
  · have e := trueAt_iff_summed ρ W v c (Z := Z) (zt := H.ztF) (by rw [hst]; exact hsz)
      (by rw [hst]; exact hu)
    rw [hst] at e
    exact e

end Lines

#print axioms call_point
#print axioms ends_all
#print axioms pointsOf_names
#print axioms longPhi_value
#print axioms names_nodup
#print axioms weights_of_names
#print axioms layTables_laid
#print axioms funsOf_mem
#print axioms longTrue_iff_phi
#print axioms shortTrue_iff_phi
#print axioms calls_share
#print axioms size_of_test
#print axioms trueAt_iff_summed
#print axioms call_token
#print axioms joinPart_of_run
#print axioms tables_of_run

end OnBytes.Road
