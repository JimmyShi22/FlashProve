-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/HonestTrace/CountsJoint.lean

If FoNums.ok h = true, the counts of a lookup taken call by call ("count",
Johnson/HonestTrace/Counts.lean), read at padJ and rowJ, are hmultP, the count in the library's
algebra of a padded lookup (Cb/Pv/Lookup/Alg/PadAlg.lean).

A lookup has one or more calls. Call c has a key vector of 2^(n_c) places and a table of 2^(k_c)
rows. Johnson/HonestTrace/Counts.lean numbers a count by a call c and a row t of that call's table,
as the byte format does. The algebra has one joint key vector of 2^v places and one joint table of
2^d rows. Place X of the joint key vector lies in tree X % 2^rK; "FoNums.keyOf" names its call and
its index there. Row u of the joint table belongs to the number u % 2^cK and to row u / 2^cK. This
file carries "count" and "bit" from the first numbering to the second.

Notation. h is any value of Forest.Shape (OnBytes/Model/Forest.lean), the type in which the Lean
verifier under OnBytes/Model/ keeps a lookup's public numbers. NC, NT, dT, rK, kT, cK are its
fields: the number of calls, the number of trees that belong to a call, and the numbers of bits of a
place in a tree, of a tree's number, of a row of the largest table, of a call's number; v = dT + rK
and d = kT + cK. n_c, k_c and iota c are FoNums.nOf h c, FoNums.kOf h c and FoNums.io h c: call c
has 2^(iota c) trees. "FoNums.ok h = true" is the test on these numbers in
OnBytes/Tie/Pv/Lookup/Port/FoNums.lean. H : Hits says of every place of every call whether it is a
padding place, and which row is chosen for it. "Fits h T K H" (Johnson/HonestTrace/Counts.lean) says
of tables T and key vectors K, for every call c below NC and every place below 2^(n_c): the chosen
row is below 2^(k_c); the key is that row's value; at a padding place the chosen row is the call's
padding row; and, for every tree below NT, h.pub counts the tree's padding places.

Main definitions and theorems:
* "padJ", "rowJ": H in the numbering of the joint key vector.
* "hmultP_joint": if FoNums.ok h = true, "hmultP" at padJ and rowJ, at any u, is count h H (u %
  2^cK) (u / 2^cK) if u % 2^cK is below NC, and 0 if not.
* "hbitP_joint": if FoNums.ok h = true, the algebra's bit "hbitP" with 32 planes at padJ and rowJ,
  at any u and j, is 1 if bit h H (u / 2^cK) (u % 2^cK) j is true, and 0 if not.
* "fT_rowJ": if FoNums.ok h = true, the joint row rowJ h H X has the call of the joint key X.
* "laidP_joint": FoNums.ok h = true and Fits h T K H give the algebra's premise "LaidP" at the joint
  vectors Port.key h T K and Port.tab h T, the list FoNums.pads h, padJ and rowJ.
* "sum_count": under the same two premises, the counts of all rows below 2^kT of all calls below NC,
  and the number h.padding, add up to 2^v. "sum_count_pub": the same without keys and tables, if
  FoNums.ok h = true, PubFits h H.pad holds, and the chosen rows of the places that are not padding
  places are below 2^kT.
* "midP_port": under the same two premises, at every shift θ and every point al of the field, the
  algebra's relation "MidP" holds of the shifted joint vectors, FoNums.pads h and the bits hbitP.

Limits. No theorem of this file shows that Fits holds of anything. Its last clause ties public
numbers to the padding places. Where that clause fails, the three theorems with the premise Fits say
nothing. No theorem of this file shows FoNums.ok h = true for any h; shape_ok
(OnBytes/Tie/Pv/Lookup/Port/FoShape.lean) has it, for what Forest.shape returns with pub filled in,
from the success of Forest.shape and Forest.pubAsk. FoNums.keyOf, FoNums.padRow and FoNums.pads are
FoNums.lean's own descriptions of the numbering in OnBytes/Model/, and Port.key and Port.tab those
of OnBytes/Tie/Pv/Lookup/Port/ShiftQPort.lean; no statement of this file compares them with a
function of OnBytes/Model/, or MidP with the byte format's relation. hmultP_joint and hbitP_joint
hold at every u, also from 2^d on, where the joint table has no row. The second clause of MidP is an
equation in the field: in a field of small characteristic it says less than sum_count.

Not claimed: that a prover's committed cells hold these bits; that a verifier accepts a proof made
with these counts; anything on soundness or zero knowledge.

-/
import Johnson.HonestTrace.Counts
import OnBytes.Tie.Pv.Lookup.Forest.FoHole
import OnBytes.Tie.Pv.Lookup.Forest.FoPadSum
import Cb.Pv.Lookup.Alg.PadAlg

set_option autoImplicit false

namespace OnBytes.HonestTrace

open Finset
open OnBytes.Model
open Cb.Lkp Cb.LdLkp

/-! ## The padding places and the chosen rows in the joint numbering -/

/-- Whether place X of the joint key vector is a padding place: H.pad c i if FoNums.keyOf h X is
(c, i); true if FoNums.keyOf h X is none, that is, if X's tree is not below h.NT. -/
def padJ (h : Forest.Shape) (H : Hits) (X : ℕ) : Bool :=
  match FoNums.keyOf h X with
  | some (c, i) => H.pad c i
  | none => true

/-- The row of the joint table that is chosen for place X of the joint key vector:
c + 2^cK · H.row c i if FoNums.keyOf h X is (c, i); FoNums.padRow h 0 if FoNums.keyOf h X is none.
A padding place has a chosen row too, and is not counted there. -/
def rowJ (h : Forest.Shape) (H : Hits) (X : ℕ) : ℕ :=
  match FoNums.keyOf h X with
  | some (c, i) => c + 2 ^ h.cK * H.row c i
  | none => FoNums.padRow h 0

/-! ## Sums over blocks of indices -/

/-- The sum of f over the numbers below a · N is the sum, over x below N and y below a, of f (y + a
· x). -/
theorem sum_block (a N : ℕ) (f : ℕ → ℕ) :
    ∑ X ∈ range (a * N), f X = ∑ x ∈ range N, ∑ y ∈ range a, f (y + a * x) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Nat.mul_succ, sum_range_add, ih, sum_range_succ]
    congr 1
    exact sum_congr rfl fun y _ => by rw [Nat.add_comm]

/-- For N ≤ M: the sum over y below M of A y where y is below N, and of B elsewhere, is the sum of A
y over y below N, plus (M - N) · B. -/
theorem sum_below {N M : ℕ} (hNM : N ≤ M) (A : ℕ → ℕ) (B : ℕ) :
    ∑ y ∈ range M, (if y < N then A y else B) = ∑ y ∈ range N, A y + (M - N) * B := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hNM
  rw [sum_range_add, Nat.add_sub_cancel_left]
  congr 1
  · exact sum_congr rfl fun y hy => if_pos (mem_range.1 hy)
  · rw [sum_congr rfl fun y _ => if_neg (by omega : ¬ N + y < N), sum_const, card_range,
      smul_eq_mul]

/-- For c below 2^a: c + 2^a · r is u if and only if c is u % 2^a and r is u / 2^a. -/
theorem split_iff {a c : ℕ} (hc : c < 2 ^ a) (r u : ℕ) :
    c + 2 ^ a * r = u ↔ c = u % 2 ^ a ∧ r = u / 2 ^ a := by
  have hp : 0 < 2 ^ a := by positivity
  constructor
  · rintro rfl
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hc, Nat.add_mul_div_left _ _ hp,
      Nat.div_eq_of_lt hc, Nat.zero_add]
    exact ⟨rfl, rfl⟩
  · rintro ⟨rfl, rfl⟩
    exact Nat.mod_add_div u (2 ^ a)

/-- The sum of a list made over List.range N, as a sum over Finset.range N. -/
theorem list_sum_range (f : ℕ → ℕ) (N : ℕ) :
    ((List.range N).map f).sum = ∑ i ∈ range N, f i := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [List.range_succ, List.map_append, List.sum_append, ih, sum_range_succ]
    simp

/-- The sum over a filtered list is the sum over the whole list with 0 at the members that the
filter drops. -/
theorem list_sum_filter (p : ℕ → Bool) (f : ℕ → ℕ) (l : List ℕ) :
    ((l.filter p).map f).sum = (l.map fun i => if p i = true then f i else 0).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    by_cases ha : p a = true
    · simp [ha, ih]
    · simp [ha, ih]

/-! ## The two maps, unfolded; sums over trees -/

/-- padJ with FoNums.keyOf unfolded. No premise. -/
theorem padJ_eq (h : Forest.Shape) (H : Hits) (X : ℕ) :
    padJ h H X = if X % 2 ^ h.rK < h.NT then
      H.pad (FoNums.co h (X % 2 ^ h.rK)) (X / 2 ^ h.rK +
        2 ^ h.dT * (X % 2 ^ h.rK % 2 ^ FoNums.io h (FoNums.co h (X % 2 ^ h.rK)))) else true := by
  unfold padJ FoNums.keyOf
  split_ifs <;> rfl

/-- rowJ with FoNums.keyOf unfolded. No premise. -/
theorem rowJ_eq (h : Forest.Shape) (H : Hits) (X : ℕ) :
    rowJ h H X = if X % 2 ^ h.rK < h.NT then
      FoNums.co h (X % 2 ^ h.rK) + 2 ^ h.cK * H.row (FoNums.co h (X % 2 ^ h.rK)) (X / 2 ^ h.rK +
        2 ^ h.dT * (X % 2 ^ h.rK % 2 ^ FoNums.io h (FoNums.co h (X % 2 ^ h.rK))))
      else FoNums.padRow h 0 := by
  unfold rowJ FoNums.keyOf
  split_ifs <;> rfl

/-- If FoNums.ok h = true and c is below h.NC: y ↦ y % 2^(iota c), with iota c = FoNums.io h c, maps
the trees y below h.NT of call c one to one onto the numbers below 2^(iota c). Stated for sums: the
sum of G (y % 2^(iota c)) over these trees is the sum of G b over b below 2^(iota c). -/
theorem sum_trees {h : Forest.Shape} (hok : FoNums.ok h = true) {c : ℕ} (hc : c < h.NC)
    (G : ℕ → ℕ) :
    ∑ y ∈ range h.NT, (if FoNums.co h y = c then G (y % 2 ^ FoNums.io h c) else 0) =
      ∑ b ∈ range (2 ^ FoNums.io h c), G b := by
  obtain ⟨_, hb, hcc, _⟩ := Cb.Fo.ok_parts hok
  obtain ⟨_, _, _, hq⟩ := hcc c hc
  rw [← sum_filter]
  refine sum_nbij' (fun y => y % 2 ^ FoNums.io h c) (fun b => FoNums.fst h c + b) ?_ ?_ ?_ ?_ ?_
  · intro y _
    exact mem_range.2 (Nat.mod_lt _ (by positivity))
  · intro b hb'
    obtain ⟨q1, q2, _⟩ := hq b (mem_range.1 hb')
    exact mem_filter.2 ⟨mem_range.2 q1, q2⟩
  · intro y hy
    obtain ⟨hy1, hy2⟩ := mem_filter.1 hy
    obtain ⟨_, lo, hi⟩ := hb y (mem_range.1 hy1)
    rw [hy2] at lo hi
    obtain ⟨_, _, q3⟩ := hq (y - FoNums.fst h c) (by omega)
    rw [Nat.add_sub_cancel' lo] at q3
    show FoNums.fst h c + y % 2 ^ FoNums.io h c = y
    rw [q3]
    omega
  · intro b hb'
    exact (hq b (mem_range.1 hb')).2.2
  · intro y _
    rfl

/-- If FoNums.ok h = true: the number of places X below 2^v of the joint key vector with padJ h H X
= β and rowJ h H X = u is a sum over the trees y below h.NT, of the number of places x below 2^dT of
tree y with H.pad = β whose chosen row in the joint table is u; plus h.emptyKeys, the number of
places in the other trees, if β is true and u is FoNums.padRow h 0. -/
theorem card_joint {h : Forest.Shape} (hok : FoNums.ok h = true) (H : Hits) (β : Bool) (u : ℕ) :
    (((range (2 ^ h.v)).filter fun X => padJ h H X = β).filter fun X => rowJ h H X = u).card =
      ∑ y ∈ range h.NT, ((range (2 ^ h.dT)).filter fun x =>
        H.pad (FoNums.co h y) (x + 2 ^ h.dT * (y % 2 ^ FoNums.io h (FoNums.co h y))) = β ∧
        FoNums.co h y + 2 ^ h.cK *
          H.row (FoNums.co h y) (x + 2 ^ h.dT * (y % 2 ^ FoNums.io h (FoNums.co h y))) = u).card +
      if β = true ∧ FoNums.padRow h 0 = u then h.emptyKeys else 0 := by
  obtain ⟨⟨_, _, _, a4, _⟩, _⟩ := Cb.Fo.ok_parts hok
  have hp : 0 < 2 ^ h.rK := by positivity
  have hv : 2 ^ h.v = 2 ^ h.rK * 2 ^ h.dT := by
    show 2 ^ (h.dT + h.rK) = _
    rw [pow_add, Nat.mul_comm]
  rw [filter_filter, card_filter, hv, sum_block, sum_comm]
  have inner : ∀ y ∈ range (2 ^ h.rK),
      (∑ x ∈ range (2 ^ h.dT),
        if padJ h H (y + 2 ^ h.rK * x) = β ∧ rowJ h H (y + 2 ^ h.rK * x) = u then 1 else 0) =
      if y < h.NT then ((range (2 ^ h.dT)).filter fun x =>
        H.pad (FoNums.co h y) (x + 2 ^ h.dT * (y % 2 ^ FoNums.io h (FoNums.co h y))) = β ∧
        FoNums.co h y + 2 ^ h.cK *
          H.row (FoNums.co h y) (x + 2 ^ h.dT * (y % 2 ^ FoNums.io h (FoNums.co h y))) = u).card
      else if β = true ∧ FoNums.padRow h 0 = u then 2 ^ h.dT else 0 := by
    intro y hy
    have hy' := mem_range.1 hy
    have em : ∀ x, (y + 2 ^ h.rK * x) % 2 ^ h.rK = y := fun x => by
      rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hy']
    have ed : ∀ x, (y + 2 ^ h.rK * x) / 2 ^ h.rK = x := fun x => by
      rw [Nat.add_mul_div_left _ _ hp, Nat.div_eq_of_lt hy', Nat.zero_add]
    by_cases hl : y < h.NT
    · rw [if_pos hl, card_filter]
      refine sum_congr rfl fun x _ => ?_
      rw [padJ_eq, rowJ_eq, em, ed, if_pos hl, if_pos hl]
    · rw [if_neg hl]
      have e : ∀ x ∈ range (2 ^ h.dT),
          (if padJ h H (y + 2 ^ h.rK * x) = β ∧ rowJ h H (y + 2 ^ h.rK * x) = u then 1 else 0) =
            if β = true ∧ FoNums.padRow h 0 = u then 1 else 0 := by
        intro x _
        rw [padJ_eq, rowJ_eq, em, if_neg hl, if_neg hl]
        by_cases hP : β = true ∧ FoNums.padRow h 0 = u
        · rw [if_pos hP, if_pos ⟨hP.1.symm, hP.2⟩]
        · rw [if_neg hP, if_neg fun q => hP ⟨q.1.symm, q.2⟩]
      rw [sum_congr rfl e]
      split_ifs <;> simp
  rw [sum_congr rfl inner, sum_below a4]
  congr 1
  unfold Forest.Shape.emptyKeys
  split_ifs <;> simp

/-! ## The counts and the bits -/

/-- **If FoNums.ok h = true, the algebra's count at the joint row u is the count by call and row.**
For every H and every u: hmultP h.v (padJ h H) (rowJ h H) u is count h H (u % 2^cK) (u / 2^cK) if u
% 2^cK is below h.NC, and 0 if not. Nothing is asked of H. -/
theorem hmultP_joint (h : Forest.Shape) (H : Hits) (hok : FoNums.ok h = true) (u : ℕ) :
    hmultP h.v (padJ h H) (rowJ h H) u =
      if u % 2 ^ h.cK < h.NC then count h H (u % 2 ^ h.cK) (u / 2 ^ h.cK) else 0 := by
  obtain ⟨⟨_, _, a3, _⟩, hb, hcc, _⟩ := Cb.Fo.ok_parts hok
  have h0 := card_joint hok H false u
  rw [if_neg (by simp), Nat.add_zero] at h0
  unfold hmultP
  rw [h0]
  have term : ∀ y ∈ range h.NT, ((range (2 ^ h.dT)).filter fun x =>
        H.pad (FoNums.co h y) (x + 2 ^ h.dT * (y % 2 ^ FoNums.io h (FoNums.co h y))) = false ∧
        FoNums.co h y + 2 ^ h.cK *
          H.row (FoNums.co h y) (x + 2 ^ h.dT * (y % 2 ^ FoNums.io h (FoNums.co h y))) = u).card =
      if FoNums.co h y = u % 2 ^ h.cK then
        (fun b => ((range (2 ^ h.dT)).filter fun x =>
          H.pad (u % 2 ^ h.cK) (x + 2 ^ h.dT * b) = false ∧
          H.row (u % 2 ^ h.cK) (x + 2 ^ h.dT * b) = u / 2 ^ h.cK).card)
          (y % 2 ^ FoNums.io h (u % 2 ^ h.cK))
      else 0 := by
    intro y hy
    have hlt : FoNums.co h y < 2 ^ h.cK := lt_of_lt_of_le (hb y (mem_range.1 hy)).1 a3
    by_cases e : FoNums.co h y = u % 2 ^ h.cK
    · rw [if_pos e]
      rw [e] at hlt ⊢
      refine congrArg card (filter_congr fun x _ => ?_)
      rw [split_iff hlt]
      exact ⟨fun q => ⟨q.1, q.2.2⟩, fun q => ⟨q.1, rfl, q.2⟩⟩
    · rw [if_neg e, card_eq_zero, filter_eq_empty_iff]
      rintro x _ ⟨_, q⟩
      exact e ((split_iff hlt _ _).1 q).1
  rw [sum_congr rfl term]
  by_cases hc : u % 2 ^ h.cK < h.NC
  · rw [if_pos hc, sum_trees hok hc fun b => ((range (2 ^ h.dT)).filter fun x =>
      H.pad (u % 2 ^ h.cK) (x + 2 ^ h.dT * b) = false ∧
      H.row (u % 2 ^ h.cK) (x + 2 ^ h.dT * b) = u / 2 ^ h.cK).card]
    unfold count
    rw [(hcc _ hc).2.2.1, card_filter, pow_add, Nat.mul_comm, sum_block]
    exact sum_congr rfl fun b _ => card_filter _ _
  · rw [if_neg hc]
    refine sum_eq_zero fun y hy => if_neg fun e => hc ?_
    rw [← e]
    exact (hb y (mem_range.1 hy)).1

/-- **If FoNums.ok h = true, the algebra's bit is the bit by row, call and plane.** In every field,
for every H, u and j: hbitP h.v 32 (padJ h H) (rowJ h H) u j is 1 if bit h H (u / 2^cK) (u % 2^cK) j
is true, and 0 if not. -/
theorem hbitP_joint {E : Type} [Field E] (h : Forest.Shape) (H : Hits)
    (hok : FoNums.ok h = true) (u j : ℕ) :
    (hbitP h.v 32 (padJ h H) (rowJ h H) u j : E) =
      if bit h H (u / 2 ^ h.cK) (u % 2 ^ h.cK) j = true then 1 else 0 := by
  unfold hbitP bit
  rw [hmultP_joint h H hok u]
  by_cases hc : u % 2 ^ h.cK < h.NC
  · by_cases hj : j < 32 <;> simp [hc, hj]
  · simp [hc]

/-- If FoNums.ok h = true, then for every H and X the call Port.fT of the joint row rowJ h H X is
the call Port.fK of the joint key X. -/
theorem fT_rowJ (h : Forest.Shape) (H : Hits) (hok : FoNums.ok h = true) (X : ℕ) :
    Port.fT h (rowJ h H X) = Port.fK h X := by
  obtain ⟨⟨_, a2, a3, _⟩, hb, _⟩ := Cb.Fo.ok_parts hok
  have hp : 0 < 2 ^ h.cK := by positivity
  rw [rowJ_eq]
  unfold Port.fK Port.fT
  split_ifs with hl
  · have hc := (hb _ hl).1
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (lt_of_lt_of_le hc a3),
      Nat.min_eq_left (by omega)]
    rfl
  · unfold FoNums.padRow
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hp, Nat.min_eq_left (Nat.zero_le _)]

/-! ## The padding, the joint table, and the bound on an index -/

/-- If FoNums.ok h = true, the list FoNums.pads h passes the algebra's test padsOK at h.v and
h.d. -/
theorem padsOK_of_ok {h : Forest.Shape} (hok : FoNums.ok h = true) :
    padsOK h.v h.d (FoNums.pads h) = true := by
  obtain ⟨_, _, _, d, e, _⟩ := Cb.Fo.ok_parts hok
  unfold padsOK padNum
  rw [Bool.and_eq_true]
  exact ⟨List.all_eq_true.2 fun x hx => decide_eq_true (d x hx), decide_eq_true e⟩

/-- If FoNums.ok h = true: the number of padding keys that the list FoNums.pads h gives to the joint
row u is the sum of h.pub[y] over the trees y below h.NT whose call's padding row FoNums.padRow is
u, plus h.emptyKeys if FoNums.padRow h 0 is u. -/
theorem padCnt_pads {h : Forest.Shape} (hok : FoNums.ok h = true) (u : ℕ) :
    padCnt (FoNums.pads h) u =
      ∑ y ∈ range h.NT, (if FoNums.padRow h (FoNums.co h y) = u then h.pub.getD y 0 else 0) +
      if FoNums.padRow h 0 = u then h.emptyKeys else 0 := by
  obtain ⟨⟨_, a2, _⟩, hb, _⟩ := Cb.Fo.ok_parts hok
  have e0 : padCnt (FoNums.pads h) u =
      ∑ c ∈ range h.NC, if FoNums.padRow h c = u then FoNums.padCount h c else 0 := by
    unfold padCnt FoNums.pads
    rw [List.map_map, ← list_sum_range]
    rfl
  have e1 : ∀ c, FoNums.padCount h c =
      ∑ y ∈ range h.NT, (if FoNums.co h y = c then h.pub.getD y 0 else 0) +
        if c = 0 then h.emptyKeys else 0 := by
    intro c
    unfold FoNums.padCount
    rw [list_sum_filter, list_sum_range]
    simp only [decide_eq_true_eq]
  have e2 : ∀ c ∈ range h.NC, (if FoNums.padRow h c = u then FoNums.padCount h c else 0) =
      ∑ y ∈ range h.NT, (if FoNums.co h y = c then
        (if FoNums.padRow h (FoNums.co h y) = u then h.pub.getD y 0 else 0) else 0) +
      if c = 0 then (if FoNums.padRow h 0 = u then h.emptyKeys else 0) else 0 := by
    intro c _
    rw [e1 c]
    by_cases hu : FoNums.padRow h c = u
    · rw [if_pos hu]
      congr 1
      · refine sum_congr rfl fun y _ => ?_
        by_cases e : FoNums.co h y = c
        · rw [if_pos e, if_pos e, e, if_pos hu]
        · rw [if_neg e, if_neg e]
      · by_cases e : c = 0
        · subst e
          rw [if_pos rfl, if_pos rfl, if_pos hu]
        · rw [if_neg e, if_neg e]
    · rw [if_neg hu]
      symm
      rw [Nat.add_eq_zero_iff]
      constructor
      · refine sum_eq_zero fun y _ => ?_
        by_cases e : FoNums.co h y = c
        · rw [if_pos e, e, if_neg hu]
        · rw [if_neg e]
      · by_cases e : c = 0
        · subst e
          rw [if_pos rfl, if_neg hu]
        · rw [if_neg e]
  rw [e0, sum_congr rfl e2, sum_add_distrib, sum_comm, sum_ite_eq', if_pos (mem_range.2 a2)]
  congr 1
  refine sum_congr rfl fun y hy => ?_
  rw [sum_ite_eq, if_pos (mem_range.2 (hb y (mem_range.1 hy)).1)]

/-- If FoNums.ok h = true, c is below h.NC and t is below 2^(k_c): row c + 2^cK · t of the joint
table Port.tab h T is T c t. -/
theorem tab_at {E : Type} [Field E] {h : Forest.Shape} (hok : FoNums.ok h = true)
    (T : ℕ → ℕ → E) {c t : ℕ} (hc : c < h.NC) (ht : t < 2 ^ FoNums.kOf h c) :
    Port.tab h T (c + 2 ^ h.cK * t) = T c t := by
  obtain ⟨⟨_, _, a3, _⟩, _⟩ := Cb.Fo.ok_parts hok
  have hp : 0 < 2 ^ h.cK := by positivity
  have hc' : c < 2 ^ h.cK := lt_of_lt_of_le hc a3
  unfold Port.tab Port.fT
  rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hc', Nat.add_mul_div_left _ _ hp,
    Nat.div_eq_of_lt hc', Nat.zero_add, Nat.min_eq_left (by omega),
    Nat.mod_eq_of_lt (show t < 2 ^ Port.kOf h c from ht)]

/-- If FoNums.ok h = true, y is below h.NT and x is below 2^dT: the index that FoNums.keyOf gives to
place x of tree y is below the length 2^(n_c) of the key vector of the tree's call c. -/
theorem idx_lt {h : Forest.Shape} (hok : FoNums.ok h = true) {y x : ℕ} (hy : y < h.NT)
    (hx : x < 2 ^ h.dT) :
    x + 2 ^ h.dT * (y % 2 ^ FoNums.io h (FoNums.co h y)) < 2 ^ FoNums.nOf h (FoNums.co h y) := by
  obtain ⟨_, hb, hcc, _⟩ := Cb.Fo.ok_parts hok
  rw [(hcc _ (hb y hy).1).2.2.1]
  exact (Cb.ldLkpShift_num _ h.dT _ x (Nat.mod_lt _ (by positivity)) hx).1

/-! ## The premise of the algebra's honest side, and what follows from it -/

/-- If FoNums.ok h = true and every chosen row, at the places below 2^(n_c) of the calls c below
h.NC, is below 2^kT, then rowJ h H X is below 2^d for X below 2^v. -/
theorem rowJ_lt (h : Forest.Shape) (H : Hits) (hok : FoNums.ok h = true)
    (hlt : ∀ c < h.NC, ∀ i < 2 ^ FoNums.nOf h c, H.row c i < 2 ^ h.kT) {X : ℕ}
    (hX : X < 2 ^ h.v) : rowJ h H X < 2 ^ h.d := by
  obtain ⟨⟨_, a2, a3, _⟩, hb, hcc, _⟩ := Cb.Fo.ok_parts hok
  have h00 := hcc 0 a2
  have hx := (Cb.ldLkpShift_split h.dT h.rK X hX).1
  rw [rowJ_eq]
  split_ifs with hl
  · have hc := (hb _ hl).1
    exact (Cb.ldLkpShift_num h.kT h.cK _ _ (hlt _ hc _ (idx_lt hok hl hx))
      (lt_of_lt_of_le hc a3)).1
  · have ht := lt_of_lt_of_le h00.1 (Nat.pow_le_pow_right (by norm_num) h00.2.1)
    exact (Cb.ldLkpShift_num h.kT h.cK _ _ ht (lt_of_lt_of_le a2 a3)).1

/-- If FoNums.ok h = true, the chosen row of every padding place below 2^(n_c) of every call c below
h.NC is the call's padding row, and PubFits h H.pad holds, then for every u the list FoNums.pads h
gives to the joint row u as many padding keys as there are places X below 2^v with padJ h H X = true
and rowJ h H X = u. -/
theorem laid_joint (h : Forest.Shape) (H : Hits) (hok : FoNums.ok h = true)
    (hpad : ∀ c < h.NC, ∀ i < 2 ^ FoNums.nOf h c, H.pad c i = true →
      H.row c i = FoNums.t0Of h c)
    (hpub : PubFits h H.pad) (u : ℕ) :
    padCnt (FoNums.pads h) u =
      (((range (2 ^ h.v)).filter fun X => padJ h H X = true).filter
        fun X => rowJ h H X = u).card := by
  obtain ⟨_, hb, _⟩ := Cb.Fo.ok_parts hok
  rw [card_joint hok H true u, padCnt_pads hok u]
  congr 1
  · refine sum_congr rfl fun y hy => ?_
    have hy' := mem_range.1 hy
    have hc := (hb y hy').1
    rw [hpub y hy']
    by_cases hu : FoNums.padRow h (FoNums.co h y) = u
    · rw [if_pos hu]
      refine congrArg card (filter_congr fun x hx => ?_)
      refine ⟨fun q => ⟨q, ?_⟩, fun q => q.1⟩
      rw [hpad _ hc _ (idx_lt hok hy' (mem_range.1 hx)) q]
      exact hu
    · rw [if_neg hu]
      symm
      rw [card_eq_zero, filter_eq_empty_iff]
      rintro x hx ⟨q1, q2⟩
      rw [hpad _ hc _ (idx_lt hok hy' (mem_range.1 hx)) q1] at q2
      exact hu q2
  · simp

/-- **The premise of the algebra's honest side.** If FoNums.ok h = true and Fits h T K H, then LaidP
holds at h.v, h.d, the joint keys Port.key h T K, the joint table Port.tab h T, the list FoNums.pads
h, padJ h H and rowJ h H. -/
theorem laidP_joint {E : Type} [Field E] (h : Forest.Shape) (T K : ℕ → ℕ → E) (H : Hits)
    (hok : FoNums.ok h = true) (hF : Fits h T K H) :
    LaidP h.v h.d (Port.key h T K) (Port.tab h T) (FoNums.pads h) (padJ h H) (rowJ h H) := by
  obtain ⟨⟨_, a2, _⟩, hb, hcc, _⟩ := Cb.Fo.ok_parts hok
  have h00 := hcc 0 a2
  refine ⟨fun X hX => rowJ_lt h H hok (fun c hc i hi => lt_of_lt_of_le (hF.lt c hc i hi)
    (Nat.pow_le_pow_right (by norm_num) (hcc c hc).2.1)) hX, fun X hX => ?_,
    fun u _ => laid_joint h H hok hF.padRow hF.pub u⟩
  have hx := (Cb.ldLkpShift_split h.dT h.rK X hX).1
  rw [rowJ_eq]
  unfold Port.key
  split_ifs with hl
  · have hc := (hb _ hl).1
    rw [tab_at hok T hc (hF.lt _ hc _ (idx_lt hok hl hx))]
    exact hF.hit _ hc _ (idx_lt hok hl hx)
  · unfold FoNums.padRow
    rw [tab_at hok T a2 h00.1]
    rfl

/-- If FoNums.ok h = true, under the premises of rowJ_lt and laid_joint: the counts count h H c t
over c below h.NC and t below 2^kT, and the number h.padding, add up to 2^v. No key and no table
occurs. -/
theorem sum_count_of (h : Forest.Shape) (H : Hits) (hok : FoNums.ok h = true)
    (hlt : ∀ c < h.NC, ∀ i < 2 ^ FoNums.nOf h c, H.row c i < 2 ^ h.kT)
    (hpad : ∀ c < h.NC, ∀ i < 2 ^ FoNums.nOf h c, H.pad c i = true →
      H.row c i = FoNums.t0Of h c)
    (hpub : PubFits h H.pad) :
    ∑ c ∈ range h.NC, ∑ t ∈ range (2 ^ h.kT), count h H c t + h.padding = 2 ^ h.v := by
  obtain ⟨⟨_, _, a3, _⟩, _⟩ := Cb.Fo.ok_parts hok
  have hR : ∀ b, b < 2 ^ h.v → rowJ h H b < 2 ^ h.d := fun b hb => rowJ_lt h H hok hlt hb
  have hin := padsOK_in (padsOK_of_ok hok)
  have hp : 0 < 2 ^ h.cK := by positivity
  have c1 : ((range (2 ^ h.v)).filter fun X => padJ h H X = true).card = h.padding := by
    rw [← Cb.Fo.pads_sum hok, card_fiber _ (rowJ h H) h.d
      (fun b hb => hR b (mem_range.1 (mem_filter.1 hb).1)),
      ← sum_padCnt h.d _ hin, Finset.sum_range]
    exact sum_congr rfl fun u _ => (laid_joint h H hok hpad hpub u).symm
  have c0 : ((range (2 ^ h.v)).filter fun X => padJ h H X = false).card =
      ∑ c ∈ range h.NC, ∑ t ∈ range (2 ^ h.kT), count h H c t := by
    rw [card_fiber _ (rowJ h H) h.d
      (fun b hb => hR b (mem_range.1 (mem_filter.1 hb).1))]
    have e : ∀ u ∈ range (2 ^ h.d),
        (((range (2 ^ h.v)).filter fun X => padJ h H X = false).filter
          fun X => rowJ h H X = u).card =
        if u % 2 ^ h.cK < h.NC then count h H (u % 2 ^ h.cK) (u / 2 ^ h.cK) else 0 :=
      fun u _ => hmultP_joint h H hok u
    have hd : 2 ^ h.d = 2 ^ h.cK * 2 ^ h.kT := by
      show 2 ^ (h.kT + h.cK) = _
      rw [pow_add, Nat.mul_comm]
    rw [sum_congr rfl e, hd, sum_block, sum_comm (s := range h.NC)]
    refine sum_congr rfl fun t _ => ?_
    have e2 : ∀ c ∈ range (2 ^ h.cK),
        (if (c + 2 ^ h.cK * t) % 2 ^ h.cK < h.NC then
          count h H ((c + 2 ^ h.cK * t) % 2 ^ h.cK) ((c + 2 ^ h.cK * t) / 2 ^ h.cK) else 0) =
        if c < h.NC then count h H c t else 0 := by
      intro c hc
      have hc' := mem_range.1 hc
      rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hc', Nat.add_mul_div_left _ _ hp,
        Nat.div_eq_of_lt hc', Nat.zero_add]
    rw [sum_congr rfl e2, sum_below a3, Nat.mul_zero, Nat.add_zero]
  have c01 := card_filter_add_card_filter_not (s := range (2 ^ h.v)) (fun X => padJ h H X = false)
  simp only [Bool.not_eq_false, card_range] at c01
  rw [← c0, ← c1]
  exact c01

/-- **All counts and all padding keys make up the 2^v keys: no key and no table is asked for.** If
FoNums.ok h = true, every place below 2^(n_c) of a call c below h.NC that is not a padding place has
its chosen row below 2^kT, and PubFits h H.pad holds, then the counts count h H c t over c below
h.NC and t below 2^kT, and the number h.padding, add up to 2^v. -/
theorem sum_count_pub (h : Forest.Shape) (H : Hits) (hok : FoNums.ok h = true)
    (hrow : ∀ c < h.NC, ∀ i < 2 ^ FoNums.nOf h c, H.pad c i = false → H.row c i < 2 ^ h.kT)
    (hpub : PubFits h H.pad) :
    ∑ c ∈ range h.NC, ∑ t ∈ range (2 ^ h.kT), count h H c t + h.padding = 2 ^ h.v := by
  obtain ⟨_, _, hcc, _⟩ := Cb.Fo.ok_parts hok
  have e : ∀ c t, count h H c t = count h
      ⟨H.pad, fun c i => if H.pad c i = true then FoNums.t0Of h c else H.row c i⟩ c t := by
    intro c t
    unfold count
    refine congrArg card (filter_congr fun i _ => ?_)
    refine and_congr_right fun hp => ?_
    show _ ↔ (if H.pad c i = true then FoNums.t0Of h c else H.row c i) = t
    rw [if_neg (by rw [hp]; exact Bool.false_ne_true)]
  simp only [e]
  refine sum_count_of h _ hok (fun c hc i hi => ?_) (fun c _ i _ hp => if_pos hp) hpub
  show (if H.pad c i = true then FoNums.t0Of h c else H.row c i) < 2 ^ h.kT
  split_ifs with hp
  · exact lt_of_lt_of_le (hcc c hc).1 (Nat.pow_le_pow_right (by norm_num) (hcc c hc).2.1)
  · exact hrow c hc i hi (by simpa using hp)

/-- **All counts and all padding keys make up the 2^v keys.** If FoNums.ok h = true and Fits h T K
H, then the counts count h H c t over c below h.NC and t below 2^kT, and the number h.padding, add
up to 2^v. An equation on natural numbers, without a subtraction. -/
theorem sum_count {E : Type} [Field E] (h : Forest.Shape) (T K : ℕ → ℕ → E) (H : Hits)
    (hok : FoNums.ok h = true) (hF : Fits h T K H) :
    ∑ c ∈ range h.NC, ∑ t ∈ range (2 ^ h.kT), count h H c t + h.padding = 2 ^ h.v :=
  sum_count_of h H hok (fun c hc i hi => lt_of_lt_of_le (hF.lt c hc i hi)
    (Nat.pow_le_pow_right (by norm_num) ((Cb.Fo.ok_parts hok).2.2.1 c hc).2.1)) hF.padRow hF.pub

/-- **The algebra's relation MidP at these counts.** If FoNums.ok h = true and Fits h T K H, then at
every shift θ and every point al of the field, MidP holds at h.v, h.d, 5, 32 of the joint keys and
the joint table, each shifted by θ times its call's number, of the list FoNums.pads h and of the
bits hbitP h.v 32 (padJ h H) (rowJ h H). MidP has three clauses: the bits are 0 or 1; their weighted
sum is, in the field, 2^v less the number of padding keys; the product of (al - key) over the 2^v
keys is the padding's factor times the product over j below 32 of (the product over the 2^d rows of
(1 + bit (al - 1 - row)))^(2^j). -/
theorem midP_port {E : Type} [Field E] (h : Forest.Shape) (T K : ℕ → ℕ → E) (H : Hits)
    (hok : FoNums.ok h = true) (hF : Fits h T K H) (θ al : E) :
    MidP h.v h.d 5 32
      (shKeyQ (Port.fK h) (Port.key h T K) (fun c => (c : E)) θ)
      (shTabQ (Port.fT h) (Port.tab h T) (fun c => (c : E)) θ)
      (FoNums.pads h) (hbitP h.v 32 (padJ h H) (rowJ h H)) al := by
  have hL := laidP_joint h T K H hok hF
  have hv : 2 ^ h.v < 2 ^ 32 :=
    Nat.pow_lt_pow_right (by norm_num) (Cb.Fo.ok_parts hok).1.2.2.2.2.1
  refine Cb.honestP E h.v h.d 5 32 _ _ _ _ _ hv (padsOK_of_ok hok)
    ⟨hL.rowLt, fun b hb => ?_, hL.laid⟩ al
  show Port.key h T K b + ((Port.fK h b : ℕ) : E) * θ =
    Port.tab h T (rowJ h H b) + ((Port.fT h (rowJ h H b) : ℕ) : E) * θ
  rw [hL.hit b hb, fT_rowJ h H hok b]

end OnBytes.HonestTrace

#print axioms OnBytes.HonestTrace.sum_block
#print axioms OnBytes.HonestTrace.sum_below
#print axioms OnBytes.HonestTrace.split_iff
#print axioms OnBytes.HonestTrace.list_sum_range
#print axioms OnBytes.HonestTrace.list_sum_filter
#print axioms OnBytes.HonestTrace.padJ_eq
#print axioms OnBytes.HonestTrace.rowJ_eq
#print axioms OnBytes.HonestTrace.sum_trees
#print axioms OnBytes.HonestTrace.card_joint
#print axioms OnBytes.HonestTrace.hmultP_joint
#print axioms OnBytes.HonestTrace.hbitP_joint
#print axioms OnBytes.HonestTrace.fT_rowJ
#print axioms OnBytes.HonestTrace.padsOK_of_ok
#print axioms OnBytes.HonestTrace.padCnt_pads
#print axioms OnBytes.HonestTrace.tab_at
#print axioms OnBytes.HonestTrace.idx_lt
#print axioms OnBytes.HonestTrace.rowJ_lt
#print axioms OnBytes.HonestTrace.laid_joint
#print axioms OnBytes.HonestTrace.laidP_joint
#print axioms OnBytes.HonestTrace.sum_count_of
#print axioms OnBytes.HonestTrace.sum_count_pub
#print axioms OnBytes.HonestTrace.sum_count
#print axioms OnBytes.HonestTrace.midP_port
