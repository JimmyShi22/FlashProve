-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K11/Honest/Law/Ends.lean: AT ITS TWO ENDS WHAT IS SUMMED IS THE FUNCTION ON WHICH THE
MERGE's SUMCHECK RUNS: the tables of Johnson/Desc/K11/Honest/Summand.lean against `shareAt` and
`fmAt` (Johnson/Road/FormsKeysMerge.lean). Lemmas with their proofs. No frame.

The chief names:
  `gamma_rows`          a claim has as many weights on the rows as its unit has rows
  `onColumns_getD`, `rowsSummed_read`   an entry of each of a claim's two tables
  `claim_dot_corners`   the product sum of a claim's two tables is the sum of the claim's share over
                        the points that spell the columns
  `claim_dot_point`     with all bits bound at challenges, the product of the two tables' one entry
                        each is the claim's share at the challenges
  `summand_ends`        for all claims: `claimedSum` reads as the sum of `fmAt` over the points that
                        spell the columns; `endAt` as `fmAt` at the challenges

Beneath them, of the library: `eps_multilinear`, `rowAt_bool`, `sum_list_comm`
(Johnson/Road/FormsKeysMerge.lean); `shape_of_claim`, `wsGamma_eq`, `gamOf_size`, `wsDigits_length`
(Johnson/Road/FormsKeysFac.lean).

Limits. Each claim's unit is asked to be in the layout and to have `UnitOK`, the claim to pass
`wsClaimShape`. Nothing on any property.

-/
import Johnson.Desc.K11.Honest.Law.Bind

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Desc.First.ForkMerge.Honest
open OnBytes (E mulE zeroE oneE)
open OnBytes.Model (Reading WsLay WsUnit WsClaim wsEpsT wsRowPart wsGamma wsClaimShape powers)
open OnBytes.Road (UnitOK GrpOK pt bitsOf rowAt shareAt fmAt)

/-- The summand's point that spells a column (`cornerOf`) is the library's `bitsOf`. -/
theorem cornerOf_eq (lk c : Nat) : cornerOf lk c = bitsOf lk c := rfl

/-- An array's member, read off the array as a list. -/
theorem toList_getD_zero (a : Array E) (j : Nat) : a.toList.getD j zeroE = a.getD j zeroE := by
  simp [Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD]

/-- A member of a table that is made number by number. -/
theorem rangeMap_getD_zero (f : Nat → E) (n c : Nat) (h : c < n) :
    ((List.range n).map f).getD c zeroE = f c := by
  rw [List.getD_eq_getElem _ _ (by simpa using h)]
  simp

/-- A claim has as many weights on the rows as its unit has rows. -/
theorem gamma_rows {lay : WsLay} {q : WsClaim} {u : WsUnit} (hu : lay.U[q.ui]? = some u)
    (hs : wsClaimShape lay q = .ok ()) (U : UnitOK lay.lk u) :
    (wsGamma u (wsRowPart lay q oneE) oneE).size = u.rows := by
  obtain ⟨hlen, hfits⟩ := OnBytes.Road.shape_of_claim hu hs
  have hmap : (q.f.zip u.g).map (·.2) = u.g := List.map_snd_zip (by omega)
  have hok : ∀ y ∈ q.f.zip u.g, GrpOK y.2 ∧ y.1.fits y.2 = true := fun y hy =>
    ⟨U.grp y.2 (by
      have h1 : y.2 ∈ (q.f.zip u.g).map (·.2) := List.mem_map_of_mem hy
      rw [hmap] at h1
      exact h1), hfits y hy⟩
  have hleft : (q.f.zip u.g).map (·.2.left) = u.g.map (·.left) := by
    conv_rhs => rw [← hmap]
    rw [List.map_map]
    rfl
  rw [OnBytes.Road.wsGamma_eq hu, OnBytes.Road.gamOf_size _ hok, hleft, U.rows, List.size_toArray,
    OnBytes.Road.wsDigits_length]

section Read
variable {K : Type} [Field K] (ρ : Reading K)

/-- A sum over a list with its members' numbers, from k on. -/
theorem zipIdx_sum_range (F : E → Nat → K) : ∀ (l : List E) (k : Nat),
    ((l.zipIdx k).map fun y => F y.1 y.2).sum =
      ∑ j ∈ Finset.range l.length, F (l.getD j zeroE) (k + j)
  | [], k => by simp
  | x :: l, k => by
    rw [List.zipIdx_cons, List.map_cons, List.sum_cons, zipIdx_sum_range F l (k + 1),
      List.length_cons, Finset.sum_range_succ', List.getD_cons_zero, Nat.add_zero, add_comm]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [List.getD_cons_succ, show k + (j + 1) = k + 1 + j by omega]

/-- The product sum of two tables of one length, entry by entry. -/
theorem tableDot_range : ∀ (a b : List E) (n : Nat), a.length = n → b.length = n →
    tableDot ρ a b = ∑ j ∈ Finset.range n, ρ.val (a.getD j zeroE) * ρ.val (b.getD j zeroE)
  | [], [], 0, _, _ => by simp [tableDot]
  | x :: a, y :: b, n + 1, ha, hb => by
    have ih := tableDot_range a b n (by simpa using ha) (by simpa using hb)
    unfold tableDot at ih ⊢
    rw [List.zip_cons_cons, List.map_cons, List.sum_cons, ih, Finset.sum_range_succ', add_comm]
    simp only [List.getD_cons_zero, List.getD_cons_succ]
  | [], _, n + 1, ha, _ => by simp at ha
  | _ :: _, _, 0, ha, _ => by simp at ha
  | [], _ :: _, 0, _, hb => by simp at hb
  | _ :: _, [], n + 1, _, hb => by simp at hb

variable {lay : WsLay} {q : WsClaim} {u : WsUnit}

/-- An entry of the first table: the claim's weight on that column. -/
theorem onColumns_getD (lay : WsLay) (q : WsClaim) (C : Nat) (hC : C < 2 ^ lay.lk) :
    (onColumns lay q).getD C zeroE = wsEpsT lay q (bitsOf lay.lk C) := by
  unfold onColumns
  rw [rangeMap_getD_zero _ _ _ hC, cornerOf_eq]

/-- An entry of the second table: the unit's rows in that column under the claim's weights. -/
theorem rowsSummed_read (hu : lay.U[q.ui]? = some u) (hs : wsClaimShape lay q = .ok ())
    (U : UnitOK lay.lk u) (entry : Nat → Nat → E) (C : Nat) (hC : C < 2 ^ lay.lk) :
    ρ.val ((rowsSummed lay entry q).getD C zeroE) =
      ∑ y ∈ Finset.range u.rows,
        ρ.val ((wsGamma u (wsRowPart lay q oneE) oneE).getD y zeroE) *
          ρ.val (entry (u.off + y) C) := by
  unfold rowsSummed
  rw [rangeMap_getD_zero _ _ _ hC]
  have ho : onRows lay q = (wsGamma u (wsRowPart lay q oneE) oneE).toList := by
    unfold onRows
    rw [hu]
  have hoff : ((lay.U[q.ui]?).map (·.off)).getD 0 = u.off := by
    rw [hu]
    rfl
  rw [ho, hoff, foldAdd_read ρ (fun y : E × Nat => mulE y.1 (entry (u.off + y.2) C)), ρ.zero,
    zero_add, zipIdx_sum_range (fun x j => ρ.val (mulE x (entry (u.off + j) C))),
    Array.length_toList, gamma_rows hu hs U]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [ρ.mul, toList_getD_zero, Nat.zero_add]

/-- The first table has one entry for each column. -/
theorem onColumns_length (lay : WsLay) (q : WsClaim) : (onColumns lay q).length = 2 ^ lay.lk := by
  simp [onColumns]

/-- So has the second. -/
theorem rowsSummed_length (lay : WsLay) (entry : Nat → Nat → E) (q : WsClaim) :
    (rowsSummed lay entry q).length = 2 ^ lay.lk := by
  simp [rowsSummed]

/-- A claim's share, its unit laid in. -/
theorem shareAt_unit (hu : lay.U[q.ui]? = some u) (W : OnBytes.Road.Wm K) (rm : Array E) :
    shareAt ρ lay W rm q = ρ.val (wsEpsT lay q rm) * ∑ y ∈ Finset.range u.rows,
      ρ.val ((wsGamma u (wsRowPart lay q oneE) oneE).getD y zeroE) *
        rowAt ρ lay.lk rm W (u.off + y) := by
  unfold shareAt
  rw [hu]

/-- The product sum of a claim's two tables is the sum of the claim's share over the points that
spell the columns. -/
theorem claim_dot_corners (hu : lay.U[q.ui]? = some u) (hs : wsClaimShape lay q = .ok ())
    (U : UnitOK lay.lk u) (entry : Nat → Nat → E) :
    tableDot ρ (onColumns lay q) (rowsSummed lay entry q) =
      ∑ C ∈ Finset.range (2 ^ lay.lk),
        shareAt ρ lay (fun r c => ρ.val (entry r c)) (bitsOf lay.lk C) q := by
  rw [tableDot_range ρ _ _ _ (onColumns_length lay q) (rowsSummed_length lay entry q)]
  refine Finset.sum_congr rfl fun C hC => ?_
  have hC' := Finset.mem_range.1 hC
  rw [onColumns_getD lay q C hC', rowsSummed_read ρ hu hs U entry C hC', shareAt_unit ρ hu]
  congr 1
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [OnBytes.Road.rowAt_bool ρ hC']

/-- With all bits bound at challenges, the product of the two tables' one entry each is the claim's
share at the challenges. -/
theorem claim_dot_point (hu : lay.U[q.ui]? = some u) (hs : wsClaimShape lay q = .ok ())
    (U : UnitOK lay.lk u) (entry : Nat → Nat → E) (rs : List E) (hr : rs.length = lay.lk) :
    ρ.val ((bindAll rs (onColumns lay q)).headD zeroE) *
        ρ.val ((bindAll rs (rowsSummed lay entry q)).headD zeroE) =
      shareAt ρ lay (fun r c => ρ.val (entry r c)) rs.toArray q := by
  rw [bindAll_head_read ρ rs _ (by rw [onColumns_length, hr]),
    bindAll_head_read ρ rs _ (by rw [rowsSummed_length, hr]), hr, shareAt_unit ρ hu,
    OnBytes.Road.eps_multilinear ρ hu (OnBytes.Road.shape_of_claim hu hs).1 U rs.toArray]
  congr 1
  · refine Finset.sum_congr rfl fun C hC => ?_
    rw [onColumns_getD lay q C (Finset.mem_range.1 hC)]
  · have e : ∀ C ∈ Finset.range (2 ^ lay.lk),
        Blocks.eqN lay.lk 0 (pt ρ rs.toArray) C *
            ρ.val ((rowsSummed lay entry q).getD C zeroE) =
          ∑ y ∈ Finset.range u.rows,
            ρ.val ((wsGamma u (wsRowPart lay q oneE) oneE).getD y zeroE) *
              (Blocks.eqN lay.lk 0 (pt ρ rs.toArray) C * ρ.val (entry (u.off + y) C)) := by
      intro C hC
      rw [rowsSummed_read ρ hu hs U entry C (Finset.mem_range.1 hC), Finset.mul_sum]
      refine Finset.sum_congr rfl fun y _ => ?_
      ring
    rw [Finset.sum_congr rfl e, Finset.sum_comm]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [← Finset.mul_sum]
    rfl

/-- **The two ends, for all claims.** Each claim's unit is in the layout and has `UnitOK`, and the
claim passes `wsClaimShape`. Then `claimedSum` of the claims' terms reads as the sum of `fmAt` over
the points that spell the columns; and at lk challenges `endAt` reads as `fmAt` at the challenges.
The matrix is the entries as they are read; claim number i has the power i of x. -/
theorem summand_ends (lay : WsLay) (entry : Nat → Nat → E) (x : E) (cl : Array WsClaim)
    (hcl : ∀ q ∈ cl, ∃ u, lay.U[q.ui]? = some u ∧ wsClaimShape lay q = .ok () ∧ UnitOK lay.lk u) :
    ρ.val (claimedSum (termsOf lay entry x cl.toList)) =
      ∑ C ∈ Finset.range (2 ^ lay.lk),
        fmAt ρ lay (fun r c => ρ.val (entry r c)) (cl.zip (powers x cl.size)).toList
          (bitsOf lay.lk C) ∧
    ∀ rs : List E, rs.length = lay.lk →
      ρ.val (endAt (termsOf lay entry x cl.toList) rs) =
        fmAt ρ lay (fun r c => ρ.val (entry r c)) (cl.zip (powers x cl.size)).toList
          rs.toArray := by
  have hz : (cl.zip (powers x cl.size)).toList =
      cl.toList.zip (powers x cl.toList.length).toList := by
    rw [Array.toList_zip, Array.length_toList]
  have hmem : ∀ y ∈ cl.toList.zip (powers x cl.toList.length).toList,
      ∃ u, lay.U[y.1.ui]? = some u ∧ wsClaimShape lay y.1 = .ok () ∧ UnitOK lay.lk u :=
    fun y hy => hcl y.1 (Array.mem_toList_iff.mp (List.of_mem_zip (a := y.1) (b := y.2) hy).1)
  constructor
  · rw [claimedSum_read, hz]
    unfold termsDot termsOf fmAt
    rw [List.map_map, OnBytes.Road.sum_list_comm]
    refine congrArg List.sum (List.map_congr_left fun y hy => ?_)
    obtain ⟨u, hu, hs, U⟩ := hmem y hy
    rw [← Finset.mul_sum]
    exact congrArg (ρ.val y.2 * ·) (claim_dot_corners ρ hu hs U entry)
  · intro rs hr
    have hl : ∀ t ∈ termsOf lay entry x cl.toList,
        (bindAll rs t.a).length = 1 ∧ (bindAll rs t.b).length = 1 := by
      intro t ht
      unfold termsOf at ht
      obtain ⟨y, _, rfl⟩ := List.mem_map.1 ht
      have l1 := bindAll_length rs (onColumns lay y.1) 0
        (by rw [onColumns_length, hr, Nat.add_zero])
      have l2 := bindAll_length rs (rowsSummed lay entry y.1) 0
        (by rw [rowsSummed_length, hr, Nat.add_zero])
      rw [pow_zero] at l1 l2
      exact ⟨l1, l2⟩
    have hl' := hl
    rw [endAt_read ρ _ rs hl, hz]
    unfold termsDot fmAt
    unfold termsOf at hl' ⊢
    rw [List.map_map]
    refine congrArg List.sum (List.map_congr_left fun y hy => ?_)
    obtain ⟨u, hu, hs, U⟩ := hmem y hy
    have h1 := hl' _ (List.mem_map_of_mem hy)
    show ρ.val y.2 * tableDot ρ (bindAll rs (onColumns lay y.1))
      (bindAll rs (rowsSummed lay entry y.1)) = _
    rw [dot_one ρ _ _ h1.1 h1.2, claim_dot_point ρ hu hs U entry rs hr]

end Read

end Johnson.Desc.First.ForkMerge.Honest

-- Each line below should name no more than propext, Classical.choice and Quot.sound.
#print axioms Johnson.Desc.First.ForkMerge.Honest.cornerOf_eq
#print axioms Johnson.Desc.First.ForkMerge.Honest.toList_getD_zero
#print axioms Johnson.Desc.First.ForkMerge.Honest.rangeMap_getD_zero
#print axioms Johnson.Desc.First.ForkMerge.Honest.gamma_rows
#print axioms Johnson.Desc.First.ForkMerge.Honest.zipIdx_sum_range
#print axioms Johnson.Desc.First.ForkMerge.Honest.tableDot_range
#print axioms Johnson.Desc.First.ForkMerge.Honest.onColumns_getD
#print axioms Johnson.Desc.First.ForkMerge.Honest.rowsSummed_read
#print axioms Johnson.Desc.First.ForkMerge.Honest.onColumns_length
#print axioms Johnson.Desc.First.ForkMerge.Honest.rowsSummed_length
#print axioms Johnson.Desc.First.ForkMerge.Honest.shareAt_unit
#print axioms Johnson.Desc.First.ForkMerge.Honest.claim_dot_corners
#print axioms Johnson.Desc.First.ForkMerge.Honest.claim_dot_point
#print axioms Johnson.Desc.First.ForkMerge.Honest.summand_ends
