-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/SumMergeStart.lean: CONDITIONAL.

What is here. The total of the merge's cube (`mergeJobOf`, Johnson/Desc/K4/Honest/Merge.lean) is the
sum, over the columns, of the function on which the library says that the merge's sumcheck runs
(`fmAt`, Johnson/Road/FormsKeysMerge.lean); and so it is the value of the verifier's form at which
that sumcheck starts (`wsForkStart`), in a world in which each claim's hidden value is what the
claim speaks of. Statements and proofs.

  `wmOf`   the matrix of words, read
  `gam_size`   a claim has a coefficient for each row of its unit
  `colTab_at`, `rowLoop_read`, `rowTab_read`, `merge_share`   a claim's two tables at a column
  `zipFoldM`, `claimVal_read`   **the honest parts' value of a claim reads as the library's**
  `mergeMaps_at`, `zipIdx_mem`, `zipIdx_zip`   which table lies where; numbered lists
  `merge_total`   **the total is the sum of `fmAt` over the columns**
  `merge_start_total`   **the verifier's start form is worth the total**

Limits. At the reading `Reading.gl` alone. Each claim has its unit in the layout, passes the
verifier's test on a claim's shape and stands on a unit as the layout leaves it: premises, as in the
library's `merge_start`. THAT EACH HIDDEN VALUE IS WHAT ITS CLAIM SPEAKS OF IS A PREMISE of
`merge_start_total`, on a world that is a premise too; "what the claim speaks of" is the LIBRARY's
`claimVal` there, and `claimVal_read` says that the honest parts' own reads as it. THAT THERE ARE AT
LEAST AS MANY COEFFICIENTS AS CLAIMS IS A PREMISE. That the form which a verifier claims is
`wsForkStart` at these slots and coefficients, and that its claims are the maker's, is not said
here. Nothing ties the matrix to a commitment. No property is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.SumMerge
import Johnson.Road.FormsKeysMerge

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K4
open OnBytes (E F ofF maddS zeroE oneE)
open OnBytes.Model (Reading World WsLay WsUnit WsClaim wsGamma wsRowPart wsEpsT wsClaimShape
  wsForkStart wsDigits)
open OnBytes.Road (Wm UnitOK fmAt shareAt rowAt_bool merge_start gl_numerals shape_of_claim
  wsGamma_eq gamOf_size wsDigits_length)
open OnBytes.Desc.First.K4.Honest
open OnBytes.Desc.First.K4.Honest.CubeLaw

/-- The matrix of words, read in the library's extension field. -/
def wmOf (w : Nat → Nat → F) : Wm Cb.Gl.E := fun y C => Reading.gl.val (ofF (w y C))

/-! ## 1 A claim's two tables -/

/-- A claim that passes the verifier's test has a coefficient for each row of its unit. -/
theorem gam_size {lay : WsLay} {c : WsClaim} {u : WsUnit} (hu : lay.U[c.ui]? = some u)
    (hs : wsClaimShape lay c = .ok ()) (U : UnitOK lay.lk u) :
    (wsGamma u (wsRowPart lay c oneE) oneE).size = u.rows := by
  obtain ⟨hlen, hfits⟩ := shape_of_claim hu hs
  have hmap : (c.f.zip u.g).map (·.2) = u.g := List.map_snd_zip (by omega)
  have hleft : ((c.f.zip u.g).map (·.2.left)).prod = (u.g.map (·.left)).prod := by
    have h1 : (((c.f.zip u.g).map (·.2)).map (·.left)).prod = (u.g.map (·.left)).prod := by
      rw [hmap]
    rw [← h1, List.map_map]
    rfl
  rw [wsGamma_eq hu, gamOf_size _ (fun y hy => ⟨U.grp y.2 (by
    have h1 : y.2 ∈ (c.f.zip u.g).map (·.2) := List.mem_map_of_mem hy
    rw [hmap] at h1
    exact h1), hfits y hy⟩), hleft, U.rows, List.size_toArray, wsDigits_length]

/-- A claim's first table at a column: the verifier's weight at the point that spells the column.
An equation on words. -/
theorem colTab_at (lay : WsLay) (c : WsClaim) (i : ℕ) (hi : i < 2 ^ lay.lk) :
    (colTab lay c).getD i zeroE = wsEpsT lay c (OnBytes.Road.bitsOf lay.lk i) := by
  show ((List.range (2 ^ lay.lk)).map fun C =>
    wsEpsT lay c (OnBytes.Road.bitsOf lay.lk C)).toArray.getD i zeroE = _
  rw [Array.getD_eq_getD_getElem?, List.getElem?_toArray, List.getElem?_map,
    List.getElem?_range hi]
  rfl

/-- The loop of `rowTab`, read. -/
theorem rowLoop_read (w : Nat → Nat → F) (off col : ℕ) : ∀ (l : List E) (s : E) (n : ℕ),
    Reading.gl.val (l.foldl (fun (s : E × Nat) k => (maddS s.1 (w (off + s.2) col) k, s.2 + 1))
      (s, n)).1 = Reading.gl.val s +
        ∑ y ∈ Finset.range l.length, Reading.gl.val (l.getD y zeroE) * wmOf w (off + (n + y)) col
  | [], s, n => by simp
  | k :: l, s, n => by
    have e : Reading.gl.val (maddS s (w (off + n) col) k) =
        Reading.gl.val s + Reading.gl.val k * wmOf w (off + n) col := by
      have h1 : Reading.gl.val (maddS s (w (off + n) col) k) =
          Reading.gl.val s + OnBytes.Slice.toF (w (off + n) col) • Reading.gl.val k :=
        OnBytes.Slice.readE_maddS s _ k
      have h2 : wmOf w (off + n) col =
          algebraMap Cb.Gl.F Cb.Gl.E (OnBytes.Slice.toF (w (off + n) col)) :=
        OnBytes.Slice.readE_ofF _
      rw [h1, h2, Algebra.smul_def, mul_comm]
    rw [List.foldl_cons, rowLoop_read w off col l, e, List.length_cons, Finset.sum_range_succ']
    simp only [List.getD_cons_succ, List.getD_cons_zero, Nat.add_zero]
    have e2 : ∀ y, n + 1 + y = n + (y + 1) := fun y => by omega
    simp only [e2]
    ring

/-- A claim's second table at a column: the unit's rows under the claim's coefficients. -/
theorem rowTab_read {lay : WsLay} {c : WsClaim} {u : WsUnit} (w : Nat → Nat → F)
    (hu : lay.U[c.ui]? = some u)
    (hsz : (wsGamma u (wsRowPart lay c oneE) oneE).size = u.rows) (i : ℕ) (hi : i < 2 ^ lay.lk) :
    Reading.gl.val ((rowTab lay w c).getD i zeroE) = ∑ y ∈ Finset.range u.rows,
      Reading.gl.val ((wsGamma u (wsRowPart lay c oneE) oneE).getD y zeroE) *
        wmOf w (u.off + y) i := by
  have e : rowTab lay w c = Array.ofFn (n := 2 ^ lay.lk) fun col =>
      ((wsGamma u (wsRowPart lay c oneE) oneE).foldl
        (fun (s : E × Nat) k => (maddS s.1 (w (u.off + s.2) col.val) k, s.2 + 1))
        (zeroE, 0)).1 := by
    unfold rowTab
    rw [hu]
  rw [e, ofFnE_getD _ i hi, ← Array.foldl_toList, rowLoop_read, Reading.gl.zero, zero_add,
    Array.length_toList, hsz]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [Nat.zero_add, Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD,
    Array.getElem?_toList]

/-- The product of a claim's two tables at a column is the claim's share there. -/
theorem merge_share {lay : WsLay} {c : WsClaim} {u : WsUnit} (w : Nat → Nat → F)
    (hu : lay.U[c.ui]? = some u) (hs : wsClaimShape lay c = .ok ()) (U : UnitOK lay.lk u) (i : ℕ)
    (hi : i < 2 ^ lay.lk) :
    Reading.gl.val ((colTab lay c).getD i zeroE) * Reading.gl.val ((rowTab lay w c).getD i zeroE) =
      shareAt Reading.gl lay (wmOf w) (OnBytes.Road.bitsOf lay.lk i) c := by
  rw [colTab_at lay c i hi, rowTab_read w hu (gam_size hu hs U) i hi]
  unfold shareAt
  rw [hu]
  show _ = Reading.gl.val (wsEpsT lay c (OnBytes.Road.bitsOf lay.lk i)) *
    ∑ y ∈ Finset.range u.rows, _
  congr 1
  exact Finset.sum_congr rfl fun y _ => by rw [rowAt_bool Reading.gl hi]

/-- The loop of the honest parts' value of a claim, read. -/
theorem zipFoldM : ∀ (a b : List E) (s : E),
    Reading.gl.val ((a.zip b).foldl (fun s y => OnBytes.maddE s y.1 y.2) s) =
      Reading.gl.val s + dotK (a.map Reading.gl.val) fun i => Reading.gl.val (b.getD i zeroE)
  | [], _, _ => by simp [dotK]
  | x :: a, [], s => by
    have e : (fun i => Reading.gl.val (([] : List E).getD i zeroE)) = fun _ => (0 : Cb.Gl.E) := by
      funext i
      simp [Reading.gl.zero]
    rw [e, dotK_zero]
    simp
  | x :: a, y :: b, s => by
    have hm : ∀ u v z : E, Reading.gl.val (OnBytes.maddE u v z) =
        Reading.gl.val u + Reading.gl.val v * Reading.gl.val z := OnBytes.Slice.readE_maddE
    rw [List.zip_cons_cons, List.foldl_cons, zipFoldM a b, hm]
    simp only [List.map_cons, dotK, List.getD_cons_zero, List.getD_cons_succ]
    ring

/-- **The honest parts' value of a claim** (`claimVal` of Johnson/Desc/K4/Honest/Merge.lean: a loop
over the claim's two tables) **reads as the library's** (`claimVal` of
Johnson/Road/FormsKeysWm.lean: the sum that the claim speaks of in the matrix). -/
theorem claimVal_read {lay : WsLay} {c : WsClaim} {u : WsUnit} (w : Nat → Nat → F)
    (hu : lay.U[c.ui]? = some u) (hs : wsClaimShape lay c = .ok ()) (U : UnitOK lay.lk u) :
    Reading.gl.val (OnBytes.Desc.First.K4.Honest.claimVal lay w c) =
      OnBytes.Road.claimVal Reading.gl lay (wmOf w) c := by
  have hsum := OnBytes.Road.merge_sum gl_numerals (wmOf w) [(c, oneE)] (lay := lay) (by
    intro y hy
    rw [List.mem_singleton] at hy
    rw [hy]
    exact ⟨u, hu, hs, U⟩)
  simp only [fmAt, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
    Reading.gl.one, one_mul] at hsum
  rw [← hsum]
  unfold OnBytes.Desc.First.K4.Honest.claimVal
  rw [← Array.foldl_toList, Array.toList_zip, zipFoldM, Reading.gl.zero, zero_add, dotK_sum,
    List.length_map, Array.length_toList, colTab_size]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [← merge_share w hu hs U i (Finset.mem_range.mp hi), getD_mapA]
  congr 2
  rw [Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD, Array.getElem?_toList]

/-! ## 2 Which table lies where -/

/-- Behind 2 k tables, claim number k has the tables 2 k and 2 k + 1. -/
theorem mergeMaps_at (lay : WsLay) (w : Nat → Nat → F) : ∀ (cls : List WsClaim) (P : List Tab)
    (k : ℕ), P.length = 2 * k → ∀ x ∈ cls.zipIdx k,
    (P ++ cls.flatMap fun c => [colTab lay c, rowTab lay w c]).getD (2 * x.2) #[] =
        colTab lay x.1 ∧
      (P ++ cls.flatMap fun c => [colTab lay c, rowTab lay w c]).getD (2 * x.2 + 1) #[] =
        rowTab lay w x.1
  | [], _, _, _, x, hx => by simp at hx
  | c :: cls, P, k, hP, x, hx => by
    rw [List.zipIdx_cons, List.mem_cons] at hx
    rcases hx with rfl | hx
    · constructor
      · rw [List.getD_append_right _ _ _ _ (by rw [hP]), hP, Nat.sub_self]
        rfl
      · rw [List.getD_append_right _ _ _ _ (by rw [hP]; omega), hP,
          show 2 * k + 1 - 2 * k = 1 by omega]
        rfl
    · have e : P ++ (c :: cls).flatMap (fun c => [colTab lay c, rowTab lay w c]) =
          (P ++ [colTab lay c, rowTab lay w c]) ++
            cls.flatMap fun c => [colTab lay c, rowTab lay w c] := by
        simp
      rw [e]
      exact mergeMaps_at lay w cls _ (k + 1) (by simp [hP]; omega) x hx

/-- A numbered member is a member. -/
theorem zipIdx_mem {α : Type} : ∀ (l : List α) (k : ℕ), ∀ x ∈ l.zipIdx k, x.1 ∈ l
  | [], _, x, hx => by simp at hx
  | a :: l, k, x, hx => by
    rw [List.zipIdx_cons, List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (zipIdx_mem l (k + 1) x hx)

/-! ## 3 The total -/

/-- **The total of the merge's cube is the sum, over the columns, of the function on which the
merge's sumcheck runs.** -/
theorem merge_total (lay : WsLay) (w : Nat → Nat → F) (cls : List WsClaim) (rho : Array E)
    (hcl : ∀ c ∈ cls, ∃ u, lay.U[c.ui]? = some u ∧ wsClaimShape lay c = .ok () ∧
      UnitOK lay.lk u) :
    Reading.gl.val (mergeJobOf lay w cls rho).cube.total = ∑ C ∈ Finset.range (2 ^ lay.lk),
      fmAt Reading.gl lay (wmOf w) (cls.zipIdx.map fun x => (x.1, rho.getD x.2 zeroE))
        (OnBytes.Road.bitsOf lay.lk C) := by
  rw [total_plain Reading.gl _ rfl]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' : i < 2 ^ lay.lk := Finset.mem_range.mp hi
  rw [termsAt_read]
  show ((cls.zipIdx.map fun x => (rho.getD x.2 zeroE, 2 * x.2, 2 * x.2 + 1)).map _).sum = _
  unfold fmAt
  rw [List.map_map, List.map_map]
  refine congrArg List.sum (List.map_congr_left fun x hx => ?_)
  obtain ⟨u, hu, hs, U⟩ := hcl x.1 (zipIdx_mem cls 0 x hx)
  have hm := mergeMaps_at lay w cls [] 0 rfl x hx
  have hg : ∀ a, (mergeJobOf lay w cls rho).cube.maps.getD a #[] =
      ([] ++ cls.flatMap fun c => [colTab lay c, rowTab lay w c]).getD a #[] := by
    intro a
    have ht : (mergeJobOf lay w cls rho).cube.maps.toList =
        [] ++ cls.flatMap fun c => [colTab lay c, rowTab lay w c] :=
      mergeMaps_toList lay w cls #[]
    rw [← ht, Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD, Array.getElem?_toList]
  show Reading.gl.val (rho.getD x.2 zeroE) *
    (Reading.gl.val (((mergeJobOf lay w cls rho).cube.maps.getD (2 * x.2) #[]).getD i zeroE) *
      Reading.gl.val (((mergeJobOf lay w cls rho).cube.maps.getD (2 * x.2 + 1) #[]).getD i
        zeroE)) = Reading.gl.val (rho.getD x.2 zeroE) * _
  rw [hg, hg, hm.1, hm.2, merge_share w hu hs U i hi']

/-- Claims numbered, each with its coefficient, where there are coefficients enough. -/
theorem zipIdx_zip {α : Type} (rho : List E) : ∀ (cls : List α) (k : ℕ),
    k + cls.length ≤ rho.length →
    (cls.zipIdx k).map (fun x => (x.1, rho.getD x.2 zeroE)) = cls.zip (rho.drop k)
  | [], _, _ => by simp
  | c :: cls, k, h => by
    rw [List.length_cons] at h
    have hk : k < rho.length := by omega
    have e : rho.drop k = rho.getD k zeroE :: rho.drop (k + 1) := by
      rw [List.drop_eq_getElem_cons hk, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]
      rfl
    rw [List.zipIdx_cons, List.map_cons, zipIdx_zip rho cls (k + 1) (by omega), e,
      List.zip_cons_cons]

/-- **The verifier's start form is worth the total of the merge's cube**, in a world in which the
hidden value under each claim's slot is the sum that the claim speaks of in the matrix. -/
theorem merge_start_total (lay : WsLay) (w : Nat → Nat → F) (Wd : World Cb.Gl.E)
    (cl : Array WsClaim) (sv : Array ℕ) (rho : Array E)
    (hcl : ∀ c ∈ cl, ∃ u, lay.U[c.ui]? = some u ∧ wsClaimShape lay c = .ok () ∧ UnitOK lay.lk u)
    (hslot : List.Forall₂ (fun s c => Wd.slot s = OnBytes.Road.claimVal Reading.gl lay (wmOf w) c)
      sv.toList cl.toList) (hlen : cl.size ≤ rho.size) :
    (wsForkStart sv rho).value Reading.gl Wd =
      Reading.gl.val (mergeJobOf lay w cl.toList rho).cube.total := by
  have e : (cl.toList.zipIdx.map fun x => (x.1, rho.getD x.2 zeroE)) = (cl.zip rho).toList := by
    have h := zipIdx_zip rho.toList cl.toList 0 (by simpa using hlen)
    rw [List.drop_zero] at h
    rw [Array.toList_zip, ← h]
    refine List.map_congr_left fun x _ => ?_
    rw [Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD, Array.getElem?_toList]
  rw [merge_start gl_numerals (wmOf w) Wd cl sv rho hcl hslot,
    merge_total lay w cl.toList rho (fun c hc => hcl c (Array.mem_def.mpr hc)), e]

end ProofFile.Honest.K4

#print axioms ProofFile.Honest.K4.gam_size
#print axioms ProofFile.Honest.K4.colTab_at
#print axioms ProofFile.Honest.K4.rowLoop_read
#print axioms ProofFile.Honest.K4.rowTab_read
#print axioms ProofFile.Honest.K4.merge_share
#print axioms ProofFile.Honest.K4.zipFoldM
#print axioms ProofFile.Honest.K4.claimVal_read
#print axioms ProofFile.Honest.K4.mergeMaps_at
#print axioms ProofFile.Honest.K4.zipIdx_mem
#print axioms ProofFile.Honest.K4.merge_total
#print axioms ProofFile.Honest.K4.zipIdx_zip
#print axioms ProofFile.Honest.K4.merge_start_total
