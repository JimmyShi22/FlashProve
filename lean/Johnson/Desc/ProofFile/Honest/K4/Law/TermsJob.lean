-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/TermsJob.lean: CONDITIONAL.

What is here. THE SECOND TOKEN SUMCHECK's JOB MEETS THE THREE PREMISES THAT THE CUBE's TIE ASKS OF A
JOB (CubeSum.lean: a polynomial along the masked line; it reads its values through the reading; on
the true end values it is the cube's summand), UNDER THE HYPOTHESIS `TripsAt` (TermsTrips.lean) at
the point that the challenges make. Statements and proofs.

  `tab_at`, `aMaps_at`, `bMaps_at`, `endMaps_at`   the cube's tables, entry by entry
  `terms_maps`   which table lies where
  `terms_summandAt`   the cube's summand at the challenges
  `terms_poly`, `terms_alike`, `terms_end`   **the three**

Limits. At the reading `Reading.gl`. `TripsAt` IS A HYPOTHESIS, not shown here (KindsOf.lean and
TermsAll.lean have it from public premises). Beside it: the job is made; as many challenges as a
token's number has bits. It stands on the job's text as Johnson/Road/K4/C/TermsOpen.lean opens it.
No property is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.TermsTrips
import Johnson.Road.K4.C.TermsOpen
import Johnson.Desc.K4.Honest.Law.Cube

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K4
open OnBytes (E zeroE)
open OnBytes.Model (Reading orderDefault)
open OnBytes.Model.Layer (nEndT)
open OnBytes.Road (pt)
open OnBytes.Road.K4.C (endMapsOf firstOf aMapsOf bMapsOf termsCube jobTermsOn_whole
  tokenRows_size)
open OnBytes.Desc.First.K4.Honest
open OnBytes.Desc.First.K4.Honest.CubeLaw

/-! ## 1 The cube's tables -/

/-- A table that is made row by row of the tokens' rows, at a token's number: beyond the rows it
holds the zero word, and so does the reader of the empty row where f of it is the zero word. -/
theorem tab_at (rows : TokRows) (f : Array E × Array Trip → E) (h0 : f (#[], #[]) = zeroE)
    (t : ℕ) : (rows.map f).getD t zeroE = f (rows.getD t (#[], #[])) := by
  rw [Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?, Array.getElem?_map]
  cases rows[t]? with
  | none => exact h0.symm
  | some x => rfl

theorem aMaps_at (rows : TokRows) (k : ℕ) (hk : k < (firstOf rows).size) (t : ℕ) :
    ((aMapsOf rows).getD k #[]).getD t zeroE = aAt rows t k := by
  have e : (aMapsOf rows).getD k #[] =
      rows.map fun x => (x.2.getD k (zeroE, zeroE, zeroE)).2.1 := by
    unfold aMapsOf
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_map, Array.getElem?_range, if_pos hk]
    rfl
  rw [e]
  exact tab_at rows _ rfl t

theorem bMaps_at (rows : TokRows) (k : ℕ) (hk : k < (firstOf rows).size) (t : ℕ) :
    ((bMapsOf rows).getD k #[]).getD t zeroE = bAt rows t k := by
  have e : (bMapsOf rows).getD k #[] =
      rows.map fun x => (x.2.getD k (zeroE, zeroE, zeroE)).2.2 := by
    unfold bMapsOf
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_map, Array.getElem?_range, if_pos hk]
    rfl
  rw [e]
  exact tab_at rows _ rfl t

theorem endMaps_at (y : OnBytes.Model.Layer.Lay) (rows : TokRows) (i : ℕ) (hi : i < nEndT y)
    (t : ℕ) : ((endMapsOf y rows).getD i #[]).getD t zeroE = shAt rows t i := by
  have e : (endMapsOf y rows).getD i #[] = rows.map fun x => x.1.getD i zeroE := by
    unfold endMapsOf
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_map, Array.getElem?_range, if_pos hi]
    rfl
  rw [e]
  exact tab_at rows _ rfl t

/-- Which table lies where in the cube's list. -/
theorem terms_maps (S : Sides) (rows : TokRows) (k : ℕ) (hk : k < (firstOf rows).size) :
    (termsCube S rows).maps.getD (nEndT S.v.y + k) #[] = (aMapsOf rows).getD k #[] ∧
      (termsCube S rows).maps.getD (nEndT S.v.y + (firstOf rows).size + k) #[] =
        (bMapsOf rows).getD k #[] := by
  have s1 : (endMapsOf S.v.y rows).size = nEndT S.v.y := by simp [endMapsOf]
  have s2 : (aMapsOf rows).size = (firstOf rows).size := by simp [aMapsOf]
  show (endMapsOf S.v.y rows ++ aMapsOf rows ++ bMapsOf rows).getD _ #[] = _ ∧
    (endMapsOf S.v.y rows ++ aMapsOf rows ++ bMapsOf rows).getD _ #[] = _
  simp only [Array.getD_eq_getD_getElem?]
  constructor
  · rw [Array.getElem?_append_left (by rw [Array.size_append, s1, s2]; omega),
      Array.getElem?_append_right (by rw [s1]; omega), s1, Nat.add_sub_cancel_left]
  · rw [Array.getElem?_append_right (by rw [Array.size_append, s1, s2]; omega), Array.size_append,
      s1, s2, Nat.add_sub_cancel_left]

/-! ## 2 The cube's summand at the challenges -/

/-- **The cube's summand at the challenges**: the sum over the products of the weight times the two
factors' extensions at the point that the challenges make. -/
theorem terms_summandAt (S : Sides) (rows : TokRows) (hfit : (termsCube S rows).fits = true)
    (rs : List E) (hr : rs.length = S.v.y.h.lt) :
    Reading.gl.val ((termsCube S rows).summandAt rs) =
      ∑ k ∈ Finset.range (rows.getD 0 (#[], #[])).2.size, Reading.gl.val (wAt rows k) *
        (Blocks.ext S.v.y.h.lt (fun t => Reading.gl.val (aAt rows t k))
            (pt Reading.gl rs.toArray) *
          Blocks.ext S.v.y.h.lt (fun t => Reading.gl.val (bAt rows t k))
            (pt Reading.gl rs.toArray)) := by
  have hp : (termsCube S rows).pointOf rs = rs.toArray := pointOf_default _ hfit rfl rs hr
  have hz : rs.toArray.size = S.v.y.h.lt := by simpa using hr
  rw [summandAt_read]
  show (((List.range (firstOf rows).size).map fun k =>
    (((firstOf rows).getD k (zeroE, zeroE, zeroE)).1, nEndT S.v.y + k,
      nEndT S.v.y + (firstOf rows).size + k)).map _).sum = _
  rw [List.map_map, sum_by_number 0, List.length_range]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' : k < (firstOf rows).size := Finset.mem_range.mp hk
  have eg : (List.range (firstOf rows).size).getD k 0 = k := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_range hk']
    rfl
  rw [eg]
  obtain ⟨m1, m2⟩ := terms_maps S rows k hk'
  show Reading.gl.val (wAt rows k) *
    (Reading.gl.val (((termsCube S rows).valuesAt rs).getD (nEndT S.v.y + k) zeroE) *
      Reading.gl.val (((termsCube S rows).valuesAt rs).getD
        (nEndT S.v.y + (firstOf rows).size + k) zeroE)) = _
  rw [valuesAt_mle Reading.gl _ hfit rs hr, valuesAt_mle Reading.gl _ hfit rs hr, hp, m1, m2,
    mle_ext, mle_ext, hz]
  congr 2
  · exact Blocks.ext_congr (fun t _ => by rw [aMaps_at rows k hk' t]) _
  · exact Blocks.ext_congr (fun t _ => by rw [bMaps_at rows k hk' t]) _

/-! ## 3 The three -/

variable {S : Sides} {J : Job} {idx : ℕ → Option ℕ}

/-- **Along the masked line the job's summand is a polynomial of degree at most 1.** -/
theorem terms_poly (hJ : jobTermsOn S = some J) (rs m : List E) (hr : rs.length = S.v.y.h.lt)
    (T : ∀ rows, tokenRows S = some rows → TripsAt S rows rs.toArray idx) :
    PolyOn J.dY fun y => J.atEnds rs (maskedEnds (J.ends rs) m y) := by
  obtain ⟨rows, h1, hfit, _, _, rfl⟩ := jobTermsOn_whole hJ
  have hp : (termsCube S rows).pointOf rs = rs.toArray := pointOf_default _ hfit rfl rs hr
  show PolyOn 1 fun y => (S.summand (maskedEnds _ m y).toArray
    ((termsCube S rows).pointOf rs)).getD zeroE
  rw [hp]
  exact trips_poly (T rows h1) _ m

/-- **It reads its values through the reading.** -/
theorem terms_alike (hJ : jobTermsOn S = some J) (rs : List E) (hr : rs.length = S.v.y.h.lt)
    (T : ∀ rows, tokenRows S = some rows → TripsAt S rows rs.toArray idx) :
    ReadsAlike (J.atEnds rs) := by
  obtain ⟨rows, h1, hfit, _, _, rfl⟩ := jobTermsOn_whole hJ
  have hp : (termsCube S rows).pointOf rs = rs.toArray := pointOf_default _ hfit rfl rs hr
  show ReadsAlike fun e => (S.summand e.toArray ((termsCube S rows).pointOf rs)).getD zeroE
  rw [hp]
  exact trips_alike (T rows h1)

/-- **On the true end values it is the cube's summand.** -/
theorem terms_end (hJ : jobTermsOn S = some J) (rs : List E) (hr : rs.length = S.v.y.h.lt)
    (T : ∀ rows, tokenRows S = some rows → TripsAt S rows rs.toArray idx) :
    Reading.gl.val (J.atEnds rs (J.ends rs)) = Reading.gl.val (J.cube.summandAt rs) := by
  obtain ⟨rows, h1, hfit, _, hsz, rfl⟩ := jobTermsOn_whole hJ
  have hp : (termsCube S rows).pointOf rs = rs.toArray := pointOf_default _ hfit rfl rs hr
  have hz : rs.toArray.size = S.v.y.h.lt := by simpa using hr
  show Reading.gl.val ((S.summand
    ((endMapsOf S.v.y rows).map fun t => mle t ((termsCube S rows).pointOf rs)).toList.toArray
    ((termsCube S rows).pointOf rs)).getD zeroE) = Reading.gl.val ((termsCube S rows).summandAt rs)
  rw [hp, terms_summandAt S rows hfit rs hr, Array.toArray_toList]
  refine trips_end (T rows h1) _ fun k i _ => ?_
  have hs : (endMapsOf S.v.y rows).size = nEndT S.v.y := by simp [endMapsOf]
  by_cases hb : i < nEndT S.v.y
  · have e : ((endMapsOf S.v.y rows).map fun t => mle t rs.toArray).getD i zeroE =
        mle ((endMapsOf S.v.y rows).getD i #[]) rs.toArray := by
      rw [Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?, Array.getElem?_map,
        Array.getElem?_eq_getElem (by rw [hs]; exact hb)]
      rfl
    rw [e, mle_ext, hz]
    exact Blocks.ext_congr (fun t _ => by rw [endMaps_at S.v.y rows i hb t]) _
  · -- beyond the shown values both sides read 0
    have e : ((endMapsOf S.v.y rows).map fun t => mle t rs.toArray).getD i zeroE = zeroE := by
      rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (by rw [Array.size_map, hs]; omega)]
      rfl
    have e0 : ∀ t, shAt rows t i = zeroE := by
      intro t
      unfold shAt
      have er : rows.getD t (#[], #[]) = (rows[t]?).getD (#[], #[]) := by
        rw [Array.getD_eq_getD_getElem?]
      rw [er]
      cases ht : rows[t]? with
      | none => rfl
      | some x =>
        have hx : x ∈ rows.toList := by
          rw [← Array.getElem?_toList] at ht
          exact List.mem_of_getElem? ht
        rw [← Array.all_toList, List.all_eq_true] at hsz
        have h2 := hsz x hx
        rw [Bool.and_eq_true, beq_iff_eq] at h2
        show x.1.getD i zeroE = zeroE
        rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (by rw [h2.1]; omega)]
        rfl
    rw [e, Reading.gl.zero]
    unfold Blocks.ext
    exact (Finset.sum_eq_zero fun t _ => by
      show _ * Reading.gl.val (shAt rows t i) = 0
      rw [e0 t, Reading.gl.zero, mul_zero]).symm

end ProofFile.Honest.K4

#print axioms ProofFile.Honest.K4.tab_at
#print axioms ProofFile.Honest.K4.aMaps_at
#print axioms ProofFile.Honest.K4.bMaps_at
#print axioms ProofFile.Honest.K4.endMaps_at
#print axioms ProofFile.Honest.K4.terms_maps
#print axioms ProofFile.Honest.K4.terms_summandAt
#print axioms ProofFile.Honest.K4.terms_poly
#print axioms ProofFile.Honest.K4.terms_alike
#print axioms ProofFile.Honest.K4.terms_end
