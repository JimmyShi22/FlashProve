-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K4/Law/SumMerge.lean: CONDITIONAL. Statements with their proofs; no
definition.

What is here. What the law of the masked sumcheck's honest part asks of a caller (`SumsTo`,
Honest/SumLaw/Terms.lean), at the merge's sumcheck of the feed-forward layers' rounds (`mergeJobOf`,
`jobMerge`, Johnson/Desc/K4/Honest/Merge.lean).

  `colTab_size`, `rowTab_size`, `mergeMaps_toList`, `mergeMaps_size`, `mergePairs_lt`   the tables,
     their number, and which of them the pairs name
  `mergeJob_fits`   the cube's sizes fit, at every list of claims, matrix and list of coefficients
  `mergeJob_jobFits`   the job has the public shape of the row's seventh call
  `k4Shapes_merge`   which is that shape
  `mergeJob_sumsTo`, `merge_sumsTo`   **the chain**, of a list of claims; at the row's own job

Limits. THREE FILES THAT ARE NAMED BELOW ARE NO PART OF THE LIBRARY YET: SumMergeStart.lean and
SumAtRun.lean beside this file, and Johnson/Desc/K4/Honest/Law/PtsPowers.lean. At the reading
`Reading.gl` alone. THAT THE LIST OF CLAIMS IS MADE (`mergeClaimsAt` returns) IS A PREMISE; so is
that there is one mask entry for the one end value, and that there are as many challenges as the
matrix has column bits, and one more. NEITHER END OF THE CHAIN IS TIED TO A VERIFIER's FORM HERE: it
begins at the reading of the cube's total and ends at the summand at the challenges plus the last
challenge times the mask entry; that the first is the value of the form that the verifier claims
(SumMergeStart.lean beside this file), and that the second is the value as it was sent, is not said
here. `mergeJob_fits` IS A WORD ON SIZES ALONE: a claim for which there is no coefficient counts
with 0, and a claim whose unit the layout lacks has a table of zeros. THE TWO PADDINGS HOLD OF THE
CHAIN TOO: where there are fewer coefficients than claims it is the chain of the shorter sum, of the
empty sum where the fourth batching round is not heard. That the claims, the coefficients and the
plan's count of claims are as many is said elsewhere, under premises: `merge_run` (SumAtRun.lean),
`pts_rhoW` (Johnson/Desc/K4/Honest/Law/PtsPowers.lean). Nothing on the claims' values, on the
committed matrix or on the pending row.

No property is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.CubeSum

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K4
open OnBytes (E F zeroE)
open OnBytes.Model (Reading WsLay WsClaim)
open OnBytes.Desc.First.K4.Honest
open OnBytes.Desc.First.K4.Honest.CubeLaw
open VerifiableInference.Desc.Part.MaskedSum (Call)
open ProofFile.Honest.SumLaw (SumsTo jobPoly)

/-! ## 1 The sizes -/

/-- A claim's first table has an entry for each column. -/
theorem colTab_size (lay : WsLay) (c : WsClaim) : (colTab lay c).size = 2 ^ lay.lk := by
  simp [colTab, Johnson.Desc.First.ForkMerge.Honest.onColumns]

/-- So has its second. -/
theorem rowTab_size (lay : WsLay) (w : Nat → Nat → F) (c : WsClaim) :
    (rowTab lay w c).size = 2 ^ lay.lk := by
  unfold rowTab
  split <;> simp

/-- The merge's tables as a list: two for each claim. -/
theorem mergeMaps_toList (lay : WsLay) (w : Nat → Nat → F) : ∀ (cls : List WsClaim)
    (acc : Array Tab),
    (cls.foldl (fun a c => (a.push (colTab lay c)).push (rowTab lay w c)) acc).toList =
      acc.toList ++ cls.flatMap fun c => [colTab lay c, rowTab lay w c]
  | [], acc => by simp
  | c :: cls, acc => by
    rw [List.foldl_cons, mergeMaps_toList lay w cls]
    simp

/-- Two tables for each claim. -/
theorem mergeMaps_size (lay : WsLay) (w : Nat → Nat → F) : ∀ (cls : List WsClaim)
    (acc : Array Tab),
    (cls.foldl (fun a c => (a.push (colTab lay c)).push (rowTab lay w c)) acc).size =
      acc.size + 2 * cls.length
  | [], acc => by simp
  | c :: cls, acc => by
    rw [List.foldl_cons, mergeMaps_size lay w cls, Array.size_push, Array.size_push,
      List.length_cons]
    omega

/-- Both tables that a pair names are there. -/
theorem mergePairs_lt (rho : Array E) : ∀ (cls : List WsClaim) (k : ℕ),
    ∀ x ∈ (cls.zipIdx k).map fun x => (rho.getD x.2 zeroE, 2 * x.2, 2 * x.2 + 1),
      x.2.1 < 2 * (k + cls.length) ∧ x.2.2 < 2 * (k + cls.length)
  | [], _, x, hx => by simp at hx
  | c :: cls, k, x, hx => by
    rw [List.zipIdx_cons, List.map_cons, List.mem_cons] at hx
    rw [List.length_cons]
    rcases hx with rfl | hx
    · constructor
      · show 2 * k < _
        omega
      · show 2 * k + 1 < _
        omega
    · have := mergePairs_lt rho cls (k + 1) x hx
      constructor <;> omega

/-- **The merge's cube fits**, whatever the claims, the matrix and the coefficients. -/
theorem mergeJob_fits (lay : WsLay) (w : Nat → Nat → F) (cls : List WsClaim) (rho : Array E) :
    (mergeJobOf lay w cls rho).cube.fits = true := by
  refine fits_of _ ?_ ?_ ?_ ?_ ?_
  · show (OnBytes.Model.orderDefault lay.lk).length = lay.lk
    simp [OnBytes.Model.orderDefault]
  · intro v hv
    show v ∈ OnBytes.Model.orderDefault lay.lk
    simpa [OnBytes.Model.orderDefault] using hv
  · intro t ht
    have ht' : t ∈ (cls.foldl (fun a c => (a.push (colTab lay c)).push (rowTab lay w c))
        #[]).toList := ht
    rw [mergeMaps_toList] at ht'
    show t.size = 2 ^ lay.lk
    simp only [List.mem_append, List.mem_flatMap, List.mem_cons] at ht'
    rcases ht' with h0 | ⟨c, _, h1 | h1 | h1⟩
    · simp at h0
    · rw [h1, colTab_size]
    · rw [h1, rowTab_size]
    · simp at h1
  · intro x hx
    have h := mergePairs_lt rho cls 0 x hx
    have hs : (mergeJobOf lay w cls rho).cube.maps.size = 0 + 2 * cls.length :=
      mergeMaps_size lay w cls #[]
    rw [hs]
    constructor <;> omega
  · intro r hr
    cases hr

/-- The job has the public shape of a plain sumcheck of lk variables with one end value, of degree
1 in the further variable. -/
theorem mergeJob_jobFits (lay : WsLay) (w : Nat → Nat → F) (cls : List WsClaim) (rho : Array E) :
    k4JobFits (k4PlainShape lay.lk 1 1) (mergeJobOf lay w cls rho) = true := by
  unfold k4JobFits
  rw [mergeJob_fits]
  simp [k4PlainShape, mergeJobOf, VerifiableInference.Desc.Part.MaskedSum.Var.d]

/-- The row's seventh call has that shape. -/
theorem k4Shapes_merge (Q : K4Pub) :
    (k4Shapes Q).getD 6 ⟨0, [], none⟩ = k4PlainShape Q.P.wsLay.lk 1 1 := rfl

/-! ## 2 The chain -/

/-- **The merge's polynomials sum, round by round, from the cube's total to the summand at the
challenges, masked.** r: the challenges of the lk column bits, then Y's. m: the one mask entry. -/
theorem mergeJob_sumsTo {W X : Type} (job : W → Front X → Option Job) (w₀ : W) (fr : Front X)
    (lay : WsLay) (w : Nat → Nat → F) (cls : List WsClaim) (rho : Array E)
    (hj : job w₀ fr = some (mergeJobOf lay w cls rho)) (m r : List E) (hm : m.length = 1)
    (hr : r.length = lay.lk + 1) :
    SumsTo Reading.gl ((k4SumJob (k4PlainShape lay.lk 1 1) job).callAt w₀ fr).all
      (jobPoly (k4SumJob (k4PlainShape lay.lk 1 1) job) w₀ fr m) [] r
      (Reading.gl.val (mergeJobOf lay w cls rho).cube.total)
      (Reading.gl.val ((mergeJobOf lay w cls rho).cube.summandAt (r.take lay.lk)) +
        Reading.gl.val (r.getD lay.lk zeroE) * Reading.gl.val (m.headD zeroE)) := by
  have key := k4_sumsTo (k4PlainShape lay.lk 1 1) job w₀ fr (mergeJobOf lay w cls rho) hj
    (mergeJob_jobFits lay w cls rho) (by show 1 + 1 < 2 ^ 32; norm_num) m r hr (by rw [hm]; rfl)
    (PolyOn.head _ m) ReadsAlike.head rfl
  obtain ⟨m0, rfl⟩ : ∃ m0, m = [m0] := List.length_eq_one_iff.mp hm
  have e : Reading.gl.val ((mergeJobOf lay w cls rho).atEnds
      (r.take (mergeJobOf lay w cls rho).cube.n)
      (maskedEnds ((mergeJobOf lay w cls rho).ends (r.take (mergeJobOf lay w cls rho).cube.n)) [m0]
        (r.getD (mergeJobOf lay w cls rho).cube.n zeroE))) =
      Reading.gl.val ((mergeJobOf lay w cls rho).cube.summandAt (r.take lay.lk)) +
        Reading.gl.val (r.getD lay.lk zeroE) * Reading.gl.val ([m0].headD zeroE) := by
    show Reading.gl.val (OnBytes.addE ((mergeJobOf lay w cls rho).cube.summandAt (r.take lay.lk))
      (OnBytes.mulE (r.getD lay.lk zeroE) m0)) = _
    rw [Reading.gl.add, Reading.gl.mul]
    rfl
  rw [e] at key
  exact key

/-- **The same at the job that the part of the row's seventh call has by reading** (`k4Sum` of
`jobMerge`; no statement here names the row), where the list of claims is made. -/
theorem merge_sumsTo (Q : K4Pub) (w : K4In) (fr : Front Unit) (cls : List WsClaim)
    (hc : mergeClaimsAt Q w (ptsOf Q w fr.heard) = some cls) (m r : List E) (hm : m.length = 1)
    (hr : r.length = Q.P.wsLay.lk + 1) :
    SumsTo Reading.gl
      ((k4SumJob (k4PlainShape Q.P.wsLay.lk 1 1) fun w fr =>
        jobMerge Q w (ptsOf Q w fr.heard)).callAt w fr).all
      (jobPoly (k4SumJob (k4PlainShape Q.P.wsLay.lk 1 1) fun w fr =>
        jobMerge Q w (ptsOf Q w fr.heard)) w fr m) [] r
      (Reading.gl.val (mergeJobOf Q.P.wsLay w.w cls (ptsOf Q w fr.heard).rhoW).cube.total)
      (Reading.gl.val ((mergeJobOf Q.P.wsLay w.w cls (ptsOf Q w fr.heard).rhoW).cube.summandAt
          (r.take Q.P.wsLay.lk)) +
        Reading.gl.val (r.getD Q.P.wsLay.lk zeroE) * Reading.gl.val (m.headD zeroE)) :=
  mergeJob_sumsTo (fun w fr => jobMerge Q w (ptsOf Q w fr.heard)) w fr Q.P.wsLay w.w cls
    (ptsOf Q w fr.heard).rhoW
    (by show (mergeClaimsAt Q w (ptsOf Q w fr.heard)).map _ = _; rw [hc]; rfl) m r hm hr

end ProofFile.Honest.K4

#print axioms ProofFile.Honest.K4.colTab_size
#print axioms ProofFile.Honest.K4.rowTab_size
#print axioms ProofFile.Honest.K4.mergeMaps_toList
#print axioms ProofFile.Honest.K4.mergeMaps_size
#print axioms ProofFile.Honest.K4.mergePairs_lt
#print axioms ProofFile.Honest.K4.mergeJob_fits
#print axioms ProofFile.Honest.K4.mergeJob_jobFits
#print axioms ProofFile.Honest.K4.k4Shapes_merge
#print axioms ProofFile.Honest.K4.mergeJob_sumsTo
#print axioms ProofFile.Honest.K4.merge_sumsTo
