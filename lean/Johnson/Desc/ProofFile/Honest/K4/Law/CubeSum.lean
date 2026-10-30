-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K4/Law/CubeSum.lean: CONDITIONAL. Two definitions, and statements with
their proofs.

What is here. From the laws on a sum over a cube (Johnson/Desc/K4/Honest/Law/Cube.lean,
CubeInY.lean) to what the law of the masked sumcheck's honest part asks of a caller (`SumsTo`,
Honest/SumLaw/Terms.lean), for a caller's job that is made of a `Job` (`k4SumJobAt`, `k4SumJob`,
Honest/K4/CubeJob.lean).

Y is the further variable of a masked sumcheck, behind the cube's own: the last round's.

  `valK j m`   the partial sums in two pieces: of at most n challenges `partK`; of more, the job's
     `atEnds` on the end values masked with challenge number n, which is Y's
  `padTo_self`, `wp_plain`, `wp_point`, `sumOf_plain3`, `sumOf_point3`, `sumOf_atZero`,
  `take_succ_getD`   small tools on the part's lists
  `SumShape`, `jobFits_parts`   what the tie spends of the public test on a job
  `round_link`   one round of the cube, in the letters of `SumsTo`
  `k4_sumsTo_shape`   **the tie**, for `k4SumJobAt` where the points are the cube's
  `k4_sumsTo_at`   the same under the public test `k4JobFits`
  `k4_sumsTo_own`, `k4_sumsTo`   the two for `k4SumJob`, whose points are read off the job's cube

Limits. THREE FILES BESIDE THIS ONE THAT ARE NAMED BELOW ARE NO PART OF THE LIBRARY YET:
SumCall.lean, TermsLed.lean, FlatStack.lean. At the reading `Reading.gl` alone. NINE PREMISES, each
owed for each job anew, at the run's own input and challenges: THE JOB's MAKER RETURNS; the caller's
points are the cube's (`k4SumJob` reads them off the cube); the public test `k4JobFits`, or what is
spent of it (`SumShape`), AT THE JOB OF THE RUN (the row's own test asks it at the zero input and
zero challenges alone); the degree in Y, plus 1, is below 2 ^ 32; there is one challenge more than
the cube has variables; there are as many mask entries as end values; `PolyOn` and `ReadsAlike` of
the job's `atEnds`; and `atEnds` on the true end values reads as the cube's summand at the
challenges. Nothing HERE says where they hold: the chain is stated for five of the row's seven
sumchecks (SumLevels.lean, SumRows.lean, SumMerge.lean); at the second token sumcheck and the
batched sumcheck the tie is spent through SumCall.lean's `k4_rowForm_worth` (TermsLed.lean,
FlatStack.lean), with the premises on the job handed on. NEITHER END OF THE CHAIN IS TIED TO A
VERIFIER's FORM: it begins at the reading of `Cube.total` and ends at the reading of `atEnds` on
`maskedEnds`; that the first is the value of the form that a verifier claims, and that the second is
a verifier's summand on the values as they were sent, is not said here. Nor is `SumsTo` all that the
law asks of a caller whose verifier runs the flat text of the sumcheck. NOTHING ON THE JOB's LEAD:
that a lead reads as the cube's total is not said here. `SumShape` leaves out the test's clauses on
the lead's length and on the number of end values. `valK` stands in no statement: it is a term of
the tie's proof.

Kin. The part's way of summing, read term by term, is the frame's `sumOf_read`
(Honest/SumLaw/SumMapReads.lean), at every reading into a field: it is called here at `Reading.gl`.
Two of the small tools are in the library already, more generally, in other kinds' files on which
this one does not build: `take_succ_getD` under the same name at every type and default
(Honest/K5/Law/SumsTo.lean); `padTo_self` under the same name at every n with a.length = n
(Honest/K3/Law/SpecStage.lean). Three more have kin in other kinds' files, in other letters, on
which this one does not build: `sumOf_plain3` on a list written out, at every reading into a field
(`sumOf_reads`, Honest/K13/SumReads.lean); `sumOf_point3` likewise at this reading
(`head_sumOf_three`, Honest/K6/PairSumsTo.lean); `sumOf_atZero` as the value at 0, where the list
has the variable's number of coefficients (`sumOf_point0`, Honest/K5/Law/SumsTo.lean). Another kind
has partial sums in two pieces under the same name, for its own sum: `PairSum.valK`
(Johnson/Desc/K6/Honest/PairLaw.lean).

No property is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K4.Part
import Johnson.Desc.ProofFile.Honest.SumLaw.More
import Johnson.Desc.ProofFile.Honest.SumLaw.SumMapReads
import Johnson.Desc.K4.Honest.Law.Cube
import Johnson.Desc.K4.Honest.Law.CubeInY

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K4
open OnBytes (E zeroE)
open OnBytes.Model (Reading)
open OnBytes.Desc.First.K4.Honest (Job polyInY)
open OnBytes.Desc.First.K4.Honest.CubeLaw
open VerifiableInference.Desc.Part.MaskedSum (Call Var valueAt total_val)
open ProofFile.Honest.SumLaw (SumsTo jobPoly sumsTo_of_vals sumOf_read)

variable {W X : Type}

/-- The partial sums in two pieces. Of at most n challenges: the cube's partial sum. Of more: the
job's `atEnds` at the first n, on the end values masked with the challenge number n. m: the end
values' mask entries. -/
def valK (j : Job) (m l : List E) : Cb.Gl.E :=
  if l.length ≤ j.cube.n then partK Reading.gl j.cube l
  else Reading.gl.val (j.atEnds (l.take j.cube.n)
    (maskedEnds (j.ends (l.take j.cube.n)) m (l.getD j.cube.n zeroE)))

/-! ## Small tools -/

/-- A list cut or filled to its own length. -/
theorem padTo_self (l : List E) : padTo l.length l = l := by
  simp [padTo]

/-- Variables that are all summed plainly, each with three coefficients, take no point. -/
theorem wp_plain : ∀ (vs : List Var) (zs : List E), (∀ v ∈ vs, v = Var.plain 3) →
    ∀ i, i < vs.length → (withPoints vs zs).getD i (.plain 0) = .plain 3
  | [], _, _, i, hi => absurd hi (Nat.not_lt_zero _)
  | v :: vs, zs, h, i, hi => by
    have hv : v = Var.plain 3 := h v (by simp)
    subst hv
    rw [withPoints]
    cases i with
    | zero => rfl
    | succ i => exact wp_plain vs zs (fun u hu => h u (by simp [hu])) i (by simpa using hi)

/-- Variables that are all summed at a point, each with three coefficients, take the points in
order. -/
theorem wp_point : ∀ (vs : List Var) (zs : List E), (∀ v ∈ vs, ∃ z, v = Var.point z 3) →
    vs.length ≤ zs.length →
    ∀ i, i < vs.length → (withPoints vs zs).getD i (.plain 0) = .point (zs.getD i zeroE) 3
  | [], _, _, _, i, hi => absurd hi (Nat.not_lt_zero _)
  | _ :: _, [], _, hl, _, _ => by simp at hl
  | v :: vs, z :: zs, h, hl, i, hi => by
    obtain ⟨z', hv⟩ := h v (by simp)
    subst hv
    rw [withPoints]
    cases i with
    | zero => rfl
    | succ i =>
      exact wp_point vs zs (fun u hu => h u (by simp [hu])) (by simpa using hl) i
        (by simpa using hi)

/-- Three coefficients summed plainly: 2 g0 + g1 + g2. -/
theorem sumOf_plain3 (g : List E) (hg : g.length = 3) :
    Reading.gl.val (sumOf (.plain 3) g) = 2 * Reading.gl.val (g.getD 0 zeroE) +
      Reading.gl.val (g.getD 1 zeroE) + Reading.gl.val (g.getD 2 zeroE) := by
  rw [sumOf_read Reading.gl, hg, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_succ, Finset.sum_range_zero]
  show 0 + 2 * _ + 1 * _ + 1 * _ = _
  ring

/-- Three coefficients summed at z: g0 + z (g1 + g2). -/
theorem sumOf_point3 (z : E) (g : List E) (hg : g.length = 3) :
    Reading.gl.val (sumOf (.point z 3) g) = Reading.gl.val (g.getD 0 zeroE) +
      Reading.gl.val z * (Reading.gl.val (g.getD 1 zeroE) + Reading.gl.val (g.getD 2 zeroE)) := by
  rw [sumOf_read Reading.gl, hg, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_succ, Finset.sum_range_zero]
  show 0 + 1 * _ + Reading.gl.val z * _ + Reading.gl.val z * _ = _
  ring

/-- Summed at 0 a polynomial gives its constant coefficient. -/
theorem sumOf_atZero (d : ℕ) (g : List E) (hg : 0 < g.length) :
    Reading.gl.val (sumOf (.point zeroE d) g) = Reading.gl.val (g.getD 0 zeroE) := by
  rw [sumOf_read Reading.gl, Finset.sum_eq_single 0]
  · show 1 * _ = _
    rw [one_mul]
  · intro b _ hb
    show (if b = 0 then 1 else Reading.gl.val zeroE) * _ = 0
    rw [if_neg hb, Reading.gl.zero, zero_mul]
  · intro h
    exact absurd (Finset.mem_range.mpr hg) h

/-- One challenge more. -/
theorem take_succ_getD (r : List E) (i : ℕ) (h : i < r.length) :
    r.take (i + 1) = r.take i ++ [r.getD i zeroE] := by
  rw [List.take_add_one, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]
  rfl

/-- **What the tie spends of the public test on a job**: the cube's sizes fit; the cube has the
call's number of variables; the call has ends, of the job's degree in the further variable; the
call's variables are summed in the cube's way, each with three coefficients. -/
def SumShape (sh : Call) (j : Job) : Prop :=
  j.cube.fits = true ∧ j.cube.n = sh.vs.length ∧ (∃ e, sh.ends = some e ∧ j.dY = e.dY) ∧
    ((j.cube.way = .plain ∧ ∀ v ∈ sh.vs, v = Var.plain 3) ∨
      ((∃ rho, j.cube.way = .point rho) ∧ ∀ v ∈ sh.vs, ∃ z, v = Var.point z 3))

/-- The public test on a job gives it. -/
theorem jobFits_parts {sh : Call} {j : Job} (h : k4JobFits sh j = true) : SumShape sh j := by
  unfold SumShape
  simp only [k4JobFits, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, _⟩, h4⟩, h5⟩, h6⟩ := h
  have h2' : j.cube.n = sh.vs.length := by simpa using h2
  have h4' : ∀ v ∈ sh.vs, v.d = 3 := by simpa using h4
  refine ⟨h1, h2', ?_, ?_⟩
  · cases he : sh.ends with
    | none =>
      rw [he] at h6
      simp at h6
    | some e =>
      rw [he] at h6
      simp only [Bool.and_eq_true, beq_iff_eq] at h6
      exact ⟨e, rfl, h6.1⟩
  · cases hw : j.cube.way with
    | plain =>
      rw [hw] at h5
      refine Or.inl ⟨rfl, fun v hv => ?_⟩
      have a := List.all_eq_true.mp h5 v hv
      have b := h4' v hv
      cases v with
      | plain d =>
        have : d = 3 := b
        rw [this]
      | point z d => simp at a
    | point rho =>
      rw [hw] at h5
      refine Or.inr ⟨⟨rho, rfl⟩, fun v hv => ?_⟩
      have a := List.all_eq_true.mp h5 v hv
      have b := h4' v hv
      cases v with
      | plain d => simp at a
      | point z d =>
        have : d = 3 := b
        rw [this]
        exact ⟨z, rfl⟩

/-- One round of the cube, in the letters of `SumsTo`. -/
theorem round_link {sh : Call} {j : Job} (h : SumShape sh j) (l : List E)
    (hl : l.length < j.cube.n) :
    Reading.gl.val (sumOf ((withPoints sh.vs j.cube.points).getD l.length (.plain 0))
      (padTo ((withPoints sh.vs j.cube.points).getD l.length (.plain 0)).d (j.cube.round l))) =
        partK Reading.gl j.cube l ∧
    ∀ x, Reading.gl.val (valueAt
      (padTo ((withPoints sh.vs j.cube.points).getD l.length (.plain 0)).d (j.cube.round l)) x) =
        partK Reading.gl j.cube (l ++ [x]) := by
  obtain ⟨hf, hn, _, hway⟩ := h
  have h3 := round_length j.cube hf l hl
  have hpad : padTo 3 (j.cube.round l) = j.cube.round l := by
    have := padTo_self (j.cube.round l)
    rwa [h3] at this
  rcases hway with ⟨hw, hv⟩ | ⟨⟨rho, hw⟩, hv⟩
  · rw [wp_plain sh.vs j.cube.points hv l.length (by omega)]
    show Reading.gl.val (sumOf (.plain 3) (padTo 3 (j.cube.round l))) = _ ∧
      ∀ x, Reading.gl.val (valueAt (padTo 3 (j.cube.round l)) x) = _
    rw [hpad, sumOf_plain3 _ h3]
    exact ⟨round_sum_plain Reading.gl j.cube hf hw l hl,
      fun x => part_next Reading.gl j.cube hf l x hl⟩
  · have hpl : sh.vs.length ≤ j.cube.points.length := by
      simp [OnBytes.Desc.First.K4.Honest.Cube.points, hw, (fitsP j.cube hf).len, hn]
    rw [wp_point sh.vs j.cube.points hv hpl l.length (by omega)]
    show Reading.gl.val (sumOf (.point (j.cube.points.getD l.length zeroE) 3)
        (padTo 3 (j.cube.round l))) = _ ∧
      ∀ x, Reading.gl.val (valueAt (padTo 3 (j.cube.round l)) x) = _
    rw [hpad, sumOf_point3 _ _ h3]
    exact ⟨round_sum_point Reading.gl j.cube hf rho hw l hl,
      fun x => part_next Reading.gl j.cube hf l x hl⟩

/-- **Round by round the job's polynomials sum from the cube's total to `atEnds` on the masked end
values.** r: the challenges of the cube's n variables, then Y's. -/
theorem k4_sumsTo_shape (sh : Call) (points : W → Front X → List E)
    (job : W → Front X → Option Job) (w : W) (fr : Front X) (j : Job) (hj : job w fr = some j)
    (hp : points w fr = j.cube.points) (hfit : SumShape sh j) (hd : j.dY + 1 < 2 ^ 32)
    (m r : List E)
    (hr : r.length = j.cube.n + 1) (hm : (j.ends (r.take j.cube.n)).length = m.length)
    (hP : PolyOn j.dY fun y =>
      j.atEnds (r.take j.cube.n) (maskedEnds (j.ends (r.take j.cube.n)) m y))
    (hA : ReadsAlike (j.atEnds (r.take j.cube.n)))
    (hE : Reading.gl.val (j.atEnds (r.take j.cube.n) (j.ends (r.take j.cube.n))) =
      Reading.gl.val (j.cube.summandAt (r.take j.cube.n))) :
    SumsTo Reading.gl ((k4SumJobAt sh points job).callAt w fr).all
      (jobPoly (k4SumJobAt sh points job) w fr m) [] r (Reading.gl.val j.cube.total)
      (Reading.gl.val (j.atEnds (r.take j.cube.n)
        (maskedEnds (j.ends (r.take j.cube.n)) m (r.getD j.cube.n zeroE)))) := by
  obtain ⟨hf, hn, ⟨e, he, hdY⟩, _⟩ := id hfit
  have hall : ((k4SumJobAt sh points job).callAt w fr).all =
      withPoints sh.vs j.cube.points ++ [.point zeroE (j.dY + 1)] := by
    have e0 : ((k4SumJobAt sh points job).callAt w fr).all =
        (match sh.ends with
         | none => withPoints sh.vs (points w fr)
         | some e => withPoints sh.vs (points w fr) ++ [.point zeroE (e.dY + 1)]) := rfl
    rw [e0, he, hp, hdY]
  have hwl : (withPoints sh.vs j.cube.points).length = j.cube.n := by
    rw [ProofFile.Honest.SumLaw.withPoints_length, hn]
  have hpoly1 : ∀ l : List E, l.length < j.cube.n →
      jobPoly (k4SumJobAt sh points job) w fr m l = j.cube.round l := by
    intro l hl
    show (if l.length < sh.vs.length then ((job w fr).map (·.cube.round l)).getD [] else _) = _
    rw [if_pos (by omega), hj]
    rfl
  have hpoly2 : ∀ l : List E, l.length = j.cube.n →
      jobPoly (k4SumJobAt sh points job) w fr m l = polyInY j.dY (j.atEnds l) (j.ends l) m := by
    intro l hl
    show (if l.length < sh.vs.length then _
      else ((job w fr).map fun j => polyInY j.dY (j.atEnds l) (j.ends l) m).getD []) = _
    rw [if_neg (by omega), hj]
    rfl
  have key := sumsTo_of_vals Reading.gl (jobPoly (k4SumJobAt sh points job) w fr m) (valK j m)
    (withPoints sh.vs j.cube.points ++ [.point zeroE (j.dY + 1)]) [] r
    (by rw [List.length_append, hwl, hr]; rfl) (by
      intro i hi
      rw [List.length_append, hwl, List.length_singleton] at hi
      rw [List.nil_append, List.nil_append]
      rcases Nat.lt_or_ge i j.cube.n with hin | hin
      · have hlen : (r.take i).length = i := by
          rw [List.length_take]
          omega
        obtain ⟨k1, k2⟩ := round_link hfit (r.take i) (by omega)
        rw [hlen] at k1 k2
        rw [List.getD_append _ _ _ _ (by omega), hpoly1 _ (by omega), k1, k2,
          take_succ_getD r i (by omega)]
        constructor
        · unfold valK
          rw [if_pos (by omega)]
        · unfold valK
          rw [if_pos (by rw [List.length_append, hlen, List.length_singleton]; omega)]
      · obtain rfl : i = j.cube.n := by omega
        have hlen : (r.take j.cube.n).length = j.cube.n := by
          rw [List.length_take]
          omega
        have hg := polyInY_length j.dY (j.atEnds (r.take j.cube.n)) (j.ends (r.take j.cube.n)) m hm
        have hpad := padTo_self
          (polyInY j.dY (j.atEnds (r.take j.cube.n)) (j.ends (r.take j.cube.n)) m)
        rw [hg] at hpad
        rw [List.getD_append_right _ _ _ _ (by omega), hwl, Nat.sub_self, hpoly2 _ hlen]
        show Reading.gl.val (sumOf (.point zeroE (j.dY + 1)) (padTo (j.dY + 1) _)) = _ ∧
          Reading.gl.val (valueAt (padTo (j.dY + 1) _) _) = _
        rw [hpad]
        constructor
        · rw [sumOf_atZero _ _ (by omega), polyInY_const' j.dY hd _ _ m hm hP hA, hE,
            ← part_last Reading.gl j.cube hf _ hlen]
          unfold valK
          rw [if_pos (by omega)]
        · have hv := polyInY_value j.dY hd _ _ m hm hP (r.getD j.cube.n zeroE)
          rw [List.take_of_length_le (show r.length ≤ j.cube.n + 1 by omega)]
          unfold valK
          rw [if_neg (by omega)]
          exact hv)
  have v0 : valK j m [] = Reading.gl.val j.cube.total := by
    unfold valK
    rw [if_pos (show ([] : List E).length ≤ j.cube.n from Nat.zero_le _)]
    exact part_nil Reading.gl j.cube
  have v1 : valK j m ([] ++ r) = Reading.gl.val (j.atEnds (r.take j.cube.n)
      (maskedEnds (j.ends (r.take j.cube.n)) m (r.getD j.cube.n zeroE))) := by
    rw [List.nil_append]
    unfold valK
    rw [if_neg (by omega)]
  rw [v0, v1] at key
  rw [hall]
  exact key

/-- The same under the public test on a job. -/
theorem k4_sumsTo_at (sh : Call) (points : W → Front X → List E) (job : W → Front X → Option Job)
    (w : W) (fr : Front X) (j : Job) (hj : job w fr = some j) (hp : points w fr = j.cube.points)
    (hfit : k4JobFits sh j = true) (hd : j.dY + 1 < 2 ^ 32) (m r : List E)
    (hr : r.length = j.cube.n + 1) (hm : (j.ends (r.take j.cube.n)).length = m.length)
    (hP : PolyOn j.dY fun y =>
      j.atEnds (r.take j.cube.n) (maskedEnds (j.ends (r.take j.cube.n)) m y))
    (hA : ReadsAlike (j.atEnds (r.take j.cube.n)))
    (hE : Reading.gl.val (j.atEnds (r.take j.cube.n) (j.ends (r.take j.cube.n))) =
      Reading.gl.val (j.cube.summandAt (r.take j.cube.n))) :
    SumsTo Reading.gl ((k4SumJobAt sh points job).callAt w fr).all
      (jobPoly (k4SumJobAt sh points job) w fr m) [] r (Reading.gl.val j.cube.total)
      (Reading.gl.val (j.atEnds (r.take j.cube.n)
        (maskedEnds (j.ends (r.take j.cube.n)) m (r.getD j.cube.n zeroE)))) :=
  k4_sumsTo_shape sh points job w fr j hj hp (jobFits_parts hfit) hd m r hr hm hP hA hE

/-- The tie where the points are read off the job's own cube, under `SumShape`. -/
theorem k4_sumsTo_own (sh : Call) (job : W → Front X → Option Job) (w : W) (fr : Front X) (j : Job)
    (hj : job w fr = some j) (hfit : SumShape sh j) (hd : j.dY + 1 < 2 ^ 32)
    (m r : List E) (hr : r.length = j.cube.n + 1)
    (hm : (j.ends (r.take j.cube.n)).length = m.length)
    (hP : PolyOn j.dY fun y =>
      j.atEnds (r.take j.cube.n) (maskedEnds (j.ends (r.take j.cube.n)) m y))
    (hA : ReadsAlike (j.atEnds (r.take j.cube.n)))
    (hE : Reading.gl.val (j.atEnds (r.take j.cube.n) (j.ends (r.take j.cube.n))) =
      Reading.gl.val (j.cube.summandAt (r.take j.cube.n))) :
    SumsTo Reading.gl ((k4SumJob sh job).callAt w fr).all (jobPoly (k4SumJob sh job) w fr m) [] r
      (Reading.gl.val j.cube.total)
      (Reading.gl.val (j.atEnds (r.take j.cube.n)
        (maskedEnds (j.ends (r.take j.cube.n)) m (r.getD j.cube.n zeroE)))) :=
  k4_sumsTo_shape sh (fun w fr => ((job w fr).map fun j : Job => j.cube.points).getD []) job w fr j
    hj (by show ((job w fr).map fun j : Job => j.cube.points).getD [] = _; rw [hj]; rfl)
    hfit hd m r hr hm hP hA hE

/-- The same where the points are read off the job's own cube. -/
theorem k4_sumsTo (sh : Call) (job : W → Front X → Option Job) (w : W) (fr : Front X) (j : Job)
    (hj : job w fr = some j) (hfit : k4JobFits sh j = true) (hd : j.dY + 1 < 2 ^ 32)
    (m r : List E) (hr : r.length = j.cube.n + 1)
    (hm : (j.ends (r.take j.cube.n)).length = m.length)
    (hP : PolyOn j.dY fun y =>
      j.atEnds (r.take j.cube.n) (maskedEnds (j.ends (r.take j.cube.n)) m y))
    (hA : ReadsAlike (j.atEnds (r.take j.cube.n)))
    (hE : Reading.gl.val (j.atEnds (r.take j.cube.n) (j.ends (r.take j.cube.n))) =
      Reading.gl.val (j.cube.summandAt (r.take j.cube.n))) :
    SumsTo Reading.gl ((k4SumJob sh job).callAt w fr).all (jobPoly (k4SumJob sh job) w fr m) [] r
      (Reading.gl.val j.cube.total)
      (Reading.gl.val (j.atEnds (r.take j.cube.n)
        (maskedEnds (j.ends (r.take j.cube.n)) m (r.getD j.cube.n zeroE)))) :=
  k4_sumsTo_own sh job w fr j hj (jobFits_parts hfit) hd m r hr hm hP hA hE

end ProofFile.Honest.K4

#print axioms ProofFile.Honest.K4.valK
#print axioms ProofFile.Honest.K4.padTo_self
#print axioms ProofFile.Honest.K4.wp_plain
#print axioms ProofFile.Honest.K4.wp_point
#print axioms ProofFile.Honest.K4.sumOf_plain3
#print axioms ProofFile.Honest.K4.sumOf_point3
#print axioms ProofFile.Honest.K4.sumOf_atZero
#print axioms ProofFile.Honest.K4.take_succ_getD
#print axioms ProofFile.Honest.K4.SumShape
#print axioms ProofFile.Honest.K4.jobFits_parts
#print axioms ProofFile.Honest.K4.round_link
#print axioms ProofFile.Honest.K4.k4_sumsTo_shape
#print axioms ProofFile.Honest.K4.k4_sumsTo_at
#print axioms ProofFile.Honest.K4.k4_sumsTo_own
#print axioms ProofFile.Honest.K4.k4_sumsTo
