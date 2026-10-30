-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/JobsSpecSums.lean: the honest side of the kind "lookup" (K3): from
the specification's statement on a summand's run to the hypothesis that the statement on the masked
sumcheck asks of a caller, across the two sorts of elements. Definitions of propositions, and
theorems.

Terms. Honest/K3/GLOSSARY.md ("specification", "job, summand", "lawful", "program's elements",
"library's field"). In this file: two files say "round by round the summand's polynomials sum from c
to c'". Johnson/HonestTrace/LookDefs.lean says it over a field, on lists of the field's elements:
`Chained`; its `Job.Lawful` says it of a job, through all variables and on through the
further variable Y. Honest/SumLaw/Terms.lean says it of a caller's functions on the program's
elements, read in a ring: `SumsTo`. This file carries the first to the second for a job that is
carried to the program's elements as Honest/K3/JobsSpec.lean carries it.

What is defined and shown.
  1 `up_valueAt`, `up_sumOf`, `evalP_zeros`, `wsum_zeros`, `ups_padTo`: the program's value and sum
    of a polynomial, read, are the specification's; zeros behind change neither.
  2 `ReadsAs`, `sumsTo_of_chained`, `ReadsAs.append`, `reads_of`: the core: where the variables'
    points and the polynomials read as the specification's, a chained run gives `SumsTo`.
  3 `JobSized`, `polyOf`, `VarsFit`, `reads_job`: a job's polynomials, carried, read as the job's.
  4 `sums_ends`, `sums_open`: conditional on `Job.Lawful` and `JobSized`: a carried job with end
    values sums from its true sum to its summand at the shown values; one without, to its summand at
    the point.
Helpers that stand in no line above: `evalGo_cons_shift`, `evalP_cons`, `up_total`, `high_sum`.

Hypotheses that remain, in `sums_open` and `sums_ends`.
  `hJ`: `J.Lawful`. `hS`: `JobSized J`. `hv`: `VarsFit vs J`: the caller's variables are the job's.
  `hr`: there are as many challenges as variables.
  `hY`, `hm`: (in `sums_ends`) the job has a degree in Y; there are as many mask entries as end
    values.
  `reads_job` takes `hS`, `hv` and `hr`. `h`: (in `ups_padTo`) the list is no longer than n.

Imported. Honest/SumLaw/Terms.lean.

Users. `sums_ends` and `sums_open` are called in Honest/K3/JobsSpecStages.lean and
Honest/K3/Law/SpecStage.lean.

Limits. Every theorem of section 4 is conditional on `Job.Lawful`, which is for another file to
show. Nothing is said here of any particular job, of what the true sum is, or of the verifier's
forms. Shown in: Honest/K3/JobsSpecStages.lean (the five jobs) and Honest/K3/Law/SpecValues.lean
(what the true sums, end values and summands come to in the verifier's terms).
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.JobsSpecPoints
import Johnson.Desc.ProofFile.Honest.SumLaw.Terms
import Johnson.HonestTrace.LookSum

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3
open OnBytes (E zeroE oneE addE mulE)
open OnBytes.Slice (readE readE_add readE_mul readE_zero readE_one)
open OnBytes.HonestTrace.Look (Job Chained evalP wsum shownL)
open ProofFile.Honest.SumLaw (SumsTo)
open VerifiableInference.Desc.Part.MaskedSum (Var valueAt total)

/-- The reading in the library's extension field. -/
abbrev gl : OnBytes.Model.Reading KE := OnBytes.Model.Reading.gl

/-! ## 1 Value and sum of a polynomial -/

/-- Horner's value, over the field. -/
theorem evalGo_cons_shift (x : KE) : ∀ (t : Nat) (q : List KE),
    TwV.evalGo x (t + 1) q = x * TwV.evalGo x t q
  | _, [] => by simp [TwV.evalGo]
  | t, c :: q => by
    simp only [TwV.evalGo]
    rw [evalGo_cons_shift x (t + 1) q]
    ring

/-- The specification's value of c :: q at x is c + x times its value of q. -/
theorem evalP_cons (c : KE) (q : List KE) (x : KE) : evalP (c :: q) x = c + x * evalP q x := by
  cases q with
  | nil => simp [evalP, TwV.evalGo]
  | cons d q =>
    simp only [evalP, List.headD_cons, List.tail_cons, TwV.evalGo]
    rw [evalGo_cons_shift]
    ring

/-- **The program's value of a polynomial, read, is the specification's.** -/
theorem up_valueAt (x : E) : ∀ g : List E, up (valueAt g x) = evalP (ups g) (up x)
  | [] => by
    show readE zeroE = _
    rw [readE_zero]
    simp [ups, evalP, TwV.evalGo]
  | c :: g => by
    have ih := up_valueAt x g
    show readE (addE (mulE (valueAt g x) x) c) = _
    rw [readE_add, readE_mul]
    show up (valueAt g x) * up x + up c = evalP (up c :: ups g) (up x)
    rw [ih, evalP_cons]
    ring

/-- The program's total of a list, read, is the sum of the readings. -/
theorem up_total (l : List E) : up (total l) = (ups l).sum := by
  have h : ∀ (l : List E) (a : E), up (l.foldl addE a) = up a + (ups l).sum := by
    intro l
    induction l with
    | nil => intro a; simp [ups]
    | cons c l ih =>
      intro a
      rw [List.foldl_cons, ih]
      show readE (addE a c) + _ = _
      rw [readE_add]
      simp only [ups, List.map_cons, List.sum_cons]
      exact add_assoc _ _ _
  have := h l zeroE
  rw [show up zeroE = 0 from readE_zero, zero_add] at this
  exact this

/-- From the linear coefficient on, each coefficient counts the point's coordinate times. -/
theorem high_sum (z : E) (d : Nat) : ∀ (g : List E) (k : Nat),
    ups ((g.zipIdx (k + 1)).map fun x => mulE x.1 (sumPow (.point z d) x.2)) =
      (ups g).map (· * up z)
  | [], _ => rfl
  | c :: g, k => by
    rw [List.zipIdx_cons, List.map_cons]
    show up (mulE c z) :: ups _ = (up c * up z) :: (ups g).map (· * up z)
    rw [high_sum z d g (k + 1), show up (mulE c z) = up c * up z from readE_mul c z]

/-- **The program's sum of a polynomial in a variable that is summed at a point, read, is the
specification's.** -/
theorem up_sumOf (z : E) (d : Nat) (g : List E) :
    up (sumOf (.point z d) g) = wsum (up z) (ups g) := by
  cases g with
  | nil =>
    show readE zeroE = _
    rw [readE_zero]
    simp [ups, wsum]
  | cons c g =>
    unfold sumOf
    rw [up_total, List.zipIdx_cons, List.map_cons]
    show (up (mulE c oneE) :: ups _).sum = _
    rw [high_sum z d g 0, List.sum_cons]
    show readE (mulE c oneE) + _ = _
    rw [readE_mul, readE_one, mul_one, List.sum_map_mul_right]
    simp only [wsum, ups, List.map_cons, List.headD_cons, List.tail_cons]
    rw [mul_comm, List.map_id']

/-- Zeros behind a polynomial change no value. -/
theorem evalP_zeros (x : KE) (n : Nat) : ∀ q : List KE,
    evalP (q ++ List.replicate n 0) x = evalP q x
  | [] => by
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [List.nil_append] at ih ⊢
      rw [List.replicate_succ, evalP_cons, ih]
      simp [evalP, TwV.evalGo]
  | c :: q => by
    rw [List.cons_append, evalP_cons, evalP_cons, evalP_zeros x n q]

/-- Zeros behind a polynomial change no sum. -/
theorem wsum_zeros (z : KE) (n : Nat) (q : List KE) :
    wsum z (q ++ List.replicate n 0) = wsum z q := by
  cases q with
  | nil =>
    cases n with
    | zero => rfl
    | succ n => simp [wsum, List.replicate_succ]
  | cons c q => simp [wsum]

/-- A list that is not too long is padded with zeros. -/
theorem ups_padTo (n : Nat) (a : List E) (h : a.length ≤ n) :
    ups (padTo n a) = ups a ++ List.replicate (n - a.length) 0 := by
  unfold padTo
  rw [List.take_of_length_le (by simp; omega)]
  unfold ups
  rw [List.map_append, List.map_replicate]
  show _ ++ List.replicate _ (readE zeroE) = _
  rw [readE_zero]

/-! ## 2 The core -/

/-- **The caller's variables and polynomials read as the specification's**: each variable is summed
at a point that reads as the specification's; the polynomial behind the challenges so far reads as
the specification's, and is not longer than the variable's number of coefficients. -/
def ReadsAs : List Var → (List E → List E) → List E → List E → List KE → List (List KE) → Prop
  | [], _, _, [], [], [] => True
  | .point z d :: vs, poly, past, r :: rs, z' :: zs, q :: qs =>
    up z = z' ∧ ups (poly past) = q ∧ (poly past).length ≤ d ∧
      ReadsAs vs poly (past ++ [r]) rs zs qs
  | _, _, _, _, _, _ => False

/-- **The core.** Where the caller's variables and polynomials read as the specification's, a
chained run from c to c' gives the statement on the masked sumcheck its hypothesis. -/
theorem sumsTo_of_chained : ∀ (vs : List Var) (poly : List E → List E) (past rs : List E)
    (zs : List KE) (qs : List (List KE)) (c c' : KE),
    ReadsAs vs poly past rs zs qs → Chained c zs qs (ups rs) c' → SumsTo gl vs poly past rs c c'
  | [], _, _, [], [], [], _, _, _, h => (show _ = _ from h).symm
  | .point z d :: vs, poly, past, r :: rs, z' :: zs, q :: qs, c, c', hR, hC => by
    obtain ⟨hz, hq, hl, hR'⟩ := hR
    have hC' : wsum z' q = c ∧ Chained (evalP q (up r)) zs qs (ups rs) c' := hC
    refine ⟨?_, ?_⟩
    · show up (sumOf (.point z d) (padTo d (poly past))) = c
      rw [up_sumOf, ups_padTo d _ hl, wsum_zeros, hq, hz]
      exact hC'.1
    · have e : gl.val (valueAt (padTo (Var.point z d).d (poly past)) r) = evalP q (up r) := by
        show up (valueAt (padTo d (poly past)) r) = _
        rw [up_valueAt, ups_padTo d _ hl, evalP_zeros, hq]
      rw [e]
      exact sumsTo_of_chained vs poly (past ++ [r]) rs zs qs _ c' hR' hC'.2
  | [], _, _, [], [], _ :: _, _, _, h, _ => h.elim
  | [], _, _, [], _ :: _, _, _, _, h, _ => h.elim
  | [], _, _, _ :: _, _, _, _, _, h, _ => h.elim
  | .plain _ :: _, _, _, _, _, _, _, _, h, _ => h.elim
  | .point _ _ :: _, _, _, [], _, _, _, _, h, _ => h.elim
  | .point _ _ :: _, _, _, _ :: _, [], _, _, _, h, _ => h.elim
  | .point _ _ :: _, _, _, _ :: _, _ :: _, [], _, _, h, _ => h.elim

/-- Two stretches of variables in a row. -/
theorem ReadsAs.append : ∀ (vs : List Var) (poly : List E → List E) (past rs : List E)
    (zs : List KE) (qs : List (List KE)) (vs' : List Var) (rs' : List E) (zs' : List KE)
    (qs' : List (List KE)),
    ReadsAs vs poly past rs zs qs → ReadsAs vs' poly (past ++ rs) rs' zs' qs' →
      ReadsAs (vs ++ vs') poly past (rs ++ rs') (zs ++ zs') (qs ++ qs')
  | [], _, past, [], [], [], _, _, _, _, _, h' => by
    rw [List.append_nil] at h'
    exact h'
  | .point z d :: vs, poly, past, r :: rs, z' :: zs, q :: qs, vs', rs', zs', qs', h, h' => by
    obtain ⟨hz, hq, hl, hR⟩ := h
    refine ⟨hz, hq, hl, ReadsAs.append vs poly (past ++ [r]) rs zs qs vs' rs' zs' qs' hR ?_⟩
    rw [List.append_assoc]
    exact h'
  | [], _, _, [], [], _ :: _, _, _, _, _, h, _ => h.elim
  | [], _, _, [], _ :: _, _, _, _, _, _, h, _ => h.elim
  | [], _, _, _ :: _, _, _, _, _, _, _, h, _ => h.elim
  | .plain _ :: _, _, _, _, _, _, _, _, _, _, h, _ => h.elim
  | .point _ _ :: _, _, _, [], _, _, _, _, _, _, h, _ => h.elim
  | .point _ _ :: _, _, _, _ :: _, [], _, _, _, _, _, h, _ => h.elim
  | .point _ _ :: _, _, _, _ :: _, _ :: _, [], _, _, _, _, h, _ => h.elim

/-- `ReadsAs`, member by member. -/
theorem reads_of : ∀ (vs : List Var) (poly : List E → List E) (past rs : List E) (zs : List KE)
    (qs : List (List KE)), rs.length = vs.length → zs.length = vs.length → qs.length = vs.length →
    (∀ i, i < vs.length → ∃ z d, vs[i]? = some (.point z d) ∧ zs[i]? = some (up z) ∧
      qs[i]? = some (ups (poly (past ++ rs.take i))) ∧ (poly (past ++ rs.take i)).length ≤ d) →
    ReadsAs vs poly past rs zs qs
  | [], _, _, [], [], [], _, _, _, _ => trivial
  | v :: vs, poly, past, r :: rs, z' :: zs, q :: qs, h1, h2, h3, h => by
    obtain ⟨z, d, e1, e2, e3, e4⟩ := h 0 (by simp)
    simp only [List.getElem?_cons_zero, Option.some.injEq, List.take_zero, List.append_nil]
      at e1 e2 e3 e4
    subst e1
    refine ⟨e2.symm, e3.symm, e4, reads_of vs poly (past ++ [r]) rs zs qs (by simpa using h1)
      (by simpa using h2) (by simpa using h3) fun i hi => ?_⟩
    obtain ⟨z, d, f1, f2, f3, f4⟩ := h (i + 1) (by simpa using hi)
    simp only [List.getElem?_cons_succ, List.take_succ_cons] at f1 f2 f3 f4
    refine ⟨z, d, f1, f2, ?_, ?_⟩
    · rw [List.append_assoc]; exact f3
    · rw [List.append_assoc]; exact f4
  | [], _, _, _ :: _, _, _, h, _, _, _ => by simp at h
  | [], _, _, [], _ :: _, _, _, h, _, _ => by simp at h
  | [], _, _, [], [], _ :: _, _, _, h, _ => by simp at h
  | _ :: _, _, _, [], _, _, h, _, _, _ => by simp at h
  | _ :: _, _, _, _ :: _, [], _, _, h, _, _ => by simp at h
  | _ :: _, _, _, _ :: _, _ :: _, [], _, _, h, _ => by simp at h

/-! ## 3 A job's polynomials, carried -/

/-- **A job's lists have the lengths that its degrees state.** -/
structure JobSized (J : Job KE) : Prop where
  dg : J.dg.length = J.zs.length
  round : ∀ rs : List KE, rs.length < J.zs.length → (J.round rs).length ≤ J.dg.getD rs.length 0 + 1
  inY : ∀ dY, J.dY = some dY → ∀ xs m : List KE, (J.inY xs m).length ≤ dY + 1

/-- **The summand's polynomial of the round behind the challenges rs**, of a job that is carried to
the program's elements: what `SumLaw.jobPoly` makes of the carried job (no lemma of this file says
so; at a course's stage: `poly_eq`, Honest/K3/Law/SpecStage.lean). Here m are the end values' mask
entries. -/
def polyOf (J : Job KE) (m rs : List E) : List E :=
  if rs.length < J.zs.length then downs (J.round (ups rs)) else downs (J.inY (ups rs) (ups m))

/-- **A caller's variables are the job's**: as many; each summed at a point that reads as the job's,
with one coefficient more than the job's degree. -/
def VarsFit (vs : List Var) (J : Job KE) : Prop :=
  vs.length = J.zs.length ∧
    ∀ i, i < vs.length → ∃ z, vs[i]? = some (.point z (J.dg.getD i 0 + 1)) ∧ J.zs[i]? = some (up z)

/-- The variables' rounds of a carried job read as the job's. -/
theorem reads_job (J : Job KE) (hS : JobSized J) (vs : List Var) (hv : VarsFit vs J)
    (m rs : List E) (hr : rs.length = J.zs.length) :
    ReadsAs vs (polyOf J m) [] rs J.zs (J.gs (ups rs)) := by
  refine reads_of vs _ [] rs J.zs _ (by rw [hr, hv.1]) hv.1.symm
    (by rw [OnBytes.HonestTrace.Look.Job.gs_length, hv.1]) fun i hi => ?_
  obtain ⟨z, e1, e2⟩ := hv.2 i hi
  have hi' : i < J.zs.length := by rw [← hv.1]; exact hi
  have hl : (rs.take i).length = i := by rw [List.length_take]; omega
  have ep : polyOf J m ([] ++ rs.take i) = downs (J.round (ups (rs.take i))) := by
    unfold polyOf
    rw [List.nil_append, hl, if_pos hi']
  refine ⟨z, _, e1, e2, ?_, ?_⟩
  · rw [ep, ups_downs]
    unfold OnBytes.HonestTrace.Look.Job.gs
    rw [List.getElem?_map, List.getElem?_range hi']
    simp [ups, List.map_take]
  · rw [ep]
    have hl' : (ups (rs.take i)).length = i := by
      unfold ups
      rw [List.length_map, hl]
    have := hS.round (ups (rs.take i)) (by rw [hl']; exact hi')
    rw [hl'] at this
    unfold downs
    rw [List.length_map]
    exact this

/-! ## 4 The hypothesis of the statement on the masked sumcheck, at a carried job -/

/-- **A carried job without end values** sums, round by round, from its true sum to its summand at
the point of the challenges. Conditional on `Job.Lawful`, `JobSized`, `VarsFit` and as many
challenges as variables. -/
theorem sums_open (J : Job KE) (hJ : J.Lawful) (hS : JobSized J) (vs : List Var)
    (hv : VarsFit vs J) (m rs : List E) (hr : rs.length = J.zs.length) :
    SumsTo gl vs (polyOf J m) [] rs J.sum (J.fin (ups rs)) :=
  sumsTo_of_chained vs _ [] rs J.zs _ _ _ (reads_job J hS vs hv m rs hr)
    (hJ.1 (ups rs) (by simp [ups, hr]))

/-- **A carried job with end values** sums, round by round and on through the further variable Y,
from its true sum to its summand at the shown values: each true end value plus the challenge of Y
times its mask entry. Conditional on `Job.Lawful`, `JobSized`, `VarsFit`, a degree in Y, as many
challenges as variables and as many mask entries as end values. -/
theorem sums_ends (J : Job KE) (hJ : J.Lawful) (hS : JobSized J) (dY : Nat) (hY : J.dY = some dY)
    (vs : List Var) (hv : VarsFit vs J) (m rs : List E) (beta : E) (hr : rs.length = J.zs.length)
    (hm : m.length = (J.ends (ups rs)).length) :
    SumsTo gl (vs ++ [.point zeroE (dY + 1)]) (polyOf J m) [] (rs ++ [beta]) J.sum
      (J.S0 (shownL (up beta) (J.ends (ups rs)) (ups m))) := by
  have hx : (ups rs).length = J.zs.length := by simp [ups, hr]
  obtain ⟨y1, y2⟩ := hJ.2 (by rw [hY]; rfl) (ups rs) (ups m) (up beta) hx (by simp [ups, hm])
  have ep : polyOf J m ([] ++ rs) = downs (J.inY (ups rs) (ups m)) := by
    unfold polyOf
    rw [List.nil_append, hr, if_neg (lt_irrefl _)]
  refine sumsTo_of_chained _ _ [] _ (J.zs ++ [0]) (J.gs (ups rs) ++ [J.inY (ups rs) (ups m)]) _ _
    (ReadsAs.append vs _ [] rs J.zs _ _ [beta] [0] _ (reads_job J hS vs hv m rs hr)
      ⟨readE_zero, by rw [ep, ups_downs], by
        rw [ep]
        simpa [downs] using hS.inY dY hY (ups rs) (ups m), trivial⟩) ?_
  have e : ups (rs ++ [beta]) = ups rs ++ [up beta] := by simp [ups]
  rw [e]
  exact Chained.append (hJ.1 (ups rs) hx) ⟨y1, y2.symm⟩

#print axioms ProofFile.Honest.K3.evalP_cons
#print axioms ProofFile.Honest.K3.up_valueAt
#print axioms ProofFile.Honest.K3.up_total
#print axioms ProofFile.Honest.K3.up_sumOf
#print axioms ProofFile.Honest.K3.evalP_zeros
#print axioms ProofFile.Honest.K3.wsum_zeros
#print axioms ProofFile.Honest.K3.ups_padTo
#print axioms ProofFile.Honest.K3.sumsTo_of_chained
#print axioms ProofFile.Honest.K3.ReadsAs.append
#print axioms ProofFile.Honest.K3.reads_of
#print axioms ProofFile.Honest.K3.reads_job
#print axioms ProofFile.Honest.K3.sums_open
#print axioms ProofFile.Honest.K3.sums_ends
#print axioms ProofFile.Honest.K3.evalGo_cons_shift
#print axioms ProofFile.Honest.K3.high_sum

end ProofFile.Honest.K3
