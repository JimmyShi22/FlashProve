-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K4/Law/SumRows.lean: CONDITIONAL. One definition, and statements with
their proofs.

What is here. What the law of the masked sumcheck's honest part asks of a caller (`SumsTo`,
Honest/SumLaw/Terms.lean), at the sumcheck over the tokens on the norms' row products (`jobRows`,
Johnson/Desc/K4/Honest/Norms.lean).

  `foldAdd_read`, `sum_flatMap`   a loop of sums, read; a sum over lists laid end to end
  `summand_read`, `rowsSummand_read`   the verifier's summand on shown values, read
  `rowsJobOf`, `jobRows_eq`   the job, of its tables
  `rowsJob_shape`, `rowsJob_ends`, `summand_poly`, `rowsJob_poly`, `summand_alike`,
  `rowsJob_alike`   the tie's premises
  `k4Shapes_rows`   the row's second call has the shape that is used here
  `rows_sumsTo`   **the chain** at the row's own job

Limits. At the reading `Reading.gl` alone. THAT THE MAKER RETURNS A JOB IS A PREMISE (it returns one
only where the tables are made and the cube's sizes fit); so is that there are as many mask entries
as the job has end values, and one challenge more than a token's number has bits. THE PREMISE ON THE
MASK ENTRIES IS A LAW ON THE MAKER: the job has as many end values as it has tables. k, THE NUMBER
OF END VALUES THAT THE CALL STATES, IS TIED TO NOTHING HERE: `rows_sumsTo` and `rowsJob_shape` hold
at every k. At the part's own mask entries the premise asks that the job have as many end values as
the call states: `rows_ends_call` of SumRowsSize.lean beside this file (no part of the library yet),
at norms of five limbs. NEITHER END OF THE CHAIN IS TIED TO A VERIFIER's FORM HERE: it begins at the
reading of the cube's total, which is the job's lead, and ends at the verifier's summand on
`maskedEnds`, with the powers omV as the maker lays them; that the first is the value of the form
that the verifier claims (SumRowsStart.lean beside this file, no part of the library yet), and that
the second stands on the values as they were sent and on what the verifier has heard, is not said
here. Nothing on what the tables hold.

Kin. BOTH TOOLS OF SECTION 1 ARE IN THE LIBRARY ALREADY, MORE GENERALLY AND IN OTHER LETTERS, in
files on which this one does not build. `foldAdd_read`: under the same name at every reading into a
commutative ring (Johnson/Desc/K11/Honest/Law/Tables.lean, another kind's). `sum_flatMap`: under the
same name over any commutative ring, the two functions in the other order
(OnBytes/Tie/Pv/Tail/EndRows.lean), and over any additive commutative monoid
(OnBytes/Tie/Pv/Lookup/Digits/PortKeys.lean); once more at the natural numbers
(E2E/KeyBookThird.lean).

No property is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.CubeSum

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K4
open OnBytes (E F addE mulE zeroE oneE)
open OnBytes.Model (Reading orderDefault)
open OnBytes.Model.Layer (Lay Heard)
open OnBytes.Desc.First (P6.summand P6.rowProducts)
open OnBytes.Desc.First.K4 (rowsSummand)
open OnBytes.Desc.First.K4.Honest
open OnBytes.Desc.First.K4.Honest.CubeLaw
open VerifiableInference.Desc.Part.MaskedSum (Call Var)
open ProofFile.Honest.SumLaw (SumsTo jobPoly)

/-! ## 1 Sums -/

/-- A loop of sums, read. -/
theorem foldAdd_read {α : Type} (g : α → E) : ∀ (l : List α) (s : E),
    Reading.gl.val (l.foldl (fun t a => addE t (g a)) s) =
      Reading.gl.val s + (l.map fun a => Reading.gl.val (g a)).sum
  | [], s => by simp
  | a :: l, s => by
    rw [List.foldl_cons, foldAdd_read g l, Reading.gl.add, List.map_cons, List.sum_cons]
    ring

/-- A sum over lists laid end to end. -/
theorem sum_flatMap {α β : Type} (f : α → List β) (h : β → Cb.Gl.E) : ∀ l : List α,
    ((l.flatMap f).map h).sum = (l.map fun a => ((f a).map h).sum).sum
  | [] => rfl
  | a :: l => by
    rw [List.flatMap_cons, List.map_append, List.sum_append, sum_flatMap f h l, List.map_cons,
      List.sum_cons]

/-- The verifier's summand of one norm's row, read. -/
theorem summand_read (om : ℕ → E) (s : ℕ → E) :
    Reading.gl.val (P6.summand om s) =
      (P6.rowProducts.zipIdx.map fun x => Reading.gl.val (om x.2) *
        (Reading.gl.val (s x.1.1) * Reading.gl.val (s x.1.2))).sum := by
  unfold P6.summand
  rw [foldAdd_read (fun x : (ℕ × ℕ) × ℕ => mulE (mulE (om x.2) (s x.1.1)) (s x.1.2)),
    Reading.gl.zero, zero_add]
  refine congrArg List.sum (List.map_congr_left fun x _ => ?_)
  rw [Reading.gl.mul, Reading.gl.mul, mul_assoc]

/-- The verifier's summand of all norms' rows on shown values, read. -/
theorem rowsSummand_read (y : Lay) (H : Heard) (sh : Array E) :
    Reading.gl.val (rowsSummand y H sh) =
      ((List.range y.NI).map fun i => (P6.rowProducts.zipIdx.map fun x =>
        Reading.gl.val (H.omV.getD (7 * i + x.2) zeroE) *
          (Reading.gl.val (sh.getD (4 * i + x.1.1) zeroE) *
            Reading.gl.val (sh.getD (4 * i + x.1.2) zeroE))).sum).sum := by
  unfold rowsSummand
  rw [foldAdd_read (fun i => P6.summand (fun r => H.omV.getD (7 * i + r) zeroE)
    fun k => sh.getD (4 * i + k) zeroE), Reading.gl.zero, zero_add]
  exact congrArg List.sum (List.map_congr_left fun i _ => summand_read _ _)

/-! ## 2 The job -/

/-- The job, of its tables, without the maker's test on the cube's sizes. -/
def rowsJobOf (Q : K4Pub) (p : Pts) (ms : Array Tab) : Job :=
  let cube : Cube :=
    { n := Q.P.y.h.lt, order := orderDefault Q.P.y.h.lt, way := .point p.PV, maps := ms
      pairs := (List.range Q.P.y.NI).flatMap fun i =>
        P6.rowProducts.zipIdx.map fun x =>
          (p.omV.getD (7 * i + x.2) zeroE, 4 * i + x.1.1, 4 * i + x.1.2) }
  { lead := [cube.total], cube, dY := 2
    ends := fun rs => (cube.valuesAt rs).toList
    atEnds := fun _ e => rowsSummand Q.P.y (heardOf Q p) e.toArray }

/-- The maker, written with `rowsJobOf`. -/
theorem jobRows_eq (Q : K4Pub) (w : K4In) (p : Pts) :
    jobRows Q w p = (rowMaps Q w p).bind fun ms =>
      if (rowsJobOf Q p ms).cube.fits then some (rowsJobOf Q p ms) else none := rfl

/-- Where its cube fits the job has what the tie spends of a token sumcheck's shape. -/
theorem rowsJob_shape (Q : K4Pub) (p : Pts) (ms : Array Tab) (k : ℕ)
    (h : (rowsJobOf Q p ms).cube.fits = true) :
    SumShape (k4TokenShape Q.P.y.h.lt 2 k) (rowsJobOf Q p ms) := by
  refine ⟨h, ?_, ⟨⟨2, k⟩, rfl, rfl⟩, Or.inr ⟨⟨p.PV, rfl⟩, fun v hv => ?_⟩⟩
  · show Q.P.y.h.lt = (List.replicate Q.P.y.h.lt (Var.point zeroE 3)).length
    rw [List.length_replicate]
  · exact ⟨zeroE, List.eq_of_mem_replicate hv⟩

/-- **On the true end values the verifier's summand reads as the cube's summand.** -/
theorem rowsJob_ends (Q : K4Pub) (p : Pts) (ms : Array Tab) (rs : List E) :
    Reading.gl.val ((rowsJobOf Q p ms).atEnds rs ((rowsJobOf Q p ms).ends rs)) =
      Reading.gl.val ((rowsJobOf Q p ms).cube.summandAt rs) := by
  show Reading.gl.val (rowsSummand Q.P.y (heardOf Q p)
    ((rowsJobOf Q p ms).cube.valuesAt rs).toList.toArray) = _
  rw [Array.toArray_toList, rowsSummand_read, summandAt_read]
  show _ = (((List.range Q.P.y.NI).flatMap fun i =>
    P6.rowProducts.zipIdx.map fun x =>
      (p.omV.getD (7 * i + x.2) zeroE, 4 * i + x.1.1, 4 * i + x.1.2)).map _).sum
  rw [sum_flatMap]
  refine congrArg List.sum (List.map_congr_left fun i _ => ?_)
  rw [List.map_map]
  rfl

/-- One norm's summand on the masked end values has degree at most 2. -/
theorem summand_poly (om : ℕ → E) (ends m : List E) (b : ℕ) :
    PolyOn 2 fun y => P6.summand om fun k => (maskedEnds ends m y).toArray.getD (b + k) zeroE :=
  PolyOn.foldl (fun y t (x : (ℕ × ℕ) × ℕ) => addE t (mulE
      (mulE (om x.2) ((maskedEnds ends m y).toArray.getD (b + x.1.1) zeroE))
      ((maskedEnds ends m y).toArray.getD (b + x.1.2) zeroE)))
    P6.rowProducts.zipIdx (fun _ => zeroE) ((PolyOn.const zeroE).mono (Nat.zero_le 2))
    fun x _ _ hG => hG.add (((PolyOn.const (om x.2)).mul (PolyOn.entryA ends m (b + x.1.1))).mul
      (PolyOn.entryA ends m (b + x.1.2)))

/-- The verifier's summand on the masked end values has degree at most 2. -/
theorem rowsJob_poly (Q : K4Pub) (p : Pts) (ms : Array Tab) (rs m : List E) :
    PolyOn (rowsJobOf Q p ms).dY fun y =>
      (rowsJobOf Q p ms).atEnds rs (maskedEnds ((rowsJobOf Q p ms).ends rs) m y) :=
  PolyOn.foldl (fun y t i => addE t (P6.summand
      (fun r => (heardOf Q p).omV.getD (7 * i + r) zeroE)
      fun k => (maskedEnds ((rowsJobOf Q p ms).ends rs) m y).toArray.getD (4 * i + k) zeroE))
    (List.range Q.P.y.NI) (fun _ => zeroE) ((PolyOn.const zeroE).mono (Nat.zero_le 2))
    fun i _ _ hG => hG.add (summand_poly _ _ m (4 * i))

/-- One norm's summand reads alike on lists that read alike. -/
theorem summand_alike (om : ℕ → E) (b : ℕ) :
    ReadsAlike fun e => P6.summand om fun k => e.toArray.getD (b + k) zeroE :=
  ReadsAlike.foldl (fun e t (x : (ℕ × ℕ) × ℕ) => addE t (mulE
      (mulE (om x.2) (e.toArray.getD (b + x.1.1) zeroE)) (e.toArray.getD (b + x.1.2) zeroE)))
    P6.rowProducts.zipIdx (fun _ => zeroE) (ReadsAlike.const zeroE)
    fun x _ _ hG => hG.add (((ReadsAlike.const (om x.2)).mul (ReadsAlike.entryA (b + x.1.1))).mul
      (ReadsAlike.entryA (b + x.1.2)))

/-- So does the verifier's summand of all norms' rows. -/
theorem rowsJob_alike (Q : K4Pub) (p : Pts) (ms : Array Tab) (rs : List E) :
    ReadsAlike ((rowsJobOf Q p ms).atEnds rs) :=
  ReadsAlike.foldl (fun e t i => addE t (P6.summand
      (fun r => (heardOf Q p).omV.getD (7 * i + r) zeroE)
      fun k => e.toArray.getD (4 * i + k) zeroE))
    (List.range Q.P.y.NI) (fun _ => zeroE) (ReadsAlike.const zeroE)
    fun i _ _ hG => hG.add (summand_alike _ (4 * i))

/-- The row's second call has a token sumcheck's shape. -/
theorem k4Shapes_rows (Q : K4Pub) :
    (k4Shapes Q).getD 1 ⟨0, [], none⟩ =
      k4TokenShape Q.P.y.h.lt 2 (OnBytes.Model.ledNO Q.P.y.h.xl * Q.P.y.NI) := rfl

/-! ## 3 The chain -/

/-- **The polynomials of the sumcheck on the row products sum, round by round, from the cube's total
to the verifier's summand on the masked end values.** k: the number of end values that the call
states. r: the challenges of a token's bits, then Y's. m: the end values' mask entries. -/
theorem rows_sumsTo (Q : K4Pub) (w : K4In) (fr : Front Unit) (j : Job) (k : ℕ)
    (hj : jobRows Q w (ptsOf Q w fr.heard) = some j) (m r : List E)
    (hm : (j.ends (r.take Q.P.y.h.lt)).length = m.length) (hr : r.length = Q.P.y.h.lt + 1) :
    SumsTo Reading.gl
      ((k4SumJob (k4TokenShape Q.P.y.h.lt 2 k) fun w fr =>
        jobRows Q w (ptsOf Q w fr.heard)).callAt w fr).all
      (jobPoly (k4SumJob (k4TokenShape Q.P.y.h.lt 2 k) fun w fr =>
        jobRows Q w (ptsOf Q w fr.heard)) w fr m) [] r (Reading.gl.val j.cube.total)
      (Reading.gl.val (rowsSummand Q.P.y (heardOf Q (ptsOf Q w fr.heard))
        (maskedEnds (j.ends (r.take Q.P.y.h.lt)) m (r.getD Q.P.y.h.lt zeroE)).toArray)) := by
  have hj' := hj
  rw [jobRows_eq] at hj'
  cases hms : rowMaps Q w (ptsOf Q w fr.heard) with
  | none =>
    rw [hms] at hj'
    cases hj'
  | some ms =>
    rw [hms] at hj'
    have hj2 : (if (rowsJobOf Q (ptsOf Q w fr.heard) ms).cube.fits then
        some (rowsJobOf Q (ptsOf Q w fr.heard) ms) else none) = some j := hj'
    split at hj2
    · rename_i hf
      obtain rfl := Option.some.inj hj2
      exact k4_sumsTo_own (k4TokenShape Q.P.y.h.lt 2 k)
        (fun w fr => jobRows Q w (ptsOf Q w fr.heard)) w fr _ hj (rowsJob_shape Q _ ms k hf)
        (by show 2 + 1 < 2 ^ 32; norm_num) m r hr hm (rowsJob_poly Q _ ms _ m)
        (rowsJob_alike Q _ ms _) (rowsJob_ends Q _ ms _)
    · cases hj2

end ProofFile.Honest.K4

#print axioms ProofFile.Honest.K4.foldAdd_read
#print axioms ProofFile.Honest.K4.sum_flatMap
#print axioms ProofFile.Honest.K4.summand_read
#print axioms ProofFile.Honest.K4.rowsSummand_read
#print axioms ProofFile.Honest.K4.rowsJobOf
#print axioms ProofFile.Honest.K4.jobRows_eq
#print axioms ProofFile.Honest.K4.rowsJob_shape
#print axioms ProofFile.Honest.K4.rowsJob_ends
#print axioms ProofFile.Honest.K4.summand_poly
#print axioms ProofFile.Honest.K4.rowsJob_poly
#print axioms ProofFile.Honest.K4.summand_alike
#print axioms ProofFile.Honest.K4.rowsJob_alike
#print axioms ProofFile.Honest.K4.k4Shapes_rows
#print axioms ProofFile.Honest.K4.rows_sumsTo
