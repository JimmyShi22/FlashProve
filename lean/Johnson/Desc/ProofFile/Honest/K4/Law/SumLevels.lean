-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K4/Law/SumLevels.lean: CONDITIONAL. One definition, and statements
with their proofs.

What is here. What the law of the masked sumcheck's honest part asks of a caller (`SumsTo`,
Honest/SumLaw/Terms.lean), at the three product levels of the feed-forward layers' rounds: the
squares (`jobSquares`, Johnson/Desc/K4/Honest/Norms.lean) and the two gated products (`levelJob`,
`jobGated`, `jobGated2`, Johnson/Desc/K4/Honest/Gated.lean).

  `prod_sumsTo`   a job whose summand on end values is the product of the first two
  `levelJob_jobFits`, `levelJob_sumsTo`   a product level of two tables
  `orderRange_mem`, `levelJob_fits`   where such a level's cube fits
  `gatedTabs_size`, `gatedTabs2_size`   the two tables' sizes, where their maker returns
  `gated_sumsTo`, `gated2_sumsTo`   at the row's own jobs, where the run's cube fits
  `gated_sumsTo'`, `gated2_sumsTo'`   the same from nine variables and the point's size
  `sqJobOf`, `jobSquares_eq`, `sqJob_jobFits`, `squares_sumsTo`   the squares
  `k4Shapes_squares`, `k4Shapes_gated`, `k4Shapes_gated2`   the row's first, fifth and sixth calls
     have the shapes that are used here

Limits. THREE FILES THAT ARE NAMED BELOW ARE NO PART OF THE LIBRARY YET: SumPaid.lean and
SumAtRun.lean beside this file, and Law/W/FitNorms.lean. At the reading `Reading.gl` alone. For the
gated products the premises that are left on the job are: the maker of the two tables returns; the
level has at least nine variables (below nine `orderRange` lists no order); and THE POINT HAS AS
MANY COORDINATES AS THE LEVEL HAS VARIABLES, at the run's own challenges. For the squares THAT THE
MAKER RETURNS A JOB IS A PREMISE (it returns one only where its cube fits); SumPaid.lean's
`jobSquares_returns`, SumAtRun.lean and Law/W/FitNorms.lean's `squares_fit` speak of it. Two mask
entries, and one challenge more than the cube has variables, are premises. NEITHER END OF A CHAIN IS
TIED TO A VERIFIER's FORM: it begins at the reading of the cube's total and ends at the product of
the two end values, each plus the last challenge times its mask entry; that the first is the value
of the form that the verifier claims, and that the second is the product of the two values as they
were sent, is not said here. Nothing on what the tables hold.

Kin. Two tools are the library's and are called here: an array's list entry by entry (`toList_getD`,
Johnson/Desc/First/Batch/Law/Equation.lean, at every type and default); from nine variables on
`orderRange` lists as many as there are (`range_length`, OnBytes/Tie/Pv/Lay/Order.lean).
`orderRange_mem` follows, from nine variables on, from that file's `range_perm` (`orderRange mu` is
a rearrangement of `List.range mu`); it stands here without the nine.

No property is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.CubeSum
import Johnson.Desc.First.Batch.Law.Equation
import OnBytes.Tie.Pv.Lay.Order

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K4
open OnBytes (E F mulE zeroE oneE)
open OnBytes.Model (Reading orderRange orderDefault)
open OnBytes.Model.Layer (downFrom normsStart)
open OnBytes.Desc.First.K4.Honest
open OnBytes.Desc.First.K4.Honest.CubeLaw
open VerifiableInference.Desc.Part.MaskedSum (Call)
open ProofFile.Honest.SumLaw (SumsTo jobPoly)
open VerifiableInference.Desc.K9L (toList_getD)
open OnBytes.Tie.Pv.Lay (range_length)

/-! ## 1 A product of two end values -/

/-- **A job whose summand on end values is the product of the first two.** r: the challenges of the
cube's variables, then Y's. m: the end values' mask entries. hE, the weightiest hypothesis: the
product of the first two true end values reads as the cube's summand at the challenges. -/
theorem prod_sumsTo {W X : Type} (sh : Call) (job : W → Front X → Option Job) (w : W)
    (fr : Front X) (j : Job) (hj : job w fr = some j) (hfit : k4JobFits sh j = true)
    (hdY : j.dY = 2)
    (hat : ∀ rs e, j.atEnds rs e = mulE (e.getD 0 zeroE) (e.getD 1 zeroE)) (m r : List E)
    (hr : r.length = j.cube.n + 1) (hm : (j.ends (r.take j.cube.n)).length = m.length)
    (hE : Reading.gl.val ((j.ends (r.take j.cube.n)).getD 0 zeroE) *
        Reading.gl.val ((j.ends (r.take j.cube.n)).getD 1 zeroE) =
      Reading.gl.val (j.cube.summandAt (r.take j.cube.n))) :
    SumsTo Reading.gl ((k4SumJob sh job).callAt w fr).all (jobPoly (k4SumJob sh job) w fr m) [] r
      (Reading.gl.val j.cube.total)
      ((Reading.gl.val ((j.ends (r.take j.cube.n)).getD 0 zeroE) +
          Reading.gl.val (r.getD j.cube.n zeroE) * Reading.gl.val (m.getD 0 zeroE)) *
        (Reading.gl.val ((j.ends (r.take j.cube.n)).getD 1 zeroE) +
          Reading.gl.val (r.getD j.cube.n zeroE) * Reading.gl.val (m.getD 1 zeroE))) := by
  have hfun : j.atEnds (r.take j.cube.n) = fun e => mulE (e.getD 0 zeroE) (e.getD 1 zeroE) :=
    funext (hat _)
  have key := k4_sumsTo sh job w fr j hj hfit (by rw [hdY]; norm_num) m r hr hm
    (by rw [hdY, hfun]; exact (PolyOn.entry _ m 0).mul (PolyOn.entry _ m 1))
    (by rw [hfun]; exact (ReadsAlike.entry 0).mul (ReadsAlike.entry 1))
    (by rw [hat, Reading.gl.mul]; exact hE)
  rw [hat, Reading.gl.mul, maskedEnds_read _ _ hm, maskedEnds_read _ _ hm] at key
  exact key

/-! ## 2 A product level of two tables -/

/-- Where its cube fits, a product level's job has the public shape of a level. -/
theorem levelJob_jobFits (mu : ℕ) (order : List ℕ) (rho : Array E) (t : Tab × Tab)
    (h : (levelJob mu order rho t).cube.fits = true) :
    k4JobFits (k4LevelShape mu) (levelJob mu order rho t) = true := by
  unfold k4JobFits
  rw [h]
  simp [k4LevelShape, levelJob, valuesAt_size, VerifiableInference.Desc.Part.MaskedSum.Var.d]

/-- **A product level's polynomials sum, round by round, from the cube's total to the product of
the two maps' values at the challenges, each masked.** -/
theorem levelJob_sumsTo {W X : Type} (job : W → Front X → Option Job) (w : W) (fr : Front X)
    (mu : ℕ) (order : List ℕ) (rho : Array E) (t : Tab × Tab)
    (hj : job w fr = some (levelJob mu order rho t))
    (hfit : (levelJob mu order rho t).cube.fits = true) (m r : List E) (hm : m.length = 2)
    (hr : r.length = mu + 1) :
    SumsTo Reading.gl ((k4SumJob (k4LevelShape mu) job).callAt w fr).all
      (jobPoly (k4SumJob (k4LevelShape mu) job) w fr m) [] r
      (Reading.gl.val (levelJob mu order rho t).cube.total)
      ((Reading.gl.val (((levelJob mu order rho t).cube.valuesAt (r.take mu)).getD 0 zeroE) +
          Reading.gl.val (r.getD mu zeroE) * Reading.gl.val (m.getD 0 zeroE)) *
        (Reading.gl.val (((levelJob mu order rho t).cube.valuesAt (r.take mu)).getD 1 zeroE) +
          Reading.gl.val (r.getD mu zeroE) * Reading.gl.val (m.getD 1 zeroE))) := by
  have key := prod_sumsTo (k4LevelShape mu) job w fr (levelJob mu order rho t) hj
    (levelJob_jobFits mu order rho t hfit) rfl (fun _ _ => rfl) m r hr
    (by
      show (((levelJob mu order rho t).cube.valuesAt (r.take mu)).toList).length = _
      rw [Array.length_toList, valuesAt_size, hm]
      rfl)
    (by
      show Reading.gl.val (((levelJob mu order rho t).cube.valuesAt (r.take mu)).toList.getD 0
          zeroE) * Reading.gl.val (((levelJob mu order rho t).cube.valuesAt
            (r.take mu)).toList.getD 1 zeroE) = _
      rw [summandAt_read, toList_getD, toList_getD]
      show _ = Reading.gl.val oneE * _ + 0
      rw [Reading.gl.one, one_mul, add_zero]
      rfl)
  have e : ∀ i, ((levelJob mu order rho t).ends (r.take (levelJob mu order rho t).cube.n)).getD i
      zeroE = ((levelJob mu order rho t).cube.valuesAt (r.take mu)).getD i zeroE :=
    fun i => toList_getD _ i _
  rw [e, e] at key
  exact key

/-! ## 3 Where a level's cube fits -/

/-- `orderRange` lists each variable. -/
theorem orderRange_mem (mu v : ℕ) (hv : v < mu) : v ∈ orderRange mu := by
  unfold orderRange
  rw [List.mem_append]
  by_cases h : v < 9
  · left
    interval_cases v <;> simp
  · right
    rw [List.mem_map]
    exact ⟨v - 9, by simp; omega, by omega⟩

/-- From sizes: the test accepts, in the order `orderRange`. -/
theorem levelJob_fits (mu : ℕ) (rho : Array E) (t : Tab × Tab) (h9 : 9 ≤ mu)
    (hrho : rho.size = mu) (h1 : t.1.size = 2 ^ mu) (h2 : t.2.size = 2 ^ mu) :
    (levelJob mu (orderRange mu) rho t).cube.fits = true := by
  refine fits_of _ (range_length mu h9) (fun v hv => orderRange_mem mu v hv) ?_ ?_ ?_
  · intro x hx
    have hx' : x ∈ [t.1, t.2] := hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx'
    rcases hx' with rfl | rfl
    · exact h1
    · exact h2
  · intro x hx
    have hx' : x ∈ [((oneE, 0, 1) : E × ℕ × ℕ)] := hx
    rw [List.mem_singleton] at hx'
    rw [hx']
    exact ⟨by show 0 < 2; norm_num, by show 1 < 2; norm_num⟩
  · intro r hr
    have : rho = r := by
      have h' : Way.point rho = Way.point r := hr
      exact Way.point.inj h'
    rw [← this]
    exact hrho

/-- Where their maker returns, the first gated product's two tables have 2 ^ muH entries. -/
theorem gatedTabs_size (Q : K4Pub) (w : K4In) (t : Tab × Tab) (ht : gatedTabs Q w = some t) :
    t.1.size = 2 ^ Q.P.rd.muH ∧ t.2.size = 2 ^ Q.P.rd.muH := by
  unfold gatedTabs at ht
  cases h1 : Q.P.y.T_ "s" with
  | none => simp [h1] at ht
  | some ts =>
    cases h2 : Q.P.y.T_ "u" with
    | none => simp [h1, h2] at ht
    | some tu =>
      simp only [h1, h2, Option.bind_eq_bind, Option.bind_some, Option.pure_def,
        Option.some.injEq] at ht
      rw [← ht]
      simp [layerTab]

/-- So have the second's, 2 ^ muH2. -/
theorem gatedTabs2_size (Q : K4Pub) (w : K4In) (t : Tab × Tab) (ht : gatedTabs2 Q w = some t) :
    t.1.size = 2 ^ Q.P.rd.muH2 ∧ t.2.size = 2 ^ Q.P.rd.muH2 := by
  unfold gatedTabs2 at ht
  cases h1 : Q.P.y.T_ "s" with
  | none => simp [h1] at ht
  | some ts =>
    cases h2 : Q.P.y.T_ "u" with
    | none => simp [h1, h2] at ht
    | some tu =>
      simp only [h1, h2, Option.bind_eq_bind, Option.bind_some, Option.pure_def,
        Option.some.injEq] at ht
      rw [← ht]
      simp [layerTab]

/-! ## 4 At the row's own jobs -/

/-- The first gated product. -/
theorem gated_sumsTo (Q : K4Pub) (w : K4In) (fr : Front Unit) (t : Tab × Tab)
    (ht : gatedTabs Q w = some t)
    (hfit : (levelJob Q.P.rd.muH (orderRange Q.P.rd.muH)
      (downFrom (ptsOf Q w fr.heard).rs (Q.P.y.h.ll + Q.P.y.lPf) ++ ztOf Q (ptsOf Q w fr.heard))
      t).cube.fits = true) (m r : List E) (hm : m.length = 2) (hr : r.length = Q.P.rd.muH + 1) :
    SumsTo Reading.gl
      ((k4SumJob (k4LevelShape Q.P.rd.muH) fun w fr =>
        jobGated Q w (ptsOf Q w fr.heard)).callAt w fr).all
      (jobPoly (k4SumJob (k4LevelShape Q.P.rd.muH) fun w fr =>
        jobGated Q w (ptsOf Q w fr.heard)) w fr m) [] r
      (Reading.gl.val (levelJob Q.P.rd.muH (orderRange Q.P.rd.muH)
        (downFrom (ptsOf Q w fr.heard).rs (Q.P.y.h.ll + Q.P.y.lPf) ++ ztOf Q (ptsOf Q w fr.heard))
        t).cube.total)
      ((Reading.gl.val (((levelJob Q.P.rd.muH (orderRange Q.P.rd.muH)
          (downFrom (ptsOf Q w fr.heard).rs (Q.P.y.h.ll + Q.P.y.lPf) ++
            ztOf Q (ptsOf Q w fr.heard)) t).cube.valuesAt (r.take Q.P.rd.muH)).getD 0 zeroE) +
          Reading.gl.val (r.getD Q.P.rd.muH zeroE) * Reading.gl.val (m.getD 0 zeroE)) *
        (Reading.gl.val (((levelJob Q.P.rd.muH (orderRange Q.P.rd.muH)
          (downFrom (ptsOf Q w fr.heard).rs (Q.P.y.h.ll + Q.P.y.lPf) ++
            ztOf Q (ptsOf Q w fr.heard)) t).cube.valuesAt (r.take Q.P.rd.muH)).getD 1 zeroE) +
          Reading.gl.val (r.getD Q.P.rd.muH zeroE) * Reading.gl.val (m.getD 1 zeroE))) :=
  levelJob_sumsTo (fun w fr => jobGated Q w (ptsOf Q w fr.heard)) w fr _ _ _ t
    (by show (gatedTabs Q w).map _ = _; rw [ht]; rfl) hfit m r hm hr

/-- The second gated product. -/
theorem gated2_sumsTo (Q : K4Pub) (w : K4In) (fr : Front Unit) (t : Tab × Tab)
    (ht : gatedTabs2 Q w = some t)
    (hfit : (levelJob Q.P.rd.muH2 (orderRange Q.P.rd.muH2)
      ((ptsOf Q w fr.heard).rhoM ++ downFrom (ptsOf Q w fr.heard).rs Q.P.y.lfe ++
        (ptsOf Q w fr.heard).rt) t).cube.fits = true) (m r : List E) (hm : m.length = 2)
    (hr : r.length = Q.P.rd.muH2 + 1) :
    SumsTo Reading.gl
      ((k4SumJob (k4LevelShape Q.P.rd.muH2) fun w fr =>
        jobGated2 Q w (ptsOf Q w fr.heard)).callAt w fr).all
      (jobPoly (k4SumJob (k4LevelShape Q.P.rd.muH2) fun w fr =>
        jobGated2 Q w (ptsOf Q w fr.heard)) w fr m) [] r
      (Reading.gl.val (levelJob Q.P.rd.muH2 (orderRange Q.P.rd.muH2)
        ((ptsOf Q w fr.heard).rhoM ++ downFrom (ptsOf Q w fr.heard).rs Q.P.y.lfe ++
          (ptsOf Q w fr.heard).rt) t).cube.total)
      ((Reading.gl.val (((levelJob Q.P.rd.muH2 (orderRange Q.P.rd.muH2)
          ((ptsOf Q w fr.heard).rhoM ++ downFrom (ptsOf Q w fr.heard).rs Q.P.y.lfe ++
            (ptsOf Q w fr.heard).rt) t).cube.valuesAt (r.take Q.P.rd.muH2)).getD 0 zeroE) +
          Reading.gl.val (r.getD Q.P.rd.muH2 zeroE) * Reading.gl.val (m.getD 0 zeroE)) *
        (Reading.gl.val (((levelJob Q.P.rd.muH2 (orderRange Q.P.rd.muH2)
          ((ptsOf Q w fr.heard).rhoM ++ downFrom (ptsOf Q w fr.heard).rs Q.P.y.lfe ++
            (ptsOf Q w fr.heard).rt) t).cube.valuesAt (r.take Q.P.rd.muH2)).getD 1 zeroE) +
          Reading.gl.val (r.getD Q.P.rd.muH2 zeroE) * Reading.gl.val (m.getD 1 zeroE))) :=
  levelJob_sumsTo (fun w fr => jobGated2 Q w (ptsOf Q w fr.heard)) w fr _ _ _ t
    (by show (gatedTabs2 Q w).map _ = _; rw [ht]; rfl) hfit m r hm hr

/-- The first gated product, from nine variables and the point's size. -/
theorem gated_sumsTo' (Q : K4Pub) (w : K4In) (fr : Front Unit) (t : Tab × Tab)
    (ht : gatedTabs Q w = some t)
    (h9 : 9 ≤ Q.P.rd.muH)
    (hrho : (downFrom (ptsOf Q w fr.heard).rs (Q.P.y.h.ll + Q.P.y.lPf) ++
      ztOf Q (ptsOf Q w fr.heard)).size = Q.P.rd.muH) (m r : List E) (hm : m.length = 2)
    (hr : r.length = Q.P.rd.muH + 1) :
    SumsTo Reading.gl
      ((k4SumJob (k4LevelShape Q.P.rd.muH) fun w fr =>
        jobGated Q w (ptsOf Q w fr.heard)).callAt w fr).all
      (jobPoly (k4SumJob (k4LevelShape Q.P.rd.muH) fun w fr =>
        jobGated Q w (ptsOf Q w fr.heard)) w fr m) [] r
      (Reading.gl.val (levelJob Q.P.rd.muH (orderRange Q.P.rd.muH)
        (downFrom (ptsOf Q w fr.heard).rs (Q.P.y.h.ll + Q.P.y.lPf) ++ ztOf Q (ptsOf Q w fr.heard))
        t).cube.total)
      ((Reading.gl.val (((levelJob Q.P.rd.muH (orderRange Q.P.rd.muH)
          (downFrom (ptsOf Q w fr.heard).rs (Q.P.y.h.ll + Q.P.y.lPf) ++
            ztOf Q (ptsOf Q w fr.heard)) t).cube.valuesAt (r.take Q.P.rd.muH)).getD 0 zeroE) +
          Reading.gl.val (r.getD Q.P.rd.muH zeroE) * Reading.gl.val (m.getD 0 zeroE)) *
        (Reading.gl.val (((levelJob Q.P.rd.muH (orderRange Q.P.rd.muH)
          (downFrom (ptsOf Q w fr.heard).rs (Q.P.y.h.ll + Q.P.y.lPf) ++
            ztOf Q (ptsOf Q w fr.heard)) t).cube.valuesAt (r.take Q.P.rd.muH)).getD 1 zeroE) +
          Reading.gl.val (r.getD Q.P.rd.muH zeroE) * Reading.gl.val (m.getD 1 zeroE))) :=
  gated_sumsTo Q w fr t ht
    (levelJob_fits _ _ t h9 hrho (gatedTabs_size Q w t ht).1 (gatedTabs_size Q w t ht).2) m r hm hr

/-- The second gated product, from nine variables and the point's size. -/
theorem gated2_sumsTo' (Q : K4Pub) (w : K4In) (fr : Front Unit) (t : Tab × Tab)
    (ht : gatedTabs2 Q w = some t)
    (h9 : 9 ≤ Q.P.rd.muH2)
    (hrho : ((ptsOf Q w fr.heard).rhoM ++ downFrom (ptsOf Q w fr.heard).rs Q.P.y.lfe ++
      (ptsOf Q w fr.heard).rt).size =
      Q.P.rd.muH2) (m r : List E) (hm : m.length = 2)
    (hr : r.length = Q.P.rd.muH2 + 1) :
    SumsTo Reading.gl
      ((k4SumJob (k4LevelShape Q.P.rd.muH2) fun w fr =>
        jobGated2 Q w (ptsOf Q w fr.heard)).callAt w fr).all
      (jobPoly (k4SumJob (k4LevelShape Q.P.rd.muH2) fun w fr =>
        jobGated2 Q w (ptsOf Q w fr.heard)) w fr m) [] r
      (Reading.gl.val (levelJob Q.P.rd.muH2 (orderRange Q.P.rd.muH2)
        ((ptsOf Q w fr.heard).rhoM ++ downFrom (ptsOf Q w fr.heard).rs Q.P.y.lfe ++
          (ptsOf Q w fr.heard).rt) t).cube.total)
      ((Reading.gl.val (((levelJob Q.P.rd.muH2 (orderRange Q.P.rd.muH2)
          ((ptsOf Q w fr.heard).rhoM ++ downFrom (ptsOf Q w fr.heard).rs Q.P.y.lfe ++
            (ptsOf Q w fr.heard).rt) t).cube.valuesAt (r.take Q.P.rd.muH2)).getD 0 zeroE) +
          Reading.gl.val (r.getD Q.P.rd.muH2 zeroE) * Reading.gl.val (m.getD 0 zeroE)) *
        (Reading.gl.val (((levelJob Q.P.rd.muH2 (orderRange Q.P.rd.muH2)
          ((ptsOf Q w fr.heard).rhoM ++ downFrom (ptsOf Q w fr.heard).rs Q.P.y.lfe ++
            (ptsOf Q w fr.heard).rt) t).cube.valuesAt (r.take Q.P.rd.muH2)).getD 1 zeroE) +
          Reading.gl.val (r.getD Q.P.rd.muH2 zeroE) * Reading.gl.val (m.getD 1 zeroE))) :=
  gated2_sumsTo Q w fr t ht
    (levelJob_fits _ _ t h9 hrho (gatedTabs2_size Q w t ht).1 (gatedTabs2_size Q w t ht).2) m r hm
    hr

/-- The row's fifth call has a level's shape. -/
theorem k4Shapes_gated (Q : K4Pub) :
    (k4Shapes Q).getD 4 ⟨0, [], none⟩ = k4LevelShape Q.P.rd.muH := rfl

/-- The sixth. -/
theorem k4Shapes_gated2 (Q : K4Pub) :
    (k4Shapes Q).getD 5 ⟨0, [], none⟩ = k4LevelShape Q.P.rd.muH2 := rfl

/-- So has its first. -/
theorem k4Shapes_squares (Q : K4Pub) :
    (k4Shapes Q).getD 0 ⟨0, [], none⟩ = k4LevelShape Q.P.rd.muV := rfl

/-! ## 5 The squares -/

/-- The squares' job, of its number of variables, point and table. -/
def sqJobOf (mu : ℕ) (rho : Array E) (t : Tab) : Job :=
  let cube : Cube :=
    { n := mu, order := orderDefault mu, way := .point rho, maps := #[t], pairs := [(oneE, 0, 0)] }
  { lead := [], cube, dY := 2
    ends := fun rs => [(cube.valuesAt rs).getD 0 zeroE, (cube.valuesAt rs).getD 0 zeroE]
    atEnds := fun _ e => mulE (e.getD 0 zeroE) (e.getD 1 zeroE) }

/-- The maker, written with `sqJobOf`. -/
theorem jobSquares_eq (Q : K4Pub) (w : K4In) (p : Pts) :
    jobSquares Q w p =
      if (sqJobOf Q.P.rd.muV (normsStart Q.P.y 0 p.gp p.rhoI p.PV).2
        (squaresTab Q w p.gp)).cube.fits then
        some (sqJobOf Q.P.rd.muV (normsStart Q.P.y 0 p.gp p.rhoI p.PV).2 (squaresTab Q w p.gp))
      else none := rfl

/-- Where its cube fits, the squares' job has the public shape of a level. -/
theorem sqJob_jobFits (mu : ℕ) (rho : Array E) (t : Tab)
    (h : (sqJobOf mu rho t).cube.fits = true) :
    k4JobFits (k4LevelShape mu) (sqJobOf mu rho t) = true := by
  unfold k4JobFits
  rw [h]
  simp [k4LevelShape, sqJobOf, VerifiableInference.Desc.Part.MaskedSum.Var.d]

/-- **The squares' polynomials sum, round by round, from the cube's total to a product of two**: the
one table's value at the challenges plus the last challenge times the first mask entry, times that
value plus the last challenge times the second. The maker returns a job only where its cube fits.
-/
theorem squares_sumsTo (Q : K4Pub) (w : K4In) (fr : Front Unit) (j : Job)
    (hj : jobSquares Q w (ptsOf Q w fr.heard) = some j) (m r : List E) (hm : m.length = 2)
    (hr : r.length = Q.P.rd.muV + 1) :
    SumsTo Reading.gl
      ((k4SumJob (k4LevelShape Q.P.rd.muV) fun w fr =>
        jobSquares Q w (ptsOf Q w fr.heard)).callAt w fr).all
      (jobPoly (k4SumJob (k4LevelShape Q.P.rd.muV) fun w fr =>
        jobSquares Q w (ptsOf Q w fr.heard)) w fr m) [] r (Reading.gl.val j.cube.total)
      ((Reading.gl.val ((j.cube.valuesAt (r.take Q.P.rd.muV)).getD 0 zeroE) +
          Reading.gl.val (r.getD Q.P.rd.muV zeroE) * Reading.gl.val (m.getD 0 zeroE)) *
        (Reading.gl.val ((j.cube.valuesAt (r.take Q.P.rd.muV)).getD 0 zeroE) +
          Reading.gl.val (r.getD Q.P.rd.muV zeroE) * Reading.gl.val (m.getD 1 zeroE))) := by
  have hj' := hj
  rw [jobSquares_eq] at hj'
  split at hj'
  · rename_i hf
    obtain rfl := Option.some.inj hj'
    exact prod_sumsTo (k4LevelShape Q.P.rd.muV)
      (fun w fr => jobSquares Q w (ptsOf Q w fr.heard)) w fr _ hj (sqJob_jobFits _ _ _ hf) rfl
      (fun _ _ => rfl) m r hr (by rw [hm]; rfl) (by
        rw [summandAt_read]
        show _ = Reading.gl.val oneE * _ + 0
        rw [Reading.gl.one, one_mul, add_zero]
        rfl)
  · cases hj'

end ProofFile.Honest.K4

#print axioms ProofFile.Honest.K4.prod_sumsTo
#print axioms ProofFile.Honest.K4.levelJob_jobFits
#print axioms ProofFile.Honest.K4.levelJob_sumsTo
#print axioms ProofFile.Honest.K4.orderRange_mem
#print axioms ProofFile.Honest.K4.levelJob_fits
#print axioms ProofFile.Honest.K4.gatedTabs_size
#print axioms ProofFile.Honest.K4.gatedTabs2_size
#print axioms ProofFile.Honest.K4.gated_sumsTo
#print axioms ProofFile.Honest.K4.gated2_sumsTo
#print axioms ProofFile.Honest.K4.gated_sumsTo'
#print axioms ProofFile.Honest.K4.gated2_sumsTo'
#print axioms ProofFile.Honest.K4.k4Shapes_gated
#print axioms ProofFile.Honest.K4.k4Shapes_gated2
#print axioms ProofFile.Honest.K4.k4Shapes_squares
#print axioms ProofFile.Honest.K4.sqJobOf
#print axioms ProofFile.Honest.K4.jobSquares_eq
#print axioms ProofFile.Honest.K4.sqJob_jobFits
#print axioms ProofFile.Honest.K4.squares_sumsTo
