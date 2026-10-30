-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K4/Law/SumPoints.lean: CONDITIONAL. Statements with their proofs; no
definition.

What is here. THE POINTS, WORD FOR WORD. The variables of the call that the honest part of a masked
sumcheck plays (`SumJob.callAt`), as weights of `verify-on-bytes` (`Var.weight`,
Johnson/Desc/Part/MaskedSumTie.lean), are the lists of weights under which the library says what the
verifier's flat text has heard: `levelWs` (OnBytes/Desc/First/P1/FlSpec.lean) at the three product
levels of the feed-forward layers' rounds, `tscWs` (OnBytes/Desc/First/P1/TscKit.lean) at the
sumcheck on the row products; at the merge, plain weights. And the challenges, laid as a point
(`Cube.pointOf`), are the array that the library's word on a level's hearing has. Equations between
lists of machine words.

  `wp_replicate_point`, `wp_replicate_of`, `wp_replicate_plain`   the run's points laid into a shape
  `fits_way`   the point's size
  `fold_levelR`, `pointOf_levelR`, `pointOf_front`   the challenges as a point are the library's
     `levelR` of them
  `point_call_vs`, `point_weights`, `levelWs_tsc`   a job that is summed at a point
  `squares_weights`, `gated_weights`, `gated2_weights`, `rows_weights`, `merge_weights`   **the
     five**

Limits. The variables in front of the further one alone. Premises: the job's maker returns at the
run's input; for a gated product the run's cube fits. THAT THE VERIFIER RUNS ITS LEVEL AT THE SAME
NUMBER OF VARIABLES, POINT AND ORDER, and its token sumcheck at the same point, AND HEARS THESE
CHALLENGES, is not said here: the right sides are typed with the makers' own letters. The tie
between the two texts of the sumcheck is not called here. No example of the premises together is
known to us at the full size.

Kin. `wp_replicate_point` IS IN THE LIBRARY ALREADY, the statement the same but for two bound
letters: `head_withPoints_replicate` (Honest/K6/PairSumsTo.lean), another kind's file, on which this
one does not build: a law on the frame's own `withPoints`, stated twice. Of kin beneath this file:
`wp_plain`, `wp_point` (CubeSum.lean): the same two facts entry by entry.

No property is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.SumLevels
import Johnson.Desc.ProofFile.Honest.K4.Law.SumRows
import Johnson.Desc.ProofFile.Honest.K4.Law.SumMerge
import Johnson.Desc.Part.MaskedSumTie
import OnBytes.Desc.First.P1.TscKit
import OnBytes.Desc.First.P1.OrderDefault

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K4
open OnBytes (E zeroE)
open OnBytes.Model (orderRange orderDefault WsClaim)
open OnBytes.Model.Layer (downFrom normsStart)
open OnBytes.Desc.First.P1 (levelWs tscWs)
open OnBytes.Desc.First.K4.Honest
open OnBytes.Desc.First.K4.Honest.CubeLaw
open VerifiableInference.Desc.Part.MaskedSum (Call Var)

variable {W X : Type}

/-! ## 1 The run's points laid into a shape -/

/-- As many points as variables, all summed at a point: each variable takes its point. -/
theorem wp_replicate_point (z0 : E) : ∀ zs : List E,
    withPoints (List.replicate zs.length (Var.point z0 3)) zs = zs.map fun z => Var.point z 3
  | [] => rfl
  | z :: zs => by
    rw [List.length_cons, List.replicate_succ, withPoints, wp_replicate_point z0 zs, List.map_cons]

/-- The same, where the number of the points is known by an equation. -/
theorem wp_replicate_of (z0 : E) (n : ℕ) (zs : List E) (h : zs.length = n) :
    withPoints (List.replicate n (Var.point z0 3)) zs = zs.map fun z => Var.point z 3 := by
  subst h
  exact wp_replicate_point z0 zs

/-- Variables that are summed plainly take none. -/
theorem wp_replicate_plain (zs : List E) : ∀ n : ℕ,
    withPoints (List.replicate n (Var.plain 3)) zs = List.replicate n (Var.plain 3)
  | 0 => by
    rw [List.replicate_zero]
    rfl
  | n + 1 => by
    rw [List.replicate_succ, withPoints, wp_replicate_plain zs n]

/-- Where a cube fits, its point has a coordinate for each variable. -/
theorem fits_way (c : Cube) (h : c.fits = true) (rho : Array E) (hw : c.way = .point rho) :
    rho.size = c.n := by
  simp only [Cube.fits, Bool.and_eq_true] at h
  obtain ⟨_, hE⟩ := h
  rw [hw] at hE
  simpa using hE

/-- The loop that lays challenges at their variables' places is the library's `levelR`. -/
theorem fold_levelR (mu : ℕ) : ∀ (order : List ℕ) (rs : List E) (r : Array E),
    (order.zip rs).foldl (fun a x => a.set! (mu - 1 - x.1) x.2) r =
      OnBytes.Desc.First.P1.levelR mu order rs r
  | [], _, _ => by
    rw [List.zip_nil_left]
    rfl
  | _ :: _, [], _ => rfl
  | v :: order, x :: rs, r => by
    rw [List.zip_cons_cons, List.foldl_cons, fold_levelR mu order rs,
      OnBytes.Desc.First.P1.levelR_cons]

/-- **The challenges as a point are the library's `levelR` of them**: `Cube.pointOf` is the array
under which the library says what a product level has heard (`Level.r`; `levelIn_heard`,
OnBytes/Desc/First/P1/Heard.lean). An equation on words. -/
theorem pointOf_levelR (c : Cube) (rs : List E) :
    c.pointOf rs = OnBytes.Desc.First.P1.levelR c.n c.order rs (Array.replicate c.n zeroE) :=
  fold_levelR c.n c.order rs _

/-- It is also what the honest parts lay as a level's challenges (`levelR`,
Johnson/Desc/K4/Honest/Front.lean), once all have been sampled. -/
theorem pointOf_front (c : Cube) (rs : List E) (hr : rs.length = c.n) :
    c.pointOf rs = OnBytes.Desc.First.K4.Honest.levelR c.n c.order rs.toArray := by
  unfold OnBytes.Desc.First.K4.Honest.levelR
  rw [if_neg (by simp [hr])]
  rfl

/-! ## 2 A job that is summed at a point -/

/-- The call's variables, of the cube's order and point. sh: a shape of mu variables that are all
summed at a point, three coefficients each. -/
theorem point_call_vs (sh : Call) (mu : ℕ) (hsh : sh.vs = List.replicate mu (Var.point zeroE 3))
    (job : W → Front X → Option Job) (w : W) (fr : Front X) (j : Job) (rho : Array E)
    (hj : job w fr = some j) (hw : j.cube.way = .point rho) (hn : j.cube.n = mu)
    (ho : j.cube.order.length = mu) :
    ((k4SumJob sh job).callAt w fr).vs =
      j.cube.order.map fun v => Var.point (rho.getD (mu - 1 - v) zeroE) 3 := by
  have hp : ((job w fr).map fun j : Job => j.cube.points).getD [] =
      j.cube.order.map fun v => rho.getD (mu - 1 - v) zeroE := by
    rw [hj]
    show j.cube.points = _
    unfold Cube.points
    rw [hw, hn]
  show withPoints sh.vs (((job w fr).map fun j : Job => j.cube.points).getD []) = _
  rw [hsh, hp, wp_replicate_of zeroE mu _ (by rw [List.length_map, ho]), List.map_map]
  rfl

/-- The same as weights: the library's list for a product level. -/
theorem point_weights (sh : Call) (mu : ℕ) (hsh : sh.vs = List.replicate mu (Var.point zeroE 3))
    (job : W → Front X → Option Job) (w : W) (fr : Front X) (j : Job) (rho : Array E)
    (hj : job w fr = some j) (hw : j.cube.way = .point rho) (hn : j.cube.n = mu)
    (ho : j.cube.order.length = mu) :
    ((k4SumJob sh job).callAt w fr).vs.map Var.weight = levelWs mu rho j.cube.order := by
  rw [point_call_vs sh mu hsh job w fr j rho hj hw hn ho, List.map_map]
  rfl

/-! ## 3 The five -/

/-- **The squares.** -/
theorem squares_weights (Q : K4Pub) (w : K4In) (fr : Front Unit) (j : Job)
    (hj : jobSquares Q w (ptsOf Q w fr.heard) = some j) :
    ((k4SumJob (k4LevelShape Q.P.rd.muV) fun w fr =>
      jobSquares Q w (ptsOf Q w fr.heard)).callAt w fr).vs.map Var.weight =
      levelWs Q.P.rd.muV (normsStart Q.P.y 0 (ptsOf Q w fr.heard).gp (ptsOf Q w fr.heard).rhoI
        (ptsOf Q w fr.heard).PV).2 (orderDefault Q.P.rd.muV) := by
  have hj' := hj
  rw [jobSquares_eq] at hj'
  split at hj'
  · obtain rfl := Option.some.inj hj'
    exact point_weights (k4LevelShape Q.P.rd.muV) Q.P.rd.muV rfl
      (fun w fr => jobSquares Q w (ptsOf Q w fr.heard)) w fr _ _ hj rfl rfl
      (by show (orderDefault Q.P.rd.muV).length = _; simp [orderDefault])
  · cases hj'

/-- **The first gated product.** -/
theorem gated_weights (Q : K4Pub) (w : K4In) (fr : Front Unit) (t : Tab × Tab)
    (ht : gatedTabs Q w = some t)
    (hfit : (levelJob Q.P.rd.muH (orderRange Q.P.rd.muH)
      (downFrom (ptsOf Q w fr.heard).rs (Q.P.y.h.ll + Q.P.y.lPf) ++ ztOf Q (ptsOf Q w fr.heard))
      t).cube.fits = true) :
    ((k4SumJob (k4LevelShape Q.P.rd.muH) fun w fr =>
      jobGated Q w (ptsOf Q w fr.heard)).callAt w fr).vs.map Var.weight =
      levelWs Q.P.rd.muH
        (downFrom (ptsOf Q w fr.heard).rs (Q.P.y.h.ll + Q.P.y.lPf) ++ ztOf Q (ptsOf Q w fr.heard))
        (orderRange Q.P.rd.muH) :=
  point_weights (k4LevelShape Q.P.rd.muH) Q.P.rd.muH rfl
    (fun w fr => jobGated Q w (ptsOf Q w fr.heard)) w fr _ _
    (by show (gatedTabs Q w).map _ = _; rw [ht]; rfl) rfl rfl (fitsP _ hfit).len

/-- **The second gated product.** -/
theorem gated2_weights (Q : K4Pub) (w : K4In) (fr : Front Unit) (t : Tab × Tab)
    (ht : gatedTabs2 Q w = some t)
    (hfit : (levelJob Q.P.rd.muH2 (orderRange Q.P.rd.muH2)
      ((ptsOf Q w fr.heard).rhoM ++ downFrom (ptsOf Q w fr.heard).rs Q.P.y.lfe ++
        (ptsOf Q w fr.heard).rt) t).cube.fits = true) :
    ((k4SumJob (k4LevelShape Q.P.rd.muH2) fun w fr =>
      jobGated2 Q w (ptsOf Q w fr.heard)).callAt w fr).vs.map Var.weight =
      levelWs Q.P.rd.muH2
        ((ptsOf Q w fr.heard).rhoM ++ downFrom (ptsOf Q w fr.heard).rs Q.P.y.lfe ++
          (ptsOf Q w fr.heard).rt) (orderRange Q.P.rd.muH2) :=
  point_weights (k4LevelShape Q.P.rd.muH2) Q.P.rd.muH2 rfl
    (fun w fr => jobGated2 Q w (ptsOf Q w fr.heard)) w fr _ _
    (by show (gatedTabs2 Q w).map _ = _; rw [ht]; rfl) rfl rfl (fitsP _ hfit).len

/-- A level's weights in the order from the highest variable down are a token sumcheck's at the same
point: the library's `levelWs_default` (OnBytes/Desc/First/P1/OrderDefault.lean), with the token
sumcheck's cut of the point. -/
theorem levelWs_tsc (mu : ℕ) (rho : Array E) (hs : rho.size = mu) :
    levelWs mu rho (orderDefault mu) = tscWs (rho.toList.take mu) := by
  rw [OnBytes.Desc.First.P1.levelWs_default mu rho hs, List.take_of_length_le (by simp [hs])]
  rfl

/-- **The row products.** k: the number of end values that the call states. -/
theorem rows_weights (Q : K4Pub) (w : K4In) (fr : Front Unit) (j : Job) (k : ℕ)
    (hj : jobRows Q w (ptsOf Q w fr.heard) = some j) :
    ((k4SumJob (k4TokenShape Q.P.y.h.lt 2 k) fun w fr =>
      jobRows Q w (ptsOf Q w fr.heard)).callAt w fr).vs.map Var.weight =
      tscWs ((ptsOf Q w fr.heard).PV.toList.take Q.P.y.h.lt) := by
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
      rw [← levelWs_tsc Q.P.y.h.lt _ (fits_way _ hf _ rfl)]
      exact point_weights (k4TokenShape Q.P.y.h.lt 2 k) Q.P.y.h.lt rfl
        (fun w fr => jobRows Q w (ptsOf Q w fr.heard)) w fr _ _ hj rfl rfl
        (by show (orderDefault Q.P.y.h.lt).length = _; simp [orderDefault])
    · cases hj2

/-- **The merge**: plain weights, whatever the maker returns. -/
theorem merge_weights (Q : K4Pub) (w : K4In) (fr : Front Unit) :
    ((k4SumJob (k4PlainShape Q.P.wsLay.lk 1 1) fun w fr =>
      jobMerge Q w (ptsOf Q w fr.heard)).callAt w fr).vs.map Var.weight =
      List.replicate Q.P.wsLay.lk (OnBytes.Psc.Weight.plain 3) := by
  show (withPoints (List.replicate Q.P.wsLay.lk (Var.plain 3)) _).map Var.weight = _
  rw [wp_replicate_plain, List.map_replicate]
  rfl

end ProofFile.Honest.K4

#print axioms ProofFile.Honest.K4.wp_replicate_point
#print axioms ProofFile.Honest.K4.wp_replicate_of
#print axioms ProofFile.Honest.K4.wp_replicate_plain
#print axioms ProofFile.Honest.K4.fits_way
#print axioms ProofFile.Honest.K4.fold_levelR
#print axioms ProofFile.Honest.K4.pointOf_levelR
#print axioms ProofFile.Honest.K4.pointOf_front
#print axioms ProofFile.Honest.K4.point_call_vs
#print axioms ProofFile.Honest.K4.point_weights
#print axioms ProofFile.Honest.K4.squares_weights
#print axioms ProofFile.Honest.K4.gated_weights
#print axioms ProofFile.Honest.K4.gated2_weights
#print axioms ProofFile.Honest.K4.levelWs_tsc
#print axioms ProofFile.Honest.K4.rows_weights
#print axioms ProofFile.Honest.K4.merge_weights
