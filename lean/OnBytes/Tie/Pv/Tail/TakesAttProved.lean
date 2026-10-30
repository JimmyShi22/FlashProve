-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Tie/Pv/Tail/TakesAttProved.lean: which entries of the plan the attention sub-proof's own
messages use up, by their names, and that the planner lays rounds with these very names.

Theorems with their proofs, by the laws of OnBytes/Tie/Pv/Tail/EndTakes.lean (`Takes x N`: wherever
the verifier's routine x returns it has used up entries with just the names N) and of
OnBytes/Tie/Pv/Req/Names.lean (`Says x N`: wherever the planner's routine x ends well it has added
rounds with just the names N). The statements are the definitions of
OnBytes/Tie/Pv/Tail/TakesRows.lean, by name.

Main names:
  `takes_scores_sc3In`, `takes_attain_scdIn`: the two kinds of sumcheck of the sub-proof.
  `takes_scores`, `takes_divide`, `takes_attain`: the three routines of the sub-proof's own
    messages (OnBytes/Model/AttentionScores.lean, AttentionDivide.lean).
  `says_attOwn_forEach`: a planner's routine on each member of a list: the members' lists in a row.
  `says_attOwn_opt`: a step that lays no round and is taken under a condition alone.
  `says_attOwn`: the planner's routine for these rounds (OnBytes/Params/SubRounds.lean).
  `att_names_own`, `att_names_calls`: where Attention.plan succeeds, eight fields of its record of
    the own rounds are the shape's; what the pass over the calls adds to the list of score segments.
  `att_names`: at a plan that Attention.plan has made the two lists of names are one.

What is not claimed: names alone: nothing on an entry's or a round's other fields. One direction:
from a run that returns, or from a plan that is made; that the routines return anywhere is not
shown. Nothing on what the rounds prove, and nothing on hiding.
-/
import OnBytes.Tie.Pv.Tail.TakesRows

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Tie.Pv.Tail.TakesProved
open OnBytes OnBytes.Model OnBytes.Tie.Pv.Tail.Used OnBytes.Tie.Pv.Tail.Lull OnBytes.Tie.Pv.Req

/-! ## The sumcheck of products -/

/-- n rounds of degree 3 use up n entries named PSC round. -/
theorem takes_scores_sc3Rounds : ∀ (n : Nat) (p : Psc) (r : Array E),
    Takes (Attention.sc3Rounds n p r) (List.replicate n "PSC round")
  | 0, p, r => by
    unfold Attention.sc3Rounds
    exact Takes.pure _
  | n + 1, p, r => by
    unfold Attention.sc3Rounds
    exact Takes.bind (N := ["PSC round"]) (takes_roundIn _ _ _ _) fun x =>
      takes_scores_sc3Rounds n _ _

/-- A sumcheck of products uses up the entries of a masked sumcheck with nv rounds. -/
theorem takes_scores_sc3In (nv nb : Nat) (start : Aff) :
    Takes (Attention.sc3In nv nb start) (pscNames nv true) := by
  unfold Attention.sc3In
  exact (Takes.bind (takes_pscBegin start) fun p =>
    Takes.bind (takes_scores_sc3Rounds nv p _) fun x =>
      Takes.before (takes_pscEnds _ _ _) fun e => Takes.pure _).of_eq (by simp [pscNames])

/-! ## The matrix of the planes and the scores -/

/-- The plane values of a unit close no round. -/
theorem takes_scores_planeUnit (S : Attention.Shape) (zk : Array (Array E))
    (u : Nat × Attention.ACall × Attention.Seg) : Takes (Attention.planeUnit S zk u) [] := by
  unfold Attention.planeUnit
  dsimp only
  exact Takes.after (by qs) fun _ => Takes.pure _

/-- The plane values of a list of units close no round. -/
theorem takes_scores_planeUnits (S : Attention.Shape) (zk : Array (Array E)) :
    ∀ (us : List (Nat × Attention.ACall × Attention.Seg)) (planes : Array Attention.PlaneClaim),
      Takes (Attention.planeUnits S zk us planes) []
  | [], planes => by
    unfold Attention.planeUnits
    exact Takes.pure _
  | u :: us, planes => by
    unfold Attention.planeUnits
    exact Takes.after (takes_scores_planeUnit S zk u) fun p => takes_scores_planeUnits S zk us _

/-- A unit of the scores uses up the entries of its sumcheck of products. -/
theorem takes_scores_scoreUnit (S : Attention.Shape) (zk : Array (Array E)) (claim : Nat)
    (u : Nat × Attention.ACall × Attention.Seg) :
    Takes (Attention.scoreUnit S zk claim u) (pscNames (S.nvKF u.2.2) true) := by
  unfold Attention.scoreUnit
  dsimp only
  refine Takes.after (by qs) fun _ => Takes.after (by qs) fun s0 => ?_
  refine Takes.before (takes_scores_sc3In _ _ _) fun sc => ?_
  exact Takes.after (by qs) fun _ => Takes.pure _

/-- A list of units of the scores: the units' lists in a row. -/
theorem takes_scores_scoreUnits (S : Attention.Shape) (zk : Array (Array E)) :
    ∀ (us : List (Nat × Attention.ACall × Attention.Seg)) (planes : Array Attention.PlaneClaim)
      (stored : Array Attention.Score),
      Takes (Attention.scoreUnits S zk us planes stored)
        (us.flatMap fun u => pscNames (S.nvKF u.2.2) true)
  | [], planes, stored => by
    unfold Attention.scoreUnits
    exact Takes.pure _
  | u :: us, planes, stored => by
    unfold Attention.scoreUnits
    rw [List.flatMap_cons]
    exact Takes.bind (takes_scores_scoreUnit S zk _ u) fun x =>
      takes_scores_scoreUnits S zk us _ _

/-- **The messages on the planes and on the scores use up one masked sumcheck for each unit of a
call of kind KFD.** -/
theorem takes_scores : TakesRows.row_takes_scores := by
  intro S zk
  unfold Attention.scores TakesRows.scoresNames
  exact Takes.after (takes_scores_planeUnits S zk _ _) fun planes =>
    takes_scores_scoreUnits S zk _ _ _

/-! ## The division and the value product -/

/-- The sumcheck for the denominator times the output. -/
theorem takes_divide_productIn (S : Attention.Shape) (pwW : Array Attention.PW) (zgW ziW : Array E)
    (sZO : Nat) : Takes (Attention.productIn S pwW zgW ziW sZO) (pscNames S.nvE true) := by
  unfold Attention.productIn
  dsimp only
  exact Takes.before (takes_scores_sc3In _ _ _) fun o => by qs

/-- The value product's sumcheck below the diagonal. -/
theorem takes_divide_valueBelowIn (S : Attention.Shape) (pwW : Array Attention.PW)
    (zgW zihi : Array E) (sCl : Nat) :
    Takes (Attention.valueBelowIn S pwW zgW zihi sCl) (pscNames S.nvVM true) := by
  unfold Attention.valueBelowIn
  dsimp only
  exact Takes.before (takes_scores_sc3In _ _ _) fun o =>
    Takes.after (by qs) fun _ => Takes.pure _

/-- The value product's sumcheck on the diagonal. -/
theorem takes_divide_valueOnIn (S : Attention.Shape) (pwW : Array Attention.PW)
    (zgW zihi : Array E) (sCl1 : Nat) :
    Takes (Attention.valueOnIn S pwW zgW zihi sCl1) (pscNames S.nvVD true) := by
  unfold Attention.valueOnIn
  dsimp only
  exact Takes.before (takes_scores_sc3In _ _ _) fun o => by qs

/-- **The messages of the division and of the value product use up three masked sumchecks and,
behind the first, the round of a batching element.** -/
theorem takes_divide : TakesRows.row_takes_divide := by
  intro S zk
  unfold Attention.divide TakesRows.divideNames
  dsimp only
  refine Takes.after (by qs) fun _ => Takes.after (by qs) fun x => ?_
  obtain ⟨qW, pwW, zW⟩ := x
  dsimp only
  refine Takes.after (by qs) fun x => ?_
  obtain ⟨qX, pwX, zX⟩ := x
  dsimp only
  refine Takes.after (by qs) fun x => ?_
  obtain ⟨qWH, pwH, zH⟩ := x
  dsimp only
  refine Takes.after (by qs) fun _ => Takes.after (by qs) fun _ => ?_
  refine Takes.after (by qs) fun s5 => Takes.after (by qs) fun sIB =>
    Takes.after (by qs) fun s5h => ?_
  refine Takes.bind (takes_divide_productIn _ _ _ _ _) fun scE => ?_
  refine Takes.bind (N := ["BAT-sigma"]) (takes_batch 2) fun gamP => ?_
  refine Takes.after (by qs) fun sCl => ?_
  refine Takes.bind (takes_divide_valueBelowIn _ _ _ _ _) fun x => ?_
  obtain ⟨vpm, wJv⟩ := x
  dsimp only
  exact Takes.before (takes_divide_valueOnIn _ _ _ _ _) fun vpd => Takes.pure _

/-! ## The maximum and the index -/

/-- The draw of an element that batches n rows. -/
theorem takes_attain_coinsOm (n : Nat) : Takes (Attention.coinsOm n) ["BAT-sigma"] := by
  unfold Attention.coinsOm
  exact takes_batch n

/-- One round for each member of the list of degrees. -/
theorem takes_attain_scdRounds : ∀ (ds : List Nat) (p : Psc) (r : Array E),
    Takes (Attention.scdRounds ds p r) (List.replicate ds.length "PSC round")
  | [], p, r => by
    unfold Attention.scdRounds
    exact Takes.pure _
  | d :: ds, p, r => by
    unfold Attention.scdRounds
    exact Takes.bind (N := ["PSC round"]) (takes_roundIn _ _ _ _) fun x =>
      takes_attain_scdRounds ds _ _

/-- A sumcheck by degrees uses up the entries of a masked sumcheck with one round for each
degree. -/
theorem takes_attain_scdIn (degrees : List Nat) (degreeInY n : Nat) (start : Aff) :
    Takes (Attention.scdIn degrees degreeInY n start) (pscNames degrees.length true) := by
  unfold Attention.scdIn
  exact (Takes.bind (takes_pscBegin start) fun p =>
    Takes.bind (takes_attain_scdRounds degrees p _) fun x =>
      Takes.before (takes_pscEnds _ _ _) fun e => Takes.pure _).of_eq (by simp [pscNames])

/-- The score at the index. -/
theorem takes_attain_scoreAtIndexIn (S : Attention.Shape) (tg ti : Array E) :
    Takes (Attention.scoreAtIndexIn S tg ti) ("BAT-sigma" :: pscNames S.nvF true) := by
  unfold Attention.scoreAtIndexIn
  dsimp only
  refine Takes.after (by qs) fun sM6 => ?_
  refine Takes.bind (N := ["BAT-sigma"]) (takes_attain_coinsOm _) fun om => ?_
  exact Takes.before (takes_scores_sc3In _ _ _) fun o =>
    Takes.after (by qs) fun _ => Takes.pure _

/-- The key at the index. -/
theorem takes_attain_keyAtIndexIn (S : Attention.Shape) (scF : Attention.Sc3) :
    Takes (Attention.keyAtIndexIn S scF)
      ("BAT-sigma" :: pscNames S.scdDegrees.length true) := by
  unfold Attention.keyAtIndexIn
  dsimp only
  refine Takes.bind (N := ["BAT-sigma"]) (takes_attain_coinsOm _) fun om4 => ?_
  refine Takes.before (takes_attain_scdIn _ _ _ _) fun o => ?_
  exact Takes.after (by qs) fun s0 => by qs

/-- The sumcheck for the cells of the index. -/
theorem takes_attain_bitsIn (S : Attention.Shape) (tk tbg tbi : Array E) :
    Takes (Attention.bitsIn S tk tbg tbi) ("BAT-sigma" :: pscNames S.nvH true) := by
  unfold Attention.bitsIn
  dsimp only
  refine Takes.bind (N := ["BAT-sigma"]) (takes_attain_coinsOm _) fun om5 => ?_
  exact Takes.before (takes_scores_sc3In _ _ _) fun o => by qs

/-- **The messages on the row maximum and on the index use up the round of the two points and three
masked sumchecks, each behind the round of a batching element.** -/
theorem takes_attain : TakesRows.row_takes_attain := by
  intro S
  unfold Attention.attain TakesRows.attainNames
  dsimp only
  refine Takes.bind (N := ["ZERO"]) (takes_point .zero _) fun points => ?_
  refine (Takes.bind (takes_attain_scoreAtIndexIn S _ _) fun x => ?_).of_eq
    (List.cons_append ..)
  obtain ⟨sM6, scF⟩ := x
  dsimp only
  refine (Takes.bind (takes_attain_keyAtIndexIn S scF) fun scd => ?_).of_eq (List.cons_append ..)
  exact Takes.before (takes_attain_bitsIn S _ _ _) fun scH => Takes.pure _

/-! ## The planner's half -/

section Planner
open OnBytes.Params

/-- A routine on each member of a list: the members' lists in a row. -/
theorem says_attOwn_forEach {α : Type} {f : α → Planning Unit} {g : α → List String}
    (h : ∀ a, Says (f a) (g a)) : ∀ l : List α, Says (forEach l f) (l.flatMap g)
  | [] => by
    unfold forEach
    exact says_pure ()
  | a :: l => by
    unfold forEach
    rw [List.flatMap_cons]
    exact Says.bind (h a) fun _ => says_attOwn_forEach h l

/-- The planner's sumcheck of products. -/
theorem says_attOwn_sc3 (nv pairs : Nat) :
    Says (planPsc (attentionSc3 nv pairs)) (pscNames nv true) := by
  have h := says_psc (attentionSc3 nv pairs)
  simpa [pscNames, attentionSc3] using h

/-- The planner's sumcheck for the key at the index. -/
theorem says_attOwn_scd (lt lgk pairs Lam : Nat) :
    Says (planPsc (attentionScd lt lgk pairs Lam)) (pscNames (lt + lgk + lt) true) := by
  have h := says_psc (attentionScd lt lgk pairs Lam)
  simpa [pscNames, attentionScd, Nat.add_assoc] using h

/-- The planner's rounds for one segment of the scores. -/
theorem says_attOwn_score (s : Nat × Nat) :
    Says (planScalars 7 >>= fun _ => planPsc (attentionSc3 s.1 s.2)) (pscNames s.1 true) :=
  Says.after (says_scalars 7) fun _ => says_attOwn_sc3 _ _

/-- A step that says nothing and is taken under a condition alone, then r. -/
theorem says_attOwn_opt {c : Prop} [Decidable c] {a : Planning PUnit} {r : PUnit → Planning Unit}
    {N : List String} (ha : Says a []) (hr : ∀ y, Says (r y) N) :
    Says (if c then a >>= r else pure PUnit.unit >>= r) N := by
  split
  · exact Says.after ha hr
  · exact Says.after (says_pure _) hr

/-- **The planner's routine for an attention sub-proof's own rounds lays rounds with the names
attOwnNames.** -/
theorem says_attOwn : TakesRows.row_says_attOwn := by
  intro x
  unfold planAttentionOwn TakesRows.attOwnNames
  dsimp only
  refine says_attOwn_opt (says_scalars _) fun _ => ?_
  refine Says.bind
    (says_attOwn_forEach (g := fun s => pscNames s.1 true) says_attOwn_score x.score) fun _ => ?_
  refine Says.after (says_scalars _) fun _ => ?_
  refine Says.bind (says_attOwn_sc3 _ _) fun _ => ?_
  refine Says.bind (N := ["BAT-sigma"]) (says_batSigma _) fun _ => ?_
  refine Says.after (says_scalars _) fun _ => ?_
  refine Says.bind (says_attOwn_sc3 _ _) fun _ => ?_
  refine Says.bind (says_attOwn_sc3 _ _) fun _ => ?_
  refine Says.bind (N := ["ZERO"]) (says_zero _) fun _ => ?_
  refine Says.after (says_scalars _) fun _ => ?_
  refine Says.bind (N := ["BAT-sigma"]) (says_batSigma _) fun _ => ?_
  refine Says.bind (says_attOwn_sc3 _ _) fun _ => ?_
  refine Says.bind (N := ["BAT-sigma"]) (says_batSigma _) fun _ => ?_
  refine Says.bind (says_attOwn_scd _ _ _ _) fun _ => ?_
  refine Says.bind (N := ["BAT-sigma"]) (says_batSigma _) fun _ => ?_
  exact says_attOwn_sc3 _ _

end Planner

/-! ## The two lists are one -/

section Lists
open OnBytes.Attention

/-- Adding plane segments leaves the list of score segments. -/
theorem att_names_plane (k : ACall) (segs : List Attention.Seg) (x : Counts) :
    (segs.foldl (Counts.plane k) x).score = x.score := by
  induction segs generalizing x with
  | nil => rfl
  | cons s l ih =>
    rw [List.foldl_cons, ih]
    by_cases hs : k.holds s = true <;> simp [Counts.plane, hs]

/-- Adding score segments appends one pair for each segment that the call holds. -/
theorem att_names_scores (S : Attention.Shape) (k : ACall) (segs : List Attention.Seg)
    (x : Counts) :
    (segs.foldl (Counts.scores S k) x).score.toList = x.score.toList ++
      (segs.filter fun s => k.holds s).map fun s => (S.nvKF s, k.npOf s) := by
  induction segs generalizing x with
  | nil => simp
  | cons s l ih =>
    rw [List.foldl_cons, ih]
    by_cases hs : k.holds s = true <;> simp [Counts.scores, hs]

/-- What one call adds to the list of score segments. -/
theorem att_names_call (S : Attention.Shape) (x : Counts) (k : ACall) :
    (Counts.call S x k).score.toList = x.score.toList ++
      (if k.kind == Table.kfd then [Attention.Seg.fm, Attention.Seg.fd].filter fun s => k.holds s
        else []).map fun s => (S.nvKF s, k.npOf s) := by
  unfold Counts.call
  by_cases h1 : (k.kind == Table.kr) = true <;> by_cases h2 : (k.kind == Table.kfd) = true <;>
    simp only [h1, h2, if_true, if_false, Bool.false_eq_true, att_names_scores, att_names_plane,
      List.map_nil, List.append_nil]

/-- What a list of calls appends to the list of score segments: one pair for each of its units. The
calls are numbered from n on. -/
theorem att_names_calls (S : Attention.Shape) (l : List ACall) (x : Counts) (n : Nat) :
    (l.foldl (Counts.call S) x).score.toList = x.score.toList ++
      ((l.zipIdx n).flatMap fun y =>
        if y.1.kind == Table.kfd then
          ([Attention.Seg.fm, Attention.Seg.fd].filter fun s => y.1.holds s).map fun s =>
            (y.2, y.1, s)
        else []).map fun p => (S.nvKF p.2.2, p.2.1.npOf p.2.2) := by
  induction l generalizing x n with
  | nil => simp
  | cons k l ih =>
    rw [List.foldl_cons, ih _ (n + 1), att_names_call, List.zipIdx_cons, List.flatMap_cons,
      List.map_append, List.append_assoc]
    by_cases h1 : (k.kind == Table.kfd) = true <;> simp [h1, Function.comp_def]

/-- Where the plan succeeds, eight fields of the record of the own rounds are the shape's, the last
as a field of the pass over the calls. -/
theorem att_names_own (settings : Settings) (i : Attention.In) (cf : Attention.Cfg)
    (P : Attention.Plan) (h : Attention.plan settings i cf = .ok P) :
    P.own.lt = P.S.cf.lt ∧ P.own.lgk = P.S.cf.lgk ∧ P.own.e = P.S.nvE ∧
    P.own.valueM = P.S.nvVM ∧ P.own.valueD = P.S.nvVD ∧ P.own.attained = P.S.nvF ∧
    P.own.bits = P.S.nvH ∧ P.own.score = (Counts.of P.S).score.toList := by
  unfold Attention.plan at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  repeat' split at h
  all_goals (cases h <;> exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩)

/-- **At a plan that Attention.plan has made, the names of the entries that the three routines use
up are the names of the rounds that the planner lays.** -/
theorem att_names : TakesRows.row_att_names := by
  intro settings i cf P h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := att_names_own settings i cf P h
  have t := att_names_calls P.S P.S.calls.toList {} 0
  rw [Array.foldl_toList] at t
  have hs : P.own.score.flatMap (fun s => pscNames s.1 true) = TakesRows.scoresNames P.S := by
    rw [h8]
    unfold Counts.of TakesRows.scoresNames unitsOf
    rw [t]
    simp [List.flatMap_map]
  have hd : P.S.scdDegrees.length = P.S.cf.lt + P.S.cf.lgk + P.S.cf.lt := by
    simp [Attention.Shape.scdDegrees, Nat.add_assoc]
  unfold TakesRows.attOwnNames TakesRows.divideNames TakesRows.attainNames
  rw [hs, h1, h2, h3, h4, h5, h6, h7, hd]
  simp only [List.append_assoc, List.cons_append]

end Lists

end OnBytes.Tie.Pv.Tail.TakesProved
