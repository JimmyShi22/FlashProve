-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Tie/Pv/Lay/PlanBounds.lean: the rounds that the planner lays for a layers' sub-proof's own
rounds, whole: with their bounds on the error, their draws and their prices, as a closed function of
the sizes.

OnBytes/Tie/Pv/Lay/PlanList.lean gives the rounds' entries. A round of a plan (Params.PlanRound)
holds more: the bound on the error of the round, what is drawn, and how the round is priced. Here
the whole rounds are written as one list, `ownRounds`, stretch by stretch, and proved of the
planner's own routine.

Main names:
  `roundOf`, `quietOf`: the round that close and closeNone lay. `closeW_at`, `noneW_at`: that they
    do.
  `AddsW s b b' x L`: as Adds, with whole rounds. `addsW_*`: this of the planner's routines, one by
    one.
  `rZero`, `rJoin`, `rLine`, `rBat`, `rEps`, `rVar`, `rY`, `wPsc`, `wLayer`: the rounds of each
    kind.
  `ownRounds`, `own_addsW`: the whole list; AddsW s 0 0 (planLayerOwn x) (ownRounds s x).
  `ownRounds_entries`: its entries are ownList's.
  `ownBounds`, `ownRounds_errors`: the bounds on the errors as a list; that they are the rounds'.

Limits: nothing is said on whether finish accepts, nor on the sum of the errors.
-/
import OnBytes.Tie.Pv.Lay.PlanList

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Tie.Pv.Lay

open OnBytes OnBytes.Params

/-- a bound as close counts it in a request's scope -/
def scaled (s : Setting) (e : Bound) : Bound := if 1 < s.instances then e * Bound.ofNat s.instances
    else e

/-- the round that close adds -/
def roundOf (s : Setting) (name : String) (b : Nat) (e : Bound) (d : Draws) : PlanRound where
  entry := entryOf name (s.workOf .field .request) b d
  error := (scaled s e).error
  group := d.group
  why := .field
  rests := d.rests
  scope := .request
  wordFault := wordFaultOf d (scaled s e).error

/-- the round that closeNone adds -/
def quietOf (name : String) (b : Nat) : PlanRound where
  entry := { name := name, msg := b }
  scope := .request

theorem closeW_at {s : Setting} {b : Nat} {p q : PlanState} (h : At s b p) (name : String)
    (e : Bound) (d : Draws) (hq : close name .field e d p = .ok ((), q)) :
    At s 0 q ∧ q.rounds = p.rounds.push (roundOf s name b e d) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  unfold close at hq
  simp only [h1, h2, h3, h4, h5] at hq
  have hb : (Scope.request == Scope.request) = true := rfl
  by_cases hi : 1 < s.instances
  · simp only [hb, hi, decide_true, Bool.and_self, if_true] at hq
    split at hq
    · cases hq
    · have e1 := (Prod.mk.inj (Except.ok.inj hq)).2
      subst e1
      exact ⟨⟨rfl, rfl, rfl, rfl, rfl⟩, by simp only [roundOf, scaled, entryOf, hi, if_true]⟩
  · simp only [hb, hi, decide_false, Bool.and_false, Bool.false_eq_true, if_false] at hq
    split at hq
    · cases hq
    · have e1 := (Prod.mk.inj (Except.ok.inj hq)).2
      subst e1
      exact ⟨⟨rfl, rfl, rfl, rfl, rfl⟩, by simp only [roundOf, scaled, entryOf, hi, if_false]⟩

theorem noneW_at {s : Setting} {b : Nat} {p q : PlanState} (h : At s b p) (name : String)
    (hq : closeNone name p = .ok ((), q)) : At s 0 q ∧ q.rounds = p.rounds.push (quietOf name b) :=
        by
  unfold closeNone at hq
  split at hq
  · cases hq
  · have e1 := (Prod.mk.inj (Except.ok.inj hq)).2
    subst e1
    exact ⟨⟨h.set, h.scope, rfl, h.roots, rfl⟩, by simp only [quietOf, h.bytes, h.answers, h.scope]⟩

/-- x, from b open bytes, ends well only with b' open bytes, and has added just the rounds L -/
def AddsW (s : Setting) (b b' : Nat) (x : Planning Unit) (L : List PlanRound) : Prop :=
  ∀ p q, At s b p → x p = .ok ((), q) → At s b' q ∧ q.rounds = p.rounds ++ L.toArray

theorem AddsW.bind {s : Setting} {b b' b'' : Nat} {x y : Planning Unit} {L L' : List PlanRound}
    (hx : AddsW s b b' x L) (hy : AddsW s b' b'' y L') : AddsW s b b'' (x >>= fun _ => y) (L ++ L')
        :=
  fun p q hp h => by
    obtain ⟨_, r, h1, h2⟩ := bind_ok h
    obtain ⟨a1, e1⟩ := hx p r hp h1
    obtain ⟨a2, e2⟩ := hy r q a1 h2
    exact ⟨a2, by rw [e2, e1]; simp⟩

theorem AddsW.pure (s : Setting) (b : Nat) : AddsW s b b (pure ()) [] := fun p q hp h => by
  obtain rfl : p = q := (Prod.mk.inj (Except.ok.inj h)).2
  exact ⟨hp, by simp⟩

theorem AddsW.ite {s : Setting} {b b' : Nat} {c : Prop} [Decidable c] {x y : Planning Unit}
    {L L' : List PlanRound}
    (hx : AddsW s b b' x L) (hy : AddsW s b b' y L') :
    AddsW s b b' (if c then x else y) (if c then L else L') := by
  split
  · exact hx
  · exact hy

theorem AddsW.cast {s : Setting} {b b' c c' : Nat} {x : Planning Unit} {L L' : List PlanRound}
    (h : AddsW s b b' x L) (e1 : b = c) (e2 : b' = c') (e3 : L = L') : AddsW s c c' x L' := by
  subst e1 e2 e3
  exact h

theorem addsW_scalars (s : Setting) (b n : Nat) : AddsW s b (b + 24 * n) (planScalars n) [] := fun
    p q hp h => by
  obtain ⟨m, e, a, r⟩ := scalars_at hp n
  rw [e] at h
  obtain rfl : m = q := (Prod.mk.inj (Except.ok.inj h)).2
  exact ⟨a, by rw [r]; simp⟩

theorem addsW_close (s : Setting) (b : Nat) (name : String) (e : Setting → Bound) (d : Draws) :
    AddsW s b 0 (theSetting >>= fun s' => close name .field (e s') d) [roundOf s name b (e s) d] :=
        fun p q hp h => by
  obtain ⟨s2, m2, g2, h2⟩ := bind_ok h
  obtain ⟨rfl, rfl⟩ : p.set = s2 ∧ p = m2 := Prod.mk.inj (Except.ok.inj g2)
  obtain ⟨a2, er⟩ := closeW_at hp _ _ _ h2
  exact ⟨a2, by rw [er, hp.set]; simp⟩

/-! ### the closed rounds -/

def rZero (s : Setting) (v : Nat) : PlanRound := roundOf s "ZERO" 0 (fieldError s v)
    { drawE := v, priced := .roundItself }
def rJoin (s : Setting) (v : Nat) : PlanRound := roundOf s "JOIN" 0 (fieldError s v)
    { drawE := v, priced := .roundItself }
def rLine (s : Setting) : PlanRound := roundOf s "LINE" 0 (fieldError s 1)
    { drawE := 1, priced := .settingAlone }
def rBat (s : Setting) (b rows : Nat) : PlanRound :=
  roundOf s "BAT-sigma" b (powersError s rows) { drawE := 1, rows := rows, priced := .asSaid }
def rEps (s : Setting) (b : Nat) : PlanRound :=
  roundOf s "PSC epsilon" (b + 24) (fieldError s 1) { drawE := 1, priced := .settingAlone }
def rVar (s : Setting) : PlanRound := roundOf s "PSC round" 48 (fieldError s 2)
    { drawE := 1, priced := .roundItself }
def rY (s : Setting) (dy : Nat) : PlanRound :=
  roundOf s "PSC Y" (24 * dy) (fieldErrorNonzero s dy)
      { drawE := 1, drawNZ := 1, priced := .roundItself }

def wPsc (s : Setting) (b n dy vals : Nat) : List PlanRound :=
  [rEps s b] ++ List.replicate n (rVar s) ++ [rY s dy, quietOf "PSC values" (24 * vals)]
def wLayer (s : Setting) (v : Nat) : List PlanRound := wPsc s 0 v 2 2 ++ [rLine s]

theorem addsW_zero (s : Setting) (v : Nat) : AddsW s 0 0 (planZero v) [rZero s v] := addsW_close s
    0 "ZERO" (fun s' => fieldError s' v) _
theorem addsW_join (s : Setting) (v : Nat) : AddsW s 0 0 (planJoin v) [rJoin s v] := addsW_close s
    0 "JOIN" (fun s' => fieldError s' v) _
theorem addsW_line (s : Setting) : AddsW s 0 0 planLine [rLine s] := addsW_close s 0 "LINE" (fun s'
    => fieldError s' 1) _
theorem addsW_bat (s : Setting) (b rows : Nat) : AddsW s b 0 (planBatSigma rows) [rBat s b rows] :=
  addsW_close s b "BAT-sigma" (fun s' => powersError s' rows) _

theorem addsW_vars (s : Setting) : ∀ n : Nat, AddsW s 0 0 (planPscRounds s (List.replicate n 3))
    (List.replicate n (rVar s))
  | 0 => AddsW.pure s 0
  | n + 1 => fun p q hp hq => by
    have hq' : (planScalars (3 - 1) >>= fun _ =>
        close "PSC round" .field (fieldError s (3 - 1)) { drawE := 1, priced := .roundItself } >>=
            fun _ =>
        planPscRounds s (List.replicate n 3)) p = .ok ((), q) := hq
    obtain ⟨_, m1, h1, hq1⟩ := bind_ok hq'
    obtain ⟨a1, r1⟩ := addsW_scalars s 0 (3 - 1) p m1 hp h1
    obtain ⟨_, m2, h2, hq2⟩ := bind_ok hq1
    obtain ⟨a2, er⟩ := closeW_at a1 _ _ _ h2
    obtain ⟨a3, el⟩ := addsW_vars s n m2 q a2 hq2
    refine ⟨a3, ?_⟩
    have e48 : roundOf s "PSC round" (0 + 24 * (3 - 1)) (fieldError s (3 - 1))
        { drawE := 1, priced := .roundItself } = rVar s := rfl
    rw [el, er, r1, e48]
    apply Array.toList_inj.mp
    simp [List.replicate_succ]

theorem addsW_psc (s : Setting) (b n dy vals : Nat) :
    AddsW s b 0 (planPsc { degree := List.replicate n 3, degreeY := dy, values := vals }) (wPsc s b
        n dy vals) :=
  fun p q hp h => by
  have h' : (theSetting >>= fun s' =>
      planScalars 1 >>= fun _ =>
      close "PSC epsilon" .field (fieldError s' 1) { drawE := 1, priced := .settingAlone } >>= fun
          _ =>
      planPscRounds s' (List.replicate n 3) >>= fun _ =>
      planScalars dy >>= fun _ =>
      close "PSC Y" .field (fieldErrorNonzero s' dy)
          { drawE := 1, drawNZ := 1, priced := .roundItself } >>= fun _ =>
      planScalars vals >>= fun _ =>
      closeNone "PSC values") p = .ok ((), q) := h
  obtain ⟨s4, m4, g4, k4⟩ := bind_ok h'
  obtain ⟨rfl, rfl⟩ : p.set = s4 ∧ p = m4 := Prod.mk.inj (Except.ok.inj g4)
  rw [hp.set] at k4
  obtain ⟨_, m5, h5, k5⟩ := bind_ok k4
  obtain ⟨a5, r5⟩ := addsW_scalars s b 1 p m5 hp h5
  obtain ⟨_, m6, h6, k6⟩ := bind_ok k5
  obtain ⟨a6, er6⟩ := closeW_at a5 _ _ _ h6
  obtain ⟨_, m7, h7, k7⟩ := bind_ok k6
  obtain ⟨a7, el7⟩ := addsW_vars s n m6 m7 a6 h7
  obtain ⟨_, m8, h8, k8⟩ := bind_ok k7
  obtain ⟨a8, r8⟩ := addsW_scalars s 0 dy m7 m8 a7 h8
  obtain ⟨_, m9, h9, k9⟩ := bind_ok k8
  obtain ⟨a9, er9⟩ := closeW_at a8 _ _ _ h9
  obtain ⟨_, m10, h10, k10⟩ := bind_ok k9
  obtain ⟨a10, r10⟩ := addsW_scalars s 0 vals m9 m10 a9 h10
  obtain ⟨a11, er11⟩ := noneW_at a10 _ k10
  refine ⟨a11, ?_⟩
  have e1 : roundOf s "PSC epsilon" (b + 24 * 1) (fieldError s 1)
      { drawE := 1, priced := .settingAlone } = rEps s b := rfl
  have e2 : roundOf s "PSC Y" (0 + 24 * dy) (fieldErrorNonzero s dy)
      { drawE := 1, drawNZ := 1, priced := .roundItself } = rY s dy := by
    rw [Nat.zero_add]
    rfl
  have e3 : quietOf "PSC values" (0 + 24 * vals) = quietOf "PSC values" (24 * vals) := by rw
      [Nat.zero_add]
  rw [er11, r10, er9, r8, el7, er6, r5, e1, e2, e3]
  apply Array.toList_inj.mp
  simp [wPsc]

theorem addsW_layer (s : Setting) (v : Nat) : AddsW s 0 0 (planProductLayer v) (wLayer s v) :=
  AddsW.bind (addsW_psc s 0 v 2 2) (addsW_line s)

theorem addsW_token (s : Setting) (lt dy shown : Nat) :
    AddsW s 0 0 (planTokenSumcheck lt dy shown) (wPsc s 24 lt dy shown) :=
  (AddsW.bind (addsW_scalars s 0 1) (addsW_psc s (0 + 24 * 1) lt dy shown)).cast rfl rfl (by simp)

/-! ### the fifteen stretches, as whole rounds -/

def ptTokenW (s : Setting) (x : LayerRounds) : List PlanRound := [rZero s x.lt]
def ptFirstW (s : Setting) (x : LayerRounds) : List PlanRound :=
  if x.firstGroup then [rZero s (x.ls + x.lt), rZero s (x.lPd - x.ls)] else []
def batLimbsW (s : Setting) (x : LayerRounds) : List PlanRound := [rBat s (24 * (x.NS * x.NI)) x.NS]
def joinNormsW (s : Setting) (x : LayerRounds) : List PlanRound := if x.lNI != 0 then [rJoin s
    x.lNI] else []
def squaresW (s : Setting) (x : LayerRounds) : List PlanRound := wLayer s (x.lNI + x.lPd + x.lt)
def batProductsW (s : Setting) (x : LayerRounds) : List PlanRound := [rBat s (24 * (x.NP * x.NI))
    (x.NP * x.NI)]
def rowProductsW (s : Setting) (x : LayerRounds) : List PlanRound := wPsc s 24 x.lt 2 (x.NO * x.NI)
def termsW (s : Setting) (x : LayerRounds) : List PlanRound := if x.withTerms then wPsc s 24 x.lt 1
    x.shownByTheTerms else []
def batTwoW (s : Setting) (x : LayerRounds) : List PlanRound := if x.withTerms then [rBat s 0 2]
    else []
def innerW (s : Setting) (x : LayerRounds) : List PlanRound := wPsc s 0 x.lamS 2 (2 + x.neverSent +
    x.weightClaims)
def gatedW (s : Setting) (x : LayerRounds) : List PlanRound := wLayer s (x.ll + x.lPf + x.lt)
def joinRoutedW (s : Setting) (x : LayerRounds) : List PlanRound :=
  if x.routed then (if 1 < x.ll then [rJoin s (x.ll - 1)] else []) else []
def routedW (s : Setting) (x : LayerRounds) : List PlanRound := if x.routed then wLayer s (x.ll - 1
    + x.lfe + x.lt) else []
def batWeightsW (s : Setting) (x : LayerRounds) : List PlanRound :=
  [rBat s (if x.firstGroup then 24 else 0) (x.weightClaims + (if x.firstGroup then 1 else 0))]
def mergeW (s : Setting) (x : LayerRounds) : List PlanRound := wPsc s 0 x.lkW 1 1

/-- THE WHOLE LIST OF WHOLE ROUNDS. -/
def ownRounds (s : Setting) (x : LayerRounds) : List PlanRound :=
  ptTokenW s x ++ ptFirstW s x ++ batLimbsW s x ++ joinNormsW s x ++ squaresW s x ++ batProductsW s
      x ++ rowProductsW s x ++
    termsW s x ++ batTwoW s x ++ innerW s x ++ gatedW s x ++ joinRoutedW s x ++ routedW s x ++
        batWeightsW s x ++ mergeW s x

theorem addsW_after (s : Setting) (x : LayerRounds) : AddsW s 0 0 (afterOwn x)
    (termsW s x ++ batTwoW s x ++ innerW s x ++ gatedW s x ++ joinRoutedW s x ++ routedW s x ++
        batWeightsW s x ++ mergeW s x) := by
  rw [after_eq]
  have hT : AddsW s 0 0 (if x.withTerms then (planTokenSumcheck x.lt 1 x.shownByTheTerms >>= fun _
      => planBatSigma 2) else pure ())
      (termsW s x ++ batTwoW s x) :=
    (AddsW.ite (AddsW.bind (addsW_token s x.lt 1 x.shownByTheTerms) (addsW_bat s 0 2)) (AddsW.pure
        s 0)).cast rfl rfl (by
      unfold termsW batTwoW
      split <;> simp)
  have hR : AddsW s 0 0 (if x.routed then ((if 1 < x.ll then planJoin (x.ll - 1) else pure ()) >>=
      fun _ =>
        planProductLayer (x.ll - 1 + x.lfe + x.lt)) else pure ()) (joinRoutedW s x ++ routedW s x)
            :=
    (AddsW.ite (AddsW.bind (AddsW.ite (addsW_join s (x.ll - 1)) (AddsW.pure s 0)) (addsW_layer s
        _)) (AddsW.pure s 0)).cast rfl rfl (by
      unfold joinRoutedW routedW
      split <;> simp)
  have hW : AddsW s 0 0 ((if x.firstGroup then planScalars 1 else pure ()) >>= fun _ =>
        planBatSigma (x.weightClaims + (if x.firstGroup then 1 else 0))) (batWeightsW s x) := by
    unfold batWeightsW
    by_cases hf : x.firstGroup = true
    · simp only [hf, if_true]
      exact (AddsW.bind (addsW_scalars s 0 1) (addsW_bat s (0 + 24 * 1) _)).cast rfl rfl (by simp)
    · simp only [hf, if_false, Bool.false_eq_true]
      exact (AddsW.bind (AddsW.pure s 0) (addsW_bat s 0 _)).cast rfl rfl (by simp)
  have h := AddsW.bind hT (AddsW.bind (addsW_psc s 0 x.lamS 2 (2 + x.neverSent + x.weightClaims))
    (AddsW.bind (addsW_layer s (x.ll + x.lPf + x.lt)) (AddsW.bind hR (AddsW.bind hW (addsW_psc s 0
        x.lkW 1 1)))))
  intro p q hp hq
  refine (h.cast rfl rfl ?_) p q hp ?_
  · simp only [innerW, gatedW, mergeW, List.append_assoc]
  · simpa only [bind_assoc] using hq

/-- The planner's own planLayerOwn adds just ownRounds: every field of every round. -/
theorem own_addsW (s : Setting) (x : LayerRounds) : AddsW s 0 0 (planLayerOwn x) (ownRounds s x) :=
    by
  rw [own_eq]
  have hF : AddsW s 0 0 (if x.firstGroup then (planZero (x.ls + x.lt) >>= fun _ => planZero (x.lPd
      - x.ls)) else pure ())
      (ptFirstW s x) :=
    AddsW.ite (AddsW.bind (addsW_zero s _) (addsW_zero s _)) (AddsW.pure s 0)
  have hJ : AddsW s 0 0 (if x.lNI != 0 then planJoin x.lNI else pure ()) (joinNormsW s x) :=
    AddsW.ite (addsW_join s x.lNI) (AddsW.pure s 0)
  have hL : AddsW s 0 0 (planScalars (x.NS * x.NI) >>= fun _ => planBatSigma x.NS) (batLimbsW s x)
      :=
    (AddsW.bind (addsW_scalars s 0 (x.NS * x.NI)) (addsW_bat s (0 + 24 * (x.NS * x.NI)) x.NS)).cast
        rfl rfl (by simp [batLimbsW])
  have hP : AddsW s 0 0 (planScalars (x.NP * x.NI) >>= fun _ => planBatSigma (x.NP * x.NI))
      (batProductsW s x) :=
    (AddsW.bind (addsW_scalars s 0 (x.NP * x.NI)) (addsW_bat s (0 + 24 * (x.NP * x.NI)) (x.NP *
        x.NI))).cast rfl rfl
      (by simp [batProductsW])
  have h := AddsW.bind (addsW_zero s x.lt) (AddsW.bind hF (AddsW.bind hL (AddsW.bind hJ
    (AddsW.bind (addsW_layer s (x.lNI + x.lPd + x.lt)) (AddsW.bind hP
      (AddsW.bind (addsW_token s x.lt 2 (x.NO * x.NI)) (addsW_after s x)))))))
  intro p q hp hq
  refine (h.cast rfl rfl ?_) p q hp ?_
  · simp only [ownRounds, ptTokenW, squaresW, rowProductsW, List.append_assoc]
  · simpa only [bind_assoc] using hq

/-- its entries are the list of OnBytes/Tie/Pv/Lay/PlanList.lean -/
theorem ownRounds_entries (s : Setting) (x : LayerRounds) :
    (ownRounds s x).map (·.entry) = ownList (s.workOf .field .request) x := by
  have hp : ∀ b n dy vals, (wPsc s b n dy vals).map (·.entry) = lPsc (s.workOf .field .request) b n
      dy vals := by
    intro b n dy vals
    simp [wPsc, lPsc, rEps, rVar, rY, roundOf, quietOf, entryOf, eDraw]
  have hl : ∀ v, (wLayer s v).map (·.entry) = lLayer (s.workOf .field .request) v := by
    intro v
    simp [wLayer, lLayer, hp, rLine, roundOf, entryOf, eDraw]
  have h1 : (ptTokenW s x).map (·.entry) = ptToken (s.workOf .field .request) x := by
    simp [ptTokenW, ptToken, rZero, roundOf, entryOf, eDraw]
  have h2 : (ptFirstW s x).map (·.entry) = ptFirst (s.workOf .field .request) x := by
    unfold ptFirstW ptFirst
    split <;> simp [rZero, roundOf, entryOf, eDraw]
  have h3 : (batLimbsW s x).map (·.entry) = batLimbs (s.workOf .field .request) x := by
    simp [batLimbsW, batLimbs, rBat, roundOf, entryOf, eBat]
  have h4 : (joinNormsW s x).map (·.entry) = joinNorms (s.workOf .field .request) x := by
    unfold joinNormsW joinNorms
    split <;> simp [rJoin, roundOf, entryOf, eDraw]
  have h6 : (batProductsW s x).map (·.entry) = batProducts (s.workOf .field .request) x := by
    simp [batProductsW, batProducts, rBat, roundOf, entryOf, eBat]
  have h8 : (termsW s x).map (·.entry) = terms (s.workOf .field .request) x := by
    unfold termsW terms
    split <;> simp [hp]
  have h9 : (batTwoW s x).map (·.entry) = batTwo (s.workOf .field .request) x := by
    unfold batTwoW batTwo
    split <;> simp [rBat, roundOf, entryOf, eBat]
  have h12 : (joinRoutedW s x).map (·.entry) = joinRouted (s.workOf .field .request) x := by
    unfold joinRoutedW joinRouted
    split
    · split <;> simp [rJoin, roundOf, entryOf, eDraw]
    · simp
  have h13 : (routedW s x).map (·.entry) = routed (s.workOf .field .request) x := by
    unfold routedW routed
    split <;> simp [hl]
  have h14 : (batWeightsW s x).map (·.entry) = batWeights (s.workOf .field .request) x := by
    simp [batWeightsW, batWeights, rBat, roundOf, entryOf, eBat]
  simp only [ownRounds, ownList, List.map_append, h1, h2, h3, h4, h6, h8, h9, h12, h13, h14,
      squaresW, squares, rowProductsW,
    rowProducts, innerW, inner, gatedW, gated, mergeW, merge, hp, hl]

/-! ### the plan's bounds, round by round -/

/-- the error that the plan writes beside a round whose bound is e; none: a round in which the
verifier says nothing -/
def errorOf (s : Setting) : Option Bound → Binary
  | some e => (scaled s e).error
  | none => {}

def bPsc (s : Setting) (n dy : Nat) : List (Option Bound) :=
  [some (fieldError s 1)] ++ List.replicate n (some (fieldError s 2)) ++ [some (fieldErrorNonzero s
      dy), none]
def bLayer (s : Setting) (v : Nat) : List (Option Bound) := bPsc s v 2 ++ [some (fieldError s 1)]

/-- THE BOUNDS, in ownList's order: fieldError s k = k / cardE; fieldErrorNonzero s k = k / (cardE
− 1); powersError s rows = (rows − 1) / cardE (Params/Distance.lean:250-257) -/
def ownBounds (s : Setting) (x : LayerRounds) : List (Option Bound) :=
  [some (fieldError s x.lt)] ++
  (if x.firstGroup then [some (fieldError s (x.ls + x.lt)), some (fieldError s (x.lPd - x.ls))]
      else []) ++
  [some (powersError s x.NS)] ++
  (if x.lNI != 0 then [some (fieldError s x.lNI)] else []) ++
  bLayer s (x.lNI + x.lPd + x.lt) ++
  [some (powersError s (x.NP * x.NI))] ++
  bPsc s x.lt 2 ++
  (if x.withTerms then bPsc s x.lt 1 else []) ++
  (if x.withTerms then [some (powersError s 2)] else []) ++
  bPsc s x.lamS 2 ++
  bLayer s (x.ll + x.lPf + x.lt) ++
  (if x.routed then (if 1 < x.ll then [some (fieldError s (x.ll - 1))] else []) else []) ++
  (if x.routed then bLayer s (x.ll - 1 + x.lfe + x.lt) else []) ++
  [some (powersError s (x.weightClaims + (if x.firstGroup then 1 else 0)))] ++
  bPsc s x.lkW 1

theorem ownRounds_errors (s : Setting) (x : LayerRounds) :
    (ownRounds s x).map (·.error) = (ownBounds s x).map (errorOf s) := by
  have hp : ∀ b n dy vals, (wPsc s b n dy vals).map (·.error) = (bPsc s n dy).map (errorOf s) := by
    intro b n dy vals
    simp [wPsc, bPsc, rEps, rVar, rY, roundOf, quietOf, errorOf]
  have hl : ∀ v, (wLayer s v).map (·.error) = (bLayer s v).map (errorOf s) := by
    intro v
    simp [wLayer, bLayer, hp, rLine, roundOf, errorOf]
  have h2 : (ptFirstW s x).map (·.error) =
      (if x.firstGroup then [some (fieldError s (x.ls + x.lt)), some (fieldError s (x.lPd - x.ls))]
          else []).map (errorOf s) := by
    unfold ptFirstW
    split <;> simp [rZero, roundOf, errorOf]
  have h4 : (joinNormsW s x).map (·.error) = (if x.lNI != 0 then [some (fieldError s x.lNI)] else
      []).map (errorOf s) := by
    unfold joinNormsW
    split <;> simp [rJoin, roundOf, errorOf]
  have h8 : (termsW s x).map (·.error) = (if x.withTerms then bPsc s x.lt 1 else []).map (errorOf
      s) := by
    unfold termsW
    split <;> simp [hp]
  have h9 : (batTwoW s x).map (·.error) = (if x.withTerms then [some (powersError s 2)] else
      []).map (errorOf s) := by
    unfold batTwoW
    split <;> simp [rBat, roundOf, errorOf]
  have h12 : (joinRoutedW s x).map (·.error) =
      (if x.routed then (if 1 < x.ll then [some (fieldError s (x.ll - 1))] else []) else []).map
          (errorOf s) := by
    unfold joinRoutedW
    split
    · split <;> simp [rJoin, roundOf, errorOf]
    · simp
  have h13 : (routedW s x).map (·.error) = (if x.routed then bLayer s (x.ll - 1 + x.lfe + x.lt)
      else []).map (errorOf s) := by
    unfold routedW
    split <;> simp [hl]
  simp only [ownRounds, ownBounds, List.map_append, h2, h4, h8, h9, h12, h13, squaresW,
      rowProductsW, innerW, gatedW, mergeW, hp, hl]
  simp [ptTokenW, batLimbsW, batProductsW, batWeightsW, rZero, rBat, roundOf, errorOf]

end OnBytes.Tie.Pv.Lay

#print axioms OnBytes.Tie.Pv.Lay.own_addsW
#print axioms OnBytes.Tie.Pv.Lay.ownRounds_entries
#print axioms OnBytes.Tie.Pv.Lay.ownRounds_errors
